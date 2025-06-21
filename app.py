import os
import json
import requests
import re
import string
import jellyfish
from flask import Flask, request, jsonify, render_template
from flask_cors import CORS
from dotenv import load_dotenv
import gspread
from google.oauth2.service_account import Credentials
from datetime import datetime, timedelta
import logging
import difflib
import uuid

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Load environment variables
load_dotenv()

TOGETHER_API_KEY = os.getenv("API")
PRODUCT_SHEET_URL = os.getenv("PRODUCT_SHEET_URL")
OFFICE_STATUS_SHEET_URL = os.getenv("OFFICE_STATUS_SHEET_URL")
ORDER_SHEET_URL = os.getenv("ORDER_SHEET_URL")
SERVICE_ACCOUNT_JSON = os.getenv("SERVICE_ACCOUNT_JSON")

# Setup Flask app
app = Flask(__name__)
CORS(app, resources={r"/*": {"origins": "https://sitetest-76es.onrender.com"}})

# Google Sheets Setup
scopes = ['https://www.googleapis.com/auth/spreadsheets']
try:
    # Parse service account JSON from environment variable
    service_account_info = json.loads(SERVICE_ACCOUNT_JSON)
    credentials = Credentials.from_service_account_info(
        service_account_info,
        scopes=scopes
    )
    gc = gspread.authorize(credentials)

    # Initialize sheets
    product_sheet = gc.open_by_url(PRODUCT_SHEET_URL).sheet1
    office_sheet = gc.open_by_url(OFFICE_STATUS_SHEET_URL).sheet1
    order_sheet = gc.open_by_url(ORDER_SHEET_URL).sheet1
    logger.info("Successfully connected to Google Sheets")
except Exception as e:
    logger.error(f"Google Sheets connection failed: {str(e)}")
    exit(1)


# Static Texts
def load_txt(filename):
    try:
        with open(filename, 'r', encoding='utf-8') as f:
            return f.read().strip()
    except FileNotFoundError:
        logger.warning(f"File {filename} not found, using default text")
        return ""


greeting_text = load_txt('greeting.txt') or "Добро пожаловать в JR Store AI Чат!"
details_text = load_txt('details.txt') or "Мы продаем iPhone с гарантией качества."
delivery_options_text = load_txt('delivery_options.txt') or (
    "Выберите способ доставки:\n- Самовывоз\n- Курьерская доставка"
)
office_closed_text = load_txt('office_closed_response.txt') or (
    "Наш офис сейчас закрыт. Хотите оформить доставку?"
)


# State Management
class UserState:
    def __init__(self):
        self.phase = "init"
        self.delivery_method = None
        self.order_data = {
            "ФИО": "",
            "Контакт": "",
            "Модель": "",
            "Объём": "",
            "Цвет": "",
            "Зарядный блок": "Нет"
        }
        self.last_active = datetime.now()
        self.asked_for_details = False
        self.order_confirmed = False
        self.context_cut = False
        self.current_order_step = None
        self.reset_context = False


user_states = {}
chat_histories = {}
MAX_CONTEXT = 15
SESSION_TIMEOUT = timedelta(minutes=45)

MODEL_PATTERNS = {
    'pro': ['pro', 'про', 'рго', 'прo', 'пpo'],
    'max': ['max', 'макс', 'маx', 'мaкс', 'мax'],
    'mini': ['mini', 'мини', 'минь', 'миni', 'мин'],
    'plus': ['plus', 'плюс', 'плс', 'pls', 'плю'],
    'standard': ['', 'стандарт', 'обычный', 'базовый']
}

MODEL_NUMBER_PATTERN = r'\d{1,2}'


def is_available(availability_str):
    if not availability_str:
        return False
    avail = availability_str.strip().lower()
    return avail in ['да', 'в наличии', 'yes', 'available', 'есть']


def cleanup_expired_sessions():
    now = datetime.now()
    expired_users = [
        user_id for user_id, state in user_states.items()
        if now - state.last_active > SESSION_TIMEOUT
    ]
    for user_id in expired_users:
        del user_states[user_id]
        if user_id in chat_histories:
            del chat_histories[user_id]
    logger.info(f"Cleaned up {len(expired_users)} expired sessions")


def normalize_model_name(model_name):
    if not model_name:
        return ""

    model = model_name.lower().translate(
        str.maketrans('', '', string.punctuation)
    )

    replacements = {
        'айфон': 'iphone',
        'iphone': '',
        'apple': '',
        'series': '',
        'model': '',
        'gb': '',
        'tb': '',
        ' ': '',
        '-': '',
        'про': 'pro',
        'макс': 'max',
        'плюс': 'plus',
        'мини': 'mini',
        'стандарт': '',
        'обычный': '',
        'базовый': '',
        'мии': 'mini',
        'промакс': 'promax',
        'промак': 'promax',
        'плю': 'plus',
        'min': 'mini',
        'pro max': 'promax'
    }

    for key, value in replacements.items():
        model = model.replace(key, value)

    model_number = re.search(MODEL_NUMBER_PATTERN, model)
    model_number = model_number.group(0) if model_number else ""

    variant = ""
    for var_type, patterns in MODEL_PATTERNS.items():
        for pattern in patterns:
            if pattern in model:
                variant = var_type
                break
        if variant:
            break

    # Handle special cases
    if "promax" in model:
        variant = "promax"
    elif "max" in model and not variant:
        variant = "max"
    elif "pro" in model and not variant:
        variant = "pro"

    return f"{model_number}{variant}"


def normalize_storage(storage):
    if not storage:
        return ""
    if isinstance(storage, str):
        storage_num = re.sub(r'[^0-9]', '', storage)
        return f"{storage_num} ГБ" if storage_num else ""
    return f"{storage} ГБ"


def normalize_color(color):
    if not color:
        return ""

    color = color.lower()
    color_map = {
        'space gray': 'серый',
        'spacegrey': 'серый',
        'spacegray': 'серый',
        'midnight': 'синий',
        'starlight': 'золотой',
        'gold': 'золотой',
        'red': 'красный',
        'blue': 'синий',
        'black': 'черный',
        'white': 'белый',
        'purple': 'фиолетовый',
        'green': 'зеленый',
        'silver': 'серебристый',
        'серый': 'серый',
        'синий': 'синий',
        'голубой': 'синий',
        'золотой': 'золотой',
        'красный': 'красный',
        'черный': 'черный',
        'белый': 'белый',
        'фиолетовый': 'фиолетовый',
        'зеленый': 'зеленый',
        'серебристый': 'серебристый',
        'розовый': 'розовый',
        'темная ночь': 'синий',
        'звездный свет': 'золотой',
    }

    if color in color_map:
        return color_map[color]

    best_match = None
    best_score = 0
    for key in color_map:
        score = jellyfish.jaro_similarity(color, key)
        if score > 0.85 and score > best_score:
            best_match = key
            best_score = score

    return color_map[best_match] if best_match else color


def find_matching_products(products, model=None, storage=None, color=None):
    results = []

    for product in products:
        if not is_available(product.get('Наличие', '')):
            continue

        match_score = 0

        if model:
            input_norm = normalize_model_name(model)
            product_norm = normalize_model_name(product.get('Модель', ''))

            if input_norm == product_norm:
                match_score += 100
            elif input_norm in product_norm or product_norm in input_norm:
                match_score += 75
            else:
                input_nums = set(re.findall(r'\d+', input_norm))
                product_nums = set(re.findall(r'\d+', product_norm))
                if input_nums and input_nums.issubset(product_nums):
                    match_score += 50
                elif input_nums and product_nums and input_nums == product_nums:
                    match_score += 40

        if storage:
            input_norm = normalize_storage(storage)
            product_norm = normalize_storage(product.get('Объём', ''))
            if input_norm == product_norm:
                match_score += 20

        if color:
            input_norm = normalize_color(color)
            product_norm = normalize_color(product.get('Цвет', ''))
            if input_norm == product_norm:
                match_score += 10

        if (model or storage or color) and match_score >= 50:
            results.append((product, match_score))

    results.sort(key=lambda x: x[1], reverse=True)
    return [item[0] for item in results]


def get_available_products():
    try:
        return product_sheet.get_all_records()
    except Exception as e:
        logger.error(f"Product fetch error: {str(e)}")
        return []


def get_available_models(products=None):
    if products is None:
        products = get_available_products()
    return list(set(
        p['Модель'] for p in products if is_available(p.get('Наличие', ''))
    ))


def get_available_storages(products, model):
    return list(set(
        p['Объём'] for p in products
        if is_available(p.get('Наличие', '')) and
        normalize_model_name(p.get('Модель', '')) == normalize_model_name(model)
    ))


def get_available_colors(products, model, storage):
    return list(set(
        p['Цвет'] for p in products
        if is_available(p.get('Наличие', '')) and
        normalize_model_name(p.get('Модель', '')) == normalize_model_name(model) and
        normalize_storage(p.get('Объём', '')) == normalize_storage(storage)
    ))


def find_similar_models(user_input, available_models):
    user_input_norm = normalize_model_name(user_input)
    suggestions = []
    seen = set()

    for model in available_models:
        norm_model = normalize_model_name(model)
        if user_input_norm in norm_model or norm_model in user_input_norm:
            if model not in seen:
                suggestions.append(model)
                seen.add(model)

    if not suggestions:
        numbers = re.findall(r'\d+', user_input)
        if numbers:
            for model in available_models:
                model_numbers = re.findall(r'\d+', model)
                if any(num in model_numbers for num in numbers):
                    if model not in seen:
                        suggestions.append(model)
                        seen.add(model)

    if not suggestions:
        for model in available_models:
            norm_model = normalize_model_name(model)
            match = True
            for keyword, patterns in MODEL_PATTERNS.items():
                if keyword in norm_model:
                    if not any(pattern in user_input_norm for pattern in patterns):
                        match = False
                        break
            if match and model not in seen:
                suggestions.append(model)
                seen.add(model)

    if not suggestions:
        similarity_scores = []
        for model in available_models:
            norm_model = normalize_model_name(model)
            similarity = jellyfish.jaro_similarity(user_input_norm, norm_model)
            if similarity > 0.85:
                similarity_scores.append((model, similarity))

        similarity_scores.sort(key=lambda x: x[1], reverse=True)
        suggestions = [item[0] for item in similarity_scores]

    if not suggestions:
        suggestions = difflib.get_close_matches(
            user_input,
            available_models,
            n=3,
            cutoff=0.7
        )

    return suggestions[:3]


def format_order_summary(order_data):
    summary = "📝 Ваш заказ:\n"
    summary += f"• Модель: {order_data['Модель']}\n"
    summary += f"• Объём: {order_data['Объём']}\n"
    summary += f"• Цвет: {order_data['Цвет']}\n"
    summary += f"• Зарядный блок: {order_data['Зарядный блок']}\n"
    summary += f"• Доставка: {order_data['Доставка']}\n"
    summary += f"• ФИО: {order_data['ФИО']}\n"
    summary += f"• Контакт: {order_data['Контакт']}"
    return summary


def extract_models_from_input(user_input):
    models = []
    patterns = [
        r'\b(?:iphone|айфон|phone)\s*(\d{1,2})\s*(pro\s*max|pro|plus|mini|max)?\b',
        r'\b(\d{1,2})\s*(pro\s*max|pro|plus|mini|max|мини|мин|мии|про|плюс)\b',
        r'\b(\d{1,2})\b',
        r'\b(?:iphone|айфон)\s*(\d{1,2})\b',
        r'\b(?:айфон|айфона|айфоном)\s*(\d{1,2})\s*(про|макс|мини|плюс)?\b'
    ]

    for pattern in patterns:
        matches = re.findall(pattern, user_input, re.IGNORECASE)
        for match in matches:
            if isinstance(match, tuple):
                number = match[0]
                variant = match[1] if len(match) > 1 else ""
            else:
                number = match
                variant = ""

            variant_map = {
                'мин': 'mini', 'мини': 'mini', 'мии': 'mini',
                'про': 'pro', 'плюс': 'plus', 'макс': 'max'
            }

            variant = variant_map.get(variant.lower(), variant.lower())
            model_name = f"iPhone {number}"
            if variant:
                model_name += f" {variant.capitalize()}"

            models.append(model_name)

    seen = set()
    return [m for m in models if not (m in seen or seen.add(m))]


def match_delivery_option(text):
    text = text.lower()
    if "самовывоз" in text or "офис" in text or "заберу" in text:
        return "Самовывоз"
    elif "курьер" in text or "доставк" in text or "привез" in text:
        return "Курьерская доставка"
    return None


def get_office_status():
    try:
        records = office_sheet.get_all_records()
        return records[0]['Состояние'] if records else "Неизвестно"
    except Exception as e:
        logger.error(f"Office status error: {str(e)}")
        return "Неизвестно"


def submit_order(data):
    try:
        order_sheet.append_row([
            data["ФИО"],
            data["Контакт"],
            data["Модель"],
            data["Объём"],
            data["Цвет"],
            data["Зарядный блок"],
            data["Доставка"]
        ], value_input_option='USER_ENTERED')
        logger.info(f"Order submitted: {data}")
        return True
    except Exception as e:
        logger.error(f"Order submission error: {str(e)}")
        return False


def generate_llama_response(prompt):
    url = "https://api.together.xyz/v1/chat/completions"
    headers = {
        "Authorization": f"Bearer {TOGETHER_API_KEY}",
        "Content-Type": "application/json"
    }
    payload = {
        "model": "meta-llama/Llama-3-70b-chat-hf",
        "messages": [
            {
                "role": "system",
                "content": "Ты консультант магазина WAY Store который продаёт технику Apple. Техника Apple как новая. Отвечай кратко и точно на русском."
            },
            {"role": "user", "content": prompt}
        ],
        "temperature": 0.3,
        "max_tokens": 300
    }

    try:
        logger.info("Sending request to AI model")
        response = requests.post(url, headers=headers, json=payload, timeout=30)
        response.raise_for_status()
        content = response.json()["choices"][0]["message"]["content"].strip()
        logger.info(f"AI response: {content}")
        return content
    except Exception as e:
        logger.error(f"AI error: {str(e)}")
        return "Извините, не могу обработать запрос. Попробуйте позже."


# New routes for web chat interface
@app.route('/')
def chat_interface():
    return render_template('chat.html')


@app.route('/start_chat', methods=['POST'])
def start_chat():
    session_id = str(uuid.uuid4())
    user_states[session_id] = UserState()
    chat_histories[session_id] = []
    return jsonify({"session_id": session_id, "message": greeting_text})


@app.route('/send_message', methods=['POST'])
def send_message():
    data = request.json
    session_id = data.get('session_id')
    user_input = data.get('message').strip()

    if not session_id or session_id not in user_states:
        return jsonify({"error": "Invalid session"}), 400

    cleanup_expired_sessions()

    user_state = user_states[session_id]
    user_state.last_active = datetime.now()
    chat_history = chat_histories[session_id]

    # Add user message to history
    chat_history.append({"role": "user", "content": user_input})

    if user_state.reset_context:
        if chat_history and chat_history[-1]["role"] == "assistant":
            chat_history = [chat_history[-1]]
            chat_histories[session_id] = chat_history
        user_state.reset_context = False

    # Trim history if needed
    if user_state.order_confirmed and not user_state.context_cut:
        if len(chat_history) > 2:
            chat_history = chat_history[-2:]
            chat_histories[session_id] = chat_history
        user_state.context_cut = True
    elif len(chat_history) > MAX_CONTEXT and not user_state.context_cut:
        chat_history.pop(0)

    # Route to appropriate handler
    if user_state.phase == "init":
        response = handle_product_inquiry(user_input, user_state, session_id)
    elif user_state.phase == "product_info":
        response = handle_product_info_response(user_input, user_state, session_id)
    elif user_state.phase == "delivery_selection":
        response = handle_delivery_selection(user_input, user_state)
    elif user_state.phase == "office_closed":
        response = handle_office_closed(user_input, user_state)
    elif user_state.phase == "order_form":
        response = handle_order_form_step(user_input, user_state, session_id)
    elif user_state.phase == "complete":
        response = handle_complete_phase(user_input, user_state, session_id)
    else:
        response = "Произошла ошибка. Пожалуйста, попробуйте позже."

    # Add assistant response to history
    if isinstance(response, str):
        chat_history.append({"role": "assistant", "content": response})
        assistant_reply = response
    elif isinstance(response, dict) and "reply" in response:
        chat_history.append({"role": "assistant", "content": response["reply"]})
        assistant_reply = response["reply"]

    # Handle context reset flag
    if user_state.reset_context:
        if chat_history and chat_history[-1]["role"] == "assistant":
            chat_histories[session_id] = [chat_history[-1]]
        user_state.reset_context = False

    return jsonify({"message": assistant_reply})


def handle_complete_phase(user_input, user_state, session_id):
    if any(word in user_input.lower() for word in ["новый", "еще", "другой", "ещё"]):
        user_state.phase = "init"
        user_state.order_confirmed = False
        user_state.context_cut = False
        user_state.current_order_step = None
        user_state.order_data = {
            "ФИО": "",
            "Контакт": "",
            "Модель": "",
            "Объём": "",
            "Цвет": "",
            "Зарядный блок": "Нет"
        }
        return "Хорошо, давайте оформим новый заказ. Какой iPhone вас интересует?"
    else:
        user_state.phase = "init"
        return handle_product_inquiry(user_input, user_state, session_id)


def handle_product_inquiry(user_input, user_state, session_id):
    if any(word in user_input.lower() for word in ["заказать", "оформить", "купить", "хочу iphone"]):
        user_state.phase = "delivery_selection"
        return delivery_options_text

    products = get_available_products()
    prev_messages = chat_histories.get(session_id, [])

    is_follow_up = any(
        msg['content'].lower() in user_input.lower()
        for msg in prev_messages[-2:]
        if msg['role'] == 'assistant'
    )

    prompt = f"""
    Пользователь спрашивает: {user_input}
    Доступные товары: {json.dumps(products, ensure_ascii=False)[:1000]}...
    Предыдущий диалог: {json.dumps(prev_messages[-2:], ensure_ascii=False) if prev_messages else 'Нет'}

    Ответь как живой консультант магазина:
    1. Веди себя реалистично как человек
    2. Добавляй эмодзи где уместно
    3. Допускай неформальные сокращения
    4. Сохраняй легкую эмоциональную окраску
    5. Добавляй персонализированные комментарии
    6. Держи ответ в 1-2 предложения
    7. Никогда не упоминай что ты ИИ
    8. Не отсылайся на другие источники
    9. Твоя цель продать айфон
    10. Не предлагай дополнительные аксессуары
    """

    ai_response = generate_llama_response(prompt)

    if (not is_follow_up and
            not any(word in user_input.lower() for word in ["нет", "не надо"]) and
            any(model.lower() in user_input.lower() for model in ["iphone", "айфон"])):
        user_state.phase = "product_info"
        user_state.asked_for_details = True
        return f"{ai_response}\n\nХотите получить полную информацию по конкретной модели?"
    else:
        user_state.phase = "init"
        return ai_response


def handle_product_info_response(user_input, user_state, session_id):
    if any(word in user_input.lower() for word in ["нет", "не надо"]):
        user_state.phase = "init"
        user_state.asked_for_details = False
        return "Хорошо, чем еще могу помочь?"

    model_query = extract_models_from_input(user_input)
    if model_query:
        model_query = model_query[0]
    else:
        model_query = re.sub(
            r'\b(да|про|информация|подробнее|хочу|модель)\b',
            '',
            user_input,
            flags=re.IGNORECASE
        ).strip()

    products = get_available_products()

    prompt = f"""
    Пользователь хочет подробности о: {model_query}
    Доступные товары: {json.dumps(products, ensure_ascii=False)[:1000]}...

    Ответь как эксперт-продажник:
    1. Начни с позитивного отклика
    2. Используй сравнения
    3. Добавь личное мнение
    4. Заверши мягким призывом к действию
    5. Сохраняй естественную пунктуацию
    6. Максимум 3 предложения
    7. Не предлагай дополнительные аксессуары
    """

    ai_response = generate_llama_response(prompt)

    if "Хотите оформить заказ" not in ai_response and not user_state.asked_for_details:
        ai_response += "\n\nХотите оформить заказ на эту модель?"
        user_state.asked_for_details = True

    user_state.phase = "delivery_selection"
    return ai_response


def handle_delivery_selection(user_input, user_state):
    if "нет" in user_input.lower():
        user_state.phase = "init"
        return "Хорошо, чем еще могу помочь?"

    delivery = match_delivery_option(user_input)
    if not delivery:
        return f"Пожалуйста, выберите способ доставки:\n{delivery_options_text}"

    user_state.delivery_method = delivery

    if delivery == "Самовывоз":
        office_status = get_office_status()
        if office_status.lower() in ["закрыт", "closed"]:
            user_state.phase = "office_closed"
            return office_closed_text

    user_state.phase = "order_form"
    user_state.current_order_step = "full_name"
    return "Пожалуйста, укажите ваше полное имя (Фамилия Имя Отчество):"


def handle_office_closed(user_input, user_state):
    if "да" in user_input.lower():
        user_state.phase = "order_form"
        user_state.delivery_method = "Курьерская доставка"
        user_state.current_order_step = "full_name"
        return "Пожалуйста, укажите ваше полное имя (Фамилия Имя Отчество):"
    else:
        user_state.phase = "complete"
        return "Хорошо, тогда обращайтесь, когда офис будет открыт."


def handle_order_form_step(user_input, user_state, session_id):
    products = get_available_products()

    if user_state.current_order_step == "full_name":
        name_parts = user_input.split()
        if len(name_parts) < 2:
            return "Пожалуйста, укажите ваше полное имя (минимум Фамилия и Имя):"

        formatted_name = " ".join([part.capitalize() for part in name_parts])
        user_state.order_data["ФИО"] = formatted_name
        user_state.current_order_step = "contact"
        return "Укажите ваш телефон (в формате +79991234567) или Telegram username (в формате @username):"

    elif user_state.current_order_step == "contact":
        phone_match = re.match(r'^(\+7|7|8)?(\d{10})$', user_input)
        telegram_match = re.match(r'^@?[a-zA-Z0-9_]{5,32}$', user_input)

        if phone_match:
            phone = "+7" + phone_match.group(2)
            user_state.order_data["Контакт"] = phone
        elif telegram_match:
            telegram = telegram_match.group(0)
            if not telegram.startswith("@"):
                telegram = "@" + telegram
            user_state.order_data["Контакт"] = telegram
        else:
            return "Пожалуйста, укажите корректный телефон (+79991234567) или Telegram (@username):"

        user_state.current_order_step = "model"
        return "Укажите модель iPhone, которую вы хотите заказать:"

    elif user_state.current_order_step == "model":
        model_input = user_input.strip()
        all_products = get_available_products()

        normalized_input = normalize_model_name(model_input)
        best_match = None
        best_score = 0

        for product in all_products:
            product_norm = normalize_model_name(product.get('Модель', ''))
            similarity = jellyfish.jaro_similarity(normalized_input, product_norm)

            if similarity > best_score:
                best_score = similarity
                best_match = product.get('Модель', '')

        if not best_match or best_score < 0.8:
            best_match = model_input

        matched_products = find_matching_products(all_products, model=best_match)

        if not matched_products:
            model_exists = any(
                normalize_model_name(p.get('Модель', '')) == normalize_model_name(best_match)
                for p in all_products
            )

            if model_exists:
                user_state.current_order_step = "out_of_stock"
                return f"⚠️ Модель '{best_match}' отсутствует в наличии. Хотите оформить заказ на другой телефон? (Да/Нет)"
            else:
                all_models = get_available_models(all_products)
                similar_models = find_similar_models(model_input, all_models)

                if similar_models:
                    suggestions = "\n".join([f"- {model}" for model in similar_models])
                    return f"Модель '{model_input}' не найдена. Возможно вы имели в виду:\n{suggestions}\nПожалуйста, укажите точное название модели."
                else:
                    return f"Модель не найдена. Доступные модели: {', '.join(all_models)}"

        user_state.order_data["Модель"] = matched_products[0].get('Модель', '')
        user_state.current_order_step = "model_confirmation"
        return f"Вы имели в виду {matched_products[0].get('Модель', '')}? (Да/Нет)"

    elif user_state.current_order_step == "model_confirmation":
        if user_input.lower() in ["да", "yes", "д"]:
            user_state.current_order_step = "storage"
            storages = get_available_storages(products, user_state.order_data["Модель"])
            return f"✅ Выбрана модель: {user_state.order_data['Модель']}. Выберите объём памяти: {', '.join(storages)}"
        elif user_input.lower() in ["нет", "no", "н"]:
            user_state.order_data["Модель"] = ""
            user_state.current_order_step = "model"
            return "Хорошо, пожалуйста, укажите точное название модели:"
        else:
            return "Пожалуйста, ответьте Да или Нет для подтверждения модели:"

    elif user_state.current_order_step == "out_of_stock":
        if user_input.lower() in ["да", "yes", "д"]:
            user_state.order_data["Модель"] = ""
            user_state.order_data["Объём"] = ""
            user_state.order_data["Цвет"] = ""
            user_state.order_data["Зарядный блок"] = "Нет"
            user_state.current_order_step = "model"
            return "Укажите модель iPhone, которую вы хотите заказать:"
        elif user_input.lower() in ["нет", "no", "н"]:
            user_state.phase = "init"
            user_state.order_data = {
                "ФИО": "",
                "Контакт": "",
                "Модель": "",
                "Объём": "",
                "Цвет": "",
                "Зарядный блок": "Нет"
            }
            return "Заказ отменён. Чем ещё могу помочь?"
        else:
            return "Пожалуйста, ответьте Да или Нет:"

    elif user_state.current_order_step == "storage":
        storage_input = normalize_storage(user_input)
        model = user_state.order_data["Модель"]
        available_storages = get_available_storages(products, model)

        if storage_input in available_storages:
            user_state.order_data["Объём"] = storage_input
            user_state.current_order_step = "color"
            colors = get_available_colors(products, model, storage_input)
            return f"📦 Выбран объём: {storage_input}. Выберите цвет: {', '.join(colors)}"
        else:
            try:
                input_num = int(re.sub(r'\D', '', storage_input))
                available_nums = [int(re.sub(r'\D', '', s)) for s in available_storages if s]
                if available_nums:
                    nearest = min(available_nums, key=lambda x: abs(x - input_num))
                    nearest_storage = f"{nearest} ГБ"
                    return f"Объём недоступен. Ближайший доступный: {nearest_storage}. Выбрать его? (Да/Нет)"
            except:
                return f"Объём недоступен. Выберите: {', '.join(available_storages)}"

    elif user_state.current_order_step == "color":
        color_input = normalize_color(user_input)
        model = user_state.order_data["Модель"]
        storage = user_state.order_data["Объём"]
        available_colors = get_available_colors(products, model, storage)

        for color in available_colors:
            if normalize_color(color) == color_input:
                user_state.order_data["Цвет"] = color
                user_state.current_order_step = "charger"
                return f"🎨 Выбран цвет: {color}. Нужен зарядный блок (20W, 2500₽)? Ответьте Да или Нет:"

        return f"Цвет недоступен. Выберите: {', '.join(available_colors)}"

    elif user_state.current_order_step == "charger":
        if user_input.lower() in ["да", "yes", "д"]:
            user_state.order_data["Зарядный блок"] = "Да"
        elif user_input.lower() in ["нет", "no", "н"]:
            user_state.order_data["Зарядный блок"] = "Нет"
        else:
            return "Пожалуйста, ответьте Да или Нет на вопрос о зарядном блоке:"

        user_state.order_data["Доставка"] = user_state.delivery_method
        user_state.current_order_step = "confirmation"
        order_summary = format_order_summary(user_state.order_data)
        return f"{order_summary}\n\nВсё верно? Подтвердите заказ (Да/Нет):"

    elif user_state.current_order_step == "confirmation":
        if user_input.lower() in ["да", "yes", "д"]:
            if submit_order(user_state.order_data):
                user_state.phase = "complete"
                user_state.order_confirmed = True
                user_state.reset_context = True
                return {
                    "reply": "✅ Заказ оформлен! Мы свяжемся с вами для уточнения деталей. Хотите оформить еще один заказ?",
                    "order_complete": True
                }
            return "Ошибка при обработке заказа. Пожалуйста, попробуйте позже."
        elif user_input.lower() in ["нет", "no", "н"]:
            user_state.phase = "init"
            return "Хорошо, заказ отменён. Хотите выбрать другую модель или уточнить детали?"
        else:
            return "Пожалуйста, ответьте Да или Нет для подтверждения заказа:"

    return "Произошла ошибка. Пожалуйста, попробуйте позже."


if __name__ == '__main__':
    app.run(host='0.0.0.0', port=10000, debug=True)
