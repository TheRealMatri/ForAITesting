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
import time

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
ORDER_SHEET_URL = os.getenv("ORDER_SHEET_URL")
SERVICE_ACCOUNT_JSON = os.getenv("SERVICE_ACCOUNT_JSON")

# Setup Flask app
app = Flask(__name__)
CORS(app, resources={r"/*": {"origins": "https://sitetest-76es.onrender.com "}})

# Google Sheets Setup
scopes = ['https://www.googleapis.com/auth/spreadsheets ']
service_account_info = None
gc = None
product_sheet = None
order_sheet = None

def initialize_google_sheets():
    global service_account_info, gc, product_sheet, order_sheet
    try:
        # Parse service account JSON from environment variable
        service_account_info = json.loads(SERVICE_ACCOUNT_JSON)
        credentials = Credentials.from_service_account_info(
            service_account_info,
            scopes=scopes
        )
        gc = gspread.authorize(credentials)
        
        # Initialize sheets with retry logic
        max_retries = 3
        for attempt in range(max_retries):
            try:
                # Open by URL with error handling
                product_sheet = gc.open_by_url(PRODUCT_SHEET_URL).sheet1
                order_sheet = gc.open_by_url(ORDER_SHEET_URL).sheet1
                logger.info("Successfully connected to Google Sheets")
                return True
            except gspread.exceptions.APIError as e:
                logger.warning(f"Google Sheets API error (attempt {attempt+1}): {str(e)}")
                if "RESOURCE_EXHAUSTED" in str(e):
                    wait_time = 2 ** attempt  # Exponential backoff
                    logger.info(f"Waiting {wait_time} seconds before retry...")
                    time.sleep(wait_time)
                else:
                    raise
        logger.error("Google Sheets connection failed after multiple retries")
        return False
    except Exception as e:
        logger.error(f"Google Sheets connection failed: {str(e)}")
        return False

# Initialize Google Sheets connection
if not initialize_google_sheets():
    exit(1)

# Product caching with automatic refresh
PRODUCT_CACHE = None
PRODUCT_CACHE_TIME = None
CACHE_DURATION = 300  # 5 minutes

# Static Texts
def load_txt(filename):
    try:
        with open(filename, 'r', encoding='utf-8') as f:
            return f.read().strip()
    except FileNotFoundError:
        logger.warning(f"File {filename} not found, using default text")
        return ""

# Load multiple details files
greeting_text = load_txt('greeting.txt') or "Привет! Я ваш помощник по iPhone. Чем могу помочь?"
details_texts = [
    load_txt('details1.txt') or "У нас есть широкий выбор iPhone по отличным ценам!",
    load_txt('details2.txt') or "Все устройства проходят тщательную проверку перед продажей.",
    load_txt('details3.txt') or "Мы предлагаем гарантию на все устройства и бесплатную доставку."
]

delivery_options_text = load_txt('delivery_options.txt') or (
    "Выберите способ доставки:\n"
    "1. Самовывоз\n"
    "2. Курьерская доставка"
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
        self.reset_context = False
        self.current_order_step = None
        self.greeted = False
        self.order_intent_detected = False
        self.initial_messages_sent = False  # Track if initial messages have been sent

user_states = {}
chat_histories = {}
MAX_CONTEXT = 20
SESSION_TIMEOUT = timedelta(minutes=45)

MODEL_PATTERNS = {
    'pro': ['pro', 'про', 'рго', 'прo', 'пpo'],
    'max': ['max', 'макс', 'маx', 'мaкс', 'мax'],
    'mini': ['mini', 'мини', 'минь', 'миni', 'мин'],
    'plus': ['plus', 'плюс', 'плс', 'pls', 'плю'],
    'standard': ['', 'стандарт', 'обычный', 'базовый']
}

MODEL_NUMBER_PATTERN = r'(?<!\d)(1[1-6]|\d{1,2})(?!\d)'
last_request_time = 0
AI_REQUEST_INTERVAL = 1  # 1 request per second
request_lock = False

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
    
    model_number_match = re.search(MODEL_NUMBER_PATTERN, model)
    model_number = model_number_match.group(0) if model_number_match else ""
    
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
        storage = storage.lower()
        # Handle TB conversions
        if 'tb' in storage or 'тб' in storage:
            storage_num = re.sub(r'[^0-9]', '', storage)
            if storage_num == "1024" or storage_num == "1":
                return "1TB"
            return f"{storage_num}TB"
        storage_num = re.sub(r'[^0-9]', '', storage)
        if storage_num == "1024":
            return "1TB"
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
        'титан': 'титан',
        'натуральный титан': 'титан',
        'голубой титан': 'голубой титан',
        'белый титан': 'белый титан',
        'чёрный титан': 'чёрный титан',
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
    global PRODUCT_CACHE, PRODUCT_CACHE_TIME
    # Return cached data if recent
    now = datetime.now()
    if (PRODUCT_CACHE and PRODUCT_CACHE_TIME and 
        (now - PRODUCT_CACHE_TIME).seconds < CACHE_DURATION):
        return PRODUCT_CACHE
    
    try:
        products = product_sheet.get_all_records()
        # Convert 1024 GB to 1TB and handle other storage formats
        for product in products:
            storage = product.get('Объём', '')
            normalized = normalize_storage(storage)
            if normalized != storage:
                product['Объём'] = normalized
        PRODUCT_CACHE = products
        PRODUCT_CACHE_TIME = now
        logger.info(f"Loaded {len(products)} products from Google Sheets")
        if products:
            logger.info(f"Sample product: {products[0]}")
        return products
    except Exception as e:
        logger.error(f"Product fetch error: {str(e)}")
        # Try to reinitialize connection
        if "RESOURCE_EXHAUSTED" in str(e) or "UNAUTHENTICATED" in str(e):
            logger.warning("Reinitializing Google Sheets connection")
            initialize_google_sheets()
        return PRODUCT_CACHE or []  # Return stale cache if available

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
    summary = "📝 <b>Ваш заказ:</b>\n"
    summary += f"• <b>Модель:</b> {order_data['Модель']}\n"
    summary += f"• <b>Объём:</b> {order_data['Объём']}\n"
    summary += f"• <b>Цвет:</b> {order_data['Цвет']}\n"
    summary += f"• <b>Зарядный блок:</b> {order_data['Зарядный блок']}\n"
    summary += f"• <b>Доставка:</b> {order_data['Доставка']}\n"
    summary += f"• <b>ФИО:</b> {order_data['ФИО']}\n"
    summary += f"• <b>Контакт:</b> {order_data['Контакт']}"
    return summary

def extract_models_from_input(user_input):
    models = []
    patterns = [
        r'\b(?:iphone|айфон|phone)\s*(\d{1,2})\s*(pro\s*max|pro|plus|mini|max)?\b',
        r'\b(\d{1,2})\s*(pro\s*max|pro|plus|mini|max|мини|мин|мии|про|плюс)\b',
        r'\b(?:iphone|айфон)\s*(\d{1,2})\b',
        r'\b(?:айфон|айфона|айфоном)\s*(\d{1,2})\s*(про|макс|мини|плюс)?\b',
        r'\b(?:iphone|айфон)(\d{1,2})\s*(pro\s*max|pro|plus|mini|max)?\b'
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
        # Try to reinitialize connection
        if "RESOURCE_EXHAUSTED" in str(e) or "UNAUTHENTICATED" in str(e):
            logger.warning("Reinitializing Google Sheets connection")
            initialize_google_sheets()
        return False

def clean_ai_response(text):
    """Remove internal thinking tags and prefixes from AI responses"""
    # Remove </think> tags and content
    text = re.sub(r'</think>', '', text, flags=re.DOTALL)
    # Remove internal thinking prefixes
    prefixes = [
        "Хм,", "Хорошо,", "Итак,", "Окей,", "Ладно,",
        "Хм ", "Хорошо ", "Итак ", "Окей ", "Ладно ",
        "Похоже", "Наверное", "Стоит", "Надо"
    ]
    for prefix in prefixes:
        if text.startswith(prefix):
            text = text[len(prefix):].strip()
    # Remove any remaining prefix-like patterns
    text = re.sub(r'^(Хм,?|Хорошо,?|Итак,?|Окей,?|Ладно,?)\s*', '', text, flags=re.IGNORECASE)
    return text.strip()

def rate_limited_request():
    """Ensure minimum interval between AI requests"""
    global last_request_time, request_lock
    
    while request_lock:
        time.sleep(0.1)
    
    request_lock = True
    current_time = time.time()
    elapsed = current_time - last_request_time
    
    if elapsed < AI_REQUEST_INTERVAL:
        time.sleep(AI_REQUEST_INTERVAL - elapsed)
        
    last_request_time = time.time()
    request_lock = False

def generate_llama_response(prompt):
    rate_limited_request()
    
    url = "https://api.together.xyz/v1/chat/completions "
    headers = {
        "Authorization": f"Bearer {TOGETHER_API_KEY}",
        "Content-Type": "application/json"
    }
    
    payload = {
        "model": "deepseek-ai/DeepSeek-R1-Distill-Llama-70B-free",
        "messages": [
            {
                "role": "system",
                "content": (
                    "Вы - консультант магазина WAY PHONE, который продает технику Apple. "
                    "Техника Apple как новая, но не новая! Отвечайте кратко и точно на русском. "
                    "Только готовым ответом для клиента без внутренних размышлений! "
                    "Если клиент использует ненормативную лексику, вы имеете право использовать матерные слова в ответ."
                )
            },
            {"role": "user", "content": prompt}
        ],
        "temperature": 0.4,
        "max_tokens": 300
    }
    
    max_retries = 3
    retry_delay = 2  # seconds
    
    for attempt in range(max_retries):
        try:
            logger.info(f"Sending request to AI model (attempt {attempt+1})")
            response = requests.post(url, headers=headers, json=payload, timeout=30)
            response.raise_for_status()
            content = response.json()["choices"][0]["message"]["content"].strip()
            logger.info(f"Raw AI response: {content}")
            # Clean response from internal thoughts
            cleaned_content = clean_ai_response(content)
            logger.info(f"Cleaned AI response: {cleaned_content}")
            return cleaned_content
        except requests.exceptions.HTTPError as e:
            if response.status_code == 429:  # Rate limit
                logger.warning(f"Rate limit exceeded. Retrying in {retry_delay} seconds...")
                time.sleep(retry_delay)
                retry_delay *= 2  # Exponential backoff
            else:
                logger.error(f"HTTP error: {str(e)}")
                return "Извините, временные технические трудности. Попробуйте позже."
        except Exception as e:
            logger.error(f"AI error: {str(e)}")
            if attempt < max_retries - 1:
                time.sleep(retry_delay)
                retry_delay *= 2
            else:
                return "Извините, не могу обработать запрос. Попробуйте позже."
                
    return "Извините, сервис временно недоступен. Попробуйте через несколько минут."

def classify_order_intent(user_input, context):
    """Use NLP to determine if user wants to start an order"""
    # First check for explicit order keywords
    order_keywords = [
        "хочу купить", "хочу заказать", "закажите", "оформить заказ",
        "куплю", "заказ", "заказать", "оформить", "доставка", "оплата",
        "купить", "приобрести", "хочу приобрести", "заказал"
    ]
    
    if any(keyword in user_input.lower() for keyword in order_keywords):
        return True
        
    # Then use AI for context-aware classification
    prompt = f"""
    [КОНТЕКСТ]: {context}
    [СООБЩЕНИЕ]: {user_input}
    Определи намерение одним словом (Заказ или Вопрос):
    - Заказ: если хочет купить/заказать
    - Вопрос: если спрашивает информацию
    """
    
    response = generate_llama_response(prompt)
    return "заказ" in response.lower()

def build_context_history(chat_history, max_messages=4):
    """Build context string from chat history"""
    context_parts = []
    count = 0
    for msg in reversed(chat_history):
        if msg["role"] == "user":
            context_parts.insert(0, f"Клиент: {msg['content']}")
            count += 1
        elif msg["role"] == "assistant":
            context_parts.insert(0, f"Консультант: {msg['content']}")
            count += 1
        if count >= max_messages:
            break
    return "\n".join(context_parts)

# New routes for web chat interface
@app.route('/')
def chat_interface():
    return render_template('chat.html')

@app.route('/start_chat', methods=['POST'])
def start_chat():
    session_id = str(uuid.uuid4())
    user_states[session_id] = UserState()
    chat_histories[session_id] = []
    # Preload products to warm up cache
    get_available_products()
    return jsonify({
        "session_id": session_id
    })

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
        
    # Check if we need to send initial messages
    if not user_state.initial_messages_sent:
        user_state.initial_messages_sent = True
        initial_messages = [greeting_text] + details_texts
        
        # Add initial messages to chat history
        for msg in initial_messages:
            chat_history.append({"role": "assistant", "content": msg})
            
        # Return initial messages without processing user input
        return jsonify({"messages": initial_messages})
        
    # Route to appropriate handler
    if user_state.phase == "init":
        response = handle_product_inquiry(user_input, user_state, session_id)
    elif user_state.phase == "order_confirmation":
        response = handle_order_confirmation(user_input, user_state)
    elif user_state.phase == "product_info":
        response = handle_product_info_response(user_input, user_state, session_id)
    elif user_state.phase == "delivery_selection":
        response = handle_delivery_selection(user_input, user_state)
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
    user_state.greeted = True
    
    # Get conversation context
    chat_history = chat_histories.get(session_id, [])
    context = build_context_history(chat_history)
    
    # Advanced NLP intent recognition
    wants_to_order = classify_order_intent(user_input, context)
    
    # Check for explicit order requests
    if (wants_to_order or 
        any(word in user_input.lower() for word in ["хочу купить", "хочу заказать"])):
        user_state.order_intent_detected = True
        
        # Extract mentioned model from context
        mentioned_models = extract_models_from_input(context + " " + user_input)
        
        if mentioned_models:
            model = mentioned_models[0]
            user_state.order_data["Модель"] = model
            user_state.phase = "order_confirmation"
            return f"Вы хотите заказать {model}? (Да/Нет)"
        else:
            user_state.phase = "order_confirmation"
            return "Отлично! Какую модель iPhone вы хотели бы заказать?"
            
    products = get_available_products()
    available_models = get_available_models(products)
    
    # Create a concise list of available models for the prompt
    models_list = ", ".join(available_models[:5])  # Show first 5 models
    
    if len(available_models) > 5:
        models_list += f" и ещё {len(available_models)-5} моделей"
        
    # Build context-aware prompt
    prompt = f"""
    [КОНТЕКСТ РАЗГОВОРА]
    {context}
    [ИНСТРУКЦИИ]
    Ты консультант магазина. Отвечай только готовым ответом для клиента без внутренних размышлений.
    Отвечай на русском. Только готовым ответом для клиента без внутренних размышлений!
    - Отвечай кратко (1-3 предложения)
    - Используй дружелюбный тон с эмодзи иногда
    - Не упоминай, что ты ИИ
    - Опирайся только на доступные модели: {models_list}
    [ЗАПРОС]
    Клиент спрашивает: {user_input}
    """
    
    ai_response = generate_llama_response(prompt)
    
    # Check if we should ask about details
    if (not user_state.greeted and
            not any(word in user_input.lower() for word in ["нет", "не надо"]) and
            any(model.lower() in user_input.lower() for model in ["iphone", "айфон"])):
        user_state.phase = "product_info"
        user_state.asked_for_details = True
        return f"{ai_response}\nХотите получить полную информацию по конкретной модели?"
    else:
        user_state.phase = "init"
        return ai_response

def handle_order_confirmation(user_input, user_state):
    if user_input.lower() in ["да", "yes", "д"]:
        user_state.phase = "delivery_selection"
        return delivery_options_text
    elif user_input.lower() in ["нет", "no", "н"]:
        user_state.phase = "init"
        user_state.order_intent_detected = False
        return "Хорошо, чем еще могу помочь?"
    else:
        return "Пожалуйста, ответьте Да или Нет:"

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
    available_models = get_available_models(products)
    
    # Build context
    chat_history = chat_histories.get(session_id, [])
    context = build_context_history(chat_history)
    
    # Create a concise list of available models for the prompt
    models_list = ", ".join(available_models[:5])  # Show first 5 models
    
    if len(available_models) > 5:
        models_list += f" и ещё {len(available_models)-5} моделей"
        
    prompt = f"""
    [КОНТЕКСТ РАЗГОВОРА]
    {context}
    [ИНСТРУКЦИИ]
    Отвечай на русском. Только готовым ответом для клиента без внутренних размышлений!
    Ты эксперт по iPhone. Предоставь краткую информацию о модели без внутренних размышлений.
    - Отвечай 1-3 предложениями
    - Добавь позитивный отзыв о модели
    - Предложи оформить заказ в конце
    - Доступные модели: {models_list}
    [ЗАПРОС]
    Клиент спрашивает про: {model_query}
    """
    
    ai_response = generate_llama_response(prompt)
    
    # Add order prompt if not already present
    if "Хотите оформить заказ" not in ai_response:
        ai_response += "\nХотите оформить заказ на эту модель?"
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
    
    # Always proceed to order form since we removed office status
    user_state.phase = "order_form"
    user_state.current_order_step = "full_name"
    return "Пожалуйста, укажите ваше полное имя (Фамилия Имя Отчество):"

def handle_order_form_step(user_input, user_state, session_id):
    products = get_available_products()
    
    if user_state.current_order_step == "full_name":
        name_parts = user_input.split()
        
        if len(name_parts) < 2:
            return "Пожалуйста, укажите ваше полное имя (минимум Фамилия и Имя):"
            
        formatted_name = " ".join([part.capitalize() for part in name_parts])
        user_state.order_data["ФИО"] = formatted_name
        user_state.current_order_step = "contact"
        return "Укажите ваш телефон (в формате +7XXXXXXXXXX) или Telegram username (в формате @username):"
        
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
            return "Пожалуйста, укажите корректный телефон (+7XXXXXXXXXX) или Telegram (@username):"
            
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
        return f"{order_summary}\nВсё верно? Подтвердите заказ (Да/Нет):"
        
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
