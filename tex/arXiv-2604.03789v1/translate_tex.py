import re
import time
from deep_translator import GoogleTranslator

def translate_text(text):
    if not text.strip():
        return text
    try:
        # Split by newlines, translate each paragraph to preserve structure
        translator = GoogleTranslator(source='en', target='zh-CN')
        return translator.translate(text)
    except Exception as e:
        print(f"Error translating: {e}")
        return text

def main():
    file_path = r'c:\Users\Admin\Desktop\lean4-learning\tex\arXiv-2604.03789v1\blog.tex'
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Translate title
    title_match = re.search(r'\\title\{(.*?)\}', content, re.DOTALL)
    if title_match:
        translated_title = translate_text(title_match.group(1))
        content = content.replace(title_match.group(1), translated_title)

    # Translate abstract
    abstract_match = re.search(r'\\abstract\{(.*?)\n\}', content, re.DOTALL)
    if abstract_match:
        translated_abstract = translate_text(abstract_match.group(1))
        content = content.replace(abstract_match.group(1), translated_abstract)

    # Write back
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(content)
        
    print("Successfully translated title and abstract.")

if __name__ == '__main__':
    main()
