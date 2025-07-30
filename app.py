from flask import Flask, render_template, request, jsonify, send_file
import requests
from bs4 import BeautifulSoup
from urllib.parse import urljoin, urlparse, urldefrag
import threading
import time
from concurrent.futures import ThreadPoolExecutor
import json
import csv
import io
import tempfile
from datetime import datetime
from collections import defaultdict, Counter
from urllib.robotparser import RobotFileParser

# Selenium imports (optional)
try:
    from selenium import webdriver
    from selenium.webdriver.chrome.service import Service
    from selenium.webdriver.chrome.options import Options
    from selenium.webdriver.common.by import By
    from selenium.webdriver.support.ui import WebDriverWait
    from selenium.webdriver.support import expected_conditions as EC
    from webdriver_manager.chrome import ChromeDriverManager
    SELENIUM_AVAILABLE = True
except ImportError:
    SELENIUM_AVAILABLE = False
    print("Selenium not available. Using requests-only mode.")

app = Flask(__name__)

class WebsiteAnalyzer:
    def __init__(self, base_url, max_pages=100, max_depth=3, selenium_threshold=5):
        self.base_url = self._clean_url(base_url)
        self.domain = urlparse(self.base_url).netloc
        self.visited_urls = set()
        self.urls_to_visit = [(self.base_url, 0)]
        self.anchor_tags = []
        self.redirect_links = []
        self.anchor_text_analysis = defaultdict(list)  # URL -> list of anchor texts
        self.max_pages = max_pages
        self.max_depth = max_depth
        self.crawl_complete = False
        self.session = requests.Session()
        self.selenium_driver = None
        self.selenium_threshold = selenium_threshold
        self.crawl_start_time = None
        self.crawl_end_time = None
        self._setup_session()
        
    def _clean_url(self, url):
        """Clean and normalize URL"""
        if not url.startswith(('http://', 'https://')):
            url = 'https://' + url
        return urldefrag(url)[0]
    
    def _setup_session(self):
        """Configure requests session"""
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Accept-Language': 'en-US,en;q=0.5',
            'Connection': 'keep-alive',
        })
        
        from requests.adapters import HTTPAdapter
        from urllib3.util.retry import Retry
        
        retry_strategy = Retry(total=3, backoff_factor=1, status_forcelist=[429, 500, 502, 503, 504])
        adapter = HTTPAdapter(max_retries=retry_strategy)
        self.session.mount("http://", adapter)
        self.session.mount("https://", adapter)
    
    def _setup_selenium_driver(self):
        """Setup Selenium WebDriver"""
        if not SELENIUM_AVAILABLE or self.selenium_driver:
            return self.selenium_driver
            
        try:
            chrome_options = Options()
            chrome_options.add_argument('--headless')
            chrome_options.add_argument('--no-sandbox')
            chrome_options.add_argument('--disable-dev-shm-usage')
            chrome_options.add_argument('--disable-gpu')
            chrome_options.add_argument('--disable-images')
            
            service = Service(ChromeDriverManager().install())
            self.selenium_driver = webdriver.Chrome(service=service, options=chrome_options)
            self.selenium_driver.set_page_load_timeout(30)
            return self.selenium_driver
        except Exception as e:
            print(f"Selenium setup failed: {e}")
            return None
    
    def _cleanup_selenium(self):
        """Clean up Selenium resources"""
        if self.selenium_driver:
            try:
                self.selenium_driver.quit()
                self.selenium_driver = None
            except:
                pass
    
    def check_redirect_chain(self, url):
        """Check if URL redirects and return final destination"""
        try:
            response = self.session.head(url, allow_redirects=True, timeout=10)
            redirect_count = len(response.history)
            
            if redirect_count > 0:
                return {
                    'is_redirect': True,
                    'original_url': url,
                    'final_url': response.url,
                    'redirect_count': redirect_count,
                    'status_codes': [r.status_code for r in response.history] + [response.status_code],
                    'redirect_chain': [r.url for r in response.history] + [response.url]
                }
            else:
                return {
                    'is_redirect': False,
                    'original_url': url,
                    'final_url': url,
                    'redirect_count': 0,
                    'status_codes': [response.status_code],
                    'redirect_chain': [url]
                }
        except Exception as e:
            return {
                'is_redirect': False,
                'original_url': url,
                'final_url': url,
                'redirect_count': 0,
                'status_codes': ['ERROR'],
                'redirect_chain': [url],
                'error': str(e)
            }
    
    def is_valid_internal_url(self, url):
        """Check if URL is internal and valid"""
        try:
            parsed = urlparse(url)
            if parsed.netloc != self.domain:
                return False
            skip_extensions = {'.jpg', '.jpeg', '.png', '.gif', '.pdf', '.zip', 
                             '.css', '.js', '.ico', '.svg', '.woff', '.woff2'}
            if any(parsed.path.lower().endswith(ext) for ext in skip_extensions):
                return False
            return True
        except:
            return False
    
    def extract_anchor_data(self, html_content, page_url, depth=0, method="requests"):
        """Extract anchor tags and analyze them"""
        soup = BeautifulSoup(html_content, 'lxml')
        
        # Remove script and style content
        for script in soup(["script", "style"]):
            script.decompose()
        
        links = soup.find_all('a', href=True)
        page_anchors = []
        
        for index, link in enumerate(links):
            href = link.get('href', '').strip()
            if not href or href.startswith(('javascript:', 'tel:')):
                continue
            
            # Get anchor text
            anchor_text = self._extract_anchor_text(link)
            absolute_url = urljoin(page_url, href)
            
            # Determine if it's internal
            is_internal = self.is_valid_internal_url(absolute_url)
            
            # Check for redirects (only for internal links)
            redirect_info = None
            if is_internal:
                redirect_info = self.check_redirect_chain(absolute_url)
            
            anchor_data = {
                'id': len(self.anchor_tags) + len(page_anchors) + 1,
                'page_url': page_url,
                'page_depth': depth,
                'original_href': href,
                'absolute_url': absolute_url,
                'anchor_text': anchor_text,
                'anchor_text_type': self._classify_anchor_text(anchor_text, link),
                'is_internal': is_internal,
                'redirect_info': redirect_info,
                'extraction_method': method,
                'anchor_index_on_page': index + 1,
                'full_tag': str(link),
                'attributes': dict(link.attrs),
                'timestamp': datetime.now().isoformat()
            }
            
            page_anchors.append(anchor_data)
            
            # Store redirect information
            if redirect_info and redirect_info['is_redirect']:
                self.redirect_links.append({
                    'page_containing_link': page_url,
                    'link_text': anchor_text,
                    'original_url': redirect_info['original_url'],
                    'final_url': redirect_info['final_url'],
                    'redirect_count': redirect_info['redirect_count'],
                    'redirect_chain': redirect_info['redirect_chain'],
                    'status_codes': redirect_info['status_codes'],
                    'full_tag': str(link),
                    'page_depth': depth,
                    'timestamp': datetime.now().isoformat()
                })
            
            # Build anchor text analysis (for internal links)
            if is_internal:
                final_url = redirect_info['final_url'] if redirect_info else absolute_url
                self.anchor_text_analysis[final_url].append({
                    'text': anchor_text,
                    'text_type': self._classify_anchor_text(anchor_text, link),
                    'source_page': page_url,
                    'is_redirect': redirect_info['is_redirect'] if redirect_info else False
                })
            
            # Add to crawl queue if internal and not visited
            if is_internal and depth < self.max_depth:
                final_url = redirect_info['final_url'] if redirect_info else absolute_url
                if final_url not in self.visited_urls and len(self.urls_to_visit) < self.max_pages:
                    self.urls_to_visit.append((final_url, depth + 1))
        
        self.anchor_tags.extend(page_anchors)
        return page_anchors
    
    def _extract_anchor_text(self, link):
        """Extract meaningful anchor text from link element"""
        # Try to get text content first
        text = link.get_text(strip=True)
        
        if text:
            return text
        
        # Check for image with alt text
        img = link.find('img')
        if img:
            alt_text = img.get('alt', '').strip()
            if alt_text:
                return f"[Image: {alt_text}]"
            else:
                return "[Image with missing alt text]"
        
        # Check if it's just a naked URL
        href = link.get('href', '')
        if href:
            # Clean up the URL for display
            clean_url = href.replace('http://', '').replace('https://', '').replace('www.', '')
            if clean_url.endswith('/'):
                clean_url = clean_url[:-1]
            return f"[Naked URL: {clean_url}]"
        
        return "[Empty link]"
    
    def _classify_anchor_text(self, text, link):
        """Classify the type of anchor text"""
        text_lower = text.lower()
        
        if text.startswith('[Image'):
            return 'image'
        elif text.startswith('[Naked URL'):
            return 'naked_url'
        elif text.startswith('[Empty'):
            return 'empty'
        elif any(word in text_lower for word in ['click here', 'read more', 'learn more', 'see more']):
            return 'generic'
        elif len(text.split()) > 8:
            return 'long_descriptive'
        elif len(text.split()) <= 2:
            return 'short'
        else:
            return 'descriptive'
    
    def should_use_selenium(self, url, response_text, initial_link_count):
        """Decide if Selenium is needed"""
        if not SELENIUM_AVAILABLE:
            return False, "Selenium not available"
        
        if initial_link_count < self.selenium_threshold:
            return True, f"Low link count ({initial_link_count})"
        
        spa_indicators = ['react', 'angular', 'vue.js', 'data-reactroot', 'ng-app']
        if any(indicator in response_text.lower() for indicator in spa_indicators):
            return True, "SPA indicators found"
        
        return False, "Standard parsing sufficient"
    
    def crawl_page(self, url, depth=0):
        """Crawl a single page"""
        try:
            response = self.session.get(url, timeout=15)
            response.raise_for_status()
            
            content_type = response.headers.get('content-type', '').lower()
            if 'text/html' not in content_type:
                return False, f"Non-HTML content: {content_type}"
            
            # Try requests first
            initial_anchors = self.extract_anchor_data(response.text, url, depth, "requests")
            initial_count = len(initial_anchors)
            
            # Check if Selenium is needed
            use_selenium, reason = self.should_use_selenium(url, response.text, initial_count)
            
            if use_selenium:
                print(f"  🔄 Using Selenium: {reason}")
                # Remove initial anchors and re-extract with Selenium
                self.anchor_tags = [a for a in self.anchor_tags if a['page_url'] != url]
                self.redirect_links = [r for r in self.redirect_links if r['page_containing_link'] != url]
                
                # Remove from anchor text analysis
                for final_url in list(self.anchor_text_analysis.keys()):
                    self.anchor_text_analysis[final_url] = [
                        item for item in self.anchor_text_analysis[final_url] 
                        if item['source_page'] != url
                    ]
                
                selenium_anchors = self.extract_anchor_data_selenium(url, depth)
                return True, f"Selenium: Found {len(selenium_anchors)} anchors"
            else:
                return True, f"Requests: Found {initial_count} anchors"
                
        except Exception as e:
            return False, f"Error: {str(e)}"
    
    def extract_anchor_data_selenium(self, url, depth=0):
        """Extract anchor data using Selenium"""
        driver = self._setup_selenium_driver()
        if not driver:
            return []
        
        try:
            driver.get(url)
            WebDriverWait(driver, 10).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
            time.sleep(3)  # Wait for dynamic content
            
            # Get page source and extract with BeautifulSoup
            page_source = driver.page_source
            return self.extract_anchor_data(page_source, url, depth, "selenium")
        except Exception as e:
            print(f"Selenium extraction error: {e}")
            return []
    
    def start_analysis(self):
        """Start the website analysis"""
        self.crawl_start_time = datetime.now()
        crawled_count = 0
        
        print(f"🚀 Starting website analysis for {self.base_url}")
        print(f"📊 Max pages: {self.max_pages}, Max depth: {self.max_depth}")
        
        with ThreadPoolExecutor(max_workers=2) as executor:
            while self.urls_to_visit and crawled_count < self.max_pages:
                if not self.urls_to_visit:
                    break
                    
                url, depth = self.urls_to_visit.pop(0)
                
                if url in self.visited_urls or depth > self.max_depth:
                    continue
                
                print(f"🔍 Analyzing (depth {depth}): {url}")
                self.visited_urls.add(url)
                
                future = executor.submit(self.crawl_page, url, depth)
                success, message = future.result()
                
                if success:
                    crawled_count += 1
                    print(f"  ✅ {message}")
                else:
                    print(f"  ❌ {message}")
                
                time.sleep(1)
        
        self._cleanup_selenium()
        self.crawl_end_time = datetime.now()
        self.crawl_complete = True
        
        print(f"\n🎉 Analysis completed!")
        print(f"📄 Pages analyzed: {len(self.visited_urls)}")
        print(f"🔗 Anchor tags found: {len(self.anchor_tags)}")
        print(f"🔄 Redirect links found: {len(self.redirect_links)}")
        print(f"📋 Unique URLs with anchor text variations: {len(self.anchor_text_analysis)}")
    
    def generate_redirect_csv(self):
        """Generate CSV report for redirect links"""
        output = io.StringIO()
        fieldnames = [
            'Page_URL', 'Link_Text', 'Original_URL', 'Final_URL', 
            'Redirect_Count', 'Status_Codes', 'Full_Redirect_Chain', 
            'Page_Depth', 'Full_Tag', 'Timestamp'
        ]
        
        writer = csv.DictWriter(output, fieldnames=fieldnames)
        writer.writeheader()
        
        for redirect in self.redirect_links:
            writer.writerow({
                'Page_URL': redirect['page_containing_link'],
                'Link_Text': redirect['link_text'][:200],  # Truncate long text
                'Original_URL': redirect['original_url'],
                'Final_URL': redirect['final_url'],
                'Redirect_Count': redirect['redirect_count'],
                'Status_Codes': ' -> '.join(map(str, redirect['status_codes'])),
                'Full_Redirect_Chain': ' -> '.join(redirect['redirect_chain']),
                'Page_Depth': redirect['page_depth'],
                'Full_Tag': redirect['full_tag'][:300],  # Truncate long tags
                'Timestamp': redirect['timestamp']
            })
        
        return output.getvalue()
    
    def generate_anchor_text_analysis_csv(self):
        """Generate CSV report for anchor text analysis"""
        output = io.StringIO()
        fieldnames = ['URL', 'Anchor_Text', 'Count', 'Text_Type', 'Source_Pages', 'Has_Redirects']
        
        writer = csv.DictWriter(output, fieldnames=fieldnames)
        writer.writeheader()
        
        for url, anchor_texts in self.anchor_text_analysis.items():
            # Count occurrences of each anchor text
            text_counter = Counter()
            text_types = {}
            source_pages = defaultdict(set)
            has_redirects = defaultdict(bool)
            
            for item in anchor_texts:
                text = item['text']
                text_counter[text] += 1
                text_types[text] = item['text_type']
                source_pages[text].add(item['source_page'])
                if item['is_redirect']:
                    has_redirects[text] = True
            
            # Write each unique anchor text as a separate row
            for text, count in text_counter.most_common():
                writer.writerow({
                    'URL': url,
                    'Anchor_Text': text,
                    'Count': count,
                    'Text_Type': text_types[text],
                    'Source_Pages': '; '.join(list(source_pages[text])[:3]) + ('...' if len(source_pages[text]) > 3 else ''),
                    'Has_Redirects': 'Yes' if has_redirects[text] else 'No'
                })
        
        return output.getvalue()
    
    def get_anchor_text_report_for_url(self, target_url):
        """Get detailed anchor text report for a specific URL"""
        # Normalize the URL
        target_url = self._clean_url(target_url)
        
        # Find all variations of this URL (including redirects)
        matching_data = []
        
        for url, anchor_texts in self.anchor_text_analysis.items():
            if url == target_url:
                matching_data.extend(anchor_texts)
        
        # Also check if any redirects lead to this URL
        for redirect in self.redirect_links:
            if redirect['final_url'] == target_url:
                matching_data.append({
                    'text': redirect['link_text'],
                    'text_type': self._classify_anchor_text(redirect['link_text'], None),
                    'source_page': redirect['page_containing_link'],
                    'is_redirect': True
                })
        
        if not matching_data:
            return None
        
        # Count and analyze
        text_counter = Counter()
        text_details = defaultdict(lambda: {
            'count': 0,
            'text_type': '',
            'source_pages': set(),
            'has_redirects': False
        })
        
        for item in matching_data:
            text = item['text']
            text_counter[text] += 1
            text_details[text]['count'] += 1
            text_details[text]['text_type'] = item['text_type']
            text_details[text]['source_pages'].add(item['source_page'])
            if item['is_redirect']:
                text_details[text]['has_redirects'] = True
        
        # Format the report
        report = {
            'target_url': target_url,
            'total_links_found': sum(text_counter.values()),
            'unique_anchor_texts': len(text_counter),
            'anchor_text_breakdown': []
        }
        
        for text, count in text_counter.most_common():
            details = text_details[text]
            report['anchor_text_breakdown'].append({
                'anchor_text': text,
                'count': count,
                'text_type': details['text_type'],
                'source_pages_count': len(details['source_pages']),
                'source_pages': list(details['source_pages'])[:5],  # Limit to first 5
                'has_redirects': details['has_redirects']
            })
        
        return report

# Global variable
current_analyzer = None

@app.route('/')
def index():
    return render_template('analyzer.html')

@app.route('/start_analysis', methods=['POST'])
def start_analysis():
    global current_analyzer
    
    data = request.get_json()
    website_url = data.get('url')
    max_pages = int(data.get('max_pages', 100))
    max_depth = int(data.get('max_depth', 3))
    selenium_threshold = int(data.get('selenium_threshold', 5))
    
    if not website_url:
        return jsonify({'error': 'Website URL is required'}), 400
    
    current_analyzer = WebsiteAnalyzer(website_url, max_pages, max_depth, selenium_threshold)
    
    def analyze_worker():
        current_analyzer.start_analysis()
    
    thread = threading.Thread(target=analyze_worker)
    thread.daemon = True
    thread.start()
    
    return jsonify({
        'status': 'Analysis started',
        'message': f'Analyzing {website_url}...',
        'selenium_available': SELENIUM_AVAILABLE
    })

@app.route('/analysis_status')
def analysis_status():
    global current_analyzer
    
    if not current_analyzer:
        return jsonify({'status': 'No analysis in progress'})
    
    return jsonify({
        'status': 'Complete' if current_analyzer.crawl_complete else 'In Progress',
        'pages_analyzed': len(current_analyzer.visited_urls),
        'total_anchors': len(current_analyzer.anchor_tags),
        'redirect_links': len(current_analyzer.redirect_links),
        'unique_urls_with_anchors': len(current_analyzer.anchor_text_analysis),
        'complete': current_analyzer.crawl_complete
    })

@app.route('/download_redirects_csv')
def download_redirects_csv():
    global current_analyzer
    
    if not current_analyzer or not current_analyzer.crawl_complete:
        return jsonify({'error': 'No completed analysis data available'}), 400
    
    csv_content = current_analyzer.generate_redirect_csv()
    
    temp_file = tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.csv')
    temp_file.write(csv_content)
    temp_file.close()
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    domain_safe = current_analyzer.domain.replace('.', '_')
    filename = f"redirect_links_{domain_safe}_{timestamp}.csv"
    
    return send_file(
        temp_file.name,
        as_attachment=True,
        download_name=filename,
        mimetype='text/csv'
    )

@app.route('/download_anchor_analysis_csv')
def download_anchor_analysis_csv():
    global current_analyzer
    
    if not current_analyzer or not current_analyzer.crawl_complete:
        return jsonify({'error': 'No completed analysis data available'}), 400
    
    csv_content = current_analyzer.generate_anchor_text_analysis_csv()
    
    temp_file = tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.csv')
    temp_file.write(csv_content)
    temp_file.close()
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    domain_safe = current_analyzer.domain.replace('.', '_')
    filename = f"anchor_text_analysis_{domain_safe}_{timestamp}.csv"
    
    return send_file(
        temp_file.name,
        as_attachment=True,
        download_name=filename,
        mimetype='text/csv'
    )

@app.route('/analyze_url', methods=['POST'])
def analyze_specific_url():  
    global current_analyzer
    
    if not current_analyzer or not current_analyzer.crawl_complete:
        return jsonify({'error': 'No completed analysis data available'}), 400
    
    data = request.get_json()
    target_url = data.get('url')
    
    if not target_url:
        return jsonify({'error': 'URL is required'}), 400
    
    report = current_analyzer.get_anchor_text_report_for_url(target_url)
    
    if not report:
        return jsonify({'error': 'No anchor text data found for this URL'}), 404
    
    return jsonify(report)

@app.route('/get_all_urls')
def get_all_urls():
    global current_analyzer
    
    if not current_analyzer or not current_analyzer.crawl_complete:
        return jsonify({'error': 'No completed analysis data available'}), 400
    
    # Get all unique URLs that have anchor text pointing to them
    urls = list(current_analyzer.anchor_text_analysis.keys())
    urls.sort()
    
    return jsonify({
        'urls': urls,
        'count': len(urls)
    })

if __name__ == '__main__':
    app.run(debug=True)
