import requests
from loguru import logger

class DeepEarLiteTools:
    """
    Tools for fetching signals from DeepEar Lite (https://deepear.vercel.app/lite).
    """
    
    LATEST_JSON_URL = "https://deepear.vercel.app/latest.json"

    def fetch_latest_signals(self):
        """
        Fetch the newest financial signals from DeepEar Lite.
        Returns a formatted summary of the latest signals.
        """
        try:
            logger.info(f"Fetching data from {self.LATEST_JSON_URL}")
            headers = {
                "User-Agent": "DeepEar-Skill-Agent/1.0 (Awesome-Finance-Skills)",
                "Referer": "https://deepear.vercel.app/lite"
            }
            response = requests.get(self.LATEST_JSON_URL, headers=headers, timeout=10)
            response.raise_for_status()
            data = response.json()
            
            generated_at = data.get("generated_at", "Unknown")
            signals = data.get("signals", [])
            
            if not signals:
                return "No signals found in the latest data."
            
            report = [f"### DeepEar Lite Signal Report (Updated: {generated_at})\n"]
            
            for i, signal in enumerate(signals, 1):
                title = signal.get("title", "No Title")
                summary = signal.get("summary", "No Summary")
                sentiment = signal.get("sentiment_score", 0)
                confidence = signal.get("confidence", 0)
                intensity = signal.get("intensity", 0)
                reasoning = signal.get("reasoning", "No Reasoning")
                
                report.append(f"#### {i}. {title}")
                report.append(f"**Sentiment**: {sentiment} | **Confidence**: {confidence} | **Intensity**: {intensity}")
                report.append(f"\n**Summary**: {summary}")
                report.append(f"\n**Reasoning**: {reasoning}")
                
                # Check for sources/links
                sources = signal.get("sources", [])
                if sources:
                    report.append("\n**Sources**:")
                    for src in sources:
                        name = src.get("name", "Link")
                        url = src.get("url", "#")
                        report.append(f"- [{name}]({url})")
                
                report.append("\n" + "-"*40 + "\n")
                
            return "\n".join(report)

        except Exception as e:
            error_msg = f"Error fetching DeepEar Lite data: {str(e)}"
            logger.error(error_msg)
            return error_msg

if __name__ == "__main__":
    tools = DeepEarLiteTools()
    print(tools.fetch_latest_signals())
