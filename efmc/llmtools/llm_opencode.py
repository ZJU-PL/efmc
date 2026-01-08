"""
Using opencode as the LLM provider (to access different models)

A possible solution: call opencode server, which offers OpenAPI

https://opencode.ai/docs/server

(If we use TypeScript/JavaScript, we can use its SDK, https://opencode.ai/docs/sdk/)
"""

import concurrent.futures
import time
from typing import Tuple

import requests
import tiktoken

from efmc.llmtools.logger import Logger


class LLMOpenCode:
    """LLM inference using OpenCode server API."""

    def __init__(
        self,
        model_name: str,
        logger: Logger,
        temperature: float = 0.0,
        system_role: str = (
            "You are an experienced programmer and good at understanding "
            "programs written in mainstream programming languages."
        ),
        server_url: str = "http://127.0.0.1:4096",
    ) -> None:
        """
        Initialize OpenCode LLM.

        Args:
            model_name: Name of the model to use
            logger: Logger instance
            temperature: Temperature for inference (note: OpenCode may not support this)
            system_role: System role message
            server_url: OpenCode server URL
        """
        self.model_name = model_name
        self.server_url = server_url
        self.encoding = tiktoken.encoding_for_model("gpt-3.5-turbo-0125")
        self.temperature = temperature
        self.system_role = system_role
        self.logger = logger
        self.session_id = None

    def _create_session(self) -> str:
        """Create a new session and return session ID."""
        try:
            response = requests.post(f"{self.server_url}/session", timeout=10)
            response.raise_for_status()
            return response.json()["id"]
        except requests.exceptions.ConnectionError:
            error_msg = f"Failed to connect to OpenCode server at {self.server_url}. Is the server running?"
            self.logger.print_log(error_msg)
            print(f"ERROR: {error_msg}")
            return None
        except requests.exceptions.Timeout:
            error_msg = f"Connection to OpenCode server at {self.server_url} timed out."
            self.logger.print_log(error_msg)
            print(f"ERROR: {error_msg}")
            return None
        except Exception as e:
            error_msg = f"Failed to create session: {e}"
            self.logger.print_log(error_msg)
            print(f"ERROR: {error_msg}")
            return None

    def infer(
        self, message: str, is_measure_cost: bool = False
    ) -> Tuple[str, int, int]:
        """
        Infer using OpenCode server.

        Args:
            message: Input message
            is_measure_cost: Whether to measure token cost

        Returns:
            Tuple of (output, input_token_cost, output_token_cost)
        """
        self.logger.print_log(self.model_name, "is running via OpenCode")

        if not self.session_id:
            self.session_id = self._create_session()
            if not self.session_id:
                return "", 0, 0

        def call_api():
            url = f"{self.server_url}/session/{self.session_id}/message"
            payload = {
                "model": self.model_name,
                "parts": [{"type": "text", "content": message}],
            }
            if self.system_role:
                payload["system"] = self.system_role

            response = requests.post(url, json=payload, timeout=300)
            response.raise_for_status()
            data = response.json()

            # Extract text from parts
            text_parts = [
                p.get("content", "")
                for p in data.get("parts", [])
                if p.get("type") == "text"
            ]
            return "".join(text_parts)

        try_count = 0
        output = ""
        while try_count < 5:
            try_count += 1
            try:
                output = self.run_with_timeout(call_api, timeout_seconds=300)
                if output:
                    break
            except Exception as e:
                self.logger.print_log(f"OpenCode API error: {e}")
            time.sleep(2)

        input_token_cost = (
            0
            if not is_measure_cost
            else len(self.encoding.encode(self.system_role))
            + len(self.encoding.encode(message))
        )
        output_token_cost = (
            0 if not is_measure_cost else len(self.encoding.encode(output))
        )
        return output, input_token_cost, output_token_cost

    def run_with_timeout(self, func, timeout_seconds):
        """Run a function with timeout."""
        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as executor:
            future = executor.submit(func)
            try:
                return future.result(timeout=timeout_seconds)
            except concurrent.futures.TimeoutError:
                self.logger.print_log("Operation timed out")
                return ""
            except Exception as e:
                self.logger.print_log(f"Operation failed: {e}")
                return ""


if __name__ == "__main__":
    import sys
    
    logger = Logger("opencode.log")
    llm = LLMOpenCode("opencode/big-pickle", logger)
    
    print("Testing OpenCode LLM connection...")
    print(f"Server URL: {llm.server_url}")
    print(f"Model: {llm.model_name}")
    print()
    
    result = llm.infer("What is the capital of France?")
    output, input_tokens, output_tokens = result
    
    if output:
        print(f"Success! Output: {output}")
        print(f"Input tokens: {input_tokens}, Output tokens: {output_tokens}")
    else:
        print("ERROR: No output received from OpenCode server.")
        print("Please check:")
        print(f"  1. Is the OpenCode server running at {llm.server_url}?")
        print("  2. Check opencode.log for detailed error messages")
        sys.exit(1)