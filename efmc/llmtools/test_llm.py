#!/usr/bin/env python3
"""
Short demo calling DeepSeek API

export DEEPSEEK_API_KEY=xxx # your DeepSeek API key
"""
from efmc.llmtools.llm_utils import LLM
from efmc.llmtools.logger import Logger
import os

def main():
    # Initialize logger
    logger = Logger("test_deepseek.log")
    
    # Create LLM instance with DeepSeek model
    # Common model names: "deepseek-chat", "deepseek-reasoner", "deepseek-r1"
    model_name = "deepseek-chat"
    model = LLM(model_name, logger, temperature=0.7)
    
    # Simple test prompt
    prompt = "What is 2+2? Answer in one sentence."
    
    print(f"Calling {model_name} with prompt: {prompt}")
    print("-" * 50)
    
    # Call the model
    response, input_tokens, output_tokens = model.infer(prompt, is_measure_cost=True)
    
    # Print results
    print(f"\nResponse:\n{response}")
    print(f"\nTokens - Input: {input_tokens}, Output: {output_tokens}")

if __name__ == "__main__":
    # Check if API key is set
    if not os.environ.get("DEEPSEEK_API_KEY"):
        print("Warning: DEEPSEEK_API_KEY environment variable not set!")
        print("Please set it before running this demo.")
    else:
        main()
