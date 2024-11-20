import spacy
import torch

def setup_parser():
    # Download and initialize the English model if not already downloaded
    try:
        nlp = spacy.load("en_core_web_sm")
    except OSError:
        from spacy.cli.download import download
        download("en_core_web_sm")
        nlp = spacy.load("en_core_web_sm")
    return nlp

def parse_text(nlp, text):
    doc = nlp(text)
    
    for sent in doc.sents:
        print("\nSentence:", sent.text)
        print("\nDependency Tree:")
        
        # Find root
        root = None
        for token in sent:
            if token.dep_ == "ROOT":
                root = token
                break
        
        def print_tree(token, level=0):
            # Print current token with indentation
            print("  " * level + "└─" + token.text + " (" + token.dep_ + ")")
            # Print all children
            children = [child for child in token.children]
            for child in children:
                print_tree(child, level + 1)
        
        print_tree(root)

if __name__ == "__main__":
    nlp = setup_parser()
    
    # Test text with LaTeX mathematical formulas
    text = "The Pythagorean theorem states that $a^2 + b^2 = c^2$ holds for any right triangle, where $\\alpha \\in (0, \\frac{\\pi}{2})$ represents the angle."
    parse_text(nlp, text)
