import warnings
warnings.filterwarnings("ignore", category=FutureWarning)
warnings.filterwarnings("ignore", category=UserWarning)
warnings.filterwarnings("ignore", module="transformers.*")
warnings.filterwarnings("ignore", module="torch.*")

import os
import torch
os.environ["TOKENIZERS_PARALLELISM"] = "false"
os.environ["TRANSFORMERS_VERBOSITY"] = "error"

from spacy.cli import download
import spacy
import benepar

class Parser:
    def __init__(self, device='cuda' if torch.cuda.is_available() else 'cpu'):
        self.device = device
        # Load models once during initialization
        self.nlp = spacy.load("en_core_web_md")
        if 'benepar' not in self.nlp.pipe_names:
            # benepar.download('benepar_en3')
            self.nlp.add_pipe('benepar', config={'model': 'benepar_en3'})
        
        # spaCy handles GPU automatically

    def parse_sentence(self, sentence):
        doc = self.nlp(sentence)
        sent = list(doc.sents)[0]
        return sent._.parse_string
    
    def parse_batch(self, sentences, batch_size=32):
        """Batch process multiple sentences for better performance"""
        return [sent._.parse_string for doc in self.nlp.pipe(sentences, batch_size=batch_size) 
                for sent in doc.sents]

# Create parser once
parser = Parser()

def parse_sentence(sentence):
    return parser.parse_sentence(sentence)

# Example usage
if __name__ == "__main__":
    # sentence = "I went home with mom and dad"
    # parse_tree = parse_sentence(sentence)
    # print("Parse Tree:")
    # print(parse_tree)

    # Example of batch processing
    sentences = ["If the dog barks, the cat will meow."]
    parse_trees = parser.parse_batch(sentences)
    for tree in parse_trees:
        print(tree)
