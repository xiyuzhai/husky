import argparse
import torch
import torch.nn as nn
import torch.optim as optim
from torch.utils.data import DataLoader, random_split
import wandb
from datasets.mini_husky import MiniHuskyDataset
from models.transformer import EncoderOnlyTransformer, CustomBERTModel
from train import train_model
from utils import set_seed, custom_collate, linear_warmup_decay, Logger, ordered_search_space

import tiktoken

import os
import pdb

tokenizer = tiktoken.encoding_for_model("gpt2")

HIDDEN_DIM_SPACE = list(range(8, 64 + 1, 8)) + [208]
BATCH_SIZE = 512

parser = argparse.ArgumentParser(description="Train Transformer models with different configurations.")
parser.add_argument('--dataset', type=str, default="n100000-f10-a5-c5-d3-v0.20-e0.50", help='Dataset to use')
parser.add_argument('--num_epochs', type=int, default=10, help='Number of epochs to train')
parser.add_argument('--seed', type=int, default=42, help='Random seed for initialization')
parser.add_argument('--server_name', type=str, default="")
parser.add_argument('--gpu_id', type=int, default=0)
parser.add_argument('--hidden_dims', nargs='+', type=int, help='List of hidden dimensions')
args = parser.parse_args()

train_dataset = MiniHuskyDataset(os.path.join(os.environ["DATA_ROOT"],
                                              "mini-husky/basic",
                                              f"dataset-{args.dataset}_train.json.gz"),
                                 desired_key="expected_type")
eval_dataset = MiniHuskyDataset(os.path.join(os.environ["DATA_ROOT"],
                                             "mini-husky/basic",
                                             f"dataset-{args.dataset}_eval.json.gz"),
                                desired_key="expected_type")
header = train_dataset.header
max_seq_len = ((max(train_dataset.get_max_len(),
                    eval_dataset.get_max_len()) - 1) // 512 + 1) * 512

def run(config, train_dataset, eval_dataset, header):
    set_seed(config["seed"])

    train_dataloader = DataLoader(
        train_dataset,
        batch_size=config["batch_size"],
        shuffle=True,
        collate_fn=custom_collate,
        num_workers=4,
    )
    eval_dataloader = DataLoader(
        eval_dataset,
        batch_size=config["batch_size"],
        shuffle=False,
        collate_fn=custom_collate,
        num_workers=4,
    )

    exp_name = f"transformer_d{config['hidden_dim']}_h{config['num_heads']}_l{config['num_layers']}_seed{config['seed']}_{args.dataset}"

    device = torch.device(f"cuda:{config['gpu_id']}" if torch.cuda.is_available() else "cpu")
    model = CustomBERTModel(output_dim=sum(train_dataset.get_output_dims()), **config).to(device)
    config["total_params"] = sum(p.numel() for p in model.parameters() if p.requires_grad)

    logger = Logger(exp_root=os.path.join(os.environ["EXP_ROOT"], "transformer_vs_rnn"),
                    exp_name=exp_name, log_wandb=True, config=config)

    criterion = nn.CrossEntropyLoss(reduction="sum")
    optimizer = optim.Adam(model.parameters(), lr=1)
    scheduler = torch.optim.lr_scheduler.LambdaLR(optimizer, lr_lambda=linear_warmup_decay(total_iters=config["num_epochs"] * len(train_dataloader), **config))

    print("Training Transformer...")
    model = train_model(model=model, header=header, train_dataloader=train_dataloader, val_dataloader=eval_dataloader, criterion=criterion, optimizer=optimizer, scheduler=scheduler, num_epochs=config["num_epochs"], micro_batch_size=config["micro_batch_size"], device=device, output_dims=train_dataset.get_output_dims(), logger=logger)

    logger.finish()
    # torch.save(model.state_dict(), os.path.join(logger.exp_path, "model.pth"))

if args.hidden_dims:
    print("Running with hidden_dims:", args.hidden_dims)
    search_space = args.hidden_dims
else:
    search_space = HIDDEN_DIM_SPACE

for hidden_dim in ordered_search_space(search_space):
    if hidden_dim <= 64:
        min_lr, max_lr = 1e-5, 1e-3
    else:
        min_lr, max_lr = 2e-6, 2e-4

    micro_batch_size = 32

    config = {
        "batch_size": BATCH_SIZE,
        "micro_batch_size": micro_batch_size,
        "min_lr": min_lr,
        "max_lr": max_lr,
        "warmup_iters": 990,
        "vocab_size": tokenizer.n_vocab,
        "output_dims": train_dataset.get_output_dims(),
        "hidden_dim": hidden_dim,
        "num_heads": 1,
        "num_layers": 8,
        "max_seq_len": max_seq_len,
        **vars(args)
    }

    # Run the training
    run(config, train_dataset, eval_dataset, header)
