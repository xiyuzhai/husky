import torch
from tqdm import tqdm


import torch.nn.functional as F

import pdb

def train_model(
    model,
    header,
    train_dataloader,
    val_dataloader,
    criterion,
    optimizer,
    num_epochs,
    micro_batch_size,
    device,
    output_dims,
    logger,
    patience=5,
    min_delta=0.001,
    scheduler=None,
):
    model.to(device)

    best_val_loss = float("inf")
    epochs_without_improvement = 0
    best_model_state = None

    for epoch in range(num_epochs):
        # Training phase
        model.train()
        train_loss, train_accs = run_epoch(
            epoch_idx=epoch,
            model=model,
            header=header,
            dataloader=train_dataloader,
            criterion=criterion,
            optimizer=optimizer,
            scheduler=scheduler,
            device=device,
            output_dims=output_dims,
            is_training=True,
            micro_batch_size=micro_batch_size,
            logger=logger,
        )

        # Validation phase
        model.eval()
        val_loss, val_accs = run_epoch(
            epoch_idx=epoch,
            model=model,
            header=header,
            dataloader=val_dataloader,
            criterion=criterion,
            optimizer=optimizer,
            device=device,
            output_dims=output_dims,
            is_training=False,
            micro_batch_size=micro_batch_size * 4,
        )

        # Early stopping check
        # if val_loss < best_val_loss - min_delta:
        #     best_val_loss = val_loss
        #     epochs_without_improvement = 0
        #     best_model_state = model.state_dict()
        # else:
        #     epochs_without_improvement += 1

        logger.log(
            {
                f"val/loss": val_loss,
                **{f"val/{k}_acc": v for k, v in val_accs.items()},
                "train/step": (epoch + 1) * len(train_dataloader),
            }
        )

        print(
            f"Epoch [{epoch + 1}/{num_epochs}], "
            f"Train Loss: {train_loss:.4f}, Val Loss: {val_loss:.4f}, "
        )
        for k in val_accs:
            print(f"Train {k} acc: {train_accs[k]:.4f}, Val {k} acc: {val_accs[k]:.4f}")

        # if epochs_without_improvement >= patience:
        #     print(f"Early stopping triggered after {epoch + 1} epochs")
        #     break

    # Load the best model state
    # if best_model_state is not None:
    #     model.load_state_dict(best_model_state)
    #     print("Loaded best model state from early stopping")

    return model

def run_epoch(
    epoch_idx,
    model,
    header,
    dataloader,
    criterion,
    optimizer,
    device,
    output_dims,
    is_training,
    micro_batch_size,
    scheduler=None,
    logger=None,
):
    total_loss = 0.0
    accs = {k: 0.0 for k in header}

    for batch_idx, (_inputs, _targets) in tqdm(enumerate(dataloader)):
        current_iter = epoch_idx * len(dataloader) + batch_idx

        _inputs = _inputs.to(device)
        _targets = [t.to(device) for t in _targets]

        if is_training:
            optimizer.zero_grad()

        with torch.set_grad_enabled(is_training):
            combined_loss = 0.0
            combined_accs = {k: 0.0 for k in header}
            cnt = {k: 0 for k in header}
            for i in range(0, _inputs.shape[0], micro_batch_size):
                outputs = model(_inputs[i:i + micro_batch_size])
                output_by_fields = list(outputs.split(output_dims, dim=-1))
                for j in range(len(output_by_fields)):
                    output_by_fields[j] = output_by_fields[j].reshape(-1, output_dims[j])

                target_by_fields = [t[i:i + micro_batch_size].view(-1) for t in _targets]

                micro_batch_loss = 0.0
                for k, o, t in zip(header, output_by_fields, target_by_fields):
                    mask = t > 0
                    
                    combined_accs[k] += (o.detach().argmax(dim=1) == t)[mask].float().sum()
                    _cnt = mask.sum()
                    cnt[k] += _cnt
                    
                    micro_batch_loss += criterion(o[mask], t[mask]) / _cnt
                
                micro_batch_loss /= (_inputs.shape[0] - 1) // micro_batch_size + 1
                if is_training:
                    micro_batch_loss.backward()
                combined_loss += micro_batch_loss.detach()

            for k, v in combined_accs.items():
                combined_accs[k] = v / cnt[k]

            if logger is not None:
                # must be training
                logger.log(
                    {
                        f"train/loss": combined_loss.item(),
                        **{f"train/{k}_acc": v.item() for k, v in combined_accs.items()},
                        f"train/learning_rate": optimizer.param_groups[0]["lr"],
                        "train/step": current_iter,
                    }
                )

            if is_training:
                optimizer.step()
                if scheduler is not None:
                    scheduler.step()

        total_loss += combined_loss.item()
        for k in accs:
            accs[k] += combined_accs[k].item()

    avg_loss = total_loss / len(dataloader)
    for k in accs:
        accs[k] /= len(dataloader)
    
    return avg_loss, accs
