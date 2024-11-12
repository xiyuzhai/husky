from dataset import Dataset
from model import train_model

if __name__ == "__main__":
    # Generate a 2D Gaussian dataset
    mean = (0, 0)
    cov = [[1, 0.5], [0.5, 1]]
    data = generate_2d_gaussian(n_samples=2000, mean=mean, cov=cov)

    # Create data loaders
    train_loader, val_loader, test_loader = create_data_loaders(data, batch_size=32)

    print(f"Number of batches in train_loader: {len(train_loader)}")
    print(f"Number of batches in val_loader: {len(val_loader)}")
    print(f"Number of batches in test_loader: {len(test_loader)}")

    # Plot the dataset
    plot_2d_gaussian(data, title="2D Gaussian Distribution Example")
