import numpy as np
import matplotlib.pyplot as plt
import torch
from torch.utils.data import Dataset, DataLoader
from sklearn.model_selection import train_test_split


class GaussianDataset(Dataset):
    def __init__(self, n_samples=1000, mean=(0, 0), cov=[[1, 0], [0, 1]]):
        self.data = torch.FloatTensor(generate_2d_gaussian(n_samples, mean, cov))

    def __len__(self):
        return len(self.data)

    def __getitem__(self, idx):
        return self.data[idx]


def generate_2d_gaussian(n_samples=1000, mean=(0, 0), cov=[[1, 0], [0, 1]]):
    """
    Generate a 2D Gaussian distribution dataset.

    Args:
        n_samples (int): Number of samples to generate.
        mean (tuple): Mean of the distribution (x, y).
        cov (list): 2x2 covariance matrix.

    Returns:
        numpy.ndarray: Array of shape (n_samples, 2) containing the generated points.
    """
    return np.random.multivariate_normal(mean, cov, n_samples)


def create_data_loaders(
    data, batch_size=32, train_ratio=0.7, val_ratio=0.15, test_ratio=0.15
):
    """
    Create train, validation, and test data loaders.

    Args:
        data (numpy.ndarray): The dataset to split and load.
        batch_size (int): Batch size for the data loaders.
        train_ratio (float): Ratio of data to use for training.
        val_ratio (float): Ratio of data to use for validation.
        test_ratio (float): Ratio of data to use for testing.

    Returns:
        tuple: (train_loader, val_loader, test_loader)
    """
    # Split the data into train+val and test
    train_val, test = train_test_split(data, test_size=test_ratio, random_state=42)

    # Split the train+val into train and val
    train, val = train_test_split(
        train_val, test_size=val_ratio / (train_ratio + val_ratio), random_state=42
    )

    # Create datasets
    train_dataset = GaussianDataset(train)
    val_dataset = GaussianDataset(val)
    test_dataset = GaussianDataset(test)

    # Create data loaders
    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True)
    val_loader = DataLoader(val_dataset, batch_size=batch_size)
    test_loader = DataLoader(test_dataset, batch_size=batch_size)

    return train_loader, val_loader, test_loader


def plot_2d_gaussian(data, title="2D Gaussian Distribution"):
    """
    Plot the 2D Gaussian distribution.

    Args:
        data (numpy.ndarray): Array of shape (n_samples, 2) containing the data points.
        title (str): Title for the plot.
    """
    plt.figure(figsize=(10, 8))
    plt.scatter(data[:, 0], data[:, 1], alpha=0.5)
    plt.title(title)
    plt.xlabel("X")
    plt.ylabel("Y")
    plt.grid(True)
    plt.show()
