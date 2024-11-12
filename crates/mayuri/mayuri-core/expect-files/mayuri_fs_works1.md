```rust
MayuriFs {
    root: "experiments/mayuri-prototype",
    src: MayuriSrc {
        dir_path: "experiments/mayuri-prototype/src",
        files: {
            "datasets/gaussian.py": MayuriSrcFile {
                content: "import numpy as np\nimport matplotlib.pyplot as plt\nimport torch\nfrom torch.utils.data import Dataset, DataLoader\nfrom sklearn.model_selection import train_test_split\n\n\nclass GaussianDataset(Dataset):\n    def __init__(self, n_samples=1000, mean=(0, 0), cov=[[1, 0], [0, 1]]):\n        self.data = torch.FloatTensor(generate_2d_gaussian(n_samples, mean, cov))\n\n    def __len__(self):\n        return len(self.data)\n\n    def __getitem__(self, idx):\n        return self.data[idx]\n\n\ndef generate_2d_gaussian(n_samples=1000, mean=(0, 0), cov=[[1, 0], [0, 1]]):\n    \"\"\"\n    Generate a 2D Gaussian distribution dataset.\n\n    Args:\n        n_samples (int): Number of samples to generate.\n        mean (tuple): Mean of the distribution (x, y).\n        cov (list): 2x2 covariance matrix.\n\n    Returns:\n        numpy.ndarray: Array of shape (n_samples, 2) containing the generated points.\n    \"\"\"\n    return np.random.multivariate_normal(mean, cov, n_samples)\n\n\ndef create_data_loaders(\n    data, batch_size=32, train_ratio=0.7, val_ratio=0.15, test_ratio=0.15\n):\n    \"\"\"\n    Create train, validation, and test data loaders.\n\n    Args:\n        data (numpy.ndarray): The dataset to split and load.\n        batch_size (int): Batch size for the data loaders.\n        train_ratio (float): Ratio of data to use for training.\n        val_ratio (float): Ratio of data to use for validation.\n        test_ratio (float): Ratio of data to use for testing.\n\n    Returns:\n        tuple: (train_loader, val_loader, test_loader)\n    \"\"\"\n    # Split the data into train+val and test\n    train_val, test = train_test_split(data, test_size=test_ratio, random_state=42)\n\n    # Split the train+val into train and val\n    train, val = train_test_split(\n        train_val, test_size=val_ratio / (train_ratio + val_ratio), random_state=42\n    )\n\n    # Create datasets\n    train_dataset = GaussianDataset(train)\n    val_dataset = GaussianDataset(val)\n    test_dataset = GaussianDataset(test)\n\n    # Create data loaders\n    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True)\n    val_loader = DataLoader(val_dataset, batch_size=batch_size)\n    test_loader = DataLoader(test_dataset, batch_size=batch_size)\n\n    return train_loader, val_loader, test_loader\n\n\ndef plot_2d_gaussian(data, title=\"2D Gaussian Distribution\"):\n    \"\"\"\n    Plot the 2D Gaussian distribution.\n\n    Args:\n        data (numpy.ndarray): Array of shape (n_samples, 2) containing the data points.\n        title (str): Title for the plot.\n    \"\"\"\n    plt.figure(figsize=(10, 8))\n    plt.scatter(data[:, 0], data[:, 1], alpha=0.5)\n    plt.title(title)\n    plt.xlabel(\"X\")\n    plt.ylabel(\"Y\")\n    plt.grid(True)\n    plt.show()\n",
            },
            "datasets/ring.py": MayuriSrcFile {
                content: "",
            },
            "main.py": MayuriSrcFile {
                content: "print(\"Hello world\")\n",
            },
            "models/fcn.py": MayuriSrcFile {
                content: "",
            },
            "visualize.py": MayuriSrcFile {
                content: "from dataset import Dataset\nfrom model import train_model\n\nif __name__ == \"__main__\":\n    # Generate a 2D Gaussian dataset\n    mean = (0, 0)\n    cov = [[1, 0.5], [0.5, 1]]\n    data = generate_2d_gaussian(n_samples=2000, mean=mean, cov=cov)\n\n    # Create data loaders\n    train_loader, val_loader, test_loader = create_data_loaders(data, batch_size=32)\n\n    print(f\"Number of batches in train_loader: {len(train_loader)}\")\n    print(f\"Number of batches in val_loader: {len(val_loader)}\")\n    print(f\"Number of batches in test_loader: {len(test_loader)}\")\n\n    # Plot the dataset\n    plot_2d_gaussian(data, title=\"2D Gaussian Distribution Example\")\n",
            },
        },
    },
    makefile: MayuriMakefileExtracted {
        content: "run:\n\tpython main.py\n",
    },
    jobs: MayuriJobs {
        jobs: [],
    },
    tests: MayuriTests {
        tests: [
            MayuriTest {
                path: "experiments/mayuri-prototype/tests/hello.yml",
                name: "hello-1",
                rank: 0,
                experiment: Experiment {
                    gene: ExperimentGene {
                        src_paths: [
                            (
                                "dataset.py",
                                "datasets/gaussian.py",
                            ),
                            (
                                "main.py",
                                "main.py",
                            ),
                            (
                                "model.py",
                                "models/fcn.py",
                            ),
                        ],
                        config: OrderedYaml("---
                        epochs: 10"),
                    },
                    gene_sha_str: "45e6a75fb81063dc",
                    protein: ExperimentProtein {
                        src_files: [
                            (
                                "dataset.py",
                                MayuriSrcFile {
                                    content: "import numpy as np\nimport matplotlib.pyplot as plt\nimport torch\nfrom torch.utils.data import Dataset, DataLoader\nfrom sklearn.model_selection import train_test_split\n\n\nclass GaussianDataset(Dataset):\n    def __init__(self, n_samples=1000, mean=(0, 0), cov=[[1, 0], [0, 1]]):\n        self.data = torch.FloatTensor(generate_2d_gaussian(n_samples, mean, cov))\n\n    def __len__(self):\n        return len(self.data)\n\n    def __getitem__(self, idx):\n        return self.data[idx]\n\n\ndef generate_2d_gaussian(n_samples=1000, mean=(0, 0), cov=[[1, 0], [0, 1]]):\n    \"\"\"\n    Generate a 2D Gaussian distribution dataset.\n\n    Args:\n        n_samples (int): Number of samples to generate.\n        mean (tuple): Mean of the distribution (x, y).\n        cov (list): 2x2 covariance matrix.\n\n    Returns:\n        numpy.ndarray: Array of shape (n_samples, 2) containing the generated points.\n    \"\"\"\n    return np.random.multivariate_normal(mean, cov, n_samples)\n\n\ndef create_data_loaders(\n    data, batch_size=32, train_ratio=0.7, val_ratio=0.15, test_ratio=0.15\n):\n    \"\"\"\n    Create train, validation, and test data loaders.\n\n    Args:\n        data (numpy.ndarray): The dataset to split and load.\n        batch_size (int): Batch size for the data loaders.\n        train_ratio (float): Ratio of data to use for training.\n        val_ratio (float): Ratio of data to use for validation.\n        test_ratio (float): Ratio of data to use for testing.\n\n    Returns:\n        tuple: (train_loader, val_loader, test_loader)\n    \"\"\"\n    # Split the data into train+val and test\n    train_val, test = train_test_split(data, test_size=test_ratio, random_state=42)\n\n    # Split the train+val into train and val\n    train, val = train_test_split(\n        train_val, test_size=val_ratio / (train_ratio + val_ratio), random_state=42\n    )\n\n    # Create datasets\n    train_dataset = GaussianDataset(train)\n    val_dataset = GaussianDataset(val)\n    test_dataset = GaussianDataset(test)\n\n    # Create data loaders\n    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True)\n    val_loader = DataLoader(val_dataset, batch_size=batch_size)\n    test_loader = DataLoader(test_dataset, batch_size=batch_size)\n\n    return train_loader, val_loader, test_loader\n\n\ndef plot_2d_gaussian(data, title=\"2D Gaussian Distribution\"):\n    \"\"\"\n    Plot the 2D Gaussian distribution.\n\n    Args:\n        data (numpy.ndarray): Array of shape (n_samples, 2) containing the data points.\n        title (str): Title for the plot.\n    \"\"\"\n    plt.figure(figsize=(10, 8))\n    plt.scatter(data[:, 0], data[:, 1], alpha=0.5)\n    plt.title(title)\n    plt.xlabel(\"X\")\n    plt.ylabel(\"Y\")\n    plt.grid(True)\n    plt.show()\n",
                                },
                            ),
                            (
                                "main.py",
                                MayuriSrcFile {
                                    content: "print(\"Hello world\")\n",
                                },
                            ),
                            (
                                "model.py",
                                MayuriSrcFile {
                                    content: "",
                                },
                            ),
                        ],
                        config: OrderedYaml("---
                        epochs: 10"),
                        makefile: MayuriMakefileExtracted {
                            content: "run:\n\tpython main.py\n",
                        },
                    },
                },
            },
            MayuriTest {
                path: "experiments/mayuri-prototype/tests/hello.yml",
                name: "hello-2",
                rank: 1,
                experiment: Experiment {
                    gene: ExperimentGene {
                        src_paths: [
                            (
                                "dataset.py",
                                "datasets/ring.py",
                            ),
                            (
                                "main.py",
                                "main.py",
                            ),
                            (
                                "model.py",
                                "models/fcn.py",
                            ),
                        ],
                        config: OrderedYaml("---
                        epochs: 10"),
                    },
                    gene_sha_str: "b8396620e16bbd15",
                    protein: ExperimentProtein {
                        src_files: [
                            (
                                "dataset.py",
                                MayuriSrcFile {
                                    content: "",
                                },
                            ),
                            (
                                "main.py",
                                MayuriSrcFile {
                                    content: "print(\"Hello world\")\n",
                                },
                            ),
                            (
                                "model.py",
                                MayuriSrcFile {
                                    content: "",
                                },
                            ),
                        ],
                        config: OrderedYaml("---
                        epochs: 10"),
                        makefile: MayuriMakefileExtracted {
                            content: "run:\n\tpython main.py\n",
                        },
                    },
                },
            },
        ],
    },
    mayuri_config: MayuriConfig,
    nemu_config: NemuConfig {
        src_paths: [
            SrcPath {
                path_str: "main.py",
            },
        ],
    },
}
```