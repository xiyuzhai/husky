# Mayuri

Mayuri is an advanced MLOps (Machine Learning Operations) system designed to streamline and optimize the process of running, managing, and reusing machine learning experiments. It offers a comprehensive set of features to enhance productivity and efficiency in ML workflows.

## Key Features

### 1. Intelligent Experiment Reuse and Caching

Mayuri takes a unique approach to experiment management:

- Considers only the actual code used in an experiment along with its configuration
- Hashes this information to create a unique identifier for each experiment
- Enables efficient caching and reuse of experiments, saving time and computational resources

### 2. Efficient Source Code Management

- Tracks source code files using a smart system
- Stores file paths and their corresponding SHA-512 hashes
- Allows for quick identification of changes and efficient storage

### 3. Comprehensive Job and Test Management

- Provides structures for managing both jobs and tests
- Allows for organized execution and tracking of experiments
- Facilitates systematic evaluation of ML models and algorithms

### 4. Flexible Configuration Management

- Uses TOML configuration files for system settings
- Supports both Mayuri-specific settings and related components (e.g., Nemu)
- Allows for flexible and human-readable configuration of the system

### 5. Seamless File System Integration

- Integrates closely with the file system
- Provides a structured way to organize and access experiment-related files and directories
- Enhances project organization and reproducibility

### 6. YAML-based Experiment Definition

- Allows experiments to be defined using YAML files
- Provides a clear and structured way to specify experiment parameters and configurations
- Enhances readability and maintainability of experiment setups

### 7. Task Allocation Server

- Features a server component for allocating tasks
- Manages the distribution of jobs across available computational resources
- Ensures efficient utilization of hardware and enables parallel execution of experiments

### 8. Modular and Extensible Design

- Structured with separate modules for different components
- Allows for easy extensibility and maintenance of the system
- Facilitates the addition of new features and integration with other tools

## Benefits

- **Improved Efficiency**: Reuse of experiments and intelligent caching reduce redundant computations
- **Enhanced Reproducibility**: Precise tracking of code, configurations, and dependencies ensures experiment reproducibility
- **Scalability**: Task allocation server allows for efficient use of computational resources
- **Flexibility**: Modular design and configuration options adapt to various ML workflows
- **Organized Workflow**: Structured management of jobs, tests, and files streamlines the research process

Mayuri represents a powerful tool for researchers and data scientists working on complex machine learning projects, offering a comprehensive solution to common challenges in ML experimentation and deployment.