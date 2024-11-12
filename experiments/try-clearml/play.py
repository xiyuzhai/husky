from clearml import Task


# Your ML code goes here
def train_model():
    # Simulating some training process
    for epoch in range(10):
        accuracy = epoch * 10  # Dummy accuracy
        task.get_logger().report_scalar(
            "train", "accuracy", value=accuracy, iteration=epoch
        )


# Run the training
if __name__ == "__main__":
    # Initialize a new task
    task = Task.init(project_name="My Project", task_name="My First Task")
    train_model()
    print("Training completed!")
