# CDMO-project

Project exam for the course in _"Combinatorial Decision Making and Optimization"_ of the Master's degree in Artificial Intelligence, University of Bologna (2023/2024).

## Docker Instructions

1. Open the terminal.
2. Navigate to the directory containing this README.
3. To build the Docker image, choose a name and run:

   `docker build . -t <image_name> -f Dockerfile`
4. Launch the Docker image in a bash shell to use it:

   `docker run -it <image_name> /bin/bash`
5. The CLI usage instructions will be displayed in the terminal. You can also refer to them [in the following section](#execution-of-the-main).
6. After all executions, to extract the results, first obtain the container ID with:

   `docker ps -qf "ancestor=<image_name>"`

   Then, extract the folder with:

   `docker cp <container_id>:<folder_path_in_container> <folder_path_in_local>`

   **Note**: When specifying the path in the container, remember that the entire project is located in `/project`.

## Execution of the main

The `main2.py` script is the primary entry point for running different combinatorial optimization approaches on specified instances. The script can be executed with various command-line options, allowing for flexible configuration and execution.

### Basic Usage

Running `main2.py` without any arguments will solve all instance numbers using all available approaches (`cp`, `sat`, `smt`, `mip`). However, you can customize the execution by specifying particular instances, approaches, or a configuration file.

### Command-line Options

- `-h, --help`

  Displays the help message and exits.
- `-instances INSTANCES [INSTANCES ...]`

  Specify one or more instance numbers to execute.

  - Example: `-instances 1 2 3`
- `-config CONFIG`

  Provide a JSON configuration file to customize execution settings such as folder names or instance numbers.

  - Example: `-config settings.json`
- `-cp`

  Run the CP (Constraint Programming) approach.
- `-sat`

  Run the SAT (Satisfiability) approach.
- `-smt`

  Run the SMT (Satisfiability Modulo Theories) approach.
- `-mip`

  Run the MIP (Mixed-Integer Programming) approach.
- `-keep_folder`

  Prevent the results folder from being emptied during subsequent executions.

### Configuration File

The configuration file is a JSON that can be used to define settings such as folder names and instance numbers. Below is an example of a JSON configuration:

```json
{
    "instances_folder": "instances_dzn",
    "smt_models_folder": "SMT/models",
    "results_folder": "res",
    "indent_results": true,
    "first": 1,
    "last": 21,
    "timeout": 300,
    "run_checker": true
}
```

### Result folder

If an instance or an approach is parsed, the results will be stored in a `<results_folder>_temp` folder.

###### Authors

• [Davide Crociati](https://github.com/davidecrociati)

• [Davide Sonno](https://github.com/davidesonno)

• [Lorenzo Pellegrino](https://github.com/lollopelle01)
