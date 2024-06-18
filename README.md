# Mechanising Proofs for Executable Code Using Hacspec & Coq

## Introduction
This repository contains the code and documentation for our master thesis project. The aim of this project is to investigate the process of mechanising proofs for executable code using Hacspec & Coq.

## Thesis
For the full report, please see [the thesis](https://github.com/JonasDAncher/MasterThesis/blob/main/MasterThesis.pdf). This file has been updated since the deadline for the report, with corrections and adjustments. The date on the report is the date of the most recent edit.

## Installation
To install the prerequisites of Hacspec and Rust:
1. Install Rust on your local machine.
2. Change the default toolchain `rustup default nightly-2023-01-15`.
3. Add necessary component to the toolchain`rustup component add --toolchain nightly-2023-01-15 llvm-tools-preview`.
4. Install the dependencies `sudo apt install llvm-dev libclang-dev clang build-essential`.
5. Clone the Hacspec [repository](https://github.com/hacspec/hacspec).
6. Navigate to the `/language` directory. 
7. Install Hacspec by running `cargo install --path .`

Coq and all its related libraries are used by entering the nix-shell. To enter this:
1. Ensure you have Nix installed.
2. Navigate to the `/nixfolder`.
3. Run `nix-shell` to enter the shell.
You now have access to Coq, CoqIDE, SSProve, Mathcomp, Mathcomp-Analysis, SSReflect, in addition to Hacspec.

## Usage
To run the proofs from the projects, based on the Rust implementation, follow these steps:

1. Navigate to `/ElGamal/`
2. Translate all `.rs` files in `/rs_src` by running `cargo hacspec --dir ./coq_src -e v`. All the translated files can be found in `/coq_src`
3. To compile & run the Coq files, run `make`.

## Contributing
Contributions to this project are welcome. If you would like to contribute, please follow these guidelines:

1. Fork the repository and create a new branch.
2. Make your changes and ensure they are properly tested.
3. Submit a pull request, describing the changes you have made.

## Contact
If you have any questions regarding this project, please feel free to contact us at <jonasdancher@hotmail.com> or <christianmjensen@outlook.com>.
