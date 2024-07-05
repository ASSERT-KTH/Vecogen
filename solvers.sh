#!/bin/bash

# This script installs the solvers required by the project

# Ensure the script is run as root
if [[ $EUID -ne 0 ]]; then
   echo "This script must be run as root" 
   exit 1
fi

# Load opam environment
eval $(opam env)

# Function to install CVC5
install_cvc5() {
    CVC5_URL="https://github.com/cvc5/cvc5/releases/download/latest/cvc5-Linux-x86_64-static-2024-07-04-2d09b3c.zip"
    wget $CVC5_URL -O cvc5.zip
    unzip cvc5.zip
    cp cvc5-Linux-x86_64-static/bin/cvc5 /usr/local/bin
    chmod +x /usr/local/bin/cvc5
    cvc5 --version
    rm -rf cvc5-Linux-x86_64-static cvc5.zip
}

# Function to install Z3
install_z3() {
    Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-4.8.6/z3-4.8.6-x64-ubuntu-16.04.zip"
    wget $Z3_URL -O z3.zip
    unzip z3.zip
    cp z3-4.8.6-x64-ubuntu-16.04/bin/z3 /usr/local/bin
    chmod +x /usr/local/bin/z3
    z3 -version
    rm -rf z3-4.8.6-x64-ubuntu-16.04 z3.zip
}

# Install required packages
apt-get update
apt-get install -y wget unzip

# Install the solvers
install_cvc5
install_z3

# Configure Why3
why3 config detect
