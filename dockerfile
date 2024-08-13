# Use the official Debian image as a base
FROM debian:latest

# Update the package list and install dependencies
RUN apt-get update && apt-get install -y \
    opam \
    m4 \
    bubblewrap \
    wget \
    gcc \
    libc-dev \
    make \
    unzip \
    graphviz \
    libcairo2-dev \
    libexpat1-dev \
    libgmp-dev \
    libgtk-3-dev \
    libgtksourceview-3.0-dev \
    pkg-config \
    zlib1g-dev \ 
    python3 \
    python3-venv \
    python3-pip

# Set the working directory
COPY requirements.txt /Vecogen/requirements.txt
WORKDIR /Vecogen

# Initialize OPAM (OCaml Package Manager) and install OCaml
RUN opam init -y --disable-sandboxing && \
    opam update && \
    opam switch create 4.14.1 && \
    opam switch 4.14.1 && \
    opam install -y opam-depext && \
    opam depext --install -y frama-c && \
    python3 -m venv venv && \
    . venv/bin/activate && \
    venv/bin/pip install --upgrade pip && \
    venv/bin/pip install -r requirements.txt && \
    CVC5_URL="https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.0/cvc5-Linux-x86_64-static.zip" && \
    wget $CVC5_URL -O cvc5.zip && \
    unzip cvc5.zip && \
    cp cvc5-Linux-x86_64-static/bin/cvc5 /usr/local/bin && \
    chmod +x /usr/local/bin/cvc5 && \
    cvc5 --version && \
    rm -rf cvc5-Linux-x86_64-static cvc5.zip && \
    Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-4.8.6/z3-4.8.6-x64-ubuntu-16.04.zip" && \
    wget $Z3_URL -O z3.zip && \
    unzip z3.zip && \
    cp z3-4.8.6-x64-ubuntu-16.04/bin/z3 /usr/local/bin && \
    chmod +x /usr/local/bin/z3 && \
    z3 -version && \
    rm -rf z3-4.8.6-x64-ubuntu-16.04 z3.zip && \
    eval $(opam env) && \
    opam env >> /root/.bashrc

# Copy the other files
COPY . /Vecogen

# Run the bash file
CMD ["bash"]
