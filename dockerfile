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
    python3-pip


# Initialize OPAM (OCaml Package Manager) and install OCaml
RUN opam init -y --disable-sandboxing && \
    opam update && \
    opam switch create 4.14.1 && \
    opam switch 4.14.1 && \
    eval $(opam env)

 # Allow installing stuff to system Python.
RUN rm -f /usr/lib/python3.11/EXTERNALLY-MANAGED

# Upgrade pip to latest version.
RUN pip3 install --upgrade pip

COPY requirements.txt /Vecogen/requirements.txt
WORKDIR /Vecogen
RUN pip3 install -r requirements.txt
COPY . /Vecogen

RUN eval $(opam env)
RUN opam install -y opam-depext
RUN opam depext --install -y frama-c


# Run the bash file
# ./solvers.sh && 
CMD ["bash"]
