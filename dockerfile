FROM debian:latest

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y \
    opam \
    m4 \
    bubblewrap \
    wget \
    curl \
    ca-certificates \
    git \
    rsync \
    patch \
    bzip2 \
    gcc \
    libc-dev \
    make \
    unzip \
    graphviz \
    mccs \
    libcairo2-dev \
    libexpat1-dev \
    libgmp-dev \
    libgtk-3-dev \
    libgtksourceview-3.0-dev \
    pkg-config \
    zlib1g-dev \
    python3 \
    python3-venv \
    python3-pip \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /Vecogen

COPY requirements.txt /Vecogen/requirements.txt

RUN opam init -y --disable-sandboxing && \
    opam update && \
    opam switch create 4.14.2 ocaml-base-compiler.4.14.2 && \
    eval $(opam env --switch=4.14.2) && \
    opam install -y opam-depext && \
    opam depext --install -y frama-c.32.0 && \
    opam install -y frama-c.32.0 && \
    frama-c -version && \
    opam env --switch=4.14.2 >> /etc/bash.bashrc

RUN python3 -m venv /Vecogen/venv && \
    /Vecogen/venv/bin/pip install --upgrade pip && \
    /Vecogen/venv/bin/pip install -r /Vecogen/requirements.txt

RUN CVC5_URL="https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.3/cvc5-Linux-x86_64-static.zip" && \
    wget "$CVC5_URL" -O cvc5.zip && \
    unzip cvc5.zip && \
    cp cvc5-Linux-x86_64-static/bin/cvc5 /usr/local/bin/cvc5 && \
    chmod +x /usr/local/bin/cvc5 && \
    cvc5 --version && \
    rm -rf cvc5-Linux-x86_64-static cvc5.zip

RUN Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-4.15.3/z3-4.15.3-x64-glibc-2.39.zip" && \
    curl -L "$Z3_URL" -o z3.zip && \
    unzip z3.zip && \
    cp z3-4.15.3-x64-glibc-2.39/bin/z3 /usr/local/bin/z3 && \
    chmod +x /usr/local/bin/z3 && \
    z3 --version && \
    rm -rf z3-4.15.3-x64-glibc-2.39 z3.zip

RUN YICES_VERSION="2.7.0" && \
    YICES_URL="https://github.com/SRI-CSL/yices2/releases/download/yices-${YICES_VERSION}/yices-${YICES_VERSION}-x86_64-pc-linux-gnu-static-gmp.tar.gz" && \
    wget "$YICES_URL" -O yices.tar.gz && \
    tar -xzf yices.tar.gz && \
    cp yices-${YICES_VERSION}/bin/yices* /usr/local/bin/ && \
    chmod +x /usr/local/bin/yices* && \
    yices-smt2 --version && \
    rm -rf yices-${YICES_VERSION} yices.tar.gz

RUN eval $(opam env --switch=4.14.2) && \
    why3 config detect && \
    why3 config list-provers

RUN yices-smt2 --version && \
    z3 --version && \
    cvc5 --version

COPY . /Vecogen

VOLUME /run
VOLUME /tmp

CMD ["bash"]