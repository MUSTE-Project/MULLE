FROM debian:testing-slim

RUN apt-get update \
 && apt-get install -y \
    libcurl4-gnutls-dev \
    libz-dev \
    haskell-stack \
    cabal-install \
    make \
    git \
 && rm -rf /var/lib/apt/lists/*

# Build app
COPY . /app
WORKDIR /app
ENV PATH=$PATH:/root/.local/bin
ENV LC_ALL=C.UTF-8
RUN ln -s stack-lts-12.yaml stack.yaml
RUN stack install muste-ajax
RUN cabal update
RUN cabal install gf
RUN git clone https://github.com/GrammaticalFramework/gf-rgl
WORKDIR /app/gf-rgl
RUN make 
RUN make install
WORKDIR /app
RUN make -C examples/grammars/exemplum/
RUN make -C examples/grammars/programming/

EXPOSE 8080
CMD ["muste-ajax", "-c", "/app/examples/config.yaml", "--recreate-db"]
