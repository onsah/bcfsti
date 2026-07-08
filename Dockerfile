FROM docker.io/rust:1.96

WORKDIR /cstb
COPY . .

RUN cargo install --path .

CMD ["bash"]
