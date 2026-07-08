FROM docker.io/rust:1.96 as cstb
WORKDIR /cstb
COPY . .
RUN cargo install --path .
CMD ["bash"]

FROM debian:trixie-slim
RUN apt-get update && rm -rf /var/lib/apt/lists/*
COPY --from=cstb /usr/local/cargo/bin/cstb /usr/local/bin/cstb
CMD ["bash"]
