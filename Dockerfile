FROM docker.io/rust:1.96 as cstb
WORKDIR /cstb
COPY . .
RUN cargo install --path .

FROM docker.io/haskell:9.4.8 as freest
RUN git clone https://github.com/freest-lang/freest.git
WORKDIR /freest
ENV GHC_NO_UNICODE=1
RUN stack build --system-ghc
RUN mkdir -p /usr/local/bin
RUN mv "$(stack path --local-install-root --system-ghc)/bin" /usr/local/bin

FROM debian:trixie-slim
RUN apt-get update && apt-get -y install locales && rm -rf /var/lib/apt/lists/*
RUN sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && locale-gen
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8
COPY --from=cstb /usr/local/cargo/bin/cstb /usr/local/bin/cstb
COPY --from=cstb /cstb/examples /examples
COPY --from=freest /usr/local/bin .
COPY --from=freest /freest/.stack-work /freest/.stack-work
CMD ["bash"]
