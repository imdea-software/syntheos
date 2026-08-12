# syntax=docker/dockerfile:1
FROM rust:1-slim-bookworm AS builder
RUN apt-get update && apt-get install -y --no-install-recommends \
    libz3-dev clang \
    && rm -rf /var/lib/apt/lists/*
WORKDIR /app
COPY Cargo.toml Cargo.lock build.rs ./
COPY src ./src
RUN cargo build --release

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends libz3-4 \
    && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/rust_shield /usr/local/bin/rust_shield
ENTRYPOINT ["rust_shield"]
