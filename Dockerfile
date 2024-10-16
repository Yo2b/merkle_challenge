FROM rust:1.81-alpine AS builder

WORKDIR /usr/src/app

COPY . .

RUN apk add --no-cache musl-dev
RUN cargo build --release --workspace

FROM debian:buster-slim

WORKDIR /usr/src/app

COPY --from=builder /usr/src/app/target/release/mock .

CMD ["./mock"]
