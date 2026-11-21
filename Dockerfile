# Mech Royale bot. Runs with no network, read-only root (writable /tmp), 1 CPU, 512 MB, map at /arena.
FROM oven/bun:1.4.4-slim
WORKDIR /bot
COPY src ./src
COPY arena ./arena
COPY params.json package.json ./
ENTRYPOINT ["bun", "/bot/src/main.ts"]
