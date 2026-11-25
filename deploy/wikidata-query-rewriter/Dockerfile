FROM maven:3.9-eclipse-temurin-11 AS build
RUN apt-get update && apt-get install -y --no-install-recommends git && rm -rf /var/lib/apt/lists/*
ARG REWRITER_REV=e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74
RUN git clone https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter.git /src && \
    git -C /src checkout --detach "$REWRITER_REV" && \
    mvn -B -f /src/java-rewriter/pom.xml package
FROM python:3.12-slim
RUN apt-get update && apt-get install -y --no-install-recommends openjdk-17-jre-headless && rm -rf /var/lib/apt/lists/* && useradd --system --uid 10001 app
WORKDIR /app
COPY --from=build /src/java-rewriter/target/sparql-rewriter.jar /app/sparql-rewriter.jar
COPY --from=build /src/LICENSE /app/UPSTREAM-LICENSE
COPY server.py /app/server.py
USER 10001
ENV PORT=8080
EXPOSE 8080
CMD ["python", "/app/server.py"]
