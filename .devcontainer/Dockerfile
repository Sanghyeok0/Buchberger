FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
       latexmk \
       texlive-binaries \
       texlive-latex-base \
       texlive-latex-extra \
       texlive-fonts-recommended \
       texlive-bibtex-extra \
       texlive-science \
       zip \
    && rm -rf /var/lib/apt/lists/*
