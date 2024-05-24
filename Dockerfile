FROM alpine:latest AS base

LABEL maintainer="boyland@uwm.edu"
LABEL version="1.0.0"

ARG SCALA_VERSION="2.13.12"
ARG BISON_VERSION="3.5.1"
ARG CLASSHOME="/usr/local"

WORKDIR /usr/lib/

# Install basics
RUN apk add --no-cache bash make flex gcompat gcc g++ openjdk11 build-base m4 git ncurses \
  && apk add --no-cache --virtual=build-dependencies wget ca-certificates

# Download Scala
RUN wget -q "https://downloads.lightbend.com/scala/${SCALA_VERSION}/scala-${SCALA_VERSION}.tgz" -O - | gunzip | tar x

ENV SCALAHOME="/usr/lib/scala-$SCALA_VERSION"
ENV PATH="$SCALAHOME/bin:$PATH"

# Build and install Bison
RUN wget -q "https://ftp.gnu.org/gnu/bison/bison-${BISON_VERSION}.tar.gz" -O - | gunzip | tar x \
  && cd "bison-${BISON_VERSION}" \
  && ./configure \
  && make \
  && make install

WORKDIR /usr/lib/aps

COPY . .

ENV APSHOME="/usr/lib/aps/bin"
ENV PATH="$APSHOME:$PATH"

RUN make
RUN cd base/scala && make aps-library.jar && make install
RUN cd examples/scala && make
RUN cd examples/scala/tests && make

WORKDIR /usr/local
