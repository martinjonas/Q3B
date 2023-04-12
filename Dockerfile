FROM ubuntu

RUN apt-get update
RUN apt-get install -y g++ autotools-dev automake wget unzip git make cmake default-jre pkg-config
RUN apt-get update
RUN apt-get install uuid-dev

RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.11.2/z3-4.11.2-x64-glibc-2.31.zip
RUN unzip z3-4.11.2-x64-glibc-2.31.zip
RUN cp z3-4.11.2-x64-glibc-2.31/bin/libz3.a /usr/lib
RUN cp z3-4.11.2-x64-glibc-2.31/include/* /usr/include

RUN git clone -b 3val https://github.com/martinjonas/cudd.git
RUN cd cudd && ./configure --enable-silent-rules --enable-obj --enable-shared && make -j4 && make install

RUN wget https://www.antlr.org/download/antlr-4.11.1-complete.jar -P /usr/share/java

RUN mkdir Q3B
COPY . Q3B
WORKDIR Q3B
RUN cmake -B build -DANTLR_EXECUTABLE=/usr/share/java/antlr-4.11.1-complete.jar
RUN cmake --build build -j4
RUN cd build && make test

ENTRYPOINT bash
