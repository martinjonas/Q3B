FROM centos:7

RUN yum makecache
RUN yum -y upgrade
RUN ulimit -n 1024 && yum -y install python3 autotools-dev automake make wget unzip git libuuid-devel
RUN ulimit -n 1024 && yum -y install centos-release-scl
RUN ulimit -n 1024 && yum -y install devtoolset-7-gcc*

RUN wget https://download.oracle.com/java/17/latest/jdk-17_linux-x64_bin.rpm
RUN ulimit -n 1024 && yum -y install ./jdk-17_linux-x64_bin.rpm

RUN wget https://cmake.org/files/v3.12/cmake-3.12.3.tar.gz
RUN tar zxvf cmake-3.*
RUN source scl_source enable devtoolset-7 && cd cmake-3.* && ./bootstrap --prefix=/usr/local && make -j$(nproc) && make install

RUN wget https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.11.2.tar.gz
RUN tar -xzvf z3-4.11.2.tar.gz
RUN source scl_source enable devtoolset-7 && cd z3-z3-4.11.2/ && mkdir build && cd build && cmake .. -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_LIBZ3_SHARED=False && make -j$(nproc) && make install

RUN git clone https://github.com/martinjonas/cudd.git
RUN source scl_source enable devtoolset-7 && cd cudd && ./configure --enable-silent-rules --enable-obj --enable-shared && make -j$(nproc) && make install

RUN wget https://www.antlr.org/download/antlr-4.9.3-complete.jar -P /usr/share/java

RUN mkdir Q3B
COPY . Q3B
WORKDIR Q3B/build

RUN source scl_source enable devtoolset-7 && cmake .. -DANTLR_EXECUTABLE=/usr/share/java/antlr-4.9.3-complete.jar
RUN source scl_source enable devtoolset-7 && make
RUN make test

ENTRYPOINT bash
