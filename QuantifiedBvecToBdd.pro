TEMPLATE = app
CONFIG += console
CONFIG -= app_bundle
CONFIG -= qt
CONFIG += c++11

SOURCES += main.cpp \
    ExprToBDDTransformer.cpp \
    UnionFind.cpp \
    VariableOrderer.cpp \
    ExprSimplifier.cpp

HEADERS += \
    ExprToBDDTransformer.h \
    VariableOrderer.h \
    ExprSimplifier.h

LIBS += -lz3
#INCLUDEPATH += /usr/local/lib
LIBS += /usr/local/lib/libbdd.a
