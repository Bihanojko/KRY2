# Project 2 - Implementation and breaking of RSA cipher
# Cryptography
# Nikola Valesova, xvales02

CC=g++
CCFLAGS=-std=c++11 -Wextra -Wall -pedantic -lgmpxx -lgmp -O3

all:
	$(CC) $(CCFLAGS) kry.cpp -o kry

clean:
	rm -f kry
