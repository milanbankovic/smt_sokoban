CXX = g++
CXXFLAGS = -std=c++17 -pthread -O3

all: generate_bv check_bv execute_parallel


generate_bv: generate_bv.cpp

check_bv: check_bv.cpp

execute_parallel: execute_parallel.cpp

clean:
	rm -f generate_bv
	rm -f check_bv
	rm -f execute_parallel
	rm -f *~
