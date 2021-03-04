#include <iostream>
#include <vector>
#include <string>
#include <cstdlib>
#include <thread>
#include <atomic>
#include <chrono>
#include <fstream>

extern "C" {

#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
}

bool solved = false;
std::atomic_uint next = 0;
std::string input_file;
unsigned length_limit;
unsigned time_limit;
std::chrono::time_point<std::chrono::system_clock> start_time;

void run(unsigned i)
{
  while(!solved)
    {
      unsigned k = next++;
      if(k > length_limit)
	return;

      std::cerr << "Length: " << k << std::endl;

      std::string smt2_file = input_file + std::string("_") + std::to_string(k) + std::string(".smt2");
      std::string out_file = input_file + std::string("_") + std::to_string(k) + std::string(".out");
      std::string moves_file = input_file + std::string("_") + std::to_string(k) + std::string(".moves");
      std::string res_file = input_file + std::string("_") + std::to_string(k) + std::string(".res");

      std::chrono::time_point<std::chrono::system_clock> instance_start_time = std::chrono::system_clock::now();
      
      std::string command = std::string("./generate_bv ") +
	input_file +
	std::string(" ") +
	smt2_file +
	std::string(" ") + 
	std::to_string(k) +
	std::string(" 2> /dev/null");

      system(command.c_str());

      command = std::string("./z3 -T:") + std::to_string(time_limit) + std::string(" ") +  
	smt2_file +
	std::string(" > ") + 
	out_file +
	std::string(" 2> /dev/null");

      system(command.c_str());

      command = std::string("grep unsat ") +
	out_file +
	std::string(" > /dev/null");
      
      int retval = system(command.c_str());

      if(WEXITSTATUS(retval) == 0)
	{
	  std::cout << "No plan of length " << k << std::endl;       	  
	}
      else
	{
	  command = std::string("grep timeout ") +
	    out_file +
	    std::string(" > /dev/null");

	  retval = system(command.c_str());
	  if(WEXITSTATUS(retval) == 0)
	    {
	      std::cout << "Time limit exceeded for length " << k << std::endl;
	    }
	  else
	    {
	      solved = true;
	      std::cout << "SUCCESS: Found plan of length: " << k << std::endl;
	      std::cout << "Verifying solution..." << std::endl;
	      command = std::string("cat ") +
		out_file +
		std::string(" | grep -o -E '#b[0-1][0-1][0-1]?' > ") +
		moves_file;
	      system(command.c_str());
	      command = std::string("./check_bv ") +
		input_file +
		std::string(" ") +
		moves_file +
		std::string(" > ") +
		res_file;
	      system(command.c_str());

	      std::chrono::duration<double, std::ratio<1>> instance_time = std::chrono::system_clock::now() - instance_start_time;
	      std::chrono::duration<double, std::ratio<1>> cumulative_time = std::chrono::system_clock::now() - start_time;

	      std::ofstream ostr(res_file, std::ios_base::app);

	      if(ostr)
		{
		  ostr << std::endl;
		  ostr << "Instance time for length " << k << ": " << instance_time.count() << "s" << std::endl;
		  ostr << "Cumulative time for length " << k << ": " << cumulative_time.count() << "s" << std::endl;
		}

	      ostr.close();
	      std::cout << "Instance time for length " << k << ": " << instance_time.count() << "s" << std::endl;
	      std::cout << "Cumulative time for length " << k << ": " << cumulative_time.count() << "s" <<  std::endl;  
	    }
	}
      unlink(smt2_file.c_str());
      unlink(out_file.c_str());
      unlink(moves_file.c_str());
    }
}

int main(int argc, char ** argv)
{
  if(argc < 5)
    {
      std::cerr << "usage: " << argv[0] << " input_file length_limit time_limit num_of_threads" << std::endl;
      exit(1);
    }


  input_file = std::string(argv[1]);
  length_limit = atoi(argv[2]);
  time_limit = atoi(argv[3]);
  unsigned num_of_threads = atoi(argv[4]);

  
  std::vector<std::thread> threads;

  start_time = std::chrono::system_clock::now();
  
  for(unsigned i = 0; i < num_of_threads; i++)
    threads.push_back(std::thread(run, i));

  for(auto & th : threads)
    th.join();
  
  return 0;
}
