#include <iostream>
#include <fstream>
#include <cstdlib>
#include <vector>
#include <string>


#define MOVE_UP 0
#define MOVE_DOWN 1
#define MOVE_LEFT 2
#define MOVE_RIGHT 3
#define MOVE_STAY 4

#define MOVE_MIN 0
#define MOVE_MAX 4

struct board {
  unsigned row_count;
  unsigned col_count;
  std::vector<bool> wall;
  std::vector<bool> box;
  std::vector<bool> home;
  unsigned x_sokoban;
  unsigned y_sokoban;
  unsigned box_count;
  
  unsigned pair_to_index(unsigned i, unsigned j) const
  {
    return i*col_count + j;
  }
  
};

std::istream & operator >> (std::istream & istr, board & brd)
{
  unsigned m, n;
  istr >> m >> n;
  if(!istr)
    return istr;

  brd.row_count = m;
  brd.col_count = n;
  brd.box_count = 0;
  
  istr >> std::noskipws;
  brd.wall.resize(m*n);
  brd.box.resize(m*n);
  brd.home.resize(m*n);
  
  char c;
  do {
    istr >> c;
  } while(c != '\n');
  
  for(unsigned i = 0; i < m; i++)
    {
      bool eofl = false;
      for(unsigned j = 0; j < n; j++)
      {
	if(!eofl)
	  istr >> c;
	if(c == '\n')
	  {
	    eofl = true;
	    c = ' ';
	  }

	switch(c)
	  {
	  case '#':
	    brd.wall[brd.pair_to_index(i,j)] = true;
	    break;
	  case 'o':
	    brd.home[brd.pair_to_index(i,j)] = true;
	    break;
	  case 'b':
	    brd.box[brd.pair_to_index(i,j)] = true;
	    brd.box_count++;
	    break;
	  case 's':
	    brd.x_sokoban = j;
	    brd.y_sokoban = i;
	    break;
	  case 'S':
	    brd.x_sokoban = j;
	    brd.y_sokoban = i;
	    brd.home[brd.pair_to_index(i,j)] = true;
	    break;
	  case 'B':
	    brd.home[brd.pair_to_index(i,j)] = true;
	    brd.box[brd.pair_to_index(i,j)] = true;
	    brd.box_count++;
	  }
      }

      if(eofl)
	continue;
      
      do {	
	istr >> c;
      } while (c != '\n');
    }
  return istr;
}


std::ostream & operator << (std::ostream & ostr, const board & brd)
{
  unsigned m = brd.row_count, n = brd.col_count;
  for(unsigned i = 0; i < m ; i++)
    {
      for(unsigned j = 0; j < n; j++)
	{
	  if(brd.wall[brd.pair_to_index(i,j)])
	    ostr << "#";
	  else if(brd.box[brd.pair_to_index(i,j)])
	    {
	      if(brd.home[brd.pair_to_index(i,j)])
		ostr << "B";
	      else
		ostr << "b";
	    }
	  else if(brd.x_sokoban == j && brd.y_sokoban == i)
	    {
	      if(brd.home[brd.pair_to_index(i,j)])
		ostr << "S";
	      else
		ostr << "s";
	    }
	  else if(brd.home[brd.pair_to_index(i,j)])
	    ostr << "o";
	  else
	    ostr << " ";
	}
      ostr << std::endl;
    }
  return ostr;
}

void read_moves(std::istream & istr, std::vector<unsigned> & moves)
{
  std::string s;
  while(istr >> s)
    {
      if(s == "#b00" || s == "#b000")	
	moves.push_back(MOVE_UP);
      else if(s == "#b01" || s == "#b001")
	moves.push_back(MOVE_DOWN);
      else if(s == "#b10" || s == "#b010")
	moves.push_back(MOVE_LEFT);
      else if(s == "#b11" || s == "#b011")
	moves.push_back(MOVE_RIGHT);
      else if(s == "#b100")
	moves.push_back(MOVE_STAY);
      else
	std::cerr << "ERROR: UNDEFINED MOVE: " << s << std::endl;
    }  
}

void print_moves(std::ostream & ostr, const std::vector<unsigned> & moves)
{
  for(auto move : moves)
    ostr << move << " ";
  ostr << std::endl;
}

bool check_plan(board & brd, const std::vector<unsigned> & moves)
{
  for(unsigned k = 0; k < moves.size(); k++)
    {
      if(moves[k] == MOVE_UP)
	{
	  if(brd.y_sokoban == 0)
	    return false;

	  if(brd.wall[brd.pair_to_index(brd.y_sokoban - 1, brd.x_sokoban)] == true)
	    return false;

	  if(brd.box[brd.pair_to_index(brd.y_sokoban - 1, brd.x_sokoban)] == true &&
	     (brd.y_sokoban == 1 ||
	      brd.wall[brd.pair_to_index(brd.y_sokoban - 2, brd.x_sokoban)] == true ||
	      brd.box[brd.pair_to_index(brd.y_sokoban - 2, brd.x_sokoban)] == true))
	    return false;

	  if(brd.box[brd.pair_to_index(brd.y_sokoban - 1, brd.x_sokoban)] == true)
	    {
	      brd.box[brd.pair_to_index(brd.y_sokoban - 2, brd.x_sokoban)] = true;
	      brd.box[brd.pair_to_index(brd.y_sokoban - 1, brd.x_sokoban)] = false;
	    }
	  brd.y_sokoban--;
	}
      else if(moves[k] == MOVE_DOWN)
	{
	  if(brd.y_sokoban == brd.row_count - 1)
	    return false;

	  if(brd.wall[brd.pair_to_index(brd.y_sokoban + 1, brd.x_sokoban)] == true)
	    return false;

	  if(brd.box[brd.pair_to_index(brd.y_sokoban + 1, brd.x_sokoban)] == true &&
	     (brd.y_sokoban == brd.row_count - 2 ||
	      brd.wall[brd.pair_to_index(brd.y_sokoban + 2, brd.x_sokoban)] == true ||
	      brd.box[brd.pair_to_index(brd.y_sokoban + 2, brd.x_sokoban)] == true))
	    return false;

	  if(brd.box[brd.pair_to_index(brd.y_sokoban + 1, brd.x_sokoban)] == true)
	    {
	      brd.box[brd.pair_to_index(brd.y_sokoban + 2, brd.x_sokoban)] = true;
	      brd.box[brd.pair_to_index(brd.y_sokoban + 1, brd.x_sokoban)] = false;
	    }
	  brd.y_sokoban++;
	}
      else if(moves[k] == MOVE_LEFT)
	{
	  if(brd.x_sokoban == 0)
	    return false;

	  if(brd.wall[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban - 1)] == true)
	    return false;

	  if(brd.box[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban - 1)] == true &&
	     (brd.x_sokoban == 1 ||
	      brd.wall[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban - 2)] == true ||
	      brd.box[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban - 2)] == true))
	    return false;

	  if(brd.box[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban - 1)] == true)
	    {
	      brd.box[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban - 2)] = true;
	      brd.box[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban - 1)] = false;
	    }
	  brd.x_sokoban--;
	}
      else if(moves[k] == MOVE_RIGHT)
	{
	  if(brd.x_sokoban == brd.col_count - 1)
	    return false;

	  if(brd.wall[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban + 1)] == true)
	    return false;

	  if(brd.box[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban + 1)] == true &&
	     (brd.x_sokoban == brd.col_count - 2 ||
	      brd.wall[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban + 2)] == true ||
	      brd.box[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban + 2)] == true))
	    return false;

	  if(brd.box[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban + 1)] == true)
	    {
	      brd.box[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban + 2)] = true;
	      brd.box[brd.pair_to_index(brd.y_sokoban, brd.x_sokoban + 1)] = false;
	    }
	  brd.x_sokoban++;
	}
      else if(moves[k] == MOVE_STAY)
	{
	  // DO NOTHING
	}
      else
	{
	  std::cerr << "UNRECOGNIZED MOVE: " << moves[k] << std::endl;
	  return false;
	}
      std::cout << "TABLE AFTER " << k + 1 << " MOVES: " << std::endl;
      std::cout << brd << std::endl;
    }

  for(unsigned i = 0; i < brd.row_count; i++)
    for(unsigned j = 0; j < brd.col_count; j++)
      if(brd.home[brd.pair_to_index(i, j)] != brd.box[brd.pair_to_index(i,j)])
	return false;
  
  return true;
}

int main(int argc, char ** argv)
{
  if(argc < 3)
    {
      std::cerr << "usage:"
		<< argv[0]
		<< " input_file moves_file"
		<< std::endl;
      exit(0);
    }

  std::ifstream istr(argv[1]);
  
  if(!istr)
    {
      std::cerr << "Cannot open input file " << argv[1] << std::endl;
      exit(1);
    }
  
  board brd;
  
  istr >> brd;

  istr.close();

  std::cout << brd << std::endl;

  std::ifstream moves_file(argv[2]);

  if(!moves_file)
    {
      std::cerr << "Cannot open moves file " << argv[2] << std::endl;
    }

  std::vector<unsigned> moves;
  read_moves(moves_file, moves);
  print_moves(std::cout, moves);
  
  if(check_plan(brd, moves))
    {
      std::cerr << "PLAN OK" << std::endl;
    }
  else
    {
      std::cerr << "PLAN FAILED" << std::endl;
    }
  
  
  return 0;
}
