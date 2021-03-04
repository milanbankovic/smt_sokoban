#include <iostream>
#include <fstream>
#include <cstdlib>
#include <vector>
#include <string>


#define MOVE_UP 0
#define MOVE_DOWN 1
#define MOVE_LEFT 2
#define MOVE_RIGHT 3

#ifdef _ENABLE_STAY
#define MOVE_STAY 4
#endif

#define MOVE_MIN 0

#ifdef _ENABLE_STAY
#define MOVE_MAX 4
#else
#define MOVE_MAX 3
#endif

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

  std::string pair_to_index_str(unsigned k, int x_off, int y_off) const
  {
    std::string y;
    if(y_off > 0)
      y = std::string("(+ y_") + std::to_string(k) + std::string(" ") + std::to_string(y_off) + std::string(")");
    else if(y_off < 0)
      y = std::string("(- y_") + std::to_string(k) + std::string(" ") + std::to_string(std::abs(y_off)) + std::string(")");
    else
      y = std::string("y_") + std::to_string(k);

    std::string x;
    if(x_off > 0)
      x = std::string("(+ x_") + std::to_string(k) + std::string(" ") + std::to_string(x_off) + std::string(")");
    else if(x_off < 0)
      x = std::string("(- x_") + std::to_string(k) + std::string(" ") + std::to_string(std::abs(x_off)) + std::string(")");
    else
      x = std::string("x_") + std::to_string(k);

    return std::string("(+ (* ") + std::to_string(col_count) + std::string(" ") + y + std::string(") ") + x + std::string(")");
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


void generate_output(const board & brd,
		     unsigned plan_length,
		     std::ostream & ostr)
{
  ostr << "(set-option :print-success false)" << std::endl;
  ostr << "(set-option :produce-models true)" << std::endl;
  ostr << "(set-logic QF_AUFLIA)" << std::endl;
  ostr << "(declare-const wall (Array Int Int))" << std::endl;
  ostr << "(declare-const home (Array Int Int))" << std::endl;

  for(unsigned i = 0; i <= plan_length; i++)
    {      
      ostr << "(declare-const box_" << i << " (Array Int Int))" << std::endl;
      ostr << "(declare-const x_" << i << " Int)" << std::endl;
      ostr << "(declare-const y_" << i << " Int)" << std::endl;
    }

for(unsigned i = 1; i <= plan_length; i++)
  {
    ostr << "(declare-const move_" << i << " Int)" << std::endl;
  }
  
  // ASSERT INITIAL STATE
  for(unsigned i = 0; i < brd.row_count; i++)
    for(unsigned j = 0; j < brd.col_count; j++)
      {
	ostr << "(assert (= (select wall " << brd.pair_to_index(i, j) << ") " << (brd.wall[brd.pair_to_index(i, j)] ? 1 : 0) << "))" << std::endl;
      }

  for(unsigned i = 0; i < brd.row_count; i++)
    for(unsigned j = 0; j < brd.col_count; j++)
      {
	ostr << "(assert (= (select home " << brd.pair_to_index(i, j) << ") " << (brd.home[brd.pair_to_index(i, j)] ? 1 : 0) << "))" << std::endl;
      }

  for(unsigned i = 0; i < brd.row_count; i++)
    for(unsigned j = 0; j < brd.col_count; j++)
      {
	ostr << "(assert (= (select box_0 " << brd.pair_to_index(i, j) << ") " << (brd.box[brd.pair_to_index(i, j)] ? 1 : 0) << "))" << std::endl;
      }

  ostr << "(assert (= x_0 " << brd.x_sokoban << "))" << std::endl;
  ostr << "(assert (= y_0 " << brd.y_sokoban << "))" << std::endl;

  // ASSERT TRANSITIONS
  for(unsigned k = 0; k < plan_length; k++)
    {
      ostr << "(assert (and (>= move_" << k+1 << " " << MOVE_MIN << ") (<= move_" << k+1 << " " << MOVE_MAX << ")))" << std::endl;

#ifdef _ENABLE_STAY
      // NON-STAY PRECONDITIONS
      ostr << "(assert" << std::endl
	   << " (=> (distinct move_" << k+1 << " " << MOVE_STAY << ")" << std::endl
	   << "     (distinct box_" << k << " home)" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;
#else
      ostr << "(assert (distinct box_" << k << " home))" << std::endl;
#endif
      
      // UP PRECONDITIONS
      ostr << "(assert"  << std::endl
           << " (=> (= move_" << k+1 << " " << MOVE_UP << ")"  << std::endl
	   << "  (and (> y_" << k << " 0)"  << std::endl
	   << "       (= (select wall " << brd.pair_to_index_str(k, 0, -1) << ") 0)"  << std::endl
	   << "       (or (= (select box_" << k << " " << brd.pair_to_index_str(k, 0, -1) << ") 0)"  << std::endl
	   << "           (and (> y_" << k << " 1)"  << std::endl
	   << "                (= (select box_" << k << " " << brd.pair_to_index_str(k, 0, -2) << ") 0)" << std::endl
	   << "                (= (select wall " << brd.pair_to_index_str(k, 0, -2) << ") 0)" << std::endl
	   << "           )"  << std::endl
	   << "       )"  << std::endl 
	   << "  )"  << std::endl 
	   << " )"  << std::endl 
	   << ")" << std::endl;
      
      // UP EFFECTS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " " << MOVE_UP << ")"  << std::endl
	   << "  (and (= y_" << k+1 << " (- y_" << k << " 1))" << std::endl 
	   << "       (= x_" << k+1 << " x_" << k << ")" << std::endl
	   << "       (=> (= (select box_" << k << " " << brd.pair_to_index_str(k, 0, -1) << ") 0)" << std::endl
	   << "           (= box_" << k+1 << " box_" << k << ")" << std::endl
	   << "       )" << std::endl
	   << "       (=> (= (select box_" << k << " " << brd.pair_to_index_str(k, 0, -1) << ") 1)" << std::endl
	   << "           (= box_" << k+1 << " (store (store box_" << k << " " << brd.pair_to_index_str(k, 0, -1) << " 0) " << brd.pair_to_index_str(k, 0, -2) << " 1))" << std::endl
	   << "       )" << std::endl
	   << "  )" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;

      
      // DOWN PRECONDTIONS
      ostr << "(assert"  << std::endl
           << " (=> (= move_" << k+1 << " " << MOVE_DOWN << ")"  << std::endl
	   << "  (and (< y_" << k << " " << brd.row_count-1 << ")"  << std::endl
	   << "       (= (select wall " << brd.pair_to_index_str(k, 0, 1) << ") 0)"  << std::endl
	   << "       (or (= (select box_" << k << " " << brd.pair_to_index_str(k, 0, 1) << ") 0)"  << std::endl
	   << "           (and (< y_" << k << " " << brd.row_count - 2 << ")"  << std::endl
	   << "                (= (select box_" << k << " " << brd.pair_to_index_str(k, 0, 2) << ") 0)" << std::endl
	   << "                (= (select wall " << brd.pair_to_index_str(k, 0, 2) << ") 0)" << std::endl
	   << "           )"  << std::endl
	   << "       )"  << std::endl 
	   << "  )"  << std::endl 
	   << " )"  << std::endl 
	   << ")" << std::endl;


      
      // DOWN EFFECTS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " " << MOVE_DOWN << ")"  << std::endl
	   << "  (and (= y_" << k+1 << " (+ y_" << k << " 1))" << std::endl 
	   << "       (= x_" << k+1 << " x_" << k << ")" << std::endl
	   << "       (=> (= (select box_" << k << " " << brd.pair_to_index_str(k, 0, 1) << ") 0)" << std::endl
	   << "           (= box_" << k+1 << " box_" << k << ")" << std::endl
	   << "       )" << std::endl
	   << "       (=> (= (select box_" << k << " " << brd.pair_to_index_str(k, 0, 1) << ") 1)" << std::endl
	   << "           (= box_" << k+1 << " (store (store box_" << k << " " << brd.pair_to_index_str(k, 0, 1) << " 0) " << brd.pair_to_index_str(k, 0, 2) << " 1))" << std::endl
	   << "       )" << std::endl
	   << "  )" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;

      
      // LEFT PRECONDITIONS
      ostr << "(assert"  << std::endl
           << " (=> (= move_" << k+1 << " " << MOVE_LEFT << ")"  << std::endl
	   << "  (and (> x_" << k << " 0)"  << std::endl
	   << "       (= (select wall " << brd.pair_to_index_str(k, -1, 0) << ") 0)"  << std::endl
	   << "       (or (= (select box_" << k << " " << brd.pair_to_index_str(k, -1, 0) << ") 0)"  << std::endl
	   << "           (and (> x_" << k << " 1)"  << std::endl
	   << "                (= (select box_" << k << " " << brd.pair_to_index_str(k, -2, 0) << ") 0)" << std::endl
	   << "                (= (select wall " << brd.pair_to_index_str(k, -2, 0) << ") 0)" << std::endl
	   << "           )"  << std::endl
	   << "       )"  << std::endl 
	   << "  )"  << std::endl 
	   << " )"  << std::endl 
	   << ")" << std::endl;
      
      // LEFT EFFECTS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " " << MOVE_LEFT << ")"  << std::endl
	   << "  (and (= x_" << k+1 << " (- x_" << k << " 1))" << std::endl 
	   << "       (= y_" << k+1 << " y_" << k << ")" << std::endl
	   << "       (=> (= (select box_" << k << " " << brd.pair_to_index_str(k, -1, 0) << ") 0)" << std::endl
	   << "           (= box_" << k+1 << " box_" << k << ")" << std::endl
	   << "       )" << std::endl
	   << "       (=> (= (select box_" << k << " " << brd.pair_to_index_str(k, -1, 0) << ") 1)" << std::endl
	   << "           (= box_" << k+1 << " (store (store box_" << k << " " << brd.pair_to_index_str(k, -1, 0) << " 0) " << brd.pair_to_index_str(k, -2, 0) << " 1))" << std::endl
	   << "       )" << std::endl
	   << "  )" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;
						       
      
      // RIGHT PRECONDITIONS
      ostr << "(assert"  << std::endl
           << " (=> (= move_" << k+1 << " " << MOVE_RIGHT << ")"  << std::endl
	   << "  (and (< x_" << k << " " << brd.col_count-1 << ")"  << std::endl
	   << "       (= (select wall " << brd.pair_to_index_str(k, 1, 0) << ") 0)"  << std::endl
	   << "       (or (= (select box_" << k << " " << brd.pair_to_index_str(k, 1, 0) << ") 0)"  << std::endl
	   << "           (and (< x_" << k << " " << brd.col_count - 2 << ")"  << std::endl
	   << "                (= (select box_" << k << " " << brd.pair_to_index_str(k, 2, 0) << ") 0)" << std::endl
	   << "                (= (select wall " << brd.pair_to_index_str(k, 2, 0) << ") 0)" << std::endl
	   << "           )"  << std::endl
	   << "       )"  << std::endl 
	   << "  )"  << std::endl 
	   << " )"  << std::endl 
	   << ")" << std::endl;

      // RIGHT EFFECTS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " " << MOVE_RIGHT << ")"  << std::endl
	   << "  (and (= x_" << k+1 << " (+ x_" << k << " 1))" << std::endl 
	   << "       (= y_" << k+1 << " y_" << k << ")" << std::endl
	   << "       (=> (= (select box_" << k << " " << brd.pair_to_index_str(k, 1, 0) << ") 0)" << std::endl
	   << "           (= box_" << k+1 << " box_" << k << ")" << std::endl
	   << "       )" << std::endl
	   << "       (=> (= (select box_" << k << " " << brd.pair_to_index_str(k, 1, 0) << ") 1)" << std::endl
	   << "           (= box_" << k+1 << " (store (store box_" << k << " " << brd.pair_to_index_str(k, 1, 0) << " 0) " << brd.pair_to_index_str(k, 2, 0) << " 1))" << std::endl
	   << "       )" << std::endl
	   << "  )" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;

#ifdef _ENABLE_STAY
      // STAY PRECONDITIONS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " " << MOVE_STAY << ")" << std::endl
	   << "     (= box_" << k << " home)" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;
      
      // STAY EFFECTS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " "  << MOVE_STAY << ")" << std::endl
	   << "   (and" << std::endl
	   << "      (= box_" << k + 1 << " box_" << k << ")" << std::endl
	   << "      (= x_" << k + 1 << " x_" << k << ")" << std::endl
	   << "      (= y_" << k + 1 << " y_" << k << ")" << std::endl
	   << "   )" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;	  
#endif
      
      // CYCLIC-AVOIDANCE
      for(unsigned s = 0; s <= k; s++)
	{
	  ostr << "(assert" << std::endl
	       << "  (or" << std::endl
#ifdef _ENABLE_STAY
	       << "    (= move_" << k+1 << " " << MOVE_STAY << ")" << std::endl
#endif
	       << "    (distinct x_" << k+1 << " x_" << s << ")" << std::endl
	       << "    (distinct y_" << k+1 << " y_" << s << ")" << std::endl
	       << "    (distinct box_" << k+1 << " box_" << s << ")" << std::endl
	       << "  )" << std::endl
	       << ")" << std::endl;	  
	}

#ifndef _DISABLE_INVARIANT
      // INVARIANT (NUMBER OF BOXES DOES NOT CHANGE)
      ostr << "(assert (= " << brd.box_count << " (+ ";
      for(unsigned i = 0; i < brd.row_count; i++)
	for(unsigned j = 0; j < brd.col_count; j++)
	  ostr << "(select box_" << k+1 << " " << brd.pair_to_index(i, j) << ") ";
      ostr << ")))" << std::endl;

      ostr << "(assert (and (>= x_" << k+1 << " " << 0 << ") (<= x_" << k+1 << " " << brd.col_count-1 << ")))" << std::endl;
      ostr << "(assert (and (>= y_" << k+1 << " " << 0 << ") (<= y_" << k+1 << " " << brd.row_count-1 << ")))" << std::endl;
#endif
    }

    // ASSERT GOAL STATE
  ostr << "(assert (= box_" << plan_length << " home))" << std::endl;  
  ostr << "(check-sat)" << std::endl;

  for(unsigned i = 1; i <= plan_length; i++)
    ostr << "(get-value (move_" << i << "))" << std::endl;
  
  ostr << "(exit)" << std::endl;
}

int main(int argc, char ** argv)
{
  if(argc < 4)
    {
      std::cerr << "usage:"
		<< argv[0]
		<< " input_file output_file plan_length"
		<< std::endl;
      exit(0);
    }

  std::ifstream istr(argv[1]);
  
  if(!istr)
    {
      std::cerr << "Cannot open input file " << argv[1] << std::endl;
      exit(1);
    }

  std::ofstream ostr(argv[2]);

  if(!ostr)
    {
      std::cerr << "Cannot open output file " << argv[2] << std::endl;
    }
  
  board brd;
  
  istr >> brd;

  istr.close();

  std::cout << brd << std::endl;
  
  unsigned plan_length = atoi(argv[3]);

  generate_output(brd, plan_length, ostr);
  
  
  return 0;
}
