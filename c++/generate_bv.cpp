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

std::string bv_const(unsigned x, unsigned size)
{
  return std::string("(_ bv") + std::to_string(x) + std::string(" ") + std::to_string(size) + std::string(")");
}

unsigned log_2(unsigned x)
{
  unsigned k = 0;
  while((1 << k) < x)
    k++;
  return k;
}

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
    unsigned x_size = log_2(col_count);
    unsigned y_size = log_2(row_count);
    unsigned ind_size = log_2(row_count * col_count);
    
    std::string y;
    if(y_off > 0)
      y = std::string("((_ zero_extend ") + std::to_string(ind_size - y_size) + std::string(") (bvadd y_") + std::to_string(k) + std::string(" ") + bv_const(y_off, y_size) + std::string("))");
    else if(y_off < 0)
      y = std::string("((_ zero_extend ") + std::to_string(ind_size - y_size) + std::string(") (bvsub y_") + std::to_string(k) + std::string(" ") + bv_const(std::abs(y_off), y_size) + std::string("))");
    else
      y = std::string("((_ zero_extend ") + std::to_string(ind_size - y_size) + std::string(") y_") + std::to_string(k) + std::string(")");

    std::string x;
    if(x_off > 0)
      x = std::string("((_ zero_extend ") + std::to_string(ind_size - x_size) + std::string(") (bvadd x_") + std::to_string(k) + std::string(" ") + bv_const(x_off, x_size) + std::string("))");
    else if(x_off < 0)
      x = std::string("((_ zero_extend ") + std::to_string(ind_size - x_size) + std::string(") (bvsub x_") + std::to_string(k) + std::string(" ") + bv_const(std::abs(x_off), x_size) + std::string("))");
    else
      x = std::string("((_ zero_extend ") + std::to_string(ind_size - x_size) + std::string(") x_") + std::to_string(k) + std::string(")");
    
    return std::string("((_ zero_extend ") + std::to_string(row_count * col_count - ind_size) + std::string(") (bvadd (bvmul ") + bv_const(col_count, ind_size) + std::string(" ") + y + std::string(") ") + x + std::string("))");
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



std::string extract_bit(const std::string & bv, unsigned i)
{
  return std::string("((_ extract ") + std::to_string(i) + std::string(" ") + std::to_string(i) + std::string(") ") + bv + std::string(")");
}

std::string select_bit(const std::string & bv, const std::string & ind_bv)
{
  return std::string("((_ extract 0 0) (bvlshr ") + bv + std::string(" ") + ind_bv + std::string("))"); 		       
}


std::string move_bit(const std::string & bv, unsigned size, const std::string & ind_bv0, const std::string & ind_bv1)
{
  std::string mask0 = std::string("(bvnot (bvshl (_ bv1 ") +  std::to_string(size) + std::string(") ") + ind_bv0 + std::string("))");
  std::string mask1 = std::string("(bvshl (_ bv1 ") +  std::to_string(size) + std::string(") ") + ind_bv1 + std::string(")");
  return std::string("(bvor (bvand ") + bv + std::string(" ") + mask0 + std::string(") ") + mask1 + std::string(")");
}

std::string box(unsigned k)
{
  return std::string("box_") + std::to_string(k);
}

void generate_output(const board & brd,
		     unsigned plan_length,
		     std::ostream & ostr)
{
  ostr << "(set-option :print-success false)" << std::endl;
  ostr << "(set-option :produce-models true)" << std::endl;
  ostr << "(set-logic QF_BV)" << std::endl;
  ostr << "(declare-const wall (_ BitVec " << brd.row_count * brd.col_count << "))" << std::endl;
  ostr << "(declare-const home (_ BitVec " << brd.row_count * brd.col_count << "))" << std::endl;

  unsigned map_size = brd.row_count * brd.col_count;
  unsigned index_size = log_2(brd.row_count * brd.col_count);
  unsigned row_index_size = log_2(brd.row_count);
  unsigned col_index_size = log_2(brd.col_count);
  unsigned move_size = log_2(MOVE_MAX + 1);
    
  for(unsigned i = 0; i <= plan_length; i++)
    {      
      ostr << "(declare-const box_" << i << " (_ BitVec " << brd.row_count * brd.col_count << "))" << std::endl;
      ostr << "(declare-const x_" << i << " (_ BitVec " << col_index_size << "))" << std::endl;
      ostr << "(declare-const y_" << i << " (_ BitVec " << row_index_size << "))" << std::endl;
    }

for(unsigned i = 1; i <= plan_length; i++)
  {
    ostr << "(declare-const move_" << i << " (_ BitVec " << move_size << "))" << std::endl;
  }
  
  // ASSERT INITIAL STATE
  for(unsigned i = 0; i < brd.row_count; i++)
    for(unsigned j = 0; j < brd.col_count; j++)
      {
	ostr << "(assert (= " << extract_bit("wall", brd.pair_to_index(i, j)) << " #b" << (brd.wall[brd.pair_to_index(i, j)] ? 1 : 0)  << "))" << std::endl;
      }

  for(unsigned i = 0; i < brd.row_count; i++)
    for(unsigned j = 0; j < brd.col_count; j++)
      {
	ostr << "(assert (= " << extract_bit("home", brd.pair_to_index(i, j)) << " #b" << (brd.home[brd.pair_to_index(i, j)] ? 1 : 0)  << "))" << std::endl;
      }

  for(unsigned i = 0; i < brd.row_count; i++)
    for(unsigned j = 0; j < brd.col_count; j++)
      {
	ostr << "(assert (= " << extract_bit("box_0", brd.pair_to_index(i, j)) << " #b" << (brd.box[brd.pair_to_index(i, j)] ? 1 : 0)  << "))" << std::endl;
      }

  ostr << "(assert (= x_0 " << bv_const(brd.x_sokoban, col_index_size) << "))" << std::endl;
  ostr << "(assert (= y_0 " << bv_const(brd.y_sokoban, row_index_size) << "))" << std::endl;

  // ASSERT TRANSITIONS
  for(unsigned k = 0; k < plan_length; k++)
    {      
      ostr << "(assert (and (bvuge move_" << k+1 << " " << bv_const(MOVE_MIN, move_size) << ") (bvule move_" << k+1 << " " << bv_const(MOVE_MAX, move_size) << ")))" << std::endl;

#ifdef _ENABLE_STAY
      // NON-STAY PRECONDITIONS
      ostr << "(assert" << std::endl
	   << " (=> (distinct move_" << k+1 << " " << bv_const(MOVE_STAY, move_size) << ")" << std::endl
	   << "     (distinct box_" << k << " home)" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;
#else
      ostr << "(assert (distinct box_" << k << " home))" << std::endl;
#endif
      
      // UP PRECONDITIONS
      ostr << "(assert"  << std::endl
           << " (=> (= move_" << k+1 << " " << bv_const(MOVE_UP, move_size) << ")"  << std::endl
	   << "  (and (bvugt y_" << k << " " << bv_const(0, row_index_size) <<  ")"  << std::endl
	   << "       (= " << select_bit("wall", brd.pair_to_index_str(k, 0, -1)) << " #b0)"  << std::endl
	   << "       (or (= " << select_bit(box(k), brd.pair_to_index_str(k, 0, -1)) << " #b0)"  << std::endl
	   << "           (and (bvugt y_" << k << " " << bv_const(1, row_index_size) << ")"  << std::endl
	   << "                (= " << select_bit(box(k), brd.pair_to_index_str(k, 0, -2)) << " #b0)" << std::endl
	   << "                (= " << select_bit("wall", brd.pair_to_index_str(k, 0, -2)) << " #b0)" << std::endl
	   << "           )"  << std::endl
	   << "       )"  << std::endl 
	   << "  )"  << std::endl 
	   << " )"  << std::endl 
	   << ")" << std::endl;
      
      // UP EFFECTS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " " << bv_const(MOVE_UP, move_size) << ")"  << std::endl
	   << "  (and (= y_" << k+1 << " (bvsub y_" << k << " " << bv_const(1, row_index_size) << "))" << std::endl 
	   << "       (= x_" << k+1 << " x_" << k << ")" << std::endl
	   << "       (=> (= " << select_bit(box(k), brd.pair_to_index_str(k, 0, -1)) << " #b0)" << std::endl
	   << "           (= box_" << k+1 << " box_" << k << ")" << std::endl
	   << "       )" << std::endl
	   << "       (=> (= " << select_bit(box(k), brd.pair_to_index_str(k, 0, -1)) << " #b1)" << std::endl
	   << "           (= box_" << k+1 << " " << move_bit(box(k), map_size, brd.pair_to_index_str(k, 0, -1), brd.pair_to_index_str(k, 0, -2)) << ")" << std::endl
	   << "       )" << std::endl
	   << "  )" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;

      
      // DOWN PRECONDTIONS
      ostr << "(assert"  << std::endl
           << " (=> (= move_" << k+1 << " " << bv_const(MOVE_DOWN, move_size) << ")"  << std::endl
	   << "  (and (bvult y_" << k << " " << bv_const(brd.row_count-1, row_index_size) << ")"  << std::endl
	   << "       (= " << select_bit("wall", brd.pair_to_index_str(k, 0, 1)) << " #b0)"  << std::endl
	   << "       (or (= " << select_bit(box(k), brd.pair_to_index_str(k, 0, 1)) << " #b0)"  << std::endl
	   << "           (and (bvult y_" << k << " " << bv_const(brd.row_count - 2, row_index_size) << ")"  << std::endl
	   << "                (= " << select_bit(box(k), brd.pair_to_index_str(k, 0, 2)) << " #b0)" << std::endl
	   << "                (= " << select_bit("wall", brd.pair_to_index_str(k, 0, 2)) << " #b0)" << std::endl
	   << "           )"  << std::endl
	   << "       )"  << std::endl 
	   << "  )"  << std::endl 
	   << " )"  << std::endl 
	   << ")" << std::endl;


      
      // DOWN EFFECTS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " " << bv_const(MOVE_DOWN, move_size) << ")"  << std::endl
	   << "  (and (= y_" << k+1 << " (bvadd y_" << k << " " << bv_const(1, row_index_size) << "))" << std::endl 
	   << "       (= x_" << k+1 << " x_" << k << ")" << std::endl
	   << "       (=> (= " << select_bit(box(k), brd.pair_to_index_str(k, 0, 1)) << " #b0)" << std::endl
	   << "           (= box_" << k+1 << " box_" << k << ")" << std::endl
	   << "       )" << std::endl
	   << "       (=> (= " << select_bit(box(k), brd.pair_to_index_str(k, 0, 1)) << " #b1)" << std::endl
	   << "           (= box_" << k+1 << " " << move_bit(box(k), map_size, brd.pair_to_index_str(k, 0, 1), brd.pair_to_index_str(k, 0, 2)) << ")" << std::endl
	   << "       )" << std::endl
	   << "  )" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;

      
      // LEFT PRECONDITIONS
      ostr << "(assert"  << std::endl
           << " (=> (= move_" << k+1 << " " << bv_const(MOVE_LEFT, move_size) << ")"  << std::endl
	   << "  (and (bvugt x_" << k << " " << bv_const(0, col_index_size) << ")"  << std::endl
	   << "       (= " << select_bit("wall", brd.pair_to_index_str(k, -1, 0)) << " #b0)"  << std::endl
	   << "       (or (= " << select_bit(box(k), brd.pair_to_index_str(k, -1, 0)) << " #b0)" << std::endl
	   << "           (and (bvugt x_" << k << " " << bv_const(1, col_index_size)  << ")"  << std::endl
	   << "                (= " << select_bit(box(k), brd.pair_to_index_str(k, -2, 0)) << " #b0)" << std::endl
	   << "                (= " << select_bit("wall", brd.pair_to_index_str(k, -2, 0)) << " #b0)" << std::endl
	   << "           )"  << std::endl
	   << "       )"  << std::endl 
	   << "  )"  << std::endl 
	   << " )"  << std::endl 
	   << ")" << std::endl;
      
      // LEFT EFFECTS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " " << bv_const(MOVE_LEFT, move_size) << ")" << std::endl
	   << "  (and (= x_" << k+1 << " (bvsub x_" << k << " " << bv_const(1, col_index_size) << "))" << std::endl 
	   << "       (= y_" << k+1 << " y_" << k << ")" << std::endl
	   << "       (=> (= " << select_bit(box(k), brd.pair_to_index_str(k, -1, 0)) << " #b0)" << std::endl
	   << "           (= box_" << k+1 << " box_" << k << ")" << std::endl
	   << "       )" << std::endl
	   << "       (=> (= " << select_bit(box(k), brd.pair_to_index_str(k, -1, 0)) << " #b1)" << std::endl
	   << "           (= box_" << k+1 << " " << move_bit(box(k), map_size, brd.pair_to_index_str(k, -1, 0), brd.pair_to_index_str(k, -2, 0)) << ")" << std::endl
	   << "       )" << std::endl
	   << "  )" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;
						       
      
      // RIGHT PRECONDITIONS
      ostr << "(assert"  << std::endl
           << " (=> (= move_" << k+1 << " " << bv_const(MOVE_RIGHT, move_size) << ")" << std::endl
	   << "  (and (bvult x_" << k << " " << bv_const(brd.col_count-1, col_index_size) << ")"  << std::endl
	   << "       (= " << select_bit("wall", brd.pair_to_index_str(k, 1, 0)) << " #b0)"  << std::endl
	   << "       (or (= " << select_bit(box(k), brd.pair_to_index_str(k, 1, 0)) << " #b0)"  << std::endl
	   << "           (and (bvult x_" << k << " " << bv_const(brd.col_count - 2, col_index_size) << ")"  << std::endl
	   << "                (= " << select_bit(box(k), brd.pair_to_index_str(k, 2, 0)) << " #b0)" << std::endl
	   << "                (= " << select_bit("wall", brd.pair_to_index_str(k, 2, 0)) << " #b0)" << std::endl
	   << "           )"  << std::endl
	   << "       )"  << std::endl 
	   << "  )"  << std::endl 
	   << " )"  << std::endl 
	   << ")" << std::endl;

      // RIGHT EFFECTS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " " << bv_const(MOVE_RIGHT, move_size) << ")"  << std::endl
	   << "  (and (= x_" << k+1 << " (bvadd x_" << k << " " << bv_const(1, col_index_size) << "))" << std::endl 
	   << "       (= y_" << k+1 << " y_" << k << ")" << std::endl
	   << "       (=> (= " << select_bit(box(k), brd.pair_to_index_str(k, 1, 0)) << " #b0)" << std::endl
	   << "           (= box_" << k+1 << " box_" << k << ")" << std::endl
	   << "       )" << std::endl
	   << "       (=> (= " << select_bit(box(k), brd.pair_to_index_str(k, 1, 0)) << " #b1)" << std::endl
	   << "           (= box_" << k+1 << " " << move_bit(box(k), map_size, brd.pair_to_index_str(k, 1, 0), brd.pair_to_index_str(k, 2, 0)) << ")" << std::endl
	   << "       )" << std::endl
	   << "  )" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;

#ifdef _ENABLE_STAY
      // STAY PRECONDITIONS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " " << bv_const(MOVE_STAY, move_size) << ")" << std::endl
	   << "     (= box_" << k << " home)" << std::endl
	   << " )" << std::endl
	   << ")" << std::endl;
      
      // STAY EFFECTS
      ostr << "(assert" << std::endl
	   << " (=> (= move_" << k+1 << " "  << bv_const(MOVE_STAY, move_size) << ")" << std::endl
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
	       << "    (= move_" << k+1 << " " << bv_const(MOVE_STAY, move_size) << ")" << std::endl
#endif
	       << "    (distinct x_" << k+1 << " x_" << s << ")" << std::endl
	       << "    (distinct y_" << k+1 << " y_" << s << ")" << std::endl
	       << "    (distinct box_" << k+1 << " box_" << s << ")" << std::endl
	       << "  )" << std::endl
	       << ")" << std::endl;	  
	}

#ifndef _DISABLE_INVARIANT
      // INVARIANT (BOUNDS FOR SOKOBAN COORDINATES)
      ostr << "(assert (and (bvuge x_" << k+1 << " " << bv_const(0, col_index_size) << ") (bvule x_" << k+1 << " " << bv_const(brd.col_count-1, col_index_size) << ")))" << std::endl;
      ostr << "(assert (and (bvuge y_" << k+1 << " " << bv_const(0, row_index_size) << ") (bvule y_" << k+1 << " " << bv_const(brd.row_count-1, row_index_size) << ")))" << std::endl;
     

      // INVARIANT (NUMBER OF BOXES DOES NOT CHANGE)
      ostr << "(assert (= " << bv_const(brd.box_count, index_size) << " ";
      for(unsigned i = 0; i < brd.row_count; i++)
      	for(unsigned j = 0; j < brd.col_count; j++)
      	  ostr << "(bvadd ((_ zero_extend " << index_size - 1 << ") " << extract_bit(box(k+1), brd.pair_to_index(i, j)) << ") ";
      ostr << bv_const(0, index_size);
      for(unsigned i = 0; i  < map_size; i++)
	ostr << ")";
      ostr << "))" << std::endl;
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

  std::cerr << brd << std::endl;
  
  unsigned plan_length = atoi(argv[3]);

  generate_output(brd, plan_length, ostr);
  
  
  return 0;
}
