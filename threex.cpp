#include <iostream>
#include <bitset>
#include <string>

int iscollatz(unsigned long long n) {
  while( n > 1 ) {
    std::cout.width(8);
    std::cout << n << " " << std::bitset<64>(n) << "\n";

    // f(n) in case the n is even
    if( ! (n & 1) ) {
      n >>= 1; // div by 2
      continue;
    }

    // split n to first three bits and the rest
    unsigned long long a = n & 0b111; // a three LSB's of n
    unsigned long long r = n - a; // from n = r + a
    if( a == 0b001 ) {
      // 3n + 1 = 3 * (n - a + a) + 1 = 3*r + 3a + 1
      // 3*r + 3* 0b001 + 1 = 3*r +  0b011 + 1 = 3*r + 0b100
      n = 3*r + 0b100;
      //n >>= 2; // optimization possible
    }
    else if( a == 0b011 ) {
      // 3n + 1 = 3 * (n - a + a) + 1 = 3*r + 3a + 1
      // 3*r + 3* 0b011 + 1 = 3*r + 0b1001 + 1 = 3*r + 0b1010
      n = 3*r + 0b1010; // adding probagates
      //n >>= 1; // optimization possible
    }
    else if( a == 0b101 ) {
      // 3n + 1 = 3 * (n - a + a) + 1 = 3*r + 3a + 1
      // 3*r + 3* 0b101 + 1 = 3*r + 0b1111 + 1 = 3*r + 0b10000
      // 0b101 * 3 + 1 = 0b1111 + 1 = 0b10000. This is a hard case because, adding will probagate.
      n = 3*r + 0b10000; // adding probagates
      // Notice, the n's three LSBs are 0, i.e. [?*]000b.
      //n >>= 3; // optimization possible
    }
    else if( a == 0b111) {
      // 3n + 1 = 3 * (n - a + a) + 1 = 3*r + 3a + 1
      // 3*r + 3* 0b111 + 1 = 3*r + 0b10101 + 1 = 3*r + 0b10110
      n = 3*r + 0b10110; // from result. The adding probagates
      //n >>= 1; // optimization possible
    }
  }
  std::cout.width(8);
  std::cout << n << " " << std::bitset<64>(n) << "\n";
  
  return 1;
}

int main(int argc, char** argv) {

  if( argc != 2 ) {
    std::cout << "Usage: threex <number>\n";
    return 1;
  }
  iscollatz(std::stoull(std::string{argv[1]}));

  return 0;
}
