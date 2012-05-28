// pre: x > max_neg_int
// -sqrt(max_int) <= x <= sqrt(max_int)  for theorem overflow
int main(int x) {
  // WP1

  int y = abs1(x);
  
  // WP2

  int z = sqrt1(y);
 
  // WP3
  
  return z;
}
// post: r >= 0 & r*r*r*r <= x*x
