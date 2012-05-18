// pre: x < max_int
int main(int x) {
  // WP1
  
  int y = x+1;

  // WP2
  y = abs1(y);
  
  // WP3
  if (y < 0x7fffffff)
    y = y + 1;
  
  return y;
}
// post: return >= 1
