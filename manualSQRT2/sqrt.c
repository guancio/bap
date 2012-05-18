// pre x >= 0
int sqrt(int x) {
  int y = 0;
  int sq = (y+1)*(y+1);
  // I = y*y <= x and sq = (y+1)*(y+1)
  while (sq <= x) {
    y +=1;
    sq = (y+1)*(y+1);
  };
  // sq > x &
  // I: sq = (y+1)*(y+1) and y*y<=x  => 
  // wp: (y*y) <= x < (y+1)*(y+1)
  return y;
}
// post: (r*r) <= p < (r+1)*(r+1)
// and r >= 0
// abd r <= 0x0000b504
