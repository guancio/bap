// pre x >= 0
int sqrt(int x) {
  int y = 0;
  int sq = (y+1)*(y+1);
  // I = y >= 0
  while (sq < x && y < 0x7fffffff) {
    y +=1;
    sq = (y+1)*(y+1);
  };
  // y >= 0 &&
  // !(sq<x && y < 0x7fffffff)
  return y;
}
// post: y >= 0


// post: (r)*(r) <= x < (r+1)*(r+1)

// pre :
int abs(int x) {
  if (x < 0)
    return -x;
  return x;
}
// post: r >= 0


// pre: 
void main(int x) {
  int y = abs(x);
  // post abs => pre sqrt
  return sqrt(y);
}
// post:
