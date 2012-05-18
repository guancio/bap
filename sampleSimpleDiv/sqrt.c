int sqrt(int x) {
  int y = 0;
  int sq = y*y;
  // I = y > 0
  do {
    y +=1;
    int sq = y*y;
  } while (sq < x);
  // sq >= x and y > 0
  return y-1;
}
