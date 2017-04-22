void swap (int list[], int i, int j) {
  int temp = list[i];
  list[i] = list[j];
  list[j] = temp;
}

void oddEvenSort (int list[], int n) {
  int sorted = 0;
  while(!sorted) {
    sorted=1;
    for(int i = 1; i < n-1; i+=2) {
      if (list[i] > list[i+1]) {
        swap(list, i, i+1);
        sorted = 0;
      }
    }

    for(int i = 0; i < n-1; i+=2) {
      if (list[i] > list[i+1]) {
        swap(list, i, i+1);
        sorted = 0;
      }
    }
  }
}
