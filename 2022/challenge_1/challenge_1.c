#include <stdlib.h>

#define N 100

typedef struct Point {
  int x;
  int y;
  int z;
} Point;

/*@ requires 0 < n;
    requires \valid(p+(0..n-1));
    requires \forall integer i; 0 <= i < n ==> 0 <= p[i].x;
    requires \forall integer i; 0 <= i < n ==> 0 <= p[i].y;
    requires \forall integer i; 0 <= i < n ==> 0 <= p[i].z;
    requires 0 < voxel_size;
    requires \valid(pd+(0..n-1));
    requires \separated(p+(0..n-1), pd+(0..n-1));
    terminates \true;
*/
void downSample (int n, Point p[], int voxel_size, Point pd[]) {
  int x_max, y_max, z_max, x_min, y_min, z_min;

  x_max = p[0].x;
  y_max = p[0].y;
  z_max = p[0].z;
  x_min = p[0].x;
  y_min = p[0].y;
  z_min = p[0].z;
  /*@ loop invariant 1 <= i <= n;
      loop invariant 0 <= x_min <= x_max;
      loop invariant 0 <= y_min <= y_max;
      loop invariant 0 <= z_min <= z_max;
      loop assigns x_max, y_max, z_max, x_min, y_min, z_min, i;
      loop variant n - i;
  */
  for (int i = 1; i < n; i++) {
    x_max = p[i].x > x_max ? p[i].x : x_max;
    y_max = p[i].y > y_max ? p[i].y : y_max;
    z_max = p[i].z > z_max ? p[i].z : z_max;
    x_min = p[i].x < x_min ? p[i].x : x_min;
    y_min = p[i].y < y_min ? p[i].y : y_min;
    z_min = p[i].z < z_min ? p[i].z : z_min;
  }

  // TODO: ceiling ?
  int num_vox_x = abs(x_max - x_min)/voxel_size;
  int num_vox_y = abs(y_max - y_min)/voxel_size;
  int num_vox_z = abs(z_max - z_min)/voxel_size;

  // we assume that we don't need more than N*N*N
  Point voxel_array[N][N][N];
  int count_array[N][N][N];

  /*@ loop invariant 0 <= i <= n;
      loop assigns voxel_array[0..n-1][0..n-1][0..n-1], i;
      loop variant n - i;
  */
  for (int i = 0; i < n; i++) {
    int x_floored = (p[i].x - x_min)/voxel_size;
    int y_floored = (p[i].y - y_min)/voxel_size;
    int z_floored = (p[i].z - z_min)/voxel_size;

    voxel_array[x_floored][y_floored][z_floored].x += p[i].x;
    voxel_array[x_floored][y_floored][z_floored].y += p[i].y;
    voxel_array[x_floored][y_floored][z_floored].z += p[i].z;
    count_array[x_floored][y_floored][z_floored] ++;
  }

  int index = 0;
  /*@ loop invariant 0 <= i <= num_vox_x;
      loop invariant 0 <= index <= n;
      loop assigns pd[0..n-1], i;
      loop variant num_vox_x - i;
  */
  for (int i = 0; i < num_vox_x; i++) {
    /* loop invariant 0 <= j <= num_vox_y;
       loop invariant 0 <= index <= n;
       loop assigns pd[0..n-1], j;
       loop variant num_vox_y - j;
    */
    for (int j = 0; j < num_vox_y; j++) {
      /*@ loop invariant 0 <= k <= num_vox_z;
          loop invariant 0 <= index <= n;
          loop assigns pd[0..n-1], k;
          loop variant num_vox_z - k;
      */
      for (int k = 0; k < num_vox_z; k++) {
        if (count_array[i][j][k] != 0) {
          Point pt;
          pt.x = voxel_array[i][j][k].x/count_array[i][j][k];
          pt.y = voxel_array[i][j][k].y/count_array[i][j][k];
          pt.z = voxel_array[i][j][k].z/count_array[i][j][k];
          pd[index] = pt;
          index++;
        }
      }
    }
  }

  return;
}
