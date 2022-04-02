// Frama-C Veterans : Lionel Blatter, Jean-Christophe Léchenet

#define N 10000

/* Simplifying hypotheses:
   - real -> int
   - all points >= (0, 0, 0)
   - we statically have a bound [N] of the needed number of cubes
   - the result is stored in the array [pd] taken as an argument,
     we assume that it is as large as the point cloud [p] and we
     return the exact size that we use

  Achievements:
  - termination
  - memory safety (unfinished)
  - size(pd) <= size(p) (unfinished)

  Alternative approach that we didn't have time to try: axiomatize a specialized
  malloc to have dynamic allocation without the inconveniences
*/

typedef struct Point {
  int x;
  int y;
  int z;
} Point;

/*@ predicate bounded_x (Point* a, int n, integer bound) =
      \forall integer i; 0 <= i < n ==> a[i].x <= bound;
    predicate bounded_y (Point* a, int n, integer bound) =
      \forall integer i; 0 <= i < n ==> a[i].y <= bound;
    predicate bounded_z (Point* a, int n, integer bound) =
      \forall integer i; 0 <= i < n ==> a[i].y <= bound;
*/
      
/*@ requires 0 < n;
    requires \valid(p+(0..n-1));
    requires \forall integer i; 0 <= i < n ==> 0 <= p[i].x;
    requires \forall integer i; 0 <= i < n ==> 0 <= p[i].y;
    requires \forall integer i; 0 <= i < n ==> 0 <= p[i].z;
    requires bounded_x (p, n, N * voxel_size - 1);
    requires bounded_y (p, n, N * voxel_size - 1);
    requires bounded_z (p, n, N * voxel_size - 1);
    requires 0 < voxel_size;
    requires \valid(pd+(0..n-1));
    requires \separated(p+(0..n-1), pd+(0..n-1));
    terminates \true;
    ensures 0 <= \result <= n;
    assigns pd[0..n-1];
*/
int downSample (int n, Point p[], int voxel_size, Point pd[]) {
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
      loop invariant bounded_x (p, i, x_max);
      loop invariant bounded_y (p, i, y_max);
      loop invariant bounded_z (p, i, z_max);
      loop invariant x_max <= N * voxel_size - 1;
      loop invariant y_max <= N * voxel_size - 1;
      loop invariant z_max <= N * voxel_size - 1;
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

  // ceiling -> we take + 1, safe over_approximation
  // abs not needed, since x_max >= x_min
  int num_vox_x = (x_max - x_min)/voxel_size + 1;
  int num_vox_y = (y_max - y_min)/voxel_size + 1;
  int num_vox_z = (z_max - z_min)/voxel_size + 1;

  //@ assert num_vox_x <= N;
  //@ assert num_vox_y <= N;
  //@ assert num_vox_z <= N;

  // thanks to the requirements, we know that we don't need more than N*N*N
  Point voxel_array[N][N][N] = {{{0}}};
  int count_array[N][N][N] = {{{0}}};

  /*@ loop invariant 0 <= i <= n;
      loop assigns voxel_array[0.. N -1][0.. N -1][0.. N -1], count_array[0.. N -1][0.. N -1][0.. N -1], i;
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
      loop assigns pd[0..n-1], index, i;
      loop variant num_vox_x - i;
  */
  for (int i = 0; i < num_vox_x; i++) {
    /*@ loop invariant 0 <= j <= num_vox_y;
       loop invariant 0 <= index <= n;
       loop assigns pd[0..n-1], index, j;
       loop variant num_vox_y - j;
    */
    for (int j = 0; j < num_vox_y; j++) {
      /*@ loop invariant 0 <= k <= num_vox_z;
          loop invariant 0 <= index <= n;
          loop assigns pd[0..n-1], index, k;
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

  return index;
}
