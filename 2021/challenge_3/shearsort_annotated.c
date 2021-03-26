#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <mpi.h>

/*! Master process. Usually process 0. */
#define MASTER      0
#define TRUE        1
#define FALSE       0
#define MAXLEN 1000000

void sort(int *row, int length) {
  int i, j, temp;
  for (i = 0; i < length; i++) {
    for (j = length - 1; j >= 0; j--) {
      if (row[j-1] > row[j]) {
	temp = row[j-1];
	row[j-1] = row[j];
	row[j] = temp;
      }
    }
  }
}

void rsort(int *row, int length) {
  int i, j, temp;
  for (i = 0; i < length; i++) {
    for (j = length - 1; j >= 0; j--) {
      if (row[j-1] < row[j]) {
	temp = row[j-1];
	row[j-1] = row[j];
	row[j] = temp;
      }
    }
  }
}

/*@ requires len > 0;
  @ requires \valid(v + (0..(len-1)));
  @ assigns v[0 .. len-1];
  @*/
void Scan_vector(int* v, int len);

/*@ assigns \nothing;
  @ ensures \result > 0;
  @ ensures MAXLEN > \result * \result;
  @*/
int getProblemSize(int procs);

/*!
 *  \param argv[1] Dimension of square matrix, i.e. number of rows = number of columns
 */
int main(int argc, char** argv) {

  /* Dimension of square matrix (i.e. number of rows = number of columns) */
  int DIMENSION;
  /* Used for error handling */
  int error_code;
  /* Total number of processes used in this program */
  int NUMBER_OF_PROCESSES;
  /* Current process */
  int PROCESS_ID;
  /* Message identifier for sending/receiving rows in a matrix */
  int ROW_TAG = 1;
  /* Message identifier for sending/receiving columns in a matrix */
  int COLUMN_TAG = 0;

  error_code = MPI_Init(&argc, &argv);

  error_code = MPI_Comm_size(MPI_COMM_WORLD, &NUMBER_OF_PROCESSES);
  error_code = MPI_Comm_rank(MPI_COMM_WORLD, &PROCESS_ID);

  if (error_code != 0) {
    printf("Error initializing MPI and obtaining task information.\n");
    MPI_Finalize();
    exit(1);
  }

  if (PROCESS_ID == 0) {
    DIMENSION = getProblemSize(NUMBER_OF_PROCESSES);
  }

  MPI_Bcast(&DIMENSION, 1, MPI_INT, 0, MPI_COMM_WORLD);

  if (DIMENSION > NUMBER_OF_PROCESSES) {
    printf("Dimension of square matrix = %d\tNumber of processes = %d\n", DIMENSION, NUMBER_OF_PROCESSES);
    printf("Number of processes does NOT equal dimension of square matrix. Please try again.\n");
    MPI_Finalize();
    exit(1);
  }

  /****************************************************************************************************
   ** MASTER                                                                                          **
   ****************************************************************************************************/
  if (PROCESS_ID == MASTER) {
    int destination, source;
    int current_column, current_row, i;
    int matrix [MAXLEN];
    int local_row[MAXLEN];

    for (int scan_counter = 0; scan_counter < DIMENSION; scan_counter++){
      Scan_vector(matrix+(DIMENSION*scan_counter),DIMENSION);
    }
    /*@ loop invariant 1 <= program_counter <= procs;
      @ loop invariant getFirst(get_type(protocol)) == getNext(split(getFirst(\at(get_type(protocol),LoopEntry)),i));
      @ loop invariant getNext(get_type(protocol)) == getNext(\at(get_type(protocol),LoopEntry));
      @ loop assigns protocol, program_counter, local_row[0..DIMENSION-1],;
      @ loop variant \log(DIMENSION) / \log(2))+ 1 - program_counter;
      @*/
    for (int program_counter = 0; program_counter < (int) ceil(log((double) DIMENSION) / log(2.0)) + 1; program_counter++) {

      /****************************************************************************************************
       ** Send unsorted rows to workers, then receive sorted rows from them                               **
       ****************************************************************************************************/
      for (destination = 1; destination < NUMBER_OF_PROCESSES; destination++) {
	for (int row_counter = 0; row_counter < DIMENSION; row_counter++){
	  local_row[row_counter] = matrix[DIMENSION*row_counter + destination];
	}
	MPI_Ssend(local_row, DIMENSION, MPI_INT, destination, ROW_TAG, MPI_COMM_WORLD);
      }
      for (source = 1; source < NUMBER_OF_PROCESSES; source++) {
	MPI_Recv(local_row, DIMENSION, MPI_INT, source, ROW_TAG, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	for (int row_counter = 0; row_counter < DIMENSION; row_counter++){
	  matrix[DIMENSION*row_counter + destination] = local_row[row_counter];
	}
      }
      /***** Master sorts its row *****/
      sort(matrix, DIMENSION);

      /****************************************************************************************************
       ** Send unsorted columns to workers, then receive sorted columns from them                         **
       ****************************************************************************************************/
      for (destination = 1; destination < NUMBER_OF_PROCESSES; destination++) {
	MPI_Ssend(matrix+(DIMENSION*destination), DIMENSION, MPI_INT, destination, COLUMN_TAG, MPI_COMM_WORLD);
      }
      for (source = 1; source < NUMBER_OF_PROCESSES; source++) {
	MPI_Recv(matrix+(DIMENSION*destination), DIMENSION, MPI_INT, source, COLUMN_TAG, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      }

      /***** Master sorts its column *****/
      for (i = 0; i < DIMENSION; i++) {
	local_row[i] = matrix[DIMENSION*i];
      }
      sort(local_row, DIMENSION);
      for (i = 0; i < DIMENSION; i++) {
	matrix[DIMENSION*i] = local_row[i];
      }
    }
  }
  /****************************************************************************************************
   ** WORKERS                                                                                         **
   ****************************************************************************************************/
  else {
    for (int program_counter = 0; program_counter < (int) ceil((log((double) DIMENSION) / log(2.0))) + 1 ; program_counter++) {
      /****************************************************************************************************
       ** Get rows from Master, sort them, and then return them back to Master                            **
       ****************************************************************************************************/
      MPI_Recv(local_row, DIMENSION, MPI_INT, MASTER, ROW_TAG, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      /***** Sort even rows in ascending order and odd rows in descending order *****/
      if (PROCESS_ID % 2 == 0) {
	sort(local_row, DIMENSION);
      }
      else {
	rsort(local_row, DIMENSION);
      }
      MPI_Ssend(local_row, DIMENSION, MPI_INT, MASTER, ROW_TAG, MPI_COMM_WORLD);

      /****************************************************************************************************
       ** Get columns from Master, sort them, and then return them back to Master                         **
       ****************************************************************************************************/
      MPI_Recv(local_row, DIMENSION, MPI_INT, MASTER, COLUMN_TAG, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      sort(local_row, DIMENSION);
      MPI_Ssend(local_row, DIMENSION, MPI_INT, MASTER, COLUMN_TAG, MPI_COMM_WORLD);
    }
  }

  MPI_Finalize();

  return 0;

}
