#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h> 


void addToCells( unsigned short cells[],  unsigned int *cellsIndex, int x, int y) {
    cells[*cellsIndex] = x;
    cells[*cellsIndex + 1] = y;
    *cellsIndex+=2;
}
void removeFromCells( unsigned short cells[],  unsigned int *cellsIndex) {
    *cellsIndex-=2;
}

void shuffle(unsigned char *array, size_t n)
{
    if (n > 1) 
    {
        size_t i;
        for (i = 0; i < n - 1; i++) 
        {
          size_t j = i + rand() / (RAND_MAX / (n - i) + 1);
          int t = array[j];
          array[j] = array[i];
          array[i] = t;
        }
    }
}

void generateMaze(unsigned char** maze, int width, int height) {
    short DX[] = {0, 0, 1, 0, -1};
    short DY[] = {0, -1, 0, 1, 0};
    unsigned short OPP[] = {0, 3, 4, 1, 2};
    size_t totalSize = width * height * sizeof(unsigned short) * 2;
    unsigned int cellsIndex = 0;
    unsigned short *cells = (unsigned short *)malloc(totalSize);
    if (cells == NULL) {
        fprintf(stderr, "Unable to allocate memory for cells array.\n");
        return;
    }
    addToCells(cells,&cellsIndex,0,0);
    srand(time(0)); 
    int sx = 0; 
    int sy = 0;
    int iteration = 0;
    while (cellsIndex > 0) {
        iteration++;
        unsigned char dirs[] = {1, 2, 3, 4};
        char stuck = 1;
        shuffle(dirs, 4);
        int x = cells[cellsIndex-2];
        int y = cells[cellsIndex-1];
        int a = rand() % 100;
        if (a < 50) {
            for (int i = 0; i < 4; ++i) {
                if (dirs[i] == OPP[maze[x][y]]) {
                    unsigned char temp = dirs[0];
                    dirs[0] = dirs[i];
                    dirs[i] = temp;
                    break;
                }
            }
        }
        for (int i = 0; i < 4; ++i) {
            int nx = x + DX[dirs[i]];
            int ny = y + DY[dirs[i]];
            if (nx >= 0 && ny >= 0 && nx < width && ny < height && maze[nx][ny] == 0) { 
                if ((nx == sx) && (ny == sy)) {continue;}
                maze[nx][ny] = OPP[dirs[i]];
                addToCells(cells,&cellsIndex,nx,ny);
                stuck = 0;
                break; 
            }
        }
        if (stuck == 1) {removeFromCells(cells,&cellsIndex);
            //printf("Backtracking at (%d, %d)\n", x, y); // Debug statement
        }

        if ((iteration % (width * height / 50) == 0) || (iteration == (width * height * 2)-1)) {
            double totSize = (width * height * 2)-1;
            double it = iteration;
            printf("at %f procent of the generateMaze\n", (it/totSize)*100);
        }
    }
    free(cells);
}








