#include <stdio.h>
#include <stdlib.h>


void addToCells( unsigned int cells[],  unsigned int *cellsIndex, int x, int y) {
    cells[*cellsIndex] = x;
    cells[*cellsIndex + 1] = y;
    *cellsIndex+=2;
}
void removeFromCells( unsigned int cells[],  unsigned int *cellsIndex) {
    *cellsIndex-=2;
}

void generateMaze(unsigned char** maze, int width, int height) {
    size_t totalSize = width * height * sizeof(unsigned int) * 2;
    unsigned int cellsIndex = 0;
    unsigned int *cells = (unsigned int *)malloc(totalSize);
    if (cells == NULL) {
        fprintf(stderr, "Unable to allocate memory for cells array.\n");
        return;
    }
    addToCells(cells,&cellsIndex,0,0);


    //maze[0][0] = 1;
}





