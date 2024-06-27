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
    unsigned int cells[width*height];
    unsigned int cellsIndex = 0;
    addToCells(cells,&cellsIndex,1,1);

    printf("cells[0]: %d\n", cells[cellsIndex-1]);
    printf("cells[1]: %d\n", cells[cellsIndex-2]);

    addToCells(cells,&cellsIndex,5,12);

    printf("cells[0]: %d\n", cells[cellsIndex-1]);
    printf("cells[1]: %d\n", cells[cellsIndex-2]);

    removeFromCells(cells,&cellsIndex);

    printf("cells[0]: %d\n", cells[cellsIndex-1]);
    printf("cells[1]: %d\n", cells[cellsIndex-2]);
}





