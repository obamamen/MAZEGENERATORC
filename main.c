#include <stdio.h>
#include <stdlib.h>
#include "bitmap.c"
#include "helpers.c"


//      ___ ___     __   __                  __  ___     ___          __     __   __     __                           __     __        ___  __      __        __   __  ___ 
//|    |__   |     /  \ |__)       |\/|  /\   / |__     |__  |\ |    |  \ | |__) /__`     / |    | |\ |    |  | |\ | /__` | / _` |\ | |__  |  \    /__` |__| /  \ |__)  |  
//|___ |___  |     \__/ |    .     |  | /~~\ /_ |___    |___ | \|    |__/ | |  \ .__/    /_ | \__/ | \|    \__/ | \| .__/ | \__> | \| |___ |__/    .__/ |  | \__/ |  \  |  
//                           '                                                                                                                                             

unsigned short directions[] = {1, 2, 3, 4};
unsigned short DX[] = {0, 0, 1, 0, -1};
unsigned short DY[] = {0, -1, 0, 1, 0};
unsigned short OPP[] = {0, 3, 4, 1, 2};

const int wallThickness = 4;
const int gridWidth = 16;
const int gridHeight = 16;
const int cellWidth = 8;
const int cellHeight = 8;

void mazeToImage(unsigned char **maze, unsigned char **image, int gridWidth, int gridHeight, int imageWidth, int imageHeight) {
    for (int i = 0; i < gridWidth; i++) {
        for (int j = 0; j < gridHeight; j++) {
            square(i*cellWidth+wallThickness+wallThickness/2-1,
            j*cellHeight+wallThickness+wallThickness/2-1,
            cellWidth-wallThickness/2,
            cellHeight-wallThickness/2,
            1,image,imageWidth,imageHeight);
        }
    }
}

int main() {
    int imageWidth = gridWidth * cellWidth + wallThickness * 2;
    int imageHeight = gridHeight * cellHeight + wallThickness * 2;


    unsigned char **image = allocate_and_initialize_image(imageWidth, imageHeight);
    unsigned char **maze = allocate_and_initialize_maze(gridWidth, gridHeight);

    maze[1][1] = 1;
    maze[2][1] = 1;
    maze[2][2] = 1;
    maze[3][2] = 1;
    maze[15][15] = 1;

    mazeToImage(maze, image, gridWidth, gridHeight, imageWidth, imageHeight);


    create_1bit_bmp_from_array("output_1bit.bmp", imageWidth, imageHeight, image);
    free_array((void**)image, imageHeight); // cast to void
    return 0;
}





