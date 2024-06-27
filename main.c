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

const int wallThickness = 1;
const int gridWidth = 16;
const int gridHeight = 32;
const int cellWidth = 4;
const int cellHeight = 4;

void mazeToImage(unsigned char **maze, unsigned char **image, int gridWidth, int gridHeight, int imageWidth, int imageHeight) {
    for (int i = 0; i < gridWidth; i++) {
        for (int j = 0; j < gridHeight; j++) {
            square(
            i*(cellWidth + wallThickness) + wallThickness, 
            j*(cellHeight + wallThickness) + wallThickness,
            cellWidth,
            cellHeight,
            1,image,imageWidth,imageHeight);
            char xOffset = 0;
            char yOffset = 0;
            unsigned char a = maze[i][j];
            if (a == 1) {yOffset = -1;}
            if (a == 2) {xOffset = 1; }
           if (a == 3) {yOffset = 1; }
            if (a == 4) {xOffset = -1;}
            if ((xOffset != 0 ) | ( yOffset != 0)) {
                square(
                i*(cellWidth + wallThickness) + wallThickness + wallThickness*xOffset,
                j*(cellHeight + wallThickness) + wallThickness + wallThickness*yOffset,
                cellWidth,                                            
                cellHeight,
                1,image,imageWidth,imageHeight); 
            }
        }
    }
}

int main() {
    int imageWidth = (gridWidth * (cellWidth + wallThickness)) + wallThickness;
    int imageHeight = (gridHeight * (cellHeight + wallThickness)) + wallThickness;

    unsigned char **image = allocate_and_initialize_image(imageWidth, imageHeight);
    unsigned char **maze = allocate_and_initialize_maze(gridWidth, gridHeight);

    maze[1][1] = 1;
    //maze[5][4] = 2;
    //maze[7][8] = 3;
    //maze[2][8] = 4;
    //maze[16][14] = 2;

    printf("maze %d\n",maze[16][14]);


    mazeToImage(maze, image, gridWidth, gridHeight, imageWidth, imageHeight);


    create_1bit_bmp_from_array("output_1bit.bmp", imageWidth, imageHeight, image);
    free_array((void**)image, imageHeight); // cast to void
    return 0;
}





