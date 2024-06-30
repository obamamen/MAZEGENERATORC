#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "helpers.c"
#include "mazegen.c"
#include "pngmaker.c"



int wallThickness = 1;
int gridWidth = 14000; //11500 max
int gridHeight =14000;
int cellWidth = 2;
int cellHeight = 2;

void mazeToImage(unsigned char **maze, unsigned char **image, int gridWidth, int gridHeight, int imageWidth, int imageHeight) {
    int iteration = 0;
    for (int i = 0; i < gridWidth; i++) {
        for (int j = 0; j < gridHeight; j++) {
        iteration++;
        if ((iteration % (gridWidth * gridHeight / 50) == 0) || (iteration == (gridWidth * gridHeight))) {
            double totSize = (gridWidth * gridHeight);
            double it = iteration;
            printf("at %f procent of the mazeToImage\n", (it/totSize)*100);
         }
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

            a  = 0;
            if ((i == 0) && (j == 0)) {
                a = 4;
            }
            if ((i == gridWidth) && (j == gridHeight)) {
                a = 2;
            }
            xOffset = 0;
            yOffset = 0;
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
    unsigned char **image = allocate_and_initialize_image(floor(imageWidth/8), imageHeight);
    unsigned char **maze = allocate_and_initialize_maze(gridWidth, gridHeight);
    generateMaze(maze,gridWidth, gridHeight);
    mazeToImage(maze, image, gridWidth, gridHeight, imageWidth, imageHeight);
    char name[50] = "Maze ";
    char add[50] = "";
    sprintf(add, "%d", gridWidth);
    strcat(name, add);
    strcat(name, " x ");
    sprintf(add, "%d", gridHeight);
    strcat(name, add);

    sprintf(add, ".png");
    strcat(name, add);

    free_array((void**)maze, gridWidth);
    create_png_from_array(name, imageWidth, imageHeight, image);
    free_array((void**)image, imageHeight);
    return 0;
}





