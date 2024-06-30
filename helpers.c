#include <stdio.h>
#include <stdlib.h>
#include <math.h>
//#include "bit.c"


void check_allocation(void *ptr) {
    if (!ptr) {
        fprintf(stderr, "Memory allocation failed\n");
        exit(EXIT_FAILURE);
    }
}

void square(int x, int y, int sizeX, int sizeY, int in, unsigned char **image, int width, int height) {
    for (int i = 0; i < sizeX; i++) {
        for (int j = 0; j < sizeY; j++) {
            if (x + i < width && y + j < height) {
                int part = floor((x+j) / 8);
                image[y + i][part] |= (in << ((x+j) % 8));
            }
        }
    }
}

unsigned char** allocate_and_initialize_image(int width, int height) {
    unsigned char **array = (unsigned char **)malloc(height * sizeof(unsigned char *));
    for (int i = 0; i < height; i++) {
        array[i] = (unsigned char *)malloc(width * sizeof(unsigned char));
        for (int j = 0; j < width; j++) {
            array[i][j] = 0;
        }
    }
    return array;
}

unsigned char** allocate_and_initialize_maze(int width, int height) {
    unsigned char **array = (unsigned char **)malloc(width * sizeof(unsigned char *));
    check_allocation(array);
    for (int i = 0; i < width; i++) {
        array[i] = (unsigned char *)malloc(height * sizeof(unsigned char));
        check_allocation(array[i]);
        for (int j = 0; j < height; j++) {
            array[i][j] = 0;
        }
    }
    return array;
}


void free_array(void **array, int height) {
    for (int i = 0; i < height; i++) {
        free(array[i]);
    }
    free(array);
}