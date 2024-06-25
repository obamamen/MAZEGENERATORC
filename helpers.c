#include <stdio.h>
#include <stdlib.h>

void square(int x, int y, int size, int in, unsigned char **array, int width, int height) {
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < size; j++) {
            if (x + i < width && y + j < height) {
                array[x + i][y + j] = in;
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

unsigned short** allocate_and_initialize_maze(int width, int height) {
    unsigned short **array = (unsigned short **)malloc(height * sizeof(unsigned short *));
    for (int i = 0; i < height; i++) {
        array[i] = (unsigned short *)malloc(width * sizeof(unsigned short));
        for (int j = 0; j < width; j++) {
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