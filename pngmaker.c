#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "lodepng.c"

void create_png_from_array(const char *filename, int width, int height, unsigned char **array) {
    unsigned char *image = NULL;
    size_t image_size = (width * height + 7) / 8; 

    image = (unsigned char *)malloc(image_size);
    if (!image) {
        fprintf(stderr, "Unable to allocate memory for image data.\n");
        return;
    }
    memset(image, 0, image_size);
    for (int y = 0; y < height; y++) {
        for (int x = 0; x < width; x++) {
            int part = floor(x / 8);
            if (array[y][part] >> (x % 8) & 1U) {
                size_t byte_index = (y * width + x) / 8;
                size_t bit_index = 7 - ((y * width + x) % 8);
                image[byte_index] |= (1 << bit_index); 
            }
        }
    }

    unsigned error = lodepng_encode_file(filename, image, width, height, 0, 1);
    if (error) {
        fprintf(stderr, "Error %u: %s\n", error, lodepng_error_text(error));
    }

    free(image);
}
