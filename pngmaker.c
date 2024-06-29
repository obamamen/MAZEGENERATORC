#include <stdio.h>
#include <stdlib.h>
#include "lodepng.c"


// Function to create PNG from array using lodepng
void create_png_from_array(const char *filename, int width, int height, unsigned char **array) {
    unsigned char *image = NULL;
    size_t image_size = (width * height + 7) / 8; // Each byte contains 8 pixels

    // Allocate memory for the packed image data
    image = (unsigned char *)malloc(image_size);
    if (!image) {
        fprintf(stderr, "Unable to allocate memory for image data.\n");
        return;
    }
    
    // Initialize image data to zero
    memset(image, 0, image_size);

    // Fill image data with black and white pixels
    for (int y = 0; y < height; y++) {
        for (int x = 0; x < width; x++) {
            if (array[y][x]) {
                //printf("at pixel (%d, %d)", x,y);
                size_t byte_index = (y * width + x) / 8;
                size_t bit_index = 7 - ((y * width + x) % 8);
                image[byte_index] |= (1 << bit_index); // Set the corresponding bit
            }
        }
    }

    // Encode the image to PNG format using lodepng with 1-bit depth
    unsigned error = lodepng_encode_file(filename, image, width, height, 0, 1);
    if (error) {
        fprintf(stderr, "Error %u: %s\n", error, lodepng_error_text(error));
    }

    // Free allocated memory
    free(image);
}
