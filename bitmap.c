#include <stdio.h>
#include <stdlib.h>

#pragma pack(push, 1)
typedef struct {
    unsigned short bfType;
    unsigned int bfSize;
    unsigned short bfReserved1;
    unsigned short bfReserved2;
    unsigned int bfOffBits;
} BITMAPFILEHEADER;

typedef struct {
    unsigned int biSize;
    int biWidth;
    int biHeight;
    unsigned short biPlanes;
    unsigned short biBitCount;
    unsigned int biCompression;
    unsigned int biSizeImage;
    int biXPelsPerMeter;
    int biYPelsPerMeter;
    unsigned int biClrUsed;
    unsigned int biClrImportant;
} BITMAPINFOHEADER;

typedef struct {
    unsigned char rgbBlue;
    unsigned char rgbGreen;
    unsigned char rgbRed;
    unsigned char rgbReserved;
} RGBQUAD;
#pragma pack(pop)

void create_1bit_bmp_from_array(const char *filename, int width, int height, unsigned char **array) {
    int paddedRowSize = (width + 31) / 32 * 4;
    int fileSize = 54 + 8 + paddedRowSize * height;

    BITMAPFILEHEADER fileHeader = {0};
    fileHeader.bfType = 0x4D42; // 'BM'
    fileHeader.bfSize = fileSize;
    fileHeader.bfOffBits = 54 + 8;

    BITMAPINFOHEADER infoHeader = {0};
    infoHeader.biSize = 40;
    infoHeader.biWidth = width;
    infoHeader.biHeight = height;
    infoHeader.biPlanes = 1;
    infoHeader.biBitCount = 1;
    infoHeader.biCompression = 0;
    infoHeader.biSizeImage = paddedRowSize * height;
    infoHeader.biXPelsPerMeter = 2835;
    infoHeader.biYPelsPerMeter = 2835;
    infoHeader.biClrUsed = 2;
    infoHeader.biClrImportant = 2;

    RGBQUAD palette[2] = {{0, 0, 0, 0}, {255, 255, 255, 0}};

    unsigned char *bitmapData = (unsigned char *)calloc(infoHeader.biSizeImage, 1);
    if (bitmapData == NULL) {
        printf("Unable to allocate memory for bitmap data.\n");
        return;
    }

    for (int y = 0; y < height; y++) {
        for (int x = 0; x < width; x++) {
            int byteIndex = (x / 8) + paddedRowSize * y;
            int bitIndex = x % 8;
            if (array[height - y - 1][x]) { // Note: BMP files are bottom to top
                bitmapData[byteIndex] |= (1 << (7 - bitIndex)); // Set bit to 1 (white)
            } else {
                bitmapData[byteIndex] &= ~(1 << (7 - bitIndex)); // Set bit to 0 (black)
            }
        }
    }

    FILE *file = fopen(filename, "wb");
    if (file == NULL) {
        printf("Unable to open file %s for writing.\n", filename);
        free(bitmapData);
        return;
    }

    fwrite(&fileHeader, sizeof(fileHeader), 1, file);
    fwrite(&infoHeader, sizeof(infoHeader), 1, file);
    fwrite(&palette, sizeof(palette), 1, file);
    fwrite(bitmapData, infoHeader.biSizeImage, 1, file);

    fclose(file);
    free(bitmapData);
}