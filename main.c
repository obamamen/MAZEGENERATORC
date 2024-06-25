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

int width = 16;
int height = 16;


int main() {
    unsigned char **image = allocate_and_initialize_image(width, height);
    unsigned short **maze = allocate_and_initialize_maze(width, height);






    create_1bit_bmp_from_array("output_1bit.bmp", width, height, image);
    free_array(image, height);
    return 0;
}
