#include "map.h"

// Map: { items, capacity, count }
// Items: { Key, Value, int present }
//   Key: { int, int }
//   value: { int, int }


  // makes
int initializeMap(Map *map, int size){
  map->capacity = size;

  map->count = 0;

  map->items = calloc(size, sizeof(Item));

  for(int i = 0; i < map->capacity; i++){
    map->items[i].existent = 0;
  }

  return (map->items == NULL) ? 0 : 1;;
};

  // frees, including map
void finalizeMap(Map *map){
  for (int i = 0; i < map->capacity; i++){
    map->items[i].existent = 0;
  }
  free(map->items);
  map->items = NULL;
  free(map);
  map = NULL;
};

int addElement(Map *map, Key *key, Value *value){
  return 0;
};

int removeElement(Map *map, Key *key, Value *value){
  return 0;
};

int getElement(Map *map, Key *key, Value *value){
  return 0;
};

int main(int argc, const char* argv[]){
  Map* test = calloc(1, sizeof(Map));
  initializeMap(test, 10);
  finalizeMap(test);

  return 0;
}