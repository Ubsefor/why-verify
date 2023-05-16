#include "map.h"

// Map: { items, capacity, count }
// Items: { Key, Value, int present }
//   Key: { int, int }
//   value: { int, int }


  // makes
int initializeMap(Map *map, int size){
  if (size < 0 || map == NULL){
    return 1;
  }

  map->capacity = size;

  map->count = 0;

  map->items = calloc(size, sizeof(Item));

  if (map->items == NULL) {
    return 1;
  }

  return 0;
};

  // frees, not including map
void finalizeMap(Map *map){
  if (map == NULL){
    return ;
  }
  if (map->items == NULL){
    return ;
  }
  for (int i = 0; i < map->capacity; i++){
    map->items[i].existent = 0;
  }
  free(map->items);
  map->items = NULL;
};

int addElement(Map *map, Key *key, Value *value){
  if (map == NULL)
    return -1;

  if (map->items == NULL)
    return -1;

  for (int i = 0; i < map->capacity; i++){
    if ((map->items[i].key.a == key->a) &&
        (map->items[i].key.b == key->b)) {

      map->items[i].key = *key;
      map->items[i].value = *value;
      map->items[i].existent = 1;

      return 1;
    }
  }

  if (map->count == map->capacity)
    return 0;

  for (int i = 0; i < map->capacity; i++){
    if (map->items[i].existent == 0) {
      map->items[i].key = *key;
      map->items[i].value = *value;
      map->items[i].existent = 1;
      map->count += 1;
      return 1;
    }
  }
};

int removeElement(Map *map, Key *key, Value *value){
  if (map == NULL)
    return -1;

  if (map->items == NULL)
    return -1;

  int end = 0;

  for (int i = 0; i < map->capacity; i++){
    if (map->items[i].key.a == key->a && map->items[i].key.b == key->b && map->items[i].existent == 1){
      map->count -= 1;
      // write removed value if not NULL
      if (value != NULL) {
        *value = map->items[i].value;
      }

      // removed last element?
      if (i == map->capacity - 1){
        map->items[i].existent = 0;
        return 1;
      }

      // swap last existing element with removed one
      int end = 0;
      for (int j = i; j < map->capacity; j++){
        if (map->items[j].existent == 1){
          end = j;
        }
      }
      map->items[i].key = map->items[end].key;
      map->items[i].value = map->items[end].value;
      map->items[end].existent = 0;

      return 1;
    }
  }
  // miss
  return 0;
};

int getElement(Map *map, Key *key, Value *value){
  if (map == NULL)
    return -1;

  if (map->items == NULL)
    return -1;

  if (key == NULL)
    return -1;

  if (value == NULL)
    return -1;

  for (int i = 0; i < map->capacity; i++){
    if (map->items[i].existent == 1 && map->items[i].key.a == key->a && map->items[i].key.b == key->b){
      *value = map->items[i].value;
      return 1;
    }
  }
  return 0;
};
