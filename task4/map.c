#include "map.h"

// Map: { items, capacity, count }
// Items: { Key, Value, int present }
//   Key: { int, int }
//   value: { int, int }

/*@
  requires is_valid_map(map);
  requires 0 <= map->capacity <= INT_MAX;

  allocates \nothing;
  assigns \nothing;

  ensures is_valid_map(map);
  ensures \result == count(map, 0, map->capacity);
  ensures \result == count_exist(map);
  ensures \result >= 1 ==> map->items[0].existent == 1;
*/
int _count_linker(Map *map){
  int cnt = 0;
  /*@
    loop invariant 0 <= i;
    loop invariant i <= map->capacity;
    loop invariant 0 <= cnt <= map->capacity;
    loop invariant cnt <= i;
    loop invariant cnt == count(map, 0, i);
    loop variant map->capacity - i;
  */
  for (int i = 0; i < map->capacity; i++){
    //@ assert \at(i, LoopCurrent) <= map->capacity;
    map->items[i].existent == 1 ? cnt++ : cnt;
  }
  return cnt;
}

/*@
  requires is_valid_map(map);
  requires 0 <= map->capacity <= INT_MAX;
  requires 0 <= m <= n < map->capacity;

  allocates \nothing;
  assigns \nothing;

  ensures is_valid_map(map);
  ensures \result == count(map, m, n);
*/
int _count_linker_2(Map *map, int m, int n){
  int cnt;
  /*@
    loop invariant 0 <= i;
    loop invariant i <= map->capacity;
    loop invariant 0 <= cnt <= map->capacity;
    loop invariant cnt <= i;
    loop invariant cnt == count(map, 0, i);
    loop variant m - i;
  */
  for (int i = 0; i < m; i++){
    //@ assert \at(i, LoopCurrent) <= map->capacity;
    map->items[i].existent == 1 ? cnt++ : cnt;
  }
  /*@
    loop invariant 0 <= i;
    loop invariant i <= map->capacity;
    loop invariant 0 <= cnt <= map->capacity;
    loop invariant cnt <= i;
    loop invariant cnt == count(map, m, i);
    loop variant n - i;
  */
  for (int i = m; i <= n; i++){
    //@ assert \at(i, LoopCurrent) <= map->capacity;
    map->items[i].existent == 1 ? cnt++ : cnt;
  }
  return cnt;
}

  // makes map
int initializeMap(Map *map, int size){
  if (size < 0 || map == NULL){
    return 1;
  }

  map->capacity = size;

  map->count = 0;

  map->items = malloc(size * sizeof(Item));

  if (map->items == NULL) {
    return 1;
  }

  for (int i = 0; i < size; i++){
    map->items[i].existent = 0;
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
  /*@
    loop invariant 0 <= i <= map->capacity;
    loop invariant is_valid_map_mem(map);
    // loop invariant is_valid_items(map);
    loop invariant all_valid_existence(map);
    loop variant map->capacity - i;
  */
  for (int i = 0; i < map->capacity; i++){
    map->items[i].existent = 0;
    //@ assert valid_existence(get_item(map, i));
  }
  //@ assert \at(map->capacity, Pre) == \at(map->capacity, Here);
  map->count = 0;
  //@ assert 0 <= \at(map->count, Here) <= \at(map->count, Pre);
  free(map->items);
  //@ assert \allocable(map->items);
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

  if (key == NULL)
    return -1;

  int end = 0;

  //@ assert count_ok(map);

  /*@
    loop invariant i >= 0;
    loop invariant 0 <= map->count <= map->capacity;
    loop invariant \valid(map->items + (0..map->capacity - 1));
    loop invariant \at(map->count, Pre) == \at(map->count, Here);
    loop invariant \forall integer j; (0 <= j < i) ==>
      !(equal_keys_now{Here}(get_key{Here}(get_item{Here}(map, j)), key) &&
      item_exists{Here}(get_item{Here}(map, j)));
    loop invariant is_valid_map(map); // он это почему то не сплиттит и боркается
    // loop invariant is_valid_map_mem(map);
    // loop invariant is_valid_map_sizes(map);
    // loop invariant is_valid_items(map);
    // loop invariant count_ok(map);
    // loop invariant begin_ok(map);
    // loop invariant unique_keys(map);
    // loop invariant all_valid_existence(map);
    // loop invariant gap_ok(map);

    loop invariant compare_values{Pre, Here}(value, value);
    loop invariant equal_keys{Pre, Here}(key, key);
    loop invariant no_new{Pre, Here}(map);
    loop invariant same_count{Pre, Here}(map);
    loop invariant same_items{Pre, Here}(map);
    loop variant map->capacity - i;
  */
  for (int i = 0; i < map->capacity; i++){
    //@ assert i <= map->capacity - 1;
    if (map->items[i].key.a == key->a && map->items[i].key.b == key->b && map->items[i].existent == 1){

      //@ assert count_ok(map);
      //@ assert (i + 1) <= map->capacity;
      //@ assert count(map, 0, i) + count(map, i, map->capacity) == count(map, 0, map->capacity);
      //@ assert count(map, i, i+1) + count(map, i+1, map->capacity) == count(map, i, map->capacity);
      //@ assert count(map, i, i+1) == 1;
      //@ assert i < map->capacity;

      /*@ghost
        int cnt = 0;
        /@
          loop invariant 0 <= j <= map->capacity;
          loop invariant 0 <= cnt <= map->capacity;
          loop invariant cnt <= j;
          loop variant i - j;
        @/
        for (int j = 0; j <= i; j++) {
          //@ assert cnt <= j;
          //@ assert j <= i;
          map->items[i].existent == 1 ? cnt++ : cnt;
          //@ assert cnt == count(map, 0, j + 1);
        }
        //@ assert cnt >= 0;
        //@ assert cnt <= i;
        //@ assert cnt == count(map, 0, i);
        //@ assert count(map, 0, i) >= 0;
      */

      //@ assert count(map, i, map->capacity) >= 0;
      //@ assert count(map, i+1, map->capacity) >= 0;
      //@ assert count(map, 0, i) >= 0;
      //@ assert count(map, i, map->capacity) >= 1;
      //@ assert count(map, 0, map->capacity) >= 1;

      //@ assert \at(map->count, Here) >= 1;
      map->count -= 1;
      //@ assert 0 <= \at(map->count, Here) < \at(map->capacity, Pre);

      // write removed value if not NULL
      if (value != NULL) {
        *value = map->items[i].value;
      }

      // removed last element?
      if (i == map->capacity - 1){
        map->items[i].existent = 0;
        //@ assert !is_key_in_map{Here}(map, key);
        return 1;
      }

      // swap last existing element with removed one
      int end = 0;
      /*@
        loop invariant j >= 0;
        loop invariant j >= i;
        loop invariant i <= map->capacity;
        loop invariant j <= map->capacity;
        loop invariant 0 <= end <= j;
        loop invariant 0 <= end <= map->capacity - 1;
        loop invariant map->count <= map->capacity;
        loop invariant \valid(map->items + (0..map->capacity - 1));
        loop variant map->capacity - j;
      */
      for (int j = i; j < map->capacity; j++){
        if (map->items[j].existent == 1){
          end = j;
        }
      }
      map->items[i].key = map->items[end].key;
      map->items[i].value = map->items[end].value;
      map->items[end].existent = 0;

      //@ assert !is_key_in_map{Here}(map, key);
      //@ assert count_ok{Here}(map);
      return 1;
    }
  }

  //@ assert no_new{Pre, Here}(map);
  //@ assert !is_key_in_map(map, key);
  //@ assert same_count{Pre, Here} (map);
  //@ assert same_capacity{Pre, Here} (map);
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

  /*@
    loop invariant 0 <= i <= map->capacity;
    loop invariant \valid(map->items + (0..map->capacity - 1));
    loop invariant compare_values{Pre, Here}(value, value);
    loop invariant \forall integer j; (0 <= j < i) ==>
      !(equal_keys_now{Here}(get_key{Here}(get_item{Here}(map, j)), key) &&
      item_exists{Here}(get_item{Here}(map, j)));
    loop variant map->capacity - i;
  */
  for (int i = 0; i < map->capacity; i++){
    if (map->items[i].existent == 1 && map->items[i].key.a == key->a && map->items[i].key.b == key->b){
      if (value == NULL)
        return -1;
      *value = map->items[i].value;
      return 1;
    }
  }
  return 0;
};
