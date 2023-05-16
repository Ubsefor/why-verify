#include "map.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#define UNMAP(ptr) free(ptr.items); \
                   ptr.items = NULL;

void print_map(Map *map){
  printf("Map indexes:\n");
  for (int i = 0; i < map->capacity; i++){
    printf("%d ", i);
  }
  printf("\nMap capacity:\n%d\n", map->capacity);
  printf("Map count:\n%d\n", map->count);
  printf("Map elements:\n");
  for (int i = 0; i < map->capacity; i++){
    printf("Key: %d %d\t Value: %d %d\t Exists: %d\n",
    map->items[i].key.a,
    map->items[i].key.b,
    map->items[i].value.c,
    map->items[i].value.d,
    map->items[i].existent);
  }
}

bool test_init(void){
  Map test;
  int ok = initializeMap(&test, 10);

  assert(test.items != NULL);
  assert(ok == 0);
  assert(test.capacity == 10);
  assert(test.count == 0);

  UNMAP(test);

  return true;
}

bool test_init_null(void){
  Map test;

  assert(initializeMap(&test, 0) == 0);
  assert(test.items != NULL);
  assert(test.capacity == 0);
  assert(test.count == 0);
  assert(initializeMap(NULL, 1));

  UNMAP(test);

  return true;
}

bool test_init_neg(void){
  Map test;

  assert(initializeMap(&test, -123) == 1);
  assert(test.items == NULL);

  UNMAP(test);

  return true;
}

bool test_finalize(void){
  Map test;
  initializeMap(&test, 10);

  finalizeMap(&test);
  assert(test.items == NULL);
  assert(&test != NULL);

  return true;
}

bool test_finalize_empty(void){
  Map test;
  initializeMap(&test, 0);

  finalizeMap(&test);
  assert(test.items == NULL);
  assert(&test != NULL);

  return true;
}

bool test_finalize_items_null(void){
  void* test = NULL;

  finalizeMap(test);
  assert(test == NULL);

  return true;
}

bool test_finalize_null(void){
  Map test;
  test.items = NULL;

  finalizeMap(&test);
  assert(test.items == NULL);

  return true;
}

bool addElement_test(void){
  Map test;
  initializeMap(&test, 2);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  Key key_test2;
  key_test2.a = 1;
  key_test2.b = 5;

  assert(addElement(&test, &key_test, &val_test));
  assert(addElement(&test, &key_test2, &val_test));
  print_map(&test);
  assert(test.items != NULL);
  assert(test.items[0].key.a == 1);
  assert(test.items[0].key.b == 2);
  assert(test.items[0].value.c == 3);
  assert(test.items[0].value.d == 4);
  assert(test.items[0].existent == 1);
  assert(test.items[1].key.a == 1);
  assert(test.items[1].key.b == 5);
  assert(test.items[1].value.c == 3);
  assert(test.items[1].value.d == 4);
  assert(test.items[1].existent == 1);
  assert(test.count == 2);

  UNMAP(test);

  return true;
}

bool addElement_test_null(void){
  Map test;
  test.items = NULL;

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  assert(addElement(&test, &key_test, &val_test) == -1);
  assert(&test != NULL);

  assert(addElement(NULL, &key_test, &val_test) == -1);

  return true;
}

bool addElement_test_none(void){
  Map test;
  initializeMap(&test, 0);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  assert(addElement(&test, &key_test, &val_test) == 0);
  assert(test.items != NULL);

  UNMAP(test);

  return true;
}

bool addElement_test_same(void){
  Map test;
  initializeMap(&test, 1);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  assert(addElement(&test, &key_test, &val_test) == 1);
  assert(addElement(&test, &key_test, &val_test) == 1);
  assert(test.items != NULL);
  assert(test.items[0].key.a == 1);
  assert(test.items[0].key.b == 2);
  assert(test.items[0].value.c == 3);
  assert(test.items[0].value.d == 4);
  assert(test.items[0].existent == 1);
  assert(test.count == 1);

  UNMAP(test);

  return true;
}

bool addElement_test_full(void){
  Map test;
  initializeMap(&test, 1);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  assert(addElement(&test, &key_test, &val_test) == 1);

  Key key_test2;
  key_test2.a = 5;
  key_test2.b = 6;
  Value val_test2;
  val_test2.c = 7;
  val_test2.d = 8;

  assert(addElement(&test, &key_test2, &val_test2) == 0);

  UNMAP(test);

  return true;
}

bool removeElement_test(void){
  Map test;
  initializeMap(&test, 1);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  Value val_ret;
  val_ret.c = 0;
  val_ret.d = 0;

  assert(addElement(&test, &key_test, &val_test) == 1);
  assert(removeElement(&test, &key_test, &val_ret) == 1);
  assert(val_ret.c == 3);
  assert(val_ret.d == 4);

  UNMAP(test);

  return true;
}

bool removeElement_test_miss(void){
  Map test;
  initializeMap(&test, 1);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  Value val_ret;
  val_ret.c = 0;
  val_ret.d = 0;

  assert(addElement(&test, &key_test, &val_test) == 1);
  key_test.b = 5;

  Key key_test2;
  key_test2.a = 3;
  key_test2.b = 4;
  Value val_test2;
  val_test2.c = 3;
  val_test2.d = 4;
  assert(removeElement(&test, &key_test, &val_ret) == 0);
  assert(removeElement(&test, &key_test2, &val_ret) == 0);
  assert(val_ret.c == 0);
  assert(val_ret.d == 0);

  UNMAP(test);

  return true;
}

bool removeElement_test_none(void){
  Map test;
  initializeMap(&test, 1);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  Value val_ret;
  val_ret.c = 0;
  val_ret.d = 0;


  assert(addElement(&test, &key_test, &val_test) == 1);
  assert(removeElement(&test, &key_test, &val_test) == 1);
  assert(removeElement(&test, &key_test, &val_ret) == 0);
  assert(val_ret.c == 0);
  assert(val_ret.d == 0);

  UNMAP(test);

  return true;
}

bool removeElement_test_empty(void){
  Map test;
  initializeMap(&test, 0);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  assert(removeElement(&test, &key_test, &val_test) == 0);

  UNMAP(test);

  return true;
}

bool removeElement_test_null(void){
  Map test;
  initializeMap(&test, 1);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  void* val_ret = NULL;

  assert(addElement(&test, &key_test, &val_test) == 1);
  assert(removeElement(&test, &key_test, val_ret) == 1);
  assert(val_ret == NULL);

  UNMAP(test);

  return true;
}

bool removeElement_test_nullmap(void){
  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  // assert(addElement(&test, &key_test, &val_test) == 1);

  assert(removeElement(NULL, &key_test, &val_test) == -1);

  return true;
}

bool removeElement_test_nullitems(void){
  Map test;
  test.items = NULL;

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  // assert(addElement(&test, &key_test, &val_test) == 1);

  assert(removeElement(&test, &key_test, &val_test) == -1);
  assert(&test != NULL);
  assert(test.items == NULL);

  UNMAP(test);

  return true;
}

bool removeElement_test_space(void){
  Map test;
  initializeMap(&test, 4);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  Key key_test2;
  key_test2.a = 10;
  key_test2.b = 20;
  Value val_test2;
  val_test2.c = 30;
  val_test2.d = 40;

  Key key_test3;
  key_test3.a = 100;
  key_test3.b = 200;
  Value val_test3;
  val_test3.c = 300;
  val_test3.d = 400;

  Key key_test4;
  key_test4.a = 1000;
  key_test4.b = 2000;
  Value val_test4;
  val_test4.c = 3000;
  val_test4.d = 4000;

  Value val_ret1;
  val_ret1.c = 0;
  val_ret1.d = 0;

  Value val_ret2;
  val_ret2.c = 0;
  val_ret2.d = 0;

  // make array: 1 2 3 4
  assert(addElement(&test, &key_test, &val_test) == 1);
  assert(addElement(&test, &key_test2, &val_test2) == 1);
  assert(addElement(&test, &key_test3, &val_test3) == 1);
  assert(addElement(&test, &key_test4, &val_test4) == 1);
  // make a space: 1 0 0 4
  // should result in: 1 4 3 0
  assert(removeElement(&test, &key_test2, &val_ret1) == 1);
  assert(val_ret1.c == 30);
  assert(val_ret1.d == 40);
  assert(test.items[1].key.a == key_test4.a);
  assert(test.items[1].key.b == key_test4.b);
  assert(test.items[2].key.a == key_test3.a);
  assert(test.items[2].key.b == key_test3.b);
  assert(test.items[2].existent == 1);
  assert(test.items[3].existent == 0);
  assert(test.count == 3);

  // should result in: 1 4 0 0
  assert(removeElement(&test, &key_test3, &val_ret2) == 1);
  assert(val_ret2.c == 300);
  assert(val_ret2.d == 400);
  assert(test.items[1].key.a == key_test4.a);
  assert(test.items[1].key.b == key_test4.b);
  assert(test.items[2].existent == 0);
  assert(test.items[3].existent == 0);
  assert(test.count == 2);

  assert(test.capacity == 4);

  UNMAP(test);

  return true;
}

bool getElement_test(void){
  Map test;
  initializeMap(&test, 4);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  Key key_test2;
  key_test2.a = 10;
  key_test2.b = 20;
  Value val_test2;
  val_test2.c = 30;
  val_test2.d = 40;

  Value val_ret1;
  val_ret1.c = 0;
  val_ret1.d = 0;

  // make array: 1 2 0 0
  assert(addElement(&test, &key_test, &val_test) == 1);
  assert(addElement(&test, &key_test2, &val_test2) == 1);

  assert(getElement(&test, &key_test, &val_ret1) == 1);
  assert(val_ret1.c == val_test.c);
  assert(val_ret1.d == val_test.d);
  assert(test.count == 2);
  assert(test.capacity == 4);

  UNMAP(test);

  return true;
}

bool getElement_test_miss(void){
  Map test;
  initializeMap(&test, 4);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  Key key_test2;
  key_test2.a = 10;
  key_test2.b = 20;
  Value val_test2;
  val_test2.c = 30;
  val_test2.d = 40;

  Value val_ret1;
  val_ret1.c = 0;
  val_ret1.d = 0;

  // make array: 1 2 0 0
  assert(addElement(&test, &key_test, &val_test) == 1);

  assert(getElement(&test, &key_test2, &val_ret1) == 0);
  assert(val_ret1.c == 0);
  assert(val_ret1.d == 0);
  assert(test.count == 1);
  assert(test.capacity == 4);

  key_test.b = 5;

  assert(getElement(&test, &key_test, &val_ret1) == 0);
  assert(val_ret1.c == 0);
  assert(val_ret1.d == 0);
  assert(test.count == 1);
  assert(test.capacity == 4);

  UNMAP(test);

  return true;
}

bool getElement_test_nullmap(void){
  Key key_test2;
  key_test2.a = 10;
  key_test2.b = 20;
  Value val_test2;
  val_test2.c = 30;
  val_test2.d = 40;

  Value val_ret1;
  val_ret1.c = 0;
  val_ret1.d = 0;

  assert(getElement(NULL, &key_test2, &val_ret1) == -1);

  return true;
}

bool getElement_test_nullitems(void){
  Map test;
  test.items = NULL;

  Key key_test2;
  key_test2.a = 10;
  key_test2.b = 20;
  Value val_test2;
  val_test2.c = 30;
  val_test2.d = 40;

  Value val_ret1;
  val_ret1.c = 0;
  val_ret1.d = 0;

  assert(getElement(&test, &key_test2, &val_ret1) == -1);

  return true;
}

bool getElement_test_null(void){
  Map test;
  initializeMap(&test, 4);

  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;

  assert(getElement(&test, &key_test, NULL) == -1);
  assert(getElement(&test, NULL, &val_test) == -1);
  assert(getElement(&test, NULL, NULL) == -1);

  UNMAP(test);

  return true;
}


int main(int argc, const char* argv[]){
  Map test;

  // test print to see that program worked
  initializeMap(&test, 10);
  Key key_test;
  key_test.a = 1;
  key_test.b = 2;
  Value val_test;
  val_test.c = 3;
  val_test.d = 4;
  addElement(&test, &key_test, &val_test);
  print_map(&test);
  removeElement(&test, &key_test, &val_test);
  finalizeMap(&test);

  assert(test_init());
  assert(test_init_null());
  assert(test_init_neg());

  assert(test_finalize());
  assert(test_finalize_empty());
  assert(test_finalize_null());
  assert(test_finalize_items_null());

  assert(addElement_test());
  assert(addElement_test_none());
  assert(addElement_test_null());
  assert(addElement_test_same());
  assert(addElement_test_full());

  assert(removeElement_test());
  assert(removeElement_test_miss());
  assert(removeElement_test_none());
  assert(removeElement_test_empty());
  assert(removeElement_test_null());
  assert(removeElement_test_nullmap());
  assert(removeElement_test_nullitems());
  assert(removeElement_test_space());

  assert(getElement_test());
  assert(getElement_test_miss());
  assert(getElement_test_nullmap());
  assert(getElement_test_nullitems());
  assert(getElement_test_null());

  return 0;
}