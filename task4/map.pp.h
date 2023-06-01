// LCOV_EXCL_START
// #ifndef __MAP_H__
// #define __MAP_H__

// #include "maptypes.h"
// #include <stdio.h>
// #include <stdlib.h>
// #include <stdbool.h>
// #include <limits.h>

/*
  Вариант А

  Формальная спецификация.

  Для типов данных:

  a) Формальная спецификация структуры Map:

  a1) Структура может хранить лишь единственное отображение для конкретного ключа (нет одинаковых ключей).
  a2) map->items структуры Map представляет собой массив длины map->capacity.
  a3) map->count == количеству элементов items с полем existent == 1.
  a4) При работе со структурой учитываются те и только те записи массива items,
    которые имеют поле item->existent установленным в истину (item->existent == 1).
  a5) 0 <= map->count <= map->capacity – количество "занятых" отображений меньше размера массива этих отображений
  a6) Отображения в map->items могут храниться с пропусками; При этом за двумя последовательно идущими элементами,
    у которых item->existent установлено в ложь, остальные элементы тоже имеют item->existent установленным в ложь
  a7) Элементы map->items хранятся с начала массива.

  b) Формальная спецификация структуры Item:

  // (b0 Item – структура, содержащая поле existent и пару значений: структуры Key и Value)
  b1) Поле existent может принимать значения 0 или 1 (false или true соответственно).
  b2) При item->existent == 0 содержимое остальных полей не учитывается при работе с структурой Map

  c) Формальная спецификация структуры Key:

  c1) Есть два поля размера int: key->a и key->b

  d) Формальная спецификация структуры Value:

  d1) Есть два поля размера int: value->c и value->d


  Для функций: (finalizeMap, removeElement, getElement)

  A. finalizeMap:

  A1) Функция finalizeMap() освобождает динамическую память, используемую для ассоциативного массива map
  A2) На вход функции должен подаваться указатель на область памяти, проинициализированную функцией initializeMap()
    (на валидную структуру Map)
  A3) После работы функции map->items == NULL
  A4) После работы функции map->items освобожден
  A5) После работы функции структура map по указателю – не валидная
  A6) Переданный функции указатель на память не портится
  A7) Функция ничего не аллоцирует
  A8) Функция не трогает count и capacity (норм, поскольку мапа все равно не валидная становится)

  B. removeElement:

  B1) Функция removeElement() удаляет сохранённое в ассоциативном массиве map значение по заданному ключу key (если оно там было)
  // после работы функции элемента нет
  B2) Функция не удаляет другие отображения // после работы функции элементы остались как были
  B3) Функция не добавляет новые отображения. // после работы функции не появилось новых (count не изменился?)
  B4) Функция возвращает истину (единицу), если функция изменила ассоциативный массив, ложь (ноль) в противном случае.
  B5) Если переданный value != NULL ==> туда пишется значение удаленного отображения
  B6) Функция имеет право изменять структуру ассоциативного массива, если это не отражается на содержащихся в нём парах.
  // все существовавшие до удаления отображения (кроме удаляемого) остаются в массиве
  B7) Ничего другого функция не делает.
  // не освобождает память, не меняет существующие отображения... см B6
  B8) map->count-- если элемент был удален или map->count остался таким же, если ничего не удалилось
  B9) map->capacity остался таким же
  B10) указатели на map и map->items не портятся, память не перевыделяется и не освобождается
  B11) Переданные в функцию значения – валидные (map валидный, key валидный, value валидный или NULL)

  C. getElement:

  C1) Функция getElement() возвращает по указателю value сохранённое в ассоциативном массиве map значение для заданного ключа key
  C2) и возвращает истину (единицу), если заданный ассоциативный массив имеет отображения для заданного ключа.
  C3) В случае, если значение по заданному ключу не содержится в отображении, возвращается ложь (ноль) и ничего другого не происходит.
  C4) Функция не меняет ассоциативный массив
  // все существовавшие отображения остаются в массиве
  C5) и переданный ключ.
  // key не перетирается и не меняется
  C6) map->capacity не меняется
  C7) map->count не меняется
  С8) map остается валидным
  C9) Переданные в функцию значения – валидные (map валидный, key валидный, value – указатель на валидную память), остаются валидными
  // ничего другого функция не делает
  С10) Функции передается на вход валидный map,
  C11) Ничего не выделяет
  С12) ничего не освобождает

*/

/*@
  logic integer count{L}(Map *map, integer m, integer n) = // посчитать все existent в Map от m до n
    m >= n ? (0) : ( (map->items[m].existent ? 1 : 0) + count(map, m + 1, n));
  logic integer count_exist(Map *map) = count(map, 0, map->capacity); // посчитать все existent в Map

  lemma count_zero: \forall Map *map, integer  m, n; m >= n ==> count(map, m, n) == 0; // пограничные штуки для count = 0
  lemma count_one: \forall Map *map, integer  m; count(map, m, m + 1) == (map->items[m].existent ? 1 : 0); // и count == 1*/
// */

/*@

  predicate is_valid_map_mem (Map *map) =
    \valid(map) &&
    \offset_max(map->items) == map->capacity - 1 &&
    !\valid(map->items + map->capacity) && // проверка а2
    \valid(map->items + (0..map->capacity - 1)); // check map ptr is valid + map->items mem is valid

  predicate is_valid_map_sizes (Map *map) =
    0 <= map->count <= map->capacity <= 0x7fffffff; // проверка a5

  predicate begin_ok (Map *map) =
    map->count > 0 ==> map->items[0].existent == 1; // проверка a7

  predicate is_valid_item (Map *map, integer idx) =
    ((is_valid_map_mem(map)) &&
    is_valid_map_sizes(map) &&
    (0 <= idx < map->capacity)) ==>
      (0 == map->items[idx].existent) // проверка b2, c1, d1
      ||
      (1 == map->items[idx].existent ==>
      ((-0x7fffffff - 1) <= map->items[idx].key.a <= 0x7fffffff &&
      (-0x7fffffff - 1) <= map->items[idx].key.b <= 0x7fffffff &&
      (-0x7fffffff - 1) <= map->items[idx].value.c <= 0x7fffffff &&
      (-0x7fffffff - 1) <= map->items[idx].value.d <= 0x7fffffff)
    );

  predicate count_ok (Map *map) =
    count_exist(map) == map->count; // проверка a3

  predicate gap_ok(Map *map) =
    \forall integer i, j;
      ((i + 1 < j < map->capacity) &&
      (0 <= i < map->capacity - 1)) &&
      ((map->items[i].existent == 0) &&
      (map->items[i + 1].existent == 0)) ==>
        map->items[j].existent == 0;  // проверка a6
        // (следующий элемент после двух пропусков: existent == 0)

  predicate is_valid_items (Map *map) =
    \forall integer i; 0 <= i < map->capacity ==> // проверка a4
      is_valid_item(map, i);

  predicate compare_keys_now (Key *k1, Key *k2) =
    (k1->a == k2->a) &&
    (k1->b == k2->b);  // сравнение ключей

  predicate compare_values_now (Value *v1, Value *v2) =
    (v1->c == v2->c) &&
    (v1->d == v2->d);  // сравнение значений

  predicate compare_keys{L1, L2} (Key *k1, Key *k2) =
    (\at(k1->a, L1) == \at(k2->a, L2)) &&
    (\at(k1->b, L1) == \at(k2->b, L2));  // сравнение ключей (+ по временным меткам)

  predicate compare_values{L1, L2} (Value *v1, Value *v2) =
    (\at(v1->c, L1) == \at(v2->c, L2)) &&
    (\at(v1->d, L1) == \at(v2->d, L2)); // сравнение значений (+ по временным меткам)

  predicate valid_existence (Item *it) =
    0 <= it->existent <= 1; // existence is _Bool, проверка b1

  predicate item_exists (Item *it) =
    it->existent == 1; // existent == 1 ?

  predicate item_exists_t {L} (Item *it) =
    \at(it->existent, L)  == 1; // как предыдущее, только в момент времени

  logic Key* get_key (Item *it) =
    &it->key; // получает ключ из item

  logic Key* get_key_t {L} (Item *it) =
    \at(&it->key, L); // как предыдущее, только в момент времени

  logic Value* get_value (Item *it) =
    &it->value; // получает значение из item

  logic Value* get_value_t {L} (Item *it) =
    \at(&it->value, L); // как предыдущее, только в момент времени

  logic Item* get_item (Map *map, integer idx) =
    &map->items[idx]; // получает item по индексу в map

  logic Item* get_item_t {L} (Map *map, integer idx) =
    \at(&map->items[idx], L); // как предыдущее, только в момент времени

  predicate all_valid_existence (Map *map) =
    \forall integer i;
      0 <= i <= map->capacity ==>
        valid_existence(get_item(map, i)); // проверка b1

  predicate unique_keys (Map *map) =
    \forall integer i, j;
      (0 <= i < map->capacity) &&
      (map->capacity > j > i) &&
      (item_exists(get_item(map, i))) &&
      (item_exists(get_item(map, j))) ==>
        !(compare_keys_now(get_key(get_item(map, i)), get_key(get_item(map, j)))); // проверка a1

  predicate compare_items{L1, L2} (Item *i1, Item *i2) =
    compare_keys{L1, L2}(\at(&i1->key, L1), \at(&i2->key, L2)) &&
    compare_values{L1, L2}(\at(&i1->value, L1), \at(&i2->value, L2)); // сравнение значений item

  predicate count_lowers{L1, L2} (Map *map) =
    \at(map->count, L1) == \at(map->count, L2) + 1; // в L2 произошло понижение счетчика count на 1 по сравнению с L1

  predicate same_count{L1, L2} (Map *map) =
    \at(map->count, L1) == \at(map->count, L2); // count остался таким же

  predicate same_capacity{L1, L2} (Map *map) =
    \at(map->capacity, L1) == \at(map->capacity, L2); // capacity остался таким же

  predicate same_items{L1, L2} (Map *map) =
    \forall integer i;
    0 <= i < (\at(map->capacity, L2)) &&
    item_exists_t{L1}(get_item_t{L1}(map, i)) &&
    item_exists_t{L2}(get_item_t{L2}(map, i)) ==>
      compare_items{L1, L2}
        (\at(&map->items[i], L1), \at(&map->items[i], L2)); // отображения остались такими же и вообще никак не поменялись

  predicate no_mchg{L1, L2} (Map *map, Key *key) = // проверяет, что в отображении остались все значения, которые были, кроме указанного
    \forall integer i;
      (0 <= i < (\at(map->capacity, L1))) &&
      item_exists_t{L1}(get_item_t{L1}(map, i)) &&
      !compare_keys{L1, L1}(key, get_key_t{L1}(get_item_t{L1}(map, i))) ==>
        (
          \exists integer j;
          (0 <= j < (\at(map->capacity, L2))) &&
          item_exists_t{L2}(get_item_t{L2}(map, j)) ==>
            compare_items{L1, L2}(get_item_t{L1}(map, i), get_item_t{L2}(map, j))
        );

  predicate no_new{L1, L2} (Map *map) = // проверяет, что каждое значение из результирующего map было в исходном
    \forall integer i;
    (0 <= i < (\at(map->capacity, L2))) &&
    item_exists_t{L2}(get_item_t{L2}(map, i)) ==>
      (
        \exists integer j;
        (0 <= j <= (\at(map->capacity, L1))) &&
        item_exists_t{L1}(get_item_t{L1}(map, j)) ==>
          compare_items{L1, L2} (get_item_t{L2}(map, i), get_item_t{L1}(map, j))
      );

  predicate is_valid_map (Map *map) =
    is_valid_map_mem(map) &&
    is_valid_map_sizes(map) &&
    is_valid_items(map) &&
    count_ok(map) &&
    begin_ok(map) &&
    unique_keys(map) &&
    all_valid_existence(map) &&
    gap_ok(map); // проверка всех условий на Map
*/
// */

int initializeMap(Map *map, int size);

// TODO: Spec
  /*@
    requires is_valid_map(map); // valid map, gotten out of initMap
    // проверка А2
    requires \freeable(map->items); // dynamic map can be freed
    // проверка А2

    assigns map->items; // for map->items = ((void *)0)
    assigns map->items[0..map->capacity - 1]; // for deinit with 0, dont need that

    allocates \nothing; // проверка A7

    frees map->items; // dynamic map gets freed
    // проверка А4, А1

    ensures \valid(map) && (map->items == ((void *)0)); // memory pointers are valid
    // проверка A6, А3
    ensures !is_valid_map(map); // проверка А5
    ensures same_capacity{Old, Post}(map); // capacity stays the same
    ensures same_count{Old, Post}(map); // count stays the same
    // проверка А8
  */
void finalizeMap(Map *map);

int addElement(Map *map, Key *key, Value *value);

// TODO: Spec
  /*@
    requires is_valid_map(map); // проверка B11
    requires \valid(key); // проверка B11
    requires value == ((void *)0) || \valid(value); // проверка B11

    assigns *value; // проверка B5 (возможность записи по *value)

    allocates \nothing; // проверка B7, B10
    frees \nothing; // проверка B7, B10

    ensures is_valid_map(map); // проверка B10
    ensures same_capacity{Old, Post}(map);   // проверка B9
    ensures // проверка B1 (ключа нет в любом случае)
      \forall integer i;
      (0 <= i < map->capacity) ==>
        !compare_keys_now(key, get_key(get_item(map, i)));

    ensures \result == 0 ==> // проверка B4
      (
        compare_keys{Old, Post}(key, key) &&       // проверка B7
        compare_values{Old, Post}(value, value) && // проверка B7
        same_count{Old, Post}(map) &&  // проверка B8
        same_items{Old, Post}(map) && // проверка B3, B4, B6 если ничего не случилось
        (
          \forall integer i;
          (0 <= i < map->capacity) ==>
            !compare_keys{Here, Here}(key, get_key(get_item(map, i))) // no such key in map
        )
      );

    ensures \result == 1 ==> // проверка B4
      count_lowers{Old, Post}(map) &&  // проверка B8
      no_mchg{Old, Post}(map, key) && // проверка B2, B6
      no_new{Old, Post}(map); // проверка B3

  */
int removeElement(Map *map, Key *key, Value *value);

// TODO: Spec
  /*@
    requires is_valid_map(map); // проверка C10
    requires \valid(key); // проверка C9
    requires \valid(value); // проверка C9

    assigns *value; // часть C1

    allocates \nothing; // проверка С13
    frees \nothing; // проверка С14

    ensures is_valid_map(map); // проверка С8
    ensures same_capacity{Old, Post}(map); // проверка С6
    ensures same_count{Old, Post}(map); // проверка С7
    ensures same_items{Old, Post}(map); // проверка С4
    ensures compare_keys{Old, Post}(key, key); // проверка С5
    ensures \valid(key); // проверка С9
    ensures \valid(value); // проверка С9

    ensures \result == 1 ==> // С2 (возвращается истина)
      \exists integer i;
      (0 <= i < map->capacity) ==>
        compare_keys{Here, Here}(key, get_key(get_item(map, i))) && // C2 (отображение было)
        compare_values{Here, Here}(value, get_value(get_item(map, i))); // проверка С1

    ensures \result == 0 ==> // С3 – вернулся 0
      compare_values{Old, Post}(value, value) && // часть С3 (ничего не происходит)
      (\forall integer i;
      (0 <= i < map->capacity) ==>
        !compare_keys{Here, Here}(key, get_key(get_item(map, i)))); // С3 (ключа не было)

  */
int getElement(Map *map, Key *key, Value *value);

// #endif // __MAP_H__
// LCOV_EXCL_STOP
