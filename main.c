//GO
#include <stdio.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

// hashtable (end hashtable at line 1747)
#ifdef ARCH_64
#define MAX_POW_TWO (((size_t)1) << 63)
#else
#define MAX_POW_TWO (((size_t)1) << 31)
#endif /* ARCH_64 */

enum cc_stat
{
  CC_OK = 0,

  CC_ERR_ALLOC = 1,
  CC_ERR_INVALID_CAPACITY = 2,
  CC_ERR_INVALID_RANGE = 3,
  CC_ERR_MAX_CAPACITY = 4,
  CC_ERR_KEY_NOT_FOUND = 6,
  CC_ERR_VALUE_NOT_FOUND = 7,
  CC_ERR_OUT_OF_RANGE = 8,

  CC_ITER_END = 9,
};

#define CC_MAX_ELEMENTS ((size_t)-2)

#if defined(_MSC_VER)

#define INLINE __inline
#define FORCE_INLINE __forceinline

#else

#define INLINE inline
#define FORCE_INLINE inline __attribute__((always_inline))

#endif /* _MSC_VER */

#define CC_CMP_STRING cc_common_cmp_str
int cc_common_cmp_str(const void *key1, const void *key2);

int cc_common_cmp_str(const void *str1, const void *str2)
{
  return strcmp((const char *)str1, (const char *)str2);
}

typedef struct array_s Array;
typedef struct array_conf_s
{
  size_t capacity;
  float exp_factor;
  void *(*mem_alloc)(size_t size);
  void *(*mem_calloc)(size_t blocks, size_t size);
  void (*mem_free)(void *block);
} ArrayConf;
typedef struct array_iter_s
{
  Array *ar;
  size_t index;
  bool last_removed;
} ArrayIter;
typedef struct array_zip_iter_s
{
  Array *ar1;
  Array *ar2;
  size_t index;
  bool last_removed;
} ArrayZipIter;

enum cc_stat array_new(Array **out);
enum cc_stat array_new_conf(ArrayConf const *const conf, Array **out);
void array_conf_init(ArrayConf *conf);

void array_destroy(Array *ar);
void array_destroy_cb(Array *ar, void (*cb)(void *));

enum cc_stat array_add(Array *ar, void *element);
enum cc_stat array_add_at(Array *ar, void *element, size_t index);
enum cc_stat array_replace_at(Array *ar, void *element, size_t index, void **out);
enum cc_stat array_swap_at(Array *ar, size_t index1, size_t index2);

enum cc_stat array_remove(Array *ar, void *element, void **out);
enum cc_stat array_remove_at(Array *ar, size_t index, void **out);
enum cc_stat array_remove_last(Array *ar, void **out);
void array_remove_all(Array *ar);
void array_remove_all_free(Array *ar);

enum cc_stat array_get_at(Array *ar, size_t index, void **out);
enum cc_stat array_get_last(Array *ar, void **out);

enum cc_stat array_subarray(Array *ar, size_t from, size_t to, Array **out);
enum cc_stat array_copy_shallow(Array *ar, Array **out);
enum cc_stat array_copy_deep(Array *ar, void *(*cp)(void *), Array **out);

void array_reverse(Array *ar);
enum cc_stat array_trim_capacity(Array *ar);

size_t array_contains(Array *ar, void *element);
size_t array_contains_value(Array *ar, void *element, int (*cmp)(const void *, const void *));
size_t array_size(Array *ar);
size_t array_capacity(Array *ar);

enum cc_stat array_index_of(Array *ar, void *element, size_t *index);
void array_sort(Array *ar, int (*cmp)(const void *, const void *));

void array_map(Array *ar, void (*fn)(void *));
void array_reduce(Array *ar, void (*fn)(void *, void *, void *), void *result);

enum cc_stat array_filter_mut(Array *ar, bool (*predicate)(const void *));
enum cc_stat array_filter(Array *ar, bool (*predicate)(const void *), Array **out);

void array_iter_init(ArrayIter *iter, Array *ar);
enum cc_stat array_iter_next(ArrayIter *iter, void **out);
enum cc_stat array_iter_remove(ArrayIter *iter, void **out);
enum cc_stat array_iter_add(ArrayIter *iter, void *element);
enum cc_stat array_iter_replace(ArrayIter *iter, void *element, void **out);
size_t array_iter_index(ArrayIter *iter);

void array_zip_iter_init(ArrayZipIter *iter, Array *a1, Array *a2);
enum cc_stat array_zip_iter_next(ArrayZipIter *iter, void **out1, void **out2);
enum cc_stat array_zip_iter_add(ArrayZipIter *iter, void *e1, void *e2);
enum cc_stat array_zip_iter_remove(ArrayZipIter *iter, void **out1, void **out2);
enum cc_stat array_zip_iter_replace(ArrayZipIter *iter, void *e1, void *e2, void **out1, void **out2);
size_t array_zip_iter_index(ArrayZipIter *iter);

const void *const *array_get_buffer(Array *ar);

#define ARRAY_FOREACH(val, array, body)                                        \
  {                                                                            \
    ArrayIter array_iter_53d46d2a04458e7b;                                     \
    array_iter_init(&array_iter_53d46d2a04458e7b, array);                      \
    void *val;                                                                 \
    while (array_iter_next(&array_iter_53d46d2a04458e7b, &val) != CC_ITER_END) \
      body                                                                     \
  }

#define ARRAY_FOREACH_ZIP(val1, val2, array1, array2, body)                                     \
  {                                                                                             \
    ArrayZipIter array_zip_iter_ea08d3e52f25883b3;                                              \
    array_zip_iter_init(&array_zip_iter_ea08d3e52f25883b, array1, array2);                      \
    void *val1;                                                                                 \
    void *val2;                                                                                 \
    while (array_zip_iter_next(&array_zip_iter_ea08d3e52f25883b3, &val1, &val2) != CC_ITER_END) \
      body                                                                                      \
  }

#define KEY_LENGTH_VARIABLE -1
#define KEY_LENGTH_POINTER sizeof(void *)

typedef struct hashtable_s HashTable;
typedef struct table_entry_s
{
  void *key;
  void *value;
  size_t hash;
  struct table_entry_s *next;
} TableEntry;

typedef struct hashtable_iter
{
  HashTable *table;
  size_t bucket_index;
  TableEntry *prev_entry;
  TableEntry *next_entry;
} HashTableIter;

typedef struct hashtable_conf_s
{
  float load_factor;
  size_t initial_capacity;
  int key_length;
  uint32_t hash_seed;

  size_t (*hash)(const void *key, int l, uint32_t seed);

  /**
     * The key comparator function */
  int (*key_compare)(const void *key1, const void *key2);
  void *(*mem_alloc)(size_t size);
  void *(*mem_calloc)(size_t blocks, size_t size);
  void (*mem_free)(void *block);
} HashTableConf;

void hashtable_conf_init(HashTableConf *conf);
enum cc_stat hashtable_new(HashTable **out);
enum cc_stat hashtable_new_conf(HashTableConf const *const conf, HashTable **out);

void hashtable_destroy(HashTable *table);
enum cc_stat hashtable_add(HashTable *table, void *key, void *val);
enum cc_stat hashtable_get(HashTable *table, void *key, void **out);
enum cc_stat hashtable_remove(HashTable *table, void *key, void **out);
void hashtable_remove_all(HashTable *table);
bool hashtable_contains_key(HashTable *table, void *key);

size_t hashtable_size(HashTable *table);
size_t hashtable_capacity(HashTable *table);

enum cc_stat hashtable_get_keys(HashTable *table, Array **out);
enum cc_stat hashtable_get_values(HashTable *table, Array **out);

size_t hashtable_hash_string(const void *key, int len, uint32_t seed);
size_t hashtable_hash(const void *key, int len, uint32_t seed);
size_t hashtable_hash_ptr(const void *key, int len, uint32_t seed);

void hashtable_foreach_key(HashTable *table, void (*op)(const void *));
void hashtable_foreach_value(HashTable *table, void (*op)(void *));

void hashtable_iter_init(HashTableIter *iter, HashTable *table);
enum cc_stat hashtable_iter_next(HashTableIter *iter, TableEntry **out);
enum cc_stat hashtable_iter_remove(HashTableIter *iter, void **out);

#define HASHTABLE_FOREACH(hashtable, key_53d46d2a04458e7b, value_53d46d2a04458e7b, body)                  \
  {                                                                                                       \
    HashTableIter hashtable_iter_53d46d2a04458e7b;                                                        \
    hashtable_iter_init(&hashtable_iter_53d46d2a04458e7b, hashtable);                                     \
    TableEntry *entry_53d46d2a04458e7b;                                                                   \
    while (hashtable_iter_next(&hashtable_iter_53d46d2a04458e7b, &entry_53d46d2a04458e7b) != CC_ITER_END) \
    {                                                                                                     \
      key_53d46d2a04458e7b = entry_53d46d2a04458e7b->key;                                                 \
      value_53d46d2a04458e7b = entry_53d46d2a04458e7b->value;                                             \
      body                                                                                                \
    }                                                                                                     \
  }

#define GENERAL_HASH hashtable_hash
#define STRING_HASH hashtable_hash_string
#define POINTER_HASH hashtable_hash_ptr
typedef HashTable *HSI;

HSI hsi_create();
void hsi_free(HSI *tbl);

int hsi_add(HSI tbl, char *key, int val);
int hsi_get(HSI tbl, char *key, int **out);
int hsi_contains(HSI tbl, char *key);

void hsi_foreach_kv(HSI tbl,
                    void (*op)(const char *, int *, void *),
                    void *user_data);

HSI hsi_create()
{
  HSI tbl;
  hashtable_new(&tbl);
  return tbl;
}

void hsi_free(HSI *tbl)
{
  hashtable_destroy(*tbl);
}

int hsi_add(HSI tbl, char *key, int val)
{
  int *data = malloc(sizeof(data));
  *data = val;
  if (hashtable_add(tbl, strdup(key), data) == CC_OK)
  {
    return 0;
  }
  return 1;
}

int hsi_get(HSI tbl, char *key, int **out)
{
  void *data;
  if (hashtable_get(tbl, key, &data) == CC_OK)
  {
    *out = (int *)data;
    return 0;
  }
  return 1;
}

int hsi_contains(HSI tbl, char *key)
{
  return hashtable_contains_key(tbl, key);
}

void hsi_foreach_kv(HSI tbl,
                    void (*op)(const char *, int *, void *),
                    void *user_data)
{
  void *key;
  void *value;
  HASHTABLE_FOREACH(tbl, key, value, op(key, value, user_data););
}

#define DEFAULT_CAPACITY 16
#define DEFAULT_LOAD_FACTOR 0.75f

struct hashtable_s
{
  size_t capacity;
  size_t size;
  size_t threshold;
  uint32_t hash_seed;
  int key_len;
  float load_factor;
  TableEntry **buckets;

  size_t (*hash)(const void *key, int l, uint32_t seed);
  int (*key_cmp)(const void *k1, const void *k2);
  void *(*mem_alloc)(size_t size);
  void *(*mem_calloc)(size_t blocks, size_t size);
  void (*mem_free)(void *block);
};

static enum cc_stat resize(HashTable *t, size_t new_capacity);
static enum cc_stat get_null_key(HashTable *table, void **out);
static enum cc_stat add_null_key(HashTable *table, void *val);
static enum cc_stat remove_null_key(HashTable *table, void **out);

static size_t get_table_index(HashTable *table, void *key);
static size_t round_pow_two(size_t n);
static void move_entries(TableEntry **src_bucket, TableEntry **dest_bucket,
                         size_t src_size, size_t dest_size);

enum cc_stat hashtable_new(HashTable **out)
{
  HashTableConf htc;
  hashtable_conf_init(&htc);
  return hashtable_new_conf(&htc, out);
}

enum cc_stat hashtable_new_conf(HashTableConf const *const conf, HashTable **out)
{
  HashTable *table = conf->mem_calloc(1, sizeof(HashTable));

  if (!table)
    return CC_ERR_ALLOC;

  table->capacity = round_pow_two(conf->initial_capacity);
  table->buckets = conf->mem_calloc(table->capacity, sizeof(TableEntry *));

  if (!table->buckets)
  {
    conf->mem_free(table);
    return CC_ERR_ALLOC;
  }

  table->hash = conf->hash;
  table->key_cmp = conf->key_compare;
  table->load_factor = conf->load_factor;
  table->hash_seed = conf->hash_seed;
  table->key_len = conf->key_length;
  table->size = 0;
  table->mem_alloc = conf->mem_alloc;
  table->mem_calloc = conf->mem_calloc;
  table->mem_free = conf->mem_free;
  table->threshold = table->capacity * table->load_factor;

  *out = table;
  return CC_OK;
}
void hashtable_conf_init(HashTableConf *conf)
{
  conf->hash = STRING_HASH;
  conf->key_compare = cc_common_cmp_str;
  conf->initial_capacity = DEFAULT_CAPACITY;
  conf->load_factor = DEFAULT_LOAD_FACTOR;
  conf->key_length = KEY_LENGTH_VARIABLE;
  conf->hash_seed = 0;
  conf->mem_alloc = malloc;
  conf->mem_calloc = calloc;
  conf->mem_free = free;
}

void hashtable_destroy(HashTable *table)
{
  size_t i;
  for (i = 0; i < table->capacity; i++)
  {
    TableEntry *next = table->buckets[i];

    while (next)
    {
      TableEntry *tmp = next->next;
      table->mem_free(next);
      next = tmp;
    }
  }
  table->mem_free(table->buckets);
  table->mem_free(table);
}

enum cc_stat hashtable_add(HashTable *table, void *key, void *val)
{
  enum cc_stat stat;
  if (table->size >= table->threshold)
  {
    if ((stat = resize(table, table->capacity << 1)) != CC_OK)
      return stat;
  }

  if (!key)
    return add_null_key(table, val);

  const size_t hash = table->hash(key, table->key_len, table->hash_seed);
  const size_t i = hash & (table->capacity - 1);

  TableEntry *replace = table->buckets[i];

  while (replace)
  {
    void *rk = replace->key;
    if (rk && table->key_cmp(rk, key) == 0)
    {
      replace->value = val;
      return CC_OK;
    }
    replace = replace->next;
  }

  TableEntry *new_entry = table->mem_alloc(sizeof(TableEntry));

  if (!new_entry)
    return CC_ERR_ALLOC;

  new_entry->key = key;
  new_entry->value = val;
  new_entry->hash = hash;
  new_entry->next = table->buckets[i];

  table->buckets[i] = new_entry;
  table->size++;

  return CC_OK;
}
static enum cc_stat add_null_key(HashTable *table, void *val)
{
  TableEntry *replace = table->buckets[0];

  while (replace)
  {
    if (!replace->key)
    {
      replace->value = val;
      return CC_OK;
    }
    replace = replace->next;
  }

  TableEntry *new_entry = table->mem_alloc(sizeof(TableEntry));

  if (!new_entry)
    return CC_ERR_ALLOC;

  new_entry->key = NULL;
  new_entry->value = val;
  new_entry->hash = 0;
  new_entry->next = table->buckets[0];

  table->buckets[0] = new_entry;
  table->size++;

  return CC_OK;
}
enum cc_stat hashtable_get(HashTable *table, void *key, void **out)
{
  if (!key)
    return get_null_key(table, out);

  size_t index = get_table_index(table, key);
  TableEntry *bucket = table->buckets[index];

  while (bucket)
  {
    if (bucket->key && table->key_cmp(bucket->key, key) == 0)
    {
      *out = bucket->value;
      return CC_OK;
    }
    bucket = bucket->next;
  }
  return CC_ERR_KEY_NOT_FOUND;
}

static enum cc_stat get_null_key(HashTable *table, void **out)
{
  TableEntry *bucket = table->buckets[0];

  while (bucket)
  {
    if (bucket->key == NULL)
    {
      *out = bucket->value;
      return CC_OK;
    }
    bucket = bucket->next;
  }
  return CC_ERR_KEY_NOT_FOUND;
}

enum cc_stat hashtable_remove(HashTable *table, void *key, void **out)
{
  if (!key)
    return remove_null_key(table, out);

  const size_t i = get_table_index(table, key);

  TableEntry *e = table->buckets[i];
  TableEntry *prev = NULL;
  TableEntry *next = NULL;

  while (e)
  {
    next = e->next;

    if (e->key && table->key_cmp(key, e->key) == 0)
    {
      void *value = e->value;

      if (!prev)
        table->buckets[i] = next;
      else
        prev->next = next;

      table->mem_free(e);
      table->size--;
      if (out)
        *out = value;
      return CC_OK;
    }
    prev = e;
    e = next;
  }
  return CC_ERR_KEY_NOT_FOUND;
}
enum cc_stat remove_null_key(HashTable *table, void **out)
{
  TableEntry *e = table->buckets[0];

  TableEntry *prev = NULL;
  TableEntry *next = NULL;

  while (e)
  {
    next = e->next;

    if (e->key == NULL)
    {
      void *value = e->value;

      if (!prev)
        table->buckets[0] = next;
      else
        prev->next = next;

      table->mem_free(e);
      table->size--;
      if (out)
        *out = value;
      return CC_OK;
    }
    prev = e;
    e = next;
  }
  return CC_ERR_KEY_NOT_FOUND;
}
void hashtable_remove_all(HashTable *table)
{
  size_t i;
  for (i = 0; i < table->capacity; i++)
  {
    TableEntry *entry = table->buckets[i];
    while (entry)
    {
      TableEntry *next = entry->next;
      table->mem_free(entry);
      table->size--;
      entry = next;
    }
    table->buckets[i] = NULL;
  }
}

static enum cc_stat resize(HashTable *t, size_t new_capacity)
{
  if (t->capacity == MAX_POW_TWO)
    return CC_ERR_MAX_CAPACITY;

  TableEntry **new_buckets = t->mem_calloc(new_capacity, sizeof(TableEntry));

  if (!new_buckets)
    return CC_ERR_ALLOC;

  TableEntry **old_buckets = t->buckets;

  move_entries(old_buckets, new_buckets, t->capacity, new_capacity);

  t->buckets = new_buckets;
  t->capacity = new_capacity;
  t->threshold = t->load_factor * new_capacity;

  t->mem_free(old_buckets);

  return CC_OK;
}
static INLINE size_t round_pow_two(size_t n)
{
  if (n >= MAX_POW_TWO)
    return MAX_POW_TWO;

  if (n == 0)
    return 2;
  n--;
  n |= n >> 1;
  n |= n >> 2;
  n |= n >> 4;
  n |= n >> 8;
  n |= n >> 16;
  n++;

  return n;
}

static INLINE void
move_entries(TableEntry **src_bucket, TableEntry **dest_bucket,
             size_t src_size, size_t dest_size)
{
  size_t i;
  for (i = 0; i < src_size; i++)
  {
    TableEntry *entry = src_bucket[i];

    while (entry)
    {
      TableEntry *next = entry->next;
      size_t index = entry->hash & (dest_size - 1);

      entry->next = dest_bucket[index];
      dest_bucket[index] = entry;

      entry = next;
    }
  }
}

size_t hashtable_size(HashTable *table)
{
  return table->size;
}
size_t hashtable_capacity(HashTable *table)
{
  return table->capacity;
}

bool hashtable_contains_key(HashTable *table, void *key)
{
  TableEntry *entry = table->buckets[get_table_index(table, key)];

  while (entry)
  {
    if (table->key_cmp(key, entry->key) == 0)
      return true;

    entry = entry->next;
  }
  return false;
}

enum cc_stat hashtable_get_values(HashTable *table, Array **out)
{
  ArrayConf ac;
  array_conf_init(&ac);

  ac.capacity = table->size;
  ac.mem_alloc = table->mem_alloc;
  ac.mem_calloc = table->mem_calloc;
  ac.mem_free = table->mem_free;

  Array *values;
  enum cc_stat stat = array_new_conf(&ac, &values);
  if (stat != CC_OK)
    return stat;

  size_t i;
  for (i = 0; i < table->capacity; i++)
  {
    TableEntry *entry = table->buckets[i];

    while (entry)
    {
      if ((stat = array_add(values, entry->value)) == CC_OK)
      {
        entry = entry->next;
      }
      else
      {
        array_destroy(values);
        return stat;
      }
    }
  }
  *out = values;
  return CC_OK;
}

enum cc_stat hashtable_get_keys(HashTable *table, Array **out)
{
  ArrayConf vc;
  array_conf_init(&vc);

  vc.capacity = table->size;
  vc.mem_alloc = table->mem_alloc;
  vc.mem_calloc = table->mem_calloc;
  vc.mem_free = table->mem_free;

  Array *keys;
  enum cc_stat stat = array_new_conf(&vc, &keys);
  if (stat != CC_OK)
    return stat;

  size_t i;
  for (i = 0; i < table->capacity; i++)
  {
    TableEntry *entry = table->buckets[i];

    while (entry)
    {
      if ((stat = array_add(keys, entry->key)) == CC_OK)
      {
        entry = entry->next;
      }
      else
      {
        array_destroy(keys);
        return stat;
      }
    }
  }
  *out = keys;
  return CC_OK;
}

static INLINE size_t get_table_index(HashTable *table, void *key)
{
  size_t hash = table->hash(key, table->key_len, table->hash_seed);
  return hash & (table->capacity - 1);
}

void hashtable_foreach_key(HashTable *table, void (*fn)(const void *key))
{
  size_t i;
  for (i = 0; i < table->capacity; i++)
  {
    TableEntry *entry = table->buckets[i];

    while (entry)
    {
      fn(entry->key);
      entry = entry->next;
    }
  }
}

void hashtable_foreach_value(HashTable *table, void (*fn)(void *val))
{
  size_t i;
  for (i = 0; i < table->capacity; i++)
  {
    TableEntry *entry = table->buckets[i];

    while (entry)
    {
      fn(entry->value);
      entry = entry->next;
    }
  }
}

void hashtable_iter_init(HashTableIter *iter, HashTable *table)
{
  memset(iter, 0, sizeof(HashTableIter));
  iter->table = table;

  size_t i;
  for (i = 0; i < table->capacity; i++)
  {
    TableEntry *e = table->buckets[i];
    if (e)
    {
      iter->bucket_index = i;
      iter->next_entry = e;
      iter->prev_entry = NULL;
      break;
    }
  }
}

enum cc_stat hashtable_iter_next(HashTableIter *iter, TableEntry **te)
{
  if (!iter->next_entry)
    return CC_ITER_END;

  iter->prev_entry = iter->next_entry;
  iter->next_entry = iter->next_entry->next;

  /* Iterate through the list */
  if (iter->next_entry)
  {
    *te = iter->prev_entry;
    return CC_OK;
  }

  /* Find the next list and return the first element*/
  size_t i;
  for (i = iter->bucket_index + 1; i < iter->table->capacity; i++)
  {
    iter->next_entry = iter->table->buckets[i];

    if (iter->next_entry)
    {
      iter->bucket_index = i;
      break;
    }
  }
  *te = iter->prev_entry;

  return CC_OK;
}

enum cc_stat hashtable_iter_remove(HashTableIter *iter, void **out)
{
  return hashtable_remove(iter->table, iter->prev_entry->key, out);
}

size_t hashtable_hash_string(const void *key, int len, uint32_t seed)
{
  const char *str = key;
  register size_t hash = seed + 5381 + len + 1; /* Suppress the unused param warning */

  int c;
  while ((c = *str++))
    hash = ((hash << 5) + hash) ^ c;

  return hash;
}

#ifdef _MSC_VER

#define ROTL32(x, y) _rotl(x, y)
#define ROTL64(x, y) _rotl64(x, y)
#define BIG_CONSTANT(x) (x)

#else

FORCE_INLINE uint32_t rotl32(uint32_t x, int8_t r)
{
  return (x << r) | (x >> (32 - r));
}

FORCE_INLINE uint64_t rotl64(uint64_t x, int8_t r)
{
  return (x << r) | (x >> (64 - r));
}

#define ROTL32(x, y) rotl32(x, y)
#define ROTL64(x, y) rotl64(x, y)
#define BIG_CONSTANT(x) (x##LLU)

#endif

#ifdef ARCH_64

FORCE_INLINE uint64_t fmix64(uint64_t k)
{
  k ^= k >> 33;
  k *= BIG_CONSTANT(0xff51afd7ed558ccd);
  k ^= k >> 33;
  k *= BIG_CONSTANT(0xc4ceb9fe1a85ec53);
  k ^= k >> 33;

  return k;
}

uint64_t hashtable_hash(const void *key, int len, uint32_t seed)
{
  const uint8_t *data = (const uint8_t *)key;
  const int nblocks = len / 16;

  uint64_t h1 = seed;
  uint64_t h2 = seed;

  const uint64_t c1 = BIG_CONSTANT(0x87c37b91114253d5);
  const uint64_t c2 = BIG_CONSTANT(0x4cf5ad432745937f);

  const uint64_t *blocks = (const uint64_t *)(data);

  int i;
  for (i = 0; i < nblocks; i++)
  {
    uint64_t k1 = blocks[i * 2 + 0];
    uint64_t k2 = blocks[i * 2 + 1];

    k1 *= c1;
    k1 = ROTL64(k1, 31);
    k1 *= c2;
    h1 ^= k1;
    h1 = ROTL64(h1, 27);
    h1 += h2;
    h1 = h1 * 5 + 0x52dce729;

    k2 *= c2;
    k2 = ROTL64(k2, 33);
    k2 *= c1;
    h2 ^= k2;
    h2 = ROTL64(h2, 31);
    h2 += h1;
    h2 = h2 * 5 + 0x38495ab5;
  }

  const uint8_t *tail = (const uint8_t *)(data + nblocks * 16);

  uint64_t k1 = 0;
  uint64_t k2 = 0;

  switch (len & 15)
  {
  case 15:
    k2 ^= ((uint64_t)tail[14]) << 48;
  case 14:
    k2 ^= ((uint64_t)tail[13]) << 40;
  case 13:
    k2 ^= ((uint64_t)tail[12]) << 32;
  case 12:
    k2 ^= ((uint64_t)tail[11]) << 24;
  case 11:
    k2 ^= ((uint64_t)tail[10]) << 16;
  case 10:
    k2 ^= ((uint64_t)tail[9]) << 8;
  case 9:
    k2 ^= ((uint64_t)tail[8]) << 0;
    k2 *= c2;
    k2 = ROTL64(k2, 33);
    k2 *= c1;
    h2 ^= k2;

  case 8:
    k1 ^= ((uint64_t)tail[7]) << 56;
  case 7:
    k1 ^= ((uint64_t)tail[6]) << 48;
  case 6:
    k1 ^= ((uint64_t)tail[5]) << 40;
  case 5:
    k1 ^= ((uint64_t)tail[4]) << 32;
  case 4:
    k1 ^= ((uint64_t)tail[3]) << 24;
  case 3:
    k1 ^= ((uint64_t)tail[2]) << 16;
  case 2:
    k1 ^= ((uint64_t)tail[1]) << 8;
  case 1:
    k1 ^= ((uint64_t)tail[0]) << 0;
    k1 *= c1;
    k1 = ROTL64(k1, 31);
    k1 *= c2;
    h1 ^= k1;
  };

  h1 ^= len;
  h2 ^= len;

  h1 += h2;
  h2 += h1;

  h1 = fmix64(h1);
  h2 = fmix64(h2);

  h1 += h2;
  h2 += h1;

  return h1;
}

/*
 * MurmurHash3 the 64bit variant that hashes the pointer itself
 */
uint64_t hashtable_hash_ptr(const void *key, int len, uint32_t seed)
{
  uint32_t h1 = seed;
  uint32_t h2 = seed;

  const uint64_t c1 = BIG_CONSTANT(0x87c37b91114253d5);
  const uint64_t c2 = BIG_CONSTANT(0x4cf5ad432745937f);

  uint32_t k1 = (uint32_t)(uintptr_t)key;
  uint32_t k2 = (uint32_t)((uintptr_t)key >> (uint64_t)32);

  k1 *= c1;
  k1 = rotl32(k1, 31);
  k1 *= c2;
  h1 ^= k1;
  h1 = rotl32(h1, 27);
  h1 += h2;
  h1 = h1 * 5 + 0x52dce729;

  k2 *= c2;
  k2 = rotl32(k2, 33);
  k2 *= c1;
  h2 ^= k2;
  h2 = rotl32(h2, 31);
  h2 += h1;
  h2 = h2 * 5 + 0x38495ab5;

  h1 ^= len;
  h2 ^= len;

  h1 += h2;
  h2 += h1;

  h1 = fmix64(h1);
  h2 = fmix64(h2);

  h1 += h2;
  h2 += h1;

  uint64_t result = ((uint64_t)h1 << 32) | (uint64_t)h2;

  return result;
}
#else

FORCE_INLINE uint32_t fmix32(uint32_t h)
{
  h ^= h >> 16;
  h *= 0x85ebca6b;
  h ^= h >> 13;
  h *= 0xc2b2ae35;
  h ^= h >> 16;

  return h;
}

/**
 * MurmurHash3 the 32bit variant.
 */
size_t hashtable_hash(const void *key, int len, uint32_t seed)
{
  const uint8_t *data = (const uint8_t *)key;
  const int nblocks = len / 4;

  uint32_t h1 = seed;

  const uint32_t c1 = 0xcc9e2d51;
  const uint32_t c2 = 0x1b873593;

  const uint32_t *blocks = (const uint32_t *)(data + nblocks * 4);

  int i;
  for (i = -nblocks; i; i++)
  {
    uint32_t k1 = blocks[i];

    k1 *= c1;
    k1 = ROTL32(k1, 15);
    k1 *= c2;

    h1 ^= k1;
    h1 = ROTL32(h1, 13);
    h1 = h1 * 5 + 0xe6546b64;
  }

  const uint8_t *tail = (const uint8_t *)(data + nblocks * 4);

  uint32_t k1 = 0;

  switch (len & 3)
  {
  case 3:
    k1 ^= tail[2] << 16;
  case 2:
    k1 ^= tail[1] << 8;
  case 1:
    k1 ^= tail[0];
    k1 *= c1;
    k1 = ROTL32(k1, 15);
    k1 *= c2;
    h1 ^= k1;
  };

  h1 ^= len;
  h1 = fmix32(h1);

  return (size_t)h1;
}

/*
 * MurmurHash3 the 32bit variant that hashes the pointer itself
 */
size_t hashtable_hash_ptr(const void *key, int len, uint32_t seed)
{
  uint32_t h1 = seed;

  const uint32_t c1 = 0xcc9e2d51;
  const uint32_t c2 = 0x1b873593;

  uint32_t k1 = (uint32_t)(uintptr_t)key;

  k1 *= c1;
  k1 = ROTL32(k1, 15);
  k1 *= c2;

  h1 ^= k1;
  h1 = ROTL32(h1, 13);
  h1 = h1 * 5 + 0xe6546b64;
  h1 ^= len;
  h1 = fmix32(h1);

  return (size_t)h1;
}

#endif /* ARCH_64 */

#define DEFAULT_EXPANSION_FACTOR 2

struct array_s
{
  size_t size;
  size_t capacity;
  float exp_factor;
  void **buffer;

  void *(*mem_alloc)(size_t size);
  void *(*mem_calloc)(size_t blocks, size_t size);
  void (*mem_free)(void *block);
};

static enum cc_stat expand_capacity(Array *ar);

enum cc_stat array_new(Array **out)
{
  ArrayConf c;
  array_conf_init(&c);
  return array_new_conf(&c, out);
}
enum cc_stat array_new_conf(ArrayConf const *const conf, Array **out)
{
  float ex;

  /* The expansion factor must be greater than one for the
     * array to grow */
  if (conf->exp_factor <= 1)
    ex = DEFAULT_EXPANSION_FACTOR;
  else
    ex = conf->exp_factor;

  /* Needed to avoid an integer overflow on the first resize and
     * to easily check for any future overflows. */
  if (!conf->capacity || ex >= CC_MAX_ELEMENTS / conf->capacity)
    return CC_ERR_INVALID_CAPACITY;

  Array *ar = conf->mem_calloc(1, sizeof(Array));

  if (!ar)
    return CC_ERR_ALLOC;

  void **buff = conf->mem_alloc(conf->capacity * sizeof(void *));

  if (!buff)
  {
    conf->mem_free(ar);
    return CC_ERR_ALLOC;
  }

  ar->buffer = buff;
  ar->exp_factor = ex;
  ar->capacity = conf->capacity;
  ar->mem_alloc = conf->mem_alloc;
  ar->mem_calloc = conf->mem_calloc;
  ar->mem_free = conf->mem_free;

  *out = ar;
  return CC_OK;
}

void array_conf_init(ArrayConf *conf)
{
  conf->exp_factor = DEFAULT_EXPANSION_FACTOR;
  conf->capacity = DEFAULT_CAPACITY;
  conf->mem_alloc = malloc;
  conf->mem_calloc = calloc;
  conf->mem_free = free;
}
void array_destroy(Array *ar)
{
  ar->mem_free(ar->buffer);
  ar->mem_free(ar);
}
void array_destroy_cb(Array *ar, void (*cb)(void *))
{
  size_t i;
  for (i = 0; i < ar->size; i++)
    cb(ar->buffer[i]);

  array_destroy(ar);
}
enum cc_stat array_add(Array *ar, void *element)
{
  if (ar->size >= ar->capacity)
  {
    enum cc_stat status = expand_capacity(ar);
    if (status != CC_OK)
      return status;
  }

  ar->buffer[ar->size] = element;
  ar->size++;

  return CC_OK;
}

enum cc_stat array_add_at(Array *ar, void *element, size_t index)
{
  if (index == ar->size)
    return array_add(ar, element);

  if ((ar->size == 0 && index != 0) || index > (ar->size - 1))
    return CC_ERR_OUT_OF_RANGE;

  if (ar->size >= ar->capacity)
  {
    enum cc_stat status = expand_capacity(ar);
    if (status != CC_OK)
      return status;
  }

  size_t shift = (ar->size - index) * sizeof(void *);

  memmove(&(ar->buffer[index + 1]),
          &(ar->buffer[index]),
          shift);

  ar->buffer[index] = element;
  ar->size++;

  return CC_OK;
}

enum cc_stat array_replace_at(Array *ar, void *element, size_t index, void **out)
{
  if (index >= ar->size)
    return CC_ERR_OUT_OF_RANGE;

  if (out)
    *out = ar->buffer[index];

  ar->buffer[index] = element;

  return CC_OK;
}

enum cc_stat array_swap_at(Array *ar, size_t index1, size_t index2)
{
  void *tmp;
  if (index1 >= ar->size || index2 >= ar->size)
    return CC_ERR_OUT_OF_RANGE;
  tmp = ar->buffer[index1];
  ar->buffer[index1] = ar->buffer[index2];
  ar->buffer[index2] = tmp;
  return CC_OK;
}
enum cc_stat array_remove(Array *ar, void *element, void **out)
{
  size_t index;
  enum cc_stat status = array_index_of(ar, element, &index);

  if (status == CC_ERR_OUT_OF_RANGE)
    return CC_ERR_VALUE_NOT_FOUND;

  if (index != ar->size - 1)
  {
    size_t block_size = (ar->size - 1 - index) * sizeof(void *);

    memmove(&(ar->buffer[index]),
            &(ar->buffer[index + 1]),
            block_size);
  }
  ar->size--;

  if (out)
    *out = element;

  return CC_OK;
}
enum cc_stat array_remove_at(Array *ar, size_t index, void **out)
{
  if (index >= ar->size)
    return CC_ERR_OUT_OF_RANGE;

  if (out)
    *out = ar->buffer[index];

  if (index != ar->size - 1)
  {
    size_t block_size = (ar->size - 1 - index) * sizeof(void *);

    memmove(&(ar->buffer[index]),
            &(ar->buffer[index + 1]),
            block_size);
  }
  ar->size--;

  return CC_OK;
}
enum cc_stat array_remove_last(Array *ar, void **out)
{
  return array_remove_at(ar, ar->size - 1, out);
}
void array_remove_all(Array *ar)
{
  ar->size = 0;
}
void array_remove_all_free(Array *ar)
{
  size_t i;
  for (i = 0; i < ar->size; i++)
    free(ar->buffer[i]);

  array_remove_all(ar);
}
enum cc_stat array_get_at(Array *ar, size_t index, void **out)
{
  if (index >= ar->size)
    return CC_ERR_OUT_OF_RANGE;

  *out = ar->buffer[index];
  return CC_OK;
}
enum cc_stat array_get_last(Array *ar, void **out)
{
  if (ar->size == 0)
    return CC_ERR_VALUE_NOT_FOUND;

  return array_get_at(ar, ar->size - 1, out);
}
enum cc_stat array_index_of(Array *ar, void *element, size_t *index)
{
  size_t i;
  for (i = 0; i < ar->size; i++)
  {
    if (ar->buffer[i] == element)
    {
      *index = i;
      return CC_OK;
    }
  }
  return CC_ERR_OUT_OF_RANGE;
}
enum cc_stat array_subarray(Array *ar, size_t b, size_t e, Array **out)
{
  if (b > e || e >= ar->size)
    return CC_ERR_INVALID_RANGE;

  Array *sub_ar = ar->mem_calloc(1, sizeof(Array));

  if (!sub_ar)
    return CC_ERR_ALLOC;

  /* Try to allocate the buffer */
  if (!(sub_ar->buffer = ar->mem_alloc(ar->capacity * sizeof(void *))))
  {
    ar->mem_free(sub_ar);
    return CC_ERR_ALLOC;
  }

  sub_ar->mem_alloc = ar->mem_alloc;
  sub_ar->mem_calloc = ar->mem_calloc;
  sub_ar->mem_free = ar->mem_free;
  sub_ar->size = e - b + 1;
  sub_ar->capacity = sub_ar->size;

  memcpy(sub_ar->buffer,
         &(ar->buffer[b]),
         sub_ar->size * sizeof(void *));

  *out = sub_ar;
  return CC_OK;
}
enum cc_stat array_copy_shallow(Array *ar, Array **out)
{
  Array *copy = ar->mem_alloc(sizeof(Array));

  if (!copy)
    return CC_ERR_ALLOC;

  if (!(copy->buffer = ar->mem_calloc(ar->capacity, sizeof(void *))))
  {
    ar->mem_free(copy);
    return CC_ERR_ALLOC;
  }
  copy->exp_factor = ar->exp_factor;
  copy->size = ar->size;
  copy->capacity = ar->capacity;
  copy->mem_alloc = ar->mem_alloc;
  copy->mem_calloc = ar->mem_calloc;
  copy->mem_free = ar->mem_free;

  memcpy(copy->buffer,
         ar->buffer,
         copy->size * sizeof(void *));

  *out = copy;
  return CC_OK;
}
enum cc_stat array_copy_deep(Array *ar, void *(*cp)(void *), Array **out)
{
  Array *copy = ar->mem_alloc(sizeof(Array));

  if (!copy)
    return CC_ERR_ALLOC;

  if (!(copy->buffer = ar->mem_calloc(ar->capacity, sizeof(void *))))
  {
    ar->mem_free(copy);
    return CC_ERR_ALLOC;
  }

  copy->exp_factor = ar->exp_factor;
  copy->size = ar->size;
  copy->capacity = ar->capacity;
  copy->mem_alloc = ar->mem_alloc;
  copy->mem_calloc = ar->mem_calloc;
  copy->mem_free = ar->mem_free;

  size_t i;
  for (i = 0; i < copy->size; i++)
    copy->buffer[i] = cp(ar->buffer[i]);

  *out = copy;

  return CC_OK;
}
enum cc_stat array_filter_mut(Array *ar, bool (*pred)(const void *))
{
  if (ar->size == 0)
    return CC_ERR_OUT_OF_RANGE;

  size_t rm = 0;
  size_t keep = 0;

  /* Look for clusters of non matching elements before moving
     * in order to minimize the number of memmoves */
  for (size_t i = ar->size - 1; i != ((size_t)-1); i--)
  {
    if (!pred(ar->buffer[i]))
    {
      rm++;
      continue;
    }
    if (rm > 0)
    {
      if (keep > 0)
      {
        size_t block_size = keep * sizeof(void *);
        memmove(&(ar->buffer[i + 1]),
                &(ar->buffer[i + 1 + rm]),
                block_size);
      }
      ar->size -= rm;
      rm = 0;
    }
    keep++;
  }
  /* Remove any remaining elements*/
  if (rm > 0)
  {
    size_t block_size = keep * sizeof(void *);
    memmove(&(ar->buffer[0]),
            &(ar->buffer[rm]),
            block_size);

    ar->size -= rm;
  }
  return CC_OK;
}

enum cc_stat array_filter(Array *ar, bool (*pred)(const void *), Array **out)
{
  if (ar->size == 0)
    return CC_ERR_OUT_OF_RANGE;

  Array *filtered = ar->mem_alloc(sizeof(Array));

  if (!filtered)
    return CC_ERR_ALLOC;

  if (!(filtered->buffer = ar->mem_calloc(ar->capacity, sizeof(void *))))
  {
    ar->mem_free(filtered);
    return CC_ERR_ALLOC;
  }

  filtered->exp_factor = ar->exp_factor;
  filtered->size = 0;
  filtered->capacity = ar->capacity;
  filtered->mem_alloc = ar->mem_alloc;
  filtered->mem_calloc = ar->mem_calloc;
  filtered->mem_free = ar->mem_free;

  size_t f = 0;
  for (size_t i = 0; i < ar->size; i++)
  {
    if (pred(ar->buffer[i]))
    {
      filtered->buffer[f++] = ar->buffer[i];
      filtered->size++;
    }
  }
  *out = filtered;

  return CC_OK;
}
void array_reverse(Array *ar)
{
  if (ar->size == 0)
    return;

  size_t i;
  size_t j;
  for (i = 0, j = ar->size - 1; i < (ar->size - 1) / 2; i++, j--)
  {
    void *tmp = ar->buffer[i];
    ar->buffer[i] = ar->buffer[j];
    ar->buffer[j] = tmp;
  }
}
enum cc_stat array_trim_capacity(Array *ar)
{
  if (ar->size == ar->capacity)
    return CC_OK;

  void **new_buff = ar->mem_calloc(ar->size, sizeof(void *));

  if (!new_buff)
    return CC_ERR_ALLOC;

  size_t size = ar->size < 1 ? 1 : ar->size;

  memcpy(new_buff, ar->buffer, size * sizeof(void *));
  ar->mem_free(ar->buffer);

  ar->buffer = new_buff;
  ar->capacity = ar->size;

  return CC_OK;
}
size_t array_contains(Array *ar, void *element)
{
  size_t o = 0;
  size_t i;
  for (i = 0; i < ar->size; i++)
  {
    if (ar->buffer[i] == element)
      o++;
  }
  return o;
}

size_t array_contains_value(Array *ar, void *element, int (*cmp)(const void *, const void *))
{
  size_t o = 0;
  size_t i;
  for (i = 0; i < ar->size; i++)
  {
    if (cmp(element, ar->buffer[i]) == 0)
      o++;
  }
  return o;
}
size_t array_size(Array *ar)
{
  return ar->size;
}

size_t array_capacity(Array *ar)
{
  return ar->capacity;
}
void array_sort(Array *ar, int (*cmp)(const void *, const void *))
{
  qsort(ar->buffer, ar->size, sizeof(void *), cmp);
}
static enum cc_stat expand_capacity(Array *ar)
{
  if (ar->capacity == CC_MAX_ELEMENTS)
    return CC_ERR_MAX_CAPACITY;

  size_t new_capacity = ar->capacity * ar->exp_factor;

  /* As long as the capacity is greater that the expansion factor
     * at the point of overflow, this is check is valid. */
  if (new_capacity <= ar->capacity)
    ar->capacity = CC_MAX_ELEMENTS;
  else
    ar->capacity = new_capacity;

  void **new_buff = ar->mem_alloc(new_capacity * sizeof(void *));

  if (!new_buff)
    return CC_ERR_ALLOC;

  memcpy(new_buff, ar->buffer, ar->size * sizeof(void *));

  ar->mem_free(ar->buffer);
  ar->buffer = new_buff;

  return CC_OK;
}
void array_map(Array *ar, void (*fn)(void *e))
{
  size_t i;
  for (i = 0; i < ar->size; i++)
    fn(ar->buffer[i]);
}
void array_reduce(Array *ar, void (*fn)(void *, void *, void *), void *result)
{
  if (ar->size == 1)
  {
    fn(ar->buffer[0], NULL, result);
    return;
  }
  if (ar->size > 1)
    fn(ar->buffer[0], ar->buffer[1], result);

  for (size_t i = 2; i < ar->size; i++)
    fn(result, ar->buffer[i], result);
}
void array_iter_init(ArrayIter *iter, Array *ar)
{
  iter->ar = ar;
  iter->index = 0;
  iter->last_removed = false;
}
enum cc_stat array_iter_next(ArrayIter *iter, void **out)
{
  if (iter->index >= iter->ar->size)
    return CC_ITER_END;

  *out = iter->ar->buffer[iter->index];

  iter->index++;
  iter->last_removed = false;

  return CC_OK;
}
enum cc_stat array_iter_remove(ArrayIter *iter, void **out)
{
  enum cc_stat status = CC_ERR_VALUE_NOT_FOUND;

  if (!iter->last_removed)
  {
    status = array_remove_at(iter->ar, iter->index - 1, out);
    if (status == CC_OK)
      iter->last_removed = true;
  }
  return status;
}

enum cc_stat array_iter_add(ArrayIter *iter, void *element)
{
  return array_add_at(iter->ar, element, iter->index++);
}
enum cc_stat array_iter_replace(ArrayIter *iter, void *element, void **out)
{
  return array_replace_at(iter->ar, element, iter->index - 1, out);
}
size_t array_iter_index(ArrayIter *iter)
{
  return iter->index - 1;
}
void array_zip_iter_init(ArrayZipIter *iter, Array *ar1, Array *ar2)
{
  iter->ar1 = ar1;
  iter->ar2 = ar2;
  iter->index = 0;
  iter->last_removed = false;
}
enum cc_stat array_zip_iter_next(ArrayZipIter *iter, void **out1, void **out2)
{
  if (iter->index >= iter->ar1->size || iter->index >= iter->ar2->size)
    return CC_ITER_END;

  *out1 = iter->ar1->buffer[iter->index];
  *out2 = iter->ar2->buffer[iter->index];

  iter->index++;
  iter->last_removed = false;

  return CC_OK;
}
enum cc_stat array_zip_iter_remove(ArrayZipIter *iter, void **out1, void **out2)
{
  if ((iter->index - 1) >= iter->ar1->size || (iter->index - 1) >= iter->ar2->size)
    return CC_ERR_OUT_OF_RANGE;

  if (!iter->last_removed)
  {
    array_remove_at(iter->ar1, iter->index - 1, out1);
    array_remove_at(iter->ar2, iter->index - 1, out2);
    iter->last_removed = true;
    return CC_OK;
  }
  return CC_ERR_VALUE_NOT_FOUND;
}

enum cc_stat array_zip_iter_add(ArrayZipIter *iter, void *e1, void *e2)
{
  size_t index = iter->index++;
  Array *ar1 = iter->ar1;
  Array *ar2 = iter->ar2;

  /* Make sure both array buffers have room */
  if ((ar1->size == ar1->capacity && (expand_capacity(ar1) != CC_OK)) ||
      (ar2->size == ar2->capacity && (expand_capacity(ar2) != CC_OK)))
    return CC_ERR_ALLOC;

  array_add_at(ar1, e1, index);
  array_add_at(ar2, e2, index);

  return CC_OK;
}
enum cc_stat array_zip_iter_replace(ArrayZipIter *iter, void *e1, void *e2, void **out1, void **out2)
{
  if ((iter->index - 1) >= iter->ar1->size || (iter->index - 1) >= iter->ar2->size)
    return CC_ERR_OUT_OF_RANGE;

  array_replace_at(iter->ar1, e1, iter->index - 1, out1);
  array_replace_at(iter->ar2, e2, iter->index - 1, out2);

  return CC_OK;
}

size_t array_zip_iter_index(ArrayZipIter *iter)
{
  return iter->index - 1;
}
// end hashtable

typedef enum
{
  CGRAPH_OUT = 1,
  CGRAPH_IN = 2,
  CGRAPH_ALL = 3,
  CGRAPH_TOTAL = 3
} cgraph_neimode_t;

#define CGRAPH_INTEGER int32_t
#define CGRAPH_REAL double

#if defined(NAN)
#define CGRAPH_NAN NAN
#elif defined(INFINITY)
#define CGRAPH_NAN (INFINITY / INFINITY)
#else
#define CGRAPH_NAN (INT_LEAST32_MIN)
#endif

typedef CGRAPH_INTEGER *cgraph_ivec_t;

#ifdef __cplusplus
extern "C"
{
#endif

  cgraph_ivec_t cgraph_ivec_create();
  cgraph_ivec_t cgraph_ivec_from_array(CGRAPH_INTEGER *a,
                                       CGRAPH_INTEGER n);

  /* Pass vector pointer by value */
  CGRAPH_INTEGER cgraph_ivec_max(cgraph_ivec_t const v);
  int cgraph_ivec_minmax(cgraph_ivec_t const v, CGRAPH_INTEGER *min, CGRAPH_INTEGER *max);
  bool cgraph_ivec_isininterval(cgraph_ivec_t const v,
                                CGRAPH_INTEGER low,
                                CGRAPH_INTEGER high);
  int cgraph_ivec_order(cgraph_ivec_t const v,
                        cgraph_ivec_t const v2,
                        cgraph_ivec_t const res);
  int cgraph_ivec_null(cgraph_ivec_t const v);
  int cgraph_ivec_setsize(cgraph_ivec_t const v,
                          CGRAPH_INTEGER newsize);
  CGRAPH_INTEGER cgraph_ivec_capacity(cgraph_ivec_t const v);
  CGRAPH_INTEGER cgraph_ivec_size(cgraph_ivec_t const v);
  int cgraph_ivec_fill(cgraph_ivec_t const v, CGRAPH_INTEGER data);
  int cgraph_ivec_print(cgraph_ivec_t const v);

  /* Pass vector pointer by reference */
  int cgraph_ivec_grow(cgraph_ivec_t *v,
                       CGRAPH_INTEGER newcapacity);
  int cgraph_ivec_init(cgraph_ivec_t *v,
                       CGRAPH_INTEGER size);

  int cgraph_ivec_push_back(cgraph_ivec_t *v,
                            CGRAPH_INTEGER value);
  int cgraph_ivec_append(cgraph_ivec_t *v,
                         CGRAPH_INTEGER *a, CGRAPH_INTEGER n);
  int cgraph_ivec_free(cgraph_ivec_t *v);

#ifdef __cplusplus
}
#endif

typedef struct cgraph_s
{
  CGRAPH_INTEGER n;
  bool directed;
  cgraph_ivec_t from;
  cgraph_ivec_t to;
  cgraph_ivec_t oi;
  cgraph_ivec_t ii;
  cgraph_ivec_t os;
  cgraph_ivec_t is;
  void *attr;
} cgraph_t;

#ifdef __cplusplus
extern "C"
{
#endif

  int cgraph_create(cgraph_t *graph,
                    cgraph_ivec_t const edges,
                    CGRAPH_INTEGER n,
                    bool directed);

#ifdef __cplusplus
}
#endif

#ifdef __cplusplus
extern "C"
{
#endif

  int cgraph_empty(cgraph_t *graph, CGRAPH_INTEGER n, bool directed);
  int cgraph_add_vertices(cgraph_t *graph, CGRAPH_INTEGER nv);
  void cgraph_destroy(cgraph_t *graph);
  int cgraph_add_edges(cgraph_t *graph, cgraph_ivec_t const edges);
  CGRAPH_INTEGER cgraph_vcount(const cgraph_t *graph);
  CGRAPH_INTEGER cgraph_ecount(const cgraph_t *graph);
  bool cgraph_is_directed(const cgraph_t *graph);
  int cgraph_neighbors(const cgraph_t *graph,
                       cgraph_ivec_t *neis,
                       CGRAPH_INTEGER vid,
                       cgraph_neimode_t mode);
  int cgraph_incident(const cgraph_t *graph,
                      cgraph_ivec_t *eids,
                      CGRAPH_INTEGER vid,
                      cgraph_neimode_t mode);

  int cgraph_degree_all(const cgraph_t *graph,
                        cgraph_ivec_t *res,
                        cgraph_neimode_t mode,
                        bool loops);

  int cgraph_degree_one(const cgraph_t *graph,
                        CGRAPH_INTEGER *res,
                        const CGRAPH_INTEGER node,
                        cgraph_neimode_t mode,
                        bool loops);
  int cgraph_edge(const cgraph_t *graph, CGRAPH_INTEGER eid,
                  CGRAPH_INTEGER *from, CGRAPH_INTEGER *to);
  int cgraph_get_eid(const cgraph_t *graph, CGRAPH_INTEGER *eid,
                     CGRAPH_INTEGER pfrom, CGRAPH_INTEGER pto,
                     bool directed);

#ifdef __cplusplus
}
#endif

#define CGRAPH_FROM(graph, eid) ((CGRAPH_INTEGER)(graph->from[(long int)(eid)]))
#define CGRAPH_TO(graph, eid) ((CGRAPH_INTEGER)(graph->to[(long int)(eid)]))
#define CGRAPH_OTHER(graph, eid, vid) \
  ((CGRAPH_INTEGER)(CGRAPH_TO(graph, (eid)) == (vid) ? CGRAPH_FROM((graph), (eid)) : CGRAPH_TO((graph), (eid))))

typedef struct cgraph_queue_s CGraphQueue;
#ifdef __cplusplus
extern "C"
{
#endif

  CGraphQueue *cgraph_queue_create();
  void cgraph_queue_free(CGraphQueue *q);
  int cgraph_queue_enqueue(CGraphQueue *q, void *value);
  int cgraph_queue_poll(CGraphQueue *q, void **out);
  int cgraph_queue_peek(const CGraphQueue *const q, void **out);
  size_t cgraph_queue_size(const CGraphQueue *const q);
  bool cgraph_queue_empty(const CGraphQueue *const q);

#ifdef __cplusplus
}
#endif

typedef CGraphQueue *cgraph_iqueue_t;
typedef const CGraphQueue *cgraph_iqueue_const_t;

#ifdef __cplusplus
extern "C"
{
#endif

  cgraph_iqueue_t cgraph_iqueue_create();

  int cgraph_iqueue_peek(cgraph_iqueue_const_t const q, CGRAPH_INTEGER *out);
  int cgraph_iqueue_poll(cgraph_iqueue_t q, CGRAPH_INTEGER *out);
  int cgraph_iqueue_enqueue(cgraph_iqueue_t q, CGRAPH_INTEGER element);

  size_t cgraph_iqueue_size(cgraph_iqueue_const_t const q);
  bool cgraph_iqueue_empty(cgraph_iqueue_t const q);

  void cgraph_iqueue_free(cgraph_iqueue_t *q);

#ifdef __cplusplus
}
#endif

#ifdef __cplusplus
extern "C"
{
#endif

  int cgraph_is_dag(const cgraph_t *graph, bool *res);
  int cgraph_topological_sorting(const cgraph_t *graph,
                                 cgraph_ivec_t *res,
                                 cgraph_neimode_t mode);

#ifdef __cplusplus
}
#endif

#ifdef __cplusplus
extern "C"
{
#endif

  typedef struct cgraph_istack_s CGraphIStack;
  typedef CGraphIStack *cgraph_istack_t;
  typedef const CGraphIStack *cgraph_istack_const_t;

  cgraph_istack_t cgraph_istack_create();
  int cgraph_istack_pop(cgraph_istack_t s, CGRAPH_INTEGER *out);
  int cgraph_istack_push(cgraph_istack_t s, CGRAPH_INTEGER element);
  void cgraph_istack_free(cgraph_istack_t *s);

  int cgraph_istack_top(cgraph_istack_const_t const s, CGRAPH_INTEGER *out);
  size_t cgraph_istack_size(cgraph_istack_const_t const s);
  bool cgraph_istack_empty(cgraph_istack_const_t const s);

#ifdef __cplusplus
}
#endif

typedef void cgraph_error_handler_t(
    const char *reason,
    const char *file,
    int line);

#define CGRAPH_ERROR(reason)                  \
  do                                          \
  {                                           \
    cgraph_error(reason, __FILE__, __LINE__); \
  } while (0)

#define CGRAPH_CHECK(a)           \
  do                              \
  {                               \
    int cgraph_i_ret = (a);       \
    if (cgraph_i_ret != 0)        \
    {                             \
      CGRAPH_ERROR("API failed"); \
    }                             \
  } while (0)

#ifdef __cplusplus
extern "C"
{
#endif

  void cgraph_error_handler_ignore(const char *, const char *, int);

  int cgraph_error(const char *reason,
                   const char *file,
                   int line);

  cgraph_error_handler_t *cgraph_set_error_handler(
      cgraph_error_handler_t *new_handler);

#ifdef __cplusplus
}
#endif

#ifdef __cplusplus
extern "C"
{
#endif

  int cgraph_bfs(const cgraph_t *graph,
                 CGRAPH_INTEGER root,
                 cgraph_neimode_t mode,
                 bool unreachable,
                 cgraph_ivec_t const restricted,
                 cgraph_ivec_t *order,
                 cgraph_ivec_t *rank,
                 cgraph_ivec_t *father,
                 cgraph_ivec_t *pred,
                 cgraph_ivec_t *succ,
                 cgraph_ivec_t *dist);

  int cgraph_simple_bfs(const cgraph_t *graph,
                        CGRAPH_INTEGER root,
                        cgraph_neimode_t mode,
                        bool unreachable,
                        cgraph_ivec_t *father,
                        cgraph_ivec_t *dist);

  int cgraph_dfs(const cgraph_t *graph,
                 CGRAPH_INTEGER root,
                 cgraph_neimode_t mode,
                 bool unreachable,
                 cgraph_ivec_t *order,
                 cgraph_ivec_t *order_out,
                 cgraph_ivec_t *father,
                 cgraph_ivec_t *dist);

#ifdef __cplusplus
}
#endif

int cgraph_bfs(const cgraph_t *graph,
               CGRAPH_INTEGER root,            // id or vertex root
               cgraph_neimode_t mode,          // CGRAPH_OUT
               bool unreachable,               // true if we wanna visit all nodes (even unreachable), false otw
               cgraph_ivec_t const restricted, // ptr to a vt containing vertex id
               cgraph_ivec_t *order,           // order of visit stored here
               cgraph_ivec_t *rank,            // rank of vertices stored here
               cgraph_ivec_t *father,          // id of father node stored here
               cgraph_ivec_t *pred,            //id of vertex that was visited before the current one is stored here. If there is no such vertex (the current vertex is the root of a search tree), then -1 is stored.
               cgraph_ivec_t *succ,            //id of the vertex that was visited after the current one is stored here. If there is no such vertex (the current one is the last in a search tree), then -1 is stored.
               cgraph_ivec_t *dist)
{ //the distance from the root of the current search tree is stored here.
  cgraph_iqueue_t q = cgraph_iqueue_create();
  CGRAPH_INTEGER no_of_nodes = cgraph_vcount(graph);
  CGRAPH_INTEGER actroot = root;

  CGRAPH_INTEGER act_rank = 0;
  CGRAPH_INTEGER pred_vec = -1;

  if (root < 0 || root >= no_of_nodes)
  {
    CGRAPH_ERROR("Invalid root vertex in BFS");
  }

  if (restricted)
  {
    CGRAPH_INTEGER min, max;
    cgraph_ivec_minmax(restricted, &min, &max);
    if (min < 0 || max >= no_of_nodes)
    {
      CGRAPH_ERROR("Invalid vertex id in restricted set");
    }
  }

  if (mode != CGRAPH_OUT && mode != CGRAPH_IN && mode != CGRAPH_ALL)
  {
    CGRAPH_ERROR("Invalid mode argument");
  }

  if (!cgraph_is_directed(graph))
  {
    mode = CGRAPH_ALL;
  }

  bool *added = (bool *)calloc(no_of_nodes, sizeof(bool));

  /* Mark the vertices that are not in the restricted set, as already
  found. Special care must be taken for vertices that are not in
  the restricted set, but are to be used as 'root' vertices. */
  if (restricted)
  {
    long int i, n = cgraph_ivec_size(restricted);
    for (i = 0; i < no_of_nodes; ++i)
    {
      added[i] = true;
    }
    for (i = 0; i < n; i++)
    {
      added[restricted[i]] = false;
    }
  }

  /* Resize result vectors, and fill them with IGRAPH_NAN */

#define VINIT(v)                        \
  if (v)                                \
  {                                     \
    cgraph_ivec_init((v), no_of_nodes); \
    cgraph_ivec_fill((*v), CGRAPH_NAN); \
  }

  VINIT(order);
  VINIT(rank);
  VINIT(father);
  VINIT(pred);
  VINIT(succ);
  VINIT(dist);
#undef VINIT

  int rootpos = 0;
  cgraph_ivec_t neis = cgraph_ivec_create();
  while (1)
  {
    if (rootpos == 0)
    {
      actroot = root;
      ++rootpos;
    }
    else if (unreachable)
    {
      if (rootpos == 1)
      {
        actroot = 0;
        ++rootpos;
      }
      else if (actroot + 1 < no_of_nodes)
      {
        ++actroot;
      }
      else
      {
        break;
      }
    }
    else
    {
      break;
    }
    if (added[actroot])
    {
      continue;
    }

    CGRAPH_CHECK(cgraph_iqueue_enqueue(q, actroot));
    CGRAPH_CHECK(cgraph_iqueue_enqueue(q, 0));
    added[actroot] = true;
    if (father)
    {
      (*father)[actroot] = -1;
    }

    pred_vec = -1;

    while (!cgraph_iqueue_empty(q))
    {
      CGRAPH_INTEGER actvect;
      cgraph_iqueue_poll(q, &actvect);
      CGRAPH_INTEGER actdist;
      cgraph_iqueue_poll(q, &actdist);
      CGRAPH_INTEGER succ_vec;

      cgraph_neighbors(graph, &neis, actvect, mode);
      long int i, n = cgraph_ivec_size(neis);

      if (pred)
      {
        (*pred)[actvect] = pred_vec;
      }
      if (rank)
      {
        (*rank)[actvect] = act_rank;
      }
      if (order)
      {
        (*order)[act_rank++] = actvect;
      }
      if (dist)
      {
        (*dist)[actvect] = actdist;
      }

      for (i = 0; i < n; i++)
      {
        CGRAPH_INTEGER nei = neis[i];
        if (!added[nei])
        {
          added[nei] = true;
          CGRAPH_CHECK(cgraph_iqueue_enqueue(q, nei));
          CGRAPH_CHECK(cgraph_iqueue_enqueue(q, actdist + 1));
          if (father)
          {
            (*father)[nei] = actvect;
          }
        }
      }

      if (cgraph_iqueue_empty(q))
      {
        succ_vec = -1;
      }
      else
      {
        cgraph_iqueue_peek(q, &succ_vec);
      }

      if (succ)
      {
        (*succ)[actvect] = succ_vec;
      }
      pred_vec = actvect;

    } /* while q !empty */
  }   /* while (1) */
  free(added);
  cgraph_ivec_free(&neis);
  cgraph_iqueue_free(&q);
  return 0;
}

int cgraph_simple_bfs(const cgraph_t *graph,
                      CGRAPH_INTEGER root,
                      cgraph_neimode_t mode,
                      bool unreachable,
                      cgraph_ivec_t *father,
                      cgraph_ivec_t *dist)
{
  return cgraph_bfs(graph,
                    root,
                    mode,
                    unreachable,
                    0,
                    0,
                    0,
                    father,
                    0,
                    0,
                    dist);
}

//igraph_dfs
/**
 * Depth-first search
 *
 * A simple depth-first search,
 * It is allowed to supply null pointers as the output arguments the
 * user is not interested in, in this case they will be ignored.
 *
 * </para><para>
 * If not all vertices can be reached from the supplied root vertex,
 * then additional root vertices will be used, in the order of their
 * vertex ids.
 * \param graph The input graph.
 * \param root The id of the root vertex.
 * \param mode For directed graphs, it defines which edges to follow.
 *        \c IGRAPH_OUT means following the direction of the edges,
 *        \c IGRAPH_IN means the opposite, and
 *        \c IGRAPH_ALL ignores the direction of the edges.
 *        This parameter is ignored for undirected graphs.
 * \param unreachable Logical scalar, whether the search should visit
 *        the vertices that are unreachable from the given root
 *        node(s). If true, then additional searches are performed
 *        until all vertices are visited.
 * \param order If not null pointer, then the vertex ids of the graph are
 *        stored here, in the same order as they were discovered.
 * \param order_out If not a null pointer, then the vertex ids of the
 *        graphs are stored here, in the order of the completion of
 *        their subtree.
 * \param father If not a null pointer, then the id of the father of
 *        each vertex is stored here.
 * \param dist If not a null pointer, then the distance from the root of
 *        the current search tree is stored here.
 * \param in_callback If not null, then it should be a pointer to a
 *        function of type \ref igraph_dfshandler_t. This function
 *        will be called, whenever a new vertex is discovered.
 * \param out_callback If not null, then it should be a pointer to a
 *        function of type \ref igraph_dfshandler_t. This function
 *        will be called, whenever the subtree of a vertex is completed.
 * \param extra Extra argument to pass to the callback function(s).
 * \return Error code.
 *
 * Time complexity: O(|V|+|E|), linear in the number of vertices and
 * edges.
 */
int cgraph_dfs(const cgraph_t *graph,
               CGRAPH_INTEGER root,
               cgraph_neimode_t mode,
               bool unreachable,
               cgraph_ivec_t *order,
               cgraph_ivec_t *order_out,
               cgraph_ivec_t *father,
               cgraph_ivec_t *dist)
{
  CGRAPH_INTEGER no_of_nodes = cgraph_vcount(graph);
  cgraph_istack_t stack = cgraph_istack_create();
  bool *added = (bool *)calloc(no_of_nodes, sizeof(bool));
  CGRAPH_INTEGER actroot, act_rank = 0, rank_out = 0, act_dist = 0;

  if (root < 0 || root >= no_of_nodes)
  {
    CGRAPH_ERROR("Invalid root vertex for DFS");
  }

  if (mode != CGRAPH_OUT && mode != CGRAPH_IN && mode != CGRAPH_ALL)
  {
    CGRAPH_ERROR("Invalid mode argument");
  }

  if (!cgraph_is_directed(graph))
  {
    mode = CGRAPH_ALL;
  }

  /* Resize result vectors and fill them with IGRAPH_NAN */

#define VINIT(v)                        \
  if (v)                                \
  {                                     \
    cgraph_ivec_init(v, no_of_nodes);   \
    cgraph_ivec_fill((*v), CGRAPH_NAN); \
  }

  VINIT(order);
  VINIT(order_out);
  VINIT(father);
  VINIT(dist);

#undef VINIT

  CGRAPH_CHECK(cgraph_istack_push(stack, root));
  added[root] = true;
  if (father)
  {
    (*father)[root] = -1;
  }
  if (order)
  {
    (*order)[act_rank++] = root;
  }
  if (dist)
  {
    (*dist)[root] = 0;
  }

  cgraph_ivec_t nptr = cgraph_ivec_create();
  cgraph_ivec_init(&nptr, no_of_nodes);
  cgraph_ivec_t *neis_cache =
      (cgraph_ivec_t *)calloc(no_of_nodes, sizeof(cgraph_ivec_t));
  cgraph_ivec_t neis = NULL;
  for (actroot = 0; actroot < no_of_nodes;)
  {

    /* 'root' first, then all other vertices */
    if (cgraph_istack_empty(stack))
    {
      if (!unreachable)
      {
        break;
      }
      if (added[actroot])
      {
        actroot++;
        continue;
      }
      CGRAPH_CHECK(cgraph_istack_push(stack, actroot));
      added[actroot] = true;
      if (father)
      {
        (*father)[actroot] = -1;
      }
      if (order)
      {
        (*order)[act_rank++] = actroot;
      }
      if (dist)
      {
        (*dist)[actroot] = 0;
      }
    }

    cgraph_ivec_fill(nptr, 0);
    while (!cgraph_istack_empty(stack))
    {
      CGRAPH_INTEGER actvect;
      cgraph_istack_top(stack, &actvect);
      if (!neis_cache[actvect])
      {
        neis_cache[actvect] = cgraph_ivec_create();
        cgraph_neighbors(graph, neis_cache + actvect, actvect, mode);
      }
      neis = neis_cache[actvect];
      CGRAPH_INTEGER n = cgraph_ivec_size(neis);

      /* Search for a neighbor that was not yet visited */
      bool any = 0;
      CGRAPH_INTEGER nei,
          *ptr = nptr + actvect;
      while (!any && (*ptr) < n)
      {
        nei = neis[*ptr];
        any = !(added[nei]);
        ++(*ptr);
      }
      if (any)
      {
        /* There is such a neighbor, add it */
        CGRAPH_CHECK(cgraph_istack_push(stack, nei));
        added[nei] = true;
        if (father)
        {
          (*father)[nei] = actvect;
        }
        if (order)
        {
          (*order)[act_rank++] = nei;
        }
        act_dist++;
        if (dist)
        {
          (*dist)[nei] = act_dist;
        }
      }
      else
      {
        /* There is no such neighbor, finished with the subtree */
        cgraph_istack_pop(stack, NULL);
        if (order_out)
        {
          (*order_out)[rank_out++] = actvect;
        }
        act_dist--;
      }
    }
  }
  for (CGRAPH_INTEGER i = 0; i < no_of_nodes; ++i)
  {
    if (neis_cache[i])
    {
      cgraph_ivec_free(neis_cache + i);
    }
  }
  free(neis_cache);
  cgraph_ivec_free(&nptr);
  cgraph_istack_free(&stack);
  free(added);
  return 0;
}

typedef CGRAPH_REAL *cgraph_rvec_t;

#ifdef __cplusplus
extern "C"
{
#endif

  cgraph_rvec_t cgraph_rvec_create();

  /* Pass vector pointer by value */
  int cgraph_rvec_setsize(cgraph_rvec_t const v,
                          CGRAPH_INTEGER newsize);
  CGRAPH_INTEGER cgraph_rvec_capacity(cgraph_rvec_t const v);
  CGRAPH_INTEGER cgraph_rvec_size(cgraph_rvec_t const v);
  int cgraph_rvec_print(cgraph_rvec_t const v);

  /* Pass vector pointer by reference */
  int cgraph_rvec_grow(cgraph_rvec_t *v,
                       CGRAPH_INTEGER newcapacity);
  int cgraph_rvec_init(cgraph_rvec_t *v,
                       CGRAPH_INTEGER size);

  int cgraph_rvec_push_back(cgraph_rvec_t *v,
                            CGRAPH_REAL value);
  int cgraph_rvec_free(cgraph_rvec_t *v);

#ifdef __cplusplus
}
#endif

#ifdef __cplusplus
extern "C"
{
#endif

  int cgraph_get_shortest_path(const cgraph_t *graph,
                               cgraph_ivec_t *vertices,
                               cgraph_ivec_t *edges,
                               CGRAPH_INTEGER from,
                               CGRAPH_INTEGER to,
                               cgraph_neimode_t mode);

  int cgraph_get_shortest_path_dijkstra(const cgraph_t *graph,
                                        cgraph_ivec_t *vertices,
                                        cgraph_ivec_t *edges,
                                        CGRAPH_INTEGER from,
                                        CGRAPH_INTEGER to,
                                        cgraph_rvec_t weights,
                                        cgraph_neimode_t mode);

#ifdef __cplusplus
}
#endif

typedef struct cgraph_2wheap_t
{
  CGRAPH_INTEGER size;
  cgraph_rvec_t data;
  cgraph_ivec_t index;
  cgraph_ivec_t index2;
} cgraph_2wheap_t;

#ifdef __cplusplus
extern "C"
{
#endif

  int cgraph_2wheap_init(cgraph_2wheap_t *h, CGRAPH_INTEGER size);
  void cgraph_2wheap_free(cgraph_2wheap_t *h);
  int cgraph_2wheap_clear(cgraph_2wheap_t *h);
  int cgraph_2wheap_push_with_index(cgraph_2wheap_t *h,
                                    CGRAPH_INTEGER idx, CGRAPH_REAL elem);
  bool cgraph_2wheap_empty(const cgraph_2wheap_t *h);
  CGRAPH_INTEGER cgraph_2wheap_size(const cgraph_2wheap_t *h);
  CGRAPH_INTEGER cgraph_2wheap_max_size(const cgraph_2wheap_t *h);
  CGRAPH_REAL cgraph_2wheap_max(const cgraph_2wheap_t *h);
  CGRAPH_INTEGER cgraph_2wheap_max_index(const cgraph_2wheap_t *h);
  CGRAPH_REAL cgraph_2wheap_deactivate_max(cgraph_2wheap_t *h);
  bool cgraph_2wheap_has_elem(const cgraph_2wheap_t *h, CGRAPH_INTEGER idx);
  bool cgraph_2wheap_has_active(const cgraph_2wheap_t *h, CGRAPH_INTEGER idx);
  CGRAPH_REAL cgraph_2wheap_get(const cgraph_2wheap_t *h, CGRAPH_INTEGER idx);
  CGRAPH_REAL cgraph_2wheap_delete_max(cgraph_2wheap_t *h);
  CGRAPH_REAL cgraph_2wheap_delete_max_index(cgraph_2wheap_t *h, CGRAPH_INTEGER *idx);
  int cgraph_2wheap_modify(cgraph_2wheap_t *h, CGRAPH_INTEGER idx, CGRAPH_REAL elem);
  int cgraph_2wheap_check(cgraph_2wheap_t *h);

#ifdef __cplusplus
}
#endif

static cgraph_error_handler_t *cgraph_i_error_handler = 0;

void cgraph_error_handler_ignore(
    const char *reason,
    const char *file,
    int line)
{
}

int cgraph_error(const char *reason, const char *file, int line)
{
  if (cgraph_i_error_handler)
  {
    cgraph_i_error_handler(reason, file, line);
  }
  return 0;
}

cgraph_error_handler_t *cgraph_set_error_handler(
    cgraph_error_handler_t *new_handler)
{
  cgraph_error_handler_t *previous_handler = cgraph_i_error_handler;
  cgraph_i_error_handler = new_handler;
  return previous_handler;
}

cgraph_iqueue_t cgraph_iqueue_create()
{
  return cgraph_queue_create();
}

int cgraph_iqueue_peek(cgraph_iqueue_const_t const q, CGRAPH_INTEGER *out)
{
  void *data;
  int ret = cgraph_queue_peek(q, &data);
  if (ret != 0)
  {
    return ret;
  }
  *out = *((CGRAPH_INTEGER *)data);
  return 0;
}

int cgraph_iqueue_poll(cgraph_iqueue_t q, CGRAPH_INTEGER *out)
{
  void *data;
  int ret = cgraph_queue_poll(q, &data);
  if (ret != 0)
  {
    return ret;
  }
  *out = *((CGRAPH_INTEGER *)data);
  free(data);
  return 0;
}

int cgraph_iqueue_enqueue(cgraph_iqueue_t q, CGRAPH_INTEGER element)
{
  CGRAPH_INTEGER *data = (CGRAPH_INTEGER *)malloc(sizeof(CGRAPH_INTEGER));
  *data = element;
  return cgraph_queue_enqueue(q, data);
}

size_t cgraph_iqueue_size(cgraph_iqueue_const_t const q)
{
  return cgraph_queue_size(q);
}

void cgraph_iqueue_free(cgraph_iqueue_t *q)
{
  cgraph_queue_free(*q);
}

bool cgraph_iqueue_empty(cgraph_iqueue_t const q)
{
  return cgraph_queue_empty(q);
}

struct cgraph_istack_s
{
  cgraph_ivec_t items;
};

cgraph_istack_t cgraph_istack_create()
{
  cgraph_istack_t s = (cgraph_istack_t)malloc(sizeof(CGraphIStack));
  if (s != NULL)
  {
    s->items = cgraph_ivec_create();
  }
  return s;
}

int cgraph_istack_push(cgraph_istack_t s, CGRAPH_INTEGER element)
{
  return cgraph_ivec_push_back(&(s->items), element);
}

int cgraph_istack_pop(cgraph_istack_t s, CGRAPH_INTEGER *out)
{
  int ret = 0;
  if (out)
  {
    ret = cgraph_istack_top(s, out);
  }
  if (ret != 0)
  {
    return ret;
  }
  return cgraph_ivec_setsize(s->items, cgraph_ivec_size(s->items) - 1);
}

void cgraph_istack_free(cgraph_istack_t *s)
{
  cgraph_ivec_free(&((*s)->items));
  free(*s);
}

int cgraph_istack_top(cgraph_istack_const_t const s, CGRAPH_INTEGER *out)
{
  size_t sz = cgraph_ivec_size(s->items);
  if (sz == 0)
  {
    return 1;
  }
  *out = (s->items)[sz - 1];
  return 0;
}

size_t cgraph_istack_size(cgraph_istack_const_t const s)
{
  return cgraph_ivec_size(s->items);
}

bool cgraph_istack_empty(cgraph_istack_const_t const s)
{
  return cgraph_istack_size(s) == 0;
}

cgraph_ivec_t cgraph_ivec_create()
{
  return (cgraph_ivec_t) & ((size_t *)calloc(2, sizeof(size_t)))[2];
}

cgraph_ivec_t cgraph_ivec_from_array(CGRAPH_INTEGER *a,
                                     CGRAPH_INTEGER n)
{
  cgraph_ivec_t v = cgraph_ivec_create();
  int ret = 0;
  for (CGRAPH_INTEGER i = 0; i < n; ++i)
  {
    ret += cgraph_ivec_push_back(&v, a[i]);
  }
  if (ret)
  {
    CGRAPH_ERROR("Can not create a vector from an array");
    cgraph_ivec_free(&v);
  }
  return ret == 0 ? v : NULL;
}

CGRAPH_INTEGER cgraph_ivec_max(cgraph_ivec_t const v)
{
  CGRAPH_INTEGER max = v[0];
  for (CGRAPH_INTEGER i = 1; i < cgraph_ivec_size(v); ++i)
  {
    if (v[i] > max)
    {
      max = v[i];
    }
  }
  return max;
}

int cgraph_ivec_minmax(cgraph_ivec_t const v, CGRAPH_INTEGER *min, CGRAPH_INTEGER *max)
{
  CGRAPH_INTEGER _min, _max;
  _min = _max = v[0];
  for (CGRAPH_INTEGER i = 1; i < cgraph_ivec_size(v); ++i)
  {
    if (v[i] > _max)
    {
      _max = v[i];
    }
    else if (v[i] < _min)
    {
      _min = v[i];
    }
  }
  if (min)
  {
    *min = _min;
  }
  if (max)
  {
    *max = _max;
  }
  if (!min && !max)
  {
    return 1;
  }
  return 0;
}

bool cgraph_ivec_isininterval(cgraph_ivec_t const v,
                              CGRAPH_INTEGER low,
                              CGRAPH_INTEGER high)
{
  for (CGRAPH_INTEGER i = 0; i < cgraph_ivec_size(v); ++i)
  {
    if (v[i] < low || v[i] > high)
    {
      return false;
    }
  }
  return true;
}

static cgraph_ivec_t _v;
static cgraph_ivec_t _v2;
int ref_cmp(const void *o1, const void *o2)
{
  CGRAPH_INTEGER i1 = *((CGRAPH_INTEGER *)o1),
                 i2 = *((CGRAPH_INTEGER *)o2);
  if (_v[i1] < _v[i2])
  {
    return -1;
  }
  else if (_v[i1] > _v[i2])
  {
    return 1;
  }
  return _v2[i1] - _v2[i2];
}

int cgraph_ivec_order(cgraph_ivec_t const v,
                      cgraph_ivec_t const v2,
                      cgraph_ivec_t const res)
{
  _v = v;
  _v2 = v2;
  CGRAPH_INTEGER n = cgraph_ivec_size(v);
  for (int i = 0; i < n; ++i)
  {
    res[i] = i;
  }
  qsort(res, n, sizeof(CGRAPH_INTEGER), ref_cmp);
  return 0;
}

int cgraph_ivec_null(cgraph_ivec_t const v)
{
  cgraph_ivec_fill(v, 0);
  return 0;
}

int cgraph_ivec_setsize(cgraph_ivec_t const v, CGRAPH_INTEGER newsize)
{
  CGRAPH_INTEGER capacity = (CGRAPH_INTEGER)cgraph_ivec_capacity(v);
  if (newsize <= capacity && v)
  {
    ((size_t *)(v))[-2] = (newsize);
    return 0;
  }
  return 1;
}

CGRAPH_INTEGER cgraph_ivec_capacity(cgraph_ivec_t const v)
{
  return ((v) ? ((size_t *)(v))[-1] : (size_t)0);
}

CGRAPH_INTEGER cgraph_ivec_size(cgraph_ivec_t const v)
{
  return ((v) ? ((size_t *)(v))[-2] : (size_t)0);
}

int cgraph_ivec_fill(cgraph_ivec_t const v, CGRAPH_INTEGER data)
{
  size_t sz = cgraph_ivec_size(v);
  for (CGRAPH_INTEGER i = 0; i < sz; ++i)
  {
    v[i] = data;
  }
  return 0;
}

int cgraph_ivec_print(cgraph_ivec_t const v)
{
  printf("size: %lld, cap: %lld, elems: ",
         (long long)cgraph_ivec_size(v),
         (long long)cgraph_ivec_capacity(v));
  for (CGRAPH_INTEGER i = 0; i < cgraph_ivec_size(v); ++i)
  {
    printf(" %lld", (long long)v[i]);
  }
  printf("\n");
  return 0;
}

int cgraph_ivec_grow(cgraph_ivec_t *v, CGRAPH_INTEGER newcapacity)
{
  CGRAPH_INTEGER capacity = (CGRAPH_INTEGER)cgraph_ivec_capacity((*v));
  if (capacity < newcapacity)
  {
    const size_t __sz = newcapacity * sizeof(CGRAPH_INTEGER) + (sizeof(size_t) * 2);
    size_t *__p1 = &((size_t *)(*v))[-2];
    size_t *__p2 = (size_t *)realloc(__p1, (__sz));
    assert(__p2);
    (*v) = (cgraph_ivec_t)(&__p2[2]);
    cgraph_ivec_t vec = *v;
    if (vec)
    {
      ((size_t *)(vec))[-1] = newcapacity;
    }
  }
  return 0;
}

int cgraph_ivec_init(cgraph_ivec_t *v, CGRAPH_INTEGER size)
{
  cgraph_ivec_grow(v, size);
  cgraph_ivec_setsize(*v, size);
  return 0;
}

int cgraph_ivec_push_back(cgraph_ivec_t *v, CGRAPH_INTEGER value)
{
  size_t __cap = cgraph_ivec_capacity(*v);
  if (__cap <= cgraph_ivec_size(*v))
  {
    cgraph_ivec_grow(v, !__cap ? __cap + 1 : __cap * 2);
  }
  cgraph_ivec_t vec = *v;
  vec[cgraph_ivec_size(vec)] = (value);
  cgraph_ivec_setsize((vec), cgraph_ivec_size(vec) + 1);
  return 0;
}

int cgraph_ivec_append(cgraph_ivec_t *v,
                       CGRAPH_INTEGER *a, CGRAPH_INTEGER n)
{
  int ret = 0;
  for (CGRAPH_INTEGER i = 0; i < n; ++i)
  {
    ret += cgraph_ivec_push_back(v, a[i]);
  }
  return ret;
}

int cgraph_ivec_free(cgraph_ivec_t *v)
{
  cgraph_ivec_t vec = *v;
  if (vec)
  {
    size_t *p1 = &((size_t *)(vec))[-2];
    free(p1);
  }
  return 0;
}

typedef struct cgraph_queue_s CGraphQueue;

#ifdef __cplusplus
extern "C"
{
#endif

  CGraphQueue *cgraph_queue_create();
  void cgraph_queue_free(CGraphQueue *q);
  int cgraph_queue_enqueue(CGraphQueue *q, void *value);
  int cgraph_queue_poll(CGraphQueue *q, void **out);
  int cgraph_queue_peek(const CGraphQueue *const q, void **out);
  size_t cgraph_queue_size(const CGraphQueue *const q);
  bool cgraph_queue_empty(const CGraphQueue *const q);

#ifdef __cplusplus
}
#endif

typedef struct _cgraph_queue_node
{
  void *value;
  struct _cgraph_queue_node *next;
} CGraphQueueNode;

struct cgraph_queue_s
{
  int size;
  CGraphQueueNode *head;
  CGraphQueueNode *tail;
};

CGraphQueue *cgraph_queue_create()
{
  CGraphQueue *q =
      (CGraphQueue *)malloc(sizeof(CGraphQueue));

  if (q == NULL)
  {
    return q;
  }

  q->size = 0;
  q->head = NULL;
  q->tail = NULL;

  return q;
}

void cgraph_queue_free(CGraphQueue *q)
{
  while (q->head != NULL)
  {
    CGraphQueueNode *tmp = q->head;
    q->head = q->head->next;
    if (tmp->value != NULL)
    {
      free(tmp->value);
    }
    free(tmp);
  }

  free(q);
}

int cgraph_queue_enqueue(CGraphQueue *q, void *value)
{
  CGraphQueueNode *node =
      (CGraphQueueNode *)malloc(sizeof(CGraphQueueNode));

  if (node == NULL)
  {
    return 1;
  }

  node->value = value;
  node->next = NULL;

  if (q->head == NULL)
  {
    q->head = node;
    q->tail = node;
    q->size = 1;
    return 0;
  }

  q->tail->next = node;
  q->tail = node;
  q->size += 1;

  return 0;
}

int cgraph_queue_poll(CGraphQueue *q, void **out)
{
  int ret = cgraph_queue_peek(q, out);
  if (ret != 0)
  {
    return ret;
  }

  CGraphQueueNode *tmp = q->head;
  q->head = q->head->next;
  q->size -= 1;
  free(tmp);
  /*
  client take the responsibility to free value
  */

  return 0;
}

int cgraph_queue_peek(const CGraphQueue *const q, void **out)
{
  if (q->size == 0)
  {
    *out = NULL;
    return 1;
  }
  *out = q->head->value;
  return 0;
}

size_t cgraph_queue_size(const CGraphQueue *const q)
{
  return q->size;
}

bool cgraph_queue_empty(const CGraphQueue *const q)
{
  return q->size == 0;
}

cgraph_rvec_t cgraph_rvec_create()
{
  return (cgraph_rvec_t) & ((size_t *)calloc(2, sizeof(size_t)))[2];
}

int cgraph_rvec_setsize(cgraph_rvec_t const v, CGRAPH_INTEGER newsize)
{
  CGRAPH_INTEGER capacity = (CGRAPH_INTEGER)cgraph_rvec_capacity(v);
  if (newsize <= capacity && v)
  {
    ((size_t *)(v))[-2] = (newsize);
    return 0;
  }
  return 1;
}

CGRAPH_INTEGER cgraph_rvec_capacity(cgraph_rvec_t const v)
{
  return ((v) ? ((size_t *)(v))[-1] : (size_t)0);
}

CGRAPH_INTEGER cgraph_rvec_size(cgraph_rvec_t const v)
{
  return ((v) ? ((size_t *)(v))[-2] : (size_t)0);
}

int cgraph_rvec_print(cgraph_rvec_t const v)
{
  printf("size: %lld, cap: %lld, elems: ",
         (long long)cgraph_rvec_size(v),
         (long long)cgraph_rvec_capacity(v));
  for (CGRAPH_INTEGER i = 0; i < cgraph_rvec_size(v); ++i)
  {
    printf(" %Lf", (long double)v[i]);
  }
  printf("\n");
  return 0;
}

int cgraph_rvec_grow(cgraph_rvec_t *v, CGRAPH_INTEGER newcapacity)
{
  CGRAPH_INTEGER capacity = (CGRAPH_INTEGER)cgraph_rvec_capacity((*v));
  if (capacity < newcapacity)
  {
    const size_t __sz = newcapacity * sizeof(CGRAPH_REAL) + (sizeof(size_t) * 2);
    size_t *__p1 = &((size_t *)(*v))[-2];
    size_t *__p2 = (size_t *)realloc(__p1, (__sz));
    assert(__p2);
    (*v) = (cgraph_rvec_t)(&__p2[2]);
    cgraph_rvec_t vec = *v;
    if (vec)
    {
      ((size_t *)(vec))[-1] = newcapacity;
    }
  }
  return 0;
}

int cgraph_rvec_init(cgraph_rvec_t *v, CGRAPH_INTEGER size)
{
  cgraph_rvec_grow(v, size);
  cgraph_rvec_setsize(*v, size);
  return 0;
}

int cgraph_rvec_push_back(cgraph_rvec_t *v, CGRAPH_REAL value)
{
  size_t __cap = cgraph_rvec_capacity(*v);
  if (__cap <= cgraph_rvec_size(*v))
  {
    cgraph_rvec_grow(v, !__cap ? __cap + 1 : __cap * 2);
  }
  cgraph_rvec_t vec = *v;
  vec[cgraph_rvec_size(vec)] = (value);
  cgraph_rvec_setsize((vec), cgraph_rvec_size(vec) + 1);
  return 0;
}

int cgraph_rvec_free(cgraph_rvec_t *v)
{
  cgraph_rvec_t vec = *v;
  if (vec)
  {
    size_t *p1 = &((size_t *)(vec))[-2];
    free(p1);
  }
  return 0;
}
#define PARENT(x) (((x) + 1) / 2 - 1)
#define LEFTCHILD(x) (((x) + 1) * 2 - 1)
#define RIGHTCHILD(x) (((x) + 1) * 2)
void cgraph_i_2wheap_switch(cgraph_2wheap_t *h,
                            CGRAPH_INTEGER e1, CGRAPH_INTEGER e2)
{
  if (e1 != e2)
  {
    CGRAPH_INTEGER tmp1, tmp2;
    CGRAPH_REAL tmp3 = h->data[e1];
    h->data[e1] = h->data[e2];
    h->data[e2] = tmp3;

    tmp1 = h->index[e1];
    tmp2 = h->index[e2];

    h->index2[tmp1] = e2 + 2;
    h->index2[tmp2] = e1 + 2;

    h->index[e1] = tmp2;
    h->index[e2] = tmp1;
  }
}

void cgraph_i_2wheap_shift_up(cgraph_2wheap_t *h,
                              CGRAPH_INTEGER elem)
{
  if (elem == 0 || h->data[elem] < h->data[PARENT(elem)])
  {
    /* at the top */
  }
  else
  {
    cgraph_i_2wheap_switch(h, elem, PARENT(elem));
    cgraph_i_2wheap_shift_up(h, PARENT(elem));
  }
}

void cgraph_i_2wheap_sink(cgraph_2wheap_t *h,
                          CGRAPH_INTEGER head)
{
  CGRAPH_INTEGER size = cgraph_2wheap_size(h);
  if (LEFTCHILD(head) >= size)
  {
    /* no subtrees */
  }
  else if (RIGHTCHILD(head) == size ||
           h->data[LEFTCHILD(head)] >= h->data[RIGHTCHILD(head)])
  {
    /* sink to the left if needed */
    if (h->data[head] < h->data[LEFTCHILD(head)])
    {
      cgraph_i_2wheap_switch(h, head, LEFTCHILD(head));
      cgraph_i_2wheap_sink(h, LEFTCHILD(head));
    }
  }
  else
  {
    /* sink to the right */
    if (h->data[head] < h->data[RIGHTCHILD(head)])
    {
      cgraph_i_2wheap_switch(h, head, RIGHTCHILD(head));
      cgraph_i_2wheap_sink(h, RIGHTCHILD(head));
    }
  }
}

/* ------------------ */
/* These are public   */
/* ------------------ */

int cgraph_2wheap_init(cgraph_2wheap_t *h, CGRAPH_INTEGER size)
{
  h->size = size;
  h->data = cgraph_rvec_create();
  h->index = cgraph_ivec_create();
  h->index2 = cgraph_ivec_create();

  /* We start with the biggest */
  CGRAPH_CHECK(cgraph_ivec_init(&h->index2, size));
  return 0;
}

void cgraph_2wheap_free(cgraph_2wheap_t *h)
{
  cgraph_rvec_free(&h->data);
  cgraph_ivec_free(&h->index);
  cgraph_ivec_free(&h->index2);
}

int cgraph_2wheap_clear(cgraph_2wheap_t *h)
{
  cgraph_rvec_setsize(h->data, 0);
  cgraph_ivec_setsize(h->index, 0);
  cgraph_ivec_setsize(h->index2, 0);
  return 0;
}

bool cgraph_2wheap_empty(const cgraph_2wheap_t *h)
{
  return cgraph_rvec_size(h->data) == 0;
}

int cgraph_2wheap_push_with_index(cgraph_2wheap_t *h,
                                  CGRAPH_INTEGER idx, CGRAPH_REAL elem)
{

  /*   printf("-> %.2g [%li]\n", elem, idx); */
  CGRAPH_INTEGER size = cgraph_rvec_size(h->data);
  CGRAPH_CHECK(cgraph_rvec_push_back(&h->data, elem));
  CGRAPH_CHECK(cgraph_ivec_push_back(&h->index, idx));
  h->index2[idx] = size + 2;

  /* maintain heap */
  cgraph_i_2wheap_shift_up(h, size);
  return 0;
}

CGRAPH_INTEGER cgraph_2wheap_size(const cgraph_2wheap_t *h)
{
  return cgraph_rvec_size(h->data);
}

CGRAPH_INTEGER cgraph_2wheap_max_size(const cgraph_2wheap_t *h)
{
  return h->size;
}

CGRAPH_REAL cgraph_2wheap_max(const cgraph_2wheap_t *h)
{
  return h->data[0];
}

CGRAPH_INTEGER cgraph_2wheap_max_index(const cgraph_2wheap_t *h)
{
  return h->index[0];
}

bool cgraph_2wheap_has_elem(const cgraph_2wheap_t *h, CGRAPH_INTEGER idx)
{
  return h->index2[idx] != 0;
}

bool cgraph_2wheap_has_active(const cgraph_2wheap_t *h, CGRAPH_INTEGER idx)
{
  return h->index2[idx] > 1;
}

CGRAPH_REAL cgraph_2wheap_get(const cgraph_2wheap_t *h, CGRAPH_INTEGER idx)
{
  CGRAPH_INTEGER i = h->index2[idx] - 2;
  return h->data[i];
}

CGRAPH_REAL cgraph_2wheap_delete_max(cgraph_2wheap_t *h)
{
  CGRAPH_REAL tmp = h->data[0];
  CGRAPH_INTEGER tmpidx = h->index[0];
  cgraph_i_2wheap_switch(h, 0, cgraph_2wheap_size(h) - 1);
  cgraph_rvec_setsize(h->data, cgraph_rvec_size(h->data) - 1);
  cgraph_ivec_setsize(h->index, cgraph_ivec_size(h->index) - 1);
  h->index2[tmpidx] = 0;
  cgraph_i_2wheap_sink(h, 0);

  /*   printf("<-max %.2g\n", tmp); */
  return tmp;
}

CGRAPH_REAL cgraph_2wheap_deactivate_max(cgraph_2wheap_t *h)
{

  CGRAPH_REAL tmp = h->data[0];
  CGRAPH_INTEGER tmpidx = h->index[0];
  cgraph_i_2wheap_switch(h, 0, cgraph_2wheap_size(h) - 1);
  cgraph_rvec_setsize(h->data, cgraph_rvec_size(h->data) - 1);
  cgraph_ivec_setsize(h->index, cgraph_ivec_size(h->index) - 1);
  h->index2[tmpidx] = 1;
  cgraph_i_2wheap_sink(h, 0);

  return tmp;
}

CGRAPH_REAL cgraph_2wheap_delete_max_index(cgraph_2wheap_t *h, CGRAPH_INTEGER *idx)
{

  CGRAPH_REAL tmp = h->data[0];
  CGRAPH_INTEGER tmpidx = h->index[0];
  cgraph_i_2wheap_switch(h, 0, cgraph_2wheap_size(h) - 1);
  cgraph_rvec_setsize(h->data, cgraph_rvec_size(h->data) - 1);
  cgraph_ivec_setsize(h->index, cgraph_ivec_size(h->index) - 1);
  h->index2[tmpidx] = 0;
  cgraph_i_2wheap_sink(h, 0);

  if (idx)
  {
    *idx = tmpidx;
  }
  return tmp;
}

int cgraph_2wheap_modify(cgraph_2wheap_t *h, CGRAPH_INTEGER idx, CGRAPH_REAL elem)
{

  CGRAPH_INTEGER pos = h->index2[idx] - 2;

  /*   printf("-- %.2g -> %.2g\n", VECTOR(h->data)[pos], elem); */

  h->data[pos] = elem;
  cgraph_i_2wheap_sink(h, pos);
  cgraph_i_2wheap_shift_up(h, pos);

  return 0;
}

/* Check that the heap is in a consistent state */

int cgraph_2wheap_check(cgraph_2wheap_t *h)
{
  CGRAPH_INTEGER size = cgraph_2wheap_size(h);
  CGRAPH_INTEGER i;
  bool error = 0;

  /* Check the heap property */
  for (i = 0; i < size; i++)
  {
    if (LEFTCHILD(i) >= size)
    {
      break;
    }
    if (h->data[LEFTCHILD(i)] > h->data[i])
    {
      error = 1;
      break;
    }
    if (RIGHTCHILD(i) >= size)
    {
      break;
    }
    if (h->data[RIGHTCHILD(i)] > h->data[i])
    {
      error = 1;
      break;
    }
  }

  if (error)
  {
    CGRAPH_ERROR("Inconsistent heap");
    return 1;
  }

  return 0;
}
int cgraph_is_dag(const cgraph_t *graph, bool *res)
{
  if (!cgraph_is_directed(graph))
  {
    *res = false;
    return 0;
  }

  CGRAPH_INTEGER no_of_nodes = cgraph_vcount(graph);
  cgraph_ivec_t degrees = cgraph_ivec_create(),
                neis = cgraph_ivec_create();
  cgraph_iqueue_t sources = cgraph_iqueue_create();
  CGRAPH_INTEGER node, i, j, nei, vertices_left;

  cgraph_degree_all(graph, &degrees, CGRAPH_OUT, true);

  vertices_left = no_of_nodes;

  /* Do we have nodes with no incoming edges? */
  for (i = 0; i < no_of_nodes; i++)
  {
    if (degrees[i] == 0)
    {
      CGRAPH_CHECK(cgraph_iqueue_enqueue(sources, i));
    }
  }

  /* Take all nodes with no incoming edges and remove them */
  while (!cgraph_iqueue_empty(sources))
  {
    cgraph_iqueue_poll(sources, &node);
    /* Exclude the node from further source searches */
    degrees[node] = -1;
    vertices_left--;

    /* Get the neighbors and decrease their degrees by one */
    CGRAPH_CHECK(cgraph_neighbors(graph, &neis, node, CGRAPH_IN));
    j = cgraph_ivec_size(neis);
    for (i = 0; i < j; i++)
    {
      nei = neis[i];
      // if (nei == node) {
      //   continue;
      // }
      degrees[nei]--;
      if (degrees[nei] == 0)
      {
        CGRAPH_CHECK(cgraph_iqueue_enqueue(sources, nei));
      }
    }
  }

  *res = (vertices_left == 0);
  if (vertices_left < 0)
  {
    CGRAPH_ERROR("vertices_left < 0 in cgraph_is_dag, possible bug");
  }

  cgraph_ivec_free(&degrees);
  cgraph_ivec_free(&neis);
  cgraph_iqueue_free(&sources);

  return 0;
}
int cgraph_topological_sorting(const cgraph_t *graph,
                               cgraph_ivec_t *res,
                               cgraph_neimode_t mode)
{
  CGRAPH_INTEGER no_of_nodes = cgraph_vcount(graph);
  cgraph_ivec_t degrees = cgraph_ivec_create(),
                neis = cgraph_ivec_create();
  cgraph_iqueue_t sources = cgraph_iqueue_create();
  cgraph_neimode_t deg_mode;

  if (mode == CGRAPH_ALL || !cgraph_is_directed(graph))
  {
    CGRAPH_ERROR("topological sorting does not make sense for undirected graphs");
  }
  else if (mode == CGRAPH_OUT)
  {
    deg_mode = CGRAPH_IN;
  }
  else if (mode == CGRAPH_IN)
  {
    deg_mode = CGRAPH_OUT;
  }
  else
  {
    CGRAPH_ERROR("invalid mode");
  }

  /* with loops, igraph doesn't count loop */
  CGRAPH_CHECK(cgraph_degree_all(graph, &degrees, deg_mode, 1));

  cgraph_ivec_setsize(*res, 0);
  /* Do we have nodes with no incoming vertices? */
  for (CGRAPH_INTEGER i = 0; i < no_of_nodes; i++)
  {
    if (degrees[i] == 0)
    {
      CGRAPH_CHECK(cgraph_iqueue_enqueue(sources, i));
    }
  }

  /* Take all nodes with no incoming vertices and remove them */
  while (!cgraph_iqueue_empty(sources))
  {
    CGRAPH_INTEGER node;
    cgraph_iqueue_poll(sources, &node);
    cgraph_ivec_push_back(res, node);
    degrees[node] = -1;
    CGRAPH_CHECK(cgraph_neighbors(graph, &neis, node, mode));
    for (CGRAPH_INTEGER i = 0; i < cgraph_ivec_size(neis); i++)
    {
      degrees[neis[i]]--;
      if (degrees[neis[i]] == 0)
      {
        CGRAPH_CHECK(cgraph_iqueue_enqueue(sources, neis[i]));
      }
    }
  }

  if (cgraph_ivec_size(*res) < no_of_nodes)
  {
    CGRAPH_ERROR("graph contains a cycle, partial result is returned");
  }

  cgraph_ivec_free(&degrees);
  cgraph_ivec_free(&neis);
  cgraph_iqueue_free(&sources);
  return 0;
}
int cgraph_get_shortest_path_dijkstra(const cgraph_t *graph,
                                      cgraph_ivec_t *vertices,
                                      cgraph_ivec_t *edges,
                                      CGRAPH_INTEGER from,
                                      CGRAPH_INTEGER to,
                                      cgraph_rvec_t weights,
                                      cgraph_neimode_t mode)
{
  if (!weights)
  {
    return cgraph_get_shortest_path(graph, vertices, edges, from, to, mode);
  }
  CGRAPH_INTEGER no_of_nodes = cgraph_vcount(graph);
  CGRAPH_INTEGER no_of_edges = cgraph_ecount(graph);
  cgraph_2wheap_t Q;
  cgraph_rvec_t dists = cgraph_rvec_create();
  if (cgraph_rvec_size(weights) != no_of_edges)
  {
    CGRAPH_ERROR("Weight vector length does not match");
  }
  CGRAPH_CHECK(cgraph_2wheap_init(&Q, no_of_nodes));
  cgraph_rvec_init(&dists, no_of_edges);
  for (CGRAPH_INTEGER i = 0; i < no_of_nodes; ++i)
  {
    dists[i] = -1.0;
  }
  CGRAPH_INTEGER *parents =
      (CGRAPH_INTEGER *)malloc(sizeof(CGRAPH_INTEGER) * no_of_nodes);
  dists[from] = 0.0;
  parents[from] = -1; /* no dirty hack in back trace */
  cgraph_2wheap_push_with_index(&Q, from, 0);
  cgraph_ivec_t neis = cgraph_ivec_create();
  bool found = false;
  while (!cgraph_2wheap_empty(&Q) && !found)
  {
    CGRAPH_INTEGER nlen, minnei = cgraph_2wheap_max_index(&Q);
    CGRAPH_REAL mindist = -cgraph_2wheap_delete_max(&Q); /* dirty hack to avoid using infinity */
    if (minnei == to)
    {
      found = true;
      break;
    }
    cgraph_incident(graph, &neis, minnei, mode);
    nlen = cgraph_ivec_size(neis);
    for (CGRAPH_INTEGER i = 0; i < nlen; ++i)
    {
      CGRAPH_INTEGER edge = neis[i];
      CGRAPH_INTEGER tto = CGRAPH_OTHER(graph, edge, minnei);
      CGRAPH_REAL altdist = mindist + weights[edge];
      CGRAPH_REAL curdist = dists[tto];
      if (curdist < 0)
      {
        dists[tto] = altdist;
        parents[tto] = edge;
        CGRAPH_CHECK(cgraph_2wheap_push_with_index(&Q, tto, -altdist));
      }
      else if (altdist < curdist)
      {
        dists[tto] = altdist;
        parents[tto] = edge;
        CGRAPH_CHECK(cgraph_2wheap_modify(&Q, tto, -altdist));
      }
    }
  }
  if (!found)
  {
    CGRAPH_ERROR("Path not found");
    if (vertices)
    {
      cgraph_ivec_setsize(*vertices, 0);
    }
    if (edges)
    {
      cgraph_ivec_setsize(*edges, 0);
    }
    return 0;
  }

  if (vertices || edges)
  {
    cgraph_ivec_t vvec, evec;
    CGRAPH_INTEGER act = to;
    CGRAPH_INTEGER size = 0;
    CGRAPH_INTEGER edge;
    while (parents[act] != -1)
    {
      ++size;
      edge = parents[act];
      act = CGRAPH_OTHER(graph, edge, act);
    }
    if (vertices)
    {
      CGRAPH_CHECK(cgraph_ivec_init(vertices, size + 1));
      vvec = *vertices;
      vvec[size] = to;
    }
    if (edges)
    {
      CGRAPH_CHECK(cgraph_ivec_init(edges, size));
      evec = *edges;
    }
    act = to;
    while (parents[act] != -1)
    {
      edge = parents[act];
      act = CGRAPH_OTHER(graph, edge, act);
      --size;
      if (vertices)
      {
        vvec[size] = act;
      }
      if (edges)
      {
        evec[size] = edge;
      }
    }
  }
  cgraph_2wheap_free(&Q);
  cgraph_rvec_free(&dists);
  free(parents);
  return 0;
}

int cgraph_get_shortest_path(const cgraph_t *graph,
                             cgraph_ivec_t *vertices,
                             cgraph_ivec_t *edges,
                             CGRAPH_INTEGER from,
                             CGRAPH_INTEGER to,
                             cgraph_neimode_t mode)
{
  CGRAPH_INTEGER no_of_edges = cgraph_ecount(graph);
  cgraph_rvec_t weights = cgraph_rvec_create();
  cgraph_rvec_init(&weights, no_of_edges);
  for (CGRAPH_INTEGER i = 0; i < no_of_edges; ++i)
  {
    weights[i] = 1.0;
  }
  CGRAPH_INTEGER ret = cgraph_get_shortest_path_dijkstra(graph, vertices, edges, from, to, weights, mode);
  cgraph_rvec_free(&weights);
  return ret;
}

int cgraph_create(cgraph_t *graph,
                  cgraph_ivec_t const edges,
                  CGRAPH_INTEGER n,
                  bool directed)
{
  bool has_edges = cgraph_ivec_size(edges) > 0;
  CGRAPH_INTEGER max = has_edges ? cgraph_ivec_max(edges) + 1 : 0;

  if (cgraph_ivec_size(edges) % 2 != 0)
  {
    CGRAPH_ERROR("Invalid (odd) edges vector");
  }
  if (has_edges && !cgraph_ivec_isininterval(edges, 0, max - 1))
  {
    CGRAPH_ERROR("Invalid (negative) vertex id");
  }

  CGRAPH_CHECK(cgraph_empty(graph, n, directed));

  if (has_edges)
  {
    CGRAPH_INTEGER vc = cgraph_vcount(graph);
    if (vc < max)
    {
      CGRAPH_CHECK(cgraph_add_vertices(graph, (CGRAPH_INTEGER)(max - vc)));
    }
    CGRAPH_CHECK(cgraph_add_edges(graph, edges));
  }

  return 0;
}
CGRAPH_INTEGER cgraph_vcount(const cgraph_t *graph)
{
  return graph->n;
}

CGRAPH_INTEGER cgraph_ecount(const cgraph_t *graph)
{
  return (CGRAPH_INTEGER)cgraph_ivec_size(graph->from);
}
bool cgraph_is_directed(const cgraph_t *graph)
{
  return graph->directed;
}

static int cgraph_i_create_start(
    cgraph_ivec_t res, cgraph_ivec_t el,
    cgraph_ivec_t iindex, CGRAPH_INTEGER nodes)
{

#define EDGE(i) el[iindex[(i)]]

  CGRAPH_INTEGER no_of_nodes;
  CGRAPH_INTEGER no_of_edges;
  CGRAPH_INTEGER i, j, idx;

  no_of_nodes = nodes;
  no_of_edges = cgraph_ivec_size(el);

  /* result */

  cgraph_ivec_setsize(res, nodes + 1);

  /* create the index */

  if (cgraph_ivec_size(el) == 0)
  {
    /* empty graph */
    cgraph_ivec_null(res);
  }
  else
  {
    idx = -1;
    for (i = 0; i <= EDGE(0); i++)
    {
      idx++;
      res[idx] = 0;
    }
    for (i = 1; i < no_of_edges; i++)
    {
      CGRAPH_INTEGER n =
          (CGRAPH_INTEGER)(EDGE(i) - EDGE(res[idx]));
      for (j = 0; j < n; j++)
      {
        idx++;
        res[idx] = i;
      }
    }
    j = EDGE(res[idx]);
    for (i = 0; i < no_of_nodes - j; i++)
    {
      idx++;
      res[idx] = no_of_edges;
    }
  }

  /* clean */

#undef EDGE
  return 0;
}
int cgraph_empty(cgraph_t *graph, CGRAPH_INTEGER n, bool directed)
{

  if (n < 0)
  {
    CGRAPH_ERROR("cannot create empty graph with negative number of vertices");
  }

  graph->n = 0;
  graph->directed = directed;
  graph->from = cgraph_ivec_create();
  graph->to = cgraph_ivec_create();
  graph->oi = cgraph_ivec_create();
  graph->ii = cgraph_ivec_create();
  graph->os = cgraph_ivec_create();
  graph->is = cgraph_ivec_create();

  cgraph_ivec_push_back(&graph->os, 0);
  cgraph_ivec_push_back(&graph->is, 0);

  /* add the vertices */
  CGRAPH_CHECK(cgraph_add_vertices(graph, n));

  return 0;
}
int cgraph_add_edges(cgraph_t *graph, cgraph_ivec_t const edges)
{
  long int no_of_edges = cgraph_ecount(graph);
  long int edges_to_add = cgraph_ivec_size(edges) / 2;
  long int i = 0;
  cgraph_error_handler_t *oldhandler;
  bool ret1, ret2;
  cgraph_ivec_t newoi = cgraph_ivec_create(),
                newii = cgraph_ivec_create();
  bool directed = cgraph_is_directed(graph);

  if (cgraph_ivec_size(edges) % 2 != 0)
  {
    CGRAPH_ERROR("invalid (odd) length of edges vector");
  }
  if (!cgraph_ivec_isininterval(edges, 0, cgraph_vcount(graph) - 1))
  {
    CGRAPH_ERROR("cannot add edges");
  }

  /* from & to */
  CGRAPH_CHECK(cgraph_ivec_grow(&graph->from, no_of_edges + edges_to_add));
  CGRAPH_CHECK(cgraph_ivec_grow(&graph->to, no_of_edges + edges_to_add));

  while (i < edges_to_add * 2)
  {
    if (directed || edges[i] > edges[i + 1])
    {
      cgraph_ivec_push_back(&graph->from, edges[i++]); /* reserved */
      cgraph_ivec_push_back(&graph->to, edges[i++]);   /* reserved */
    }
    else
    {
      cgraph_ivec_push_back(&graph->to, edges[i++]);   /* reserved */
      cgraph_ivec_push_back(&graph->from, edges[i++]); /* reserved */
    }
  }

  /* disable the error handler temporarily */
  oldhandler = cgraph_set_error_handler(cgraph_error_handler_ignore);

  /* oi & ii */
  ret1 = cgraph_ivec_init(&newoi, no_of_edges + edges_to_add);
  ret2 = cgraph_ivec_init(&newii, no_of_edges + edges_to_add);
  if (ret1 != 0 || ret2 != 0)
  {
    cgraph_ivec_setsize(graph->from, no_of_edges); /* gets smaller */
    cgraph_ivec_setsize(graph->to, no_of_edges);   /* gets smaller */
    cgraph_set_error_handler(oldhandler);
    CGRAPH_ERROR("cannot add edges");
  }
  ret1 = cgraph_ivec_order(graph->from, graph->to, newoi);
  ret2 = cgraph_ivec_order(graph->to, graph->from, newii);
  if (ret1 != 0 || ret2 != 0)
  {
    cgraph_ivec_setsize(graph->from, no_of_edges);
    cgraph_ivec_setsize(graph->to, no_of_edges);
    cgraph_ivec_free(&newoi);
    cgraph_ivec_free(&newii);
    cgraph_set_error_handler(oldhandler);
    CGRAPH_ERROR("cannot add edges");
  }

  /* os & is, its length does not change, error safe */
  cgraph_i_create_start(graph->os, graph->from, newoi, graph->n);
  cgraph_i_create_start(graph->is, graph->to, newii, graph->n);

  /* everything went fine  */
  cgraph_ivec_free(&graph->oi);
  cgraph_ivec_free(&graph->ii);
  graph->oi = newoi;
  graph->ii = newii;
  cgraph_set_error_handler(oldhandler);

  return 0;
}
int cgraph_add_vertices(cgraph_t *graph, CGRAPH_INTEGER nv)
{
  long int ec = cgraph_ecount(graph);
  long int i;

  if (nv < 0)
  {
    CGRAPH_ERROR("cannot add negative number of vertices");
  }

  CGRAPH_CHECK(cgraph_ivec_grow(&graph->os, graph->n + nv + 1));
  CGRAPH_CHECK(cgraph_ivec_grow(&graph->is, graph->n + nv + 1));
  cgraph_ivec_setsize(graph->os, graph->n + nv + 1);
  cgraph_ivec_setsize(graph->is, graph->n + nv + 1);

  for (i = graph->n + 1; i < graph->n + nv + 1; i++)
  {
    (graph->os)[i] = ec;
    (graph->is)[i] = ec;
  }

  graph->n += nv;

  return 0;
}
void cgraph_destroy(cgraph_t *graph)
{
  cgraph_ivec_free(&graph->from);
  cgraph_ivec_free(&graph->to);
  cgraph_ivec_free(&graph->oi);
  cgraph_ivec_free(&graph->ii);
  cgraph_ivec_free(&graph->os);
  cgraph_ivec_free(&graph->is);
}

int cgraph_neighbors(const cgraph_t *graph,
                     cgraph_ivec_t *neis,
                     CGRAPH_INTEGER vid,
                     cgraph_neimode_t mode)
{
  const CGRAPH_INTEGER node = vid;

  if (node < 0 || node > cgraph_vcount(graph) - 1)
  {
    CGRAPH_ERROR("cannot get neighbors");
  }
  if (mode != CGRAPH_OUT && mode != CGRAPH_IN &&
      mode != CGRAPH_ALL)
  {
    CGRAPH_ERROR("cannot get neighbors");
  }

  if (!graph->directed)
  {
    mode = CGRAPH_ALL;
  }

  cgraph_ivec_setsize(*neis, 0);

  if (!cgraph_is_directed(graph) || mode != CGRAPH_ALL)
  {
    if (mode & CGRAPH_OUT)
    {
      CGRAPH_INTEGER j = (graph->os)[node + 1];
      for (CGRAPH_INTEGER i = (graph->os)[node]; i < j; i++)
      {
        cgraph_ivec_push_back(neis, (graph->to)[(graph->oi)[i]]);
      }
    }
    if (mode & CGRAPH_IN)
    {
      CGRAPH_INTEGER j = (graph->is)[node + 1];
      for (CGRAPH_INTEGER i = (graph->is)[node]; i < j; i++)
      {
        cgraph_ivec_push_back(neis, (graph->from)[(graph->ii)[i]]);
      }
    }
  }
  else
  {
    /* both in- and out- neighbors in a directed graph,
       we need to merge the two 'vectors' */
    CGRAPH_INTEGER j1 = (graph->os)[node + 1];
    CGRAPH_INTEGER j2 = (graph->is)[node + 1];
    CGRAPH_INTEGER i1 = (graph->os)[node];
    CGRAPH_INTEGER i2 = (graph->is)[node];
    while (i1 < j1 && i2 < j2)
    {
      CGRAPH_INTEGER n1 = (graph->to)[(graph->oi)[i1]];
      CGRAPH_INTEGER n2 = (graph->from)[(graph->ii)[i2]];
      if (n1 < n2)
      {
        cgraph_ivec_push_back(neis, n1);
        i1++;
      }
      else if (n1 > n2)
      {
        cgraph_ivec_push_back(neis, n2);
        i2++;
      }
      else
      {
        cgraph_ivec_push_back(neis, n1);
        cgraph_ivec_push_back(neis, n2);
        i1++;
        i2++;
      }
    }
    while (i1 < j1)
    {
      CGRAPH_INTEGER n1 = (graph->to)[(graph->oi)[i1]];
      cgraph_ivec_push_back(neis, n1);
      i1++;
    }
    while (i2 < j2)
    {
      CGRAPH_INTEGER n2 = (graph->from)[(graph->ii)[i2]];
      cgraph_ivec_push_back(neis, n2);
      i2++;
    }
  }

  return 0;
}

int cgraph_incident(const cgraph_t *graph,
                    cgraph_ivec_t *eids,
                    CGRAPH_INTEGER vid,
                    cgraph_neimode_t mode)
{
  const CGRAPH_INTEGER node = vid;
  if (node < 0 || node > cgraph_vcount(graph) - 1)
  {
    CGRAPH_ERROR("cannot get neighbors");
  }
  if (mode != CGRAPH_OUT && mode != CGRAPH_IN &&
      mode != CGRAPH_ALL)
  {
    CGRAPH_ERROR("cannot get neighbors");
  }

  if (!graph->directed)
  {
    mode = CGRAPH_ALL;
  }

  cgraph_ivec_setsize(*eids, 0);

  if (mode & CGRAPH_OUT)
  {
    CGRAPH_INTEGER j = (graph->os)[node + 1];
    for (CGRAPH_INTEGER i = (graph->os)[node]; i < j; i++)
    {
      cgraph_ivec_push_back(eids, (graph->oi)[i]);
    }
  }
  if (mode & CGRAPH_IN)
  {
    CGRAPH_INTEGER j = (graph->is)[node + 1];
    for (CGRAPH_INTEGER i = (graph->is)[node]; i < j; i++)
    {
      cgraph_ivec_push_back(eids, (graph->ii)[i]);
    }
  }
  return 0;
}

int cgraph_degree_all(const cgraph_t *graph,
                      cgraph_ivec_t *res,
                      cgraph_neimode_t mode,
                      bool loops)
{
  if (mode != CGRAPH_OUT && mode != CGRAPH_IN &&
      mode != CGRAPH_ALL)
  {
    CGRAPH_ERROR("cannot get degree");
  }
  if (!cgraph_is_directed(graph))
  {
    mode = CGRAPH_ALL;
  }
  CGRAPH_INTEGER no_of_nodes = cgraph_vcount(graph);
  CGRAPH_INTEGER no_of_edges = cgraph_ecount(graph);
  cgraph_ivec_init(res, no_of_nodes);
  cgraph_ivec_t v = *res;
  cgraph_ivec_fill(v, 0);

  for (CGRAPH_INTEGER ed = 0; ed < no_of_edges; ++ed)
  {
    if (loops || graph->from[ed] != graph->to[ed])
    {
      if (mode & CGRAPH_IN)
      {
        v[graph->to[ed]] += 1;
      }
      if (mode & CGRAPH_OUT)
      {
        v[graph->from[ed]] += 1;
      }
    }
  }
  return 0;
}

int cgraph_degree_one(const cgraph_t *graph,
                      CGRAPH_INTEGER *res,
                      const CGRAPH_INTEGER node,
                      cgraph_neimode_t mode,
                      bool loops)
{
  if (node < 0 || node > cgraph_vcount(graph) - 1)
  {
    CGRAPH_ERROR("cannot get degree");
  }
  if (mode != CGRAPH_OUT && mode != CGRAPH_IN &&
      mode != CGRAPH_ALL)
  {
    CGRAPH_ERROR("cannot get degree");
  }
  if (!cgraph_is_directed(graph))
  {
    mode = CGRAPH_ALL;
  }
  CGRAPH_INTEGER d = 0;
  if (mode & CGRAPH_IN)
  {
    d += (graph->is[node + 1] - graph->is[node]);
  }
  if (mode & CGRAPH_OUT)
  {
    d += (graph->os[node + 1] - graph->os[node]);
  }
  if (!loops)
  {
    if (mode & CGRAPH_IN)
    {
      CGRAPH_INTEGER j = graph->is[node];
      CGRAPH_INTEGER j1 = graph->is[node + 1];
      for (CGRAPH_INTEGER i = j; i < j1; ++i)
      {
        CGRAPH_INTEGER idx = graph->ii[i];
        if (graph->from[idx] == graph->to[idx])
        {
          --d;
        }
      }
    }
    if (mode & CGRAPH_OUT)
    {
      CGRAPH_INTEGER j = graph->os[node];
      CGRAPH_INTEGER j1 = graph->os[node + 1];
      for (CGRAPH_INTEGER i = j; i < j1; ++i)
      {
        CGRAPH_INTEGER idx = graph->oi[i];
        if (graph->from[idx] == graph->to[idx])
        {
          --d;
        }
      }
    }
  }
  *res = d;
  return 0;
}
int cgraph_edge(const cgraph_t *graph, CGRAPH_INTEGER eid,
                CGRAPH_INTEGER *from, CGRAPH_INTEGER *to)
{
  if (cgraph_is_directed(graph))
  {
    *from = (CGRAPH_INTEGER)(graph->from)[eid];
    *to = (CGRAPH_INTEGER)(graph->to)[eid];
  }
  else
  {
    *from = (CGRAPH_INTEGER)(graph->to)[eid];
    *to = (CGRAPH_INTEGER)(graph->from)[eid];
  }

  return 0;
}
#define BINSEARCH(start, end, value, iindex, edgelist, N, pos) \
  do                                                           \
  {                                                            \
    while ((start) < (end))                                    \
    {                                                          \
      CGRAPH_INTEGER mid = (start) + ((end) - (start)) / 2;    \
      CGRAPH_INTEGER e = (iindex)[mid];                        \
      if ((edgelist)[e] < (value))                             \
      {                                                        \
        (start) = mid + 1;                                     \
      }                                                        \
      else                                                     \
      {                                                        \
        (end) = mid;                                           \
      }                                                        \
    }                                                          \
    if ((start) < (N))                                         \
    {                                                          \
      CGRAPH_INTEGER e = (iindex)[(start)];                    \
      if ((edgelist)[e] == (value))                            \
      {                                                        \
        *(pos) = (CGRAPH_INTEGER)e;                            \
      }                                                        \
    }                                                          \
  } while (0)

#define FIND_DIRECTED_EDGE(graph, xfrom, xto, eid)                     \
  do                                                                   \
  {                                                                    \
    CGRAPH_INTEGER start = (graph->os)[xfrom];                         \
    CGRAPH_INTEGER end = (graph->os)[xfrom + 1];                       \
    CGRAPH_INTEGER N = end;                                            \
    CGRAPH_INTEGER start2 = (graph->is)[xto];                          \
    CGRAPH_INTEGER end2 = (graph->is)[xto + 1];                        \
    CGRAPH_INTEGER N2 = end2;                                          \
    if (end - start < end2 - start2)                                   \
    {                                                                  \
      BINSEARCH(start, end, xto, graph->oi, graph->to, N, eid);        \
    }                                                                  \
    else                                                               \
    {                                                                  \
      BINSEARCH(start2, end2, xfrom, graph->ii, graph->from, N2, eid); \
    }                                                                  \
  } while (0)

#define FIND_UNDIRECTED_EDGE(graph, from, to, eid) \
  do                                               \
  {                                                \
    CGRAPH_INTEGER xfrom1 = from > to ? from : to; \
    CGRAPH_INTEGER xto1 = from > to ? to : from;   \
    FIND_DIRECTED_EDGE(graph, xfrom1, xto1, eid);  \
  } while (0)

int cgraph_get_eid(const cgraph_t *graph, CGRAPH_INTEGER *eid,
                   CGRAPH_INTEGER pfrom, CGRAPH_INTEGER pto,
                   bool directed)
{

  CGRAPH_INTEGER from = pfrom, to = pto;
  CGRAPH_INTEGER nov = cgraph_vcount(graph);

  if (from < 0 || to < 0 || from > nov - 1 || to > nov - 1)
  {
    CGRAPH_ERROR("cannot get edge id");
  }

  *eid = -1;
  if (cgraph_is_directed(graph))
  {

    /* Directed graph */
    FIND_DIRECTED_EDGE(graph, from, to, eid);
    if (!directed && *eid < 0)
    {
      FIND_DIRECTED_EDGE(graph, to, from, eid);
    }
  }
  else
  {
    /* Undirected graph, they only have one mode */
    FIND_UNDIRECTED_EDGE(graph, from, to, eid);
  }

  if (*eid < 0)
  {
    CGRAPH_ERROR("Cannot get edge id, no such edge");
  }

  return 0;
}

/******************************** Util and main functions ********************************/

int main()
{
  FILE *fptr = fopen("input.txt", "r");
  int n, i = 0;
  cgraph_ivec_t edges = cgraph_ivec_create();
  cgraph_ivec_t order = cgraph_ivec_create();
  cgraph_ivec_t order_out = cgraph_ivec_create();
  cgraph_t g;
  cgraph_ivec_push_back(&edges, 1);
  cgraph_ivec_push_back(&edges, 2);

  cgraph_ivec_push_back(&edges, 1);
  cgraph_ivec_push_back(&edges, 3);

  cgraph_ivec_push_back(&edges, 2);
  cgraph_ivec_push_back(&edges, 4);

  cgraph_ivec_push_back(&edges, 2);
  cgraph_ivec_push_back(&edges, 5);

  cgraph_ivec_push_back(&edges, 2);
  cgraph_ivec_push_back(&edges, 6);

  cgraph_ivec_push_back(&edges, 5);
  cgraph_ivec_push_back(&edges, 7);

  cgraph_ivec_push_back(&edges, 3);
  cgraph_ivec_push_back(&edges, 6);

  cgraph_ivec_push_back(&edges, 4);
  cgraph_ivec_push_back(&edges, 7);

  cgraph_create(&g, edges, 0, true);
  // cgraph_dfs(&g, 1, CGRAPH_OUT, false, &order, &order_out, NULL, NULL);
  cgraph_ivec_t res = cgraph_ivec_create();
  cgraph_degree_all(&g, &res, CGRAPH_OUT, true);
  for (i = 0; i < cgraph_vcount(&g); i++)
  {
    printf("%d", res[i]);
  }
  fclose(fptr);
  fptr = fopen("output.txt", "w");
  cgraph_destroy(&g);
  cgraph_ivec_free(&edges);
  fclose(fptr);
  return 0;
}