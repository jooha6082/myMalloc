#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation

  header * dumb = NULL;

  // check raw_size is usable
  if (raw_size == 0) {
    return NULL;
  }

  // round up raw_size to multiple of 8
  size_t alloc_size = (raw_size + 7) & -8;
  if (alloc_size < 16) {
    alloc_size = 16;
  }
  alloc_size += ALLOC_HEADER_SIZE;

  // find the start index for searching freelist
  size_t initial = alloc_size / 8 - 1;
  if (initial > N_LISTS - 1) {
    initial = N_LISTS - 1;
  }

  //iterate freelist to find block////
  for (int i = initial; i < N_LISTS; i++) {

    if (freelistSentinels[i].next == &freelistSentinels[i]) {
        continue;
    }

    // unalloc block exactly equal alloc_size
    if (get_size(((header *)&freelistSentinels[i])->next) == alloc_size) {

      header * head  = freelistSentinels[i].next;
      freelistSentinels[i].next->prev = &freelistSentinels[i];
      freelistSentinels[i].next = head->next;
      head->prev = NULL;
      head->next = NULL;
      set_size(head, alloc_size);
      set_state(head, ALLOCATED);
      return (header *)head->data;

    // unalloc block greater than alloc_size
    } else if ((get_size(((header *)&freelistSentinels[i])->next) > alloc_size)) {

      // set unallocated
      header * head = freelistSentinels[i].next;
      freelistSentinels[i].next->prev = &freelistSentinels[i];
      freelistSentinels[i].next = head->next;
      head->prev = NULL;
      head->next = NULL;
      set_size(head, get_size(head) - alloc_size);
      set_state(head, UNALLOCATED);

      i = (get_size(head) - ALLOC_HEADER_SIZE) / 8 - 1;

      if (i > N_LISTS - 1) {
        i = N_LISTS - 1;
      }

      // insert to freelist
      freelistSentinels[i].next->prev = head;
      head->next = freelistSentinels[i].next;
      head->prev = &freelistSentinels[i];
      freelistSentinels[i].next = head;

      // set allocated
      set_size(get_right_header(head), alloc_size);
      set_state(get_right_header(head), ALLOCATED);
      get_right_header(head)->left_size = get_size(head);
      get_right_header(get_right_header(head))->left_size = get_size(get_right_header(head));
      return (header *)get_right_header(head)->data;

    // unalloc block less than alloc_size
    } else {
      break;
    }
  }
  header * new_chunk = allocate_chunk(ARENA_SIZE);
  header * left_fencepost = get_header_from_offset(new_chunk, -ALLOC_HEADER_SIZE);
  header * original_lf = get_header_from_offset(left_fencepost, -ALLOC_HEADER_SIZE);

  // R_FP1 = lastFencePost (adjacent)
  if (get_header_from_offset(left_fencepost, -ALLOC_HEADER_SIZE) == lastFencePost) {

    lastFencePost = get_right_header(new_chunk);
    lastFencePost->left_size = alloc_size;

    //set_size(get_header_from_offset(lastFencePost, -(alloc_size + ALLOC_HEADER_SIZE)), alloc_size + ALLOC_HEADER_SIZE);
    //set_state(get_header_from_offset(lastFencePost, -(alloc_size + ALLOC_HEADER_SIZE)), ALLOCATED);

    set_state(left_fencepost, UNALLOCATED);

    // when there are remaining memory in firt chunk
    if (get_state(get_left_header(original_lf)) != ALLOCATED) {
      get_left_header(original_lf)->prev->next = get_left_header(original_lf)->next;
      get_left_header(original_lf)->next->prev = get_left_header(original_lf)->prev;

      original_lf = get_left_header(original_lf);
      set_size(original_lf, get_size(original_lf) + get_size(left_fencepost) + get_size(new_chunk) + ALLOC_HEADER_SIZE);
      set_state(original_lf, UNALLOCATED);

      header * new_head = get_header_from_offset(original_lf, get_size(original_lf) - alloc_size);
      set_size(new_head, alloc_size);
      set_state(new_head, ALLOCATED);
      set_size(original_lf, get_size(original_lf) - get_size(new_head));
      new_head->left_size = get_size(original_lf);

      int i = (get_size(original_lf) - ALLOC_HEADER_SIZE) / 8 - 1;
      if (i > N_LISTS - 1) {
        i = N_LISTS - 1;
      }

      freelistSentinels[i].next->prev = original_lf;
      original_lf->next = freelistSentinels[i].next;
      original_lf->prev = &freelistSentinels[i];
      freelistSentinels[i].next = original_lf;

      return (header *)new_head->data;

    // no remaining memory in first chunk
    } else {

      set_size(original_lf, get_size(original_lf) + get_size(left_fencepost) + get_size(new_chunk) - 2 * ALLOC_HEADER_SIZE);
      set_state(original_lf, UNALLOCATED);

      int i = (get_size(original_lf) - ALLOC_HEADER_SIZE) / 8 - 1;
      if (i > N_LISTS - 1) {
        i = N_LISTS - 1;
      }

      freelistSentinels[i].next->prev = original_lf;
      original_lf->next = freelistSentinels[i].next;
      original_lf->prev = &freelistSentinels[i];
      freelistSentinels[i].next = original_lf;

      header * new_head = get_header_from_offset(original_lf, get_size(original_lf));
      set_size(new_head, alloc_size);
      set_state(new_head, ALLOCATED);
      new_head->left_size = get_size(original_lf);





    return (header *)new_head->data;
    }

  // not adjacent
  } else {
    insert_os_chunk(get_left_header(new_chunk));
  }

  lastFencePost = get_right_header(new_chunk);

  set_size(new_chunk, get_size(new_chunk) - alloc_size);
  set_state(new_chunk, UNALLOCATED);

  set_size(get_right_header(new_chunk), alloc_size);
  set_state(get_right_header(new_chunk), ALLOCATED);
  get_right_header(new_chunk)->left_size = get_size(new_chunk);
  get_right_header(get_right_header(new_chunk))->left_size = get_size(get_right_header(new_chunk));

  int i = (get_size(new_chunk) - ALLOC_HEADER_SIZE) / 8 - 1;

  if (i > N_LISTS - 1) {
    i = N_LISTS - 1;
  }

  new_chunk->next = freelistSentinels[i].next;
  new_chunk->prev = &freelistSentinels[i];
  freelistSentinels[i].next = new_chunk;
  freelistSentinels[i].next->prev = &freelistSentinels[i];
  freelistSentinels[i].next->next->prev = NULL; 
  new_chunk->next->prev = new_chunk;

  return (header *)get_right_header(new_chunk)->data;
}
/*
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));/i
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  if (p == NULL) {
    return;
  }
  header * head = (header *)((char *) p - ALLOC_HEADER_SIZE);

  //check for double free
  if (get_state(head) == UNALLOCATED) {
    printf("Double Free Detected\n");
    assert(false);
  }
  set_state(head, UNALLOCATED);
  int notcoalesced = 0;
  header * list = NULL;

  // both sides are not unallocated
  if (get_state(get_left_header(head)) != UNALLOCATED && get_state(get_right_header(head)) != UNALLOCATED) {

    notcoalesced++;

    size_t nometasize = (get_size(head) - ALLOC_HEADER_SIZE) / 8 - 1;
    if (nometasize > N_LISTS - 1) {
      nometasize = N_LISTS - 1;
    }
    list = &freelistSentinels[nometasize];
    head->prev = list;
    head->next = list->next;
    list->next->prev = head;
    list->next = head;
    lastFencePost->left_size = get_size(get_left_header(lastFencePost));

  // only left is unallocated
  } else if (get_state(get_left_header(head)) == UNALLOCATED && get_state(get_right_header(head)) != UNALLOCATED) {

    get_left_header(head)->prev->next = get_left_header(head)->next;
    get_left_header(head)->next->prev = get_left_header(head)->prev;
    size_t mergedsize = get_size(get_left_header(head)) + get_size(head);
    set_size(get_left_header(head), mergedsize);
    get_right_header(head)->left_size = get_size(get_left_header(head));

    mergedsize = (mergedsize - ALLOC_HEADER_SIZE) / 8 - 1;
    if (mergedsize >  N_LISTS){
      mergedsize = N_LISTS - 1;
    }

    header * list = &freelistSentinels[mergedsize];
    get_left_header(head)->prev = list;
    get_left_header(head)->next = list->next;
    list->next->prev = get_left_header(head);
    list->next = get_left_header(head);
    get_left_header(head)->next->left_size = get_size(head);
    lastFencePost->left_size = get_size(get_left_header(lastFencePost));

  // only right is unallocated
  } else if (get_state(get_left_header(head)) != UNALLOCATED && get_state(get_right_header(head)) == UNALLOCATED) {

    get_right_header(head)->prev->next = get_right_header(head)->next;
    get_right_header(head)->next->prev = get_right_header(head)->prev;
    size_t mergedsize = get_size(get_right_header(head)) + get_size(head);
    set_size(head, mergedsize);
    get_right_header(get_right_header(head))->left_size = get_size(get_left_header(head));

    mergedsize = (mergedsize - ALLOC_HEADER_SIZE) / 8 - 1;
    if (mergedsize >  N_LISTS){
      mergedsize = N_LISTS - 1;
    }

    header * list = &freelistSentinels[mergedsize];
    head->prev = list;
    head->next = list->next;
    list->next->prev = head;
    list->next = head;
    head->next->left_size = get_size(head);
    lastFencePost->left_size = get_size(head);

  // both are unallocated
  } else {
      notcoalesced--;
      size_t mergedsize = get_size(get_left_header(head)) + get_size(head) + get_size(get_right_header(head));
      set_size(get_left_header(head), mergedsize);
      get_left_header(head)->left_size = get_size(get_left_header(get_left_header(head)));
      lastFencePost->left_size = get_size(get_left_header(head));
      get_left_header(head)->next->prev = get_left_header(head)->prev;
      get_left_header(head)->prev->next = get_left_header(head)->next;
      get_right_header(head)->next->prev = get_right_header(head)->prev;
      get_right_header(head)->prev->next = get_right_header(head)->next;

      mergedsize = (mergedsize - ALLOC_HEADER_SIZE) /8 - 1;
      if (mergedsize >  N_LISTS){
        mergedsize = N_LISTS - 1;
      }

      header * list = &freelistSentinels[mergedsize];
      get_left_header(head)->next = list->next;
      get_left_header(head)->prev = list;
      list->next->prev = get_left_header(head);
      list->next = get_left_header(head);
      lastFencePost->left_size = get_size(get_left_header(lastFencePost));

 }

}
/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next;
         fast != freelist;
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
