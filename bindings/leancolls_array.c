#include <lean/lean.h>
#include <string.h>
#include <stdlib.h>

/*
ArrayUninit C implementation

Representation specified by three things:
  - uint64 n: length 
  - uint64 m: m <= n, "filled" length
  - lean_object*[n] backing:
    for 0 <= i < m, backing[i] is initialized with a valid lean_object*
    for m <= i < n, backing[i] is uninitialized

TODO: Eventually we may be able to ensure that the finalizer is
only called if all elements are uninitialized. Then we could
generalize to avoid the m parameter entirely, and let the
initialization status be a noncomputable property of the use code.
*/

// Declare external class

static lean_external_class* leancolls_array_external_class = NULL;

static inline void leancolls_array_finalizer(void *ptr)
{
    // TODO: Need to rc dec all elements of array (needs linear typing)
    free(ptr);
}

static inline void leancolls_array_foreach(void *mod, b_lean_obj_arg fn) {
    // TODO: what is this for ??
}

lean_obj_res leancolls_array_initialize()
{
    leancolls_array_external_class = lean_register_external_class(leancolls_array_finalizer, leancolls_array_foreach);
    return lean_io_result_mk_ok(lean_box(0));
}


// Getting into/out of lean_obj*

lean_obj_res leancolls_array_box(lean_object** arr) {
    return lean_alloc_external(leancolls_array_external_class, arr);
}

lean_object** leancolls_array_unbox(lean_obj_arg o) {
    assert (lean_is_external(o));
    return (lean_object**)(lean_get_external_data(o));
}

static inline size_t leancolls_array_unbox_size(b_lean_obj_arg n) {
    // On both 64bit and 32bit systems, if n is not scalar this would OOM
    if (!lean_is_scalar(n)) {
        lean_internal_panic_out_of_memory();
    }

    size_t len = (size_t)(lean_unbox(n));
    if (len != sizeof(lean_object*) * len / sizeof(lean_object*)) {
        lean_internal_panic_out_of_memory();
    }

    return len;
}


// Exclusivity checking

uint8_t leancolls_array_isexclusive(b_lean_obj_arg a) {
    if (lean_is_exclusive(a))
        return 1;
    else
        return 0;
}

static inline void leancolls_array_ensure_exclusive(lean_obj_arg a) {
    if (LEAN_LIKELY(lean_is_exclusive(a)))
        return;
    
    if (lean_is_persistent(a)) {
        lean_panic_fn(NULL, lean_mk_string(
            "LeanColls.Array: Mutation on persistent array! (Try `set_option compiler.extract_closed false`)"
        ));
    } else {
        lean_panic_fn(NULL, lean_mk_string(
            "LeanColls.Array: Mutation on shared array!"
        ));
    }
}


// Implement basic external functions

lean_obj_res leancolls_array_new(b_lean_obj_arg n) {

    size_t len = leancolls_array_unbox_size(n);

    lean_object** backing = malloc(sizeof(lean_object*) * len);
    // Check if malloc failed
    if (backing == NULL) {
        lean_panic_fn(NULL, lean_mk_string(
            "LeanColls.Array: New allocation failed! (Out of memory?)"
        ));
    }

    return leancolls_array_box(backing);
}

// Assuming `arr[i]` is initialized, retrieve it
lean_obj_res leancolls_array_get(
    b_lean_obj_arg len, b_lean_obj_arg filled,
    b_lean_obj_arg arr, b_lean_obj_arg i
) {
    // `len` is scalar; non-scalar `len` will OOM (see `leancolls_array_new`)
    assert(lean_is_scalar(len));
    // `filled <= len` (an invariant that should be maintained)
    assert(lean_is_scalar(filled));
    assert(lean_unbox(filled) <= lean_unbox(len));
    // `i < filled`
    assert(lean_is_scalar(i));
    assert(lean_unbox(i) < lean_unbox(filled));
    // `arr` is an external obj
    assert(lean_is_external(arr));

    lean_object** backing = leancolls_array_unbox(arr);

    size_t i_ = lean_unbox(i);

    lean_object* a = backing[i_];
    lean_inc(a);
    return a;
}

lean_obj_res leancolls_array_push(
    b_lean_obj_arg len, b_lean_obj_arg filled,
    lean_obj_arg arr, lean_obj_arg a
) {
    // `len` is scalar; non-scalar `len` will OOM (see `leancolls_array_new`)
    assert(lean_is_scalar(len));
    // `filled < len`
    assert(lean_is_scalar(filled));
    assert(lean_unbox(filled) < lean_unbox(len));
    // `arr` is an external obj
    assert(lean_is_external(arr));

    leancolls_array_ensure_exclusive(arr);

    lean_object** backing = leancolls_array_unbox(arr);

    size_t i_ = lean_unbox(filled);

    // Insert new value; old value is uninitialized.
    backing[i_] = a;

    return arr;
}

lean_obj_res leancolls_array_pop(
    b_lean_obj_arg len, b_lean_obj_arg filled,
    lean_obj_arg arr
) {
    // `len` is scalar; non-scalar `len` will OOM (see `leancolls_array_new`)
    assert(lean_is_scalar(len));
    // `0 < filled <= len`
    assert(lean_is_scalar(filled));
    assert(0 < lean_unbox(filled));
    assert(lean_unbox(filled) <= lean_unbox(len));
    // `arr` is an external obj
    assert(lean_is_external(arr));

    leancolls_array_ensure_exclusive(arr);

    lean_object** backing = leancolls_array_unbox(arr);

    size_t i_ = lean_unbox(filled);

    // Throw out old initialized value
    lean_dec(backing[i_ - 1]);

    return arr;
}

lean_obj_res leancolls_array_set(
    b_lean_obj_arg len, b_lean_obj_arg filled,
    lean_obj_arg arr, b_lean_obj_arg i, lean_obj_arg a
) {
    // `len` is scalar; non-scalar `len` will OOM (see `leancolls_array_new`)
    assert(lean_is_scalar(len));
    // `filled <= len`
    assert(lean_is_scalar(filled));
    assert(lean_unbox(filled) <= lean_unbox(len));
    // `i < filled`
    assert(lean_is_scalar(i));
    assert(lean_unbox(i) < lean_unbox(filled));
    // `arr` is an external obj
    assert(lean_is_external(arr));

    leancolls_array_ensure_exclusive(arr);

    lean_object** backing = leancolls_array_unbox(arr);

    size_t i_ = lean_unbox(i);

    // Remove old value
    lean_object* old = backing[i_];
    lean_dec(old);

    // Insert new value
    backing[i_] = a;

    return arr;
}

lean_object* leancolls_array_resize(
    b_lean_obj_arg len, b_lean_obj_arg filled,
    lean_obj_arg arr, b_lean_obj_arg len_
) {
    // `len` is scalar; non-scalar `len` will OOM (see `leancolls_array_unbox_size`)
    assert(lean_is_scalar(len));
    // filled <= len
    assert(lean_is_scalar(filled));
    assert(lean_unbox(filled) <= lean_unbox(len));

    size_t old_len = lean_unbox(len);
    size_t new_len = leancolls_array_unbox_size(len_);

    // filled <= len_ (so that no initialized elements are dropped)
    assert(lean_unbox(filled) <= new_len);

    leancolls_array_ensure_exclusive(arr);

    lean_object** old_backing = leancolls_array_unbox(arr);
    lean_free_small_object(arr);

    lean_object** new_backing = realloc(old_backing, sizeof(lean_object*) * new_len);
    // Check if realloc failed
    if (new_backing == NULL) {
        lean_panic_fn(NULL, lean_mk_string(
            "LeanColls.Array: Reallocation failed! (Out of memory?)"
        ));
    }

    return leancolls_array_box(new_backing);
}

