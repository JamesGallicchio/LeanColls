#include <lean/lean.h>
#include <string.h>

// Declare array class

static lean_external_class* leancolls_array_external_class = NULL;

static inline void leancolls_array_finalizer(void *ptr)
{
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

lean_obj_res leancolls_array_box(lean_object** arr)
{
    return lean_alloc_external(leancolls_array_external_class, arr);
}

lean_object** leancolls_array_unbox(lean_obj_arg o) {
    return (lean_object**)(lean_get_external_data(o));
}

static inline void leancolls_array_ensure_exclusive(lean_obj_arg a) {
    if (lean_is_exclusive(a))
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

static inline size_t leancolls_unbox_array_size(b_lean_obj_arg n) {
    // On both 64bit and 32bit systems, if n is not scalar this would OOM
    if (!lean_is_scalar(n)) {
        lean_internal_panic_out_of_memory();
    }

    size_t len = (size_t)(n>>1);
    if (len != sizeof(lean_object*) * len / sizeof(lean_object*)) {
        lean_internal_panic_out_of_memory();
    }

    return len;
}


// Implement basic external functions

lean_obj_res leancolls_array_new(b_lean_obj_arg n) {

    size_t len = leancolls_unbox_array_size(n);

    lean_object** backing = malloc(sizeof(lean_object*) * len);
    // Check if malloc failed
    if (backing == NULL) {
        lean_panic_fn(NULL, lean_mk_string(
            "LeanColls.Array: New allocation failed! (Out of memory?)"
        ));
    }

    return leancolls_array_box(backing);
}

lean_obj_res leancolls_array_get(b_lean_obj_arg len, b_lean_obj_arg arr, b_lean_obj_arg i) {
    // `len` is scalar; non-scalar `len` will OOM (see `leancolls_unbox_array_size`)
    assert(lean_is_scalar(len));
    // `(i : Fin len)` so `i` should be a scalar less than `len`
    assert(lean_is_scalar(i));
    assert(lean_unbox(i) < lean_unbox(len)); // (Could compare boxed values directly but...)

    lean_object* a = (leancolls_array_unbox(arr))[lean_unbox(i)];
    lean_inc(a);
    return a;
}

lean_obj_res leancolls_array_set(b_lean_obj_arg len, lean_obj_arg arr, b_lean_obj_arg i, lean_obj_arg a) {
    // `len` is scalar; non-scalar `len` will OOM (see `new`)
    assert(lean_is_scalar(len));
    // `(i : Fin len)` so `i` should be a scalar less than `len`
    assert(lean_is_scalar(i));
    assert(lean_unbox(i) < lean_unbox(len)); // (Could compare boxed values directly but...)

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

lean_object* leancolls_array_resize(b_lean_obj_arg len, lean_obj_arg arr, b_lean_obj_arg m) {
    size_t new_len = leancolls_unbox_array_size(m);

    lean_object** old_backing = leancolls_unbox_array(arr);
    lean_object** new_backing = realloc(old_backing, sizeof(lean_object*) * new_len);
    // Check if realloc failed
    if (new_backing == NULL) {
        lean_panic_fn(NULL, lean_mk_string(
            "LeanColls.Array: Reallocation failed! (Out of memory?)"
        ));
    }

    return leancolls_array_box(backing);
}
