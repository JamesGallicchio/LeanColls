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

static inline lean_obj_res leancolls_array_ensure_exclusive(size_t len, lean_obj_arg a) {
    if (lean_is_exclusive(a))
        return a;
    
    if (lean_is_persistent(a)) {
        // Make a copy I guess?
        lean_object** backing = malloc(sizeof(lean_object*) * len);
        memcpy(backing, leancolls_array_unbox(a), sizeof(lean_object*) * len);

        return lean_alloc_external(leancolls_array_external_class, backing);
    }
    
    lean_panic_fn(NULL, lean_mk_string("LeanColls.Array being mutated, but not exclusive or persistent!"));
}



// Implement basic external functions

lean_obj_res leancolls_array_new(lean_obj_arg a, size_t len) {

    // TODO: Check that len is not too big (panic if it is)
    lean_object** backing = malloc(sizeof(lean_object*) * len);
    
    for (size_t i = 0; i < len; i++) {
        lean_inc(a);
        backing[i] = a;
    }
    return leancolls_array_box(backing);
}

lean_obj_res leancolls_array_get(b_lean_obj_arg n, lean_obj_arg arr, size_t i) {
    lean_object* a = (leancolls_array_unbox(arr))[i];
    lean_inc(a);
    return a;
}

lean_obj_res leancolls_array_set(size_t len, lean_obj_arg arr, size_t i, lean_obj_arg a) {
    arr = leancolls_array_ensure_exclusive(len, arr);

    lean_object** backing = leancolls_array_unbox(arr);
    lean_object* old = backing[i];
    lean_dec(old);

    lean_inc(a);
    backing[i] = a;

    return arr;
}

lean_object* leancolls_array_extend(lean_object* idk, lean_object* what, lean_object* this) {
    return 0;
}

lean_object* leancolls_array_shrink(lean_object* idk, lean_object* what, lean_object* this) {
    return 0;
}

lean_object* leancolls_array_unwrap_somes(lean_object* idk, lean_object* what) {
    return 0;
}

// Implement functions to/from Lean internal representation

lean_object* leancolls_array_to_list(lean_object* idk, lean_object* what) {
    return 0;
}

lean_object* leancolls_array_of_list(lean_object* idk, lean_object* what) {
    return 0;
}
