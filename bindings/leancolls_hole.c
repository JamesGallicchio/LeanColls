#include <lean/lean.h>
#include <string.h>
#include <stdlib.h>

/*
Hole C implementation

A hole includes a lean_object* and a pointer to the memory
where the hole needs to be filled.
*/
typedef struct {
    lean_object* head;
    lean_object** hole;
} hole_t;

// Declare external class

static lean_external_class* leancolls_hole_external_class = NULL;

static inline void leancolls_hole_finalizer(void *ptr)
{
    // TODO: rc dec everything? unsure how -- once linear typing,
    // can just ensure the value doesn't get dropped
    free(ptr);
}

static inline void leancolls_hole_foreach(void *mod, b_lean_obj_arg fn) {
    // TODO: what is this for ??
}

lean_obj_res leancolls_hole_initialize()
{
    leancolls_hole_external_class = lean_register_external_class(leancolls_hole_finalizer, leancolls_hole_foreach);
    return lean_io_result_mk_ok(lean_box(0));
}


// Exclusivity checks

static inline void leancolls_hole_ensure_exclusive(lean_obj_arg h) {
    if (LEAN_LIKELY(lean_is_exclusive(h)))
        return;
    
    if (lean_is_persistent(h)) {
        lean_panic_fn(NULL, lean_mk_string(
            "LeanColls.Hole: Mutation on persistent hole! (Try `set_option compiler.extract_closed false`)"
        ));
    } else {
        lean_panic_fn(NULL, lean_mk_string(
            "LeanColls.Hole: Mutation on shared hole!"
        ));
    }
}



// Making/finishing

lean_obj_res leancolls_hole_mk() {
    hole_t* hole = malloc(sizeof(hole_t));
    // The hole to be filled is found within the hole_t struct itself!
    hole->hole = &hole->head;
    return lean_alloc_external(leancolls_hole_external_class, (void*) hole);
}

lean_obj_res leancolls_hole_fill(lean_obj_arg h, lean_obj_arg a) {
    assert(lean_is_external(h));
    leancolls_hole_ensure_exclusive(h);

    // Deconstruct external object

    hole_t* hole = (hole_t*) lean_get_external_data(h);

    // Set hole to a
    *(hole->hole) = a;

    // Free the hole allocation and return the head value
    lean_obj_res head = hole->head;

    lean_dec(h);

    return head;
}




// Hole constructor implementations

lean_obj_res leancolls_hole_cons (lean_obj_arg h, lean_obj_arg a) {
    assert(lean_is_external(h));
    leancolls_hole_ensure_exclusive(h);

    lean_object* new_ctor = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(new_ctor, 0, a);
    
    lean_object** new_hole = &(lean_ctor_obj_cptr(new_ctor)[1]);

    hole_t* hole = lean_get_external_data(h);
    *(hole->hole) = new_ctor;
    hole->hole = new_hole;

    return h;
}
