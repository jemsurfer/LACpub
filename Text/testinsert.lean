open List hiding Perm perm_cons perm_nil

variable {A B C : Type}

inductive Insert : A → List A → List A → Prop
| ins_hd : ∀ a:A, ∀ as : List A,

    ---------------------
    Insert a as (a :: as)

| ins_tl : ∀ a b:A, ∀ as as': List A,

    Insert a as as' →
    -----------------------------
    Insert a (b :: as) (b :: as')
