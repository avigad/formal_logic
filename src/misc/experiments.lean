import .vm_check ..syntax

/-
foo is an rbmap with ("A", 0) to ("Z", 25) 
-/
def foo := 
let l := (list.range 26).map (λ i, (char.to_string $ char.of_nat (i + 65), i))
in rbmap.from_list l

#eval foo.find "Z"

/- check time -/
-- set_option profiler true

-- too slow
-- theorem bar : foo.find "Z" = some 25 := rfl

#eval foo.find "Z"


-- curiously, fails; VM doesn't have code associated with bool.tt
-- example : tt = tt := by vm_check_tt

example : id tt = tt := by vm_check_tt

example : tt && tt = tt := by vm_check_tt

example : 2 < 5 := vm_check

-- fails
-- example : 5 < 2 := vm_check

-- fails
-- example : ∀ x, 2 < x := vm_check

example : 1000 * 1000 = 1000000 := vm_check

-- set_option profiler true

theorem bar : foo.find "Z" = some 25 := vm_check

-- fails
-- example : ∀ x : nat, x = x :=
-- assume x, vm_check

namespace testeq

def foo (s t : string) : nat :=
if s = t then 0 else 1

def foo' (s t : nat) : nat :=
if s = t then 0 else 1

def bar (s t : string) : nat → nat
| 0 := 0
| (n+1):= foo s t + bar n

def bar' (s t : nat) : nat → nat
| 0 := 0
| (n+1):= foo' s t + bar' n

def baz := "hello"

def bla (s : string) : nat → nat
| 0 := 0
| (n+1):= foo s s + bla n

def bla' := "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"

def bla'' := "oxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"

set_option profiler true

/-
#eval bar bla' bla' 1000000

#eval bar bla' bla'' 1000000

#eval bar ("o"++ bla') bla'' 1000000

#eval bar "hello" "goodbye" 1000000

#eval bar "hello" "hello" 1000000

#eval bar "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
1000000

--#eval bar baz baz 1000000

--#eval bla "hello" 1000000

--#eval bar' 25 67 1000000

--#eval bar' 43 43 1000000

-/

end testeq

/-do
tgt ← target,
apply `(@of_to_bool_eq_tt %%tgt),
skip
-/


section
open hol
open hol.type

-- these seem slow
set_option profiler true

theorem arities_ok_mk_prop : arities_ok mk_prop :=
by { dsimp [mk_prop, arities_ok, arities_ok_aux, list.empty, coe_sort], reflexivity }

theorem arities_ok_mk_list_type (t : type) (h : arities_ok t) : arities_ok (mk_list_type t) = tt :=
by { dsimp [mk_list_type, arities_ok, coe_sort] at *, dsimp [arities_ok_aux], rw h, reflexivity }

theorem arities_ok_mk_list_type' (t : type) (h : arities_ok t) : arities_ok (mk_list_type t) = tt :=
by { simp [mk_list_type, arities_ok, coe_sort] at *, simp [arities_ok_aux], split, assumption, reflexivity }

@[simp] theorem arity_list : constructor.list.arity = 1 := rfl

theorem arities_ok_mk_list_type'' (t : type) (h : arities_ok t = tt) : arities_ok (mk_list_type t) = tt :=
by { simp [arities_ok] at *, simp [mk_list_type, arities_ok_aux, h] }

theorem arities_ok_mk_list_type''' (t : type) (h : arities_ok t = tt) : arities_ok (mk_list_type t) = tt :=  by { dsimp [arities_ok] at *, dsimp [mk_list_type, arities_ok_aux, constructor.list], rw h, reflexivity }

-- much faster
#eval arities_ok mk_prop
#eval arities_ok (mk_list_type mk_prop)

end
