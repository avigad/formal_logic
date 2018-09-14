/-
A keyed_array is an array of data, each with a string key. The array index acts as a unique id. The
rbmap provides the inverse: given a key, it finds the index.
-/
import data.list

structure keyed_array (α : Type*) :=
(size : nat) (array : array size (string × α)) (rbmap : rbmap string nat)

namespace keyed_array

def read_key_safe {α : Type*} (k : keyed_array α) {i : nat} (h : i < k.size) := 
  (k.array.read ⟨i, h⟩).1

def read_safe {α : Type*} (k : keyed_array α) {i : nat} (h : i < k.size) := 
  (k.array.read ⟨i, h⟩).2

def read_key {α : Type*} (k : keyed_array α) (i : nat) : option string :=
if h : i < k.size then some (k.read_key_safe h) else none

def read {α : Type*} (k : keyed_array α) (i : nat) : option α :=
if h : i < k.size then some (k.read_safe h) else none

def find {α : Type*} (k : keyed_array α) (s : string) : option nat :=
  k.rbmap.find s

def is_sound {α : Type*} (k : keyed_array α) : Prop :=
(∀ i (h : i < k.size), k.find (k.read_key_safe h) = some i) ∧ 
  (∀ s i, k.find s = some i → ∃ h : i < k.size, k.read_key_safe h = s)

end keyed_array

namespace list
  private def to_rbmap_aux {α : Type*} : ℕ → list (string × α) → rbmap string nat 
  | n []            := mk_rbmap string nat
  | n ((k, d) :: l) := (to_rbmap_aux (n+1) l).insert k n 

  private def to_rbmap {α : Type*} (l : list (string × α)) : rbmap string nat :=
  to_rbmap_aux 0 l

  def to_keyed_array {α : Type*} (l : list (string × α)) : keyed_array α :=
  ⟨l.length, l.to_array, to_rbmap l⟩

  -- TODO: show this gives a sound keyed_array if there are no duplicates on the list.
end list
