/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import .subst

section examples

open hol
open hol.term

private def foo : term :=
  let ty := mk_nat ⇒ mk_nat ⇒ mk_nat,
      f := Const (const.user 0 ty []),
      x := Var 0,
      y := Var 1,
      t := abstract 1 "y" mk_nat (App (App f x) y),
      c := Const (const.user 1 mk_nat []),
      s := subst c 0 t in
  s

#eval foo.repr
#eval repr (foo.typeof [])

end examples


