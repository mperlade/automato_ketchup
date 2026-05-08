theorem Vector.get_ofFn {α} {n: Nat} {f: Fin n → α} {i: Fin n}:
    (Vector.ofFn f).get i = f i :=
  Array.getElem_ofFn _
