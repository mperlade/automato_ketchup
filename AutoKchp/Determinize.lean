/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.NatNFA
public import AutoKchp.NatCDFA
import AutoKchp.Internal.HeapSort


def powerInitial {a: Nat} {r: NatNFA a}: Array (Fin r.n) :=
  canonicalize (Fin.foldl r.n (fun acc q => if r.i q then acc.push q else acc) #[])


def powerDelta {a: Nat} {r: NatNFA a} (p: Array (Fin r.n)) (b: Fin a):
    Array (Fin r.n) :=
  canonicalize (p.foldl (fun acc q => acc.append (r.δ q b)) #[])


def powerFinal {a: Nat} {r: NatNFA a}: Array (Fin r.n) → Bool :=
  fun v => v.any (fun p => r.f p)
