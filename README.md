# automato_ketchup

[![Build](https://github.com/mperlade/automato_ketchup/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/mperlade/automato_ketchup/actions/workflows/lean_action_ci.yml)

Efficient and verified DFA minimization in Lean 4


> [!WARNING]  
> This library is currently under active development. As a result, the API should be considered **unstable and subject to change without notice**. 


> [!NOTE]
> The algorithms in this library are not designed to be run by the proof kernel. They make extensive use of Array access and in-place mutation. These operations are $O(1)$ for compiled code, but $O(n)$ for the kernel that sees them as linked lists. If you want to use this library for proofs, it is recommended to use `native_decide`. Eventually, this library is intended to include tactics that can procedurally generate simple kernel-verifiable certificates (e.g. morphisms to a common automaton for automaton equivalence or counterexample words for automaton non-equivalence).

## Usage

The main type in this library is [`NatCDFA (a: Nat)`](https://mperlade.github.io/automato_ketchup/AutoKchp/CDFA.html#NatCDFA), representing complete deterministic finite automata on the alphabet `Fin a` whose states are natural numbers. Below are listed the main operations supported at this time: 

- **Minimization**: the API exposes [`NatCDFA.minimize`](https://mperlade.github.io/automato_ketchup/AutoKchp/Minimize.html#NatCDFA.minimize). This function uses Moore's radix sort-based algorithm and runs in $O(n^2 a)$.

- **Computation of a morphism**: see [`NatCDFA.findMorphism`](https://mperlade.github.io/automato_ketchup/AutoKchp/MorphismDfs.html#NatCDFA.findMorphism).

## Documentation

The automatically generated documentation is available [here](https://mperlade.github.io/automato_ketchup). It currently lacks comments.
