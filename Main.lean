import Automata.NatCDFA
import Automata.Moore

def exampleAutomaton: NatCDFA 2 := {
  n := 3
  δ := fun σ α => match (σ, α) with
    | (0, 0) => 0
    | (0, 1) => 1
    | (1, 0) => 2
    | (1, 1) => 1
    | (2, _) => 2,
  i := 0,
  t := fun q => q = 0 || q = 1
}

def inputABString: IO (Option (List (Fin 2))) := do
  IO.print "Please enter a string: "
  let stdin <- IO.getStdin
  let line <- stdin.getLine
  let characters: List Char := line.trimAscii.chars.toList
  pure (characters.mapM fun
    | 'a' => some 0
    | 'b' => some 1
    | _ => none
  )

def inputRetry: Nat → IO (List (Fin 2))
  | n + 1 => inputABString >>= fun
    | some list => pure list
    | none => do
      IO.println "Invalid input! "
      inputRetry n
  | 0 => pure []

def inputAndTest (r: NatCDFA 2): IO Unit := do
  let input <- inputRetry 1000000000
  let result := r.accepts input
  if result then
    IO.println "Accepted! "
  else
    IO.println "Not accepted! "

def main : IO Unit :=
  let rec aux: Nat → IO Unit
    | n + 1 => do
      inputAndTest exampleAutomaton
      aux n
    | 0 => pure ()
  aux 1000000000
