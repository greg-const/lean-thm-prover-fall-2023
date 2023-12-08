
def char_to_num (c : Char) : Nat :=
match c with
| 'I' => 1
| 'V' => 5
| 'X' => 10
| 'L' => 50
| 'C' => 100
| 'D' => 500
| 'M' => 1000
| _ => 0

def sum_list (l : List Nat) (counter : Nat) : Nat :=
match l with
| [] => counter
| h :: t => sum_list t (h + counter)

def start_with_a (s : String) : Bool :=
  let cs := s.toList
  match cs with
  | 'a' :: _ => true
  | _ => false

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "Please enter a number in Roman Numerals"
  let input ← (stdin.getLine)

  -- Roman Numeral Alg
  let input1 := (input.replace "IV" "IIII").replace "IX" "VIIII"
  let input1 := (input1.replace "XL" "XXXX").replace "XC" "LXXXX"
  let input1 := (input1.replace "CD" "CCCC").replace "CM" "DCCCC"

  let input_list := input1.toList -- Turn result into a list of chars

  let num_list := input_list.map char_to_num  -- Map our translation function

  let result :=  sum_list num_list 0 -- sum the List of Nats

  -- Format output
  let input := input.dropRightWhile Char.isWhitespace
  stdout.putStrLn (input ++ s!" Translated to Base 10 Natural: {result}!")
