def last (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [x] => some x
  | _ :: xs => last xs

example : last [1, 2, 3] = some 3 := by rfl

example : last ["a"] = some "a" := by rfl

example : last ([] : List Nat) = none := by rfl

def Prod.switch {α β : Type} : α × β → β × α
  | (a, b) => (b, a)

inductive PetName : Type where
  | dog : String → PetName
  | cat : String → PetName
deriving Repr

def zip {α β : Type} : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys

example : zip [1, 2, 3] ["a", "b", "c"] = [(1, "a"), (2, "b"), (3, "c")] := by rfl

example : zip [1, 2] ["a", "b", "c"] = [(1, "a"), (2, "b")] := by rfl

example : zip [1, 2, 3] ["a"] = [(1, "a")] := by rfl

def take {α : Type} : Nat → List α → List α
  | 0, _ => []
  | _, [] => []
  | n + 1, x :: xs => x :: take n xs

example : take 3 ["bolete", "oyster"] = ["bolete", "oyster"] := by rfl

example : take 1 ["bolete", "oyster"] = ["bolete"] := by rfl

def distribute {α β γ : Type} : α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)

example :
  let x : Nat × (String ⊕ Bool) := (42, Sum.inl "hello")
  distribute x = Sum.inl (42, "hello") := by rfl

example :
  let y : Nat × (String ⊕ Bool) := (42, Sum.inr true)
  distribute y = Sum.inr (42, true) := by rfl

-- Is there a typo in the question?
def f {α : Type} : Bool × α → α ⊕ α
  | (true, x) => Sum.inl x
  | (false, x) => Sum.inr x
