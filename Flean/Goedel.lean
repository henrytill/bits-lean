-- Translation from https://cstheory.stackexchange.com/a/20582

inductive Ty : Type where
  | nat : Ty
  | unit : Ty
  | arrow : Ty → Ty → Ty

infixr:60 " ~> " => Ty.arrow

abbrev Ty.denote : Ty → Type
  | .nat => Nat
  | .unit => Unit
  | .arrow a b => a.denote → b.denote

inductive Term : Ty → Type where
  | zero : Term .nat
  | succ : Term (.nat ~> .nat)
  | const : {a b : Ty} → Term (a ~> b ~> a)
  | fork : {a b c : Ty} → Term ((a ~> b ~> c) ~> (a ~> b) ~> (a ~> c))
  | iter : {a : Ty} → Term (a ~> (a ~> a) ~> .nat ~> a)
  | app : {a b : Ty} → Term (a ~> b) → Term a → Term b

def iterate {a : Type} (base : a) (step : a → a) : Nat → a
  | 0 => base
  | n + 1 => step (iterate base step n)

def Term.denote : {a : Ty} → Term a → a.denote
  | _, .zero => 0
  | _, .succ => fun n => n + 1
  | _, .const => fun x _ => x
  | _, .fork => fun f g x => f x (g x)
  | _, .iter => fun base step n => iterate base step n
  | _, .app f x => (f.denote) (x.denote)

section Tests

def tm1 := Term.app Term.succ Term.zero
def tm2 := Term.app Term.succ tm1
def tm3 := Term.app Term.succ tm2
def tm5 := Term.app Term.succ (Term.app Term.succ tm3)

example : tm1.denote = 1 := by rfl
example : tm2.denote = 2 := by rfl
example : tm3.denote = 3 := by rfl
example : tm5.denote = 5 := by rfl

def iter8 := Term.app (Term.app (Term.app Term.iter tm5) Term.succ) tm3

example : iter8.denote = 8 := by rfl

end Tests
