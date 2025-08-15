namespace Untyped

inductive Binop where
  | plus : Binop
  | times : Binop

def Binop.denote (b : Binop) : Nat -> Nat -> Nat :=
  match b with
  | .plus => Nat.add
  | .times => Nat.mul

inductive Exp where
  | const : Nat -> Exp
  | binop : Binop -> Exp -> Exp -> Exp

def Exp.denote (e : Exp) : Nat :=
  match e with
  | .const n => n
  | .binop b e1 e2 => b.denote e1.denote e2.denote

example : (Exp.const 42).denote = 42 := by rfl

example : (Exp.binop .plus (.const 2) (.const 2)).denote = 4 := by rfl

example : (Exp.binop .times (.binop .plus (.const 2) (.const 2)) (.const 7)).denote = 28 := by rfl

inductive Instr where
  | const : Nat -> Instr
  | binop : Binop -> Instr

abbrev Stack := List Nat

def Instr.denote (i : Instr) (s : Stack) : Option Stack :=
  match i with
  | .const n => some (n :: s)
  | .binop b =>
    match s with
    | arg1 :: arg2 :: s' => some (b.denote arg1 arg2 :: s')
    | _ => none

abbrev Prog := List Instr

def Prog.denote (p : Prog) (s : Stack) : Option Stack :=
  match p with
  | [] => some s
  | i :: (p' : Prog) =>
    match i.denote s with
    | none => none
    | some s' => p'.denote s'

def Exp.compile (e : Exp) : Prog :=
  match e with
  | .const n => [.const n]
  | .binop b e1 e2 => e2.compile ++ e1.compile ++ [.binop b]

example : (Exp.const 42).compile =
  [.const 42] := by rfl

example : (Exp.binop .plus (.const 2) (.const 2)).compile =
  [.const 2, .const 2, .binop .plus] := by rfl

example : (Exp.binop .times (.binop .plus (.const 2) (.const 2)) (.const 7)).compile =
  [.const 7, .const 2, .const 2, .binop .plus, .binop .times] := by rfl

example : (Exp.const 42).compile.denote [] =
  some [42] := by rfl

example : (Exp.binop .plus (.const 2) (.const 2)).compile.denote [] =
  some [4] := by rfl

example : (Exp.binop .times (.binop .plus (.const 2) (.const 2)) (.const 7)).compile.denote [] =
  some [28] := by rfl

theorem Exp.compile_correct' (e : Exp) (p : Prog) (s : Stack) :
  (e.compile ++ p).denote s = p.denote (e.denote :: s) := by
  induction e generalizing p s with
  | const n =>
    simp [Exp.compile, Prog.denote, Instr.denote, Exp.denote]
  | binop b e1 e2 ih1 ih2 =>
    simp [Exp.compile]
    rw [ih2, ih1]
    simp [Prog.denote, Instr.denote, Exp.denote]

theorem Exp.compile_correct (e : Exp) :
  e.compile.denote [] = some [e.denote] := by
  have h := Exp.compile_correct' e [] []
  rw [List.append_nil] at h
  exact h

end Untyped

namespace Typed

inductive Ty : Type where
  | natural : Ty
  | boolean : Ty
deriving Repr

abbrev Ty.denote (code : Ty) : Type :=
  match code with
  | .natural => Nat
  | .boolean => Bool

inductive Binop : Ty -> Ty -> Ty -> Type where
  | plus : Binop .natural .natural .natural
  | times : Binop .natural .natural .natural
  | eq (t : Ty) : Binop t t .boolean
  | lt : Binop .natural .natural .boolean
deriving Repr

def Binop.denote (b : Binop t u v) : (t.denote -> u.denote -> v.denote) :=
  match b with
  | .plus => Nat.add
  | .times => Nat.mul
  | .eq .natural => (· == ·)
  | .eq .boolean => (· == ·)
  | .lt => (· < ·)

inductive Exp : Ty -> Type where
  | nconst : Nat -> Exp .natural
  | bconst : Bool -> Exp .boolean
  | binop : Binop t u v -> Exp t -> Exp u -> Exp v
deriving Repr

def Exp.denote (e : Exp t) : t.denote :=
  match e with
  | .nconst n => n
  | .bconst b => b
  | .binop b e1 e2 => b.denote e1.denote e2.denote

example : (Exp.nconst 42).denote = 42 := by rfl

example : (Exp.bconst true).denote = true := by rfl

example : (Exp.bconst false).denote = false := by rfl

example : (Exp.binop .times (.binop .plus (.nconst 2) (.nconst 2)) (.nconst 7)).denote = 28 := by rfl

example : (Exp.binop (.eq .natural) (.binop .plus (.nconst 2) (.nconst 2)) (.nconst 7)).denote = false := by rfl

example : (Exp.binop .lt (.binop .plus (.nconst 2) (.nconst 2)) (.nconst 7)).denote = true := by rfl

abbrev Stack := List Ty

inductive Instr : Stack -> Stack -> Type where
  | nconst (n : Nat) : Instr s (.natural :: s)
  | bconst (b : Bool) : Instr s (.boolean :: s)
  | binop (op : Binop t u v) : Instr (t :: u :: s) (v :: s)
deriving Repr

abbrev VStack : Stack -> Type
  | [] => Unit
  | t :: ts => t.denote × VStack ts

def Instr.denote : Instr t u -> VStack t -> VStack u
  | .nconst n => fun s => (n, s)
  | .bconst b => fun s => (b, s)
  | .binop op => fun (x, (y, s)) => (op.denote x y, s)

inductive Prog : Stack -> Stack -> Type where
  | nil : Prog s s
  | cons : Instr t u -> Prog u v -> Prog t v
deriving Repr

def Prog.denote : Prog t u -> VStack t -> VStack u
  | .nil => fun s => s
  | .cons i p => fun s => p.denote (i.denote s)

def Prog.concat : Prog t u → Prog u v → Prog t v
  | .nil => fun p => p
  | .cons i p => fun q => .cons i (concat p q)

def Exp.compile (e : Exp t) (s : Stack) : Prog s (t :: s) :=
  match e with
  | .nconst n => .cons (Instr.nconst n) .nil
  | .bconst b => .cons (Instr.bconst b) .nil
  | .binop b e1 e2 => (e2.compile _).concat ((e1.compile _).concat (.cons (Instr.binop b) .nil))

example : ((Exp.nconst 42).compile []).denote () = (42, ()) := by rfl

example : ((Exp.bconst true).compile []).denote () = (true, ()) := by rfl

example : ((Exp.binop .times (.binop .plus (.nconst 2) (.nconst 2)) (.nconst 7)).compile []).denote () = (28, ()) := by rfl

example : ((Exp.binop (.eq .natural) (.binop .plus (.nconst 2) (.nconst 2)) (.nconst 7)).compile []).denote () = (false, ()) := by rfl

example : ((Exp.binop .lt (.binop .plus (.nconst 2) (.nconst 2)) (.nconst 7)).compile []).denote () = (true, ()) := by rfl

#eval (Exp.binop .lt (.binop .plus (.nconst 2) (.nconst 2)) (.nconst 7)).compile []

theorem Prog.concat_correct (p : Prog a b) (q : Prog b c) (s : VStack a) :
  (p.concat q).denote s = q.denote (p.denote s) := by
  induction p with
  | nil =>
    simp [Prog.concat, Prog.denote]
  | cons i p ih =>
    simp [Prog.concat, Prog.denote]
    rw [ih]

theorem Exp.compile_correct' : forall (e : Exp t) (ts : Stack) (s : VStack ts),
  (e.compile ts).denote s = (e.denote, s) := by
  intro e
  induction e <;> simp_all [
    Exp.compile,
    Prog.denote,
    Instr.denote,
    Exp.denote,
    Prog.concat_correct,
  ]

theorem Exp.compile_correct : forall (e : Exp t),
  (e.compile []).denote () = (e.denote, ()) := by
  simp [Exp.compile_correct']

end Typed
