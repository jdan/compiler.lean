import tactic

namespace compiler

/- expressions are values and add-expressions -/
inductive Expr
| Val : ℕ -> Expr
| Add : Expr -> Expr -> Expr
open Expr

/-- evaluate an expression directly -/
@[simp] def eval : Expr -> ℕ
| (Val n) := n
| (Add a b) := eval a + eval b

/-
  we'll compile our expressions to instructions of a stack machine
  which supports push and add operations
-/
inductive Instr
| PUSH : ℕ -> Instr
| ADD : Instr
open Instr

/-- execute a list of instructions on a stack -/
@[simp] def exec : list Instr -> list ℕ -> list ℕ
| ((PUSH n) :: rest) s := exec rest (n :: s)
| (ADD :: rest) (a :: b :: s) := exec rest ((a + b) :: s)
| _ s := s

/-- compile an expression to an instruction list -/
@[simp] def compile : Expr -> list Instr
| (Val n) := [PUSH n]
| (Add a b) := compile a ++ compile b ++ [ADD]

/-- compiled expressions only add to the stack when `exec`d -/
@[simp] lemma exec_compile_concat (e : Expr) : ∀ instrs stack,
  exec (compile e ++ instrs) stack = exec instrs (eval e :: stack) :=
begin
  induction e with n a b iha ihb,
  { intros,
    simp,
  },
  { intros,
    simp [iha, ihb, add_comm],
  }
end

/-- exec (compile e) = eval e -/
theorem eval_eq_exec_compile (e : Expr) : exec (compile e) [] = [eval e] :=
by simpa using exec_compile_concat e [] []

end compiler
