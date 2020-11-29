import tactic

namespace compiler

/- expressions are values and add-expressions -/
inductive expr
| val : ℕ -> expr
| add : expr -> expr -> expr

/-- evaluate an expression directly -/
@[simp] def eval : expr -> ℕ
| (expr.val n) := n
| (expr.add a b) := eval a + eval b

/-
  we'll compile our expressions to instructions of a stack machine
  which supports push and add operations
-/
inductive instr
| push : ℕ -> instr
| add : instr

/-- execute a list of instructions on a stack -/
@[simp] def exec : list instr -> list ℕ -> list ℕ
| ((instr.push n) :: rest) s :=
  exec rest (n :: s)
| (instr.add :: rest) (a :: b :: s) :=
  exec rest ((a + b) :: s)
| _ s := s

/-- compile an expression to an instruction list -/
@[simp] def compile : expr -> list instr
| (expr.val n) := [instr.push n]
| (expr.add a b) := compile a ++ compile b ++ [instr.add]

/-- compiled expressions only add to the stack when `exec`d -/
@[simp] lemma exec_compile_concat (e : expr) : ∀ instrs stack,
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
theorem eval_eq_exec_compile (e : expr) : exec (compile e) [] = [eval e] :=
by simpa using exec_compile_concat e [] []

end compiler
