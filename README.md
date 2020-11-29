## compiler.lean

Inspired by the wonderful [Program Correctness](https://www.youtube.com/watch?v=T_IINWzQhow) video over on [Computerphile](https://www.youtube.com/channel/UC9-y-6csu5WGm29I7JiwpnA), this repo contains a formally verified "compiler" for a language with natural number values and add expressions. It is written using the [Lean theorem prover](https://leanprover-community.github.io/).

We define an expression type for our language and an instruction type for the stack machine which our compiler targets.

```
inductive expr
| val : ℕ -> expr
| add : expr -> expr -> expr

inductive instr
| push : ℕ -> instr
| add : instr
```

### `theorem eval_eq_exec_compile : ∀ e, exec (compile e) [] = [eval e]`

[[Source]](/src/compiler.lean)

All expressions `e` when compiled and executed on an empty stack produce the same value as `eval`.

I'm still new to lean so my proofs aren't great. Suggestions welcome!

### `eval : expr -> ℕ`

Evaluates an `expr` to produce a natural number

```
eval (expr.val 5)
=> 5
eval (expr.add (expr.add (expr.val 10) (expr.val 20))
               (expr.val 30))
=> 60
```

### `compile : expr -> list instr`

Compiles an `expr` to produce a list of instructions

```
compile (expr.val 42)
=> [instr.push 42]
compile (expr.add (expr.add (expr.val 10) (expr.val 20))
                  (expr.val 30))
=> [instr.push 10, instr.push 20, instr.add, instr.push 30, instr.add]
```

### `exec : list instr -> list ℕ -> list ℕ`

Executes a list of instructions on a stack

```
exec [instr.push 42] []
=> [42]
exec [instr.push 10, instr.push 20, instr.add, instr.push 30, instr.add] []
=> [60]
```
