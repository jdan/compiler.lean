## compiler.lean

Inspired by the wonderful [Program Correctness](https://www.youtube.com/watch?v=T_IINWzQhow) video over on [Computerphile](https://www.youtube.com/channel/UC9-y-6csu5WGm29I7JiwpnA), this repo contains a formally verified "compiler" for a language with natural number values and add expressions. It is written using the [Lean theorem prover](https://leanprover-community.github.io/).

We define an expression type for our language and an instruction type for the stack machine which our compiler targets.

```
inductive Expr
| Val : ℕ -> Expr
| Add : Expr -> Expr -> Expr

inductive Instr
| PUSH : ℕ -> Instr
| ADD : Instr
```

### `exec_compile_eq_eval (e : Expr) : exec (compile e) [] = [eval e]`

[[Source]](/src/compiler.lean)

All expressions `e` when compiled and executed on an empty stack produce the same value as `eval`.

I'm still new to lean so my proofs aren't great. Suggestions welcome!

### `eval : Expr -> ℕ`

Evaluates an `Expr` to produce a natural number

```
eval (Val 5)
=> 5
eval (Add (Add (Val 10) (Val 20))
          (Val 30))
=> 60
```

### `compile : Expr -> list Instr`

Compiles an `Expr` to produce a list of instructions

```
compile (Val 42)
=> [PUSH 42]
compile (Add (Add (Val 10) (Val 20))
             (Val 30))
=> [PUSH 10, PUSH 20, ADD, PUSH 30, ADD]
```

### `exec : list Instr -> list ℕ -> list ℕ`

Executes a list of instructions on a stack

```
exec [PUSH 42] []
=> [42]
exec [PUSH 10, PUSH 20, ADD, PUSH 30, ADD][]
=> [60]
```
