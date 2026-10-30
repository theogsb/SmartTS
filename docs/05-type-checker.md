# 5 — The Type Checker

The type checker is the second stage of the pipeline.
It reads the `Contract` AST produced by the parser and either reports the first type error it finds, or returns the same contract with the type of every expression filled in.
It covers base types, records, variants (with `match`) and lists (with comprehensions).

---

## Three Errors the Type Checker Catches

Before diving into how it works, here are three concrete examples of what the
type checker prevents.

### Error 1: Return type mismatch

```typescript
contract C {
  storage: { x: int };

  @originate
  init(): int {
    return true;  // int expected, bool given
  }
}
```

Error: `return value has wrong type: expected int, inferred bool.`

### Error 2: Arithmetic on a non-integer

```typescript
contract C {
  storage: { x: int };

  @originate
  init(): int {
    return 1 + true;  // both operands must be int
  }
}
```

Error: `right operand of arithmetic operator has wrong type: expected int, inferred bool.`

### Error 3: Assignment to an immutable val

```typescript
contract C {
  storage: { x: int };

  @originate
  init(): int {
    val v: int = 1;
    v = 2;  // val cannot be reassigned
    return 0;
  }
}
```

Error: ``Cannot assign to immutable val `v` (or through it for field updates).``

---

## How the Type Checker Works

The entry point is:

```haskell
typeCheckContract :: ParsedContract -> Either String TypedContract
```

It takes the contract exactly as the parser produced it, with no annotations (`Expr ()`).
On success it returns the same contract with every expression annotated with its type (`Expr Type`).
On failure it returns the first error as a message.

It runs these checks in order:

1. **Duplicate storage fields**: no two fields in `storage: { … }` may share a name.
2. **Well-formed storage types**: no record repeats a field and no variant repeats a tag, at any depth (see [Well-Formed Types](#well-formed-types)).
3. **Duplicate parameters**: within each method, no two formal parameters may share a name.
4. **Well-formed signatures**: the same check on every parameter type and on the return type of each method.
5. **Method bodies**: every method is checked independently with `checkMethod`.

### Tracking names with `TcEnv`

To know the type of a variable at any point in a method body, the type checker
keeps an environment:

```haskell
data TcEnv = TcEnv
  { envStorageType        :: Type               -- the contract's full storage record type
  , envBindings           :: Map Name TcBinding
  , envFunctionSignatures :: Map Name Signature -- callable @private methods
  , envReturnType         :: Type               -- the method's declared return type
  }
```

`envFunctionSignatures` is built once per method check from all `@private`
methods in the contract (`buildSigMap`), so every method — `@originate`,
`@entrypoint`, or `@private` — can call any private helper.

Each binding records whether the name is a parameter, a mutable local (`var`),
or an immutable local (`val`):

```haskell
data BindingKind = Param | LocalMutable | LocalImmutable
```

### The checking monad

Rather than threading `TcEnv` manually through every function, the type checker
uses a monad:

```haskell
type TcM = StateT TcEnv (Either String)
```

`checkStmt`, `checkExpr` and `inferExpr` all run in `TcM`. Reading the environment uses
`gets`; adding a new local uses `modify`. Errors short-circuit via `lift .
Left`. The entry function `checkMethod` runs a `TcM` action with
`runStateT` and discards the final environment.

The environment for a method starts with all parameters bound as `Param`. As
the checker walks the statement sequence, `var` and `val` declarations extend
the map via `modify`, so declarations in earlier statements are visible to
later ones in the same sequence.

---

## Well-Formed Types

A type written by the programmer can itself be wrong.
`variant { A | A }` repeats a tag, and `{ x: int, x: bool }` repeats a field.
A type is **well formed** when no record repeats a field name and no variant repeats a tag, at any depth.
The check goes inside variant payloads, record fields and list elements, so an error deep inside a type is found.
The same tag or field name at different levels is fine: `variant { A(variant { A | B }) | B }` is well formed.

The check runs on every type the programmer writes: storage fields, parameters, return types, and the types of `val` and `var`.
The message says where the type was written:

```
Storage field `estado` has an ill-formed type: duplicate tag `Aberto` in variant { Aberto | Fechado | Aberto }.
Parameter `p` has an ill-formed type: duplicate tag `A` in variant { A | A }.
Return type of method `f` has an ill-formed type: duplicate tag `A` in variant { A | A }.
Local `y` has an ill-formed type: duplicate tag `A` in variant { A | A }.
```

For a `val` or `var`, the type is validated before the initializer is looked at, so the reported error is the one in the type and not a consequence of it.
A top-level storage field repeated by name is still reported by the earlier duplicate-field check, with its own message.

---

## Scoping Rules

### Statement sequences

`checkStmt` for `SequenceStmt` uses `foldM`, threading the environment from
left to right:

```
stmt1 → extended env → stmt2 → extended env → stmt3 → …
```

A `var x` or `val x` declaration in `stmt1` is visible in `stmt2` and beyond.

### Branches do not export locals

`if` and `while` branches are checked inside `withSavedEnv`, which saves the
current `TcEnv` before entering the branch and restores it afterwards. Any
`var` or `val` declared inside a branch does not escape:

```typescript
if (flag) {
  var inner: int = 10;  // inner is visible only inside this branch
}
// inner is NOT in scope here
```

### Shadowing parameters

Declaring `var x` or `val x` is rejected if `x` is already a **local** in
the current environment. But if `x` is only a **parameter**, the declaration
is allowed and the new local **shadows** the parameter for subsequent
statements. This mirrors the runtime lookup order: locals are checked before
parameters.

---

### Names bound by `match`

A case such as `Ok(v) => body` binds `v` to the payload of the tag.
The name is an immutable local with the payload type, and it is visible only inside the body of that case.
Each case is checked inside `withSavedEnv`, so neither the bound name nor any local declared in the body is visible after the case.
Two cases may bind the same name, even with different types.

The binding follows the same rules as `val`: a name that is already a local is rejected, and a name that is only a parameter is shadowed.

### Names bound by `for`

Each generator `for x in xs` binds `x` as an immutable local with the element type of `xs`.
The name is visible to the clauses after it and to the element expression, and it disappears when the comprehension ends.
The same rule as `val` applies: repeating the name of a local is an error, and that includes the name of an earlier generator in the same comprehension.
Clauses are read from left to right, so in `[x for x in xs if y > 0 for y in ys]` the guard sees `x` but not `y`.

---

## Inferring and Checking

Expressions are typed in two modes.
They differ in what the checker knows before it looks at the expression.

**Inference** (`inferExpr`) works from the bottom up.
It looks at an expression and discovers its type: `1 + 2` is `int` because both operands are `int`.
In the usual notation this is `Γ ⊢ e ⇒ T`: in environment Γ, `e` produces type `T`.

**Checking** (`checkExpr`) works from the top down.
It receives the type the context expects and verifies that the expression fits it: `Γ ⊢ e ⇐ T`.
Its first argument describes where the expression appears, and it starts the error message.

```haskell
inferExpr :: Expr () -> TcM (Expr Type)
checkExpr :: String -> Expr () -> Type -> TcM (Expr Type)
```

Both return the expression annotated with its type.
Inference reads the environment with `gets`.
It modifies it only for a comprehension, which adds the names of its generators and restores the environment before returning.
Statements are the other place where the environment grows, in `checkStmt`.

### Why two modes

Variants are structural: there is no declared type called `Option`.
So `#Some(1)` fits `variant { Some(int) | None }`, `variant { Some(int) | Err(bool) }` and many other types, and looking only at the expression gives no single answer.
The same is true of `[]`: an empty list of what?
The type has to come from an annotation, and checking is how it travels from the annotation to the expression.

```typescript
val o: variant { Some(int) | None } = #Some(1);
//     └── expected type goes down to #Some(1) ──┘
```

`checkExpr` has a case of its own for each form that inference cannot type:

| Expression | Checked against | What happens |
|------------|-----------------|--------------|
| `#tag(e)` | `variant { … tag(P) … }` | `e` is checked against `P`. The tag must be one of the alternatives. |
| `[e₁, …, eₙ]` and `[]` | `list<T>` | Each element is checked against `T`. The empty list passes, because there is nothing to check. |
| `[body for …]` | `list<T>` | The clauses are checked from left to right, then `body` is checked against `T`. |
| `{ k₁: e₁, … }` | `{ k₁: T₁, … }` | Each `eᵢ` is checked against `Tᵢ`, so an expected type reaches the constructors inside. If the field names differ, the error is about the record. |
| anything else | any type | Infer the type, then compare it with the expected one. |

The last row is why the two modes can coexist.
For every expression that existed before variants and lists, checking is the old behavior: infer, then compare.

When an expression of those forms has no expected type, inference refuses it and says how to fix it:

```
Cannot infer the type of `#Some`; annotate it (for example, with the type of a `val`).
Cannot infer the element type of `[]`; annotate it (for example, with the type of a `val`).
```

### Where each mode is used

| Position | What the checker does |
|----------|-----------------------|
| `val x: T = e`, `var x: T = e` | `checkExpr e` against `T` |
| `return e` | `checkExpr e` against the return type of the method |
| `lv = e` | `checkExpr e` against the type of `lv` |
| argument `eᵢ` of `f(…)` | `checkExpr eᵢ` against parameter `i`, from left to right |
| `a == b`, `a != b` | see [Equality and Comparable Types](#equality-and-comparable-types) |
| guard of a comprehension | `checkExpr` against `bool` |
| source of a generator, `match` scrutinee | inference: it must turn out to be a list, or a variant |
| conditions, `!`, arithmetic | inference, then compare: the expected type is a fixed base type |

---

## Expression Typing Rules

The summary below describes the type each expression gets.

Summary of the rules:

| Expression | Type |
|------------|------|
| Integer literal | `int` |
| `true` / `false` | `bool` |
| `()` | `unit` |
| `storage` | the contract's storage record type |
| `x` (variable) | the type bound to `x` in the environment |
| `e.f` | the type of field `f` in the record type of `e` |
| `{ k1: e1, … }` | `{ k1: T1, … }` where each `Ti` is inferred from `ei` |
| `f(e1, …, en)` | the `returnType` of the signature for `f` (arity and argument types must match) |
| `!e` | `bool` (requires `e : bool`) |
| `e1 && e2`, `e1 \|\| e2` | `bool` (requires both operands `bool`) |
| `+`, `-`, `*`, `/`, `%` | `int` (requires both operands `int`) |
| `<`, `<=`, `>`, `>=` | `bool` (requires both operands `int`) |
| `==`, `!=` | `bool` (requires both operands to have the **same**, **comparable** type) |
| `#tag(e)` | no type of its own: only in checking mode, against a variant type |
| `[e₁, …, eₙ]` | `list<T>`, where `T` is the type of `e₁` and every other element is checked against `T` |
| `[]` | no type of its own: only in checking mode, against a list type |
| `[body for …]` | `list<E>`, where `E` is the type of `body`, with the names bound by the generators in scope |

### Type equality

Two types are equal if and only if:

- They are the same primitive (`int`, `bool`, or `unit`), **or**
- They are both records, or both variants, of the same length, and at each position `i` the names are equal and the types are recursively equal, **or**
- They are both lists and their element types are equal.

The **order** of fields, and of variant tags, is part of the type.
`variant { A | B }` and `variant { B | A }` are different types, which matches how Michelson encodes a variant as nested `or`.
A tag without payload has payload type `unit`, so `Err` and `Err(unit)` are the same alternative.

There is no width subtyping, no row polymorphism, and no implicit coercion.

---

## Statement Checking Rules

| Statement | Rule |
|-----------|------|
| `return e` | Check `e` against `envReturnType`. |
| `var x: T = e` | No duplicate local `x`; `T` must be well formed; check `e` against `T`; add `LocalMutable` binding. |
| `val x: T = e` | Same as `var`, but binding is `LocalImmutable`. |
| `lv = e` | Check `lv` is assignable; compute type of `lv`; check `e` against it. |
| `if (cond) then [else]` | Cond must be `bool`; check each branch with outer env; env unchanged after. |
| `while (cond) body` | Cond must be `bool`; check body with outer env; env unchanged after. |
| `match (s) { cases }` | `s` must be a variant; each case is checked in its own scope; the cases must cover every tag or include `_`. See [Checking a `match`](#checking-a-match). |

### Assignability

Before type-checking an assignment's right-hand side, the checker verifies
the left-hand side is writable:

- `LStorage` or any `LField` rooted at `LStorage` — always assignable.
- `LVar x` or `LField (LVar x) …` — `x` must be a `LocalMutable` binding.
  Parameters (`Param`) and immutable locals (`LocalImmutable`) are rejected.

### Checking a `match`

```typescript
match (r) {
  Ok(v)  => { storage.total = v; }
  Err    => { return (); }
  _      => { return (); }
}
```

The checker infers the scrutinee `r`, which must be a variant, and then goes through the cases from top to bottom.
Each case runs in its own scope, as described in [Names bound by `match`](#names-bound-by-match).
After the last case, if there is no `_`, the tags the cases did not handle must be empty: the match must be **exhaustive**.

| Situation | Message starts with |
|-----------|---------------------|
| scrutinee is not a variant | ``match scrutinee must be a variant, but it has type int`` |
| no cases | ``match has no cases`` |
| tag not in the variant | ``Tag `Nope` is not part of variant { … }`` |
| tag handled twice | ``Tag `Err` is handled more than once in this match`` |
| a case after `_`, including a second `_` | ``Case `Err` comes after `_` and can never run`` |
| a name on a tag without payload | ``Tag `Err` has no payload, so it cannot bind a name`` |
| tags missing and no `_` | ``match is not exhaustive: missing `Err`, `Pending`; add those cases or a `_` case`` |

A `_` that covers nothing the earlier cases missed is allowed, as defensive style.
A case written after `_` is always an error, because it can never run.
A name on a tag without payload would always have type `unit`, which almost always means a mistake.

---

## Equality and Comparable Types

`a == b` and `a != b` require both operands to have the same type, and that type must be comparable.
The rule follows Michelson, where `COMPARE` accepts only comparable types.

| Type | Comparable |
|------|------------|
| `int`, `bool`, `unit` | yes |
| record | if every field type is |
| variant | if every payload type is |
| `list<T>` | never |

A type that contains a list is not comparable either, so `r == r` is rejected when `r` is a record with a list field.
The message names the type of the operands.
For `xs == ys` with two `list<int>` it is ``Cannot compare values of type list<int>: it is or contains a list, and lists are not comparable.``
For a record `r: { n: int, xs: list<int> }` it names the whole record: ``Cannot compare values of type {n: int, xs: list<int>}: it is or contains a list, and lists are not comparable.``
When the two operands have different types, the older message is kept: ``Equality requires operands of the same type (got int and bool).``

An operand such as `#Some(1)` or `[]` has no type of its own, so the other operand provides it.
When exactly one operand needs an expected type, the checker infers the other operand and checks the first against that type.
That works in either order: `x == #A` and `#A == x` are both accepted.
The checker decides by the form of the expression and not by catching errors, so a real error in an operand is never hidden by the attempt.
When both operands need one, as in `#A == #B`, there is nothing to take the type from, and the checker reports that.

---

## What the Type Checker Does Not Verify

- **Termination** — a method may fall off the end without a `return`. That is
  not checked; it will produce a `Nothing` return value at runtime.
- **Division by zero** — still a runtime error.
- **Exactly one `@originate`** — the parser and interpreter enforce this; the
  type checker checks each method independently without cross-method analysis.
- **Polymorphism, type inference** — the language is fully annotated by
  design; the checker infers expression types but all declarations carry
  explicit annotations.
- **Run-time support for variants and lists.** The interpreter and the LLTZ code generator do not handle `#tag(e)`, `match`, list literals or comprehensions yet.
  A contract that type checks can still fail when it is run.
  For example, a list literal reaches the interpreter's explicit "list literal reached the interpreter" error, and a variant argument passed with `--call` is rejected by the JSON decoder.

---

## Key Design Decision: First Error Only

The type checker stops and reports the first error it encounters. It does not
collect multiple errors and report them all at once. This is appropriate for
a language where contracts are short and errors are typically fixed one at a
time.
Within one construct the errors are found from left to right.
For a call `g(true, unknown)`, the first argument is reported, and not the unknown name.
The exception is `==` and `!=` when one operand has no type of its own, such as `#A(nope) == other`.
The other operand is inferred first because it provides the type, so an error in it is reported before an error in the operand on the left.

---

**What to read next →** [06-interpreter.md](06-interpreter.md)
