# Lean: specifications, implementations and proofs

The cryptographic primitives (e.g. a block function or a field
multiplication) are assembly written in Lean as structured programs over a
Lean model of each ISA, proven correct in Lean, and printed into `src/asm/`
as Rust naked functions. The crate's public APIs are Rust that composes those
primitives: this directory verifies the primitives, not the Rust around them.

## Layout

```
VerifiedGarbage/
  TCB/          Trusted computing base: definitions only, Lean core only
    Mem.lean        byte-addressed memory, regions
    Code.lean       structured programs, big-step semantics with leakage, constant time
    Print.lean      lowering of structured control flow to labels and branches
    Artifact.lean   Target, Contract, `Verified`, `Artifact`: what "verified" means
    Rust.lean       rendering artifacts as Rust naked functions
    Axioms.lean     `#assert_standard_axioms`
    X86_64/         ISA model, printer, System V ABI target
  Spec/         Algorithm specifications and per-target contracts (trusted, must be reviewed)
  Impl/         Implementations: `Prog`s over an ISA model (untrusted)
  Proof/        Proofs and intermediate proof artifacts (untrusted)
    Framework/      generic lemmas: determinism, WP rules, memory frames, and a
                    taint-tracking checker that proves constant time by evaluation
  Artifacts.lean  The registry: the single list of everything that is emitted
VerifiedGarbageTest/  Golden tests for the (unverified) printers
Emit.lean       Renders `VG.artifacts` into `../src/asm/`
```

`ci/check_lean_imports.py` enforces the import discipline between these
directories: `TCB/` imports only Lean core and itself; `Spec/` and `Impl/`
never import proofs.

## The pipeline

1. **Spec** — `Spec/<Alg>.lean` defines the algorithm as a readable Lean
   function transcribed from the standard, and a `Contract` per target: a
   precondition (argument registers, permitted memory regions), a
   postcondition (in terms of the spec), and a `pub` relation saying which
   inputs are public for constant-time purposes.
2. **Impl** — `Impl/<Alg>/<Target>.lean` defines the code as a `Prog`.
3. **Proof** — `Proof/<Alg>/…` proves `Verified target code contract`:
   termination without faults (hence memory safety), the postcondition,
   the ABI obligations (callee-saved registers etc.), constant time, and
   satisfiability of the precondition.
4. **Registry** — `Artifacts.lean` lists every `Artifact`, bundling target,
   Rust name and signature, code, contract and proof. An `Artifact` cannot be
   built without the proof, and `#assert_standard_axioms` rejects `sorry`,
   `native_decide` and any non-standard axiom anywhere in the list.
5. **Emit** — `Emit.lean` renders the registry into `src/asm/<target>/<module>.rs`.
   CI fails if the checked-in files differ from what Lean generates, so the
   Rust crate contains exactly the verified code.

## What you need to trust

* `TCB/` — in particular the ISA models, which must match the vendor manuals,
  and the printers, which must print what the models mean.
* For each artifact: its contract in `Spec/` (and the algorithm spec it
  refers to), and its `rustSig` and `doc` in `Artifacts.lean`.
* Lean's kernel, and the assembler in `rustc`/LLVM.

Everything in `Impl/` and `Proof/` is checked by Lean and need not be read.

To keep review of the trusted parts focused, new specs, additions to the TCB,
and new implementations are never combined in one PR: an implementation is
only proven against a spec and TCB that were reviewed and merged beforehand.

## Building

```sh
lake exe cache get                  # download prebuilt Mathlib
lake build                          # check every proof, run the axiom audit and golden tests
lake env lean --run Emit.lean       # regenerate ../src/asm
lake env lean --run Emit.lean --check
```
