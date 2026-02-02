# Moonwalk Verified

Formalization of a moonwalk (backslide) step and a simple validator extracted to OCaml.

## Build

PowerShell:

```
.\build.ps1
```

This compiles `Moonwalk.v` and regenerates `moonwalk_validator.ml`.

## Validator

The extracted validator exposes:

- `validate_sequence` for the default continuity bound.
- `validate_sequence_bounded` for a custom bound.
- `validate_sequence_footpos` for per-foot continuity.
- `validate_sequence_footpos_bounded` for per-foot continuity with a custom bound.

Default continuity bound is 10 (see `continuity_bound`).
Default per-foot bound is 10 (see `footpos_bound`).

## Demo (optional)

If you have OCaml available:

```
ocamlc -o moonwalk_demo moonwalk_validator.ml moonwalk_harness.ml
.\moonwalk_demo.exe
```

## Bound Sensitivity Test (optional)

```
ocamlc -o moonwalk_bounds_test moonwalk_validator.ml moonwalk_bounds_test.ml
.\moonwalk_bounds_test.exe
```
