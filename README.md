# Moonwalk Verified

Formalization of a moonwalk (backslide) step and a simple validator extracted to OCaml.

## Build

PowerShell:

```
.\build.ps1
```

This compiles `Moonwalk.v` and regenerates `moonwalk_validator.ml`.

## Units and Calibration

- Distances are in millimeters (mm).
- Time is in milliseconds (ms).
- Friction coefficient `mu` is scaled by 1000 (e.g., 0.30 -> 300).

Calibration is explicit via `default_calibration` (thresholds and bounds for
friction, step size, heel lift, timing, speeds, continuity, and illusion range).

## Validator

The extracted validator exposes:

- `validate_sequence` (default calibration + default continuity bound).
- `validate_sequence_bounded` (custom calibration + custom bound).
- `validate_sequence_bounded_default` (default calibration + custom bound).
- `validate_sequence_footpos` (default calibration + default footpos bound).
- `validate_sequence_footpos_bounded` (custom calibration + custom bound).
- `validate_sequence_footpos_bounded_default` (default calibration + custom bound).

Default bounds come from `default_calibration`:
`continuity_bound`, `continuity_dt_bound`, and `footpos_bound`.

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
