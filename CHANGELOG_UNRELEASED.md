# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `bigcup_distrl`
  + definition `trivIset`
  + lemmas `trivIset_bigUI`, `trivIset_setI`
- in `ereal.v`:
  + definition `mule` and its notation `*` (scope `ereal_scope`)
  + definition `abse` and its notation `` `| | `` (scope `ereal_scope`)

  + lemmas `setIIl`, `setIIr`, `setCS`, `setSD`, `setDS`, `setDSS`, `setCI`,
    `setDUr`, `setDUl`, `setIDA`, `setDD`
- in `normedtype.v`:
  + lemma `closed_ereal_le_ereal`
  + lemma `closed_ereal_ge_ereal`
  + section "LinearContinuousBounded"
  + section "Closed_ball"
  
### Changed

### Renamed

- in `classical_sets.v`:
  + `subset_empty` -> `subset_nonempty`

### Removed

### Infrastructure

### Misc
