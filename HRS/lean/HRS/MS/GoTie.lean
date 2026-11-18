import HRS.MS.GoFeatAux2

/-!
# S5.5 ties

`HRS.MS.Go.general_orbits_commutator_proof` has exactly the statement of the frozen
`HRS.Whole.general_orbits_commutator` (Orbits.lean).  `general_orbits_features` and `general_orbits_maximal` are
not tied here: see the docstring of `GoFeatAux2.lean` (status: blocked, the `t`-measurability / junk-value issue of
the `L²_t` component of `gradFeature`, i.e. uniqueness of `propagatorW`).
-/

example := (@HRS.MS.Go.general_orbits_commutator_proof : type_of% @HRS.Whole.general_orbits_commutator)
