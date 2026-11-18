import HRS.MH.CondOuSpec

/-!
# `HRS.MH.CondOu.conditioned_ou_prob`: proof (packet (a))

Route: generalise `HRS.StaticLimitsAux.prob_cos` from `k = e_j` to an arbitrary nonzero lattice vector `k`.
The shift by `t = mk(e_j / (2 k_j))` (any `j` with `k_j ≠ 0`) flips the sign of `cos(2π k·x)`; the sum-level set
`{Σ_i cos(2π k·x_i) = 0}` is null by Fubini, using that every level set `{cos(2π k·x) = c}` is Haar-null
(Fubini in the coordinate `j`, then the one-dimensional fact that `t ↦ e^{2πi n t} w` has `Re = c` on a null set).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.CondOuP

open HRS HRS.Main HRS.StaticLimitsAux

/-- Finitely many unit complex numbers `z` with `(z w).re = c`, for a unit `w`. -/
theorem unit_re_set_finite (c : ℝ) (w : ℂ) (hw : ‖w‖ = 1) :
    {z : ℂ | (z * w).re = c ∧ ‖z‖ = 1}.Finite := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  have hB : {v : ℂ | v.re = c ∧ ‖v‖ = 1}.Finite := by
    refine (Set.toFinite {(⟨c, Real.sqrt (1 - c^2)⟩ : ℂ), ⟨c, -Real.sqrt (1 - c^2)⟩}).subset ?_
    rintro v ⟨h1, h2⟩
    have h3 : v.im ^ 2 = 1 - c ^ 2 := by
      have := Complex.sq_norm v
      rw [h2, Complex.normSq_apply, h1] at this
      nlinarith
    have h4 : 0 ≤ 1 - c ^ 2 := by rw [← h3]; positivity
    have h5 : v.im = Real.sqrt (1 - c^2) ∨ v.im = -Real.sqrt (1 - c^2) := by
      have : v.im ^ 2 = (Real.sqrt (1 - c^2)) ^ 2 := by rw [Real.sq_sqrt h4, h3]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    rcases h5 with h | h
    · left; exact Complex.ext h1 h
    · right; exact Complex.ext h1 h
  refine (hB.image (fun v : ℂ => v * w⁻¹)).subset ?_
  rintro z ⟨h1, h2⟩
  refine ⟨z * w, ⟨h1, ?_⟩, mul_inv_cancel_right₀ hw0 z⟩
  rw [norm_mul, h2, hw, mul_one]

/-- Level sets of `t ↦ Re(e_1(t) w)` are null on the circle, for a unit `w`. -/
theorem circle_mul_re_null (w : ℂ) (hw : ‖w‖ = 1) (c : ℝ) :
    (volume : Measure UnitAddCircle) {u : UnitAddCircle | (fourier (1:ℤ) u * w).re = c} = 0 := by
  apply circle_finite_null
  have hinj : Function.Injective (fun t : UnitAddCircle => fourier (1:ℤ) t) := by
    intro a b h
    simp only [fourier_one] at h
    exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext h)
  refine ((unit_re_set_finite c w hw).preimage hinj.injOn).subset fun u hu => ⟨hu, ?_⟩
  exact Circle.norm_coe _

/-- The same for `t ↦ Re(e_n(t) w)`, `n ≠ 0`, by the measure-preserving map `t ↦ n • t`. -/
theorem circle_mul_re_null_zsmul (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : ‖w‖ = 1) (c : ℝ) :
    (volume : Measure UnitAddCircle) {t : UnitAddCircle | (fourier n t * w).re = c} = 0 := by
  have hset : {t : UnitAddCircle | (fourier n t * w).re = c} =
      (fun t : UnitAddCircle => n • t) ⁻¹' {u : UnitAddCircle | (fourier (1:ℤ) u * w).re = c} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [fourier_apply, fourier_apply, one_smul]
  have hs : MeasurableSet {u : UnitAddCircle | (fourier (1:ℤ) u * w).re = c} :=
    (isClosed_eq (Complex.continuous_re.comp ((fourier (1:ℤ)).continuous.mul continuous_const))
      continuous_const).measurableSet
  have hpm := MeasureTheory.Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) hn
  have hmp := hpm.measure_preimage hs.nullMeasurableSet
  rw [hset, hmp]
  exact circle_mul_re_null w hw c

/-- Every level set of `cos(2π k·x)` on the torus is Haar-null, for `k ≠ 0`. -/
theorem torus_cos_level_null (m : ℕ) (k : Lattice (m+1)) (hk : k ≠ 0) (c : ℝ) :
    (volume : Measure (Torus (m+1))) {x | Torus.cosMode k x = c} = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext h)
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => (volume : Measure UnitAddCircle)) j
  set W : (Fin m → UnitAddCircle) → ℂ :=
    fun y => ∏ i : Fin m, fourier (k (j.succAbove i)) (y i) with hW
  set S : Set (UnitAddCircle × (Fin m → UnitAddCircle)) :=
    {p | (fourier (k j) p.1 * W p.2).re = c} with hS
  have hmeas : MeasurableSet S := by
    have hc : Continuous (fun p : UnitAddCircle × (Fin m → UnitAddCircle) =>
        (fourier (k j) p.1 * W p.2).re) := by
      rw [hW]
      fun_prop
    exact (isClosed_eq hc continuous_const).measurableSet
  have hpre : {x : Torus (m+1) | Torus.cosMode k x = c} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => UnitAddCircle) j) ⁻¹' S := by
    ext x
    have hmode : Torus.mode k x = fourier (k j) (x j) *
        ∏ i : Fin m, fourier (k (j.succAbove i)) (x (j.succAbove i)) := by
      simp only [Torus.mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
      exact Fin.prod_univ_succAbove (fun i => fourier (k i) (x i)) j
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS, hW, MeasurableEquiv.piFinSuccAbove_apply,
      Torus.cosMode, hmode]
    exact Iff.rfl
  have hfib : ∀ y : Fin m → UnitAddCircle,
      (volume : Measure UnitAddCircle) ((fun a => (a, y)) ⁻¹' S) = 0 := by
    intro y
    have hw : ‖W y‖ = 1 := by
      rw [hW]
      simp only
      rw [norm_prod]
      exact Finset.prod_eq_one fun i _ => Circle.norm_coe _
    have e1 : (fun a => (a, y)) ⁻¹' S = {a : UnitAddCircle | (fourier (k j) a * W y).re = c} := rfl
    rw [e1]
    exact circle_mul_re_null_zsmul (k j) hj (W y) hw c
  rw [hpre]
  show (Measure.pi fun _ : Fin (m+1) => (volume : Measure UnitAddCircle)) _ = 0
  rw [mp.measure_preimage_equiv, Measure.prod_apply_symm hmeas]
  simp [hfib]

/-- The sum-level set `{Σ_i cos(2π k·x_i) = 0}` is null in `N = n+1` particles. -/
theorem null_cos_sum_gen (n : ℕ) {m : ℕ} (k : Lattice (m+1)) (hk : k ≠ 0) :
    (volume : Measure (Config (m+1) (n+1)))
      {X | ∑ i, Torus.cosMode k (X i) = 0} = 0 := by
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure (Torus (m+1)))) 0
  set S' : Set (Torus (m+1) × (Fin n → Torus (m+1))) :=
    {p | Torus.cosMode k p.1 + ∑ i, Torus.cosMode k (p.2 i) = 0} with hS'
  have hmeas : MeasurableSet S' := by
    have hc : Continuous (Torus.cosMode k) := Complex.continuous_re.comp (Torus.continuous_mode _)
    refine measurableSet_eq_fun ?_ measurable_const
    exact (hc.measurable.comp measurable_fst).add
      (Finset.measurable_sum _ fun i _ => hc.measurable.comp ((measurable_pi_apply i).comp measurable_snd))
  have hpre : {X : Config (m+1) (n+1) | ∑ i, Torus.cosMode k (X i) = 0}
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Torus (m+1)) 0) ⁻¹' S' := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS', MeasurableEquiv.piFinSuccAbove_apply,
      Fin.sum_univ_succ]
    rfl
  rw [hpre]
  show (Measure.pi fun _ : Fin (n+1) => (volume : Measure (Torus (m+1)))) _ = 0
  rw [mp.measure_preimage_equiv, Measure.prod_apply_symm hmeas]
  have hfib : ∀ y : Fin n → Torus (m+1),
      (volume : Measure (Torus (m+1))) ((fun x => (x, y)) ⁻¹' S') = 0 := by
    intro y
    set c := ∑ i, Torus.cosMode k (y i) with hc
    have e1 : (fun x => (x, y)) ⁻¹' S' = {x : Torus (m+1) | Torus.cosMode k x = -c} := by
      ext x
      simp only [hS', Set.mem_preimage, Set.mem_setOf_eq]
      constructor <;> intro h <;> linarith
    rw [e1]
    exact torus_cos_level_null m k hk (-c)
  simp [hfib]

/-- A nonzero lattice vector has a coordinate `j` with `k j ≠ 0`. -/
theorem exists_coord_ne_zero {d : ℕ} (k : Lattice d) (hk : k ≠ 0) : ∃ j, k j ≠ 0 := by
  by_contra h
  push_neg at h
  exact hk (funext h)

/-- The shift `t = mk(e_j / (2 k_j))` flips the sign of `cos(2π k·x)`. -/
theorem cos_shift {d : ℕ} (k : Lattice d) (j : Fin d) (hj : k j ≠ 0) (x : Torus d) :
    Torus.cosMode k (Torus.mk (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) + x) =
      - Torus.cosMode k x := by
  have hj' : (k j : ℝ) ≠ 0 := by exact_mod_cast hj
  conv_lhs => rw [← Torus.mk_rep x, ← Torus.mk_add, Torus.cosMode_mk]
  conv_rhs => rw [← Torus.mk_rep x, Torus.cosMode_mk]
  rw [Torus.dot_add]
  have : Lattice.dot k (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) = 1/2 := by
    simp only [Lattice.dot, EuclideanSpace.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    field_simp
  rw [this, mul_add, show 2 * Real.pi * (1/2 : ℝ) = Real.pi by ring, add_comm Real.pi,
    Real.cos_add_pi]

/-- `∫ cos(2π k·x) dx = 0` for `k ≠ 0`. -/
theorem integral_cos_mode_zero {d : ℕ} (k : Lattice d) (hk : k ≠ 0) :
    ∫ x : Torus d, Torus.cosMode k x = 0 := by
  obtain ⟨j, hj⟩ := exists_coord_ne_zero k hk
  have h1 : ∫ x : Torus d, Torus.cosMode k
      (Torus.mk (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) + x) =
      ∫ x : Torus d, Torus.cosMode k x :=
    integral_add_left_eq_self (μ := (volume : Measure (Torus d))) _ _
  simp only [cos_shift k j hj, integral_neg] at h1
  linarith

theorem conditioned_ou_prob_proof : type_of% @HRS.MH.CondOu.conditioned_ou_prob := by
  intro d hd s hs0 hsd β hβ k hk N hN
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  haveI := gibbs_prob (N := n+1) hd hs0 hsd 0 β hβ.le
  set P := canonicalGibbs (periodicRiesz (m+1) s) (fun _ => (0:ℝ)) (n+1) β with hP
  obtain ⟨j, hj⟩ := exists_coord_ne_zero k hk
  set t : Torus (m+1) := Torus.mk (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) with ht
  have hNpos : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  set Z : Config (m+1) (n+1) → ℝ := fun X => Real.sqrt ((n+1 : ℕ) : ℝ) * ((1 / ((n+1 : ℕ) : ℝ)) *
        ∑ i, Real.sqrt 2 * Torus.cosMode k (X i)) with hZ
  have hc : Continuous (Torus.cosMode k) := Complex.continuous_re.comp (Torus.continuous_mode _)
  have hZm : Measurable Z := by
    refine measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_))
    exact measurable_const.mul (hc.measurable.comp (measurable_pi_apply i))
  have hneg : ∀ X, Z (shiftEquiv t X) = -Z X := by
    intro X
    simp only [hZ, shiftEquiv_apply, ht, cos_shift k j hj, mul_neg, Finset.sum_neg_distrib]
  have hnull : P {X | Z X = 0} = 0 := by
    refine gibbs_ac _ _ _ ?_
    refine measure_mono_null ?_ (null_cos_sum_gen n k hk)
    intro X hX
    simp only [Set.mem_setOf_eq, hZ] at hX ⊢
    have h1 : Real.sqrt ((n+1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNpos).ne'
    have h2 : (1 / ((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
    rcases mul_eq_zero.1 hX with h | h
    · exact absurd h h1
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h h2
    rw [← Finset.mul_sum] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (by positivity)
    · exact h
  have hp0 : ∫ x, PDE.cosTest k x ∂(volume : Measure (Torus (m+1))) = 0 := by
    simp only [PDE.cosTest, integral_const_mul, integral_cos_mode_zero k hk, mul_zero]
  have hset : {X : Config (m+1) (n+1) | 0 < linCoord (volume : Measure (Torus (m+1))) (PDE.cosTest k) X}
      = {X | 0 < Z X} := by
    ext X
    simp only [Set.mem_setOf_eq, linCoord, pair, hp0, sub_zero]
    exact Iff.rfl
  rw [hset]
  exact prob_half P _ (gibbs_inv _ _ _ _) Z hZm hneg hnull

end HRS.MH.CondOuP
