/-
# HRS.Equilibrium.RepulsiveBridge — package REP-01: algebra of the exponent and the `DGRHS` bridge

Pure bookkeeping between the `HRS` conventions (`modulatedEnergyKernel`, `convMeasure`,
`energyPairing`, `centeredKernel`) and the `DGRHS` conventions (`hoeffdingCentered`,
`iidNegativeStatistic`), plus the two facts about the partition function that reduce the
`γ`-uniform statement to a single `β = B₀`.

All statements are `sorry`-ed specifications (see `docs/REPULSIVE_PLAN.md`, §3, REP-01).
Model: `HRS/Equilibrium/PreparationAttractive.lean` (`potential_eq`, `centeredKernel_eq`,
`modulatedEnergyKernel_eq`, and the `KE`/Bochner conversion inside `log_prep_attractive`).
-/
import HRS.Equilibrium.RepulsiveDefs

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Repulsive

variable {d : ℕ}

/-! ### The centred pair kernel -/

/-- `centeredKernel` is measurable in the pair for a measurable `f`. -/
theorem measurable_pairKernel {f : Torus d → ℝ} (hf : Measurable f) (μ : Measure (Torus d))
    [SFinite μ] : Measurable (pairKernel f μ) := by
  have hc : Measurable (convMeasure f μ) := PoleCavityAux.measurable_convMeasure hf μ
  have h : pairKernel f μ = fun p : Torus d × Torus d =>
      f (p.1 - p.2) - convMeasure f μ p.1 - convMeasure f μ p.2 + energyPairing f μ μ := rfl
  rw [h]
  exact (((hf.comp (measurable_fst.sub measurable_snd)).sub (hc.comp measurable_fst)).sub
    (hc.comp measurable_snd)).add measurable_const

/-- Symmetry of the centred kernel of an even function. -/
theorem pairKernel_symm {f : Torus d → ℝ} (hf : ∀ z, f (-z) = f z) (μ : Measure (Torus d))
    (x y : Torus d) : pairKernel f μ (x, y) = pairKernel f μ (y, x) := by
  show centeredKernel f μ x y = centeredKernel f μ y x
  have h : f (x - y) = f (y - x) := by rw [← hf (x - y), neg_sub]
  unfold centeredKernel
  rw [h]
  ring

/-- Continuity of the centred kernel of a continuous (hence bounded) function on the torus. -/
theorem continuous_pairKernel {f : Torus d → ℝ} (hf : Continuous f) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] : Continuous (pairKernel f μ) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hconv : Continuous (convMeasure f μ) := by
    unfold convMeasure
    refine continuous_of_dominated (F := fun x y => f (x - y)) (bound := fun _ => C)
      (fun x => ?_) (fun x => ae_of_all _ fun a => hC _ (Set.mem_univ _)) (integrable_const C)
      (ae_of_all _ fun a => hf.comp (continuous_id.sub continuous_const))
    exact (hf.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have h : pairKernel f μ = fun p : Torus d × Torus d =>
      f (p.1 - p.2) - convMeasure f μ p.1 - convMeasure f μ p.2 + energyPairing f μ μ := rfl
  rw [h]
  exact (((hf.comp (continuous_fst.sub continuous_snd)).sub (hconv.comp continuous_fst)).sub
    (hconv.comp continuous_snd)).add continuous_const

/-- Canonical centering: `∫ g̃(x, y) dμ(y) = 0` for every `x` for which `y ↦ f(x - y)` is
`μ`-integrable, provided `g*μ` is `μ`-integrable (so that `∬ g dμ dμ = ∫ g*μ dμ`). -/
theorem integral_pairKernel_eq_zero {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {f : Torus d → ℝ} (hconv : Integrable (convMeasure f μ) μ) (x : Torus d)
    (hx : Integrable (fun y => f (x - y)) μ) :
    ∫ y, pairKernel f μ (x, y) ∂μ = 0 := by
  have hX : ∫ y, f (x - y) ∂μ = convMeasure f μ x := rfl
  have hE : ∫ y, convMeasure f μ y ∂μ = energyPairing f μ μ := rfl
  have h : (fun y => pairKernel f μ (x, y)) = fun y =>
      ((f (x - y) - convMeasure f μ x) - convMeasure f μ y) + energyPairing f μ μ := rfl
  have i1 : Integrable (fun y => f (x - y) - convMeasure f μ x) μ :=
    hx.sub (integrable_const _)
  have i2 : Integrable (fun y => f (x - y) - convMeasure f μ x - convMeasure f μ y) μ :=
    i1.sub hconv
  rw [h, integral_add i2 (integrable_const _), integral_sub i1 hconv,
    integral_sub hx (integrable_const _), integral_const, integral_const, hX, hE]
  simp

/-- Centering kills constants. -/
theorem pairKernel_const (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (c : ℝ)
    (x y : Torus d) : pairKernel (fun _ => c) μ (x, y) = 0 := by
  have h1 : ∀ z : Torus d, convMeasure (fun _ : Torus d => c) μ z = c := fun z => by
    simp [convMeasure]
  have h2 : energyPairing (fun _ : Torus d => c) μ μ = c := by simp [energyPairing]
  show c - convMeasure (fun _ : Torus d => c) μ x - convMeasure (fun _ : Torus d => c) μ y +
    energyPairing (fun _ : Torus d => c) μ μ = 0
  rw [h1 x, h1 y, h2]
  ring

/-- Centering commutes with scalar multiplication. -/
theorem pairKernel_smul (f : Torus d → ℝ) (μ : Measure (Torus d)) (c : ℝ) (x y : Torus d) :
    pairKernel (fun z => c * f z) μ (x, y) = c * pairKernel f μ (x, y) := by
  simp only [pairKernel, centeredKernel, convMeasure, energyPairing, integral_const_mul]
  ring

/-- Additivity of centering, under the integrability needed to split the one-body potentials
and the pair energy. -/
theorem pairKernel_add {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f₁ f₂ : Torus d → ℝ}
    (h₁ : ∀ x, Integrable (fun y => f₁ (x - y)) μ) (h₂ : ∀ x, Integrable (fun y => f₂ (x - y)) μ)
    (h₁c : Integrable (convMeasure f₁ μ) μ) (h₂c : Integrable (convMeasure f₂ μ) μ)
    (x y : Torus d) :
    pairKernel (fun z => f₁ z + f₂ z) μ (x, y) = pairKernel f₁ μ (x, y) + pairKernel f₂ μ (x, y) := by
  have hC : ∀ z, convMeasure (fun w => f₁ w + f₂ w) μ z =
      convMeasure f₁ μ z + convMeasure f₂ μ z := by
    intro z
    unfold convMeasure
    exact integral_add (h₁ z) (h₂ z)
  have hE : energyPairing (fun w => f₁ w + f₂ w) μ μ =
      energyPairing f₁ μ μ + energyPairing f₂ μ μ := by
    show ∫ z, convMeasure (fun w => f₁ w + f₂ w) μ z ∂μ =
      ∫ z, convMeasure f₁ μ z ∂μ + ∫ z, convMeasure f₂ μ z ∂μ
    simp_rw [hC]
    exact integral_add h₁c h₂c
  simp only [pairKernel, centeredKernel]
  rw [hC x, hC y, hE]
  ring

/-- Two functions that agree off the origin have the same centred kernel off the diagonal
(the diagonal `x = y` is where `f(x - y)` sees the origin), for `μ` without atoms at the
relevant points (we use `μ = ρ dx`). -/
theorem pairKernel_congr_offDiag {ρ : Torus d → ℝ} {μ : Measure (Torus d)}
    (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ) {f₁ f₂ : Torus d → ℝ}
    (hf : ∀ z, z ≠ 0 → f₁ z = f₂ z) (x y : Torus d) (hxy : x ≠ y) :
    pairKernel f₁ μ (x, y) = pairKernel f₂ μ (x, y) := by
  subst hμ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact absurd (Subsingleton.elim x y) hxy
  have hae : ∀ z : Torus d, ∀ᵐ w ∂(withDensityReal ρ), w ≠ z := by
    intro z
    have h0 : (withDensityReal ρ) {z} = 0 :=
      withDensity_absolutelyContinuous _ _ (volume_singleton_torus hd z)
    exact compl_mem_ae_iff.mpr h0
  have hC : ∀ z : Torus d, convMeasure f₁ (withDensityReal ρ) z =
      convMeasure f₂ (withDensityReal ρ) z := by
    intro z
    unfold convMeasure
    apply integral_congr_ae
    filter_upwards [hae z] with w hw
    exact hf (z - w) (sub_ne_zero.mpr (Ne.symm hw))
  have hE : energyPairing f₁ (withDensityReal ρ) (withDensityReal ρ) =
      energyPairing f₂ (withDensityReal ρ) (withDensityReal ρ) := by
    unfold energyPairing
    congr 1
    funext z
    exact hC z
  simp only [pairKernel, centeredKernel]
  rw [hC x, hC y, hE, hf (x - y) (sub_ne_zero.mpr hxy)]

/-- The `HRS` centred kernel of an even function is the `DGRHS` Hoeffding-centred kernel of
`W(x, y) = f(x - y)` (compare `PreparationAttractive.centeredKernel_eq`, where `W = -g`). -/
theorem pairKernel_eq_hoeffdingCentered {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {f : Torus d → ℝ} (hf : ∀ z, f (-z) = f z)
    (hI : Integrable (fun p : Torus d × Torus d => f (p.1 - p.2)) (μ.prod μ)) :
    pairKernel f μ = DGRHS.Gaussian.hoeffdingCentered μ (fun p => f (p.1 - p.2)) := by
  have hsec : ∀ y : Torus d, ∫ x, f (x - y) ∂μ = convMeasure f μ y := by
    intro y
    unfold convMeasure
    congr 1
    funext x
    rw [← hf (x - y), neg_sub]
  have hpair : ∫ z : Torus d × Torus d, f (z.1 - z.2) ∂(μ.prod μ) = energyPairing f μ μ := by
    rw [integral_prod _ hI]
    rfl
  funext p
  simp only [pairKernel, DGRHS.Gaussian.hoeffdingCentered, DGRHS.centeredKernel,
    DGRHS.potential, DGRHS.secondPotential]
  rw [hsec p.2, hpair]
  unfold centeredKernel convMeasure energyPairing
  ring

/-! ### Integrability against a bounded density -/

/-- For `μ = ρ dx` with `ρ ≤ Λ`, every translate of a `dx`-integrable function is
`μ`-integrable (`∫ |f(x - y)| ρ(y) dy ≤ Λ ∫ |f|`).  Companion of
`PreparationAux.integrable_pair_withDensity`. -/
theorem integrable_shift_withDensity {ρ : Torus d → ℝ} {Λ : ℝ} {μ : Measure (Torus d)}
    (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    {f : Torus d → ℝ} (hf : Integrable f) (x : Torus d) :
    Integrable (fun y => f (x - y)) μ := by
  subst hμ
  have : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  have hac : withDensityReal ρ ≪ volume := withDensity_absolutelyContinuous _ _
  have hq : MeasureTheory.Measure.QuasiMeasurePreserving (fun y : Torus d => x - y) (withDensityReal ρ) volume :=
    ((MeasureTheory.Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving).mono_left hac
  refine ⟨hf.aestronglyMeasurable.comp_quasiMeasurePreserving hq, ?_⟩
  have h2 : ∫⁻ y, ‖f (x - y)‖ₑ ∂withDensityReal ρ ≤ ENNReal.ofReal Λ * ∫⁻ y, ‖f y‖ₑ :=
    KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ‖f z‖ₑ) x
  exact lt_of_le_of_lt h2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)

/-- `g*μ` is bounded by `Λ ∫ |g|`, hence `μ`-integrable, for `μ = ρ dx`, `ρ ≤ Λ`. -/
theorem integrable_convMeasure_withDensity {ρ : Torus d → ℝ} {Λ : ℝ} {μ : Measure (Torus d)}
    (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    {f : Torus d → ℝ} (hf : Measurable f) (hfi : Integrable f) :
    Integrable (convMeasure f μ) μ := by
  subst hμ
  have hsm : StronglyMeasurable (fun p : Torus d × Torus d => f (p.1 - p.2)) :=
    (hf.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  have : IsFiniteMeasure (withDensityReal ρ) := by
    refine ⟨lt_of_le_of_lt (Measure.le_iff'.mp (KernelAux2.withDensityReal_le ρ Λ hΛ) Set.univ) ?_⟩
    rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_lt_top
  obtain ⟨C, hC⟩ := KernelAux2.convMeasure_bounded' f hfi ρ Λ hΛ
  refine Integrable.of_bound
    (hsm.integral_prod_right' (ν := withDensityReal ρ)).aestronglyMeasurable C
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hC x

/-- The collision set `𝔇_N` is null for the product of an absolutely continuous `μ`. -/
theorem ae_notMem_collisionSet (hd : 1 ≤ d) {ρ : Torus d → ℝ} {μ : Measure (Torus d)}
    (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ) (N : ℕ) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), X ∉ collisionSet d N := by
  have hatom : ∀ x : Torus d, μ {x} = 0 := by
    intro x
    rw [hμ]
    exact withDensity_absolutelyContinuous _ _ (volume_singleton_torus hd x)
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have hint : Integrable ρ := by
      by_contra h
      have h0 := hρ.integral_one
      rw [integral_undef h] at h0
      exact zero_ne_one h0
    rw [hμ]
    unfold withDensityReal
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hρ.nonneg), hρ.integral_one,
      ENNReal.ofReal_one]
  have hm : ∀ k : Fin N,
      (Measure.pi fun _ : Fin N => μ).map (fun X : Fin N → Torus d => X k) = μ := fun k =>
    (measurePreserving_eval (fun _ : Fin N => μ) k).map_eq
  have hpair : ∀ i j : Fin N, i ≠ j → ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), X i ≠ X j := by
    intro i j hij
    have hind : ProbabilityTheory.IndepFun (fun X : Fin N → Torus d => X i) (fun X : Fin N → Torus d => X j)
        (Measure.pi fun _ : Fin N => μ) :=
      (ProbabilityTheory.iIndepFun_pi (X := fun _ : Fin N => (id : Torus d → Torus d))
        (μ := fun _ : Fin N => μ) (fun _ => aemeasurable_id)).indepFun hij
    have hmap : (Measure.pi fun _ : Fin N => μ).map
        (fun X : Fin N → Torus d => (X i, X j)) = μ.prod μ := by
      have hEq := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable).mp hind
      rw [hEq, hm i, hm j]
    have hD : MeasurableSet {p : Torus d × Torus d | p.1 = p.2} :=
      isClosed_diagonal.measurableSet
    have hnull : (μ.prod μ) {p : Torus d × Torus d | p.1 = p.2} = 0 := by
      rw [Measure.measure_prod_null hD]
      refine ae_of_all _ fun x => ?_
      have hx : Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 = p.2} = {x} := by
        ext y
        exact eq_comm
      show μ (Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 = p.2}) = 0
      rw [hx]
      exact hatom x
    have hnull' : (Measure.pi fun _ : Fin N => μ)
        ((fun X : Fin N → Torus d => (X i, X j)) ⁻¹' {p : Torus d × Torus d | p.1 = p.2}) = 0 := by
      rw [← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hD,
        hmap, hnull]
    rw [ae_iff]
    exact measure_mono_null (fun X hX => not_not.mp hX) hnull'
  have hall : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ i j : Fin N, i ≠ j → X i ≠ X j := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i = j
    · exact ae_of_all _ fun X h => absurd hij h
    · exact (hpair i j hij).mono fun X hX _ => hX
  filter_upwards [hall] with X hX
  rintro ⟨i, j, hij, hXij⟩
  exact hX i j hij hXij

/-! ### The exponent -/

/-- The exponent `-βN F_N` is measurable in the configuration. -/
theorem measurable_exponent (hd : 2 ≤ d) (β : ℝ) (N : ℕ) (μ : Measure (Torus d)) [SFinite μ] :
    Measurable (exponent d β N μ) := by
  have hg : Measurable (periodicRiesz d 0) :=
    PoleCavityAux.measurable_periodicRiesz hd (le_refl 0) (by exact_mod_cast (by omega : 0 < d))
  have hS : Measurable fun X : Config d N =>
      ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d 0 (X i - X j) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  have hT : Measurable fun X : Config d N => ∑ i, ∫ y, periodicRiesz d 0 (X i - y) ∂μ := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have hF : StronglyMeasurable (fun p : Config d N × Torus d => periodicRiesz d 0 (p.1 i - p.2)) :=
      (hg.comp (((measurable_pi_apply i).comp measurable_fst).sub measurable_snd)).stronglyMeasurable
    exact (hF.integral_prod_right' (ν := μ)).measurable
  unfold exponent modulatedEnergyKernel modulatedEnergy
  exact (((hS.const_mul _).sub (hT.const_mul _)).add measurable_const).const_mul _

/-- The Hoeffding decomposition of the exponent (DGR eq:hoeffdingDecomposition, specialised):
`-βN F_N(X) = β · iidNeg_N(g̃)(X) + (β/N) ∑_i g*μ(x_i) - (β/2) ∬ g dμ dμ`, where
`iidNeg_N(h)(X) = -∑_{i≠j} h(x_i, x_j) / (2N)`.  Purely algebraic: no integrability and no
collision hypothesis is needed, because `g̃(x_i, x_j) = g(x_i - x_j) - g*μ(x_i) - g*μ(x_j) + E`
holds pointwise by definition. -/
theorem exponent_eq (β : ℝ) {N : ℕ} (hN : 0 < N) (μ : Measure (Torus d)) (X : Config d N) :
    exponent d β N μ X =
      β * DGRHS.Concentration.iidNegativeStatistic N (pairKernel (periodicRiesz d 0) μ) X +
        (β / (N : ℝ)) * ∑ i, convMeasure (periodicRiesz d 0) μ (X i) -
        β / 2 * energyPairing (periodicRiesz d 0) μ μ := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hite : ∀ (i : Fin N) (f : Fin N → ℝ),
      ∑ j, (if i ≠ j then f j else 0) = ∑ j, f j - f i := by
    intro i f
    rw [← Finset.sum_erase_eq_sub (Finset.mem_univ i), ← Finset.sum_filter]
    congr 1
    ext j
    simp [Finset.mem_erase, ne_comm]
  unfold exponent modulatedEnergyKernel modulatedEnergy DGRHS.Concentration.iidNegativeStatistic
    DGRHS.Concentration.iidCoupledSum DGRHS.Decoupling.offDiagonalSum
  simp only [hite, pairKernel, centeredKernel, convMeasure, energyPairing]
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [← Finset.mul_sum]
  field_simp
  ring

/-! ### Algebra of `iidNegativeStatistic` -/

theorem iidNegativeStatistic_add {N : ℕ} (h₁ h₂ : Torus d × Torus d → ℝ) (X : Config d N) :
    DGRHS.Concentration.iidNegativeStatistic N (fun p => h₁ p + h₂ p) X =
      DGRHS.Concentration.iidNegativeStatistic N h₁ X +
        DGRHS.Concentration.iidNegativeStatistic N h₂ X := by
  unfold DGRHS.Concentration.iidNegativeStatistic DGRHS.Concentration.iidCoupledSum
    DGRHS.Decoupling.offDiagonalSum
  have key : ∑ i, ∑ j, (if i ≠ j then h₁ (X i, X j) + h₂ (X i, X j) else 0) =
      ∑ i, ∑ j, (if i ≠ j then h₁ (X i, X j) else 0) + ∑ i, ∑ j, (if i ≠ j then h₂ (X i, X j) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  simp only []
  rw [key]
  ring

theorem iidNegativeStatistic_smul {N : ℕ} (c : ℝ) (h : Torus d × Torus d → ℝ) (X : Config d N) :
    DGRHS.Concentration.iidNegativeStatistic N (fun p => c * h p) X =
      c * DGRHS.Concentration.iidNegativeStatistic N h X := by
  unfold DGRHS.Concentration.iidNegativeStatistic DGRHS.Concentration.iidCoupledSum
    DGRHS.Decoupling.offDiagonalSum
  have key : ∑ i, ∑ j, (if i ≠ j then c * h (X i, X j) else 0) =
      c * ∑ i, ∑ j, (if i ≠ j then h (X i, X j) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  simp only []
  rw [key]
  ring

/-- Off the collision set only off-diagonal values of the kernel enter. -/
theorem iidNegativeStatistic_congr {N : ℕ} (h₁ h₂ : Torus d × Torus d → ℝ) (X : Config d N)
    (hX : X ∉ collisionSet d N) (h : ∀ x y, x ≠ y → h₁ (x, y) = h₂ (x, y)) :
    DGRHS.Concentration.iidNegativeStatistic N h₁ X =
      DGRHS.Concentration.iidNegativeStatistic N h₂ X := by
  have hne : ∀ i j : Fin N, i ≠ j → X i ≠ X j := fun i j hij hXij => hX ⟨i, j, hij, hXij⟩
  unfold DGRHS.Concentration.iidNegativeStatistic DGRHS.Concentration.iidCoupledSum
    DGRHS.Decoupling.offDiagonalSum
  have key : ∑ i, ∑ j, (if i ≠ j then h₁ (X i, X j) else 0) =
      ∑ i, ∑ j, (if i ≠ j then h₂ (X i, X j) else 0) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · exact h _ _ (hne i j hij)
    · rfl
  simp only []
  rw [key]

/-- A kernel bounded below by `-M` off the diagonal has negative statistic at most `N M / 2`. -/
theorem iidNegativeStatistic_le_of_le {N : ℕ} (h : Torus d × Torus d → ℝ) (X : Config d N)
    (hX : X ∉ collisionSet d N) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x y, x ≠ y → -M ≤ h (x, y)) :
    DGRHS.Concentration.iidNegativeStatistic N h X ≤ (N : ℝ) * M / 2 := by
  have hne : ∀ i j : Fin N, i ≠ j → X i ≠ X j := fun i j hij hXij => hX ⟨i, j, hij, hXij⟩
  have hsum : ∑ _i : Fin N, ∑ _j : Fin N, (-M) ≤
      ∑ i, ∑ j, (if i ≠ j then h (X i, X j) else 0) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    split_ifs with hij
    · exact hM _ _ (hne i j hij)
    · linarith
  have h0 : ∑ _i : Fin N, ∑ _j : Fin N, (-M) = -((N : ℝ) * N * M) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold DGRHS.Concentration.iidNegativeStatistic DGRHS.Concentration.iidCoupledSum
    DGRHS.Decoupling.offDiagonalSum
  simp only []
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-! ### Reduction of the partition function -/

/-- Monotone reduction in `γ`: `e^{-γ N F} ≤ 1 + e^{-β N F}` pointwise for `0 ≤ γ ≤ β`, hence
`K_{N,γ} ≤ 1 + K_{N,β}` (`μ` a probability measure). -/
theorem KE_le_one_add (g : Torus d → ℝ) (N : ℕ) {γ β : ℝ} (hγ : 0 ≤ γ) (hγβ : γ ≤ β)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    PreparationAux.KE g N γ μ ≤ 1 + PreparationAux.KE g N β μ := by
  have key : ∀ t : ℝ, Real.exp (γ * t) ≤ 1 + Real.exp (β * t) := by
    intro t
    rcases le_total t 0 with ht | ht
    · have h1 : Real.exp (γ * t) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hγ ht)
      have h2 := Real.exp_pos (β * t)
      linarith
    · have h1 : Real.exp (γ * t) ≤ Real.exp (β * t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hγβ ht)
      have h2 := Real.exp_pos (β * t)
      linarith
  unfold PreparationAux.KE
  calc ∫⁻ X, ENNReal.ofReal (Real.exp (-γ * N * modulatedEnergyKernel g X μ))
        ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ∫⁻ X, (1 + ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g X μ)))
          ∂(Measure.pi fun _ : Fin N => μ) := by
        refine lintegral_mono fun X => ?_
        have e1 : -γ * N * modulatedEnergyKernel g X μ = γ * (-(N * modulatedEnergyKernel g X μ)) := by
          ring
        have e2 : -β * N * modulatedEnergyKernel g X μ = β * (-(N * modulatedEnergyKernel g X μ)) := by
          ring
        rw [e1, e2]
        calc ENNReal.ofReal (Real.exp (γ * (-(N * modulatedEnergyKernel g X μ))))
            ≤ ENNReal.ofReal (1 + Real.exp (β * (-(N * modulatedEnergyKernel g X μ)))) :=
              ENNReal.ofReal_le_ofReal (key _)
          _ = 1 + ENNReal.ofReal (Real.exp (β * (-(N * modulatedEnergyKernel g X μ)))) := by
              rw [ENNReal.ofReal_add zero_le_one (Real.exp_pos _).le, ENNReal.ofReal_one]
    _ = 1 + ∫⁻ X, ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g X μ))
          ∂(Measure.pi fun _ : Fin N => μ) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- `K_{N,β}` as a Bochner integral of `exp (exponent)` (`ofReal_integral_eq_lintegral_ofReal`). -/
theorem KE_eq_ofReal_integral (β : ℝ) (N : ℕ) (μ : Measure (Torus d))
    (hint : Integrable (fun X => Real.exp (exponent d β N μ X)) (Measure.pi fun _ : Fin N => μ)) :
    PreparationAux.KE (periodicRiesz d 0) N β μ =
      ENNReal.ofReal (∫ X, Real.exp (exponent d β N μ X) ∂(Measure.pi fun _ : Fin N => μ)) := by
  unfold PreparationAux.KE
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun X => (Real.exp_pos _).le)]
  rfl

end Repulsive

end HRS

end
