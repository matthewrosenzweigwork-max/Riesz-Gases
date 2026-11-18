import HRS.MS.WrPoleAux3
import HRS.MS.WrKernAux1
import HRS.Equilibrium.MarginalExpFamily

/-!
# HRS.MS.WrInsAux1 -- insertion pressure on `Euc d`: exponent, tilt, right derivative at `0` (WR-13c2, part 1)

Packet WR-13c2 (T9 of `docs/WR_B_PLAN.md`), namespace `HRS.MS.Wr`, helper prefix `wr13c2_`.

With `P0 = cavityLaw d s N β μ` (`n = N-1`, `λ = β/N`) and `X_x(Y) = -λ ∑_i g(x - Y_i) ≤ 0`:

* `wr13c2_tvDist_eq`: the one-line equality `Bias.tvDist = External.Entropy.tvDist`;
* `wr13c2_poleLaw_eq_tilted`: `poleLaw d s N β μ x t = P0.tilted (t X_x)` (`0 ≤ t`);
* `wr13c2_integrable_X`: `X_x ∈ L¹(P0)` (one-coordinate density bound of `wr13a_pole_bundle` plus exchangeability);
* `wr13c2_insertionPressure_eq`: `insertionPressure = cgf X_x P0` (the Mathlib cumulant generating function);
* `wr13c2_hasDerivWithinAt`: the right derivative of `insertionPressure` at `0` exists and equals `P0[X_x]`
  (so `Bias.insertionDefect = cgf X_x P0 1 - P0[X_x]`, no junk value of `derivWithin`).

Part 2 (`WrInsAux2`) carries the radial `t`-integrals, `insDefect_le` and `cavity_tv`.
No frozen file is edited.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole (rieszKernel EucConfig)

section Basics

variable {d : ℕ} {s : ℝ}

/-- The one-line equality of the two total-variation conventions: `Bias.tvDist` (`sup_E |ν(E)-ν'(E)|` with
`toReal`) is `External.Entropy.tvDist` (with `Measure.real`). -/
theorem wr13c2_tvDist_eq {α : Type*} [MeasurableSpace α] (ν ν' : Measure α) :
    HRS.Whole.tvDist ν ν' = HRS.External.Entropy.tvDist ν ν' := rfl

/-- The pole exponent `X_x(Y) = -λ ∑_i g(x - Y_i)`, `λ = β/N`, on `(ℝ^d)^{N-1}`. -/
def wr13c2_X (d : ℕ) (s : ℝ) (N : ℕ) (β : ℝ) (x : Euc d) (Y : EucConfig d (N - 1)) : ℝ :=
  -(β / N) * ∑ i, rieszKernel d s (x - Y i)

theorem wr13c2_X_meas (hs0 : 0 < s) (N : ℕ) (β : ℝ) (x : Euc d) :
    Measurable (wr13c2_X d s N β x) :=
  (Finset.measurable_sum _ fun i _ =>
    (wr13a_g_meas hs0).comp (measurable_const.sub (measurable_pi_apply i))).const_mul _

theorem wr13c2_X_le_zero (hs0 : 0 < s) {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) (x : Euc d)
    (Y : EucConfig d (N - 1)) : wr13c2_X d s N β x Y ≤ 0 := by
  unfold wr13c2_X
  have h1 : -(β / (N : ℝ)) ≤ 0 := neg_nonpos.2 (div_nonneg hβ (Nat.cast_nonneg _))
  exact mul_nonpos_of_nonpos_of_nonneg h1 (wr13a_sum_g_nonneg hs0 x Y)

theorem wr13c2_poleWeight_eq (N : ℕ) (β t : ℝ) (x : Euc d) (Y : EucConfig d (N - 1)) :
    HRS.Whole.poleWeight d s N β x t Y = Real.exp (t * wr13c2_X d s N β x Y) := by
  unfold HRS.Whole.poleWeight wr13c2_X
  congr 1
  ring

theorem wr13c2_Ep_eq {μ : Measure (Euc d)} (N : ℕ) (β t : ℝ) (x : Euc d) (Y : EucConfig d (N - 1)) :
    wr13a_Ep d s μ (β / N) β x t Y = wr13a_E d s μ (β / N) β Y + t * wr13c2_X d s N β x Y := by
  unfold wr13a_Ep wr13c2_X
  ring

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β t : ℝ}

/-- `poleLaw = P0.tilted (t X_x)`. -/
theorem wr13c2_poleLaw_eq_tilted (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (N : ℕ) (x : Euc d) :
    HRS.Whole.poleLaw d s N β μ x t =
      (HRS.Whole.cavityLaw d s N β μ).tilted (fun Y => t * wr13c2_X d s N β x Y) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg _)
  have hE := wr13a_E_meas hs0 μ (β / (N : ℝ)) β (n := N - 1)
  have hEi : Integrable (fun Y : EucConfig d (N - 1) => Real.exp (wr13a_E d s μ (β / N) β Y))
      (Measure.pi fun _ : Fin (N - 1) => μ) := wr13a_cavityWeight_integrable hs0 hconv hβ N
  rw [wr13a_poleLaw_eq hs0 hconv hβ ht N x,
    wr13b_tilt_eq_tilted _ (wr13a_Ep_meas hs0 μ (β / N) β x t)
      (fun Y => wr13a_Ep_le hs0 hconv hlam hβ ht x Y),
    wr13a_cavityLaw_eq hs0 hconv hβ N,
    wr13b_tilt_eq_tilted _ hE (fun Y => wr13a_E_le hs0 hconv hlam hβ Y),
    tilted_tilted hEi]
  congr 1
  funext Y
  exact wr13c2_Ep_eq N β t x Y

theorem wr13c2_poleLaw_zero (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β)
    (N : ℕ) (x : Euc d) :
    HRS.Whole.poleLaw d s N β μ x 0 = HRS.Whole.cavityLaw d s N β μ := by
  haveI := wr13a_cavityLaw_isProb hs0 hconv hβ N
  rw [wr13c2_poleLaw_eq_tilted hs0 hconv hβ le_rfl N x]
  simp only [zero_mul]
  exact tilted_zero _

theorem wr13c2_poleLaw_isProb (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (N : ℕ) (x : Euc d) : IsProbabilityMeasure (HRS.Whole.poleLaw d s N β μ x t) :=
  wr13b_poleLaw_isProb hs0 hconv hβ ht N x

theorem wr13c2_cavityLaw_exchangeable (hs0 : 0 < s)
    (hconv : ∀ z, HRS.Whole.convMeasure (rieszKernel d s) μ z ≤ Mg) (hβ : 0 ≤ β) (N : ℕ) :
    HRS.External.Entropy.IsExchangeable (HRS.Whole.cavityLaw d s N β μ) := by
  have := wr13b_poleLaw_exchangeable hs0 hconv hβ (le_refl (0 : ℝ)) N (0 : Euc d)
  rwa [wr13c2_poleLaw_zero hs0 hconv hβ N 0] at this

end Basics

section Deriv

variable {d : ℕ} {s : ℝ}

/-- Every coordinate `g(x - Y_j)` is integrable under the cavity law (one-coordinate density bound of
`wr13a_pole_bundle` at `t = 0` and exchangeability). -/
theorem wr13c2_integrable_coord (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 2 ≤ N) (x : Euc d) (j : Fin (N - 1)) :
    Integrable (fun Y : EucConfig d (N - 1) => rieszKernel d s (x - Y j))
      (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)) := by
  haveI := wr13a_isProb_density hρ
  have hconv := wr13a_conv_le_density (by omega) hs0 hsd hρ hM
  have hint := fun z => (wr13a_potential_bound (by omega) hs0 hsd hρ hM z).1
  obtain ⟨C, -, hb⟩ := wr13a_pole_bundle hd hs0 hsd hβ M
  obtain ⟨-, -, hpole⟩ := hb ρ hρ hM β hβ le_rfl N hN
  have h1 := (hpole x 0 ⟨le_rfl, zero_le_one⟩).2.1
  rw [wr13c2_poleLaw_zero hs0 hconv hβ N x] at h1
  have hpos : 0 < N - 1 := by omega
  have hmarg : (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).map
      (fun Y : EucConfig d (N - 1) => Y j) ≤
      ENNReal.ofReal C • HRS.Whole.withDensityReal ρ := by
    have e : (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).map
        (fun Y : EucConfig d (N - 1) => Y j) =
        HRS.Whole.firstMarginal (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)) := by
      unfold HRS.Whole.firstMarginal
      rw [dif_pos hpos]
      exact (wr13c2_cavityLaw_exchangeable hs0 hconv hβ N).marginal_eq j ⟨0, hpos⟩
    rw [e]
    refine h1.trans (le_of_eq ?_)
    rw [← withDensity_const]
    congr 1
    funext y
    simp
  have hgm : Measurable (fun y : Euc d => rieszKernel d s (x - y)) :=
    (wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)
  have hi : Integrable (fun y : Euc d => rieszKernel d s (x - y))
      ((HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)).map
        (fun Y : EucConfig d (N - 1) => Y j)) :=
    ((hint x).smul_measure (c := ENNReal.ofReal C) ENNReal.ofReal_ne_top).mono_measure hmarg
  exact (integrable_map_measure (hgm.comp measurable_id).aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable).1 hi

theorem wr13c2_integrable_X (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 2 ≤ N) (x : Euc d) :
    Integrable (wr13c2_X d s N β x)
      (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)) :=
  (integrable_finset_sum _ fun j _ => wr13c2_integrable_coord hd hs0 hsd hρ hM hβ hN x j).const_mul _

theorem wr13c2_insertionPressure_eq (N : ℕ) (β : ℝ) (μ : Measure (Euc d)) (x : Euc d) :
    HRS.Whole.insertionPressure d s N β μ x =
      cgf (wr13c2_X d s N β x) (HRS.Whole.cavityLaw d s N β μ) := by
  funext t
  unfold HRS.Whole.insertionPressure HRS.Whole.poleNormalizer cgf mgf
  simp only [wr13c2_poleWeight_eq]

/-- The right derivative at `0` of the cumulant generating function of a variable bounded above, when the
variable is integrable. -/
theorem wr13c2_hasDerivWithinAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hXm : Measurable X) (hb : ∀ ω, X ω ≤ 0)
    (hXi : Integrable X P) : HasDerivWithinAt (cgf X P) (P[X]) (Ici 0) 0 := by
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0) ?_ ?_ self_mem_nhdsWithin ?_
  · intro t ht
    exact (HRS.MarginalAux.EF.hasDerivAt_cgf hXm hb ht).differentiableAt.differentiableWithinAt
  · have := HRS.MarginalAux.EF.tendsto_cgf_zero (P := P) hXm hb
    rw [ContinuousWithinAt, cgf_zero]
    exact this
  · have h := HRS.MarginalAux.EF.tendsto_mean_zero hXm hb hXi
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((HRS.MarginalAux.EF.hasDerivAt_cgf hXm hb ht).deriv).symm

theorem wr13c2_insertionDefect_eq (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} (hN : 2 ≤ N) (x : Euc d) :
    HasDerivWithinAt (HRS.Whole.insertionPressure d s N β (HRS.Whole.withDensityReal ρ) x)
      (∫ Y, wr13c2_X d s N β x Y ∂(HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)))
      (Ici 0) 0 ∧
    HRS.Whole.insertionDefect d s N β (HRS.Whole.withDensityReal ρ) x =
      cgf (wr13c2_X d s N β x) (HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)) 1 -
        ∫ Y, wr13c2_X d s N β x Y ∂(HRS.Whole.cavityLaw d s N β (HRS.Whole.withDensityReal ρ)) := by
  haveI := wr13a_isProb_density hρ
  have hconv := wr13a_conv_le_density (by omega) hs0 hsd hρ hM
  haveI := wr13a_cavityLaw_isProb hs0 hconv hβ N
  have h := wr13c2_hasDerivWithinAt (wr13c2_X_meas hs0 N β x) (wr13c2_X_le_zero hs0 hβ N x)
    (wr13c2_integrable_X hd hs0 hsd hρ hM hβ hN x)
  rw [← wr13c2_insertionPressure_eq] at h
  refine ⟨h, ?_⟩
  unfold HRS.Whole.insertionDefect
  rw [h.derivWithin (uniqueDiffWithinAt_Ici 0), wr13c2_insertionPressure_eq]

end Deriv

end HRS.MS.Wr
