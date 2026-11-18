import HRS.MS.PsdHeatAux2

/-!
# WR-7: diagonal bound `N F_N^{k} ≥ -½ k(0)` for the bounded positive-definite part of the kernel

Packet WR-7 of `docs/SUPP_FOUND_PACKETS.md` (Track D), namespace `HRS.MS.Wr`.

For a configuration `X = (x_1,…,x_N)`, the empirical measure `μ_N = N⁻¹ ∑ δ_{x_i}` (`HRS.Whole.empirical`)
and a difference kernel `h(x,y) = g(x-y)` with `g` symmetric,
`pairEnergy h X μ = ½ ∬ g d(σ⊗σ) - g(0)/(2N)` with the signed measure `σ = μ_N - μ`
(`wr7_pairEnergy_eq`).  The signed measure is written as `σ = u ν` with `ν = μ_N + μ` and
`u = dμ_N/dν - dμ/dν` (Radon-Nikodym), so that positive definiteness of `kTau` and conditional
positive definiteness of `kTauLog` (`kTau_posdef`, `kTauLog_cpd` of `PsdHeatAux1/2`) apply.

Main results (`μ` a probability measure, atoms allowed, `1 ≤ N`, arbitrary configuration `X`):

* `kTau_diag_bound`: for `0 < s`, `0 < τ`,
  `-(1/2) * kTau d s τ 0 ≤ N * pairEnergy (fun x y => kTau d s τ (x - y)) X μ`.
  No integrability hypothesis is needed (`kTau` is bounded and continuous).
* `kTauLog_diag_bound`: for `0 < τ` and a finite logarithmic moment
  `Integrable (fun x => Real.log (2 + ‖x‖)) μ` of `μ`,
  `-(1/2) * kTauLog d τ 0 ≤ N * pairEnergy (fun x y => kTauLog d τ (x - y)) X μ`.
  The signed measure `μ_N - μ` has mass zero automatically (both are probability measures); the log
  moment hypothesis is exactly what makes every Bochner integral in `pairEnergy` a genuine integral
  (`kTauLog_rows_integrable`, `kTauLog_pair_integrable`: no junk-value branch).

Helper lemmas carry the prefix `wr7_`.  No statement is weakened: the only hypotheses beyond the
sketch are `1 ≤ N` (for the bound to make sense) and, in the log case, the log moment of `μ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.Wr

open HRS.Whole HRS.MS.Psd

variable {d N : ℕ}

/-! ### Transfer of densities on `ν ⊗ ν` -/

section Transfer

/-- Lebesgue decomposition for finite measures (the default instance search is too slow on `Euc d`). -/
local instance wr7_hld (α ν : Measure (Euc d)) [IsFiniteMeasure α] [IsFiniteMeasure ν] :
    α.HaveLebesgueDecomposition ν := Measure.haveLebesgueDecomposition_of_finiteMeasure

variable {ν α β : Measure (Euc d)} [IsFiniteMeasure ν] [IsFiniteMeasure α] [IsFiniteMeasure β]

theorem wr7_prod_eq (hα : α ≪ ν) (hβ : β ≪ ν) :
    α.prod β = (ν.prod ν).withDensity (fun z => α.rnDeriv ν z.1 * β.rnDeriv ν z.2) := by
  have h1 := Measure.withDensity_rnDeriv_eq α ν hα
  have h2 := Measure.withDensity_rnDeriv_eq β ν hβ
  calc α.prod β = (ν.withDensity (α.rnDeriv ν)).prod (ν.withDensity (β.rnDeriv ν)) := by
        rw [h1, h2]
    _ = _ := prod_withDensity (Measure.measurable_rnDeriv _ _) (Measure.measurable_rnDeriv _ _)

theorem wr7_prod_meas (α β : Measure (Euc d)) :
    Measurable (fun z : Euc d × Euc d => α.rnDeriv ν z.1 * β.rnDeriv ν z.2) :=
  ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul
    ((Measure.measurable_rnDeriv _ _).comp measurable_snd)

theorem wr7_prod_lt_top :
    ∀ᵐ z ∂(ν.prod ν), α.rnDeriv ν z.1 * β.rnDeriv ν z.2 < ∞ := by
  have h1 : ∀ᵐ z ∂(ν.prod ν), α.rnDeriv ν z.1 < ∞ :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.rnDeriv_lt_top α ν)
  have h2 : ∀ᵐ z ∂(ν.prod ν), β.rnDeriv ν z.2 < ∞ :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.rnDeriv_lt_top β ν)
  filter_upwards [h1, h2] with z hz1 hz2 using ENNReal.mul_lt_top hz1 hz2

theorem wr7_transfer_integral (hα : α ≪ ν) (hβ : β ≪ ν) (k : Euc d × Euc d → ℝ) :
    ∫ z, ((α.rnDeriv ν z.1).toReal * (β.rnDeriv ν z.2).toReal) * k z ∂(ν.prod ν) =
      ∫ z, k z ∂(α.prod β) := by
  rw [wr7_prod_eq hα hβ, integral_withDensity_eq_integral_toReal_smul (wr7_prod_meas α β)
    wr7_prod_lt_top]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [ENNReal.toReal_mul, smul_eq_mul]

theorem wr7_transfer_integrable (hα : α ≪ ν) (hβ : β ≪ ν) (k : Euc d × Euc d → ℝ) :
    Integrable (fun z => ((α.rnDeriv ν z.1).toReal * (β.rnDeriv ν z.2).toReal) * k z)
        (ν.prod ν) ↔ Integrable k (α.prod β) := by
  rw [wr7_prod_eq hα hβ, integrable_withDensity_iff_integrable_smul' (wr7_prod_meas α β)
    wr7_prod_lt_top]
  simp only [ENNReal.toReal_mul, smul_eq_mul]

/-- The pairing of the signed measure `u ν`, `u = dα/dν - dβ/dν`, against a kernel splits into the
four pairings of `α` and `β`. -/
theorem wr7_signed_pair (hα : α ≪ ν) (hβ : β ≪ ν) (g : Euc d → ℝ)
    (haa : Integrable (fun z : Euc d × Euc d => g (z.1 - z.2)) (α.prod α))
    (hab : Integrable (fun z : Euc d × Euc d => g (z.1 - z.2)) (α.prod β))
    (hba : Integrable (fun z : Euc d × Euc d => g (z.1 - z.2)) (β.prod α))
    (hbb : Integrable (fun z : Euc d × Euc d => g (z.1 - z.2)) (β.prod β)) :
    ∫ z : Euc d × Euc d, g (z.1 - z.2) *
        (((α.rnDeriv ν z.1).toReal - (β.rnDeriv ν z.1).toReal) *
          ((α.rnDeriv ν z.2).toReal - (β.rnDeriv ν z.2).toReal)) ∂(ν.prod ν) =
      ∫ z, g (z.1 - z.2) ∂(α.prod α) - ∫ z, g (z.1 - z.2) ∂(α.prod β) -
        ∫ z, g (z.1 - z.2) ∂(β.prod α) + ∫ z, g (z.1 - z.2) ∂(β.prod β) := by
  set k : Euc d × Euc d → ℝ := fun z => g (z.1 - z.2) with hk
  have e : ∀ z : Euc d × Euc d, k z *
      (((α.rnDeriv ν z.1).toReal - (β.rnDeriv ν z.1).toReal) *
        ((α.rnDeriv ν z.2).toReal - (β.rnDeriv ν z.2).toReal)) =
      (((α.rnDeriv ν z.1).toReal * (α.rnDeriv ν z.2).toReal) * k z -
        ((α.rnDeriv ν z.1).toReal * (β.rnDeriv ν z.2).toReal) * k z) -
        ((β.rnDeriv ν z.1).toReal * (α.rnDeriv ν z.2).toReal) * k z +
        ((β.rnDeriv ν z.1).toReal * (β.rnDeriv ν z.2).toReal) * k z := by
    intro z; ring
  have Taa := (wr7_transfer_integrable hα hα k).2 haa
  have Tab := (wr7_transfer_integrable hα hβ k).2 hab
  have Tba := (wr7_transfer_integrable hβ hα k).2 hba
  have Tbb := (wr7_transfer_integrable hβ hβ k).2 hbb
  have I1 : Integrable (fun z : Euc d × Euc d =>
      ((α.rnDeriv ν z.1).toReal * (α.rnDeriv ν z.2).toReal) * k z -
        ((α.rnDeriv ν z.1).toReal * (β.rnDeriv ν z.2).toReal) * k z) (ν.prod ν) := Taa.sub Tab
  have I2 : Integrable (fun z : Euc d × Euc d =>
      ((α.rnDeriv ν z.1).toReal * (α.rnDeriv ν z.2).toReal) * k z -
        ((α.rnDeriv ν z.1).toReal * (β.rnDeriv ν z.2).toReal) * k z -
        ((β.rnDeriv ν z.1).toReal * (α.rnDeriv ν z.2).toReal) * k z) (ν.prod ν) := I1.sub Tba
  show ∫ z, k z * _ ∂(ν.prod ν) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_add I2 Tbb, integral_sub I1 Tba,
    integral_sub Taa Tab, wr7_transfer_integral hα hα k, wr7_transfer_integral hα hβ k,
    wr7_transfer_integral hβ hα k, wr7_transfer_integral hβ hβ k]

theorem wr7_u_meas :
    Measurable (fun x : Euc d => (α.rnDeriv ν x).toReal - (β.rnDeriv ν x).toReal) :=
  ((Measure.measurable_rnDeriv _ _).ennreal_toReal).sub
    ((Measure.measurable_rnDeriv _ _).ennreal_toReal)

theorem wr7_u_int :
    Integrable (fun x : Euc d => (α.rnDeriv ν x).toReal - (β.rnDeriv ν x).toReal) ν :=
  Measure.integrable_toReal_rnDeriv.sub Measure.integrable_toReal_rnDeriv

theorem wr7_u_mass (hα : α ≪ ν) (hβ : β ≪ ν) :
    ∫ x, ((α.rnDeriv ν x).toReal - (β.rnDeriv ν x).toReal) ∂ν =
      α.real Set.univ - β.real Set.univ := by
  rw [integral_sub Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv,
    Measure.integral_toReal_rnDeriv hα, Measure.integral_toReal_rnDeriv hβ]

theorem wr7_u_log (hα : α ≪ ν) (hβ : β ≪ ν) {L : Euc d → ℝ} (hLα : Integrable L α)
    (hLβ : Integrable L β) :
    Integrable (fun x : Euc d => L x *
      ((α.rnDeriv ν x).toReal - (β.rnDeriv ν x).toReal)) ν := by
  have h1 := (integrable_toReal_rnDeriv_mul_iff hα).2 hLα
  have h2 := (integrable_toReal_rnDeriv_mul_iff hβ).2 hLβ
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  ring

end Transfer

/-! ### The empirical measure -/

theorem wr7_emp_integral {α : Measure (Euc d)} (X : EucConfig d N) (hα : α = HRS.Whole.empirical X)
    (φ : Euc d → ℝ) : ∫ x, φ x ∂α = (N : ℝ)⁻¹ * ∑ i, φ (X i) := by
  subst hα
  unfold HRS.Whole.empirical
  rw [integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp [integral_dirac, ENNReal.toReal_inv]

theorem wr7_emp_integrable (hN : 1 ≤ N) (X : EucConfig d N) (φ : Euc d → ℝ) :
    Integrable φ (HRS.Whole.empirical X) := by
  unfold HRS.Whole.empirical
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (by exact_mod_cast (show N ≠ 0 by omega)))
  rw [integrable_finsetSum_measure]
  exact fun i _ => integrable_dirac (by simp)

theorem wr7_emp_prob (hN : 1 ≤ N) (X : EucConfig d N) : IsProbabilityMeasure (HRS.Whole.empirical X) := by
  refine ⟨?_⟩
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [HRS.Whole.empirical, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    measure_univ, smul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  exact ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top N)

/-! ### Integrability of the pair kernel against products -/

theorem wr7_int_of_bound {α β : Measure (Euc d)} [IsFiniteMeasure α] [IsFiniteMeasure β]
    {g : Euc d → ℝ} (hg : Measurable g) (C : ℝ) (M : Euc d → ℝ) (hMα : Integrable M α)
    (hMβ : Integrable M β) (hb : ∀ a b : Euc d, |g (a - b)| ≤ C + M a + M b) :
    Integrable (fun z : Euc d × Euc d => g (z.1 - z.2)) (α.prod β) := by
  have h1 : Integrable (fun z : Euc d × Euc d => M z.1) (α.prod β) := by
    simpa using hMα.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : Euc d => (1 : ℝ)) β)
  have h2 : Integrable (fun z : Euc d × Euc d => M z.2) (α.prod β) := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Euc d => (1 : ℝ)) α).mul_prod hMβ
  have hm : Measurable (fun z : Euc d × Euc d => g (z.1 - z.2)) :=
    hg.comp (measurable_fst.sub measurable_snd)
  refine Integrable.mono' (((integrable_const C).add h1).add h2) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact hb z.1 z.2

/-! ### The energy identity -/

/-- `pairEnergy` of the difference kernel `g(x-y)` (symmetric `g`) at `X` is half the `g`-energy of
the signed measure `μ_N - μ = u (μ_N + μ)` minus the diagonal term `g(0)/(2N)`. -/
theorem wr7_pairEnergy_eq (hN : 1 ≤ N) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (g : Euc d → ℝ) (hsymm : ∀ w, g (-w) = g w) (X : EucConfig d N)
    (haa : Integrable (fun z : Euc d × Euc d => g (z.1 - z.2)) ((HRS.Whole.empirical X).prod (HRS.Whole.empirical X)))
    (hab : Integrable (fun z : Euc d × Euc d => g (z.1 - z.2)) ((HRS.Whole.empirical X).prod μ))
    (hbb : Integrable (fun z : Euc d × Euc d => g (z.1 - z.2)) (μ.prod μ)) :
    pairEnergy (fun x y => g (x - y)) X μ =
      (1 / 2) * ∫ z : Euc d × Euc d, g (z.1 - z.2) *
        ((((HRS.Whole.empirical X).rnDeriv (HRS.Whole.empirical X + μ) z.1).toReal -
            (μ.rnDeriv (HRS.Whole.empirical X + μ) z.1).toReal) *
          (((HRS.Whole.empirical X).rnDeriv (HRS.Whole.empirical X + μ) z.2).toReal -
            (μ.rnDeriv (HRS.Whole.empirical X + μ) z.2).toReal))
          ∂((HRS.Whole.empirical X + μ).prod (HRS.Whole.empirical X + μ)) - g 0 / (2 * N) := by
  haveI := wr7_emp_prob hN X
  set α : Measure (Euc d) := HRS.Whole.empirical X with hαdef
  have hαν : α ≪ α + μ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hμν : μ ≪ α + μ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hba : Integrable (fun z : Euc d × Euc d => g (z.1 - z.2)) (μ.prod α) := by
    have := hab.swap
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp, Prod.fst_swap, Prod.snd_swap]
    rw [← hsymm (z.2 - z.1), neg_sub]
  have key := wr7_signed_pair hαν hμν g haa hab hba hbb
  have hswap : ∫ z : Euc d × Euc d, g (z.1 - z.2) ∂(μ.prod α) =
      ∫ z : Euc d × Euc d, g (z.1 - z.2) ∂(α.prod μ) := by
    rw [← integral_prod_swap (μ := α) (ν := μ) (fun z : Euc d × Euc d => g (z.1 - z.2))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [← hsymm (z.2 - z.1), neg_sub]
  have eαα : ∫ z : Euc d × Euc d, g (z.1 - z.2) ∂(α.prod α) =
      (N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ i, ∑ j, g (X i - X j)) := by
    rw [integral_prod _ haa, wr7_emp_integral X hαdef]
    simp_rw [wr7_emp_integral X hαdef]
    rw [← Finset.mul_sum]
  have eαμ : ∫ z : Euc d × Euc d, g (z.1 - z.2) ∂(α.prod μ) =
      (N : ℝ)⁻¹ * ∑ i, ∫ y, g (X i - y) ∂μ := by
    rw [integral_prod _ hab, wr7_emp_integral X hαdef]
  have eμμ : ∫ z : Euc d × Euc d, g (z.1 - z.2) ∂(μ.prod μ) =
      ∫ x, ∫ y, g (x - y) ∂μ ∂μ := integral_prod _ hbb
  have hsum : ∀ i : Fin N, ∑ j, g (X i - X j) = g 0 + ∑ j ∈ Finset.univ.erase i, g (X i - X j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), sub_self]
  have hS : ∑ i, ∑ j, g (X i - X j) =
      (N : ℝ) * g 0 + ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) := by
    rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.sum_add_distrib]
    simp
  rw [key, hswap, eαα, eαμ, eμμ, hS]
  unfold pairEnergy
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp
  ring

/-! ### The bounded part `kTau` -/

theorem wr7_kTau_symm {s : ℝ} {τ : ℝ} (w : Euc d) : kTau d s τ (-w) = kTau d s τ w := by
  unfold kTau psd3_F heatKerE
  simp only [norm_neg]

theorem wr7_kTau_abs_le {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) (w : Euc d) :
    |kTau d s τ w| ≤ kTau d s τ 0 := by
  rw [abs_of_nonneg (kTau_nonneg hs hτ w)]
  exact kTau_le_zero hs hτ w

/-- **WR-7, `s > 0`.**  `N F_N^{kTau}(X) ≥ -½ kTau 0` for every configuration `X` and every
probability measure `μ` (atoms allowed). -/
theorem kTau_diag_bound {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) (hN : 1 ≤ N)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (X : EucConfig d N) :
    -(1 / 2) * kTau d s τ 0 ≤
      (N : ℝ) * pairEnergy (fun x y => kTau d s τ (x - y)) X μ := by
  haveI := wr7_emp_prob hN X
  set α : Measure (Euc d) := HRS.Whole.empirical X with hαdef
  have hαν : α ≪ α + μ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hμν : μ ≪ α + μ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hint : ∀ (a b : Measure (Euc d)) [IsFiniteMeasure a] [IsFiniteMeasure b],
      Integrable (fun z : Euc d × Euc d => kTau d s τ (z.1 - z.2)) (a.prod b) := fun a b _ _ =>
    wr7_int_of_bound (kTau_continuous hs hτ).measurable (kTau d s τ 0) (fun _ => 0)
      (integrable_zero _ _ _) (integrable_zero _ _ _) (fun x y => by
        simpa using wr7_kTau_abs_le hs hτ (x - y))
  have hE := wr7_pairEnergy_eq hN μ (kTau d s τ) wr7_kTau_symm X (hint α α) (hint α μ) (hint μ μ)
  have hpos := kTau_posdef hs hτ (ν := α + μ) (wr7_u_meas (α := α) (β := μ) (ν := α + μ))
    (wr7_u_int (α := α) (β := μ) (ν := α + μ))
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hE]
  set T := ∫ z : Euc d × Euc d, kTau d s τ (z.1 - z.2) *
      (((α.rnDeriv (α + μ) z.1).toReal - (μ.rnDeriv (α + μ) z.1).toReal) *
        ((α.rnDeriv (α + μ) z.2).toReal - (μ.rnDeriv (α + μ) z.2).toReal))
        ∂((α + μ).prod (α + μ)) with hT
  have h0 : (N : ℝ) * ((1 / 2) * T - kTau d s τ 0 / (2 * N)) =
      (N : ℝ) / 2 * T - kTau d s τ 0 / 2 := by
    field_simp
  rw [h0]
  nlinarith [mul_nonneg hN'.le hpos]

/-! ### The logarithmic part `kTauLog` -/

theorem wr7_kTauLog_symm {τ : ℝ} (w : Euc d) : kTauLog d τ (-w) = kTauLog d τ w := by
  unfold kTauLog
  simp only [norm_neg]

theorem wr7_kTauLog_int {τ : ℝ} (hτ : 0 < τ) {a b : Measure (Euc d)} [IsFiniteMeasure a]
    [IsFiniteMeasure b] (ha : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) a)
    (hb : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) b) :
    Integrable (fun z : Euc d × Euc d => kTauLog d τ (z.1 - z.2)) (a.prod b) :=
  wr7_int_of_bound (kTauLog_continuous hτ).measurable (1 / (2 * τ) + τ / 2)
    (fun x => Real.log (2 + ‖x‖)) ha hb (fun x y => by
      have h1 := kTauLog_abs_le hτ (x - y)
      have h2 := psd3_log_sub_le x y
      linarith)

theorem wr7_log_int_emp (hN : 1 ≤ N) (X : EucConfig d N) :
    Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.empirical X) := wr7_emp_integrable hN X _

/-- Well-definedness (no junk values) of the rows of the log kernel in `pairEnergy`. -/
theorem kTauLog_rows_integrable {τ : ℝ} (hτ : 0 < τ) (μ : Measure (Euc d)) [IsFiniteMeasure μ]
    (hlog : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) μ) (x : Euc d) :
    Integrable (fun y => kTauLog d τ (x - y)) μ := by
  have hm : Measurable (fun y : Euc d => kTauLog d τ (x - y)) :=
    (kTauLog_continuous hτ).measurable.comp (measurable_const.sub measurable_id)
  refine Integrable.mono' ((integrable_const (1 / (2 * τ) + τ / 2 + Real.log (2 + ‖x‖))).add hlog)
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  have h1 := kTauLog_abs_le hτ (x - y)
  have h2 := psd3_log_sub_le x y
  simp only [Pi.add_apply]
  linarith

/-- Well-definedness of the pair term of `pairEnergy` for the log kernel. -/
theorem kTauLog_pair_integrable {τ : ℝ} (hτ : 0 < τ) (μ : Measure (Euc d)) [IsFiniteMeasure μ]
    (hlog : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) μ) :
    Integrable (fun z : Euc d × Euc d => kTauLog d τ (z.1 - z.2)) (μ.prod μ) :=
  wr7_kTauLog_int hτ hlog hlog

/-- **WR-7, logarithmic case.**  `N F_N^{kTauLog}(X) ≥ -½ kTauLog 0` for every configuration `X`
and every probability measure `μ` with a finite logarithmic moment. -/
theorem kTauLog_diag_bound {τ : ℝ} (hτ : 0 < τ) (hN : 1 ≤ N)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (hlog : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) μ) (X : EucConfig d N) :
    -(1 / 2) * kTauLog d τ 0 ≤
      (N : ℝ) * pairEnergy (fun x y => kTauLog d τ (x - y)) X μ := by
  haveI := wr7_emp_prob hN X
  set α : Measure (Euc d) := HRS.Whole.empirical X with hαdef
  have hαν : α ≪ α + μ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hμν : μ ≪ α + μ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hlogα : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) α := wr7_log_int_emp hN X
  have hE := wr7_pairEnergy_eq hN μ (kTauLog d τ) wr7_kTauLog_symm X
    (wr7_kTauLog_int hτ hlogα hlogα) (wr7_kTauLog_int hτ hlogα hlog)
    (wr7_kTauLog_int hτ hlog hlog)
  have hmass : ∫ x, ((α.rnDeriv (α + μ) x).toReal - (μ.rnDeriv (α + μ) x).toReal) ∂(α + μ) = 0 := by
    rw [wr7_u_mass hαν hμν]
    simp [Measure.real]
  have hpos := kTauLog_cpd hτ (ν := α + μ) (wr7_u_meas (α := α) (β := μ) (ν := α + μ))
    (wr7_u_int (α := α) (β := μ) (ν := α + μ)) (wr7_u_log hαν hμν hlogα hlog) hmass
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hE]
  set T := ∫ z : Euc d × Euc d, kTauLog d τ (z.1 - z.2) *
      (((α.rnDeriv (α + μ) z.1).toReal - (μ.rnDeriv (α + μ) z.1).toReal) *
        ((α.rnDeriv (α + μ) z.2).toReal - (μ.rnDeriv (α + μ) z.2).toReal))
        ∂((α + μ).prod (α + μ)) with hT
  have h0 : (N : ℝ) * ((1 / 2) * T - kTauLog d τ 0 / (2 * N)) =
      (N : ℝ) / 2 * T - kTauLog d τ 0 / 2 := by
    field_simp
  rw [h0]
  nlinarith [mul_nonneg hN'.le hpos]

end HRS.MS.Wr
