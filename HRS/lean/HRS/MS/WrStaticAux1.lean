import HRS.MS.WrQuadAux3
import HRS.MS.WrTr
import HRS.MS.WrKerAux3
import HRS.MS.WrRefMargAux1
import HRS.MS.WrCavAux1

/-!
# HRS.MS.WrStaticAux1 -- linear statistics for every `N >= 2` (WR-14b, part 1)

Packet WR-14b of `docs/WR_B_PLAN.md` (T12), namespace `HRS.MS.Wr`, helper prefix `wr14b_`.

Conjunct 2 of `HRS.Whole.euc_static`: `Var_{Q_N}[mu_N(f)] <= C/N ||f||^2_{L^2(mu)}` for every `N >= 2`,
`beta` in `[beta_-, beta_+]`, uniformly in the probability densities `rho <= M`:

* `wr14b_Q_le`: the crude density bound `Q_N <= e^{beta N M_g} mu^{tensor N}` (the Gibbs weight is at most
  `e^{beta N M_g}` since `g >= 0` and `g * mu <= M_g`, and the normaliser is `>= 1`);
* `wr14b_lin_small`: `Var_Q(sum f(x_i)) <= e^{beta N M_g} N int f^2` for measurable `f in L^2(mu)`;
* `wr14b_lin_large`: for `N >= N0`, `Var_Q(sum f(x_i)) <= C N int f^2` (`euc_linear_variance` and the density bound
  `d pi^R_N / d mu <= C` of the reference marginal);
* `wr14b_linear`: the packaged clause for all `N >= 2`, all `f in L^2(mu)` (not necessarily measurable).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

open HRS.External HRS.MS.Psd

variable {d : ℕ} {s : ℝ}

/-! ### The crude density bound for every `N` -/

/-- The Riesz kernel `g(x - y)` is an `EWeakKernel` for `mu = rho dx`, `rho <= M`, with row bound `M_g`. -/
theorem wr14b_weak_g (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    EWeakKernel (HRS.Whole.withDensityReal ρ) (HRS.Whole.potentialBound d s M)
      (fun x y : Euc d => HRS.Whole.rieszKernel d s (x - y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (wr13a_g_meas hs0).comp (measurable_fst.sub measurable_snd)
  · intro x y
    exact wr13a_g_sub_swap y x
  · intro x y
    exact wr13a_g_nonneg hs0 _
  · intro x
    obtain ⟨hi, -, hb⟩ := wr13a_potential_bound hd hs0 hsd hρ hM x
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun y => wr13a_g_nonneg hs0 _)]
    exact ENNReal.ofReal_le_ofReal hb

theorem wr14b_potentialBound_nonneg (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    0 ≤ HRS.Whole.potentialBound d s M := by
  obtain ⟨-, h0, hb⟩ := wr13a_potential_bound hd hs0 hsd hρ hM 0
  exact h0.trans hb

/-- The modulated energy is at least `-M_g`. -/
theorem wr14b_energy_ge (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {N : ℕ} (hN : 0 < N)
    (X : Fin N → Euc d) :
    -HRS.Whole.potentialBound d s M ≤
      HRS.Whole.modulatedEnergy (HRS.Whole.rieszKernel d s) X (HRS.Whole.withDensityReal ρ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold HRS.Whole.modulatedEnergy
  have h1 : 0 ≤ (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
      HRS.Whole.rieszKernel d s (X i - X j) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      wr13a_g_nonneg hs0 _)
  have h2 : (1 / (N : ℝ)) * ∑ i, HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s)
      (HRS.Whole.withDensityReal ρ) (X i) ≤ HRS.Whole.potentialBound d s M := by
    have hsum : ∑ i, HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s)
        (HRS.Whole.withDensityReal ρ) (X i) ≤ N * HRS.Whole.potentialBound d s M := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun i => HRS.Whole.convMeasure
        (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) (X i))
        (HRS.Whole.potentialBound d s M) (fun i _ => (wr13a_potential_bound hd hs0 hsd hρ hM (X i)).2.2)
      simpa [nsmul_eq_mul] using this
    calc (1 / (N : ℝ)) * ∑ i, HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s)
          (HRS.Whole.withDensityReal ρ) (X i) ≤ (1 / (N : ℝ)) * (N * HRS.Whole.potentialBound d s M) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = HRS.Whole.potentialBound d s M := by field_simp
  have h3 : 0 ≤ (1 / 2 : ℝ) * HRS.Whole.energyPairing (HRS.Whole.rieszKernel d s)
      (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ) := by
    refine mul_nonneg (by norm_num) (integral_nonneg fun x => integral_nonneg fun y => ?_)
    exact wr13a_g_nonneg hs0 _
  linarith

/-- **Crude density bound, every `N ≥ 1`**: `Q_N ≤ e^{β N M_g} μ^{⊗N}`. -/
theorem wr14b_Q_le (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ}
    (hN : 0 < N) :
    HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (Real.exp (β * N * HRS.Whole.potentialBound d s M)) •
        Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ := by
  haveI := wr13a_isProb_density hρ
  have ha := wr14b_potentialBound_nonneg hd hs0 hsd hρ hM
  obtain ⟨-, h1⟩ := (wr14b_weak_g hd hs0 hsd hρ hM).gibbsWellDefined_E ha hβ hN
  have hK : 1 ≤ HRS.Whole.gibbsNormalizer (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ) := by
    rw [← HRS.Whole.pairNormalizer_diff]
    exact h1
  unfold HRS.Whole.modulatedGibbs
  refine Measure.le_iff.2 fun A hA => ?_
  rw [Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul, Measure.smul_apply, smul_eq_mul,
    ← setLIntegral_const]
  have hinv : (ENNReal.ofReal (HRS.Whole.gibbsNormalizer (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal ρ)))⁻¹ ≤ 1 := ENNReal.inv_le_one.2 (ENNReal.one_le_ofReal.2 hK)
  calc _ ≤ 1 * ∫⁻ X in A, ENNReal.ofReal (Real.exp (-β * N * HRS.Whole.modulatedEnergy
          (HRS.Whole.rieszKernel d s) X (HRS.Whole.withDensityReal ρ)))
          ∂(Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) :=
        mul_le_mul_left hinv _
    _ = ∫⁻ X in A, ENNReal.ofReal (Real.exp (-β * N * HRS.Whole.modulatedEnergy
          (HRS.Whole.rieszKernel d s) X (HRS.Whole.withDensityReal ρ)))
          ∂(Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) := one_mul _
    _ ≤ _ := by
        refine lintegral_mono fun X => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have hF := wr14b_energy_ge hd hs0 hsd hρ hM hN X
        have hβN : 0 ≤ β * N := mul_nonneg hβ (Nat.cast_nonneg N)
        have : -β * N * HRS.Whole.modulatedEnergy (HRS.Whole.rieszKernel d s) X
            (HRS.Whole.withDensityReal ρ) =
            (β * N) * (-HRS.Whole.modulatedEnergy (HRS.Whole.rieszKernel d s) X
              (HRS.Whole.withDensityReal ρ)) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (by linarith) hβN

/-! ### Linear statistics, small `N` -/

/-- Variance of a sum of i.i.d. coordinates. -/
theorem wr14b_evariance_sum_pi {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (N : ℕ) :
    evariance (fun X : Fin N → Euc d => ∑ i, f (X i)) (Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (N * ∫ x, f x ^ 2 ∂μ) := by
  have hmem : ∀ i : Fin N, MemLp (fun X : Fin N → Euc d => f (X i)) 2 (Measure.pi fun _ : Fin N => μ) :=
    fun i => hf2.comp_measurePreserving (measurePreserving_eval _ i)
  have hS : MemLp (fun X : Fin N → Euc d => ∑ i, f (X i)) 2 (Measure.pi fun _ : Fin N => μ) := by
    have := memLp_finsetSum' (s := Finset.univ) (fun i _ => hmem i)
    convert this using 1
    funext X
    simp [Finset.sum_apply]
  rw [← hS.ofReal_variance_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hv := variance_sum_pi (μ := fun _ : Fin N => μ) (X := fun _ => f) (fun _ => hf2)
  have e : (fun X : Fin N → Euc d => ∑ i, f (X i)) = ∑ i : Fin N, fun ω : Fin N → Euc d => f (ω i) := by
    funext X
    simp [Finset.sum_apply]
  rw [e, hv]
  have h1 : variance f μ ≤ ∫ x, f x ^ 2 ∂μ := by
    have := variance_le_expectation_sq (μ := μ) hf.aestronglyMeasurable
    simpa using this
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N)

/-- Variance of `∑ f(x_i)` under `Q`, every `N ≥ 1`: `≤ e^{β N M_g} N ∫ f²`. -/
theorem wr14b_lin_small (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 < β) {N : ℕ}
    (hN : 0 < N) {f : Euc d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 (HRS.Whole.withDensityReal ρ)) :
    evariance (fun X : Fin N → Euc d => ∑ i, f (X i))
        (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
      ENNReal.ofReal (Real.exp (β * N * HRS.Whole.potentialBound d s M)) *
        ENNReal.ofReal (N * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
  haveI := wr13a_isProb_density hρ
  haveI := wr14a_isProb_Q hd hs0 hsd hρ hM hβ hN
  have hSm : Measurable (fun X : Fin N → Euc d => ∑ i, f (X i)) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  refine (evariance_le_lintegral_sub _ hSm.aestronglyMeasurable
    (∫ X, ∑ i, f (X i) ∂(Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ))).trans ?_
  calc _ ≤ ∫⁻ X, ‖∑ i, f (X i) - ∫ X, ∑ i, f (X i) ∂(Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ)‖ₑ ^ 2
        ∂(ENNReal.ofReal (Real.exp (β * N * HRS.Whole.potentialBound d s M)) •
          Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) :=
        lintegral_mono' (wr14b_Q_le hd hs0 hsd hρ hM hβ.le hN) le_rfl
    _ = ENNReal.ofReal (Real.exp (β * N * HRS.Whole.potentialBound d s M)) *
        evariance (fun X : Fin N → Euc d => ∑ i, f (X i))
          (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) := by
        rw [lintegral_smul_measure, smul_eq_mul]
        rfl
    _ ≤ _ := mul_le_mul' le_rfl (wr14b_evariance_sum_pi hf hf2 N)

/-! ### Linear statistics, large `N` -/

/-- A probability measure with an a.e. bounded Radon-Nikodym derivative is dominated by a multiple of `μ`. -/
theorem wr14b_le_smul_of_rnDeriv {μ π : Measure (Euc d)} [IsFiniteMeasure μ] [IsFiniteMeasure π]
    {C : ℝ} (hac : π ≪ μ) (hb : ∀ᵐ x ∂μ, π.rnDeriv μ x ≤ ENNReal.ofReal C) :
    π ≤ ENNReal.ofReal C • μ := by
  refine Measure.le_iff.2 fun A hA => ?_
  haveI : π.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  have heq : μ.withDensity (π.rnDeriv μ) = π := Measure.withDensity_rnDeriv_eq π μ hac
  rw [← heq, withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  exact lintegral_mono_ae (ae_restrict_of_ae hb)

/-- `∫⁻ ‖f‖² dμ = ofReal ∫ f²` for `f ∈ L²`. -/
theorem wr14b_lintegral_sq {μ : Measure (Euc d)} {f : Euc d → ℝ} (hf2 : MemLp f 2 μ) :
    ∫⁻ z, ‖f z - 0‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf2.integrable_sq (Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun z => ?_
  rw [sub_zero, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- **Linear statistics, `N ≥ N₀`**: `Var_Q(∑ f(x_i)) ≤ C N ∫ f²` (`euc_linear_variance` and the first-marginal
density bound of the reference law). -/
theorem wr14b_lin_large (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (βp M : ℝ) :
    ∃ C : ℝ, ∃ N0 : ℕ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N0 ≤ N → 1 ≤ N → ∀ f : Euc d → ℝ, Measurable f →
        MemLp f 2 (HRS.Whole.withDensityReal ρ) →
        evariance (fun X : Fin N → Euc d => ∑ i, f (X i))
            (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (C * N * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨τ, hτ, N0, hN0, hlv⟩ := euc_linear_variance hd1 hs0 hsd βp M
  haveI := featMap_separableSpace (d := d) hs0 hτ
  obtain ⟨Cπ, hπ⟩ := wr13e_reference_marginal_density_le hd1 hs0 hsd hτ βp M (featMap_hyp hs0 hτ)
  have hk0 : 0 ≤ kTau d s τ 0 := (featMap_hyp hs0 hτ).k_zero_nonneg
  refine ⟨2 * Real.exp (4 * max βp 0 * kTau d s τ 0) * max Cπ 0, N0, ?_⟩
  intro ρ hρ hM β hβ hβp N hN0N hN1 f hf hf2
  haveI := wr13a_isProb_density hρ
  haveI : NeZero N := ⟨by omega⟩
  have hNpos : 0 < N := by omega
  have hT := wr14a_transferHyp hd1 hs0 hsd hτ hρ hM
  haveI hRN : IsProbabilityMeasure (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) (featMap d s τ) β N) := wr11b_isProb_RN hT hβ.le hNpos
  obtain ⟨hac, hrn⟩ := hπ ρ hρ hM β hβ hβp N hN1
  haveI := wr14a_isProb_firstMarginal hNpos
    (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) (featMap d s τ) β N)
  have hle : HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
      (HRS.Whole.withDensityReal ρ) (featMap d s τ) β N) ≤
      ENNReal.ofReal (max Cπ 0) • HRS.Whole.withDensityReal ρ :=
    wr14b_le_smul_of_rnDeriv hac
      (hrn.mono fun x hx => hx.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hmar : (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ)
      (featMap d s τ) β N).map (fun X : Fin N → Euc d => X 0) =
      HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
        (HRS.Whole.withDensityReal ρ) (featMap d s τ) β N) := by
    unfold HRS.Whole.firstMarginal
    rw [dif_pos hNpos]
    rfl
  have hv : evariance f ((RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ)
      (featMap d s τ) β N).map (fun X : Fin N → Euc d => X 0)) ≤
      ENNReal.ofReal (max Cπ 0) * ENNReal.ofReal (∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
    rw [hmar]
    refine (evariance_le_lintegral_sub _ hf.aestronglyMeasurable 0).trans ?_
    calc ∫⁻ z, ‖f z - 0‖ₑ ^ 2 ∂(HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y))
            (HRS.Whole.withDensityReal ρ) (featMap d s τ) β N))
        ≤ ∫⁻ z, ‖f z - 0‖ₑ ^ 2 ∂(ENNReal.ofReal (max Cπ 0) • HRS.Whole.withDensityReal ρ) :=
          lintegral_mono' hle le_rfl
      _ = ENNReal.ofReal (max Cπ 0) * ∫⁻ z, ‖f z - 0‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ = _ := by rw [wr14b_lintegral_sq hf2]
  have hI : 0 ≤ ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) := integral_nonneg fun x => sq_nonneg _
  have hb0 : 0 ≤ max Cπ 0 := le_max_right _ _
  have hE : Real.exp (4 * β * kTau d s τ 0) ≤ Real.exp (4 * max βp 0 * kTau d s τ 0) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hβp.trans (le_max_left _ _)) (by norm_num)) hk0)
  calc _ ≤ _ := hlv ρ hρ hM β hβ hβp N hN0N f hf
    _ ≤ ENNReal.ofReal (Real.exp (4 * β * kTau d s τ 0)) * (2 * (N : ℝ≥0∞) *
        (ENNReal.ofReal (max Cπ 0) * ENNReal.ofReal (∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ)))) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (4 * β * kTau d s τ 0) *
        (2 * N * (max Cπ 0 * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ)))) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hb0, ENNReal.ofReal_natCast]
        simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc Real.exp (4 * β * kTau d s τ 0) *
              (2 * N * (max Cπ 0 * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ)))
            ≤ Real.exp (4 * max βp 0 * kTau d s τ 0) *
              (2 * N * (max Cπ 0 * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ))) :=
              mul_le_mul_of_nonneg_right hE (by positivity)
          _ = _ := by ring

/-! ### The packaged linear clause -/

/-- **Conjunct 2 of `euc_static`** for all `N ≥ 2`, all `f ∈ L²(μ)` (not necessarily measurable). -/
theorem wr14b_linear (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβ : βm ≤ βp) (M : ℝ) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β ∈ Set.Icc βm βp, ∀ N : ℕ, 2 ≤ N → ∀ f : Euc d → ℝ,
        MemLp f 2 (HRS.Whole.withDensityReal ρ) →
        evariance (HRS.Whole.linStat f)
            (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C1, N0, h1⟩ := wr14b_lin_large hd hs0 hsd βp M
  set Ks : ℝ := Real.exp (max βp 0 * N0 * HRS.Whole.potentialBound d s M) with hKs
  refine ⟨max C1 Ks, ?_⟩
  intro ρ hρ hM β hβmem N hN f hf2
  obtain ⟨hβ1, hβ2⟩ := hβmem
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  haveI := wr13a_isProb_density hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set Q := HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β μ with hQ
  -- a measurable representative
  have hfm : AEStronglyMeasurable f μ := hf2.aestronglyMeasurable
  set f' : Euc d → ℝ := hfm.mk f with hf'
  have hf'm : Measurable f' := hfm.stronglyMeasurable_mk.measurable
  have hae : f =ᵐ[μ] f' := hfm.ae_eq_mk
  have hf'2 : MemLp f' 2 μ := hf2.ae_eq hae
  have hint : ∫ x, f' x ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ :=
    integral_congr_ae (hae.mono fun x hx => by simp [hx])
  have hI : 0 ≤ ∫ x, f' x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have ha := wr14b_potentialBound_nonneg hd1 hs0 hsd hρ hM
  -- the bound for the measurable representative
  have hS : evariance (fun X : Fin N → Euc d => ∑ i, f' (X i)) Q ≤
      ENNReal.ofReal (max C1 Ks * N * ∫ x, f' x ^ 2 ∂μ) := by
    by_cases hNN : N0 ≤ N
    · refine (h1 ρ hρ hM β hβpos hβ2 N hNN (by omega) f' hf'm hf'2).trans
        (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hN'.le) hI
    · push Not at hNN
      refine (wr14b_lin_small hd1 hs0 hsd hρ hM hβpos hNpos hf'm hf'2).trans ?_
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp : Real.exp (β * N * HRS.Whole.potentialBound d s M) ≤ max C1 Ks := by
        refine le_trans ?_ (le_max_right _ _)
        refine Real.exp_le_exp.2 ?_
        have hNN' : (N : ℝ) ≤ N0 := by exact_mod_cast hNN.le
        have hβ' : β ≤ max βp 0 := hβ2.trans (le_max_left _ _)
        have h0 : 0 ≤ β * N := by positivity
        calc β * N * HRS.Whole.potentialBound d s M ≤ max βp 0 * N0 * HRS.Whole.potentialBound d s M := by
              refine mul_le_mul_of_nonneg_right ?_ ha
              exact mul_le_mul hβ' hNN' hN'.le (le_trans hβpos.le hβ')
          _ = max βp 0 * N0 * HRS.Whole.potentialBound d s M := rfl
      calc Real.exp (β * N * HRS.Whole.potentialBound d s M) * (N * ∫ x, f' x ^ 2 ∂μ)
          ≤ max C1 Ks * (N * ∫ x, f' x ^ 2 ∂μ) := mul_le_mul_of_nonneg_right hexp (by positivity)
        _ = _ := by ring
  -- a.e. identification of the statistics
  have hQac : Q ≪ Measure.pi fun _ : Fin N => μ :=
    Measure.absolutelyContinuous_of_le_smul (wr14b_Q_le hd1 hs0 hsd hρ hM hβpos.le hNpos)
  have hpi : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ i, f (X i) = f' (X i) := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hae
  have hlin : HRS.Whole.linStat f =ᵐ[Q] fun X : Fin N → Euc d => (N : ℝ)⁻¹ * ∑ i, f' (X i) := by
    filter_upwards [hQac.ae_le hpi] with X hX
    unfold HRS.Whole.linStat
    rw [HRS.Whole.pair_empirical hNpos]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hX i
  rw [evariance_congr hlin, evariance_mul, ← hint]
  calc ENNReal.ofReal (((N : ℝ)⁻¹) ^ 2) * evariance (fun X : Fin N → Euc d => ∑ i, f' (X i)) Q
      ≤ ENNReal.ofReal (((N : ℝ)⁻¹) ^ 2) * ENNReal.ofReal (max C1 Ks * N * ∫ x, f' x ^ 2 ∂μ) :=
        mul_le_mul' le_rfl hS
    _ = ENNReal.ofReal (max C1 Ks / N * ∫ x, f' x ^ 2 ∂μ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end HRS.MS.Wr
