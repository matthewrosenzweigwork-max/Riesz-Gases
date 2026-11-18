import HRS.Equilibrium.PairMomentsEnergy
import HRS.ME.NfUPU1bB

/-!
# Packet PU8, part B (uniform reference energy bounds `energy_ref_crude`, `energy_ref_large`)

Uniform copies (namespace `HRS.ME.NfU`) of the following lemmas (rule in `docs/MAIN_E_NF_PLAN.md`; conventions as in
`NfUPU8.lean`).  Fixed data: `d, s, βm, βp, c₀, Λ₀` with `0 < βm`, `βm ≤ βp`, `1 ≤ Λ₀`, and the setting parameters
of the original statement.  The constant is chosen before `β ∈ Set.Icc βm βp` and before `ρ`; the thermal
hypothesis is `RhoU d βm βp c₀ Λ₀ β ρ`.

* `energy_ref_crude_unif` of `HRS.PairMom.energy_ref_crude` (PairMomentsEnergy l.265).  The envelope constants
  `BA, BB` come from `gradEnv_bounds_unif` (uniform in `ρ` for `ρ ≤ Λ₀`), `ρ ≤ Λ₀` is `RhoU.hup`.
* `energy_ref_large_unif` of `HRS.PairMom.energy_ref_large` (PairMomentsEnergy l.161).  Same envelope source.
* In both, the prefactor `exp (M'max + β max γmax 0 + Mmax)` is bounded by its value at `βp` (`E0`), using
  `varInt_noLog` resp. `rowData_noLog` (at the given `β`, `ρ`) and a monotone conversion.
* `Hypotheses on V mentioning β` (`weakKappa V β`, `RefDens V β n _ _`) stay on `V`, after `β`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.External HRS.Quad HRS.External.PoleVar HRS.PairMom HRS.PairCorrAux HRS.PoleCavityAux
  HRS.ME.PmU

variable {d : ℕ}

/-- Uniform `energy_ref_large`: the constant `d (8 Vc + 16 Cm²)(1 + BA)²` with `Vc = E0 BB`, `E0` the value of the
pole prefactor at `βp`, is chosen after the fixed data and the envelope constants `BA, BB, BC` of `gradEnv_bounds_unif`. -/
theorem energy_ref_large_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c Mmax M'max γmax Cq : ℝ) (Cu : ℝ) (hCu : 0 ≤ Cu)
    (δC C1 : ℝ) (hδC : 0 ≤ δC) (hC1 : 0 ≤ C1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V →
      (∀ x y : Torus d, x ≠ y → V.q x y ≤ Cu * wEnv s x y) → ∀ n : ℕ, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      RefDens V β n (δC * deltaN d s (n + 1)) C1 →
      ∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), (∀ x y, ψ x y = ψ y x) →
      IsCanonicalPair (withDensityReal ρ) ψ →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d) →
      (∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
        K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s))) →
        ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
            ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * K ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨BA, BB, BC, hBA0, hBB0, hBC0, hEnvU⟩ := gradEnv_bounds_unif hd hcrit Cu hCu Λ₀ hΛ
  set E0 : ℝ := Real.exp (M'max + βp * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set Cm : ℝ := δC * BA + C1 * BC with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set Vc : ℝ := E0 * BB with hVc
  have hVc0 : 0 ≤ Vc := by positivity
  refine ⟨d * (8 * Vc + 16 * Cm ^ 2) * (1 + BA) ^ 2, by positivity,
    fun β hβI ρ hU V hV hVu n hn hκ hRD K ψ hsymm hcan hsm hgrad => ?_⟩
  have hβ : 0 < β := hU.hβpos
  have hβle : β ≤ βp := hU.hβle
  have hρ : SmoothPosDensity ρ := hU.rho
  have hEnv := hEnvU ρ hU.hup
  have hE0le : Real.exp (M'max + β * max γmax 0 + Mmax) ≤ E0 := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hβle (le_max_right γmax 0)
    linarith
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  set N : ℕ := n + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnR : (n : ℝ) ≤ N := by simp [hNdef]
  haveI : NeZero n := ⟨by omega⟩
  have hL2 := logEN_sq_le (N := N) hN1
  have hL0 : 0 ≤ logEN N := by linarith [logEN_pos' (N := N) hN1]
  set K' : ℝ := |K| * (1 + BA) with hK'
  have hker := fun m : Fin d => corrected_kernel hd hcrit hρ hBA0 hEnv.A hcan hsm hgrad m
  have hae := energy_ae_eq V hβ.le (n := n) hatom hsymm hsm (fun m => (hker m).2.2.2)
  have hrow : ∀ (m : Fin d) (i : Fin (n + 1)),
      ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal (2 * n) * ENNReal.ofReal (K' ^ 2 * Vc) + ENNReal.ofReal ((|K'| * Cm * logEN N) ^ 2) := by
    intro m i
    obtain ⟨hm, hcm, hbd, -⟩ := hker m
    obtain ⟨hV1raw, hM1⟩ := rowData_noLog hd β hβ ρ hρ c Mmax M'max γmax Cq Cu hCu δC C1 hδC hC1 hcrit V hV hVu hn hRD
      (measurable_gradEnv s) hBA0 hBB0 hBC0 hEnv K' hm hcm hbd
    have hV1 : ∀ x : Torus d, ∫⁻ y, ‖vcorr (withDensityReal ρ) ψ m x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (K' ^ 2 * Vc) := fun x =>
      (hV1raw x).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE0le hBB0) (sq_nonneg K')))
    exact row_moment_le V hβ.le hκ hm i (Eventually.of_forall hV1) (Eventually.of_forall hM1)
  have hmeasRow : ∀ (m : Fin d) (i : Fin (n + 1)), Measurable fun Y : Config d (n + 1) =>
      ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2 :=
    fun m i => (measurable_rowSum (hker m).1 i).enorm.pow_const 2
  set a2 : ℝ := 4 * (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 with ha2
  set Bd : ℝ≥0∞ := ENNReal.ofReal (2 * n) * ENNReal.ofReal (K' ^ 2 * Vc) +
    ENNReal.ofReal ((|K'| * Cm * logEN N) ^ 2) with hBd
  calc ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      = ∫⁻ X, ∑ i : Fin (n + 1), ∑ m : Fin d, ENNReal.ofReal a2 *
          ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (X i) (X j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with X hX
        exact Finset.sum_congr rfl fun i _ => hX i
    _ = ∑ i : Fin (n + 1), ∑ m : Fin d, ENNReal.ofReal a2 * ∫⁻ X,
          ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (X i) (X j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
        rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ fun m _ => (hmeasRow m i).const_mul _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ (fun m _ => (hmeasRow m i).const_mul _)]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [lintegral_const_mul _ (hmeasRow m i)]
    _ ≤ ∑ _i : Fin (n + 1), ∑ _m : Fin d, ENNReal.ofReal a2 * Bd := by
        gcongr with i _ m _
        exact hrow m i
    _ = ENNReal.ofReal (a2 * ((N : ℝ) * d * (2 * n * (K' ^ 2 * Vc) + (|K'| * Cm * logEN N) ^ 2))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : (0 : ℝ) ≤ 2 * n := by positivity
        rw [hBd, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [show ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by rw [ENNReal.ofReal_natCast],
          show ((d : ℕ) : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) by rw [ENNReal.ofReal_natCast]]
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := real_psi (N : ℝ) (n : ℝ) Vc K' (logEN N) (|K'| * Cm * logEN N) Cm (by exact_mod_cast hN1)
          (Nat.cast_nonneg n) hnR hVc0 hL2 hCm0 (by positivity) le_rfl
        have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 3 := by
          rw [rpow_sq_neg N (by omega)]
          have : (2 * (3 / 2 : ℝ)) = ((3 : ℕ) : ℝ) := by norm_num
          rw [this, Real.rpow_natCast]
        have hK'2 : K' ^ 2 = K ^ 2 * (1 + BA) ^ 2 := by
          rw [hK', mul_pow, sq_abs]
        rw [ha2, hc2]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have e : 4 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * d * (2 * n * (K' ^ 2 * Vc) + (|K'| * Cm * logEN N) ^ 2)) =
            (d / 2) * (8 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * (2 * n * (K' ^ 2 * Vc) + (|K'| * Cm * logEN N) ^ 2))) := by
          ring
        rw [e]
        calc (d / 2) * (8 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * (2 * n * (K' ^ 2 * Vc) + (|K'| * Cm * logEN N) ^ 2)))
            ≤ (d / 2) * ((16 * Vc + 32 * Cm ^ 2) * K' ^ 2 / N) := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = d * (8 * Vc + 16 * Cm ^ 2) * (1 + BA) ^ 2 * K ^ 2 / N := by rw [hK'2]; ring

/-- Uniform `energy_ref_crude`: the constant `4 d Vc (1 + BA)²`, `Vc = E0 BB` with `E0` the pole prefactor at `βp`,
is chosen after the fixed data and the envelope constants of `gradEnv_bounds_unif`. -/
theorem energy_ref_crude_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c Mmax M'max γmax Cq : ℝ) (Cu : ℝ) (hCu : 0 ≤ Cu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ n : ℕ, 1 ≤ n →
      ∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), (∀ x y, ψ x y = ψ y x) →
      IsCanonicalPair (withDensityReal ρ) ψ →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d) →
      (∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
        K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s))) →
        ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
            ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * K ^ 2) := by
  obtain ⟨BA, BB, BC, hBA0, hBB0, hBC0, hEnvU⟩ := gradEnv_bounds_unif hd hcrit Cu hCu Λ₀ hΛ
  set E0 : ℝ := Real.exp (M'max + βp * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set Vc : ℝ := E0 * BB with hVc
  have hVc0 : 0 ≤ Vc := by positivity
  refine ⟨4 * d * Vc * (1 + BA) ^ 2, by positivity,
    fun β hβI ρ hU V hV n hn K ψ hsymm hcan hsm hgrad => ?_⟩
  have hβ : 0 < β := hU.hβpos
  have hβle : β ≤ βp := hU.hβle
  have hρ : SmoothPosDensity ρ := hU.rho
  have hEnv := hEnvU ρ hU.hup
  have hE0le : Real.exp (M'max + β * max γmax 0 + Mmax) ≤ E0 := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hβle (le_max_right γmax 0)
    linarith
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  set N : ℕ := n + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnR : (n : ℝ) ≤ N := by simp [hNdef]
  set K' : ℝ := |K| * (1 + BA) with hK'
  have hker := fun m : Fin d => corrected_kernel hd hcrit hρ hBA0 hEnv.A hcan hsm hgrad m
  have hae := energy_ae_eq V hβ.le (n := n) hatom hsymm hsm (fun m => (hker m).2.2.2)
  have hrow : ∀ (m : Fin d) (i : Fin (n + 1)),
      ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal ((n : ℝ) ^ 2) * ENNReal.ofReal (K' ^ 2 * Vc) := by
    intro m i
    obtain ⟨hm, hcm, hbd, -⟩ := hker m
    have hW : ∀ x : Torus d, ∫⁻ z, ‖vcorr (withDensityReal ρ) ψ m x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z)) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (K' ^ 2 * Vc) := fun x =>
      (varInt_noLog hd β hβ ρ hρ c Mmax M'max γmax Cq hN1 V hV hBB0 hEnv K' hbd x _ rfl).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE0le hBB0) (sq_nonneg K')))
    have hmeasP : ∀ a b : Fin (n + 1), Measurable fun Y : Config d (n + 1) =>
        ‖vcorr (withDensityReal ρ) ψ m (Y a) (Y b)‖ₑ ^ 2 :=
      fun a b => ((measurable_h_pair hm a b).enorm).pow_const 2
    calc ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
        ≤ ∫⁻ Y, ENNReal.ofReal ((Finset.univ.erase i).card : ℝ) *
            ∑ j ∈ Finset.univ.erase i, ‖vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
          lintegral_mono fun Y => enorm_sq_sum_le _ _
      _ = ENNReal.ofReal ((Finset.univ.erase i).card : ℝ) * ∑ j ∈ Finset.univ.erase i, ∫⁻ Y,
            ‖vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
          rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j _ => hmeasP i j),
            lintegral_finsetSum _ (fun j _ => hmeasP i j)]
      _ ≤ ENNReal.ofReal ((Finset.univ.erase i).card : ℝ) * ∑ _j ∈ Finset.univ.erase i,
            ENNReal.ofReal (K' ^ 2 * Vc) := by
          gcongr with j hj
          exact pair_lintegral_le V hβ.le i j (Finset.ne_of_mem_erase hj).symm hm hW
      _ = ENNReal.ofReal ((n : ℝ) ^ 2) * ENNReal.ofReal (K' ^ 2 * Vc) := by
          have hcard : (Finset.univ.erase i).card = n := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]; rfl
          rw [Finset.sum_const, hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring
  have hmeasRow : ∀ (m : Fin d) (i : Fin (n + 1)), Measurable fun Y : Config d (n + 1) =>
      ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2 :=
    fun m i => (measurable_rowSum (hker m).1 i).enorm.pow_const 2
  set a2 : ℝ := 4 * (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 with ha2
  calc ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      = ∫⁻ X, ∑ i : Fin (n + 1), ∑ m : Fin d, ENNReal.ofReal a2 *
          ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (X i) (X j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with X hX
        exact Finset.sum_congr rfl fun i _ => hX i
    _ = ∑ i : Fin (n + 1), ∑ m : Fin d, ENNReal.ofReal a2 * ∫⁻ X,
          ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (X i) (X j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
        rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ fun m _ => (hmeasRow m i).const_mul _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ (fun m _ => (hmeasRow m i).const_mul _)]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [lintegral_const_mul _ (hmeasRow m i)]
    _ ≤ ∑ _i : Fin (n + 1), ∑ _m : Fin d, ENNReal.ofReal a2 *
          (ENNReal.ofReal ((n : ℝ) ^ 2) * ENNReal.ofReal (K' ^ 2 * Vc)) := by
        gcongr with i _ m _
        exact hrow m i
    _ = ENNReal.ofReal (a2 * ((N : ℝ) * d * ((n : ℝ) ^ 2 * (K' ^ 2 * Vc)))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_mul (by positivity)]
        rw [show ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by rw [ENNReal.ofReal_natCast],
          show ((d : ℕ) : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) by rw [ENNReal.ofReal_natCast]]
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 3 := by
          rw [rpow_sq_neg N (by omega)]
          have : (2 * (3 / 2 : ℝ)) = ((3 : ℕ) : ℝ) := by norm_num
          rw [this, Real.rpow_natCast]
        have hK'2 : K' ^ 2 = K ^ 2 * (1 + BA) ^ 2 := by
          rw [hK', mul_pow, sq_abs]
        rw [ha2, hc2]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hn2 : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hn0 hnR 2
        have hP : 0 ≤ d * (K' ^ 2 * Vc) := by positivity
        have e : 4 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * d * ((n : ℝ) ^ 2 * (K' ^ 2 * Vc))) =
            4 * ((n : ℝ) ^ 2 / (N : ℝ) ^ 2) * (d * (K' ^ 2 * Vc)) := by
          field_simp
        rw [e]
        have h5 : (n : ℝ) ^ 2 / (N : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]; exact hn2
        calc 4 * ((n : ℝ) ^ 2 / (N : ℝ) ^ 2) * (d * (K' ^ 2 * Vc)) ≤ 4 * 1 * (d * (K' ^ 2 * Vc)) := by
              gcongr
          _ = 4 * d * Vc * (1 + BA) ^ 2 * K ^ 2 := by rw [hK'2]; ring

end HRS.ME.NfU
