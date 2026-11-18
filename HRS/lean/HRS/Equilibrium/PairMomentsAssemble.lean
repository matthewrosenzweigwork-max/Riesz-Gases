/-
# HRS.Equilibrium.PairMomentsAssemble -- transfer to `P_{N,β}` and assembly (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsPairs

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

section Transfer

variable {α : Type*} [MeasurableSpace α]

/-- Variance transfer: `P ≤ K R` gives `Var_P F ≤ K Var_R F`. -/
theorem evar_transfer_large {P ν : Measure α} [IsProbabilityMeasure P] {K : ℝ}
    (hle : P ≤ ENNReal.ofReal K • ν) {F : α → ℝ} (hF : Measurable F) :
    evariance F P ≤ ENNReal.ofReal K * evariance F ν :=
  evariance_le_of_le_smul hle hF

/-- Crude transfer: `Var_P F ≤ E_P F² ≤ K E_R F²`. -/
theorem evar_transfer_crude {P ν : Measure α} [IsProbabilityMeasure P] {K : ℝ}
    (hle : P ≤ ENNReal.ofReal K • ν) {F : α → ℝ} (hF : Measurable F) :
    evariance F P ≤ ENNReal.ofReal K * (∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν) := by
  have h1 := evariance_le_lintegral_sub P hF.aestronglyMeasurable 0
  simp only [sub_zero] at h1
  refine h1.trans ?_
  calc ∫⁻ x, ‖F x‖ₑ ^ 2 ∂P ≤ ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(ENNReal.ofReal K • ν) := lintegral_mono' hle le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]

end Transfer

section CrudePair

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- Crude variance bound for a scaled ordered pair sum under a measure dominated by the reference. -/
theorem crude_pairSum (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    {v : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry v)) (c : ℝ) {𝒲 : ℝ≥0∞}
    (hW : ∀ x, ∫⁻ z, ‖v x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z)) ∂μ ≤ 𝒲)
    {Q : Measure (Config d (n + 1))} [IsProbabilityMeasure Q] {K' : ℝ}
    (hle : Q ≤ ENNReal.ofReal K' • pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :
    evariance (fun X : Config d (n + 1) => c * pairSumOrdered v X) Q ≤
      ENNReal.ofReal K' * (ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 4) * 𝒲)) := by
  have hF : Measurable (fun X : Config d (n + 1) => c * pairSumOrdered v X) :=
    measurable_const.mul (measurable_pairSumOrdered hm)
  refine (evar_transfer_crude hle hF).trans (mul_le_mul' le_rfl ?_)
  have hS : Measurable fun X : Config d (n + 1) => ‖pairSumOrdered v X‖ₑ ^ 2 :=
    (measurable_pairSumOrdered hm).enorm.pow_const 2
  calc ∫⁻ X, ‖c * pairSumOrdered v X‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      = ENNReal.ofReal (c ^ 2) * ∫⁻ X, ‖pairSumOrdered v X‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
        simp_rw [enorm_sq_mul_real]
        exact lintegral_const_mul _ hS
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_pairSum_sq_le V hβ hm hW)

end CrudePair

section PartBAll

variable {s : ℝ}

/-- Part (b) of Proposition 4.12 for `Q_{N,β}(μ)`, all `N ≥ 2`. -/
theorem partb_all (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℝ) (b : Torus d → Torus d → ℝ), Measurable (Function.uncurry b) →
      (∀ x y, b x y = b y x) → (∀ x y, x ≠ y → |b x y| ≤ K * wEnv s x y ^ 2) → ∀ N : ℕ, 2 ≤ N →
        evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered b X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * K ^ 2 / N) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρs.density
  obtain ⟨c, Cq, Mmax, M'max, γmax, N₁, KQ, δC, C1, Cu, C2, Vf, hc, hCq, hN₁, hKQ, hδC, hC1, hCu, hC2, hVu, hbd,
    hprob, hcrude, hlarge, hlarge2⟩ := exists_setting hd hcrit β hβ ρ hρs
  obtain ⟨C0, hC00, hC0⟩ := pole_w_integrals hd hcrit β hβ ρ hρs c hc Mmax M'max γmax Cq hCq
  obtain ⟨Cb, hCb0, hCb⟩ := partb_ref hd hcrit β hβ ρ hρs c hc Mmax M'max γmax Cq hCq
  choose K' hK'pos hK'le using hcrude
  set Csum : ℝ := ∑ n ∈ Finset.range N₁, K' n * C0 * (N₁ : ℝ) ^ 2 with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun n _ => by have := hK'pos n; positivity
  refine ⟨max (KQ * Cb) Csum, le_trans (by positivity) (le_max_left _ _), fun K b hm hsym hb N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hF : Measurable (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered b X) :=
    measurable_const.mul (measurable_pairSumOrdered hm)
  haveI := hprob n
  have hNp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  by_cases hbig : N₁ ≤ n + 1
  · obtain ⟨hle, hκ, hRD⟩ := hlarge n hbig
    refine (evar_transfer_large hle hF).trans ?_
    have h1 := hCb (Vf n) (hbd n) n (by omega) hκ K b hm hsym hb
    refine (mul_le_mul' le_rfl h1).trans ?_
    rw [← ENNReal.ofReal_mul hKQ.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : KQ * (Cb * K ^ 2 / ((n + 1 : ℕ) : ℝ)) ≤ max (KQ * Cb) Csum * K ^ 2 / ((n + 1 : ℕ) : ℝ) := by
      rw [← mul_div_assoc, ← mul_assoc]
      refine div_le_div_of_nonneg_right ?_ hNp.le
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    exact this
  · push Not at hbig
    have hNlt : n + 1 < N₁ := hbig
    have hbs : ∀ x y, x ≠ y → ‖b x y‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wEnv s x y ^ 4) := by
      intro x y hxy
      rw [← ENNReal.ofReal_mul (sq_nonneg _), ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 := pow_le_pow_left₀ (abs_nonneg _) (hb x y hxy) 2
      rw [sq_abs] at h2
      calc b x y ^ 2 ≤ (K * wEnv s x y ^ 2) ^ 2 := h2
        _ = _ := by ring
    have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
    have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := fun x => PoleVar.ae_ne_pt hatom x
    have hW : ∀ x : Torus d, ∫⁻ z, ‖b x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((Vf n).M' + β * (Vf n).γ +
        pinField (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z))
        ∂(withDensityReal ρ) ≤ ENNReal.ofReal (K ^ 2 * (C0 * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
      intro x
      calc _ ≤ ∫⁻ y, (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wEnv s x y ^ 4)) *
            ENNReal.ofReal (Real.exp ((Vf n).M' + β * (Vf n).γ +
              pinField (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
            ∂(withDensityReal ρ) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae x] with y hy
            exact mul_le_mul' (hbs x y (Ne.symm hy)) le_rfl
        _ = ENNReal.ofReal (K ^ 2) * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4) *
            ENNReal.ofReal (Real.exp ((Vf n).M' + β * (Vf n).γ +
              pinField (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
            ∂(withDensityReal ρ) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun y => ?_
            rw [mul_assoc]
        _ ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (C0 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
            gcongr
            exact (hC0 (Vf n) (hbd n) (n + 1) (by omega) x).2
        _ = _ := (ENNReal.ofReal_mul (sq_nonneg _)).symm
    obtain ⟨hle⟩ : Nonempty (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤
        ENNReal.ofReal (K' n) • pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
      ⟨hK'le n⟩
    have hcr := crude_pairSum (Vf n) hβ.le hm (((n + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) hW hle
    refine hcr.trans ?_
    have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) ^ 2 = 1 / ((n + 1 : ℕ) : ℝ) ^ 5 := by
      rw [rpow_sq_neg (n + 1) (by omega)]
      have : (2 * (5 / 2 : ℝ)) = ((5 : ℕ) : ℝ) := by norm_num
      rw [this, Real.rpow_natCast]
    rw [hc2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by have := hK'pos n; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hKn := hK'pos n
    have hNN1 : ((n + 1 : ℕ) : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hNlt.le
    have hterm : K' n * C0 * (N₁ : ℝ) ^ 2 ≤ Csum := by
      rw [hCsum]
      exact Finset.single_le_sum (f := fun n => K' n * C0 * (N₁ : ℝ) ^ 2)
        (fun n _ => by have := hK'pos n; positivity) (Finset.mem_range.2 (by omega))
    have e : K' n * (1 / ((n + 1 : ℕ) : ℝ) ^ 5 * (((n + 1 : ℕ) : ℝ) ^ 4 * (K ^ 2 * (C0 * ((n + 1 : ℕ) : ℝ) ^ 2))))
        = (K' n * C0 * K ^ 2) * ((n + 1 : ℕ) : ℝ) := by
      field_simp
    rw [e]
    have h2 : (K' n * C0 * K ^ 2) * ((n + 1 : ℕ) : ℝ) ≤ (K' n * C0 * (N₁ : ℝ) ^ 2) * K ^ 2 / ((n + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hNp]
      have : ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ (N₁ : ℝ) ^ 2 := by nlinarith
      have h3 : 0 ≤ K' n * C0 * K ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h3]
    refine h2.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hterm.trans (le_max_right _ _)) (sq_nonneg _)) hNp.le

end PartBAll

section PartJAll

variable {s : ℝ}

/-- Part (j) of Proposition 4.12 for `Q_{N,β}(μ)`, all `N ≥ 2`. -/
theorem partj_all (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℝ) (j : Torus d → Torus d → ℝ), Measurable (Function.uncurry j) →
      (∀ x y, j x y = j y x) → IsCanonicalPair (withDensityReal ρ) j →
      (∀ x y, x ≠ y → |j x y| ≤ K * wEnv s x y) → ∀ N : ℕ, 2 ≤ N →
        evariance (fun X : Config d N => (N : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered j X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * K ^ 2 * logEN N / N) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρs.density
  obtain ⟨c, Cq, Mmax, M'max, γmax, N₁, KQ, δC, C1, Cu, C2, Vf, hc, hCq, hN₁, hKQ, hδC, hC1, hCu, hC2, hVu, hbd,
    hprob, hcrude, hlarge, hlarge2⟩ := exists_setting hd hcrit β hβ ρ hρs
  obtain ⟨C0, hC00, hC0⟩ := pole_w_integrals hd hcrit β hβ ρ hρs c hc Mmax M'max γmax Cq hCq
  obtain ⟨Cj, hCj0, hCj⟩ := partj_ref hd hcrit β hβ ρ hρs c hc Mmax M'max γmax Cq hCq Cu hCu δC C1 hδC hC1
  choose K' hK'pos hK'le using hcrude
  set Csum : ℝ := ∑ n ∈ Finset.range N₁, K' n * C0 * (N₁ : ℝ) ^ 2 with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun n _ => by have := hK'pos n; positivity
  refine ⟨max (KQ * Cj) Csum, le_trans (by positivity) (le_max_left _ _),
    fun K j hm hsym hcan hj N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hF : Measurable (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered j X) :=
    measurable_const.mul (measurable_pairSumOrdered hm)
  haveI := hprob n
  have hNp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hL1 := logEN_pos' (N := n + 1) (by omega)
  by_cases hbig : N₁ ≤ n + 1
  · obtain ⟨hle, hκ, hRD⟩ := hlarge n hbig
    refine (evar_transfer_large hle hF).trans ?_
    have h1 := hCj (Vf n) (hbd n) (hVu n) n (by omega) hκ hRD K j hm hsym hcan hj
    refine (mul_le_mul' le_rfl h1).trans ?_
    rw [← ENNReal.ofReal_mul hKQ.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : KQ * (Cj * K ^ 2 * logEN (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤
        max (KQ * Cj) Csum * K ^ 2 * logEN (n + 1) / ((n + 1 : ℕ) : ℝ) := by
      rw [← mul_div_assoc, ← mul_assoc, ← mul_assoc]
      refine div_le_div_of_nonneg_right ?_ hNp.le
      have : 0 ≤ K ^ 2 * logEN (n + 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left (KQ * Cj) Csum) this]
    exact this
  · push Not at hbig
    have hNlt : n + 1 < N₁ := hbig
    have hbs : ∀ x y, x ≠ y → ‖j x y‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wEnv s x y ^ 2) := by
      intro x y hxy
      rw [← ENNReal.ofReal_mul (sq_nonneg _), ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 := pow_le_pow_left₀ (abs_nonneg _) (hj x y hxy) 2
      rw [sq_abs] at h2
      calc j x y ^ 2 ≤ (K * wEnv s x y) ^ 2 := h2
        _ = _ := by ring
    have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
    have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := fun x => PoleVar.ae_ne_pt hatom x
    have hW : ∀ x : Torus d, ∫⁻ z, ‖j x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((Vf n).M' + β * (Vf n).γ +
        pinField (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z))
        ∂(withDensityReal ρ) ≤ ENNReal.ofReal (K ^ 2 * (C0 * logEN (n + 1))) := by
      intro x
      calc _ ≤ ∫⁻ y, (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wEnv s x y ^ 2)) *
            ENNReal.ofReal (Real.exp ((Vf n).M' + β * (Vf n).γ +
              pinField (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
            ∂(withDensityReal ρ) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae x] with y hy
            exact mul_le_mul' (hbs x y (Ne.symm hy)) le_rfl
        _ = ENNReal.ofReal (K ^ 2) * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2) *
            ENNReal.ofReal (Real.exp ((Vf n).M' + β * (Vf n).γ +
              pinField (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
            ∂(withDensityReal ρ) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun y => ?_
            rw [mul_assoc]
        _ ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (C0 * logEN (n + 1)) := by
            gcongr
            exact (hC0 (Vf n) (hbd n) (n + 1) (by omega) x).1
        _ = _ := (ENNReal.ofReal_mul (sq_nonneg _)).symm
    obtain ⟨hle⟩ : Nonempty (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤
        ENNReal.ofReal (K' n) • pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
      ⟨hK'le n⟩
    have hcr := crude_pairSum (Vf n) hβ.le hm (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) hW hle
    refine hcr.trans ?_
    have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / ((n + 1 : ℕ) : ℝ) ^ 3 := by
      rw [rpow_sq_neg (n + 1) (by omega)]
      have : (2 * (3 / 2 : ℝ)) = ((3 : ℕ) : ℝ) := by norm_num
      rw [this, Real.rpow_natCast]
    rw [hc2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by have := hK'pos n; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hKn := hK'pos n
    have hterm : K' n * C0 * (N₁ : ℝ) ^ 2 ≤ Csum := by
      rw [hCsum]
      exact Finset.single_le_sum (f := fun n => K' n * C0 * (N₁ : ℝ) ^ 2)
        (fun n _ => by have := hK'pos n; positivity) (Finset.mem_range.2 (by omega))
    have hNN1 : ((n + 1 : ℕ) : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hNlt.le
    have e : K' n * (1 / ((n + 1 : ℕ) : ℝ) ^ 3 * (((n + 1 : ℕ) : ℝ) ^ 4 * (K ^ 2 * (C0 * logEN (n + 1)))))
        = (K' n * C0 * K ^ 2 * logEN (n + 1)) * ((n + 1 : ℕ) : ℝ) := by
      field_simp
    rw [e]
    have h2 : (K' n * C0 * K ^ 2 * logEN (n + 1)) * ((n + 1 : ℕ) : ℝ) ≤
        (K' n * C0 * (N₁ : ℝ) ^ 2) * K ^ 2 * logEN (n + 1) / ((n + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hNp]
      have : ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ (N₁ : ℝ) ^ 2 := by nlinarith
      have h3 : 0 ≤ K' n * C0 * K ^ 2 * logEN (n + 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h3]
    refine h2.trans ?_
    refine div_le_div_of_nonneg_right ?_ hNp.le
    have : 0 ≤ K ^ 2 * logEN (n + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (hterm.trans (le_max_right (KQ * Cj) Csum)) this]

end PartJAll

section PartPsiAll

variable {s : ℝ}

/-- Variance part of statement (psi) of Proposition 4.12 for `Q_{N,β}(μ)`, all `N ≥ 2`. -/
theorem partpsi_all (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), Measurable (Function.uncurry ψ) →
      (∀ x y, ψ x y = ψ y x) → IsCanonicalPair (withDensityReal ρ) ψ →
      (∀ x y, x ≠ y → |ψ x y| ≤ K * psiEnv s x y) → ∀ N : ℕ, 2 ≤ N →
        evariance (fun X : Config d N => (N : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered ψ X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * K ^ 2 / N) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρs.density
  obtain ⟨c, Cq, Mmax, M'max, γmax, N₁, KQ, δC, C1, Cu, C2, Vf, hc, hCq, hN₁, hKQ, hδC, hC1, hCu, hC2, hVu, hbd,
    hprob, hcrude, hlarge, hlarge2⟩ := exists_setting hd hcrit β hβ ρ hρs
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρs
  obtain ⟨BA, BB, BC, hBA, hBB, hBC, hEnv⟩ := psiEnv_bounds (d := d) hd hcrit Cu hCu ρ hΛ hΛ0.le
  obtain ⟨Cj, hCj0, hCj⟩ := pairVar_noLog hd hcrit β hβ ρ hρs c Mmax M'max γmax Cq Cu hCu δC C1 hδC hC1
    (measurable_psiEnv s) hBA hBB hBC hEnv
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  choose K' hK'pos hK'le using hcrude
  set Csum : ℝ := ∑ n ∈ Finset.range N₁, K' n * (E0 * BB) * (N₁ : ℝ) ^ 2 with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun n _ => by have := hK'pos n; positivity
  refine ⟨max (KQ * Cj) Csum, le_trans (by positivity) (le_max_left _ _),
    fun K ψ hm hsym hcan hψ N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hF : Measurable (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered ψ X) :=
    measurable_const.mul (measurable_pairSumOrdered hm)
  haveI := hprob n
  have hNp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  by_cases hbig : N₁ ≤ n + 1
  · obtain ⟨hle, hκ, hRD⟩ := hlarge n hbig
    refine (evar_transfer_large hle hF).trans ?_
    have h1 := hCj (Vf n) (hbd n) (hVu n) n (by omega) hκ hRD K ψ hm hsym hcan hψ
    refine (mul_le_mul' le_rfl h1).trans ?_
    rw [← ENNReal.ofReal_mul hKQ.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : KQ * (Cj * K ^ 2 / ((n + 1 : ℕ) : ℝ)) ≤ max (KQ * Cj) Csum * K ^ 2 / ((n + 1 : ℕ) : ℝ) := by
      rw [← mul_div_assoc, ← mul_assoc]
      refine div_le_div_of_nonneg_right ?_ hNp.le
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    exact this
  · push Not at hbig
    have hNlt : n + 1 < N₁ := hbig
    have hW : ∀ x : Torus d, ∫⁻ z, ‖ψ x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((Vf n).M' + β * (Vf n).γ +
        pinField (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z))
        ∂(withDensityReal ρ) ≤ ENNReal.ofReal (K ^ 2 * (E0 * BB)) := fun x =>
      varInt_noLog hd β hβ ρ hρs c Mmax M'max γmax Cq (N := n + 1) (by omega) (Vf n) (hbd n) hBB hEnv K hψ x _ rfl
    obtain ⟨hle⟩ : Nonempty (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤
        ENNReal.ofReal (K' n) • pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
      ⟨hK'le n⟩
    have hcr := crude_pairSum (Vf n) hβ.le hm (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) hW hle
    refine hcr.trans ?_
    have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / ((n + 1 : ℕ) : ℝ) ^ 3 := by
      rw [rpow_sq_neg (n + 1) (by omega)]
      have : (2 * (3 / 2 : ℝ)) = ((3 : ℕ) : ℝ) := by norm_num
      rw [this, Real.rpow_natCast]
    rw [hc2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by have := hK'pos n; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hKn := hK'pos n
    have hterm : K' n * (E0 * BB) * (N₁ : ℝ) ^ 2 ≤ Csum := by
      rw [hCsum]
      exact Finset.single_le_sum (f := fun n => K' n * (E0 * BB) * (N₁ : ℝ) ^ 2)
        (fun n _ => by have := hK'pos n; positivity) (Finset.mem_range.2 (by omega))
    have hNN1 : ((n + 1 : ℕ) : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hNlt.le
    have e : K' n * (1 / ((n + 1 : ℕ) : ℝ) ^ 3 * (((n + 1 : ℕ) : ℝ) ^ 4 * (K ^ 2 * (E0 * BB))))
        = (K' n * (E0 * BB) * K ^ 2) * ((n + 1 : ℕ) : ℝ) := by
      field_simp
    rw [e]
    have h2 : (K' n * (E0 * BB) * K ^ 2) * ((n + 1 : ℕ) : ℝ) ≤
        (K' n * (E0 * BB) * (N₁ : ℝ) ^ 2) * K ^ 2 / ((n + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hNp]
      have : ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ (N₁ : ℝ) ^ 2 := by nlinarith
      have h3 : 0 ≤ K' n * (E0 * BB) * K ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h3]
    refine h2.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hterm.trans (le_max_right _ _)) (sq_nonneg _)) hNp.le

end PartPsiAll

end HRS.PairMom

end
