import HRS.ME.NfUPU7
import HRS.ME.NfUPU8
import HRS.ME.NfUPU1bB
import HRS.Equilibrium.PairMomentsAssemble

/-!
# Packet PU10a (uniform `partb_all`, `partj_all`, `partpsi_all`)

Uniform copies (namespace `HRS.ME.NfU`) of the three lemmas of `HRS/Equilibrium/PairMomentsAssemble.lean`
(rule for uniform statements in `docs/MAIN_E_NF_PLAN.md`):

* `partb_all_unif` of `HRS.PairMom.partb_all` (PairMomentsAssemble l.75),
* `partj_all_unif` of `HRS.PairMom.partj_all` (PairMomentsAssemble l.179),
* `partpsi_all_unif` of `HRS.PairMom.partpsi_all` (PairMomentsAssemble l.291).

Fixed data: `d, s` (with `hd`, `hcrit`), `βm βp c₀ Λ₀` with `0 < βm`, `βm ≤ βp`, `1 ≤ Λ₀`, `0 < c₀`.
The constant `C` is chosen before `β ∈ Set.Icc βm βp` and before `ρ`; it is built from the setting constants of
`exists_setting_unif` (including the fixed sequence `K'`), from `pole_w_integrals_unif`, `partb_ref_unif`,
`partj_ref_unif`, `psiEnv_bounds_unif`, `pairVar_noLog_unif`.  The thermal hypothesis is
`RhoU d βm βp c₀ Λ₀ β ρ` (it replaces `SmoothPosDensity ρ` and `0 < β`; `RhoU` gives `ρ ≤ Λ₀`, `c₀ ≤ ρ`).

Only `V` (the potential `Vf n` from the setting) depends on `(β, ρ)`; the prefactor `exp (M'max + β γmax⁺ + Mmax)`
is bounded by its value at `βp` (`E0`, monotone in `β`); the variance integral `varInt_noLog` is converted by the
same monotone bound.  No hypothesis beyond `RhoU` is added.
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

/-- Uniform `partb_all` (`HRS/Equilibrium/PairMomentsAssemble.lean` l.75). -/
theorem partb_all_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (K : ℝ) (b : Torus d → Torus d → ℝ), Measurable (Function.uncurry b) →
      (∀ x y, b x y = b y x) → (∀ x y, x ≠ y → |b x y| ≤ K * wEnv s x y ^ 2) → ∀ N : ℕ, 2 ≤ N →
        evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered b X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * K ^ 2 / N) := by
  obtain ⟨c, Cq, Mmax, M'max, γmax, N₁, KQ, δC, C1, Cu, C2, K', hc, hCq, hN₁, hKQ, hδC, hC1, hCu, hC2,
    hK'pos, hset⟩ := exists_setting_unif hd hcrit hβm hββ hc₀ hΛ
  obtain ⟨C0, hC00, hC0⟩ := pole_w_integrals_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  obtain ⟨Cb, hCb0, hCb⟩ := partb_ref_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  set Csum : ℝ := ∑ n ∈ Finset.range N₁, K' n * C0 * (N₁ : ℝ) ^ 2 with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun n _ => by have := hK'pos n; positivity
  refine ⟨max (KQ * Cb) Csum, le_trans (by positivity) (le_max_left _ _),
    fun β hβI ρ U K b hm hsym hb N hN => ?_⟩
  obtain ⟨Vf, hVu, hbd, hprob, hcrude, hlarge, -⟩ := hset β hβI ρ U
  have hβ : 0 < β := U.hβpos
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal U.rho.density
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hF : Measurable (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered b X) :=
    measurable_const.mul (measurable_pairSumOrdered hm)
  haveI := hprob n
  have hNp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  by_cases hbig : N₁ ≤ n + 1
  · obtain ⟨hle, hκ, hRD⟩ := hlarge n hbig
    refine (evar_transfer_large hle hF).trans ?_
    have h1 := hCb β hβI ρ U (Vf n) (hbd n) n (by omega) hκ K b hm hsym hb
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
            exact (hC0 β hβI ρ U (Vf n) (hbd n) (n + 1) (by omega) x).2
        _ = _ := (ENNReal.ofReal_mul (sq_nonneg _)).symm
    have hle := hcrude n
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

/-- Uniform `partj_all` (`HRS/Equilibrium/PairMomentsAssemble.lean` l.179). -/
theorem partj_all_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (K : ℝ) (j : Torus d → Torus d → ℝ), Measurable (Function.uncurry j) →
      (∀ x y, j x y = j y x) → IsCanonicalPair (withDensityReal ρ) j →
      (∀ x y, x ≠ y → |j x y| ≤ K * wEnv s x y) → ∀ N : ℕ, 2 ≤ N →
        evariance (fun X : Config d N => (N : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered j X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * K ^ 2 * logEN N / N) := by
  obtain ⟨c, Cq, Mmax, M'max, γmax, N₁, KQ, δC, C1, Cu, C2, K', hc, hCq, hN₁, hKQ, hδC, hC1, hCu, hC2,
    hK'pos, hset⟩ := exists_setting_unif hd hcrit hβm hββ hc₀ hΛ
  obtain ⟨C0, hC00, hC0⟩ := pole_w_integrals_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  obtain ⟨Cj, hCj0, hCj⟩ := partj_ref_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq Cu hCu
    δC C1 hδC hC1
  set Csum : ℝ := ∑ n ∈ Finset.range N₁, K' n * C0 * (N₁ : ℝ) ^ 2 with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun n _ => by have := hK'pos n; positivity
  refine ⟨max (KQ * Cj) Csum, le_trans (by positivity) (le_max_left _ _),
    fun β hβI ρ U K j hm hsym hcan hj N hN => ?_⟩
  obtain ⟨Vf, hVu, hbd, hprob, hcrude, hlarge, -⟩ := hset β hβI ρ U
  have hβ : 0 < β := U.hβpos
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal U.rho.density
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hF : Measurable (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered j X) :=
    measurable_const.mul (measurable_pairSumOrdered hm)
  haveI := hprob n
  have hNp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hL1 := logEN_pos' (N := n + 1) (by omega)
  by_cases hbig : N₁ ≤ n + 1
  · obtain ⟨hle, hκ, hRD⟩ := hlarge n hbig
    refine (evar_transfer_large hle hF).trans ?_
    have h1 := hCj β hβI ρ U (Vf n) (hbd n) (hVu n) n (by omega) hκ hRD K j hm hsym hcan hj
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
            exact (hC0 β hβI ρ U (Vf n) (hbd n) (n + 1) (by omega) x).1
        _ = _ := (ENNReal.ofReal_mul (sq_nonneg _)).symm
    have hle := hcrude n
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

/-- Uniform `partpsi_all` (`HRS/Equilibrium/PairMomentsAssemble.lean` l.291). -/
theorem partpsi_all_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), Measurable (Function.uncurry ψ) →
      (∀ x y, ψ x y = ψ y x) → IsCanonicalPair (withDensityReal ρ) ψ →
      (∀ x y, x ≠ y → |ψ x y| ≤ K * psiEnv s x y) → ∀ N : ℕ, 2 ≤ N →
        evariance (fun X : Config d N => (N : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered ψ X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * K ^ 2 / N) := by
  obtain ⟨c, Cq, Mmax, M'max, γmax, N₁, KQ, δC, C1, Cu, C2, K', hc, hCq, hN₁, hKQ, hδC, hC1, hCu, hC2,
    hK'pos, hset⟩ := exists_setting_unif hd hcrit hβm hββ hc₀ hΛ
  obtain ⟨BA, BB, BC, hBA, hBB, hBC, hEnv⟩ := psiEnv_bounds_unif hd hcrit Cu hCu Λ₀ hΛ
  obtain ⟨Cj, hCj0, hCj⟩ := pairVar_noLog_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c Mmax M'max γmax Cq Cu hCu
    δC C1 hδC hC1 (measurable_psiEnv s) BA BB BC hBA hBB hBC hEnv
  set E0 : ℝ := Real.exp (M'max + βp * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set Csum : ℝ := ∑ n ∈ Finset.range N₁, K' n * (E0 * BB) * (N₁ : ℝ) ^ 2 with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun n _ => by have := hK'pos n; positivity
  refine ⟨max (KQ * Cj) Csum, le_trans (by positivity) (le_max_left _ _),
    fun β hβI ρ U K ψ hm hsym hcan hψ N hN => ?_⟩
  obtain ⟨Vf, hVu, hbd, hprob, hcrude, hlarge, -⟩ := hset β hβI ρ U
  have hβ : 0 < β := U.hβpos
  have hβle : β ≤ βp := U.hβle
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal U.rho.density
  have hEnvρ := hEnv ρ U.hup
  have hE0le : Real.exp (M'max + β * max γmax 0 + Mmax) ≤ E0 := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hβle (le_max_right γmax 0)
    linarith
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hF : Measurable (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered ψ X) :=
    measurable_const.mul (measurable_pairSumOrdered hm)
  haveI := hprob n
  have hNp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  by_cases hbig : N₁ ≤ n + 1
  · obtain ⟨hle, hκ, hRD⟩ := hlarge n hbig
    refine (evar_transfer_large hle hF).trans ?_
    have h1 := hCj β hβI ρ U (Vf n) (hbd n) (hVu n) n (by omega) hκ hRD K ψ hm hsym hcan hψ
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
      (varInt_noLog hd β hβ ρ U.rho c Mmax M'max γmax Cq (N := n + 1) (by omega) (Vf n) (hbd n) hBB hEnvρ
        K hψ x _ rfl).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE0le hBB) (sq_nonneg K)))
    have hle := hcrude n
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

end HRS.ME.NfU
