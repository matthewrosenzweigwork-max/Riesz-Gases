import HRS.Equilibrium.PairMomentsPairs
import HRS.ME.NfUPU1b

/-!
# Packet PU8, part A (uniform reference-level bounds `partb_ref`, `partj_ref`)

Uniform copies (namespace `HRS.ME.NfU`) of the following lemmas (rule for uniform statements in
`docs/MAIN_E_NF_PLAN.md`).  Fixed data: `d, s, βm, βp, c₀, Λ₀` with `0 < βm`, `βm ≤ βp`, `1 ≤ Λ₀`
(`1 ≤ Λ₀` is the hypothesis of `pole_w_integrals_unif`; `RhoU` gives `ρ ≤ Λ₀`), and the setting parameters of
the original statement (`c`, `Mmax M'max γmax Cq`, `Cu`, `δC C1`).  The constant is chosen before
`β ∈ Set.Icc βm βp` and before `ρ`; the thermal hypothesis is `RhoU d βm βp c₀ Λ₀ β ρ`.

* `partb_ref_unif` of `HRS.PairMom.partb_ref` (PairMomentsBase l.482).  Uses `pole_w_integrals_unif`.
* `partj_ref_unif` of `HRS.PairMom.partj_ref` (PairMomentsPairs l.89).  Uses `pole_w_integrals_unif`,
  `lintegral_mu_w` and `lintegral_mu_cap` (their constants are chosen before `ρ`), and `ρ ≤ Λ₀` from `RhoU.hup`
  in place of `exists_density_bound`; the density constant is the fixed `Λ := Λ₀`.  The prefactor
  `exp (M'max + β max γmax 0 + Mmax)` is bounded by its value at `βp` (`E0`, monotone in `β`).
* Hypotheses on `V` that mention `β` (`weakKappa V β ≤ 1/2`, `RefDens V β n _ _`) stay on `V`, after `β`.
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

/-- Uniform `partb_ref`: the constant `8 (2 C0 + 4 C0²)` is chosen after `d, s, βm, βp, c₀, Λ₀` and the
potential data, with `C0` from `pole_w_integrals_unif`; the statement is uniform in `β ∈ [βm, βp]` and `ρ`. -/
theorem partb_ref_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ n : ℕ, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      ∀ (K : ℝ) (b : Torus d → Torus d → ℝ), Measurable (Function.uncurry b) → (∀ x y, b x y = b y x) →
      (∀ x y, x ≠ y → |b x y| ≤ K * wEnv s x y ^ 2) →
        evariance (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered b X)
            (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * K ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨C0, hC00, hC0⟩ := pole_w_integrals_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  refine ⟨8 * (2 * C0 + 4 * C0 ^ 2), by positivity, fun β hβI ρ hU V hV n hn hκ K b hm hsym hb => ?_⟩
  have hβ : 0 < β := hU.hβpos
  have hρ : SmoothPosDensity ρ := hU.rho
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  set N : ℕ := n + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnR : (n : ℝ) ≤ N := by simp [hNdef]
  haveI : NeZero n := ⟨by omega⟩
  have hLp := logEN_pos' (N := N) hN1
  have hL2 := logEN_sq_le (N := N) hN1
  -- pointwise kernel bounds
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := fun x => HRS.External.PoleVar.ae_ne_pt hatom x
  have hsq : ∀ x y, x ≠ y → ‖b x y‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wEnv s x y ^ 4) := by
    intro x y hxy
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hb x y hxy
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h2
    calc b x y ^ 2 ≤ (K * wEnv s x y ^ 2) ^ 2 := h2
      _ = _ := by ring
  have habs : ∀ x y, x ≠ y → ‖b x y‖ₑ ≤ ENNReal.ofReal |K| * ENNReal.ofReal (wEnv s x y ^ 2) := by
    intro x y hxy
    rw [← ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |b x y| ≤ K * wEnv s x y ^ 2 := hb x y hxy
      _ ≤ |K| * wEnv s x y ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
  -- row bounds
  have hlam0 : 0 ≤ β / N := by positivity
  have hVint : ∀ x : Torus d, ∫⁻ y, ‖b x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (K ^ 2 * (C0 * (N : ℝ) ^ 2)) := by
    intro x
    calc _ ≤ ∫⁻ y, (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wEnv s x y ^ 4)) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
          ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          exact mul_le_mul' (hsq x y (Ne.symm hy)) le_rfl
      _ = ENNReal.ofReal (K ^ 2) * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
          ∂(withDensityReal ρ) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          rw [mul_assoc]
      _ ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (C0 * (N : ℝ) ^ 2) := by
          gcongr
          exact (hC0 β hβI ρ hU V hV N hN2 x).2
      _ = _ := (ENNReal.ofReal_mul (sq_nonneg _)).symm
  have hVmean : ∀ x : Torus d, ∫⁻ y, ‖b x y‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (|K| * (C0 * logEN N)) := by
    intro x
    calc _ ≤ ∫⁻ y, (ENNReal.ofReal |K| * ENNReal.ofReal (wEnv s x y ^ 2)) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
          ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          exact mul_le_mul' (habs x y (Ne.symm hy)) le_rfl
      _ = ENNReal.ofReal |K| * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
          ∂(withDensityReal ρ) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          rw [mul_assoc]
      _ ≤ ENNReal.ofReal |K| * ENNReal.ofReal (C0 * logEN N) := by
          gcongr
          exact (hC0 β hβI ρ hU V hV N hN2 x).1
      _ = _ := (ENNReal.ofReal_mul (abs_nonneg _)).symm
  have hcard : n + Fintype.card (Option Empty) ≤ n + 1 := by simp
  have hrow : ∀ i : Fin (n + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (2 * n) * ENNReal.ofReal (K ^ 2 * (C0 * (N : ℝ) ^ 2)) +
        ENNReal.ofReal ((n * (|K| * (C0 * logEN N))) ^ 2) := by
    intro i
    refine row_moment_le V hβ.le hκ hm i (𝒱 := ENNReal.ofReal (K ^ 2 * (C0 * (N : ℝ) ^ 2)))
      (𝓜 := n * (|K| * (C0 * logEN N))) (Filter.Eventually.of_forall hVint) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    exact abs_sum_marg_le V hβ.le (by omega) hcard _ (measurable_h_x hm x)
      (by positivity) (hVmean x)
  have hWu := evariance_pairSum_le V hβ.le (by omega : 0 < n + 1) hκ hm hsym (((n + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)))
  refine hWu.trans ?_
  have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 5 := by
    rw [rpow_sq_neg N (by omega)]
    have : (2 * (5 / 2 : ℝ)) = ((5 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  rw [hc2]
  calc ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 5)) * ∑ i : Fin (n + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i,
        b (Y i) (Y j)‖ₑ ^ 2 ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 5)) * ∑ _i : Fin (n + 1),
          (ENNReal.ofReal (2 * n) * ENNReal.ofReal (K ^ 2 * (C0 * (N : ℝ) ^ 2)) +
            ENNReal.ofReal ((n * (|K| * (C0 * logEN N))) ^ 2)) := by
        gcongr with i _
        exact hrow i
    _ = ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 5) * (N * (2 * n * (K ^ 2 * (C0 * (N : ℝ) ^ 2)) +
          (n * (|K| * (C0 * logEN N))) ^ 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : (0 : ℝ) ≤ 2 * n := by positivity
        rw [show (((n + 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal (N : ℝ) by
          rw [ENNReal.ofReal_natCast]]
        rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact real_partb N n C0 K (logEN N) (by exact_mod_cast hN1) (Nat.cast_nonneg n) hnR
          (by linarith) hL2 hC00




/-- Uniform `partj_ref`: the constant `16 C0 + 8 Cm²`, `Cm = δC Λ₀ B + C1 Λ₀ Ccap (1 + Cu)(1 + |log(1 + Cu)|)`,
is chosen after the fixed data; `C0` from `pole_w_integrals_unif`, `B, Ccap` from `lintegral_mu_w`,
`lintegral_mu_cap`.  Uniform in `β ∈ [βm, βp]` and `ρ` (`RhoU`). -/
theorem partj_ref_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) (Cu : ℝ) (hCu : 0 ≤ Cu) (δC C1 : ℝ) (hδC : 0 ≤ δC)
    (hC1 : 0 ≤ C1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V →
      (∀ x y : Torus d, x ≠ y → V.q x y ≤ Cu * wEnv s x y) → ∀ n : ℕ, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      RefDens V β n (δC * deltaN d s (n + 1)) C1 →
      ∀ (K : ℝ) (j : Torus d → Torus d → ℝ), Measurable (Function.uncurry j) → (∀ x y, j x y = j y x) →
      IsCanonicalPair (withDensityReal ρ) j → (∀ x y, x ≠ y → |j x y| ≤ K * wEnv s x y) →
        evariance (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered j X)
            (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * K ^ 2 * logEN (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨C0, hC00, hC0⟩ := pole_w_integrals_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  obtain ⟨B, hB0, hB⟩ := lintegral_mu_w hd hcrit
  obtain ⟨Ccap, hCcap0, hCcap⟩ := lintegral_mu_cap hd hcrit
  obtain ⟨Λ, hΛeq⟩ : ∃ Λ : ℝ, Λ = Λ₀ := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛeq]; linarith
  set E0 : ℝ := Real.exp (M'max + βp * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set Cm : ℝ := δC * (Λ * B) + C1 * (Λ * (Ccap * ((1 + Cu) * (1 + |Real.log (1 + Cu)|)))) with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  refine ⟨16 * C0 + 8 * Cm ^ 2, by positivity,
    fun β hβI ρ hU V hV hVu n hn hκ hRD K j hm hsym hcan hj => ?_⟩
  have hβ : 0 < β := hU.hβpos
  have hβle : β ≤ βp := hU.hβle
  have hρ : SmoothPosDensity ρ := hU.rho
  have hΛ : ∀ x, ρ x ≤ Λ := fun x => by rw [hΛeq]; exact hU.hup x
  have hE0le : Real.exp (M'max + β * max γmax 0 + Mmax) ≤ E0 := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hβle (le_max_right γmax 0)
    linarith
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  set N : ℕ := n + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnR : (n : ℝ) ≤ N := by simp [hNdef]
  haveI : NeZero n := ⟨by omega⟩
  have hL1 := logEN_pos' (N := N) hN1
  have hLN := logEN_le_N (N := N) hN1
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := fun x => HRS.External.PoleVar.ae_ne_pt hatom x
  have hlam0 : 0 ≤ β / N := by positivity
  have hlamβ : β / N ≤ β := by rw [div_le_iff₀ hNp]; nlinarith
  -- pointwise kernel bounds
  have hsq : ∀ x y, x ≠ y → ‖j x y‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wEnv s x y ^ 2) := by
    intro x y hxy
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hj x y hxy) 2
    rw [sq_abs] at h2
    calc j x y ^ 2 ≤ (K * wEnv s x y) ^ 2 := h2
      _ = _ := by ring
  have habs : ∀ x y, x ≠ y → |j x y| ≤ |K| * wEnv s x y := by
    intro x y hxy
    calc |j x y| ≤ K * wEnv s x y := hj x y hxy
      _ ≤ |K| * wEnv s x y := mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith [PairCorrAux.one_le_wEnv s x y])
  have hVint : ∀ x : Torus d, ∫⁻ y, ‖j x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (K ^ 2 * (C0 * logEN N)) := by
    intro x
    calc _ ≤ ∫⁻ y, (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wEnv s x y ^ 2)) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
          ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          exact mul_le_mul' (hsq x y (Ne.symm hy)) le_rfl
      _ = ENNReal.ofReal (K ^ 2) * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
          ∂(withDensityReal ρ) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          rw [mul_assoc]
      _ ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (C0 * logEN N) := by
          gcongr
          exact (hC0 β hβI ρ hU V hV N hN2 x).1
      _ = _ := (ENNReal.ofReal_mul (sq_nonneg _)).symm
  have hδ0 : 0 ≤ deltaN d s N := by
    rw [deltaN_crit hcrit]; positivity
  set δ : ℝ := δC * deltaN d s N with hδdef
  have hδ00 : 0 ≤ δ := mul_nonneg hδC hδ0
  set lam : ℝ := (1 + Cu) / N with hlamdef
  have hlam : 0 < lam := by positivity
  set W : ℝ := |K| * (δ * (Λ * B)) + |K| * (C1 * (Λ * (Ccap * lam * (1 + |Real.log lam|)))) with hWdef
  have hW0 : 0 ≤ W := by positivity
  have hmeasw : ∀ x : Torus d, Measurable fun y => ENNReal.ofReal (wEnv s x y) :=
    fun x => ENNReal.measurable_ofReal.comp (PairCorrAux.measurable_wEnv s x)
  have hmeasc : ∀ x : Torus d, Measurable fun y => ENNReal.ofReal (wEnv s x y * min 1 (lam * wEnv s x y)) :=
    fun x => ENNReal.measurable_ofReal.comp ((PairCorrAux.measurable_wEnv s x).mul
      (measurable_const.min (measurable_const.mul (PairCorrAux.measurable_wEnv s x))))
  -- the refined mean integral
  have hWint : ∀ x : Torus d, ∫⁻ y, ENNReal.ofReal (|j x y| * (δ + C1 * min 1 ((1 / ((n + 1 : ℕ) : ℝ)) *
      (1 + V.q y x)))) ∂(withDensityReal ρ) ≤ ENNReal.ofReal W := by
    intro x
    have hpt : ∀ᵐ y ∂(withDensityReal ρ), ENNReal.ofReal (|j x y| * (δ + C1 * min 1 ((1 / ((n + 1 : ℕ) : ℝ)) *
        (1 + V.q y x)))) ≤ ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (wEnv s x y) +
          ENNReal.ofReal (|K| * C1) * ENNReal.ofReal (wEnv s x y * min 1 (lam * wEnv s x y)) := by
      filter_upwards [hae x] with y hy
      have hxy : x ≠ y := Ne.symm hy
      have hw1 := PairCorrAux.one_le_wEnv s x y
      have hq1 : V.q y x ≤ Cu * wEnv s x y := by
        have := hVu y x hy
        rwa [PairCorrAux.wEnv_symm s y x] at this
      have hm1 := min_cap_mono (N := (N : ℝ)) (Cu := Cu) (q := V.q y x) (w := wEnv s x y) hNp hCu hw1
        (V.q_nonneg y x) hq1
      have hj1 := habs x y hxy
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hmin0 : 0 ≤ min 1 ((1 / (N : ℝ)) * (1 + V.q y x)) :=
        le_min zero_le_one (by have := V.q_nonneg y x; positivity)
      calc |j x y| * (δ + C1 * min 1 ((1 / (N : ℝ)) * (1 + V.q y x)))
          ≤ (|K| * wEnv s x y) * (δ + C1 * min 1 (lam * wEnv s x y)) := by
            refine mul_le_mul hj1 ?_ (by positivity) (by positivity)
            have : C1 * min 1 ((1 / (N : ℝ)) * (1 + V.q y x)) ≤ C1 * min 1 (lam * wEnv s x y) :=
              mul_le_mul_of_nonneg_left hm1 hC1
            linarith
        _ = |K| * δ * wEnv s x y + |K| * C1 * (wEnv s x y * min 1 (lam * wEnv s x y)) := by ring
    calc _ ≤ ∫⁻ y, (ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (wEnv s x y) +
          ENNReal.ofReal (|K| * C1) * ENNReal.ofReal (wEnv s x y * min 1 (lam * wEnv s x y)))
          ∂(withDensityReal ρ) := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (|K| * δ) * ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂(withDensityReal ρ) +
          ENNReal.ofReal (|K| * C1) * ∫⁻ y, ENNReal.ofReal (wEnv s x y * min 1 (lam * wEnv s x y))
            ∂(withDensityReal ρ) := by
          rw [lintegral_add_left ((hmeasw x).const_mul _), lintegral_const_mul _ (hmeasw x),
            lintegral_const_mul _ (hmeasc x)]
      _ ≤ ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (Λ * B) +
          ENNReal.ofReal (|K| * C1) * ENNReal.ofReal (Λ * (Ccap * lam * (1 + |Real.log lam|))) := by
          gcongr
          · exact hB hΛ hΛ0 x
          · exact hCcap hΛ hΛ0 lam hlam x
      _ = ENNReal.ofReal W := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; rw [hWdef]; ring
  -- finiteness for the integrability against the marginals
  have hWfin : ∀ x : Torus d, ∫⁻ y, ‖j x y‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (|K| * E0 * (Λ * B)) := by
    intro x
    calc _ ≤ ∫⁻ y, (ENNReal.ofReal (|K| * E0) * ENNReal.ofReal (wEnv s x y)) ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          have hxy : x ≠ y := Ne.symm hy
          have hw1 := PairCorrAux.one_le_wEnv s x y
          have h1 : ‖j x y‖ₑ ≤ ENNReal.ofReal (|K| * wEnv s x y) := by
            rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (habs x y hxy)
          have h2 := (poleW_le_const (V := V) hV hβ.le hlam0 (pinsWith (fun e : Empty => e.elim) x) y).trans (ENNReal.ofReal_le_ofReal hE0le)
          calc ‖j x y‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
                pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
              ≤ ENNReal.ofReal (|K| * wEnv s x y) * ENNReal.ofReal E0 := mul_le_mul' h1 h2
            _ = _ := by
                rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
                congr 1; ring
      _ = ENNReal.ofReal (|K| * E0) * ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂(withDensityReal ρ) :=
          lintegral_const_mul _ (hmeasw x)
      _ ≤ ENNReal.ofReal (|K| * E0) * ENNReal.ofReal (Λ * B) := by
          gcongr; exact hB hΛ hΛ0 x
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hcard : n + Fintype.card (Option Empty) ≤ N := by simp [hNdef]
  have hM : ∀ x : Torus d, |∑ k : Fin n, ∫ y, j x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))| ≤ n * W := by
    intro x
    refine row_mean_refined hβ.le hRD x (hcan x).1 (hcan x).2 (fun k => ?_) hW0 (hWint x)
    exact integrable_marg V hβ.le (by omega) hcard _ k (measurable_h_x hm x) ENNReal.ofReal_ne_top (hWfin x)
  -- the size of the mean
  have hMb : (n : ℝ) * W ≤ |K| * Cm * logEN N := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hLeq : logEN N = 1 + Real.log N := PairCorrAux.logEN_eq N hN1
    have hNd : (N : ℝ) * deltaN d s N = logEN N := N_mul_deltaN hcrit hN1
    have h1 : (n : ℝ) * δ ≤ δC * logEN N := by
      calc (n : ℝ) * δ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right hnR hδ00
        _ = δC * ((N : ℝ) * deltaN d s N) := by rw [hδdef]; ring
        _ = δC * logEN N := by rw [hNd]
    have h2 := lam_log_bound (N := (N : ℝ)) (n := (n : ℝ)) (Cu := Cu) (by exact_mod_cast hN1) hn0 hnR hCu
    rw [← hlamdef, ← hLeq] at h2
    have hΛB : 0 ≤ Λ * B := by positivity
    have e : (n : ℝ) * W = |K| * ((n : ℝ) * δ) * (Λ * B) +
        |K| * (C1 * Λ * Ccap) * ((n : ℝ) * (lam * (1 + |Real.log lam|))) := by
      rw [hWdef]; ring
    rw [e]
    have t1 : |K| * ((n : ℝ) * δ) * (Λ * B) ≤ |K| * (δC * logEN N) * (Λ * B) := by
      gcongr
    have t2 : |K| * (C1 * Λ * Ccap) * ((n : ℝ) * (lam * (1 + |Real.log lam|))) ≤
        |K| * (C1 * Λ * Ccap) * ((1 + Cu) * ((1 + |Real.log (1 + Cu)|) * logEN N)) := by
      gcongr
    calc _ ≤ |K| * (δC * logEN N) * (Λ * B) +
          |K| * (C1 * Λ * Ccap) * ((1 + Cu) * ((1 + |Real.log (1 + Cu)|) * logEN N)) := add_le_add t1 t2
      _ = |K| * Cm * logEN N := by rw [hCm]; ring
  -- assemble
  have hVar := pairVar_bound V hβ.le hκ hm hsym (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
    (𝒱 := ENNReal.ofReal (K ^ 2 * (C0 * logEN N))) (𝓜 := n * W) hVint hM
  refine hVar.trans ?_
  have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 3 := by
    rw [rpow_sq_neg N (by omega)]
    have : (2 * (3 / 2 : ℝ)) = ((3 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  rw [hc2]
  have hconv : ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 3)) * (((n + 1 : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (2 * n) * ENNReal.ofReal (K ^ 2 * (C0 * logEN N)) + ENNReal.ofReal (((n : ℝ) * W) ^ 2)))
      = ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * (2 * n * (K ^ 2 * (C0 * logEN N)) +
        ((n : ℝ) * W) ^ 2))) := by
    rw [show (((n + 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal (N : ℝ) by rw [ENNReal.ofReal_natCast]]
    have h1 : (0 : ℝ) ≤ 2 * n := by positivity
    rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [hconv]
  refine ENNReal.ofReal_le_ofReal ?_
  have hreal := real_partj (N : ℝ) (n : ℝ) C0 K (logEN N) ((n : ℝ) * W) Cm (by exact_mod_cast hN1)
    (Nat.cast_nonneg n) hnR hL1 hLN hC00 hCm0 (by positivity) hMb
  exact hreal

end HRS.ME.NfU
