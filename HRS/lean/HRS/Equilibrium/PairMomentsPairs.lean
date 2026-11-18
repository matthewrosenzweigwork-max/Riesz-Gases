/-
# HRS.Equilibrium.PairMomentsPairs -- pair-sum variance bounds under the reference (EQ-01b)

Parts (j) and (psi) of Proposition 4.12 under the calibrated reference.
-/
import HRS.Equilibrium.PairMomentsEnv

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad

variable {d : ℕ} {s : ℝ}

section PairVar

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- **Variance of a pair sum from row bounds**: `Var_R(c ∑_{i≠j} v) ≤ 8c² N (2n 𝒱 + 𝓜²)`. -/
theorem pairVar_bound (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} [NeZero n]
    (hκ : weakKappa V β ≤ 1 / 2) {v : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry v))
    (hsym : ∀ x y, v x y = v y x) (c : ℝ) {𝒱 : ℝ≥0∞} {𝓜 : ℝ}
    (hV : ∀ x, ∫⁻ y, ‖v x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂μ ≤ 𝒱)
    (hM : ∀ x, |∑ k : Fin n, ∫ y, v x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))| ≤ 𝓜) :
    evariance (fun X : Config d (n + 1) => c * pairSumOrdered v X)
        (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal (8 * c ^ 2) * (((n + 1 : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2))) := by
  refine (evariance_pairSum_le V hβ (Nat.succ_pos n) hκ hm hsym c).trans ?_
  refine mul_le_mul' le_rfl ?_
  calc ∑ i : Fin (n + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, v (Y i) (Y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ∑ _i : Fin (n + 1), (ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact row_moment_le V hβ hκ hm i (Filter.Eventually.of_forall hV) (Filter.Eventually.of_forall hM)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end PairVar

section PartJ

theorem logEN_le_N {N : ℕ} (hN : 1 ≤ N) : logEN N ≤ N := by
  rw [PairCorrAux.logEN_eq N hN]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have := Real.log_le_sub_one_of_pos hN0
  linarith

theorem real_partj (N n C0 K L M Cm : ℝ) (hN : 1 ≤ N) (hn : 0 ≤ n) (hnN : n ≤ N) (hL1 : 1 ≤ L)
    (hLN : L ≤ N) (hC0 : 0 ≤ C0) (hCm : 0 ≤ Cm) (hM0 : 0 ≤ M) (hM : M ≤ |K| * Cm * L) :
    8 * (1 / N ^ 3) * (N * (2 * n * (K ^ 2 * (C0 * L)) + M ^ 2))
      ≤ (16 * C0 + 8 * Cm ^ 2) * K ^ 2 * L / N := by
  have hN0 : 0 < N := by linarith
  have hM2 : M ^ 2 ≤ K ^ 2 * Cm ^ 2 * L ^ 2 := by
    have : M ^ 2 ≤ (|K| * Cm * L) ^ 2 := pow_le_pow_left₀ hM0 hM 2
    calc M ^ 2 ≤ (|K| * Cm * L) ^ 2 := this
      _ = K ^ 2 * Cm ^ 2 * L ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  have hL2 : L ^ 2 ≤ L * N := by nlinarith
  have hX : 2 * n * (K ^ 2 * (C0 * L)) + M ^ 2 ≤ K ^ 2 * L * N * (2 * C0 + Cm ^ 2) := by
    have h1 : 2 * n * (K ^ 2 * (C0 * L)) ≤ 2 * C0 * K ^ 2 * L * N := by
      have : n * (K ^ 2 * (C0 * L)) ≤ N * (K ^ 2 * (C0 * L)) :=
        mul_le_mul_of_nonneg_right hnN (by positivity)
      nlinarith
    have h2 : K ^ 2 * Cm ^ 2 * L ^ 2 ≤ K ^ 2 * Cm ^ 2 * (L * N) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    nlinarith
  calc 8 * (1 / N ^ 3) * (N * (2 * n * (K ^ 2 * (C0 * L)) + M ^ 2))
      ≤ 8 * (1 / N ^ 3) * (N * (K ^ 2 * L * N * (2 * C0 + Cm ^ 2))) := by gcongr
    _ = 8 * (2 * C0 + Cm ^ 2) * K ^ 2 * L / N := by field_simp
    _ ≤ (16 * C0 + 8 * Cm ^ 2) * K ^ 2 * L / N := by
        refine div_le_div_of_nonneg_right ?_ hN0.le
        have : 0 ≤ K ^ 2 * L := by positivity
        nlinarith

end PartJ

section PartJRef

/-- Part (j) under the reference: `Var_R F_N(j) ≤ C K² L_N / N`. -/
theorem partj_ref (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) (Cu : ℝ) (hCu : 0 ≤ Cu) (δC C1 : ℝ) (hδC : 0 ≤ δC)
    (hC1 : 0 ≤ C1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V →
      (∀ x y : Torus d, x ≠ y → V.q x y ≤ Cu * wEnv s x y) → ∀ n : ℕ, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      RefDens V β n (δC * deltaN d s (n + 1)) C1 →
      ∀ (K : ℝ) (j : Torus d → Torus d → ℝ), Measurable (Function.uncurry j) → (∀ x y, j x y = j y x) →
      IsCanonicalPair (withDensityReal ρ) j → (∀ x y, x ≠ y → |j x y| ≤ K * wEnv s x y) →
        evariance (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered j X)
            (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * K ^ 2 * logEN (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨C0, hC00, hC0⟩ := pole_w_integrals hd hcrit β hβ ρ hρ c hc Mmax M'max γmax Cq hCq
  obtain ⟨B, hB0, hB⟩ := lintegral_mu_w hd hcrit
  obtain ⟨Ccap, hCcap0, hCcap⟩ := lintegral_mu_cap hd hcrit
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set Cm : ℝ := δC * (Λ * B) + C1 * (Λ * (Ccap * ((1 + Cu) * (1 + |Real.log (1 + Cu)|)))) with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  refine ⟨16 * C0 + 8 * Cm ^ 2, by positivity, fun V hV hVu n hn hκ hRD K j hm hsym hcan hj => ?_⟩
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
          exact (hC0 V hV N hN2 x).1
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
          · exact hB hΛ hΛ0.le x
          · exact hCcap hΛ hΛ0.le lam hlam x
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
          have h2 := poleW_le_const (V := V) hV hβ.le hlam0 (pinsWith (fun e : Empty => e.elim) x) y
          calc ‖j x y‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
                pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
              ≤ ENNReal.ofReal (|K| * wEnv s x y) * ENNReal.ofReal E0 := mul_le_mul' h1 h2
            _ = _ := by
                rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
                congr 1; ring
      _ = ENNReal.ofReal (|K| * E0) * ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂(withDensityReal ρ) :=
          lintegral_const_mul _ (hmeasw x)
      _ ≤ ENNReal.ofReal (|K| * E0) * ENNReal.ofReal (Λ * B) := by
          gcongr; exact hB hΛ hΛ0.le x
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

end PartJRef

section RowData

/-- Row data for a kernel with an integrable envelope: the variance integral `≤ K² E₀ B_B` and the
refined conditional mean `≤ |K| (δ_C B_A + C₁ B_C) L_N`. -/
theorem rowData_noLog (hd : 2 ≤ d) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)
    (c Mmax M'max γmax Cq : ℝ) (Cu : ℝ) (hCu : 0 ≤ Cu) (δC C1 : ℝ) (hδC : 0 ≤ δC) (hC1 : 0 ≤ C1)
    (hcrit : s = (d : ℝ) / 2)
    (V : WeakPotential (withDensityReal ρ)) (hV : PotBound (d := d) s c Mmax M'max γmax Cq V)
    (hVu : ∀ x y : Torus d, x ≠ y → V.q x y ≤ Cu * wEnv s x y) {n : ℕ} (hn : 1 ≤ n)
    (hRD : RefDens V β n (δC * deltaN d s (n + 1)) C1)
    {Env : Torus d → Torus d → ℝ} (hEm : ∀ x, Measurable (Env x)) {BA BB BC : ℝ}
    (hBA : 0 ≤ BA) (hBB : 0 ≤ BB) (hBC : 0 ≤ BC)
    (hEnv : EnvBounds (d := d) s Cu (withDensityReal ρ) Env BA BB BC) (K : ℝ)
    {v : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry v))
    (hcan : IsCanonicalPair (withDensityReal ρ) v) (hv : ∀ x y, x ≠ y → |v x y| ≤ K * Env x y) :
    (∀ x : Torus d, ∫⁻ y, ‖v x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (K ^ 2 * (Real.exp (M'max + β * max γmax 0 + Mmax) * BB))) ∧
    (∀ x : Torus d, |∑ k : Fin n, ∫ y, v x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))| ≤
      |K| * (δC * BA + C1 * BC) * logEN (n + 1)) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  set N : ℕ := n + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnR : (n : ℝ) ≤ N := by simp [hNdef]
  have hL1 := logEN_pos' (N := N) hN1
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := fun x => HRS.External.PoleVar.ae_ne_pt hatom x
  have hlam0 : 0 ≤ β / N := by positivity
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set δ : ℝ := δC * deltaN d s N with hδdef
  have hδ0 : 0 ≤ deltaN d s N := by rw [deltaN_crit hcrit]; positivity
  have hδ00 : 0 ≤ δ := mul_nonneg hδC hδ0
  have hKn : ∀ x y, x ≠ y → ‖v x y‖ₑ ≤ ENNReal.ofReal |K| * ENNReal.ofReal (Env x y) := by
    intro x y hxy
    rw [← ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |v x y| ≤ K * Env x y := hv x y hxy
      _ ≤ |K| * Env x y := mul_le_mul_of_nonneg_right (le_abs_self K) (hEnv.nonneg x y)
  have hmeasE : ∀ x : Torus d, Measurable fun y => ENNReal.ofReal (Env x y) :=
    fun x => ENNReal.measurable_ofReal.comp (hEm x)
  constructor
  · intro x
    calc _ ≤ ∫⁻ y, (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal E0) * ENNReal.ofReal (Env x y ^ 2)
          ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          have hxy : x ≠ y := Ne.symm hy
          have h1 : ‖v x y‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (Env x y ^ 2) := by
            rw [← ENNReal.ofReal_mul (sq_nonneg _), ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
            refine ENNReal.ofReal_le_ofReal ?_
            have h2 := pow_le_pow_left₀ (abs_nonneg _) (hv x y hxy) 2
            rw [sq_abs] at h2
            calc v x y ^ 2 ≤ (K * Env x y) ^ 2 := h2
              _ = _ := by ring
          have h2 := poleW_le_const (V := V) hV hβ.le hlam0 (pinsWith (fun e : Empty => e.elim) x) y
          calc ‖v x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
                pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
              ≤ (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (Env x y ^ 2)) * ENNReal.ofReal E0 :=
                mul_le_mul' h1 h2
            _ = _ := by ring
      _ = (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal E0) * ∫⁻ y, ENNReal.ofReal (Env x y ^ 2)
          ∂(withDensityReal ρ) := lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.ofReal_ne_top)
      _ ≤ (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal E0) * ENNReal.ofReal BB := by
          gcongr; exact hEnv.B x
      _ = _ := by
          rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  · intro x
    set W : ℝ := |K| * (δ * BA) + |K| * (C1 / N * BC) with hWdef
    have hW0 : 0 ≤ W := by positivity
    have hWint : ∫⁻ y, ENNReal.ofReal (|v x y| * (δ + C1 * min 1 ((1 / ((n + 1 : ℕ) : ℝ)) *
        (1 + V.q y x)))) ∂(withDensityReal ρ) ≤ ENNReal.ofReal W := by
      have hpt : ∀ᵐ y ∂(withDensityReal ρ), ENNReal.ofReal (|v x y| * (δ + C1 * min 1 ((1 / ((n + 1 : ℕ) : ℝ)) *
          (1 + V.q y x)))) ≤ ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (Env x y) +
            ENNReal.ofReal (|K| * (C1 / N)) * ENNReal.ofReal (Env x y * (1 + Cu * wEnv s x y)) := by
        filter_upwards [hae x] with y hy
        have hxy : x ≠ y := Ne.symm hy
        have hq1 : V.q y x ≤ Cu * wEnv s x y := by
          have := hVu y x hy
          rwa [PairCorrAux.wEnv_symm s y x] at this
        have hE1 := hEnv.nonneg x y
        have hw0 : 0 ≤ wEnv s x y := by linarith [PairCorrAux.one_le_wEnv s x y]
        have hv1 : |v x y| ≤ |K| * Env x y := by
          calc |v x y| ≤ K * Env x y := hv x y hxy
            _ ≤ |K| * Env x y := mul_le_mul_of_nonneg_right (le_abs_self K) hE1
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hmin : min 1 ((1 / (N : ℝ)) * (1 + V.q y x)) ≤ (1 / (N : ℝ)) * (1 + Cu * wEnv s x y) := by
          refine (min_le_right _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have hmin0 : 0 ≤ min 1 ((1 / (N : ℝ)) * (1 + V.q y x)) :=
          le_min zero_le_one (by have := V.q_nonneg y x; positivity)
        calc |v x y| * (δ + C1 * min 1 ((1 / (N : ℝ)) * (1 + V.q y x)))
            ≤ (|K| * Env x y) * (δ + C1 * ((1 / (N : ℝ)) * (1 + Cu * wEnv s x y))) := by
              refine mul_le_mul hv1 ?_ (by positivity) (by positivity)
              have := mul_le_mul_of_nonneg_left hmin hC1
              linarith
          _ = |K| * δ * Env x y + |K| * (C1 / N) * (Env x y * (1 + Cu * wEnv s x y)) := by ring
      have hmeasC : Measurable fun y => ENNReal.ofReal (Env x y * (1 + Cu * wEnv s x y)) :=
        ENNReal.measurable_ofReal.comp ((hEm x).mul (measurable_const.add (measurable_const.mul
          (PairCorrAux.measurable_wEnv s x))))
      calc _ ≤ ∫⁻ y, (ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (Env x y) +
            ENNReal.ofReal (|K| * (C1 / N)) * ENNReal.ofReal (Env x y * (1 + Cu * wEnv s x y)))
            ∂(withDensityReal ρ) := lintegral_mono_ae hpt
        _ = ENNReal.ofReal (|K| * δ) * ∫⁻ y, ENNReal.ofReal (Env x y) ∂(withDensityReal ρ) +
            ENNReal.ofReal (|K| * (C1 / N)) * ∫⁻ y, ENNReal.ofReal (Env x y * (1 + Cu * wEnv s x y))
              ∂(withDensityReal ρ) := by
            rw [lintegral_add_left ((hmeasE x).const_mul _), lintegral_const_mul _ (hmeasE x),
              lintegral_const_mul _ hmeasC]
        _ ≤ ENNReal.ofReal (|K| * δ) * ENNReal.ofReal BA +
            ENNReal.ofReal (|K| * (C1 / N)) * ENNReal.ofReal BC := by
            gcongr
            · exact hEnv.A x
            · exact hEnv.C x
        _ = ENNReal.ofReal W := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; rw [hWdef]; ring
    have hcard : n + Fintype.card (Option Empty) ≤ N := by simp [hNdef]
    have hWfin : ∫⁻ y, ‖v x y‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (|K| * E0 * BA) := by
      calc _ ≤ ∫⁻ y, (ENNReal.ofReal (|K| * E0)) * ENNReal.ofReal (Env x y) ∂(withDensityReal ρ) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae x] with y hy
            have hxy : x ≠ y := Ne.symm hy
            have h2 := poleW_le_const (V := V) hV hβ.le hlam0 (pinsWith (fun e : Empty => e.elim) x) y
            calc ‖v x y‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
                  pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
                ≤ (ENNReal.ofReal |K| * ENNReal.ofReal (Env x y)) * ENNReal.ofReal E0 :=
                  mul_le_mul' (hKn x y hxy) h2
              _ = _ := by
                  rw [ENNReal.ofReal_mul (abs_nonneg K)]; ring
        _ = ENNReal.ofReal (|K| * E0) * ∫⁻ y, ENNReal.ofReal (Env x y) ∂(withDensityReal ρ) :=
            lintegral_const_mul _ (hmeasE x)
        _ ≤ ENNReal.ofReal (|K| * E0) * ENNReal.ofReal BA := by gcongr; exact hEnv.A x
        _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
    have hM := row_mean_refined hβ.le hRD x (hcan x).1 (hcan x).2 (fun k => ?_) hW0 hWint
    · refine hM.trans ?_
      have hL : (1 : ℝ) ≤ logEN N := hL1
      have hNd : (N : ℝ) * deltaN d s N = logEN N := N_mul_deltaN hcrit hN1
      have h1 : (n : ℝ) * δ ≤ δC * logEN N := by
        calc (n : ℝ) * δ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right hnR hδ00
          _ = δC * ((N : ℝ) * deltaN d s N) := by rw [hδdef]; ring
          _ = δC * logEN N := by rw [hNd]
      have h2 : (n : ℝ) * (C1 / N) ≤ C1 := by
        rw [mul_div_assoc', div_le_iff₀ hNp]; nlinarith
      have e : (n : ℝ) * W = |K| * ((n : ℝ) * δ) * BA + |K| * ((n : ℝ) * (C1 / N)) * BC := by
        rw [hWdef]; ring
      rw [e]
      have t1 : |K| * ((n : ℝ) * δ) * BA ≤ |K| * (δC * logEN N) * BA := by gcongr
      have t2 : |K| * ((n : ℝ) * (C1 / N)) * BC ≤ |K| * C1 * BC * logEN N := by
        calc |K| * ((n : ℝ) * (C1 / N)) * BC ≤ |K| * C1 * BC := by gcongr
          _ ≤ |K| * C1 * BC * logEN N := le_mul_of_one_le_right (by positivity) hL
      calc _ ≤ |K| * (δC * logEN N) * BA + |K| * C1 * BC * logEN N := add_le_add t1 t2
        _ = _ := by ring
    · exact integrable_marg V hβ.le (by omega) hcard _ k (measurable_h_x hm x) ENNReal.ofReal_ne_top hWfin

end RowData

section PartPsi

theorem real_psi (N n Vc K L M Cm : ℝ) (hN : 1 ≤ N) (hn : 0 ≤ n) (hnN : n ≤ N) (hVc : 0 ≤ Vc)
    (hL2 : L ^ 2 ≤ 4 * N) (hCm : 0 ≤ Cm) (hM0 : 0 ≤ M) (hM : M ≤ |K| * Cm * L) :
    8 * (1 / N ^ 3) * (N * (2 * n * (K ^ 2 * Vc) + M ^ 2)) ≤ (16 * Vc + 32 * Cm ^ 2) * K ^ 2 / N := by
  have hN0 : 0 < N := by linarith
  have hM2 : M ^ 2 ≤ K ^ 2 * Cm ^ 2 * L ^ 2 := by
    have : M ^ 2 ≤ (|K| * Cm * L) ^ 2 := pow_le_pow_left₀ hM0 hM 2
    calc M ^ 2 ≤ (|K| * Cm * L) ^ 2 := this
      _ = K ^ 2 * Cm ^ 2 * L ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  have hX : 2 * n * (K ^ 2 * Vc) + M ^ 2 ≤ K ^ 2 * N * (2 * Vc + 4 * Cm ^ 2) := by
    have h1 : 2 * n * (K ^ 2 * Vc) ≤ 2 * Vc * K ^ 2 * N := by
      have : n * (K ^ 2 * Vc) ≤ N * (K ^ 2 * Vc) := mul_le_mul_of_nonneg_right hnN (by positivity)
      nlinarith
    have h2 : K ^ 2 * Cm ^ 2 * L ^ 2 ≤ K ^ 2 * Cm ^ 2 * (4 * N) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    nlinarith
  calc 8 * (1 / N ^ 3) * (N * (2 * n * (K ^ 2 * Vc) + M ^ 2))
      ≤ 8 * (1 / N ^ 3) * (N * (K ^ 2 * N * (2 * Vc + 4 * Cm ^ 2))) := by gcongr
    _ = 8 * (2 * Vc + 4 * Cm ^ 2) * K ^ 2 / N := by field_simp
    _ = (16 * Vc + 32 * Cm ^ 2) * K ^ 2 / N := by ring

/-- Pair-sum variance under the reference for a canonical symmetric kernel with an integrable
envelope: `Var_R(N^{-3/2} ∑_{i≠j} v) ≤ C K² / N`. -/
theorem pairVar_noLog (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c Mmax M'max γmax Cq : ℝ) (Cu : ℝ) (hCu : 0 ≤ Cu)
    (δC C1 : ℝ) (hδC : 0 ≤ δC) (hC1 : 0 ≤ C1)
    {Env : Torus d → Torus d → ℝ} (hEm : ∀ x, Measurable (Env x)) {BA BB BC : ℝ}
    (hBA : 0 ≤ BA) (hBB : 0 ≤ BB) (hBC : 0 ≤ BC)
    (hEnv : EnvBounds (d := d) s Cu (withDensityReal ρ) Env BA BB BC) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V →
      (∀ x y : Torus d, x ≠ y → V.q x y ≤ Cu * wEnv s x y) → ∀ n : ℕ, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      RefDens V β n (δC * deltaN d s (n + 1)) C1 →
      ∀ (K : ℝ) (v : Torus d → Torus d → ℝ), Measurable (Function.uncurry v) → (∀ x y, v x y = v y x) →
      IsCanonicalPair (withDensityReal ρ) v → (∀ x y, x ≠ y → |v x y| ≤ K * Env x y) →
        evariance (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered v X)
            (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * K ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set Vc : ℝ := E0 * BB with hVc
  set Cm : ℝ := δC * BA + C1 * BC with hCm
  refine ⟨16 * Vc + 32 * Cm ^ 2, by positivity, fun V hV hVu n hn hκ hRD K v hm hsym hcan hv => ?_⟩
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨hV1, hM1⟩ := rowData_noLog hd β hβ ρ hρ c Mmax M'max γmax Cq Cu hCu δC C1 hδC hC1 hcrit V hV hVu hn hRD
    hEm hBA hBB hBC hEnv K hm hcan hv
  set N : ℕ := n + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnR : (n : ℝ) ≤ N := by simp [hNdef]
  haveI : NeZero n := ⟨by omega⟩
  have hL2 := logEN_sq_le (N := N) hN1
  have hL0 : 0 ≤ logEN N := by linarith [logEN_pos' (N := N) hN1]
  have hVar := pairVar_bound V hβ.le hκ hm hsym (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
    (𝒱 := ENNReal.ofReal (K ^ 2 * Vc)) (𝓜 := |K| * Cm * logEN N) hV1 hM1
  refine hVar.trans ?_
  have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 3 := by
    rw [rpow_sq_neg N (by omega)]
    have : (2 * (3 / 2 : ℝ)) = ((3 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  rw [hc2]
  have hconv : ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 3)) * (((n + 1 : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (2 * n) * ENNReal.ofReal (K ^ 2 * Vc) + ENNReal.ofReal ((|K| * Cm * logEN N) ^ 2)))
      = ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * (2 * n * (K ^ 2 * Vc) +
        (|K| * Cm * logEN N) ^ 2))) := by
    rw [show (((n + 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal (N : ℝ) by rw [ENNReal.ofReal_natCast]]
    have h1 : (0 : ℝ) ≤ 2 * n := by positivity
    rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [hconv]
  refine ENNReal.ofReal_le_ofReal ?_
  exact real_psi (N : ℝ) (n : ℝ) Vc K (logEN N) (|K| * Cm * logEN N) Cm (by exact_mod_cast hN1)
    (Nat.cast_nonneg n) hnR (by positivity) hL2 (by positivity) (by positivity) le_rfl

end PartPsi

section VarInt

/-- The variance integral `∫ |v(x,y)|² e^{M'+βγ+ψ_x(y)} dμ ≤ K² E₀ B_B` (no refined hypotheses). -/
theorem varInt_noLog (hd : 2 ≤ d) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)
    (c Mmax M'max γmax Cq : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (V : WeakPotential (withDensityReal ρ)) (hV : PotBound (d := d) s c Mmax M'max γmax Cq V)
    {Env : Torus d → Torus d → ℝ} {BA BB BC Cu : ℝ} (hBB : 0 ≤ BB)
    (hEnv : EnvBounds (d := d) s Cu (withDensityReal ρ) Env BA BB BC) (K : ℝ)
    {v : Torus d → Torus d → ℝ} (hv : ∀ x y, x ≠ y → |v x y| ≤ K * Env x y) (x : Torus d)
    (pins : Option Empty → Torus d) (hpins : pins = pinsWith (fun e : Empty => e.elim) x) :
    ∫⁻ y, ‖v x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / N) pins y))
        ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (K ^ 2 * (Real.exp (M'max + β * max γmax 0 + Mmax) * BB)) := by
  subst hpins
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := fun x => HRS.External.PoleVar.ae_ne_pt hatom x
  have hlam0 : 0 ≤ β / N := by positivity
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  calc _ ≤ ∫⁻ y, (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal E0) * ENNReal.ofReal (Env x y ^ 2)
        ∂(withDensityReal ρ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae x] with y hy
        have hxy : x ≠ y := Ne.symm hy
        have h1 : ‖v x y‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (Env x y ^ 2) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg _), ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 := pow_le_pow_left₀ (abs_nonneg _) (hv x y hxy) 2
          rw [sq_abs] at h2
          calc v x y ^ 2 ≤ (K * Env x y) ^ 2 := h2
            _ = _ := by ring
        have h2 := poleW_le_const (V := V) hV hβ.le hlam0 (pinsWith (fun e : Empty => e.elim) x) y
        calc ‖v x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
              pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) y))
            ≤ (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (Env x y ^ 2)) * ENNReal.ofReal E0 :=
              mul_le_mul' h1 h2
          _ = _ := by ring
    _ = (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal E0) * ∫⁻ y, ENNReal.ofReal (Env x y ^ 2)
        ∂(withDensityReal ρ) := lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ENNReal.ofReal_ne_top)
    _ ≤ (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal E0) * ENNReal.ofReal BB := by
        gcongr; exact hEnv.B x
    _ = _ := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end VarInt

end HRS.PairMom

end
