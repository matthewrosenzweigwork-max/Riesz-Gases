import HRS.Equilibrium.QuadraticVariance

/-!
# EQ-STATIC-U, part 1: the weak-ensemble quadratic bound, uniform in `β ∈ [β₋,β₊]`

`HRS.Quad.quad_weak_bound` (`A:eq:reference-quadratic`) with the constant chosen BEFORE `β ∈ [β₋,β₊]` and before
the density `ρ ≤ Λ`: the proof is the one of `quad_weak_bound`, with every constant that depended on `β`
replaced by the monotone upper bound at `β₊` (and `max 1 (2/β)` by `max 1 (2/β₋)`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.MD.EQStat

open HRS HRS.Quad HRS.External HRS.External.RefMarg HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

set_option maxHeartbeats 1600000 in
theorem eqstat_quad_weak_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ (ρ : Torus d → ℝ), IsProbDensity ρ → (∀ y, ρ y ≤ Λ) →
      ∀ (V : WeakPotential (withDensityReal ρ)), V.M ≤ Mmax → V.M' ≤ M'max → V.γ ≤ γmax →
      (∀ x y : Torus d, x ≠ y → envT s (x - y) - Cq ≤ V.q x y) →
      ∀ {n : ℕ}, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      ∀ (B : ℝ), 0 ≤ B → ∀ (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h
          ((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map (fun X => X 0)) X)
          (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
        ≤ ENNReal.ofReal (C * B ^ 2 * deltaN d s (n + 1)) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨cH, hcH, hHc⟩ := Hc_bound hd hs0 hsd
  obtain ⟨c₁, hc₁, hvar⟩ := variance_integral_le hd hs0 hsd
  obtain ⟨c₂, hc₂, hmean⟩ := mean_one_le hd hs0 hsd
  set cc : ℝ := max 1 (2 / βm) with hcc
  have hcc0 : 0 < cc := lt_max_of_lt_left one_pos
  obtain ⟨cg, hcg, hgm⟩ := gFun_mul_le hd hs0 hsd hcc0
  set γ' : ℝ := max γmax 0 with hγ'
  set Cp : ℝ := Real.exp (Mmax + M'max + βp * γ') with hCp
  have hCp0 : 0 < Cp := Real.exp_pos _
  set HB : ℝ := cH * Cp * Λ with hHB
  have hHB0 : 0 ≤ HB := by positivity
  set bb : ℝ := 1 + 3 * HB with hbb
  have hbb1 : 1 ≤ bb := by linarith
  set M0 : ℝ := Mmax + M'max + βp * γ' + βp * Cq with hM0
  set C6 : ℝ := 2 * bb + 2 * c₂ * Cp * Λ * bb + HB with hC6
  have hC60 : 0 ≤ C6 := by positivity
  refine ⟨16 * c₁ * Λ * bb ^ 2 * Real.exp M0 * cg + 8 * C6 ^ 2 + 1, by positivity, ?_⟩
  intro β hβ1 hβ2 ρ hρ hΛ V hVM hVM' hVγ hq n hn hκ B hB h hm hsym hh
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hγ'0 : 0 ≤ γ' := le_max_right _ _
  have hβγ : β * V.γ ≤ βp * γ' :=
    (mul_le_mul_of_nonneg_left (hVγ.trans (le_max_left _ _)) hβ.le).trans
      (mul_le_mul_of_nonneg_right hβ2 hγ'0)
  haveI : NeZero n := ⟨by omega⟩
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamβ : lam ≤ β := by
    rw [hlam, div_le_iff₀ hNpos]; exact le_mul_of_one_le_right hβ.le hNR
  set R := pinnedLaw V lam (n + 1) (fun e : Empty => e.elim) with hR
  haveI hRp : IsProbabilityMeasure R := isProb_pinnedLaw V hlam0.le (n + 1) _
  set π : Measure (Torus d) := R.map (fun X => X 0) with hπ
  haveI hπp : IsProbabilityMeasure π := inferInstance
  have hVC : Real.exp (V.M + V.M' + β * V.γ) ≤ Cp := by
    refine Real.exp_le_exp.2 ?_
    have h1 := hβγ
    linarith
  have hπle : π ≤ ENNReal.ofReal Cp • withDensityReal ρ := by
    have h1 := marginal_le_smul (B := Empty) V hβ.le hN0 (n := n + 1) (by simp) (fun e : Empty => e.elim) 0
    refine h1.trans ?_
    refine Measure.le_iff'.2 fun A => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hVC) le_rfl
  have hνle : ∀ (x : Torus d) (k : Fin n), (pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
      (fun Y => Y k) ≤ ENNReal.ofReal Cp • withDensityReal ρ := by
    intro x k
    have h1 := pinned_marginal_le_density (B := Option Empty) V hβ.le hN0 (n := n)
      (by simp) (pinsWith (fun e : Empty => e.elim) x) k
    refine Measure.le_iff.2 fun A hA => (h1 A).trans ?_
    rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul]
    calc ∫⁻ z in A, ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V lam
          (pinsWith (fun e : Empty => e.elim) x) z)) ∂(withDensityReal ρ)
        ≤ ∫⁻ _z in A, ENNReal.ofReal Cp ∂(withDensityReal ρ) := by
          refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have h2 := (isField_pinField V hlam0.le (pinsWith (fun e : Empty => e.elim) x)).le z
          have h3 := hβγ
          linarith
      _ = ENNReal.ofReal Cp * withDensityReal ρ A := by rw [setLIntegral_const, mul_comm]
  -- the one-point function and the centered kernel
  have hHcB : ∀ x, |Hc h π x| ≤ HB * B := fun x => by
    have := hHc hΛ hΛ0 hπle hCp0.le hB hh x
    simpa [hHB] using this
  have hcK : ∀ x y : Torus d, y ≠ x → |cK h π x y| ≤ (bb * B) * envT s (x - y) := by
    intro x y hy
    have := abs_cK_le (s := s) π hB hHcB hh x y hy
    have e : B + 3 * (HB * B) = bb * B := by rw [hbb]; ring
    rwa [e] at this
  have hHm : Measurable (Hc h π) := measurable_Hc hm π
  have hHi : Integrable (Hc h π) π :=
    Integrable.of_bound hHm.aestronglyMeasurable (HB * B) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hHcB x)
  have hhint : ∀ x, Integrable (h x) π := fun x =>
    integrable_of_env_bound hd hs0 hsd hΛ hΛ0 hπle hCp0.le hB (measurable_h_x hm x) (fun y hy => by
      have := hh x y (Ne.symm hy)
      rwa [eucDist_sub] at this)
  have hzero : ∀ x, ∫ y, cK h π x y ∂π = 0 := fun x => integral_cK_eq_zero π x (hhint x) hHi
  -- the variance integral with retained repulsion
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hccN1 : 1 ≤ cc * N := by
    have : 1 ≤ cc := le_max_left _ _
    exact one_le_mul_of_one_le_of_one_le this hNR
  have hccN2 : 2 / lam ≤ cc * N := by
    rw [hlam, div_div_eq_mul_div, div_le_iff₀ hβ]
    have h1 : 2 / β ≤ cc := (div_le_div_of_nonneg_left (by norm_num) hβm hβ1).trans (le_max_right _ _)
    have h2 : 2 ≤ cc * β := by
      rw [div_le_iff₀ hβ] at h1; exact h1
    calc 2 * N ≤ (cc * β) * N := mul_le_mul_of_nonneg_right h2 hNpos.le
      _ = cc * N * β := by ring
  have hVx : ∀ x : Torus d, ∫⁻ y, ‖cK h π x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V lam (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 * (cg * gFun d s N)) := by
    intro x
    have h1 := hvar hΛ hΛ0 (b := bb * B) (by positivity) (x := x) (lam := lam) (K := cc * N) (M0 := M0)
      hlam0 hccN1 hccN2 (f := cK h π x) (ψ := fun y => V.M' + β * V.γ +
        pinField V lam (pinsWith (fun e : Empty => e.elim) x) y) (fun y hy => hcK x y hy) (fun y hy => by
        rw [pinField_pinsWith, pinField_empty]
        have h2 := V.φ_le y
        have h3 := hq y x hy
        rw [envT_sub_comm y x] at h3
        have h4 := hβγ
        have h5 : lam * Cq ≤ βp * Cq := mul_le_mul_of_nonneg_right (hlamβ.trans hβ2) hCq
        have h6 : lam * (envT s (x - y) - Cq) ≤ lam * V.q y x := mul_le_mul_of_nonneg_left h3 hlam0.le
        rw [hM0]
        linarith)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 := hgm N hNR hccN1
    have h3 : 0 ≤ c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 := by positivity
    calc c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 * gFun d s (cc * N)
        ≤ c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 * (cg * gFun d s N) := mul_le_mul_of_nonneg_left h2 h3
      _ = _ := rfl
  -- the mean of the row
  have hp := one_lt_pOf hd hs0 hsd
  set K : ℝ := N ^ (1 / pOf d s) with hKdef
  have hK1 : 1 ≤ K := Real.one_le_rpow hNR (by positivity)
  set ε : ℝ := 2 * weakKappa V β / N with hεdef
  have hκ0 : 0 ≤ weakKappa V β := weakKappa_nonneg V hβ.le
  have hε0 : 0 ≤ ε := by positivity
  have hNK : N * K ^ (1 - pOf d s) = K := rpow_identity hNpos (by linarith)
  have hcKm : ∀ x, Measurable (cK h π x) := fun x => by
    unfold cK
    exact (((measurable_h_x hm x).sub measurable_const).sub hHm).add measurable_const
  have hMx : ∀ x : Torus d, |∑ k : Fin n, ∫ y, cK h π x y ∂((pinnedLaw V lam n
      (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)) - Hc h π x| ≤ C6 * B * K := by
    intro x
    have hper : ∀ k : Fin n, |∫ y, cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
        (fun Y => Y k))| ≤ 2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s)) := by
      intro k
      haveI := isProb_pinnedLaw V hlam0.le n (pinsWith (fun e : Empty => e.elim) x)
      have := hmean hΛ hΛ0 hCp0.le (b := bb * B) (by positivity) (x := x) (ε := ε) (K := K) hε0 hK1
        (π := π) (ν := (pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))
        hπle (hνle x k) (fun A hA => tv_pin_le V hβ.le hκ x k hA) (hcKm x) (fun y hy => hcK x y hy)
      rwa [hzero x, sub_zero] at this
    have hsum : |∑ k : Fin n, ∫ y, cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
        (fun Y => Y k))| ≤ (n : ℝ) * (2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k : Fin n, |∫ y, cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
            (fun Y => Y k))| ≤ ∑ _k : Fin n, (2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s))) :=
            Finset.sum_le_sum fun k _ => hper k
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnN : (n : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith
    have hper0 : 0 ≤ 2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s)) := by positivity
    have hnper : (n : ℝ) * (2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s)))
        ≤ (2 + 2 * c₂ * Cp * Λ) * (bb * B) * K := by
      calc (n : ℝ) * (2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s)))
          ≤ N * (2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s))) :=
            mul_le_mul_of_nonneg_right hnN hper0
        _ = 2 * (bb * B) * K * (N * ε) + 2 * (c₂ * Cp * Λ * (bb * B)) * (N * K ^ (1 - pOf d s)) := by ring
        _ = 2 * (bb * B) * K * (2 * weakKappa V β) + 2 * (c₂ * Cp * Λ * (bb * B)) * K := by
            rw [hNK, hεdef]; field_simp
        _ ≤ 2 * (bb * B) * K * 1 + 2 * (c₂ * Cp * Λ * (bb * B)) * K := by
            gcongr
            linarith
        _ = _ := by ring
    have hHx : |Hc h π x| ≤ HB * B * K := by
      calc |Hc h π x| ≤ HB * B := hHcB x
        _ ≤ HB * B * K := by
          have : 0 ≤ HB * B := by positivity
          exact le_mul_of_one_le_right this hK1
    calc |∑ k : Fin n, ∫ y, cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
          (fun Y => Y k)) - Hc h π x|
        ≤ |∑ k : Fin n, ∫ y, cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
          (fun Y => Y k))| + |Hc h π x| := abs_sub _ _
      _ ≤ (2 + 2 * c₂ * Cp * Λ) * (bb * B) * K + HB * B * K := add_le_add (hsum.trans hnper) hHx
      _ = C6 * B * K := by rw [hC6]; ring
  -- assembly
  have hfin := quad_reference_le V hβ.le hκ hm hsym π
    (𝒱 := ENNReal.ofReal (c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 * (cg * gFun d s N))) (𝓜 := C6 * B * K) hVx hMx
  refine hfin.trans ?_
  have hg1 : 1 ≤ gFun d s N := one_le_gFun hd hs0 hsd hNR
  have hK2 : K ^ 2 ≤ N * gFun d s N := by
    have e : K ^ 2 = N ^ (2 / pOf d s) := by
      rw [hKdef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      congr 1; push_cast; ring
    rw [e]; exact rpow_two_div_le hd hs0 hsd hNR
  have hδ : deltaN d s (n + 1) = N⁻¹ * gFun d s N := deltaN_eq_gFun hd hs0 hsd hN0
  have hnN : (n : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hδ]
  set g := gFun d s N with hgdef
  set D₁ : ℝ := c₁ * Λ * bb ^ 2 * Real.exp M0 * cg with hD₁
  have hD0 : 0 ≤ D₁ := by positivity
  have e1 : c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 * (cg * g) = D₁ * B ^ 2 * g := by rw [hD₁]; ring
  rw [e1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have e2 : (16 * c₁ * Λ * bb ^ 2 * Real.exp M0 * cg + 8 * C6 ^ 2 + 1) * B ^ 2 * (N⁻¹ * g) * N ^ 2
      = (16 * D₁ + 8 * C6 ^ 2 + 1) * B ^ 2 * g * N := by
    rw [hD₁]; field_simp
  rw [e2]
  have h1 : 8 * (2 * (n : ℝ) * (D₁ * B ^ 2 * g) + (C6 * B * K) ^ 2)
      ≤ 8 * (2 * N * (D₁ * B ^ 2 * g) + C6 ^ 2 * B ^ 2 * (N * g)) := by
    have : (C6 * B * K) ^ 2 = C6 ^ 2 * B ^ 2 * K ^ 2 := by ring
    rw [this]
    gcongr
  have h2 : 0 ≤ B ^ 2 * g * N := by positivity
  linarith [h1, h2]

end HRS.MD.EQStat

end
