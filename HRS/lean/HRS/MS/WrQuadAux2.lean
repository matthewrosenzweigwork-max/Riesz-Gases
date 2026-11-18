import HRS.MS.WrQuadAux1

/-!
# HRS.MS.WrQuadAux2 -- reference quadratic bound, change of centering, crude bound (WR-14a, part 2)

Packet WR-14a of `docs/WR_B_PLAN.md` (T12; TeX `euc-reference-quadratic`, change of centering, `euc-quadratic`),
namespace `HRS.MS.Wr`, helper prefix `wr14a_`.  Euclidean port of `HRS/Equilibrium/QuadraticVariance.lean`
(`quad_weak_bound:1348`, `evariance_quad_change:1612`, `change_term_le:1682`, `quadStat_sq_le:1814`,
`quad_crude_weak:1853`).

All statements are for a generic weak potential `V : WeakPotential μ` (`μ = ρ dx`, `ρ ≤ M`) whose pair kernel
satisfies the lower envelope `q(x,y) ≥ W_s(x-y) - C_q` (`W_s = rieszWeight s`); the constants are uniform in
`ρ ≤ M` and in `β ∈ [β₋, β₊]` (the rate `J_s(β/N)` of the retained repulsion is compared with `gFun d s N`
uniformly for `β ∈ [β₋, β₊]`, `wr14a_J_le_gFun`).

* `wr14a_quad_weak_bound`: `N Var_R[D_N(h;π^R)] ≤ C B² δ_N` for the pinned weak ensemble `R`, `π^R = R^{(1)}`
  (this is `quad_reference_E` of the plan; with `V = weakPotE` it is the calibrated reference `R_N`);
* `wr14a_evariance_quad_change`, `wr14a_change_term_le`: change of the centering measure
  (`N Var_R D_N(h;ν) ≤ 2 N Var_R D_N(h;π) + 16 ∫ |H_ν - H_π|² dπ`, and Schur's test with the kernel `1 + W_s`);
* `wr14a_quad_crude_weak`: crude second-moment bound for fixed `n` (no smallness), used for finitely many `N`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.Wr

open HRS.External

variable {d : ℕ} {s : ℝ}

/-! ### Arithmetic of the rates -/

theorem wr14a_W_symm (z : Euc d) : HRS.Whole.rieszWeight s (-z) = HRS.Whole.rieszWeight s z := by
  unfold HRS.Whole.rieszWeight
  rw [norm_neg]

theorem wr14a_W_sub_comm (x y : Euc d) :
    HRS.Whole.rieszWeight s (y - x) = HRS.Whole.rieszWeight s (x - y) := by
  rw [← neg_sub x y, wr14a_W_symm]

/-- The radial rate `J_s(β/N)` is controlled by `gFun d s N`, uniformly for `β ∈ [β₋, β₊]`. -/
theorem wr14a_J_le_gFun (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm) :
    ∃ c : ℝ, 0 < c ∧ ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ {N : ℝ}, 1 ≤ N →
      wr13c_J d s (β / N) ≤ c * RefMarg.gFun d s N := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set L : ℝ := |Real.log βm| + |Real.log βp| with hL
  set e : ℝ := (d : ℝ) / s - 2 with he
  have hL0 : 0 ≤ L := by positivity
  have hβm0 : 0 < βm ^ e := Real.rpow_pos_of_pos hβm _
  refine ⟨1 + (1 + L) + (1 + βm ^ e), by positivity, fun {β} hβ1 hβ2 {N} hN => ?_⟩
  have hβ0 : 0 < β := hβm.trans_le hβ1
  have hN0 : 0 < N := by linarith
  have hg1 := RefMarg.one_le_gFun hd hs0.le hsd hN
  unfold wr13c_J
  by_cases h1 : 2 * s < d
  · have hg : RefMarg.gFun d s N = 1 := by
      unfold RefMarg.gFun; rw [if_pos (by linarith)]
    rw [if_pos h1, hg]
    nlinarith
  · by_cases h2 : 2 * s = d
    · have hg : RefMarg.gFun d s N = 1 + Real.log N := by
        unfold RefMarg.gFun
        rw [if_neg (by linarith), if_pos (by linarith), Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
      rw [if_neg h1, if_pos h2, hg]
      have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
      have hlb : |Real.log β| ≤ L := by
        have h3 : Real.log βm ≤ Real.log β := Real.log_le_log hβm hβ1
        have h4 : Real.log β ≤ Real.log βp := Real.log_le_log hβ0 hβ2
        rw [hL]
        rw [abs_le]
        constructor <;> nlinarith [abs_nonneg (Real.log βm), abs_nonneg (Real.log βp),
          neg_abs_le (Real.log βm), le_abs_self (Real.log βp)]
      have hlog : |Real.log (β / N)| ≤ L + Real.log N := by
        rw [Real.log_div hβ0.ne' hN0.ne']
        rw [abs_le]
        have := abs_le.1 hlb
        constructor <;> linarith [this.1, this.2]
      nlinarith [mul_nonneg hL0 hlogN]
    · have h3 : (d : ℝ) < 2 * s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
      have hg : RefMarg.gFun d s N = N ^ (2 - (d : ℝ) / s) := by
        unfold RefMarg.gFun
        rw [if_neg (by intro hh; apply h1; linarith), if_neg (by intro hh; apply h2; linarith)]
      have hed : e < 0 := by
        rw [he]
        have : (d : ℝ) / s < 2 := by rw [div_lt_iff₀ hs0]; linarith
        linarith
      rw [if_neg h1, if_neg h2, hg]
      have hNe : 1 ≤ N ^ (2 - (d : ℝ) / s) := Real.one_le_rpow hN (by linarith)
      have hdiv : (β / N) ^ e = β ^ e * N ^ (2 - (d : ℝ) / s) := by
        rw [Real.div_rpow hβ0.le hN0.le, div_eq_mul_inv, ← Real.rpow_neg hN0.le]
        congr 2
        rw [he]; ring
      have hβe : β ^ e ≤ βm ^ e := Real.rpow_le_rpow_of_nonpos hβm hβ1 hed.le
      rw [show (d : ℝ) / s - 2 = e from rfl, hdiv]
      have : β ^ e * N ^ (2 - (d : ℝ) / s) ≤ βm ^ e * N ^ (2 - (d : ℝ) / s) :=
        mul_le_mul_of_nonneg_right hβe (by linarith)
      nlinarith

/-! ### The reference quadratic bound -/

set_option maxHeartbeats 1600000 in
/-- **`quad_reference_E`** (TeX `euc-reference-quadratic`): for the pinned weak ensemble `R` of a weak potential
`V` with `q ≥ W_s - C_q` off the diagonal and `κ ≤ 1/2`, and `|h| ≤ B (1 + W_s)` off the diagonal,
`N Var_R[D_N(h; π^R)] ≤ C B² δ_N`, `π^R = R^{(1)}`, `N = n + 1`, uniformly in `ρ ≤ M`, `β ∈ [β₋, β₊]`. -/
theorem wr14a_quad_weak_bound (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (M Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ (V : WeakPotential (HRS.Whole.withDensityReal ρ)), V.M ≤ Mmax → V.M' ≤ M'max → V.γ ≤ γmax →
      (∀ x y : Euc d, x ≠ y → HRS.Whole.rieszWeight s (x - y) - Cq ≤ V.q x y) →
      ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ {n : ℕ}, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      ∀ (B : ℝ), 0 ≤ B → ∀ (h : Euc d → Euc d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X
          ((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map (fun X => X 0)))
          (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
        ≤ ENNReal.ofReal (C * B ^ 2 * deltaN d s (n + 1)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨cH, hcH0, hHc⟩ := wr14a_Hc_bound hd1 hs0.le hsd M
  obtain ⟨c₁, hc₁0, hvar⟩ := wr14a_variance_integral_le hd1 hs0 hsd M
  obtain ⟨c₂, hc₂0, hmean⟩ := wr14a_mean_one_le hd1 hs0 hsd M
  obtain ⟨cJ, hcJ, hJ⟩ := wr14a_J_le_gFun hd hs0 hsd (βp := βp) hβm
  set γ' : ℝ := max γmax 0 with hγ'
  have hγ'0 : 0 ≤ γ' := le_max_right _ _
  set Cp : ℝ := Real.exp (Mmax + M'max + βp * γ') with hCp
  have hCp0 : 0 < Cp := Real.exp_pos _
  set HB : ℝ := cH * Cp with hHB
  have hHB0 : 0 ≤ HB := by positivity
  set bb : ℝ := 1 + 3 * HB with hbb
  have hbb1 : 1 ≤ bb := by linarith
  set M0 : ℝ := Mmax + M'max + βp * γ' + βp * Cq with hM0
  set C6 : ℝ := 4 * bb + 2 * c₂ * Cp * bb + HB with hC6
  have hC60 : 0 ≤ C6 := by positivity
  set D₁ : ℝ := c₁ * bb ^ 2 * Real.exp M0 * cJ with hD₁
  have hD0 : 0 ≤ D₁ := by positivity
  refine ⟨16 * D₁ + 8 * C6 ^ 2 + 1, by positivity, ?_⟩
  intro ρ hρ hM V hVM hVM' hVγ hq β hβ1 hβ2 n hn hκ B hB h hm hsym hh
  haveI : NeZero n := ⟨by omega⟩
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hM0' : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamβ : lam ≤ β := by
    rw [hlam, div_le_iff₀ hNpos]; exact le_mul_of_one_le_right hβpos.le hNR
  set R := pinnedLaw V lam (n + 1) (fun e : Empty => e.elim) with hR
  haveI hRp : IsProbabilityMeasure R := isProb_pinnedLaw V hlam0.le (n + 1) _
  set π : Measure (Euc d) := R.map (fun X => X 0) with hπ
  haveI hπp : IsProbabilityMeasure π := inferInstance
  have hβγ : β * V.γ ≤ βp * γ' :=
    mul_le_mul hβ2 (hVγ.trans (le_max_left _ _)) V.γ_nonneg (hβpos.le.trans hβ2)
  have hVC : Real.exp (V.M + V.M' + β * V.γ) ≤ Cp := by
    refine Real.exp_le_exp.2 ?_
    linarith
  have hπle : π ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ := by
    have h1 := RefMarg.marginal_le_smul (B := Empty) V hβpos.le hN0 (n := n + 1) (by simp)
      (fun e : Empty => e.elim) 0
    refine h1.trans ?_
    refine Measure.le_iff'.2 fun A => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hVC) le_rfl
  have hνle : ∀ (x : Euc d) (k : Fin n), (pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
      (fun Y => Y k) ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ := by
    intro x k
    have h1 := HRS.Quad.pinned_marginal_le_density (B := Option Empty) V hβpos.le hN0 (n := n)
      (by simp) (pinsWith (fun e : Empty => e.elim) x) k
    refine Measure.le_iff.2 fun A hA => (h1 A).trans ?_
    rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul]
    calc ∫⁻ z in A, ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V lam
          (pinsWith (fun e : Empty => e.elim) x) z)) ∂(HRS.Whole.withDensityReal ρ)
        ≤ ∫⁻ _z in A, ENNReal.ofReal Cp ∂(HRS.Whole.withDensityReal ρ) := by
          refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have h2 := (isField_pinField V hlam0.le (pinsWith (fun e : Empty => e.elim) x)).le z
          linarith
      _ = ENNReal.ofReal Cp * HRS.Whole.withDensityReal ρ A := by rw [setLIntegral_const, mul_comm]
  -- the one-point function and the centered kernel
  have hHcB : ∀ x, |wr14a_Hc h π x| ≤ HB * B := fun x => by
    have := hHc hρ hM hπle hCp0.le hB hh x
    simpa [hHB, mul_comm, mul_assoc, mul_left_comm] using this
  have hcK : ∀ x y : Euc d, y ≠ x →
      |wr14a_cK h π x y| ≤ (bb * B) * (1 + HRS.Whole.rieszWeight s (x - y)) := by
    intro x y hy
    have := wr14a_abs_cK_le (s := s) π hB hHcB hh x y hy
    have e : B + 3 * (HB * B) = bb * B := by rw [hbb]; ring
    rwa [e] at this
  have hHm : Measurable (wr14a_Hc h π) := wr14a_measurable_Hc hm π
  have hHi : Integrable (wr14a_Hc h π) π :=
    Integrable.of_bound hHm.aestronglyMeasurable (HB * B) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hHcB x)
  have hhint : ∀ x, Integrable (h x) π := fun x =>
    wr14a_integrable_of_env_bound hd1 hs0.le hsd M hρ hM hπle hCp0.le hB (wr14a_measurable_h_x hm x)
      (fun y hy => hh x y (Ne.symm hy))
  have hzero : ∀ x, ∫ y, wr14a_cK h π x y ∂π = 0 := fun x => wr14a_integral_cK_eq_zero π x (hhint x) hHi
  -- the variance integral with retained repulsion
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hVx : ∀ x : Euc d, ∫⁻ y, ‖wr14a_cK h π x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V lam (pinsWith (fun e : Empty => e.elim) x) y)) ∂(HRS.Whole.withDensityReal ρ)
      ≤ ENNReal.ofReal (c₁ * (bb * B) ^ 2 * Real.exp M0 * (cJ * RefMarg.gFun d s N)) := by
    intro x
    have h1 := hvar hρ hM (b := bb * B) (by positivity) (x := x) (lam := lam) (M0 := M0) hlam0
      (f := wr14a_cK h π x) (ψ := fun y => V.M' + β * V.γ +
        pinField V lam (pinsWith (fun e : Empty => e.elim) x) y) (fun y hy => hcK x y hy) (fun y hy => by
        rw [pinField_pinsWith, RefMarg.pinField_empty]
        have h2 := V.φ_le y
        have h3 := hq y x hy
        rw [wr14a_W_sub_comm x y] at h3
        have h5 : lam * Cq ≤ βp * Cq :=
          mul_le_mul_of_nonneg_right (hlamβ.trans hβ2) hCq
        have h6 : lam * (HRS.Whole.rieszWeight s (x - y) - Cq) ≤ lam * V.q y x :=
          mul_le_mul_of_nonneg_left h3 hlam0.le
        rw [hM0]
        nlinarith)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : wr13c_J d s lam ≤ cJ * RefMarg.gFun d s N := hJ hβ1 hβ2 hNR
    have h3 : 0 ≤ c₁ * (bb * B) ^ 2 * Real.exp M0 := by positivity
    exact mul_le_mul_of_nonneg_left h2 h3
  -- the mean of the row
  have hp := RefMarg.one_lt_pOf hd hs0.le hsd
  have hpd : RefMarg.pOf d s = (d : ℝ) / s := by simp [RefMarg.pOf, hs0.ne']
  set K : ℝ := N ^ (1 / RefMarg.pOf d s) with hKdef
  have hK1 : 1 ≤ K := Real.one_le_rpow hNR (by positivity)
  set ε : ℝ := 2 * weakKappa V β / N with hεdef
  have hκ0 : 0 ≤ weakKappa V β := weakKappa_nonneg V hβpos.le
  have hε0 : 0 ≤ ε := by positivity
  have hNK : N * K ^ (1 - RefMarg.pOf d s) = K := HRS.Quad.rpow_identity hNpos (by linarith)
  have hcKm : ∀ x, Measurable (wr14a_cK h π x) := fun x => by
    unfold wr14a_cK
    exact (((wr14a_measurable_h_x hm x).sub measurable_const).sub hHm).add measurable_const
  have hMx : ∀ x : Euc d, |∑ k : Fin n, ∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n
      (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)) - wr14a_Hc h π x| ≤ C6 * B * K := by
    intro x
    have hper : ∀ k : Fin n, |∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
        (fun Y => Y k))| ≤ 4 * (bb * B) * K * ε + 2 * (c₂ * Cp * (bb * B) * K ^ (1 - RefMarg.pOf d s)) := by
      intro k
      haveI := isProb_pinnedLaw V hlam0.le n (pinsWith (fun e : Empty => e.elim) x)
      have := hmean hρ hM hCp0.le (b := bb * B) (by positivity) (x := x) (ε := ε) (K := K) hε0 hK1
        (π := π) (ν := (pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))
        hπle (hνle x k) (fun A hA => wr14a_tv_pin_le V hβpos.le hκ x k hA) (hcKm x)
        (fun y hy => hcK x y hy)
      rw [hzero x, sub_zero] at this
      rw [hpd]
      exact this
    have hsum : |∑ k : Fin n, ∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
        (fun Y => Y k))| ≤ (n : ℝ) * (4 * (bb * B) * K * ε + 2 * (c₂ * Cp * (bb * B) * K ^ (1 - RefMarg.pOf d s))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k : Fin n, |∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
            (fun Y => Y k))| ≤ ∑ _k : Fin n, (4 * (bb * B) * K * ε + 2 * (c₂ * Cp * (bb * B) * K ^ (1 - RefMarg.pOf d s))) :=
            Finset.sum_le_sum fun k _ => hper k
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnN : (n : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith
    have hper0 : 0 ≤ 4 * (bb * B) * K * ε + 2 * (c₂ * Cp * (bb * B) * K ^ (1 - RefMarg.pOf d s)) := by positivity
    have hnper : (n : ℝ) * (4 * (bb * B) * K * ε + 2 * (c₂ * Cp * (bb * B) * K ^ (1 - RefMarg.pOf d s)))
        ≤ (4 + 2 * c₂ * Cp) * (bb * B) * K := by
      calc (n : ℝ) * (4 * (bb * B) * K * ε + 2 * (c₂ * Cp * (bb * B) * K ^ (1 - RefMarg.pOf d s)))
          ≤ N * (4 * (bb * B) * K * ε + 2 * (c₂ * Cp * (bb * B) * K ^ (1 - RefMarg.pOf d s))) :=
            mul_le_mul_of_nonneg_right hnN hper0
        _ = 4 * (bb * B) * K * (N * ε) + 2 * (c₂ * Cp * (bb * B)) * (N * K ^ (1 - RefMarg.pOf d s)) := by ring
        _ = 4 * (bb * B) * K * (2 * weakKappa V β) + 2 * (c₂ * Cp * (bb * B)) * K := by
            rw [hNK, hεdef]; field_simp
        _ ≤ 4 * (bb * B) * K * 1 + 2 * (c₂ * Cp * (bb * B)) * K := by
            gcongr
            linarith
        _ = _ := by ring
    have hHx : |wr14a_Hc h π x| ≤ HB * B * K := by
      calc |wr14a_Hc h π x| ≤ HB * B := hHcB x
        _ ≤ HB * B * K := by
          have : 0 ≤ HB * B := by positivity
          exact le_mul_of_one_le_right this hK1
    calc |∑ k : Fin n, ∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
          (fun Y => Y k)) - wr14a_Hc h π x|
        ≤ |∑ k : Fin n, ∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
          (fun Y => Y k))| + |wr14a_Hc h π x| := abs_sub _ _
      _ ≤ (4 + 2 * c₂ * Cp) * (bb * B) * K + HB * B * K := add_le_add (hsum.trans hnper) hHx
      _ = C6 * B * K := by rw [hC6]; ring
  -- assembly
  have hfin := wr14a_quad_reference_le V hβpos.le hκ hm hsym π
    (𝒱 := ENNReal.ofReal (c₁ * (bb * B) ^ 2 * Real.exp M0 * (cJ * RefMarg.gFun d s N))) (𝓜 := C6 * B * K) hVx hMx
  refine hfin.trans ?_
  have hg1 : 1 ≤ RefMarg.gFun d s N := RefMarg.one_le_gFun hd hs0.le hsd hNR
  have hK2 : K ^ 2 ≤ N * RefMarg.gFun d s N := by
    have e : K ^ 2 = N ^ (2 / RefMarg.pOf d s) := by
      rw [hKdef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      congr 1; push_cast; ring
    rw [e]; exact HRS.Quad.rpow_two_div_le hd hs0.le hsd hNR
  have hδ : deltaN d s (n + 1) = N⁻¹ * RefMarg.gFun d s N := RefMarg.deltaN_eq_gFun hd hs0.le hsd hN0
  have hnN : (n : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hδ]
  set g := RefMarg.gFun d s N with hgdef
  have e1 : c₁ * (bb * B) ^ 2 * Real.exp M0 * (cJ * g) = D₁ * B ^ 2 * g := by rw [hD₁]; ring
  rw [e1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have e2 : (16 * D₁ + 8 * C6 ^ 2 + 1) * B ^ 2 * (N⁻¹ * g) * N ^ 2
      = (16 * D₁ + 8 * C6 ^ 2 + 1) * B ^ 2 * g * N := by
    field_simp
  rw [e2]
  have h1 : 8 * (2 * (n : ℝ) * (D₁ * B ^ 2 * g) + (C6 * B * K) ^ 2)
      ≤ 8 * (2 * N * (D₁ * B ^ 2 * g) + C6 ^ 2 * B ^ 2 * (N * g)) := by
    have : (C6 * B * K) ^ 2 = C6 ^ 2 * B ^ 2 * K ^ 2 := by ring
    rw [this]
    gcongr
  have h2 : 0 ≤ B ^ 2 * g * N := by positivity
  nlinarith [h1, h2]

/-! ### Change of the centering measure -/

section Change

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- `D_N(h;ν) - D_N(h;π) = -(2/N) ∑_i φ(x_i) + (h₀(ν) - h₀(π))`, `φ = H_ν - H_π`. -/
theorem wr14a_D_sub_eq (h : Euc d → Euc d → ℝ) (π ν : Measure (Euc d)) {N : ℕ} (X : Fin N → Euc d) :
    HRS.Whole.centeredPairFunctional h X ν = HRS.Whole.centeredPairFunctional h X π +
      ((-(2 / (N : ℝ))) * ∑ i, (wr14a_Hc h ν (X i) - wr14a_Hc h π (X i)) + (wr14a_h0 h ν - wr14a_h0 h π)) := by
  unfold HRS.Whole.centeredPairFunctional wr14a_Hc wr14a_h0
  simp only [Finset.sum_sub_distrib, mul_sub]
  ring

/-- **Change of the centering measure**:
`N Var_R D_N(h;ν) ≤ 2 N Var_R D_N(h;π) + 16 ∫ |H_ν - H_π|² dπ`, `π = R^{(1)}`. -/
theorem wr14a_evariance_quad_change (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} [NeZero N]
    (hκ : weakKappa V β ≤ 1 / 2) {h : Euc d → Euc d → ℝ} (hm : Measurable (Function.uncurry h))
    (ν : Measure (Euc d)) [IsProbabilityMeasure ν] :
    ((N : ℕ) : ℝ≥0∞) * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν)
        (pinnedLaw V (β / N) N (fun e : Empty => e.elim))
      ≤ 2 * ((N : ℕ) : ℝ≥0∞) * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X
          ((pinnedLaw V (β / N) N (fun e : Empty => e.elim)).map (fun X => X 0)))
          (pinnedLaw V (β / N) N (fun e : Empty => e.elim))
        + 16 * ∫⁻ x, ‖wr14a_Hc h ν x - wr14a_Hc h ((pinnedLaw V (β / N) N (fun e : Empty => e.elim)).map
            (fun X => X 0)) x‖ₑ ^ 2
          ∂((pinnedLaw V (β / N) N (fun e : Empty => e.elim)).map (fun X => X 0)) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlam : 0 ≤ β / N := div_nonneg hβ hNR.le
  set R := pinnedLaw V (β / N) N (fun e : Empty => e.elim) with hR
  haveI : IsProbabilityMeasure R := isProb_pinnedLaw V hlam N _
  set π : Measure (Euc d) := R.map (fun X => X 0) with hπ
  set φ : Euc d → ℝ := fun x => wr14a_Hc h ν x - wr14a_Hc h π x with hφ
  have hφm : Measurable φ := (wr14a_measurable_Hc hm ν).sub (wr14a_measurable_Hc hm π)
  have hS : Measurable (fun X : Fin N → Euc d => ∑ i, φ (X i)) :=
    Finset.measurable_sum _ fun i _ => hφm.comp (measurable_pi_apply i)
  set c0 : ℝ := wr14a_h0 h ν - wr14a_h0 h π with hc0
  have hFπ : Measurable (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X π) :=
    wr14a_measurable_D hm π
  have e1 : (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν) = fun X =>
      HRS.Whole.centeredPairFunctional h X π + ((-(2 / (N : ℝ))) * ∑ i, φ (X i) + c0) :=
    funext fun X => wr14a_D_sub_eq h π ν X
  have hG : Measurable (fun X : Fin N → Euc d => (-(2 / (N : ℝ))) * ∑ i, φ (X i) + c0) :=
    (hS.const_mul _).add_const _
  have h1 : evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν) R ≤
      2 * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X π) R +
        2 * evariance (fun X : Fin N → Euc d => (-(2 / (N : ℝ))) * ∑ i, φ (X i) + c0) R := by
    rw [e1]
    exact HRS.Quad.evariance_add_le' hFπ.aestronglyMeasurable hG.aestronglyMeasurable
  have h2 : evariance (fun X : Fin N → Euc d => (-(2 / (N : ℝ))) * ∑ i, φ (X i) + c0) R
      = ENNReal.ofReal ((2 / (N : ℝ)) ^ 2) * evariance (fun X : Fin N → Euc d => ∑ i, φ (X i)) R := by
    rw [evariance_add_const' R (hS.const_mul _).aestronglyMeasurable c0, evariance_mul]
    congr 2; ring
  have h4 : evariance (fun X : Fin N → Euc d => ∑ i, φ (X i)) R ≤ 2 * N * evariance φ π :=
    weak_linear_variance_symm (B := Empty) V hβ hN0 (by simp) (fun e : Empty => e.elim) hκ φ hφm
  have h5 : evariance φ π ≤ ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂π := by
    have := evariance_le_lintegral_sub π hφm.aestronglyMeasurable 0
    simpa using this
  have e : ENNReal.ofReal ((2 / (N : ℝ)) ^ 2) * (N : ℝ≥0∞) * (N : ℝ≥0∞) = 4 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have : (2 / (N : ℝ)) ^ 2 * N * N = 4 := by field_simp; norm_num
    rw [this]; simp
  calc (N : ℝ≥0∞) * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X ν) R
      ≤ (N : ℝ≥0∞) * (2 * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X π) R +
          2 * (ENNReal.ofReal ((2 / (N : ℝ)) ^ 2) * (2 * N * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂π))) := by
        gcongr
        refine h1.trans ?_
        gcongr
        rw [h2]
        gcongr
        exact h4.trans (by gcongr)
    _ = 2 * (N : ℝ≥0∞) * evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X π) R +
        16 * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂π := by
        have : (N : ℝ≥0∞) * (2 * (ENNReal.ofReal ((2 / (N : ℝ)) ^ 2) * (2 * N * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂π)))
            = (ENNReal.ofReal ((2 / (N : ℝ)) ^ 2) * (N : ℝ≥0∞) * (N : ℝ≥0∞)) * 4 * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂π := by ring
        rw [mul_add, this, e]
        ring

end Change

/-- **The change term** (Schur's test with the kernel `1 + W_s`): `∫ |H_ν - H_π|² dπ ≤ c Cp B²
‖dν/dμ - dπ/dμ‖²_{L²(μ)}`. -/
theorem wr14a_change_term_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ {Cp : ℝ}, 0 ≤ Cp → ∀ {B : ℝ}, 0 ≤ B → ∀ {h : Euc d → Euc d → ℝ},
      Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ {π ν : Measure (Euc d)} [IsProbabilityMeasure π] [IsProbabilityMeasure ν],
      π ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ →
      ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ →
      π ≪ HRS.Whole.withDensityReal ρ → ν ≪ HRS.Whole.withDensityReal ρ →
      ∫⁻ x, ‖wr14a_Hc h ν x - wr14a_Hc h π x‖ₑ ^ 2 ∂π ≤ ENNReal.ofReal (c * Cp * B ^ 2) *
        (eLpNorm (fun y => (ν.rnDeriv (HRS.Whole.withDensityReal ρ) y).toReal -
          (π.rnDeriv (HRS.Whole.withDensityReal ρ) y).toReal) 2 (HRS.Whole.withDensityReal ρ)) ^ 2 := by
  obtain ⟨CS, hCS0, hCS⟩ := wr13c_schur_W hd hs0 hsd M
  refine ⟨CS ^ 2, by positivity, fun {ρ} hρ hM {Cp} hCp {B} hB {h} hm hh {π ν} _ _ hπ hν hπac hνac => ?_⟩
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  haveI : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
  haveI : π.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
  set g : Euc d → ℝ := fun y => (ν.rnDeriv μ y).toReal - (π.rnDeriv μ y).toReal with hg
  have hgm : Measurable g :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.sub (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hhint : ∀ (κ : Measure (Euc d)), κ ≤ ENNReal.ofReal Cp • μ → ∀ x, Integrable (h x) κ :=
    fun κ hκ x => wr14a_integrable_of_env_bound hd hs0 hsd M hρ hM hκ hCp hB
      (wr14a_measurable_h_x hm x) (fun y hy => hh x y (Ne.symm hy))
  have hΔ : ∀ x, ‖wr14a_Hc h ν x - wr14a_Hc h π x‖ₑ ≤ ∫⁻ y, ENNReal.ofReal |h x y| * ‖g y‖ₑ ∂μ := by
    intro x
    have hiν : Integrable (fun y => (ν.rnDeriv μ y).toReal * h x y) μ :=
      (integrable_toReal_rnDeriv_mul_iff hνac).2 (hhint ν hν x)
    have hiπ : Integrable (fun y => (π.rnDeriv μ y).toReal * h x y) μ :=
      (integrable_toReal_rnDeriv_mul_iff hπac).2 (hhint π hπ x)
    have e : wr14a_Hc h ν x - wr14a_Hc h π x = ∫ y, g y * h x y ∂μ := by
      unfold wr14a_Hc
      rw [← integral_toReal_rnDeriv_mul hνac, ← integral_toReal_rnDeriv_mul hπac,
        ← integral_sub hiν hiπ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hg]; ring
    rw [e]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_mul, Real.enorm_eq_ofReal_abs (h x y), mul_comm]
  have hhm : Measurable (fun p : Euc d × Euc d => h p.1 p.2) := hm
  have hschur := hCS ρ hρ hM B hB h hhm hh (fun y => ‖g y‖ₑ) hgm.enorm
  calc ∫⁻ x, ‖wr14a_Hc h ν x - wr14a_Hc h π x‖ₑ ^ 2 ∂π
      ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal |h x y| * ‖g y‖ₑ ∂μ) ^ 2 ∂π :=
        lintegral_mono fun x => pow_le_pow_left' (hΔ x) 2
    _ ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal |h x y| * ‖g y‖ₑ ∂μ) ^ 2 ∂(ENNReal.ofReal Cp • μ) :=
        lintegral_mono' hπ le_rfl
    _ = ENNReal.ofReal Cp * ∫⁻ x, (∫⁻ y, ENNReal.ofReal |h x y| * ‖g y‖ₑ ∂μ) ^ 2 ∂μ := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal Cp * (ENNReal.ofReal (CS * B) ^ 2 * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂μ) :=
        mul_le_mul' le_rfl hschur
    _ = ENNReal.ofReal (CS ^ 2 * Cp * B ^ 2) * (eLpNorm g 2 μ) ^ 2 := by
        rw [HRS.Quad.lintegral_enorm_sq_eq_eLpNorm_sq hgm.aestronglyMeasurable]
        have e : ENNReal.ofReal (CS ^ 2 * Cp * B ^ 2) =
            ENNReal.ofReal Cp * ENNReal.ofReal (CS * B) ^ 2 := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hCp]
          congr 1; ring
        rw [e]; ring

/-! ### The crude bound -/

theorem wr14a_D_sq_le {N : ℕ} (hN : 0 < N) (h : Euc d → Euc d → ℝ) (ν : Measure (Euc d))
    [IsProbabilityMeasure ν] {H' : ℝ} (hH : ∀ x, |wr14a_Hc h ν x| ≤ H') (Y : Fin N → Euc d) :
    HRS.Whole.centeredPairFunctional h Y ν ^ 2 ≤
      3 * (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) ^ 2 + 15 * H' ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hH0 : 0 ≤ H' := (abs_nonneg _).trans (hH (Y ⟨0, hN⟩))
  set a : ℝ := (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) with ha
  set b : ℝ := -(2 * ((1 / (N : ℝ)) * ∑ i, wr14a_Hc h ν (Y i))) with hb
  set c : ℝ := wr14a_h0 h ν with hc
  have e : HRS.Whole.centeredPairFunctional h Y ν = a + b + c := by
    unfold HRS.Whole.centeredPairFunctional; rw [ha, hb, hc]; unfold wr14a_Hc wr14a_h0; ring
  have ha2 : a ^ 2 ≤ (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) ^ 2 := by
    rw [ha, mul_pow]
    have := HRS.Quad.sq_sum_sum_erase_le (fun i j => h (Y i) (Y j))
    calc (1 / (N : ℝ) ^ 2) ^ 2 * (∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)) ^ 2
        ≤ (1 / (N : ℝ) ^ 2) ^ 2 * ((N : ℝ) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) ^ 2) := by gcongr
      _ = _ := by field_simp
  have hb2 : b ^ 2 ≤ 4 * H' ^ 2 := by
    have h1 : |∑ i, wr14a_Hc h ν (Y i)| ≤ N * H' := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |wr14a_Hc h ν (Y i)| ≤ ∑ _i : Fin N, H' := Finset.sum_le_sum fun i _ => hH _
        _ = N * H' := by simp
    have h2 : |b| ≤ 2 * H' := by
      have e1 : |b| = 2 * ((1 / (N : ℝ)) * |∑ i, wr14a_Hc h ν (Y i)|) := by
        rw [hb, abs_neg, abs_mul, abs_mul, abs_of_pos (one_div_pos.2 hNR)]
        norm_num
      rw [e1]
      calc 2 * ((1 / (N : ℝ)) * |∑ i, wr14a_Hc h ν (Y i)|) ≤ 2 * ((1 / (N : ℝ)) * (N * H')) := by gcongr
        _ = 2 * H' := by field_simp
    nlinarith [abs_nonneg b, sq_abs b]
  have hc2 : c ^ 2 ≤ H' ^ 2 := by
    have : |c| ≤ H' := wr14a_abs_h0_le ν hH
    nlinarith [abs_nonneg c, sq_abs c]
  rw [e]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

set_option maxHeartbeats 1600000 in
/-- **Crude bound** (fixed `n`, no smallness): `E_R |D_N(h;ν)|² ≤ C (1 + Cp²) B²`. -/
theorem wr14a_quad_crude_weak (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (M Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ : Euc d → ℝ}, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ (V : WeakPotential (HRS.Whole.withDensityReal ρ)), V.M ≤ Mmax → V.M' ≤ M'max → V.γ ≤ γmax →
      (∀ x y : Euc d, x ≠ y → HRS.Whole.rieszWeight s (x - y) - Cq ≤ V.q x y) →
      ∀ {β : ℝ}, βm ≤ β → β ≤ βp →
      ∀ (B : ℝ), 0 ≤ B → ∀ (h : Euc d → Euc d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) →
      ∀ {Cp : ℝ}, 0 ≤ Cp → ∀ (ν : Measure (Euc d)) [IsProbabilityMeasure ν],
      ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ →
      ∫⁻ Y, ‖HRS.Whole.centeredPairFunctional h Y ν‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
        ≤ ENNReal.ofReal (C * (1 + Cp ^ 2) * B ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨cH, hcH0, hHc⟩ := wr14a_Hc_bound hd1 hs0.le hsd M
  obtain ⟨c₁, hc₁0, hvar⟩ := wr14a_variance_integral_le hd1 hs0 hsd M
  obtain ⟨cJ, hcJ, hJ⟩ := wr14a_J_le_gFun hd hs0 hsd (βp := βp) hβm
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  set γ' : ℝ := max γmax 0 with hγ'
  have hγ'0 : 0 ≤ γ' := le_max_right _ _
  set M0 : ℝ := Mmax + M'max + βp * γ' + βp * Cq with hM0
  set Wc : ℝ := c₁ * Real.exp M0 * (cJ * RefMarg.gFun d s ((n + 1 : ℕ) : ℝ)) with hWc
  have hg1 : 1 ≤ RefMarg.gFun d s ((n + 1 : ℕ) : ℝ) := RefMarg.one_le_gFun hd hs0.le hsd hNR
  have hWc0 : 0 ≤ Wc := by rw [hWc]; positivity
  refine ⟨3 * Wc + 15 * cH ^ 2 + 1, by positivity, ?_⟩
  intro ρ hρ hM V hVM hVM' hVγ hq β hβ1 hβ2 B hB h hm hh Cp hCp ν _ hν
  have hβpos : 0 < β := hβm.trans_le hβ1
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamβ : lam ≤ β := by rw [hlam, div_le_iff₀ hNpos]; nlinarith
  set P0 := pinnedLaw V lam (n + 1) (fun e : Empty => e.elim) with hP0
  haveI hRp : IsProbabilityMeasure P0 := isProb_pinnedLaw V hlam0.le (n + 1) _
  have hβγ : β * V.γ ≤ βp * γ' :=
    mul_le_mul hβ2 (hVγ.trans (le_max_left _ _)) V.γ_nonneg (hβpos.le.trans hβ2)
  have hpair : ∀ a b : Fin (n + 1), a ≠ b →
      ∫⁻ Y, ‖h ((Y : Fin (n + 1) → Euc d) a) (Y b)‖ₑ ^ 2 ∂P0 ≤ ENNReal.ofReal (Wc * B ^ 2) := by
    intro a b hab
    refine wr14a_pair_lintegral_le V hβpos.le a b hab hm (fun x => ?_)
    have h1 := hvar hρ hM (b := B) hB (x := x) (lam := lam) (M0 := M0) hlam0
      (f := h x) (ψ := fun y => V.M' + β * V.γ + pinField V lam (pinsWith (fun e : Empty => e.elim) x) y)
      (fun y hy => hh x y (Ne.symm hy)) (fun y hy => by
        rw [pinField_pinsWith, RefMarg.pinField_empty]
        have h2 := V.φ_le y
        have h3 := hq y x hy
        rw [wr14a_W_sub_comm x y] at h3
        have h5 : lam * Cq ≤ βp * Cq := mul_le_mul_of_nonneg_right (hlamβ.trans hβ2) hCq
        have h6 : lam * (HRS.Whole.rieszWeight s (x - y) - Cq) ≤ lam * V.q y x :=
          mul_le_mul_of_nonneg_left h3 hlam0.le
        rw [hM0]
        nlinarith)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : wr13c_J d s lam ≤ cJ * RefMarg.gFun d s ((n + 1 : ℕ) : ℝ) := hJ hβ1 hβ2 hNR
    have h3 : 0 ≤ c₁ * B ^ 2 * Real.exp M0 := by positivity
    rw [hWc]
    calc c₁ * B ^ 2 * Real.exp M0 * wr13c_J d s lam
        ≤ c₁ * B ^ 2 * Real.exp M0 * (cJ * RefMarg.gFun d s ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = _ := by ring
  have hH' : ∀ x, |wr14a_Hc h ν x| ≤ cH * Cp * B := fun x => hHc hρ hM hν hCp hB hh x
  set H' : ℝ := cH * Cp * B with hH'def
  have hNn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by linarith
  have hc3 : (0 : ℝ) ≤ 3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hmeas : ∀ i j : Fin (n + 1), Measurable fun Y : Fin (n + 1) → Euc d => ‖h (Y i) (Y j)‖ₑ ^ 2 :=
    fun i j => ((wr14a_measurable_h_pair hm i j).enorm).pow_const 2
  have hpt : ∀ Y : Fin (n + 1) → Euc d, ‖HRS.Whole.centeredPairFunctional h Y ν‖ₑ ^ 2 ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2
        + ENNReal.ofReal (15 * H' ^ 2) := by
    intro Y
    have h1 := wr14a_D_sq_le hN0 h ν hH' Y
    have e1 : ‖HRS.Whole.centeredPairFunctional h Y ν‖ₑ ^ 2 =
        ENNReal.ofReal (HRS.Whole.centeredPairFunctional h Y ν ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    have e2 : ∀ i j : Fin (n + 1), ‖h (Y i) (Y j)‖ₑ ^ 2 = ENNReal.ofReal (h (Y i) (Y j) ^ 2) := fun i j => by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e1]
    simp_rw [e2]
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), Finset.mul_sum]
    refine add_le_add (le_of_eq ?_) le_rfl
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_mul hc3]
  calc ∫⁻ Y, ‖HRS.Whole.centeredPairFunctional h Y ν‖ₑ ^ 2 ∂P0
      ≤ ∫⁻ Y, (∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ‖h (Y i) (Y j)‖ₑ ^ 2 + ENNReal.ofReal (15 * H' ^ 2)) ∂P0 := lintegral_mono hpt
    _ = (∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ∫⁻ Y, ‖h (Y i) (Y j)‖ₑ ^ 2 ∂P0) + ENNReal.ofReal (15 * H' ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        congr 1
        rw [lintegral_finsetSum Finset.univ (f := fun i (Y : Fin (n + 1) → Euc d) => ∑ j ∈ Finset.univ.erase i,
          ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2)
          (fun i _ => Finset.measurable_sum _ fun j _ => measurable_const.mul (hmeas i j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum (Finset.univ.erase i) (f := fun j (Y : Fin (n + 1) → Euc d) =>
          ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2)
          (fun j _ => measurable_const.mul (hmeas i j))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_const_mul _ (hmeas i j)]
    _ ≤ (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ENNReal.ofReal (Wc * B ^ 2)) + ENNReal.ofReal (15 * H' ^ 2) := by
        gcongr with i _ j hj
        exact hpair i j (Finset.ne_of_mem_erase hj).symm
    _ ≤ ENNReal.ofReal (3 * (Wc * B ^ 2)) + ENNReal.ofReal (15 * H' ^ 2) := by
        gcongr
        calc (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
              ENNReal.ofReal (Wc * B ^ 2))
            ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
              ENNReal.ofReal (Wc * B ^ 2) := by
              refine Finset.sum_le_sum fun i _ => ?_
              exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
          _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) *
              (Wc * B ^ 2)))) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              rw [ENNReal.ofReal_mul hNn, ENNReal.ofReal_mul hNn, ENNReal.ofReal_mul hc3,
                ENNReal.ofReal_natCast]
          _ = _ := by congr 1; field_simp
    _ = ENNReal.ofReal (3 * (Wc * B ^ 2) + 15 * H' ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hH'def]
        have h1 : 0 ≤ Wc * B ^ 2 := by positivity
        nlinarith [sq_nonneg cH, sq_nonneg Cp, sq_nonneg B, mul_nonneg (sq_nonneg Cp) h1,
          mul_nonneg (sq_nonneg cH) (sq_nonneg B), mul_nonneg (sq_nonneg Cp) (sq_nonneg B),
          mul_nonneg (mul_nonneg (sq_nonneg cH) (sq_nonneg Cp)) (sq_nonneg B)]

end HRS.MS.Wr
