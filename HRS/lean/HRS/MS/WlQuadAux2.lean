import HRS.MS.WlQuadAux1

/-!
# HRS.MS.WlQuadAux2 -- the centered quadratic functional under the calibrated reference `R_N` (WL-10)

Packet WL-10 of `docs/WR_LOG_PLAN.md` (Step 11 of the proof of `r2_log_static`, TeX `eq:r2-log-reference-quadratic`).
Infrastructure lemmas, not manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl10_`.  Port of
`wr14a_quad_weak_bound` (`HRS.MS.WrQuadAux2`) to the logarithmic envelope `|h| ≤ B (1 + K)`, using the merged
`wr14a_*` lemmas (`wr14a_quad_reference_le` = `wr14a_evariance_quad_le` + `wr14a_row_lintegral_le`,
`wr14a_pair_lintegral_le` is not needed, `wr14a_tv_pin_le`) with the calibrated reference of `WlRefAux1-3`.

Contents.
* `wl10_row_bounds`: for a weak potential `V` (any pair kernel with row bound, one-body field bounded above, constants
  `V.M, V.M', V.γ` bounded) and `κ(V, β) ≤ 1/2`: the two row inputs of `wr14a_quad_reference_le`,
  (i) the variance integral `∫ |h_c(x,y)|² e^{M' + βγ + ψ_x(y)} dμ(y) ≤ D B²` and
  (ii) **the truncated row mean** `|∑_k ∫ h_c(x,·) dν^x_k - H(x)| ≤ C B log(eN)`, obtained by splitting `{K(x,y) > L}`,
  `L = max 1 (2 log(eN)/d)` (`wl10_mean_one_le`: `wl_row_tail`, pin TV `2κ/N ≤ 1/N`, `|h_c| ≤ C B (1+L)`);
* `wl10_quad_weak_bound`: `Var_R[D_N(h; π^R)] ≤ C B² / N²` for the pinned weak ensemble `R` of such a `V`;
* `wl_quad_ref` (**TeX `eq:r2-log-reference-quadratic`**): the same for the calibrated reference `R_N = wl9_RN`
  (the weak ensemble of the field `ψ_R = ψ0 + ⟪t_N, Ξ⟫`, realised as `pinnedLaw (wlPot …) (β/N) N ∅`).

Adjustments with respect to the plan (documented, harmless).  The hypotheses of `wl_quad_ref` are those of
`wl_ref_marginal_L2`: `∃ M0, ∀ M ≥ M0, ∃ N0 C, ∀ ρ β N V` with `V.q = q_M` (the head index `M` is large so that the
Dobrushin coefficient `κ ≤ 1/2`; `N0` makes the calibration field `|⟪t_N, Ξ⟫| ≤ 1`, `wl_field_small`).  The bound
`π^R ≤ C μ` is not taken from `wl_ref_density_le` but re-derived from the constants of the weak potential
(`RefMarg.marginal_le_smul`), exactly as in the Euclidean proof; `h` is required symmetric and jointly measurable and
`B ≥ 0` is derived (`wl2_B_nonneg`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-! ### The truncation level `L = max 1 (2 log(eN)/d)` -/

/-- The truncation level of the row mean. -/
def wl10_L (d : ℕ) (N : ℝ) : ℝ := max 1 (2 * Real.log (Real.exp 1 * N) / d)

lemma wl10_log_eN_ge_one {N : ℝ} (hN : 1 ≤ N) : 1 ≤ Real.log (Real.exp 1 * N) := by
  have hN0 : 0 < N := by linarith
  rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
  linarith [Real.log_nonneg hN]

lemma wl10_one_le_L (d : ℕ) (N : ℝ) : 1 ≤ wl10_L d N := le_max_left _ _

lemma wl10_L_le {N : ℝ} (hN : 1 ≤ N) (hd : 1 ≤ d) : wl10_L d N ≤ 2 * Real.log (Real.exp 1 * N) := by
  have h1 := wl10_log_eN_ge_one hN
  refine max_le (by linarith) ?_
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_le_self (by linarith) hd1

lemma wl10_exp_L_le {N : ℝ} (hN : 1 ≤ N) (hd : 1 ≤ d) :
    Real.exp (-(d : ℝ) * wl10_L d N) ≤ (N ^ 2)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : 2 * Real.log (Real.exp 1 * N) ≤ (d : ℝ) * wl10_L d N := by
    have : 2 * Real.log (Real.exp 1 * N) / d ≤ wl10_L d N := le_max_right _ _
    rw [div_le_iff₀ hd0] at this
    linarith
  have h2 : 2 * Real.log N ≤ 2 * Real.log (Real.exp 1 * N) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]; linarith
  have h3 : -(d : ℝ) * wl10_L d N ≤ -(2 * Real.log N) := by linarith
  refine (Real.exp_le_exp.2 h3).trans (le_of_eq ?_)
  rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log hN0]
  ring

lemma wl10_log_eN_le_sqrt {N : ℝ} (hN : 1 ≤ N) : Real.log (Real.exp 1 * N) ≤ 2 * Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have h1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt hN0.le
  rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
  linarith

lemma wl10_one_add_L_sq_le {N : ℝ} (hN : 1 ≤ N) (hd : 1 ≤ d) : (1 + wl10_L d N) ^ 2 ≤ 25 * N := by
  have hN0 : 0 < N := by linarith
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN
  have h1 := wl10_L_le hN hd
  have h2 := wl10_log_eN_le_sqrt hN
  have h3 : 1 + wl10_L d N ≤ 5 * Real.sqrt N := by linarith
  have h4 : 0 ≤ 1 + wl10_L d N := by linarith [wl10_one_le_L d N]
  calc (1 + wl10_L d N) ^ 2 ≤ (5 * Real.sqrt N) ^ 2 := pow_le_pow_left₀ h4 h3 2
    _ = 25 * N := by rw [mul_pow, Real.sq_sqrt hN0.le]; ring

lemma wl10_one_add_L_le_log {N : ℝ} (hN : 1 ≤ N) (hd : 1 ≤ d) :
    1 + wl10_L d N ≤ 3 * Real.log (Real.exp 1 * N) := by
  have := wl10_L_le hN hd
  have := wl10_log_eN_ge_one hN
  linarith

/-! ### The two row inputs: variance integral and truncated row mean -/

/-- **Row bounds for the pinned weak ensemble** (TeX `eq:r2-log-reference-quadratic`, row part).  Let `V` be a weak
potential on `μ = ρ dx` (`HasSphericalBound A ρ`) with `V.M ≤ Mmax`, `V.M' ≤ M'max`, `V.γ ≤ γmax`,
`κ(V, β) ≤ 1/2`, `0 ≤ β ≤ βp`, `N = n + 1`, `n ≥ 1`, and `|h| ≤ B (1 + K)` off the diagonal.  With
`π = R^{(1)}`, `R = pinnedLaw V (β/N) N ∅`, `h_c` the doubly centered kernel and `ψ_x` the pinned one-body field:
(i) `∫ |h_c(x,y)|² e^{M' + βγ + ψ_x(y)} dμ(y) ≤ D B²`;
(ii) `|∑_k ∫ h_c(x,·) dν^x_k - H(x)| ≤ C B log(eN)` where `ν^x_k` is the `k`-th marginal of the ensemble pinned at `x`
(**the truncated row mean**: split `{K(x,·) > L}`, `L = max 1 (2 log(eN)/d)`). -/
theorem wl10_row_bounds (hd : 2 ≤ d) (A βp Mmax M'max γmax : ℝ) :
    ∃ Dv C6 : ℝ, 0 ≤ Dv ∧ 0 ≤ C6 ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ), V.M ≤ Mmax → V.M' ≤ M'max → V.γ ≤ γmax →
      ∀ {β : ℝ}, 0 ≤ β → β ≤ βp → ∀ {n : ℕ}, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      ∀ {B : ℝ}, 0 ≤ B → ∀ {h : Euc d → Euc d → ℝ}, Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      (∀ x : Euc d, ∫⁻ y, ‖wr14a_cK h ((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1)
            (fun e : Empty => e.elim)).map (fun X => X 0)) x y‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / ((n + 1 : ℕ) : ℝ))
            (pinsWith (fun e : Empty => e.elim) x) y)) ∂(HRS.Whole.withDensityReal ρ)
          ≤ ENNReal.ofReal (Dv * B ^ 2)) ∧
      (∀ x : Euc d, |∑ k : Fin n, ∫ y, wr14a_cK h ((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1)
            (fun e : Empty => e.elim)).map (fun X => X 0)) x y
          ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))
          - wr14a_Hc h ((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1)
            (fun e : Empty => e.elim)).map (fun X => X 0)) x|
          ≤ C6 * B * Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨cH, hcH0, hHc⟩ := wl10_Hc_bound hd A
  obtain ⟨cv, hcv0, hvar⟩ := wl10_variance_integral_le hd A
  obtain ⟨cm, hcm0, hmean⟩ := wl10_mean_one_le hd A
  set γ' : ℝ := max γmax 0 with hγ'
  have hγ'0 : 0 ≤ γ' := le_max_right _ _
  set M0 : ℝ := Mmax + M'max + βp * γ' with hM0
  set Cp : ℝ := Real.exp M0 with hCp
  have hCp0 : 0 < Cp := Real.exp_pos _
  set HB : ℝ := cH * Cp with hHB
  have hHB0 : 0 ≤ HB := by positivity
  set bb : ℝ := 1 + 3 * HB with hbb
  have hbb1 : 1 ≤ bb := by linarith
  refine ⟨cv * bb ^ 2 * Cp, 3 * (2 + 2 * cm * Cp) * bb + HB, by positivity, by positivity,
    fun ρ hρ hA V hVM hVM' hVγ {β} hβ hββp {n} hn hκ {B} hB {h} hm hh => ?_⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := wl2_isProb hρ
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set R := pinnedLaw V lam (n + 1) (fun e : Empty => e.elim) with hR
  haveI hRp : IsProbabilityMeasure R := isProb_pinnedLaw V hlam0 (n + 1) _
  set π : Measure (Euc d) := R.map (fun X => X 0) with hπ
  haveI hπp : IsProbabilityMeasure π := inferInstance
  have hβγ : β * V.γ ≤ βp * γ' :=
    mul_le_mul hββp (hVγ.trans (le_max_left _ _)) V.γ_nonneg (hβ.trans hββp)
  have hVC : Real.exp (V.M + V.M' + β * V.γ) ≤ Cp := by
    refine Real.exp_le_exp.2 ?_
    rw [hM0]; linarith
  have hπle : π ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ := by
    have h1 := RefMarg.marginal_le_smul (B := Empty) V hβ hN0 (n := n + 1) (by simp)
      (fun e : Empty => e.elim) 0
    refine h1.trans ?_
    refine Measure.le_iff'.2 fun A' => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hVC) le_rfl
  have hνle : ∀ (x : Euc d) (k : Fin n), (pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
      (fun Y => Y k) ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ := by
    intro x k
    have h1 := HRS.Quad.pinned_marginal_le_density (B := Option Empty) V hβ hN0 (n := n)
      (by simp) (pinsWith (fun e : Empty => e.elim) x) k
    refine Measure.le_iff.2 fun A' hA' => (h1 A').trans ?_
    rw [withDensity_apply _ hA', Measure.smul_apply, smul_eq_mul]
    calc ∫⁻ z in A', ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V lam
          (pinsWith (fun e : Empty => e.elim) x) z)) ∂(HRS.Whole.withDensityReal ρ)
        ≤ ∫⁻ _z in A', ENNReal.ofReal Cp ∂(HRS.Whole.withDensityReal ρ) := by
          refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
          refine le_trans (Real.exp_le_exp.2 ?_) hVC
          have h2 := (isField_pinField V hlam0 (pinsWith (fun e : Empty => e.elim) x)).le z
          linarith
      _ = ENNReal.ofReal Cp * HRS.Whole.withDensityReal ρ A' := by rw [setLIntegral_const, mul_comm]
  -- the one-point function and the centered kernel
  have hHcB : ∀ x, |wr14a_Hc h π x| ≤ HB * B := fun x => by
    have := hHc ρ hρ hA hπle hCp0.le hB hh x
    simpa [hHB, mul_comm, mul_assoc, mul_left_comm] using this
  have hcK : ∀ x y : Euc d, y ≠ x →
      |wr14a_cK h π x y| ≤ (bb * B) * (1 + sphericalLogKernel x y) := by
    intro x y hy
    have hK0 := HRS.MS.Comm.comm_log_nonneg x y
    have := wl10_abs_cK_le (h := h) π (B := B) (HB := HB * B) hHcB x y (e := 1 + sphericalLogKernel x y)
      (by linarith) (hh x y (Ne.symm hy))
    have e : B + 3 * (HB * B) = bb * B := by rw [hbb]; ring
    rwa [e] at this
  have hHm : Measurable (wr14a_Hc h π) := wr14a_measurable_Hc hm π
  have hHi : Integrable (wr14a_Hc h π) π :=
    Integrable.of_bound hHm.aestronglyMeasurable (HB * B) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hHcB x)
  have hhint : ∀ x, Integrable (h x) π := fun x =>
    wl10_integrable_of_env_bound hd A ρ hρ hA hπle hCp0.le hB (wr14a_measurable_h_x hm x)
      (fun y hy => hh x y (Ne.symm hy))
  have hzero : ∀ x, ∫ y, wr14a_cK h π x y ∂π = 0 := fun x => wr14a_integral_cK_eq_zero π x (hhint x) hHi
  have hcKm : ∀ x, Measurable (wr14a_cK h π x) := fun x => by
    unfold wr14a_cK
    exact (((wr14a_measurable_h_x hm x).sub measurable_const).sub hHm).add measurable_const
  refine ⟨fun x => ?_, fun x => ?_⟩
  · -- (i) the variance integral
    have h1 := hvar ρ hρ hA (b := bb * B) (by positivity) (x := x) (M0 := M0)
      (f := wr14a_cK h π x) (ψ := fun y => V.M' + β * V.γ +
        pinField V lam (pinsWith (fun e : Empty => e.elim) x) y) (fun y hy => hcK x y hy) (fun y => by
        rw [pinField_pinsWith, RefMarg.pinField_empty]
        have h2 := V.φ_le y
        have h3 := mul_nonneg hlam0 (V.q_nonneg y x)
        rw [hM0]
        linarith)
    refine h1.trans (le_of_eq ?_)
    congr 1; rw [hCp]; ring
  · -- (ii) the truncated row mean
    set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
    set L : ℝ := wl10_L d N with hLdef
    have hL1 : 1 ≤ L := wl10_one_le_L d N
    have hLe : Real.exp (-(d : ℝ) * L) ≤ (N ^ 2)⁻¹ := wl10_exp_L_le hNR hd1
    have hlg1 : 1 ≤ Real.log (Real.exp 1 * N) := wl10_log_eN_ge_one hNR
    have hL3 : 1 + L ≤ 3 * Real.log (Real.exp 1 * N) := wl10_one_add_L_le_log hNR hd1
    set ε : ℝ := 2 * weakKappa V β / N with hεdef
    have hκ0 : 0 ≤ weakKappa V β := weakKappa_nonneg V hβ
    have hε0 : 0 ≤ ε := by positivity
    have hper : ∀ k : Fin n, |∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
        (fun Y => Y k))| ≤ 2 * (bb * B) * (1 + L) * ε
          + 2 * (cm * Cp * (bb * B) * (1 + L) * Real.exp (-(d : ℝ) * L)) := by
      intro k
      haveI := isProb_pinnedLaw V hlam0 n (pinsWith (fun e : Empty => e.elim) x)
      have := hmean ρ hρ hA hCp0.le (b := bb * B) (by positivity) (x := x) (ε := ε) (L := L) hε0 hL1
        (π := π) (ν := (pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))
        hπle (hνle x k) (fun S hS => wr14a_tv_pin_le V hβ hκ x k hS) (hcKm x)
        (fun y hy => hcK x y hy)
      rw [hzero x, sub_zero] at this
      exact this
    have hsum : |∑ k : Fin n, ∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
        (fun Y => Y k))| ≤ (n : ℝ) * (2 * (bb * B) * (1 + L) * ε
          + 2 * (cm * Cp * (bb * B) * (1 + L) * Real.exp (-(d : ℝ) * L))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k : Fin n, |∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
            (fun Y => Y k))| ≤ ∑ _k : Fin n, (2 * (bb * B) * (1 + L) * ε
              + 2 * (cm * Cp * (bb * B) * (1 + L) * Real.exp (-(d : ℝ) * L))) :=
            Finset.sum_le_sum fun k _ => hper k
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnN : (n : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hbB : 0 ≤ bb * B := by positivity
    have hnε : (n : ℝ) * ε ≤ 1 := by
      calc (n : ℝ) * ε = (n : ℝ) / N * (2 * weakKappa V β) := by rw [hεdef]; ring
        _ ≤ 1 * 1 := by
          refine mul_le_mul ((div_le_one hNpos).2 hnN) (by linarith) (by positivity) zero_le_one
        _ = 1 := one_mul 1
    have hnexp : (n : ℝ) * Real.exp (-(d : ℝ) * L) ≤ 1 := by
      calc (n : ℝ) * Real.exp (-(d : ℝ) * L) ≤ N * (N ^ 2)⁻¹ :=
            mul_le_mul hnN hLe (Real.exp_pos _).le hNpos.le
        _ = N⁻¹ := by field_simp
        _ ≤ 1 := inv_le_one_of_one_le₀ hNR
    have hnper : (n : ℝ) * (2 * (bb * B) * (1 + L) * ε
          + 2 * (cm * Cp * (bb * B) * (1 + L) * Real.exp (-(d : ℝ) * L)))
        ≤ (2 + 2 * cm * Cp) * (bb * B) * (1 + L) := by
      have h1L : 0 ≤ 1 + L := by linarith
      calc (n : ℝ) * (2 * (bb * B) * (1 + L) * ε
          + 2 * (cm * Cp * (bb * B) * (1 + L) * Real.exp (-(d : ℝ) * L)))
          = 2 * (bb * B) * (1 + L) * ((n : ℝ) * ε)
            + 2 * (cm * Cp * (bb * B) * (1 + L)) * ((n : ℝ) * Real.exp (-(d : ℝ) * L)) := by ring
        _ ≤ 2 * (bb * B) * (1 + L) * 1 + 2 * (cm * Cp * (bb * B) * (1 + L)) * 1 := by
            gcongr
        _ = _ := by ring
    have hHx : |wr14a_Hc h π x| ≤ HB * B := hHcB x
    calc |∑ k : Fin n, ∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
          (fun Y => Y k)) - wr14a_Hc h π x|
        ≤ |∑ k : Fin n, ∫ y, wr14a_cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
          (fun Y => Y k))| + |wr14a_Hc h π x| := abs_sub _ _
      _ ≤ (2 + 2 * cm * Cp) * (bb * B) * (1 + L) + HB * B := add_le_add (hsum.trans hnper) hHx
      _ ≤ (2 + 2 * cm * Cp) * (bb * B) * (3 * Real.log (Real.exp 1 * N)) + HB * B * Real.log (Real.exp 1 * N) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hL3 (by positivity)) ?_
          exact le_mul_of_one_le_right (by positivity) hlg1
      _ = (3 * (2 + 2 * cm * Cp) * bb + HB) * B * Real.log (Real.exp 1 * N) := by ring

/-! ### The reference quadratic bound for a pinned weak ensemble -/

/-- Division by `N` in `ℝ≥0∞` (copy of `wr14a_evariance_div`). -/
theorem wl10_evariance_div {V : ℝ≥0∞} {X : ℝ} {N : ℕ} (hN : 0 < N)
    (h : (N : ℝ≥0∞) * V ≤ ENNReal.ofReal X) : V ≤ ENNReal.ofReal (X / N) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast,
    ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.2 hN.ne')) (Or.inl (ENNReal.natCast_ne_top N))]
  rwa [mul_comm]

/-- **`Var_R[D_N(h; π^R)] ≤ C B² / N²`** for the pinned weak ensemble `R = pinnedLaw V (β/N) N ∅`, `N = n + 1`,
`π^R = R^{(1)}`, of a weak potential `V` with bounded constants and `κ(V, β) ≤ 1/2`, for symmetric jointly measurable `h`
with `|h| ≤ B (1 + K)` off the diagonal.  `C` is uniform in `ρ` (`HasSphericalBound A ρ`), `V`, `β ≤ βp`, `n ≥ 1`. -/
theorem wl10_quad_weak_bound (hd : 2 ≤ d) (A βp Mmax M'max γmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ), V.M ≤ Mmax → V.M' ≤ M'max → V.γ ≤ γmax →
      ∀ {β : ℝ}, 0 ≤ β → β ≤ βp → ∀ {n : ℕ}, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      ∀ {B : ℝ}, 0 ≤ B → ∀ {h : Euc d → Euc d → ℝ}, Measurable (Function.uncurry h) →
      (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      evariance (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X
          ((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map (fun X => X 0)))
          (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
        ≤ ENNReal.ofReal (C * B ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨Dv, C6, hDv0, hC60, hrow⟩ := wl10_row_bounds hd A βp Mmax M'max γmax
  refine ⟨16 * Dv + 32 * C6 ^ 2, by positivity, fun ρ hρ hA V hVM hVM' hVγ {β} hβ hββp {n} hn hκ {B} hB
    {h} hm hsym hh => ?_⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := wl2_isProb hρ
  obtain ⟨hVx, hMx⟩ := hrow ρ hρ hA V hVM hVM' hVγ hβ hββp hn hκ hB hm hh
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  set π : Measure (Euc d) := (pinnedLaw V (β / N) (n + 1) (fun e : Empty => e.elim)).map (fun X => X 0) with hπ
  haveI : IsProbabilityMeasure (pinnedLaw V (β / N) (n + 1) (fun e : Empty => e.elim)) :=
    isProb_pinnedLaw V (div_nonneg hβ hNpos.le) (n + 1) _
  haveI : IsProbabilityMeasure π := inferInstance
  have hfin := wr14a_quad_reference_le V hβ hκ hm hsym π
    (𝒱 := ENNReal.ofReal (Dv * B ^ 2)) (𝓜 := C6 * B * Real.log (Real.exp 1 * N)) hVx hMx
  have hlg0 := wl10_log_eN_ge_one hNR
  have hlg2 : Real.log (Real.exp 1 * N) ^ 2 ≤ 4 * N := by
    have h1 := wl10_log_eN_le_sqrt hNR
    calc Real.log (Real.exp 1 * N) ^ 2 ≤ (2 * Real.sqrt N) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      _ = 4 * N := by rw [mul_pow, Real.sq_sqrt hNpos.le]; ring
  have hnN : (n : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set X0 : ℝ := 8 / N ^ 2 * (2 * n * (Dv * B ^ 2) + (C6 * B * Real.log (Real.exp 1 * N)) ^ 2) with hX0
  have hX : ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Fin (n + 1) → Euc d => HRS.Whole.centeredPairFunctional h X π)
      (pinnedLaw V (β / N) (n + 1) (fun e : Empty => e.elim)) ≤ ENNReal.ofReal X0 := by
    refine hfin.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  refine (wl10_evariance_div hN0 hX).trans (ENNReal.ofReal_le_ofReal ?_)
  have key : 2 * n * (Dv * B ^ 2) + (C6 * B * Real.log (Real.exp 1 * N)) ^ 2
      ≤ N * (2 * Dv + 4 * C6 ^ 2) * B ^ 2 := by
    have e : (C6 * B * Real.log (Real.exp 1 * N)) ^ 2 = C6 ^ 2 * B ^ 2 * Real.log (Real.exp 1 * N) ^ 2 := by ring
    rw [e]
    have h1 : 2 * (n : ℝ) * (Dv * B ^ 2) ≤ 2 * N * (Dv * B ^ 2) := by gcongr
    have h2 : C6 ^ 2 * B ^ 2 * Real.log (Real.exp 1 * N) ^ 2 ≤ C6 ^ 2 * B ^ 2 * (4 * N) := by gcongr
    nlinarith
  calc X0 / N = 8 * (2 * n * (Dv * B ^ 2) + (C6 * B * Real.log (Real.exp 1 * N)) ^ 2) / (N ^ 2 * N) := by
        rw [hX0]; field_simp
    _ ≤ 8 * (N * (2 * Dv + 4 * C6 ^ 2) * B ^ 2) / (N ^ 2 * N) := by gcongr
    _ = (16 * Dv + 32 * C6 ^ 2) * B ^ 2 / N ^ 2 := by field_simp; ring

/-! ### The calibrated reference `R_N` -/

/-- **`Var_{R_N}(D_N(h; π^R)) ≤ C B² / N²`** (TeX `eq:r2-log-reference-quadratic`).  For `d ≥ 2`, `A`, `βp ≥ 0` there is
a head index `M0` such that for every `M ≥ M0` there are `N0 ≥ 2` and `C ≥ 0` (quantified before `ρ, β, N, V, B, h`)
with, for every probability density `ρ` with `HasSphericalBound A ρ` (`μ = ρ dx`), `β ∈ (0, βp]`, `N ≥ N0`, every weak
potential `V` with `V.q = q_M`, every `B` and every symmetric jointly measurable `h` with `|h| ≤ B (1 + K)` off the
diagonal: with `R_N = wl9_RN μ M V β N` the calibrated reference and `π^R = firstMarginal R_N`,
`Var_{R_N}(D_N(h; π^R)) ≤ C B² / N²`.  (`B < 0` forces `h = 0` off the diagonal: no hypothesis `B ≥ 0` is needed.) -/
theorem wl_quad_ref (hd : 2 ≤ d) (A βp : ℝ) (hβp : 0 ≤ βp) :
    ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M → ∃ (N0 : ℕ) (C : ℝ), 2 ≤ N0 ∧ 0 ≤ C ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N0 ≤ N →
      ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ), V.q = wl_qm (d := d) M →
      ∀ (B : ℝ) (h : Euc d → Euc d → ℝ), Measurable (fun p : Euc d × Euc d => h p.1 p.2) →
      (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      evariance (fun X : Fin N → Euc d => HRS.Whole.centeredPairFunctional h X
          (HRS.Whole.firstMarginal (wl9_RN (HRS.Whole.withDensityReal ρ) M V β N)))
          (wl9_RN (HRS.Whole.withDensityReal ρ) M V β N)
        ≤ ENNReal.ofReal (C * B ^ 2 / (N : ℝ) ^ 2) := by
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  obtain ⟨hCq0, hCqspec⟩ := wl4b_Cq_spec hd A
  set Cq := wl4b_Cq d A with hCq
  set Cl' : ℝ := max Cl 0 with hCl'
  have hCl'0 : 0 ≤ Cl' := le_max_right _ _
  set Mf : ℝ := βp * Cq + 1 with hMf
  set M1f : ℝ := βp * Cl' + 1 + βp * Cq with hM1f
  have hMf0 : 0 ≤ Mf := by positivity
  have hM1f0 : 0 ≤ M1f := by positivity
  obtain ⟨M0, hM0, hhead⟩ := wl9_head (d := d) (by omega) Cq βp Mf M1f
  obtain ⟨C, hC0, hquad⟩ := wl10_quad_weak_bound hd A βp Mf M1f Cq
  refine ⟨M0, hM0, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := le_trans hM0 hM
  obtain ⟨N0, hN0⟩ := wl_field_small hd A βp 0 M hM1
  refine ⟨max N0 2, C, le_max_right _ _, hC0, fun ρ hρ hA β hβ hββp N hN V hV B h hm hsym hh => ?_⟩
  have hNN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  haveI := wl_isProb hρ
  obtain ⟨-, hℓ, hℓle, -, -⟩ := hQ ρ hρ hA β hβ.le N (by omega)
  have hq := hCqspec ρ hρ hA M hM1
  set a : ℝ := Cq * (M : ℝ) ^ (-((d : ℝ) / 2)) with hadef
  have ha : 0 ≤ a := mul_nonneg hCq0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have haC : a ≤ Cq := by
    calc a ≤ Cq * 1 := mul_le_mul_of_nonneg_left (wl9_rpow_le_one M hM1) hCq0
      _ = Cq := mul_one _
  have hm' : ∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ) ≤ Cl' := hℓle.trans (le_max_left _ _)
  have hF : WlFam 0 β N N (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (0 : Euc d)) (fun _ => (0 : ℝ)) :=
    { one_le := by omega
      n_le := le_rfl
      β_nonneg := hβ.le
      p_le := by norm_num
      t_nonneg := fun a => a.elim0
      t_le := fun a => a.elim0
      v_meas := measurable_const
      v_bdd := fun x => by simp }
  have hc : ∀ x, |inner ℝ (wl9_tN (HRS.Whole.withDensityReal ρ) M V β N)
      (Xi (HRS.Whole.withDensityReal ρ) (wl_psi M) x)| ≤ 1 := fun x =>
    hN0 ρ hρ hA β hβ hββp N N hNN0 (by omega) 0 (fun _ => (0 : ℝ)) (fun _ => (0 : Euc d)) (fun _ => 0) hF V hV x
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hN0pos : 0 < n + 1 := Nat.succ_pos n
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlamdef
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le hNpos.le
  have hlam_le : lam ≤ β := by
    rw [hlamdef, div_le_iff₀ hNpos]
    exact le_mul_of_one_le_right hβ.le (by exact_mod_cast hN0pos)
  -- the field `ψ_R` and its weak potential
  have hψ : IsField (HRS.Whole.withDensityReal ρ) (wl9_psiR (HRS.Whole.withDensityReal ρ) M V β (n + 1)) (β * a + 1) (lam * Cl' + 1) :=
    wl9_isField_psiR hq ha hℓ hm' hβ.le hN0pos V hc
  set V' : WeakPotential (HRS.Whole.withDensityReal ρ) := wlPot hq ha hψ with hV'
  have hV'M : V'.M = β * a + 1 := rfl
  have hV'M' : V'.M' = lam * Cl' + 1 := rfl
  have hV'γ : V'.γ = a := rfl
  have hβaC : β * a ≤ βp * Cq := mul_le_mul hββp haC ha hβp
  have hMle : β * a + 1 ≤ Mf := by linarith
  have h1 : lam * Cl' ≤ βp * Cl' := mul_le_mul (hlam_le.trans hββp) le_rfl hCl'0 hβp
  have hM1le : lam * Cl' + 1 ≤ M1f := by linarith [mul_nonneg hβp hCq0]
  have hs : β * a ≤ min 1 (1 / (16 * Real.exp (Mf + M1f + 1))) :=
    (mul_le_mul_of_nonneg_right hββp ha).trans (hhead M hM)
  have hsψ : β * a ≤ min 1 (1 / (16 * Real.exp ((β * a + 1) + (lam * Cl' + 1) + 1))) :=
    wl9_hs_mono hMle hM1le hs
  have hκ : weakKappa V' β ≤ 1 / 2 := (wl_kappa_lt_half hq ha hψ hβ.le hsψ).le
  -- `R_N` is the pinned law of `V'`
  have hRN : wl9_RN (HRS.Whole.withDensityReal ρ) M V β (n + 1) = pinnedLaw V' lam (n + 1) (fun e : Empty => e.elim) := by
    rw [wl9_RN_eq hq ha hℓ hm' hβ.le hN0pos V hc,
      wl5_fieldLaw_congr_q (V' := V') (by rw [hV]; rfl) _ _ _, wl5_pinnedLaw_empty V' lam (n + 1)]
    rfl
  have hB : 0 ≤ B := wl2_B_nonneg (by omega) hh
  rw [hRN, wl6_firstMarginal_def (d := d) n]
  exact hquad ρ hρ hA V' (by rw [hV'M]; exact hMle) (by rw [hV'M']; exact hM1le) (by rw [hV'γ]; exact haC)
    hβ.le hββp hn hκ hB hm hsym hh

end HRS.MS.Wl
