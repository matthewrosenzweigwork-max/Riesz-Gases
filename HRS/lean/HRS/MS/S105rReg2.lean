import HRS.MS.S105rReg1

/-!
# S10.5 (nonlinear), packet S105R-2: `S105nReg` proved

`s105r_reg`: `S105nReg d s a β εstar c₁ C₁` for `2 ≤ d`, `0 ≤ s < d`, `a, β > 0` and all `εstar, c₁, C₁`; `s105r_hReg`: the form
needed by the ties `s104b_general_initial_of_inputs` (with `εn = 1`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S105r

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S104b HRS.MS.Mov63

variable {d : ℕ}

/-- The Gaussian bounds for `ρ^t = ρ_β + √ρ_β v_t`, uniformly in `v` with uniformly bounded derivatives. -/
theorem s105r_leibniz {ρβ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (hq : 0 < q')
    (hR : HRS.MS.Gap.GapRef d ρβ q' B) (Cv E : ℝ) (hCv : 0 ≤ Cv) (hE : 0 ≤ E) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ v : Euc d → ℝ, ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) v →
      (∀ k ≤ 3, ∀ x : Euc d, ‖iteratedFDeriv ℝ k v x‖ ≤ Cv * E) →
      ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun x => ρβ x + Real.sqrt (ρβ x) * v x) ∧
      ∀ k ≤ 3, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun x => ρβ x + Real.sqrt (ρβ x) * v x) x‖ ≤
        K * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨hρs, cρ, hcρ, hρb⟩ := HRS.MS.Mov0.mv0_hgauss_gapref hq hR
  obtain ⟨hss, -, cs, hcs, hsb⟩ := HRS.MS.Mov0.mv0_sqrt_gauss hq hR
  choose Cρ hCρ using hρb
  choose Cs hCs using hsb
  set c0 : ℝ := min cρ cs with hc0
  have hc0pos : 0 < c0 := lt_min hcρ hcs
  set Pρ : ℝ := ∑ k ∈ Finset.range 4, |Cρ k| with hPρ
  set Ps : ℝ := ∑ k ∈ Finset.range 4, |Cs k| with hPs
  have hPρ0 : 0 ≤ Pρ := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hPs0 : 0 ≤ Ps := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hexp1 : ∀ (r : ℝ), Real.exp (-cρ * r ^ 2) ≤ Real.exp (-c0 * r ^ 2) := fun r => by
    apply Real.exp_le_exp.2
    have : c0 ≤ cρ := min_le_left _ _
    nlinarith [sq_nonneg r]
  have hexp2 : ∀ (r : ℝ), Real.exp (-cs * r ^ 2) ≤ Real.exp (-c0 * r ^ 2) := fun r => by
    apply Real.exp_le_exp.2
    have : c0 ≤ cs := min_le_right _ _
    nlinarith [sq_nonneg r]
  have hρk : ∀ k ≤ 3, ∀ x : Euc d, ‖iteratedFDeriv ℝ k ρβ x‖ ≤ Pρ * Real.exp (-c0 * ‖x‖ ^ 2) := by
    intro k hk x
    have h1 := hCρ k x
    have h2 : Cρ k ≤ Pρ := by
      calc Cρ k ≤ |Cρ k| := le_abs_self _
        _ ≤ Pρ := Finset.single_le_sum (f := fun k => |Cρ k|) (fun k _ => abs_nonneg _)
            (Finset.mem_range.2 (by omega))
    refine h1.trans ?_
    have h3 := hexp1 ‖x‖
    have h4 : 0 ≤ Real.exp (-c0 * ‖x‖ ^ 2) := (Real.exp_pos _).le
    have h5 : 0 ≤ Real.exp (-cρ * ‖x‖ ^ 2) := (Real.exp_pos _).le
    nlinarith [mul_le_mul h2 h3 h5 hPρ0]
  have hsk : ∀ k ≤ 3, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρβ y)) x‖ ≤
      Ps * Real.exp (-c0 * ‖x‖ ^ 2) := by
    intro k hk x
    have h1 := hCs k x
    have h2 : Cs k ≤ Ps := by
      calc Cs k ≤ |Cs k| := le_abs_self _
        _ ≤ Ps := Finset.single_le_sum (f := fun k => |Cs k|) (fun k _ => abs_nonneg _)
            (Finset.mem_range.2 (by omega))
    refine h1.trans ?_
    have h3 := hexp2 ‖x‖
    have h5 : 0 ≤ Real.exp (-cs * ‖x‖ ^ 2) := (Real.exp_pos _).le
    nlinarith [mul_le_mul h2 h3 h5 hPs0]
  refine ⟨c0, Pρ + 8 * (Ps * (Cv * E)), hc0pos, by positivity, fun v hv hvb => ?_⟩
  have hρ3 : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) ρβ := hρs.of_le (by simp)
  have hs3 : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun y => Real.sqrt (ρβ y)) := hss.of_le (by simp)
  have hprod : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun x => Real.sqrt (ρβ x) * v x) := hs3.mul hv
  refine ⟨hρ3.add hprod, fun k hk x => ?_⟩
  have hkc : (k : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hk
  have hsum : iteratedFDeriv ℝ k (fun x => ρβ x + Real.sqrt (ρβ x) * v x) x =
      iteratedFDeriv ℝ k ρβ x + iteratedFDeriv ℝ k (fun x => Real.sqrt (ρβ x) * v x) x :=
    iteratedFDeriv_add_apply ((hρ3.of_le hkc).contDiffAt) ((hprod.of_le hkc).contDiffAt)
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hs3 hv x (n := k) (by exact_mod_cast hk)
  have hex0 : 0 ≤ Real.exp (-c0 * ‖x‖ ^ 2) := (Real.exp_pos _).le
  have hterm : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => Real.sqrt (ρβ y)) x‖ *
      ‖iteratedFDeriv ℝ (k - i) v x‖ ≤ (k.choose i : ℝ) * (Ps * Real.exp (-c0 * ‖x‖ ^ 2) * (Cv * E)) := by
    intro i hi
    have hik : i ≤ 3 := by have := Finset.mem_range.1 hi; omega
    have a1 := hsk i hik x
    have a2 := hvb (k - i) (by omega) x
    have : ‖iteratedFDeriv ℝ i (fun y => Real.sqrt (ρβ y)) x‖ * ‖iteratedFDeriv ℝ (k - i) v x‖ ≤
        Ps * Real.exp (-c0 * ‖x‖ ^ 2) * (Cv * E) :=
      mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have hsumle : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => Real.sqrt (ρβ y)) x‖ *
      ‖iteratedFDeriv ℝ (k - i) v x‖ ≤ 8 * (Ps * (Cv * E)) * Real.exp (-c0 * ‖x‖ ^ 2) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hch : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
      exact_mod_cast Nat.sum_range_choose k
    have h2k : (2 : ℝ) ^ k ≤ 8 := by
      calc (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
        _ = 8 := by norm_num
    have h8 : 0 ≤ Ps * Real.exp (-c0 * ‖x‖ ^ 2) * (Cv * E) := by positivity
    rw [hch]
    calc (2 : ℝ) ^ k * (Ps * Real.exp (-c0 * ‖x‖ ^ 2) * (Cv * E))
        ≤ 8 * (Ps * Real.exp (-c0 * ‖x‖ ^ 2) * (Cv * E)) := mul_le_mul_of_nonneg_right h2k h8
      _ = 8 * (Ps * (Cv * E)) * Real.exp (-c0 * ‖x‖ ^ 2) := by ring
  rw [hsum]
  refine (norm_add_le _ _).trans ?_
  have := hρk k hk x
  nlinarith

/-- The main theorem: `S105nReg`. -/
theorem s105r_reg (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) : S105nReg d s a β εstar c₁ C₁ := by
  intro ρβ hρβ ε ψ ρ hadm hres T0 hT0
  have hC1 : 0 < C₁ := s105r_C1_pos hρβ hres
  obtain ⟨B, hBdef, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρβ
  have hq : 0 < β * a := mul_pos hβ ha
  have hpos : ∀ x, 0 < ρβ x := hR.pos
  have hρβc : Continuous ρβ := hR.smooth.continuous
  -- the Sobolev data
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 102 * d + 1020 := ⟨_, rfl⟩
  have hmR : (m : ℝ) = 102 * (d : ℝ) + 1020 := by rw [hm]; push_cast; ring
  have hm1 : (d : ℝ) / 2 + ((1 : ℕ) : ℝ) + 2 < m := by
    rw [hmR]; push_cast; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  obtain ⟨Cv, hCv0, hCv⟩ := mn_force_bound hd hs0 hsd β a hβ ha ρβ hρβ 1 m hm1
  set E : ℝ := |C₁| * |εstar| with hEdef
  have hE0 : 0 ≤ E := by positivity
  obtain ⟨c, K, hc, hK0, hKb⟩ := s105r_leibniz hq hR Cv E hCv0 hE0
  obtain ⟨P, hP0, hP⟩ := s105r_gauss_reg (d := d) hc
  -- data of the force part
  obtain ⟨M0, hM0⟩ := HRS.MS.Mov0.mov0_B_bdd hR
  set Λ1 : ℝ := 4 * K + P * K with hΛ1
  set Λ2 : ℝ := |(rieszConst d s)⁻¹| * (E + β⁻¹ * E + β⁻¹ * |M0|) with hΛ2
  have hΛ10 : 0 ≤ Λ1 := by positivity
  -- pointwise structure of `ρ t`
  have hstruct : ∀ t : ℝ, 0 ≤ t →
      (ρ t = fun x => ρβ x + Real.sqrt (ρβ x) *
        ((ρ t x - ρβ x) / Real.sqrt (ρβ x))) ∧
      Continuous (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) ∧
      MemOsc (m : ℝ) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) ∧
      oscNorm (m : ℝ) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) ≤ E := by
    intro t ht
    refine ⟨funext fun x => ?_, ?_, ?_, ?_⟩
    · have hsq : 0 < Real.sqrt (ρβ x) := Real.sqrt_pos.2 (hpos x)
      field_simp
      ring
    · exact ((hres.regular t ht).sub hρβc).div hρβc.sqrt (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
    · rw [hmR]; exact (hres.weighted t ht).1
    · rw [hmR]
      refine ((hres.weighted t ht).2).trans ?_
      have h1 : Real.exp (-c₁ * t) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := hres.cpos
        nlinarith
      have h2 : 0 ≤ Real.exp (-c₁ * t) := (Real.exp_pos _).le
      calc C₁ * εstar * Real.exp (-c₁ * t) ≤ |C₁ * εstar| * Real.exp (-c₁ * t) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h2
        _ ≤ |C₁ * εstar| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = E := by rw [mul_one, abs_mul]
  -- the `C^3` part
  have hreg3 : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (ρ t) ∧
      HRS.MemCb 3 (ρ t) ∧ weightedSupE 3 ((d : ℝ) + 3) (ρ t) ≤ ENNReal.ofReal (P * K) ∧
      HRS.cbNorm 3 (ρ t) ≤ 4 * K := by
    intro t ht
    obtain ⟨hdec, hvc, hvm, hvn⟩ := hstruct t ht
    obtain ⟨hv3, hvb, -⟩ := hCv _ hvc hvm
    have hv3' : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) := by
      simpa using hv3
    have hvb' : ∀ k ≤ 3, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) x‖ ≤
        Cv * E := fun k hk x => (hvb k (by omega) x).trans (mul_le_mul_of_nonneg_left hvn hCv0)
    obtain ⟨hcd, hKb'⟩ := hKb _ hv3' hvb'
    rw [← hdec] at hcd hKb'
    exact ⟨hcd, hP (ρ t) K hK0 hcd hKb'⟩
  -- the singular force part
  have hforce : ∀ t : ℝ, 0 ≤ t → ∀ x : Euc d,
      ‖convGradConvW (rieszKernelGrad d s) (ρ t) x‖ ≤ E + β⁻¹ * E + β⁻¹ * |M0| := by
    intro t ht x
    obtain ⟨hcd, -⟩ := hreg3 t ht
    have hρtd : Differentiable ℝ (ρ t) := hcd.differentiable (by simp)
    have hρtpos : ∀ y, 0 < ρ t y := fun y =>
      lt_of_lt_of_le (mul_pos (inv_pos.2 hC1) (hpos y)) (hres.ratio t ht y).1
    have hlogt : Differentiable ℝ (fun y => Real.log (ρ t y)) := fun y =>
      ((hρtd y).hasFDerivAt.log (hρtpos y).ne').differentiableAt
    have hlogb : Differentiable ℝ (fun y => Real.log (ρβ y)) := fun y =>
      ((hR.smooth.differentiable (by simp) y).hasFDerivAt.log (hpos y).ne').differentiableAt
    have hdiv : (fun y => Real.log (ρ t y / ρβ y)) = fun y => Real.log (ρ t y) - Real.log (ρβ y) :=
      funext fun y => Real.log_div (hρtpos y).ne' (hpos y).ne'
    set w : Euc d := gradient (fun y => Real.log (ρ t y / ρβ y)) x with hw
    set L : Euc d := gradient (fun y => Real.log (ρβ y)) x with hL
    have hgrad : gradient (fun y => Real.log (ρ t y)) x = w + L := by
      rw [hw, hdiv]
      refine ext_inner_left ℝ fun v => ?_
      rw [HRS.MS.PoisKolm.kl_inner_gradient, inner_add_right, HRS.MS.PoisKolm.kl_inner_gradient,
        HRS.MS.PoisKolm.kl_inner_gradient, fderiv_fun_sub (hlogt x) (hlogb x)]
      simp [hL]
    -- velocity bounds
    have hvel := hres.velocity t ht
    have hX : C₁ * εstar * Real.exp (-c₁ * t) ≤ E := by
      have h1 : Real.exp (-c₁ * t) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := hres.cpos
        nlinarith
      have h2 : 0 ≤ Real.exp (-c₁ * t) := (Real.exp_pos _).le
      calc C₁ * εstar * Real.exp (-c₁ * t) ≤ |C₁ * εstar| * Real.exp (-c₁ * t) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h2
        _ ≤ |C₁ * εstar| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = E := by rw [mul_one, abs_mul]
    have hvel' := hvel.trans (ENNReal.ofReal_le_ofReal hX)
    have hwb : ‖w‖ ≤ E := by
      have h1 := (s105r_cbvec_zero (100 * d + 1000) (fun x => gradient (fun y => Real.log (ρ t y / ρβ y)) x) x).trans
        (le_self_add.trans hvel')
      exact (ENNReal.ofReal_le_ofReal_iff hE0).1 h1
    set u : Euc d := β⁻¹ • gradient (fun y => Real.log (ρ t y)) x + a • x +
      convGradConvW (rieszKernelGrad d s) (ρ t) x with hu
    have hub : ‖u‖ ≤ E := by
      have h1 := (s105r_cbvec_zero (100 * d + 1000) (fun x => β⁻¹ • gradient (fun y => Real.log (ρ t y)) x +
        a • x + convGradConvW (rieszKernelGrad d s) (ρ t) x) x).trans
        (le_add_self.trans hvel')
      exact (ENNReal.ofReal_le_ofReal_iff hE0).1 h1
    -- the equilibrium identity
    have hth := HRS.MS.Mov0.mv0_thermal_force hd hs0 hsd ha hβ hρβ x
    have hLeq : L = -(β * a) • x + B x := HRS.MS.Mov0.mov0_grad_log hR x
    set C0 : Euc d := convGradConvW (rieszKernelGrad d s) ρβ x with hC0
    have hC0eq : C0 = -(β⁻¹ • B x) := by
      have hβne : β ≠ 0 := hβ.ne'
      have e1 : β⁻¹ • L + a • x + C0 = 0 := hth
      rw [hLeq, smul_add, smul_smul] at e1
      have e2 : β⁻¹ * -(β * a) = -a := by field_simp
      rw [e2, neg_smul] at e1
      linear_combination (norm := module) e1
    have hC0b : ‖C0‖ ≤ β⁻¹ * |M0| := by
      rw [hC0eq, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hβ]
      exact mul_le_mul_of_nonneg_left ((hM0 x).trans (le_abs_self _)) (inv_nonneg.2 hβ.le)
    have hu' : u = β⁻¹ • (w + L) + a • x + convGradConvW (rieszKernelGrad d s) (ρ t) x := by
      rw [← hgrad]
    have heq : convGradConvW (rieszKernelGrad d s) (ρ t) x = u - β⁻¹ • w + C0 := by
      have hth' : β⁻¹ • L + a • x + C0 = 0 := hth
      linear_combination (norm := module) (-1 : ℝ) • hu' + (-1 : ℝ) • hth'
    rw [heq]
    calc ‖u - β⁻¹ • w + C0‖ ≤ ‖u - β⁻¹ • w‖ + ‖C0‖ := norm_add_le _ _
      _ ≤ (‖u‖ + ‖β⁻¹ • w‖) + ‖C0‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ E + β⁻¹ * E + β⁻¹ * |M0| := by
          have : ‖β⁻¹ • w‖ ≤ β⁻¹ * E := by
            rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hβ]
            exact mul_le_mul_of_nonneg_left hwb (inv_nonneg.2 hβ.le)
          linarith
  refine ⟨max Λ1 Λ2, ⟨fun t ht => ?_, fun _ t ht x => ?_⟩⟩
  · obtain ⟨-, hmc, hws, hcb⟩ := hreg3 t ht.1
    refine ⟨hmc, lt_of_le_of_lt hws ENNReal.ofReal_lt_top, ?_⟩
    have h1 : (weightedSupE 3 ((d : ℝ) + 3) (ρ t)).toReal ≤ P * K := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hws
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    exact (add_le_add hcb h1).trans (le_max_left _ _)
  · have h1 := hforce t ht.1 x
    unfold fracForceRd
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)).trans (le_max_right _ _)

/-- The form needed by the ties of S104b (`εn = 1`). -/
theorem s105r_hReg : ∀ {d : ℕ}, 2 ≤ d → ∀ (s a β c₁ C₁ : ℝ), 0 ≤ s → s < d → 0 < a → 0 < β → ∃ εn : ℝ, 0 < εn ∧
      ∀ εstar : ℝ, εstar ≤ εn → S105nReg d s a β εstar c₁ C₁ :=
  fun {_} hd s a β c₁ C₁ hs0 hsd ha hβ => ⟨1, one_pos, fun εstar _ => s105r_reg hd hs0 hsd ha hβ εstar c₁ C₁⟩

end HRS.MS.S105r
