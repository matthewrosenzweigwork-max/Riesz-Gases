import HRS.PDE.Toolbox.CoeffBounds
import HRS.Kernel.GradReg
import HRS.PDE.MeanFieldAprioriPhi

/-!
# `C^j` calculus tools for the velocity decay (package P8a of MF-01)

Products, inverses, logarithms and vector-valued sums on the torus, with `C_b^j` bounds.
Used by `MeanFieldVelocity.lean` (packet P8b).  Nothing here depends on the mean-field theory,
and this file imports neither `HRS.PDE.MeanField` nor `HRS.PDE.MeanFieldInputs`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.PDE.MFVelocity

variable {d : ℕ}

section Smul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- General `C^j` bound of a scalar-times-`E`-valued product, with the explicit constant
`(j+1) 2^j`. -/
theorem cbNorm_smul_le_gen (j : ℕ) (a : Torus d → ℝ) (v : Torus d → E) (ha : Torus.IsCk j a)
    (hv : Torus.IsCk j v) :
    Torus.IsCk j (fun x => a x • v x) ∧
      Torus.cbNorm j (fun x => a x • v x) ≤
        ((j + 1 : ℝ) * 2 ^ j) * Torus.cbNorm j a * Torus.cbNorm j v := by
  have e : Torus.lift (fun x => a x • v x) = fun y => Torus.lift a y • Torus.lift v y := rfl
  have hCk : Torus.IsCk j (fun x => a x • v x) := by
    unfold Torus.IsCk at *
    rw [e]
    exact ha.smul hv
  refine ⟨hCk, ?_⟩
  have hna : 0 ≤ Torus.cbNorm j a := HRS.KernelGrad.cbNorm_nonneg' a j
  have hnv : 0 ≤ Torus.cbNorm j v := HRS.KernelGrad.cbNorm_nonneg' v j
  have hterm : ∀ n ∈ Finset.range (j + 1),
      (⨆ x : Euc d, ‖iteratedFDeriv ℝ n (Torus.lift (fun x => a x • v x)) x‖) ≤
        2 ^ j * Torus.cbNorm j a * Torus.cbNorm j v := by
    intro n hn
    have hnj : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    refine ciSup_le fun y => ?_
    rw [e]
    have hb := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (f := Torus.lift a) (g := Torus.lift v)
      (N := (j : WithTop ℕ∞)) ha hv y (n := n) (by exact_mod_cast hnj)
    refine hb.trans ?_
    calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Torus.cbNorm j a * Torus.cbNorm j v := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have h1 := HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm ha (j := i) (hin.trans hnj) y
          have h2 := HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm hv (j := n - i)
            ((Nat.sub_le _ _).trans hnj) y
          have hc : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
          gcongr
      _ = 2 ^ n * Torus.cbNorm j a * Torus.cbNorm j v := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact_mod_cast Nat.sum_range_choose n
      _ ≤ _ := by
          have : (2 : ℝ) ^ n ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hnj
          gcongr
  have h : Torus.cbNorm j (fun x => a x • v x) ≤
      ∑ _n ∈ Finset.range (j + 1), 2 ^ j * Torus.cbNorm j a * Torus.cbNorm j v :=
    Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end Smul

/-- (D1) `C^j` bound of a scalar–vector product. -/
theorem exists_cbNorm_smul_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Torus d → ℝ) (v : Torus d → Euc d), Torus.IsCk j a → Torus.IsCk j v →
      Torus.IsCk j (fun x => a x • v x) ∧
        Torus.cbNorm j (fun x => a x • v x) ≤ C * Torus.cbNorm j a * Torus.cbNorm j v :=
  ⟨(j + 1 : ℝ) * 2 ^ j, by positivity, fun a v ha hv => cbNorm_smul_le_gen j a v ha hv⟩

/-- (D1') `C^j` bound of a scalar product. -/
theorem exists_cbNorm_mul_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : Torus d → ℝ), Torus.IsCk j a → Torus.IsCk j b →
      Torus.IsCk j (fun x => a x * b x) ∧
        Torus.cbNorm j (fun x => a x * b x) ≤ C * Torus.cbNorm j a * Torus.cbNorm j b :=
  ⟨(j + 1 : ℝ) * 2 ^ j, by positivity, fun a b ha hb => by
    simpa only [smul_eq_mul] using cbNorm_smul_le_gen j a b ha hb⟩

/-- (D3) `log ∘ ρ ∈ C^j` for `ρ ∈ C^j` positive. -/
theorem isCk_log (j : ℕ) (ρ : Torus d → ℝ) (hρ : Torus.IsCk j ρ) (hpos : ∀ x, 0 < ρ x) :
    Torus.IsCk j (fun y => Real.log (ρ y)) := by
  unfold Torus.IsCk at *
  have e : Torus.lift (fun y => Real.log (ρ y)) = fun z => Real.log (Torus.lift ρ z) := rfl
  rw [e]
  exact hρ.log fun z => (hpos (Torus.mk z)).ne'

/-- (D3) `∇ log ρ = ρ⁻¹ ∇ρ` for positive `C¹` `ρ`. -/
theorem grad_log_eq (ρ : Torus d → ℝ) (hρ : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x) :
    Torus.IsCk 1 (fun y => Real.log (ρ y)) ∧
      ∀ x, Torus.grad (fun y => Real.log (ρ y)) x = (ρ x)⁻¹ • Torus.grad ρ x := by
  refine ⟨isCk_log 1 ρ (by simpa using hρ) hpos, fun x => ?_⟩
  ext i
  have hΦ : ContDiffOn ℝ 1 Real.log (Set.Ioi 0) :=
    (Real.contDiffOn_log (n := 1)).mono fun y hy => (ne_of_gt (Set.mem_Ioi.mp hy))
  have h := MFApriori.partialDeriv_comp i Real.log (Set.Ioi 0) isOpen_Ioi hΦ ρ hρ hpos x
  rw [MFAux.grad_apply]
  simp [h, Real.deriv_log, MFAux.grad_apply]

/-- (D4) Vector-valued `C^j` algebra: sums. -/
theorem isCk_add_vec (j : ℕ) (φ ψ : Torus d → Euc d) (hφ : Torus.IsCk j φ) (hψ : Torus.IsCk j ψ) :
    Torus.IsCk j (φ + ψ) := by
  unfold Torus.IsCk at *
  have e : Torus.lift (φ + ψ) = Torus.lift φ + Torus.lift ψ := rfl
  rw [e]
  exact hφ.add hψ

theorem cbNorm_add_le_vec (j : ℕ) (φ ψ : Torus d → Euc d) (hφ : Torus.IsCk j φ)
    (hψ : Torus.IsCk j ψ) : Torus.cbNorm j (φ + ψ) ≤ Torus.cbNorm j φ + Torus.cbNorm j ψ := by
  unfold Torus.cbNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n hn => ?_
  have hnj : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hφ' : ContDiff ℝ n (Torus.lift φ) := hφ.of_le (by exact_mod_cast hnj)
  have hψ' : ContDiff ℝ n (Torus.lift ψ) := hψ.of_le (by exact_mod_cast hnj)
  have b1 := HRS.KernelGrad.bddAbove_iteratedFDeriv hφ hnj
  have b2 := HRS.KernelGrad.bddAbove_iteratedFDeriv hψ hnj
  refine ciSup_le fun x => ?_
  have e : Torus.lift (φ + ψ) = Torus.lift φ + Torus.lift ψ := rfl
  rw [e, iteratedFDeriv_add_apply hφ'.contDiffAt hψ'.contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (le_ciSup b1 x) (le_ciSup b2 x))

/-- (D4) Vector-valued `C^j` algebra: constant multiples. -/
theorem cbNorm_const_smul_le_vec (j : ℕ) (a : ℝ) (φ : Torus d → Euc d) (hφ : Torus.IsCk j φ) :
    Torus.IsCk j (fun x => a • φ x) ∧ Torus.cbNorm j (fun x => a • φ x) ≤ |a| * Torus.cbNorm j φ := by
  refine ⟨?_, ?_⟩
  · unfold Torus.IsCk at *
    have e : Torus.lift (fun x => a • φ x) = fun z => a • Torus.lift φ z := rfl
    rw [e]
    exact (contDiff_const (c := a)).smul hφ
  · set T : Euc d →L[ℝ] Euc d := a • ContinuousLinearMap.id ℝ (Euc d) with hT
    have h := HRS.PDE.cbNorm_clm_comp_le T j φ hφ
    have hn : ‖T‖ ≤ |a| := by
      refine (ContinuousLinearMap.opNorm_smul_le a _).trans ?_
      rw [Real.norm_eq_abs]
      calc |a| * ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ |a| * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg a)
        _ = |a| := mul_one _
    have hc : Torus.cbNorm j (fun x => a • φ x) = Torus.cbNorm j (fun x => T (φ x)) := rfl
    rw [hc]
    exact h.trans (mul_le_mul_of_nonneg_right hn (HRS.KernelGrad.cbNorm_nonneg' φ j))

/-! ### The inverse -/

/-- A smooth compactly supported extension of `r ↦ r⁻¹` from `[cL, cU]`. -/
theorem exists_inv_cutoff (cL cU : ℝ) (hcL : 0 < cL) (hcU : cL ≤ cU) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g ∧
      ∀ r, cL ≤ r → r ≤ cU → g r = r⁻¹ := by
  let ψ : ContDiffBump ((cL + cU) / 2) :=
    { rIn := (cU - cL) / 2 + cL / 4
      rOut := (cU - cL) / 2 + cL / 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hψ0 : ∀ r, r ≤ cL / 2 → ψ r = 0 := by
    intro r hr
    apply ContDiffBump.zero_of_le_dist
    rw [Real.dist_eq]
    show (cU - cL) / 2 + cL / 2 ≤ |r - (cL + cU) / 2|
    have : (cL + cU) / 2 - r ≤ |r - (cL + cU) / 2| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  refine ⟨fun r => ψ r * r⁻¹, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro r
    by_cases hr : r = 0
    · subst hr
      have hev : (fun r : ℝ => ψ r * r⁻¹) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
        have : Set.Iio (cL / 2) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by linarith)
        filter_upwards [this] with x hx
        rw [hψ0 x (le_of_lt hx), zero_mul]
      exact (contDiffAt_const).congr_of_eventuallyEq hev
    · exact ψ.contDiffAt.mul (contDiffAt_inv ℝ hr)
  · refine HasCompactSupport.mul_right ψ.hasCompactSupport
  · intro r h1 h2
    have : ψ r = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      show -((cU - cL) / 2 + cL / 4) ≤ _ ∧ _ ≤ (cU - cL) / 2 + cL / 4
      constructor <;> linarith
    simp [this]

/-- Uniform bound on the first `j` derivatives of the cutoff. -/
theorem exists_deriv_bound (g : ℝ → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hsupp : HasCompactSupport g) (j : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ i, i ≤ j → ∀ r, ‖iteratedFDeriv ℝ i g r‖ ≤ Cg := by
  have h : ∀ i : ℕ, ∃ M : ℝ, ∀ r, ‖iteratedFDeriv ℝ i g r‖ ≤ M := fun i =>
    (hsupp.iteratedFDeriv i).exists_bound_of_continuous
      (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  choose M hM using h
  refine ⟨∑ i ∈ Finset.range (j + 1), |M i|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun i hi r => ?_⟩
  refine (hM i r).trans ?_
  refine (le_abs_self _).trans ?_
  exact Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

/-- (D2) `C^j` bound of `1/ρ` for `cL ≤ ρ ≤ cU` (Faà di Bruno through a smooth compactly
supported extension of `r ↦ 1/r` from `[cL, cU]`). -/
theorem exists_cbNorm_inv_le (j : ℕ) (cL cU : ℝ) (hcL : 0 < cL) (hcU : cL ≤ cU) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Torus d → ℝ, Torus.IsCk j ρ → (∀ x, cL ≤ ρ x ∧ ρ x ≤ cU) →
      Torus.IsCk j (fun x => (ρ x)⁻¹) ∧
        Torus.cbNorm j (fun x => (ρ x)⁻¹) ≤ C * (1 + Torus.cbNorm j ρ) ^ j := by
  obtain ⟨g, hg, hsupp, hgr⟩ := exists_inv_cutoff cL cU hcL hcU
  obtain ⟨Cg, hCg0, hCg⟩ := exists_deriv_bound g hg hsupp j
  have hgj : ContDiff ℝ (j : WithTop ℕ∞) g := hg.of_le (by exact_mod_cast le_top)
  refine ⟨(j + 1 : ℝ) * (j.factorial : ℝ) * Cg, by positivity, fun ρ hρ hb => ?_⟩
  have e : Torus.lift (fun x => (ρ x)⁻¹) = g ∘ Torus.lift ρ := by
    funext y
    simp only [Function.comp, Torus.lift]
    rw [hgr _ (hb _).1 (hb _).2]
  have hCk : Torus.IsCk j (fun x => (ρ x)⁻¹) := by
    unfold Torus.IsCk
    rw [e]
    exact hgj.comp hρ
  refine ⟨hCk, ?_⟩
  set D : ℝ := 1 + Torus.cbNorm j ρ with hD
  have hcb : 0 ≤ Torus.cbNorm j ρ := HRS.KernelGrad.cbNorm_nonneg' ρ j
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have hterm : ∀ n ∈ Finset.range (j + 1),
      (⨆ x : Euc d, ‖iteratedFDeriv ℝ n (Torus.lift (fun x => (ρ x)⁻¹)) x‖) ≤
        (j.factorial : ℝ) * Cg * D ^ j := by
    intro n hn
    have hnj : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    refine ciSup_le fun y => ?_
    rw [e]
    have hb' := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := g) (f := Torus.lift ρ)
      (n := n) (N := (j : WithTop ℕ∞)) hgj hρ (by exact_mod_cast hnj) y (C := Cg) (D := D)
      (fun i hi => hCg i (hi.trans hnj) _)
      (fun i hi1 hin => by
        have h1 := HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm hρ (j := i) (hin.trans hnj) y
        calc _ ≤ Torus.cbNorm j ρ := h1
          _ ≤ D := by rw [hD]; linarith
          _ ≤ D ^ i := le_self_pow₀ hD1 (by omega))
    refine hb'.trans ?_
    have h1 : (n.factorial : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_le hnj
    have h2 : D ^ n ≤ D ^ j := pow_le_pow_right₀ hD1 hnj
    have h3 : (0 : ℝ) ≤ D ^ n := by positivity
    have h4 : (0 : ℝ) ≤ (n.factorial : ℝ) * Cg := by positivity
    calc (n.factorial : ℝ) * Cg * D ^ n ≤ (j.factorial : ℝ) * Cg * D ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hCg0) h3
      _ ≤ (j.factorial : ℝ) * Cg * D ^ j :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have h : Torus.cbNorm j (fun x => (ρ x)⁻¹) ≤
      ∑ _n ∈ Finset.range (j + 1), (j.factorial : ℝ) * Cg * D ^ j :=
    Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end HRS.PDE.MFVelocity
