import HRS.Sections.ScrnAux33

/-!
# Packet SCRN, part 34: the transported tests `f_a` of the mesoscopic tests and their decay

* `scrn_f_exists`: for `ψ = mesoTest d ℓ x₀ φ` and `t ≥ 0` there is a transported test `f` (the constant
  datum for `t = 0`, the classical adjoint solution for `t > 0`) with `f̂(r,k) = e^{-(t-r)λ_k} ψ̂(k)`.
* `scrn_lam_nonneg`: `λ_k ≥ 0`.
* `scrn_f_decay`: `ScrnDecay ψ (f r) (exp (-(t-r) λ_*))` for `r ∈ [0,t]` with
  `λ_* = min(c, 1/b₊) ℓ^{max(q-2,0)}`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

open PDE PDE.ClassicalAux

theorem scrn_lam_nonneg {s : ℝ} (hc : 0 < rieszConst d s) {invβ : ℝ} (hβ : 0 ≤ invβ)
    (k : Lattice d) : 0 ≤ scrnLam d s invβ k := by
  by_cases hk : k = 0
  · subst hk
    unfold scrnLam
    have : Lattice.enorm (0 : Lattice d) = 0 := by
      simp [Lattice.enorm, Lattice.toEuc]; rfl
    rw [this]; simp
  · rw [scrn_lam_eq _ hk]
    have hr : 0 < 2 * Real.pi * Lattice.enorm k := by
      have := one_le_enorm_of_ne_zero hk
      positivity
    positivity

theorem scrn_f_exists (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (x₀ : Euc d) {φ : Euc d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ f : ℝ → Torus d → ℝ,
      ((t = 0 ∧ f = fun _ => mesoTest d ℓ x₀ φ) ∨
        (0 < t ∧ IsClassicalAdjointSolution (mfData d s hs0 hsd (fun _ => 0) β hβ)
          (fun _ _ => (1 : ℝ)) t (mesoTest d ℓ x₀ φ) f)) ∧
      ∀ r ∈ Icc 0 t, ∀ k : Lattice d,
        coeffOf (f r) k = ((Real.exp (-(t - r) * scrnLam d s β⁻¹ k) : ℝ) : ℂ) *
          coeffOf (mesoTest d ℓ x₀ φ) k := by
  rcases ht.eq_or_lt with h0 | hpos
  · refine ⟨fun _ => mesoTest d ℓ x₀ φ, Or.inl ⟨h0.symm, rfl⟩, fun r hr k => ?_⟩
    have : r = t := le_antisymm hr.2 (by linarith [hr.1, h0])
    subst this
    simp
  · have hsm : Torus.IsSmooth (mesoTest d ℓ x₀ φ) := isCk_mesoTest hℓ x₀ hφ hc _ le_rfl
    have hcont : Continuous (mesoTest d ℓ x₀ φ) :=
      KernelGrad.isCk_continuous (isCk_mesoTest hℓ x₀ hφ hc 1 (by
        have h : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
        exact h))
    obtain ⟨f, hcls, hco⟩ := Scrn.classical_diag hd hs0 hsd hβ hpos hcont
      (MFSemigroup.memSobolev_of_isSmooth hsm _)
    refine ⟨f, Or.inr ⟨hpos, hcls⟩, fun r hr k => ?_⟩
    rw [hco r hr k, Complex.ofReal_exp]

theorem scrn_f_decay (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ℓ bp : ℝ} (hℓ : 0 < ℓ) (hbp : 0 < bp) (hβb : β * ℓ ^ ((d : ℝ) - s) ≤ bp) (x₀ : Euc d)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) {t : ℝ} (ht : 0 ≤ t)
    {f : ℝ → Torus d → ℝ}
    (hf : (t = 0 ∧ f = fun _ => mesoTest d ℓ x₀ φ) ∨
        (0 < t ∧ IsClassicalAdjointSolution (mfData d s hs0 hsd (fun _ => 0) β hβ)
          (fun _ _ => (1 : ℝ)) t (mesoTest d ℓ x₀ φ) f))
    (hfc : ∀ r ∈ Icc 0 t, ∀ k : Lattice d,
        coeffOf (f r) k = ((Real.exp (-(t - r) * scrnLam d s β⁻¹ k) : ℝ) : ℂ) *
          coeffOf (mesoTest d ℓ x₀ φ) k) :
    ∀ r ∈ Icc 0 t, ScrnDecay (mesoTest d ℓ x₀ φ) (f r)
      (Real.exp (-(t - r) * (min (rieszConst d s) bp⁻¹ * ℓ ^ (max ((d : ℝ) - s - 2) 0)))) := by
  intro r hr
  have hcr : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
  set lamS : ℝ := min (rieszConst d s) bp⁻¹ * ℓ ^ (max ((d : ℝ) - s - 2) 0) with hlamS
  have hlamS0 : 0 ≤ lamS := by
    have : 0 < min (rieszConst d s) bp⁻¹ := lt_min hcr (inv_pos.2 hbp)
    positivity
  have htr : 0 ≤ t - r := by linarith [hr.2]
  have hlow : ∀ k : Lattice d, k ≠ 0 → lamS ≤ scrnLam d s β⁻¹ k := by
    intro k hk
    refine scrn_lam_lower hcr hℓ hbp ?_ hk
    rw [div_le_iff₀ hbp]
    have h1 : 0 < ℓ ^ ((d : ℝ) - s) := Real.rpow_pos_of_pos hℓ _
    rw [inv_mul_eq_div, le_div_iff₀ hβ]
    nlinarith
  have hcont : Continuous (f r) := by
    rcases hf with ⟨h0, hfe⟩ | ⟨hpos, hcl⟩
    · subst hfe
      exact KernelGrad.isCk_continuous (isCk_mesoTest hℓ x₀ hφ hc 1 (by
        have h : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
        exact h))
    · exact scrn_cont_of_ck2 (hcl.c2 r hr)
  have hnorm : ∀ k : Lattice d, ‖coeffOf (f r) k‖ =
      Real.exp (-(t - r) * scrnLam d s β⁻¹ k) * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ := by
    intro k
    rw [hfc r hr k, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine ⟨Real.exp_pos _ |>.le, ?_, hcont, fun k => ?_, fun k hk => ?_⟩
  · rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg htr hlamS0]
  · rw [hnorm k]
    have : Real.exp (-(t - r) * scrnLam d s β⁻¹ k) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_nonneg htr (scrn_lam_nonneg hcr (inv_nonneg.2 hβ.le) k)]
    calc _ ≤ 1 * ‖coeffOf (mesoTest d ℓ x₀ φ) k‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := one_mul _
  · rw [hnorm k]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    nlinarith [hlow k hk]

end HRS
