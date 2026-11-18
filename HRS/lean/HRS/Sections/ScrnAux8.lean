import HRS.Sections.ScrnAux7

/-!
# Packet SCRN, part 8: the Fourier-diagonal adjoint solution for `ρ ≡ 1`

For `D = mfData d s _ _ 0 β _`, `ρ ≡ 1` and a test `ψ` (smooth, `MemSobolev m_*`), the classical adjoint
solution of Proposition 3.9 satisfies `coeffOf (f^r) k = e^{-(T-r) λ_k} ψ̂(k)` (`scrn_classical_diag`),
obtained from `hasDerivAt_coeff`, `coeffOf_backwardGenerator`, `scrn_forwardGen_one` and scalar ODE uniqueness.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

/-- A continuous function on `[a,b]` with zero derivative on `(a,b)` is constant. -/
lemma scrn_const_of_deriv_zero (w : ℝ → ℂ) {a b : ℝ} (hab : a < b) (hc : ContinuousOn w (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt w 0 x) : ∀ x ∈ Icc a b, w x = w b := by
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hconst : ∀ x ∈ Ioo a b, w x = w ((a + b) / 2) := by
    intro x hx
    exact (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hd y hy).deriv) hx hm)
  have hext : EqOn w (fun _ => w ((a + b) / 2)) (Icc a b) :=
    Set.EqOn.of_subset_closure hconst hc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  intro x hx
  rw [hext hx, hext (right_mem_Icc.2 hab.le)]

namespace Scrn

open PDE PDE.ClassicalAux

theorem adjointData (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) (m : ℕ) :
    ∃ (R : Regime) (ν₀ MB Λ VB : ℝ), ∀ T : ℝ, 0 < T →
      AdjointData s m R MB Λ VB (mfData d s hs0 hsd (fun _ => 0) β hβ) ν₀ T (fun _ _ => (1 : ℝ)) := by
  have hdens : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one, measurable_const, by simp⟩
  have hsm1 : ∀ n : ℕ, Torus.IsCk n (fun _ : Torus d => (1 : ℝ)) := fun n => by
    unfold Torus.IsCk Torus.lift; exact contDiff_const
  have hsm0 : ∀ n : ℕ, Torus.IsCk n (fun _ : Torus d => (0 : ℝ)) := fun n => by
    unfold Torus.IsCk Torus.lift; exact contDiff_const
  by_cases hR : s ≤ (d : ℝ) - 2
  · refine ⟨Regime.R1, β⁻¹, 1, Torus.cbNorm (m + 3) (fun _ : Torus d => (1 : ℝ)),
      Torus.cbNorm (m + 3) (fun _ : Torus d => (0 : ℝ)), fun T hT => ?_⟩
    refine ⟨rfl, ?_, ⟨hsm0 _, le_rfl⟩, ⟨fun r hr => hdens, fun r hr => hsm1 _, fun r hr => le_rfl,
      fun ψ hψ => continuousOn_const⟩, hT, hR⟩
    intro i j
    show |((-1 : Matrix (Fin d) (Fin d) ℝ) i j)| ≤ 1
    simp only [Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  · push_neg at hR
    refine ⟨Regime.R3, β⁻¹, 1, Torus.cbNorm (m + 3) (fun _ : Torus d => (1 : ℝ)),
      Torus.cbNorm (m + 3) (fun _ : Torus d => (0 : ℝ)), fun T hT => ?_⟩
    refine ⟨rfl, ?_, ⟨hsm0 _, le_rfl⟩, ⟨fun r hr => hdens, fun r hr => hsm1 _, fun r hr => le_rfl,
      fun ψ hψ => continuousOn_const⟩, hT, ⟨hR, inv_pos.2 hβ, le_rfl⟩⟩
    intro i j
    show |((-1 : Matrix (Fin d) (Fin d) ℝ) i j)| ≤ 1
    simp only [Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp


/-- The Fourier-diagonal classical solution. -/
theorem classical_diag (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {t : ℝ} (ht : 0 < t) {ψ : Torus d → ℝ} (hψc : Continuous ψ)
    (hψS : MemSobolev (mStar d : ℝ) ψ) :
    ∃ f : ℝ → Torus d → ℝ,
      IsClassicalAdjointSolution (mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ _ => (1 : ℝ)) t ψ f ∧
      ∀ r ∈ Icc 0 t, ∀ k : Lattice d,
        coeffOf (f r) k = Complex.exp (((-(t - r) * scrnLam d s β⁻¹ k : ℝ) : ℂ)) * coeffOf ψ k := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨R, ν₀, MB, Λ, VB, hA⟩ := adjointData hd1 hs0 hsd hβ (mStar d)
  obtain ⟨C, Cs, hC, hCs, h⟩ := adjoint_torus_classical hd1 s hs0 hsd (mStar d) le_rfl R MB Λ VB
  obtain ⟨hcls, -⟩ := h (mfData d s hs0 hsd (fun _ => 0) β hβ) ν₀ t (fun _ _ => (1 : ℝ))
    (hA t ht) t ⟨ht, le_rfl⟩ ψ hψc hψS
  set D := mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  set f : ℝ → Torus d → ℝ := fun r x => toFun (propagatorCoeff D (fun _ _ => (1 : ℝ)) (mStar d) t
    (coeffOf ψ) (t - r)) x with hf
  refine ⟨f, hcls, fun r hr k => ?_⟩
  have hK := convKernelFacts hd1 D
  have hV1 : Torus.IsCk 1 D.V := by
    show Torus.IsCk 1 (fun _ : Torus d => (0 : ℝ))
    unfold Torus.IsCk Torus.lift; exact contDiff_const
  have hρ1 : Torus.IsCk 1 (fun _ : Torus d => (1 : ℝ)) := by
    unfold Torus.IsCk Torus.lift; exact contDiff_const
  set lam : ℝ := scrnLam d s β⁻¹ k with hlam
  set y : ℝ → ℂ := fun r => coeffOf (f r) k with hy
  have hycont : ContinuousOn y (Icc 0 t) := continuousOn_coeff hcls k
  have hyder : ∀ r ∈ Ioo 0 t, HasDerivAt y ((lam : ℂ) * y r) r := by
    intro r hr
    have h1 := hasDerivAt_coeff hcls k hr
    have h2 := coeffOf_backwardGenerator D hK hV1 (ρ := fun _ => (1 : ℝ)) hρ1
      (hcls.c2 r (Ioo_subset_Icc_self hr))
    have h3 := scrn_forwardGen_one hs0 hsd β hβ (coeffOf (f r)) k
    rw [h2] at h1
    have h4 : (fun r' => coeffOf (f r') k) = y := rfl
    rw [h4] at h1
    convert h1 using 1
    rw [h3]
    simp only [hy, hlam]
    ring
  set w : ℝ → ℂ := fun r => Complex.exp (((lam * (t - r) : ℝ) : ℂ)) * y r with hw
  have hwc : ContinuousOn w (Icc 0 t) := by
    refine ContinuousOn.mul ?_ hycont
    exact (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
      (by fun_prop))).continuousOn
  have hwd : ∀ x ∈ Ioo 0 t, HasDerivAt w 0 x := by
    intro x hx
    have he : HasDerivAt (fun r : ℝ => Complex.exp (((lam * (t - r) : ℝ) : ℂ)))
        (Complex.exp (((lam * (t - x) : ℝ) : ℂ)) * (-(lam : ℂ))) x := by
      have h0 : HasDerivAt (fun r : ℝ => ((lam * (t - r) : ℝ) : ℂ)) (-(lam : ℂ)) x := by
        have := ((hasDerivAt_id x).const_sub t).const_mul lam
        have h5 := this.ofReal_comp
        exact h5.congr_deriv (by push_cast; ring)
      exact h0.cexp
    have := he.mul (hyder x hx)
    convert this using 1
    ring
  have hconst := scrn_const_of_deriv_zero w ht hwc hwd r hr
  have hwt : w t = coeffOf ψ k := by
    simp only [hw, hy, sub_self, mul_zero, Complex.ofReal_zero, Complex.exp_zero, one_mul]
    rw [show f t = ψ from hcls.terminal]
  rw [hwt] at hconst
  have : y r = Complex.exp (((-(t - r) * lam : ℝ) : ℂ)) * coeffOf ψ k := by
    have h6 : y r = Complex.exp (((-(lam * (t - r)) : ℝ) : ℂ)) * w r := by
      simp only [hw]
      rw [← mul_assoc, ← Complex.exp_add]
      push_cast
      simp
    rw [h6, hconst]
    congr 3
    ring
  exact this

end Scrn

end HRS
