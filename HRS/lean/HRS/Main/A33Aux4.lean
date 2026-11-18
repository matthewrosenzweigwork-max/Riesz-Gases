import Mathlib
import HRS.Main.A33Aux3

/-!
# Packet A33, helper 4: uniform bounds for the propagator and joint continuity of the density path
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

/-- Uniform bounds: the `H^J` bound of the propagator and the `C^1` bound by the `H^{m_*}` norm
of the datum. -/
theorem a33_bounds (hd : 1 ≤ d) (J : ℕ) (hJ : mStar d ≤ J) (R : Regime) (MB Λ VB : ℝ)
    (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData D.s J R MB Λ VB D ν₀ T μ) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ t ∈ Set.Ioc 0 T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ∀ r ∈ Set.Icc 0 t,
        MemSobolev (J : ℝ) (propagator D μ r t φ) ∧
        sobolevNorm (J : ℝ) (propagator D μ r t φ) ≤ K₁ * sobolevNorm (J : ℝ) φ ∧
        ∀ x : Torus d, ‖Torus.grad (propagator D μ r t φ) x‖ ≤ K₂ * sobolevNorm (mStar d : ℝ) φ := by
  obtain ⟨C, Cs, hC, hCs, hmain⟩ := adjoint_torus_classical hd D.s D.hs0 D.hsd J hJ R MB Λ VB
  set l1 := R.lambdaM (Cs J) ν₀ (thetaOrder d D.s) with hl1
  set l2 := R.lambdaM (Cs (mStar d)) ν₀ (thetaOrder d D.s) with hl2
  have hT : 0 < T := hA.hT
  have hJ3 := ClassicalPart.three_le_mStar d
  have hJ1 : 1 ≤ J := by omega
  refine ⟨Real.exp (|l1| * T), C * Real.exp (|l2| * T), (Real.exp_pos _).le,
    mul_nonneg hC.le (Real.exp_pos _).le, fun t ht φ hφ r hr => ?_⟩
  obtain ⟨hcl, hpe, h3, h4⟩ := hmain D ν₀ T μ hA t ht φ (a33_cont hφ) (a33_memSob (J : ℝ) hφ)
  have htr : t - r ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩
  have hexp : ∀ l : ℝ, Real.exp (l * (t - r)) ≤ Real.exp (|l| * T) := fun l =>
    Real.exp_le_exp.2 (by
      calc l * (t - r) ≤ |l| * (t - r) := mul_le_mul_of_nonneg_right (le_abs_self l) htr.1
        _ ≤ |l| * T := mul_le_mul_of_nonneg_left htr.2 (abs_nonneg l))
  obtain ⟨hm, hb⟩ := h3 J hJ1 le_rfl r hr
  refine ⟨hm, hb.trans (mul_le_mul_of_nonneg_right (hexp l1) (Real.sqrt_nonneg _)), fun x => ?_⟩
  have hCk : Torus.IsCk 2 (propagator D μ r t φ) := by rw [hpe r hr]; exact hcl.c2 r hr
  have h1 : ‖Torus.grad (propagator D μ r t φ) x‖ ≤ Torus.cbNorm 2 (propagator D μ r t φ) := by
    have := norm_iteratedFDeriv_le_cbNorm (k := 2) (j := 1) (by norm_num) hCk (Torus.rep x)
    rw [norm_iteratedFDeriv_one] at this
    unfold Torus.grad
    rw [gradient]
    simpa using this
  refine h1.trans ((h4 r hr).trans ?_)
  have h0 : 0 ≤ sobolevNorm (mStar d : ℝ) φ := Real.sqrt_nonneg _
  calc C * Real.exp (l2 * (t - r)) * sobolevNorm (mStar d : ℝ) φ
      ≤ C * Real.exp (|l2| * T) * sobolevNorm (mStar d : ℝ) φ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp l2) hC.le) h0
    _ = _ := by ring

/-- Joint continuity of the density path `(r, x) ↦ ρ r x` on `[0,T] × 𝕋^d` (from the weak
continuity in `r` and the `C^{m+3}` bounds, via `ℓ¹`-continuity of the Fourier coefficients). -/
theorem a33_rho_cont {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Torus d → ℝ} (hμ : CoeffHyp m Λ T ρ)
    (hmd : (d : ℝ) / 2 < m) (hT : 0 < T) :
    ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) := by
  obtain ⟨⟨K, hK⟩, hconv⟩ := ClassicalPart.density_path_ws1 hμ hmd (t := T) ⟨hT, le_rfl⟩
  have hmem : ∀ r : Set.Icc (0 : ℝ) T, T - r.1 ∈ Set.Icc (0 : ℝ) T := fun r =>
    ⟨by linarith [r.2.2], by linarith [r.2.1]⟩
  set g : Set.Icc (0 : ℝ) T → Coeff d := fun r => coeffOf (ρ r.1) with hg
  have hWS1 : ∀ r : Set.Icc (0 : ℝ) T, ClassicalPart.WS 1 (g r) := by
    intro r
    have := (hK (T - r.1) (hmem r)).1
    simpa [hg] using this
  have hWS0 : ∀ r : Set.Icc (0 : ℝ) T, ClassicalPart.WS 0 (g r) := fun r =>
    (hWS1 r).mono (by norm_num)
  have hc : ∀ r₀ : Set.Icc (0 : ℝ) T,
      Tendsto (fun r => ClassicalPart.WN 0 (g r - g r₀)) (𝓝 r₀) (𝓝 0) := by
    intro r₀
    have h1 := hconv (T - r₀.1) (hmem r₀)
    have h2 : Tendsto (fun r : Set.Icc (0 : ℝ) T => T - r.1) (𝓝 r₀)
        (𝓝[Set.Icc (0 : ℝ) T] (T - r₀.1)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hmem⟩
      exact (continuous_const.sub continuous_subtype_val).tendsto r₀
    have h3 := h1.comp h2
    refine squeeze_zero (fun r => ClassicalPart.WN_nonneg _ _) (fun r => ?_) h3
    have e1 : coeffOf (ρ (T - (T - r.1))) = g r := by simp [hg]
    have e2 : coeffOf (ρ (T - (T - r₀.1))) = g r₀ := by simp [hg]
    simp only [Function.comp, e1, e2]
    exact ClassicalPart.WN_mono (by norm_num) ((hWS1 r).sub (hWS1 r₀))
  have hcont := ClassicalPart.continuous_toFun_family g hWS0 hc
  have hρ : ∀ (r : Set.Icc (0 : ℝ) T) (x : Torus d), toFun (g r) x = ρ r.1 x := by
    intro r x
    have hρc : Continuous (ρ r.1) :=
      ClassicalAux.continuous_of_isCk (ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3)) (hμ.smooth r.1 r.2))
    have hs : Summable fun k => ‖coeffOf (ρ r.1) k‖ := (ClassicalPart.WS_zero_iff _).1 (hWS0 r)
    exact congrFun (toFun_coeffOf (ρ r.1) hρc hs) x
  have hcont' : Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => ρ p.1.1 p.2 := by
    refine hcont.congr fun p => ?_
    exact hρ p.1 p.2
  rw [continuousOn_iff_continuous_domRestrict]
  have : (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Torus d))).domRestrict (fun p : ℝ × Torus d => ρ p.1 p.2)
      = (fun p : Set.Icc (0 : ℝ) T × Torus d => ρ p.1.1 p.2) ∘
        (fun p : ↥(Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Torus d))) =>
          ((⟨p.1.1, p.2.1⟩ : Set.Icc (0 : ℝ) T), p.1.2)) := rfl
  rw [this]
  refine hcont'.comp ?_
  exact (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _).prodMk
    (continuous_snd.comp continuous_subtype_val)

end HRS.A33
