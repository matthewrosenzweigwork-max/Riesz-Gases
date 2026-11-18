import HRS.MS.SA12DE7F

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part G: real `C_c^∞` weak derivatives are `WD`

`sa12de7_WD_of_cc`: if `f, g ∈ L²(ℝ^d; ℝ)` satisfy `∫ g ψ = -∫ f ∂_iψ` for every real `C_c^∞` test function `ψ`, then the
repository's weak-derivative relation `WD i f g` (complex Schwartz tests, `∂_i` as the Schwartz line derivative) holds for the
complex casts.  (Part F extends the identity to smooth `L²` tests; the real and imaginary parts of a Schwartz function are
such tests.)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Limit HRS.Whole.AppendixA HRS.Whole.Q09A

variable {d : ℕ}

open LineDeriv in
theorem sa12de7_WD_of_cc {f g : Euc d → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (i : Fin d)
    (h : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      ∫ x, g x * ψ x = -∫ x, f x * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) :
    WD i (fun x => ((f x : ℝ) : ℂ)) (fun x => ((g x : ℝ) : ℂ)) := by
  refine ⟨hf.ofReal (K := ℂ), hg.ofReal (K := ℂ), fun ψ => ?_⟩
  set Dψ : SchwartzMap (Euc d) ℂ := ∂_{(EuclideanSpace.single i (1 : ℝ) : Euc d)} ψ with hDψ
  have hDapp : ∀ x, Dψ x = fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ) : Euc d) := fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv _ ψ x
  have hψ2 : MemLp (fun x => ψ x) 2 volume := ψ.memLp 2 volume
  have hDψ2 : MemLp (fun x => Dψ x) 2 volume := Dψ.memLp 2 volume
  have hψs : ContDiff ℝ ∞ ψ := ψ.smooth ⊤
  -- real and imaginary parts
  have hre : ∀ x, HasFDerivAt (fun y => (ψ y).re) (Complex.reCLM.comp (fderiv ℝ ψ x)) x := fun x =>
    Complex.reCLM.hasFDerivAt.comp x (ψ.hasFDerivAt x)
  have him : ∀ x, HasFDerivAt (fun y => (ψ y).im) (Complex.imCLM.comp (fderiv ℝ ψ x)) x := fun x =>
    Complex.imCLM.hasFDerivAt.comp x (ψ.hasFDerivAt x)
  have hdre : ∀ x, fderiv ℝ (fun y => (ψ y).re) x (EuclideanSpace.single i (1 : ℝ) : Euc d) = (Dψ x).re := fun x => by
    rw [(hre x).fderiv, hDapp]; rfl
  have hdim : ∀ x, fderiv ℝ (fun y => (ψ y).im) x (EuclideanSpace.single i (1 : ℝ) : Euc d) = (Dψ x).im := fun x => by
    rw [(him x).fderiv, hDapp]; rfl
  have hsre : ContDiff ℝ ∞ (fun y => (ψ y).re) := Complex.reCLM.contDiff.comp hψs
  have hsim : ContDiff ℝ ∞ (fun y => (ψ y).im) := Complex.imCLM.contDiff.comp hψs
  have hm1 : MemLp (fun x => fderiv ℝ (fun y => (ψ y).re) x (EuclideanSpace.single i (1 : ℝ) : Euc d)) 2 volume := by
    have : (fun x => fderiv ℝ (fun y => (ψ y).re) x (EuclideanSpace.single i (1 : ℝ) : Euc d)) = fun x => (Dψ x).re := funext hdre
    rw [this]; exact hDψ2.re
  have hm2 : MemLp (fun x => fderiv ℝ (fun y => (ψ y).im) x (EuclideanSpace.single i (1 : ℝ) : Euc d)) 2 volume := by
    have : (fun x => fderiv ℝ (fun y => (ψ y).im) x (EuclideanSpace.single i (1 : ℝ) : Euc d)) = fun x => (Dψ x).im := funext hdim
    rw [this]; exact hDψ2.im
  have h1 := sa12de7_ibp_extend hf hg i h hsre (hψ2.re) hm1
  have h2 := sa12de7_ibp_extend hf hg i h hsim (hψ2.im) hm2
  simp only [hdre, hdim] at h1 h2
  -- integrability of the complex integrands
  have hI1 : Integrable (fun x => ((g x : ℝ) : ℂ) * ψ x) volume := (hg.ofReal (K := ℂ)).integrable_mul hψ2
  have hI2 : Integrable (fun x => ((f x : ℝ) : ℂ) * Dψ x) volume := (hf.ofReal (K := ℂ)).integrable_mul hDψ2
  change ∫ x, ((g x : ℝ) : ℂ) * ψ x = -∫ x, ((f x : ℝ) : ℂ) * Dψ x
  apply Complex.ext
  · have e1 : (∫ x, ((g x : ℝ) : ℂ) * ψ x).re = ∫ x, g x * (ψ x).re := by
      simpa using (integral_re hI1).symm
    have e2 : (∫ x, ((f x : ℝ) : ℂ) * Dψ x).re = ∫ x, f x * (Dψ x).re := by
      simpa using (integral_re hI2).symm
    rw [Complex.neg_re, e1, e2, h1]
  · have e1 : (∫ x, ((g x : ℝ) : ℂ) * ψ x).im = ∫ x, g x * (ψ x).im := by
      simpa using (integral_im hI1).symm
    have e2 : (∫ x, ((f x : ℝ) : ℂ) * Dψ x).im = ∫ x, f x * (Dψ x).im := by
      simpa using (integral_im hI2).symm
    rw [Complex.neg_im, e1, e2, h2]

end HRS.MS.SA12DE7
