import HRS.Commutator.Torus.TPOSAux14

/-!
# T-POS helpers, part 15: `g_η^𝕋` equals its Fourier series; `g_η^𝕋(0)` is the local value
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

lemma tpos_local_data (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 → periodicRiesz d s (Torus.mk x) =
        (if s = 0 then -Real.log ‖x‖ else ‖x‖ ^ (-s)) + r (Torus.mk x) := by
  have hd0 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases hs : s = 0
  · subst hs
    obtain ⟨r, δ, hδ, hr, h⟩ := periodicLog_local_singularity (d := d) (by omega)
    exact ⟨r, δ, hδ, hr, fun x hx hx0 => by simpa using h x hx hx0⟩
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨r, δ, hδ, hr, h⟩ := periodicRiesz_local_singularity (d := d) (s := s) (by omega) hs'
      (by linarith)
    exact ⟨r, δ, hδ, hr, fun x hx hx0 => by simpa [hs] using h x hx hx0⟩

lemma tpos_fcoef_eq_funFourier (u : Torus d → ℝ) (k : Lattice d) :
    Torus.fcoef u k = Torus.funFourierCoeff (fun x => ((u x : ℝ) : ℂ)) k := by
  rw [PDE.funFourierCoeff_eq_int]
  rfl

theorem tpos_gTorus_eq (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    (r : Torus d → ℝ) (δ : ℝ) (hδ : 0 < δ) (hr : Torus.IsSmooth r)
    (hsing : ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 → periodicRiesz d s (Torus.mk x) =
      (if s = 0 then -Real.log ‖x‖ else ‖x‖ ^ (-s)) + r (Torus.mk x)) :
    gTorus s η = tposH d s η ∧ gTorus0 d s η = tposGloc s η r 0 := by
  classical
  have hsum := tpos_gTcoef_summable (d := d) hs0 hsd hη
  have hGc : Continuous (tposGstar s η r) :=
    Torus.continuous_of_continuous_lift (tpos_Gstar_lift_continuous hd hs0 hsd hη r δ hδ hr hsing)
  have hHc : Continuous (tposH d s η) := tposH_continuous hsum
  have hae : (tposGstar s η r : Torus d → ℝ) =ᵐ[volume] (gTorus s η : Torus d → ℝ) := by
    filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with x hx
    simp [tposGstar, hx]
  have hcoefG : ∀ k : Lattice d, Torus.fcoef (tposGstar s η r : Torus d → ℝ) k =
      ((gTcoef d s η k : ℝ) : ℂ) := by
    intro k
    rw [← tpos_fcoef_gTorus hd hs0 hsd hη k]
    unfold Torus.fcoef
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have heq : tposGstar s η r = tposH d s η := by
    refine PDE.MFAux.eq_of_funFourierCoeff_eq hGc hHc (fun k => ?_)
    rw [← tpos_fcoef_eq_funFourier, ← tpos_fcoef_eq_funFourier, hcoefG, tposH_fcoef hsum]
  have h0 : gTorus0 d s η = tposGloc s η r 0 := by
    have h1 := congrFun heq 0
    simp only [tposGstar, if_true] at h1
    rw [h1, tposH_zero hsum]
  refine ⟨?_, h0⟩
  funext x
  by_cases hx : x = 0
  · subst hx
    rw [tposH_zero hsum]
    simp [gTorus]
  · have h1 := congrFun heq x
    simp only [tposGstar, if_neg hx] at h1
    exact h1

end HRS.Commutator.TorusNote
