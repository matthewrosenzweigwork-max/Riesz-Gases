import HRS.MS.S11Q3B2
import HRS.MS.S113EndAux22

/-!
# S11.3 / S11.4 (worker S11Q3), C1: joint continuity of the jets of `ρ_t = ρ_* + √ρ_* V_t` along a continuous path in `Σ^m`

`s11q3_rho_joint`: for `v` continuous on `[0,∞)` into `OscSpace d m` (`m > d/2 + 3`), the functions `(t,x) ↦ ρ_{v_t}(x)`, `D_xρ_{v_t}(x)`, `D²_xρ_{v_t}(x)`
are continuous on `[0,∞) × ℝ^d` (linearity of `u ↦ h_u` and its uniform bounds, `mne_joint_lin`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MS.Mov63

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ} {m : ℕ}

theorem s11q3_fderiv_sub {f g : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Euc d) :
    fderiv ℝ (fun y => f y - g y) x = fderiv ℝ f x - fderiv ℝ g x ∧
      fderiv ℝ (fderiv ℝ (fun y => f y - g y)) x = fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have h1 : fderiv ℝ (fun y => f y - g y) = fun y => fderiv ℝ f y - fderiv ℝ g y := by
    funext y
    exact ((hfd y).hasFDerivAt.sub (hgd y).hasFDerivAt).fderiv
  refine ⟨by rw [h1], ?_⟩
  have hf1 : Differentiable ℝ (fderiv ℝ f) := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg1 : Differentiable ℝ (fderiv ℝ g) := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [h1]
  exact ((hf1 x).hasFDerivAt.sub (hg1 x).hasFDerivAt).fderiv

theorem s11q3_fderiv_add {f g : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Euc d) :
    fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x ∧
      fderiv ℝ (fderiv ℝ (f + g)) x = fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have h1 : fderiv ℝ (f + g) = fun y => fderiv ℝ f y + fderiv ℝ g y := by
    funext y
    exact ((hfd y).hasFDerivAt.add (hgd y).hasFDerivAt).fderiv
  refine ⟨by rw [h1], ?_⟩
  have hf1 : Differentiable ℝ (fderiv ℝ f) := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg1 : Differentiable ℝ (fderiv ℝ g) := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [h1]
  exact ((hf1 x).hasFDerivAt.add (hg1 x).hasFDerivAt).fderiv

section Joint

variable (hm : (d : ℝ) / 2 + 3 < m) (H : Mov2dTh d s β q ρ₀)

include H in
theorem s11q3_hu_joint {S : Set ℝ} {v : ℝ → OscSpace d (m : ℝ)} (hv : ContinuousOn v S) :
    ContinuousOn (fun p : ℝ × Euc d => mnc_hu ρ₀ (mne_hn hm) (v p.1) p.2) (S ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (mnc_hu ρ₀ (mne_hn hm) (v p.1)) p.2) (S ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ (mnc_hu ρ₀ (mne_hn hm) (v p.1))) p.2) (S ×ˢ univ) := by
  obtain ⟨K, hK0, hK⟩ := mne_hu_iter hm H
  have hcd : ∀ u : OscSpace d (m : ℝ), ContDiff ℝ 3 (mnc_hu ρ₀ (mne_hn hm) u) := mne_hu_cd hm H
  have hcd2 : ∀ u : OscSpace d (m : ℝ), ContDiff ℝ 2 (mnc_hu ρ₀ (mne_hn hm) u) := fun u =>
    (hcd u).of_le (by norm_num)
  refine ⟨(mne_joint hm H hv).1, ?_, ?_⟩
  · refine mne_joint_lin (Ψ := fun u x => fderiv ℝ (mnc_hu ρ₀ (mne_hn hm) u) x) K ?_ ?_ ?_ hv
    · intro u u' x
      have := (s11q3_fderiv_sub (hcd2 u) (hcd2 u') x).1
      rw [mne_hu_sub hm u u']
      exact this.symm
    · intro u x
      have := hK u 1 (by norm_num) x
      rwa [norm_iteratedFDeriv_one] at this
    · intro u
      exact ((hcd u).fderiv_right (m := 2) (by norm_num)).continuous
  · refine mne_joint_lin (Ψ := fun u x => fderiv ℝ (fderiv ℝ (mnc_hu ρ₀ (mne_hn hm) u)) x) K ?_ ?_ ?_ hv
    · intro u u' x
      have := (s11q3_fderiv_sub (hcd2 u) (hcd2 u') x).2
      rw [mne_hu_sub hm u u']
      exact this.symm
    · intro u x
      have := hK u 2 (by norm_num) x
      rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
    · intro u
      exact ((hcd u).fderiv_right (m := 2) (by norm_num) |>.fderiv_right (m := 1) (by norm_num)).continuous

include H in
theorem s11q3_rho_joint {v : ℝ → OscSpace d (m : ℝ)} (hv : ContinuousOn v (Ici 0)) :
    ContinuousOn (fun p : ℝ × Euc d => mneRho ρ₀ hm (v p.1) p.2) (Ici 0 ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (mneRho ρ₀ hm (v p.1)) p.2) (Ici 0 ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ (mneRho ρ₀ hm (v p.1))) p.2) (Ici 0 ×ˢ univ) := by
  obtain ⟨h0, h1, h2⟩ := s11q3_hu_joint hm H hv
  have hρ : ContDiff ℝ 2 ρ₀ := ((mnc_rho_smooth H).of_le (by simp) : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) ρ₀)
  have hρ1 : Continuous (fderiv ℝ ρ₀) := hρ.continuous_fderiv (by norm_num)
  have hρ2 : Continuous (fderiv ℝ (fderiv ℝ ρ₀)) :=
    (hρ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hcd2 : ∀ u : OscSpace d (m : ℝ), ContDiff ℝ 2 (mnc_hu ρ₀ (mne_hn hm) u) := fun u =>
    (mne_hu_cd hm H u).of_le (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · exact (hρ.continuous.comp continuous_snd).continuousOn.add h0
  · refine ((hρ1.comp continuous_snd).continuousOn.add h1).congr fun p _ => ?_
    exact (s11q3_fderiv_add hρ (hcd2 (v p.1)) p.2).1
  · refine ((hρ2.comp continuous_snd).continuousOn.add h2).congr fun p _ => ?_
    exact (s11q3_fderiv_add hρ (hcd2 (v p.1)) p.2).2

end Joint

end HRS.MS.S11Q3

end
