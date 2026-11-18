import HRS.MS.Fp81S21QwinDecay2
import HRS.MS.Fp81S21WindowFeature7

/-!
# HRS S2.1(iii), SOL26 packet 27c: decay of the propagated terminal jets

This converts the moving first-datum and second-terminal gradient-orbit bounds
into pointwise scalar derivative bounds at physical time zero.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.R2WinOrb
open HRS.MS.R2WinOrbNL
open HRS.MS.R2WinErr

private theorem fp81s21_qwin_scalar_jet_of_orbit
    {d : ℕ} {C : WholeCoeff d} {t A c : ℝ}
    {g : Euc d → ℝ} {α : MultiIndex d} {k : ℕ} {x : Euc d}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hk : 1 ≤ k)
    (hkJ : k ≤ 4 * d + 40)
    (hOrbit : R2OrbitGrad C (4 * d + 42) t g
      (A * s103_b d α) c)
    (hClass : IsClassicalAdjointW C t g
      (fun r => propagatorW C r t g)) :
    ‖iteratedFDeriv ℝ k (propagatorW C 0 t g) x‖ ≤
      ((4 * d + 42 : ℕ) + 1 : ℝ) * A * Real.exp (-c * t) * s103_b d α := by
  have hr : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have hAmp : 0 ≤ A * s103_b d α := mul_nonneg hA (s103_b_nonneg α)
  obtain ⟨hgrad, hvec⟩ :=
    HRS.MS.R2WinErr.s104_vec_bound C hAmp hOrbit hr
  let X : ℝ := A * s103_b d α * Real.exp (-c * t)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  let Xcb : ℝ := ((4 * d + 42 : ℕ) + 1 : ℝ) * X
  have hXcb : 0 ≤ Xcb := by dsimp [Xcb]; positivity
  have hpoint : ∀ j ≤ 4 * d + 42, ∀ y,
      ‖iteratedFDeriv ℝ j (fun z => gradient (propagatorW C 0 t g) z) y‖ ≤ X := by
    intro j hj y
    have h := hvec j hj y
    simpa [X, sub_zero, mul_assoc] using h
  have hcb := HRS.MS.Mov63.mng_cbVecE_le hX hpoint
  have hg : ContDiff ℝ 1 (propagatorW C 0 t g) :=
    (hClass.c2 0 hr).of_le (by norm_num)
  obtain ⟨_, hjet⟩ := fp81s21_scalar_pos_deriv_of_gradient_cb
    hg hgrad hcb hXcb hk (by omega : k ≤ (4 * d + 42) + 1)
  calc
    ‖iteratedFDeriv ℝ k (propagatorW C 0 t g) x‖ ≤
        Xcb := hjet x
    _ = ((4 * d + 42 : ℕ) + 1 : ℝ) * A *
        Real.exp (-c * t) * s103_b d α := by
          dsimp [Xcb, X]
          ring

theorem fp81s21_qwin_terminal_jet_decay (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧
          ∀ α : MultiIndex p.d, ∀ t : ℝ, 0 ≤ t →
            ∀ k : ℕ, 1 ≤ k → k ≤ 4 * p.d + 40 → ∀ x : Euc p.d,
              ‖iteratedFDeriv ℝ k
                (propagatorW (r26t3_coeff R) 0 t
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ ≤
                  C * Real.exp (-c * t) * s103_b p.d α ∧
              ‖iteratedFDeriv ℝ k
                (propagatorW (r26t3_coeff R) 0 t
                  (generatorW (r26t3_coeff R) t
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x‖ ≤
                  C * Real.exp (-c * t) * s103_b p.d α ∧
              ‖iteratedFDeriv ℝ k
                (propagatorW (r26t3_coeff R) 0 t
                  (s103nData (r26t3_coeff R)
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α) 2 t)) x‖ ≤
                  C * Real.exp (-c * t) * s103_b p.d α := by
  obtain ⟨δr, _, _, hδr, hδrhalf, _, hcommon⟩ := fp81s21_common_radius p
  obtain ⟨δm, hδm, hδmhalf, hmoving⟩ :=
    fp81s21_moving_orbit_gradient_decay p
  obtain ⟨δs, hδs, hδshalf, hsecond⟩ :=
    fp81s21_second_terminal_grad p
  let δ0 : ℝ := min δr (min δm δs)
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min hδr (lt_min hδm hδs)
  have hδ0half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hδrhalf
  refine ⟨δ0, hδ0, hδ0half, fun δ hδ hδle R => ?_⟩
  have hδr : δ ≤ δr := hδle.trans (min_le_left _ _)
  have hδm' : δ ≤ δm := hδle.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδs' : δ ≤ δs := hδle.trans
    ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Cs, cm, hCs, hcm, _, hmove⟩ := hmoving δ hδ hδm' R
  obtain ⟨As, hAs, cs, hcs, hsec⟩ := hsecond δ hδ hδs' R
  obtain ⟨hOrbit, _, hterm, _⟩ := hcommon δ hδ hδr R.ρβ R.thermal
  let c : ℝ := min cm cs
  have hc : 0 < c := by dsimp [c]; exact lt_min hcm hcs
  let M : ℝ := max Cs As
  have hM : 0 ≤ M := le_trans hAs (le_max_right _ _)
  let K : ℝ := ((4 * p.d + 42 : ℕ) + 1 : ℝ) * M
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, c, hc, ?_⟩
  intro α t ht k hk hkJ x
  let C := r26t3_coeff R
  let φ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  have hclass (i : Fin 3) :
      IsClassicalAdjointW C t (s103nData C φ i t)
        (fun r => propagatorW C r t (s103nData C φ i t)) := by
    have hex := hterm R.ε R.ψ R.ρ R.admissible R.resulting α t ht
    exact HRS.MS.Fcau.propagatorW_isClassical
      (hex.1 i t ⟨ht, le_rfl⟩)
  obtain ⟨hg0, hg1⟩ := hmove α
  have hOrbit0 : R2OrbitGrad C (4 * p.d + 42) t φ
      (Cs * s103_b p.d α) c := by
    have hraw := hg0 t ht
    have hraw' : R2OrbitGrad C (4 * p.d + 42) t φ
        (Cs * s103_b p.d α) cm := by
      simpa [C, φ, r26t3_coeff, wholeSpaceIndex, s104_b, s103_b] using hraw
    exact s103n_orbitGrad_mono_c hraw' (by dsimp [c]; exact min_le_left _ _)
      (mul_nonneg hCs (s103_b_nonneg α))
  have hOrbit1 : R2OrbitGrad C (4 * p.d + 42) t
      (generatorW C t φ) (Cs * s103_b p.d α) c := by
    have hraw := hg1 t ht
    have hraw' : R2OrbitGrad C (4 * p.d + 42) t
        (generatorW C t φ) (Cs * s103_b p.d α) cm := by
      simpa [C, φ, r26t3_coeff, wholeSpaceIndex, s104_b, s103_b] using hraw
    exact s103n_orbitGrad_mono_c hraw' (by dsimp [c]; exact min_le_left _ _)
      (mul_nonneg hCs (s103_b_nonneg α))
  have hOrbit2 : R2OrbitGrad C (4 * p.d + 42) t
      (s103nData C φ 2 t) (As * s103_b p.d α) c := by
    have hraw := hsec α t ht
    exact s103n_orbitGrad_mono_c hraw (by dsimp [c]; exact min_le_right _ _)
      (mul_nonneg hAs (s103_b_nonneg α))
  have hclass0 : IsClassicalAdjointW C t φ
      (fun r => propagatorW C r t φ) := by
    simpa [s103nData, φ] using hclass ⟨0, by norm_num⟩
  have hclass1 : IsClassicalAdjointW C t (generatorW C t φ)
      (fun r => propagatorW C r t (generatorW C t φ)) := by
    simpa [s103nData, φ] using hclass ⟨1, by norm_num⟩
  have hclass2 : IsClassicalAdjointW C t (s103nData C φ 2 t)
      (fun r => propagatorW C r t (s103nData C φ 2 t)) := by
    exact hclass ⟨2, by norm_num⟩
  have hjet0 := fp81s21_qwin_scalar_jet_of_orbit
    (d := p.d) (C := C) (t := t) (A := Cs) (c := c) (g := φ)
    (α := α) (k := k) (x := x) hCs ht hk hkJ hOrbit0 hclass0
  have hjet1 := fp81s21_qwin_scalar_jet_of_orbit
    (d := p.d) (C := C) (t := t) (A := Cs) (c := c)
    (g := generatorW C t φ) (α := α) (k := k) (x := x)
    hCs ht hk hkJ hOrbit1 hclass1
  have hjet2 := fp81s21_qwin_scalar_jet_of_orbit
    (d := p.d) (C := C) (t := t) (A := As) (c := c)
    (g := s103nData C φ 2 t) (α := α) (k := k) (x := x)
    hAs ht hk hkJ hOrbit2 hclass2
  have hweight : 0 ≤ s103_b p.d α := s103_b_nonneg α
  have hexp : 0 ≤ Real.exp (-c * t) := (Real.exp_pos _).le
  have hfac : 0 ≤ Real.exp (-c * t) * s103_b p.d α := mul_nonneg hexp hweight
  have hcoeffS : ((4 * p.d + 42 : ℕ) + 1 : ℝ) * Cs ≤ K := by
    dsimp [K, M]
    exact mul_le_mul_of_nonneg_left (le_max_left Cs As) (by positivity)
  have hcoeffA : ((4 * p.d + 42 : ℕ) + 1 : ℝ) * As ≤ K := by
    dsimp [K, M]
    exact mul_le_mul_of_nonneg_left (le_max_right Cs As) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · calc
      ‖iteratedFDeriv ℝ k (propagatorW C 0 t φ) x‖ ≤
          ((4 * p.d + 42 : ℕ) + 1 : ℝ) * Cs * Real.exp (-c * t) * s103_b p.d α := hjet0
      _ = (((4 * p.d + 42 : ℕ) + 1 : ℝ) * Cs) *
          (Real.exp (-c * t) * s103_b p.d α) := by ring
      _ ≤ K * (Real.exp (-c * t) * s103_b p.d α) :=
        mul_le_mul_of_nonneg_right hcoeffS hfac
      _ = K * Real.exp (-c * t) * s103_b p.d α := by ring
  · calc
      ‖iteratedFDeriv ℝ k (propagatorW C 0 t (generatorW C t φ)) x‖ ≤
          ((4 * p.d + 42 : ℕ) + 1 : ℝ) * Cs * Real.exp (-c * t) * s103_b p.d α := hjet1
      _ = (((4 * p.d + 42 : ℕ) + 1 : ℝ) * Cs) *
          (Real.exp (-c * t) * s103_b p.d α) := by ring
      _ ≤ K * (Real.exp (-c * t) * s103_b p.d α) :=
        mul_le_mul_of_nonneg_right hcoeffS hfac
      _ = K * Real.exp (-c * t) * s103_b p.d α := by ring
  · calc
      ‖iteratedFDeriv ℝ k (propagatorW C 0 t (s103nData C φ 2 t)) x‖ ≤
          ((4 * p.d + 42 : ℕ) + 1 : ℝ) * As * Real.exp (-c * t) * s103_b p.d α := hjet2
      _ = (((4 * p.d + 42 : ℕ) + 1 : ℝ) * As) *
          (Real.exp (-c * t) * s103_b p.d α) := by ring
      _ ≤ K * (Real.exp (-c * t) * s103_b p.d α) :=
        mul_le_mul_of_nonneg_right hcoeffA hfac
      _ = K * Real.exp (-c * t) * s103_b p.d α := by ring

#print axioms fp81s21_qwin_terminal_jet_decay

end HRS.Fp81.S21

end
