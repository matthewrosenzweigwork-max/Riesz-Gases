import HRS.MS.Fp81S21ShiftedMild
import HRS.MS.R2GenInitAux24

/-!
# HRS S2.1(iii), packet 9c: deterministic shifted noise feature

The compiled window feature used here is `HRS.Whole.r2WindowFeature`.  In
`HRS/Whole/Window.lean` it is, verbatim, `KSpace.mk base (if h : MemLp f 2
(volume.restrict (Icc 0 T)) then h.toLp f else 0) terminal`, where

* `base = ellVec m (fun α => Dop (propagatorW C r (max b r)
  (oscTestFun m α)) x)`;
* `f u = if r < b + u then ellVec m (fun α => Dop
  (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x)
  else 0`;
* `terminal = if b ≤ r then ellVec m (fun α => Dop (oscTestFun m α) x)
  else 0`.

The shifted feature is exactly this compiled feature at physical noise time
`r = b + u`.  Thus its base and terminal oscillator coordinates are
`∇φ_α(x)`, and its middle component is
`v ↦ 1_{u < v} ∇U^{b+u,b+v}(L_{b+v}φ_α)(x)`.

The compiled `s105_ident` contract in `R2GenInitAux24.lean` reconstructs the
Itô integral over physical times `[0,b+u]`.  It is not by itself the shifted
noise: the desired `[b,b+u]` integral is obtained only after subtracting the
reconstruction at local time zero (or after truncating the integrand to the
shifted interval).  No martingale maximal inequality is applied here.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2GenInit HRS.MS.S52
open HRS.MS.R26T3

/-- The shifted feature at local noise time `u` is the existing window feature
at physical time `b + u`. -/
def fp81s21_shiftedNoiseFeature
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (H b u : ℝ) (a : Fin p.d) (x : Euc p.d) :
    KSpace p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H :=
  r2WindowFeature (r26t3_coeff R) ((wholeSpaceIndex p.d : ℕ) : ℝ)
    H (gradComp a) b (b + u) x

/-- The shifted feature's terminal block is the oscillator gradient.  The
`S105WinK` premise is precisely the existing no-junk-values contract needed
to identify the `KSpace` representative. -/
theorem fp81s21_shiftedNoiseFeature_y2
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {H b u : ℝ} (hb : 0 ≤ b) (hu : u ∈ Icc (0 : ℝ) H)
    (a : Fin p.d) (x : Euc p.d) (α : MultiIndex p.d)
    (hK : S105WinK (r26t3_coeff R) ((wholeSpaceIndex p.d : ℕ) : ℝ)
      H b a (b + u) x) :
    inner ℝ (fp81s21_shiftedNoiseFeature p R H b u a x)
        (s52y2 ((wholeSpaceIndex p.d : ℕ) : ℝ) H α) =
      gradComp a (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α) x := by
  have hbu : b ≤ b + u := by linarith [hu.1]
  rcases hK with ⟨hA, hB, hmemℓ, hmem⟩
  have hpair := s105_pair_y2 (r26t3_coeff R)
    ((wholeSpaceIndex p.d : ℕ) : ℝ) H b (b + u) a x hA hB hmem α
  simpa [fp81s21_shiftedNoiseFeature, hbu] using hpair

/-- Pairing the shifted feature with the reconstruction vector at local time
`s` gives the propagated gradient until the physical noise time reaches the
terminal time, and the unpropagated gradient afterwards. -/
theorem fp81s21_shiftedNoiseFeature_y1
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {H b u s : ℝ} (hb : 0 ≤ b)
    (hu : u ∈ Icc (0 : ℝ) H) (hs : s ∈ Icc (0 : ℝ) H)
    (hC : OscAdjointInput (r26t3_coeff R)
      ((wholeSpaceIndex p.d : ℕ) : ℝ) (b + H))
    (a : Fin p.d) (x : Euc p.d) (α : MultiIndex p.d)
    (hK : S105WinK (r26t3_coeff R) ((wholeSpaceIndex p.d : ℕ) : ℝ)
      H b a (b + u) x) :
    inner ℝ (fp81s21_shiftedNoiseFeature p R H b u a x)
        (s52y1 ((wholeSpaceIndex p.d : ℕ) : ℝ) H s α) =
      if u ≤ s then
        gradComp a (propagatorW (r26t3_coeff R) (b + u) (b + s)
          (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α)) x
      else gradComp a (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α) x := by
  have hbu0 : 0 ≤ b + u := by linarith [hu.1]
  have hbuH : b + u ≤ b + H := by linarith [hu.2]
  rcases hK with ⟨hA, hB, hmemℓ, hmem⟩
  have hpair := s105_pair_y1 (r26t3_coeff R)
    (m := ((wholeSpaceIndex p.d : ℕ) : ℝ)) (T := H) (b := b) (r := b + u)
    hC hb hbu0 hbuH hs a x hA hmemℓ hmem α
  have hshift : (b + u ≤ b + s) = (u ≤ s) :=
    propext (add_le_add_iff_left b)
  simpa [fp81s21_shiftedNoiseFeature, hshift] using hpair

#print axioms HRS.Fp81.S21.fp81s21_shiftedNoiseFeature_y2
#print axioms HRS.Fp81.S21.fp81s21_shiftedNoiseFeature_y1

end HRS.Fp81.S21

end
