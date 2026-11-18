import HRS.MS.Fp81S21WindowOrbitDecay
import HRS.MS.S104bNL8

/-! Common-radius moving adjoint and window feature inputs. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.R26T3
open HRS.MS.R2WinOrb HRS.MS.R2WinOrbNL HRS.MS.R2WinErr
open HRS.MS.R2GenInit HRS.MS.S104b

/-- The same radius supplies the adjoint input at every positive horizon and the
window feature membership at every nonnegative start. -/
theorem fp81s21_path_moving_adjoint_window (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        (∀ T : ℝ, 0 < T →
          OscAdjointInput (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) T) ∧
        (∀ H : ℝ, 0 < H → ∀ b : ℝ, 0 ≤ b →
          ∀ (a : Fin p.d) (r : ℝ), r ∈ Icc 0 (b + H) → ∀ x,
            S105WinK (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H b a r x) := by
  obtain ⟨δc, Co, co, hδc, hδch, hco, hcommon⟩ := fp81s21_common_radius p
  obtain ⟨δg, hδg, hδgh, hgrad⟩ := fp81s21_moving_orbit_gradient_decay p
  refine ⟨min δc δg, lt_min hδc hδg, (min_le_left _ _).trans hδch, ?_⟩
  intro δ hδ hδle R
  have hδc' : δ ≤ δc := hδle.trans (min_le_left _ _)
  have hδg' : δ ≤ δg := hδle.trans (min_le_right _ _)
  obtain ⟨-, -, hterm, -⟩ := hcommon δ hδ hδc' R.ρβ R.thermal
  obtain ⟨Cs0, cdec, hCs0, hcdec, hsum, hgradR⟩ := hgrad δ hδ hδg' R
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  obtain ⟨Cphi, hCphi0, hphi'⟩ := s104_hphi hd1
  let Cs : ℝ := max Cs0 Cphi
  have hCs : 0 ≤ Cs := hCphi0.trans (le_max_right _ _)
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := wholeSpaceIndex p.d
  let k : ℕ := 4 * p.d + 42
  have horb : ∀ α : MultiIndex p.d, ∀ T : ℝ, 0 ≤ T →
      S104nOrbit C (oscTestFun m α) T := by
    intro α T hT
    exact s104b_orbit_of_termRegGen hterm R.admissible R.resulting α T hT
  have hG : ∀ α : MultiIndex p.d,
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α)
        (Cs * s104_b p.d α) cdec) ∧
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t
        (generatorW C t (oscTestFun m α)) (Cs * s104_b p.d α) cdec) := by
    intro α
    have hle : Cs0 * s104_b p.d α ≤ Cs * s104_b p.d α :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (s104_b_nonneg α)
    exact ⟨fun t ht => s104_R2OrbitGrad_mono _ ((hgradR α).1 t ht) hle,
      fun t ht => s104_R2OrbitGrad_mono _ ((hgradR α).2 t ht) hle⟩
  have hφ : ∀ α a, ContDiff ℝ k (fun x => gradComp a (oscTestFun m α) x) ∧
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun m α) x) x‖ ≤
        Cs * s104_b p.d α := fun α a =>
    ⟨(hphi' α a).1, fun j hj x => ((hphi' α a).2 j hj x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (s104_b_nonneg α))⟩
  constructor
  · intro T hT
    refine ⟨fun r t hr hrt htT α a x => s104b_duhamel (horb α T hT.le) hr hrt htT a x, ?_⟩
    intro a r hr x
    have hmeas0 : ∀ α x, AEStronglyMeasurable (fun u => if r < 0 + u then
        gradComp a (propagatorW C r (0 + u)
          (generatorW C (0 + u) (oscTestFun m α))) x else 0)
        (volume.restrict (Icc (0 : ℝ) T)) :=
      fun α x => s104n_hobs (horb α T hT.le) hT.le le_rfl (by linarith) hr.1 a x
    obtain ⟨-, -, h3, h4⟩ := s105_winK C k m T cdec Cs hcdec.le hCs hsum
      (fun α => (hG α).1) (fun α => (hG α).2) hφ le_rfl hr.1 a hmeas0 x
    refine ⟨s105_memℓp_of_bound (K := Cs) (fun α => ?_) hsum, fun t ht => ?_, ?_⟩
    · have h := (hφ α a).2 0 (Nat.zero_le _) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    · have h := h3 t ⟨by linarith [hr.1, ht.1], ht.2⟩ (by simpa using ht.1)
      simpa only [zero_add] using h
    · simpa only [zero_add] using h4
  · intro H hH b hb a r hr x
    have hτ : 0 ≤ b + H := by linarith
    have hmeasU : ∀ α x, AEStronglyMeasurable (fun u => if r < b + u then
        gradComp a (propagatorW C r (b + u)
          (generatorW C (b + u) (oscTestFun m α))) x else 0)
        (volume.restrict (Icc (0 : ℝ) H)) :=
      fun α x => s104n_hobs (horb α (b + H) hτ) hH.le hb le_rfl hr.1 a x
    exact s105_winK C k m H cdec Cs hcdec.le hCs hsum (fun α => (hG α).1)
      (fun α => (hG α).2) hφ hb hr.1 a hmeasU x

#print axioms HRS.Fp81.S21.fp81s21_path_moving_adjoint_window

end HRS.Fp81.S21
