import HRS.Sections.QuenchAux22
import HRS.Sections.QuenchAux20

/-!
# Packet QUENCH (Q27), part 23: window data of the OU field `Z` and the mode paths

`WinData` for `t ↦ Z^{a+t}` with diagonal coordinate covariance
`c_j(t,r) = ⟨j⟩^{-2m}(v_{β,j} e^{-λ_j|t-r|} + δv_j e^{-2λ_j a} e^{-λ_j (t+r)})`, and the identification
`modePath (modeFn k b) = sgn_b ⟨k⟩^{-m} • pathOf (e^{-λ t}) (idx k b)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

section WinZ

variable {s β β₀ m : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℝ → Ω → NegSobolev d m} {Y : Ω → NegSobolev d m}

/-- The diagonal coordinate covariance of the window `Z^{a+·}`. -/
def cwin (d : ℕ) (s β β₀ m a : ℝ) (j : NonzeroLattice d) (t r : ℝ) : ℝ :=
  Lattice.jp j.1 ^ (-(2 * m)) * (varMode d s β j.1 * Real.exp (-(lamMode d s β j.1) * |t - r|) +
    deltaVar d s β β₀ j.1 * Real.exp (-(lamMode d s β j.1) * (2 * a)) *
      Real.exp (-(lamMode d s β j.1) * (t + r)))

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

include hd hs0 hsd hβ in
theorem winData_Z (hβ₀ : 0 < β₀) (hm : (d : ℝ) / 2 + 1 < m) (mf : ModeField d s β β₀ m P Z Y)
    {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 < T) :
    WinData P m T (fun t ω => Z (a + t) ω) (cwin d s β β₀ m a) := by
  refine ⟨fun t => mf.meas (a + t), ?_, window_dom hd hs0 hsd hβ hβ₀ hm mf ha hT, ?_⟩
  · filter_upwards [mf.cont] with ω h
    have h1 : ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)) := h (a + T)
    refine h1.comp (continuousOn_const.add continuousOn_id) fun t ht => ?_
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht r hr j j'
    have h1 : ∀ ω, NegSobolev.coord (Z (a + t) ω) j * NegSobolev.coord (Z (a + r) ω) j' =
        Lattice.jp j.1 ^ (-m) * Lattice.jp j'.1 ^ (-m) *
          (NegSobolev.fourierCoeff (Z (a + t) ω) j * NegSobolev.fourierCoeff (Z (a + r) ω) j') := by
      intro ω; rw [coord_eq_fc, coord_eq_fc]; ring
    simp_rw [h1]
    rw [integral_const_mul, Z_cov hd hs0 hsd hβ mf j j' (by linarith [ht.1]) (by linarith [hr.1])]
    by_cases hj : j = j'
    · subst hj
      simp only [if_true, cwin]
      have e1 : (a + t) - (a + r) = t - r := by ring
      have e2 : Real.exp (-(lamMode d s β j.1) * ((a + t) + (a + r))) =
          Real.exp (-(lamMode d s β j.1) * (2 * a)) * Real.exp (-(lamMode d s β j.1) * (t + r)) := by
        rw [← Real.exp_add]; congr 1; ring
      have e3 : Lattice.jp j.1 ^ (-m) * Lattice.jp j.1 ^ (-m) = Lattice.jp j.1 ^ (-(2 * m)) := by
        rw [← Real.rpow_add (Torus.jp_pos _)]; congr 1; ring
      rw [e1, e2, e3]; ring
    · simp [hj]

end WinZ

end Qch

end HRS
