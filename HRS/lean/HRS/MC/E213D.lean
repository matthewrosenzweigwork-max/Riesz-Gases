import HRS.MC.E213A
import HRS.Sections.Q38bAux4
import HRS.Sections.Sec7Fields

/-!
# Packet E213D: stable evolution for `Vprop`, uniform in time (step C1 of the Theorem 2.13 scope)

`vprop_eq_vev`: `Vprop D ρ j t u` is the dual evolution `Vev t u` of any `IsDualEvolution D ρ j Vev`.
`vprop_stable_of_prepared`: `‖Vprop R.D R.ρ j t u F‖ ≤ C e^{-c(t-u)} ‖F‖` for `0 ≤ u ≤ t`, every real `j`.
-/

noncomputable section

open HRS HRS.Main HRS.Sec7 HRS.Uniform

namespace HRS.MC.E213D

variable {d : ℕ}

/-- A dual evolution reproduces `Vprop`. -/
theorem vprop_eq_vev (D : DynData d) (ρ : ℝ → Torus d → ℝ) (j : ℝ)
    (Vev : ℝ → ℝ → NegSobolev d j →L[ℝ] NegSobolev d j) (hdual : IsDualEvolution D ρ j Vev)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (F : NegSobolev d j) :
    Vprop D ρ j t u F = Vev t u F := by
  have hcoef : ∀ k : NonzeroLattice d,
      NegSobolev.eval F (propagator D ρ u t (Torus.realMode k)) =
        NegSobolev.fourierCoeff (Vev t u F) k := by
    intro k
    rw [← q38b_eval_realMode (Vev t u F) k]
    exact (hdual u t hu hut F _ (q38b_isSmooth_realMode k)).symm
  unfold Vprop
  simp_rw [hcoef]
  set G := Vev t u F with hG
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-j) * NegSobolev.fourierCoeff G k) 2 := by
    have h : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-j) * NegSobolev.fourierCoeff G k) =
        fun k => NegSobolev.coord G k := by
      funext k
      unfold NegSobolev.fourierCoeff
      rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
      simp
    rw [h]
    exact (show lp (fun _ : NonzeroLattice d => ℝ) 2 from G).2
  have := NegSobolev.ofSeq_of_mem (m := j) (NegSobolev.fourierCoeff G) hmem
  have e : (NegSobolev.ofSeq j (NegSobolev.fourierCoeff G) : lp (fun _ : NonzeroLattice d => ℝ) 2) =
      (G : lp (fun _ : NonzeroLattice d => ℝ) 2) := by
    rw [this]
    apply Subtype.ext
    funext k
    show Lattice.jp k.1 ^ (-j) * NegSobolev.fourierCoeff G k = NegSobolev.coord G k
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
    simp
  exact e

/-- **(C1)** Stable evolution for `Vprop`, uniform in time, at every real energy index `j`. -/
theorem vprop_stable_of_prepared (S : PreparedData d) (β₀ : ℝ) {m : ℝ}
    (hE : EdgeworthHyp S β₀ m) (j : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ F : NegSobolev d j,
      ‖Vprop (E213A.regimeOfPrepared S β₀ hE).D (E213A.regimeOfPrepared S β₀ hE).ρ j t u F‖ ≤
        C * Real.exp (-c * (t - u)) * ‖F‖ := by
  obtain ⟨Cr, cr, hC, hc, Vev, hdual, -, hdec, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd (E213A.isSmoothPositiveTrajectory_of_prepared S) j
  refine ⟨Cr, cr, hC, hc, fun u t hu hut F => ?_⟩
  have hdual' : IsDualEvolution (E213A.regimeOfPrepared S β₀ hE).D (E213A.regimeOfPrepared S β₀ hE).ρ j Vev :=
    hdual
  rw [vprop_eq_vev _ _ j Vev hdual' hu hut F]
  exact (Vev t u).le_of_opNorm_le (hdec u t hu hut) F

end HRS.MC.E213D

end
