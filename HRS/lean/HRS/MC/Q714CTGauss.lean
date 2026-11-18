import HRS.MC.Q714CTAux
import HRS.MC.Q714CTForm

/-!
# Packet 7.14 CT (Gauss): the time-zero coordinate of a window is a centred Gaussian
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.CT

open HRS HRS.Sec7 HRS.Qch

variable {d : ℕ} {m T : ℝ} {s β β₀ : ℝ}

/-- On a path-continuous sample, `ℓ_j` of the window is the coordinate of `Z^a`. -/
theorem ct_ell_procWin (hT : 0 < T) (j : NonzeroLattice d) {Ω : Type} (Z : ℝ → Ω → NegSobolev d m)
    {a : ℝ} (ha : 0 ≤ a) {ω : Ω} (hω : ∀ T' : ℝ, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T')) :
    ell hT j (procWin m T a Z ω) = NegSobolev.coord (Z a ω) j := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Z (a + t) ω := by
    have h1 : Continuous fun t : Set.Icc (0 : ℝ) T => a + (t : ℝ) := by fun_prop
    refine (hω (a + T)).comp_continuous h1 (fun t => ?_)
    exact ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
  have e : toPath m T (fun t ω => Z (a + t) ω) ω =
      ((⟨fun t : Set.Icc (0 : ℝ) T => Z (a + t) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) :
        PathSpace d m T) := by
    simp [toPath, hc]
    rfl
  unfold procWin
  refine (congrArg (fun w : PathSpace d m T => ell hT j w) e).trans ?_
  show NegSobolev.coord (Z (a + ((0 : ℝ))) ω) j = _
  rw [add_zero]

theorem ct_coord_eq (F : NegSobolev d m) (j : NonzeroLattice d) :
    NegSobolev.coord F j = Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j := by
  unfold NegSobolev.fourierCoeff
  have : 0 < Lattice.jp j.1 ^ m := Real.rpow_pos_of_pos (Torus.jp_pos _) _
  rw [Real.rpow_neg (Torus.jp_pos _).le]
  field_simp

theorem ct_gauss (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ℝ → Ω → NegSobolev d m} {Y : Ω → NegSobolev d m}
    (mf : ModeField d s β β₀ m P Z Y) (k : PosHalf d) {a : ℝ} (ha : 0 ≤ a) :
    HasGaussianLaw (fun ω => ell hT (idx k true) (procWin m T a Z ω)) P ∧
      ∫ ω, ell hT (idx k true) (procWin m T a Z ω) ∂P = 0 := by
  have hae : (fun ω => ell hT (idx k true) (procWin m T a Z ω)) =ᵐ[P]
      fun ω => Lattice.jp (idx k true).1 ^ (-m) • Xmode Z (k, true) a.toNNReal ω := by
    filter_upwards [mf.cont] with ω hω
    rw [ct_ell_procWin hT _ Z ha hω, ct_coord_eq, Xmode_eq]
    simp [sgn, Real.coe_toNNReal _ ha]
  have hG := (isGaussianProcess_Xmode hd hs0 hsd hβ mf).hasGaussianLaw_eval
    (⟨(k, true), a.toNNReal⟩ : (_ : PosHalf d × Bool) × ℝ≥0)
  refine ⟨(hG.fun_smul _).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_smul]
  have : ∫ ω, Xmode Z (k, true) a.toNNReal ω ∂P = 0 := by
    simp only [Xmode_eq]
    rw [integral_const_mul, mean_fcZ hd hs0 hsd hβ mf _ (NNReal.coe_nonneg _), mul_zero]
  simp [this]

end HRS.MC.Q714.CT
