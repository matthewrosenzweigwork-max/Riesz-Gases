import HRS.MH.MfclSpec
import HRS.MD.EQGaussWindow
import HRS.MD.EQBurnClt

/-!
# Proofs of `HRS.MH.Mfcl.exists_pathEval` (A1) and `HRS.MH.Mfcl.gauss_pathEval` (A9)

Statement-only packets from `HRS/MH/MfclSpec.lean`; proofs only, no statement is changed.
The helpers of `HRS/ME/FamVC.lean` (`memℓp_fourierVec`, `fourierVec`, `eval_eq_inner_cos`) are copied for a
general smooth `φ` (namespace `HRS.MH.MfclP`), so that `HRS.ME.FamVC` need not be imported.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.MfclP

open HRS HRS.Main HRS.LZ HRS.MD.EQ29

theorem memℓp_fourierVec_phi (d : ℕ) (m : ℝ) (φ : Torus d → ℝ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) 2 := by
  rw [Torus.memℓp_two_iff]
  refine hs.congr fun k => ?_
  rw [mul_pow, Torus.jp_rpow_sq]

/-- The `ℓ²` vector `k ↦ ⟨k⟩^{m} φ̂(k)` representing `F ↦ F(φ)` in `E_m` (copy of `HRS.ME.FamV.fourierVec`). -/
def fourierVecPhi (d : ℕ) (m : ℝ) (φ : Torus d → ℝ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    NegSobolev d m :=
  (⟨fun k : NonzeroLattice d => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k,
    memℓp_fourierVec_phi d m φ hs⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)

theorem eval_eq_inner_phi {d : ℕ} {m : ℝ} (F : NegSobolev d m) (φ : Torus d → ℝ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    NegSobolev.eval F φ = @inner ℝ (NegSobolev d m) _ F (fourierVecPhi d m φ hs) := by
  have h := lp.inner_eq_tsum (𝕜 := ℝ) (G := fun _ : NonzeroLattice d => ℝ)
    (F : lp (fun _ : NonzeroLattice d => ℝ) 2)
    (fourierVecPhi d m φ hs : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine Eq.trans ?_ h.symm
  unfold NegSobolev.eval
  refine tsum_congr fun l => ?_
  simp only [NegSobolev.fourierCoeff, RCLike.inner_apply, conj_trivial]
  show Lattice.jp l.1 ^ m * NegSobolev.coord F l * Torus.funRealCoeff φ l =
    (Lattice.jp l.1 ^ m * Torus.funRealCoeff φ l) * NegSobolev.coord F l
  ring

/-- A1: the time-zero pairing with a smooth test function is a continuous linear functional on path space. -/
theorem exists_pathEval_proof : type_of% @HRS.MH.Mfcl.exists_pathEval := by
  intro d m T hT φ hφ
  have hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 :=
    (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ m).2
  refine ⟨(innerSL ℝ (fourierVecPhi d m φ hs)).comp
    (ContinuousMap.evalCLM ℝ (⟨0, Set.left_mem_Icc.2 hT⟩ : Set.Icc (0 : ℝ) T)), fun w => ?_⟩
  show innerSL ℝ (fourierVecPhi d m φ hs) (w.at' ⟨0, Set.left_mem_Icc.2 hT⟩) = _
  rw [innerSL_apply_apply, eval_eq_inner_phi, real_inner_comm]

/-- A9: the time-zero pairing of the Gaussian window is a centred Gaussian `N(0, v)`, and the window is measurable. -/
theorem gauss_pathEval_proof : type_of% @HRS.MH.Mfcl.gauss_pathEval := by
  intro d hd s hs0 hsd V hV β hβ ρβ hρβ hρs m T hT Ω' _ P' _ Z hZ ℓ hℓ
  have hW : AEMeasurable (windowPath m T 0 Z) P' :=
    (HRS.MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ ρβ m T P' Z hZ 0 le_rfl).1
  have hae : (ℓ ∘ windowPath m T 0 Z) =ᵐ[P'] fun ω => NegSobolev.eval (Z 0 ω) ρβ := by
    filter_upwards [hZ.cont] with ω hω
    have h0 : (0 : ℝ) + ((⟨0, Set.left_mem_Icc.2 hT⟩ : Set.Icc (0 : ℝ) T) : ℝ) = 0 := by simp
    show ℓ (windowPath m T 0 Z ω) = _
    rw [hℓ, HRS.MD.EQGaussWindow.eqgw_windowPath_at T 0 le_rfl Z ω hω, h0]
  have hmap : (law P' (windowPath m T 0 Z)).map ℓ = P'.map (fun ω => NegSobolev.eval (Z 0 ω) ρβ) :=
    calc (law P' (windowPath m T 0 Z)).map ℓ = P'.map (ℓ ∘ windowPath m T 0 Z) :=
          AEMeasurable.map_map_of_aemeasurable ℓ.continuous.measurable.aemeasurable hW
      _ = P'.map (fun ω => NegSobolev.eval (Z 0 ω) ρβ) := Measure.map_congr hae
  have hgauss := HRS.MD.EQBurnClt.eqclt_gauss_law hd hs0 hsd V hV hβ ρβ hρβ P' Z hZ hρs
  refine ⟨hW, ?_, ?_⟩
  · rw [hmap, hgauss]
    unfold gaussianLaw
    exact memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  · rw [hmap, hgauss]
    unfold gaussianLaw
    exact integral_id_gaussianReal

end HRS.MH.MfclP
