import HRS.Main.HeadlineEdgeworth
import HRS.Sections.AdjKGlue
import HRS.Main.T25PAux10
import HRS.Main.Lattice39FA2

/-!
# Packet CC4: `ccd_dual_pairing_bound` (statement of `HRS/MC/CrossCovSpec.lean`, proved)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CrossCov

open HRS HRS.Main

variable {d : ℕ}

/-- Embedding of a smooth mean-zero `w` into `E_{-N}`: same underlying `ℓ²` sequence as `lpFun N w`,
so `fourierCoeff = ŵ`. -/
def p_cc4_emb (N : ℕ) (w : Torus d → ℝ) : NegSobolev d (-(N : ℝ)) :=
  (HRS.Uniform.Q54c.lpFun (N : ℝ) w : NegSobolev d (N : ℝ))

theorem p_cc4_emb_norm (N : ℕ) (w : Torus d → ℝ) :
    ‖p_cc4_emb N w‖ ≤ HRS.sobolevNorm (N : ℝ) w :=
  HRS.Uniform.Q54c.norm_lpFun_le (N : ℝ) w

theorem p_cc4_emb_fc {N : ℕ} {w : Torus d → ℝ} (hw : Torus.IsSmooth w) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (p_cc4_emb N w) k = Torus.funRealCoeff w k := by
  have hm : MemSobolev (N : ℝ) w := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hw _
  have h := HRS.Uniform.Q54c.coord_lpFun hm k
  unfold NegSobolev.fourierCoeff
  have h' : NegSobolev.coord (p_cc4_emb N w) k = Lattice.jp k.1 ^ (N : ℝ) * Torus.funRealCoeff w k := h
  rw [h', ← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
  simp

theorem p_cc4_eval_emb {N : ℕ} {w g : Torus d → ℝ} (hw : Torus.IsSmooth w) (hw0 : Torus.mean w = 0)
    (hg : MemLp g 2 volume) :
    NegSobolev.eval (p_cc4_emb N w) g = ∫ x, g x * w x := by
  have hwL : MemLp w 2 volume := (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hw 0).1
  have := HRS.Main.lat39fa_integral_mul_eq_tsum hwL hg hw0
  unfold NegSobolev.eval
  simp_rw [p_cc4_emb_fc hw]
  rw [← this]
  exact (integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _))

theorem ccd_dual_pairing_bound (S : PreparedData d) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ w ψ : Torus d → ℝ,
      Torus.IsSmooth w → Torus.mean w = 0 → Torus.IsSmooth ψ →
      |∫ x, propagator S.dyn S.ρ u t ψ x * w x| ≤
        C * HRS.sobolevNorm (N : ℝ) w * HRS.sobolevNorm (-(N : ℝ)) ψ := by
  have htr := HRS.T25.t25_traj S
  obtain ⟨Cr, cr, hCr, hcr, Vev, hdual, -, hdec, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd htr (-(N : ℝ))
  refine ⟨Cr, hCr.le, fun u t hu hut w ψ hw hw0 hψ => ?_⟩
  have hKb : ‖Vev t u‖ ≤ Cr := by
    refine (hdec u t hu hut).trans ?_
    have h1 : Real.exp (-cr * (t - u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sub_nonneg.2 hut]
    nlinarith
  have hmem := HRS.T25P.t25p_memSobolev_propagator S.hd htr hdual hCr.le hu hut hKb hψ
  have hψm : MemSobolev (-(N : ℝ)) ψ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hψ _
  set F := p_cc4_emb N w with hF
  have e1 : ∫ x, propagator S.dyn S.ρ u t ψ x * w x = NegSobolev.eval (Vev t u F) ψ := by
    rw [hdual u t hu hut F ψ hψ, p_cc4_eval_emb hw hw0 hmem.1]
    rfl
  rw [e1, HRS.Uniform.Q54c.eval_lpFun _ hψm]
  calc |inner ℝ (Vev t u F) (HRS.Uniform.Q54c.lpFun (-(N : ℝ)) ψ)|
      ≤ ‖Vev t u F‖ * ‖HRS.Uniform.Q54c.lpFun (-(N : ℝ)) ψ‖ := abs_real_inner_le_norm _ _
    _ ≤ (Cr * ‖F‖) * HRS.sobolevNorm (-(N : ℝ)) ψ := by
        gcongr
        · exact ((Vev t u).le_opNorm F).trans (mul_le_mul_of_nonneg_right hKb (norm_nonneg _))
        · exact HRS.Uniform.Q54c.norm_lpFun_le _ _
    _ ≤ Cr * HRS.sobolevNorm (N : ℝ) w * HRS.sobolevNorm (-(N : ℝ)) ψ := by
        have h0 : 0 ≤ HRS.sobolevNorm (-(N : ℝ)) ψ := Real.sqrt_nonneg _
        have := p_cc4_emb_norm N w
        gcongr

end HRS.MC.CrossCov

end
