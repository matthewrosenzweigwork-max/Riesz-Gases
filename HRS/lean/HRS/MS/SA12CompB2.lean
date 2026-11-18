import HRS.Whole.AppendixA
import HRS.PDE.ToolboxRd.Fourier

/-!
# S.A.12 B2: the uloc, varpi and Fourier Sobolev norms are invariant under a.e. equality
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa12b2_memSobolev_congr (r : ℝ) {a b : Euc d → ℝ} (hab : a =ᵐ[volume] b) :
    HRS.PDE.ToolboxRd.MemSobolev r a ↔ HRS.PDE.ToolboxRd.MemSobolev r b := by
  have hF := HRS.PDE.ToolboxRd.FourierAux.fourierL2_congr_ae hab
  unfold HRS.PDE.ToolboxRd.MemSobolev
  rw [hF]
  exact and_congr ⟨fun h => h.ae_eq hab, fun h => h.ae_eq hab.symm⟩ Iff.rfl

theorem sa12b2_sobolevNormSq_congr (r : ℝ) {a b : Euc d → ℝ} (hab : a =ᵐ[volume] b) :
    HRS.PDE.ToolboxRd.sobolevNormSq r a = HRS.PDE.ToolboxRd.sobolevNormSq r b := by
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  rw [HRS.PDE.ToolboxRd.FourierAux.fourierL2_congr_ae hab]

theorem sa12b2_sobolevNormE_congr (r : ℝ) {a b : Euc d → ℝ} (hab : a =ᵐ[volume] b) :
    HRS.Whole.sobolevNormE r a = HRS.Whole.sobolevNormE r b := by
  unfold HRS.Whole.sobolevNormE
  by_cases ha : HRS.PDE.ToolboxRd.MemSobolev r a
  · have hb := (sa12b2_memSobolev_congr r hab).1 ha
    simp [ha, hb, sa12b2_sobolevNormSq_congr r hab]
  · have hb : ¬ HRS.PDE.ToolboxRd.MemSobolev r b := fun hb => ha ((sa12b2_memSobolev_congr r hab).2 hb)
    simp [ha, hb]

-- BEGIN SA12.B2
theorem norm_congr_ae (m : ℕ) (χ u v : Euc d → ℝ) (h : u =ᵐ[volume] v) :
    ulocNormE m χ u=ulocNormE m χ v ∧
      varpiNormE m χ u=varpiNormE m χ v ∧
      (HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u ↔ HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) v) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) u=HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) v := by
  have hcut : ∀ c : Euc d, (fun x => χ (x - c) * u x) =ᵐ[volume] fun x => χ (x - c) * v x :=
    fun c => by filter_upwards [h] with x hx; simp [hx]
  refine ⟨?_, ?_, sa12b2_memSobolev_congr _ h, sa12b2_sobolevNormSq_congr _ h⟩
  · unfold ulocNormE
    exact iSup_congr fun z => sa12b2_sobolevNormE_congr _ (hcut z)
  · unfold varpiNormE
    congr 1
    exact tsum_congr fun z => by rw [sa12b2_sobolevNormE_congr _ (hcut (cellPt d z))]
-- END SA12.B2

end HRS.MH.AdjointRd.Phase2SA12Companions
