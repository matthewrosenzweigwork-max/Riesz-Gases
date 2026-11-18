import HRS.MC.CepP5Aux5

/-!
# Packet P5, Aux6: `fkeForward` in covering coordinates
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP5

open HRS HRS.MC.CepP3 HRS.MC.CepP4

variable {d N : ℕ}

theorem fderiv_slice_loc {H : ℝ × (Fin N → Euc d) → ℝ} {r : ℝ} {Y : Fin N → Euc d}
    (hH : DifferentiableAt ℝ H (r, Y)) (v : Fin N → Euc d) :
    fderiv ℝ (fun Z => H (r, Z)) Y v = fderiv ℝ H (r, Y) (0, v) := by
  have := (hH.hasFDerivAt.comp Y (hasFDerivAt_prodMk_right r Y)).fderiv
  show fderiv ℝ (H ∘ Prod.mk r) Y v = _
  rw [this]
  rfl

theorem fderiv2_slice_loc {O : Set (ℝ × (Fin N → Euc d))} (hO : IsOpen O)
    {G : ℝ × (Fin N → Euc d) → ℝ} (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G O)
    {r : ℝ} {Y : Fin N → Euc d} (hp : (r, Y) ∈ O) (v w : Fin N → Euc d) :
    fderiv ℝ (fderiv ℝ (fun Z => G (r, Z))) Y v w = fderiv ℝ (fderiv ℝ G) (r, Y) (0, v) (0, w) := by
  have hGd : ∀ q ∈ O, DifferentiableAt ℝ G q := fun q hq =>
    (hG.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  have hD : DifferentiableAt ℝ (fderiv ℝ G) (r, Y) :=
    ((hG.fderiv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hO (by simp)).contDiffAt
      (hO.mem_nhds hp)).differentiableAt (by simp)
  have hnhds : {Z : Fin N → Euc d | (r, Z) ∈ O} ∈ 𝓝 Y :=
    (hO.preimage (Continuous.prodMk_right r)).mem_nhds hp
  have e1 : fderiv ℝ (fun Z => G (r, Z)) =ᶠ[𝓝 Y] fun Z =>
      (ContinuousLinearMap.compL ℝ (Fin N → Euc d) (ℝ × (Fin N → Euc d)) ℝ).flip
        (ContinuousLinearMap.inr ℝ ℝ (Fin N → Euc d)) (fderiv ℝ G (r, Z)) := by
    filter_upwards [hnhds] with Z hZ
    exact ((hGd _ hZ).hasFDerivAt.comp Z (hasFDerivAt_prodMk_right r Z)).fderiv
  have h3 : HasFDerivAt (fun Z => fderiv ℝ G (r, Z))
      ((fderiv ℝ (fderiv ℝ G) (r, Y)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin N → Euc d))) Y :=
    hD.hasFDerivAt.comp Y (hasFDerivAt_prodMk_right r Y)
  have h4 := ((ContinuousLinearMap.compL ℝ (Fin N → Euc d) (ℝ × (Fin N → Euc d)) ℝ).flip
        (ContinuousLinearMap.inr ℝ ℝ (Fin N → Euc d))).hasFDerivAt.comp Y h3
  rw [e1.fderiv_eq]
  exact congrArg (fun L => L v w) h4.fderiv

theorem fkeForward_eq {O : Set (ℝ × (Fin N → Euc d))} (hO : IsOpen O) {D : DynData d}
    {f : ℝ → Config d N → ℝ}
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin N → Euc d) => f p.1 (mkC p.2)) O)
    (hb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bC (N := N) D) O)
    {r : ℝ} {x : Config d N} (hp : (r, repC x) ∈ O) :
    fkeForward D f r x = Fwd D.invβ (bC D) (fun p : ℝ × (Fin N → Euc d) => f p.1 (mkC p.2)) (r, repC x) := by
  dsimp only [fkeForward, Fwd]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact fderiv2_slice_loc hO hg hp _ _
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    have hd : DifferentiableAt ℝ (fun q : ℝ × (Fin N → Euc d) => bk (bC D) k q * f q.1 (mkC q.2)) (r, repC x) :=
      (((contDiffOn_bk hb k).mul hg).contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
    exact fderiv_slice_loc (H := fun q : ℝ × (Fin N → Euc d) => bk (bC D) k q * f q.1 (mkC q.2)) hd _

end HRS.MC.CepP5
