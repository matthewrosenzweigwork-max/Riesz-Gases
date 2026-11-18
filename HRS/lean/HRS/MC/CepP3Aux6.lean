import HRS.MC.CepP3Aux5

/-!
# Packet P3, Aux6: the drift on the covering space, chain rules for slices, and `fkeIto = L`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

/-! ### The drift on the covering space -/

theorem liftedDrift_eq_driftVec (D : DynData d) (Y : Fin N → Euc d) :
    liftedDrift D Y = driftVec D (mkC Y) := rfl

/-- The drift on the covering space `ℝ × (Fin N → Euc d)` (independent of time). -/
def bC (D : DynData d) (p : ℝ × (Fin N → Euc d)) : Fin N → Euc d := liftedDrift D p.2

theorem bC_tau (D : DynData d) (w : Fin N → Lattice d) (p : ℝ × (Fin N → Euc d)) :
    bC D (tau w p) = bC D p := by
  show liftedDrift D (p.2 + lat w) = liftedDrift D p.2
  rw [liftedDrift_eq_driftVec, liftedDrift_eq_driftVec, mkC_add_lat]

theorem contDiffOn_liftedDrift_top (D : DynData d) (hV : Torus.IsSmooth D.V) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (liftedDrift (N := N) D) (liftedFree d N) := by
  have hK1 := smoothOffZero_of_dim D
  have hMv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.matVec D.M) :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin D.M)).contDiff
  have hV1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gradient (Torus.lift D.V)) := by
    have hV' : ContDiff ℝ ∞ (Torus.lift D.V) := hV
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (Torus.lift D.V)) :=
      hV'.fderiv_right (m := ∞) (by simp)
    have : gradient (Torus.lift D.V) =
        (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ (Torus.lift D.V) := by
      funext x; rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp h1
  refine contDiffOn_pi.2 fun i => ?_
  have e : (fun Y : Fin N → Euc d => liftedDrift D Y i) = fun Y =>
      (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
        Torus.matVec D.M (Torus.lift (periodicRieszGrad d D.s) (Y i - Y j)) -
          gradient (Torus.lift D.V) (Y i) := funext fun Y => liftedDrift_apply D Y i
  show ContDiffOn ℝ _ (fun Y : Fin N → Euc d => liftedDrift D Y i) (liftedFree d N)
  rw [e]
  refine ContDiffOn.sub (ContDiffOn.const_smul _ (ContDiffOn.sum fun j hj => ?_)) ?_
  · have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    refine hMv.comp_contDiffOn (hK1.comp (f := fun Y : Fin N → Euc d => Y i - Y j) ?_ ?_)
    · exact ((contDiff_apply ℝ (Euc d) i).sub (contDiff_apply ℝ (Euc d) j)).contDiffOn
    · intro Y hY
      exact mk_sub_ne_zero_of_mem_liftedFree hY hij
  · exact (hV1.comp (contDiff_apply ℝ (Euc d) i)).contDiffOn

theorem contDiffOn_bC (D : DynData d) (hV : Torus.IsSmooth D.V) {T : ℝ} :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bC (N := N) D) (Ioo 0 T ×ˢ liftedFree d N) :=
  (contDiffOn_liftedDrift_top D hV).comp contDiff_snd.contDiffOn (fun p hp => hp.2)

/-! ### Chain rules for slices -/

theorem hasDerivAt_slice_time {G : ℝ × (Fin N → Euc d) → ℝ} (hG : Differentiable ℝ G)
    (Y : Fin N → Euc d) (r : ℝ) :
    HasDerivAt (fun r' => G (r', Y)) (fderiv ℝ G (r, Y) (1, 0)) r := by
  have h1 : HasDerivAt (fun r' : ℝ => (r', Y)) ((1 : ℝ), (0 : Fin N → Euc d)) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r Y)
  exact ((hG (r, Y)).hasFDerivAt).comp_hasDerivAt r h1

theorem fderiv_slice_space {G : ℝ × (Fin N → Euc d) → ℝ} (hG : Differentiable ℝ G) (r : ℝ)
    (Y : Fin N → Euc d) :
    fderiv ℝ (fun Z => G (r, Z)) Y = (fderiv ℝ G (r, Y)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin N → Euc d)) :=
  ((hG (r, Y)).hasFDerivAt.comp Y (hasFDerivAt_prodMk_right r Y)).fderiv

theorem fderiv2_slice_space {G : ℝ × (Fin N → Euc d) → ℝ} (hG : ContDiff ℝ 2 G) (r : ℝ)
    (Y v w : Fin N → Euc d) :
    fderiv ℝ (fderiv ℝ (fun Z => G (r, Z))) Y v w = fderiv ℝ (fderiv ℝ G) (r, Y) (0, v) (0, w) := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e1 : fderiv ℝ (fun Z => G (r, Z)) = fun Z =>
      (ContinuousLinearMap.compL ℝ (Fin N → Euc d) (ℝ × (Fin N → Euc d)) ℝ).flip
        (ContinuousLinearMap.inr ℝ ℝ (Fin N → Euc d)) (fderiv ℝ G (r, Z)) := by
    funext Z
    rw [fderiv_slice_space hGd]
    rfl
  have h3 : HasFDerivAt (fun Z => fderiv ℝ G (r, Z))
      ((fderiv ℝ (fderiv ℝ G) (r, Y)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin N → Euc d))) Y :=
    (hD (r, Y)).hasFDerivAt.comp Y (hasFDerivAt_prodMk_right r Y)
  have h4 := ((ContinuousLinearMap.compL ℝ (Fin N → Euc d) (ℝ × (Fin N → Euc d)) ℝ).flip
        (ContinuousLinearMap.inr ℝ ℝ (Fin N → Euc d))).hasFDerivAt.comp Y h3
  rw [e1]
  exact congrArg (fun L => L v w) h4.fderiv

end HRS.MC.CepP3
