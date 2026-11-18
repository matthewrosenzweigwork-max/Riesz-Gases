import HRS.Equilibrium.Parametrix.PXFIDAuxG

/-!
# Packet PX-FID, file H: first and second derivatives of an affine slice of a function
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

section Slice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slice_fderiv (G : E → ℝ) (A : Euc d →L[ℝ] E) (c : E) {S : Set E} (hS : IsOpen S)
    (hG : ContDiffOn ℝ 2 G S) {p : Euc d} (hp : A p + c ∈ S) :
    fderiv ℝ (fun p' => G (A p' + c)) p = (fderiv ℝ G (A p + c)).comp A := by
  have hGd : DifferentiableAt ℝ G (A p + c) :=
    ((hG.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp))
  have hι : HasFDerivAt (fun p' : Euc d => A p' + c) A p := A.hasFDerivAt.add_const c
  exact (hGd.hasFDerivAt.comp p hι).fderiv

theorem slice_fderiv2 (G : E → ℝ) (A : Euc d →L[ℝ] E) (c : E) {S : Set E} (hS : IsOpen S)
    (hG : ContDiffOn ℝ 2 G S) {p : Euc d} (hp : A p + c ∈ S) (w v : Euc d) :
    fderiv ℝ (fderiv ℝ (fun p' => G (A p' + c))) p w v =
      fderiv ℝ (fderiv ℝ G) (A p + c) (A w) (A v) := by
  have hGc : ContDiffAt ℝ 2 G (A p + c) := hG.contDiffAt (hS.mem_nhds hp)
  have hι : HasFDerivAt (fun p' : Euc d => A p' + c) A p := A.hasFDerivAt.add_const c
  have hGd' : DifferentiableAt ℝ (fderiv ℝ G) (A p + c) :=
    (hGc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hιc : ContDiffAt ℝ 2 (fun p' : Euc d => A p' + c) p :=
    (A.contDiff.add contDiff_const).contDiffAt
  have hFc : ContDiffAt ℝ 2 (fun p' : Euc d => G (A p' + c)) p := hGc.comp p hιc
  have hFd : DifferentiableAt ℝ (fderiv ℝ (fun p' : Euc d => G (A p' + c))) p :=
    (hFc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  -- the open neighbourhood
  have hnhds : {p' : Euc d | A p' + c ∈ S} ∈ 𝓝 p :=
    (hS.preimage (A.continuous.add continuous_const)).mem_nhds hp
  have h1 : fderiv ℝ (fderiv ℝ (fun p' : Euc d => G (A p' + c))) p w v =
      fderiv ℝ (fun p' => fderiv ℝ (fun p'' : Euc d => G (A p'' + c)) p' v) p w := by
    rw [fderiv_clm_apply hFd (differentiableAt_const v)]
    simp
  have h2 : (fun p' => fderiv ℝ (fun p'' : Euc d => G (A p'' + c)) p' v) =ᶠ[𝓝 p]
      fun p' => fderiv ℝ G (A p' + c) (A v) := by
    filter_upwards [hnhds] with p' hp'
    rw [slice_fderiv G A c hS hG hp']
    rfl
  have h3 : HasFDerivAt (fun p' : Euc d => fderiv ℝ G (A p' + c))
      ((fderiv ℝ (fderiv ℝ G) (A p + c)).comp A) p := hGd'.hasFDerivAt.comp p hι
  have h4 := h3.clm_apply (hasFDerivAt_const (A v) p)
  rw [h1, h2.fderiv_eq, h4.fderiv]
  simp

theorem abs_fderiv2_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → ℝ) (P u v : E) :
    |fderiv ℝ (fderiv ℝ G) P u v| ≤ ‖iteratedFDeriv ℝ 2 G P‖ * ‖u‖ * ‖v‖ := by
  have h : iteratedFDeriv ℝ 2 G P ![u, v] = fderiv ℝ (fderiv ℝ G) P u v := by
    rw [iteratedFDeriv_two_apply]; rfl
  rw [← h, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans (le_of_eq ?_)
  simp [Fin.prod_univ_two, mul_assoc]

end Slice

theorem isOpen_offDiag'' (d : ℕ) : IsOpen (offDiag d) := by
  have hc1 : Continuous fun p : Euc d × Euc d => Torus.mk p.1 :=
    Torus.continuous_mk.comp continuous_fst
  have hc2 : Continuous fun p : Euc d × Euc d => Torus.mk p.2 :=
    Torus.continuous_mk.comp continuous_snd
  exact isOpen_ne_fun hc1 hc2

/-- `PsiSize` bounds give the `SingSlice` bounds for an affine slice of `lift2 ψ`. -/
theorem singSlice_of_affine {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K₁ ψ)
    (A : Euc d →L[ℝ] Euc d × Euc d) (hA : ∀ v, ‖A v‖ ≤ ‖v‖) (c : Euc d × Euc d)
    (u : Torus d → ℝ) (ã : Euc d)
    (hlift : Torus.lift u = fun p => lift2 ψ (A p + c))
    (hmem : ∀ p, Torus.mk p ≠ Torus.mk ã ↔ A p + c ∈ offDiag d)
    (hr : ∀ p, rTrunc (Torus.mk (A p + c).1) (Torus.mk (A p + c).2) =
      rTrunc (Torus.mk p) (Torus.mk ã)) :
    SingSlice s K₁ ã u := by
  have hS := isOpen_offDiag'' d
  have hG : ContDiffOn ℝ 2 (lift2 ψ) (offDiag d) :=
    (hψ.smooth).of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  have hιc : ContDiff ℝ ∞ (fun p : Euc d => A p + c) := A.contDiff.add contDiff_const
  have hAn : ‖A‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
    simpa using hA v)
  refine ⟨?_, ?_, ?_⟩
  · rw [hlift]
    have hι2 : ContDiffOn ℝ 2 (fun p : Euc d => A p + c) {p | Torus.mk p ≠ Torus.mk ã} :=
      (hιc.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top)).contDiffOn
    exact hG.comp hι2 (fun p hp => (hmem p).1 hp)
  · intro p hp
    rw [hlift]
    have hp' := (hmem p).1 hp
    rw [slice_fderiv (lift2 ψ) A c hS hG hp']
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := hψ.grad (A p + c) hp'
    rw [hr] at h1
    calc ‖fderiv ℝ (lift2 ψ) (A p + c)‖ * ‖A‖ ≤ ‖fderiv ℝ (lift2 ψ) (A p + c)‖ * 1 :=
          mul_le_mul_of_nonneg_left hAn (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h1
  · intro p hp j
    rw [hlift]
    have hp' := (hmem p).1 hp
    rw [slice_fderiv2 (lift2 ψ) A c hS hG hp']
    have h1 := hψ.hess (A p + c) hp'
    rw [hr] at h1
    have h2 := abs_fderiv2_le (lift2 ψ) (A p + c) (A (EuclideanSpace.single j 1))
      (A (EuclideanSpace.single j 1))
    have hn : ‖A (EuclideanSpace.single j (1 : ℝ))‖ ≤ 1 := by
      refine (hA _).trans ?_
      simp
    refine h2.trans ?_
    refine le_trans ?_ h1
    have h3 : 0 ≤ ‖iteratedFDeriv ℝ 2 (lift2 ψ) (A p + c)‖ := norm_nonneg _
    calc ‖iteratedFDeriv ℝ 2 (lift2 ψ) (A p + c)‖ * ‖A (EuclideanSpace.single j 1)‖ *
          ‖A (EuclideanSpace.single j 1)‖
        ≤ ‖iteratedFDeriv ℝ 2 (lift2 ψ) (A p + c)‖ * 1 * 1 := by
          gcongr
      _ = _ := by ring

theorem singSlice_fst {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K₁ ψ) (y : Torus d) :
    SingSlice s K₁ (Torus.rep y) (fun z => ψ z y) := by
  refine singSlice_of_affine hψ (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) (fun v => by simp)
    (0, Torus.rep y) _ _ ?_ ?_ ?_
  · funext p
    simp [Torus.lift, lift2, Torus.mk_rep]
  · intro p
    simp [offDiag]
  · intro p
    simp

theorem singSlice_snd {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K₁ ψ) (x : Torus d) :
    SingSlice s K₁ (Torus.rep x) (fun z => ψ x z) := by
  refine singSlice_of_affine hψ (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) (fun v => by simp)
    (Torus.rep x, 0) _ _ ?_ ?_ ?_
  · funext p
    simp [Torus.lift, lift2, Torus.mk_rep]
  · intro p
    simp [offDiag, ne_comm]
  · intro p
    simp [PairCorrAux.rTrunc_symm]

end HRS.Parx.PXFID

end
