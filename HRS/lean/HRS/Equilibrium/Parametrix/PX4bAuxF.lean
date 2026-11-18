import HRS.Equilibrium.Parametrix.PX4bAuxE

/-!
# Packet PX4b auxiliaries F: the derivative of `g ⋆ h` at a regular point, no flux

For `h` that is `C¹` off a point `y` with `h` and `∂_i h` integrable, and `x ≠ y`:
`∂_i (g ⋆ h)(x) = (g ⋆ ∂_i h)(x)` (`g` integrable, smooth off `0`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma px4b_integral_sub_left (f : Torus d → ℝ) (x : Torus d) :
    ∫ w, f (x - w) = ∫ w, f w := integral_sub_left_eq_self f volume x

theorem px4b_partialDeriv_convFun (hd : 2 ≤ d) (i : Fin d) {g h : Torus d → ℝ}
    (hg : Integrable g) (hgs : Torus.IsSmoothOffZero g) {y x : Torus d} (hxy : x ≠ y)
    (hh : ∀ v : Euc d, Torus.mk v ≠ y → ContDiffAt ℝ 1 (Torus.lift h) v)
    (hhi : Integrable h) (hdh : Integrable (Torus.partialDeriv i h)) :
    Integrable (fun w => g (x - w) * Torus.partialDeriv i h w) ∧
      Torus.partialDeriv i (convFun g h) x = convFun g (Torus.partialDeriv i h) x := by
  obtain ⟨δ, hδ, hδ6, hnot⟩ := px4b_delta hxy
  obtain ⟨gn, gf, hφ, hsum, hgn, hgf, hhφ, hgn0, hagree, hz⟩ :=
    px4b_convFun_split hg hgs hhi (Torus.rep x) hδ hδ6 (fun v hv => hh v (hnot v hv))
  have hx0 : px4b_D (Torus.rep x - Torus.rep x) < δ := by
    rw [sub_self, px4b_D_mk_zero (mk_isLat isLat_zero)]; exact hδ
  have hgfc : Continuous gf := KernelGrad.continuous_of_lift hgf.continuous
  have hφc : Continuous (Torus.partialDeriv i hφ) := PDE.continuous_partialDeriv i hφ hhφ
  -- (1) decomposition of the derivative
  have hd1 := PDE.MFSchauder.convFun_hasFDerivAt hgn hhφ (Torus.rep x)
  have hd2 := PDE.MFSchauder.convFun_hasFDerivAt hhi hgf (Torus.rep x)
  have e2 : convFun gf h = convFun h gf := funext (px4b_convFun_comm gf h)
  have hev : Torus.lift (convFun g h) =ᶠ[𝓝 (Torus.rep x)]
      fun v => Torus.lift (convFun gn hφ) v + Torus.lift (convFun h gf) v := by
    filter_upwards [(px4b_isOpen_D_lt (Torus.rep x) δ).mem_nhds hx0] with v hv
    have := (hz v hv).2
    show convFun g h (Torus.mk v) = convFun gn hφ (Torus.mk v) + convFun h gf (Torus.mk v)
    rw [this, e2]
  have hdA : DifferentiableAt ℝ (Torus.lift (convFun gn hφ)) (Torus.rep x) := hd1.differentiableAt
  have hdB : DifferentiableAt ℝ (Torus.lift (convFun h gf)) (Torus.rep x) := hd2.differentiableAt
  have hfd : Torus.partialDeriv i (convFun g h) x =
      Torus.partialDeriv i (convFun gn hφ) x + Torus.partialDeriv i (convFun h gf) x := by
    show fderiv ℝ (Torus.lift (convFun g h)) (Torus.rep x) (px4b_e i) =
      fderiv ℝ (Torus.lift (convFun gn hφ)) (Torus.rep x) (px4b_e i) +
        fderiv ℝ (Torus.lift (convFun h gf)) (Torus.rep x) (px4b_e i)
    rw [hev.fderiv_eq, fderiv_fun_add hdA hdB]
    rfl
  rw [hfd, PDE.MFSchauder.convFun_partialDeriv hgn hhφ i x,
    PDE.MFSchauder.convFun_partialDeriv hhi hgf i x]
  -- (2) the near part sees `h` itself
  have hnear : ∀ w : Torus d, gn (x - w) * Torus.partialDeriv i hφ w =
      gn (x - w) * Torus.partialDeriv i h w := by
    intro w
    by_cases h0 : gn (x - w) = 0
    · simp [h0]
    · congr 1
      have hmk : x - w = Torus.mk (Torus.rep x - Torus.rep w) := by
        rw [mk_sub_eq, Torus.mk_rep, Torus.mk_rep]
      rw [hmk] at h0
      have hD : px4b_D (Torus.rep x - Torus.rep w) < 2 * δ := by
        by_contra hcon
        exact h0 (hgn0 _ (not_lt.1 hcon))
      have hD' : px4b_D (Torus.rep w - Torus.rep x) < 3 * δ := by
        rw [← px4b_D_neg, neg_sub]; linarith
      have hopen := px4b_isOpen_D_lt (Torus.rep x) (3 * δ)
      have hev2 : Torus.lift hφ =ᶠ[𝓝 (Torus.rep w)] Torus.lift h := by
        filter_upwards [hopen.mem_nhds hD'] with v hv
        exact hagree v hv
      show fderiv ℝ (Torus.lift hφ) (Torus.rep w) (px4b_e i) =
        fderiv ℝ (Torus.lift h) (Torus.rep w) (px4b_e i)
      rw [hev2.fderiv_eq]
  have hIn : Integrable (fun w => gn (x - w) * Torus.partialDeriv i h w) := by
    obtain ⟨C, hC⟩ := PDE.MFSchauder.exists_bound_of_cont hφc
    have := (hgn.comp_sub_left x).mul_bdd (c := C) hφc.aestronglyMeasurable
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hC w)
    exact this.congr (Eventually.of_forall fun w => hnear w)
  have hIf : Integrable (fun w => gf (x - w) * Torus.partialDeriv i h w) := by
    obtain ⟨C, hC⟩ := PDE.MFSchauder.exists_bound_of_cont hgfc
    refine hdh.bdd_mul (c := C) (f := fun w => gf (x - w))
      (hgfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs]; exact hC _
  -- (3) integration by parts for the smooth part
  have hψ : Torus.IsCk 1 (fun w => gf (x - w)) := by
    show ContDiff ℝ 1 (Torus.lift fun w => gf (x - w))
    have e : Torus.lift (fun w => gf (x - w)) = fun v => Torus.lift gf (Torus.rep x - v) := by
      funext v
      simp only [Torus.lift, Function.comp]
      rw [show x - Torus.mk v = Torus.mk (Torus.rep x - v) by rw [mk_sub_eq, Torus.mk_rep]]
    rw [e]
    exact (show ContDiff ℝ 1 (Torus.lift gf) from hgf).comp (contDiff_const.sub contDiff_id)
  have hψd : ∀ w : Torus d, Torus.partialDeriv i (fun w => gf (x - w)) w =
      -Torus.partialDeriv i gf (x - w) := by
    intro w
    have e : Torus.lift (fun w => gf (x - w)) = fun v => Torus.lift gf (Torus.rep x - v) := by
      funext v
      simp only [Torus.lift, Function.comp]
      rw [show x - Torus.mk v = Torus.mk (Torus.rep x - v) by rw [mk_sub_eq, Torus.mk_rep]]
    show fderiv ℝ (Torus.lift fun w => gf (x - w)) (Torus.rep w) (px4b_e i) = _
    rw [e]
    have hdf : DifferentiableAt ℝ (Torus.lift gf) (Torus.rep x - Torus.rep w) :=
      ((show ContDiff ℝ 1 (Torus.lift gf) from hgf).differentiable one_ne_zero) _
    have hc := hdf.hasFDerivAt.comp (Torus.rep w) ((hasFDerivAt_id (Torus.rep w)).const_sub (Torus.rep x))
    have hh2 : HasFDerivAt (fun v => Torus.lift gf (Torus.rep x - v))
        ((fderiv ℝ (Torus.lift gf) (Torus.rep x - Torus.rep w)).comp (-(ContinuousLinearMap.id ℝ (Euc d))))
        (Torus.rep w) := hc
    rw [hh2.fderiv]
    have := px4b_lift_partialDeriv gf i (Torus.rep x - Torus.rep w)
    change Torus.partialDeriv i gf (Torus.mk (Torus.rep x - Torus.rep w)) = _ at this
    rw [show Torus.mk (Torus.rep x - Torus.rep w) = x - w by rw [mk_sub_eq, Torus.mk_rep, Torus.mk_rep]]
      at this
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, map_neg]
    exact congrArg Neg.neg this.symm
  have hibp := px4b_ibp hd i hh hψ hhi hdh
  simp only [hψd] at hibp
  have hflip : convFun h (Torus.partialDeriv i gf) x =
      ∫ w, h w * Torus.partialDeriv i gf (x - w) := by
    have := px4b_integral_sub_left (fun w => h w * Torus.partialDeriv i gf (x - w)) x
    rw [← this]
    unfold convFun
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [sub_sub_cancel]
  have hibp' : ∫ w, gf (x - w) * Torus.partialDeriv i h w =
      ∫ w, h w * Torus.partialDeriv i gf (x - w) := by
    rw [hibp]
    simp only [neg_mul, integral_neg, neg_neg]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [mul_comm]
  refine ⟨?_, ?_⟩
  · refine (hIn.add hIf).congr (Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply]
    beta_reduce
    rw [hsum (x - w)]; ring
  · rw [hflip, ← hibp']
    unfold convFun
    simp only [hnear]
    rw [← integral_add hIn hIf]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    beta_reduce
    rw [hsum (x - w)]; ring

end HRS.Parx
end
