import HRS.MC.CepE6E3

/-!
# Packet CEPE6E, file 4: S6 (Slater duality) and the deterministic main estimate

For a constant vector `u` with `‖u‖ ≤ 1/2`, the Minty inequality at the path `y = Zl + t_ε (v_ε(Zl) + u)` (which lies in the
open alcove by the Slater lemma) gives
`⟨u, A(T) - ∫∇Φ(Zl)⟩ ≤ -L_ε + ∫⟨v_ε(Zl), ∇Φ(Zl)⟩`, `L_ε = lim ∫⟨v_ε(Zs_i), b_i⟩`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE6D

variable {N : ℕ}

theorem cepe6e_det_main {a : ℝ} {J : ℝ → Ch N → Ch N} {T : ℝ} {nn : ℕ → ℝ} {Zs : ℕ → ℝ → Ch N}
    {Zl : ℝ → Ch N} (D : Det a J T nn Zs Zl) (hN : 1 ≤ N) {A : ℝ → Ch N}
    (hA : TendstoUniformlyOn (fun i t => ∫ s in (0 : ℝ)..t, bF J nn Zs i s) A atTop (Icc 0 T))
    {K : ℝ} (hK : ∀ᶠ i in atTop, ∫ s in (0 : ℝ)..T, ‖bF J nn Zs i s‖ ≤ K)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) {u : Ch N} (hu : ‖u‖ ≤ 1 / 2) :
    ∃ L : ℝ, Tendsto (fun i => ∫ s in (0 : ℝ)..T, ⟪vv ε (Zs i s), bF J nn Zs i s⟫) atTop (𝓝 L) ∧
      ⟪u, A T - ∫ s in (0 : ℝ)..T, gradient (cep_chamberPot a N) (Zl s)⟫ ≤
        -L + ∫ s in (0 : ℝ)..T, ⟪vv ε (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫ := by
  have hT := D.hT
  obtain ⟨Λ, hΛb, hΛ1, hΛ2, -⟩ := cepe6d_weak_limit_on hT (b := bF J nn Zs)
    (fun i => (D.bF_cont i).continuousOn) hA hK
  have hW : IsWL J nn Zs T Λ := hΛ2
  set t : ℝ := tEps ε N with ht
  have htpos : 0 < t := tEps_pos hε hN
  have hvvc : Continuous (vv (N := N) ε) := (cepe6d_cutoff_calculus ε hε hε1 N).2.1.continuous
  set y : ℝ → Ch N := fun s => Zl s + t • (vv ε (Zl s) + u) with hy
  have hVc0 : Continuous fun s => vv (N := N) ε (Zl s) := hvvc.comp D.hZl
  have hyc : Continuous y := D.hZl.add ((hVc0.add continuous_const).const_smul t)
  have hyA : ∀ s ∈ Icc (0 : ℝ) T, y s ∈ cep_Alcove N := by
    intro s hs
    have := cepe6d_S2_slater_closure hε hε1 (z := Zl s) (D.hcl s hs) (e := vv ε (Zl s) + u)
      (by simpa using hu)
    exact this
  have hmin := cepe6e_minty D hW hK hyc hyA
  -- the pieces
  set V : ℝ → Ch N := fun s => vv ε (Zl s) with hV
  have hVc : Continuous V := hvvc.comp D.hZl
  have hfeq : (fun s => Zl s - y s) = fun s => (-t) • (V s + u) := by
    funext s; simp only [hy, hV]; rw [neg_smul, sub_add_cancel_left]
  have hfc : ContinuousOn (fun s => Zl s - y s) (Icc 0 T) := (D.hZl.sub hyc).continuousOn
  have hsum : ofFun (fun s => Zl s - y s) hfc = (-t) • (ofFun V hVc.continuousOn +
      ofFun (fun _ => u) continuousOn_const) := by
    refine ContinuousMap.ext fun x => ?_
    show Zl x.1 - y x.1 = (-t) • (V x.1 + u)
    exact congrFun hfeq x.1
  -- integrals
  have hIV : IntervalIntegrable (fun s => ⟪V s, gradient (cep_chamberPot a N) (Zl s)⟫) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]; exact D.integrableOn_inner hVc.continuousOn
  have hIu : IntervalIntegrable (fun s => ⟪u, gradient (cep_chamberPot a N) (Zl s)⟫) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    exact D.integrableOn_inner (g := fun _ => u) continuousOn_const
  have hint : ∫ s in (0 : ℝ)..T, ⟪Zl s - y s, gradient (cep_chamberPot a N) (Zl s)⟫ =
      (-t) * ((∫ s in (0 : ℝ)..T, ⟪V s, gradient (cep_chamberPot a N) (Zl s)⟫) +
        ∫ s in (0 : ℝ)..T, ⟪u, gradient (cep_chamberPot a N) (Zl s)⟫) := by
    rw [← intervalIntegral.integral_add hIV hIu, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show ⟪Zl s - y s, gradient (cep_chamberPot a N) (Zl s)⟫ = _
    rw [congrFun hfeq s, real_inner_smul_left, inner_add_left]
  rw [hint, hsum, map_smul, map_add, smul_eq_mul] at hmin
  have hP1 : Λ (ofFun (fun _ => u) continuousOn_const) = ⟪u, A T⟫ := by
    have := hΛ1 (fun _ => u) contDiff_const
    simpa using this
  have hL : Tendsto (fun i => ∫ s in (0 : ℝ)..T, ⟪vv ε (Zs i s), bF J nn Zs i s⟫) atTop
      (𝓝 (Λ (ofFun V hVc.continuousOn))) := by
    refine hW (fun i s => vv ε (Zs i s)) V (fun i => (hvvc.comp (D.hZs i)).continuousOn)
      hVc.continuousOn ?_
    exact cepe6e_tuo_comp hvvc isCompact_Icc D.hZl.continuousOn D.hunif
  refine ⟨Λ (ofFun V hVc.continuousOn), hL, ?_⟩
  rw [hP1] at hmin
  have hinner : ⟪u, A T - ∫ s in (0 : ℝ)..T, gradient (cep_chamberPot a N) (Zl s)⟫ =
      ⟪u, A T⟫ - ∫ s in (0 : ℝ)..T, ⟪u, gradient (cep_chamberPot a N) (Zl s)⟫ := by
    have hGint : IntervalIntegrable (fun s => gradient (cep_chamberPot a N) (Zl s)) volume 0 T := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]; exact D.grZl_integrable
    have hcomm := (innerSL ℝ u).intervalIntegral_comp_comm (μ := volume) (a := 0) (b := T)
      (f := fun s => gradient (cep_chamberPot a N) (Zl s)) hGint
    simp only [innerSL_apply_apply] at hcomm
    rw [inner_sub_right, hcomm]
  rw [hinner]
  nlinarith [htpos]

end HRS.MC.CepE6E
