import HRS.Main.GFEVAux19

/-!
# Packet GFEVG, part 20: `GFAbs` for the concrete data
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ} {s : ℝ} {γ : ℕ} {R : Regime} {VB Λ : ℝ} {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem gfev_integral_eval {γ : ℕ} {φ : Torus d → ℝ} (hφ : MemSobolev (γ : ℝ) φ)
    {f : ℝ → NegSobolev d (γ : ℝ)} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    NegSobolev.eval (∫ r in a..b, f r) φ = ∫ r in a..b, NegSobolev.eval (f r) φ := by
  have hL : ∀ F : NegSobolev d (γ : ℝ), NegSobolev.eval F φ = innerSL ℝ (lpOf (γ : ℝ) hφ) F := by
    intro F
    rw [eval_eq_inner _ F hφ, real_inner_comm]; rfl
  simp_rw [hL]
  exact ((innerSL ℝ (lpOf (γ : ℝ) hφ)).intervalIntegral_comp_comm hf).symm

theorem GFPde.absData (h : GFPde d s γ R VB Λ D T ρ) (l₀ l₂ l₄ : ℝ)
    (hq0 : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) (γ : ℝ) l₀)
    (hq2 : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) ((γ : ℝ) - 2) l₂)
    (hq4 : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) ((γ : ℝ) - 4) l₄) :
    ∃ (V : ℝ → ℝ → NegSobolev d (γ : ℝ) →L[ℝ] NegSobolev d (γ : ℝ))
      (W : ℝ → ℝ → NegSobolev d ((γ : ℝ) - 4) →L[ℝ] NegSobolev d ((γ : ℝ) - 4))
      (A2 : ℝ → NegSobolev d ((γ : ℝ) - 2) →L[ℝ] NegSobolev d (γ : ℝ)) (M : ℝ),
      GFAbs V (gfevD d γ) (fun s => gfevAop (A2 s)) l₀ ∧ 0 ≤ M ∧ (∀ t, ‖A2 t‖ ≤ M) ∧ Continuous A2 ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ (z : NegSobolev d (γ : ℝ)) (φ : Torus d → ℝ), Dom (γ + 2) φ →
        NegSobolev.eval (V t u z) φ = NegSobolev.eval z (UpF D (gfevMu T ρ) u t φ)) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖W t u‖ ≤ Real.exp (l₄ * (t - u))) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ z : NegSobolev d ((γ : ℝ) - 4),
        V t u (NegSobolev.embed (γ : ℝ) z) = NegSobolev.embed (γ : ℝ) (W t u z)) := by
  obtain ⟨V, W, hVd, hVb, hVs, hVc, hVcont, hWb, hcons⟩ := h.evolution l₀ l₂ l₄ hq0 hq2 hq4
  obtain ⟨M, A2, hM, hA2n, hA2d, hdh⟩ := h.generatorOp
  have hA2c : Continuous A2 := h.generatorOp_cont A2 hA2d hdh
  have hcore := h.core
  have hAT : ∀ s w, gfevAt (gfevD d γ) (fun s => gfevAop (A2 s)) s (NegSobolev.embed (γ : ℝ) w) =
      A2 s (NegSobolev.embed ((γ : ℝ) - 2) w) := fun s w => gfevAt_embed A2 s w
  set AT := gfevAt (gfevD d γ) (fun s => gfevAop (A2 s)) with hATdef
  -- continuity of `s ↦ V t s (AT s x)`
  have hVs_cont : ∀ t : ℝ, 0 ≤ t → ∀ y : NegSobolev d (γ : ℝ),
      ContinuousOn (fun s => V t s y) (Set.Icc 0 t) := fun t ht y =>
    (hVcont t y).comp (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hs.1, hs.2, le_rfl⟩)
  have hVs_bd : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ Set.Icc (0 : ℝ) t, ‖V t s‖ ≤ Real.exp (|l₀| * t) := fun t ht s hs =>
    (hVb s t hs.1 hs.2).trans (gfev_exp_le l₀ (by linarith [hs.2]) (by linarith [hs.1]))
  have hATc : ∀ x ∈ gfevD d γ, Continuous fun s => AT s x := by
    intro x hx
    obtain ⟨w, rfl⟩ := gfev_mem_D hx
    simp_rw [hAT]
    exact hA2c.clm_apply continuous_const
  have hVA : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ gfevD d γ, ContinuousOn (fun s => V t s (AT s y)) (Set.Icc 0 t) := by
    intro t ht y hy
    exact gfev_continuousOn_clm_apply (hVs_cont t ht) _ (hVs_bd t ht) (hATc y hy).continuousOn
  have hinv : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ x ∈ gfevD d γ, V t u x ∈ gfevD d γ := by
    intro u t hu hut x hx
    obtain ⟨w, rfl⟩ := gfev_mem_D hx
    rw [hcons u t hu hut w]
    exact gfev_embed_mem γ _
  have hcontAV : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ gfevD d γ,
      ContinuousOn (fun s => AT s (V s r x)) (Set.Ici r) := by
    intro r hr x hx
    obtain ⟨w, rfl⟩ := gfev_mem_D hx
    have hEq : Set.EqOn (fun s => AT s (V s r (NegSobolev.embed (γ : ℝ) w)))
        (fun s => A2 s (NegSobolev.embed ((γ : ℝ) - 2) (W s r w))) (Set.Ici r) := by
      intro s hs
      simp only
      rw [hcons r s hr hs, hAT]
    have hwc : ContinuousOn (fun s => NegSobolev.embed ((γ : ℝ) - 2) (W s r w)) (Set.Ici r) := by
      intro s₀ hs₀
      have hs₀' : r ≤ s₀ := hs₀
      refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_ (mem_nhdsWithin.2 ⟨Set.Iio (s₀ + 1), isOpen_Iio,
        by simp, fun y hy => ⟨hy.2, hy.1.le⟩⟩ : Set.Icc r (s₀ + 1) ∈ 𝓝[Set.Ici r] s₀)
      refine gfev_cont_interp (S := Set.Icc r (s₀ + 1)) (y := fun s => W s r w)
        (Real.exp (|l₄| * (s₀ + 1)) * ‖w‖) (fun s hs => ?_) ?_ ⟨hs₀', by linarith⟩
      · calc ‖W s r w‖ ≤ ‖W s r‖ * ‖w‖ := (W s r).le_opNorm w
          _ ≤ Real.exp (|l₄| * (s₀ + 1)) * ‖w‖ := by
            refine mul_le_mul_of_nonneg_right ((hWb r s hr hs.1).trans (gfev_exp_le l₄ (by linarith [hs.1])
              (by linarith [hs.2]))) (norm_nonneg _)
      · have hc := hVcont (s₀ + 1) (NegSobolev.embed (γ : ℝ) w)
        have hc2 : ContinuousOn (fun s => V s r (NegSobolev.embed (γ : ℝ) w)) (Set.Icc r (s₀ + 1)) :=
          hc.comp (continuous_id.prodMk continuous_const).continuousOn
            (fun s hs => ⟨hr, hs.1, hs.2⟩)
        have hc3 := hc2 s₀ ⟨hs₀', by linarith⟩
        refine hc3.congr (fun s hs => ?_) ?_
        · exact (hcons r s hr hs.1 w).symm
        · exact (hcons r s₀ hr hs₀' w).symm
    exact (gfev_continuousOn_clm_apply (Vf := A2) (fun z => (hA2c.clm_apply continuous_const).continuousOn)
      M (fun s _ => hA2n s) hwc).congr hEq
  -- the two mild identities
  have hmem_dom : ∀ {φ : Torus d → ℝ}, Torus.IsSmooth φ → Dom (γ + 2) φ := fun hφ => dom_smooth hφ
  have hmild_r : ∀ t : ℝ, 0 ≤ t → ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ t → ∀ x ∈ gfevD d γ,
      V t u x - V t u' x = ∫ r in u..u', V t r (AT r x) := by
    intro t ht u u' hu huu' hu't x hx
    obtain ⟨w, rfl⟩ := gfev_mem_D hx
    refine eq_of_eval_smooth fun φ hφ => ?_
    have hD := hmem_dom hφ
    have hφM : MemSobolev (γ : ℝ) φ := memSobolev_of_dom (by push_cast; linarith) hD
    set z : NegSobolev d ((γ : ℝ) - 2) := NegSobolev.embed ((γ : ℝ) - 2) w with hz
    have hii : IntervalIntegrable (fun r => V t r (AT r (NegSobolev.embed (γ : ℝ) w))) volume u u' :=
      ((hVA t ht _ hx).mono (Set.uIcc_subset_Icc ⟨hu, huu'.trans hu't⟩ ⟨hu.trans huu', hu't⟩)).intervalIntegrable
    rw [eval_sub_left _ _ hφM, gfev_integral_eval hφM hii, hVd u t hu (huu'.trans hu't) _ φ hD,
      hVd u' t (hu.trans huu') hu't _ φ hD, gfev_eval_embed (gfev_le4 γ), gfev_eval_embed (gfev_le4 γ)]
    have hdu := h.duhamel l₀ hq0 hD hu huu' hu't z
    have e1 : ∀ f : Torus d → ℝ, NegSobolev.eval w f = NegSobolev.eval z f := fun f =>
      (gfev_eval_embed (gfev_le42 γ) w f).symm
    rw [e1, e1, hdu]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le huu'] at hr
    have hr0 : 0 ≤ r := hu.trans hr.1
    have hrt : r ≤ t := hr.2.trans hu't
    rw [hVd r t hr0 hrt _ φ hD, hAT r w, hA2d r z _ (hcore.dom r t hr0 hrt φ hD)]
  have hmild_t : ∀ r t t' : ℝ, 0 ≤ r → r ≤ t → t ≤ t' → ∀ x ∈ gfevD d γ,
      V t' r x - V t r x = ∫ q in t..t', V t' q (AT q (V t r x)) := by
    intro r t t' hr hrt htt' x hx
    obtain ⟨w, rfl⟩ := gfev_mem_D hx
    refine eq_of_eval_smooth fun φ hφ => ?_
    have hD := hmem_dom hφ
    have hφM : MemSobolev (γ : ℝ) φ := memSobolev_of_dom (by push_cast; linarith) hD
    have ht0 : 0 ≤ t := hr.trans hrt
    have ht'0 : 0 ≤ t' := ht0.trans htt'
    set w' : NegSobolev d ((γ : ℝ) - 4) := W t r w with hw'
    have hy : V t r (NegSobolev.embed (γ : ℝ) w) = NegSobolev.embed (γ : ℝ) w' := hcons r t hr hrt w
    have hyD : V t r (NegSobolev.embed (γ : ℝ) w) ∈ gfevD d γ := by rw [hy]; exact gfev_embed_mem γ _
    set z : NegSobolev d ((γ : ℝ) - 2) := NegSobolev.embed ((γ : ℝ) - 2) w' with hz
    have hii : IntervalIntegrable (fun q => V t' q (AT q (V t r (NegSobolev.embed (γ : ℝ) w)))) volume t t' :=
      ((hVA t' ht'0 _ hyD).mono (Set.uIcc_subset_Icc ⟨ht0, htt'⟩ ⟨ht'0, le_rfl⟩)).intervalIntegrable
    rw [eval_sub_left _ _ hφM, gfev_integral_eval hφM hii]
    have hdu := h.duhamel l₀ hq0 hD ht0 htt' le_rfl z
    -- left side
    have hL1 : NegSobolev.eval (V t' r (NegSobolev.embed (γ : ℝ) w)) φ =
        NegSobolev.eval (V t r (NegSobolev.embed (γ : ℝ) w)) (UpF D (gfevMu T ρ) t t' φ) := by
      rw [hVd r t' hr (hrt.trans htt') _ φ hD,
        hVd r t hr hrt _ _ (hcore.dom t t' ht0 htt' φ hD), hcore.cocycle r t t' hr hrt htt' φ hD]
    have hL2 : NegSobolev.eval (V t r (NegSobolev.embed (γ : ℝ) w)) φ =
        NegSobolev.eval (V t r (NegSobolev.embed (γ : ℝ) w)) (UpF D (gfevMu T ρ) t' t' φ) := by
      rw [upF_self]
    rw [hL1, hL2, hy, gfev_eval_embed (gfev_le4 γ), gfev_eval_embed (gfev_le4 γ)]
    have e1 : ∀ f : Torus d → ℝ, NegSobolev.eval w' f = NegSobolev.eval z f := fun f =>
      (gfev_eval_embed (gfev_le42 γ) w' f).symm
    rw [e1, e1, hdu]
    refine intervalIntegral.integral_congr fun q hq => ?_
    rw [Set.uIcc_of_le htt'] at hq
    have hq0 : 0 ≤ q := ht0.trans hq.1
    have hqt : q ≤ t' := hq.2
    show NegSobolev.eval z (gfevL D (gfevMu T ρ q) (UpF D (gfevMu T ρ) q t' φ)) =
      NegSobolev.eval (V t' q (AT q (NegSobolev.embed (γ : ℝ) w'))) φ
    rw [hVd q t' hq0 hqt _ φ hD, hAT q w', hA2d q z _ (hcore.dom q t' hq0 hqt φ hD)]
  exact ⟨V, W, A2, M, ⟨hVb, hVs, hVc, hVcont, hinv, hATc, hcontAV, hmild_r, hmild_t⟩, hM, hA2n, hA2c, hVd, hWb, hcons⟩

end HRS.GF
