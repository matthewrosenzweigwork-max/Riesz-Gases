import HRS.MC.S7PIDBTrunc
import HRS.MC.S7PIDTMain

/-!
# Packet PI-D, sub-packet B (part 2): `nuc^F (M) → nuc (M)` as `F ↑ all modes`

For node families `w, w'` that are a.e. strongly measurable and a.e. bounded on `(c,c']`, the truncated tensors
`nuc (Π_F w) (Π_F w') M` converge along `F → atTop` to `nuc w w' M`: replace the families by a globally measurable bounded
modification, write both sides as integrals of `M[polyPath, polyPath]` (`S7PIDT_nuc_apply`), and use dominated convergence
(`polyPath` is a continuous linear map of the node vector, `S7PIDT_Phi`, bounded by `s7_PID_poly_proof`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDB

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

set_option maxSynthPendingDepth 3 in
/-- dominated convergence for globally measurable, globally bounded node families -/
theorem S7PIDB_tendsto (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (c c' : ℝ) (hc : 0 ≤ c) (hlt : c < c') (hc' : c' ≤ T) (n : ℕ) (w w' : ℝ → ℕ → NegSobolev d m)
    (hw : ∀ i, Measurable fun u => w u i) (hw' : ∀ i, Measurable fun u => w' u i) (b : ℝ)
    (hb : ∀ u i, ‖w u i‖ ≤ b) (hb' : ∀ u i, ‖w' u i‖ ≤ b) (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    Tendsto (fun F : Finset (NonzeroLattice d) => ∫ u in Set.Ioc c c',
        M ![polyPath R.D R.ρ m T c c' n (fun i => truncF m F (w u i)),
          polyPath R.D R.ρ m T c c' n (fun i => truncF m F (w' u i))]) atTop
      (𝓝 (∫ u in Set.Ioc c c', M ![polyPath R.D R.ρ m T c c' n (w u), polyPath R.D R.ρ m T c c' n (w' u)])) := by
  obtain ⟨Φ, hΦ⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_Phi R m hm T hT c c' hc hlt hc' n
  obtain ⟨C₁, hC₁, hpoly⟩ := HRS.MC.Sec7.S7PIDP.s7_PID_poly_proof R m hm T hT
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  let g : (Fin (2 ^ n + 1) → NegSobolev d m) × (Fin (2 ^ n + 1) → NegSobolev d m) → ℝ :=
    fun z => M ![Φ z.1, Φ z.2]
  have hgc : Continuous g := by
    have h1 : Continuous fun z : (Fin (2 ^ n + 1) → NegSobolev d m) × (Fin (2 ^ n + 1) → NegSobolev d m) =>
        (![Φ z.1, Φ z.2] : Fin 2 → PathSpace d m T) := by
      refine continuous_pi fun i => ?_
      fin_cases i
      · exact Φ.continuous.comp continuous_fst
      · exact Φ.continuous.comp continuous_snd
    exact M.cont.comp h1
  let ψ : Finset (NonzeroLattice d) → ℝ → (Fin (2 ^ n + 1) → NegSobolev d m) × (Fin (2 ^ n + 1) → NegSobolev d m) :=
    fun F u => ((fun i => truncF m F (w u i.1)), (fun i => truncF m F (w' u i.1)))
  let ψ0 : ℝ → (Fin (2 ^ n + 1) → NegSobolev d m) × (Fin (2 ^ n + 1) → NegSobolev d m) :=
    fun u => ((fun i => w u i.1), (fun i => w' u i.1))
  have hFeq : ∀ (F : Finset (NonzeroLattice d)) (u : ℝ),
      M ![polyPath R.D R.ρ m T c c' n (fun i => truncF m F (w u i)),
        polyPath R.D R.ρ m T c c' n (fun i => truncF m F (w' u i))] = g (ψ F u) := by
    intro F u
    simp only [g, ψ, hΦ]
  have h0eq : ∀ u : ℝ,
      M ![polyPath R.D R.ρ m T c c' n (w u), polyPath R.D R.ρ m T c c' n (w' u)] = g (ψ0 u) := by
    intro u
    simp only [g, ψ0, hΦ]
  simp_rw [hFeq, h0eq]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖M‖ * (C₁ * b) * (C₁ * b))
    (Filter.Eventually.of_forall fun F => ?_) (Filter.Eventually.of_forall fun F => ?_)
    (integrable_const _) (Filter.Eventually.of_forall fun u => ?_)
  · have hm1 : Measurable (ψ F) := by
      refine Measurable.prodMk ?_ ?_
      · exact measurable_pi_iff.2 fun i => (S7PIDB_trunc_lip m F).continuous.measurable.comp (hw i.1)
      · exact measurable_pi_iff.2 fun i => (S7PIDB_trunc_lip m F).continuous.measurable.comp (hw' i.1)
    exact (hgc.comp_stronglyMeasurable hm1.stronglyMeasurable).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    rw [← hFeq]
    have h1 := (hpoly c c' hc hlt.le hc' n (fun i => truncF m F (w u i))).2.1 b fun i _ =>
      (HRS.MC.Sec7.S7PIDT.S7PIDT_trunc_norm_le m F _).trans (hb u i)
    have h2 := (hpoly c c' hc hlt.le hc' n (fun i => truncF m F (w' u i))).2.1 b fun i _ =>
      (HRS.MC.Sec7.S7PIDT.S7PIDT_trunc_norm_le m F _).trans (hb' u i)
    calc ‖M ![polyPath R.D R.ρ m T c c' n (fun i => truncF m F (w u i)),
          polyPath R.D R.ρ m T c c' n (fun i => truncF m F (w' u i))]‖
        ≤ ‖M‖ * ∏ i, ‖(![polyPath R.D R.ρ m T c c' n (fun i => truncF m F (w u i)),
          polyPath R.D R.ρ m T c c' n (fun i => truncF m F (w' u i))] : Fin 2 → PathSpace d m T) i‖ :=
          M.le_opNorm _
      _ = ‖M‖ * (‖polyPath R.D R.ρ m T c c' n (fun i => truncF m F (w u i))‖ *
          ‖polyPath R.D R.ρ m T c c' n (fun i => truncF m F (w' u i))‖) := by
          simp [Fin.prod_univ_two]
      _ ≤ ‖M‖ * ((C₁ * b) * (C₁ * b)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
            (norm_nonneg _)
      _ = ‖M‖ * (C₁ * b) * (C₁ * b) := by ring
  · have hpt : Tendsto (fun F : Finset (NonzeroLattice d) => ψ F u) atTop (𝓝 (ψ0 u)) := by
      refine Tendsto.prodMk_nhds ?_ ?_
      · exact tendsto_pi_nhds.2 fun i => S7PIDB_trunc_tendsto m _
      · exact tendsto_pi_nhds.2 fun i => S7PIDB_trunc_tendsto m _
    exact (hgc.tendsto _).comp hpt

set_option maxSynthPendingDepth 3 in
/-- the truncated tensors converge, evaluated at every bounded bilinear form -/
theorem S7PIDB_nuc_tendsto (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (c c' : ℝ) (hc : 0 ≤ c) (hlt : c < c') (hc' : c' ≤ T) (n : ℕ) (w w' : ℝ → ℕ → NegSobolev d m) (b : ℝ)
    (hw : ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => w u i) (volume.restrict (Set.Ioc c c')))
    (hw' : ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => w' u i) (volume.restrict (Set.Ioc c c')))
    (hb : ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖w u i‖ ≤ b)
    (hb' : ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖w' u i‖ ≤ b)
    (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    Tendsto (fun F : Finset (NonzeroLattice d) =>
        nuc R.D R.ρ m T c c' n (fun u i => truncF m F (w u i)) (fun u i => truncF m F (w' u i)) M) atTop
      (𝓝 (nuc R.D R.ρ m T c c' n w w' M)) := by
  obtain ⟨wt, hwt1, hwt2, hwt3⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_modify m _ (2 ^ n) w b hw hb
  obtain ⟨wt', hwt1', hwt2', hwt3'⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_modify m _ (2 ^ n) w' b hw' hb'
  have e0 : nuc R.D R.ρ m T c c' n w w' M = ∫ u in Set.Ioc c c',
      M ![polyPath R.D R.ρ m T c c' n (wt u), polyPath R.D R.ρ m T c c' n (wt' u)] := by
    rw [HRS.MC.Sec7.S7PIDT.S7PIDT_nuc_apply R m hm T hT c c' hc hlt.le hc' n w w' b hw hw' hb hb' M]
    refine integral_congr_ae ?_
    filter_upwards [hwt3, hwt3'] with u h1 h2
    rw [HRS.MC.Sec7.S7PIDN.S7PIDN_polyPath_congr R.D R.ρ m T c c' n (w u) (wt u) fun i hi => (h1 i hi).symm,
      HRS.MC.Sec7.S7PIDN.S7PIDN_polyPath_congr R.D R.ρ m T c c' n (w' u) (wt' u) fun i hi => (h2 i hi).symm]
  have eF : ∀ F : Finset (NonzeroLattice d),
      nuc R.D R.ρ m T c c' n (fun u i => truncF m F (w u i)) (fun u i => truncF m F (w' u i)) M =
        ∫ u in Set.Ioc c c', M ![polyPath R.D R.ρ m T c c' n (fun i => truncF m F (wt u i)),
          polyPath R.D R.ρ m T c c' n (fun i => truncF m F (wt' u i))] := by
    intro F
    have hlip := S7PIDB_trunc_lip m F
    rw [HRS.MC.Sec7.S7PIDT.S7PIDT_nuc_apply R m hm T hT c c' hc hlt.le hc' n _ _ b
      (fun i hi => hlip.continuous.comp_aestronglyMeasurable (hw i hi))
      (fun i hi => hlip.continuous.comp_aestronglyMeasurable (hw' i hi))
      (fun i hi => (hb i hi).mono fun u hu => (HRS.MC.Sec7.S7PIDT.S7PIDT_trunc_norm_le m F _).trans hu)
      (fun i hi => (hb' i hi).mono fun u hu => (HRS.MC.Sec7.S7PIDT.S7PIDT_trunc_norm_le m F _).trans hu) M]
    refine integral_congr_ae ?_
    filter_upwards [hwt3, hwt3'] with u h1 h2
    rw [HRS.MC.Sec7.S7PIDN.S7PIDN_polyPath_congr R.D R.ρ m T c c' n (fun i => truncF m F (w u i))
        (fun i => truncF m F (wt u i)) fun i hi => by rw [h1 i hi],
      HRS.MC.Sec7.S7PIDN.S7PIDN_polyPath_congr R.D R.ρ m T c c' n (fun i => truncF m F (w' u i))
        (fun i => truncF m F (wt' u i)) fun i hi => by rw [h2 i hi]]
  rw [e0]
  refine (tendsto_congr eF).2 ?_
  exact S7PIDB_tendsto R m hm T hT c c' hc hlt hc' n wt wt' hwt1 hwt1' (max b 0) hwt2 hwt2' M

end HRS.MC.Sec7.S7PIDB

end
