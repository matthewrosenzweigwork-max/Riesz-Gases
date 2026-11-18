import HRS.MC.WinJSpecDefs
import HRS.MC.WinJP3
import HRS.MC.WinJP6
import HRS.MC.E213M3
import HRS.MC.S7PIDKMain

/-!
# WJ7: P7 `p7_cov_diff` (difference covariance tensor)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

section P7

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
set_option maxSynthPendingDepth 3 in
/-- the limit of the nuclear tensors exists, is a bounded `projTensor` element and satisfies `CovEval`
(the proof of `E213M.e213m_cov`, with the limit exposed) -/
lemma p_wj7_cov_lim (Rb : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (p q : ℝ → ℝ) (Bp Bq : ℝ) (hp : Measurable p) (hq : Measurable q)
    (hpB : ∀ u, |p u| ≤ Bp) (hqB : ∀ u, |q u| ≤ Bq) (c c' : ℝ) (hc : 0 ≤ c) (hlt : c < c')
    (hc' : c' ≤ T) (k l : NonzeroLattice d) (W : ℝ) (hW0 : 0 ≤ W)
    (hτb : ∀ n, ‖nucK Rb m T c c' n p q k l id‖ ≤ W)
    (hτd : ∀ n, ‖nucK Rb m T c c' (n + 1) p q k l id - nucK Rb m T c c' n p q k l id‖ ≤
      W * (2 : ℝ) ^ (-(n : ℝ) / 4)) :
    ∃ τ' : TensorDual (PathSpace d m T) 2, τ' ∈ projTensor (PathSpace d m T) 2 ∧
      Tendsto (fun n => nucK Rb m T c c' n p q k l id) atTop (𝓝 τ') ∧
      CovEval Rb m T p q c c' k l τ' := by
  have hcc : c ≤ c' := hlt.le
  obtain ⟨Cb, hCb0, hnodes⟩ := HRS.MC.Sec7.S7PIDK.S7PIDK_nodes Rb m hm T hT
  obtain ⟨C₁, hC₁, hC⟩ := HRS.MC.Sec7.S7PIDP.s7_PID_poly_proof Rb m hm T hT
  set e : NegSobolev d m := modeVec m k with he
  set e' : NegSobolev d m := modeVec m l with he'
  set b : ℝ := max (Bp * (Cb * ‖e‖)) (Bq * (Cb * ‖e'‖)) with hb
  have hBp : 0 ≤ Bp := (abs_nonneg _).trans (hpB 0)
  have hBq : 0 ≤ Bq := (abs_nonneg _).trans (hqB 0)
  have hb0 : 0 ≤ b := le_trans (by positivity) (le_max_left _ _)
  have hmeasP : ∀ n, ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => kernelNodes Rb.D Rb.ρ m c c' n p e u i)
      (volume.restrict (Set.Ioc c c')) := fun n => (hnodes p Bp hp hpB c c' hc hcc hc' e n).1
  have hmeasQ : ∀ n, ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => kernelNodes Rb.D Rb.ρ m c c' n q e' u i)
      (volume.restrict (Set.Ioc c c')) := fun n => (hnodes q Bq hq hqB c c' hc hcc hc' e' n).1
  have hbdP : ∀ n, ∀ i ≤ 2 ^ n, ∀ u ∈ Set.Ioc c c', ‖kernelNodes Rb.D Rb.ρ m c c' n p e u i‖ ≤ b :=
    fun n i hi u hu => ((hnodes p Bp hp hpB c c' hc hcc hc' e n).2 i hi u hu).trans (le_max_left _ _)
  have hbdQ : ∀ n, ∀ i ≤ 2 ^ n, ∀ u ∈ Set.Ioc c c', ‖kernelNodes Rb.D Rb.ρ m c c' n q e' u i‖ ≤ b :=
    fun n i hi u hu => ((hnodes q Bq hq hqB c c' hc hcc hc' e' n).2 i hi u hu).trans (le_max_right _ _)
  have hbdP' : ∀ n, ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖kernelNodes Rb.D Rb.ρ m c c' n p e u i‖ ≤ b :=
    fun n i hi => (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => hbdP n i hi u hu)
  have hbdQ' : ∀ n, ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖kernelNodes Rb.D Rb.ρ m c c' n q e' u i‖ ≤ b :=
    fun n i hi => (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => hbdQ n i hi u hu)
  set τ : ℕ → TensorDual (PathSpace d m T) 2 := fun n => nuc Rb.D Rb.ρ m T c c' n
    (kernelNodes Rb.D Rb.ρ m c c' n p e) (kernelNodes Rb.D Rb.ρ m c c' n q e') with hτ
  have hτeq : ∀ n, nucK Rb m T c c' n p q k l id = τ n := fun n => rfl
  have hτmem : ∀ n, τ n ∈ projTensor (PathSpace d m T) 2 := fun n =>
    HRS.MC.Sec7.S7PIDK.S7PIDK_nuc_mem Rb m hm T hT c c' hc hcc hc' n _ _ b (hmeasP n) (hmeasQ n)
      (hbdP' n) (hbdQ' n)
  have hτb' : ∀ n, ‖τ n‖ ≤ W := fun n => hτb n
  have hτd' : ∀ n, ‖τ (n + 1) - τ n‖ ≤ W * (2 : ℝ) ^ (-(n : ℝ) / 4) := fun n => hτd n
  obtain ⟨τ', hτ'mem, hτ'lim, hτ'norm⟩ :=
    HRS.MC.Sec7.S7PIDK.S7PIDK_limit τ hτmem W hW0 hτd' hτb'
  refine ⟨τ', hτ'mem, hτ'lim, hτ'mem, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  have hsa := HRS.MC.Sec7.S7PIDK.S7PIDK_summable_smooth m hφa
  have hsb := HRS.MC.Sec7.S7PIDK.S7PIDK_summable_smooth m hφb
  set f : ℕ → ℝ → ℝ := fun n u => l₁ (polyPath Rb.D Rb.ρ m T c c' n (kernelNodes Rb.D Rb.ρ m c c' n p e u)) *
    l₂ (polyPath Rb.D Rb.ρ m T c c' n (kernelNodes Rb.D Rb.ρ m c c' n q e' u)) with hf
  have hnp : ∀ n, τ n (prodForm l₁ l₂) = ∫ u in Set.Ioc c c', f n u ∧
      AEStronglyMeasurable (f n) (volume.restrict (Set.Ioc c c')) := fun n =>
    HRS.MC.Sec7.S7PIDK.S7PIDK_nuc_prodForm Rb m hm T hT c c' hc hlt hc' n _ _ b (hmeasP n) (hmeasQ n)
      (hbdP' n) (hbdQ' n) l₁ l₂
  set Lf : ℝ → ℝ := fun u =>
    (p u * NegSobolev.eval (causalVec Rb.D Rb.ρ m ta u e) φa) *
      (q u * NegSobolev.eval (causalVec Rb.D Rb.ρ m tb u e') φb) with hLf
  have hdom : ∀ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖f n u‖ ≤ (‖l₁‖ * (C₁ * b)) * (‖l₂‖ * (C₁ * b)) := by
    intro n
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have h1 := (hC c c' hc hcc hc' n (kernelNodes Rb.D Rb.ρ m c c' n p e u)).2.1 b
      (fun i hi => hbdP n i hi u hu)
    have h2 := (hC c c' hc hcc hc' n (kernelNodes Rb.D Rb.ρ m c c' n q e' u)).2.1 b
      (fun i hi => hbdQ n i hi u hu)
    have g1 : ‖l₁ (polyPath Rb.D Rb.ρ m T c c' n (kernelNodes Rb.D Rb.ρ m c c' n p e u))‖ ≤ ‖l₁‖ * (C₁ * b) :=
      (l₁.le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    have g2 : ‖l₂ (polyPath Rb.D Rb.ρ m T c c' n (kernelNodes Rb.D Rb.ρ m c c' n q e' u))‖ ≤ ‖l₂‖ * (C₁ * b) :=
      (l₂.le_opNorm _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    simp only [hf, norm_mul]
    exact mul_le_mul g1 g2 (norm_nonneg _) ((norm_nonneg _).trans g1)
  have hne : ∀ x : ℝ, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), u ≠ x := by
    intro x
    refine ae_restrict_of_ae ?_
    have := (Set.countable_singleton x).ae_notMem (volume : Measure ℝ)
    filter_upwards [this] with u hu
    simpa using hu
  have hlim : ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), Tendsto (fun n => f n u) atTop (𝓝 (Lf u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne ta, hne tb] with u hu hua hub
    have A1 : Tendsto (fun n => l₁ (polyPath Rb.D Rb.ρ m T c c' n (kernelNodes Rb.D Rb.ρ m c c' n p e u))) atTop
        (𝓝 (p u * NegSobolev.eval (causalVec Rb.D Rb.ρ m ta u e) φa)) := by
      have h1 := HRS.MC.Sec7.S7PIDK.S7PIDK_eval_tendsto hsa
        (HRS.MC.Sec7.S7PIDK.S7PIDK_pathAt_tendsto Rb m hm T hT hc hlt hc' (p u) k hu hta hua)
      rw [HRS.MC.Sec7.S7PIDK.S7PIDK_eval_smul] at h1
      simp only [hl₁]
      exact h1
    have A2 : Tendsto (fun n => l₂ (polyPath Rb.D Rb.ρ m T c c' n (kernelNodes Rb.D Rb.ρ m c c' n q e' u))) atTop
        (𝓝 (q u * NegSobolev.eval (causalVec Rb.D Rb.ρ m tb u e') φb)) := by
      have h1 := HRS.MC.Sec7.S7PIDK.S7PIDK_eval_tendsto hsb
        (HRS.MC.Sec7.S7PIDK.S7PIDK_pathAt_tendsto Rb m hm T hT hc hlt hc' (q u) l hu htb hub)
      rw [HRS.MC.Sec7.S7PIDK.S7PIDK_eval_smul] at h1
      simp only [hl₂]
      exact h1
    exact A1.mul A2
  have hDCT := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Set.Ioc c c'))
    (F := f) (f := Lf) (fun _ => (‖l₁‖ * (C₁ * b)) * (‖l₂‖ * (C₁ * b)))
    (fun n => (hnp n).2) (integrable_const _) hdom hlim
  have hconv : Tendsto (fun n => τ n (prodForm l₁ l₂)) atTop (𝓝 (τ' (prodForm l₁ l₂))) :=
    ((ContinuousLinearMap.apply ℝ ℝ (prodForm l₁ l₂)).continuous.tendsto τ').comp hτ'lim
  have hEq : τ' (prodForm l₁ l₂) = ∫ u in Set.Ioc c c', Lf u :=
    tendsto_nhds_unique hconv (hDCT.congr fun n => ((hnp n).1).symm)
  rw [hEq, ← setIntegral_indicator measurableSet_Icc]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  simp only [hLf]
  by_cases hmem : u ∈ Set.Icc (0 : ℝ) (min ta tb)
  · rw [Set.indicator_of_mem hmem]
    have hua : u ≤ ta := hmem.2.trans (min_le_left _ _)
    have hub : u ≤ tb := hmem.2.trans (min_le_right _ _)
    simp only [causalVec, if_pos hua, if_pos hub]
    ring
  · rw [Set.indicator_of_notMem hmem]
    have hu0 : 0 ≤ u := hc.trans hu.1.le
    have hnot : ¬ (u ≤ ta ∧ u ≤ tb) := by
      intro h
      exact hmem ⟨hu0, le_min h.1 h.2⟩
    by_cases hua : u ≤ ta
    · have hub : ¬ u ≤ tb := fun h => hnot ⟨hua, h⟩
      simp only [causalVec, if_neg hub, HRS.MC.Sec7.S7PIDK.S7PIDK_eval_zero]
      ring
    · simp only [causalVec, if_neg hua, HRS.MC.Sec7.S7PIDK.S7PIDK_eval_zero]
      ring

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

set_option maxHeartbeats 1600000 in
set_option maxSynthPendingDepth 3 in
theorem p7_cov_diff (sd : StatDatum S β₀ m hE) (T : ℝ) (hT : 0 < T) :
    ∃ K κ : ℝ, 0 ≤ K ∧ 0 < κ ∧ ∀ (b : ℝ) (hb : 0 ≤ b) (p q : ℝ → ℝ) (Bp Bq : ℝ), Measurable p → Measurable q →
      (∀ u, |p u| ≤ Bp) → (∀ u, |q u| ≤ Bq) → ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → ∀ k l : NonzeroLattice d,
      ∃ τ τ' : TensorDual (PathSpace d m T) 2,
        CovEval (Rp sd b hb) m T p q c c' k l τ ∧ CovEval (Rs sd b hb) m T p q c c' k l τ' ∧
        ‖τ - τ'‖ ≤ K * Bp * Bq * Real.exp (-κ * b) * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) *
          (c' - c) := by
  obtain ⟨K, κ, hK, hκ, h6⟩ := p6_nucbound_diff sd T hT
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hms : 3 * (d : ℝ) + 8 < m := sd.hEs.m_gt
  obtain ⟨K1, hK1, hb1⟩ := HRS.MC.E213M.e213m_nucbound (regime S β₀ hE) m hm T hT
  obtain ⟨K2, hK2, hb2⟩ := HRS.MC.E213M.e213m_nucbound (regime sd.Ss S.β sd.hEs) m hms T hT
  refine ⟨K, κ, hK, hκ, ?_⟩
  intro b hb p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l
  have hBp : 0 ≤ Bp := (abs_nonneg _).trans (hpB 0)
  have hBq : 0 ≤ Bq := (abs_nonneg _).trans (hqB 0)
  have hjk : 0 ≤ Lattice.jp k.1 ^ (-(m - 1)) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hjl : 0 ≤ Lattice.jp l.1 ^ (-(m - 1)) := Real.rpow_nonneg (Torus.jp_pos l.1).le _
  by_cases hceq : c = c'
  · subst hceq
    refine ⟨0, 0, ⟨Submodule.zero_mem _, ?_⟩, ⟨Submodule.zero_mem _, ?_⟩, ?_⟩
    · intro ta tb φa φb l₁ l₂ _ _ _ _ _ _
      simp
    · intro ta tb φa φb l₁ l₂ _ _ _ _ _ _
      simp
    · rw [sub_zero, norm_zero, sub_self, mul_zero]
  have hlt : c < c' := lt_of_le_of_ne hcc hceq
  have hΔ : 0 ≤ c' - c := sub_nonneg.2 hcc
  have hW1 : 0 ≤ K1 * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) := by
    positivity
  have hW2 : 0 ≤ K2 * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) := by
    positivity
  have hn1 := hb1 b hb p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l
  have hn2 := hb2 b hb p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l
  obtain ⟨τ, -, hτl, hτc⟩ := p_wj7_cov_lim (Rp sd b hb) m hm T hT p q Bp Bq hp hq hpB hqB c c' hc hlt hc' k l
    _ hW1 (fun n => (hn1 n).1) (fun n => (hn1 n).2)
  obtain ⟨τ', -, hτ'l, hτ'c⟩ := p_wj7_cov_lim (Rs sd b hb) m hms T hT p q Bp Bq hp hq hpB hqB c c' hc hlt hc' k l
    _ hW2 (fun n => (hn2 n).1) (fun n => (hn2 n).2)
  refine ⟨τ, τ', hτc, hτ'c, ?_⟩
  exact le_of_tendsto' (hτl.sub hτ'l).norm fun n => (h6 b hb p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l n).1

end P7

end HRS.MC.WinJ

end
