import HRS.MC.S7PIDBMain
import HRS.MC.S7PIDKPtw
import HRS.MC.S7PIDKEval
import HRS.MC.S7PIDKNuc
import HRS.MC.S7PIDKLim

/-!
# Packet PI-D, sub-packet K (part 7): proof of `s7_PID_cov_tensor` (D5)

The statement is copied verbatim from `HRS/MC/S7PIDPlan.lean`.  Route: `τ_n = nuc_n (kernel_n p e_k) (kernel_n q e_l)` is Cauchy
in `TensorDual` by `s7_PID_nuc_bound_proof` (geometric rate `2^{-n/4}`), lies in the closed subspace `projTensor`
(`S7PIDK_nuc_mem`), and has a limit `τ`.  The evaluation formula: `τ_n(ℓ_a ⊗ ℓ_b)` is an integral of the product of the evaluations of
the polygonal paths at `t_a`, `t_b`; these converge pointwise in `u ≠ t_a, t_b` (`S7PIDK_pathAt_tendsto`: strong continuity of `V`,
semigroup law for `t_a > c'`) and are dominated by a constant (`s7_PID_poly_proof`, `pie_Vbound`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDK

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

theorem S7PIDK_summable_smooth (m : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 := by
  set L : ℕ := ⌈m⌉₊ with hL
  have hdom : HRS.A33.Dom L φ := HRS.A33.dom_smooth hφ
  have hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * (L : ℝ)) * Torus.funRealCoeff φ k ^ 2 :=
    hdom.2.2
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (sq_nonneg _))
    (fun k => ?_) hs
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one k.1) ?_) (sq_nonneg _)
  have := Nat.le_ceil m
  linarith

set_option maxHeartbeats 1000000 in
set_option maxSynthPendingDepth 3 in
/-- **s7_PID_cov_tensor_proof**: proof of `HRS.MC.Sec7.PIDPlan.s7_PID_cov_tensor` (statement verbatim). -/
theorem s7_PID_cov_tensor_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p q : ℝ → ℝ) (Bp Bq : ℝ), Measurable p → Measurable q → (∀ u, |p u| ≤ Bp) →
      (∀ u, |q u| ≤ Bq) → ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → ∀ k l : NonzeroLattice d,
      ∃ τ : TensorDual (PathSpace d m T) 2, τ ∈ projTensor (PathSpace d m T) 2 ∧
        ‖τ‖ ≤ K * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) ∧
        ∀ (ta tb : ℝ) (φa φb : Torus d → ℝ) (l₁ l₂ : StrongDual ℝ (PathSpace d m T)),
          Torus.IsSmooth φa → Torus.IsSmooth φb →
          ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
          (∀ w, l₁ w = NegSobolev.eval (pathAt w ta) φa) → (∀ w, l₂ w = NegSobolev.eval (pathAt w tb) φb) →
          τ (prodForm l₁ l₂) = ∫ u in Set.Ioc c c' ∩ Set.Icc 0 (min ta tb), p u * q u *
            NegSobolev.eval (Vprop R.D R.ρ m ta u (modeVec m k)) φa *
            NegSobolev.eval (Vprop R.D R.ρ m tb u (modeVec m l)) φb := by
  obtain ⟨K, hK0, hbd⟩ := HRS.MC.Sec7.S7PIDB.s7_PID_nuc_bound_proof R m hm T hT
  refine ⟨K, hK0, ?_⟩
  intro p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l
  have hBp : 0 ≤ Bp := (abs_nonneg _).trans (hpB 0)
  have hBq : 0 ≤ Bq := (abs_nonneg _).trans (hqB 0)
  have hjk : 0 ≤ Lattice.jp k.1 ^ (-(m - 1)) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hjl : 0 ≤ Lattice.jp l.1 ^ (-(m - 1)) := Real.rpow_nonneg (Torus.jp_pos l.1).le _
  have hW0 : 0 ≤ K * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) := by
    have : 0 ≤ c' - c := sub_nonneg.2 hcc
    positivity
  by_cases hceq : c = c'
  · -- degenerate interval
    subst hceq
    refine ⟨0, Submodule.zero_mem _, ?_, ?_⟩
    · rw [norm_zero]; exact hW0
    · intro ta tb φa φb l₁ l₂ _ _ _ _ _ _
      simp
  have hlt : c < c' := lt_of_le_of_ne hcc hceq
  set W : ℝ := K * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) with hWdef
  obtain ⟨Cb, hCb0, hnodes⟩ := S7PIDK_nodes R m hm T hT
  obtain ⟨C₁, hC₁, hC⟩ := S7PIDP.s7_PID_poly_proof R m hm T hT
  set e : NegSobolev d m := modeVec m k with he
  set e' : NegSobolev d m := modeVec m l with he'
  set b : ℝ := max (Bp * (Cb * ‖e‖)) (Bq * (Cb * ‖e'‖)) with hb
  have hb0 : 0 ≤ b := le_trans (by positivity) (le_max_left _ _)
  have hmeasP : ∀ n, ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => kernelNodes R.D R.ρ m c c' n p e u i)
      (volume.restrict (Set.Ioc c c')) := fun n => (hnodes p Bp hp hpB c c' hc hcc hc' e n).1
  have hmeasQ : ∀ n, ∀ i ≤ 2 ^ n, AEStronglyMeasurable (fun u => kernelNodes R.D R.ρ m c c' n q e' u i)
      (volume.restrict (Set.Ioc c c')) := fun n => (hnodes q Bq hq hqB c c' hc hcc hc' e' n).1
  have hbdP : ∀ n, ∀ i ≤ 2 ^ n, ∀ u ∈ Set.Ioc c c', ‖kernelNodes R.D R.ρ m c c' n p e u i‖ ≤ b :=
    fun n i hi u hu => ((hnodes p Bp hp hpB c c' hc hcc hc' e n).2 i hi u hu).trans (le_max_left _ _)
  have hbdQ : ∀ n, ∀ i ≤ 2 ^ n, ∀ u ∈ Set.Ioc c c', ‖kernelNodes R.D R.ρ m c c' n q e' u i‖ ≤ b :=
    fun n i hi u hu => ((hnodes q Bq hq hqB c c' hc hcc hc' e' n).2 i hi u hu).trans (le_max_right _ _)
  have hbdP' : ∀ n, ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖kernelNodes R.D R.ρ m c c' n p e u i‖ ≤ b :=
    fun n i hi => (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => hbdP n i hi u hu)
  have hbdQ' : ∀ n, ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖kernelNodes R.D R.ρ m c c' n q e' u i‖ ≤ b :=
    fun n i hi => (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => hbdQ n i hi u hu)
  -- the sequence of tensors
  set τ : ℕ → TensorDual (PathSpace d m T) 2 := fun n => nuc R.D R.ρ m T c c' n
    (kernelNodes R.D R.ρ m c c' n p e) (kernelNodes R.D R.ρ m c c' n q e') with hτ
  have hτmem : ∀ n, τ n ∈ projTensor (PathSpace d m T) 2 := fun n =>
    S7PIDK_nuc_mem R m hm T hT c c' hc hcc hc' n _ _ b (hmeasP n) (hmeasQ n) (hbdP' n) (hbdQ' n)
  have hτb : ∀ n, ‖τ n‖ ≤ W := fun n => (hbd p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l n).1
  have hτd : ∀ n, ‖τ (n + 1) - τ n‖ ≤ W * (2 : ℝ) ^ (-(n : ℝ) / 4) := fun n =>
    (hbd p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l n).2
  obtain ⟨τ', hτ'mem, hτ'lim, hτ'norm⟩ := S7PIDK_limit τ hτmem W hW0 hτd hτb
  refine ⟨τ', hτ'mem, hτ'norm, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  have hsa := S7PIDK_summable_smooth m hφa
  have hsb := S7PIDK_summable_smooth m hφb
  -- evaluation of `τ_n`
  set f : ℕ → ℝ → ℝ := fun n u => l₁ (polyPath R.D R.ρ m T c c' n (kernelNodes R.D R.ρ m c c' n p e u)) *
    l₂ (polyPath R.D R.ρ m T c c' n (kernelNodes R.D R.ρ m c c' n q e' u)) with hf
  have hnp : ∀ n, τ n (prodForm l₁ l₂) = ∫ u in Set.Ioc c c', f n u ∧
      AEStronglyMeasurable (f n) (volume.restrict (Set.Ioc c c')) := fun n =>
    S7PIDK_nuc_prodForm R m hm T hT c c' hc hlt hc' n _ _ b (hmeasP n) (hmeasQ n) (hbdP' n) (hbdQ' n) l₁ l₂
  -- the limit function
  set Lf : ℝ → ℝ := fun u =>
    (p u * NegSobolev.eval (causalVec R.D R.ρ m ta u e) φa) *
      (q u * NegSobolev.eval (causalVec R.D R.ρ m tb u e') φb) with hLf
  -- domination
  have hdom : ∀ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), ‖f n u‖ ≤ (‖l₁‖ * (C₁ * b)) * (‖l₂‖ * (C₁ * b)) := by
    intro n
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have h1 := (hC c c' hc hcc hc' n (kernelNodes R.D R.ρ m c c' n p e u)).2.1 b
      (fun i hi => hbdP n i hi u hu)
    have h2 := (hC c c' hc hcc hc' n (kernelNodes R.D R.ρ m c c' n q e' u)).2.1 b
      (fun i hi => hbdQ n i hi u hu)
    have g1 : ‖l₁ (polyPath R.D R.ρ m T c c' n (kernelNodes R.D R.ρ m c c' n p e u))‖ ≤ ‖l₁‖ * (C₁ * b) :=
      (l₁.le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    have g2 : ‖l₂ (polyPath R.D R.ρ m T c c' n (kernelNodes R.D R.ρ m c c' n q e' u))‖ ≤ ‖l₂‖ * (C₁ * b) :=
      (l₂.le_opNorm _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    simp only [hf, norm_mul]
    exact mul_le_mul g1 g2 (norm_nonneg _) ((norm_nonneg _).trans g1)
  -- pointwise limit
  have hne : ∀ x : ℝ, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), u ≠ x := by
    intro x
    refine ae_restrict_of_ae ?_
    have := (Set.countable_singleton x).ae_notMem (volume : Measure ℝ)
    filter_upwards [this] with u hu
    simpa using hu
  have hlim : ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')), Tendsto (fun n => f n u) atTop (𝓝 (Lf u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne ta, hne tb] with u hu hua hub
    have A1 : Tendsto (fun n => l₁ (polyPath R.D R.ρ m T c c' n (kernelNodes R.D R.ρ m c c' n p e u))) atTop
        (𝓝 (p u * NegSobolev.eval (causalVec R.D R.ρ m ta u e) φa)) := by
      have h1 := S7PIDK_eval_tendsto hsa
        (S7PIDK_pathAt_tendsto R m hm T hT hc hlt hc' (p u) k hu hta hua)
      rw [S7PIDK_eval_smul] at h1
      simp only [hl₁]
      exact h1
    have A2 : Tendsto (fun n => l₂ (polyPath R.D R.ρ m T c c' n (kernelNodes R.D R.ρ m c c' n q e' u))) atTop
        (𝓝 (q u * NegSobolev.eval (causalVec R.D R.ρ m tb u e') φb)) := by
      have h1 := S7PIDK_eval_tendsto hsb
        (S7PIDK_pathAt_tendsto R m hm T hT hc hlt hc' (q u) l hu htb hub)
      rw [S7PIDK_eval_smul] at h1
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
      simp only [causalVec, if_neg hub, S7PIDK_eval_zero]
      ring
    · simp only [causalVec, if_neg hua, S7PIDK_eval_zero]
      ring

end HRS.MC.Sec7.S7PIDK

end
