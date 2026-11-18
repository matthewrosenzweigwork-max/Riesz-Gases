import HRS.MC.S7PIDTKer
import HRS.MC.S7PIDTVec

/-!
# Packet PI-D, sub-packet T (part 9): the coordinate families of kernel nodes

For a `1`-Lipschitz coordinate map `G : E_m → ℝ^r` the functions `g_i(u) = G(p(u) · 1_{u ≤ t_i} V^{t_i,u} e_k)` are in
`L²(c,c']`, with `∫ ‖g_j - g_i‖² ≤ K₁ B_p² ⟨k⟩^{-2(m-1)} (t_j - t_i)` and `∫ ‖g_i‖² ≤ K₁ B_p² ⟨k⟩^{-2(m-1)} (c'-c)`
(from `s7_PID_incr_proof`, after proving the measurability and the boundedness of the kernel in `u`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

lemma S7PIDT_grid_mem (c c' : ℝ) (hcc : c ≤ c') (ν i : ℕ) (hi : i ≤ 2 ^ ν) :
    c ≤ gridPt c c' ν i ∧ gridPt c c' ν i ≤ c' := by
  have h2 : (0 : ℝ) < 2 ^ ν := by positivity
  have hi' : (i : ℝ) ≤ 2 ^ ν := by exact_mod_cast hi
  unfold gridPt
  constructor
  · have : 0 ≤ (c' - c) * i / 2 ^ ν := by
      apply div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) h2.le
    linarith
  · have : (c' - c) * i / 2 ^ ν ≤ c' - c := by
      rw [div_le_iff₀ h2]
      nlinarith [mul_le_mul_of_nonneg_left hi' (sub_nonneg.2 hcc)]
    linarith

lemma S7PIDT_grid_sub (c c' : ℝ) (ν i j : ℕ) :
    gridPt c c' ν j - gridPt c c' ν i = (c' - c) * ((j : ℝ) - i) / 2 ^ ν := by
  unfold gridPt; ring

theorem S7PIDT_fam (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ K₁ Cb : ℝ, 0 ≤ K₁ ∧ 0 ≤ Cb ∧ ∀ {r : ℕ} (G : NegSobolev d m → EuclideanSpace ℝ (Fin r)),
      (∀ a b, ‖G a - G b‖ ≤ ‖a - b‖) → (∀ a, ‖G a‖ ≤ ‖a‖) → Continuous G →
      ∀ (p : ℝ → ℝ) (B : ℝ), Measurable p → (∀ u, |p u| ≤ B) →
      ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → ∀ (k : NonzeroLattice d) (ν : ℕ),
        (∀ i ≤ 2 ^ ν, MemLp (fun u => G (kernelNodes R.D R.ρ m c c' ν p (modeVec m k) u i)) 2
            (volume.restrict (Set.Ioc c c'))) ∧
        (∀ i j, i ≤ j → j ≤ 2 ^ ν →
          ∫ u in Set.Ioc c c', ‖G (kernelNodes R.D R.ρ m c c' ν p (modeVec m k) u j) -
              G (kernelNodes R.D R.ρ m c c' ν p (modeVec m k) u i)‖ ^ 2 ≤
            K₁ * B ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) * (gridPt c c' ν j - gridPt c c' ν i)) ∧
        (∀ i ≤ 2 ^ ν, ∫ u in Set.Ioc c c', ‖G (kernelNodes R.D R.ρ m c c' ν p (modeVec m k) u i)‖ ^ 2 ≤
            K₁ * B ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) * (c' - c)) ∧
        (∀ i ≤ 2 ^ ν, AEStronglyMeasurable (fun u => kernelNodes R.D R.ρ m c c' ν p (modeVec m k) u i)
            (volume.restrict (Set.Ioc c c'))) ∧
        (∀ i ≤ 2 ^ ν, ∀ u ∈ Set.Ioc c c', ‖kernelNodes R.D R.ρ m c c' ν p (modeVec m k) u i‖ ≤
            B * (Cb * ‖modeVec m k‖)) := by
  obtain ⟨K₁, hK₁, hinc⟩ := S7PIDI.s7_PID_incr_proof R m hm T hT
  obtain ⟨Cb, hCb0, hker⟩ := S7PIDT_ker R m hm T hT
  refine ⟨K₁, Cb, hK₁, hCb0, fun {r} G hG1 hG0 hGc p B hp hpB c c' hc hcc hc' k ν => ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hpB 0)
  set e := modeVec m k with he
  -- measurability and bound of the kernel nodes
  have hmeas : ∀ i ≤ 2 ^ ν, AEStronglyMeasurable (fun u => kernelNodes R.D R.ρ m c c' ν p e u i)
      (volume.restrict (Set.Ioc c c')) := by
    intro i hi
    obtain ⟨h1, h2⟩ := S7PIDT_grid_mem c c' hcc ν i hi
    exact hp.aestronglyMeasurable.smul (hker c c' hc hcc hc' e _ h1 h2).1
  have hbd : ∀ i ≤ 2 ^ ν, ∀ u ∈ Set.Ioc c c', ‖kernelNodes R.D R.ρ m c c' ν p e u i‖ ≤ B * (Cb * ‖e‖) := by
    intro i hi u hu
    obtain ⟨h1, h2⟩ := S7PIDT_grid_mem c c' hcc ν i hi
    unfold kernelNodes
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hpB u) ((hker c c' hc hcc hc' e _ h1 h2).2 u hu) (norm_nonneg _) hB0
  have hmem : ∀ i ≤ 2 ^ ν, MemLp (fun u => G (kernelNodes R.D R.ρ m c c' ν p e u i)) 2
      (volume.restrict (Set.Ioc c c')) := by
    intro i hi
    refine MemLp.of_bound (hGc.comp_aestronglyMeasurable (hmeas i hi)) (B * (Cb * ‖e‖)) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    exact (hG0 _).trans (hbd i hi u hu)
  refine ⟨hmem, ?_, ?_, hmeas, hbd⟩
  · intro i j hij hj
    have hi : i ≤ 2 ^ ν := hij.trans hj
    obtain ⟨hi1, hi2⟩ := S7PIDT_grid_mem c c' hcc ν i hi
    obtain ⟨hj1, hj2⟩ := S7PIDT_grid_mem c c' hcc ν j hj
    have hst : gridPt c c' ν i ≤ gridPt c c' ν j := by
      have := S7PIDT_grid_sub c c' ν i j
      have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      have h0 : 0 ≤ (c' - c) * ((j : ℝ) - i) / 2 ^ ν :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      linarith
    have hinc' := (hinc p B hp hpB c c' hc hcc hc' k _ _ hi1 hst hj2).1
    have hlhs : Integrable (fun u => ‖G (kernelNodes R.D R.ρ m c c' ν p e u j) -
        G (kernelNodes R.D R.ρ m c c' ν p e u i)‖ ^ 2) (volume.restrict (Set.Ioc c c')) :=
      ((hmem j hj).sub (hmem i hi)).norm.integrable_sq
    have hrhs : Integrable (fun u => ‖p u • causalVec R.D R.ρ m (gridPt c c' ν j) u e -
        p u • causalVec R.D R.ρ m (gridPt c c' ν i) u e‖ ^ 2) (volume.restrict (Set.Ioc c c')) := by
      have hm' : AEStronglyMeasurable (fun u => kernelNodes R.D R.ρ m c c' ν p e u j -
          kernelNodes R.D R.ρ m c c' ν p e u i) (volume.restrict (Set.Ioc c c')) :=
        (hmeas j hj).sub (hmeas i hi)
      have hmem' : MemLp (fun u => kernelNodes R.D R.ρ m c c' ν p e u j -
          kernelNodes R.D R.ρ m c c' ν p e u i) 2 (volume.restrict (Set.Ioc c c')) := by
        refine MemLp.of_bound hm' (B * (Cb * ‖e‖) + B * (Cb * ‖e‖)) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
        exact (norm_sub_le _ _).trans (add_le_add (hbd j hj u hu) (hbd i hi u hu))
      exact hmem'.norm.integrable_sq
    refine le_trans (integral_mono hlhs hrhs (fun u => ?_)) hinc'
    show ‖G (kernelNodes R.D R.ρ m c c' ν p e u j) - G (kernelNodes R.D R.ρ m c c' ν p e u i)‖ ^ 2 ≤
      ‖p u • causalVec R.D R.ρ m (gridPt c c' ν j) u e - p u • causalVec R.D R.ρ m (gridPt c c' ν i) u e‖ ^ 2
    exact pow_le_pow_left₀ (norm_nonneg _) (hG1 _ _) 2
  · intro i hi
    obtain ⟨hi1, hi2⟩ := S7PIDT_grid_mem c c' hcc ν i hi
    have hinc' := (hinc p B hp hpB c c' hc hcc hc' k _ _ hi1 le_rfl hi2).2
    have hlhs : Integrable (fun u => ‖G (kernelNodes R.D R.ρ m c c' ν p e u i)‖ ^ 2)
        (volume.restrict (Set.Ioc c c')) := (hmem i hi).norm.integrable_sq
    have hrhs : Integrable (fun u => ‖p u • causalVec R.D R.ρ m (gridPt c c' ν i) u e‖ ^ 2)
        (volume.restrict (Set.Ioc c c')) := by
      have hmem' : MemLp (fun u => kernelNodes R.D R.ρ m c c' ν p e u i) 2
          (volume.restrict (Set.Ioc c c')) := by
        refine MemLp.of_bound (hmeas i hi) (B * (Cb * ‖e‖)) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
        exact hbd i hi u hu
      exact hmem'.norm.integrable_sq
    refine le_trans (integral_mono hlhs hrhs (fun u => ?_)) hinc'
    show ‖G (kernelNodes R.D R.ρ m c c' ν p e u i)‖ ^ 2 ≤
      ‖p u • causalVec R.D R.ρ m (gridPt c c' ν i) u e‖ ^ 2
    exact pow_le_pow_left₀ (norm_nonneg _) (hG0 _) 2

end HRS.MC.Sec7.S7PIDT

end
