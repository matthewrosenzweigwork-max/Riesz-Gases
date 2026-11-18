import HRS.MC.E213J1
import HRS.MC.E213J3
import HRS.MC.S7PIDTFam

/-!
# Packet E213J4: family-quantified `S7PIDT_fam` (Theorem 2.13, translation-uniform PI-D)

The constants `K₁ = L² G + Am²` and `Cb` are chosen before the shift `b ≥ 0`; the regimes are `E213F.shift R b hb` at the
fixed horizon `G`.  (The coordinate map, called `G` in `S7PIDT_fam`, is called `Φ` here.)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213J

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDT

variable {d : ℕ}

theorem e213j_fam (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) :
    ∃ K₁ Cb : ℝ, 0 ≤ K₁ ∧ 0 ≤ Cb ∧ ∀ b : ℝ, ∀ hb : 0 ≤ b,
      ∀ {r : ℕ} (Φ : NegSobolev d m → EuclideanSpace ℝ (Fin r)),
      (∀ a b, ‖Φ a - Φ b‖ ≤ ‖a - b‖) → (∀ a, ‖Φ a‖ ≤ ‖a‖) → Continuous Φ →
      ∀ (p : ℝ → ℝ) (B : ℝ), Measurable p → (∀ u, |p u| ≤ B) →
      ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ G → ∀ (k : NonzeroLattice d) (ν : ℕ),
        (∀ i ≤ 2 ^ ν, MemLp (fun u => Φ (kernelNodes (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ
            m c c' ν p (modeVec m k) u i)) 2 (volume.restrict (Set.Ioc c c'))) ∧
        (∀ i j, i ≤ j → j ≤ 2 ^ ν →
          ∫ u in Set.Ioc c c', ‖Φ (kernelNodes (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ
                m c c' ν p (modeVec m k) u j) -
              Φ (kernelNodes (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ
                m c c' ν p (modeVec m k) u i)‖ ^ 2 ≤
            K₁ * B ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) * (gridPt c c' ν j - gridPt c c' ν i)) ∧
        (∀ i ≤ 2 ^ ν, ∫ u in Set.Ioc c c', ‖Φ (kernelNodes (HRS.MC.E213F.shift R b hb).D
              (HRS.MC.E213F.shift R b hb).ρ m c c' ν p (modeVec m k) u i)‖ ^ 2 ≤
            K₁ * B ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) * (c' - c)) ∧
        (∀ i ≤ 2 ^ ν, AEStronglyMeasurable (fun u => kernelNodes (HRS.MC.E213F.shift R b hb).D
              (HRS.MC.E213F.shift R b hb).ρ m c c' ν p (modeVec m k) u i)
            (volume.restrict (Set.Ioc c c'))) ∧
        (∀ i ≤ 2 ^ ν, ∀ u ∈ Set.Ioc c c', ‖kernelNodes (HRS.MC.E213F.shift R b hb).D
              (HRS.MC.E213F.shift R b hb).ρ m c c' ν p (modeVec m k) u i‖ ≤
            B * (Cb * ‖modeVec m k‖)) := by
  obtain ⟨K₁, hK₁, hinc⟩ := e213j_incr R m hm G hG
  obtain ⟨Cb, hCb0, hker⟩ := e213j_ker R m hm G hG
  refine ⟨K₁, Cb, hK₁, hCb0, fun b₀ hb₀ {r} Φ hΦ1 hΦ0 hΦc p B hp hpB c c' hc hcc hc' k ν => ?_⟩
  set Rb := HRS.MC.E213F.shift R b₀ hb₀ with hRb
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hpB 0)
  set e := modeVec m k with he
  -- measurability and bound of the kernel nodes
  have hmeas : ∀ i ≤ 2 ^ ν, AEStronglyMeasurable (fun u => kernelNodes Rb.D Rb.ρ m c c' ν p e u i)
      (volume.restrict (Set.Ioc c c')) := by
    intro i hi
    obtain ⟨h1, h2⟩ := S7PIDT_grid_mem c c' hcc ν i hi
    exact hp.aestronglyMeasurable.smul (hker b₀ hb₀ c c' hc hcc hc' e _ h1 h2).1
  have hbd : ∀ i ≤ 2 ^ ν, ∀ u ∈ Set.Ioc c c', ‖kernelNodes Rb.D Rb.ρ m c c' ν p e u i‖ ≤ B * (Cb * ‖e‖) := by
    intro i hi u hu
    obtain ⟨h1, h2⟩ := S7PIDT_grid_mem c c' hcc ν i hi
    unfold kernelNodes
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hpB u) ((hker b₀ hb₀ c c' hc hcc hc' e _ h1 h2).2 u hu) (norm_nonneg _) hB0
  have hmem : ∀ i ≤ 2 ^ ν, MemLp (fun u => Φ (kernelNodes Rb.D Rb.ρ m c c' ν p e u i)) 2
      (volume.restrict (Set.Ioc c c')) := by
    intro i hi
    refine MemLp.of_bound (hΦc.comp_aestronglyMeasurable (hmeas i hi)) (B * (Cb * ‖e‖)) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    exact (hΦ0 _).trans (hbd i hi u hu)
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
    have hinc' := (hinc b₀ hb₀ p B hp hpB c c' hc hcc hc' k _ _ hi1 hst hj2).1
    have hlhs : Integrable (fun u => ‖Φ (kernelNodes Rb.D Rb.ρ m c c' ν p e u j) -
        Φ (kernelNodes Rb.D Rb.ρ m c c' ν p e u i)‖ ^ 2) (volume.restrict (Set.Ioc c c')) :=
      ((hmem j hj).sub (hmem i hi)).norm.integrable_sq
    have hrhs : Integrable (fun u => ‖p u • causalVec Rb.D Rb.ρ m (gridPt c c' ν j) u e -
        p u • causalVec Rb.D Rb.ρ m (gridPt c c' ν i) u e‖ ^ 2) (volume.restrict (Set.Ioc c c')) := by
      have hm' : AEStronglyMeasurable (fun u => kernelNodes Rb.D Rb.ρ m c c' ν p e u j -
          kernelNodes Rb.D Rb.ρ m c c' ν p e u i) (volume.restrict (Set.Ioc c c')) :=
        (hmeas j hj).sub (hmeas i hi)
      have hmem' : MemLp (fun u => kernelNodes Rb.D Rb.ρ m c c' ν p e u j -
          kernelNodes Rb.D Rb.ρ m c c' ν p e u i) 2 (volume.restrict (Set.Ioc c c')) := by
        refine MemLp.of_bound hm' (B * (Cb * ‖e‖) + B * (Cb * ‖e‖)) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
        exact (norm_sub_le _ _).trans (add_le_add (hbd j hj u hu) (hbd i hi u hu))
      exact hmem'.norm.integrable_sq
    refine le_trans (integral_mono hlhs hrhs (fun u => ?_)) hinc'
    show ‖Φ (kernelNodes Rb.D Rb.ρ m c c' ν p e u j) - Φ (kernelNodes Rb.D Rb.ρ m c c' ν p e u i)‖ ^ 2 ≤
      ‖p u • causalVec Rb.D Rb.ρ m (gridPt c c' ν j) u e - p u • causalVec Rb.D Rb.ρ m (gridPt c c' ν i) u e‖ ^ 2
    exact pow_le_pow_left₀ (norm_nonneg _) (hΦ1 _ _) 2
  · intro i hi
    obtain ⟨hi1, hi2⟩ := S7PIDT_grid_mem c c' hcc ν i hi
    have hinc' := (hinc b₀ hb₀ p B hp hpB c c' hc hcc hc' k _ _ hi1 le_rfl hi2).2
    have hlhs : Integrable (fun u => ‖Φ (kernelNodes Rb.D Rb.ρ m c c' ν p e u i)‖ ^ 2)
        (volume.restrict (Set.Ioc c c')) := (hmem i hi).norm.integrable_sq
    have hrhs : Integrable (fun u => ‖p u • causalVec Rb.D Rb.ρ m (gridPt c c' ν i) u e‖ ^ 2)
        (volume.restrict (Set.Ioc c c')) := by
      have hmem' : MemLp (fun u => kernelNodes Rb.D Rb.ρ m c c' ν p e u i) 2
          (volume.restrict (Set.Ioc c c')) := by
        refine MemLp.of_bound (hmeas i hi) (B * (Cb * ‖e‖)) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
        exact hbd i hi u hu
      exact hmem'.norm.integrable_sq
    refine le_trans (integral_mono hlhs hrhs (fun u => ?_)) hinc'
    show ‖Φ (kernelNodes Rb.D Rb.ρ m c c' ν p e u i)‖ ^ 2 ≤
      ‖p u • causalVec Rb.D Rb.ρ m (gridPt c c' ν i) u e‖ ^ 2
    exact pow_le_pow_left₀ (norm_nonneg _) (hΦ0 _) 2

end HRS.MC.E213J

end
