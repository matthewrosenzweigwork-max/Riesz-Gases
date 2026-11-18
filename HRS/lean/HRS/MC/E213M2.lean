import HRS.MC.E213M1
import HRS.MC.S7PIDBMain

/-!
# Packet E213M2: family-quantified `s7_PID_nuc_bound` (Theorem 2.13, translation-uniform PI-D)

The constant `K` is chosen before the shift `b₀ ≥ 0`; the regimes are `E213F.shift R b₀ hb₀` at the fixed horizon `T`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213M

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDB

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
set_option maxSynthPendingDepth 3 in
theorem e213m_nucbound (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b₀ : ℝ, ∀ hb₀ : 0 ≤ b₀, ∀ (p q : ℝ → ℝ) (Bp Bq : ℝ), Measurable p → Measurable q → (∀ u, |p u| ≤ Bp) →
      (∀ u, |q u| ≤ Bq) → ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → ∀ (k l : NonzeroLattice d) (n : ℕ),
      ‖nuc (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m T c c' n (kernelNodes (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m c c' n p (modeVec m k))
          (kernelNodes (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m c c' n q (modeVec m l))‖ ≤
        K * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) ∧
      ‖nuc (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m T c c' (n + 1) (kernelNodes (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m c c' (n + 1) p (modeVec m k))
          (kernelNodes (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m c c' (n + 1) q (modeVec m l)) -
        nuc (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m T c c' n (kernelNodes (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m c c' n p (modeVec m k))
          (kernelNodes (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ m c c' n q (modeVec m l))‖ ≤
        K * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) *
          (2 : ℝ) ^ (-(n : ℝ) / 4) := by
  obtain ⟨K, hK0, htr⟩ := HRS.MC.E213M.e213m_trunc R m hm T hT
  refine ⟨K, hK0, fun b₀ hb₀ => ?_⟩
  have htr := htr b₀ hb₀
  set Rb := HRS.MC.E213F.shift R b₀ hb₀ with hRb
  intro p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l n
  have hBp : 0 ≤ Bp := (abs_nonneg _).trans (hpB 0)
  have hBq : 0 ≤ Bq := (abs_nonneg _).trans (hqB 0)
  by_cases hceq : c = c'
  · subst hceq
    have h0 : ∀ μ w w', nuc Rb.D Rb.ρ m T c c μ w w' = 0 := by
      intro μ w w'
      unfold nuc
      rw [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]
    simp [h0]
  have hlt : c < c' := lt_of_le_of_ne hcc hceq
  have hΔ0 : 0 < c' - c := sub_pos.2 hlt
  have hjk : 0 ≤ Lattice.jp k.1 := (Torus.jp_pos k.1).le
  have hjl : 0 ≤ Lattice.jp l.1 := (Torus.jp_pos l.1).le
  have hαk : 0 ≤ Lattice.jp k.1 ^ (-(m - 1)) := Real.rpow_nonneg hjk _
  have hαl : 0 ≤ Lattice.jp l.1 ^ (-(m - 1)) := Real.rpow_nonneg hjl _
  -- bounds and measurability of the kernel nodes
  obtain ⟨K₁, Cb, hK₁, hCb, hfam⟩ := HRS.MC.E213J.e213j_fam R m hm T hT
  obtain ⟨r, emb, G, -, hG1, hG0, hGc, -⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_vec' m (∅ : Finset (NonzeroLattice d))
  have hF := fun ν => hfam b₀ hb₀ G hG1 hG0 hGc p Bp hp hpB c c' hc hcc hc' k ν
  have hF' := fun ν => hfam b₀ hb₀ G hG1 hG0 hGc q Bq hq hqB c c' hc hcc hc' l ν
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = max (Bp * (Cb * ‖modeVec m k‖)) (Bq * (Cb * ‖modeVec m l‖)) := ⟨_, rfl⟩
  have hbd : ∀ ν, ∀ i ≤ 2 ^ ν, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')),
      ‖kernelNodes Rb.D Rb.ρ m c c' ν p (modeVec m k) u i‖ ≤ b := fun ν i hi =>
    (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu =>
      ((hF ν).2.2.2.2 i hi u hu).trans (hb ▸ le_max_left _ _))
  have hbd' : ∀ ν, ∀ i ≤ 2 ^ ν, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')),
      ‖kernelNodes Rb.D Rb.ρ m c c' ν q (modeVec m l) u i‖ ≤ b := fun ν i hi =>
    (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu =>
      ((hF' ν).2.2.2.2 i hi u hu).trans (hb ▸ le_max_right _ _))
  -- the limits `F → atTop`
  have hlim : ∀ (ν : ℕ) (M : PathSpace d m T [×2]→L[ℝ] ℝ),
      Tendsto (fun F : Finset (NonzeroLattice d) =>
        nuc Rb.D Rb.ρ m T c c' ν
          (fun u i => truncF m F (kernelNodes Rb.D Rb.ρ m c c' ν p (modeVec m k) u i))
          (fun u i => truncF m F (kernelNodes Rb.D Rb.ρ m c c' ν q (modeVec m l) u i)) M) atTop
        (𝓝 (nuc Rb.D Rb.ρ m T c c' ν (kernelNodes Rb.D Rb.ρ m c c' ν p (modeVec m k))
          (kernelNodes Rb.D Rb.ρ m c c' ν q (modeVec m l)) M)) := fun ν M =>
    S7PIDB_nuc_tendsto Rb m hm T hT c c' hc hlt hc' ν _ _ b
      (fun i hi => (hF ν).2.2.2.1 i hi) (fun i hi => (hF' ν).2.2.2.1 i hi) (hbd ν) (hbd' ν) M
  have hW0 : 0 ≤ K * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) := by
    positivity
  refine ⟨?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ hW0 fun M => ?_
    rw [Real.norm_eq_abs]
    refine le_trans ?_ (le_of_eq (mul_comm _ _))
    exact le_of_tendsto' (f := fun F : Finset (NonzeroLattice d) => |nuc Rb.D Rb.ρ m T c c' n
          (fun u i => truncF m F (kernelNodes Rb.D Rb.ρ m c c' n p (modeVec m k) u i))
          (fun u i => truncF m F (kernelNodes Rb.D Rb.ρ m c c' n q (modeVec m l) u i)) M|)
      (hlim n M).abs fun F => (htr p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l F n M).1
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun M => ?_
    rw [Real.norm_eq_abs, ContinuousLinearMap.sub_apply]
    refine le_trans ?_ (le_of_eq (mul_comm _ _))
    have hd := (hlim (n + 1) M).sub (hlim n M)
    exact le_of_tendsto' hd.abs fun F => by
      have := (htr p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l F n M).2
      simpa only [ContinuousLinearMap.sub_apply] using this

end HRS.MC.E213M

end
