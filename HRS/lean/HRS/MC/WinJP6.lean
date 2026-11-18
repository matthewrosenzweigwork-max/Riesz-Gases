import HRS.MC.WinJSpecDefs
import HRS.MC.WinJP4
import HRS.MC.WinJP5
import HRS.MC.S7PIDBLim

/-!
# WJ6: P6 `p6_nucbound_diff` (removal of the truncation in the nuclear bound for the difference)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

section P6

variable {d : ℕ}

/-- the truncated time-smoothed nuclear tensors converge to the full one as `F ↑ all`, for a shifted regime -/
lemma p_wj6_tendsto (R0 : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (b : ℝ) (hb : 0 ≤ b) (p q : ℝ → ℝ) (Bp Bq : ℝ) (hp : Measurable p) (hq : Measurable q)
    (hpB : ∀ u, |p u| ≤ Bp) (hqB : ∀ u, |q u| ≤ Bq) (c c' : ℝ) (hc : 0 ≤ c) (hlt : c < c')
    (hc' : c' ≤ T) (k l : NonzeroLattice d) (n : ℕ) (M : PathSpace d m T [×2]→L[ℝ] ℝ) :
    Tendsto (fun F : Finset (NonzeroLattice d) =>
        nucK (HRS.MC.E213F.shift R0 b hb) m T c c' n p q k l (truncF m F) M) atTop
      (𝓝 (nucK (HRS.MC.E213F.shift R0 b hb) m T c c' n p q k l id M)) := by
  obtain ⟨K₁, Cb, hK₁, hCb, hfam⟩ := HRS.MC.E213J.e213j_fam R0 m hm T hT
  obtain ⟨r, emb, G, -, hG1, hG0, hGc, -⟩ :=
    HRS.MC.Sec7.S7PIDT.S7PIDT_vec' m (∅ : Finset (NonzeroLattice d))
  have hc'0 : c ≤ c' := hlt.le
  have hF := fun ν => hfam b hb G hG1 hG0 hGc p Bp hp hpB c c' hc hc'0 hc' k ν
  have hF' := fun ν => hfam b hb G hG1 hG0 hGc q Bq hq hqB c c' hc hc'0 hc' l ν
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = max (Bp * (Cb * ‖modeVec m k‖)) (Bq * (Cb * ‖modeVec m l‖)) :=
    ⟨_, rfl⟩
  have hbd : ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')),
      ‖kernelNodes (HRS.MC.E213F.shift R0 b hb).D (HRS.MC.E213F.shift R0 b hb).ρ m c c' n p
        (modeVec m k) u i‖ ≤ β := fun i hi =>
    (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu =>
      ((hF n).2.2.2.2 i hi u hu).trans (hβ ▸ le_max_left _ _))
  have hbd' : ∀ i ≤ 2 ^ n, ∀ᵐ u ∂(volume.restrict (Set.Ioc c c')),
      ‖kernelNodes (HRS.MC.E213F.shift R0 b hb).D (HRS.MC.E213F.shift R0 b hb).ρ m c c' n q
        (modeVec m l) u i‖ ≤ β := fun i hi =>
    (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu =>
      ((hF' n).2.2.2.2 i hi u hu).trans (hβ ▸ le_max_right _ _))
  exact HRS.MC.Sec7.S7PIDB.S7PIDB_nuc_tendsto (HRS.MC.E213F.shift R0 b hb) m hm T hT c c' hc hlt hc' n _ _ β
    (fun i hi => (hF n).2.2.2.1 i hi) (fun i hi => (hF' n).2.2.2.1 i hi) hbd hbd' M

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

set_option maxHeartbeats 1600000 in
theorem p6_nucbound_diff (sd : StatDatum S β₀ m hE) (T : ℝ) (hT : 0 < T) :
    ∃ K κ : ℝ, 0 ≤ K ∧ 0 < κ ∧ ∀ (b : ℝ) (hb : 0 ≤ b) (p q : ℝ → ℝ) (Bp Bq : ℝ), Measurable p → Measurable q →
      (∀ u, |p u| ≤ Bp) → (∀ u, |q u| ≤ Bq) → ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T →
      ∀ (k l : NonzeroLattice d) (n : ℕ),
      ‖nucK (Rp sd b hb) m T c c' n p q k l id - nucK (Rs sd b hb) m T c c' n p q k l id‖ ≤
        K * Bp * Bq * Real.exp (-κ * b) * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) ∧
      ‖(nucK (Rp sd b hb) m T c c' (n + 1) p q k l id - nucK (Rs sd b hb) m T c c' (n + 1) p q k l id) -
          (nucK (Rp sd b hb) m T c c' n p q k l id - nucK (Rs sd b hb) m T c c' n p q k l id)‖ ≤
        K * Bp * Bq * Real.exp (-κ * b) * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) *
          (2 : ℝ) ^ (-(n : ℝ) / 4) := by
  obtain ⟨K, κ, hK, hκ, h5⟩ := p5_nuc_trunc_diff sd T hT
  refine ⟨K, κ, hK, hκ, ?_⟩
  intro b hb p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l n
  have hBp : 0 ≤ Bp := (abs_nonneg _).trans (hpB 0)
  have hBq : 0 ≤ Bq := (abs_nonneg _).trans (hqB 0)
  by_cases hceq : c = c'
  · subst hceq
    have h0 : ∀ (R : Regime d) (μ : ℕ), nucK R m T c c μ p q k l id = 0 := by
      intro R μ
      unfold nucK nuc
      rw [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]
    refine ⟨ContinuousLinearMap.opNorm_le_bound _ (by simp) fun M => ?_,
      ContinuousLinearMap.opNorm_le_bound _ (by simp) fun M => ?_⟩
    · simp [h0]
    · simp [h0]
  have hlt : c < c' := lt_of_le_of_ne hcc hceq
  have hΔ0 : 0 < c' - c := sub_pos.2 hlt
  have hjk : 0 ≤ Lattice.jp k.1 := (Torus.jp_pos k.1).le
  have hjl : 0 ≤ Lattice.jp l.1 := (Torus.jp_pos l.1).le
  have hαk : 0 ≤ Lattice.jp k.1 ^ (-(m - 1)) := Real.rpow_nonneg hjk _
  have hαl : 0 ≤ Lattice.jp l.1 ^ (-(m - 1)) := Real.rpow_nonneg hjl _
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hms : 3 * (d : ℝ) + 8 < m := sd.hEs.m_gt
  have hlim : ∀ (ν : ℕ) (M : PathSpace d m T [×2]→L[ℝ] ℝ),
      Tendsto (fun F : Finset (NonzeroLattice d) =>
        nucK (Rp sd b hb) m T c c' ν p q k l (truncF m F) M -
          nucK (Rs sd b hb) m T c c' ν p q k l (truncF m F) M) atTop
        (𝓝 (nucK (Rp sd b hb) m T c c' ν p q k l id M - nucK (Rs sd b hb) m T c c' ν p q k l id M)) :=
    fun ν M =>
    (p_wj6_tendsto (regime S β₀ hE) m hm T hT b hb p q Bp Bq hp hq hpB hqB c c' hc hlt hc' k l ν M).sub
      (p_wj6_tendsto (regime sd.Ss S.β sd.hEs) m hms T hT b hb p q Bp Bq hp hq hpB hqB c c' hc hlt hc'
        k l ν M)
  have hW0 : 0 ≤ K * Bp * Bq * Real.exp (-κ * b) * Lattice.jp k.1 ^ (-(m - 1)) *
      Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) := by positivity
  refine ⟨?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ hW0 fun M => ?_
    rw [sub_apply, Real.norm_eq_abs]
    refine le_trans ?_ (le_of_eq (mul_comm _ _))
    exact le_of_tendsto' (hlim n M).abs fun F => (h5 b hb p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l F n M).1
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun M => ?_
    rw [Real.norm_eq_abs]
    simp only [sub_apply]
    refine le_trans ?_ (le_of_eq (mul_comm _ _))
    have hd := (hlim (n + 1) M).sub (hlim n M)
    refine le_of_tendsto' hd.abs fun F => ?_
    have := (h5 b hb p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l F n M).2
    exact this

end P6

end HRS.MC.WinJ

end
