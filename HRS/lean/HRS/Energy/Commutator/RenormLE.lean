import HRS.Energy.Commutator.RenormAI

/-!
# Route S, packet S4: local energy lemma (LE)

For a finite signed measure `f = s m` (`|s| ≤ 1`, neutral for `l = 0`) of finite `G_l`-energy, the field
`F = w_l * f` satisfies `‖F‖²_{L²(T^d)} ≤ ∬ G_l df df`.

Proof: heat-regularise, `hk_ε ⋆ F = e^{lε} ∇H_ε` with `H_ε = G_{l,ε} * f` smooth, the energy identity of
`RoughMain`, the `L¹` approximate identity (`RenormAI`) and Fatou.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux HRS.Commutator.FourierAux HRS.Commutator.RoughAux HRS.Commutator.RoughHeat
  HRS.Commutator.RoughLimit

namespace HRS.Commutator.Renorm

variable {d : ℕ}

/-- The `j`-th component of the field `w_l * (s m)`. -/
def Fj (l : ℝ) (m : Measure (Torus d)) (s : Torus d → ℝ) (j : Fin d) (x : Torus d) : ℝ :=
  ∫ z, s z * SliceAux.sgc j l (x - z) ∂m

theorem integrable_conv_swap {φ : Torus d → ℝ} (hφm : Measurable φ) (hφ : Integrable φ volume)
    (m : Measure (Torus d)) [IsFiniteMeasure m] :
    Integrable (fun p : Torus d × Torus d => φ (p.2 - p.1)) (m.prod volume) := by
  have hm : Measurable fun p : Torus d × Torus d => φ (p.2 - p.1) :=
    hφm.comp (measurable_snd.sub measurable_fst)
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun z => hφ.comp_sub_right z, ?_⟩
  have : (fun z : Torus d => ∫ y, ‖φ (y - z)‖ ∂(volume : Measure (Torus d))) = fun _ => ∫ y, ‖φ y‖ := by
    funext z
    exact integral_sub_right_eq_self (fun y => ‖φ y‖) z
  show Integrable (fun z : Torus d => ∫ y, ‖φ (y - z)‖ ∂(volume : Measure (Torus d))) m
  rw [this]
  exact integrable_const _

/-- `hk_ε ⋆ F_j = e^{lε} ∂_j H_ε`. -/
theorem cv_Fj {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) (j : Fin d) (x : Torus d) :
    cv ε (Fj l m s j) x = Real.exp (l * ε) *
      Torus.partialDeriv j (convS (ser (cW l ε)) m s) x := by
  rw [RoughMain.grad_formula hl hε m hsm hs j x]
  rw [← mul_assoc, ← Real.exp_add]
  simp only [add_neg_cancel, Real.exp_zero, one_mul]
  unfold cv Fj convS
  obtain ⟨M, hM⟩ := hk_bdd (d := d) hε
  have hsg := RoughKernel.integrable_sgc (d := d) j hl
  have hsgm : Measurable (SliceAux.sgc j l : Torus d → ℝ) := (SliceAux.measurable_sgc j).comp (measurable_const.prodMk measurable_id)
  -- integrability on `m × vol`
  have hI : Integrable (fun p : Torus d × Torus d => SliceAux.sgc j l (p.2 - p.1)) (m.prod volume) :=
    integrable_conv_swap hsgm hsg m
  have hB : Integrable (fun p : Torus d × Torus d => |SliceAux.sgc j l (p.2 - p.1)|) (m.prod volume) := hI.abs
  -- LHS: swap
  have hL : Integrable (fun p : Torus d × Torus d => hk ε (x - p.2) * (s p.1 * SliceAux.sgc j l (p.2 - p.1)))
      (m.prod volume) := by
    refine Integrable.mono' (hB.const_mul M) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (((continuous_hk hε).measurable.comp (measurable_const.sub measurable_snd)).mul
        ((hsm.comp measurable_fst).mul (hsgm.comp (measurable_snd.sub measurable_fst)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hk_nonneg hε _)]
      have h1 := hs p.1
      have h2 : hk ε (x - p.2) ≤ M := hM _
      calc hk ε (x - p.2) * (|s p.1| * |SliceAux.sgc j l (p.2 - p.1)|)
          ≤ M * (1 * |SliceAux.sgc j l (p.2 - p.1)|) := by
            refine mul_le_mul h2 (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) (by positivity) ((hk_nonneg hε _).trans h2)
        _ = M * |SliceAux.sgc j l (p.2 - p.1)| := by ring
  have hR : Integrable (fun p : Torus d × Torus d =>
      SliceAux.sgc j l p.2 * (hk ε (x - p.2 - p.1) * s p.1)) (m.prod volume) := by
    have hB2 : Integrable (fun p : Torus d × Torus d => |SliceAux.sgc j l p.2|) (m.prod volume) :=
      hsg.abs.comp_snd (μ := m)
    refine Integrable.mono' (hB2.const_mul M) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((hsgm.comp measurable_snd).mul (((continuous_hk hε).measurable.comp
        ((measurable_const.sub measurable_snd).sub measurable_fst)).mul (hsm.comp measurable_fst))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hk_nonneg hε _)]
      have h1 := hs p.1
      have h2 : hk ε (x - p.2 - p.1) ≤ M := hM _
      calc |SliceAux.sgc j l p.2| * (hk ε (x - p.2 - p.1) * |s p.1|)
          ≤ |SliceAux.sgc j l p.2| * (M * 1) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul h2 h1 (abs_nonneg _) ((hk_nonneg hε _).trans h2)) (abs_nonneg _)
        _ = M * |SliceAux.sgc j l p.2| := by ring
  have swapL := integral_integral_swap (μ := m) (ν := volume)
    (f := fun z y => hk ε (x - y) * (s z * SliceAux.sgc j l (y - z))) hL
  have swapR := integral_integral_swap (μ := m) (ν := volume)
    (f := fun z u => SliceAux.sgc j l u * (hk ε (x - u - z) * s z)) hR
  have eL : ∀ y, hk ε (x - y) * ∫ z, s z * SliceAux.sgc j l (y - z) ∂m =
      ∫ z, hk ε (x - y) * (s z * SliceAux.sgc j l (y - z)) ∂m := fun y => (integral_const_mul _ _).symm
  have eR : ∀ u, SliceAux.sgc j l u * ∫ y, ser (aW ε) (x - u - y) * s y ∂m =
      ∫ z, SliceAux.sgc j l u * (hk ε (x - u - z) * s z) ∂m := fun u => (integral_const_mul _ _).symm
  simp_rw [eL, eR]
  rw [← swapL, ← swapR]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only []
  have e1 : ∫ y, hk ε (x - y) * (s z * SliceAux.sgc j l (y - z)) =
      s z * ∫ y, hk ε (x - y) * SliceAux.sgc j l (y - z) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []; ring
  have e2 : ∫ u, SliceAux.sgc j l u * (hk ε (x - u - z) * s z) =
      s z * ∫ u, SliceAux.sgc j l u * hk ε (x - u - z) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only []; ring
  rw [e1, e2]
  congr 1
  have := integral_add_right_eq_self (μ := (volume : Measure (Torus d)))
    (fun y => hk ε (x - y) * SliceAux.sgc j l (y - z)) z
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [add_sub_cancel_right, sub_add_eq_sub_sub]
  ring


/-- The level-`ε` energy inequality for the mollified field. -/
theorem level_energy {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) (hneut : l = 0 → ∫ y, s y ∂m = 0) :
    ∫ x, ∑ j, (cv ε (Fj l m s j) x) ^ 2 ≤
      ∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l ε (p.1 - p.2) ∂(m.prod m) := by
  set H := convS (ser (cW l ε)) m s with hH
  set ρ := convS (ser (aW ε)) m s with hρ
  have hcG := RoughMain.cW_gauss (d := d) hl hε
  have hH2 : Torus.IsCk 2 H := by
    obtain ⟨ε', C, hε', hC⟩ := hcG
    exact isCk_convS 2 hε' hC (cW_even l ε) m hsm hs
  have hHc : Continuous H :=
    continuous_convS (continuous_ser (GaussDecay.summable hcG)) m hsm hs
  have hcv : ∀ j x, cv ε (Fj l m s j) x = Real.exp (l * ε) * Torus.partialDeriv j H x :=
    fun j x => cv_Fj hl hε m hsm hs j x
  have hgreen : ∀ x, l * H x - Torus.laplacian H x = Real.exp (-l * ε) * ρ x := fun x =>
    green_identity hl hε m hsm hs hneut x
  -- rewrite the integrand
  have e1 : ∀ x, ∑ j, (cv ε (Fj l m s j) x) ^ 2 = Real.exp (2 * (l * ε)) * ‖Torus.grad H x‖ ^ 2 := by
    intro x
    have h1 := StressAux.norm_grad_sq H x
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcv j x, mul_pow, ← Real.exp_nat_mul]
    ring_nf
  simp_rw [e1]
  have hgradc : Integrable (fun x => ‖Torus.grad H x‖ ^ 2) (volume : Measure (Torus d)) := by
    have hnorm := StressAux.norm_grad_sq H
    simp_rw [hnorm]
    have hw1 : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j H) := fun j => PDE.isCk_one_partialDeriv j H hH2
    have hwc : ∀ j, Continuous (Torus.partialDeriv j H) := fun j =>
      PDE.continuous_partialDeriv j H (hH2.of_le (by norm_num))
    exact integrable_finsetSum _ fun j _ => StressAux.int_of_cont ((hwc j).mul (hwc j))
  rw [integral_const_mul]
  have hE := energy_by_parts hH2 l
  have hrhs : ∫ x, H x * (l * H x - Torus.laplacian H x) = Real.exp (-l * ε) * ∫ x, H x * ρ x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hgreen x]; ring)
  have hside := RoughMain.energy_side hl hε m hsm hs
  have hHi : Integrable (fun x => l * H x ^ 2) (volume : Measure (Torus d)) :=
    StressAux.int_of_cont (continuous_const.mul (hHc.pow 2))
  have hle : ∫ x, ‖Torus.grad H x‖ ^ 2 ≤ ∫ x, (l * H x ^ 2 + ‖Torus.grad H x‖ ^ 2) := by
    refine integral_mono hgradc (hHi.add hgradc) fun x => ?_
    have : 0 ≤ l * H x ^ 2 := by positivity
    linarith
  rw [hE, hrhs] at hle
  have hside' : ∫ x, H x * ρ x = Real.exp (-(l * ε)) * ∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l ε (p.1 - p.2) ∂(m.prod m) := hside
  rw [hside'] at hle
  have e2 : Real.exp (2 * (l * ε)) * (Real.exp (-l * ε) * (Real.exp (-(l * ε)) * ∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l ε (p.1 - p.2) ∂(m.prod m))) =
      ∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l ε (p.1 - p.2) ∂(m.prod m) := by
    rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    have : 2 * (l * ε) + -l * ε + -(l * ε) = 0 := by ring
    rw [this, Real.exp_zero, one_mul]
  calc Real.exp (2 * (l * ε)) * ∫ x, ‖Torus.grad H x‖ ^ 2 ≤
        Real.exp (2 * (l * ε)) * (Real.exp (-l * ε) * (Real.exp (-(l * ε)) * ∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l ε (p.1 - p.2) ∂(m.prod m))) :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = _ := e2


/-- The limit of the level-`ε` energies. -/
theorem Ehat_limit {l : ℝ} (hl : 0 ≤ l) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1)
    (hint : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (m.prod m))
    (hgood : ∀ᵐ p ∂(m.prod m), IntW l (p.1 - p.2)) :
    Tendsto (fun ε : ℝ => ∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l ε (p.1 - p.2) ∂(m.prod m))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p : Torus d × Torus d, s p.1 * s p.2 * sliceGfull d l (p.1 - p.2) ∂(m.prod m))) := by
  obtain ⟨Kc, hKc, hlow⟩ := Ehat_lower d
  set Gf : Torus d × Torus d → ℝ := fun p => sliceGfull d l (p.1 - p.2) with hGf
  have hint' : Integrable Gf (m.prod m) := hint
  have hss : ∀ p : Torus d × Torus d, |s p.1 * s p.2| ≤ 1 := fun p => by
    rw [abs_mul]; exact mul_le_one₀ (hs _) (abs_nonneg _) (hs _)
  have hssm : Measurable fun p : Torus d × Torus d => s p.1 * s p.2 :=
    (hsm.comp measurable_fst).mul (hsm.comp measurable_snd)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun p => Real.exp (2 * l) * |Gf p| + 2 + Kc) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hssm.mul ((RoughMain.measurable_Ehat hl hε).comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
    filter_upwards [hgood] with p hp
    have hε0 : 0 < ε := hε.1
    rw [Real.norm_eq_abs, abs_mul]
    have h2 := Ehat_upper hl hp hε0
    have h4 := hlow l hl (p.1 - p.2) hp ε hε0
    have h3 : Real.exp (2 * l * ε) * sliceGfull d l (p.1 - p.2) ≤ Real.exp (2 * l) * |Gf p| := by
      calc Real.exp (2 * l * ε) * sliceGfull d l (p.1 - p.2) ≤ Real.exp (2 * l * ε) * |Gf p| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le
        _ ≤ Real.exp (2 * l) * |Gf p| :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hl (sub_nonneg.mpr hε.2.le)]))
              (abs_nonneg _)
    have hE : |Ehat l ε (p.1 - p.2)| ≤ Real.exp (2 * l) * |Gf p| + 2 + Kc := by
      rw [abs_le]
      constructor
      · have : 0 ≤ Real.exp (2 * l) * |Gf p| := by positivity
        linarith
      · have : 2 * ε ≤ 2 := by linarith [hε.2]
        linarith
    calc |s p.1 * s p.2| * |Ehat l ε (p.1 - p.2)| ≤ 1 * (Real.exp (2 * l) * |Gf p| + 2 + Kc) :=
          mul_le_mul (hss p) hE (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  · exact ((hint'.abs.const_mul _).add (integrable_const (2 : ℝ))).add (integrable_const Kc)
  · filter_upwards [hgood] with p hp
    exact (Ehat_tendsto hl hp).const_mul (s p.1 * s p.2)


theorem Fj_measurable {l : ℝ} (m : Measure (Torus d)) [IsFiniteMeasure m] {s : Torus d → ℝ}
    (hsm : Measurable s) (j : Fin d) : Measurable (Fj l m s j) := by
  have hg : Measurable fun p : Torus d × Torus d => s p.2 * SliceAux.sgc j l (p.1 - p.2) :=
    (hsm.comp measurable_snd).mul ((SliceAux.measurable_sgc j).comp (measurable_const.prodMk (measurable_fst.sub measurable_snd)))
  exact (hg.stronglyMeasurable.integral_prod_right' (ν := m)).measurable

theorem Fj_integrable {l : ℝ} (hl : 0 ≤ l) (m : Measure (Torus d)) [IsFiniteMeasure m] {s : Torus d → ℝ}
    (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) (j : Fin d) : Integrable (Fj l m s j) volume := by
  have hsgm : Measurable (SliceAux.sgc j l : Torus d → ℝ) :=
    (SliceAux.measurable_sgc j).comp (measurable_const.prodMk measurable_id)
  have hI := integrable_conv_swap hsgm (RoughKernel.integrable_sgc (d := d) j hl) m
  have hf : Integrable (fun p : Torus d × Torus d => s p.1 * SliceAux.sgc j l (p.2 - p.1)) (m.prod volume) := by
    refine Integrable.mono' hI.abs ((hsm.comp measurable_fst).mul (hsgm.comp (measurable_snd.sub measurable_fst))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |s p.1| * |SliceAux.sgc j l (p.2 - p.1)| ≤ 1 * |SliceAux.sgc j l (p.2 - p.1)| :=
          mul_le_mul_of_nonneg_right (hs _) (abs_nonneg _)
      _ = _ := one_mul _
  exact hf.integral_prod_right

theorem cv_Fj_continuous {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) (j : Fin d) :
    Continuous (cv ε (Fj l m s j)) := by
  have hcG := RoughMain.cW_gauss (d := d) hl hε
  have hH2 : Torus.IsCk 2 (convS (ser (cW l ε)) m s) := by
    obtain ⟨ε', C, hε', hC⟩ := hcG
    exact isCk_convS 2 hε' hC (cW_even l ε) m hsm hs
  have hc : Continuous (Torus.partialDeriv j (convS (ser (cW l ε)) m s)) :=
    PDE.continuous_partialDeriv j _ (hH2.of_le (by norm_num))
  have : cv ε (Fj l m s j) = fun x => Real.exp (l * ε) * Torus.partialDeriv j (convS (ser (cW l ε)) m s) x :=
    funext fun x => cv_Fj hl hε m hsm hs j x
  rw [this]
  exact continuous_const.mul hc

theorem local_energy {l : ℝ} (hl : 0 ≤ l) (m : Measure (Torus d)) [IsFiniteMeasure m]
    {s : Torus d → ℝ} (hsm : Measurable s) (hs : ∀ y, |s y| ≤ 1) (hneut : l = 0 → ∫ y, s y ∂m = 0)
    (hint : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (m.prod m))
    (hgood : ∀ᵐ p ∂(m.prod m), IntW l (p.1 - p.2)) :
    Integrable (fun x => ∑ j, (Fj l m s j x) ^ 2) volume ∧
    ∫ x, ∑ j, (Fj l m s j x) ^ 2 ≤ ∫ p : Torus d × Torus d, s p.1 * s p.2 * sliceGfull d l (p.1 - p.2) ∂(m.prod m) := by
  set R : ℝ := ∫ p : Torus d × Torus d, s p.1 * s p.2 * sliceGfull d l (p.1 - p.2) ∂(m.prod m) with hR
  have hFm : ∀ j, Measurable (Fj l m s j) := fun j => Fj_measurable m hsm j
  have hFi : ∀ j, Integrable (Fj l m s j) volume := fun j => Fj_integrable hl m hsm hs j
  -- the sequence of regularisations
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [hεdef]; positivity
  have hεlim : Tendsto ε atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall hεpos⟩
  -- the approximants
  set D : ℕ → Torus d → ℝ := fun n x => ∑ j, |cv (ε n) (Fj l m s j) x - Fj l m s j x| with hD
  have hDint : ∀ n, Integrable (D n) volume := by
    intro n
    refine integrable_finsetSum _ fun j _ => ?_
    have hcv : Integrable (cv (ε n) (Fj l m s j)) volume :=
      (integrable_cv_prod (hFm j) (hFi j) (hεpos n)).integral_prod_left
    exact (hcv.sub (hFi j)).abs
  have hDlim : Tendsto (fun n => ∫ x, D n x) atTop (𝓝 0) := by
    have h1 : ∀ j : Fin d, Tendsto (fun n => ∫ x, |cv (ε n) (Fj l m s j) x - Fj l m s j x|) atTop (𝓝 0) :=
      fun j => (cv_L1 (hFm j) (hFi j)).comp hεlim
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun j _ => h1 j)
    simp only [Finset.sum_const_zero] at h2
    refine h2.congr fun n => ?_
    simp only [hD]
    rw [integral_finsetSum]
    intro j _
    have hcv : Integrable (cv (ε n) (Fj l m s j)) volume :=
      (integrable_cv_prod (hFm j) (hFi j) (hεpos n)).integral_prod_left
    exact (hcv.sub (hFi j)).abs
  -- convergence in measure and an a.e. convergent subsequence
  have hDnn : ∀ n x, 0 ≤ D n x := fun n x => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hmeasD : TendstoInMeasure (volume : Measure (Torus d)) D atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero ?_
    have e : ∀ n, eLpNorm (D n - fun _ => (0 : ℝ)) 1 volume = ENNReal.ofReal (∫ x, D n x) := by
      intro n
      have e0 : D n - (fun _ => (0 : ℝ)) = D n := by
        funext x; simp only [Pi.sub_apply, sub_zero]
      rw [e0, eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hDint n)]
      · congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [Real.norm_eq_abs, abs_of_nonneg (hDnn n x)]
      · exact (hDint n).aestronglyMeasurable
    simp_rw [e]
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hDlim
    rw [ENNReal.ofReal_zero] at this
    exact this
  obtain ⟨ns, hns, hae⟩ := hmeasD.exists_seq_tendsto_ae
  have hcvx : ∀ᵐ x ∂(volume : Measure (Torus d)), ∀ j, Tendsto (fun i => cv (ε (ns i)) (Fj l m s j) x) atTop
      (𝓝 (Fj l m s j x)) := by
    filter_upwards [hae] with x hx j
    have hle : ∀ i, |cv (ε (ns i)) (Fj l m s j) x - Fj l m s j x| ≤ D (ns i) x := fun i =>
      Finset.single_le_sum (f := fun j => |cv (ε (ns i)) (Fj l m s j) x - Fj l m s j x|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have h0 := squeeze_zero (fun i => abs_nonneg _) hle hx
    exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa [Real.norm_eq_abs] using h0)
  -- Fatou
  set f : ℕ → Torus d → ℝ≥0∞ := fun i x => ENNReal.ofReal (∑ j, (cv (ε (ns i)) (Fj l m s j) x) ^ 2) with hf
  have hcont : ∀ i j, Continuous (cv (ε (ns i)) (Fj l m s j)) := fun i j =>
    cv_Fj_continuous hl (hεpos _) m hsm hs j
  have hfm : ∀ i, Measurable (f i) := fun i =>
    ENNReal.measurable_ofReal.comp (continuous_finsetSum _ fun j _ => (hcont i j).pow 2).measurable
  have hlim : ∀ᵐ x ∂(volume : Measure (Torus d)),
      Tendsto (fun i => f i x) atTop (𝓝 (ENNReal.ofReal (∑ j, (Fj l m s j x) ^ 2))) := by
    filter_upwards [hcvx] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_finsetSum _ fun j _ => (hx j).pow 2)
  have hEi : Tendsto (fun i => ∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l (ε (ns i)) (p.1 - p.2) ∂(m.prod m))
      atTop (𝓝 R) :=
    (Ehat_limit hl m hsm hs hint hgood).comp (hεlim.comp hns.tendsto_atTop)
  have hint_i : ∀ i, ∫⁻ x, f i x ∂(volume : Measure (Torus d)) ≤
      ENNReal.ofReal (∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l (ε (ns i)) (p.1 - p.2) ∂(m.prod m)) := by
    intro i
    have hI : Integrable (fun x => ∑ j, (cv (ε (ns i)) (Fj l m s j) x) ^ 2) (volume : Measure (Torus d)) :=
      StressAux.int_of_cont (continuous_finsetSum _ fun j _ => (hcont i j).pow 2)
    have hnn : 0 ≤ᵐ[volume] fun x => ∑ j, (cv (ε (ns i)) (Fj l m s j) x) ^ 2 :=
      Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
    rw [hf]
    simp only []
    rw [← ofReal_integral_eq_lintegral_ofReal hI hnn]
    exact ENNReal.ofReal_le_ofReal (level_energy hl (hεpos _) m hsm hs hneut)
  have hR0 : 0 ≤ R := by
    refine ge_of_tendsto hEi (Filter.Eventually.of_forall fun i => ?_)
    refine le_trans ?_ (level_energy hl (hεpos _) m hsm hs hneut)
    exact integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hfat : ∫⁻ x, ENNReal.ofReal (∑ j, (Fj l m s j x) ^ 2) ≤ ENNReal.ofReal R := by
    have h1 : ∫⁻ x, ENNReal.ofReal (∑ j, (Fj l m s j x) ^ 2) = ∫⁻ x, liminf (fun i => f i x) atTop := by
      refine lintegral_congr_ae ?_
      filter_upwards [hlim] with x hx
      exact hx.liminf_eq.symm
    rw [h1]
    refine (lintegral_liminf_le hfm).trans ?_
    have h2 : Tendsto (fun i => ENNReal.ofReal (∫ p : Torus d × Torus d, s p.1 * s p.2 * Ehat l (ε (ns i)) (p.1 - p.2) ∂(m.prod m)))
        atTop (𝓝 (ENNReal.ofReal R)) := (ENNReal.continuous_ofReal.tendsto _).comp hEi
    refine (liminf_le_liminf (Filter.Eventually.of_forall hint_i)).trans (le_of_eq h2.liminf_eq)
  -- conclusion
  have hgm : Measurable fun x => ∑ j, (Fj l m s j x) ^ 2 :=
    Finset.measurable_sum _ fun j _ => (hFm j).pow_const 2
  have hnn : 0 ≤ᵐ[volume] fun x => ∑ j, (Fj l m s j x) ^ 2 :=
    Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hfin : Integrable (fun x => ∑ j, (Fj l m s j x) ^ 2) volume := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hfat ENNReal.ofReal_lt_top
  refine ⟨hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hgm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hR0 hfat


/-- Explicit form of `RoughReduce.reduce`. -/
theorem reduce_explicit {α : Type*} [MeasurableSpace α] {ν μ : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure μ] :
    ∃ a : α → ℝ, Measurable a ∧ (∀ y, 0 ≤ a y ∧ a y ≤ 1) ∧
      (∀ g : α → ℝ, ∫ y, g y ∂ν = ∫ y, a y * g y ∂(ν + μ)) ∧
      (∀ g : α → ℝ, ∫ y, g y ∂μ = ∫ y, (1 - a y) * g y ∂(ν + μ)) ∧
      ∀ K : α → α → ℝ, Measurable (Function.uncurry K) → (∀ x y, K x y = K y x) →
        Integrable (Function.uncurry K) ((ν + μ).prod (ν + μ)) →
        (∫ x, ∫ y, K x y ∂ν ∂ν) - 2 * (∫ x, ∫ y, K x y ∂μ ∂ν) + (∫ x, ∫ y, K x y ∂μ ∂μ) =
          ∫ p : α × α, (a p.1 - (1 - a p.1)) * (a p.2 - (1 - a p.2)) * K p.1 p.2 ∂((ν + μ).prod (ν + μ)) := by
  obtain ⟨a, ham, ha01, hνa, hμa⟩ := RoughReduce.exists_density ν μ
  set m : Measure α := ν + μ with hm
  refine ⟨a, ham, ha01, hνa, hμa, ?_⟩
  intro K hKm hKs hKi
  set b : α → ℝ := fun y => 1 - a y with hb
  have hbm : Measurable b := measurable_const.sub ham
  have ha1 : ∀ y, |a y| ≤ 1 := fun y => by rw [abs_of_nonneg (ha01 y).1]; exact (ha01 y).2
  have hb1 : ∀ y, |b y| ≤ 1 := fun y => by
    simp only [hb]; rw [abs_of_nonneg (by linarith [(ha01 y).2])]; linarith [(ha01 y).1]
  have hI := fun (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g) (h1 : ∀ y, |f y| ≤ 1)
    (h2 : ∀ y, |g y| ≤ 1) => RoughReduce.integrable_phi hKm hKi hf hg h1 h2
  -- iterated form of the pairing
  have hiter : ∀ (f g : α → ℝ), Measurable f → Measurable g → (∀ y, |f y| ≤ 1) → (∀ y, |g y| ≤ 1) →
      ∫ x, f x * (∫ y, g y * K x y ∂m) ∂m = ∫ p : α × α, f p.1 * g p.2 * K p.1 p.2 ∂(m.prod m) := by
    intro f g hf hg h1 h2
    rw [integral_prod _ (hI f g hf hg h1 h2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  have T11 : ∫ x, ∫ y, K x y ∂ν ∂ν = ∫ x, a x * (∫ y, a y * K x y ∂m) ∂m := by
    have e : ∀ x, ∫ y, K x y ∂ν = ∫ y, a y * K x y ∂m := fun x => hνa _
    simp_rw [e]
    exact hνa (fun x => ∫ y, a y * K x y ∂m)
  have T12 : ∫ x, ∫ y, K x y ∂μ ∂ν = ∫ x, a x * (∫ y, b y * K x y ∂m) ∂m := by
    have e : ∀ x, ∫ y, K x y ∂μ = ∫ y, b y * K x y ∂m := fun x => hμa _
    simp_rw [e]
    exact hνa (fun x => ∫ y, b y * K x y ∂m)
  have T22 : ∫ x, ∫ y, K x y ∂μ ∂μ = ∫ x, b x * (∫ y, b y * K x y ∂m) ∂m := by
    have e : ∀ x, ∫ y, K x y ∂μ = ∫ y, b y * K x y ∂m := fun x => hμa _
    simp_rw [e]
    exact hμa (fun x => ∫ y, b y * K x y ∂m)
  rw [T11, T12, T22, hiter a a ham ham ha1 ha1, hiter a b ham hbm ha1 hb1, hiter b b hbm hbm hb1 hb1]
  -- symmetry of the pairing
  have hsym : ∫ p : α × α, b p.1 * a p.2 * K p.1 p.2 ∂(m.prod m) =
      ∫ p : α × α, a p.1 * b p.2 * K p.1 p.2 ∂(m.prod m) := by
    rw [← integral_prod_swap (fun p : α × α => a p.1 * b p.2 * K p.1 p.2)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [hKs p.2 p.1]; ring)
  have hex : ∀ p : α × α, (a p.1 - b p.1) * (a p.2 - b p.2) * K p.1 p.2 =
      a p.1 * a p.2 * K p.1 p.2 - a p.1 * b p.2 * K p.1 p.2 - b p.1 * a p.2 * K p.1 p.2 +
        b p.1 * b p.2 * K p.1 p.2 := fun p => by ring
  have hI1 := hI a a ham ham ha1 ha1
  have hI2 := hI a b ham hbm ha1 hb1
  have hI3 := hI b a hbm ham hb1 ha1
  have hI4 := hI b b hbm hbm hb1 hb1
  set F1 : α × α → ℝ := fun p => a p.1 * a p.2 * K p.1 p.2 with hF1
  set F2 : α × α → ℝ := fun p => a p.1 * b p.2 * K p.1 p.2 with hF2
  set F3 : α × α → ℝ := fun p => b p.1 * a p.2 * K p.1 p.2 with hF3
  set F4 : α × α → ℝ := fun p => b p.1 * b p.2 * K p.1 p.2 with hF4
  have hs : ∫ p : α × α, (a p.1 - (1 - a p.1)) * (a p.2 - (1 - a p.2)) * K p.1 p.2 ∂(m.prod m) =
      ∫ p, F1 p ∂(m.prod m) - ∫ p, F2 p ∂(m.prod m) - ∫ p, F3 p ∂(m.prod m) + ∫ p, F4 p ∂(m.prod m) := by
    have e : (fun p : α × α => (a p.1 - (1 - a p.1)) * (a p.2 - (1 - a p.2)) * K p.1 p.2) =
        F1 - F2 - F3 + F4 := by
      funext p; simp only [hF1, hF2, hF3, hF4, hb, Pi.add_apply, Pi.sub_apply]; ring
    rw [e, integral_add' ((hI1.sub hI2).sub hI3) hI4, integral_sub' (hI1.sub hI2) hI3, integral_sub' hI1 hI2]
  rw [hs, hsym]
  ring



/-- Local energy for a pair of finite measures. -/
theorem LE_measures (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) (ν μ : Measure (Torus d)) [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] (hneut : l = 0 → ν Set.univ = μ Set.univ)
    (hatom : 2 ≤ d → (∀ x, ν {x} = 0) ∧ ∀ x, μ {x} = 0)
    (hint : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) ((ν + μ).prod (ν + μ))) :
    Integrable (fun x => ∑ j, ((∫ z, SliceAux.sgc j l (x - z) ∂ν) - ∫ z, SliceAux.sgc j l (x - z) ∂μ) ^ 2) volume ∧
    ∫ x, ∑ j, ((∫ z, SliceAux.sgc j l (x - z) ∂ν) - ∫ z, SliceAux.sgc j l (x - z) ∂μ) ^ 2 ≤
      quadForm (fun x y => sliceGfull d l (x - y)) ν μ := by
  obtain ⟨a, ham, ha01, hνa, hμa, hred⟩ := reduce_explicit (ν := ν) (μ := μ)
  set m : Measure (Torus d) := ν + μ with hm
  set s : Torus d → ℝ := fun y => a y - (1 - a y) with hsdef
  have hsm : Measurable s := ham.sub (measurable_const.sub ham)
  have hs : ∀ y, |s y| ≤ 1 := fun y => by
    have := ha01 y
    simp only [hsdef]; rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hai : Integrable a m := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ham.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (ha01 y).1]; exact (ha01 y).2
  have hsint : ∫ y, s y ∂m = ν.real Set.univ - μ.real Set.univ := by
    have h1 : ν.real Set.univ = ∫ y, a y ∂m := by
      have := hνa (fun _ => (1 : ℝ)); simpa [Measure.real] using this
    have h2 : μ.real Set.univ = ∫ y, (1 - a y) ∂m := by
      have := hμa (fun _ => (1 : ℝ)); simpa [Measure.real] using this
    rw [h1, h2]
    simp only [hsdef]
    have hb : Integrable (fun y => 1 - a y) m := (integrable_const (1 : ℝ)).sub hai
    exact integral_sub hai hb
  have hneut' : l = 0 → ∫ y, s y ∂m = 0 := by
    intro h0
    rw [hsint]
    simp only [Measure.real, hneut h0, sub_self]
  have hgood : ∀ᵐ p ∂(m.prod m), IntW l (p.1 - p.2) := by
    rcases (by omega : d = 1 ∨ 2 ≤ d) with rfl | h2
    · exact Filter.Eventually.of_forall fun p => RoughD1.d1_intW hl _
    · obtain ⟨h1, h2'⟩ := hatom h2
      have hm0 : ∀ x, m {x} = 0 := fun x => by
        simp only [hm, Measure.add_apply, h1 x, h2' x, add_zero]
      filter_upwards [RoughFinal.ae_ne_of_noAtoms m hm0] with p hp
      exact intW_of_ne_zero hl (sub_ne_zero.mpr hp)
  obtain ⟨hI, hle⟩ := local_energy hl m hsm hs hneut' hint hgood
  have hGm : Measurable (Function.uncurry fun x y : Torus d => sliceGfull d l (x - y)) :=
    (EnergyAux.measurable_sliceGfull l).comp (measurable_fst.sub measurable_snd)
  have hGs : ∀ x y : Torus d, sliceGfull d l (x - y) = sliceGfull d l (y - x) := fun x y => by
    unfold sliceGfull
    rw [show y - x = -(x - y) by abel, EnergyAux.sliceG_neg]
  have hQ := hred (fun x y => sliceGfull d l (x - y)) hGm hGs hint
  -- the a.e. identification of the two fields
  have hae : ∀ᵐ x ∂(volume : Measure (Torus d)), ∀ j, Fj l m s j x =
      (∫ z, SliceAux.sgc j l (x - z) ∂ν) - ∫ z, SliceAux.sgc j l (x - z) ∂μ := by
    rw [ae_all_iff]
    intro j
    have hsgm : Measurable (SliceAux.sgc j l : Torus d → ℝ) :=
      (SliceAux.measurable_sgc j).comp (measurable_const.prodMk measurable_id)
    have hI2 := integrable_conv_swap hsgm (RoughKernel.integrable_sgc (d := d) j hl) m
    filter_upwards [hI2.prod_left_ae] with x hx
    unfold Fj
    have hg : Integrable (fun z => SliceAux.sgc j l (x - z)) m := hx
    have hgm : Measurable fun z => SliceAux.sgc j l (x - z) := hsgm.comp (measurable_const.sub measurable_id)
    rw [hνa, hμa]
    have h1 : Integrable (fun z => a z * SliceAux.sgc j l (x - z)) m := by
      refine Integrable.mono' hg.norm (ham.mul hgm).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha01 z).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (ha01 z).2 |>.trans (le_of_eq (by simp [Real.norm_eq_abs]))
    have h2 : Integrable (fun z => (1 - a z) * SliceAux.sgc j l (x - z)) m := by
      refine Integrable.mono' hg.norm ((measurable_const.sub ham).mul hgm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [(ha01 z).2])]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [(ha01 z).1]) |>.trans (le_of_eq (by simp [Real.norm_eq_abs]))
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hsdef]; ring
  have e1 : (fun x => ∑ j, (Fj l m s j x) ^ 2) =ᵐ[volume] fun x => ∑ j, ((∫ z, SliceAux.sgc j l (x - z) ∂ν) -
      ∫ z, SliceAux.sgc j l (x - z) ∂μ) ^ 2 := by
    filter_upwards [hae] with x hx
    exact Finset.sum_congr rfl fun j _ => by rw [hx j]
  refine ⟨hI.congr e1, ?_⟩
  rw [← integral_congr_ae e1]
  refine hle.trans (le_of_eq ?_)
  unfold quadForm
  rw [hQ]

end HRS.Commutator.Renorm
