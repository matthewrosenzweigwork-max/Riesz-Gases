import HRS.Whole.AppendixAAdjoint
import HRS.Commutator.Whole.RieszAux

/-!
# SYM-LIN, part 1: the odd symmetrisation of the truncated odd linear kernel

Packet SYM-LIN (CZ development), kernel side.  Notation: `symlin_K d θ i z = z_i / |z|^{d+θ}` is the kernel
of `pvOdd d θ (fun u => u i)` (`Ω(z/|z|)/|z|^{d+θ-1}` with `Ω(u) = u_i`).

For `d ≥ 1`, `0 < θ < 2` and a real Schwartz function `Z`, the odd symmetrisation
`(Z(x-z) - Z(x+z))/2` is `O(|z|)`, so `z ↦ symlin_K z * (Z(x-z) - Z(x+z))/2` is absolutely integrable
(`|z|^{2-d-θ}` near `0`, since `θ < 2`), the truncations `∫_{ε<|z|} K(z) Z(x-z) dz` equal the truncated
symmetrised integrals, and the `limUnder` of the frozen `pvOdd` is the absolutely convergent integral
(`symlin_pvOdd_eq`).  Everything is stated with explicit hypotheses `0 < θ < 2`, `1 ≤ d`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.Sym

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the odd linear kernel `z_i / |z|^{d+θ}` -/
def symlin_K (d : ℕ) (θ : ℝ) (i : Fin d) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  z i / ‖z‖ ^ ((d : ℝ) + θ)

lemma symlin_K_neg (θ : ℝ) (i : Fin d) (z : 𝔼) : symlin_K d θ i (-z) = - symlin_K d θ i z := by
  simp [symlin_K, neg_div]

lemma symlin_K_zero (θ : ℝ) (i : Fin d) : symlin_K d θ i 0 = 0 := by
  simp [symlin_K]

lemma symlin_K_measurable (θ : ℝ) (i : Fin d) : Measurable (symlin_K d θ i) := by
  unfold symlin_K
  exact ((EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).continuous.measurable).div
    (measurable_norm.pow_const _)

lemma symlin_K_abs_le (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) (i : Fin d) (z : 𝔼) :
    |symlin_K d θ i z| ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by
  by_cases hz : z = 0
  · subst hz
    rw [symlin_K_zero, abs_zero]
    exact Real.rpow_nonneg (norm_nonneg _) _
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [symlin_K, abs_div, abs_of_pos (Real.rpow_pos_of_pos hn _), Real.rpow_sub hn, Real.rpow_one]
    gcongr
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z i

lemma symlin_one_sub_nonpos (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) : 1 - ((d : ℝ) + θ) ≤ 0 := by
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- `|K(z)| · C|z| ≤ C |z|^{2-d-θ}` -/
lemma symlin_K_mul_le (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) (i : Fin d) (z : 𝔼) {C : ℝ} (hC : 0 ≤ C) :
    |symlin_K d θ i z| * (C * ‖z‖) ≤ C * ‖z‖ ^ (2 - ((d : ℝ) + θ)) := by
  by_cases hz : z = 0
  · subst hz
    rw [symlin_K_zero, abs_zero, zero_mul]
    exact mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have h1 := symlin_K_abs_le hd hθ i z
    calc |symlin_K d θ i z| * (C * ‖z‖) ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) * (C * ‖z‖) := by gcongr
      _ = C * (‖z‖ ^ (1 - ((d : ℝ) + θ)) * ‖z‖) := by ring
      _ = C * ‖z‖ ^ (2 - ((d : ℝ) + θ)) := by
          congr 1
          have : (2 : ℝ) - ((d : ℝ) + θ) = (1 - ((d : ℝ) + θ)) + 1 := by ring
          rw [this, Real.rpow_add hn, Real.rpow_one]

/-- integrability of `K · h` for `h` integrable with `‖h z‖ ≤ C ‖z‖` -/
lemma symlin_integrable_K_smul (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : 𝔼 → F}
    (hm : AEStronglyMeasurable h volume) (hint : Integrable h) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖h z‖ ≤ C * ‖z‖) :
    Integrable (fun z => symlin_K d θ i z • h z) := by
  have hloc : IntegrableOn (fun z : 𝔼 => ‖z‖ ^ (2 - ((d : ℝ) + θ))) (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume)
      (f := fun z : 𝔼 => ‖z‖ ^ (2 - ((d : ℝ) + θ)))
      (C := 1) (α := (d : ℝ) + θ - 2) (r := 1) (by rw [finrank_euclideanSpace_fin]; exact hd) ?_ ?_ ?_
    · rw [finrank_euclideanSpace_fin]; linarith
    · exact Eventually.of_forall fun x => by
        rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
        apply le_of_eq
        congr 1
        ring
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  have hind : Integrable (Set.indicator (ball (0 : 𝔼) 1) fun z : 𝔼 => ‖z‖ ^ (2 - ((d : ℝ) + θ))) :=
    (integrable_indicator_iff measurableSet_ball).2 hloc
  refine Integrable.mono' ((hind.const_mul C).add hint.norm) ?_ (Eventually.of_forall fun z => ?_)
  · exact ((symlin_K_measurable θ i).aestronglyMeasurable).smul hm
  · rw [norm_smul, Real.norm_eq_abs]
    by_cases hz : z ∈ ball (0 : 𝔼) 1
    · have h1 := symlin_K_mul_le hd hθ0 i z hC0
      have h2 : |symlin_K d θ i z| * ‖h z‖ ≤ |symlin_K d θ i z| * (C * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hC z) (abs_nonneg _)
      have h3 : (Set.indicator (ball (0 : 𝔼) 1) fun z : 𝔼 => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z =
          ‖z‖ ^ (2 - ((d : ℝ) + θ)) := Set.indicator_of_mem hz _
      show _ ≤ C * (Set.indicator (ball (0 : 𝔼) 1) fun z : 𝔼 => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z + ‖h z‖
      rw [h3]
      linarith [norm_nonneg (h z)]
    · have hx1 : 1 ≤ ‖z‖ := by
        simpa only [mem_ball, dist_zero_right, not_lt] using hz
      have hK : |symlin_K d θ i z| ≤ 1 :=
        (symlin_K_abs_le hd hθ0 i z).trans
          (Real.rpow_le_one_of_one_le_of_nonpos hx1 (symlin_one_sub_nonpos hd hθ0))
      have h3 : (Set.indicator (ball (0 : 𝔼) 1) fun z : 𝔼 => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z = 0 :=
        Set.indicator_of_notMem hz _
      show _ ≤ C * (Set.indicator (ball (0 : 𝔼) 1) fun z : 𝔼 => ‖z‖ ^ (2 - ((d : ℝ) + θ))) z + ‖h z‖
      rw [h3, mul_zero, zero_add]
      calc |symlin_K d θ i z| * ‖h z‖ ≤ 1 * ‖h z‖ := by gcongr
        _ = ‖h z‖ := one_mul _

/-- a Schwartz function is globally Lipschitz -/
lemma symlin_schwartz_lip {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : 𝓢(𝔼, F)) : ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : 𝔼, ‖Z a - Z b‖ ≤ M * ‖a - b‖ := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ 𝔼 F Z), by positivity, fun a b => ?_⟩
  have hb : ∀ x ∈ (Set.univ : Set 𝔼), ‖fderiv ℝ Z x‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ 𝔼 F Z) := fun x _ => by
    have := SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.fderivCLM ℝ 𝔼 F Z) x
    simpa using this
  have := (convex_univ : Convex ℝ (Set.univ : Set 𝔼)).norm_image_sub_le_of_norm_fderiv_le
    (f := Z) (fun x _ => Z.differentiableAt) hb (mem_univ b) (mem_univ a)
  simpa using this

lemma symlin_sym_bound (Z : 𝓢(𝔼, ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x z : 𝔼, ‖(Z (x - z) - Z (x + z)) / 2‖ ≤ M * ‖z‖ := by
  obtain ⟨M, hM0, hM⟩ := symlin_schwartz_lip Z
  refine ⟨M, hM0, fun x z => ?_⟩
  have h1 := hM (x - z) (x + z)
  have h2 : ‖(x - z) - (x + z)‖ = 2 * ‖z‖ := by
    have : (x - z) - (x + z) = (-(2 : ℝ)) • z := by
      rw [neg_smul, two_smul]; abel
    rw [this, norm_smul]; simp
  rw [h2] at h1
  rw [norm_div, Real.norm_two]
  linarith

lemma symlin_integrable_sym (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    Integrable (fun z : 𝔼 => symlin_K d θ i z * ((Z (x - z) - Z (x + z)) / 2)) := by
  obtain ⟨M, hM0, hM⟩ := symlin_sym_bound Z
  have hc : Continuous (fun z : 𝔼 => (Z (x - z) - Z (x + z)) / 2) :=
    ((Z.continuous.comp (continuous_const.sub continuous_id)).sub
      (Z.continuous.comp (continuous_const.add continuous_id))).div_const 2
  have hi : Integrable (fun z : 𝔼 => (Z (x - z) - Z (x + z)) / 2) :=
    ((Z.integrable.comp_sub_left x).sub (Z.integrable.comp_add_left x)).div_const 2
  have h := symlin_integrable_K_smul hd hθ0 hθ2 i hc.aestronglyMeasurable hi hM0 (fun z => hM x z)
  simpa [smul_eq_mul] using h

lemma symlin_integrableOn_trunc (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (i : Fin d) (Z : 𝓢(𝔼, ℝ))
    (x : 𝔼) (a : 𝔼 → 𝔼) {ε : ℝ} (hε : 0 < ε) (ha : Continuous a)
    (hai : Integrable (fun z : 𝔼 => Z (a z))) :
    IntegrableOn (fun z : 𝔼 => symlin_K d θ i z * Z (a z)) {z : 𝔼 | ε < ‖z‖} := by
  have hS : MeasurableSet {z : 𝔼 | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  refine Integrable.mono' (g := fun z => ε ^ (1 - ((d : ℝ) + θ)) * ‖Z (a z)‖)
    (hai.norm.const_mul _).integrableOn ?_ ?_
  · exact ((symlin_K_measurable θ i).aestronglyMeasurable.mul
      (Z.continuous.comp ha).aestronglyMeasurable).restrict
  · refine (ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_)
    have hz' : ε < ‖z‖ := hz
    rw [norm_mul, Real.norm_eq_abs]
    have h1 := symlin_K_abs_le hd hθ0 i z
    have h2 : ‖z‖ ^ (1 - ((d : ℝ) + θ)) ≤ ε ^ (1 - ((d : ℝ) + θ)) :=
      Real.rpow_le_rpow_of_nonpos hε hz'.le (symlin_one_sub_nonpos hd hθ0)
    gcongr
    exact h1.trans h2

lemma symlin_trunc_eq (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (i : Fin d) (Z : 𝓢(𝔼, ℝ)) (x : 𝔼)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ z in {z : 𝔼 | ε < ‖z‖}, symlin_K d θ i z * Z (x - z) =
      ∫ z in {z : 𝔼 | ε < ‖z‖}, symlin_K d θ i z * ((Z (x - z) - Z (x + z)) / 2) := by
  set S : Set 𝔼 := {z : 𝔼 | ε < ‖z‖} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hf : IntegrableOn (fun z : 𝔼 => symlin_K d θ i z * Z (x - z)) S :=
    symlin_integrableOn_trunc hd hθ0 i Z x (fun z => x - z) hε (continuous_const.sub continuous_id)
      (Z.integrable.comp_sub_left x)
  have hg : IntegrableOn (fun z : 𝔼 => symlin_K d θ i z * Z (x + z)) S :=
    symlin_integrableOn_trunc hd hθ0 i Z x (fun z => x + z) hε (continuous_const.add continuous_id)
      (Z.integrable.comp_add_left x)
  have hneg : ∫ z in S, symlin_K d θ i z * Z (x + z) = -∫ z in S, symlin_K d θ i z * Z (x - z) := by
    rw [← integral_indicator hS, ← integral_indicator hS]
    have key := integral_neg_eq_self (fun z => S.indicator (fun z => symlin_K d θ i z * Z (x - z)) z)
      volume
    rw [← key, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : z ∈ S
    · have hz' : -z ∈ S := by
        simpa [hSdef] using hz
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz', symlin_K_neg, sub_neg_eq_add]
      ring
    · have hz' : -z ∉ S := by
        simpa [hSdef] using hz
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
      simp
  have hpt : ∀ z : 𝔼, symlin_K d θ i z * ((Z (x - z) - Z (x + z)) / 2) =
      (symlin_K d θ i z * Z (x - z) - symlin_K d θ i z * Z (x + z)) / 2 := fun z => by ring
  simp_rw [hpt]
  rw [integral_div, integral_sub hf hg, hneg]
  ring

lemma symlin_tendsto_trunc (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    Tendsto (fun ε : ℝ => ∫ z in {z : 𝔼 | ε < ‖z‖},
        symlin_K d θ i z * ((Z (x - z) - Z (x + z)) / 2)) (𝓝[>] 0)
      (𝓝 (∫ z, symlin_K d θ i z * ((Z (x - z) - Z (x + z)) / 2))) := by
  set g : 𝔼 → ℝ := fun z => symlin_K d θ i z * ((Z (x - z) - Z (x + z)) / 2) with hg
  have hgi : Integrable g := symlin_integrable_sym hd hθ0 hθ2 i Z x
  have hS : ∀ ε : ℝ, MeasurableSet {z : 𝔼 | ε < ‖z‖} := fun ε =>
    measurableSet_lt measurable_const measurable_norm
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε : ℝ => Set.indicator {z : 𝔼 | ε < ‖z‖} g) (f := g) (fun z => ‖g z‖)
    (Eventually.of_forall fun ε => hgi.aestronglyMeasurable.indicator (hS ε))
    (Eventually.of_forall fun ε => ae_of_all _ fun z => by
      by_cases hz : z ∈ {z : 𝔼 | ε < ‖z‖}
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]; simp)
    hgi.norm
    (ae_of_all _ fun z => by
      by_cases hz : z = 0
      · subst hz
        have h0 : g 0 = 0 := by simp [hg, symlin_K_zero]
        refine tendsto_const_nhds.congr (fun ε => ?_)
        simp [Set.indicator_apply, h0]
      · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hn] with ε hε
        rw [Set.indicator_of_mem (show z ∈ {z : 𝔼 | ε < ‖z‖} from hε.2)])
  refine h.congr (fun ε => ?_)
  rw [integral_indicator (hS ε)]

theorem symlin_pvOdd_eq (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) x =
      ∫ z, symlin_K d θ i z * ((Z (x - z) - Z (x + z)) / 2) := by
  unfold HRS.Whole.AppendixA.pvOdd
  have hlim := symlin_tendsto_trunc hd hθ0 hθ2 i Z x
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ z in {z : 𝔼 | ε < ‖z‖}, symlin_K d θ i z * ((Z (x - z) - Z (x + z)) / 2) =
      ∫ z in {z : 𝔼 | ε < ‖z‖}, (fun u : 𝔼 => u i) (‖z‖⁻¹ • z) /
        ‖z‖ ^ ((d : ℝ) + θ - 1) * Z (x - z) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hS : MeasurableSet {z : 𝔼 | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
    rw [← symlin_trunc_eq hd hθ0 i Z x (show (0 : ℝ) < ε from hε)]
    refine setIntegral_congr_fun hS (fun z hz => ?_)
    have hz' : ε < ‖z‖ := hz
    have hn : 0 < ‖z‖ := lt_trans hε hz'
    simp only [symlin_K, PiLp.smul_apply, smul_eq_mul]
    rw [Real.rpow_sub_one hn.ne']
    field_simp
  exact (hlim.congr' heq).limUnder_eq

end HRS.CZ.Sym
