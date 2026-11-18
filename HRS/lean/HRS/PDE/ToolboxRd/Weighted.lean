import HRS.PDE.ToolboxRd.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Lemma C.3 (iii), (iv) on `ℝ^d`: weighted symmetrization and comparison

`ℝ^d` analogue of `HRS/PDE/Toolbox/Weighted.lean` (with `LocalInt.lean`).  The quadratic form is used only
through the `bound`, `smooth` and `bilinear` fields of `IsLevyKernel`.  The two facts of the Fourier
worker (`hbdd`: a Lipschitz `L²` function is bounded; `hmul`: multiplication by a bounded Lipschitz
function preserves `H¹`) are hypotheses of the cores.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.ToolboxRd.WeightAux

variable {d : ℕ}

/-! ### Lipschitz algebra -/

theorem isLipschitz_continuous {L : ℝ} {u : Euc d → ℝ} (h : IsLipschitz L u) : Continuous u := by
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal L) (fun x y => ?_)).continuous
  rw [Real.dist_eq, dist_eq_norm]
  refine (h x y).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  simp [Real.coe_toNNReal']

theorem isLipschitz_add {L L' : ℝ} {u v : Euc d → ℝ} (hu : IsLipschitz L u)
    (hv : IsLipschitz L' v) : IsLipschitz (L + L') (fun x => u x + v x) := by
  intro x y
  have e : u x + v x - (u y + v y) = (u x - u y) + (v x - v y) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have := norm_nonneg (x - y)
  linarith [hu x y, hv x y]

theorem isLipschitz_mul {L L' Bu Bv : ℝ} {u v : Euc d → ℝ} (hu : IsLipschitz L u)
    (hv : IsLipschitz L' v) (hBu : ∀ x, |u x| ≤ Bu) (hBv : ∀ x, |v x| ≤ Bv) :
    IsLipschitz (Bu * L' + Bv * L) (fun x => u x * v x) := by
  intro x y
  have hA := hBu x
  have hB := hBv y
  have h1 := hu x y
  have h2 := hv x y
  have e : u x * v x - u y * v y = u x * (v x - v y) + v y * (u x - u y) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have := mul_le_mul hA h2 (abs_nonneg _) ((abs_nonneg _).trans hA)
  have := mul_le_mul hB h1 (abs_nonneg _) ((abs_nonneg _).trans hB)
  nlinarith

/-! ### Measurability of the kernel -/

theorem measurable_of_smooth {𝔨 : Euc d → ℝ}
    (h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) 𝔨 {z | z ≠ 0}) : Measurable 𝔨 := by
  refine measurable_of_measurable_on_compl_singleton (0 : Euc d) ?_
  have hc : Continuous (Set.domRestrict {(0 : Euc d)}ᶜ 𝔨) := by
    have : ContinuousOn 𝔨 {z : Euc d | z ≠ 0} := h.continuousOn
    rw [continuousOn_iff_continuous_domRestrict] at this
    exact this
  exact hc.measurable

/-! ### Integrability of `|𝔨| min(‖z‖², 1)` -/

theorem ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ z : Euc d ∂(volume : Measure (Euc d)), z ≠ 0 := by
  have : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [finrank_euclideanSpace_fin]; omega
  have : (volume : Measure (Euc d)) {0} = 0 := measure_singleton 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with z hz
  simpa using hz

theorem integrable_kernel_min (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2) {𝔨 : Euc d → ℝ}
    (hmeas : Measurable 𝔨)
    (hbound : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ)) :
    Integrable (fun z : Euc d => |𝔨 z| * min (‖z‖ ^ 2) 1) := by
  obtain ⟨C, hC⟩ := hbound
  have hfr : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  have hm : Measurable fun z : Euc d => |𝔨 z| * min (‖z‖ ^ 2) 1 :=
    hmeas.abs.mul ((measurable_norm.pow_const 2).min measurable_const)
  have key : ∀ z : Euc d, z ≠ 0 → |𝔨 z| * min (‖z‖ ^ 2) 1 ≤ |C| * ‖z‖ ^ (-(d : ℝ) - θ) * min (‖z‖ ^ 2) 1 := by
    intro z hz
    exact mul_le_mul_of_nonneg_right ((hC z hz).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (norm_nonneg _) _)))
      (le_min (by positivity) zero_le_one)
  have hin : IntegrableOn (fun z : Euc d => |𝔨 z| * min (‖z‖ ^ 2) 1) (Metric.ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (C := |C|) (α := (d : ℝ) + θ - 2) (r := 1)
      (by rw [hfr]; omega) (by rw [hfr]; linarith) ?_ hm.aestronglyMeasurable
    refine ae_restrict_of_ae ?_
    filter_upwards [ae_ne_zero hd] with z hz
    have ht : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (le_min (by positivity) zero_le_one))]
    refine (key z hz).trans ?_
    have h2 : ‖z‖ ^ (-(d : ℝ) - θ) * ‖z‖ ^ 2 = ‖z‖ ^ (-((d : ℝ) + θ - 2)) := by
      rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_add ht]
      congr 1; push_cast; ring
    calc |C| * ‖z‖ ^ (-(d : ℝ) - θ) * min (‖z‖ ^ 2) 1
        ≤ |C| * ‖z‖ ^ (-(d : ℝ) - θ) * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ = |C| * ‖z‖ ^ (-((d : ℝ) + θ - 2)) := by rw [mul_assoc, h2]
  have hout : IntegrableOn (fun z : Euc d => |𝔨 z| * min (‖z‖ ^ 2) 1) (Metric.ball 0 1)ᶜ := by
    have hdom : Integrable (fun z : Euc d => |C| * 2 ^ ((d : ℝ) + θ) * (1 + ‖z‖) ^ (-((d : ℝ) + θ))) :=
      (integrable_one_add_norm (by rw [hfr]; linarith)).const_mul _
    refine (hdom.mono_measure Measure.restrict_le_self).mono' hm.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' (measurableSet_ball.compl)).2 (Eventually.of_forall fun z hz => ?_)
    have h1 : 1 ≤ ‖z‖ := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have ht : 0 < ‖z‖ := by linarith
    have hz0 : z ≠ 0 := norm_pos_iff.1 ht
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (le_min (by positivity) zero_le_one))]
    refine (key z hz0).trans ?_
    have hmin : min (‖z‖ ^ 2) 1 ≤ 1 := min_le_right _ _
    have hr : (0 : ℝ) ≤ (d : ℝ) + θ := by positivity
    have h3 : ‖z‖ ^ (-(d : ℝ) - θ) ≤ 2 ^ ((d : ℝ) + θ) * (1 + ‖z‖) ^ (-((d : ℝ) + θ)) := by
      have e1 : (2 * ‖z‖) ^ (-((d : ℝ) + θ)) ≤ (1 + ‖z‖) ^ (-((d : ℝ) + θ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      rw [Real.mul_rpow (by norm_num) ht.le] at e1
      have e2 : (2 : ℝ) ^ ((d : ℝ) + θ) * 2 ^ (-((d : ℝ) + θ)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      have e3 : ‖z‖ ^ (-(d : ℝ) - θ) = 2 ^ ((d : ℝ) + θ) * (2 ^ (-((d : ℝ) + θ)) * ‖z‖ ^ (-(d : ℝ) - θ)) := by
        rw [← mul_assoc, e2, one_mul]
      rw [e3]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : -(d : ℝ) - θ = -((d : ℝ) + θ) := by ring
      rw [this]; exact e1
    calc |C| * ‖z‖ ^ (-(d : ℝ) - θ) * min (‖z‖ ^ 2) 1 ≤ |C| * ‖z‖ ^ (-(d : ℝ) - θ) * 1 :=
          mul_le_mul_of_nonneg_left hmin (by positivity)
      _ = |C| * ‖z‖ ^ (-(d : ℝ) - θ) := by ring
      _ ≤ |C| * (2 ^ ((d : ℝ) + θ) * (1 + ‖z‖) ^ (-((d : ℝ) + θ))) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = |C| * 2 ^ ((d : ℝ) + θ) * (1 + ‖z‖) ^ (-((d : ℝ) + θ)) := by ring
  have := hin.union hout
  rwa [Set.union_compl_self, IntegrableOn, Measure.restrict_univ] at this

/-! ### Schur / Young bound -/

section Schur

variable {ρ g : Euc d → ℝ}

theorem integrable_sub_mul_snd (hρ : Integrable ρ) (hg : Integrable g) :
    Integrable (fun p : Euc d × Euc d => ρ (p.1 - p.2) * g p.2) ∧
    ∫ p : Euc d × Euc d, ρ (p.1 - p.2) * g p.2 = (∫ z, ρ z) * ∫ y, g y := by
  have hmeas : AEStronglyMeasurable (fun p : Euc d × Euc d => ρ (p.1 - p.2) * g p.2)
      (volume.prod volume) :=
    (hρ.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (Euc d)) volume)).mul
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hint : Integrable (fun p : Euc d × Euc d => ρ (p.1 - p.2) * g p.2)
      (volume.prod volume) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Eventually.of_forall fun y => (hρ.comp_sub_right y).mul_const (g y), ?_⟩
    refine (hg.norm.const_mul (∫ z, ‖ρ z‖)).congr (Eventually.of_forall fun y => ?_)
    simp only
    have : ∀ x : Euc d, ‖ρ (x - y) * g y‖ = ‖ρ (x - y)‖ * ‖g y‖ := fun x => norm_mul _ _
    simp_rw [this]
    rw [integral_mul_const, integral_sub_right_eq_self (fun x => ‖ρ x‖) y, mul_comm]
  refine ⟨hint, ?_⟩
  rw [show (volume : Measure (Euc d × Euc d)) = volume.prod volume from rfl,
    integral_prod_symm _ hint]
  have : ∀ y : Euc d, ∫ x : Euc d, ρ (x - y) * g y = (∫ z, ρ z) * g y := fun y => by
    rw [integral_mul_const, integral_sub_right_eq_self ρ y]
  simp_rw [this]
  rw [integral_const_mul]

theorem integrable_sub_mul_fst (hρ : Integrable ρ) (hg : Integrable g) :
    Integrable (fun p : Euc d × Euc d => ρ (p.1 - p.2) * g p.1) ∧
    ∫ p : Euc d × Euc d, ρ (p.1 - p.2) * g p.1 = (∫ z, ρ z) * ∫ y, g y := by
  have hmeas : AEStronglyMeasurable (fun p : Euc d × Euc d => ρ (p.1 - p.2) * g p.1)
      (volume.prod volume) :=
    (hρ.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (Euc d)) volume)).mul
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  have hint : Integrable (fun p : Euc d × Euc d => ρ (p.1 - p.2) * g p.1)
      (volume.prod volume) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Eventually.of_forall fun x => (hρ.comp_sub_left x).mul_const (g x), ?_⟩
    refine (hg.norm.const_mul (∫ z, ‖ρ z‖)).congr (Eventually.of_forall fun x => ?_)
    simp only
    have : ∀ y : Euc d, ‖ρ (x - y) * g x‖ = ‖ρ (x - y)‖ * ‖g x‖ := fun y => norm_mul _ _
    simp_rw [this]
    rw [integral_mul_const, integral_sub_left_eq_self (fun x => ‖ρ x‖) volume x, mul_comm]
  refine ⟨hint, ?_⟩
  rw [show (volume : Measure (Euc d × Euc d)) = volume.prod volume from rfl,
    integral_prod _ hint]
  have : ∀ x : Euc d, ∫ y : Euc d, ρ (x - y) * g x = (∫ z, ρ z) * g x := fun x => by
    rw [integral_mul_const, integral_sub_left_eq_self ρ volume x]
  simp_rw [this]
  rw [integral_const_mul]

/-- **Schur/Young bound**: for an integrable `ρ ≥ 0`, `w ∈ L²`, and `G` a.e.-measurable with
`|G(x,y)| ≤ ρ(x-y)|w(x)||w(y)|`, `G` is integrable and `|∬ G| ≤ (∫ρ) ‖w‖²₂`. -/
theorem schur_bound (hρ : Integrable ρ) (hρ0 : ∀ z, 0 ≤ ρ z) {w : Euc d → ℝ}
    (hw : MemLp w 2 volume) {G : Euc d × Euc d → ℝ}
    (hG : AEStronglyMeasurable G (volume : Measure (Euc d × Euc d)))
    (hbd : ∀ p : Euc d × Euc d, |G p| ≤ ρ (p.1 - p.2) * (|w p.1| * |w p.2|)) :
    Integrable G ∧ |∫ p, G p| ≤ (∫ z, ρ z) * ∫ x, w x ^ 2 := by
  have hw2 : Integrable (fun x => w x ^ 2) := hw.integrable_sq
  obtain ⟨hB, hBv⟩ := integrable_sub_mul_snd hρ hw2
  obtain ⟨hA, hAv⟩ := integrable_sub_mul_fst hρ hw2
  have hdom : Integrable (fun p : Euc d × Euc d =>
      (1 / 2 : ℝ) * (ρ (p.1 - p.2) * w p.1 ^ 2 + ρ (p.1 - p.2) * w p.2 ^ 2)) :=
    (hA.add hB).const_mul _
  have hpt : ∀ p : Euc d × Euc d, |G p| ≤
      (1 / 2 : ℝ) * (ρ (p.1 - p.2) * w p.1 ^ 2 + ρ (p.1 - p.2) * w p.2 ^ 2) := by
    intro p
    refine (hbd p).trans ?_
    have h2 : |w p.1| * |w p.2| ≤ (1 / 2) * (w p.1 ^ 2 + w p.2 ^ 2) := by
      nlinarith [sq_nonneg (|w p.1| - |w p.2|), sq_abs (w p.1), sq_abs (w p.2)]
    calc ρ (p.1 - p.2) * (|w p.1| * |w p.2|)
        ≤ ρ (p.1 - p.2) * ((1 / 2) * (w p.1 ^ 2 + w p.2 ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (hρ0 _)
      _ = _ := by ring
  have hint : Integrable G := by
    refine hdom.mono' hG (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]; exact hpt p
  refine ⟨hint, ?_⟩
  have hnorm : ‖∫ p, G p‖ ≤ ∫ p : Euc d × Euc d,
      (1 / 2 : ℝ) * (ρ (p.1 - p.2) * w p.1 ^ 2 + ρ (p.1 - p.2) * w p.2 ^ 2) :=
    norm_integral_le_of_norm_le hdom (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hpt p)
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add hA hB, hAv, hBv]
  ring

end Schur

/-! ### The shear -/

/-- `(x, z) ↦ (x, x - z)` -/
def shear (d : ℕ) : (Euc d × Euc d) ≃ᵐ (Euc d × Euc d) where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := measurable_fst.prodMk (measurable_fst.sub measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_fst.sub measurable_snd)

theorem measurePreserving_shear :
    MeasurePreserving (shear d) (volume : Measure (Euc d × Euc d)) volume := by
  have h := (MeasurePreserving.id (volume : Measure (Euc d))).skew_product
    (μc := (volume : Measure (Euc d))) (μd := (volume : Measure (Euc d)))
    (g := fun x z : Euc d => x - z) (measurable_fst.sub measurable_snd)
    (Eventually.of_forall fun x => Measure.map_sub_left_eq_self (volume : Measure (Euc d)) x)
  exact h

/-! ### The weighted error bound -/

theorem weighted_bound (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2) {𝔨 : Euc d → ℝ}
    (hmeas : Measurable 𝔨)
    (hbound : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Lm M : ℝ) (m w : Euc d → ℝ), IsLipschitz Lm m →
      (∀ x, |m x| ≤ M) → MemLp w 2 volume →
      Integrable (fun p : Euc d × Euc d =>
        𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) ∧
      |∫ p : Euc d × Euc d, 𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2| ≤
        C * (Lm ^ 2 + M ^ 2) * ∫ x, w x ^ 2 := by
  have hρ := integrable_kernel_min hd hθ0 hθ hmeas hbound
  set ρ : Euc d → ℝ := fun z => |𝔨 z| * min (‖z‖ ^ 2) 1 with hρdef
  have hρ0 : ∀ z, 0 ≤ ρ z := fun z => mul_nonneg (abs_nonneg _) (le_min (by positivity) zero_le_one)
  have hI0 : 0 ≤ ∫ z, ρ z := integral_nonneg hρ0
  refine ⟨4 * ∫ z, ρ z, by positivity, ?_⟩
  intro Lm M m w hm hM hw
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set K : ℝ := Lm ^ 2 + 4 * M ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hρK : Integrable (fun z : Euc d => K * ρ z) := hρ.const_mul K
  have hρK0 : ∀ z, 0 ≤ K * ρ z := fun z => mul_nonneg hK0 (hρ0 z)
  set Gt : Euc d × Euc d → ℝ := fun q => 𝔨 (q.1 - q.2) * w q.1 * w q.2 * (m q.1 - m q.2) ^ 2
    with hGt
  have hmc : Continuous m := isLipschitz_continuous hm
  have hwm : AEStronglyMeasurable w volume := hw.aestronglyMeasurable
  have hGtm : AEStronglyMeasurable Gt (volume : Measure (Euc d × Euc d)) := by
    have h1 : AEStronglyMeasurable (fun q : Euc d × Euc d => 𝔨 (q.1 - q.2))
        (volume : Measure (Euc d × Euc d)) :=
      (hmeas.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun q : Euc d × Euc d => w q.1)
        (volume : Measure (Euc d × Euc d)) :=
      hwm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h3 : AEStronglyMeasurable (fun q : Euc d × Euc d => w q.2)
        (volume : Measure (Euc d × Euc d)) :=
      hwm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h4 : AEStronglyMeasurable (fun q : Euc d × Euc d => (m q.1 - m q.2) ^ 2)
        (volume : Measure (Euc d × Euc d)) :=
      ((hmc.measurable.comp measurable_fst).sub (hmc.measurable.comp measurable_snd)).pow_const 2
        |>.aestronglyMeasurable
    exact ((h1.mul h2).mul h3).mul h4
  have hbd : ∀ q : Euc d × Euc d, |Gt q| ≤ (K * ρ (q.1 - q.2)) * (|w q.1| * |w q.2|) := by
    intro q
    set t := ‖q.1 - q.2‖ with htdef
    have t0 : 0 ≤ t := norm_nonneg _
    have hΔ1 : |m q.1 - m q.2| ≤ Lm * t := hm q.1 q.2
    have hΔ2 : |m q.1 - m q.2| ≤ 2 * M := by
      calc |m q.1 - m q.2| ≤ |m q.1| + |m q.2| := abs_sub _ _
        _ ≤ M + M := add_le_add (hM _) (hM _)
        _ = 2 * M := by ring
    have hsq : (m q.1 - m q.2) ^ 2 ≤ K * min (t ^ 2) 1 := by
      rw [← sq_abs]
      by_cases ht1 : t ≤ 1
      · have : t ^ 2 ≤ 1 := by nlinarith
        rw [min_eq_left this]
        calc |m q.1 - m q.2| ^ 2 ≤ (Lm * t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hΔ1 2
          _ = Lm ^ 2 * t ^ 2 := by ring
          _ ≤ K * t ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              rw [hK]; nlinarith [sq_nonneg M]
      · push Not at ht1
        have : 1 ≤ t ^ 2 := by nlinarith
        rw [min_eq_right this]
        calc |m q.1 - m q.2| ^ 2 ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hΔ2 2
          _ = 4 * M ^ 2 := by ring
          _ ≤ K * 1 := by rw [hK]; nlinarith [sq_nonneg Lm]
    have hρq : ρ (q.1 - q.2) = |𝔨 (q.1 - q.2)| * min (t ^ 2) 1 := rfl
    have : |Gt q| = |𝔨 (q.1 - q.2)| * ((m q.1 - m q.2) ^ 2) * (|w q.1| * |w q.2|) := by
      simp only [hGt, abs_mul]
      rw [abs_of_nonneg (sq_nonneg (m q.1 - m q.2))]; ring
    rw [this, hρq]
    have h5 : |𝔨 (q.1 - q.2)| * ((m q.1 - m q.2) ^ 2) ≤ |𝔨 (q.1 - q.2)| * (K * min (t ^ 2) 1) :=
      mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
    calc |𝔨 (q.1 - q.2)| * ((m q.1 - m q.2) ^ 2) * (|w q.1| * |w q.2|)
        ≤ |𝔨 (q.1 - q.2)| * (K * min (t ^ 2) 1) * (|w q.1| * |w q.2|) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = K * (|𝔨 (q.1 - q.2)| * min (t ^ 2) 1) * (|w q.1| * |w q.2|) := by ring
  obtain ⟨hGtint, hGtbound⟩ := schur_bound hρK hρK0 hw hGtm hbd
  have hcomp : (fun p : Euc d × Euc d =>
      𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) = Gt ∘ (shear d) := by
    funext p
    simp [hGt, shear, sub_sub_cancel]
  have hmp := measurePreserving_shear (d := d)
  rw [hcomp]
  refine ⟨(hmp.integrable_comp_emb (shear d).measurableEmbedding).2 hGtint, ?_⟩
  have hI : ∫ p : Euc d × Euc d, (Gt ∘ shear d) p = ∫ p : Euc d × Euc d, Gt p :=
    hmp.integral_comp' Gt
  refine (le_of_eq (congrArg abs hI)).trans (hGtbound.trans ?_)
  rw [integral_const_mul]
  have hw2 : 0 ≤ ∫ x, w x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have : K * (∫ z, ρ z) ≤ 4 * (∫ z, ρ z) * (Lm ^ 2 + M ^ 2) := by
    rw [hK]; nlinarith [sq_nonneg Lm, sq_nonneg M]
  exact mul_le_mul_of_nonneg_right this hw2

/-! ### The abstract bilinear representation -/

/-- `B u v = ½ ∬ 𝔨(z) δ_z u δ_z v` for Lipschitz `u, v ∈ H¹`, with absolute convergence
(this is the `bilinear` field of `IsLevyKernel`). -/
def BilinRep (𝔨 : Euc d → ℝ) (B : (Euc d → ℝ) → (Euc d → ℝ) → ℝ) : Prop :=
  ∀ (Lu Lv : ℝ) (u v : Euc d → ℝ), IsLipschitz Lu u → IsLipschitz Lv v →
    MemSobolev 1 u → MemSobolev 1 v →
    Integrable (fun p : Euc d × Euc d => 𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))) ∧
    B u v = (1 / 2) * ∫ p : Euc d × Euc d,
      𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))

theorem isLipschitz_congr {L : ℝ} {u v : Euc d → ℝ} (h : ∀ x, u x = v x)
    (hu : IsLipschitz L u) : IsLipschitz L v := by
  have : u = v := funext h
  rwa [← this]

/-- A bounded Lipschitz `b` times a bounded Lipschitz `h ∈ H¹` is Lipschitz and in `H¹`. -/
theorem prod_good
    (hmul : ∀ (b h : Euc d → ℝ) (Lb : ℝ), IsLipschitz Lb b → (∃ B : ℝ, ∀ x, |b x| ≤ B) →
      MemSobolev 1 h → MemSobolev 1 (fun x => b x * h x))
    {Lb Lh Bb Bh : ℝ} {b h : Euc d → ℝ} (hb : IsLipschitz Lb b) (hh : IsLipschitz Lh h)
    (hBb : ∀ x, |b x| ≤ Bb) (hBh : ∀ x, |h x| ≤ Bh) (hH : MemSobolev 1 h) :
    IsLipschitz (Bb * Lh + Bh * Lb) (fun x => b x * h x) ∧ MemSobolev 1 (fun x => b x * h x) :=
  ⟨isLipschitz_mul hb hh hBb hBh, hmul b h Lb hb ⟨Bb, hBb⟩ hH⟩

/-! ### Lemma C.3 (iii), abstractly -/

theorem weighted_abs (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2) {𝔨 : Euc d → ℝ}
    (hmeas : Measurable 𝔨)
    (hbound : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ))
    (hbdd : ∀ (w : Euc d → ℝ) (L : ℝ), IsLipschitz L w → MemLp w 2 volume →
      ∃ B : ℝ, ∀ x, |w x| ≤ B)
    (hmul : ∀ (b h : Euc d → ℝ) (Lb : ℝ), IsLipschitz Lb b → (∃ B : ℝ, ∀ x, |b x| ≤ B) →
      MemSobolev 1 h → MemSobolev 1 (fun x => b x * h x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : (Euc d → ℝ) → (Euc d → ℝ) → ℝ), BilinRep 𝔨 B →
      ∀ (Lm M Lw : ℝ) (m w a : Euc d → ℝ), IsLipschitz Lm m → (∀ x, |m x| ≤ M) →
      IsLipschitz Lw w → MemSobolev 1 w → (∀ x, a x = m x ^ 2) →
      Integrable (fun p : Euc d × Euc d =>
        𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) ∧
      B (fun x => a x * w x) w - B (fun x => m x * w x) (fun x => m x * w x) =
        -(1 / 2) * ∫ p : Euc d × Euc d,
          𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2 ∧
      |B (fun x => a x * w x) w - B (fun x => m x * w x) (fun x => m x * w x)| ≤
        C * (Lm ^ 2 + M ^ 2) * ∫ x, w x ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := weighted_bound hd hθ0 hθ hmeas hbound
  refine ⟨C, hC0, ?_⟩
  intro B hB Lm M Lw m w a hm hM hw hwH ha
  obtain ⟨Bw, hBw⟩ := hbdd w Lw hw hwH.1
  have hmm := isLipschitz_mul hm hm hM hM
  have haL : IsLipschitz _ a := isLipschitz_congr (fun x => by rw [ha x]; ring) hmm
  have hBa : ∀ x, |a x| ≤ M * M := fun x => by
    rw [ha x, abs_pow, sq]
    exact mul_le_mul (hM x) (hM x) (abs_nonneg _) ((abs_nonneg _).trans (hM x))
  obtain ⟨hu1, hu1H⟩ := prod_good hmul haL hw hBa hBw hwH
  obtain ⟨hu2, hu2H⟩ := prod_good hmul hm hw hM hBw hwH
  obtain ⟨i1, e1⟩ := hB _ _ _ _ hu1 hw hu1H hwH
  obtain ⟨i2, e2⟩ := hB _ _ _ _ hu2 hu2 hu2H hu2H
  obtain ⟨hJ, hJb⟩ := hC Lm M m w hm hM hwH.1
  have hE : B (fun x => a x * w x) w - B (fun x => m x * w x) (fun x => m x * w x) =
      -(1 / 2) * ∫ p : Euc d × Euc d,
          𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2 := by
    rw [e1, e2, ← mul_sub, ← integral_sub i1 i2]
    have : (fun p : Euc d × Euc d =>
        𝔨 p.2 * (a p.1 * w p.1 - a (p.1 - p.2) * w (p.1 - p.2)) * (w p.1 - w (p.1 - p.2)) -
        𝔨 p.2 * (m p.1 * w p.1 - m (p.1 - p.2) * w (p.1 - p.2)) *
          (m p.1 * w p.1 - m (p.1 - p.2) * w (p.1 - p.2))) =
        fun p => -(𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) := by
      funext p
      rw [ha p.1, ha (p.1 - p.2)]
      ring
    simp only [this, integral_neg]
    ring
  refine ⟨hJ, hE, ?_⟩
  rw [hE, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hw2 : 0 ≤ ∫ x, w x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have : 0 ≤ C * (Lm ^ 2 + M ^ 2) * ∫ x, w x ^ 2 := by positivity
  linarith

/-! ### Lemma C.3 (iv), abstractly -/

/-- Facts about `c01Norm` of a bounded Lipschitz function. -/
theorem c01_facts {L M : ℝ} {m : Euc d → ℝ} (hm : IsLipschitz L m) (hM : ∀ x, |m x| ≤ M) :
    IsLipschitz (⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2}, |m p.1.1 - m p.1.2| / ‖p.1.1 - p.1.2‖) m ∧
    (∀ x, |m x| ≤ ⨆ x, |m x|) ∧
    (⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2}, |m p.1.1 - m p.1.2| / ‖p.1.1 - p.1.2‖) ^ 2 +
      (⨆ x, |m x|) ^ 2 ≤ c01Norm m ^ 2 := by
  have hbdd : BddAbove (Set.range fun p : {p : Euc d × Euc d // p.1 ≠ p.2} =>
      |m p.1.1 - m p.1.2| / ‖p.1.1 - p.1.2‖) := by
    refine ⟨L, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hp : 0 < ‖p.1.1 - p.1.2‖ := norm_pos_iff.2 (sub_ne_zero.2 p.2)
    show |m p.1.1 - m p.1.2| / ‖p.1.1 - p.1.2‖ ≤ L
    rw [div_le_iff₀ hp]
    exact hm _ _
  have hbdd2 : BddAbove (Set.range fun x => |m x|) := ⟨M, by rintro _ ⟨x, rfl⟩; exact hM x⟩
  have hS0 : 0 ≤ ⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2}, |m p.1.1 - m p.1.2| / ‖p.1.1 - p.1.2‖ :=
    Real.iSup_nonneg fun p => by positivity
  have hs0 : 0 ≤ ⨆ x, |m x| := Real.iSup_nonneg fun x => abs_nonneg _
  refine ⟨?_, fun x => le_ciSup hbdd2 x, ?_⟩
  · intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    have h1 := le_ciSup hbdd (⟨(x, y), hxy⟩ : {p : Euc d × Euc d // p.1 ≠ p.2})
    have hp : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    exact (div_le_iff₀ hp).1 h1
  · unfold c01Norm
    nlinarith [mul_nonneg hS0 hs0]

theorem compare_abs (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2) {𝔨 : Euc d → ℝ}
    (hmeas : Measurable 𝔨)
    (hbound : ∃ C : ℝ, ∀ z : Euc d, z ≠ 0 → |𝔨 z| ≤ C * ‖z‖ ^ (-(d : ℝ) - θ))
    (hbdd : ∀ (w : Euc d → ℝ) (L : ℝ), IsLipschitz L w → MemLp w 2 volume →
      ∃ B : ℝ, ∀ x, |w x| ≤ B)
    (hmul : ∀ (b h : Euc d → ℝ) (Lb : ℝ), IsLipschitz Lb b → (∃ B : ℝ, ∀ x, |b x| ≤ B) →
      MemSobolev 1 h → MemSobolev 1 (fun x => b x * h x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : (Euc d → ℝ) → (Euc d → ℝ) → ℝ), BilinRep 𝔨 B →
      (∀ f, 0 ≤ B f f) →
      ∀ (lam0 Lm Lm' Lw A : ℝ) (a w : Euc d → ℝ), 0 < lam0 → (∀ x, lam0 ≤ a x) →
      (∀ x, a x ≤ A) →
      IsLipschitz Lm (fun x => Real.sqrt (a x)) →
      IsLipschitz Lm' (fun x => Real.sqrt (a x / lam0 - 1)) → IsLipschitz Lw w →
      MemSobolev 1 w →
      B w w ≤ lam0⁻¹ * B (fun x => Real.sqrt (a x) * w x) (fun x => Real.sqrt (a x) * w x) +
        C * (1 + lam0⁻¹) * (c01Norm (fun x => Real.sqrt (a x)) ^ 2 +
          c01Norm (fun x => Real.sqrt (a x / lam0 - 1)) ^ 2 + 1) * ∫ x, w x ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := weighted_abs hd hθ0 hθ hmeas hbound hbdd hmul
  refine ⟨C, hC0, ?_⟩
  intro B hB hnn lam0 Lm Lm' Lw A a w hl hla hAa hm hm' hw hwH
  set m : Euc d → ℝ := fun x => Real.sqrt (a x) with hmdef
  set m' : Euc d → ℝ := fun x => Real.sqrt (a x / lam0 - 1) with hm'def
  set a' : Euc d → ℝ := fun x => a x / lam0 - 1 with ha'def
  have ha0 : ∀ x, 0 ≤ a x := fun x => hl.le.trans (hla x)
  have ha'0 : ∀ x, 0 ≤ a' x := fun x => by
    simp only [ha'def]
    have : 1 ≤ a x / lam0 := (one_le_div hl).2 (hla x)
    linarith
  have ham : ∀ x, a x = m x ^ 2 := fun x => (Real.sq_sqrt (ha0 x)).symm
  have ham' : ∀ x, a' x = m' x ^ 2 := fun x => (Real.sq_sqrt (ha'0 x)).symm
  have hA0 : 0 ≤ A := (ha0 0).trans (hAa 0)
  have hM : ∀ x, |m x| ≤ Real.sqrt A := fun x => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hAa x)
  have hM' : ∀ x, |m' x| ≤ Real.sqrt (A / lam0) := fun x => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    have : a x / lam0 ≤ A / lam0 := div_le_div_of_nonneg_right (hAa x) hl.le
    linarith
  obtain ⟨hmH, hmsup, hP⟩ := c01_facts hm hM
  obtain ⟨hm'H, hm'sup, hQ⟩ := c01_facts hm' hM'
  obtain ⟨-, hEa_eq, hEa⟩ := hC B hB _ _ Lw m w a hmH hmsup hw hwH ham
  obtain ⟨-, hE'_eq, hE'⟩ := hC B hB _ _ Lw m' w a' hm'H hm'sup hw hwH ham'
  -- Lipschitz / H¹ facts
  obtain ⟨Bw, hBw⟩ := hbdd w Lw hw hwH.1
  have hmm := isLipschitz_mul hmH hmH hmsup hmsup
  have hm'm' := isLipschitz_mul hm'H hm'H hm'sup hm'sup
  have ha_L : IsLipschitz _ a := isLipschitz_congr (fun x => by rw [ham x]; ring) hmm
  have ha'_L : IsLipschitz _ a' := isLipschitz_congr (fun x => by rw [ham' x]; ring) hm'm'
  have hBa : ∀ x, |a x| ≤ A := fun x => by
    rw [abs_of_nonneg (ha0 x)]; exact hAa x
  have hBa' : ∀ x, |a' x| ≤ A / lam0 := fun x => by
    rw [abs_of_nonneg (ha'0 x)]
    have : a x / lam0 ≤ A / lam0 := div_le_div_of_nonneg_right (hAa x) hl.le
    simp only [ha'def]; linarith
  obtain ⟨hu1, hu1H⟩ := prod_good hmul ha_L hw hBa hBw hwH
  obtain ⟨hu3, hu3H⟩ := prod_good hmul ha'_L hw hBa' hBw hwH
  obtain ⟨hv1, hv1H⟩ := prod_good hmul hmH hw (fun x => (hmsup x)) hBw hwH
  obtain ⟨hv2, hv2H⟩ := prod_good hmul hm'H hw (fun x => (hm'sup x)) hBw hwH
  obtain ⟨i1, e1⟩ := hB _ _ _ _ hu1 hw hu1H hwH
  obtain ⟨i2, e2⟩ := hB _ _ _ _ hw hw hwH hwH
  obtain ⟨i3, e3⟩ := hB _ _ _ _ hu3 hw hu3H hwH
  -- abbreviations
  set S1 := B (fun x => a x * w x) w
  set S2 := B w w
  set S3 := B (fun x => a' x * w x) w
  set Sm := B (fun x => m x * w x) (fun x => m x * w x)
  set Sm' := B (fun x => m' x * w x) (fun x => m' x * w x)
  set W := ∫ x, w x ^ 2 with hWdef
  have hW0 : 0 ≤ W := integral_nonneg fun x => sq_nonneg _
  have hSm' : 0 ≤ Sm' := hnn _
  have hal : ∀ x, a x = lam0 * (a' x + 1) := fun x => by
    simp only [ha'def]; field_simp; ring
  have h1 : S1 = lam0 * (S2 + S3) := by
    rw [e1, e2, e3]
    have hf : (fun p : Euc d × Euc d =>
        𝔨 p.2 * (a p.1 * w p.1 - a (p.1 - p.2) * w (p.1 - p.2)) * (w p.1 - w (p.1 - p.2))) =
        fun p => lam0 * (𝔨 p.2 * (w p.1 - w (p.1 - p.2)) * (w p.1 - w (p.1 - p.2)) +
          𝔨 p.2 * (a' p.1 * w p.1 - a' (p.1 - p.2) * w (p.1 - p.2)) * (w p.1 - w (p.1 - p.2))) := by
      funext p
      rw [hal p.1, hal (p.1 - p.2)]
      ring
    rw [hf, integral_const_mul, integral_add i2 i3]
    ring
  have h2 : lam0⁻¹ * S1 = S2 + S3 := by
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul]
  -- the error bounds
  have hEa' : S1 - Sm ≤ C * c01Norm m ^ 2 * W :=
    (le_abs_self _).trans (hEa.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hP hC0) hW0))
  have hE'' : -(S3 - Sm') ≤ C * c01Norm m' ^ 2 * W :=
    (neg_le_abs _).trans (hE'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hQ hC0) hW0))
  have hli : 0 < lam0⁻¹ := inv_pos.2 hl
  set P := c01Norm m ^ 2 with hPdef
  set Q := c01Norm m' ^ 2 with hQdef
  have hP0 : 0 ≤ P := sq_nonneg _
  have hQ0 : 0 ≤ Q := sq_nonneg _
  have h3 : S2 = lam0⁻¹ * (Sm + (S1 - Sm)) - (Sm' + (S3 - Sm')) := by
    have : S2 = lam0⁻¹ * S1 - S3 := by linarith
    rw [this]; ring
  have h4 : lam0⁻¹ * (S1 - Sm) ≤ lam0⁻¹ * (C * P * W) := mul_le_mul_of_nonneg_left hEa' hli.le
  have h5 : C * (1 + lam0⁻¹) * (P + Q + 1) * W - (lam0⁻¹ * (C * P * W) + C * Q * W) =
      C * W * (P + 1 + lam0⁻¹ * Q + lam0⁻¹) := by ring
  have h6 : 0 ≤ C * W * (P + 1 + lam0⁻¹ * Q + lam0⁻¹) := by positivity
  show S2 ≤ lam0⁻¹ * Sm + C * (1 + lam0⁻¹) * (P + Q + 1) * W
  nlinarith [h3, h4, h5, h6, hE'', hSm']

/-! ### Public cores -/

/-- `B(u,u) = Re ∫ m |û|² ≥ 0` for a nonnegative symbol (junk values included). -/
theorem symbolForm_self_nonneg' {m : Euc d → ℝ} (hm : ∀ ξ, 0 ≤ m ξ) (u : Euc d → ℝ) :
    0 ≤ symbolForm m u u := by
  unfold symbolForm
  have h : ∀ ξ, ((m ξ : ℝ) : ℂ) * (fourierL2 u ξ * conj (fourierL2 u ξ)) =
      ((m ξ * Complex.normSq (fourierL2 u ξ) : ℝ) : ℂ) := fun ξ => by
    rw [Complex.mul_conj]; push_cast; ring
  simp_rw [h]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun ξ => mul_nonneg (hm ξ) (Complex.normSq_nonneg _)

/-- Lemma C.3(iii) on `ℝ^d`, from the `bound`, `smooth`, `bilinear` fields of `IsLevyKernel` and the
two Fourier facts `hbdd`, `hmul`; the conclusion is exactly that of `quadratic_toolbox_weighted`. -/
theorem weighted_core (hd : 1 ≤ d) (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (m𝔪 : Euc d → ℝ) (𝔨 : Euc d → ℝ) (h𝔨 : IsLevyKernel θ m𝔪 𝔨)
    (hbdd : ∀ (w : Euc d → ℝ) (L : ℝ), IsLipschitz L w → MemLp w 2 volume →
      ∃ B : ℝ, ∀ x, |w x| ≤ B)
    (hmul : ∀ (b h : Euc d → ℝ) (Lb : ℝ), IsLipschitz Lb b → (∃ B : ℝ, ∀ x, |b x| ≤ B) →
      MemSobolev 1 h → MemSobolev 1 (fun x => b x * h x)) :
    ∃ C : ℝ, ∀ (L La Lm Lw : ℝ) (a w : Euc d → ℝ), (∀ x, 0 ≤ a x) → IsC11 L a →
      IsLipschitz La a → IsLipschitz Lm (fun x => Real.sqrt (a x)) →
      IsLipschitz Lw w → MemSobolev 1 w →
      let m := fun x => Real.sqrt (a x)
      let E := symbolForm m𝔪 (fun x => a x * w x) w -
        symbolForm m𝔪 (fun x => m x * w x) (fun x => m x * w x)
      Integrable (fun p : Euc d × Euc d => 𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) ∧
      E = -(1 / 2) * ∫ p : Euc d × Euc d, 𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2 ∧
      |E| ≤ C * (Lm ^ 2 + (⨆ x, |m x|) ^ 2) * l2NormSq w := by
  obtain ⟨C, -, hC⟩ := weighted_abs hd hθ0 hθ2 (measurable_of_smooth h𝔨.smooth) h𝔨.bound hbdd hmul
  refine ⟨C, ?_⟩
  intro L La Lm Lw a w ha0 haC haL hm hw hwH m E
  obtain ⟨A, hA⟩ := haC.2.1
  have hM : ∀ x, |m x| ≤ Real.sqrt A := fun x => by
    show |Real.sqrt (a x)| ≤ _
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans (hA x))
  obtain ⟨-, hmsup, -⟩ := c01_facts hm hM
  exact hC (symbolForm m𝔪) h𝔨.bilinear Lm _ Lw m w a hm hmsup hw hwH
    (fun x => (Real.sq_sqrt (ha0 x)).symm)

/-- Lemma C.3(iv) on `ℝ^d`, from the Lévy kernel and the two Fourier facts; the conclusion is exactly
that of `quadratic_toolbox_compare`. -/
theorem compare_core (hd : 1 ≤ d) (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (m𝔪 : Euc d → ℝ) (hm𝔪 : IsHomogSymbol θ m𝔪) (𝔨 : Euc d → ℝ) (h𝔨 : IsLevyKernel θ m𝔪 𝔨)
    (hbdd : ∀ (w : Euc d → ℝ) (L : ℝ), IsLipschitz L w → MemLp w 2 volume →
      ∃ B : ℝ, ∀ x, |w x| ≤ B)
    (hmul : ∀ (b h : Euc d → ℝ) (Lb : ℝ), IsLipschitz Lb b → (∃ B : ℝ, ∀ x, |b x| ≤ B) →
      MemSobolev 1 h → MemSobolev 1 (fun x => b x * h x)) :
    ∃ C : ℝ, ∀ (L lam0 Lm Lm' Lw : ℝ) (a w : Euc d → ℝ), 0 < lam0 → (∀ x, lam0 ≤ a x) → IsC11 L a →
      IsLipschitz Lm (fun x => Real.sqrt (a x)) →
      IsLipschitz Lm' (fun x => Real.sqrt (a x / lam0 - 1)) → IsLipschitz Lw w → MemSobolev 1 w →
      let m := fun x => Real.sqrt (a x)
      symbolForm m𝔪 w w ≤ lam0⁻¹ * symbolForm m𝔪 (fun x => m x * w x) (fun x => m x * w x) +
        C * (1 + lam0⁻¹) * (c01Norm m ^ 2 +
          c01Norm (fun x => Real.sqrt (a x / lam0 - 1)) ^ 2 + 1) * l2NormSq w := by
  obtain ⟨C, -, hC⟩ := compare_abs hd hθ0 hθ2 (measurable_of_smooth h𝔨.smooth) h𝔨.bound hbdd hmul
  refine ⟨C, ?_⟩
  intro L lam0 Lm Lm' Lw a w hl hla haC hm hm' hw hwH m
  obtain ⟨A, hA⟩ := haC.2.1
  exact hC (symbolForm m𝔪) h𝔨.bilinear (symbolForm_self_nonneg' hm𝔪.nonneg) lam0 Lm Lm' Lw A a w hl hla
    (fun x => (le_abs_self _).trans (hA x)) hm hm' hw hwH

end HRS.PDE.ToolboxRd.WeightAux
