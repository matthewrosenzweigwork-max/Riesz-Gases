import HRS.PDE.Toolbox.LocalInt
import HRS.PDE.Toolbox.Product

/-!
# Appendix C helper lemmas: weighted symmetrization and comparison (Lemma C.3 (iii), (iv))

Auxiliary results for `HRS/PDE/Toolbox.lean`.

The quadratic form `B` is kept abstract: `BilinRep 𝔨 B` says `B u v = ½ ∬ 𝔨(z) δ_z u δ_z v` with
absolute convergence for Lipschitz `u, v` (the `bilinear` field of `IsLevyKernel`).  Everything is
proved for such `B`; `Toolbox.lean` instantiates `B = symbolForm 𝔪`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.WeightAux

variable {d : ℕ}

/-! ### Lipschitz algebra -/

theorem isLipschitz_add {L L' : ℝ} {u v : Torus d → ℝ} (hu : Torus.IsLipschitz L u)
    (hv : Torus.IsLipschitz L' v) : Torus.IsLipschitz (L + L') (fun x => u x + v x) := by
  intro x y
  have t0 := LocInt.tdist_nonneg x y
  have e : u x + v x - (u y + v y) = (u x - u y) + (v x - v y) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  linarith [hu x y, hv x y]

theorem isLipschitz_const_mul {L : ℝ} {u : Torus d → ℝ} (c : ℝ) (hu : Torus.IsLipschitz L u) :
    Torus.IsLipschitz (|c| * L) (fun x => c * u x) := by
  intro x y
  have t0 := LocInt.tdist_nonneg x y
  have e : c * u x - c * u y = c * (u x - u y) := by ring
  rw [e, abs_mul]
  have := hu x y
  have h2 : |u x - u y| ≤ L * Torus.tdist x y := this
  calc |c| * |u x - u y| ≤ |c| * (L * Torus.tdist x y) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |c| * L * Torus.tdist x y := by ring

theorem isLipschitz_sub_const {L : ℝ} {u : Torus d → ℝ} (c : ℝ) (hu : Torus.IsLipschitz L u) :
    Torus.IsLipschitz L (fun x => u x - c) := by
  intro x y
  have e : u x - c - (u y - c) = u x - u y := by ring
  rw [e]; exact hu x y

theorem isLipschitz_congr {L : ℝ} {u v : Torus d → ℝ} (h : ∀ x, u x = v x)
    (hu : Torus.IsLipschitz L u) : Torus.IsLipschitz L v := by
  have : u = v := funext h
  rwa [← this]

/-! ### The abstract bilinear representation -/

/-- `B u v = ½ ∬ 𝔨(z) δ_z u(x) δ_z v(x)` for Lipschitz `u, v`, with absolute convergence. -/
def BilinRep (𝔨 : Torus d → ℝ) (B : (Torus d → ℝ) → (Torus d → ℝ) → ℝ) : Prop :=
  ∀ (Lu Lv : ℝ) (u v : Torus d → ℝ), Torus.IsLipschitz Lu u → Torus.IsLipschitz Lv v →
    Integrable (fun p : Torus d × Torus d =>
      𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))) ∧
    B u v = (1 / 2) * ∫ p : Torus d × Torus d,
      𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))

theorem B_add_left {𝔨 : Torus d → ℝ} {B : (Torus d → ℝ) → (Torus d → ℝ) → ℝ} (hB : BilinRep 𝔨 B)
    {L1 L2 Lv : ℝ} {u1 u2 v : Torus d → ℝ} (h1 : Torus.IsLipschitz L1 u1)
    (h2 : Torus.IsLipschitz L2 u2) (hv : Torus.IsLipschitz Lv v) :
    B (fun x => u1 x + u2 x) v = B u1 v + B u2 v := by
  obtain ⟨i1, e1⟩ := hB _ _ _ _ h1 hv
  obtain ⟨i2, e2⟩ := hB _ _ _ _ h2 hv
  obtain ⟨-, e3⟩ := hB _ _ _ _ (isLipschitz_add h1 h2) hv
  rw [e1, e2, e3, ← mul_add, ← integral_add i1 i2]
  congr 2
  funext p
  ring

theorem B_const_mul_left {𝔨 : Torus d → ℝ} {B : (Torus d → ℝ) → (Torus d → ℝ) → ℝ}
    (hB : BilinRep 𝔨 B) {L Lv : ℝ} {u v : Torus d → ℝ} (c : ℝ) (h : Torus.IsLipschitz L u)
    (hv : Torus.IsLipschitz Lv v) : B (fun x => c * u x) v = c * B u v := by
  obtain ⟨-, e1⟩ := hB _ _ _ _ h hv
  obtain ⟨-, e2⟩ := hB _ _ _ _ (isLipschitz_const_mul c h) hv
  have : ∫ p : Torus d × Torus d, 𝔨 p.2 * (c * u p.1 - c * u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2)) =
      c * ∫ p : Torus d × Torus d, 𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2)) := by
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
  rw [e1, e2, this]
  ring

/-! ### The shear -/

/-- `(x, z) ↦ (x, x - z)` -/
def shear (d : ℕ) : (Torus d × Torus d) ≃ᵐ (Torus d × Torus d) where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := measurable_fst.prodMk (measurable_fst.sub measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_fst.sub measurable_snd)

theorem measurePreserving_shear :
    MeasurePreserving (shear d) (volume : Measure (Torus d × Torus d)) volume := by
  have h := (MeasurePreserving.id (volume : Measure (Torus d))).skew_product
    (μc := (volume : Measure (Torus d))) (μd := (volume : Measure (Torus d)))
    (g := fun x z : Torus d => x - z) (measurable_fst.sub measurable_snd)
    (Eventually.of_forall fun x => Measure.map_sub_left_eq_self (volume : Measure (Torus d)) x)
  exact h

/-! ### Integrability of `|𝔨| min(t², 1)` -/

theorem integrable_kernel_min (hd : 1 ≤ d) {θ : ℝ} (hθ : θ < 2) {𝔨 : Torus d → ℝ}
    (hmeas : Measurable 𝔨)
    (hbound : ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
      |𝔨 z| ≤ C * (Torus.tdist z 0 ^ (-(d : ℝ) - θ) + 1)) :
    Integrable (fun z : Torus d => |𝔨 z| * min (Torus.tdist z 0 ^ 2) 1) := by
  obtain ⟨C, hC⟩ := hbound
  have hα : (d : ℝ) + θ - 2 < d := by linarith
  have hdom : Integrable (fun z : Torus d =>
      |C| * (Torus.tdist z 0 ^ (-((d : ℝ) + θ - 2)) + 1)) :=
    ((LocInt.integrable_tdist_rpow hα).add (integrable_const 1)).const_mul _
  have hm : Measurable fun z : Torus d => |𝔨 z| * min (Torus.tdist z 0 ^ 2) 1 :=
    hmeas.abs.mul ((Kern.measurable_tdist_zero.pow_const 2).min measurable_const)
  refine hdom.mono' hm.aestronglyMeasurable ?_
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  filter_upwards [LocInt.ae_coords_ne_zero] with z hz
  have hz0 : z ≠ 0 := fun h => hz ⟨0, hd⟩ (by simp [h])
  have ht : 0 < Torus.tdist z 0 :=
    lt_of_le_of_ne (LocInt.tdist_nonneg z 0) (fun h => hz0 ((LocInt.tdist_eq_zero_iff _ _).1 h.symm))
  set t := Torus.tdist z 0 with htdef
  have hmin0 : 0 ≤ min (t ^ 2) 1 := le_min (by positivity) zero_le_one
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hmin0)]
  have hp0 : 0 ≤ t ^ (-(d : ℝ) - θ) := Real.rpow_nonneg ht.le _
  have h1 : |𝔨 z| ≤ |C| * (t ^ (-(d : ℝ) - θ) + 1) :=
    (hC z hz0).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h2 : t ^ (-(d : ℝ) - θ) * t ^ 2 = t ^ (-((d : ℝ) + θ - 2)) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht]
    congr 1; push_cast; ring
  calc |𝔨 z| * min (t ^ 2) 1 ≤ (|C| * (t ^ (-(d : ℝ) - θ) + 1)) * min (t ^ 2) 1 :=
        mul_le_mul_of_nonneg_right h1 hmin0
    _ = |C| * (t ^ (-(d : ℝ) - θ) * min (t ^ 2) 1 + min (t ^ 2) 1) := by ring
    _ ≤ |C| * (t ^ (-((d : ℝ) + θ - 2)) + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have a1 : t ^ (-(d : ℝ) - θ) * min (t ^ 2) 1 ≤ t ^ (-(d : ℝ) - θ) * t ^ 2 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hp0
        have a2 : min (t ^ 2) 1 ≤ 1 := min_le_right _ _
        rw [h2] at a1
        linarith

/-! ### The weighted error bound -/

theorem weighted_bound (hd : 1 ≤ d) {θ : ℝ} (hθ : θ < 2) {𝔨 : Torus d → ℝ}
    (hmeas : Measurable 𝔨)
    (hbound : ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
      |𝔨 z| ≤ C * (Torus.tdist z 0 ^ (-(d : ℝ) - θ) + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Lm M : ℝ) (m w : Torus d → ℝ), Torus.IsLipschitz Lm m →
      (∀ x, |m x| ≤ M) → MemLp w 2 volume →
      Integrable (fun p : Torus d × Torus d =>
        𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) ∧
      |∫ p : Torus d × Torus d, 𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2| ≤
        C * (Lm ^ 2 + M ^ 2) * ∫ x, w x ^ 2 := by
  have hρ := integrable_kernel_min hd hθ hmeas hbound
  set ρ : Torus d → ℝ := fun z => |𝔨 z| * min (Torus.tdist z 0 ^ 2) 1 with hρdef
  have hρ0 : ∀ z, 0 ≤ ρ z := fun z => mul_nonneg (abs_nonneg _) (le_min (by positivity) zero_le_one)
  have hI0 : 0 ≤ ∫ z, ρ z := integral_nonneg hρ0
  refine ⟨4 * ∫ z, ρ z, by positivity, ?_⟩
  intro Lm M m w hm hM hw
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set K : ℝ := Lm ^ 2 + 4 * M ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hρK : Integrable (fun z : Torus d => K * ρ z) := hρ.const_mul K
  have hρK0 : ∀ z, 0 ≤ K * ρ z := fun z => mul_nonneg hK0 (hρ0 z)
  set Gt : Torus d × Torus d → ℝ := fun q => 𝔨 (q.1 - q.2) * w q.1 * w q.2 * (m q.1 - m q.2) ^ 2
    with hGt
  have hmc : Continuous m := LocInt.continuous_of_isLipschitz hm
  have hwm : AEStronglyMeasurable w volume := hw.aestronglyMeasurable
  have hGtm : AEStronglyMeasurable Gt (volume : Measure (Torus d × Torus d)) := by
    have h1 : AEStronglyMeasurable (fun q : Torus d × Torus d => 𝔨 (q.1 - q.2))
        (volume : Measure (Torus d × Torus d)) :=
      (hmeas.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun q : Torus d × Torus d => w q.1)
        (volume : Measure (Torus d × Torus d)) :=
      hwm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h3 : AEStronglyMeasurable (fun q : Torus d × Torus d => w q.2)
        (volume : Measure (Torus d × Torus d)) :=
      hwm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h4 : AEStronglyMeasurable (fun q : Torus d × Torus d => (m q.1 - m q.2) ^ 2)
        (volume : Measure (Torus d × Torus d)) :=
      ((hmc.measurable.comp measurable_fst).sub (hmc.measurable.comp measurable_snd)).pow_const 2
        |>.aestronglyMeasurable
    exact ((h1.mul h2).mul h3).mul h4
  have hbd : ∀ q : Torus d × Torus d, |Gt q| ≤ (K * ρ (q.1 - q.2)) * (|w q.1| * |w q.2|) := by
    intro q
    set t := Torus.tdist q.1 q.2 with htdef
    have ht0 : Torus.tdist (q.1 - q.2) 0 = t := (LocInt.tdist_zero_right _ _).symm
    have t0 : 0 ≤ t := LocInt.tdist_nonneg _ _
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
    have hρq : ρ (q.1 - q.2) = |𝔨 (q.1 - q.2)| * min (t ^ 2) 1 := by
      simp only [hρdef]; rw [ht0]
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
  obtain ⟨hGtint, hGtbound⟩ := LocInt.schur_bound hρK hρK0 hw hGtm hbd
  have hcomp : (fun p : Torus d × Torus d =>
      𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) = Gt ∘ (shear d) := by
    funext p
    simp [hGt, shear, sub_sub_cancel]
  have hmp := measurePreserving_shear (d := d)
  rw [hcomp]
  refine ⟨(hmp.integrable_comp_emb (shear d).measurableEmbedding).2 hGtint, ?_⟩
  have hI : ∫ p : Torus d × Torus d, (Gt ∘ shear d) p = ∫ p : Torus d × Torus d, Gt p :=
    hmp.integral_comp' Gt
  refine (le_of_eq (congrArg abs hI)).trans (hGtbound.trans ?_)
  rw [integral_const_mul]
  have hw2 : 0 ≤ ∫ x, w x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have : K * (∫ z, ρ z) ≤ 4 * (∫ z, ρ z) * (Lm ^ 2 + M ^ 2) := by
    rw [hK]; nlinarith [sq_nonneg Lm, sq_nonneg M]
  exact mul_le_mul_of_nonneg_right this hw2

/-! ### Lemma C.3 (iii), abstractly -/

theorem weighted_core (hd : 1 ≤ d) {θ : ℝ} (hθ : θ < 2) {𝔨 : Torus d → ℝ}
    (hmeas : Measurable 𝔨)
    (hbound : ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
      |𝔨 z| ≤ C * (Torus.tdist z 0 ^ (-(d : ℝ) - θ) + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : (Torus d → ℝ) → (Torus d → ℝ) → ℝ), BilinRep 𝔨 B →
      ∀ (Lm Lw : ℝ) (m w a : Torus d → ℝ), Torus.IsLipschitz Lm m → Torus.IsLipschitz Lw w →
      (∀ x, a x = m x ^ 2) →
      Integrable (fun p : Torus d × Torus d =>
        𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) ∧
      B (fun x => a x * w x) w - B (fun x => m x * w x) (fun x => m x * w x) =
        -(1 / 2) * ∫ p : Torus d × Torus d,
          𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2 ∧
      |B (fun x => a x * w x) w - B (fun x => m x * w x) (fun x => m x * w x)| ≤
        C * (Lm ^ 2 + Torus.supNorm m ^ 2) * ∫ x, w x ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := weighted_bound hd hθ hmeas hbound
  refine ⟨C, hC0, ?_⟩
  intro B hB Lm Lw m w a hm hw ha
  have hmm := LocInt.isLipschitz_mul hm hm
  have haL : Torus.IsLipschitz _ a :=
    isLipschitz_congr (fun x => by rw [ha x]; ring) hmm
  have hu1 := LocInt.isLipschitz_mul haL hw
  have hu2 := LocInt.isLipschitz_mul hm hw
  obtain ⟨i1, e1⟩ := hB _ _ _ _ hu1 hw
  obtain ⟨i2, e2⟩ := hB _ _ _ _ hu2 hu2
  obtain ⟨hJ, hJb⟩ := hC Lm (Torus.supNorm m) m w hm
    (LocInt.abs_le_supNorm_of_isLipschitz hm) (LocInt.memLp_two_of_isLipschitz hw)
  have hid : ∀ p : Torus d × Torus d,
      𝔨 p.2 * (a p.1 * w p.1 - a (p.1 - p.2) * w (p.1 - p.2)) * (w p.1 - w (p.1 - p.2)) -
        𝔨 p.2 * (m p.1 * w p.1 - m (p.1 - p.2) * w (p.1 - p.2)) *
          (m p.1 * w p.1 - m (p.1 - p.2) * w (p.1 - p.2)) =
        -(𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) := by
    intro p
    rw [ha p.1, ha (p.1 - p.2)]
    ring
  have hE : B (fun x => a x * w x) w - B (fun x => m x * w x) (fun x => m x * w x) =
      -(1 / 2) * ∫ p : Torus d × Torus d,
          𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2 := by
    rw [e1, e2, ← mul_sub, ← integral_sub i1 i2]
    have : (fun p : Torus d × Torus d =>
        𝔨 p.2 * (a p.1 * w p.1 - a (p.1 - p.2) * w (p.1 - p.2)) * (w p.1 - w (p.1 - p.2)) -
        𝔨 p.2 * (m p.1 * w p.1 - m (p.1 - p.2) * w (p.1 - p.2)) *
          (m p.1 * w p.1 - m (p.1 - p.2) * w (p.1 - p.2))) =
        fun p => -(𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) := funext hid
    simp only [this, integral_neg]
    ring
  refine ⟨hJ, hE, ?_⟩
  rw [hE, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hw2 : 0 ≤ ∫ x, w x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have : 0 ≤ C * (Lm ^ 2 + Torus.supNorm m ^ 2) * ∫ x, w x ^ 2 := by
    have := supNorm_nonneg m
    positivity
  linarith

/-! ### Lemma C.3 (iv), abstractly -/

theorem sq_add_sq_le_c01 (m : Torus d → ℝ) :
    Torus.holderSeminorm 1 m ^ 2 + Torus.supNorm m ^ 2 ≤ Torus.c01Norm m ^ 2 := by
  have h1 := LocInt.holderSeminorm_nonneg m
  have h2 := supNorm_nonneg m
  unfold Torus.c01Norm
  nlinarith [mul_nonneg h1 h2]

theorem compare_core (hd : 1 ≤ d) {θ : ℝ} (hθ : θ < 2) {𝔨 : Torus d → ℝ}
    (hmeas : Measurable 𝔨)
    (hbound : ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
      |𝔨 z| ≤ C * (Torus.tdist z 0 ^ (-(d : ℝ) - θ) + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : (Torus d → ℝ) → (Torus d → ℝ) → ℝ), BilinRep 𝔨 B →
      (∀ f, 0 ≤ B f f) →
      ∀ (lam0 Lm Lm' Lw : ℝ) (a w : Torus d → ℝ), 0 < lam0 → (∀ x, lam0 ≤ a x) →
      Torus.IsLipschitz Lm (fun x => Real.sqrt (a x)) →
      Torus.IsLipschitz Lm' (fun x => Real.sqrt (a x / lam0 - 1)) → Torus.IsLipschitz Lw w →
      B w w ≤ lam0⁻¹ * B (fun x => Real.sqrt (a x) * w x) (fun x => Real.sqrt (a x) * w x) +
        C * (1 + lam0⁻¹) * (Torus.c01Norm (fun x => Real.sqrt (a x)) ^ 2 +
          Torus.c01Norm (fun x => Real.sqrt (a x / lam0 - 1)) ^ 2 + 1) * ∫ x, w x ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := weighted_core hd hθ hmeas hbound
  refine ⟨C, hC0, ?_⟩
  intro B hB hnn lam0 Lm Lm' Lw a w hl hla hm hm' hw
  set m : Torus d → ℝ := fun x => Real.sqrt (a x) with hmdef
  set m' : Torus d → ℝ := fun x => Real.sqrt (a x / lam0 - 1) with hm'def
  set a' : Torus d → ℝ := fun x => a x / lam0 - 1 with ha'def
  have ha0 : ∀ x, 0 ≤ a x := fun x => hl.le.trans (hla x)
  have ha'0 : ∀ x, 0 ≤ a' x := fun x => by
    simp only [ha'def]
    have : 1 ≤ a x / lam0 := (one_le_div hl).2 (hla x)
    linarith
  have ham : ∀ x, a x = m x ^ 2 := fun x => (Real.sq_sqrt (ha0 x)).symm
  have ham' : ∀ x, a' x = m' x ^ 2 := fun x => (Real.sq_sqrt (ha'0 x)).symm
  have hmH := LocInt.isLipschitz_holder hm
  have hm'H := LocInt.isLipschitz_holder hm'
  obtain ⟨-, hEa_eq, hEa⟩ := hC B hB _ Lw m w a hmH hw ham
  obtain ⟨-, hE'_eq, hE'⟩ := hC B hB _ Lw m' w a' hm'H hw ham'
  -- Lipschitz facts
  have ha_L : Torus.IsLipschitz _ a := isLipschitz_congr (fun x => by rw [ham x]; ring)
    (LocInt.isLipschitz_mul hmH hmH)
  have ha'_L : Torus.IsLipschitz _ a' := isLipschitz_congr (fun x => by rw [ham' x]; ring)
    (LocInt.isLipschitz_mul hm'H hm'H)
  have hu2 := LocInt.isLipschitz_mul ha'_L hw
  have heq1 : (fun x => w x + a' x * w x) = fun x => a x / lam0 * w x := by
    funext x; simp only [ha'def]; ring
  have hu3 := isLipschitz_congr (fun x => congrFun heq1 x) (isLipschitz_add hw hu2)
  have hsum : B (fun x => w x + a' x * w x) w = B w w + B (fun x => a' x * w x) w :=
    B_add_left hB hw hu2 hw
  have hsmul : B (fun x => lam0 * (a x / lam0 * w x)) w = lam0 * B (fun x => a x / lam0 * w x) w :=
    B_const_mul_left hB lam0 hu3 hw
  have heq2 : (fun x => lam0 * (a x / lam0 * w x)) = fun x => a x * w x := by
    funext x; field_simp
  rw [heq1] at hsum
  rw [heq2] at hsmul
  -- abbreviations
  set S1 := B (fun x => a x * w x) w
  set S2 := B w w
  set S3 := B (fun x => a' x * w x) w
  set Sm := B (fun x => m x * w x) (fun x => m x * w x)
  set Sm' := B (fun x => m' x * w x) (fun x => m' x * w x)
  set W := ∫ x, w x ^ 2 with hWdef
  have hW0 : 0 ≤ W := integral_nonneg fun x => sq_nonneg _
  have hSm' : 0 ≤ Sm' := hnn _
  have h1 : S1 = lam0 * (S2 + S3) := by rw [hsmul, hsum]
  have h2 : lam0⁻¹ * S1 = S2 + S3 := by
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul]
  -- the error bounds
  have hP : Torus.holderSeminorm 1 m ^ 2 + Torus.supNorm m ^ 2 ≤ Torus.c01Norm m ^ 2 :=
    sq_add_sq_le_c01 m
  have hQ : Torus.holderSeminorm 1 m' ^ 2 + Torus.supNorm m' ^ 2 ≤ Torus.c01Norm m' ^ 2 :=
    sq_add_sq_le_c01 m'
  have hEa' : S1 - Sm ≤ C * Torus.c01Norm m ^ 2 * W :=
    (le_abs_self _).trans (hEa.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hP hC0) hW0))
  have hE'' : -(S3 - Sm') ≤ C * Torus.c01Norm m' ^ 2 * W :=
    (neg_le_abs _).trans (hE'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hQ hC0) hW0))
  have hli : 0 < lam0⁻¹ := inv_pos.2 hl
  set P := Torus.c01Norm m ^ 2 with hPdef
  set Q := Torus.c01Norm m' ^ 2 with hQdef
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

end HRS.PDE.WeightAux
