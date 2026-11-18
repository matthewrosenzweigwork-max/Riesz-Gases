/-
# HRS.External.WeakPointwise -- weighted (position-aware) Dobrushin comparison

Pointwise-in-position version of the Rebeschini-van Handel comparison of `WeakSpec`.  For two
one-site specifications `S, S'` on `Fin n → E` with densities `p, p'` w.r.t. `μ`, where `p`
depends on the neighbours through a kernel `ω(z, x)` and `|p' - p| ≤ D`, the difference of the
coordinate marginals is controlled in `L¹`-dual (density) form by `D + ∫ D` plus the first
iterates of the adjoint resolvent operator `T* u = (n-1)(ω u + ∫ u ω)`.
(Source: `Q:eq:measure-disagreement` / `Q:eq:pin-resolvent`, lines 4503-4550, in function-side form.)
-/
import HRS.External.WeakSpec

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.External

section Pointwise

open Spec

variable {E : Type*} [MeasurableSpace E] {n : ℕ} {μ : Measure E}

/-- Weighted oscillation class: `|g y - g y'| ≤ ∑_{j : y_j ≠ y'_j} (φ_j(y_j) + φ_j(y'_j))`. -/
def WLip (φ : Fin n → E → ℝ) (g : (Fin n → E) → ℝ) : Prop :=
  ∀ y y', |g y - g y'| ≤ ∑ j, if y j = y' j then 0 else φ j (y j) + φ j (y' j)

/-- Averaging a pointwise inequality over a free base point. -/
lemma le_add_integral_of_forall [IsProbabilityMeasure μ] {c A B : ℝ} {φ : E → ℝ}
    (hφ : Integrable φ μ) (_hB : 0 ≤ B) (h : ∀ z0, c ≤ A + φ z0 * B) :
    c ≤ A + (∫ z, φ z ∂μ) * B := by
  have h1 : ∫ _z0, c ∂μ ≤ ∫ z0, (A + φ z0 * B) ∂μ :=
    integral_mono (integrable_const _) ((integrable_const _).add (hφ.mul_const _)) h
  rw [integral_add (integrable_const _) (hφ.mul_const _), integral_mul_const] at h1
  simpa using h1

/-- Two densities integrating to one, a test function with weighted oscillation:
`|∫ F p₁ - ∫ F p₂| ≤ ∫ φ D + (∫ φ)(∫ D)` whenever `|p₁ - p₂| ≤ D`. -/
lemma abs_integral_mul_sub_le [IsProbabilityMeasure μ] {p₁ p₂ Dz φ F : E → ℝ}
    (hp₁ : Integrable p₁ μ) (hp₂ : Integrable p₂ μ) (h1 : ∫ z, p₁ z ∂μ = 1)
    (h2 : ∫ z, p₂ z ∂μ = 1) (hF : Measurable F) {M : ℝ} (hFb : ∀ z, |F z| ≤ M)
    (hDz : ∀ z, |p₁ z - p₂ z| ≤ Dz z) (hDi : Integrable Dz μ)
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) {B : ℝ} (hφb : ∀ z, φ z ≤ B)
    (hFφ : ∀ z z', |F z - F z'| ≤ φ z + φ z') :
    |∫ z, F z * p₁ z ∂μ - ∫ z, F z * p₂ z ∂μ|
      ≤ ∫ z, φ z * Dz z ∂μ + (∫ z, φ z ∂μ) * ∫ z, Dz z ∂μ := by
  have hφi : Integrable φ μ :=
    Integrable.of_bound hφm.aestronglyMeasurable B (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hφ0 z)]; exact hφb z)
  have hD0 : 0 ≤ ∫ z, Dz z ∂μ := integral_nonneg fun z => (abs_nonneg _).trans (hDz z)
  have hFi : ∀ q : E → ℝ, Integrable q μ → Integrable (fun z => F z * q z) μ := fun q hq =>
    hq.bdd_mul hF.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hFb z)
  have hφD : Integrable (fun z => φ z * Dz z) μ :=
    hDi.bdd_mul hφm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hφ0 z)]; exact hφb z)
  have key : ∀ z0, |∫ z, F z * p₁ z ∂μ - ∫ z, F z * p₂ z ∂μ|
      ≤ (∫ z, φ z * Dz z ∂μ) + φ z0 * ∫ z, Dz z ∂μ := by
    intro z0
    have e : ∫ z, F z * p₁ z ∂μ - ∫ z, F z * p₂ z ∂μ
        = ∫ z, (F z - F z0) * (p₁ z - p₂ z) ∂μ := by
      have : ∀ z, (F z - F z0) * (p₁ z - p₂ z)
          = (F z * p₁ z - F z * p₂ z) - F z0 * (p₁ z - p₂ z) := fun z => by ring
      simp_rw [this]
      have i1 := hFi _ hp₁
      have i2 := hFi _ hp₂
      have i3 : Integrable (fun z => F z0 * (p₁ z - p₂ z)) μ := (hp₁.sub hp₂).const_mul _
      have hB : ∫ z, (F z * p₁ z - F z * p₂ z - F z0 * (p₁ z - p₂ z)) ∂μ
          = ∫ z, (F z * p₁ z - F z * p₂ z) ∂μ - ∫ z, F z0 * (p₁ z - p₂ z) ∂μ :=
        integral_sub (i1.sub i2) i3
      have hA : ∫ z, (F z * p₁ z - F z * p₂ z) ∂μ
          = ∫ z, F z * p₁ z ∂μ - ∫ z, F z * p₂ z ∂μ := integral_sub i1 i2
      rw [hB, hA, integral_const_mul, integral_sub hp₁ hp₂, h1, h2]
      ring
    rw [e]
    have hb : ∀ z, ‖(F z - F z0) * (p₁ z - p₂ z)‖ ≤ φ z * Dz z + φ z0 * Dz z := fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |F z - F z0| * |p₁ z - p₂ z| ≤ (φ z + φ z0) * Dz z :=
            mul_le_mul (hFφ z z0) (hDz z) (abs_nonneg _) (add_nonneg (hφ0 z) (hφ0 z0))
        _ = _ := by ring
    have hI : ∫ z, (φ z * Dz z + φ z0 * Dz z) ∂μ
        = (∫ z, φ z * Dz z ∂μ) + φ z0 * ∫ z, Dz z ∂μ := by
      rw [integral_add hφD (hDi.const_mul _), integral_const_mul]
    have := norm_integral_le_of_norm_le (hφD.add (hDi.const_mul (φ z0)))
      (Filter.Eventually.of_forall hb)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_of_eq hI)
  exact le_add_integral_of_forall hφi hD0 key

/-- The one-site kernels of `S` have the (real) densities `p i x` with respect to `μ`. -/
structure DensKernel (μ : Measure E) (S : Spec E n) (p : Fin n → (Fin n → E) → E → ℝ) : Prop where
  eq : ∀ i x, S.G i x = μ.withDensity (fun z => ENNReal.ofReal (p i x z))
  nonneg : ∀ i x z, 0 ≤ p i x z
  meas : ∀ i x, Measurable (p i x)

namespace DensKernel

variable {S : Spec E n} {p : Fin n → (Fin n → E) → E → ℝ}

lemma integral_G (h : DensKernel μ S p) (i : Fin n) (x : Fin n → E) (F : E → ℝ) :
    ∫ z, F z ∂(S.G i x) = ∫ z, F z * p i x z ∂μ := by
  rw [h.eq i x, integral_withDensity_eq_integral_toReal_smul
    (h.meas i x).ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (h.nonneg i x z), mul_comm]

lemma integral_p (h : DensKernel μ S p) (i : Fin n) (x : Fin n → E) :
    ∫ z, p i x z ∂μ = 1 := by
  have := h.integral_G i x (fun _ => 1)
  simpa using this.symm

lemma integrable_p (h : DensKernel μ S p) (i : Fin n) (x : Fin n → E) :
    Integrable (p i x) μ :=
  Integrable.of_integral_ne_zero (by rw [h.integral_p i x]; exact one_ne_zero)

lemma site_eq (h : DensKernel μ S p) (i : Fin n) (g : (Fin n → E) → ℝ) (x : Fin n → E) :
    S.site i g x = ∫ z, g (update x i z) * p i x z ∂μ :=
  h.integral_G i x _

end DensKernel

/-! ### The kernel `ω` and the dual operators -/

/-- Data of the dependence kernel `ω(z, x) ≥ 0`: jointly measurable, integrable columns,
column sums at most `ρc`. -/
structure KerData (μ : Measure E) (ω : E → E → ℝ) (ρc : ℝ) : Prop where
  meas : Measurable (fun p : E × E => ω p.1 p.2)
  nonneg : ∀ z x, 0 ≤ ω z x
  integrable : ∀ x, Integrable (fun z => ω z x) μ
  col_le : ∀ x, ∫ z, ω z x ∂μ ≤ ρc
  row_integrable : ∀ z, Integrable (fun x => ω z x) μ
  row_le : ∀ z, ∫ x, ω z x ∂μ ≤ ρc

/-- Column sum `∫ ω(z, x) μ(dz)`. -/
def colS (μ : Measure E) (ω : E → E → ℝ) (x : E) : ℝ := ∫ z, ω z x ∂μ

/-- `K φ (x) = ∫ φ(z) ω(z,x) μ(dz) + (∫ ω(z,x) μ(dz)) (∫ φ dμ)`. -/
def Kop (μ : Measure E) (ω : E → E → ℝ) (φ : E → ℝ) (x : E) : ℝ :=
  ∫ z, φ z * ω z x ∂μ + colS μ ω x * ∫ z, φ z ∂μ

/-- One step of the weight recursion. -/
def stepW (μ : Measure E) (ω : E → E → ℝ) (φ : Fin n → E → ℝ) : Fin n → E → ℝ := fun k x =>
  (1 - 1 / (n : ℝ)) * φ k x + (1 / (n : ℝ)) * ∑ i ∈ Finset.univ.erase k, Kop μ ω (φ i) x

/-- The adjoint operator `T* u (z) = (n-1) (∫ ω(z,x) u(x) μ(dx) + ∫ u(x) colS(x) μ(dx))`. -/
def Tstar (μ : Measure E) (ω : E → E → ℝ) (n : ℕ) (u : E → ℝ) (z : E) : ℝ :=
  ((n : ℝ) - 1) * (∫ x, u x * ω z x ∂μ + ∫ x, u x * colS μ ω x ∂μ)

/-- Admissible weight vectors: measurable, nonnegative, bounded. -/
structure GoodW (φ : Fin n → E → ℝ) : Prop where
  meas : ∀ k, Measurable (φ k)
  nonneg : ∀ k x, 0 ≤ φ k x
  bdd : ∃ B : ℝ, ∀ k x, φ k x ≤ B

section Ops

variable [IsProbabilityMeasure μ] {ω : E → E → ℝ} {ρc : ℝ}

lemma KerData.colS_nonneg (hω : KerData μ ω ρc) (x : E) : 0 ≤ colS μ ω x :=
  integral_nonneg fun z => hω.nonneg z x

lemma KerData.measurable_colS (hω : KerData μ ω ρc) : Measurable (colS μ ω) := by
  have : StronglyMeasurable (fun p : E × E => ω p.2 p.1) :=
    (hω.meas.comp measurable_swap).stronglyMeasurable
  exact (this.integral_prod_right' (ν := μ)).measurable

lemma KerData.integrable_mul (hω : KerData μ ω ρc) {u : E → ℝ} (hu : Measurable u) {B : ℝ}
    (hb : ∀ z, |u z| ≤ B) (x : E) : Integrable (fun z => u z * ω z x) μ :=
  (hω.integrable x).bdd_mul hu.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hb z)

lemma KerData.measurable_Wop (hω : KerData μ ω ρc) {u : E → ℝ} (hu : Measurable u) :
    Measurable (fun x => ∫ z, u z * ω z x ∂μ) := by
  have : StronglyMeasurable (fun p : E × E => u p.2 * ω p.2 p.1) :=
    ((hu.comp measurable_snd).mul (hω.meas.comp measurable_swap)).stronglyMeasurable
  exact (this.integral_prod_right' (ν := μ)).measurable

lemma KerData.measurable_Kop (hω : KerData μ ω ρc) {u : E → ℝ} (hu : Measurable u) :
    Measurable (Kop μ ω u) :=
  (hω.measurable_Wop hu).add (hω.measurable_colS.mul_const _)

lemma KerData.Kop_nonneg (hω : KerData μ ω ρc) {u : E → ℝ} (hu0 : ∀ z, 0 ≤ u z) (x : E) :
    0 ≤ Kop μ ω u x :=
  add_nonneg (integral_nonneg fun z => mul_nonneg (hu0 z) (hω.nonneg z x))
    (mul_nonneg (hω.colS_nonneg x) (integral_nonneg hu0))

lemma KerData.Kop_le (hω : KerData μ ω ρc) {u : E → ℝ} (hu : Measurable u) (hu0 : ∀ z, 0 ≤ u z)
    {B : ℝ} (hb : ∀ z, u z ≤ B) (x : E) : Kop μ ω u x ≤ 2 * B * ρc := by
  have hB : 0 ≤ B := by
    have := hb x
    linarith [hu0 x]
  have h1 : ∫ z, u z * ω z x ∂μ ≤ B * ρc := by
    calc ∫ z, u z * ω z x ∂μ ≤ ∫ z, B * ω z x ∂μ :=
          integral_mono (hω.integrable_mul hu (B := B) (fun z => by
            rw [abs_of_nonneg (hu0 z)]; exact hb z) x)
            ((hω.integrable x).const_mul _) fun z => mul_le_mul_of_nonneg_right (hb z) (hω.nonneg z x)
      _ = B * colS μ ω x := integral_const_mul _ _
      _ ≤ B * ρc := mul_le_mul_of_nonneg_left (hω.col_le x) hB
  have h2 : ∫ z, u z ∂μ ≤ B := by
    calc ∫ z, u z ∂μ ≤ ∫ _z, B ∂μ := integral_mono_of_nonneg (Filter.Eventually.of_forall hu0)
          (integrable_const _) (Filter.Eventually.of_forall hb)
      _ = B := by simp
  have h3 : colS μ ω x * ∫ z, u z ∂μ ≤ ρc * B :=
    mul_le_mul (hω.col_le x) h2 (integral_nonneg hu0) ((hω.colS_nonneg x).trans (hω.col_le x))
  unfold Kop
  nlinarith

end Ops


section Step

variable [IsProbabilityMeasure μ] {ω : E → E → ℝ} {ρc : ℝ} {S : Spec E n}
  {p : Fin n → (Fin n → E) → E → ℝ}

lemma wlip_update {φ : Fin n → E → ℝ} {g : (Fin n → E) → ℝ} (hg : WLip φ g) (i : Fin n)
    (y y' : Fin n → E) (z : E) :
    |g (update y i z) - g (update y' i z)|
      ≤ ∑ k ∈ Finset.univ.erase i, if y k = y' k then 0 else φ k (y k) + φ k (y' k) := by
  refine (hg _ _).trans (le_of_eq ?_)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [update_self, ite_true, zero_add]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hki : k ≠ i := Finset.ne_of_mem_erase hk
  simp [update_of_ne hki]

lemma wlip_update_self {φ : Fin n → E → ℝ} (hφ0 : ∀ k x, 0 ≤ φ k x) {g : (Fin n → E) → ℝ}
    (hg : WLip φ g) (i : Fin n) (y : Fin n → E) (z z' : E) :
    |g (update y i z) - g (update y i z')| ≤ φ i z + φ i z' := by
  refine (hg _ _).trans ?_
  rw [Finset.sum_eq_single i]
  · simp only [update_self]
    split_ifs
    · exact add_nonneg (hφ0 _ _) (hφ0 _ _)
    · exact le_rfl
  · intro j _ hj
    simp [update_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma integral_mul_pair (hω : KerData μ ω ρc) {u : E → ℝ} (hu : Measurable u) {B : ℝ}
    (hb : ∀ z, |u z| ≤ B) (a b : E) :
    ∫ z, u z * (if a = b then 0 else ω z a + ω z b) ∂μ
      = if a = b then 0 else (∫ z, u z * ω z a ∂μ + ∫ z, u z * ω z b ∂μ) := by
  split_ifs with h
  · simp
  · simp_rw [mul_add]
    exact integral_add (hω.integrable_mul hu hb a) (hω.integrable_mul hu hb b)

lemma integral_pair (hω : KerData μ ω ρc) (a b : E) :
    ∫ z, (if a = b then 0 else ω z a + ω z b) ∂μ
      = if a = b then 0 else (colS μ ω a + colS μ ω b) := by
  split_ifs with h
  · simp
  · exact integral_add (hω.integrable a) (hω.integrable b)

lemma integrable_pair (hω : KerData μ ω ρc) (a b : E) :
    Integrable (fun z => if a = b then 0 else ω z a + ω z b) μ := by
  split_ifs with h
  · exact integrable_zero _ _ _
  · exact (hω.integrable a).add (hω.integrable b)

/-- The one-site operator maps the weighted class `WLip φ` into `WLip` of the shifted weights. -/
lemma site_wlip (hS : DensKernel μ S p) (hω : KerData μ ω ρc)
    (hosc : ∀ i x y z, |p i x z - p i y z|
      ≤ ∑ j ∈ Finset.univ.erase i, if x j = y j then 0 else ω z (x j) + ω z (y j))
    {φ : Fin n → E → ℝ} (hφ : GoodW φ) {g : (Fin n → E) → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) (hgl : WLip φ g) (i : Fin n) (y y' : Fin n → E) :
    |S.site i g y - S.site i g y'|
      ≤ ∑ k ∈ Finset.univ.erase i, if y k = y' k then 0 else
          ((φ k (y k) + Kop μ ω (φ i) (y k)) + (φ k (y' k) + Kop μ ω (φ i) (y' k))) := by
  obtain ⟨B, hB⟩ := hφ.bdd
  set C1 : ℝ := ∑ k ∈ Finset.univ.erase i, if y k = y' k then 0 else φ k (y k) + φ k (y' k) with hC1
  set Dz : E → ℝ := fun z => ∑ j ∈ Finset.univ.erase i,
    if y j = y' j then 0 else ω z (y j) + ω z (y' j) with hDz
  set F : E → ℝ := fun z => g (update y' i z) with hF
  have hsplit : S.site i g y - S.site i g y'
      = (∫ z, (g (update y i z) - g (update y' i z)) ∂(S.G i y))
        + ((∫ z, F z ∂(S.G i y)) - ∫ z, F z ∂(S.G i y')) := by
    have h1 : Integrable (fun z => g (update y i z)) (S.G i y) := integrable_section hg hgb i y
    have h2 : Integrable (fun z => F z) (S.G i y) :=
      Integrable.of_bound (measurable_section g hg i y').aestronglyMeasurable M
        (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hgb _)
    rw [integral_sub h1 h2]
    simp only [site, hF]
    ring
  have hfirst : |∫ z, (g (update y i z) - g (update y' i z)) ∂(S.G i y)| ≤ C1 := by
    have := norm_integral_le_of_norm_le_const (μ := S.G i y)
      (f := fun z => g (update y i z) - g (update y' i z)) (C := C1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact wlip_update hgl i y y' z)
    simpa using this
  have hFm : Measurable F := measurable_section g hg i y'
  have hDi : Integrable Dz μ := by
    simp only [hDz]
    exact integrable_finsetSum _ fun k _ => integrable_pair hω _ _
  have hsecond : |(∫ z, F z ∂(S.G i y)) - ∫ z, F z ∂(S.G i y')|
      ≤ ∑ k ∈ Finset.univ.erase i, if y k = y' k then 0 else
          (Kop μ ω (φ i) (y k) + Kop μ ω (φ i) (y' k)) := by
    rw [hS.integral_G, hS.integral_G]
    have hmain := abs_integral_mul_sub_le (μ := μ) (p₁ := p i y) (p₂ := p i y') (Dz := Dz)
      (φ := φ i) (F := F) (hS.integrable_p i y) (hS.integrable_p i y')
      (hS.integral_p i y) (hS.integral_p i y') hFm (M := M)
      (fun z => hgb _) (fun z => hosc i y y' z) hDi (hφ.meas i) (hφ.nonneg i) (B := B) (hB i)
      (fun z z' => wlip_update_self hφ.nonneg hgl i y' z z')
    refine hmain.trans (le_of_eq ?_)
    have hb : ∀ z, |φ i z| ≤ B := fun z => by rw [abs_of_nonneg (hφ.nonneg i z)]; exact hB i z
    have e1 : ∫ z, φ i z * Dz z ∂μ = ∑ k ∈ Finset.univ.erase i, if y k = y' k then 0 else
        (∫ z, φ i z * ω z (y k) ∂μ + ∫ z, φ i z * ω z (y' k) ∂μ) := by
      simp only [hDz, Finset.mul_sum]
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl fun k _ => integral_mul_pair hω (hφ.meas i) hb _ _
      · intro k _
        exact ((integrable_pair hω (y k) (y' k)).bdd_mul (hφ.meas i).aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb z))
    have e2 : ∫ z, Dz z ∂μ = ∑ k ∈ Finset.univ.erase i, if y k = y' k then 0 else
        (colS μ ω (y k) + colS μ ω (y' k)) := by
      simp only [hDz]
      rw [integral_finsetSum _ fun k _ => integrable_pair hω _ _]
      exact Finset.sum_congr rfl fun k _ => integral_pair hω _ _
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold Kop
    split_ifs <;> ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add hfirst hsecond).trans (le_of_eq ?_)
  rw [hC1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

end Step


section Scan

variable [IsProbabilityMeasure μ] {ω : E → E → ℝ} {ρc : ℝ} {S : Spec E n}
  {p : Fin n → (Fin n → E) → E → ℝ}

lemma scan_wlip [NeZero n] (hS : DensKernel μ S p) (hω : KerData μ ω ρc)
    (hosc : ∀ i x y z, |p i x z - p i y z|
      ≤ ∑ j ∈ Finset.univ.erase i, if x j = y j then 0 else ω z (x j) + ω z (y j))
    {φ : Fin n → E → ℝ} (hφ : GoodW φ) {g : (Fin n → E) → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) (hgl : WLip φ g) :
    WLip (stepW μ ω φ) (S.scan g) := by
  intro y y'
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold scan
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hn)]
  calc 1 / (n : ℝ) * |∑ i, (S.site i g y - S.site i g y')|
      ≤ 1 / (n : ℝ) * ∑ i, ∑ k ∈ Finset.univ.erase i, if y k = y' k then 0 else
          ((φ k (y k) + Kop μ ω (φ i) (y k)) + (φ k (y' k) + Kop μ ω (φ i) (y' k))) := by
        refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr hn).le
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => site_wlip hS hω hosc hφ hg hgb hgl i y y')
    _ = ∑ k, if y k = y' k then 0 else stepW μ ω φ k (y k) + stepW μ ω φ k (y' k) := by
        rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun k => Finset.univ.erase k)
          (fun i k => by simp [Finset.mem_erase, ne_comm]), Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : y k = y' k
        · simp [hk]
        · simp only [hk, ite_false, stepW]
          have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))]; simp
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hn1]
          field_simp

end Scan


/-- Admissible functions: measurable, nonnegative, bounded. -/
structure GoodF (u : E → ℝ) : Prop where
  meas : Measurable u
  nonneg : ∀ x, 0 ≤ u x
  bdd : ∃ B : ℝ, ∀ x, u x ≤ B

/-- The operator `Top u = (n-1) K u`. -/
def Top (μ : Measure E) (ω : E → E → ℝ) (n : ℕ) (u : E → ℝ) (x : E) : ℝ :=
  ((n : ℝ) - 1) * Kop μ ω u x

section Ops2

variable [IsProbabilityMeasure μ] {ω : E → E → ℝ} {ρc : ℝ}

lemma integrable_mul_bdd {a b : E → ℝ} (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (hA : ∀ x, |a x| ≤ A) (hB : ∀ x, |b x| ≤ B) : Integrable (fun x => a x * b x) μ :=
  (Integrable.of_bound hb.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hB x)).bdd_mul ha.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hA x)

lemma KerData.rho_nonneg (hω : KerData μ ω ρc) [Nonempty E] : 0 ≤ ρc :=
  (hω.colS_nonneg (Classical.arbitrary E)).trans (hω.col_le _)

lemma GoodF.integrable {u : E → ℝ} (hu : GoodF u) : Integrable u μ := by
  obtain ⟨B, hB⟩ := hu.bdd
  exact Integrable.of_bound hu.meas.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (hu.nonneg x)]; exact hB x)

lemma GoodF.abs_le {u : E → ℝ} (hu : GoodF u) : ∃ B, ∀ x, |u x| ≤ B := by
  obtain ⟨B, hB⟩ := hu.bdd
  exact ⟨B, fun x => by rw [abs_of_nonneg (hu.nonneg x)]; exact hB x⟩

lemma GoodF.Kop (hω : KerData μ ω ρc) {u : E → ℝ} (hu : GoodF u) : GoodF (Kop μ ω u) := by
  obtain ⟨B, hB⟩ := hu.bdd
  exact ⟨hω.measurable_Kop hu.meas, hω.Kop_nonneg hu.nonneg, 2 * B * ρc,
    hω.Kop_le hu.meas hu.nonneg hB⟩

lemma KerData.integrable_prod (hω : KerData μ ω ρc) :
    Integrable (fun p : E × E => ω p.2 p.1) (μ.prod μ) := by
  have hm : AEStronglyMeasurable (fun p : E × E => ω p.2 p.1) (μ.prod μ) :=
    (hω.meas.comp measurable_swap).aestronglyMeasurable
  rw [integrable_prod_iff hm]
  refine ⟨Filter.Eventually.of_forall fun x => hω.integrable x, ?_⟩
  have : (fun x => ∫ z, ‖ω z x‖ ∂μ) = colS μ ω := by
    funext x
    simp only [colS]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      simp [Real.norm_of_nonneg (hω.nonneg z x)])
  simp only
  rw [this]
  exact Integrable.of_bound hω.measurable_colS.aestronglyMeasurable ρc
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hω.colS_nonneg x)]; exact hω.col_le x)

lemma KerData.measurable_Wop' (hω : KerData μ ω ρc) {u : E → ℝ} (hu : Measurable u) :
    Measurable (fun z => ∫ x, u x * ω z x ∂μ) := by
  have : StronglyMeasurable (fun p : E × E => u p.2 * ω p.1 p.2) :=
    ((hu.comp measurable_snd).mul hω.meas).stronglyMeasurable
  exact (this.integral_prod_right' (ν := μ)).measurable

lemma GoodF.Tstar [NeZero n] (hω : KerData μ ω ρc) [Nonempty E] {u : E → ℝ} (hu : GoodF u) :
    GoodF (Tstar μ ω n u) := by
  obtain ⟨B, hB⟩ := hu.bdd
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    linarith
  have hB0 : 0 ≤ B := (hu.nonneg (Classical.arbitrary E)).trans (hB _)
  have hρ := hω.rho_nonneg
  have hcol : ∫ x, u x * colS μ ω x ∂μ ≤ B * ρc := by
    calc ∫ x, u x * colS μ ω x ∂μ ≤ ∫ _x, B * ρc ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
            mul_nonneg (hu.nonneg x) (hω.colS_nonneg x)) (integrable_const _)
            (Filter.Eventually.of_forall fun x => ?_)
          exact mul_le_mul (hB x) (hω.col_le x) (hω.colS_nonneg x) hB0
      _ = B * ρc := by simp
  have hrow : ∀ z, ∫ x, u x * ω z x ∂μ ≤ B * ρc := fun z => by
    calc ∫ x, u x * ω z x ∂μ ≤ ∫ x, B * ω z x ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
            mul_nonneg (hu.nonneg x) (hω.nonneg z x)) ((hω.row_integrable z).const_mul _)
            (Filter.Eventually.of_forall fun x => mul_le_mul_of_nonneg_right (hB x) (hω.nonneg z x))
      _ = B * ∫ x, ω z x ∂μ := integral_const_mul _ _
      _ ≤ B * ρc := mul_le_mul_of_nonneg_left (hω.row_le z) hB0
  refine ⟨?_, fun z => ?_, ((n : ℝ) - 1) * (B * ρc + B * ρc), fun z => ?_⟩
  · exact (measurable_const.mul ((hω.measurable_Wop' hu.meas).add
      (measurable_const (a := ∫ x, u x * colS μ ω x ∂μ))))
  · exact mul_nonneg hn1 (add_nonneg (integral_nonneg fun x => mul_nonneg (hu.nonneg x) (hω.nonneg z x))
      (integral_nonneg fun x => mul_nonneg (hu.nonneg x) (hω.colS_nonneg x)))
  · exact mul_le_mul_of_nonneg_left (add_le_add (hrow z) hcol) hn1

lemma GoodF.Top [NeZero n] (hω : KerData μ ω ρc) [Nonempty E] {u : E → ℝ} (hu : GoodF u) :
    GoodF (Top μ ω n u) := by
  obtain ⟨B, hB⟩ := (hu.Kop hω).bdd
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    linarith
  exact ⟨measurable_const.mul (hu.Kop hω).meas, fun x => mul_nonneg hn1 ((hu.Kop hω).nonneg x),
    ((n : ℝ) - 1) * B, fun x => mul_le_mul_of_nonneg_left (hB x) hn1⟩

/-- Pairing identity (Fubini): `∫ u · Top Θ = ∫ Θ · T* u`. -/
lemma pairing [NeZero n] (hω : KerData μ ω ρc) [Nonempty E] {u Θ : E → ℝ} (hu : GoodF u)
    (hΘ : GoodF Θ) :
    ∫ x, u x * Top μ ω n Θ x ∂μ = ∫ z, Θ z * Tstar μ ω n u z ∂μ := by
  obtain ⟨Bu, hBu⟩ := hu.abs_le
  obtain ⟨BΘ, hBΘ⟩ := hΘ.abs_le
  have hρ := hω.rho_nonneg
  -- Fubini for the kernel part
  have hF : ∫ x, u x * (∫ z, Θ z * ω z x ∂μ) ∂μ = ∫ z, Θ z * (∫ x, u x * ω z x ∂μ) ∂μ := by
    have hint : Integrable (Function.uncurry fun x z : E => u x * (Θ z * ω z x)) (μ.prod μ) := by
      have : Integrable (fun p : E × E => (u p.1 * Θ p.2) * ω p.2 p.1) (μ.prod μ) :=
        hω.integrable_prod.bdd_mul
          ((hu.meas.comp measurable_fst).mul (hΘ.meas.comp measurable_snd)).aestronglyMeasurable
          (c := Bu * BΘ) (Filter.Eventually.of_forall fun p => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul (hBu _) (hBΘ _) (abs_nonneg _) ((abs_nonneg _).trans (hBu p.1)))
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp [Function.uncurry]; ring
    have := integral_integral_swap hint
    calc ∫ x, u x * (∫ z, Θ z * ω z x ∂μ) ∂μ = ∫ x, ∫ z, u x * (Θ z * ω z x) ∂μ ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only
          rw [integral_const_mul]
      _ = ∫ z, ∫ x, u x * (Θ z * ω z x) ∂μ ∂μ := this
      _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only; ring
  -- bounded integrands
  have hWΘ : ∀ x, ∫ z, Θ z * ω z x ∂μ ≤ BΘ * ρc := fun x => by
    calc ∫ z, Θ z * ω z x ∂μ ≤ ∫ z, BΘ * ω z x ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z =>
            mul_nonneg (hΘ.nonneg z) (hω.nonneg z x)) ((hω.integrable x).const_mul _)
            (Filter.Eventually.of_forall fun z => mul_le_mul_of_nonneg_right
              ((le_abs_self _).trans (hBΘ z)) (hω.nonneg z x))
      _ = BΘ * colS μ ω x := integral_const_mul _ _
      _ ≤ BΘ * ρc := mul_le_mul_of_nonneg_left (hω.col_le x)
            ((abs_nonneg _).trans (hBΘ (Classical.arbitrary E)))
  have hWm : Measurable (fun x => ∫ z, Θ z * ω z x ∂μ) := hω.measurable_Wop hΘ.meas
  have hWb : ∀ x, |∫ z, Θ z * ω z x ∂μ| ≤ BΘ * ρc := fun x => by
    rw [abs_of_nonneg (integral_nonneg fun z => mul_nonneg (hΘ.nonneg z) (hω.nonneg z x))]
    exact hWΘ x
  have hab : ∀ z, ∫ x, u x * ω z x ∂μ ≤ Bu * ρc := fun z => by
    calc ∫ x, u x * ω z x ∂μ ≤ ∫ x, Bu * ω z x ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
            mul_nonneg (hu.nonneg x) (hω.nonneg z x)) ((hω.row_integrable z).const_mul _)
            (Filter.Eventually.of_forall fun x => mul_le_mul_of_nonneg_right
              ((le_abs_self _).trans (hBu x)) (hω.nonneg z x))
      _ = Bu * ∫ x, ω z x ∂μ := integral_const_mul _ _
      _ ≤ Bu * ρc := mul_le_mul_of_nonneg_left (hω.row_le z)
            ((abs_nonneg _).trans (hBu (Classical.arbitrary E)))
  have habm : Measurable (fun z => ∫ x, u x * ω z x ∂μ) := hω.measurable_Wop' hu.meas
  have hcb : ∀ x, |colS μ ω x| ≤ ρc := fun x => by
    rw [abs_of_nonneg (hω.colS_nonneg x)]; exact hω.col_le x
  have hI1 : Integrable (fun x => u x * ∫ z, Θ z * ω z x ∂μ) μ :=
    integrable_mul_bdd hu.meas hWm hBu hWb
  have hI2 : Integrable (fun x => u x * colS μ ω x) μ :=
    integrable_mul_bdd hu.meas hω.measurable_colS hBu hcb
  have hI3 : Integrable (fun z => Θ z * ∫ x, u x * ω z x ∂μ) μ :=
    integrable_mul_bdd hΘ.meas habm hBΘ (fun z => by
      rw [abs_of_nonneg (integral_nonneg fun x => mul_nonneg (hu.nonneg x) (hω.nonneg z x))]
      exact hab z)
  have hI4 : Integrable (fun z => Θ z) μ := hΘ.integrable
  have lhs : ∫ x, u x * Top μ ω n Θ x ∂μ
      = ((n : ℝ) - 1) * (∫ x, u x * (∫ z, Θ z * ω z x ∂μ) ∂μ)
        + ((n : ℝ) - 1) * (∫ z, Θ z ∂μ) * ∫ x, u x * colS μ ω x ∂μ := by
    have : ∀ x, u x * Top μ ω n Θ x
        = ((n : ℝ) - 1) * (u x * (∫ z, Θ z * ω z x ∂μ))
          + (((n : ℝ) - 1) * (∫ z, Θ z ∂μ)) * (u x * colS μ ω x) := fun x => by
      unfold Top Kop; ring
    simp_rw [this]
    rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul]
  have rhs : ∫ z, Θ z * Tstar μ ω n u z ∂μ
      = ((n : ℝ) - 1) * (∫ z, Θ z * (∫ x, u x * ω z x ∂μ) ∂μ)
        + ((n : ℝ) - 1) * (∫ x, u x * colS μ ω x ∂μ) * ∫ z, Θ z ∂μ := by
    have : ∀ z, Θ z * Tstar μ ω n u z
        = ((n : ℝ) - 1) * (Θ z * (∫ x, u x * ω z x ∂μ))
          + (((n : ℝ) - 1) * (∫ x, u x * colS μ ω x ∂μ)) * Θ z := fun z => by
      unfold Tstar; ring
    simp_rw [this]
    rw [integral_add (hI3.const_mul _) (hI4.const_mul _), integral_const_mul, integral_const_mul]
  rw [lhs, rhs, hF]
  ring

end Ops2


section Rec

variable [IsProbabilityMeasure μ] {ω : E → E → ℝ} {ρc : ℝ}

lemma Kop_const_mul (c : ℝ) (u : E → ℝ) (x : E) :
    Kop μ ω (fun z => c * u z) x = c * Kop μ ω u x := by
  unfold Kop
  have : ∀ z, c * u z * ω z x = c * (u z * ω z x) := fun z => by ring
  simp_rw [this]
  rw [integral_const_mul, integral_const_mul]
  ring

lemma Kop_sum (hω : KerData μ ω ρc) {ι : Type*} (s : Finset ι) (u : ι → E → ℝ)
    (hu : ∀ i ∈ s, GoodF (u i)) (x : E) :
    Kop μ ω (fun z => ∑ i ∈ s, u i z) x = ∑ i ∈ s, Kop μ ω (u i) x := by
  unfold Kop
  have h1 : ∫ z, (∑ i ∈ s, u i z) * ω z x ∂μ = ∑ i ∈ s, ∫ z, u i z * ω z x ∂μ := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum]
    intro i hi
    obtain ⟨B, hB⟩ := (hu i hi).abs_le
    exact hω.integrable_mul (hu i hi).meas hB x
  have h2 : ∫ z, ∑ i ∈ s, u i z ∂μ = ∑ i ∈ s, ∫ z, u i z ∂μ :=
    integral_finsetSum _ fun i hi => (hu i hi).integrable
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]

lemma GoodW.step [NeZero n] [Nonempty E] (hω : KerData μ ω ρc) {φ : Fin n → E → ℝ}
    (hφ : GoodW φ) : GoodW (stepW μ ω φ) := by
  obtain ⟨B, hB⟩ := hφ.bdd
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hgood : ∀ i, GoodF (φ i) := fun i => ⟨hφ.meas i, hφ.nonneg i, B, hB i⟩
  have hc : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hn]; exact hn1
  have hB0 : 0 ≤ B := (hφ.nonneg ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ (Classical.arbitrary E)).trans
    (hB _ _)
  have hρ := hω.rho_nonneg
  refine ⟨fun k => ?_, fun k x => ?_, B + 2 * B * ρc, fun k x => ?_⟩
  · exact (measurable_const.mul (hφ.meas k)).add (measurable_const.mul
      (Finset.measurable_sum _ fun i _ => (hgood i).Kop hω |>.meas))
  · exact add_nonneg (mul_nonneg hc (hφ.nonneg k x)) (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => ((hgood i).Kop hω).nonneg x))
  · have h1 : ∑ i ∈ Finset.univ.erase k, Kop μ ω (φ i) x ≤ n * (2 * B * ρc) := by
      calc ∑ i ∈ Finset.univ.erase k, Kop μ ω (φ i) x
          ≤ ∑ _i ∈ Finset.univ.erase k, (2 * B * ρc) :=
            Finset.sum_le_sum fun i _ => hω.Kop_le (hφ.meas i) (hφ.nonneg i) (hB i) x
        _ = ((Finset.univ.erase k).card : ℝ) * (2 * B * ρc) := by simp
        _ ≤ n * (2 * B * ρc) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast (Finset.card_erase_le).trans (by simp)
    unfold stepW
    have h2 : (1 - 1 / (n : ℝ)) * φ k x ≤ B := by
      calc (1 - 1 / (n : ℝ)) * φ k x ≤ 1 * B :=
            mul_le_mul (by linarith [one_div_pos.mpr hn]) (hB k x) (hφ.nonneg k x) zero_le_one
        _ = B := one_mul _
    have h3 : 1 / (n : ℝ) * ∑ i ∈ Finset.univ.erase k, Kop μ ω (φ i) x ≤ 2 * B * ρc := by
      calc 1 / (n : ℝ) * ∑ i ∈ Finset.univ.erase k, Kop μ ω (φ i) x
          ≤ 1 / (n : ℝ) * (n * (2 * B * ρc)) :=
            mul_le_mul_of_nonneg_left h1 (one_div_pos.mpr hn).le
        _ = 2 * B * ρc := by field_simp
    linarith

/-- The total weight `Φ̄ = ∑_k φ_k` satisfies `Φ̄' = (1 - 1/n) Φ̄ + (1/n) T Φ̄`. -/
lemma Phi_step [NeZero n] (hω : KerData μ ω ρc) {φ : Fin n → E → ℝ} (hφ : GoodW φ) (x : E) :
    ∑ k, stepW μ ω φ k x
      = (1 - 1 / (n : ℝ)) * ∑ k, φ k x + (1 / (n : ℝ)) * Top μ ω n (fun z => ∑ k, φ k z) x := by
  obtain ⟨B, hB⟩ := hφ.bdd
  have hgood : ∀ i, GoodF (φ i) := fun i => ⟨hφ.meas i, hφ.nonneg i, B, hB i⟩
  have e : ∑ k, ∑ i ∈ Finset.univ.erase k, Kop μ ω (φ i) x
      = ((n : ℝ) - 1) * Kop μ ω (fun z => ∑ k, φ k z) x := by
    rw [Kop_sum hω Finset.univ φ (fun i _ => hgood i), Finset.mul_sum]
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun k => Finset.univ.erase k)
      (fun i k => by simp [Finset.mem_erase, ne_comm])]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))]; simp
    rw [hn1]
  unfold stepW Top
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e]

end Rec


section Iter

variable [IsProbabilityMeasure μ] {ω : E → E → ℝ} {ρc : ℝ} {S S' : Spec E n}
  {p p' : Fin n → (Fin n → E) → E → ℝ}

lemma iter_wlip [NeZero n] [Nonempty E] (hS : DensKernel μ S p) (hω : KerData μ ω ρc)
    (hosc : ∀ i x y z, |p i x z - p i y z|
      ≤ ∑ j ∈ Finset.univ.erase i, if x j = y j then 0 else ω z (x j) + ω z (y j))
    {φ0 : Fin n → E → ℝ} (hφ0 : GoodW φ0) {f : (Fin n → E) → ℝ} (hf : Measurable f) {M : ℝ}
    (hfb : ∀ x, |f x| ≤ M) (hfl : WLip φ0 f) (m : ℕ) :
    GoodW ((stepW μ ω)^[m] φ0) ∧ Measurable (S.scan^[m] f) ∧ (∀ x, |S.scan^[m] f x| ≤ M) ∧
      WLip ((stepW μ ω)^[m] φ0) (S.scan^[m] f) := by
  induction m with
  | zero => exact ⟨hφ0, hf, hfb, hfl⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨h1.step hω, measurable_scan h2, fun x => abs_scan_le h3 x,
      scan_wlip hS hω hosc h1 h2 h3 h4⟩

lemma scan_diff [NeZero n] (hS : DensKernel μ S p) (hS' : DensKernel μ S' p') {D : E → ℝ}
    (hDm : Measurable D) (hD0 : ∀ z, 0 ≤ D z) {BD : ℝ} (hDb : ∀ z, D z ≤ BD)
    (hpD : ∀ i x z, |p' i x z - p i x z| ≤ D z)
    {φ : Fin n → E → ℝ} (hφ : GoodW φ) {g : (Fin n → E) → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ x, |g x| ≤ M) (hgl : WLip φ g) (y : Fin n → E) :
    |S'.scan g y - S.scan g y|
      ≤ (1 / (n : ℝ)) * ∫ z, (∑ k, φ k z) * (D z + ∫ w, D w ∂μ) ∂μ := by
  obtain ⟨B, hB⟩ := hφ.bdd
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hDi : Integrable D μ :=
    Integrable.of_bound hDm.aestronglyMeasurable BD (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hD0 z)]; exact hDb z)
  have hgood : ∀ i, GoodF (φ i) := fun i => ⟨hφ.meas i, hφ.nonneg i, B, hB i⟩
  have hper : ∀ i, |S'.site i g y - S.site i g y|
      ≤ ∫ z, φ i z * D z ∂μ + (∫ z, φ i z ∂μ) * ∫ z, D z ∂μ := by
    intro i
    rw [hS'.site_eq, hS.site_eq]
    exact abs_integral_mul_sub_le (μ := μ) (p₁ := p' i y) (p₂ := p i y) (Dz := D) (φ := φ i)
      (F := fun z => g (update y i z)) (hS'.integrable_p i y) (hS.integrable_p i y)
      (hS'.integral_p i y) (hS.integral_p i y) (measurable_section g hg i y) (M := M)
      (fun z => hgb _) (fun z => hpD i y z) hDi (hφ.meas i) (hφ.nonneg i) (B := B) (hB i)
      (fun z z' => wlip_update_self hφ.nonneg hgl i y z z')
  unfold scan
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hn)]
  refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr hn).le
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hper i).trans (le_of_eq ?_)
  have e1 : ∫ z, (∑ k, φ k z) * (D z + ∫ w, D w ∂μ) ∂μ
      = ∑ k, (∫ z, φ k z * D z ∂μ + (∫ z, φ k z ∂μ) * ∫ w, D w ∂μ) := by
    have : ∀ z, (∑ k, φ k z) * (D z + ∫ w, D w ∂μ)
        = ∑ k, (φ k z * D z + (∫ w, D w ∂μ) * φ k z) := fun z => by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    simp_rw [this]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hφk : Integrable (φ k) μ := (hgood k).integrable
      have hφD : Integrable (fun z => φ k z * D z) μ :=
        integrable_mul_bdd (hφ.meas k) hDm (A := B) (B := BD)
          (fun z => by rw [abs_of_nonneg (hφ.nonneg k z)]; exact hB k z)
          (fun z => by rw [abs_of_nonneg (hD0 z)]; exact hDb z)
      rw [integral_add hφD (hφk.const_mul _), integral_const_mul]
      ring
    · intro k _
      have hφk : Integrable (φ k) μ := (hgood k).integrable
      have hφD : Integrable (fun z => φ k z * D z) μ :=
        integrable_mul_bdd (hφ.meas k) hDm (A := B) (B := BD)
          (fun z => by rw [abs_of_nonneg (hφ.nonneg k z)]; exact hB k z)
          (fun z => by rw [abs_of_nonneg (hD0 z)]; exact hDb z)
      exact hφD.add (hφk.const_mul _)
  rw [e1]

lemma telescope [NeZero n] (S S' : Spec E n) {f : (Fin n → E) → ℝ} (hf : Measurable f) {M : ℝ}
    (hfb : ∀ x, |f x| ≤ M) (ℓ : ℕ) :
    ∫ x, f x ∂S'.P - ∫ x, f x ∂S.P
      = ∑ m ∈ Finset.range ℓ, ∫ x, (S'.scan (S.scan^[m] f) x - S.scan (S.scan^[m] f) x) ∂S'.P
        + (∫ x, S.scan^[ℓ] f x ∂S'.P - ∫ x, S.scan^[ℓ] f x ∂S.P) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    obtain ⟨hm, hb, -⟩ := integral_scan_iterate (S := S) hf hfb ℓ
    rw [Finset.sum_range_succ, ih]
    have h1 := integral_scan (S := S') hm hb
    have h2 := integral_scan (S := S) hm hb
    have hi1 : Integrable (S'.scan (S.scan^[ℓ] f)) S'.P :=
      integrable_of_bdd (measurable_scan hm) (abs_scan_le hb)
    have hi2 : Integrable (S.scan (S.scan^[ℓ] f)) S'.P :=
      integrable_of_bdd (measurable_scan hm) (abs_scan_le hb)
    rw [integral_sub hi1 hi2]
    rw [Function.iterate_succ_apply']
    linarith

end Iter


section Theta

variable [IsProbabilityMeasure μ] {ω : E → E → ℝ} {ρc : ℝ}

lemma GoodF.const_mul' {u : E → ℝ} (hu : GoodF u) {c : ℝ} (hc : 0 ≤ c) :
    GoodF (fun z => c * u z) := by
  obtain ⟨B, hB⟩ := hu.bdd
  exact ⟨measurable_const.mul hu.meas, fun z => mul_nonneg hc (hu.nonneg z), c * B,
    fun z => mul_le_mul_of_nonneg_left (hB z) hc⟩

lemma GoodF.sum {ι : Type*} (s : Finset ι) {u : ι → E → ℝ} (hu : ∀ i ∈ s, GoodF (u i)) :
    GoodF (fun z => ∑ i ∈ s, u i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨measurable_const, fun _ => by simp, 0, fun _ => by simp⟩
  | insert a s ha ih =>
    have h1 := hu a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hu i (Finset.mem_insert_of_mem hi)
    obtain ⟨B1, hB1⟩ := h1.bdd
    obtain ⟨B2, hB2⟩ := h2.bdd
    refine ⟨?_, fun z => ?_, B1 + B2, fun z => ?_⟩
    · simp_rw [Finset.sum_insert ha]; exact h1.meas.add h2.meas
    · simp_rw [Finset.sum_insert ha]; exact add_nonneg (h1.nonneg z) (h2.nonneg z)
    · simp_rw [Finset.sum_insert ha]; exact add_le_add (hB1 z) (hB2 z)

lemma integral_mul_le_of_le {a b c : E → ℝ} (ha : GoodF a) (hb : GoodF b) (hc : GoodF c)
    (h : ∀ x, b x ≤ c x) : ∫ x, a x * b x ∂μ ≤ ∫ x, a x * c x ∂μ := by
  obtain ⟨A, hA⟩ := ha.abs_le
  obtain ⟨B, hB⟩ := hb.abs_le
  obtain ⟨C, hC⟩ := hc.abs_le
  exact integral_mono (integrable_mul_bdd ha.meas hb.meas hA hB) (integrable_mul_bdd ha.meas hc.meas hA hC)
    fun x => mul_le_mul_of_nonneg_left (h x) (ha.nonneg x)

/-- Core summation estimate for the dual weights. -/
lemma theta_bound [NeZero n] [Nonempty E] (hω : KerData μ ω ρc) {Φ : ℕ → E → ℝ}
    (hΦ : ∀ m, GoodF (Φ m))
    (hrec : ∀ m x, Φ (m + 1) x = (1 - 1 / (n : ℝ)) * Φ m x + (1 / (n : ℝ)) * Top μ ω n (Φ m) x)
    {v0 : E → ℝ} (hv0 : GoodF v0) {B2 : ℝ}
    (hB2 : ∀ z, Tstar μ ω n (Tstar μ ω n v0) z ≤ B2)
    (hε : ((n : ℝ) - 1) * (2 * ρc) ≤ 1 / 2) (ℓ : ℕ) :
    ∫ z, (1 / (n : ℝ)) * (∑ m ∈ Finset.range ℓ, Φ m z) * v0 z ∂μ
      ≤ ∫ z, Φ 0 z * (v0 z + Tstar μ ω n v0 z + 2 * B2) ∂μ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hinv : 0 ≤ 1 / (n : ℝ) := (one_div_pos.mpr hn).le
  set Θ : E → ℝ := fun z => ∑ m ∈ Finset.range ℓ, (1 / (n : ℝ)) * Φ m z with hΘ
  have hΘg : GoodF Θ := GoodF.sum _ fun m _ => (hΦ m).const_mul' hinv
  have hrewr : ∀ z, (1 / (n : ℝ)) * (∑ m ∈ Finset.range ℓ, Φ m z) = Θ z := fun z => by
    simp only [hΘ]; rw [Finset.mul_sum]
  -- Top of Θ
  have hTopΘ : ∀ x, Top μ ω n Θ x = ∑ m ∈ Finset.range ℓ, (1 / (n : ℝ)) * Top μ ω n (Φ m) x := by
    intro x
    unfold Top
    simp only [hΘ]
    rw [Kop_sum hω _ (fun m z => (1 / (n : ℝ)) * Φ m z) (fun m _ => (hΦ m).const_mul' hinv),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Kop_const_mul]; ring
  -- Θ + Φ ℓ = Φ 0 + Top Θ
  have hid : ∀ ℓ' x, (∑ m ∈ Finset.range ℓ', (1 / (n : ℝ)) * Φ m x) + Φ ℓ' x
      = Φ 0 x + ∑ m ∈ Finset.range ℓ', (1 / (n : ℝ)) * Top μ ω n (Φ m) x := by
    intro ℓ' x
    induction ℓ' with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hrec k x]
      linarith
  have hle : ∀ x, Θ x ≤ Φ 0 x + Top μ ω n Θ x := by
    intro x
    have := hid ℓ x
    rw [hTopΘ x]
    simp only [hΘ]
    linarith [(hΦ ℓ).nonneg x]
  have hTg : GoodF (Top μ ω n Θ) := hΘg.Top hω
  -- pairing inequality
  have hpair : ∀ u : E → ℝ, GoodF u →
      ∫ x, u x * Θ x ∂μ ≤ ∫ x, u x * Φ 0 x ∂μ + ∫ z, Θ z * Tstar μ ω n u z ∂μ := by
    intro u hu
    have h1 : ∫ x, u x * Θ x ∂μ ≤ ∫ x, u x * (Φ 0 x + Top μ ω n Θ x) ∂μ :=
      integral_mul_le_of_le hu hΘg (⟨(hΦ 0).meas.add hTg.meas, fun x => add_nonneg ((hΦ 0).nonneg x)
        (hTg.nonneg x), by
          obtain ⟨b1, hb1⟩ := (hΦ 0).bdd
          obtain ⟨b2, hb2⟩ := hTg.bdd
          exact ⟨b1 + b2, fun x => add_le_add (hb1 x) (hb2 x)⟩⟩ : GoodF (fun x => Φ 0 x + Top μ ω n Θ x))
        hle
    refine h1.trans (le_of_eq ?_)
    have : ∀ x, u x * (Φ 0 x + Top μ ω n Θ x) = u x * Φ 0 x + u x * Top μ ω n Θ x := fun x => by ring
    simp_rw [this]
    rw [integral_add, pairing hω hu hΘg]
    · obtain ⟨A, hA⟩ := hu.abs_le
      obtain ⟨B, hB⟩ := (hΦ 0).abs_le
      exact integrable_mul_bdd hu.meas (hΦ 0).meas hA hB
    · obtain ⟨A, hA⟩ := hu.abs_le
      obtain ⟨B, hB⟩ := hTg.abs_le
      exact integrable_mul_bdd hu.meas hTg.meas hA hB
  -- Tstar 1 ≤ 1/2
  have hone : GoodF (fun _ : E => (1 : ℝ)) := ⟨measurable_const, fun _ => zero_le_one, 1, fun _ => le_rfl⟩
  have hT1 : ∀ z, Tstar μ ω n (fun _ : E => (1 : ℝ)) z ≤ 1 / 2 := by
    intro z
    unfold Tstar
    have h1 : ∫ x, (1 : ℝ) * ω z x ∂μ ≤ ρc := by simpa using hω.row_le z
    have h2 : ∫ x, (1 : ℝ) * colS μ ω x ∂μ ≤ ρc := by
      calc ∫ x, (1 : ℝ) * colS μ ω x ∂μ ≤ ∫ _x, ρc ∂μ :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by
              show (0 : ℝ) ≤ 1 * colS μ ω x
              rw [one_mul]; exact hω.colS_nonneg x) (integrable_const _)
              (Filter.Eventually.of_forall fun x => by
                show 1 * colS μ ω x ≤ ρc
                rw [one_mul]; exact hω.col_le x)
        _ = ρc := by simp
    calc ((n : ℝ) - 1) * (∫ x, (1 : ℝ) * ω z x ∂μ + ∫ x, (1 : ℝ) * colS μ ω x ∂μ)
        ≤ ((n : ℝ) - 1) * (ρc + ρc) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by linarith)
      _ = ((n : ℝ) - 1) * (2 * ρc) := by ring
      _ ≤ 1 / 2 := hε
  have hmass : ∫ z, Θ z ∂μ ≤ 2 * ∫ z, Φ 0 z ∂μ := by
    have := hpair (fun _ => 1) hone
    simp only [one_mul] at this
    have h2 : ∫ z, Θ z * Tstar μ ω n (fun _ : E => (1 : ℝ)) z ∂μ ≤ ∫ z, Θ z * (1 / 2) ∂μ :=
      integral_mul_le_of_le hΘg ((hone.Tstar hω)) ⟨measurable_const, fun _ => by norm_num, 1, fun _ => by norm_num⟩ hT1
    rw [integral_mul_const] at h2
    linarith
  -- chain
  have hu1 : GoodF (Tstar μ ω n v0) := hv0.Tstar hω
  have hu2 : GoodF (Tstar μ ω n (Tstar μ ω n v0)) := hu1.Tstar hω
  have hB2' : 0 ≤ B2 := (hu2.nonneg (Classical.arbitrary E)).trans (hB2 _)
  have c1 := hpair v0 hv0
  have c2 := hpair _ hu1
  have c3 : ∫ z, Θ z * Tstar μ ω n (Tstar μ ω n v0) z ∂μ ≤ ∫ z, Θ z * B2 ∂μ :=
    integral_mul_le_of_le hΘg hu2 ⟨measurable_const, fun _ => hB2', B2, fun _ => le_rfl⟩ hB2
  rw [integral_mul_const] at c3
  have e1 : ∫ z, (1 / (n : ℝ)) * (∑ m ∈ Finset.range ℓ, Φ m z) * v0 z ∂μ = ∫ x, v0 x * Θ x ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [hrewr z]; ring
  have e2 : ∫ z, Φ 0 z * (v0 z + Tstar μ ω n v0 z + 2 * B2) ∂μ
      = ∫ x, v0 x * Φ 0 x ∂μ + ∫ x, Tstar μ ω n v0 x * Φ 0 x ∂μ + 2 * B2 * ∫ z, Φ 0 z ∂μ := by
    have hF0 := (hΦ 0)
    obtain ⟨A0, hA0⟩ := hF0.abs_le
    obtain ⟨A1, hA1⟩ := hv0.abs_le
    obtain ⟨A2, hA2⟩ := hu1.abs_le
    have i1 : Integrable (fun x => v0 x * Φ 0 x) μ := integrable_mul_bdd hv0.meas hF0.meas hA1 hA0
    have i2 : Integrable (fun x => Tstar μ ω n v0 x * Φ 0 x) μ :=
      integrable_mul_bdd hu1.meas hF0.meas hA2 hA0
    have i3 : Integrable (fun x => 2 * B2 * Φ 0 x) μ := hF0.integrable.const_mul _
    have : ∀ z, Φ 0 z * (v0 z + Tstar μ ω n v0 z + 2 * B2)
        = v0 z * Φ 0 z + Tstar μ ω n v0 z * Φ 0 z + 2 * B2 * Φ 0 z := fun z => by ring
    simp_rw [this]
    have h1 : ∫ z, (v0 z * Φ 0 z + Tstar μ ω n v0 z * Φ 0 z + 2 * B2 * Φ 0 z) ∂μ
        = ∫ z, (v0 z * Φ 0 z + Tstar μ ω n v0 z * Φ 0 z) ∂μ + ∫ z, 2 * B2 * Φ 0 z ∂μ :=
      integral_add (i1.add i2) i3
    have h2 : ∫ z, (v0 z * Φ 0 z + Tstar μ ω n v0 z * Φ 0 z) ∂μ
        = ∫ z, v0 z * Φ 0 z ∂μ + ∫ z, Tstar μ ω n v0 z * Φ 0 z ∂μ := integral_add i1 i2
    rw [h1, h2, integral_const_mul]
  rw [e1, e2]
  have hc : ∫ x, Tstar μ ω n v0 x * Θ x ∂μ = ∫ z, Θ z * Tstar μ ω n v0 z ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only; ring)
  have c2' : ∫ x, Tstar μ ω n v0 x * Θ x ∂μ ≤ ∫ x, Tstar μ ω n v0 x * Φ 0 x ∂μ
      + ∫ z, Θ z * Tstar μ ω n (Tstar μ ω n v0) z ∂μ := c2
  nlinarith [c1, c2', c3, hmass, hB2', hc]

end Theta


section Main

variable [IsProbabilityMeasure μ] {ω : E → E → ℝ} {ρc : ℝ} {S S' : Spec E n}
  {p p' : Fin n → (Fin n → E) → E → ℝ}

/-- **Weighted comparison of two one-site specifications** (function side of
`Q:eq:measure-disagreement`).  If the one-site densities of `S` depend on the neighbours through
the kernel `ω`, `|p' - p| ≤ D`, and `S` is Dobrushin-contracting, then for every bounded
measurable `f` the difference of the `i₀`-th coordinate expectations is bounded by
`∫ |f| (v₀ + T* v₀ + 2 B₂)`, `v₀ = D + ∫ D`, `B₂ ≥ T*² v₀`. -/
theorem pointwise_marginal_comparison [NeZero n] [Nonempty E]
    (hS : DensKernel μ S p) (hS' : DensKernel μ S' p') (hω : KerData μ ω ρc)
    (hosc : ∀ i x y z, |p i x z - p i y z|
      ≤ ∑ j ∈ Finset.univ.erase i, if x j = y j then 0 else ω z (x j) + ω z (y j))
    {D : E → ℝ} (hDm : Measurable D) (hD0 : ∀ z, 0 ≤ D z) {BD : ℝ} (hDb : ∀ z, D z ≤ BD)
    (hpD : ∀ i x z, |p' i x z - p i x z| ≤ D z)
    {c : Fin n → Fin n → ℝ} (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) (hr : r < 1)
    (hε : ((n : ℝ) - 1) * (2 * ρc) ≤ 1 / 2) {B2 : ℝ}
    (hB2 : ∀ z, Tstar μ ω n (Tstar μ ω n (fun z => D z + ∫ w, D w ∂μ)) z ≤ B2)
    (i0 : Fin n) {f : E → ℝ} (hf : Measurable f) {M : ℝ} (hfb : ∀ z, |f z| ≤ M) :
    |∫ x, f (x i0) ∂S'.P - ∫ x, f (x i0) ∂S.P|
      ≤ ∫ z, |f z| * ((D z + ∫ w, D w ∂μ) + Tstar μ ω n (fun z => D z + ∫ w, D w ∂μ) z
          + 2 * B2) ∂μ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set v0 : E → ℝ := fun z => D z + ∫ w, D w ∂μ with hv0def
  have hDi : Integrable D μ :=
    Integrable.of_bound hDm.aestronglyMeasurable BD (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hD0 z)]; exact hDb z)
  have hI0 : 0 ≤ ∫ w, D w ∂μ := integral_nonneg hD0
  have hv0 : GoodF v0 :=
    ⟨hDm.add measurable_const, fun z => add_nonneg (hD0 z) hI0, BD + ∫ w, D w ∂μ,
      fun z => add_le_add (hDb z) le_rfl⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfb (Classical.arbitrary E))
  -- initial weights
  set φ0 : Fin n → E → ℝ := fun j z => if j = i0 then |f z| else 0 with hφ0def
  have hφ0 : GoodW φ0 :=
    ⟨fun j => by simp only [hφ0def]; split_ifs; exacts [hf.abs, measurable_const],
      fun j z => by simp only [hφ0def]; split_ifs; exacts [abs_nonneg _, le_rfl],
      M, fun j z => by simp only [hφ0def]; split_ifs; exacts [hfb z, hM0]⟩
  set f' : (Fin n → E) → ℝ := fun x => f (x i0) with hf'def
  have hf'm : Measurable f' := hf.comp (measurable_pi_apply i0)
  have hf'b : ∀ x, |f' x| ≤ M := fun x => hfb _
  have hf'l : WLip φ0 f' := by
    intro y y'
    rw [Finset.sum_eq_single i0]
    · simp only [hφ0def, ite_true, hf'def]
      split_ifs with h
      · rw [h]; simp
      · exact abs_sub _ _
    · intro j _ hj
      simp [hφ0def, hj]
    · intro h; exact absurd (Finset.mem_univ i0) h
  -- dual weights
  set it : ℕ → Fin n → E → ℝ := fun m => (stepW μ ω)^[m] φ0 with hit
  set Φ : ℕ → E → ℝ := fun m z => ∑ k, it m k z with hΦdef
  have hitg : ∀ m, GoodW (it m) := fun m =>
    (iter_wlip hS hω hosc hφ0 hf'm hf'b hf'l m).1
  have hΦ : ∀ m, GoodF (Φ m) := fun m => by
    obtain ⟨B, hB⟩ := (hitg m).bdd
    exact GoodF.sum _ fun k _ => ⟨(hitg m).meas k, (hitg m).nonneg k, B, hB k⟩
  have hrec : ∀ m x, Φ (m + 1) x
      = (1 - 1 / (n : ℝ)) * Φ m x + (1 / (n : ℝ)) * Top μ ω n (Φ m) x := by
    intro m x
    have := Phi_step hω (hitg m) x
    simp only [hΦdef, hit] at this ⊢
    rw [Function.iterate_succ_apply']
    exact this
  have hΦ0 : ∀ z, Φ 0 z = |f z| := by
    intro z
    simp [hΦdef, hit, hφ0def]
  -- one-step bounds
  have hstep : ∀ m, |∫ x, (S'.scan (S.scan^[m] f') x - S.scan (S.scan^[m] f') x) ∂S'.P|
      ≤ (1 / (n : ℝ)) * ∫ z, Φ m z * v0 z ∂μ := by
    intro m
    obtain ⟨_, hgm, hgb, hgl⟩ := iter_wlip hS hω hosc hφ0 hf'm hf'b hf'l m
    have := norm_integral_le_of_norm_le_const (μ := S'.P)
      (f := fun x => S'.scan (S.scan^[m] f') x - S.scan (S.scan^[m] f') x)
      (C := (1 / (n : ℝ)) * ∫ z, Φ m z * v0 z ∂μ)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact scan_diff hS hS' hDm hD0 hDb hpD (hitg m) hgm hgb hgl x)
    simpa using this
  -- decay
  set ρ : ℝ := 1 - (1 - r) / n with hρdef
  have hρ0 : 0 ≤ ρ := rho_nonneg hc hrow
  have hρ1 : ρ < 1 := by
    have : 0 < (1 - r) / n := div_pos (by linarith) hn
    linarith
  set Csum : ℝ := ∫ z, |f z| * ((D z + ∫ w, D w ∂μ) + Tstar μ ω n v0 z + 2 * B2) ∂μ with hCsum
  have hbound : ∀ ℓ : ℕ, |∫ x, f (x i0) ∂S'.P - ∫ x, f (x i0) ∂S.P| ≤ Csum + ρ ^ ℓ * (n * (2 * M)) := by
    intro ℓ
    have htel := telescope S S' hf'm hf'b ℓ
    obtain ⟨hgm, hgb, hint⟩ := integral_scan_iterate (S := S) hf'm hf'b ℓ
    -- remainder
    have hrem : |∫ x, S.scan^[ℓ] f' x ∂S'.P - ∫ x, S.scan^[ℓ] f' x ∂S.P| ≤ ρ ^ ℓ * (n * (2 * M)) := by
      rw [hint]
      have e : ∫ x, S.scan^[ℓ] f' x ∂S'.P - ∫ x, f' x ∂S.P
          = ∫ x, (S.scan^[ℓ] f' x - ∫ y, f' y ∂S.P) ∂S'.P := by
        rw [integral_sub (integrable_of_bdd hgm hgb) (integrable_const _)]; simp
      rw [e]
      have := norm_integral_le_of_norm_le_const (μ := S'.P)
        (f := fun x => S.scan^[ℓ] f' x - ∫ y, f' y ∂S.P) (C := ρ ^ ℓ * (n * (2 * M)))
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact abs_scan_iterate_sub_integral_le hc hrow hf'm hf'b ℓ x)
      simpa using this
    -- sum
    have hsum : |∑ m ∈ Finset.range ℓ, ∫ x, (S'.scan (S.scan^[m] f') x - S.scan (S.scan^[m] f') x) ∂S'.P|
        ≤ Csum := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun m _ => hstep m).trans ?_
      rw [← Finset.mul_sum]
      have hint2 : ∑ m ∈ Finset.range ℓ, ∫ z, Φ m z * v0 z ∂μ
          = ∫ z, (∑ m ∈ Finset.range ℓ, Φ m z) * v0 z ∂μ := by
        simp_rw [Finset.sum_mul]
        rw [integral_finsetSum]
        intro m _
        obtain ⟨A, hA⟩ := (hΦ m).abs_le
        obtain ⟨A', hA'⟩ := hv0.abs_le
        exact integrable_mul_bdd (hΦ m).meas hv0.meas hA hA'
      have := theta_bound hω hΦ hrec hv0 (B2 := B2) hB2 hε ℓ
      calc 1 / (n : ℝ) * ∑ m ∈ Finset.range ℓ, ∫ z, Φ m z * v0 z ∂μ
          = ∫ z, 1 / (n : ℝ) * (∑ m ∈ Finset.range ℓ, Φ m z) * v0 z ∂μ := by
            rw [hint2, ← integral_const_mul]
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            simp only; ring
        _ ≤ ∫ z, Φ 0 z * (v0 z + Tstar μ ω n v0 z + 2 * B2) ∂μ := this
        _ = Csum := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            simp only [hΦ0, hv0def]
    have : |∫ x, f' x ∂S'.P - ∫ x, f' x ∂S.P| ≤ Csum + ρ ^ ℓ * (n * (2 * M)) := by
      rw [htel]
      exact (abs_add_le _ _).trans (add_le_add hsum hrem)
    exact this
  have htend : Filter.Tendsto (fun ℓ : ℕ => Csum + ρ ^ ℓ * (n * (2 * M))) Filter.atTop
      (nhds (Csum + 0 * (n * (2 * M)))) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const _)
  rw [zero_mul, add_zero] at htend
  exact ge_of_tendsto htend (Filter.Eventually.of_forall hbound)

end Main


section Field

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ ψ' : E → ℝ} {M M₁ M₁' lam : ℝ}

/-- Density (w.r.t. `μ`) of the one-site conditional law of the field ensemble. -/
def fieldP (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (i : Fin n) (x : Fin n → E)
    (z : E) : ℝ :=
  siteU V ψ lam i x z / ∫ z', siteU V ψ lam i x z' ∂μ

lemma fieldSpec_dens (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) :
    DensKernel μ (fieldSpec (V := V) hψ hlam n) (fun i x z => fieldP V ψ lam i x z) where
  eq i x := by
    rw [fieldSpec_G, siteKernel_fieldDensity hψ hlam]
    rfl
  nonneg i x z := div_nonneg (siteU_pos V ψ lam i x z).le (integral_siteU_pos hψ hlam i x).le
  meas i x := (measurable_siteU hψ.measurable V lam i x).div_const _

lemma fieldP_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} {Λ : ℝ}
    (hΛ : M₁ + lam * n * V.γ ≤ Λ) (i : Fin n) (x : Fin n → E) (z : E) :
    fieldP V ψ lam i x z ≤ Real.exp (M + Λ) :=
  siteU_div_le hψ hlam hΛ i x z

lemma exp_neg_le_integral_siteU (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} {Λ : ℝ}
    (hΛ : M₁ + lam * n * V.γ ≤ Λ) (i : Fin n) (x : Fin n → E) :
    Real.exp (-Λ) ≤ ∫ z, siteU V ψ lam i x z ∂μ :=
  le_trans (Real.exp_le_exp.2 (by linarith)) (exp_le_integral_siteU (V := V) hψ hlam i x)

lemma abs_div_sub_div_le {Ux Uy Zx Zy : ℝ} (hUy : 0 ≤ Uy) (hZx : 0 < Zx) (hZy : 0 < Zy) :
    |Ux / Zx - Uy / Zy| ≤ |Ux - Uy| / Zx + (Uy / Zy) * |Zx - Zy| / Zx := by
  have e : Ux / Zx - Uy / Zy = (Ux - Uy) / Zx + (Uy / Zy) * (Zy - Zx) / Zx := by
    field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add (le_of_eq (by rw [abs_div, abs_of_pos hZx])) ?_)
  rw [abs_div, abs_mul, abs_of_pos hZx, abs_of_nonneg (div_nonneg hUy hZy.le), abs_sub_comm Zy Zx]

lemma abs_siteU_sub_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} (i : Fin n)
    (x y : Fin n → E) (z : E) :
    |siteU V ψ lam i x z - siteU V ψ lam i y z|
      ≤ Real.exp M * lam * ∑ j ∈ Finset.univ.erase i,
          if x j = y j then 0 else V.q z (x j) + V.q z (y j) := by
  unfold siteU
  refine (abs_exp_sub_exp_le (M := M) ?_ ?_).trans ?_
  · have := mul_nonneg hlam (sumq_nonneg V i x z); linarith [hψ.le z]
  · have := mul_nonneg hlam (sumq_nonneg V i y z); linarith [hψ.le z]
  · have e : ψ z - lam * ∑ l ∈ Finset.univ.erase i, V.q z (x l)
        - (ψ z - lam * ∑ l ∈ Finset.univ.erase i, V.q z (y l))
        = -(lam * ∑ l ∈ Finset.univ.erase i, (V.q z (x l) - V.q z (y l))) := by
      rw [Finset.sum_sub_distrib]; ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg hlam]
    have h1 : |∑ l ∈ Finset.univ.erase i, (V.q z (x l) - V.q z (y l))|
        ≤ ∑ j ∈ Finset.univ.erase i, if x j = y j then 0 else V.q z (x j) + V.q z (y j) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      split_ifs with h
      · rw [h]; simp
      · rw [abs_le]; constructor <;> linarith [V.q_nonneg z (x j), V.q_nonneg z (y j)]
    calc Real.exp M * (lam * |∑ l ∈ Finset.univ.erase i, (V.q z (x l) - V.q z (y l))|)
        ≤ Real.exp M * (lam * ∑ j ∈ Finset.univ.erase i,
            if x j = y j then 0 else V.q z (x j) + V.q z (y j)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hlam) (Real.exp_pos _).le
      _ = _ := by ring

lemma integrable_qpair (V : WeakPotential μ) (a b : E) :
    Integrable (fun z => if a = b then 0 else V.q z a + V.q z b) μ := by
  split_ifs with h
  · exact integrable_zero _ _ _
  · exact (integrable_q_left V a).add (integrable_q_left V b)

lemma integral_qpair_le (V : WeakPotential μ) (a b : E) :
    ∫ z, (if a = b then 0 else V.q z a + V.q z b) ∂μ ≤ if a = b then 0 else 2 * V.γ := by
  split_ifs with h
  · simp
  · rw [integral_add (integrable_q_left V a) (integrable_q_left V b)]
    linarith [integral_q_left_le V a, integral_q_left_le V b]

lemma integrable_siteU_sub (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} (i : Fin n)
    (x y : Fin n → E) :
    Integrable (fun z => |siteU V ψ lam i x z - siteU V ψ lam i y z|) μ :=
  ((integrable_siteU hψ hlam i x).sub (integrable_siteU hψ hlam i y)).abs

lemma integral_abs_siteU_sub_le' (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} (i : Fin n)
    (x y : Fin n → E) :
    ∫ z, |siteU V ψ lam i x z - siteU V ψ lam i y z| ∂μ
      ≤ Real.exp M * lam * ∑ j ∈ Finset.univ.erase i, if x j = y j then 0 else 2 * V.γ := by
  have hi2 : Integrable (fun z => Real.exp M * lam * ∑ j ∈ Finset.univ.erase i,
      if x j = y j then 0 else V.q z (x j) + V.q z (y j)) μ :=
    (integrable_finsetSum _ fun j _ => integrable_qpair V _ _).const_mul _
  calc ∫ z, |siteU V ψ lam i x z - siteU V ψ lam i y z| ∂μ
      ≤ ∫ z, Real.exp M * lam * ∑ j ∈ Finset.univ.erase i,
          if x j = y j then 0 else V.q z (x j) + V.q z (y j) ∂μ :=
        integral_mono (integrable_siteU_sub (V := V) hψ hlam i x y) hi2
          (fun z => abs_siteU_sub_le (V := V) hψ hlam i x y z)
    _ = Real.exp M * lam * ∑ j ∈ Finset.univ.erase i, ∫ z,
          (if x j = y j then 0 else V.q z (x j) + V.q z (y j)) ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ => integrable_qpair V _ _]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => integral_qpair_le V _ _) ?_
        exact mul_nonneg (Real.exp_pos _).le hlam

/-- Dependence of the one-site density on the neighbours (multi-coordinate version of
`abs_siteKernel_sub_le`), pointwise in the new value `z`. -/
lemma abs_fieldP_sub_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} {Λ : ℝ}
    (hΛ : M₁ + lam * n * V.γ ≤ Λ) (i : Fin n) (x y : Fin n → E) (z : E) :
    |fieldP V ψ lam i x z - fieldP V ψ lam i y z|
      ≤ ∑ j ∈ Finset.univ.erase i, if x j = y j then 0 else
          (Real.exp (M + Λ) * (1 + Real.exp (M + Λ)) * lam * (V.q z (x j) + V.γ)
            + Real.exp (M + Λ) * (1 + Real.exp (M + Λ)) * lam * (V.q z (y j) + V.γ)) := by
  unfold fieldP
  have hZx := integral_siteU_pos (V := V) hψ hlam i x
  have hZy := integral_siteU_pos (V := V) hψ hlam i y
  have hZxl := exp_neg_le_integral_siteU (V := V) hψ hlam hΛ i x
  have hq := abs_div_sub_div_le (Ux := siteU V ψ lam i x z) (Uy := siteU V ψ lam i y z)
    (siteU_pos V ψ lam i y z).le hZx hZy
  set K1 := Real.exp (M + Λ) with hK1
  have hK1pos : 0 < K1 := Real.exp_pos _
  have hpy : siteU V ψ lam i y z / ∫ z', siteU V ψ lam i y z' ∂μ ≤ K1 := siteU_div_le hψ hlam hΛ i y z
  have hinv : 1 / (∫ z', siteU V ψ lam i x z' ∂μ) ≤ Real.exp Λ := by
    rw [div_le_iff₀ hZx]
    calc (1 : ℝ) = Real.exp Λ * Real.exp (-Λ) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hZxl (Real.exp_pos _).le
  have hZdiff : |(∫ z', siteU V ψ lam i x z' ∂μ) - ∫ z', siteU V ψ lam i y z' ∂μ|
      ≤ ∫ z', |siteU V ψ lam i x z' - siteU V ψ lam i y z'| ∂μ := by
    rw [← integral_sub (integrable_siteU hψ hlam i x) (integrable_siteU hψ hlam i y)]
    exact abs_integral_le_integral_abs
  have hexpMΛ : Real.exp Λ * Real.exp M = K1 := by rw [hK1, ← Real.exp_add]; ring_nf
  set Sx : ℝ := ∑ j ∈ Finset.univ.erase i, if x j = y j then 0 else V.q z (x j) + V.q z (y j) with hSx
  set Sg : ℝ := ∑ j ∈ Finset.univ.erase i, if x j = y j then 0 else 2 * V.γ with hSg
  have hSx0 : 0 ≤ Sx := Finset.sum_nonneg fun j _ => by
    split_ifs
    · exact le_rfl
    · linarith [V.q_nonneg z (x j), V.q_nonneg z (y j)]
  have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun j _ => by
    split_ifs
    · exact le_rfl
    · have := V.γ_nonneg; linarith
  have hU := abs_siteU_sub_le (V := V) hψ hlam i x y z
  have hI := integral_abs_siteU_sub_le' (V := V) hψ hlam i x y
  -- first term
  have t1 : |siteU V ψ lam i x z - siteU V ψ lam i y z| / (∫ z', siteU V ψ lam i x z' ∂μ)
      ≤ K1 * lam * Sx := by
    rw [div_eq_mul_one_div]
    calc |siteU V ψ lam i x z - siteU V ψ lam i y z| * (1 / ∫ z', siteU V ψ lam i x z' ∂μ)
        ≤ (Real.exp M * lam * Sx) * Real.exp Λ :=
          mul_le_mul hU hinv (by positivity) (by have := hlam; positivity)
      _ = K1 * lam * Sx := by rw [← hexpMΛ]; ring
  have t2 : (siteU V ψ lam i y z / ∫ z', siteU V ψ lam i y z' ∂μ)
        * |(∫ z', siteU V ψ lam i x z' ∂μ) - ∫ z', siteU V ψ lam i y z' ∂μ|
        / (∫ z', siteU V ψ lam i x z' ∂μ) ≤ K1 * K1 * lam * Sg := by
    have hJ : |(∫ z', siteU V ψ lam i x z' ∂μ) - ∫ z', siteU V ψ lam i y z' ∂μ|
        ≤ Real.exp M * lam * Sg := hZdiff.trans hI
    have hp0 : 0 ≤ siteU V ψ lam i y z / ∫ z', siteU V ψ lam i y z' ∂μ :=
      div_nonneg (siteU_pos V ψ lam i y z).le hZy.le
    rw [div_eq_mul_one_div _ (∫ z', siteU V ψ lam i x z' ∂μ)]
    calc (siteU V ψ lam i y z / ∫ z', siteU V ψ lam i y z' ∂μ)
          * |(∫ z', siteU V ψ lam i x z' ∂μ) - ∫ z', siteU V ψ lam i y z' ∂μ|
          * (1 / ∫ z', siteU V ψ lam i x z' ∂μ)
        ≤ (K1 * (Real.exp M * lam * Sg)) * Real.exp Λ :=
          mul_le_mul (mul_le_mul hpy hJ (abs_nonneg _) hK1pos.le) hinv (by positivity)
            (by have := hlam; positivity)
      _ = K1 * K1 * lam * Sg := by rw [← hexpMΛ]; ring
  refine hq.trans ((add_le_add t1 t2).trans ?_)
  rw [hSx, hSg, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with h
  · simp
  · have hqx := V.q_nonneg z (x j)
    have hqy := V.q_nonneg z (y j)
    have hγ := V.γ_nonneg
    have hd : 0 ≤ K1 * K1 * lam * (V.q z (x j) + V.q z (y j)) + K1 * lam * (2 * V.γ) := by
      have := hlam; positivity
    nlinarith [hd]

end Field


section FieldDiff

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ ψ' : E → ℝ} {M M₁ M₁' lam : ℝ}

lemma abs_siteU_sub_field_le (hψ : IsField μ ψ M M₁) (hψ' : IsField μ ψ' M M₁') (hlam : 0 ≤ lam)
    {n : ℕ} (i : Fin n) (x : Fin n → E) (z : E) :
    |siteU V ψ lam i x z - siteU V ψ' lam i x z| ≤ Real.exp M * |ψ z - ψ' z| := by
  unfold siteU
  refine (abs_exp_sub_exp_le (M := M) ?_ ?_).trans (le_of_eq ?_)
  · have := mul_nonneg hlam (sumq_nonneg V i x z); linarith [hψ.le z]
  · have := mul_nonneg hlam (sumq_nonneg V i x z); linarith [hψ'.le z]
  · congr 1; ring_nf

/-- Pointwise change of the one-site density under a change of the one-body field. -/
lemma abs_fieldP_sub_field_le (hψ : IsField μ ψ M M₁) (hψ' : IsField μ ψ' M M₁')
    (hlam : 0 ≤ lam) {n : ℕ} {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ)
    (hΛ' : M₁' + lam * n * V.γ ≤ Λ) (i : Fin n) (x : Fin n → E) (z : E) :
    |fieldP V ψ' lam i x z - fieldP V ψ lam i x z|
      ≤ Real.exp (M + Λ) * |ψ' z - ψ z|
        + Real.exp (M + Λ) * Real.exp (M + Λ) * ∫ w, |ψ' w - ψ w| ∂μ := by
  unfold fieldP
  have hZ := integral_siteU_pos (V := V) hψ hlam i x
  have hZ' := integral_siteU_pos (V := V) hψ' hlam i x
  have hZl := exp_neg_le_integral_siteU (V := V) hψ hlam hΛ i x
  rw [abs_sub_comm]
  have hq := abs_div_sub_div_le (Ux := siteU V ψ lam i x z) (Uy := siteU V ψ' lam i x z)
    (siteU_pos V ψ' lam i x z).le hZ hZ'
  set K1 := Real.exp (M + Λ) with hK1
  have hK1pos : 0 < K1 := Real.exp_pos _
  have hpy : siteU V ψ' lam i x z / ∫ z', siteU V ψ' lam i x z' ∂μ ≤ K1 :=
    siteU_div_le hψ' hlam hΛ' i x z
  have hinv : 1 / (∫ z', siteU V ψ lam i x z' ∂μ) ≤ Real.exp Λ := by
    rw [div_le_iff₀ hZ]
    calc (1 : ℝ) = Real.exp Λ * Real.exp (-Λ) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hZl (Real.exp_pos _).le
  have hexpMΛ : Real.exp Λ * Real.exp M = K1 := by rw [hK1, ← Real.exp_add]; ring_nf
  have hdiffI : ∫ z', |siteU V ψ lam i x z' - siteU V ψ' lam i x z'| ∂μ
      ≤ Real.exp M * ∫ w, |ψ' w - ψ w| ∂μ := by
    have hi1 : Integrable (fun z' => |siteU V ψ lam i x z' - siteU V ψ' lam i x z'|) μ :=
      ((integrable_siteU hψ hlam i x).sub (integrable_siteU hψ' hlam i x)).abs
    have hi2 : Integrable (fun w => |ψ' w - ψ w|) μ := (hψ'.integrable.sub hψ.integrable).abs
    calc ∫ z', |siteU V ψ lam i x z' - siteU V ψ' lam i x z'| ∂μ
        ≤ ∫ w, Real.exp M * |ψ' w - ψ w| ∂μ :=
          integral_mono hi1 (hi2.const_mul _) fun w => by
            refine (abs_siteU_sub_field_le (V := V) hψ hψ' hlam i x w).trans (le_of_eq ?_)
            rw [abs_sub_comm]
      _ = _ := integral_const_mul _ _
  have hZdiff : |(∫ z', siteU V ψ lam i x z' ∂μ) - ∫ z', siteU V ψ' lam i x z' ∂μ|
      ≤ ∫ z', |siteU V ψ lam i x z' - siteU V ψ' lam i x z'| ∂μ := by
    rw [← integral_sub (integrable_siteU hψ hlam i x) (integrable_siteU hψ' hlam i x)]
    exact abs_integral_le_integral_abs
  have hU := abs_siteU_sub_field_le (V := V) hψ hψ' hlam i x z
  have hI0 : 0 ≤ ∫ w, |ψ' w - ψ w| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have t1 : |siteU V ψ lam i x z - siteU V ψ' lam i x z| / (∫ z', siteU V ψ lam i x z' ∂μ)
      ≤ K1 * |ψ' z - ψ z| := by
    rw [div_eq_mul_one_div]
    calc |siteU V ψ lam i x z - siteU V ψ' lam i x z| * (1 / ∫ z', siteU V ψ lam i x z' ∂μ)
        ≤ (Real.exp M * |ψ z - ψ' z|) * Real.exp Λ := mul_le_mul hU hinv (by positivity) (by positivity)
      _ = K1 * |ψ' z - ψ z| := by rw [abs_sub_comm, ← hexpMΛ]; ring
  have t2 : (siteU V ψ' lam i x z / ∫ z', siteU V ψ' lam i x z' ∂μ)
        * |(∫ z', siteU V ψ lam i x z' ∂μ) - ∫ z', siteU V ψ' lam i x z' ∂μ|
        / (∫ z', siteU V ψ lam i x z' ∂μ) ≤ K1 * K1 * ∫ w, |ψ' w - ψ w| ∂μ := by
    rw [div_eq_mul_one_div _ (∫ z', siteU V ψ lam i x z' ∂μ)]
    calc (siteU V ψ' lam i x z / ∫ z', siteU V ψ' lam i x z' ∂μ)
          * |(∫ z', siteU V ψ lam i x z' ∂μ) - ∫ z', siteU V ψ' lam i x z' ∂μ|
          * (1 / ∫ z', siteU V ψ lam i x z' ∂μ)
        ≤ (K1 * (Real.exp M * ∫ w, |ψ' w - ψ w| ∂μ)) * Real.exp Λ :=
          mul_le_mul (mul_le_mul hpy (hZdiff.trans hdiffI) (abs_nonneg _) hK1pos.le) hinv
            (by positivity) (by positivity)
      _ = K1 * K1 * ∫ w, |ψ' w - ψ w| ∂μ := by rw [← hexpMΛ]; ring
  exact hq.trans (add_le_add t1 t2)

end FieldDiff


section FieldMain

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ ψ' : E → ℝ} {M M₁ M₁' lam : ℝ}

/-- The dependence kernel `ω(z, w) = K₁ (1 + K₁) lam (q(z, w) + γ)` of the field ensembles. -/
def fieldOmega (V : WeakPotential μ) (lam K1 : ℝ) : E → E → ℝ :=
  fun z w => K1 * (1 + K1) * lam * (V.q z w + V.γ)

lemma fieldOmega_ker (V : WeakPotential μ) {lam K1 : ℝ} (hlam : 0 ≤ lam) (hK1 : 0 ≤ K1) :
    KerData μ (fieldOmega V lam K1) (2 * (K1 * (1 + K1) * lam) * V.γ) := by
  have hC : 0 ≤ K1 * (1 + K1) * lam := by positivity
  have hγ := V.γ_nonneg
  have hint : ∀ x, Integrable (fun z => V.q z x + V.γ) μ := fun x =>
    (integrable_q_left V x).add (integrable_const _)
  have hint' : ∀ z, Integrable (fun x => V.q z x + V.γ) μ := fun z =>
    (V.integrable_q z).add (integrable_const _)
  refine ⟨?_, fun z x => ?_, fun x => ?_, fun x => ?_, fun z => ?_, fun z => ?_⟩
  · unfold fieldOmega
    exact measurable_const.mul (V.measurable_q.add measurable_const)
  · unfold fieldOmega; have := V.q_nonneg z x; positivity
  · exact (hint x).const_mul _
  · unfold fieldOmega
    rw [integral_const_mul, integral_add (integrable_q_left V x) (integrable_const _)]
    have := integral_q_left_le V x
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    nlinarith
  · exact (hint' z).const_mul _
  · unfold fieldOmega
    rw [integral_const_mul, integral_add (V.integrable_q z) (integrable_const _)]
    have := V.row_le z
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    nlinarith

theorem field_pointwise_comparison {n : ℕ} [NeZero n] (hψ : IsField μ ψ M M₁)
    (hψ' : IsField μ ψ' M M₁') (hlam : 0 ≤ lam) {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ)
    (hΛ' : M₁' + lam * n * V.γ ≤ Λ)
    (hr : (n : ℝ) * (4 * Real.exp (M + Λ) * lam * V.γ) < 1)
    (hε : ((n : ℝ) - 1) * (2 * (2 * (Real.exp (M + Λ) * (1 + Real.exp (M + Λ)) * lam) * V.γ))
      ≤ 1 / 2)
    {D : E → ℝ} (hDm : Measurable D) (hD0 : ∀ z, 0 ≤ D z) {BD : ℝ} (hDb : ∀ z, D z ≤ BD)
    (hD : ∀ z, min (Real.exp (M + Λ)) (Real.exp (M + Λ) * |ψ' z - ψ z|
        + Real.exp (M + Λ) * Real.exp (M + Λ) * ∫ w, |ψ' w - ψ w| ∂μ) ≤ D z)
    {B2 : ℝ}
    (hB2 : ∀ z, Tstar μ (fieldOmega V lam (Real.exp (M + Λ))) n
      (Tstar μ (fieldOmega V lam (Real.exp (M + Λ))) n (fun z => D z + ∫ w, D w ∂μ)) z ≤ B2)
    (i0 : Fin n) {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hfb : ∀ z, |f z| ≤ B) :
    |∫ x, f (x i0) ∂(fieldLaw V ψ' lam n) - ∫ x, f (x i0) ∂(fieldLaw V ψ lam n)|
      ≤ ∫ z, |f z| * ((D z + ∫ w, D w ∂μ)
          + Tstar μ (fieldOmega V lam (Real.exp (M + Λ))) n (fun z => D z + ∫ w, D w ∂μ) z
          + 2 * B2) ∂μ := by
  have : Nonempty E := (Measure.nonempty_of_neZero μ)
  set K1 := Real.exp (M + Λ) with hK1
  have hK1pos : 0 < K1 := Real.exp_pos _
  have hker := fieldOmega_ker (μ := μ) V hlam hK1pos.le
  have hc0 : 0 ≤ 4 * K1 * lam * V.γ := by have := V.γ_nonneg; positivity
  have hdob : IsDobrushin (fieldSpec (V := V) hψ hlam n) (fun _ _ => 4 * K1 * lam * V.γ) :=
    ⟨fun _ _ => hc0, fun i j hij x y hxy A hA =>
      abs_siteKernel_sub_le (V := V) hψ hlam hΛ hij hxy hA⟩
  have hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i, 4 * K1 * lam * V.γ
      ≤ (n : ℝ) * (4 * K1 * lam * V.γ) := fun i => by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.card_erase_le).trans (by simp)) hc0
  have hosc : ∀ (i : Fin n) (x y : Fin n → E) (z : E),
      |fieldP V ψ lam i x z - fieldP V ψ lam i y z|
        ≤ ∑ j ∈ Finset.univ.erase i, if x j = y j then 0 else
            fieldOmega V lam K1 z (x j) + fieldOmega V lam K1 z (y j) := by
    intro i x y z
    refine (abs_fieldP_sub_le hψ hlam hΛ i x y z).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [fieldOmega, hK1]
  have hpD : ∀ (i : Fin n) (x : Fin n → E) (z : E),
      |fieldP V ψ' lam i x z - fieldP V ψ lam i x z| ≤ D z := by
    intro i x z
    refine le_trans ?_ (hD z)
    refine le_min ?_ (abs_fieldP_sub_field_le hψ hψ' hlam hΛ hΛ' i x z)
    have h1 := fieldP_le hψ' hlam hΛ' i x z
    have h2 := fieldP_le hψ hlam hΛ i x z
    have h3 : 0 ≤ fieldP V ψ' lam i x z :=
      div_nonneg (siteU_pos V ψ' lam i x z).le (integral_siteU_pos hψ' hlam i x).le
    have h4 : 0 ≤ fieldP V ψ lam i x z :=
      div_nonneg (siteU_pos V ψ lam i x z).le (integral_siteU_pos hψ hlam i x).le
    rw [abs_le]; constructor <;> linarith
  have := pointwise_marginal_comparison (fieldSpec_dens (V := V) hψ hlam n)
    (fieldSpec_dens (V := V) hψ' hlam n) hker hosc hDm hD0 hDb hpD hdob hrow hr hε hB2 i0 hf hfb
  exact this

end FieldMain


section SetBound

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ ψ' : E → ℝ} {M M₁ M₁' lam : ℝ}

/-- From a set-wise bound `|ν'(A) - ν(A)| ≤ ∫_A Ψ dμ` to the pointwise bound of the densities. -/
lemma ae_abs_rnDeriv_sub_le {ν ν' : Measure E} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (hν : ν ≪ μ) (hν' : ν' ≪ μ) {Ψ : E → ℝ} (hΨ : Integrable Ψ μ)
    (h : ∀ A, MeasurableSet A → |ν'.real A - ν.real A| ≤ ∫ z in A, Ψ z ∂μ) :
    ∀ᵐ z ∂μ, |(ν'.rnDeriv μ z).toReal - (ν.rnDeriv μ z).toReal| ≤ Ψ z := by
  have hi : Integrable (fun z => (ν.rnDeriv μ z).toReal) μ := Measure.integrable_toReal_rnDeriv
  have hi' : Integrable (fun z => (ν'.rnDeriv μ z).toReal) μ := Measure.integrable_toReal_rnDeriv
  have e : ∀ A, MeasurableSet A → ν'.real A - ν.real A
      = ∫ z in A, ((ν'.rnDeriv μ z).toReal - (ν.rnDeriv μ z).toReal) ∂μ := by
    intro A hA
    rw [integral_sub hi'.integrableOn hi.integrableOn, Measure.setIntegral_toReal_rnDeriv hν',
      Measure.setIntegral_toReal_rnDeriv hν]
  have h1 : 0 ≤ᵐ[μ] fun z => Ψ z - ((ν'.rnDeriv μ z).toReal - (ν.rnDeriv μ z).toReal) := by
    refine ae_nonneg_of_forall_setIntegral_nonneg (hΨ.sub (hi'.sub hi)) fun A hA _ => ?_
    have hs : ∫ x in A, (Ψ x - ((ν'.rnDeriv μ x).toReal - (ν.rnDeriv μ x).toReal)) ∂μ
        = (∫ x in A, Ψ x ∂μ) - ∫ x in A, ((ν'.rnDeriv μ x).toReal - (ν.rnDeriv μ x).toReal) ∂μ :=
      integral_sub hΨ.integrableOn (hi'.sub hi).integrableOn
    rw [hs, ← e A hA]
    have := h A hA
    rw [abs_le] at this
    linarith
  have h2 : 0 ≤ᵐ[μ] fun z => Ψ z + ((ν'.rnDeriv μ z).toReal - (ν.rnDeriv μ z).toReal) := by
    refine ae_nonneg_of_forall_setIntegral_nonneg (hΨ.add (hi'.sub hi)) fun A hA _ => ?_
    have hs : ∫ x in A, (Ψ x + ((ν'.rnDeriv μ x).toReal - (ν.rnDeriv μ x).toReal)) ∂μ
        = (∫ x in A, Ψ x ∂μ) + ∫ x in A, ((ν'.rnDeriv μ x).toReal - (ν.rnDeriv μ x).toReal) ∂μ :=
      integral_add hΨ.integrableOn (hi'.sub hi).integrableOn
    rw [hs, ← e A hA]
    have := h A hA
    rw [abs_le] at this
    linarith
  filter_upwards [h1, h2] with z hz1 hz2
  rw [abs_le]
  simp only [Pi.zero_apply] at hz1 hz2
  constructor <;> linarith

end SetBound


section SetBound2

variable [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ ψ' : E → ℝ} {M M₁ M₁' lam : ℝ}

theorem field_marginal_set_bound {n : ℕ} [NeZero n] (hψ : IsField μ ψ M M₁)
    (hψ' : IsField μ ψ' M M₁') (hlam : 0 ≤ lam) {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ)
    (hΛ' : M₁' + lam * n * V.γ ≤ Λ)
    (hr : (n : ℝ) * (4 * Real.exp (M + Λ) * lam * V.γ) < 1)
    (hε : ((n : ℝ) - 1) * (2 * (2 * (Real.exp (M + Λ) * (1 + Real.exp (M + Λ)) * lam) * V.γ))
      ≤ 1 / 2)
    {D : E → ℝ} (hDm : Measurable D) (hD0 : ∀ z, 0 ≤ D z) {BD : ℝ} (hDb : ∀ z, D z ≤ BD)
    (hD : ∀ z, min (Real.exp (M + Λ)) (Real.exp (M + Λ) * |ψ' z - ψ z|
        + Real.exp (M + Λ) * Real.exp (M + Λ) * ∫ w, |ψ' w - ψ w| ∂μ) ≤ D z)
    {B2 : ℝ}
    (hB2 : ∀ z, Tstar μ (fieldOmega V lam (Real.exp (M + Λ))) n
      (Tstar μ (fieldOmega V lam (Real.exp (M + Λ))) n (fun z => D z + ∫ w, D w ∂μ)) z ≤ B2)
    {Ψ : E → ℝ} (hΨi : Integrable Ψ μ)
    (hΨ : ∀ᵐ z ∂μ, (D z + ∫ w, D w ∂μ)
          + Tstar μ (fieldOmega V lam (Real.exp (M + Λ))) n (fun z => D z + ∫ w, D w ∂μ) z
          + 2 * B2 ≤ Ψ z)
    (i0 : Fin n) {A : Set E} (hA : MeasurableSet A) :
    |((fieldLaw V ψ' lam n).map (fun x => x i0)).real A
        - ((fieldLaw V ψ lam n).map (fun x => x i0)).real A| ≤ ∫ z in A, Ψ z ∂μ := by
  have : Nonempty E := (Measure.nonempty_of_neZero μ)
  set K1 := Real.exp (M + Λ) with hK1
  have hK1pos : 0 < K1 := Real.exp_pos _
  have hker := fieldOmega_ker (μ := μ) V hlam hK1pos.le
  have hI0 : 0 ≤ ∫ w, D w ∂μ := integral_nonneg hD0
  have hv0 : GoodF (fun z => D z + ∫ w, D w ∂μ) :=
    ⟨hDm.add measurable_const, fun z => add_nonneg (hD0 z) hI0, BD + ∫ w, D w ∂μ,
      fun z => add_le_add (hDb z) le_rfl⟩
  have hu1 := hv0.Tstar (n := n) hker
  have hu2 := hu1.Tstar (n := n) hker
  have hB2' : 0 ≤ B2 := (hu2.nonneg (Classical.arbitrary E)).trans (hB2 _)
  set f : E → ℝ := A.indicator (fun _ => (1 : ℝ)) with hf
  have hfm : Measurable f := measurable_const.indicator hA
  have hfb : ∀ z, |f z| ≤ 1 := fun z => by
    simp only [hf, Set.indicator]; split_ifs <;> simp
  have key := field_pointwise_comparison (V := V) hψ hψ' hlam hΛ hΛ' hr hε hDm hD0 hDb hD hB2
    i0 hfm hfb
  have conv : ∀ ψ'' : E → ℝ, ∫ x, f (x i0) ∂(fieldLaw V ψ'' lam n)
      = ((fieldLaw V ψ'' lam n).map (fun x => x i0)).real A := by
    intro ψ''
    have h1 : (fun x : Fin n → E => f (x i0))
        = ((fun x : Fin n → E => x i0) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ) := by
      funext x; simp [hf, Set.indicator]
    rw [h1, integral_indicator_one (measurable_pi_apply i0 hA),
      map_measureReal_apply (measurable_pi_apply i0) hA]
  rw [conv, conv] at key
  refine key.trans ?_
  have hfi : Integrable (fun z => |f z| * Ψ z) μ :=
    hΨi.bdd_mul hfm.abs.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_abs]; exact hfb z)
  have hnn : 0 ≤ᵐ[μ] fun z => |f z| * ((D z + ∫ w, D w ∂μ)
      + Tstar μ (fieldOmega V lam K1) n (fun z => D z + ∫ w, D w ∂μ) z + 2 * B2) :=
    Filter.Eventually.of_forall fun z => mul_nonneg (abs_nonneg _)
      (add_nonneg (add_nonneg (hv0.nonneg z) (hu1.nonneg z)) (by linarith))
  refine (integral_mono_of_nonneg hnn hfi ?_).trans (le_of_eq ?_)
  · filter_upwards [hΨ] with z hz
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  · have : ∀ z, |f z| * Ψ z = A.indicator Ψ z := fun z => by
      simp only [hf, Set.indicator]; split_ifs <;> simp
    simp_rw [this]
    exact integral_indicator hA

end SetBound2


section TstarLe

variable [IsProbabilityMeasure μ] {ω : E → E → ℝ} {ρc : ℝ}

lemma integral_le_of_lintegral {f : E → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfm : Measurable f)
    (ū : E → ℝ≥0∞) (hle : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) ≤ ū x) {T : ℝ} (hT : 0 ≤ T)
    (h : ∫⁻ x, ū x ∂μ ≤ ENNReal.ofReal T) : ∫ x, f x ∂μ ≤ T := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hT ((lintegral_mono_ae hle).trans h)

/-- A bound for `T* u (z)` from `lintegral` bounds of a majorant. -/
theorem Tstar_le_of_lintegral (hω : KerData μ ω ρc) {n : ℕ} (hn : 1 ≤ n) {u : E → ℝ}
    (hu : GoodF u) (ū : E → ℝ≥0∞) (hle : ∀ᵐ x ∂μ, ENNReal.ofReal (u x) ≤ ū x) (z : E)
    {T1 T2 : ℝ} (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2)
    (h1 : ∫⁻ x, ū x * ENNReal.ofReal (ω z x) ∂μ ≤ ENNReal.ofReal T1)
    (h2 : ∫⁻ x, ū x * ENNReal.ofReal (colS μ ω x) ∂μ ≤ ENNReal.ofReal T2) :
    Tstar μ ω n u z ≤ ((n : ℝ) - 1) * (T1 + T2) := by
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hωz : Measurable (fun x => ω z x) := hω.meas.comp (measurable_const.prodMk measurable_id)
  have hb1 : ∫ x, u x * ω z x ∂μ ≤ T1 := by
    refine integral_le_of_lintegral (fun x => mul_nonneg (hu.nonneg x) (hω.nonneg z x))
      (hu.meas.mul hωz) (fun x => ū x * ENNReal.ofReal (ω z x)) ?_ hT1 h1
    filter_upwards [hle] with x hx
    rw [ENNReal.ofReal_mul (hu.nonneg x)]
    exact mul_le_mul' hx le_rfl
  have hb2 : ∫ x, u x * colS μ ω x ∂μ ≤ T2 := by
    refine integral_le_of_lintegral (fun x => mul_nonneg (hu.nonneg x) (hω.colS_nonneg x))
      (hu.meas.mul hω.measurable_colS) (fun x => ū x * ENNReal.ofReal (colS μ ω x)) ?_ hT2 h2
    filter_upwards [hle] with x hx
    rw [ENNReal.ofReal_mul (hu.nonneg x)]
    exact mul_le_mul' hx le_rfl
  unfold Tstar
  exact mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) hn1

end TstarLe


end Pointwise

end HRS.External
