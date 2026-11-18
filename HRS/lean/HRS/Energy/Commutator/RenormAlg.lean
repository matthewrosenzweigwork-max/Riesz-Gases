import HRS.Energy.Commutator.Stress
import HRS.Energy.Commutator.AbsConv

/-!
# Route S, packet S4: the exact decomposition `P = Q + R` (abstract algebra)

Abstract in the force `w` (odd, `L¹`, bounded away from `0`), the velocity `v` (continuous) and the
smeared charges `σ_i` (finite measures supported in `B̄(x_i, η_i)`, reproducing `w` outside the balls).
See `docs/external/super_core_proof.md`, Prop. A.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.Renorm

variable {d : ℕ}

/-- The commutator kernel without the diagonal convention. -/
def kern (w v : Torus d → Euc d) (x y : Torus d) : ℝ := inner ℝ (v x - v y) (w (x - y))

theorem commKernel_eq_kern (w v : Torus d → Euc d) (x y : Torus d) :
    commKernel w v x y = kern w v x y := by
  unfold commKernel kern
  split_ifs with h
  · subst h; simp
  · rfl

theorem kern_symm {w : Torus d → Euc d} (hw : ∀ z, w (-z) = -w z) (v : Torus d → Euc d) (x y : Torus d) :
    kern w v y x = kern w v x y := by
  unfold kern
  have : y - x = -(x - y) := by abel
  rw [this, hw, inner_neg_right, ← inner_neg_left, neg_sub]

theorem integrable_inner_of_bdd {σ : Measure (Torus d)} {u f : Torus d → Euc d} (hu : Measurable u) {C : ℝ}
    (hC : ∀ x, ‖u x‖ ≤ C) (hf : Integrable f σ) : Integrable (fun x => inner ℝ (u x) (f x)) σ := by
  refine Integrable.mono' (hf.norm.const_mul C) (hu.aestronglyMeasurable.inner hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

/-- **Function-level reproducing identity.**  For a finite measure `σ` and a point `a`:
`∫ k(x,y) dσ(x) = k(a,y) - ∫ ψ(x)·w(x-y) dσ(x) - (v a - v y)·Δ(y)`, `ψ = v a - v`,
`Δ(y) = w(a-y) - ∫ w(x-y) dσ(x)`. -/
theorem kern_integral_charge (w v : Torus d → Euc d) {σ : Measure (Torus d)} (a y : Torus d)
    (hvm : Measurable v) {C : ℝ} (hvb : ∀ x, ‖v x‖ ≤ C) (hw : Integrable (fun x => w (x - y)) σ) :
    ∫ x, kern w v x y ∂σ =
      kern w v a y - ∫ x, inner ℝ (v a - v x) (w (x - y)) ∂σ -
        inner ℝ (v a - v y) (w (a - y) - ∫ x, w (x - y) ∂σ) := by
  have h1 : ∀ x, kern w v x y = inner ℝ (v a - v y) (w (x - y)) - inner ℝ (v a - v x) (w (x - y)) := by
    intro x
    unfold kern
    have : v x - v y = (v a - v y) - (v a - v x) := by abel
    rw [this, inner_sub_left]
  have hint1 : Integrable (fun x => inner ℝ (v a - v x) (w (x - y))) σ :=
    integrable_inner_of_bdd (hvm.const_sub (v a)) (C := ‖v a‖ + C)
      (fun x => (norm_sub_le _ _).trans (by linarith [hvb x])) hw
  have hint2 : Integrable (fun x => inner ℝ (v a - v y) (w (x - y))) σ :=
    integrable_inner_of_bdd (measurable_const) (C := ‖v a - v y‖) (fun x => le_rfl) hw
  simp_rw [h1]
  rw [integral_sub hint2 hint1, integral_inner hw, inner_sub_right]
  simp only [sub_self, inner_zero_left]
  ring


/-! ### Expansion of the quadratic form for a family of charges -/

variable {N : ℕ}

/-- The averaged charge `N⁻¹ ∑ σ_i`. -/
def avgM (σ : Fin N → Measure (Torus d)) : Measure (Torus d) := (N : ℝ≥0∞)⁻¹ • ∑ i, σ i

theorem avgM_eq_chargeMeasure (σ0 : ℝ → Measure (Torus d)) (η : Fin N → ℝ) (X : Config d N) :
    chargeMeasure σ0 η X = avgM (fun i => (σ0 (η i)).map (fun y => y + X i)) := rfl

theorem prod_sum_right' (α : Measure (Torus d)) [SFinite α] (m : Fin N → Measure (Torus d))
    [∀ i, SFinite (m i)] : α.prod (∑ i, m i) = ∑ i, α.prod (m i) := by
  rw [← Measure.sum_fintype, Measure.prod_sum_right, Measure.sum_fintype]

theorem prod_sum_left' (β : Measure (Torus d)) [SFinite β] (m : Fin N → Measure (Torus d))
    [∀ i, SFinite (m i)] : (∑ i, m i).prod β = ∑ i, (m i).prod β := by
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype]

theorem avgM_prod_right (α : Measure (Torus d)) [SFinite α] (σ : Fin N → Measure (Torus d))
    [∀ i, SFinite (σ i)] :
    α.prod (avgM σ) = (N : ℝ≥0∞)⁻¹ • ∑ i, α.prod (σ i) := by
  unfold avgM
  haveI : SFinite (∑ i, σ i) := by rw [← Measure.sum_fintype]; infer_instance
  rw [Measure.prod_smul_right, prod_sum_right']

theorem avgM_prod_left (β : Measure (Torus d)) [SFinite β] (σ : Fin N → Measure (Torus d))
    [∀ i, SFinite (σ i)] :
    (avgM σ).prod β = (N : ℝ≥0∞)⁻¹ • ∑ i, (σ i).prod β := by
  unfold avgM
  rw [Measure.prod_smul_left, prod_sum_left']

theorem integrable_avg_right {K : Torus d × Torus d → ℝ} (hN : N ≠ 0) (α : Measure (Torus d)) [SFinite α]
    (σ : Fin N → Measure (Torus d)) [∀ i, SFinite (σ i)] (h : ∀ i, Integrable K (α.prod (σ i))) :
    Integrable K (α.prod (avgM σ)) := by
  rw [avgM_prod_right]
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (by exact_mod_cast hN))
  exact integrable_finsetSum_measure.mpr fun i _ => h i

theorem integrable_avg_left {K : Torus d × Torus d → ℝ} (hN : N ≠ 0) (β : Measure (Torus d)) [SFinite β]
    (σ : Fin N → Measure (Torus d)) [∀ i, SFinite (σ i)] (h : ∀ i, Integrable K ((σ i).prod β)) :
    Integrable K ((avgM σ).prod β) := by
  rw [avgM_prod_left]
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (by exact_mod_cast hN))
  exact integrable_finsetSum_measure.mpr fun i _ => h i

theorem integral_avg_right {K : Torus d × Torus d → ℝ} (α : Measure (Torus d)) [SFinite α]
    (σ : Fin N → Measure (Torus d)) [∀ i, SFinite (σ i)] (h : ∀ i, Integrable K (α.prod (σ i))) :
    ∫ p, K p ∂(α.prod (avgM σ)) = (1 / (N : ℝ)) * ∑ i, ∫ p, K p ∂(α.prod (σ i)) := by
  rw [avgM_prod_right, integral_smul_measure, integral_finsetSum_measure (fun i _ => h i)]
  rw [ENNReal.toReal_inv]
  simp

theorem integral_avg_left {K : Torus d × Torus d → ℝ} (β : Measure (Torus d)) [SFinite β]
    (σ : Fin N → Measure (Torus d)) [∀ i, SFinite (σ i)] (h : ∀ i, Integrable K ((σ i).prod β)) :
    ∫ p, K p ∂((avgM σ).prod β) = (1 / (N : ℝ)) * ∑ i, ∫ p, K p ∂((σ i).prod β) := by
  rw [avgM_prod_left, integral_smul_measure, integral_finsetSum_measure (fun i _ => h i)]
  rw [ENNReal.toReal_inv]
  simp

/-- Expansion of the quadratic form of the averaged charge. -/
theorem quadForm_avg {K : Torus d → Torus d → ℝ} (hN : N ≠ 0) (σ : Fin N → Measure (Torus d))
    [∀ i, IsFiniteMeasure (σ i)] (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (hσσ : ∀ i j, Integrable (fun p : Torus d × Torus d => K p.1 p.2) ((σ i).prod (σ j)))
    (hσμ : ∀ i, Integrable (fun p : Torus d × Torus d => K p.1 p.2) ((σ i).prod μ))
    (hμμ : Integrable (fun p : Torus d × Torus d => K p.1 p.2) (μ.prod μ)) :
    quadForm K (avgM σ) μ =
      (1 / (N : ℝ)) ^ 2 * ∑ i, ∑ j, ∫ p, K p.1 p.2 ∂((σ i).prod (σ j))
        - 2 * ((1 / (N : ℝ)) * ∑ i, ∫ p, K p.1 p.2 ∂((σ i).prod μ))
        + ∫ p, K p.1 p.2 ∂(μ.prod μ) := by
  have : IsFiniteMeasure (avgM σ) := by
    unfold avgM
    refine ⟨?_⟩
    simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by simpa using Nat.pos_of_ne_zero hN))
      (ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top _ _)
  have hν1 : Integrable (fun p : Torus d × Torus d => K p.1 p.2) ((avgM σ).prod (avgM σ)) := by
    refine integrable_avg_left hN _ σ fun i => ?_
    exact integrable_avg_right hN _ σ fun j => hσσ i j
  have hν2 : Integrable (fun p : Torus d × Torus d => K p.1 p.2) ((avgM σ).prod μ) :=
    integrable_avg_left hN _ σ hσμ
  unfold quadForm
  rw [← integral_prod (fun p : Torus d × Torus d => K p.1 p.2) hν1,
    ← integral_prod (fun p : Torus d × Torus d => K p.1 p.2) hν2,
    ← integral_prod (fun p : Torus d × Torus d => K p.1 p.2) hμμ]
  rw [integral_avg_left _ σ (fun i => integrable_avg_right hN _ σ fun j => hσσ i j),
    integral_avg_left _ σ hσμ]
  have : ∀ i, ∫ p, K p.1 p.2 ∂((σ i).prod (avgM σ)) = (1 / (N : ℝ)) * ∑ j, ∫ p, K p.1 p.2 ∂((σ i).prod (σ j)) :=
    fun i => integral_avg_right _ σ (hσσ i)
  simp_rw [this, ← Finset.mul_sum]
  ring


/-! ### `L¹` convolution facts for the force -/

section Conv

variable {w : Torus d → Euc d}

theorem tdist_ge_of_near {x y a : Torus d} {η : ℝ} (h : KernelGrad.tdist x a ≤ η) :
    KernelGrad.tdist y a - η ≤ KernelGrad.tdist x y := by
  have h1 := EnergyAux.tdist_add_ge (a - y) (x - a)
  have e1 : (x - a) + (a - y) = x - y := by abel
  rw [e1] at h1
  have e2 : KernelGrad.tdist (a - y) 0 = KernelGrad.tdist y a := by
    rw [EnergyAux.tdist_def y a, ← KernelGrad.tdist_neg]
    congr 1; abel
  have e3 : KernelGrad.tdist (x - a) 0 = KernelGrad.tdist x a := (EnergyAux.tdist_def x a).symm
  have e4 : KernelGrad.tdist (x - y) 0 = KernelGrad.tdist x y := (EnergyAux.tdist_def x y).symm
  rw [e2, e3, e4] at h1
  linarith

theorem integrable_norm_conv (hwm : Measurable w) (hwint : Integrable w volume) (σ : Measure (Torus d))
    [IsFiniteMeasure σ] :
    Integrable (fun p : Torus d × Torus d => ‖w (p.1 - p.2)‖) (σ.prod volume) := by
  have hm : Measurable fun p : Torus d × Torus d => ‖w (p.1 - p.2)‖ :=
    (hwm.comp (measurable_fst.sub measurable_snd)).norm
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · exact (hwint.comp_sub_left x).norm
  · have : (fun x : Torus d => ∫ y, ‖‖w (x - y)‖‖ ∂(volume : Measure (Torus d))) = fun _ => ∫ y, ‖w y‖ := by
      funext x
      simp only [norm_norm]
      exact integral_sub_left_eq_self (fun y => ‖w y‖) volume x
    rw [this]
    exact integrable_const _

theorem ae_integrable_w_sub (hwm : Measurable w) (hwint : Integrable w volume) (σ : Measure (Torus d))
    [IsFiniteMeasure σ] : ∀ᵐ y ∂(volume : Measure (Torus d)), Integrable (fun x => w (x - y)) σ := by
  have h2 := (integrable_norm_conv hwm hwint σ).prod_left_ae
  filter_upwards [h2] with y hy
  exact (integrable_norm_iff (hwm.comp (measurable_id.sub measurable_const)).aestronglyMeasurable).mp hy

theorem integrable_pot (hwm : Measurable w) (hwint : Integrable w volume) (σ : Measure (Torus d))
    [IsFiniteMeasure σ] : Integrable (fun y => ∫ x, w (x - y) ∂σ) (volume : Measure (Torus d)) := by
  have h : Integrable (fun p : Torus d × Torus d => w (p.2 - p.1)) ((volume : Measure (Torus d)).prod σ) := by
    have := (integrable_norm_conv hwm hwint σ).swap
    refine (integrable_norm_iff ?_).mp ?_
    · exact (hwm.comp (measurable_snd.sub measurable_fst)).aestronglyMeasurable
    · exact this
  exact h.integral_prod_left

end Conv


/-! ### Geometry and reproducing property -/

theorem tdist_symm' (x y : Torus d) : KernelGrad.tdist x y = KernelGrad.tdist y x := by
  rw [EnergyAux.tdist_def x y, EnergyAux.tdist_def y x, ← KernelGrad.tdist_neg]
  congr 1; abel

theorem measurable_kern {w v : Torus d → Euc d} (hwm : Measurable w) (hvm : Measurable v) :
    Measurable fun p : Torus d × Torus d => kern w v p.1 p.2 := by
  unfold kern
  exact Measurable.inner ((hvm.comp measurable_fst).sub (hvm.comp measurable_snd))
    (hwm.comp (measurable_fst.sub measurable_snd))

section Block

variable {N : ℕ} {w v : Torus d → Euc d} {X : Fin N → Torus d} {η : Fin N → ℝ}
  {σ : Fin N → Measure (Torus d)} [∀ i, IsFiniteMeasure (σ i)]

/-- `w(· - y)` is bounded on the support of `σ i` for `y` outside the ball. -/
theorem w_bdd_near (hwbdd : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ z, δ ≤ KernelGrad.tdist z 0 → ‖w z‖ ≤ B)
    (hsupp : ∀ i, ∀ᵐ x ∂σ i, KernelGrad.tdist x (X i) ≤ η i) {i : Fin N} {y : Torus d}
    (hy : η i < KernelGrad.tdist y (X i)) :
    ∃ B : ℝ, ∀ᵐ x ∂σ i, ‖w (x - y)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hwbdd (KernelGrad.tdist y (X i) - η i) (by linarith)
  refine ⟨B, ?_⟩
  filter_upwards [hsupp i] with x hx
  apply hB
  have := tdist_ge_of_near (y := y) hx
  rw [← EnergyAux.tdist_def x y]
  exact this

theorem integrable_w_sub_near (hwm : Measurable w)
    (hwbdd : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ z, δ ≤ KernelGrad.tdist z 0 → ‖w z‖ ≤ B)
    (hsupp : ∀ i, ∀ᵐ x ∂σ i, KernelGrad.tdist x (X i) ≤ η i) {i : Fin N} {y : Torus d}
    (hy : η i < KernelGrad.tdist y (X i)) : Integrable (fun x => w (x - y)) (σ i) := by
  obtain ⟨B, hB⟩ := w_bdd_near hwbdd hsupp hy
  refine Integrable.mono' (integrable_const B)
    (hwm.comp (measurable_id.sub measurable_const)).aestronglyMeasurable ?_
  filter_upwards [hB] with x hx
  exact hx

/-- Reproducing property in the form used in `kern_integral_charge`. -/
theorem rep' (hwodd : ∀ z, w (-z) = -w z)
    (hrep : ∀ i y, η i < KernelGrad.tdist y (X i) → ∫ x, w (y - x) ∂σ i = w (y - X i))
    {i : Fin N} {y : Torus d} (hy : η i < KernelGrad.tdist y (X i)) :
    ∫ x, w (x - y) ∂σ i = w (X i - y) := by
  have e : ∀ x, w (x - y) = -w (y - x) := fun x => by
    rw [← hwodd]; congr 1; abel
  simp_rw [e]
  rw [integral_neg, hrep i y hy, ← hwodd]


theorem ae_far (hsupp : ∀ i, ∀ᵐ x ∂σ i, KernelGrad.tdist x (X i) ≤ η i)
    (hsep : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j)) {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ p ∂((σ i).prod (σ j)),
      KernelGrad.tdist (X i) (X j) - η i - η j ≤ KernelGrad.tdist (p.1 - p.2) 0 := by
  have h1 : ∀ᵐ p ∂((σ i).prod (σ j)), KernelGrad.tdist p.1 (X i) ≤ η i :=
    Measure.quasiMeasurePreserving_fst.ae (hsupp i)
  have h2 : ∀ᵐ p ∂((σ i).prod (σ j)), KernelGrad.tdist p.2 (X j) ≤ η j :=
    Measure.quasiMeasurePreserving_snd.ae (hsupp j)
  filter_upwards [h1, h2] with p hp1 hp2
  have a1 := tdist_ge_of_near (y := p.2) hp1
  have a2 := tdist_ge_of_near (y := X i) hp2
  rw [← EnergyAux.tdist_def p.1 p.2]
  linarith

theorem integrable_kern_pair (hwm : Measurable w) (hvm : Measurable v) {Cv : ℝ} (hvb : ∀ x, ‖v x‖ ≤ Cv)
    (hwbdd : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ z, δ ≤ KernelGrad.tdist z 0 → ‖w z‖ ≤ B)
    (hsupp : ∀ i, ∀ᵐ x ∂σ i, KernelGrad.tdist x (X i) ≤ η i)
    (hsep : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j)) {i j : Fin N} (hij : i ≠ j) :
    Integrable (fun p : Torus d × Torus d => kern w v p.1 p.2) ((σ i).prod (σ j)) := by
  have hδ : 0 < KernelGrad.tdist (X i) (X j) - η i - η j := by linarith [hsep i j hij]
  obtain ⟨B, hB⟩ := hwbdd _ hδ
  refine Integrable.mono' (integrable_const (2 * Cv * B)) (measurable_kern hwm hvm).aestronglyMeasurable ?_
  filter_upwards [ae_far hsupp hsep hij] with p hp
  have h1 := hB _ hp
  unfold kern
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h2 : ‖v p.1 - v p.2‖ ≤ 2 * Cv := by
    have := norm_sub_le (v p.1) (v p.2)
    linarith [hvb p.1, hvb p.2]
  exact mul_le_mul h2 h1 (norm_nonneg _) (by linarith [norm_nonneg (v p.1 - v p.2), h2])


theorem pair_block (hwm : Measurable w) (hwodd : ∀ z, w (-z) = -w z)
    (hwbdd : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ z, δ ≤ KernelGrad.tdist z 0 → ‖w z‖ ≤ B)
    (hvm : Measurable v) {Cv : ℝ} (hvb : ∀ x, ‖v x‖ ≤ Cv)
    (hη0 : ∀ i, 0 ≤ η i)
    (hsupp : ∀ i, ∀ᵐ x ∂σ i, KernelGrad.tdist x (X i) ≤ η i)
    (hrep : ∀ i y, η i < KernelGrad.tdist y (X i) → ∫ x, w (y - x) ∂σ i = w (y - X i))
    (hsep : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j)) {i j : Fin N} (hij : i ≠ j) :
    ∫ p, kern w v p.1 p.2 ∂((σ i).prod (σ j)) =
      kern w v (X i) (X j) - ∫ x, inner ℝ (v (X i) - v x) (w (x - X j)) ∂σ i
        - ∫ y, inner ℝ (v (X j) - v y) (w (y - X i)) ∂σ j := by
  have hwodd' := hwodd
  have hint := integrable_kern_pair hwm hvm hvb hwbdd hsupp hsep hij
  have hji : j ≠ i := fun h => hij h.symm
  have hsepij := hsep i j hij
  have hsepji := hsep j i hji
  rw [integral_prod _ hint]
  -- geometry: points of `supp σ_i` are outside the ball `j`
  have hout_x : ∀ᵐ x ∂σ i, η j < KernelGrad.tdist x (X j) := by
    filter_upwards [hsupp i] with x hx
    have := tdist_ge_of_near (y := X j) hx
    rw [tdist_symm' (X j) (X i)] at this
    linarith
  have hout_y : ∀ᵐ y ∂σ j, η i < KernelGrad.tdist y (X i) := by
    filter_upwards [hsupp j] with y hy
    have := tdist_ge_of_near (y := X i) hy
    linarith
  -- (1) inner integral
  have hinner : ∀ᵐ x ∂σ i, ∫ y, kern w v x y ∂σ j =
      kern w v (X j) x - ∫ y, inner ℝ (v (X j) - v y) (w (y - x)) ∂σ j := by
    filter_upwards [hout_x] with x hx
    have h1 : ∫ y, kern w v x y ∂σ j = ∫ y, kern w v y x ∂σ j :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => kern_symm hwodd v y x)
    rw [h1, kern_integral_charge w v (X j) x hvm hvb (integrable_w_sub_near hwm hwbdd hsupp hx),
      rep' hwodd hrep hx]
    simp
  rw [integral_congr_ae hinner]
  obtain ⟨B1, hB1⟩ := hwbdd (KernelGrad.tdist (X i) (X j) - η i - η j) (by linarith)
  obtain ⟨B2, hB2⟩ := hwbdd (KernelGrad.tdist (X i) (X j) - η i) (by linarith [hη0 j])
  have hG : Integrable (fun p : Torus d × Torus d => inner ℝ (v (X j) - v p.2) (w (p.2 - p.1)))
      ((σ i).prod (σ j)) := by
    refine Integrable.mono' (integrable_const (2 * Cv * B1)) ?_ ?_
    · exact Measurable.aestronglyMeasurable
        (Measurable.inner ((measurable_const).sub (hvm.comp measurable_snd))
          (hwm.comp (measurable_snd.sub measurable_fst)))
    · filter_upwards [ae_far hsupp hsep hij] with p hp
      have h1 := hB1 (p.2 - p.1) (by
        have : KernelGrad.tdist (p.2 - p.1) 0 = KernelGrad.tdist (p.1 - p.2) 0 := by
          rw [← KernelGrad.tdist_neg]; congr 1; abel
        rw [this]; exact hp)
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      have h2 : ‖v (X j) - v p.2‖ ≤ 2 * Cv := by
        have := norm_sub_le (v (X j)) (v p.2)
        linarith [hvb (X j), hvb p.2]
      exact mul_le_mul h2 h1 (norm_nonneg _) (by linarith [norm_nonneg (v (X j) - v p.2), h2])
  have hA := hG.integral_prod_left
  have hf1 : Integrable (fun x => kern w v (X j) x) (σ i) := by
    refine Integrable.mono' (integrable_const (2 * Cv * B2)) ?_ ?_
    · exact (measurable_kern hwm hvm).comp (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable
    · filter_upwards [hsupp i] with x hx
      have h1 := hB2 (X j - x) (by
        have := tdist_ge_of_near (y := X j) hx
        rw [← EnergyAux.tdist_def, tdist_symm' (X j) x, tdist_symm' (X j) (X i)] at *
        linarith)
      unfold kern
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      have h2 : ‖v (X j) - v x‖ ≤ 2 * Cv := by
        have := norm_sub_le (v (X j)) (v x)
        linarith [hvb (X j), hvb x]
      exact mul_le_mul h2 h1 (norm_nonneg _) (by linarith [norm_nonneg (v (X j) - v x), h2])
  rw [integral_sub hf1 hA]
  -- first piece
  have hfirst : ∫ x, kern w v (X j) x ∂σ i = kern w v (X i) (X j) -
      ∫ x, inner ℝ (v (X i) - v x) (w (x - X j)) ∂σ i := by
    have hXj : η i < KernelGrad.tdist (X j) (X i) := by
      rw [tdist_symm' (X j) (X i)]; linarith [hη0 j]
    have h1 : ∫ x, kern w v (X j) x ∂σ i = ∫ x, kern w v x (X j) ∂σ i :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => kern_symm hwodd v x (X j))
    rw [h1, kern_integral_charge w v (X i) (X j) hvm hvb (integrable_w_sub_near hwm hwbdd hsupp hXj),
      rep' hwodd hrep hXj]
    simp
  rw [hfirst]
  -- second piece
  have hsecond : ∫ x, ∫ y, inner ℝ (v (X j) - v y) (w (y - x)) ∂σ j ∂σ i =
      ∫ y, inner ℝ (v (X j) - v y) (w (y - X i)) ∂σ j := by
    have hsw := integral_integral_swap (f := fun x y => inner ℝ (v (X j) - v y) (w (y - x))) hG
    rw [hsw]
    refine integral_congr_ae ?_
    filter_upwards [hout_y] with y hy
    have hw1 : Integrable (fun x => w (y - x)) (σ i) := by
      have := (integrable_w_sub_near hwm hwbdd hsupp hy).neg
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.neg_apply]
      rw [← hwodd]; congr 1; abel
    rw [integral_inner hw1, hrep i y hy]
  rw [hsecond]

end Block


/-! ### Background measure with bounded density -/

section Mu

variable {w : Torus d → Euc d} {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞}

theorem integrable_mu_of_vol {E : Type*} [NormedAddCommGroup E] {f : Torus d → E}
    (hf : Integrable f volume) (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d))) :
    Integrable f μ :=
  (hf.smul_measure hc).mono_measure hμ

theorem integrable_norm_conv_mu (hwm : Measurable w) (hwint : Integrable w volume)
    (σ : Measure (Torus d)) [IsFiniteMeasure σ] (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d))) :
    Integrable (fun p : Torus d × Torus d => ‖w (p.1 - p.2)‖) (σ.prod μ) := by
  have h := (integrable_norm_conv hwm hwint σ).smul_measure hc
  have e : σ.prod (c • (volume : Measure (Torus d))) = c • σ.prod volume := Measure.prod_smul_right c
  rw [← e] at h
  exact h.mono_measure (Measure.prod_mono le_rfl hμ)

theorem norm_conv_mu_le (hwint : Integrable w volume) (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) (x : Torus d) :
    ‖∫ y, w (x - y) ∂μ‖ ≤ c.toReal * ∫ z, ‖w z‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  have h1 : Integrable (fun y => ‖w (x - y)‖) volume := (hwint.comp_sub_left x).norm
  calc ∫ y, ‖w (x - y)‖ ∂μ ≤ ∫ y, ‖w (x - y)‖ ∂(c • (volume : Measure (Torus d))) :=
        integral_mono_measure hμ (Filter.Eventually.of_forall fun y => norm_nonneg _)
          (h1.smul_measure hc)
    _ = c.toReal * ∫ z, ‖w z‖ := by
        rw [integral_smul_measure]
        simp only [smul_eq_mul]
        congr 1
        exact integral_sub_left_eq_self (fun z => ‖w z‖) volume x


theorem cross_block {N : ℕ} {X : Fin N → Torus d} {σ : Fin N → Measure (Torus d)}
    [∀ i, IsFiniteMeasure (σ i)] {v : Torus d → Euc d}
    (hwm : Measurable w) (hwint : Integrable w volume)
    (hvm : Measurable v) {Cv : ℝ} (hvb : ∀ x, ‖v x‖ ≤ Cv) (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) (i : Fin N)
    (hint : Integrable (fun p : Torus d × Torus d => kern w v p.1 p.2) ((σ i).prod μ)) :
    ∫ p, kern w v p.1 p.2 ∂((σ i).prod μ) =
      ∫ y, kern w v (X i) y ∂μ
        - ∫ y, inner ℝ (v (X i) - v y) (w (X i - y) - ∫ x, w (x - y) ∂σ i) ∂μ
        - ∫ x, inner ℝ (v (X i) - v x) (∫ y, w (x - y) ∂μ) ∂σ i := by
  have hvmeas := hvm
  rw [integral_prod_symm _ hint]
  -- the a.e. identity from `kern_integral_charge`
  have hae : ∀ᵐ y ∂μ, ∫ x, kern w v x y ∂σ i =
      kern w v (X i) y - ∫ x, inner ℝ (v (X i) - v x) (w (x - y)) ∂σ i -
        inner ℝ (v (X i) - v y) (w (X i - y) - ∫ x, w (x - y) ∂σ i) := by
    have h0 := ae_integrable_w_sub hwm hwint (σ i)
    have h1 : ∀ᵐ y ∂μ, Integrable (fun x => w (x - y)) (σ i) :=
      (Measure.AbsolutelyContinuous.ae_le (Measure.absolutelyContinuous_of_le_smul hμ) h0)
    filter_upwards [h1] with y hy
    exact kern_integral_charge w v (X i) y hvm hvb hy
  rw [integral_congr_ae hae]
  -- integrability of the three pieces
  have hf1 : Integrable (fun y => kern w v (X i) y) μ := by
    have hw1 : Integrable (fun y => w (X i - y)) volume := hwint.comp_sub_left _
    refine integrable_mu_of_vol (c := c) ?_ hc hμ
    refine Integrable.mono' (hw1.norm.const_mul (2 * Cv))
      ((measurable_kern hwm hvm).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun y => ?_
    unfold kern
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h2 : ‖v (X i) - v y‖ ≤ 2 * Cv := by
      have := norm_sub_le (v (X i)) (v y)
      linarith [hvb (X i), hvb y]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hG : Integrable (fun p : Torus d × Torus d => inner ℝ (v (X i) - v p.1) (w (p.1 - p.2)))
      ((σ i).prod μ) := by
    refine Integrable.mono' ((integrable_norm_conv_mu hwm hwint (σ i) hc hμ).const_mul (2 * Cv))
      (Measurable.aestronglyMeasurable
        (Measurable.inner (measurable_const.sub (hvm.comp measurable_fst))
          (hwm.comp (measurable_fst.sub measurable_snd)))) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h2 : ‖v (X i) - v p.1‖ ≤ 2 * Cv := by
      have := norm_sub_le (v (X i)) (v p.1)
      linarith [hvb (X i), hvb p.1]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hf2 : Integrable (fun y => ∫ x, inner ℝ (v (X i) - v x) (w (x - y)) ∂σ i) μ :=
    hG.integral_prod_right
  have hpot : Integrable (fun y => ∫ x, w (x - y) ∂σ i) μ :=
    integrable_mu_of_vol (integrable_pot hwm hwint (σ i)) hc hμ
  have hf3 : Integrable (fun y => inner ℝ (v (X i) - v y) (w (X i - y) - ∫ x, w (x - y) ∂σ i)) μ := by
    have hw1 : Integrable (fun y => w (X i - y)) μ := integrable_mu_of_vol (hwint.comp_sub_left _) hc hμ
    have hd : Integrable (fun y => w (X i - y) - ∫ x, w (x - y) ∂σ i) μ := hw1.sub hpot
    exact integrable_inner_of_bdd (hvm.const_sub (v (X i)) ) (C := ‖v (X i)‖ + Cv)
      (fun y => (norm_sub_le _ _).trans (by linarith [hvb y])) hd
  have hf12 : Integrable (fun y => kern w v (X i) y - ∫ x, inner ℝ (v (X i) - v x) (w (x - y)) ∂σ i) μ :=
    hf1.sub hf2
  rw [integral_sub hf12 hf3, integral_sub hf1 hf2]
  -- the middle term via Fubini
  have hmid : ∫ y, ∫ x, inner ℝ (v (X i) - v x) (w (x - y)) ∂σ i ∂μ =
      ∫ x, inner ℝ (v (X i) - v x) (∫ y, w (x - y) ∂μ) ∂σ i := by
    have hsw := integral_integral_swap (f := fun x y => inner ℝ (v (X i) - v x) (w (x - y))) hG
    rw [← hsw]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hwx : Integrable (fun y => w (x - y)) μ := integrable_mu_of_vol (hwint.comp_sub_left x) hc hμ
    simp only []
    rw [integral_inner hwx]
  rw [hmid]
  ring


theorem sum_erase_swap {N : ℕ} (f : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f j i = ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  have h := Finset.sum_comm' (s := (Finset.univ : Finset (Fin N))) (t := fun x => Finset.univ.erase x)
    (s' := fun y => Finset.univ.erase y) (t' := (Finset.univ : Finset (Fin N))) (f := fun x y => f x y)
    (fun x y => by simp [Finset.mem_erase, eq_comm])
  exact h.symm

/-- **Exact decomposition `P = Q + R`** (abstract form). -/
theorem comm_decomp {N : ℕ} {X : Fin N → Torus d} {η : Fin N → ℝ} {σ : Fin N → Measure (Torus d)}
    [∀ i, IsFiniteMeasure (σ i)] {v : Torus d → Euc d}
    (hN : N ≠ 0) (hwm : Measurable w) (hwodd : ∀ z, w (-z) = -w z) (hwint : Integrable w volume)
    (hwbdd : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ z, δ ≤ KernelGrad.tdist z 0 → ‖w z‖ ≤ B)
    (hvm : Measurable v) {Cv : ℝ} (hvb : ∀ x, ‖v x‖ ≤ Cv) (hη0 : ∀ i, 0 ≤ η i)
    (hsupp : ∀ i, ∀ᵐ x ∂σ i, KernelGrad.tdist x (X i) ≤ η i)
    (hrep : ∀ i y, η i < KernelGrad.tdist y (X i) → ∫ x, w (y - x) ∂σ i = w (y - X i))
    (hsep : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j))
    (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d)))
    (hii : ∀ i, Integrable (fun p : Torus d × Torus d => kern w v p.1 p.2) ((σ i).prod (σ i)))
    (hiμ : ∀ i, Integrable (fun p : Torus d × Torus d => kern w v p.1 p.2) ((σ i).prod μ))
    (hμμ : Integrable (fun p : Torus d × Torus d => kern w v p.1 p.2) (μ.prod μ)) :
    offDiagPairing (commKernel w v) X μ =
      quadForm (commKernel w v) (avgM σ) μ
        - (1 / (N : ℝ)) ^ 2 * ∑ i, ∫ p, kern w v p.1 p.2 ∂((σ i).prod (σ i))
        - (2 / (N : ℝ)) * ∑ i, ∫ y, inner ℝ (v (X i) - v y) (w (X i - y) - ∫ x, w (x - y) ∂σ i) ∂μ
        + (2 / (N : ℝ)) * ∑ i, ∫ x, inner ℝ (v (X i) - v x)
            ((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, w (x - X j) - ∫ y, w (x - y) ∂μ) ∂σ i := by
  have hk : commKernel w v = kern w v := funext fun x => funext fun y => commKernel_eq_kern w v x y
  rw [hk]
  have hij : ∀ i j, Integrable (fun p : Torus d × Torus d => kern w v p.1 p.2) ((σ i).prod (σ j)) := by
    intro i j
    by_cases h : i = j
    · subst h; exact hii i
    · exact integrable_kern_pair hwm hvm hvb hwbdd hsupp hsep h
  rw [quadForm_avg hN σ μ hij hiμ hμμ]
  -- the point-pairing side
  unfold offDiagPairing
  rw [← integral_prod (fun p : Torus d × Torus d => kern w v p.1 p.2) hμμ]
  -- diagonal blocks and off-diagonal blocks
  have hsplit : ∀ i, ∑ j, ∫ p, kern w v p.1 p.2 ∂((σ i).prod (σ j)) =
      (∫ p, kern w v p.1 p.2 ∂((σ i).prod (σ i))) +
        ∑ j ∈ Finset.univ.erase i, (kern w v (X i) (X j) -
          ∫ x, inner ℝ (v (X i) - v x) (w (x - X j)) ∂σ i -
          ∫ y, inner ℝ (v (X j) - v y) (w (y - X i)) ∂σ j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    exact pair_block hwm hwodd hwbdd hvm hvb hη0 hsupp hrep hsep (Finset.ne_of_mem_erase hj).symm
  simp_rw [hsplit]
  simp_rw [cross_block hwm hwint hvm hvb hc hμ (X := X) (σ := σ) _ (hiμ _)]
  -- the field term
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Fin N → Fin N → ℝ, ∀ i j, Θ i j = ∫ x, inner ℝ (v (X i) - v x) (w (x - X j)) ∂σ i :=
    ⟨fun i j => _, fun _ _ => rfl⟩
  obtain ⟨Cm, hCm⟩ : ∃ Cm : Fin N → ℝ, ∀ i, Cm i =
      ∫ x, inner ℝ (v (X i) - v x) (∫ y, w (x - y) ∂μ) ∂σ i := ⟨fun i => _, fun _ => rfl⟩
  have hT : ∀ i, ∫ x, inner ℝ (v (X i) - v x)
      ((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, w (x - X j) - ∫ y, w (x - y) ∂μ) ∂σ i =
      (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, Θ i j - Cm i := by
    intro i
    have hint1 : ∀ j ∈ Finset.univ.erase i,
        Integrable (fun x => inner ℝ (v (X i) - v x) (w (x - X j))) (σ i) := by
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hy : η i < KernelGrad.tdist (X j) (X i) := by
        rw [tdist_symm' (X j) (X i)]; linarith [hsep i j hji.symm, hη0 j]
      exact integrable_inner_of_bdd (hvm.const_sub (v (X i))) (C := ‖v (X i)‖ + Cv)
        (fun y => (norm_sub_le _ _).trans (by linarith [hvb y])) (integrable_w_sub_near hwm hwbdd hsupp hy)
    have hint2 : Integrable (fun x => inner ℝ (v (X i) - v x) (∫ y, w (x - y) ∂μ)) (σ i) := by
      have hmeas : AEStronglyMeasurable (fun x => ∫ y, w (x - y) ∂μ) (σ i) :=
        (hwm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.integral_prod_right'
      refine Integrable.mono' (integrable_const ((‖v (X i)‖ + Cv) * (c.toReal * ∫ z, ‖w z‖)))
        ((hvm.const_sub (v (X i))).aestronglyMeasurable.inner hmeas) (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      exact mul_le_mul ((norm_sub_le _ _).trans (by linarith [hvb x])) (norm_conv_mu_le hwint hc hμ x)
        (norm_nonneg _) (by linarith [norm_nonneg (v (X i)), hvb (X i), (norm_nonneg (v x)).trans (hvb x)])
    have hint3 : Integrable (fun x => inner ℝ (v (X i) - v x)
        ((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, w (x - X j))) (σ i) := by
      have : ∀ x, inner ℝ (v (X i) - v x) ((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, w (x - X j)) =
          (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, inner ℝ (v (X i) - v x) (w (x - X j)) := by
        intro x
        rw [inner_smul_right, inner_sum]
      simp_rw [this]
      exact (integrable_finsetSum _ hint1).const_mul _
    simp_rw [inner_sub_right]
    rw [integral_sub hint3 hint2, hCm]
    congr 1
    have : ∀ x, inner ℝ (v (X i) - v x) ((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, w (x - X j)) =
        (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, inner ℝ (v (X i) - v x) (w (x - X j)) := by
      intro x
      rw [inner_smul_right, inner_sum]
    simp_rw [this]
    rw [integral_const_mul, integral_finsetSum _ hint1]
    simp_rw [hΘ]
  simp_rw [hT]
  have hswap : ∑ i, ∑ j ∈ Finset.univ.erase i, Θ j i = ∑ i, ∑ j ∈ Finset.univ.erase i, Θ i j :=
    sum_erase_swap Θ
  simp only [← hΘ, ← hCm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hswap]
  ring

end Mu

end HRS.Commutator.Renorm
