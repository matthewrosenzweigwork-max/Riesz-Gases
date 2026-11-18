import HRS.Uniform.Spec
import HRS.Uniform.Q45Blocks4

/-!
# Q45: piecewise-linear interpolation in `C([0,T];E)`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

/-- The hat function centred at `iT/g` of width `T/g`. -/
def hatFn (T : ℝ) (g i : ℕ) (t : ℝ) : ℝ := max 0 (1 - |t * g / T - i|)

lemma hatFn_nonneg (T : ℝ) (g i : ℕ) (t : ℝ) : 0 ≤ hatFn T g i t := le_max_left _ _

lemma hatFn_le_one (T : ℝ) (g i : ℕ) (t : ℝ) : hatFn T g i t ≤ 1 := by
  unfold hatFn
  exact max_le zero_le_one (by linarith [abs_nonneg (t * g / T - i)])

lemma continuous_hatFn (T : ℝ) (g i : ℕ) : Continuous (hatFn T g i) := by
  unfold hatFn
  fun_prop

lemma hatFn_eq_zero {T : ℝ} (g i : ℕ) {t : ℝ} (h : 1 ≤ |t * g / T - i|) : hatFn T g i t = 0 := by
  unfold hatFn
  exact max_eq_left (by linarith)

/-- Partition of unity. -/
lemma hatFn_sum {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ∑ i ∈ Finset.range (g + 1), hatFn T g i t = 1 := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  set s : ℝ := t * g / T with hs
  have hs0 : 0 ≤ s := by positivity [ht.1]
  have hsg : s ≤ g := by
    rw [hs, div_le_iff₀ hT]
    nlinarith [ht.2]
  set k : ℕ := ⌊s⌋₊ with hk
  have hk1 : (k : ℝ) ≤ s := Nat.floor_le hs0
  have hk2 : s < k + 1 := Nat.lt_floor_add_one s
  have hkg : k ≤ g := by
    have : (k : ℝ) ≤ g := hk1.trans hsg
    exact_mod_cast this
  have hz : ∀ i ∈ Finset.range (g + 1), i ≠ k → i ≠ k + 1 → hatFn T g i t = 0 := by
    intro i _ h1 h2
    apply hatFn_eq_zero
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hlt
      rw [abs_of_nonneg (by linarith)]; linarith
    · have hgt2 : k + 2 ≤ i := by omega
      have : (k : ℝ) + 2 ≤ i := by exact_mod_cast hgt2
      rw [abs_of_nonpos (by linarith)]; linarith
  have hvk : hatFn T g k t = 1 - (s - k) := by
    unfold hatFn
    rw [← hs, abs_of_nonneg (by linarith)]
    exact max_eq_right (by linarith)
  by_cases hkgt : k = g
  · have hsg' : s = g := by
      have : (g : ℝ) ≤ s := by rw [← hkgt]; exact hk1
      linarith
    have hmem : k ∈ Finset.range (g + 1) := Finset.mem_range.2 (by omega)
    rw [Finset.sum_eq_single_of_mem k hmem (fun i hi hik => hz i hi hik (by
      intro h; have := Finset.mem_range.1 hi; omega)), hvk, hsg', hkgt]
    simp
  · have hk' : k < g := lt_of_le_of_ne hkg hkgt
    have hmem : k ∈ Finset.range (g + 1) := Finset.mem_range.2 (by omega)
    have hmem' : k + 1 ∈ Finset.range (g + 1) := Finset.mem_range.2 (by omega)
    have hvk1 : hatFn T g (k + 1) t = 1 - (k + 1 - s) := by
      have e : |s - ((k + 1 : ℕ) : ℝ)| = (k + 1) - s := by
        rw [abs_of_nonpos (by push_cast; linarith)]
        push_cast; ring
      unfold hatFn
      rw [← hs, e]
      exact max_eq_right (by linarith)
    rw [Finset.sum_eq_add_of_mem k (k + 1) hmem hmem' (by omega) (fun c hc hc' =>
      hz c hc hc'.1 hc'.2), hvk, hvk1]
    ring

lemma hatFn_support {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) (i : ℕ) {t : ℝ}
    (h : hatFn T g i t ≠ 0) : |t - i * T / g| < T / g := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  by_contra hcon
  rw [not_lt] at hcon
  apply h
  apply hatFn_eq_zero
  have : |t * g / T - i| = |t - i * T / g| * g / T := by
    have e : t * g / T - i = (t - i * T / g) * g / T := by field_simp
    rw [e, abs_div, abs_mul, abs_of_pos hg', abs_of_pos hT]
  rw [this, le_div_iff₀ hT, one_mul]
  calc T = T / g * g := by field_simp
    _ ≤ |t - i * T / g| * g := mul_le_mul_of_nonneg_right hcon hg'.le


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A path as a continuous map. -/
def pcm {T : ℝ} (y : PathSp T E) : C(Set.Icc (0 : ℝ) T, E) := y

lemma pcm_ext {T : ℝ} {y y' : PathSp T E} (h : ∀ t, pcm y t = pcm y' t) : y = y' :=
  ContinuousMap.ext h

lemma pcm_add {T : ℝ} (y y' : PathSp T E) (t : Set.Icc (0 : ℝ) T) :
    pcm (y + y') t = pcm y t + pcm y' t := rfl

lemma pcm_sub {T : ℝ} (y y' : PathSp T E) (t : Set.Icc (0 : ℝ) T) :
    pcm (y - y') t = pcm y t - pcm y' t := rfl

lemma pcm_smul {T : ℝ} (c : ℝ) (y : PathSp T E) (t : Set.Icc (0 : ℝ) T) :
    pcm (c • y) t = c • pcm y t := rfl

lemma norm_pcm_le {T : ℝ} (y : PathSp T E) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t, ‖pcm y t‖ ≤ B) : ‖y‖ ≤ B :=
  (ContinuousMap.norm_le (pcm y) hB).2 h

lemma norm_pcm_apply_le {T : ℝ} (y : PathSp T E) (t : Set.Icc (0 : ℝ) T) : ‖pcm y t‖ ≤ ‖y‖ :=
  ContinuousMap.norm_coe_le_norm (pcm y) t

/-- The piecewise-linear path with values `v i` at the nodes `iT/g`. -/
def hatPath (T : ℝ) (g : ℕ) (v : Fin (g + 1) → E) : PathSp T E :=
  (⟨fun t => ∑ i : Fin (g + 1), hatFn T g i (t : ℝ) • v i, by
    refine continuous_finset_sum _ fun i _ => ?_
    exact ((continuous_hatFn T g i).comp continuous_subtype_val).smul continuous_const⟩ :
    C(Set.Icc (0 : ℝ) T, E))

lemma hatPath_apply (T : ℝ) (g : ℕ) (v : Fin (g + 1) → E) (t : Set.Icc (0 : ℝ) T) :
    pcm (hatPath T g v) t = ∑ i : Fin (g + 1), hatFn T g i (t : ℝ) • v i := rfl

lemma hatPath_add (T : ℝ) (g : ℕ) (v w : Fin (g + 1) → E) :
    hatPath T g (v + w) = hatPath T g v + hatPath T g w := by
  refine pcm_ext fun t => ?_
  rw [pcm_add, hatPath_apply, hatPath_apply, hatPath_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_add]

lemma hatPath_smul (T : ℝ) (g : ℕ) (c : ℝ) (v : Fin (g + 1) → E) :
    hatPath T g (c • v) = c • hatPath T g v := by
  refine pcm_ext fun t => ?_
  rw [pcm_smul, hatPath_apply, hatPath_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_smul, mul_comm]

lemma norm_hatPath_le {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) (v : Fin (g + 1) → E) {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ i, ‖v i‖ ≤ B) : ‖hatPath T g v‖ ≤ B := by
  refine norm_pcm_le _ hB fun t => ?_
  rw [hatPath_apply]
  calc ‖∑ i : Fin (g + 1), hatFn T g i (t : ℝ) • v i‖
      ≤ ∑ i : Fin (g + 1), ‖hatFn T g i (t : ℝ) • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (g + 1), hatFn T g i (t : ℝ) * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (hatFn_nonneg _ _ _ _)]
        exact mul_le_mul_of_nonneg_left (hv i) (hatFn_nonneg _ _ _ _)
    _ = B := by
        rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun i => hatFn T g i (t : ℝ)) (g + 1),
          hatFn_sum hT hg t.2, one_mul]

/-- The node values of a path at `iT/g`. -/
def samplePath {T : ℝ} (hT : 0 ≤ T) (g : ℕ) (y : PathSp T E) : Fin (g + 1) → E :=
  fun i => pcm y (Set.projIcc 0 T hT (i * T / g))

lemma hatPath_sample_close {T : ℝ} (hT : 0 < T) (y : PathSp T E) {ε : ℝ} (hε : 0 < ε) :
    ∃ g0 : ℕ, ∀ g ≥ g0, 1 ≤ g → ‖hatPath T g (samplePath hT.le g y) - y‖ ≤ ε := by
  have huc : UniformContinuous (pcm y) := CompactSpace.uniformContinuous_of_continuous (pcm y).continuous
  obtain ⟨δ, hδ, hδy⟩ := Metric.uniformContinuous_iff.1 huc ε hε
  obtain ⟨g0, hg0⟩ := exists_nat_gt (T / δ)
  refine ⟨g0, fun g hg hg1 => ?_⟩
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg1
  have hTg : T / g < δ := by
    rw [div_lt_iff₀ hg']
    have : (g0 : ℝ) ≤ g := by exact_mod_cast hg
    rw [div_lt_iff₀ hδ] at hg0
    nlinarith
  refine norm_pcm_le _ hε.le fun t => ?_
  have hsum : ∑ i : Fin (g + 1), hatFn T g i (t : ℝ) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => hatFn T g i (t : ℝ)) (g + 1)]
    exact hatFn_sum hT hg1 t.2
  have e : pcm (hatPath T g (samplePath hT.le g y) - y) t =
      ∑ i : Fin (g + 1), hatFn T g i (t : ℝ) • (samplePath hT.le g y i - pcm y t) := by
    rw [pcm_sub, hatPath_apply]
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hsum, one_smul]
  rw [e]
  calc ‖∑ i : Fin (g + 1), hatFn T g i (t : ℝ) • (samplePath hT.le g y i - pcm y t)‖
      ≤ ∑ i : Fin (g + 1), ‖hatFn T g i (t : ℝ) • (samplePath hT.le g y i - pcm y t)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin (g + 1), hatFn T g i (t : ℝ) * ε := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (hatFn_nonneg _ _ _ _)]
        by_cases h0 : hatFn T g i (t : ℝ) = 0
        · rw [h0]; simp
        · refine mul_le_mul_of_nonneg_left ?_ (hatFn_nonneg _ _ _ _)
          have hsupp := hatFn_support hT hg1 i h0
          have hi : (i : ℝ) * T / g ∈ Set.Icc 0 T := by
            refine ⟨by positivity, ?_⟩
            rw [div_le_iff₀ hg']
            have : (i : ℝ) ≤ g := by exact_mod_cast Nat.lt_succ_iff.1 i.2
            nlinarith
          have hd : dist (Set.projIcc 0 T hT.le (i * T / g)) t < δ := by
            rw [Subtype.dist_eq, Set.projIcc_of_mem hT.le hi, Real.dist_eq, abs_sub_comm]
            exact hsupp.trans hTg
          have := hδy hd
          rw [dist_eq_norm] at this
          exact this.le
    _ = ε := by rw [← Finset.sum_mul, hsum, one_mul]

end HRS.Uniform.Q45
