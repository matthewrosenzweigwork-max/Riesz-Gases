import Mathlib

/-!
# Lemma 7.5: second moment of a degenerate `U`-statistic (auxiliary development for `q08_energy_L2`,
prefix `q08e_`)

For a symmetric degenerate kernel `κ ∈ L²(μ⊗μ)` the ordered double sum
`D_N = ∑_{i ≠ j} κ(X_i, X_j)` has `E_{μ^{⊗N}} D_N² = 2 N (N - 1) ‖κ‖²`.  The proof is an induction on `N`
along the last coordinate.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

section DD

variable {T : Type*} [MeasurableSpace T]

/-- The ordered double sum over pairs of distinct indices. -/
def q08e_DD (κ : T → T → ℝ) {N : ℕ} (X : Fin N → T) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else κ (X i) (X j)

theorem q08e_DD_meas (κ : T → T → ℝ) (hm : Measurable (Function.uncurry κ)) {N : ℕ} :
    Measurable (q08e_DD κ : (Fin N → T) → ℝ) := by
  unfold q08e_DD
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  by_cases h : i = j
  · simp only [h, ite_true]; exact measurable_const
  · simp only [h, ite_false]
    have h2 : Measurable (fun X : Fin N → T => (X i, X j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hm.comp h2

theorem q08e_DD_succ (κ : T → T → ℝ) (hs : ∀ x y, κ x y = κ y x) {N : ℕ} (X : Fin (N + 1) → T) :
    q08e_DD κ X = q08e_DD κ (fun j : Fin N => X j.castSucc) +
      2 * ∑ j : Fin N, κ (X j.castSucc) (X (Fin.last N)) := by
  unfold q08e_DD
  have h1 : ∀ x : Fin N, (Fin.castSucc x = Fin.last N) = False := fun x =>
    eq_false (Fin.castSucc_lt_last x).ne
  have h2 : ∀ x : Fin N, (Fin.last N = Fin.castSucc x) = False := fun x =>
    eq_false (Fin.castSucc_lt_last x).ne'
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc, Fin.castSucc_inj, h1, h2, ite_false, ite_true, add_zero,
    Finset.sum_add_distrib]
  have : ∀ j : Fin N, κ (X (Fin.last N)) (X j.castSucc) = κ (X j.castSucc) (X (Fin.last N)) :=
    fun j => hs _ _
  simp only [this]
  ring


variable (μ : Measure T) [IsProbabilityMeasure μ]

/-- The map `(y, Y) ↦ (Y i, y)` is measure preserving from `μ ⊗ μ^{⊗N}` to `μ ⊗ μ`. -/
theorem q08e_mp_pair {N : ℕ} (i : Fin N) :
    MeasurePreserving (fun p : T × (Fin N → T) => (p.2 i, p.1))
      (μ.prod (Measure.pi fun _ : Fin N => μ)) (μ.prod μ) := by
  have h1 : MeasurePreserving (Prod.map (fun Y : Fin N → T => Y i) (id : T → T))
      ((Measure.pi fun _ : Fin N => μ).prod μ) (μ.prod μ) :=
    MeasurePreserving.prod (measurePreserving_eval (fun _ : Fin N => μ) i) (MeasurePreserving.id μ)
  exact h1.comp Measure.measurePreserving_swap

theorem q08e_memLp_f (κ : T → T → ℝ) (hκ : MemLp (Function.uncurry κ) 2 (μ.prod μ)) {N : ℕ}
    (i : Fin N) :
    MemLp (fun p : T × (Fin N → T) => κ (p.2 i) p.1) 2 (μ.prod (Measure.pi fun _ : Fin N => μ)) :=
  hκ.comp_measurePreserving (q08e_mp_pair μ i)


section Orth

variable (κ : T → T → ℝ) (hm : Measurable (Function.uncurry κ)) (hs : ∀ x y, κ x y = κ y x)
  (hd : ∀ x, ∫ y, κ x y ∂μ = 0) (hκ : MemLp (Function.uncurry κ) 2 (μ.prod μ))

include hm hs hd hκ

theorem q08e_orth {N : ℕ} (i i' : Fin N) (h : i ≠ i') :
    ∫ p : T × (Fin N → T), κ (p.2 i) p.1 * κ (p.2 i') p.1
      ∂(μ.prod (Measure.pi fun _ : Fin N => μ)) = 0 := by
  have hint : Integrable (fun p : T × (Fin N → T) => κ (p.2 i) p.1 * κ (p.2 i') p.1)
      (μ.prod (Measure.pi fun _ : Fin N => μ)) :=
    (q08e_memLp_f μ κ hκ i).integrable_mul (q08e_memLp_f μ κ hκ i')
  rw [integral_prod _ hint]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  have hrow : Measurable (fun x => κ x y) := hm.comp (measurable_id.prodMk measurable_const)
  have hind := (iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ (x : T) => κ x y)
    (fun _ => hrow.aemeasurable)).indepFun h
  have hmean : ∀ k : Fin N, ∫ Y : Fin N → T, κ (Y k) y ∂(Measure.pi fun _ : Fin N => μ) = 0 := by
    intro k
    have hmp := measurePreserving_eval (fun _ : Fin N => μ) k
    rw [← integral_map hmp.measurable.aemeasurable hrow.aestronglyMeasurable, hmp.map_eq]
    simp_rw [hs _ y]
    exact hd y
  have := hind.integral_mul_eq_mul_integral (hrow.comp (measurable_pi_apply i)).aestronglyMeasurable
    (hrow.comp (measurable_pi_apply i')).aestronglyMeasurable
  simp only [Pi.mul_apply] at this
  show ∫ Y : Fin N → T, κ (Y i) y * κ (Y i') y ∂(Measure.pi fun _ : Fin N => μ) = 0
  rw [this, hmean i, hmean i', zero_mul]

theorem q08e_diag {N : ℕ} (i : Fin N) :
    ∫ p : T × (Fin N → T), κ (p.2 i) p.1 ^ 2 ∂(μ.prod (Measure.pi fun _ : Fin N => μ)) =
      ∫ z : T × T, κ z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  have hmp := q08e_mp_pair μ (N := N) i
  have h := integral_map (μ := μ.prod (Measure.pi fun _ : Fin N => μ)) hmp.measurable.aemeasurable
    (f := fun z : T × T => κ z.1 z.2 ^ 2)
    ((hm.pow_const 2).aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h.symm

theorem q08e_S_second (N : ℕ) :
    ∫ p : T × (Fin N → T), (∑ i, κ (p.2 i) p.1) ^ 2 ∂(μ.prod (Measure.pi fun _ : Fin N => μ)) =
      N * ∫ z : T × T, κ z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  have hint : ∀ i i' : Fin N, Integrable (fun p : T × (Fin N → T) => κ (p.2 i) p.1 * κ (p.2 i') p.1)
      (μ.prod (Measure.pi fun _ : Fin N => μ)) := fun i i' =>
    (q08e_memLp_f μ κ hκ i).integrable_mul (q08e_memLp_f μ κ hκ i')
  have e : ∀ p : T × (Fin N → T), (∑ i, κ (p.2 i) p.1) ^ 2 =
      ∑ i, ∑ i', κ (p.2 i) p.1 * κ (p.2 i') p.1 := by
    intro p; rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ => hint i i']
  simp_rw [integral_finsetSum _ fun i' _ => hint _ i']
  have : ∀ i i' : Fin N, ∫ p : T × (Fin N → T), κ (p.2 i) p.1 * κ (p.2 i') p.1
      ∂(μ.prod (Measure.pi fun _ : Fin N => μ)) =
      if i = i' then ∫ z : T × T, κ z.1 z.2 ^ 2 ∂(μ.prod μ) else 0 := by
    intro i i'
    by_cases h : i = i'
    · subst h
      simp only [if_true, ← sq]
      exact q08e_diag μ κ hm hs hd hκ i
    · simp only [h, ite_false]
      exact q08e_orth μ κ hm hs hd hκ i i' h
  simp_rw [this]
  simp


theorem q08e_DS {N : ℕ} (D : (Fin N → T) → ℝ)
    (hD : MemLp D 2 (Measure.pi fun _ : Fin N => μ)) :
    ∫ p : T × (Fin N → T), D p.2 * ∑ i, κ (p.2 i) p.1
      ∂(μ.prod (Measure.pi fun _ : Fin N => μ)) = 0 := by
  have hD' : MemLp (fun p : T × (Fin N → T) => D p.2) 2 (μ.prod (Measure.pi fun _ : Fin N => μ)) :=
    hD.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := Measure.pi fun _ : Fin N => μ))
  have hint : ∀ i : Fin N, Integrable (fun p : T × (Fin N → T) => D p.2 * κ (p.2 i) p.1)
      (μ.prod (Measure.pi fun _ : Fin N => μ)) := fun i =>
    hD'.integrable_mul (q08e_memLp_f μ κ hκ i)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_prod_symm _ (hint i)]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun Y => ?_)
  show ∫ y, D Y * κ (Y i) y ∂μ = 0
  rw [integral_const_mul, hd, mul_zero]


theorem q08e_DD_second (N : ℕ) :
    MemLp (q08e_DD κ : (Fin N → T) → ℝ) 2 (Measure.pi fun _ : Fin N => μ) ∧
      ∫ X : Fin N → T, (q08e_DD κ X) ^ 2 ∂(Measure.pi fun _ : Fin N => μ) =
        2 * N * (N - 1) * ∫ z : T × T, κ z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  induction N with
  | zero =>
    have h0 : (q08e_DD κ : (Fin 0 → T) → ℝ) = fun _ => 0 := by
      funext X; simp [q08e_DD]
    rw [h0]
    refine ⟨MemLp.zero' , ?_⟩
    simp
  | succ N ih =>
    obtain ⟨hD2, hDint⟩ := ih
    set πN : Measure (Fin N → T) := Measure.pi fun _ : Fin N => μ with hπN
    set ν : Measure (T × (Fin N → T)) := μ.prod πN with hν
    have hp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => T) (Fin.last N))
        (Measure.pi fun _ : Fin (N + 1) => μ) ν := by
      simpa using measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) (Fin.last N)
    set F : T × (Fin N → T) → ℝ := fun p => q08e_DD κ p.2 + 2 * ∑ i, κ (p.2 i) p.1 with hF
    have hFe : ∀ X : Fin (N + 1) → T, q08e_DD κ X =
        F (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => T) (Fin.last N) X) := by
      intro X
      rw [q08e_DD_succ κ hs X]
      show _ = F (X (Fin.last N), fun j => X ((Fin.last N).succAbove j))
      simp only [hF, Fin.succAbove_last]
    have hD' : MemLp (fun p : T × (Fin N → T) => q08e_DD κ p.2) 2 ν :=
      hD2.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := πN))
    have hS : MemLp (fun p : T × (Fin N → T) => ∑ i, κ (p.2 i) p.1) 2 ν :=
      memLp_finsetSum (Finset.univ) (fun i _ => q08e_memLp_f μ κ hκ i)
    have hFm : MemLp F 2 ν := hD'.add (hS.const_mul 2)
    have hDD : (q08e_DD κ : (Fin (N + 1) → T) → ℝ) = F ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => T) (Fin.last N)) :=
      funext hFe
    refine ⟨?_, ?_⟩
    · rw [hDD]
      exact hFm.comp_measurePreserving hp
    · have e1 : ∫ X : Fin (N + 1) → T, (q08e_DD κ X) ^ 2 ∂(Measure.pi fun _ : Fin (N + 1) => μ) =
          ∫ p, F p ^ 2 ∂ν := by
        have := hp.integral_comp' (g := fun p => F p ^ 2)
        rw [← this]
        refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
        simp only [hFe X]
      rw [e1]
      have hi1 : Integrable (fun p : T × (Fin N → T) => q08e_DD κ p.2 ^ 2) ν := hD'.integrable_sq
      have hi2 : Integrable (fun p : T × (Fin N → T) => q08e_DD κ p.2 *
          ∑ i, κ (p.2 i) p.1) ν := hD'.integrable_mul hS
      have hi3 : Integrable (fun p : T × (Fin N → T) => (∑ i, κ (p.2 i) p.1) ^ 2) ν := hS.integrable_sq
      have e2 : ∀ p : T × (Fin N → T), F p ^ 2 = q08e_DD κ p.2 ^ 2 +
          4 * (q08e_DD κ p.2 * ∑ i, κ (p.2 i) p.1) + 4 * (∑ i, κ (p.2 i) p.1) ^ 2 := by
        intro p; simp only [hF]; ring
      simp_rw [e2]
      have h12 : Integrable (fun p : T × (Fin N → T) => q08e_DD κ p.2 ^ 2 +
          4 * (q08e_DD κ p.2 * ∑ i, κ (p.2 i) p.1)) ν := hi1.add (hi2.const_mul 4)
      rw [integral_add h12 (hi3.const_mul 4), integral_add hi1 (hi2.const_mul 4),
        integral_const_mul, integral_const_mul]
      rw [q08e_DS μ κ hm hs hd hκ (q08e_DD κ) hD2, q08e_S_second μ κ hm hs hd hκ N]
      have e3 : ∫ p : T × (Fin N → T), q08e_DD κ p.2 ^ 2 ∂ν = ∫ Y, q08e_DD κ Y ^ 2 ∂πN := by
        have h := integral_map (μ := ν) (measurePreserving_snd (μ := μ) (ν := πN)).measurable.aemeasurable
          (f := fun Y : Fin N → T => q08e_DD κ Y ^ 2)
          (((q08e_DD_meas κ hm).pow_const 2).aestronglyMeasurable)
        rw [(measurePreserving_snd (μ := μ) (ν := πN)).map_eq] at h
        exact h.symm
      rw [e3, hDint]
      push_cast
      ring

end Orth


section Lin

variable (μ : Measure T) [IsProbabilityMeasure μ]

theorem q08e_lin_second (ℓ : T → ℝ) (hℓ : Measurable ℓ) (h2 : MemLp ℓ 2 μ) (h0 : ∫ x, ℓ x ∂μ = 0)
    (N : ℕ) :
    MemLp (fun X : Fin N → T => ∑ i, ℓ (X i)) 2 (Measure.pi fun _ : Fin N => μ) ∧
      ∫ X : Fin N → T, (∑ i, ℓ (X i)) ^ 2 ∂(Measure.pi fun _ : Fin N => μ) =
        N * ∫ x, ℓ x ^ 2 ∂μ := by
  have hX : ∀ k : Fin N, MemLp (fun X : Fin N → T => ℓ (X k)) 2 (Measure.pi fun _ : Fin N => μ) :=
    fun k => h2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) k)
  have hcoord : ∀ (g : T → ℝ), Measurable g → ∀ k : Fin N,
      ∫ X : Fin N → T, g (X k) ∂(Measure.pi fun _ : Fin N => μ) = ∫ x, g x ∂μ := by
    intro g hg k
    have h := measurePreserving_eval (fun _ : Fin N => μ) k
    rw [← integral_map h.measurable.aemeasurable hg.aestronglyMeasurable, h.map_eq]
  have hS : MemLp (fun X : Fin N → T => ∑ i, ℓ (X i)) 2 (Measure.pi fun _ : Fin N => μ) :=
    memLp_finsetSum (Finset.univ) (fun k _ => hX k)
  refine ⟨hS, ?_⟩
  have hmean : ∫ X : Fin N → T, ∑ i, ℓ (X i) ∂(Measure.pi fun _ : Fin N => μ) = 0 := by
    rw [integral_finsetSum _ (fun k _ => (hX k).integrable one_le_two)]
    simp only [hcoord ℓ hℓ, h0, Finset.sum_const_zero]
  have hvar := variance_of_integral_eq_zero hS.aemeasurable hmean
  have hind : Set.Pairwise (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)) fun i j =>
      IndepFun (fun X : Fin N → T => ℓ (X i)) (fun X : Fin N → T => ℓ (X j))
        (Measure.pi fun _ : Fin N => μ) := by
    intro i _ j _ hij
    exact (iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ (x : T) => ℓ x)
      (fun _ => hℓ.aemeasurable)).indepFun hij
  have hv := IndepFun.variance_sum (X := fun k (X : Fin N → T) => ℓ (X k)) (s := Finset.univ)
    (fun k _ => hX k) hind
  have e : (∑ k ∈ (Finset.univ : Finset (Fin N)), fun X : Fin N → T => ℓ (X k)) =
      fun X => ∑ k, ℓ (X k) := by
    ext X; simp [Finset.sum_apply]
  rw [e] at hv
  rw [← hvar, hv]
  have hk : ∀ k : Fin N, variance (fun X : Fin N → T => ℓ (X k)) (Measure.pi fun _ : Fin N => μ) =
      ∫ x, ℓ x ^ 2 ∂μ := by
    intro k
    rw [variance_of_integral_eq_zero (hX k).aemeasurable (by rw [hcoord ℓ hℓ k, h0])]
    exact hcoord (fun x => ℓ x ^ 2) (hℓ.pow_const 2) k
  simp [hk]

end Lin


section Analytic

variable (μ : Measure T) [IsProbabilityMeasure μ] (k : T → T → ℝ)
  (hm : Measurable (Function.uncurry k)) (hk : Integrable (fun z : T × T => k z.1 z.2 ^ 2) (μ.prod μ))

include hm hk

theorem q08e_k_memLp : MemLp (Function.uncurry k) 2 (μ.prod μ) :=
  (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hk

theorem q08e_a_meas : Measurable (fun x => ∫ y, k x y ∂μ) :=
  (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem q08e_a_integrable : Integrable (fun x => ∫ y, k x y ∂μ) μ :=
  (q08e_k_memLp μ k hm hk).integrable one_le_two |>.integral_prod_left

theorem q08e_a_memLp : MemLp (fun x => ∫ y, k x y ∂μ) 2 μ ∧
    ∫ x, (∫ y, k x y ∂μ) ^ 2 ∂μ ≤ ∫ z : T × T, k z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  have hm2 : Measurable (fun z : T × T => k z.1 z.2 ^ 2) := (hm.pow_const 2 : _)
  obtain ⟨hrow, hb⟩ := (integrable_prod_iff hm2.aestronglyMeasurable).1 hk
  have ham := q08e_a_meas μ k hm hk
  -- pointwise Cauchy-Schwarz for rows in L²
  have hcs : ∀ᵐ x ∂μ, (∫ y, k x y ∂μ) ^ 2 ≤ ∫ y, k x y ^ 2 ∂μ := by
    filter_upwards [hrow] with x hx
    have hrm : Measurable (fun y => k x y) := hm.comp (measurable_const.prodMk measurable_id)
    have hmem : MemLp (fun y => k x y) 2 μ := (memLp_two_iff_integrable_sq hrm.aestronglyMeasurable).2 hx
    have := variance_nonneg (fun y => k x y) μ
    rw [variance_eq_sub hmem] at this
    simp only [Pi.pow_apply] at this
    linarith
  have hb' : Integrable (fun x => ∫ y, k x y ^ 2 ∂μ) μ := by
    refine hb.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact abs_of_nonneg (sq_nonneg _)
  have hai : Integrable (fun x => (∫ y, k x y ∂μ) ^ 2) μ := by
    refine Integrable.mono' hb' (ham.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hcs] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  refine ⟨(memLp_two_iff_integrable_sq ham.aestronglyMeasurable).2 hai, ?_⟩
  rw [integral_prod _ hk]
  exact integral_mono_ae hai hb' hcs


end Analytic

/-- Row integral `a(x) = ∫ k(x, y) dμ(y)`. -/
def q08e_a (μ : Measure T) (k : T → T → ℝ) (x : T) : ℝ := ∫ y, k x y ∂μ

/-- The mean `m = ∬ k`. -/
def q08e_m (μ : Measure T) (k : T → T → ℝ) : ℝ := ∫ x, q08e_a μ k x ∂μ

/-- The degenerate (Hoeffding) part of `k`. -/
def q08e_kt (μ : Measure T) (k : T → T → ℝ) (x y : T) : ℝ :=
  k x y - q08e_a μ k x - q08e_a μ k y + q08e_m μ k

section Kt

variable (μ : Measure T) [IsProbabilityMeasure μ] (k : T → T → ℝ)
  (hm : Measurable (Function.uncurry k)) (hs : ∀ x y, k x y = k y x)
  (hk : Integrable (fun z : T × T => k z.1 z.2 ^ 2) (μ.prod μ))

include hm hk

theorem q08e_a_meas' : Measurable (q08e_a μ k) := q08e_a_meas μ k hm hk

theorem q08e_a_int' : Integrable (q08e_a μ k) μ := q08e_a_integrable μ k hm hk

theorem q08e_kt_meas : Measurable (Function.uncurry (q08e_kt μ k)) := by
  have ha := q08e_a_meas' μ k hm hk
  unfold q08e_kt
  have h1 : Measurable (fun z : T × T => q08e_a μ k z.1) := ha.comp measurable_fst
  have h2 : Measurable (fun z : T × T => q08e_a μ k z.2) := ha.comp measurable_snd
  exact (((hm.sub h1).sub h2).add measurable_const)

theorem q08e_a_pair_memLp :
    MemLp (fun z : T × T => q08e_a μ k z.1) 2 (μ.prod μ) ∧
      MemLp (fun z : T × T => q08e_a μ k z.2) 2 (μ.prod μ) := by
  have h := (q08e_a_memLp μ k hm hk).1
  exact ⟨h.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := μ)),
    h.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := μ))⟩

theorem q08e_kt_memLp : MemLp (Function.uncurry (q08e_kt μ k)) 2 (μ.prod μ) := by
  obtain ⟨h1, h2⟩ := q08e_a_pair_memLp μ k hm hk
  have hk2 := q08e_k_memLp μ k hm hk
  have : Function.uncurry (q08e_kt μ k) = fun z => (Function.uncurry k z - q08e_a μ k z.1) -
      q08e_a μ k z.2 + q08e_m μ k := by
    funext z; rfl
  rw [this]
  exact ((hk2.sub h1).sub h2).add (memLp_const _)

theorem q08e_kt_degenerate (x : T) : ∫ y, q08e_kt μ k x y ∂μ = 0 := by
  have ha := q08e_a_int' μ k hm hk
  have hdecomp : ∀ y, q08e_kt μ k x y = k x y + (q08e_m μ k - q08e_a μ k x) - q08e_a μ k y := by
    intro y; unfold q08e_kt; ring
  by_cases hx : Integrable (fun y => k x y) μ
  · simp_rw [hdecomp]
    have h1 : Integrable (fun y => k x y + (q08e_m μ k - q08e_a μ k x)) μ :=
      hx.add (integrable_const _)
    rw [integral_sub h1 ha, integral_add hx (integrable_const _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have : ∫ y, q08e_a μ k y ∂μ = q08e_m μ k := rfl
    rw [this]
    have : ∫ y, k x y ∂μ = q08e_a μ k x := rfl
    rw [this]
    ring
  · apply integral_undef
    intro hint
    apply hx
    have h2 : Integrable (fun y => q08e_kt μ k x y - (q08e_m μ k - q08e_a μ k x) + q08e_a μ k y) μ :=
      (hint.sub (integrable_const _)).add ha
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hdecomp]
    ring


omit hm hk in
theorem q08e_kt_symm (hs : ∀ x y, k x y = k y x) (x y : T) : q08e_kt μ k x y = q08e_kt μ k y x := by
  unfold q08e_kt; rw [hs x y]; ring

theorem q08e_kt_norm_le (hs : ∀ x y, k x y = k y x) :
    ∫ z : T × T, q08e_kt μ k z.1 z.2 ^ 2 ∂(μ.prod μ) ≤ ∫ z : T × T, k z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  obtain ⟨h1, h2⟩ := q08e_a_pair_memLp μ k hm hk
  have hkt2 := q08e_kt_memLp μ k hm hk
  have hktm := q08e_kt_meas μ k hm hk
  have hφ : MemLp (fun z : T × T => q08e_a μ k z.1 + q08e_a μ k z.2 - q08e_m μ k) 2 (μ.prod μ) :=
    (h1.add h2).sub (memLp_const _)
  have hkt2' : MemLp (fun z : T × T => q08e_kt μ k z.1 z.2) 2 (μ.prod μ) := hkt2
  have hktint : Integrable (fun z : T × T => q08e_kt μ k z.1 z.2) (μ.prod μ) :=
    hkt2'.integrable one_le_two
  have hi1 : Integrable (fun z : T × T => q08e_kt μ k z.1 z.2 ^ 2) (μ.prod μ) := hkt2'.integrable_sq
  have hi3 : Integrable (fun z : T × T => (q08e_a μ k z.1 + q08e_a μ k z.2 - q08e_m μ k) ^ 2)
      (μ.prod μ) := hφ.integrable_sq
  have hi2 : Integrable (fun z : T × T => q08e_kt μ k z.1 z.2 *
      (q08e_a μ k z.1 + q08e_a μ k z.2 - q08e_m μ k)) (μ.prod μ) := hkt2'.integrable_mul hφ
  have hia1 : Integrable (fun z : T × T => q08e_kt μ k z.1 z.2 * q08e_a μ k z.1) (μ.prod μ) :=
    hkt2'.integrable_mul h1
  have hia2 : Integrable (fun z : T × T => q08e_kt μ k z.1 z.2 * q08e_a μ k z.2) (μ.prod μ) :=
    hkt2'.integrable_mul h2
  -- the cross term vanishes
  have hc1 : ∫ z : T × T, q08e_kt μ k z.1 z.2 * q08e_a μ k z.1 ∂(μ.prod μ) = 0 := by
    rw [integral_prod _ hia1]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    show ∫ y, q08e_kt μ k x y * q08e_a μ k x ∂μ = 0
    rw [integral_mul_const, q08e_kt_degenerate μ k hm hk x, zero_mul]
  have hc2 : ∫ z : T × T, q08e_kt μ k z.1 z.2 * q08e_a μ k z.2 ∂(μ.prod μ) = 0 := by
    rw [integral_prod_symm _ hia2]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    show ∫ x, q08e_kt μ k x y * q08e_a μ k y ∂μ = 0
    rw [integral_mul_const]
    have : ∫ x, q08e_kt μ k x y ∂μ = 0 := by
      simp_rw [q08e_kt_symm μ k hs _ y]
      exact q08e_kt_degenerate μ k hm hk y
    rw [this, zero_mul]
  have hc3 : ∫ z : T × T, q08e_kt μ k z.1 z.2 ∂(μ.prod μ) = 0 := by
    rw [integral_prod _ hktint]
    simp_rw [q08e_kt_degenerate μ k hm hk]
    simp
  have hcross : ∫ z : T × T, q08e_kt μ k z.1 z.2 *
      (q08e_a μ k z.1 + q08e_a μ k z.2 - q08e_m μ k) ∂(μ.prod μ) = 0 := by
    have e : ∀ z : T × T, q08e_kt μ k z.1 z.2 * (q08e_a μ k z.1 + q08e_a μ k z.2 - q08e_m μ k) =
        q08e_kt μ k z.1 z.2 * q08e_a μ k z.1 + q08e_kt μ k z.1 z.2 * q08e_a μ k z.2 -
          q08e_m μ k * q08e_kt μ k z.1 z.2 := fun z => by ring
    simp_rw [e]
    have hsum : Integrable (fun z : T × T => q08e_kt μ k z.1 z.2 * q08e_a μ k z.1 +
        q08e_kt μ k z.1 z.2 * q08e_a μ k z.2) (μ.prod μ) := hia1.add hia2
    rw [integral_sub hsum (hktint.const_mul (q08e_m μ k)), integral_add hia1 hia2, hc1, hc2,
      integral_const_mul, hc3]
    simp
  have hsplit : ∀ z : T × T, k z.1 z.2 ^ 2 = q08e_kt μ k z.1 z.2 ^ 2 +
      2 * (q08e_kt μ k z.1 z.2 * (q08e_a μ k z.1 + q08e_a μ k z.2 - q08e_m μ k)) +
      (q08e_a μ k z.1 + q08e_a μ k z.2 - q08e_m μ k) ^ 2 := by
    intro z; unfold q08e_kt; ring
  simp_rw [hsplit]
  have hsum2 : Integrable (fun z : T × T => q08e_kt μ k z.1 z.2 ^ 2 +
      2 * (q08e_kt μ k z.1 z.2 * (q08e_a μ k z.1 + q08e_a μ k z.2 - q08e_m μ k))) (μ.prod μ) :=
    hi1.add (hi2.const_mul 2)
  rw [integral_add hsum2 hi3, integral_add hi1 (hi2.const_mul 2), integral_const_mul, hcross]
  have : 0 ≤ ∫ z : T × T, (q08e_a μ k z.1 + q08e_a μ k z.2 - q08e_m μ k) ^ 2 ∂(μ.prod μ) :=
    integral_nonneg fun z => sq_nonneg _
  linarith


theorem q08e_ell_facts :
    MemLp (fun x => q08e_a μ k x - q08e_m μ k) 2 μ ∧ ∫ x, (q08e_a μ k x - q08e_m μ k) ∂μ = 0 ∧
      ∫ x, (q08e_a μ k x - q08e_m μ k) ^ 2 ∂μ ≤ ∫ z : T × T, k z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  obtain ⟨hmem, hle⟩ := q08e_a_memLp μ k hm hk
  have ha := q08e_a_int' μ k hm hk
  have hmem' : MemLp (q08e_a μ k) 2 μ := hmem
  refine ⟨hmem'.sub (memLp_const _), ?_, ?_⟩
  · rw [integral_sub ha (integrable_const _)]
    simp [q08e_m]
  · have hvar := variance_le_expectation_sq (μ := μ) hmem'.aestronglyMeasurable
    rw [variance_eq_integral hmem'.aemeasurable] at hvar
    have e : μ[q08e_a μ k] = q08e_m μ k := rfl
    rw [e] at hvar
    refine hvar.trans ?_
    simpa [q08e_a, Pi.pow_apply] using hle

omit hm hk in
theorem q08e_ite_sum {N : ℕ} (c : ℝ) (i : Fin N) :
    ∑ j : Fin N, (if i = j then (0 : ℝ) else c) = ((N : ℝ) - 1) * c := by
  have e : ∀ j : Fin N, (if i = j then (0 : ℝ) else c) = c - (if i = j then c else 0) := by
    intro j; by_cases h : i = j <;> simp [h]
  simp_rw [e]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq]
  simp
  ring

omit hm hk in
theorem q08e_DD_kt {N : ℕ} (X : Fin N → T) :
    q08e_DD (q08e_kt μ k) X = q08e_DD k X - 2 * ((N : ℝ) - 1) * ∑ i, q08e_a μ k (X i) +
      N * ((N : ℝ) - 1) * q08e_m μ k := by
  unfold q08e_DD q08e_kt
  have e : ∀ i j : Fin N, (if i = j then (0 : ℝ) else k (X i) (X j) - q08e_a μ k (X i) -
      q08e_a μ k (X j) + q08e_m μ k) =
      (if i = j then 0 else k (X i) (X j)) - (if i = j then 0 else q08e_a μ k (X i)) -
        (if i = j then 0 else q08e_a μ k (X j)) + (if i = j then 0 else q08e_m μ k) := by
    intro i j; by_cases h : i = j <;> simp [h]
  simp_rw [e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h2 : ∑ i : Fin N, ∑ j : Fin N, (if i = j then (0 : ℝ) else q08e_a μ k (X j)) =
      ((N : ℝ) - 1) * ∑ j, q08e_a μ k (X j) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← q08e_ite_sum (N := N) (q08e_a μ k (X j)) j]
    exact Finset.sum_congr rfl fun i _ => if_congr eq_comm rfl rfl
  have h1 : ∑ i : Fin N, ∑ j : Fin N, (if i = j then (0 : ℝ) else q08e_a μ k (X i)) =
      ((N : ℝ) - 1) * ∑ i, q08e_a μ k (X i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => q08e_ite_sum _ i
  have h3 : ∑ i : Fin N, ∑ j : Fin N, (if i = j then (0 : ℝ) else q08e_m μ k) =
      N * (((N : ℝ) - 1) * q08e_m μ k) := by
    rw [Finset.sum_congr rfl fun i _ => q08e_ite_sum (q08e_m μ k) i]
    simp
  rw [h1, h2, h3]
  ring


omit hm hk in
theorem q08e_DD_erase {N : ℕ} (X : Fin N → T) :
    q08e_DD k X = ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j) := by
  unfold q08e_DD
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have e : ∀ j : Fin N, (if i = j then (0 : ℝ) else k (X i) (X j)) =
      k (X i) (X j) - (if i = j then k (X i) (X j) else 0) := by
    intro j; by_cases h : i = j <;> simp [h]
  simp_rw [e]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

/-- The centred energy `N F_N + ½ ∬ k`, expressed with the kernel `k`. -/
def q08e_Z (μ : Measure T) (k : T → T → ℝ) {N : ℕ} (X : Fin N → T) : ℝ :=
  (N : ℝ) * ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)
    - (1 / (N : ℝ)) * ∑ i, ∫ y, k (X i) y ∂μ + (1 / 2) * ∫ x, ∫ y, k x y ∂μ ∂μ) +
    (1 / 2) * ∫ x, ∫ y, k x y ∂μ ∂μ

omit hm hk in
theorem q08e_Z_eq {N : ℕ} (hN : 1 ≤ N) (X : Fin N → T) :
    q08e_Z μ k X = (1 / (2 * (N : ℝ))) * q08e_DD (q08e_kt μ k) X -
      (1 / (N : ℝ)) * ∑ i, (q08e_a μ k (X i) - q08e_m μ k) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [q08e_DD_kt, q08e_DD_erase]
  unfold q08e_Z
  have e1 : ∀ i, ∫ y, k (X i) y ∂μ = q08e_a μ k (X i) := fun i => rfl
  have e2 : ∫ x, ∫ y, k x y ∂μ ∂μ = q08e_m μ k := rfl
  simp_rw [e1, e2]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  field_simp
  ring


theorem q08e_main (hs : ∀ x y, k x y = k y x) {N : ℕ} (hN : 1 ≤ N) :
    ∫ X : Fin N → T, q08e_Z μ k X ^ 2 ∂(Measure.pi fun _ : Fin N => μ) ≤
      3 * ∫ z : T × T, k z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hDmem, hDint⟩ := q08e_DD_second μ (q08e_kt μ k) (q08e_kt_meas μ k hm hk)
    (q08e_kt_symm μ k hs) (q08e_kt_degenerate μ k hm hk) (q08e_kt_memLp μ k hm hk) N
  obtain ⟨hl2, hl0, hlle⟩ := q08e_ell_facts μ k hm hk
  have hlm : Measurable (fun x => q08e_a μ k x - q08e_m μ k) :=
    (q08e_a_meas' μ k hm hk).sub measurable_const
  obtain ⟨hLmem, hLint⟩ := q08e_lin_second μ (fun x => q08e_a μ k x - q08e_m μ k) hlm hl2 hl0 N
  have hqle := q08e_kt_norm_le μ k hm hk hs
  set q := ∫ z : T × T, q08e_kt μ k z.1 z.2 ^ 2 ∂(μ.prod μ) with hq
  set r := ∫ x, (q08e_a μ k x - q08e_m μ k) ^ 2 ∂μ with hr
  set Q := ∫ z : T × T, k z.1 z.2 ^ 2 ∂(μ.prod μ) with hQ
  have hq0 : 0 ≤ q := integral_nonneg fun z => sq_nonneg _
  have hr0 : 0 ≤ r := integral_nonneg fun z => sq_nonneg _
  set πN : Measure (Fin N → T) := Measure.pi fun _ : Fin N => μ with hπN
  have hA : MemLp (fun X : Fin N → T => (1 / (2 * (N : ℝ))) * q08e_DD (q08e_kt μ k) X) 2 πN :=
    hDmem.const_mul _
  have hB : MemLp (fun X : Fin N → T => (1 / (N : ℝ)) * ∑ i, (q08e_a μ k (X i) - q08e_m μ k)) 2 πN :=
    hLmem.const_mul _
  have hZ : ∀ X, q08e_Z μ k X = (1 / (2 * (N : ℝ))) * q08e_DD (q08e_kt μ k) X -
      (1 / (N : ℝ)) * ∑ i, (q08e_a μ k (X i) - q08e_m μ k) := fun X => q08e_Z_eq μ k hN X
  have hAi := hA.integrable_sq
  have hBi := hB.integrable_sq
  have hZi : Integrable (fun X : Fin N → T => (q08e_Z μ k X) ^ 2) πN := by
    have := (hA.sub hB).integrable_sq
    refine this.congr (Filter.Eventually.of_forall fun X => ?_)
    simp only [Pi.sub_apply, hZ]
  have hint2 : Integrable (fun X : Fin N → T => 2 * ((1 / (2 * (N : ℝ))) * q08e_DD (q08e_kt μ k) X) ^ 2 +
      2 * ((1 / (N : ℝ)) * ∑ i, (q08e_a μ k (X i) - q08e_m μ k)) ^ 2) πN :=
    (hAi.const_mul 2).add (hBi.const_mul 2)
  have h1 : ∫ X, q08e_Z μ k X ^ 2 ∂πN ≤ ∫ X : Fin N → T,
      (2 * ((1 / (2 * (N : ℝ))) * q08e_DD (q08e_kt μ k) X) ^ 2 +
        2 * ((1 / (N : ℝ)) * ∑ i, (q08e_a μ k (X i) - q08e_m μ k)) ^ 2) ∂πN := by
    refine integral_mono hZi hint2 fun X => ?_
    simp only [hZ]
    nlinarith [sq_nonneg ((1 / (2 * (N : ℝ))) * q08e_DD (q08e_kt μ k) X +
      (1 / (N : ℝ)) * ∑ i, (q08e_a μ k (X i) - q08e_m μ k))]
  refine h1.trans ?_
  rw [integral_add (hAi.const_mul 2) (hBi.const_mul 2), integral_const_mul, integral_const_mul]
  have eA : ∫ X : Fin N → T, ((1 / (2 * (N : ℝ))) * q08e_DD (q08e_kt μ k) X) ^ 2 ∂πN =
      (1 / (2 * (N : ℝ))) ^ 2 * (2 * N * (N - 1) * q) := by
    simp_rw [mul_pow]
    rw [integral_const_mul, hDint]
  have eB : ∫ X : Fin N → T, ((1 / (N : ℝ)) * ∑ i, (q08e_a μ k (X i) - q08e_m μ k)) ^ 2 ∂πN =
      (1 / (N : ℝ)) ^ 2 * (N * r) := by
    simp_rw [mul_pow]
    rw [integral_const_mul, hLint]
  rw [eA, eB]
  have key : 2 * ((1 / (2 * (N : ℝ))) ^ 2 * (2 * N * (N - 1) * q)) + 2 * ((1 / (N : ℝ)) ^ 2 * (N * r)) =
      ((N - 1) / N) * q + (2 / N) * r := by
    field_simp
  rw [key]
  have hr1 : (2 / (N : ℝ)) * r ≤ 2 * r := by
    have : 2 / (N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hN0]; have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    exact mul_le_mul_of_nonneg_right this hr0
  have hq1 : ((N - 1) / (N : ℝ)) * q ≤ q := by
    have : ((N : ℝ) - 1) / N ≤ 1 := by
      rw [div_le_one hN0]; linarith
    calc ((N - 1) / (N : ℝ)) * q ≤ 1 * q := mul_le_mul_of_nonneg_right this hq0
      _ = q := one_mul q
  linarith

end Kt

end DD

end HRS.Q08

end
