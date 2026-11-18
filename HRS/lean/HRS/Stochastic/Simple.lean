import HRS.Stochastic.Brownian

/-!
# Simple (elementary predictable) integrands and the elementary Itô integral

Package SI-01, part 2.  A simple integrand is a step process
`Φ_s = ∑_i 1_{(t_i, t_{i+1}]}(s) ξ_i` with `0 ≤ t_0 ≤ ⋯ ≤ t_n`, `ξ_i` bounded and
`ℱ_{t_i}`-measurable with values in `ι → ℝ`.  Its elementary integral against the `ι`-family of
Brownian motions `W` is
`I_t = ∑_i ∑_k ξ_i^k (W^k_{t_{i+1} ∧ t} - W^k_{t_i ∧ t})`
(which vanishes for `t ≤ t_0`, in particular for `t ≤ 0`).

Main statements: `I` is a continuous martingale (`martingale_elemIntegral`), the Itô isometry
`E[I_t²] = E ∫_0^t ∑_k |Φ^k_s|² ds` with vanishing cross terms between different coordinates
(`integral_elemIntegral_sq`, `integral_elemIntegral_mul`), the compensator martingale
`I_t² - ∫_0^t |Φ|²` (`martingale_elemIntegral_sq_sub`), and the density of simple integrands in the
progressive `L²` class (`exists_simple_approx`).

The `L²` size of an integrand over `[0, T]` is measured by `sqIntegralOn P Φ T = E ∫_0^T ∑_k |Φ^k|²`
as an `ℝ≥0∞`-valued lower integral (no integrability side conditions).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

/-- `E ∫_0^T ∑_k |Φ^k_s|² ds ∈ [0, ∞]`, the squared `L²(dt ⊗ P)`-norm of an integrand on `[0, T]`. -/
def sqIntegralOn (P : Measure Ω) (Φ : ℝ → Ω → ι → ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ∂P

theorem sqIntegralOn_mono (P : Measure Ω) (Φ : ℝ → Ω → ι → ℝ) {T T' : ℝ} (h : T ≤ T') :
    sqIntegralOn P Φ T ≤ sqIntegralOn P Φ T' := by
  unfold sqIntegralOn
  exact lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right h)

/-! ### Step-sum bookkeeping -/

/-- Finitely many weights with vanishing partial sums vanish. -/
theorem weights_eq_zero_of_partial_sums (w : ℝ → ℝ) :
    ∀ (S : Finset ℝ), (∀ r : ℝ, ∑ x ∈ S with x < r, w x = 0) → ∀ x ∈ S, w x = 0 := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m S hlt ih =>
    intro h
    have hm : m ∉ S := fun hm => lt_irrefl _ (hlt m hm)
    have hfilt : ∀ r, m < r → (insert m S).filter (· < r) = insert m S := by
      intro r hr
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hr
      · exact (hlt x hx).trans hr
    have hfilt' : ∀ r, m < r → S.filter (· < r) = S := by
      intro r hr
      apply Finset.filter_true_of_mem
      intro x hx
      exact (hlt x hx).trans hr
    have hS : ∑ x ∈ S, w x = 0 := by
      have := h m
      rw [Finset.filter_insert, if_neg (lt_irrefl m)] at this
      rwa [Finset.filter_true_of_mem (fun x hx => hlt x hx)] at this
    have hwm : w m = 0 := by
      have := h (m + 1)
      rw [hfilt _ (by linarith), Finset.sum_insert hm, hS] at this
      simpa using this
    have hS' : ∀ x ∈ S, w x = 0 := by
      apply ih
      intro r
      by_cases hr : m < r
      · rw [hfilt' r hr]; exact hS
      · have := h r
        rw [Finset.filter_insert, if_neg hr] at this
        exact this
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hwm
    · exact hS' x hx

/-- If a finite combination of half-open interval indicators vanishes identically, then the
corresponding combination of increments of any function `G` vanishes. -/
theorem stepSum_eq_zero {κ : Type*} [Fintype κ] (a b c : κ → ℝ) (G : ℝ → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (h : ∀ r : ℝ, ∑ i, (Set.Ioc (a i) (b i)).indicator (fun _ => c i) r = 0) :
    ∑ i, c i * (G (b i) - G (a i)) = 0 := by
  classical
  set S : Finset ℝ := Finset.univ.image a ∪ Finset.univ.image b with hS
  have haS : ∀ i, a i ∈ S := fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hbS : ∀ i, b i ∈ S := fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  set w : ℝ → ℝ := fun x => ∑ i, c i * ((if a i = x then 1 else 0) - (if b i = x then 1 else 0)) with hw
  have hpart : ∀ r : ℝ, ∑ x ∈ S with x < r, w x = 0 := by
    intro r
    have : ∑ x ∈ S with x < r, w x
        = ∑ i, c i * ((if a i < r then 1 else 0) - (if b i < r then 1 else 0)) := by
      simp only [hw]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
      congr 2
      · rw [Finset.sum_ite_eq]
        simp [haS i]
      · rw [Finset.sum_ite_eq]
        simp [hbS i]
    refine this.trans (Eq.trans ?_ (h r))
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := hab i
    by_cases h1 : a i < r <;> by_cases h2 : r ≤ b i
    · have h3 : ¬ b i < r := not_lt.2 h2
      simp [Set.indicator, h1, h2, h3]
    · have h3 : b i < r := not_le.1 h2
      simp [Set.indicator, h1, h2, h3]
    · have h3 : ¬ b i < r := by intro h3; exact h1 (lt_of_le_of_lt hi h3)
      simp [Set.indicator, h1, h3]
    · exfalso; linarith [not_lt.1 h1, not_le.1 h2]
  have hw0 := weights_eq_zero_of_partial_sums w S hpart
  have key : ∑ x ∈ S, w x * G x = ∑ i, c i * (G (a i) - G (b i)) := by
    simp only [hw, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : ∑ x ∈ S, c i * ((if a i = x then 1 else 0) - (if b i = x then 1 else 0)) * G x
        = c i * (∑ x ∈ S, if a i = x then G x else 0) - c i * (∑ x ∈ S, if b i = x then G x else 0) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> ring
    rw [e1, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (haS i), if_pos (hbS i)]
    ring
  have : ∑ i, c i * (G (a i) - G (b i)) = 0 := by
    rw [← key]; exact Finset.sum_eq_zero fun x hx => by rw [hw0 x hx, zero_mul]
  have h2 : ∑ i, c i * (G (b i) - G (a i)) = - ∑ i, c i * (G (a i) - G (b i)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2, this, neg_zero]

/-- A simple integrand: a partition `0 ≤ t_0 ≤ ⋯ ≤ t_n` and bounded `ℱ_{t_i}`-measurable values
`ξ_i : Ω → ι → ℝ` on `(t_i, t_{i+1}]`. -/
structure SimpleIntegrand (ℱ : Filtration ℝ mΩ) (ι : Type*) where
  /-- number of steps -/
  n : ℕ
  /-- the partition points -/
  t : Fin (n + 1) → ℝ
  mono : Monotone t
  nonneg : 0 ≤ t 0
  /-- the value on `(t_i, t_{i+1}]` -/
  ξ : Fin n → Ω → ι → ℝ
  meas : ∀ i, Measurable[ℱ (t i.castSucc)] (ξ i)
  bdd : ∃ C : ℝ, ∀ i ω k, |ξ i ω k| ≤ C

namespace SimpleIntegrand

variable {ℱ : Filtration ℝ mΩ}

/-- The step process `s ↦ ∑_i 1_{(t_i, t_{i+1}]}(s) ξ_i`. -/
def toFun (Ψ : SimpleIntegrand ℱ ι) : ℝ → Ω → ι → ℝ :=
  fun s ω => ∑ i : Fin Ψ.n, Set.indicator (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)) (fun _ => Ψ.ξ i ω) s

/-- The elementary integral `∑_i ∑_k ξ_i^k (W^k_{t_{i+1} ∧ t} - W^k_{t_i ∧ t})`. -/
def elemIntegral (W : ℝ≥0 → Ω → ι → ℝ) (Ψ : SimpleIntegrand ℱ ι) : ℝ → Ω → ℝ :=
  fun s ω => ∑ i : Fin Ψ.n, ∑ k, Ψ.ξ i ω k *
    (W (Real.toNNReal (min (Ψ.t i.succ) s)) ω k - W (Real.toNNReal (min (Ψ.t i.castSucc) s)) ω k)

theorem elemIntegral_of_le_first (W : ℝ≥0 → Ω → ι → ℝ) (Ψ : SimpleIntegrand ℱ ι) {s : ℝ}
    (hs : s ≤ Ψ.t 0) (ω : Ω) : elemIntegral W Ψ s ω = 0 := by
  unfold elemIntegral
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
  have h1 : min (Ψ.t i.succ) s = s := min_eq_right (hs.trans (Ψ.mono (Fin.zero_le _)))
  have h2 : min (Ψ.t i.castSucc) s = s := min_eq_right (hs.trans (Ψ.mono (Fin.zero_le _)))
  rw [h1, h2]; simp

theorem elemIntegral_of_nonpos (W : ℝ≥0 → Ω → ι → ℝ) (Ψ : SimpleIntegrand ℱ ι) {s : ℝ}
    (hs : s ≤ 0) (ω : Ω) : elemIntegral W Ψ s ω = 0 :=
  elemIntegral_of_le_first W Ψ (hs.trans Ψ.nonneg) ω

theorem toFun_apply (Ψ : SimpleIntegrand ℱ ι) (s : ℝ) (ω : Ω) (k : ι) :
    Ψ.toFun s ω k =
      ∑ i : Fin Ψ.n, (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator (fun _ => Ψ.ξ i ω k) s := by
  unfold toFun
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : s ∈ Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ) <;> simp [h]

theorem elemIntegral_eq_sum_comm (W : ℝ≥0 → Ω → ι → ℝ) (Ψ : SimpleIntegrand ℱ ι) (s : ℝ) (ω : Ω) :
    elemIntegral W Ψ s ω = ∑ k, ∑ i : Fin Ψ.n, Ψ.ξ i ω k *
      (W (Real.toNNReal (min (Ψ.t i.succ) s)) ω k - W (Real.toNNReal (min (Ψ.t i.castSucc) s)) ω k) :=
  Finset.sum_comm

/-- The elementary integral depends only on the step process. -/
theorem elemIntegral_congr (W : ℝ≥0 → Ω → ι → ℝ) (Ψ Ψ' : SimpleIntegrand ℱ ι)
    (h : Ψ.toFun = Ψ'.toFun) : elemIntegral W Ψ = elemIntegral W Ψ' := by
  funext s ω
  rw [elemIntegral_eq_sum_comm, elemIntegral_eq_sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  set G : ℝ → ℝ := fun x => W (Real.toNNReal (min x s)) ω k with hG
  have key := stepSum_eq_zero (κ := Fin Ψ.n ⊕ Fin Ψ'.n)
    (Sum.elim (fun i => Ψ.t i.castSucc) (fun i => Ψ'.t i.castSucc))
    (Sum.elim (fun i => Ψ.t i.succ) (fun i => Ψ'.t i.succ))
    (Sum.elim (fun i => Ψ.ξ i ω k) (fun i => - Ψ'.ξ i ω k)) G
    (by
      rintro (i | i)
      · exact Ψ.mono (Fin.castSucc_le_succ i)
      · exact Ψ'.mono (Fin.castSucc_le_succ i))
    (by
      intro r
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Set.indicator_neg, Finset.sum_neg_distrib]
      rw [← toFun_apply Ψ, ← toFun_apply Ψ', h]; ring)
  rw [Fintype.sum_sum_type] at key
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
  simp only [hG] at key
  linarith

theorem toFun_bdd (Ψ : SimpleIntegrand ℱ ι) : ∃ C : ℝ, ∀ s ω k, |Ψ.toFun s ω k| ≤ C := by
  obtain ⟨C, hC⟩ := Ψ.bdd
  refine ⟨Ψ.n * C, fun s ω k => ?_⟩
  rw [toFun_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i : Fin Ψ.n, |(Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator (fun _ => Ψ.ξ i ω k) s| ≤ C := by
    intro i
    by_cases h : s ∈ Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)
    · simpa [h] using hC i ω k
    · have := (abs_nonneg (Ψ.ξ i ω k)).trans (hC i ω k)
      simpa [h] using this
  refine (Finset.sum_le_sum fun i _ => this i).trans ?_
  simp

theorem isProgressive_toFun (Ψ : SimpleIntegrand ℱ ι) : IsProgressive ℱ Ψ.toFun := by
  intro t
  let mt : MeasurableSpace (Set.Iic t × Ω) := Subtype.instMeasurableSpace.prod (ℱ t)
  show Measurable (fun p : Set.Iic t × Ω => Ψ.toFun p.1 p.2)
  refine measurable_pi_iff.2 fun k => ?_
  have hk : ∀ p : Set.Iic t × Ω, Ψ.toFun p.1 p.2 k =
      ∑ i : Fin Ψ.n, (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator (fun _ => Ψ.ξ i p.2 k) p.1 :=
    fun p => toFun_apply Ψ _ _ k
  simp_rw [hk]
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases hit : Ψ.t i.castSucc ≤ t
  · have hmeas : Measurable[ℱ t] fun ω => Ψ.ξ i ω k :=
      (measurable_pi_apply k).comp ((Ψ.meas i).mono (ℱ.mono hit) le_rfl)
    have h1 : Measurable fun p : Set.Iic t × Ω => Ψ.ξ i p.2 k :=
      hmeas.comp (@measurable_snd _ _ Subtype.instMeasurableSpace (ℱ t))
    have h2 : MeasurableSet
        {p : Set.Iic t × Ω | (p.1 : ℝ) ∈ Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)} :=
      (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ t)) (measurable_subtype_coe measurableSet_Ioc)
    exact h1.indicator h2
  · have : ∀ p : Set.Iic t × Ω, (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator
        (fun _ => Ψ.ξ i p.2 k) p.1 = 0 := by
      intro p
      refine Set.indicator_of_notMem ?_ _
      intro hp
      exact hit (hp.1.le.trans p.1.2)
    simp_rw [this]
    exact measurable_const

theorem sqIntegralOn_toFun_lt_top (P : Measure Ω) [IsProbabilityMeasure P]
    (Ψ : SimpleIntegrand ℱ ι) (T : ℝ) : sqIntegralOn P Ψ.toFun T < ∞ := by
  obtain ⟨C, hC⟩ := toFun_bdd Ψ
  set B : ℝ≥0∞ := ∑ _k : ι, ENNReal.ofReal C ^ 2 with hB
  have hBt : B < ∞ := by
    rw [hB]
    exact ENNReal.sum_lt_top.2 fun _ _ => ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have hle : ∀ s ω, ∑ k, ‖Ψ.toFun s ω k‖ₑ ^ 2 ≤ B := by
    intro s ω
    refine Finset.sum_le_sum fun k _ => ?_
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hC s ω k)
  calc sqIntegralOn P Ψ.toFun T ≤ ∫⁻ _ω, (∫⁻ _s in Set.Icc 0 T, B) ∂P := by
        unfold sqIntegralOn
        exact lintegral_mono fun ω => lintegral_mono fun s => hle s ω
    _ < ∞ := by
        simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, measure_univ, mul_one]
        exact ENNReal.mul_lt_top hBt ENNReal.ofReal_lt_top

variable {P : Measure Ω} {W : ℝ≥0 → Ω → ι → ℝ}

theorem continuous_elemIntegral (hW : ∀ ω, Continuous fun t => W t ω) (Ψ : SimpleIntegrand ℱ ι)
    (ω : Ω) : Continuous fun s => elemIntegral W Ψ s ω := by
  unfold elemIntegral
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun k _ => ?_
  have hc : ∀ c : ℝ, Continuous fun s : ℝ => W (Real.toNNReal (min c s)) ω k := fun c =>
    (continuous_apply k).comp ((hW ω).comp (continuous_real_toNNReal.comp
      (continuous_const.min continuous_id)))
  exact continuous_const.mul ((hc _).sub (hc _))

theorem adapted_elemIntegral (hW : IsBrownianFiltration P ℱ W) (Ψ : SimpleIntegrand ℱ ι) :
    Adapted ℱ (elemIntegral W Ψ) := by
  intro s
  unfold elemIntegral
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  by_cases h : Ψ.t i.castSucc ≤ s
  · have hξ : Measurable[ℱ s] fun ω => Ψ.ξ i ω k :=
      (measurable_pi_apply k).comp ((Ψ.meas i).mono (ℱ.mono h) le_rfl)
    have hb : ∀ x ≤ s, Measurable[ℱ s] fun ω => W (Real.toNNReal x) ω k := fun x hx =>
      (measurable_pi_apply k).comp ((hW.adapted_ofNNRealTime x).mono (ℱ.mono hx) le_rfl)
    exact hξ.mul ((hb _ (min_le_right _ _)).sub (hb _ (min_le_right _ _)))
  · rw [not_le] at h
    have h1 : min (Ψ.t i.succ) s = s := min_eq_right (h.le.trans (Ψ.mono (Fin.castSucc_le_succ i)))
    have h2 : min (Ψ.t i.castSucc) s = s := min_eq_right h.le
    simp only [h1, h2, sub_self, mul_zero]
    exact measurable_const

theorem stronglyAdapted_elemIntegral (hW : IsBrownianFiltration P ℱ W)
    (Ψ : SimpleIntegrand ℱ ι) : StronglyAdapted ℱ (elemIntegral W Ψ) :=
  (adapted_elemIntegral hW Ψ).stronglyAdapted

/-- Coordinates of `W` are in `L^p`, `p < ∞`.  On the integration branch this is
`IsBrownianFiltration.memLp_coord hW t k hp`; in this worktree `Brownian.lean` still has the old
(`p = ∞`-inclusive) `memLp`, which is used here only for `p ≠ ∞`. -/
theorem memLp_coord_aux (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] (t : ℝ≥0)
    (k : ι) {p : ℝ≥0∞} (_hp : p ≠ ∞) : MemLp (fun ω => W t ω k) p P :=
  hW.memLp_coord t k _hp

/-- The elementary integral is in every `L^p`, `p < ∞`. -/
theorem memLp_elemIntegral (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (Ψ : SimpleIntegrand ℱ ι) (s : ℝ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (elemIntegral W Ψ s) p P := by
  obtain ⟨C, hC⟩ := Ψ.bdd
  unfold elemIntegral
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun k _ => ?_
  have hξ : MemLp (fun ω => Ψ.ξ i ω k) ∞ P :=
    memLp_top_of_bound (((measurable_pi_apply k).comp ((Ψ.meas i).mono (ℱ.le _) le_rfl)).aestronglyMeasurable)
      C (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC i ω k)
  exact hξ.fun_mul (((memLp_coord_aux hW _ k hp).sub (memLp_coord_aux hW _ k hp)))

/-! ### Martingale bookkeeping -/

/-- A martingale stopped at a deterministic time is a martingale. -/
theorem martingale_stopAt [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ} (hX : Martingale X ℱ P)
    (c : ℝ) : Martingale (fun s => X (min c s)) ℱ P := by
  refine ⟨fun s => (hX.stronglyAdapted (min c s)).mono (ℱ.mono (min_le_right c s)),
    fun s t hst => ?_⟩
  by_cases hcs : c ≤ s
  · have e1 : min c s = c := min_eq_left hcs
    have e2 : min c t = c := min_eq_left (hcs.trans hst)
    simp only [e1, e2]
    rw [condExp_of_stronglyMeasurable (ℱ.le s) ((hX.stronglyAdapted c).mono (ℱ.mono hcs))
      (hX.integrable c)]
  · rw [not_le] at hcs
    have e1 : min c s = s := min_eq_right hcs.le
    simp only [e1]
    exact hX.condExp_ae_eq (le_min hcs.le hst)

/-- If `Y` is a martingale vanishing up to time `a` and `ξ` is `ℱ a`-measurable with `ξ Y_s`
integrable, then `ξ Y` is a martingale. -/
theorem martingale_mul_left [IsProbabilityMeasure P] {Y : ℝ → Ω → ℝ} (hY : Martingale Y ℱ P)
    {a : ℝ} (h0 : ∀ s ≤ a, Y s = 0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ a] ξ)
    (hint : ∀ s, Integrable (fun ω => ξ ω * Y s ω) P) :
    Martingale (fun s ω => ξ ω * Y s ω) ℱ P := by
  refine ⟨fun s => ?_, fun s t hst => ?_⟩
  · by_cases h : a ≤ s
    · exact (hξ.mono (ℱ.mono h)).mul (hY.stronglyAdapted s)
    · have : ∀ ω, Y s ω = 0 := fun ω => congrFun (h0 s (not_le.1 h).le) ω
      simp only [this, mul_zero]
      exact stronglyMeasurable_const
  · by_cases h : a ≤ s
    · have key := condExp_mul_of_stronglyMeasurable_left (m := ℱ s) (μ := P)
        (hξ.mono (ℱ.mono h)) (hint t) (hY.integrable t)
      refine key.trans ?_
      filter_upwards [hY.condExp_ae_eq hst] with ω hω
      simp [hω]
    · rw [not_le] at h
      have hYs : ∀ ω, Y s ω = 0 := fun ω => congrFun (h0 s h.le) ω
      by_cases ht : t ≤ a
      · have hYt : ∀ ω, Y t ω = 0 := fun ω => congrFun (h0 t ht) ω
        simp only [hYt, hYs, mul_zero]
        rw [condExp_const (ℱ.le s)]
      · rw [not_le] at ht
        have h1 : P[fun ω => ξ ω * Y t ω | ℱ a] =ᵐ[P] fun ω => ξ ω * Y a ω := by
          have key := condExp_mul_of_stronglyMeasurable_left (m := ℱ a) (μ := P)
            hξ (hint t) (hY.integrable t)
          refine key.trans ?_
          filter_upwards [hY.condExp_ae_eq ht.le] with ω hω
          simp [hω]
        have h2 := condExp_condExp_of_le (μ := P) (f := fun ω => ξ ω * Y t ω)
          (ℱ.mono h.le) (ℱ.le a)
        have h3 : P[P[fun ω => ξ ω * Y t ω | ℱ a] | ℱ s] =ᵐ[P] P[fun ω => ξ ω * Y a ω | ℱ s] :=
          condExp_congr_ae h1
        have hYa : ∀ ω, Y a ω = 0 := fun ω => congrFun (h0 a le_rfl) ω
        simp only [hYa, mul_zero] at h3
        simp only [hYs, mul_zero]
        rw [condExp_const (ℱ.le s)] at h3
        exact h2.symm.trans h3

/-- Finite sums of martingales are martingales. -/
theorem martingale_finset_sum [IsProbabilityMeasure P] {κ : Type*} (S : Finset κ)
    {f : κ → ℝ → Ω → ℝ} (h : ∀ q ∈ S, Martingale (f q) ℱ P) :
    Martingale (fun s ω => ∑ q ∈ S, f q s ω) ℱ P := by
  classical
  induction S using Finset.induction_on with
  | empty => exact martingale_zero ℝ ℱ P
  | insert q S hq ih =>
    have := (h q (Finset.mem_insert_self _ _)).add
      (ih fun q' hq' => h q' (Finset.mem_insert_of_mem hq'))
    have e : (fun s ω => ∑ q' ∈ insert q S, f q' s ω) = f q + fun s ω => ∑ q ∈ S, f q s ω := by
      funext s ω; simp [Finset.sum_insert hq]
    rw [e]; exact this

/-! ### Compensator bookkeeping for pairs of steps -/

/-- `max (min (min c d) s) 0 = ∫_{[0,s]} 1_{(0,c]} 1_{(0,d]}`. -/
def gOv (c d s : ℝ) : ℝ := max (min (min c d) s) 0

/-- `∫_{[0,s]} 1_{(a,b]} 1_{(a',b']}` for `0 ≤ a ≤ b`, `0 ≤ a' ≤ b'`. -/
def stepLam (a b a' b' s : ℝ) : ℝ := gOv b b' s - gOv b a' s - gOv a b' s + gOv a a' s

/-- The compensated product of two stopped coordinates is a martingale (basic case). -/
theorem martingale_prod_base [DecidableEq ι] (hW : IsBrownianFiltration P ℱ W)
    [IsProbabilityMeasure P] (k l : ι) :
    Martingale (fun (s : ℝ) ω => ofNNRealTime W s ω k * ofNNRealTime W s ω l -
      (if k = l then max s 0 else 0)) ℱ P := by
  by_cases hkl : k = l
  · subst hkl
    simpa [sq] using hW.martingale_sq_sub k
  · simpa [hkl] using hW.martingale_mul hkl

theorem martingale_stop_prod_le [DecidableEq ι] (hW : IsBrownianFiltration P ℱ W)
    [IsProbabilityMeasure P] (k l : ι) {c d : ℝ} (hcd : c ≤ d) :
    Martingale (fun (s : ℝ) ω => ofNNRealTime W (min c s) ω k * ofNNRealTime W (min d s) ω l -
      (if k = l then gOv c d s else 0)) ℱ P := by
  have h1 := martingale_stopAt (martingale_prod_base hW k l) c
  have hMl := hW.martingale l
  have hN : Martingale (fun (s : ℝ) ω => ofNNRealTime W (min d s) ω l -
      ofNNRealTime W (min c s) ω l) ℱ P :=
    (martingale_stopAt hMl d).sub (martingale_stopAt hMl c)
  have hξ : StronglyMeasurable[ℱ c] fun ω => ofNNRealTime W c ω k :=
    (((measurable_pi_apply k).comp (hW.adapted_ofNNRealTime c)).stronglyMeasurable)
  have hint : ∀ s, Integrable (fun ω => ofNNRealTime W c ω k *
      (ofNNRealTime W (min d s) ω l - ofNNRealTime W (min c s) ω l)) P := by
    intro s
    have h2 : MemLp (fun ω => ofNNRealTime W c ω k) 2 P := memLp_coord_aux hW _ k (by norm_num)
    have h3 : MemLp (fun ω => ofNNRealTime W (min d s) ω l -
        ofNNRealTime W (min c s) ω l) 2 P := (memLp_coord_aux hW _ l (by norm_num)).sub (memLp_coord_aux hW _ l (by norm_num))
    exact h2.integrable_mul h3
  have h2 := martingale_mul_left hN (a := c) (fun s hs => by
      funext ω
      simp [min_eq_right hs, min_eq_right (hs.trans hcd)]) hξ hint
  have h3 := h1.add h2
  convert h3 using 1
  funext s ω
  simp only [Pi.add_apply]
  rcases le_or_gt c s with h | h
  · simp only [min_eq_left h, gOv, min_eq_left hcd]
    ring
  · simp only [min_eq_right h.le, min_eq_right (h.le.trans hcd), gOv, min_eq_left hcd]
    ring

theorem martingale_stop_prod [DecidableEq ι] (hW : IsBrownianFiltration P ℱ W)
    [IsProbabilityMeasure P] (k l : ι) (c d : ℝ) :
    Martingale (fun (s : ℝ) ω => ofNNRealTime W (min c s) ω k * ofNNRealTime W (min d s) ω l -
      (if k = l then gOv c d s else 0)) ℱ P := by
  rcases le_total c d with h | h
  · exact martingale_stop_prod_le hW k l h
  · have := martingale_stop_prod_le hW l k h
    convert this using 1
    funext s ω
    simp only [gOv, min_comm c d, eq_comm (a := k) (b := l)]
    ring

omit [Fintype ι] in
theorem gOv_eq_left {c c' d s : ℝ} (h1 : s ≤ c) (h2 : s ≤ c') : gOv c d s = gOv c' d s := by
  have : ∀ c' : ℝ, s ≤ c' → min (min c' d) s = min d s := fun c' h => by
    rw [min_comm c' d, min_assoc, min_eq_right h]
  unfold gOv
  rw [this c h1, this c' h2]

omit [Fintype ι] in
theorem gOv_eq_right {c d d' s : ℝ} (h1 : s ≤ d) (h2 : s ≤ d') : gOv c d s = gOv c d' s := by
  have : ∀ d' : ℝ, s ≤ d' → min (min c d') s = min c s := fun d' h => by
    rw [min_assoc, min_eq_right h]
  unfold gOv
  rw [this d h1, this d' h2]

omit [Fintype ι] in
theorem stepLam_eq_zero {a b a' b' s : ℝ} (hab : a ≤ b) (hab' : a' ≤ b') (hs : s ≤ max a a') :
    stepLam a b a' b' s = 0 := by
  unfold stepLam
  rcases le_max_iff.1 hs with h | h
  · have e1 := gOv_eq_left (d := b') (h.trans hab) h
    have e2 := gOv_eq_left (d := a') (h.trans hab) h
    linarith
  · have e1 := gOv_eq_right (c := b) (h.trans hab') h
    have e2 := gOv_eq_right (c := a) (h.trans hab') h
    linarith

/-- A bounded `ℱ a`-measurable multiple of an increment of `W^k` after time `a` is a martingale. -/
theorem martingale_step [DecidableEq ι] (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (k : ι) {a b : ℝ} (hab : a ≤ b) {ξ : Ω → ℝ} (hξ : Measurable[ℱ a] ξ) {C : ℝ}
    (hC : ∀ ω, |ξ ω| ≤ C) :
    Martingale (fun (s : ℝ) ω => ξ ω * (ofNNRealTime W (min b s) ω k -
      ofNNRealTime W (min a s) ω k)) ℱ P := by
  have hMk := hW.martingale k
  have hN : Martingale (fun (s : ℝ) ω => ofNNRealTime W (min b s) ω k -
      ofNNRealTime W (min a s) ω k) ℱ P :=
    (martingale_stopAt hMk b).sub (martingale_stopAt hMk a)
  refine martingale_mul_left hN (a := a) (fun s hs => by
      funext ω
      simp [min_eq_right hs, min_eq_right (hs.trans hab)]) hξ.stronglyMeasurable fun s => ?_
  exact (hN.integrable s).bdd_mul ((hξ.mono (ℱ.le a) le_rfl).aestronglyMeasurable)
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC ω)

/-- The compensated product of two step increments is a martingale (after multiplication by the
bounded initial data). -/
theorem martingale_step_pair [DecidableEq ι] (hW : IsBrownianFiltration P ℱ W)
    [IsProbabilityMeasure P] (k l : ι) {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b')
    {ξ ξ' : Ω → ℝ} (hξ : Measurable[ℱ a] ξ) (hξ' : Measurable[ℱ a'] ξ') {C C' : ℝ}
    (hC : ∀ ω, |ξ ω| ≤ C) (hC' : ∀ ω, |ξ' ω| ≤ C') :
    Martingale (fun (s : ℝ) ω => ξ ω * ξ' ω * (
      (ofNNRealTime W (min b s) ω k - ofNNRealTime W (min a s) ω k) *
      (ofNNRealTime W (min b' s) ω l - ofNNRealTime W (min a' s) ω l) -
      (if k = l then stepLam a b a' b' s else 0))) ℱ P := by
  have hY : Martingale (fun (s : ℝ) ω =>
      (ofNNRealTime W (min b s) ω k - ofNNRealTime W (min a s) ω k) *
      (ofNNRealTime W (min b' s) ω l - ofNNRealTime W (min a' s) ω l) -
      (if k = l then stepLam a b a' b' s else 0)) ℱ P := by
    have := (((martingale_stop_prod hW k l b b').sub (martingale_stop_prod hW k l b a')).sub
      (martingale_stop_prod hW k l a b')).add (martingale_stop_prod hW k l a a')
    convert this using 1
    funext s ω
    simp only [Pi.add_apply, Pi.sub_apply, stepLam]
    split_ifs <;> ring
  have hmax : ∀ s ≤ max a a', ∀ ω,
      (ofNNRealTime W (min b s) ω k - ofNNRealTime W (min a s) ω k) *
      (ofNNRealTime W (min b' s) ω l - ofNNRealTime W (min a' s) ω l) -
      (if k = l then stepLam a b a' b' s else 0) = 0 := by
    intro s hs ω
    rw [stepLam_eq_zero hab hab' hs]
    rcases le_max_iff.1 hs with h | h
    · simp [min_eq_right h, min_eq_right (h.trans hab)]
    · simp [min_eq_right h, min_eq_right (h.trans hab')]
  refine martingale_mul_left hY (a := max a a') (fun s hs => funext (hmax s hs))
    (ξ := fun ω => ξ ω * ξ' ω)
    (((hξ.mono (ℱ.mono (le_max_left a a')) le_rfl).mul
      (hξ'.mono (ℱ.mono (le_max_right a a')) le_rfl)).stronglyMeasurable) fun s => ?_
  refine (hY.integrable s).bdd_mul (c := C * C')
    (((hξ.mono (ℱ.le a) le_rfl).mul (hξ'.mono (ℱ.le a') le_rfl)).aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hC ω) (hC' ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))

/-- Indicator of `(a, b]` as a real function. -/
def ind (a b r : ℝ) : ℝ := (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) r

omit [Fintype ι] in
theorem integral_ind_zero (e s : ℝ) :
    ∫ r in Set.Icc (0 : ℝ) s, ind 0 e r = max (min e s) 0 := by
  unfold ind
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const]
  have hset : Set.Icc (0 : ℝ) s ∩ Set.Ioc 0 e = Set.Ioc 0 (min e s) := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc, le_min_iff]
    constructor
    · rintro ⟨⟨_, h2⟩, h3, h4⟩; exact ⟨h3, h4, h2⟩
    · rintro ⟨h3, h4, h2⟩; exact ⟨⟨h3.le, h2⟩, h3, h4⟩
  rw [hset, Real.volume_real_Ioc]
  simp [max_comm]

omit [Fintype ι] in
theorem ind_eq_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (r : ℝ) : ind a b r = ind 0 b r - ind 0 a r := by
  unfold ind
  by_cases h1 : r ∈ Set.Ioc a b
  · have h2 : r ∈ Set.Ioc (0 : ℝ) b := ⟨ha.trans_lt h1.1, h1.2⟩
    have h3 : r ∉ Set.Ioc (0 : ℝ) a := fun h => absurd h.2 (not_le.2 h1.1)
    simp [h1, h2, h3]
  · by_cases h2 : r ∈ Set.Ioc (0 : ℝ) b
    · have h3 : r ∈ Set.Ioc (0 : ℝ) a := ⟨h2.1, by
        by_contra h; exact h1 ⟨not_le.1 h, h2.2⟩⟩
      simp [h1, h2, h3]
    · have h3 : r ∉ Set.Ioc (0 : ℝ) a := fun h => h2 ⟨h.1, h.2.trans hab⟩
      simp [h1, h2, h3]

omit [Fintype ι] in
theorem ind_mul_ind (c d r : ℝ) : ind 0 c r * ind 0 d r = ind 0 (min c d) r := by
  unfold ind
  by_cases h1 : r ∈ Set.Ioc (0 : ℝ) c <;> by_cases h2 : r ∈ Set.Ioc (0 : ℝ) d
  · have : r ∈ Set.Ioc (0 : ℝ) (min c d) := ⟨h1.1, le_min h1.2 h2.2⟩
    simp [h1, h2, this]
  all_goals
    have : r ∉ Set.Ioc (0 : ℝ) (min c d) := fun h =>
      by first | exact h1 ⟨h.1, h.2.trans (min_le_left _ _)⟩ | exact h2 ⟨h.1, h.2.trans (min_le_right _ _)⟩
    simp [h1, h2, this]

omit [Fintype ι] in
theorem integrableOn_ind (a b s : ℝ) : IntegrableOn (fun r => ind a b r) (Set.Icc 0 s) := by
  unfold ind
  exact (integrable_const (1 : ℝ)).indicator measurableSet_Ioc

omit [Fintype ι] in
theorem integral_ind_mul_ind {a b a' b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ha' : 0 ≤ a')
    (hab' : a' ≤ b') (s : ℝ) :
    ∫ r in Set.Icc 0 s, ind a b r * ind a' b' r = stepLam a b a' b' s := by
  have e : ∀ r, ind a b r * ind a' b' r = ind 0 (min b b') r - ind 0 (min b a') r -
      ind 0 (min a b') r + ind 0 (min a a') r := by
    intro r
    rw [ind_eq_sub ha hab, ind_eq_sub ha' hab']
    have := ind_mul_ind b b' r
    have := ind_mul_ind b a' r
    have := ind_mul_ind a b' r
    have := ind_mul_ind a a' r
    nlinarith
  have hI : ∀ c d, ∫ r in Set.Icc 0 s, ind 0 (min c d) r = gOv c d s := fun c d =>
    integral_ind_zero _ _
  simp_rw [e]
  rw [integral_add, integral_sub, integral_sub]
  · simp only [hI, stepLam]
  all_goals
    first
      | exact integrableOn_ind _ _ _
      | exact (integrableOn_ind _ _ _).sub (integrableOn_ind _ _ _)
      | exact ((integrableOn_ind _ _ _).sub (integrableOn_ind _ _ _)).sub (integrableOn_ind _ _ _)

omit [Fintype ι] in
theorem integrableOn_ind_mul (a b a' b' s : ℝ) :
    IntegrableOn (fun r => ind a b r * ind a' b' r) (Set.Icc 0 s) := by
  refine (integrableOn_ind a b s).mul_bdd (c := 1)
    ((measurable_const.indicator measurableSet_Ioc : Measurable fun r => ind a' b' r).aestronglyMeasurable)
    (ae_of_all _ fun r => ?_)
  unfold ind
  by_cases h : r ∈ Set.Ioc a' b' <;> simp [h]

omit [Fintype ι] in
theorem indicator_const_eq (a b c r : ℝ) :
    (Set.Ioc a b).indicator (fun _ => c) r = c * ind a b r := by
  unfold ind
  by_cases h : r ∈ Set.Ioc a b <;> simp [h]

theorem sum_toFun_mul_eq (Ψ Ψ' : SimpleIntegrand ℱ ι) (ω : Ω) (r : ℝ) :
    ∑ k, Ψ.toFun r ω k * Ψ'.toFun r ω k = ∑ i : Fin Ψ.n, ∑ j : Fin Ψ'.n, ∑ k,
      (Ψ.ξ i ω k * Ψ'.ξ j ω k) * (ind (Ψ.t i.castSucc) (Ψ.t i.succ) r *
        ind (Ψ'.t j.castSucc) (Ψ'.t j.succ) r) := by
  simp only [toFun_apply, indicator_const_eq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem integrableOn_sum_toFun_mul (Ψ Ψ' : SimpleIntegrand ℱ ι) (s : ℝ) (ω : Ω) :
    IntegrableOn (fun r => ∑ k, Ψ.toFun r ω k * Ψ'.toFun r ω k) (Set.Icc 0 s) := by
  simp_rw [sum_toFun_mul_eq]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ => (integrableOn_ind_mul _ _ _ _ s).const_mul _

theorem integral_toFun_mul (Ψ Ψ' : SimpleIntegrand ℱ ι) (s : ℝ) (ω : Ω) :
    ∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k * Ψ'.toFun r ω k =
      ∑ i : Fin Ψ.n, ∑ j : Fin Ψ'.n, ∑ k, Ψ.ξ i ω k * Ψ'.ξ j ω k *
        stepLam (Ψ.t i.castSucc) (Ψ.t i.succ) (Ψ'.t j.castSucc) (Ψ'.t j.succ) s := by
  have e := sum_toFun_mul_eq Ψ Ψ' ω
  simp_rw [e]
  have hnn : ∀ (Ψ : SimpleIntegrand ℱ ι) (i : Fin Ψ.n), 0 ≤ Ψ.t i.castSucc :=
    fun Ψ i => Ψ.nonneg.trans (Ψ.mono (Fin.zero_le _))
  have hle : ∀ (Ψ : SimpleIntegrand ℱ ι) (i : Fin Ψ.n), Ψ.t i.castSucc ≤ Ψ.t i.succ :=
    fun Ψ i => Ψ.mono (Fin.castSucc_le_succ i)
  rw [integral_finset_sum _ (fun i _ => ?_)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => ?_)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finset_sum _ (fun k _ => ?_)]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul, integral_ind_mul_ind (hnn Ψ i) (hle Ψ i) (hnn Ψ' j) (hle Ψ' j)]
      · exact (integrableOn_ind_mul _ _ _ _ s).const_mul _
    · exact integrable_finset_sum _ fun k _ => (integrableOn_ind_mul _ _ _ _ s).const_mul _
  · exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
      (integrableOn_ind_mul _ _ _ _ s).const_mul _

/-- Auxiliary form of `martingale_elemIntegral_mul_sub`. -/
theorem martingale_elemIntegral_mul_sub_aux (hW : IsBrownianFiltration P ℱ W)
    [IsProbabilityMeasure P] (Ψ Ψ' : SimpleIntegrand ℱ ι) :
    Martingale (fun s ω => elemIntegral W Ψ s ω * elemIntegral W Ψ' s ω -
      ∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k * Ψ'.toFun r ω k) ℱ P := by
  classical
  obtain ⟨C, hC⟩ := Ψ.bdd
  obtain ⟨C', hC'⟩ := Ψ'.bdd
  have key : Martingale (fun s ω => ∑ i : Fin Ψ.n, ∑ j : Fin Ψ'.n, ∑ k, ∑ l,
      (Ψ.ξ i ω k * Ψ'.ξ j ω l) * (
        (ofNNRealTime W (min (Ψ.t i.succ) s) ω k - ofNNRealTime W (min (Ψ.t i.castSucc) s) ω k) *
        (ofNNRealTime W (min (Ψ'.t j.succ) s) ω l - ofNNRealTime W (min (Ψ'.t j.castSucc) s) ω l) -
        (if k = l then stepLam (Ψ.t i.castSucc) (Ψ.t i.succ) (Ψ'.t j.castSucc) (Ψ'.t j.succ) s
          else 0))) ℱ P := by
    refine martingale_finset_sum _ fun i _ => martingale_finset_sum _ fun j _ =>
      martingale_finset_sum _ fun k _ => martingale_finset_sum _ fun l _ => ?_
    exact martingale_step_pair hW k l (Ψ.mono (Fin.castSucc_le_succ i))
      (Ψ'.mono (Fin.castSucc_le_succ j)) ((measurable_pi_apply k).comp (Ψ.meas i))
      ((measurable_pi_apply l).comp (Ψ'.meas j)) (fun ω => hC i ω k) (fun ω => hC' j ω l)
  convert key using 1
  funext s ω
  have hA : elemIntegral W Ψ s ω * elemIntegral W Ψ' s ω = ∑ i : Fin Ψ.n, ∑ j : Fin Ψ'.n, ∑ k, ∑ l,
      (Ψ.ξ i ω k * Ψ'.ξ j ω l) * (
        (ofNNRealTime W (min (Ψ.t i.succ) s) ω k - ofNNRealTime W (min (Ψ.t i.castSucc) s) ω k) *
        (ofNNRealTime W (min (Ψ'.t j.succ) s) ω l - ofNNRealTime W (min (Ψ'.t j.castSucc) s) ω l)) := by
    unfold elemIntegral
    simp only [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [ofNNRealTime]
    ring
  have hB : ∑ i : Fin Ψ.n, ∑ j : Fin Ψ'.n, ∑ k, Ψ.ξ i ω k * Ψ'.ξ j ω k *
        stepLam (Ψ.t i.castSucc) (Ψ.t i.succ) (Ψ'.t j.castSucc) (Ψ'.t j.succ) s =
      ∑ i : Fin Ψ.n, ∑ j : Fin Ψ'.n, ∑ k, ∑ l, (Ψ.ξ i ω k * Ψ'.ξ j ω l) *
        (if k = l then stepLam (Ψ.t i.castSucc) (Ψ.t i.succ) (Ψ'.t j.castSucc) (Ψ'.t j.succ) s
          else 0) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    simp [mul_ite]
  rw [integral_toFun_mul, hA, hB]
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem martingale_integral_eq [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ} (hZ : Martingale Z ℱ P)
    {i j : ℝ} (hij : i ≤ j) : ∫ ω, Z j ω ∂P = ∫ ω, Z i ω ∂P := by
  rw [← integral_condExp (ℱ.le i) (f := Z j)]
  exact integral_congr_ae (hZ.condExp_ae_eq hij)

theorem martingale_integral_eq_zero_time [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ}
    (hZ : Martingale Z ℱ P) (s : ℝ) : ∫ ω, Z s ω ∂P = ∫ ω, Z 0 ω ∂P := by
  rcases le_total 0 s with h | h
  · exact martingale_integral_eq hZ h
  · exact (martingale_integral_eq hZ h).symm

theorem integrable_compensator (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (Ψ Ψ' : SimpleIntegrand ℱ ι) (s : ℝ) :
    Integrable (fun ω => ∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k * Ψ'.toFun r ω k) P := by
  have hint : Integrable (fun ω => elemIntegral W Ψ s ω * elemIntegral W Ψ' s ω) P :=
    (memLp_elemIntegral hW Ψ s 2 (by norm_num)).integrable_mul (memLp_elemIntegral hW Ψ' s 2 (by norm_num))
  have := hint.sub ((martingale_elemIntegral_mul_sub_aux hW Ψ Ψ').integrable s)
  refine this.congr (ae_of_all _ fun ω => ?_)
  simp

theorem integral_elemIntegral_mul_aux (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (Ψ Ψ' : SimpleIntegrand ℱ ι) (s : ℝ) :
    ∫ ω, elemIntegral W Ψ s ω * elemIntegral W Ψ' s ω ∂P =
      ∫ ω, (∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k * Ψ'.toFun r ω k) ∂P := by
  have hZ := martingale_elemIntegral_mul_sub_aux hW Ψ Ψ'
  have hint : Integrable (fun ω => elemIntegral W Ψ s ω * elemIntegral W Ψ' s ω) P :=
    (memLp_elemIntegral hW Ψ s 2 (by norm_num)).integrable_mul (memLp_elemIntegral hW Ψ' s 2 (by norm_num))
  have h0 := martingale_integral_eq_zero_time hZ s
  have hZ0 : ∫ ω, (elemIntegral W Ψ 0 ω * elemIntegral W Ψ' 0 ω -
      ∫ r in Set.Icc (0 : ℝ) 0, ∑ k, Ψ.toFun r ω k * Ψ'.toFun r ω k) ∂P = 0 := by
    have e1 : ∀ ω, elemIntegral W Ψ 0 ω = 0 := elemIntegral_of_nonpos W Ψ (le_refl (0 : ℝ))
    simp [e1]
  rw [hZ0, integral_sub hint (integrable_compensator hW Ψ Ψ' s)] at h0
  linarith


theorem enorm_sq_eq' (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

/-- The elementary integral is a martingale (over real time). -/
theorem martingale_elemIntegral (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (Ψ : SimpleIntegrand ℱ ι) : Martingale (elemIntegral W Ψ) ℱ P := by
  classical
  obtain ⟨C, hC⟩ := Ψ.bdd
  exact martingale_finset_sum (Finset.univ : Finset (Fin Ψ.n))
    (f := fun i s ω => ∑ k, Ψ.ξ i ω k * (ofNNRealTime W (min (Ψ.t i.succ) s) ω k -
      ofNNRealTime W (min (Ψ.t i.castSucc) s) ω k))
    fun i _ => martingale_finset_sum (Finset.univ : Finset ι) fun k _ =>
      martingale_step hW k (Ψ.mono (Fin.castSucc_le_succ i))
        ((measurable_pi_apply k).comp (Ψ.meas i)) (fun ω => hC i ω k)

theorem integral_elemIntegral (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (Ψ : SimpleIntegrand ℱ ι) (s : ℝ) : ∫ ω, elemIntegral W Ψ s ω ∂P = 0 := by
  have h := martingale_integral_eq_zero_time (martingale_elemIntegral hW Ψ) s
  have h0 : ∀ ω, elemIntegral W Ψ 0 ω = 0 := elemIntegral_of_nonpos W Ψ (le_refl (0 : ℝ))
  simpa [h0] using h

/-- **Itô isometry** for simple integrands (cross terms between different coordinates and
different time steps vanish): `E[I_s²] = E ∫_0^s ∑_k |Φ^k_r|² dr`. -/
theorem integral_elemIntegral_sq (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (Ψ : SimpleIntegrand ℱ ι) (s : ℝ) :
    ∫ ω, elemIntegral W Ψ s ω ^ 2 ∂P = ∫ ω, (∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k ^ 2) ∂P := by
  have := integral_elemIntegral_mul_aux hW Ψ Ψ s
  simpa [pow_two] using this

/-- The isometry in `ℝ≥0∞` form. -/
theorem lintegral_elemIntegral_sq (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (Ψ : SimpleIntegrand ℱ ι) (s : ℝ) :
    ∫⁻ ω, ‖elemIntegral W Ψ s ω‖ₑ ^ 2 ∂P = sqIntegralOn P Ψ.toFun s := by
  have hI2 : Integrable (fun ω => elemIntegral W Ψ s ω ^ 2) P :=
    (memLp_elemIntegral hW Ψ s 2 (by norm_num)).integrable_sq
  have hH : ∀ ω, ∫⁻ r in Set.Icc 0 s, ∑ k, ‖Ψ.toFun r ω k‖ₑ ^ 2 =
      ENNReal.ofReal (∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k ^ 2) := by
    intro ω
    have hint : IntegrableOn (fun r => ∑ k, Ψ.toFun r ω k ^ 2) (Set.Icc 0 s) := by
      simpa [pow_two] using integrableOn_sum_toFun_mul Ψ Ψ s ω
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun r => Finset.sum_nonneg fun k _ => sq_nonneg _)]
    refine lintegral_congr fun r => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun k _ => enorm_sq_eq' _
  have hHint : Integrable (fun ω => ∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k ^ 2) P := by
    simpa [pow_two] using integrable_compensator hW Ψ Ψ s
  unfold sqIntegralOn
  simp_rw [hH]
  rw [← ofReal_integral_eq_lintegral_ofReal hHint
    (ae_of_all _ fun ω => integral_nonneg fun r => Finset.sum_nonneg fun k _ => sq_nonneg _),
    ← integral_elemIntegral_sq hW Ψ s,
    ofReal_integral_eq_lintegral_ofReal hI2 (ae_of_all _ fun ω => sq_nonneg _)]
  exact lintegral_congr fun ω => enorm_sq_eq' _

/-- Polarised isometry: `E[I_s(Ψ) I_s(Ψ')] = E ∫_0^s ∑_k Ψ^k_r Ψ'^k_r dr`. -/
theorem integral_elemIntegral_mul (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (Ψ Ψ' : SimpleIntegrand ℱ ι) (s : ℝ) :
    ∫ ω, elemIntegral W Ψ s ω * elemIntegral W Ψ' s ω ∂P =
      ∫ ω, (∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k * Ψ'.toFun r ω k) ∂P :=
  integral_elemIntegral_mul_aux hW Ψ Ψ' s

/-- The compensated square `I_s² - ∫_0^s ∑_k |Φ^k_r|² dr` is a martingale. -/
theorem martingale_elemIntegral_sq_sub (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (Ψ : SimpleIntegrand ℱ ι) :
    Martingale (fun s ω => elemIntegral W Ψ s ω ^ 2 - ∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k ^ 2)
      ℱ P := by
  have := martingale_elemIntegral_mul_sub_aux hW Ψ Ψ
  simpa [pow_two] using this

/-- The compensated product `I_s(Ψ) I_s(Ψ') - ∫_0^s ∑_k Ψ^k Ψ'^k` is a martingale. -/
theorem martingale_elemIntegral_mul_sub (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (Ψ Ψ' : SimpleIntegrand ℱ ι) :
    Martingale (fun s ω => elemIntegral W Ψ s ω * elemIntegral W Ψ' s ω -
      ∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k * Ψ'.toFun r ω k) ℱ P :=
  martingale_elemIntegral_mul_sub_aux hW Ψ Ψ'

/-! ### Doob's `L²` inequality -/

/-- Doob's `L²` maximal inequality for a nonnegative `L²` submartingale (discrete time). -/
theorem doob_L2_discrete [IsProbabilityMeasure P] {𝒢 : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} (hsub : Submartingale f 𝒢 P)
    (hnn : 0 ≤ f) (hL2 : ∀ k, MemLp (f k) 2 P) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => f k ω) ^ 2) ∂P ≤ 4 * ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2) ∂P := by
  set S : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => f k ω with hS
  have hfm : ∀ k, Measurable (f k) := fun k =>
    ((hsub.stronglyMeasurable k).measurable).mono (𝒢.le k) le_rfl
  have hSm : Measurable S := by
    have := Finset.measurable_sup' (s := Finset.range (n + 1)) Finset.nonempty_range_add_one
      (f := f) (fun k _ => hfm k)
    convert this using 1
    funext ω
    simp [hS, Finset.sup'_apply]
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω =>
    (hnn 0 ω).trans (Finset.le_sup' (fun k => f k ω) (Finset.mem_range.2 (Nat.succ_pos n)))
  have hSsq : ∀ ω, S ω ^ 2 ≤ ∑ k ∈ Finset.range (n + 1), f k ω ^ 2 := by
    intro ω
    obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one (fun k => f k ω)
    simp only [hS]
    rw [hk']
    exact Finset.single_le_sum (f := fun k => f k ω ^ 2) (fun k _ => sq_nonneg _) hk
  have hSint : Integrable (fun ω => S ω ^ 2) P := by
    refine Integrable.mono' (g := fun ω => ∑ k ∈ Finset.range (n + 1), f k ω ^ 2)
      (integrable_finsetSum (Finset.range (n + 1)) fun k _ => (hL2 k).integrable_sq)
      (hSm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hSsq ω
  have hSL2 : MemLp S 2 P := (memLp_two_iff_integrable_sq hSm.aestronglyMeasurable).2 hSint
  have hfS : Integrable (fun ω => f n ω * S ω) P := (hL2 n).integrable_mul hSL2
  -- weak-type inequality
  have hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * P {ω | t ≤ S ω} ≤
      ∫⁻ ω in {ω | t ≤ S ω}, ENNReal.ofReal (f n ω) ∂P := by
    intro t ht
    have h := maximal_ineq hsub hnn (ε := t.toNNReal) n
    rw [Real.coe_toNNReal t ht.le] at h
    rw [← ofReal_integral_eq_lintegral_ofReal ((hsub.integrable n).integrableOn)
      (ae_of_all _ fun ω => hnn n ω)]
    exact h
  -- layer cake
  have hlayer : ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂P =
      ENNReal.ofReal 2 * ∫⁻ t in Set.Ioi 0, P {ω | t ≤ S ω} * ENNReal.ofReal t := by
    have := lintegral_rpow_eq_lintegral_meas_le_mul P (f := S) (ae_of_all _ hS0)
      hSm.aemeasurable (p := 2) (by norm_num)
    simpa [Real.rpow_two, show (2:ℝ) - 1 = 1 by norm_num] using this
  have hbound : ∫⁻ t in Set.Ioi (0:ℝ), P {ω | t ≤ S ω} * ENNReal.ofReal t ≤
      ENNReal.ofReal (∫ ω, f n ω * S ω ∂P) := by
    calc ∫⁻ t in Set.Ioi (0:ℝ), P {ω | t ≤ S ω} * ENNReal.ofReal t
        ≤ ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ ω, {ω | t ≤ S ω}.indicator
            (fun ω => ENNReal.ofReal (f n ω)) ω ∂P := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          rw [lintegral_indicator (measurableSet_le measurable_const hSm), mul_comm]
          exact hweak t ht
      _ = ∫⁻ ω, ∫⁻ t in Set.Ioi (0:ℝ), {ω | t ≤ S ω}.indicator
            (fun ω => ENNReal.ofReal (f n ω)) ω ∂volume ∂P := by
          refine lintegral_lintegral_swap ?_
          have h1 : Measurable fun p : ℝ × Ω => ENNReal.ofReal (f n p.2) :=
            (ENNReal.measurable_ofReal.comp (hfm n)).comp measurable_snd
          have h2 : MeasurableSet {p : ℝ × Ω | p.1 ≤ S p.2} :=
            measurableSet_le measurable_fst (hSm.comp measurable_snd)
          exact (h1.indicator h2).aemeasurable
      _ = ∫⁻ ω, ENNReal.ofReal (f n ω) * ENNReal.ofReal (S ω) ∂P := by
          refine lintegral_congr fun ω => ?_
          have e : (fun t : ℝ => {ω | t ≤ S ω}.indicator (fun ω => ENNReal.ofReal (f n ω)) ω) =
              (Set.Iic (S ω)).indicator (fun _ => ENNReal.ofReal (f n ω)) := by
            funext t
            simp [Set.indicator]
          rw [e, lintegral_indicator_const measurableSet_Iic,
            Measure.restrict_apply measurableSet_Iic, Set.inter_comm, Set.Ioi_inter_Iic,
            Real.volume_Ioc, sub_zero]
      _ = ENNReal.ofReal (∫ ω, f n ω * S ω ∂P) := by
          rw [ofReal_integral_eq_lintegral_ofReal hfS
            (ae_of_all _ fun ω => mul_nonneg (hnn n ω) (hS0 ω))]
          exact lintegral_congr fun ω => (ENNReal.ofReal_mul (hnn n ω)).symm
  have hint1 : ENNReal.ofReal (∫ ω, S ω ^ 2 ∂P) ≤ ENNReal.ofReal (2 * ∫ ω, f n ω * S ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hSint (ae_of_all _ fun ω => sq_nonneg _), hlayer,
      ENNReal.ofReal_mul (by norm_num)]
    gcongr
  have hreal : ∫ ω, S ω ^ 2 ∂P ≤ 2 * ∫ ω, f n ω * S ω ∂P :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num)
      (integral_nonneg fun ω => mul_nonneg (hnn n ω) (hS0 ω)))).1 hint1
  have hf2 : Integrable (fun ω => f n ω ^ 2) P := (hL2 n).integrable_sq
  have hAMGM : 2 * ∫ ω, f n ω * S ω ∂P ≤ 2 * ∫ ω, f n ω ^ 2 ∂P + (1 / 2) * ∫ ω, S ω ^ 2 ∂P := by
    have hI : Integrable (fun ω => 2 * f n ω ^ 2 + 1 / 2 * S ω ^ 2) P :=
      (hf2.const_mul 2).add (hSint.const_mul (1 / 2))
    have := integral_mono (hfS.const_mul 2) hI
      (fun ω => by
        simp only
        nlinarith [sq_nonneg (2 * f n ω - S ω)])
    rw [integral_const_mul, integral_add (hf2.const_mul 2) (hSint.const_mul (1 / 2)),
      integral_const_mul, integral_const_mul] at this
    linarith
  have hfin : ∫ ω, S ω ^ 2 ∂P ≤ 4 * ∫ ω, f n ω ^ 2 ∂P := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hSint (ae_of_all _ fun ω => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun ω => sq_nonneg _)]
  calc ENNReal.ofReal (∫ ω, S ω ^ 2 ∂P) ≤ ENNReal.ofReal (4 * ∫ ω, f n ω ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal hfin
    _ = 4 * ENNReal.ofReal (∫ ω, f n ω ^ 2 ∂P) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

/-- The filtration `j ↦ ℱ (u j)` along a monotone sequence of times. -/
def gridFiltration (ℱ : Filtration ℝ mΩ) (u : ℕ → ℝ) (hu : Monotone u) : Filtration ℕ mΩ where
  seq j := ℱ (u j)
  mono' := fun _ _ hij => ℱ.mono (hu hij)
  le' := fun _ => ℱ.le _

theorem enorm_eq_ofReal_abs (x : ℝ) : ‖x‖ₑ = ENNReal.ofReal |x| := by
  rw [← Real.norm_eq_abs, ofReal_norm]

/-- Doob's `L²` maximal inequality for a continuous `L²` martingale. -/
theorem doob_L2_continuous [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {I : ℝ → Ω → ℝ} (hI : Martingale I ℱ P)
    (hcont : ∀ ω, Continuous fun t => I t ω) (hL2 : ∀ t, MemLp (I t) 2 P) (T : ℝ) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖I t ω‖ₑ) ^ 2 ∂P ≤ 4 * ∫⁻ ω, ‖I T ω‖ₑ ^ 2 ∂P := by
  rcases lt_or_ge T 0 with hT | hT
  · have : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty (not_le.2 hT)
    simp [this]
  set u : ℕ → ℕ → ℝ := fun m j => T * ((min j (2 ^ m) : ℕ) : ℝ) / 2 ^ m with hu_def
  have hu : ∀ m, Monotone (u m) := by
    intro m i j hij
    simp only [hu_def]
    have : ((min i (2 ^ m) : ℕ) : ℝ) ≤ ((min j (2 ^ m) : ℕ) : ℝ) := by
      exact_mod_cast min_le_min_right _ hij
    gcongr
  have hu_top : ∀ m, u m (2 ^ m) = T := by
    intro m
    simp only [hu_def, min_self]
    push_cast
    field_simp
  have hu_nn : ∀ m j, 0 ≤ u m j := fun m j => by
    simp only [hu_def]; positivity
  have hu_le : ∀ m j, u m j ≤ T := fun m j => by
    simp only [hu_def]
    have h1 : ((min j (2 ^ m) : ℕ) : ℝ) ≤ 2 ^ m := by exact_mod_cast min_le_right _ _
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- grid sup
  set Z : ℕ → Ω → ℝ := fun m ω => (Finset.range (2 ^ m + 1)).sup' Finset.nonempty_range_add_one
    fun k => |I (u m k) ω| with hZ
  have hImeas : ∀ t, Measurable (I t) := fun t =>
    (hI.stronglyMeasurable t).measurable.mono (ℱ.le t) le_rfl
  have hZmeas : ∀ m, Measurable (Z m) := by
    intro m
    have := Finset.measurable_sup' (s := Finset.range (2 ^ m + 1)) Finset.nonempty_range_add_one
      (f := fun k ω => |I (u m k) ω|) (fun k _ => (hImeas _).abs)
    convert this using 1
    funext ω
    simp [hZ, Finset.sup'_apply]
  -- step 1: discrete Doob
  have step1 : ∀ m, ∫⁻ ω, ENNReal.ofReal (Z m ω ^ 2) ∂P ≤ 4 * ∫⁻ ω, ‖I T ω‖ₑ ^ 2 ∂P := by
    intro m
    have hg : Martingale (fun j ω => I (u m j) ω) (gridFiltration ℱ (u m) (hu m)) P :=
      ⟨fun j => hI.stronglyAdapted (u m j), fun i j hij => hI.condExp_ae_eq (hu m hij)⟩
    have hsub : Submartingale (fun j ω => |I (u m j) ω|) (gridFiltration ℱ (u m) (hu m)) P := by
      have := hg.submartingale.sup hg.neg.submartingale
      convert this using 1
      funext j ω
      simp [abs_eq_max_neg]
    have hL2' : ∀ k, MemLp (fun ω => |I (u m k) ω|) 2 P := fun k => (hL2 _).abs
    have := doob_L2_discrete hsub (fun j ω => abs_nonneg _) hL2' (2 ^ m)
    simp only [hu_top] at this
    simpa [hZ, ← enorm_sq_eq'] using this
  -- grid approximation of times
  have hgrid : ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ j : ℕ → ℕ, (∀ m, j m ≤ 2 ^ m) ∧
      Tendsto (fun m => u m (j m)) atTop (𝓝 t) := by
    intro t ht
    rcases hT.eq_or_lt with h0 | hpos
    · have : t = 0 := by
        have := ht.2; rw [← h0] at this; exact le_antisymm this ht.1
      refine ⟨fun _ => 0, fun m => Nat.zero_le _, ?_⟩
      simp [hu_def, ← h0, this]
    · set j : ℕ → ℕ := fun m => ⌊t * 2 ^ m / T⌋₊ with hj
      have hx0 : ∀ m : ℕ, 0 ≤ t * 2 ^ m / T := fun m => by
        have := ht.1; positivity
      have hjle : ∀ m, (j m : ℝ) ≤ t * 2 ^ m / T := fun m => Nat.floor_le (hx0 m)
      have hjlt : ∀ m, t * 2 ^ m / T < (j m : ℝ) + 1 := fun m => Nat.lt_floor_add_one _
      have hjm : ∀ m, j m ≤ 2 ^ m := by
        intro m
        have : t * 2 ^ m / T ≤ 2 ^ m := by
          rw [div_le_iff₀ hpos]
          nlinarith [ht.2, (by positivity : (0:ℝ) < 2 ^ m)]
        exact_mod_cast (hjle m).trans this
      refine ⟨j, hjm, ?_⟩
      have hum : ∀ m, u m (j m) = T * (j m : ℝ) / 2 ^ m := by
        intro m; simp only [hu_def, min_eq_left (hjm m)]
      simp_rw [hum]
      have hlow : ∀ m : ℕ, t - T * (1 / 2) ^ m ≤ T * (j m : ℝ) / 2 ^ m := by
        intro m
        have h1 := hjlt m
        have h2 : (0:ℝ) < 2 ^ m := by positivity
        rw [one_div, inv_pow, ← div_eq_mul_inv, sub_le_iff_le_add, ← add_div, le_div_iff₀ h2]
        have : t * 2 ^ m < T * ((j m : ℝ) + 1) := by
          rw [div_lt_iff₀ hpos] at h1; nlinarith
        nlinarith
      have hup : ∀ m : ℕ, T * (j m : ℝ) / 2 ^ m ≤ t := by
        intro m
        have h2 : (0:ℝ) < 2 ^ m := by positivity
        rw [div_le_iff₀ h2]
        have := hjle m
        rw [le_div_iff₀ hpos] at this
        nlinarith
      have hT0 : Tendsto (fun m : ℕ => T * (1 / 2 : ℝ) ^ m) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
          (by norm_num)).const_mul T
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlow hup
      simpa using (tendsto_const_nhds (x := t)).sub hT0
  -- pointwise comparison
  have step2 : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖I t ω‖ₑ) ^ 2 ≤
      liminf (fun m => ENNReal.ofReal (Z m ω ^ 2)) atTop := by
    intro ω
    have : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
    have e : (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖I t ω‖ₑ) = ⨆ t : Set.Icc (0 : ℝ) T, ‖I t ω‖ₑ :=
      iSup_subtype'
    rw [e, ENNReal.iSup_pow]
    refine iSup_le fun ⟨t, ht⟩ => ?_
    obtain ⟨j, hj, hjt⟩ := hgrid t ht
    have hten : Tendsto (fun m => ‖I (u m (j m)) ω‖ₑ ^ 2) atTop (𝓝 (‖I t ω‖ₑ ^ 2)) := by
      have h1 : Tendsto (fun m => I (u m (j m)) ω) atTop (𝓝 (I t ω)) :=
        ((hcont ω).tendsto t).comp hjt
      exact ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp h1)
    calc ‖I t ω‖ₑ ^ 2 = liminf (fun m => ‖I (u m (j m)) ω‖ₑ ^ 2) atTop := hten.liminf_eq.symm
      _ ≤ liminf (fun m => ENNReal.ofReal (Z m ω ^ 2)) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun m => ?_)
        rw [enorm_sq_eq']
        apply ENNReal.ofReal_le_ofReal
        have : |I (u m (j m)) ω| ≤ Z m ω := Finset.le_sup' (fun k => |I (u m k) ω|)
          (Finset.mem_range.2 (Nat.lt_succ_of_le (hj m)))
        calc I (u m (j m)) ω ^ 2 = |I (u m (j m)) ω| ^ 2 := (sq_abs _).symm
          _ ≤ Z m ω ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖I t ω‖ₑ) ^ 2 ∂P
      ≤ ∫⁻ ω, liminf (fun m => ENNReal.ofReal (Z m ω ^ 2)) atTop ∂P := lintegral_mono step2
    _ ≤ liminf (fun m => ∫⁻ ω, ENNReal.ofReal (Z m ω ^ 2) ∂P) atTop :=
        lintegral_liminf_le fun m => ENNReal.measurable_ofReal.comp ((hZmeas m).pow_const 2)
    _ ≤ 4 * ∫⁻ ω, ‖I T ω‖ₑ ^ 2 ∂P :=
        (liminf_le_liminf (Eventually.of_forall step1)).trans_eq (liminf_const _)


/-- Doob's `L²` maximal inequality for the elementary integral:
`E sup_{t ≤ T} I_t² ≤ 4 E ∫_0^T |Φ|²`. -/
theorem lintegral_iSup_elemIntegral_sq_le (hW : IsBrownianFiltration P ℱ W)
    [IsProbabilityMeasure P] (Ψ : SimpleIntegrand ℱ ι) (T : ℝ) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖elemIntegral W Ψ t ω‖ₑ) ^ 2 ∂P ≤
      4 * sqIntegralOn P Ψ.toFun T := by
  have := doob_L2_continuous (martingale_elemIntegral hW Ψ)
    (fun ω => continuous_elemIntegral hW.cont Ψ ω) (fun t => memLp_elemIntegral hW Ψ t 2 (by norm_num)) T
  rwa [lintegral_elemIntegral_sq hW Ψ T] at this

end SimpleIntegrand

/-! ### Density of simple integrands -/

section DensityAux

variable {P : Measure Ω}

/-- squared Euclidean norm in `ℝ≥0∞` -/
def qn (v : ι → ℝ) : ℝ≥0∞ := ∑ k, ‖v k‖ₑ ^ 2

theorem continuous_qn : Continuous (qn (ι := ι)) := by
  unfold qn
  refine continuous_finsetSum _ fun k _ => ?_
  exact (ENNReal.continuous_pow 2).comp ((continuous_enorm).comp (continuous_apply k))

theorem measurable_qn : Measurable (qn (ι := ι)) := continuous_qn.measurable

theorem qn_add_le (u v : ι → ℝ) : qn (u + v) ≤ 2 * qn u + 2 * qn v := by
  unfold qn
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Pi.add_apply, SimpleIntegrand.enorm_sq_eq']
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg (u k - v k)]

theorem qn_sub_le (u v : ι → ℝ) : qn (u - v) ≤ 2 * qn u + 2 * qn v := by
  have := qn_add_le u (-v)
  have e : qn (-v) = qn v := by
    unfold qn; simp
  rwa [e, ← sub_eq_add_neg] at this

theorem qn_mono {u v : ι → ℝ} (h : ∀ k, |u k| ≤ |v k|) : qn u ≤ qn v := by
  unfold qn
  refine Finset.sum_le_sum fun k _ => ?_
  gcongr
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (by simpa using h k)

/-- Dominated convergence for `sqIntegralOn`. -/
theorem tendsto_sqIntegralOn_of_dominated {P : Measure Ω} [IsProbabilityMeasure P]
    {Fn : ℕ → ℝ → Ω → ι → ℝ} {F : ℝ → Ω → ι → ℝ} (T : ℝ)
    (hFn : ∀ n, Measurable fun x : ℝ × Ω => Fn n x.1 x.2)
    (hF : Measurable fun x : ℝ × Ω => F x.1 x.2)
    {D : ℝ → Ω → ℝ≥0∞} (hD : Measurable fun x : ℝ × Ω => D x.1 x.2)
    (hDfin : ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, D s ω) ∂P ≠ ∞)
    (hle : ∀ n s ω, s ∈ Set.Icc 0 T → qn (Fn n s ω - F s ω) ≤ D s ω)
    (hconv : ∀ ω, ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)),
      Tendsto (fun n => Fn n s ω) atTop (𝓝 (F s ω))) :
    Tendsto (fun n => sqIntegralOn P (fun s ω => Fn n s ω - F s ω) T) atTop (𝓝 0) := by
  have hmeas_n : ∀ n, Measurable fun x : ℝ × Ω => qn (Fn n x.1 x.2 - F x.1 x.2) := fun n =>
    measurable_qn.comp ((hFn n).sub hF)
  have houter : ∀ n, Measurable fun ω => ∫⁻ s in Set.Icc 0 T, qn (Fn n s ω - F s ω) :=
    fun n => (hmeas_n n).lintegral_prod_left'
  have hDm : Measurable fun ω => ∫⁻ s in Set.Icc 0 T, D s ω := hD.lintegral_prod_left'
  have hgood := ae_lt_top hDm hDfin
  have := tendsto_lintegral_of_dominated_convergence (μ := P)
    (F := fun n ω => ∫⁻ s in Set.Icc 0 T, qn (Fn n s ω - F s ω)) (f := fun _ => 0)
    (fun ω => ∫⁻ s in Set.Icc 0 T, D s ω) houter
    (fun n => ae_of_all _ fun ω => lintegral_mono_ae
      ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => hle n s ω hs))) hDfin ?_
  · simpa [sqIntegralOn, qn] using this
  · filter_upwards [hgood] with ω hω
    have h0 := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Set.Icc 0 T))
      (F := fun n s => qn (Fn n s ω - F s ω)) (f := fun _ => 0) (fun s => D s ω)
      (fun n => measurable_qn.comp (((hFn n).comp measurable_prodMk_right).sub
        (hF.comp measurable_prodMk_right)))
      (fun n => (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => hle n s ω hs))
      hω.ne ?_
    · simpa using h0
    · filter_upwards [hconv ω] with s hs
      have : Tendsto (fun n => Fn n s ω - F s ω) atTop (𝓝 (F s ω - F s ω)) :=
        hs.sub tendsto_const_nhds
      rw [sub_self] at this
      have h2 := (continuous_qn.tendsto 0).comp this
      have e0 : qn (0 : ι → ℝ) = 0 := by simp [qn]
      rw [e0] at h2
      exact h2


section Mollifier

/-- `G(·, ω, k)` cut off at times `≤ 0`. -/
def cutG (G : ℝ → Ω → ι → ℝ) (k : ι) (ω : Ω) : ℝ → ℝ := (Set.Ioi 0).indicator (fun r => G r ω k)

/-- Primitive `∫_0^a` of the cut-off coordinate. -/
def primG (G : ℝ → Ω → ι → ℝ) (k : ι) (ω : Ω) (a : ℝ) : ℝ := ∫ r in (0:ℝ)..a, cutG G k ω r

/-- Backward moving average `h⁻¹ ∫_{s-h}^{s}` of the cut-off integrand. -/
def molG (G : ℝ → Ω → ι → ℝ) (h s : ℝ) (ω : Ω) : ι → ℝ := fun k =>
  (primG G k ω (max s 0) - primG G k ω (max (s - h) 0)) / h

theorem measurable_cutG {G : ℝ → Ω → ι → ℝ} (hG : Measurable fun x : ℝ × Ω => G x.1 x.2)
    (k : ι) (ω : Ω) : Measurable (cutG G k ω) := by
  have : Measurable fun r : ℝ => G r ω k :=
    (measurable_pi_apply k).comp (hG.comp measurable_prodMk_right)
  exact this.indicator measurableSet_Ioi

theorem abs_cutG_le {G : ℝ → Ω → ι → ℝ} {M : ℝ} (hb : ∀ s ω k, |G s ω k| ≤ M) (k : ι) (ω : Ω)
    (r : ℝ) : |cutG G k ω r| ≤ M := by
  unfold cutG
  by_cases h : r ∈ Set.Ioi (0:ℝ)
  · simpa [h] using hb r ω k
  · simp only [Set.indicator_of_notMem h, abs_zero]
    exact (abs_nonneg _).trans (hb 0 ω k)

theorem intervalIntegrable_cutG {G : ℝ → Ω → ι → ℝ} {M : ℝ} (hG : Measurable fun x : ℝ × Ω => G x.1 x.2)
    (hb : ∀ s ω k, |G s ω k| ≤ M) (k : ι) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (cutG G k ω) volume a b := by
  have hI : ∀ x y : ℝ, IntegrableOn (cutG G k ω) (Set.Ioc x y) := fun x y =>
    Integrable.of_bound (C := M) (measurable_cutG hG k ω).aestronglyMeasurable
      (ae_of_all _ fun r => by simpa [Real.norm_eq_abs] using abs_cutG_le hb k ω r)
  exact ⟨hI a b, hI b a⟩

theorem abs_molG_le {G : ℝ → Ω → ι → ℝ} {M : ℝ} (hG : Measurable fun x : ℝ × Ω => G x.1 x.2)
    (hb : ∀ s ω k, |G s ω k| ≤ M) {h : ℝ} (hh : 0 < h) (s : ℝ) (ω : Ω) (k : ι) :
    |molG G h s ω k| ≤ M := by
  unfold molG primG
  have hint := intervalIntegrable_cutG hG hb k ω
  rw [intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := max (s - h) 0) (b := max s 0)
    (f := cutG G k ω) (C := M) (fun r _ => by simpa [Real.norm_eq_abs] using abs_cutG_le hb k ω r)
  have h2 : |max s 0 - max (s - h) 0| ≤ h := by
    rw [abs_le]; constructor <;> cases max_cases s 0 <;> cases max_cases (s - h) 0 <;> 
      simp_all <;> linarith
  rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0 ω k)
  calc _ = ‖∫ x in (max (s - h) 0)..(max s 0), cutG G k ω x‖ := by rw [Real.norm_eq_abs]
    _ ≤ M * |max s 0 - max (s - h) 0| := h1
    _ ≤ M * h := by gcongr
    _ = M * h := rfl


theorem continuous_primG {G : ℝ → Ω → ι → ℝ} {M : ℝ} (hG : Measurable fun x : ℝ × Ω => G x.1 x.2)
    (hb : ∀ s ω k, |G s ω k| ≤ M) (k : ι) (ω : Ω) : Continuous (primG G k ω) :=
  intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_cutG hG hb k ω a b) 0

theorem continuous_molG {G : ℝ → Ω → ι → ℝ} {M : ℝ} (hG : Measurable fun x : ℝ × Ω => G x.1 x.2)
    (hb : ∀ s ω k, |G s ω k| ≤ M) (h : ℝ) (ω : Ω) (k : ι) :
    Continuous fun s => molG G h s ω k := by
  unfold molG
  have := continuous_primG hG hb k ω
  fun_prop

theorem primG_eq {G : ℝ → Ω → ι → ℝ} {a : ℝ} (ha : 0 ≤ a) (k : ι) (ω : Ω) :
    primG G k ω a = ∫ r in Set.Ioc 0 a, G r ω k := by
  unfold primG
  rw [intervalIntegral.integral_of_le ha]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  simp [cutG, Set.indicator, hr.1]

theorem measurable_primG {G : ℝ → Ω → ι → ℝ}
    (hG : Measurable fun x : ℝ × Ω => G x.1 x.2) {a : ℝ} (ha : 0 ≤ a) (k : ι) :
    Measurable fun ω => primG G k ω a := by
  have : (fun ω => primG G k ω a) = fun ω => ∫ r in Set.Ioc 0 a, G r ω k := by
    funext ω; exact primG_eq ha k ω
  rw [this]
  have hm : StronglyMeasurable (Function.uncurry fun (r : ℝ) (ω : Ω) => G r ω k) :=
    ((measurable_pi_apply k).comp hG).stronglyMeasurable
  exact (hm.integral_prod_left (μ := volume.restrict (Set.Ioc (0:ℝ) a))).measurable

theorem measurable_molG {G : ℝ → Ω → ι → ℝ} {M : ℝ} (hG : Measurable fun x : ℝ × Ω => G x.1 x.2)
    (hb : ∀ s ω k, |G s ω k| ≤ M) (h : ℝ) :
    Measurable fun x : ℝ × Ω => molG G h x.1 x.2 := by
  refine measurable_pi_iff.2 fun k => ?_
  have := measurable_uncurry_of_continuous_of_measurable
    (u := fun (s : ℝ) (ω : Ω) => molG G h s ω k) (fun ω => continuous_molG hG hb h ω k)
    (fun s => by
      unfold molG
      exact ((measurable_primG hG (le_max_right s 0) k).sub
        (measurable_primG hG (le_max_right (s - h) 0) k)).div_const h)
  exact this

/-- Adaptedness of the moving average. -/
theorem measurable_molG_of_primitive {m : MeasurableSpace Ω} {G : ℝ → Ω → ι → ℝ} {s h : ℝ}
    (hs : 0 ≤ s) (hh : 0 < h)
    (hA : ∀ a, 0 ≤ a → a ≤ s → ∀ k, Measurable[m] fun ω => ∫ r in Set.Ioc 0 a, G r ω k) :
    Measurable[m] (molG G h s) := by
  refine measurable_pi_iff.2 fun k => ?_
  have e : (fun ω => molG G h s ω k) = fun ω =>
      ((∫ r in Set.Ioc 0 s, G r ω k) - ∫ r in Set.Ioc 0 (max (s - h) 0), G r ω k) / h := by
    funext ω
    unfold molG
    rw [max_eq_left hs, primG_eq hs, primG_eq (le_max_right _ _)]
  rw [e]
  exact ((hA s hs le_rfl k).sub (hA _ (le_max_right _ _) (max_le (by linarith) hs) k)).div_const h


theorem locallyIntegrable_cutG {G : ℝ → Ω → ι → ℝ} {M : ℝ} (hG : Measurable fun x : ℝ × Ω => G x.1 x.2)
    (hb : ∀ s ω k, |G s ω k| ≤ M) (k : ι) (ω : Ω) : LocallyIntegrable (cutG G k ω) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    (measurable_cutG hG k ω).aestronglyMeasurable
    (ae_of_all _ fun r => by simpa [Real.norm_eq_abs] using abs_cutG_le hb k ω r)

theorem tendsto_molG_ae {G : ℝ → Ω → ι → ℝ} {M : ℝ} (hG : Measurable fun x : ℝ × Ω => G x.1 x.2)
    (hb : ∀ s ω k, |G s ω k| ≤ M) (T : ℝ) (ω : Ω) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)),
      Tendsto (fun n : ℕ => molG G (1 / ((n : ℝ) + 1)) s ω) atTop (𝓝 (G s ω)) := by
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), ∀ k, ∀ c,
      HasDerivAt (fun x => ∫ t in c..x, cutG G k ω t) (cutG G k ω s) s := by
    rw [ae_all_iff]
    exact fun k => LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_cutG hG hb k ω)
  have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({0} : Set ℝ) :=
    (Set.countable_singleton (0 : ℝ)).ae_notMem volume
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_of_ae h0,
    ae_restrict_mem measurableSet_Icc] with s hs hs0 hsI
  have hpos : 0 < s := lt_of_le_of_ne hsI.1 (fun h => hs0 (by simp [← h]))
  have hh : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < s := hh.eventually (gt_mem_nhds hpos)
  refine tendsto_pi_nhds.2 fun k => ?_
  have hd := (hasDerivAt_iff_tendsto_slope_zero.1 (hs k 0))
  have ht : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using hh.neg, Eventually.of_forall fun n => by
      have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith⟩
  have key := hd.comp ht
  have hg : cutG G k ω s = G s ω k := by simp [cutG, hpos]
  rw [hg] at key
  refine key.congr' ?_
  filter_upwards [hev] with n hn
  have hnpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  simp only [Function.comp, molG, primG, smul_eq_mul]
  rw [max_eq_left hpos.le, max_eq_left (by linarith),
    show s + -(1 / ((n : ℝ) + 1)) = s - 1 / ((n : ℝ) + 1) by ring]
  generalize 1 / ((n : ℝ) + 1) = h at *
  generalize (∫ t in (0:ℝ)..s, cutG G k ω t) = A
  generalize (∫ t in (0:ℝ)..(s - h), cutG G k ω t) = B
  rw [inv_neg]
  field_simp
  ring


theorem qn_le_of_abs_le {v : ι → ℝ} {C : ℝ} (hv : ∀ k, |v k| ≤ C) :
    qn v ≤ ∑ _k : ι, ENNReal.ofReal C ^ 2 := by
  unfold qn
  refine Finset.sum_le_sum fun k _ => ?_
  gcongr
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hv k)

theorem lintegral_const_lt_top {P : Measure Ω} [IsProbabilityMeasure P] (c : ℝ≥0∞) (hc : c ≠ ∞)
    (T : ℝ) : ∫⁻ _ω, (∫⁻ _s in Set.Icc (0:ℝ) T, c) ∂P ≠ ∞ := by
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, measure_univ, mul_one]
  exact ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top

theorem tendsto_sqIntegralOn_molG {P : Measure Ω} [IsProbabilityMeasure P] {G : ℝ → Ω → ι → ℝ}
    {M : ℝ} (hG : Measurable fun x : ℝ × Ω => G x.1 x.2) (hb : ∀ s ω k, |G s ω k| ≤ M) (T : ℝ) :
    Tendsto (fun n : ℕ => sqIntegralOn P
      (fun s ω => molG G (1 / ((n : ℝ) + 1)) s ω - G s ω) T) atTop (𝓝 0) := by
  refine tendsto_sqIntegralOn_of_dominated (D := fun _ _ => ∑ _k : ι, ENNReal.ofReal (2 * M) ^ 2) T
    (fun n => measurable_molG hG hb _) hG measurable_const ?_ ?_ (fun ω => tendsto_molG_ae hG hb T ω)
  · exact lintegral_const_lt_top _ (ENNReal.sum_ne_top.2 fun _ _ =>
      ENNReal.pow_ne_top ENNReal.ofReal_ne_top) T
  · intro n s ω _
    refine qn_le_of_abs_le fun k => ?_
    have hh : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h1 := abs_molG_le hG hb hh s ω k
    have h2 := hb s ω k
    simp only [Pi.sub_apply]
    calc _ ≤ |molG G (1 / ((n : ℝ) + 1)) s ω k| + |G s ω k| := abs_sub _ _
      _ ≤ 2 * M := by linarith

end Mollifier

section Clip

/-- Coordinatewise truncation at level `M`. -/
def clipv (M : ℝ) (v : ι → ℝ) : ι → ℝ := fun k => max (-M) (min M (v k))

theorem abs_clip_sub_le {M x : ℝ} (hM : 0 ≤ M) : |max (-M) (min M x) - x| ≤ |x| := by
  rcases le_total x (-M) with h | h
  · have h1 : min M x = x := min_eq_right (by linarith)
    rw [h1, max_eq_left h, abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
  rcases le_total x M with h' | h'
  · rw [min_eq_right h', max_eq_right h]; simp
  · rw [min_eq_left h', max_eq_right (by linarith)]
    rw [abs_le]; constructor <;> cases abs_cases x <;> linarith

theorem abs_clip_le {M x : ℝ} (hM : 0 ≤ M) : |max (-M) (min M x)| ≤ M := by
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem measurable_clipv (M : ℝ) : Measurable (clipv (ι := ι) M) :=
  measurable_pi_iff.2 fun k => (measurable_const.max (measurable_const.min (measurable_pi_apply k)))

theorem tendsto_sqIntegralOn_clip {P : Measure Ω} [IsProbabilityMeasure P] {G : ℝ → Ω → ι → ℝ} {T : ℝ}
    (hG : Measurable fun x : ℝ × Ω => G x.1 x.2)
    (hfin : ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, qn (G s ω)) ∂P ≠ ∞) :
    Tendsto (fun n : ℕ => sqIntegralOn P (fun s ω => clipv n (G s ω) - G s ω) T) atTop (𝓝 0) := by
  refine tendsto_sqIntegralOn_of_dominated (D := fun s ω => qn (G s ω)) T
    (fun n => (measurable_clipv _).comp hG) hG (measurable_qn.comp hG) hfin ?_ ?_
  · intro n s ω _
    refine qn_mono fun k => ?_
    exact abs_clip_sub_le (Nat.cast_nonneg n)
  · intro ω
    refine ae_of_all _ fun s => ?_
    refine tendsto_pi_nhds.2 fun k => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|G s ω k|⌉₊] with n hn
    have h1 : |G s ω k| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [abs_le] at h1
    simp only [clipv]
    rw [min_eq_right h1.2, max_eq_right h1.1]

end Clip

theorem measurable_integral_of_progressive {ℱ : Filtration ℝ mΩ} {Φ : ℝ → Ω → ι → ℝ}
    (hΦ : IsProgressive ℱ Φ) {ψ : ℝ → ℝ} (hψ : Measurable ψ) (s a : ℝ) (has : a ≤ s) (k : ι) :
    Measurable[ℱ s] fun ω => ∫ r in Set.Ioc 0 a, ψ (Φ r ω k) := by
  let mS : MeasurableSpace Ω := ℱ s
  have hq : Measurable fun x : ℝ × Ω => ((⟨min x.1 s, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic s), x.2) :=
    Measurable.prodMk (Measurable.subtype_mk (measurable_fst.min measurable_const)) measurable_snd
  have hF : Measurable fun x : ℝ × Ω => ψ (Φ (min x.1 s) x.2 k) :=
    hψ.comp ((measurable_pi_apply k).comp ((hΦ s).comp hq))
  have e : (fun ω => ∫ r in Set.Ioc 0 a, ψ (Φ r ω k)) =
      fun ω => ∫ r in Set.Ioc 0 a, ψ (Φ (min r s) ω k) := by
    funext ω
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    simp only [min_eq_left (hr.2.trans has)]
  rw [e]
  have hm : StronglyMeasurable (Function.uncurry fun (r : ℝ) (ω : Ω) => ψ (Φ (min r s) ω k)) :=
    hF.stronglyMeasurable
  exact (hm.integral_prod_left (μ := volume.restrict (Set.Ioc (0:ℝ) a))).measurable


end DensityAux



section Riemann

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ}

theorem SimpleIntegrand.measurable_toFun_joint (Ψ : SimpleIntegrand ℱ ι) :
    Measurable fun x : ℝ × Ω => Ψ.toFun x.1 x.2 := by
  refine measurable_pi_iff.2 fun k => ?_
  have hk : ∀ x : ℝ × Ω, Ψ.toFun x.1 x.2 k =
      ∑ i : Fin Ψ.n, {x : ℝ × Ω | x.1 ∈ Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)}.indicator
        (fun x => Ψ.ξ i x.2 k) x := by
    intro x
    rw [SimpleIntegrand.toFun_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Set.indicator]
  simp_rw [hk]
  refine Finset.measurable_sum _ fun i _ => ?_
  have h1 : Measurable fun x : ℝ × Ω => Ψ.ξ i x.2 k :=
    ((measurable_pi_apply k).comp ((Ψ.meas i).mono (ℱ.le _) le_rfl)).comp measurable_snd
  exact h1.indicator (measurable_fst measurableSet_Ioc)

/-- Left-endpoint Riemann sums of a process `Θ`, as a simple integrand with `n + 1` steps. -/
def riemannSimple (ℱ : Filtration ℝ mΩ) (Θ : ℝ → Ω → ι → ℝ) (M T : ℝ) (hT : 0 ≤ T)
    (had : ∀ s ∈ Set.Icc 0 T, Measurable[ℱ s] (Θ s)) (hb : ∀ s ω k, |Θ s ω k| ≤ M) (n : ℕ) :
    SimpleIntegrand ℱ ι where
  n := n + 1
  t := fun i : Fin (n + 2) => T * ((i : ℕ) : ℝ) / ((n : ℝ) + 1)
  mono := fun i j hij => by
    have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this hT) hn.le
  nonneg := by
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_div, le_refl]
  ξ := fun i => Θ (T * (((i.castSucc : Fin (n + 2)) : ℕ) : ℝ) / ((n : ℝ) + 1))
  meas := fun i => by
    refine had _ ⟨by positivity, ?_⟩
    have hi : (((i.castSucc : Fin (n + 2)) : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
      have : ((i.castSucc : Fin (n + 2)) : ℕ) ≤ n + 1 := by omega
      exact_mod_cast this
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hn]
    nlinarith
  bdd := ⟨M, fun i ω k => hb _ ω k⟩

omit [Fintype ι] in
theorem riemann_mem_iff {T s : ℝ} (hT : 0 < T) (n : ℕ) (i : ℕ) :
    s ∈ Set.Ioc (T * (i : ℝ) / ((n : ℝ) + 1)) (T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ↔
      (i : ℝ) < s * ((n : ℝ) + 1) / T ∧ s * ((n : ℝ) + 1) / T ≤ (i : ℝ) + 1 := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Set.mem_Ioc, div_lt_iff₀ hN, le_div_iff₀ hN, lt_div_iff₀ hT, div_le_iff₀ hT]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

theorem riemannSimple_mem_iff (Θ : ℝ → Ω → ι → ℝ) {M T : ℝ} (hT : 0 < T)
    (had : ∀ s ∈ Set.Icc 0 T, Measurable[ℱ s] (Θ s)) (hb : ∀ s ω k, |Θ s ω k| ≤ M) (n : ℕ) (s : ℝ)
    (i : Fin (riemannSimple ℱ Θ M T hT.le had hb n).n) :
    s ∈ Set.Ioc ((riemannSimple ℱ Θ M T hT.le had hb n).t i.castSucc)
        ((riemannSimple ℱ Θ M T hT.le had hb n).t i.succ) ↔
      ((i : ℕ) : ℝ) < s * ((n : ℝ) + 1) / T ∧ s * ((n : ℝ) + 1) / T ≤ ((i : ℕ) : ℝ) + 1 := by
  have := riemann_mem_iff (s := s) hT n (i : ℕ)
  exact this

theorem riemannSimple_toFun_eq (Θ : ℝ → Ω → ι → ℝ) {M T : ℝ} (hT : 0 < T)
    (had : ∀ s ∈ Set.Icc 0 T, Measurable[ℱ s] (Θ s)) (hb : ∀ s ω k, |Θ s ω k| ≤ M) (n : ℕ)
    {s : ℝ} (hs : s ∈ Set.Ioc 0 T) (ω : Ω) :
    (riemannSimple ℱ Θ M T hT.le had hb n).toFun s ω =
      Θ (T * ((⌈s * ((n : ℝ) + 1) / T⌉₊ - 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ω := by
  funext k
  rw [SimpleIntegrand.toFun_apply]
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set x : ℝ := s * ((n : ℝ) + 1) / T with hx
  have hx0 : 0 < x := by have := hs.1; positivity
  have hxn : x ≤ (n : ℝ) + 1 := by
    rw [hx, div_le_iff₀ hT]; nlinarith [hs.2]
  set c : ℕ := ⌈x⌉₊ with hc
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hx0).ne'
  have hcn : c ≤ n + 1 := by
    rw [hc]; exact Nat.ceil_le.2 (by exact_mod_cast hxn)
  have hj1 : ((c - 1 : ℕ) : ℝ) < x := by
    have := Nat.ceil_lt_add_one hx0.le
    rw [Nat.cast_sub hc1]; simp only [Nat.cast_one]; linarith
  have hj2 : x ≤ ((c - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hc1]; simp only [Nat.cast_one]
    have := Nat.le_ceil x
    linarith
  have hjlt : c - 1 < n + 1 := by omega
  let j : Fin (riemannSimple ℱ Θ M T hT.le had hb n).n := ⟨c - 1, hjlt⟩
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
  · have hmem := (riemannSimple_mem_iff Θ hT had hb n s j).2 ⟨hj1, hj2⟩
    rw [Set.indicator_of_mem hmem]
    rfl
  · intro i _ hij
    refine Set.indicator_of_notMem ?_ _
    intro hi
    rw [riemannSimple_mem_iff Θ hT had hb n s i] at hi
    apply hij
    ext
    have h1 : ((i : ℕ) : ℝ) < ((c - 1 : ℕ) : ℝ) + 1 := hi.1.trans_le hj2
    have h2 : ((c - 1 : ℕ) : ℝ) < ((i : ℕ) : ℝ) + 1 := hj1.trans_le hi.2
    have h1' : (i : ℕ) < c - 1 + 1 := by exact_mod_cast h1
    have h2' : c - 1 < (i : ℕ) + 1 := by exact_mod_cast h2
    show (i : ℕ) = c - 1
    omega

omit [Fintype ι] in
theorem ceil_pred_bounds {x : ℝ} (hx0 : 0 < x) :
    ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x ∧ x ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 := by
  have hc1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hx0).ne'
  rw [Nat.cast_sub hc1]; simp only [Nat.cast_one]
  have h1 := Nat.ceil_lt_add_one hx0.le
  have h2 := Nat.le_ceil x
  constructor <;> linarith

omit [Fintype ι] in
theorem riemann_sigma_bounds {T s : ℝ} (hT : 0 < T) (hs : s ∈ Set.Ioc 0 T) (n : ℕ) :
    s - T / ((n : ℝ) + 1) ≤ T * ((⌈s * ((n : ℝ) + 1) / T⌉₊ - 1 : ℕ) : ℝ) / ((n : ℝ) + 1) ∧
      T * ((⌈s * ((n : ℝ) + 1) / T⌉₊ - 1 : ℕ) : ℝ) / ((n : ℝ) + 1) ≤ s := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx0 : 0 < s * ((n : ℝ) + 1) / T := by have := hs.1; positivity
  obtain ⟨h1, h2⟩ := ceil_pred_bounds hx0
  rw [lt_div_iff₀ hT] at h1
  rw [div_le_iff₀ hT] at h2
  constructor
  · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN]
    nlinarith
  · rw [div_le_iff₀ hN]
    nlinarith

theorem tendsto_sqIntegralOn_riemann [IsProbabilityMeasure P] (Θ : ℝ → Ω → ι → ℝ) {M T : ℝ}
    (hT : 0 < T) (had : ∀ s ∈ Set.Icc 0 T, Measurable[ℱ s] (Θ s))
    (hb : ∀ s ω k, |Θ s ω k| ≤ M)
    (hmeas : Measurable fun x : ℝ × Ω => Θ x.1 x.2) (hcont : ∀ ω, Continuous fun s => Θ s ω) :
    Tendsto (fun n : ℕ => sqIntegralOn P
      (fun s ω => (riemannSimple ℱ Θ M T hT.le had hb n).toFun s ω - Θ s ω) T) atTop (𝓝 0) := by
  set Ψ := fun n => riemannSimple ℱ Θ M T hT.le had hb n with hΨ
  refine tendsto_sqIntegralOn_of_dominated (D := fun _ _ => ∑ _k : ι, ENNReal.ofReal (2 * M) ^ 2) T
    (fun n => (Ψ n).measurable_toFun_joint) hmeas measurable_const ?_ ?_ ?_
  · exact lintegral_const_lt_top _ (ENNReal.sum_ne_top.2 fun _ _ =>
      ENNReal.pow_ne_top ENNReal.ofReal_ne_top) T
  · intro n s ω hs
    refine qn_le_of_abs_le fun k => ?_
    have hbk := hb s ω k
    have hM : 0 ≤ M := (abs_nonneg _).trans hbk
    simp only [Pi.sub_apply]
    rcases hs.1.eq_or_lt with h0 | hpos
    · have : (Ψ n).toFun s ω k = 0 := by
        rw [SimpleIntegrand.toFun_apply]
        refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem ?_ _
        intro hi
        have := hi.1
        have h2 : 0 ≤ (Ψ n).t i.castSucc := (Ψ n).nonneg.trans ((Ψ n).mono (Fin.zero_le _))
        rw [← h0] at this
        linarith
      rw [this]; simp only [zero_sub, abs_neg]; linarith
    · rw [riemannSimple_toFun_eq Θ hT had hb n ⟨hpos, hs.2⟩ ω]
      calc _ ≤ |Θ (T * ((⌈s * ((n : ℝ) + 1) / T⌉₊ - 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ω k| + |Θ s ω k| :=
            abs_sub _ _
        _ ≤ 2 * M := by linarith [hb (T * ((⌈s * ((n : ℝ) + 1) / T⌉₊ - 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ω k]
  · intro ω
    have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({0} : Set ℝ) :=
      (Set.countable_singleton (0 : ℝ)).ae_notMem volume
    filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem measurableSet_Icc] with s hs0 hsI
    have hpos : 0 < s := lt_of_le_of_ne hsI.1 (fun h => hs0 (by simp [← h]))
    have hsI' : s ∈ Set.Ioc 0 T := ⟨hpos, hsI.2⟩
    have hev : ∀ n : ℕ, (Ψ n).toFun s ω =
        Θ (T * ((⌈s * ((n : ℝ) + 1) / T⌉₊ - 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ω :=
      fun n => riemannSimple_toFun_eq Θ hT had hb n hsI' ω
    have hσ : Tendsto (fun n : ℕ => T * ((⌈s * ((n : ℝ) + 1) / T⌉₊ - 1 : ℕ) : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 s) := by
      have hT0 : Tendsto (fun n : ℕ => T * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
        (fun n => (riemann_sigma_bounds hT hsI' n).1) (fun n => (riemann_sigma_bounds hT hsI' n).2)
      simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := s)).sub hT0
    exact (((hcont ω).tendsto s).comp hσ).congr fun n => (hev n).symm

end Riemann


section Assembly

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ}

theorem sqIntegralOn_congr (P : Measure Ω) {F F' : ℝ → Ω → ι → ℝ} (T : ℝ)
    (h : ∀ s ∈ Set.Icc 0 T, ∀ ω, F s ω = F' s ω) : sqIntegralOn P F T = sqIntegralOn P F' T := by
  unfold sqIntegralOn
  refine lintegral_congr fun ω => ?_
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp only [h s hs ω]

theorem sqIntegralOn_eq_qn (P : Measure Ω) (F : ℝ → Ω → ι → ℝ) (T : ℝ) :
    sqIntegralOn P F T = ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, qn (F s ω)) ∂P := rfl

theorem sqIntegralOn_sub_le [IsProbabilityMeasure P] {A B C : ℝ → Ω → ι → ℝ} (T : ℝ)
    (hAB : Measurable fun x : ℝ × Ω => A x.1 x.2 - B x.1 x.2)
    (hBC : Measurable fun x : ℝ × Ω => B x.1 x.2 - C x.1 x.2) :
    sqIntegralOn P (fun s ω => A s ω - C s ω) T ≤
      2 * sqIntegralOn P (fun s ω => A s ω - B s ω) T +
        2 * sqIntegralOn P (fun s ω => B s ω - C s ω) T := by
  have h1 : Measurable fun x : ℝ × Ω => qn (A x.1 x.2 - B x.1 x.2) :=
    (measurable_qn (ι := ι)).comp hAB
  have h2 : Measurable fun x : ℝ × Ω => qn (B x.1 x.2 - C x.1 x.2) :=
    (measurable_qn (ι := ι)).comp hBC
  have e1 : ∀ ω, Measurable fun s => qn (A s ω - B s ω) := fun ω => by
    have := h1.comp (measurable_prodMk_right (y := ω))
    exact this
  have e2 : ∀ ω, Measurable fun s => qn (B s ω - C s ω) := fun ω => by
    have := h2.comp (measurable_prodMk_right (y := ω))
    exact this
  have m1 : Measurable fun ω => ∫⁻ s in Set.Icc 0 T, qn (A s ω - B s ω) := by
    have := h1.lintegral_prod_left' (μ := volume.restrict (Set.Icc (0:ℝ) T))
    exact this
  have m2 : Measurable fun ω => ∫⁻ s in Set.Icc 0 T, qn (B s ω - C s ω) := by
    have := h2.lintegral_prod_left' (μ := volume.restrict (Set.Icc (0:ℝ) T))
    exact this
  rw [sqIntegralOn_eq_qn, sqIntegralOn_eq_qn, sqIntegralOn_eq_qn]
  calc ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, qn (A s ω - C s ω)) ∂P
      ≤ ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, (2 * qn (A s ω - B s ω) + 2 * qn (B s ω - C s ω))) ∂P := by
        refine lintegral_mono fun ω => lintegral_mono fun s => ?_
        have := qn_add_le (A s ω - B s ω) (B s ω - C s ω)
        have e : A s ω - C s ω = (A s ω - B s ω) + (B s ω - C s ω) := by abel
        rw [e]; exact this
    _ = ∫⁻ ω, (2 * (∫⁻ s in Set.Icc 0 T, qn (A s ω - B s ω)) +
          2 * (∫⁻ s in Set.Icc 0 T, qn (B s ω - C s ω))) ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [lintegral_add_left ((e1 ω).const_mul 2), lintegral_const_mul _ (e1 ω),
          lintegral_const_mul _ (e2 ω)]
    _ = 2 * ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, qn (A s ω - B s ω)) ∂P +
        2 * ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, qn (B s ω - C s ω)) ∂P := by
        rw [lintegral_add_left (m1.const_mul 2), lintegral_const_mul _ m1,
          lintegral_const_mul _ m2]

/-- `F` is approximable on `[0, T]` by simple integrands in the `sqIntegralOn` seminorm. -/
def ApproxBy (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (T : ℝ) (F : ℝ → Ω → ι → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ Ψ : SimpleIntegrand ℱ ι,
    sqIntegralOn P (fun s ω => Ψ.toFun s ω - F s ω) T < ε

theorem ApproxBy.of_close [IsProbabilityMeasure P] {T : ℝ} {F : ℝ → Ω → ι → ℝ}
    (hF : Measurable fun x : ℝ × Ω => F x.1 x.2)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ G : ℝ → Ω → ι → ℝ, (Measurable fun x : ℝ × Ω => G x.1 x.2) ∧
      ApproxBy P ℱ T G ∧ sqIntegralOn P (fun s ω => G s ω - F s ω) T < ε) :
    ApproxBy P ℱ T F := by
  intro ε hε
  have hε4 : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨G, hG, hGa, hGF⟩ := h (ε / 4) hε4
  obtain ⟨Ψ, hΨ⟩ := hGa (ε / 4) hε4
  refine ⟨Ψ, lt_of_le_of_lt (sqIntegralOn_sub_le (P := P) (A := fun s ω => Ψ.toFun s ω) (B := G)
    (C := F) T (Ψ.measurable_toFun_joint.sub hG) (hG.sub hF)) ?_⟩
  have h1 : 2 * sqIntegralOn P (fun s ω => Ψ.toFun s ω - G s ω) T < 2 * (ε / 4) :=
    (ENNReal.mul_lt_mul_iff_right (by norm_num) (by norm_num)).2 hΨ
  have h2 : 2 * sqIntegralOn P (fun s ω => G s ω - F s ω) T < 2 * (ε / 4) :=
    (ENNReal.mul_lt_mul_iff_right (by norm_num) (by norm_num)).2 hGF
  refine (ENNReal.add_lt_add h1 h2).trans_eq ?_
  rw [← add_mul, show (2 : ℝ≥0∞) + 2 = 4 by norm_num]
  exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

theorem approxBy_of_riemann [IsProbabilityMeasure P] (Θ : ℝ → Ω → ι → ℝ) {M T : ℝ}
    (hT : 0 < T) (had : ∀ s ∈ Set.Icc 0 T, Measurable[ℱ s] (Θ s))
    (hb : ∀ s ω k, |Θ s ω k| ≤ M)
    (hmeas : Measurable fun x : ℝ × Ω => Θ x.1 x.2) (hcont : ∀ ω, Continuous fun s => Θ s ω) :
    ApproxBy P ℱ T Θ := by
  intro ε hε
  have := tendsto_sqIntegralOn_riemann (P := P) Θ hT had hb hmeas hcont
  obtain ⟨n, hn⟩ := ((tendsto_order.1 this).2 ε hε).exists
  exact ⟨_, hn⟩

theorem approxBy_of_bounded [IsProbabilityMeasure P] {G : ℝ → Ω → ι → ℝ} {M T : ℝ} (hT : 0 < T)
    (hG : Measurable fun x : ℝ × Ω => G x.1 x.2) (hb : ∀ s ω k, |G s ω k| ≤ M)
    (hA : ∀ s ∈ Set.Icc 0 T, ∀ a, 0 ≤ a → a ≤ s → ∀ k,
      Measurable[ℱ s] fun ω => ∫ r in Set.Ioc 0 a, G r ω k) :
    ApproxBy P ℱ T G := by
  refine ApproxBy.of_close hG fun ε hε => ?_
  have := tendsto_sqIntegralOn_molG (P := P) hG hb T
  obtain ⟨m, hm⟩ := ((tendsto_order.1 this).2 ε hε).exists
  have hh : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  refine ⟨molG G (1 / ((m : ℝ) + 1)), measurable_molG hG hb _, ?_, hm⟩
  refine approxBy_of_riemann (M := M) _ hT (fun s hs => ?_)
    (fun s ω k => abs_molG_le hG hb hh s ω k) (measurable_molG hG hb _)
    (fun ω => continuous_pi fun k => continuous_molG hG hb _ ω k)
  exact measurable_molG_of_primitive hs.1 hh (hA s hs)

theorem measurable_progressive_min {Φ : ℝ → Ω → ι → ℝ} (hΦ : IsProgressive ℱ Φ) (T : ℝ) :
    Measurable fun x : ℝ × Ω => Φ (min x.1 T) x.2 := by
  have hq : Measurable[Prod.instMeasurableSpace, Subtype.instMeasurableSpace.prod (ℱ T)]
      fun x : ℝ × Ω => ((⟨min x.1 T, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic T), x.2) :=
    Measurable.prodMk (Measurable.subtype_mk (measurable_fst.min measurable_const))
      (measurable_snd.mono le_rfl (ℱ.le T))
  exact (hΦ T).comp hq

/-- The trivial simple integrand. -/
def zeroSimple (ℱ : Filtration ℝ mΩ) : SimpleIntegrand ℱ ι where
  n := 0
  t := fun _ => 0
  mono := fun _ _ _ => le_rfl
  nonneg := le_rfl
  ξ := fun i => i.elim0
  meas := fun i => i.elim0
  bdd := ⟨0, fun i => i.elim0⟩

end Assembly

/-- Every progressively measurable integrand with `E ∫_0^T |Φ|² < ∞` is the `L²([0,T] × Ω)`-limit
of simple integrands. -/
theorem exists_simple_approx (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (Φ : ℝ → Ω → ι → ℝ) (hΦ : IsProgressive ℱ Φ) (T : ℝ) (hT : sqIntegralOn P Φ T < ∞) :
    ∃ Ψ : ℕ → SimpleIntegrand ℱ ι,
      Tendsto (fun n => sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) T) atTop (𝓝 0) := by
  rcases le_or_gt T 0 with hT0 | hTpos
  · refine ⟨fun _ => zeroSimple ℱ, ?_⟩
    have hz : ∀ F : ℝ → Ω → ι → ℝ, sqIntegralOn P F T = 0 := fun F => by
      unfold sqIntegralOn
      have : (volume : Measure ℝ).restrict (Set.Icc 0 T) = 0 :=
        Measure.restrict_eq_zero.2 (by simpa using hT0)
      simp [this]
    simp only [hz]
    exact tendsto_const_nhds
  · set Φh : ℝ → Ω → ι → ℝ := fun s ω => Φ (min s T) ω with hΦh
    have hΦm : Measurable fun x : ℝ × Ω => Φh x.1 x.2 := measurable_progressive_min hΦ T
    have hcongr : ∀ F : ℝ → Ω → ι → ℝ, sqIntegralOn P (fun s ω => F s ω - Φ s ω) T =
        sqIntegralOn P (fun s ω => F s ω - Φh s ω) T := fun F =>
      sqIntegralOn_congr P T fun s hs ω => by simp [hΦh, min_eq_left hs.2]
    have hfin : ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, qn (Φh s ω)) ∂P ≠ ∞ := by
      have h0 : sqIntegralOn P (fun s ω => 0 - Φ s ω) T = sqIntegralOn P Φ T := by
        unfold sqIntegralOn; simp
      have h1 := hcongr (fun _ _ => 0)
      rw [h0] at h1
      have h2 : sqIntegralOn P (fun s ω => 0 - Φh s ω) T = sqIntegralOn P Φh T := by
        unfold sqIntegralOn; simp
      rw [h2] at h1
      rw [← sqIntegralOn_eq_qn]
      rw [← h1]; exact hT.ne
    have hAppr : ApproxBy P ℱ T Φh := by
      refine ApproxBy.of_close hΦm fun ε hε => ?_
      obtain ⟨n, hn⟩ := ((tendsto_order.1 (tendsto_sqIntegralOn_clip (P := P) hΦm hfin)).2 ε hε).exists
      refine ⟨fun s ω => clipv n (Φh s ω), (measurable_clipv _).comp hΦm, ?_, hn⟩
      refine approxBy_of_bounded (M := n) hTpos ((measurable_clipv _).comp hΦm)
        (fun s ω k => abs_clip_le (Nat.cast_nonneg n)) ?_
      intro s hs a ha has k
      have e : (fun ω => ∫ r in Set.Ioc 0 a, clipv n (Φh r ω) k) =
          fun ω => ∫ r in Set.Ioc 0 a, (fun x : ℝ => max (-(n : ℝ)) (min (n : ℝ) x)) (Φ r ω k) := by
        funext ω
        refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        simp [clipv, hΦh, min_eq_left (hr.2.trans (has.trans hs.2))]
      rw [e]
      exact measurable_integral_of_progressive hΦ
        (measurable_const.max (measurable_const.min measurable_id)) s a has k
    choose Ψ hΨ using fun n : ℕ => hAppr ((n : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
    refine ⟨Ψ, ?_⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun n => bot_le) (fun n => ?_)
    rw [hcongr]
    exact (hΨ n).le

end HRS
