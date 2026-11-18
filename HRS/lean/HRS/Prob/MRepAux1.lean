import HRS.Prob.HilbertMartingale

/-!
# MREP, part 1: elementary stochastic integrals against a family of continuous martingales

A *noise* is a family `N^α` of continuous `L²` martingales with covariation densities `Q_{αβ}`:
`N^α N^β - ∫_0^· Q_{αβ}` is a martingale.  This file proves the elementary-integral calculus
(martingale property, compensator of products, cross-covariation with a test martingale).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

open HRS.SimpleIntegrand

section StopMul

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}

/-- If `U V` are `L²` martingales and `UV - Λ` is a martingale then so is the stopped version
`U_{c∧s} V_s - Λ_{c∧s}`. -/
theorem martingale_stop_mul {U V Λ : ℝ → Ω → ℝ} (hU : Martingale U ℱ P) (hV : Martingale V ℱ P)
    (hU2 : ∀ t, MemLp (U t) 2 P) (hV2 : ∀ t, MemLp (V t) 2 P)
    (hΛ : Martingale (fun t ω => U t ω * V t ω - Λ t ω) ℱ P) (c : ℝ) :
    Martingale (fun s ω => U (min c s) ω * V s ω - Λ (min c s) ω) ℱ P := by
  have hUV : ∀ s t, Integrable (fun ω => U s ω * V t ω) P :=
    fun s t => (hU2 s).integrable_mul (hV2 t)
  have hΛe : ∀ s, Λ s = fun ω => U s ω * V s ω - (U s ω * V s ω - Λ s ω) := by
    intro s; funext ω; ring
  have hΛm : ∀ s, StronglyMeasurable[ℱ s] (Λ s) := by
    intro s
    rw [hΛe s]
    exact ((hU.stronglyAdapted s).mul (hV.stronglyAdapted s)).sub (hΛ.stronglyAdapted s)
  have hΛi : ∀ s, Integrable (Λ s) P := by
    intro s
    rw [hΛe s]
    exact (hUV s s).sub (hΛ.integrable s)
  have case1 : ∀ s t, c ≤ s → s ≤ t →
      P[fun ω => U c ω * V t ω - Λ c ω | ℱ s] =ᵐ[P] fun ω => U c ω * V s ω - Λ c ω := by
    intro s t hcs hst
    have hUc : StronglyMeasurable[ℱ s] (U c) := (hU.stronglyAdapted c).mono (ℱ.mono hcs)
    have h1 : P[fun ω => U c ω * V t ω - Λ c ω | ℱ s] =ᵐ[P]
        P[fun ω => U c ω * V t ω | ℱ s] - P[Λ c | ℱ s] :=
      condExp_sub (hUV c t) (hΛi c) (ℱ s)
    have h2 : P[fun ω => U c ω * V t ω | ℱ s] =ᵐ[P] fun ω => U c ω * P[V t | ℱ s] ω :=
      condExp_mul_of_stronglyMeasurable_left hUc (hUV c t) (hV.integrable t)
    have h3 : P[Λ c | ℱ s] = Λ c :=
      condExp_of_stronglyMeasurable (ℱ.le s) ((hΛm c).mono (ℱ.mono hcs)) (hΛi c)
    have h4 := hV.condExp_ae_eq hst
    filter_upwards [h1, h2, h4] with ω e1 e2 e4
    simp only [Pi.sub_apply] at e1
    rw [e1, e2, e4, h3]
  refine ⟨fun s => ?_, fun s t hst => ?_⟩
  · exact (((hU.stronglyAdapted (min c s)).mono (ℱ.mono (min_le_right c s))).mul
      (hV.stronglyAdapted s)).sub ((hΛm (min c s)).mono (ℱ.mono (min_le_right c s)))
  · by_cases hcs : c ≤ s
    · simp only [min_eq_left hcs, min_eq_left (hcs.trans hst)]
      exact case1 s t hcs hst
    · rw [not_le] at hcs
      simp only [min_eq_right hcs.le]
      by_cases hct : t ≤ c
      · simp only [min_eq_right hct]
        exact hΛ.condExp_ae_eq hst
      · rw [not_le] at hct
        simp only [min_eq_left hct.le]
        have h1 := condExp_condExp_of_le (μ := P)
          (f := fun ω => U c ω * V t ω - Λ c ω) (ℱ.mono hcs.le) (ℱ.le c)
        have h2 := condExp_congr_ae (m := ℱ s) (case1 c t le_rfl hct.le)
        have h3 := hΛ.condExp_ae_eq hcs.le
        exact (h1.symm.trans h2).trans h3

/-- A bounded `ℱ a`-measurable multiple of a stopped-difference of compensated products. -/
theorem martingale_step_mul {U V Λ : ℝ → Ω → ℝ} (hU : Martingale U ℱ P) (hV : Martingale V ℱ P)
    (hU2 : ∀ t, MemLp (U t) 2 P) (hV2 : ∀ t, MemLp (V t) 2 P)
    (hΛ : Martingale (fun t ω => U t ω * V t ω - Λ t ω) ℱ P) {a b : ℝ} (hab : a ≤ b)
    {ξ : Ω → ℝ} (hξ : Measurable[ℱ a] ξ) {C : ℝ} (hC : ∀ ω, |ξ ω| ≤ C) :
    Martingale (fun s ω => ξ ω * ((U (min b s) ω - U (min a s) ω) * V s ω -
      (Λ (min b s) ω - Λ (min a s) ω))) ℱ P := by
  have hY : Martingale (fun s ω => (U (min b s) ω * V s ω - Λ (min b s) ω) -
      (U (min a s) ω * V s ω - Λ (min a s) ω)) ℱ P :=
    (martingale_stop_mul hU hV hU2 hV2 hΛ b).sub (martingale_stop_mul hU hV hU2 hV2 hΛ a)
  have h0 : ∀ s ≤ a, (fun ω => (U (min b s) ω * V s ω - Λ (min b s) ω) -
      (U (min a s) ω * V s ω - Λ (min a s) ω)) = 0 := by
    intro s hs
    funext ω
    simp [min_eq_right hs, min_eq_right (hs.trans hab)]
  have hint : ∀ s, Integrable (fun ω => ξ ω * ((U (min b s) ω * V s ω - Λ (min b s) ω) -
      (U (min a s) ω * V s ω - Λ (min a s) ω))) P := by
    intro s
    have this := hY.integrable s
    refine this.bdd_mul (c := C) (hξ.mono (ℱ.le a) le_rfl).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    simpa [Real.norm_eq_abs] using hC ω
  have := martingale_mul_left (P := P) (ℱ := ℱ) (Y := fun s ω => (U (min b s) ω * V s ω - Λ (min b s) ω) -
      (U (min a s) ω * V s ω - Λ (min a s) ω)) hY (a := a) h0
    hξ.stronglyMeasurable hint
  have e : (fun s ω => ξ ω * ((U (min b s) ω - U (min a s) ω) * V s ω -
      (Λ (min b s) ω - Λ (min a s) ω))) = fun s ω => ξ ω * ((U (min b s) ω * V s ω - Λ (min b s) ω) -
      (U (min a s) ω * V s ω - Λ (min a s) ω)) := by
    funext s ω; ring
  rw [e]; exact this

end StopMul

section Elem

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} {κ : Type*} [Fintype κ]

/-- A noise: a family of continuous `L²` martingales `N^α` with covariation densities `Q_{αβ}`. -/
structure IsNoise (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (N : ℝ → Ω → A → ℝ)
    (Q : ℝ → Ω → A → A → ℝ) : Prop where
  mart : ∀ α, Martingale (fun t ω => N t ω α) ℱ P
  cont : ∀ ω α, Continuous fun t => N t ω α
  sq : ∀ t α, MemLp (fun ω => N t ω α) 2 P
  Qmeas : ∀ α β, Measurable (fun p : ℝ × Ω => Q p.1 p.2 α β)
  Qint : ∀ᵐ ω ∂P, ∀ α β (t : ℝ), IntegrableOn (fun r => Q r ω α β) (Set.Icc 0 t)
  cov : ∀ α β, Martingale (fun t ω => N t ω α * N t ω β - ∫ r in Set.Icc 0 t, Q r ω α β) ℱ P

/-- The elementary integral `∑_i ∑_k ξ_i^k (N^{a k}_{t_{i+1} ∧ s} - N^{a k}_{t_i ∧ s})`. -/
def nInt (N : ℝ → Ω → A → ℝ) (a : κ → A) (Ψ : SimpleIntegrand ℱ κ) : ℝ → Ω → ℝ :=
  fun s ω => ∑ i : Fin Ψ.n, ∑ k, Ψ.ξ i ω k *
    (N (min (Ψ.t i.succ) s) ω (a k) - N (min (Ψ.t i.castSucc) s) ω (a k))

theorem tnn (Ψ : SimpleIntegrand ℱ κ) (i : Fin (Ψ.n + 1)) : 0 ≤ Ψ.t i :=
  Ψ.nonneg.trans (Ψ.mono (Fin.zero_le i))

theorem nInt_of_nonpos (N : ℝ → Ω → A → ℝ) (a : κ → A) (Ψ : SimpleIntegrand ℱ κ) {s : ℝ}
    (hs : s ≤ 0) (ω : Ω) : nInt N a Ψ s ω = 0 := by
  unfold nInt
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
  rw [min_eq_right (hs.trans (tnn Ψ _)), min_eq_right (hs.trans (tnn Ψ _))]
  simp

theorem continuous_nInt {N : ℝ → Ω → A → ℝ} (hc : ∀ ω α, Continuous fun t => N t ω α) (a : κ → A)
    (Ψ : SimpleIntegrand ℱ κ) (ω : Ω) : Continuous fun s => nInt N a Ψ s ω := by
  have h1 : ∀ (c : ℝ) (k : κ), Continuous fun s : ℝ => N (min c s) ω (a k) := fun c k =>
    (hc ω (a k)).comp (continuous_const.min continuous_id)
  show Continuous fun s : ℝ => ∑ i : Fin Ψ.n, ∑ k, Ψ.ξ i ω k *
    (N (min (Ψ.t i.succ) s) ω (a k) - N (min (Ψ.t i.castSucc) s) ω (a k))
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro k _
  exact (continuous_const (y := Ψ.ξ i ω k)).mul ((h1 _ k).sub (h1 _ k))

/-- A bounded `ℱ a`-measurable multiple of an increment of a martingale after time `a`. -/
theorem martingale_step_one {U : ℝ → Ω → ℝ} (hU : Martingale U ℱ P) {a b : ℝ} (hab : a ≤ b)
    {ξ : Ω → ℝ} (hξ : Measurable[ℱ a] ξ) {C : ℝ} (hC : ∀ ω, |ξ ω| ≤ C) :
    Martingale (fun s ω => ξ ω * (U (min b s) ω - U (min a s) ω)) ℱ P := by
  have hN : Martingale (fun s ω => U (min b s) ω - U (min a s) ω) ℱ P :=
    (martingale_stopAt hU b).sub (martingale_stopAt hU a)
  refine martingale_mul_left hN (a := a) (fun s hs => by
      funext ω
      simp [min_eq_right hs, min_eq_right (hs.trans hab)]) hξ.stronglyMeasurable fun s => ?_
  exact (hN.integrable s).bdd_mul ((hξ.mono (ℱ.le a) le_rfl).aestronglyMeasurable)
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC ω)

theorem martingale_nInt {N : ℝ → Ω → A → ℝ} (hN : ∀ α, Martingale (fun t ω => N t ω α) ℱ P)
    (a : κ → A) (Ψ : SimpleIntegrand ℱ κ) : Martingale (nInt N a Ψ) ℱ P := by
  obtain ⟨C, hC⟩ := Ψ.bdd
  have h : ∀ i : Fin Ψ.n, ∀ k, Martingale (fun s ω => Ψ.ξ i ω k *
      (N (min (Ψ.t i.succ) s) ω (a k) - N (min (Ψ.t i.castSucc) s) ω (a k))) ℱ P := by
    intro i k
    exact martingale_step_one (hN (a k)) (Ψ.mono (Fin.castSucc_le_succ i))
      ((measurable_pi_apply k).comp (Ψ.meas i)) (C := C) (fun ω => hC i ω k)
  have := HRS.SimpleIntegrand.martingale_finset_sum (P := P) (ℱ := ℱ) Finset.univ (f := fun (i : Fin Ψ.n) s ω =>
    ∑ k, Ψ.ξ i ω k * (N (min (Ψ.t i.succ) s) ω (a k) - N (min (Ψ.t i.castSucc) s) ω (a k)))
    (fun i _ => HRS.SimpleIntegrand.martingale_finset_sum Finset.univ (fun k _ => h i k))
  exact this

theorem memLp_nInt {N : ℝ → Ω → A → ℝ} (hN2 : ∀ t α, MemLp (fun ω => N t ω α) 2 P)
    (a : κ → A) (Ψ : SimpleIntegrand ℱ κ) (s : ℝ) : MemLp (nInt N a Ψ s) 2 P := by
  obtain ⟨C, hC⟩ := Ψ.bdd
  show MemLp (fun ω => ∑ i : Fin Ψ.n, ∑ k, Ψ.ξ i ω k *
    (N (min (Ψ.t i.succ) s) ω (a k) - N (min (Ψ.t i.castSucc) s) ω (a k))) 2 P
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun k _ => ?_
  have hξ : MemLp (fun ω => Ψ.ξ i ω k) ⊤ P :=
    memLp_top_of_bound ((measurable_pi_apply k).comp ((Ψ.meas i).mono (ℱ.le _) le_rfl)).aestronglyMeasurable
      C (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hC i ω k)
  have hd := (hN2 (min (Ψ.t i.succ) s) (a k)).sub (hN2 (min (Ψ.t i.castSucc) s) (a k))
  exact hξ.fun_mul hd

/-- Cross covariation of an elementary integral with a test martingale (step form). -/
theorem martingale_nInt_mul_step {N : ℝ → Ω → A → ℝ}
    (hN : ∀ α, Martingale (fun t ω => N t ω α) ℱ P) (hN2 : ∀ t α, MemLp (fun ω => N t ω α) 2 P)
    (a : κ → A) (Ψ : SimpleIntegrand ℱ κ) {V : ℝ → Ω → ℝ} (hV : Martingale V ℱ P)
    (hV2 : ∀ t, MemLp (V t) 2 P) {Λ : κ → ℝ → Ω → ℝ}
    (hΛ : ∀ k, Martingale (fun t ω => N t ω (a k) * V t ω - Λ k t ω) ℱ P) :
    Martingale (fun s ω => nInt N a Ψ s ω * V s ω - ∑ i : Fin Ψ.n, ∑ k, Ψ.ξ i ω k *
      (Λ k (min (Ψ.t i.succ) s) ω - Λ k (min (Ψ.t i.castSucc) s) ω)) ℱ P := by
  obtain ⟨C, hC⟩ := Ψ.bdd
  have h : ∀ (i : Fin Ψ.n) k, Martingale (fun s ω => Ψ.ξ i ω k *
      ((N (min (Ψ.t i.succ) s) ω (a k) - N (min (Ψ.t i.castSucc) s) ω (a k)) * V s ω -
      (Λ k (min (Ψ.t i.succ) s) ω - Λ k (min (Ψ.t i.castSucc) s) ω))) ℱ P := by
    intro i k
    exact martingale_step_mul (U := fun t ω => N t ω (a k)) (hN (a k)) hV (fun t => hN2 t (a k)) hV2
      (hΛ k) (Ψ.mono (Fin.castSucc_le_succ i)) ((measurable_pi_apply k).comp (Ψ.meas i))
      (C := C) (fun ω => hC i ω k)
  have := HRS.SimpleIntegrand.martingale_finset_sum (P := P) (ℱ := ℱ) Finset.univ
    (f := fun (i : Fin Ψ.n) s ω => ∑ k, Ψ.ξ i ω k *
      ((N (min (Ψ.t i.succ) s) ω (a k) - N (min (Ψ.t i.castSucc) s) ω (a k)) * V s ω -
      (Λ k (min (Ψ.t i.succ) s) ω - Λ k (min (Ψ.t i.castSucc) s) ω)))
    (fun i _ => HRS.SimpleIntegrand.martingale_finset_sum Finset.univ (fun k _ => h i k))
  have e : (fun s ω => nInt N a Ψ s ω * V s ω - ∑ i : Fin Ψ.n, ∑ k, Ψ.ξ i ω k *
      (Λ k (min (Ψ.t i.succ) s) ω - Λ k (min (Ψ.t i.castSucc) s) ω)) =
      fun s ω => ∑ i : Fin Ψ.n, ∑ k, Ψ.ξ i ω k *
      ((N (min (Ψ.t i.succ) s) ω (a k) - N (min (Ψ.t i.castSucc) s) ω (a k)) * V s ω -
      (Λ k (min (Ψ.t i.succ) s) ω - Λ k (min (Ψ.t i.castSucc) s) ω)) := by
    funext s ω
    simp only [nInt, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e]; exact this

lemma setIntegral_Icc_diff {f : ℝ → ℝ} {c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c')
    (hf : IntegrableOn f (Set.Icc 0 c')) :
    ∫ r in Set.Icc 0 c', f r = (∫ r in Set.Icc 0 c, f r) + ∫ r in Set.Ioc c c', f r := by
  have hu : Set.Icc 0 c' = Set.Icc 0 c ∪ Set.Ioc c c' := (Set.Icc_union_Ioc_eq_Icc hc hcc).symm
  conv_lhs => rw [hu]
  exact setIntegral_union (Set.disjoint_left.2 fun x hx hx' => not_le.2 hx'.1 hx.2) measurableSet_Ioc
    (hf.mono_set (Set.Icc_subset_Icc_right hcc))
    (hf.mono_set (fun x hx => ⟨hc.trans hx.1.le, hx.2⟩))

lemma integral_Icc_indicator_Ioc {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ t, IntegrableOn f (Set.Icc 0 t)) (s : ℝ) :
    ∫ r in Set.Icc 0 s, (Set.Ioc a b).indicator f r =
      (∫ r in Set.Icc 0 (min b s), f r) - ∫ r in Set.Icc 0 (min a s), f r := by
  by_cases hs : s < 0
  · have h1 : min b s = s := min_eq_right (hs.le.trans (ha.trans hab))
    have h2 : min a s = s := min_eq_right (hs.le.trans ha)
    have h3 : Set.Icc (0 : ℝ) s = ∅ := Set.Icc_eq_empty (not_le.2 hs)
    simp [h1, h2, h3]
  · rw [not_lt] at hs
    rw [setIntegral_indicator measurableSet_Ioc]
    have hset : Set.Icc 0 s ∩ Set.Ioc a b = Set.Ioc (min a s) (min b s) := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc, lt_min_iff, le_min_iff]
      constructor
      · rintro ⟨⟨h0, hrs⟩, hra, hrb⟩
        refine ⟨?_, hrb, hrs⟩
        rcases le_total a s with h | h
        · rw [min_eq_left h]; exact hra
        · rw [min_eq_right h]; exact lt_of_le_of_lt h hra |>.trans_le le_rfl |> fun h' => by
            exact absurd hrs (not_le.2 (lt_of_le_of_lt h hra))
      · rintro ⟨hlow, hrb, hrs⟩
        have hmin : 0 ≤ min a s := le_min ha hs
        refine ⟨⟨(hmin.trans hlow.le), hrs⟩, ?_, hrb⟩
        rcases le_total a s with h | h
        · rw [min_eq_left h] at hlow; exact hlow
        · rw [min_eq_right h] at hlow; exact absurd hrs (not_le.2 hlow)
    rw [hset]
    have h1 := setIntegral_Icc_diff (f := f) (le_min ha hs) (min_le_min_right s hab) (hf (min b s))
    rw [h1]; ring

lemma step_sum_eq_integral {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
    {κ : Type*} [Fintype κ] (Ψ : SimpleIntegrand ℱ κ) {q : κ → ℝ → Ω → ℝ} (ω : Ω)
    (hqi : ∀ k t, IntegrableOn (fun r => q k r ω) (Set.Icc 0 t)) (s : ℝ) :
    ∑ i : Fin Ψ.n, ∑ k, Ψ.ξ i ω k * ((∫ r in Set.Icc 0 (min (Ψ.t i.succ) s), q k r ω) -
      ∫ r in Set.Icc 0 (min (Ψ.t i.castSucc) s), q k r ω) =
      ∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k * q k r ω := by
  have e1 : ∀ r, ∑ k, Ψ.toFun r ω k * q k r ω = ∑ k, ∑ i : Fin Ψ.n,
      (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator (fun r => Ψ.ξ i ω k * q k r ω) r := by
    intro r
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [SimpleIntegrand.toFun_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : r ∈ Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ) <;> simp [h]
  simp_rw [e1]
  have hint : ∀ (k : κ) (i : Fin Ψ.n), Integrable ((Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator
      (fun r => Ψ.ξ i ω k * q k r ω)) (volume.restrict (Set.Icc 0 s)) := fun k i =>
    ((hqi k s).const_mul (Ψ.ξ i ω k)).indicator measurableSet_Ioc
  rw [integral_finset_sum _ (fun k _ => integrable_finsetSum _ fun i _ => hint k i)]
  have hk : ∀ k : κ, ∫ r in Set.Icc 0 s, ∑ i : Fin Ψ.n,
      (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator (fun r => Ψ.ξ i ω k * q k r ω) r =
      ∑ i : Fin Ψ.n, ∫ r in Set.Icc 0 s,
      (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator (fun r => Ψ.ξ i ω k * q k r ω) r :=
    fun k => integral_finset_sum _ (fun i _ => hint k i)
  simp_rw [hk]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  have e2 : (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator (fun r => Ψ.ξ i ω k * q k r ω) =
      fun r => Ψ.ξ i ω k * (Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ)).indicator (fun r => q k r ω) r := by
    funext r; by_cases h : r ∈ Set.Ioc (Ψ.t i.castSucc) (Ψ.t i.succ) <;> simp [h]
  rw [e2, integral_const_mul,
    integral_Icc_indicator_Ioc (tnn Ψ _) (Ψ.mono (Fin.castSucc_le_succ i)) (hqi k) s]

theorem martingale_congr_complete (hℱ : IsCompleteFiltration P ℱ) {X Y : ℝ → Ω → ℝ}
    (hX : Martingale X ℱ P) (hYm : ∀ t, Measurable (Y t)) (h : ∀ t, X t =ᵐ[P] Y t) :
    Martingale Y ℱ P := by
  refine hX.congr (fun t => ?_) h
  have hm : Measurable[ℱ t] (Y t) :=
    hℱ.measurable_of_ae_eq_aux t ((hX.stronglyAdapted t).measurable) (hYm t) (h t)
  exact hm.stronglyMeasurable

theorem measurable_setIntegral_Icc {g : ℝ → Ω → ℝ} (hg : Measurable fun p : ℝ × Ω => g p.1 p.2)
    (s : ℝ) : Measurable fun ω => ∫ r in Set.Icc 0 s, g r ω := by
  have h1 : StronglyMeasurable fun p : Ω × ℝ => g p.2 p.1 :=
    (hg.comp measurable_swap).stronglyMeasurable
  exact (h1.integral_prod_right' (ν := volume.restrict (Set.Icc 0 s))).measurable

/-- Cross covariation of an elementary integral with a test martingale (integral form). -/
theorem martingale_nInt_mul (hℱ : IsCompleteFiltration P ℱ) {N : ℝ → Ω → A → ℝ}
    (hN : ∀ α, Martingale (fun t ω => N t ω α) ℱ P) (hN2 : ∀ t α, MemLp (fun ω => N t ω α) 2 P)
    (a : κ → A) (Ψ : SimpleIntegrand ℱ κ) {V : ℝ → Ω → ℝ} (hV : Martingale V ℱ P)
    (hV2 : ∀ t, MemLp (V t) 2 P) {q : κ → ℝ → Ω → ℝ}
    (hqm : ∀ k, Measurable fun p : ℝ × Ω => q k p.1 p.2)
    (hqi : ∀ᵐ ω ∂P, ∀ k t, IntegrableOn (fun r => q k r ω) (Set.Icc 0 t))
    (hΛ : ∀ k, Martingale (fun t ω => N t ω (a k) * V t ω - ∫ r in Set.Icc 0 t, q k r ω) ℱ P) :
    Martingale (fun s ω => nInt N a Ψ s ω * V s ω -
      ∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k * q k r ω) ℱ P := by
  have h1 := martingale_nInt_mul_step hN hN2 a Ψ hV hV2
    (Λ := fun k t ω => ∫ r in Set.Icc 0 t, q k r ω) hΛ
  refine martingale_congr_complete hℱ h1 (fun t => ?_) (fun t => ?_)
  · have hn : Measurable (nInt N a Ψ t) :=
      ((martingale_nInt hN a Ψ).stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl
    have hv : Measurable (V t) := (hV.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl
    refine (hn.mul hv).sub (measurable_setIntegral_Icc ?_ t)
    refine Finset.measurable_sum _ fun k _ => ?_
    have := (measurable_pi_apply k).comp Ψ.measurable_toFun_joint
    exact this.mul (hqm k)
  · filter_upwards [hqi] with ω hω
    rw [step_sum_eq_integral Ψ ω hω t]

/-- Compensated product of two elementary integrals. -/
theorem martingale_nInt_mul_nInt {κ' : Type*} [Fintype κ'] (hℱ : IsCompleteFiltration P ℱ)
    {N : ℝ → Ω → A → ℝ} {Q : ℝ → Ω → A → A → ℝ} (hN : IsNoise P ℱ N Q)
    (a : κ → A) (a' : κ' → A) (Ψ : SimpleIntegrand ℱ κ) (Ψ' : SimpleIntegrand ℱ κ') :
    Martingale (fun s ω => nInt N a Ψ s ω * nInt N a' Ψ' s ω -
      ∫ r in Set.Icc 0 s, ∑ k, ∑ l, Ψ.toFun r ω k * Ψ'.toFun r ω l * Q r ω (a k) (a' l)) ℱ P := by
  obtain ⟨C, hC⟩ := HRS.SimpleIntegrand.toFun_bdd Ψ
  obtain ⟨C', hC'⟩ := HRS.SimpleIntegrand.toFun_bdd Ψ'
  -- step 1: integrator Ψ against a single coordinate of the second noise
  have step1 : ∀ l, Martingale (fun s ω => nInt N a Ψ s ω * N s ω (a' l) -
      ∫ r in Set.Icc 0 s, ∑ k, Ψ.toFun r ω k * Q r ω (a k) (a' l)) ℱ P := fun l =>
    martingale_nInt_mul hℱ hN.mart hN.sq a Ψ (hN.mart (a' l)) (fun t => hN.sq t (a' l))
      (q := fun k r ω => Q r ω (a k) (a' l)) (fun k => hN.Qmeas _ _)
      (by filter_upwards [hN.Qint] with ω hω k t using hω _ _ t) (fun k => hN.cov (a k) (a' l))
  -- step 2: integrator Ψ' against the test martingale `nInt Ψ`
  have hqm : ∀ l, Measurable fun p : ℝ × Ω => ∑ k, Ψ.toFun p.1 p.2 k * Q p.1 p.2 (a k) (a' l) := by
    intro l
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((measurable_pi_apply k).comp Ψ.measurable_toFun_joint).mul (hN.Qmeas _ _)
  have hqi : ∀ᵐ ω ∂P, ∀ l t, IntegrableOn
      (fun r => ∑ k, Ψ.toFun r ω k * Q r ω (a k) (a' l)) (Set.Icc 0 t) := by
    filter_upwards [hN.Qint] with ω hω l t
    refine integrable_finsetSum _ fun k _ => ?_
    refine (hω (a k) (a' l) t).bdd_mul (c := C) ?_ (ae_of_all _ fun r => ?_)
    · exact (((measurable_pi_apply k).comp Ψ.measurable_toFun_joint).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · simpa [Real.norm_eq_abs] using hC r ω k
  have step2 := martingale_nInt_mul hℱ hN.mart hN.sq a' Ψ' (martingale_nInt hN.mart a Ψ)
    (fun t => memLp_nInt hN.sq a Ψ t) hqm hqi (fun l => by
      have e1 : (fun t ω => N t ω (a' l) * nInt N a Ψ t ω -
          ∫ r in Set.Icc 0 t, ∑ k, Ψ.toFun r ω k * Q r ω (a k) (a' l)) =
          fun t ω => nInt N a Ψ t ω * N t ω (a' l) -
          ∫ r in Set.Icc 0 t, ∑ k, Ψ.toFun r ω k * Q r ω (a k) (a' l) := by
        funext t ω; ring
      rw [e1]; exact step1 l)
  have e2 : (fun s ω => nInt N a Ψ s ω * nInt N a' Ψ' s ω -
      ∫ r in Set.Icc 0 s, ∑ k, ∑ l, Ψ.toFun r ω k * Ψ'.toFun r ω l * Q r ω (a k) (a' l)) =
      fun s ω => nInt N a' Ψ' s ω * nInt N a Ψ s ω -
      ∫ r in Set.Icc 0 s, ∑ l, Ψ'.toFun r ω l * ∑ k, Ψ.toFun r ω k * Q r ω (a k) (a' l) := by
    funext s ω
    rw [mul_comm]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    beta_reduce
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [e2]; exact step2

end Elem

end HRS.MRep
