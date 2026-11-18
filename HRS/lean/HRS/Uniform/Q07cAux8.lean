import HRS.Uniform.Q07cAux7

/-!
# Q07c, part 8: independence of a Hilbert martingale with deterministic covariation from `ℱ 0`

If `G` is a continuous `H`-valued martingale with `G 0 = 0` and deterministic covariation density
`d` (in the sense of `IsHilbertMartingaleWithCovariation`), then for every finite family of times
in `[0,t]` the vector `(G τ_i)_i` is independent of `ℱ 0`.  Proof: for each linear functional the
combination `∑ ⟨G_{τ_i ∧ s}, y_i⟩` is a continuous real martingale with deterministic bracket, hence
Gaussian under `P(· | A)` for every `A ∈ ℱ 0` (`pc_law_cond`), and Cramér–Wold.
-/

noncomputable section

open HRS HRS.MRep
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q07c

section Pair

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {N : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {t : ℝ}

theorem pair_stop {U V Λ : ℝ → Ω → ℝ} (hU : Martingale U ℱ P) (hV : Martingale V ℱ P)
    (hU2 : ∀ t, MemLp (U t) 2 P) (hV2 : ∀ t, MemLp (V t) 2 P)
    (hΛ : Martingale (fun t ω => U t ω * V t ω - Λ t ω) ℱ P) {a b : ℝ} (hab : a ≤ b) :
    Martingale (fun s ω => U (min a s) ω * V (min b s) ω - Λ (min a s) ω) ℱ P := by
  have h := martingale_stop_time (martingale_stop_mul hU hV hU2 hV2 hΛ a) b
  have e : ∀ s, min a (min b s) = min a s := fun s => by rw [← min_assoc, min_eq_left hab]
  simpa only [e] using h

theorem _root_.HRS.IsHilbertMartingaleWithCovariation.pair_stopped
    (hM : IsHilbertMartingaleWithCovariation P ℱ t N Sg) (ht : 0 ≤ t) (x y : H) {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ t) :
    Martingale (fun s ω => inner ℝ (N (min a s) ω) x * inner ℝ (N (min b s) ω) y -
      ∫ σ in Set.Icc 0 (min a s), Sg σ ω x y) ℱ P := by
  have hX := hM.covariation x y
  have hUt : Martingale (fun τ ω => inner ℝ (N (min t τ) ω) x) ℱ P :=
    martingale_stop_time (F := fun τ ω => inner ℝ (N τ ω) x) (hM.martingale x) t
  have hVt : Martingale (fun τ ω => inner ℝ (N (min t τ) ω) y) ℱ P :=
    martingale_stop_time (F := fun τ ω => inner ℝ (N τ ω) y) (hM.martingale y) t
  have hΛ : Martingale (fun τ ω => inner ℝ (N (min t τ) ω) x * inner ℝ (N (min t τ) ω) y -
      ∫ σ in Set.Icc 0 (min t τ), Sg σ ω x y) ℱ P :=
    martingale_stop_time (F := fun τ ω => inner ℝ (N τ ω) x * inner ℝ (N τ ω) y -
      ∫ σ in Set.Icc 0 τ, Sg σ ω x y) hX t
  have h := pair_stop hUt hVt (fun τ => memLp_inner_aux hM ht x (min_le_left t τ))
    (fun τ => memLp_inner_aux hM ht y (min_le_left t τ)) hΛ hab
  have e : ∀ s, min t (min a s) = min a s := fun s =>
    min_eq_right ((min_le_left a s).trans (hab.trans hb))
  have e' : ∀ s, min t (min b s) = min b s := fun s => min_eq_right ((min_le_left b s).trans hb)
  simpa only [e, e'] using h

end Pair

section Comb

open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {G : ℝ → Ω → H} {d : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {t : ℝ}
variable {ι : Type*} [Fintype ι]

lemma martingale_finsum {κ : Type*} (s : Finset κ) {f : κ → ℝ → Ω → ℝ}
    (h : ∀ i ∈ s, Martingale (f i) ℱ P) : Martingale (fun t ω => ∑ i ∈ s, f i t ω) ℱ P := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact martingale_zero ℝ ℱ P
  | insert i s hi ih =>
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have := h1.add h2
    simp only [Finset.sum_insert hi]; exact this

/-- `∑_i ⟨G_{s ∧ τ_i}, y_i⟩`. -/
def comb (G : ℝ → Ω → H) (τ : ι → ℝ) (y : ι → H) (s : ℝ) (ω : Ω) : ℝ :=
  ∑ i, inner ℝ (G (min s (τ i)) ω) (y i)

/-- The bracket density `d_σ(u_σ, u_σ)`, `u_σ = ∑_i 1_{σ ≤ τ_i} y_i`, written as a double sum. -/
def combQ (d : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (τ : ι → ℝ) (y : ι → H) (σ : ℝ) : ℝ :=
  ∑ i, ∑ j, if σ ≤ min (τ i) (τ j) then d σ (y i) (y j) else 0

lemma combQ_eq (d : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (τ : ι → ℝ) (y : ι → H) (σ : ℝ) :
    combQ d τ y σ = d σ (∑ i, (if σ ≤ τ i then (1 : ℝ) else 0) • y i)
      (∑ i, (if σ ≤ τ i then (1 : ℝ) else 0) • y i) := by
  set c : ι → ℝ := fun i => if σ ≤ τ i then (1 : ℝ) else 0 with hc
  have hr1 : d σ (∑ i, c i • y i) = ∑ i, c i • d σ (y i) := by
    simp [map_sum, map_smul]
  have hr2 : ∀ i, d σ (y i) (∑ j, c j • y j) = ∑ j, c j * d σ (y i) (y j) := fun i => by
    simp [map_sum, map_smul]
  rw [hr1, ContinuousLinearMap.sum_apply]
  unfold combQ
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hr2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : σ ≤ τ i <;> by_cases h2 : σ ≤ τ j <;> simp [hc, h1, h2, le_min_iff]

lemma combQ_nonneg (hd : ∀ σ ∈ Set.Icc 0 t, IsTraceClassCov (d σ)) (τ : ι → ℝ) (y : ι → H)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) : 0 ≤ combQ d τ y σ := by
  rw [combQ_eq]
  exact (hd σ hσ).nonneg _

/-- The compensator `a(s) = ∑_{i,j} ∫_0^{s ∧ τ_i ∧ τ_j} d_σ(y_i, y_j) dσ`. -/
def combA (d : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (τ : ι → ℝ) (y : ι → H) (s : ℝ) : ℝ :=
  ∑ i, ∑ j, ∫ σ in Set.Icc 0 (min (min (τ i) (τ j)) s), d σ (y i) (y j)

theorem law_comb
    (hG : IsHilbertMartingaleWithCovariation P ℱ t G (fun r _ => d r)) (ht : 0 ≤ t)
    (hcont : ∀ ω, Continuous fun s => G s ω) (hz : ∀ ω, G 0 ω = 0)
    (τ : ι → ℝ) (hτ : ∀ i, 0 ≤ τ i ∧ τ i ≤ t) (y : ι → H) {A : Set Ω}
    (hA : MeasurableSet[ℱ 0] A) (hPA : P A ≠ 0) :
    law (ProbabilityTheory.cond P A) (comb G τ y t) = gaussianLaw (combA d τ y t) := by
  obtain ⟨ω₀, hent, htc⟩ : ∃ ω₀ : Ω, (∀ x y : H, IntegrableOn (fun σ => d σ x y) (Set.Icc 0 t)) ∧
      (∀ σ ∈ Set.Icc 0 t, IsTraceClassCov (d σ)) := by
    obtain ⟨ω, h1, h2⟩ := (hG.sigma_entry_int.and hG.sigma_traceClass).exists
    exact ⟨ω, h1, h2⟩
  have hsymm : ∀ σ ∈ Set.Icc 0 t, ∀ x y : H, d σ x y = d σ y x := fun σ hσ x y =>
    (htc σ hσ).symm x y
  have hmin : ∀ i j, 0 ≤ min (τ i) (τ j) ∧ min (τ i) (τ j) ≤ t := fun i j =>
    ⟨le_min (hτ i).1 (hτ j).1, (min_le_left _ _).trans (hτ i).2⟩
  have hqint : IntegrableOn (combQ d τ y) (Set.Icc 0 t) := by
    unfold combQ
    refine integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => ?_
    have : (fun σ => if σ ≤ min (τ i) (τ j) then d σ (y i) (y j) else 0) =
        (Set.Iic (min (τ i) (τ j))).indicator (fun σ => d σ (y i) (y j)) := by
      funext σ; simp [Set.indicator]
    rw [this]
    exact (hent _ _).indicator measurableSet_Iic
  -- representation of the compensator on `[0,t]`
  have hint : ∀ s, s ≤ t → ∀ i j, Integrable
      (fun σ => if σ ≤ min (τ i) (τ j) then d σ (y i) (y j) else 0) (volume.restrict (Set.Icc 0 s)) := by
    intro s hs i j
    have hsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc 0 t := Set.Icc_subset_Icc_right hs
    have : (fun σ => if σ ≤ min (τ i) (τ j) then d σ (y i) (y j) else 0) =
        (Set.Iic (min (τ i) (τ j))).indicator (fun σ => d σ (y i) (y j)) := by
      funext σ; simp [Set.indicator]
    rw [this]
    exact ((hent _ _).mono_set hsub).indicator measurableSet_Iic
  have hrep : ∀ s ∈ Set.Icc (0 : ℝ) t, combA d τ y s = ∫ σ in Set.Icc 0 s, combQ d τ y σ := by
    intro s hs
    unfold combA combQ
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hint s hs.2 i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => hint s hs.2 i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [HRS.MRep.integral_ite_Icc (min (τ i) (τ j)) s (fun σ => d σ (y i) (y j)), min_comm]
  have ha0 : combA d τ y 0 = 0 := by
    unfold combA
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [min_eq_right (hmin i j).1]
    simp
  have hac : ContinuousOn (combA d τ y) (Set.Icc 0 t) := by
    have h1 : ContinuousOn (fun s => ∫ σ in (0 : ℝ)..s, combQ d τ y σ) (Set.Icc 0 t) := by
      have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := t)
        (f := combQ d τ y) (μ := volume) (by rwa [Set.uIcc_of_le ht])
      rwa [Set.uIcc_of_le ht] at this
    refine h1.congr fun s hs => ?_
    dsimp only
    rw [hrep s hs, intervalIntegral.integral_of_le hs.1, integral_Icc_eq_integral_Ioc]
  have ham : MonotoneOn (combA d τ y) (Set.Icc 0 t) := by
    intro s hs s' hs' hss'
    rw [hrep s hs, hrep s' hs']
    refine setIntegral_mono_set (hqint.mono_set (Set.Icc_subset_Icc_right hs'.2)) ?_
      (Filter.Eventually.of_forall (Set.Icc_subset_Icc_right hss'))
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    exact combQ_nonneg htc τ y ⟨hσ.1, hσ.2.trans hs'.2⟩
  -- the martingale
  have hX : ∀ i, Martingale (fun s ω => inner ℝ (G (min s (τ i)) ω) (y i)) ℱ P := fun i => by
    have := martingale_stop_time (F := fun s ω => inner ℝ (G s ω) (y i)) (hG.martingale (y i)) (τ i)
    simpa only [min_comm] using this
  have hMart : Martingale (comb G τ y) ℱ P := by
    have := martingale_finsum (P := P) (ℱ := ℱ) Finset.univ (fun i _ => hX i)
    exact this
  have hcont' : ∀ ω, Continuous fun s => comb G τ y s ω := fun ω => by
    unfold comb
    refine continuous_finset_sum _ fun i _ => ?_
    exact ((hcont ω).comp (continuous_id.min continuous_const)).inner continuous_const
  have hzero' : ∀ ω, comb G τ y 0 ω = 0 := fun ω => by
    unfold comb
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [min_eq_left (hτ i).1, hz ω]; simp
  have hL2 : ∀ s, MemLp (comb G τ y s) 2 P := fun s => by
    have := memLp_finset_sum (p := 2) (μ := P) Finset.univ
      (f := fun i ω => inner ℝ (G (min s (τ i)) ω) (y i))
      (fun i _ => memLp_inner_aux hG ht (y i) ((min_le_right s (τ i)).trans (hτ i).2))
    exact this
  have hpair : ∀ i j, Martingale (fun s ω => inner ℝ (G (min s (τ i)) ω) (y i) *
      inner ℝ (G (min s (τ j)) ω) (y j) -
      ∫ σ in Set.Icc 0 (min (min (τ i) (τ j)) s), d σ (y i) (y j)) ℱ P := by
    intro i j
    rcases le_total (τ i) (τ j) with h | h
    · have := hG.pair_stopped ht (y i) (y j) h (hτ j).2
      have hf : (fun (s : ℝ) (ω : Ω) => inner ℝ (G (min s (τ i)) ω) (y i) *
          inner ℝ (G (min s (τ j)) ω) (y j) -
          ∫ σ in Set.Icc 0 (min (min (τ i) (τ j)) s), d σ (y i) (y j)) =
          fun s ω => inner ℝ (G (min (τ i) s) ω) (y i) * inner ℝ (G (min (τ j) s) ω) (y j) -
          ∫ σ in Set.Icc 0 (min (τ i) s), d σ (y i) (y j) := by
        funext s ω
        rw [min_comm s (τ i), min_comm s (τ j), min_eq_left h]
      rw [hf]; exact this
    · have := hG.pair_stopped ht (y j) (y i) h (hτ i).2
      have hsy : ∀ s, ∫ σ in Set.Icc 0 (min (τ j) s), d σ (y i) (y j) =
          ∫ σ in Set.Icc 0 (min (τ j) s), d σ (y j) (y i) := fun s => by
        refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
        exact hsymm σ ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hτ j).2)⟩ _ _
      have hf : (fun (s : ℝ) (ω : Ω) => inner ℝ (G (min s (τ i)) ω) (y i) *
          inner ℝ (G (min s (τ j)) ω) (y j) -
          ∫ σ in Set.Icc 0 (min (min (τ i) (τ j)) s), d σ (y i) (y j)) =
          fun s ω => inner ℝ (G (min (τ j) s) ω) (y j) * inner ℝ (G (min (τ i) s) ω) (y i) -
          ∫ σ in Set.Icc 0 (min (τ j) s), d σ (y j) (y i) := by
        funext s ω
        rw [min_comm s (τ i), min_comm s (τ j), min_eq_right h, mul_comm, hsy]
      rw [hf]; exact this
  have hMa : Martingale (fun s ω => comb G τ y s ω ^ 2 - combA d τ y s) ℱ P := by
    have := martingale_finsum (P := P) (ℱ := ℱ) Finset.univ (fun i _ =>
      martingale_finsum (P := P) (ℱ := ℱ) Finset.univ (fun j _ => hpair i j))
    have hf : (fun (s : ℝ) (ω : Ω) => comb G τ y s ω ^ 2 - combA d τ y s) =
        fun s ω => ∑ i, ∑ j, (inner ℝ (G (min s (τ i)) ω) (y i) *
          inner ℝ (G (min s (τ j)) ω) (y j) -
          ∫ σ in Set.Icc 0 (min (min (τ i) (τ j)) s), d σ (y i) (y j)) := by
      funext s ω
      unfold comb combA
      rw [sq, Finset.sum_mul_sum]
      simp only [Finset.sum_sub_distrib]
    rw [hf]; exact this
  exact pc_law_cond ht hMart hcont' hzero' hL2 hMa ha0 hac ham hA hPA

lemma measurable_of_isHM {N : ℝ → Ω → H} {Sg : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ}
    (hM : IsHilbertMartingaleWithCovariation P ℱ t N Sg) (τ : ℝ) : Measurable (N τ) := by
  obtain ⟨ι₀, hι₀, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι₀
  refine measurable_of_inner_basis b fun i => ?_
  have := (((hM.martingale (b i)).1 τ).measurable.mono (ℱ.le τ) le_rfl)
  simpa [real_inner_comm] using this

theorem law_vec_eq
    (hG : IsHilbertMartingaleWithCovariation P ℱ t G (fun r _ => d r)) (ht : 0 ≤ t)
    (hcont : ∀ ω, Continuous fun s => G s ω) (hz : ∀ ω, G 0 ω = 0)
    (τ : ι → ℝ) (hτ : ∀ i, 0 ≤ τ i ∧ τ i ≤ t) {A : Set Ω}
    (hA : MeasurableSet[ℱ 0] A) (hPA : P A ≠ 0) :
    law (ProbabilityTheory.cond P A) (fun ω i => G (τ i) ω) = law P (fun ω i => G (τ i) ω) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond P A) :=
    ProbabilityTheory.cond_isProbabilityMeasure hPA
  have hYm : Measurable (fun ω i => G (τ i) ω) :=
    measurable_pi_iff.2 fun i => measurable_of_isHM hG (τ i)
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  set y : ι → H := fun i => (InnerProductSpace.toDual ℝ H).symm
    (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => H) i)) with hy
  have hLY : ∀ ω, L (fun i => G (τ i) ω) = comb G τ y t ω := by
    intro ω
    have h1 : (fun i => G (τ i) ω) = ∑ i, Pi.single i (G (τ i) ω) := by
      rw [Finset.univ_sum_single]
    conv_lhs => rw [h1]
    rw [map_sum]
    unfold comb
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [min_eq_right (hτ i).2, real_inner_comm, hy]
    simp only [InnerProductSpace.toDual_symm_apply]
    rfl
  have hmap : ∀ μ : Measure Ω, (μ.map fun ω i => G (τ i) ω).map L = μ.map (comb G τ y t) := by
    intro μ
    rw [Measure.map_map L.continuous.measurable hYm]
    congr 1
    funext ω
    exact hLY ω
  rw [hmap, hmap]
  have h1 := law_comb hG ht hcont hz τ hτ y hA hPA
  have h2 := law_comb hG ht hcont hz τ hτ y (A := Set.univ) MeasurableSet.univ (by simp)
  rw [ProbabilityTheory.cond_univ] at h2
  unfold law at h1 h2
  rw [h1, h2]

theorem indep_comap_vec
    (hG : IsHilbertMartingaleWithCovariation P ℱ t G (fun r _ => d r)) (ht : 0 ≤ t)
    (hcont : ∀ ω, Continuous fun s => G s ω) (hz : ∀ ω, G 0 ω = 0)
    (𝒢 : InitialSigma ℱ) (τ : ι → ℝ) (hτ : ∀ i, 0 ≤ τ i ∧ τ i ≤ t) :
    Indep 𝒢.1 (MeasurableSpace.comap (fun ω i => G (τ i) ω) inferInstance) P := by
  have hYm : Measurable (fun ω i => G (τ i) ω) :=
    measurable_pi_iff.2 fun i => measurable_of_isHM hG (τ i)
  rw [Indep_iff]
  intro A B hA hB
  obtain ⟨S, hS, rfl⟩ := hB
  have hA' : MeasurableSet[mΩ] A := ℱ.le 0 _ (𝒢.2 _ hA)
  by_cases hPA : P A = 0
  · rw [measure_mono_null Set.inter_subset_left hPA, hPA, zero_mul]
  · have hlaw := law_vec_eq hG ht hcont hz τ hτ (A := A) (𝒢.2 _ hA) hPA
    have h2 : ProbabilityTheory.cond P A ((fun ω i => G (τ i) ω) ⁻¹' S) =
        P ((fun ω i => G (τ i) ω) ⁻¹' S) := by
      have := congrArg (fun μ : Measure (ι → H) => μ S) hlaw
      simp only [law, Measure.map_apply hYm hS] at this
      exact this
    rw [ProbabilityTheory.cond_apply hA'] at h2
    rw [← h2, ← mul_assoc, ENNReal.mul_inv_cancel hPA (measure_ne_top _ _), one_mul]

lemma comap_coord_le_comap_pi' {Ξ : Type*} {s : Type*} {E : s → Type*} [∀ k, MeasurableSpace (E k)]
    (g : Ξ → ∀ k, E k) (k : s) :
    MeasurableSpace.comap (fun ω => g ω k) inferInstance ≤ MeasurableSpace.comap g inferInstance := by
  rw [show (fun ω => g ω k) = (fun v : ∀ k, E k => v k) ∘ g from rfl, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply k).comap_le

theorem indep_path
    (hG : IsHilbertMartingaleWithCovariation P ℱ t G (fun r _ => d r)) (ht : 0 ≤ t)
    (hcont : ∀ ω, Continuous fun s => G s ω) (hz : ∀ ω, G 0 ω = 0) (𝒢 : InitialSigma ℱ) :
    Indep 𝒢.1 (⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ τ ≤ t}, MeasurableSpace.comap (G τ) inferInstance) P := by
  set S : Set ℝ := {τ | 0 ≤ τ ∧ τ ≤ t} with hS
  let κ := {F : Finset ℝ // ∀ τ ∈ F, τ ∈ S}
  let m : κ → MeasurableSpace Ω := fun F =>
    ⨆ τ ∈ (F.1 : Finset ℝ), MeasurableSpace.comap (G τ) inferInstance
  have hGm : ∀ τ, MeasurableSpace.comap (G τ) inferInstance ≤ mΩ := fun τ =>
    (measurable_of_isHM hG τ).comap_le
  have hle : ∀ F : κ, m F ≤ mΩ := fun F => iSup₂_le fun τ _ => hGm τ
  have hind : ∀ F : κ, Indep (m F) 𝒢.1 P := fun F => by
    have h := indep_comap_vec hG ht hcont hz 𝒢 (ι := (F.1 : Finset ℝ)) (fun i => (i : ℝ))
      (fun i => F.2 i i.2)
    refine (indep_of_indep_of_le_right h ?_).symm
    refine iSup₂_le fun τ hτ => ?_
    exact comap_coord_le_comap_pi' (fun ω (i : (F.1 : Finset ℝ)) => G (i : ℝ) ω) ⟨τ, hτ⟩
  have hdir : Directed (· ≤ ·) m := by
    intro F F'
    refine ⟨⟨F.1 ∪ F'.1, fun τ hτ => ?_⟩, ?_, ?_⟩
    · rcases Finset.mem_union.1 hτ with h | h
      · exact F.2 τ h
      · exact F'.2 τ h
    · exact iSup₂_le fun τ hτ => le_iSup₂_of_le τ (Finset.mem_union_left _ hτ) le_rfl
    · exact iSup₂_le fun τ hτ => le_iSup₂_of_le τ (Finset.mem_union_right _ hτ) le_rfl
  have hbig := indep_iSup_of_directed_le hind hle (𝒢.2.trans (ℱ.le 0)) hdir
  refine (indep_of_indep_of_le_right hbig.symm ?_)
  refine iSup₂_le fun τ hτ => ?_
  exact le_iSup_of_le (⟨{τ}, fun τ' hτ' => by simpa [Finset.mem_singleton.1 hτ'] using hτ⟩ : κ)
    (le_iSup₂_of_le τ (Finset.mem_singleton_self τ) le_rfl)

end Comb

end HRS.Uniform.Q07c
