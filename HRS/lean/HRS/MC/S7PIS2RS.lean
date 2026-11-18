import HRS.MC.S7PIDefs

/-!
# Packet piS2, part 2: `s7_PIS_RS_basic` (Riemann-Stieltjes integrals: uniqueness and the density case)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- Uniform tagged partitions of arbitrarily small mesh. -/
theorem S7PIS2_exists_partition {T : ℝ} (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (u : Fin (n + 1) → ℝ) (τ : Fin n → ℝ), StrictMono u ∧ u 0 = 0 ∧ u (Fin.last n) = T ∧
      (∀ i : Fin n, u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ) ∧ (∀ i : Fin n, u i.succ - u i.castSucc < δ) := by
  set n : ℕ := ⌈T / δ⌉₊ + 1 with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
  have hTn : T / δ < n := by
    have := Nat.le_ceil (T / δ)
    rw [hn]; push_cast; linarith
  refine ⟨n, fun i => (i : ℕ) * T / n, fun i => ((i : ℕ) : ℝ) * T / n, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    show ((i : ℕ) : ℝ) * T / n < ((j : ℕ) : ℝ) * T / n
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right this hT) hnpos
  · simp
  · show ((Fin.last n : Fin (n + 1)) : ℕ) * T / n = T
    simp [Fin.val_last]
  · intro i
    exact ⟨le_rfl, by
      show ((i.castSucc : Fin (n + 1)) : ℕ) * T / n ≤ ((i.succ : Fin (n + 1)) : ℕ) * T / n
      simp only [Fin.val_castSucc, Fin.val_succ]
      apply div_le_div_of_nonneg_right _ hnpos.le
      push_cast
      nlinarith⟩
  · intro i
    show ((i.succ : Fin (n + 1)) : ℕ) * T / n - ((i.castSucc : Fin (n + 1)) : ℕ) * T / n < δ
    simp only [Fin.val_castSucc, Fin.val_succ]
    have : ((i : ℕ) + 1 : ℝ) * T / n - (i : ℕ) * T / n = T / n := by field_simp; ring
    push_cast
    rw [this, div_lt_iff₀ hnpos]
    rwa [div_lt_iff₀ hδ, mul_comm] at hTn

theorem S7PIS2_RS_unique (T : ℝ) (hT : 0 < T) (S : ℝ → ℝ → ℝ → ℝ) (I I' : ℝ) (h : IsRS T S I)
    (h' : IsRS T S I') : I = I' := by
  by_contra hne
  have hpos : 0 < |I - I'| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δ1, hδ1, H1⟩ := h (|I - I'| / 2) (by positivity)
  obtain ⟨δ2, hδ2, H2⟩ := h' (|I - I'| / 2) (by positivity)
  obtain ⟨n, u, τ, hs, h0, hl, htag, hmesh⟩ := S7PIS2_exists_partition hT (lt_min hδ1 hδ2)
  have e1 := H1 n u τ hs h0 hl htag (fun i => lt_of_lt_of_le (hmesh i) (min_le_left _ _))
  have e2 := H2 n u τ hs h0 hl htag (fun i => lt_of_lt_of_le (hmesh i) (min_le_right _ _))
  have := abs_sub_le I (∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ)) I'
  have h2 := abs_sub_comm I (∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ))
  linarith

/-- Additivity of the integral over the pieces of a partition. -/
theorem S7PIS2_partition_sum {n : ℕ} (u : Fin (n + 1) → ℝ) (hu : StrictMono u) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Icc (u 0) (u (Fin.last n)))) :
    ∑ k : Fin n, ∫ x in Set.Ioc (u k.castSucc) (u k.succ), f x =
      ∫ x in Set.Ioc (u 0) (u (Fin.last n)), f x := by
  classical
  set a : ℕ → ℝ := fun k => u ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩ with ha
  have hmono : Monotone a := fun k l hkl =>
    hu.monotone (Fin.mk_le_mk.2 (min_le_min_right _ hkl))
  have hlo : ∀ k, u 0 ≤ a k := fun k => hu.monotone (Fin.zero_le _)
  have hhi : ∀ k, a k ≤ u (Fin.last n) := fun k => hu.monotone (Fin.le_last _)
  have hcast : ∀ i : Fin n, a i = u i.castSucc := fun i => by
    simp only [ha]; congr 1; ext; simp [min_eq_left i.2.le]
  have hsucc : ∀ i : Fin n, a (i + 1) = u i.succ := fun i => by
    simp only [ha]; congr 1; ext; simp [min_eq_left (Nat.succ_le_of_lt i.2)]
  have h0 : a 0 = u 0 := by simp only [ha]; congr 1
  have hn : a n = u (Fin.last n) := by simp only [ha]; congr 1; ext; simp
  have hii : ∀ k, IntervalIntegrable f volume (a k) (a (k + 1)) := fun k => by
    refine IntegrableOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (hmono (Nat.le_succ k))]
    exact hf.mono_set (Set.Icc_subset_Icc (hlo k) (hhi _))
  have key := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume) (a := a)
    (n := n) (fun k _ => hii k)
  rw [← Fin.sum_univ_eq_sum_range (fun k => ∫ x in a k..a (k + 1), f x) n, h0, hn] at key
  rw [intervalIntegral.integral_of_le (hu.monotone (Fin.zero_le (Fin.last n)))] at key
  rw [← key]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_of_le (hmono (Nat.le_succ _)), hcast, hsucc]

/-- The one-interval estimate. -/
theorem S7PIS2_RS_local {a b τ c : ℝ} (g h : ℝ → ℝ) (hτ : τ ∈ Set.Icc a b)
    (hh : IntegrableOn h (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hc : ∀ x ∈ Set.Ioc a b, |g τ - g x| ≤ c) :
    |g τ * (∫ x in Set.Ioc a b, h x) - ∫ x in Set.Ioc a b, g x * h x| ≤ c * ∫ x in Set.Ioc a b, |h x| := by
  have hh' : IntegrableOn h (Set.Ioc a b) := hh.mono_set Set.Ioc_subset_Icc_self
  have hgh : IntegrableOn (fun x => g x * h x) (Set.Ioc a b) :=
    (IntegrableOn.continuousOn_mul hg hh isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have e1 : ∫ x in Set.Ioc a b, (g τ - g x) * h x =
      g τ * (∫ x in Set.Ioc a b, h x) - ∫ x in Set.Ioc a b, g x * h x := by
    simp_rw [sub_mul]
    rw [integral_sub (hh'.const_mul _) hgh, integral_const_mul]
  rw [← e1]
  have hint : Integrable (fun x => c * |h x|) (volume.restrict (Set.Ioc a b)) :=
    (hh'.abs).const_mul c
  have := norm_integral_le_of_norm_le (μ := volume.restrict (Set.Ioc a b))
    (f := fun x => (g τ - g x) * h x) hint ?_
  · rw [integral_const_mul] at this
    simpa [Real.norm_eq_abs] using this
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hc x hx) (abs_nonneg _)

theorem S7PIS2_RS_density (T : ℝ) (hT : 0 < T) {ι : Type} [Fintype ι] (g h : ι → ℝ → ℝ)
    (hg : ∀ i, ContinuousOn (g i) (Set.Icc 0 T)) (hh : ∀ i, IntegrableOn (h i) (Set.Icc 0 T)) :
    IsRS T (fun τ a b => ∑ i, g i τ * ∫ u in Set.Ioc a b, h i u) (∫ u in Set.Ioc 0 T, ∑ i, g i u * h i u) := by
  intro ε hε
  set H : ℝ := (∑ i, ∫ x in Set.Icc (0 : ℝ) T, |h i x|) + 1 with hH
  have hS0 : 0 ≤ ∑ i, ∫ x in Set.Icc (0 : ℝ) T, |h i x| :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun x => abs_nonneg _
  have hHpos : 0 < H := by rw [hH]; linarith
  have hεH : 0 < ε / H := by positivity
  have hunif : ∀ i, ∃ η : ℝ, 0 < η ∧ ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T,
      |x - y| < η → |g i x - g i y| < ε / H := fun i => by
    have := (isCompact_Icc.uniformContinuousOn_of_continuous (hg i))
    rw [Metric.uniformContinuousOn_iff] at this
    obtain ⟨η, hη, H'⟩ := this (ε / H) hεH
    exact ⟨η, hη, fun x hx y hy hxy => by simpa [Real.dist_eq] using H' x hx y hy (by simpa [Real.dist_eq] using hxy)⟩
  choose η hη0 hη using hunif
  obtain ⟨δ, hδη, hδ0⟩ : ∃ δ : ℝ, (∀ i, δ < η i) ∧ 0 < δ := by
    have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, δ < η i :=
      Filter.eventually_all.2 fun i => nhdsWithin_le_nhds (eventually_lt_nhds (hη0 i))
    obtain ⟨δ, h2, h3⟩ := (h1.and self_mem_nhdsWithin).exists
    exact ⟨δ, h2, h3⟩
  refine ⟨δ, hδ0, ?_⟩
  intro n u τ hs h0 hl htag hmesh
  have hmem : ∀ j, u j ∈ Set.Icc (0 : ℝ) T := fun j =>
    ⟨h0 ▸ hs.monotone (Fin.zero_le j), hl ▸ hs.monotone (Fin.le_last j)⟩
  have hF : IntegrableOn (fun x => ∑ i, g i x * h i x) (Set.Icc (u 0) (u (Fin.last n))) := by
    rw [h0, hl]
    exact integrable_finset_sum _ fun i _ => IntegrableOn.continuousOn_mul (hg i) (hh i) isCompact_Icc
  have hA : ∀ i, IntegrableOn (fun x => |h i x|) (Set.Icc (u 0) (u (Fin.last n))) := fun i => by
    rw [h0, hl]; exact (hh i).abs
  have hsubI : ∀ k : Fin n, Set.Icc (u k.castSucc) (u k.succ) ⊆ Set.Icc 0 T := fun k =>
    Set.Icc_subset_Icc (hmem _).1 (hmem _).2
  -- per-interval estimate
  have key : ∀ k : Fin n,
      |(∑ i, g i (τ k) * ∫ x in Set.Ioc (u k.castSucc) (u k.succ), h i x) -
        ∫ x in Set.Ioc (u k.castSucc) (u k.succ), ∑ i, g i x * h i x| ≤
      ε / H * ∑ i, ∫ x in Set.Ioc (u k.castSucc) (u k.succ), |h i x| := fun k => by
    have hint : ∀ i, IntegrableOn (fun x => g i x * h i x) (Set.Ioc (u k.castSucc) (u k.succ)) :=
      fun i => (IntegrableOn.continuousOn_mul ((hg i).mono (hsubI k)) ((hh i).mono_set (hsubI k))
        isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    rw [integral_finset_sum _ (fun i _ => hint i), ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine S7PIS2_RS_local (g i) (h i) (htag k) ((hh i).mono_set (hsubI k))
      ((hg i).mono (hsubI k)) fun x hx => ?_
    have hxT : x ∈ Set.Icc (0 : ℝ) T :=
      hsubI k ⟨hx.1.le, hx.2⟩
    have hτT : τ k ∈ Set.Icc (0 : ℝ) T := hsubI k (htag k)
    refine (hη i (τ k) hτT x hxT ?_).le
    have h1 := (htag k).1
    have h2 := (htag k).2
    have h3 := hmesh k
    have h4 := hδη i
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hsum_I : ∑ k : Fin n, ∫ x in Set.Ioc (u k.castSucc) (u k.succ), ∑ i, g i x * h i x =
      ∫ x in Set.Ioc 0 T, ∑ i, g i x * h i x := by
    have := S7PIS2_partition_sum u hs _ hF
    rwa [h0, hl] at this
  have hsum_A : ∀ i, ∑ k : Fin n, ∫ x in Set.Ioc (u k.castSucc) (u k.succ), |h i x| =
      ∫ x in Set.Ioc 0 T, |h i x| := fun i => by
    have := S7PIS2_partition_sum u hs _ (hA i)
    rwa [h0, hl] at this
  beta_reduce
  rw [← hsum_I, ← Finset.sum_sub_distrib]
  calc |∑ k : Fin n, ((∑ i, g i (τ k) * ∫ x in Set.Ioc (u k.castSucc) (u k.succ), h i x) -
          ∫ x in Set.Ioc (u k.castSucc) (u k.succ), ∑ i, g i x * h i x)|
      ≤ ∑ k : Fin n, |(∑ i, g i (τ k) * ∫ x in Set.Ioc (u k.castSucc) (u k.succ), h i x) -
          ∫ x in Set.Ioc (u k.castSucc) (u k.succ), ∑ i, g i x * h i x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, ε / H * ∑ i, ∫ x in Set.Ioc (u k.castSucc) (u k.succ), |h i x| :=
        Finset.sum_le_sum fun k _ => key k
    _ = ε / H * ∑ i, ∫ x in Set.Ioc 0 T, |h i x| := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [hsum_A]
    _ ≤ ε / H * ∑ i, ∫ x in Set.Icc (0 : ℝ) T, |h i x| := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hεH.le
        exact setIntegral_mono_set (hh i).abs (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (Filter.Eventually.of_forall Set.Ioc_subset_Icc_self)
    _ < ε := by
        have : ε / H * ∑ i, ∫ x in Set.Icc (0 : ℝ) T, |h i x| < ε / H * H :=
          mul_lt_mul_of_pos_left (by rw [hH]; linarith) hεH
        rwa [div_mul_cancel₀ _ hHpos.ne'] at this

theorem s7_PIS_RS_basic_proof (T : ℝ) (hT : 0 < T) :
    (∀ (S : ℝ → ℝ → ℝ → ℝ) (I I' : ℝ), IsRS T S I → IsRS T S I' → I = I') ∧
    (∀ {ι : Type} [Fintype ι] (g h : ι → ℝ → ℝ), (∀ i, ContinuousOn (g i) (Set.Icc 0 T)) →
      (∀ i, IntegrableOn (h i) (Set.Icc 0 T)) →
      IsRS T (fun τ a b => ∑ i, g i τ * ∫ u in Set.Ioc a b, h i u) (∫ u in Set.Ioc 0 T, ∑ i, g i u * h i u)) :=
  ⟨fun S I I' h h' => S7PIS2_RS_unique T hT S I I' h h',
    fun g h hg hh => S7PIS2_RS_density T hT g h hg hh⟩

end HRS.MC.Sec7.S7PIS2

end
