import HRS.Uniform.Q45Cov3

/-!
# Q45 (Lemma 3.20): propagated observations and covariance of Riemann sums
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Pullback

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma pullback_inner (S : EvolData H E) (t r : ℝ) (ℓ : E →L[ℝ] ℝ) (x : H) :
    inner ℝ (pullbackVec S t r ℓ) x = ℓ (S.VE t r (S.j x)) := by
  unfold pullbackVec
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

lemma norm_pullback_le {T K : ℝ} (hT : 0 ≤ T) {S : EvolData H E} (hS : S.MaxHyp T K) {r t : ℝ}
    (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) (ℓ : E →L[ℝ] ℝ) :
    ‖pullbackVec S t r ℓ‖ ≤ detConst T K * ‖ℓ‖ := by
  unfold pullbackVec
  rw [LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := detConst_pos T K; positivity) fun b => ?_
  simp only [ContinuousLinearMap.comp_apply]
  calc ‖ℓ (S.VE t r (S.j b))‖ ≤ ‖ℓ‖ * ‖S.VE t r (S.j b)‖ := ℓ.le_opNorm _
    _ ≤ ‖ℓ‖ * (detConst T K * ‖b‖) :=
        mul_le_mul_of_nonneg_left (EvolData.MaxHyp.norm_le hT hS hr hrt htT b) (norm_nonneg _)
    _ = detConst T K * ‖ℓ‖ * ‖b‖ := by ring

/-- Weak continuity of `r ↦ V(t,r)^*ℓ` on `[0,t]`. -/
lemma pullback_weak_tendsto {T : ℝ} {S : EvolData H E} (hev : S.IsEvolution T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (ℓ : E →L[ℝ] ℝ) {ι : Type*} {l : Filter ι} (a : ι → ℝ) {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Icc (0 : ℝ) t) (ha : ∀ᶠ i in l, a i ∈ Set.Icc (0 : ℝ) t)
    (hlim : Tendsto a l (𝓝 r₀)) (x : H) :
    Tendsto (fun i => inner ℝ (pullbackVec S t (a i) ℓ) x) l (𝓝 (inner ℝ (pullbackVec S t r₀ ℓ) x)) := by
  simp only [pullback_inner]
  have hc := hev.cont_E (S.j x)
  have hmap : Set.MapsTo (fun r : ℝ => (t, r)) (Set.Icc 0 t)
      {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := fun r hr => ⟨hr.1, hr.2, ht.2⟩
  have h1 : ContinuousWithinAt (fun r : ℝ => S.VE t r (S.j x)) (Set.Icc 0 t) r₀ :=
    (hc.comp (Continuous.continuousOn (by fun_prop)) hmap) r₀ hr₀
  have h2 : Tendsto a l (𝓝[Set.Icc 0 t] r₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, ha⟩
  have h3 := (ℓ.continuous.tendsto _).comp (h1.tendsto.comp h2)
  exact h3

end Pullback

section Sums

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {T : ℝ} {G : ℝ → Ω → H} {Dd : ℝ → H →L[ℝ] H →L[ℝ] ℝ}

/-- The increment `⟨G_{r_{i+1}} - G_{r_i}, x⟩`. -/
def incr (G : ℝ → Ω → H) (r : ℕ → ℝ) (xs : ℕ → H) (i : ℕ) (ω : Ω) : ℝ :=
  inner ℝ (G (r (i + 1)) ω) (xs i) - inner ℝ (G (r i) ω) (xs i)

lemma incr_memLp (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Dd r)) {r : ℕ → ℝ}
    (hr : Monotone r) (h0 : 0 ≤ r 0) {i : ℕ} (hiT : r (i + 1) ≤ T) (xs : ℕ → H) :
    MemLp (incr G r xs i) 2 P := by
  have h1 : r i ∈ Set.Icc (0 : ℝ) T :=
    ⟨h0.trans (hr (Nat.zero_le i)), (hr (Nat.le_succ i)).trans hiT⟩
  have h2 : r (i + 1) ∈ Set.Icc (0 : ℝ) T := ⟨h0.trans (hr (Nat.zero_le _)), hiT⟩
  exact (HM_memLp hG h2 (xs i)).sub (HM_memLp hG h1 (xs i))

lemma incr_cov (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Dd r)) {r : ℕ → ℝ}
    (hr : Monotone r) (h0 : 0 ≤ r 0) {i k : ℕ} (hiT : r (i + 1) ≤ T) (hkT : r (k + 1) ≤ T)
    (xs ys : ℕ → H) :
    ∫ ω, incr G r xs i ω * incr G r ys k ω ∂P =
      if i = k then ∫ σ in Set.Icc (r i) (r (i + 1)), Dd σ (xs i) (ys i) else 0 := by
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    exact HM_incr_same hG (h0.trans (hr (Nat.zero_le i))) (hr (Nat.le_succ i)) hiT (xs i) (ys i)
  · rw [if_neg hik]
    rcases Nat.lt_or_gt_of_ne hik with hlt | hgt
    · exact HM_incr_orth hG (h0.trans (hr (Nat.zero_le i))) (hr (Nat.le_succ i))
        (hr (Nat.succ_le_of_lt hlt)) (hr (Nat.le_succ k)) hkT (xs i) (ys k)
    · have := HM_incr_orth hG (h0.trans (hr (Nat.zero_le k))) (hr (Nat.le_succ k))
        (hr (Nat.succ_le_of_lt hgt)) (hr (Nat.le_succ i)) hiT (ys k) (xs i)
      simp only [incr]
      calc ∫ ω, (inner ℝ (G (r (i + 1)) ω) (xs i) - inner ℝ (G (r i) ω) (xs i)) *
            (inner ℝ (G (r (k + 1)) ω) (ys k) - inner ℝ (G (r k) ω) (ys k)) ∂P
          = ∫ ω, (inner ℝ (G (r (k + 1)) ω) (ys k) - inner ℝ (G (r k) ω) (ys k)) *
            (inner ℝ (G (r (i + 1)) ω) (xs i) - inner ℝ (G (r i) ω) (xs i)) ∂P := by
            refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
            simp only []
            ring
        _ = 0 := this

/-- Covariance of two Riemann-type sums over the cells of a common partition (the first sum uses only the first `n`
cells). -/
lemma cov_sum_nat (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Dd r)) {r : ℕ → ℝ}
    (hr : Monotone r) (h0 : 0 ≤ r 0) {n m : ℕ} (hnm : n ≤ m) (hmT : r m ≤ T) (xs ys : ℕ → H) :
    ∫ ω, (∑ i ∈ Finset.range n, incr G r xs i ω) * (∑ k ∈ Finset.range m, incr G r ys k ω) ∂P =
      ∑ i ∈ Finset.range n, ∫ σ in Set.Icc (r i) (r (i + 1)), Dd σ (xs i) (ys i) := by
  have hcell : ∀ i, i < m → r (i + 1) ≤ T := fun i hi =>
    (hr (Nat.succ_le_of_lt hi)).trans hmT
  have hint : ∀ i k, i < m → k < m →
      Integrable (fun ω => incr G r xs i ω * incr G r ys k ω) P := fun i k hi hk =>
    (incr_memLp hG hr h0 (hcell i hi) xs).integrable_mul (incr_memLp hG hr h0 (hcell k hk) ys)
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finset_sum _ (fun i hi => integrable_finset_sum _ fun k hk =>
    hint i k (lt_of_lt_of_le (Finset.mem_range.1 hi) hnm) (Finset.mem_range.1 hk))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < m := lt_of_lt_of_le (Finset.mem_range.1 hi) hnm
  rw [integral_finset_sum _ (fun k hk => hint i k hi' (Finset.mem_range.1 hk))]
  rw [Finset.sum_eq_single i]
  · rw [incr_cov hG hr h0 (hcell i hi') (hcell i hi') xs ys, if_pos rfl]
  · intro k hk hki
    rw [incr_cov hG hr h0 (hcell i hi') (hcell k (Finset.mem_range.1 hk)) xs ys, if_neg (Ne.symm hki)]
  · intro h; exact absurd (Finset.mem_range.2 hi') h

end Sums

section Riemann

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A functional applied to a Riemann sum is a sum of increments against the propagated observation. -/
lemma functional_riemannSum (S : EvolData H E) (G : ℝ → Ω → H) (t : ℝ) (ℓ : E →L[ℝ] ℝ) (r : ℕ → ℝ)
    (N : ℕ) (ω : Ω) :
    ℓ (riemannSum S.VE S.j G t (fun i : Fin (N + 1) => r i) ω) =
      ∑ i ∈ Finset.range N, incr G r (fun i => pullbackVec S t (r i) ℓ) i ω := by
  unfold riemannSum
  rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun i => incr G r (fun i => pullbackVec S t (r i) ℓ) i ω) N]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.val_castSucc, Fin.val_succ, incr]
  rw [← pullback_inner, real_inner_comm, inner_sub_left]

end Riemann

end HRS.Uniform.Q45
