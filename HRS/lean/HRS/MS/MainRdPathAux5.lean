import HRS.MS.MainRdPathAux4
import HRS.MS.IidInitAux1

/-!
# S.A.9, packet P3a: tightness of random elements of a Hilbert space from uniform tails

Abstract machinery (no `H^{-q}` specifics):

* `Sa9Parseval c`: a family of continuous linear functionals `c ℓ` with `∑ (c ℓ x)² = ‖x‖²` (a Parseval frame);
* `sa9_tail c L x = ‖x‖² - ∑_{ℓ<L} (c ℓ x)²`;
* `sa9_isCompact_closure`: `{‖x‖ ≤ R, tail_{L_k}(x) ≤ δ_k ∀k}` with `δ_k → 0` has compact closure;
* `sa9_tightFam_of_tails`: a family of random elements with bounded second moments and uniformly small expected tails
  is tight;
* `sa9_tightFam_add`: sums of tight families are tight;
* `sa9_tightFam_of_l1`: a family tending to `0` in `L¹` is tight;
* `sa9_tightFam_union`, `sa9_tightFam_finite`: finitely many indices are harmless.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Pointwise

namespace HRS.MS.MainRdPath

/-- Tightness of the family `F N` of random elements, `N ∈ J`, under `P N`. -/
def Sa9TightFam {H : Type*} [TopologicalSpace H] {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (J : Set ℕ) (P : ∀ N, Measure (Ω N)) (F : ∀ N, Ω N → H) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ N ∈ J, P N {ζ | F N ζ ∉ K} ≤ ε

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A Parseval frame of continuous functionals. -/
def Sa9Parseval (c : ℕ → H →L[ℝ] ℝ) : Prop := ∀ x : H, HasSum (fun ℓ => (c ℓ x) ^ 2) (‖x‖ ^ 2)

/-- The tail of the Parseval expansion beyond `L`. -/
def sa9_tail (c : ℕ → H →L[ℝ] ℝ) (L : ℕ) (x : H) : ℝ := ‖x‖ ^ 2 - ∑ ℓ ∈ Finset.range L, (c ℓ x) ^ 2

variable {c : ℕ → H →L[ℝ] ℝ}

theorem sa9_tail_eq (hc : Sa9Parseval c) (L : ℕ) (x : H) :
    sa9_tail c L x = ∑' ℓ, (c (ℓ + L) x) ^ 2 := by
  have h := (hc x).summable.sum_add_tsum_nat_add L
  rw [(hc x).tsum_eq] at h
  unfold sa9_tail
  linarith

theorem sa9_tail_nonneg (hc : Sa9Parseval c) (L : ℕ) (x : H) : 0 ≤ sa9_tail c L x := by
  rw [sa9_tail_eq hc]; exact tsum_nonneg fun _ => sq_nonneg _

theorem sa9_coord_sq_le (hc : Sa9Parseval c) (ℓ : ℕ) (x : H) : (c ℓ x) ^ 2 ≤ ‖x‖ ^ 2 := by
  have := sum_le_hasSum ({ℓ} : Finset ℕ) (fun j _ => sq_nonneg (c j x)) (hc x)
  simpa using this

theorem sa9_tail_sub_le (hc : Sa9Parseval c) (L : ℕ) (x y : H) :
    sa9_tail c L (x - y) ≤ 2 * sa9_tail c L x + 2 * sa9_tail c L y := by
  rw [sa9_tail_eq hc, sa9_tail_eq hc, sa9_tail_eq hc]
  have hs : ∀ z : H, Summable fun ℓ => (c (ℓ + L) z) ^ 2 := fun z =>
    (summable_nat_add_iff L).2 (hc z).summable
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add ((hs x).mul_left 2) ((hs y).mul_left 2)]
  refine Summable.tsum_le_tsum (fun ℓ => ?_) (hs _) (((hs x).mul_left 2).add ((hs y).mul_left 2))
  rw [map_sub]
  nlinarith [sq_nonneg (c (ℓ + L) x + c (ℓ + L) y)]

theorem sa9_tail_continuous (L : ℕ) : Continuous (sa9_tail c L) := by
  unfold sa9_tail
  exact (continuous_norm.pow 2).sub (continuous_finset_sum _ fun ℓ _ => (c ℓ).continuous.pow 2)

theorem sa9_norm_sq_split (hc : Sa9Parseval c) (L : ℕ) (x : H) :
    ‖x‖ ^ 2 = ∑ ℓ ∈ Finset.range L, (c ℓ x) ^ 2 + sa9_tail c L x := by
  unfold sa9_tail; ring

/-- Relative compactness from a norm bound and tails. -/
theorem sa9_isCompact_closure (hc : Sa9Parseval c) (R : ℝ) (Lk : ℕ → ℕ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    IsCompact (closure {x : H | ‖x‖ ≤ R ∧ ∀ k, sa9_tail c (Lk k) x ≤ δ k}) := by
  set A : Set H := {x : H | ‖x‖ ≤ R ∧ ∀ k, sa9_tail c (Lk k) x ≤ δ k} with hA
  have htb : TotallyBounded A := by
    classical
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := (hδ.eventually (gt_mem_nhds (show (0 : ℝ) < ε ^ 2 / 8 by positivity))).exists
    set L := Lk k with hL
    set ρ : ℝ := ε / (2 * (L + 1)) with hρ
    have hρ0 : 0 < ρ := by positivity
    let Φ : H → (Fin L → ℝ) := fun x i => c i x
    have hΦ : Φ '' A ⊆ Metric.closedBall (0 : Fin L → ℝ) (max R 0) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
      intro i
      rw [Real.norm_eq_abs]
      exact (abs_le_of_sq_le_sq (sa9_coord_sq_le hc i x) (norm_nonneg x)).trans
        (hx.1.trans (le_max_left _ _))
    have htb' : TotallyBounded (Φ '' A) := (isCompact_closedBall _ _).totallyBounded.subset hΦ
    obtain ⟨t, htfin, htcov⟩ := Metric.totallyBounded_iff.1 htb' (ρ / 2) (by positivity)
    let xz : (Fin L → ℝ) → H := fun z =>
      if h : ∃ x ∈ A, dist (Φ x) z < ρ / 2 then h.choose else 0
    have hxz : ∀ z, ∀ x ∈ A, dist (Φ x) z < ρ / 2 → xz z ∈ A ∧ dist (Φ (xz z)) z < ρ / 2 := by
      intro z x hx hxd
      have h : ∃ x ∈ A, dist (Φ x) z < ρ / 2 := ⟨x, hx, hxd⟩
      simp only [xz, dif_pos h]
      exact h.choose_spec
    refine ⟨xz '' t, htfin.image _, ?_⟩
    intro x hx
    have hΦx : Φ x ∈ Φ '' A := ⟨x, hx, rfl⟩
    obtain ⟨z, hzt, hz⟩ := Set.mem_iUnion₂.1 (htcov hΦx)
    have hz' : dist (Φ x) z < ρ / 2 := hz
    obtain ⟨hxzA, hxzd⟩ := hxz z x hx hz'
    refine Set.mem_iUnion₂.2 ⟨xz z, ⟨z, hzt, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hcoord : ∀ i : Fin L, |c i x - c i (xz z)| < ρ := by
      intro i
      have h1 : dist (Φ x) (Φ (xz z)) < ρ := by
        calc dist (Φ x) (Φ (xz z)) ≤ dist (Φ x) z + dist z (Φ (xz z)) := dist_triangle _ _ _
          _ < ρ / 2 + ρ / 2 := by rw [dist_comm z]; exact add_lt_add hz' hxzd
          _ = ρ := by ring
      have h2 : dist (Φ x i) (Φ (xz z) i) < ρ := lt_of_le_of_lt (dist_le_pi_dist _ _ i) h1
      simpa [Φ, Real.dist_eq] using h2
    have hsplit := sa9_norm_sq_split hc L (x - xz z)
    have hsum : ∑ ℓ ∈ Finset.range L, (c ℓ (x - xz z)) ^ 2 ≤ L * ρ ^ 2 := by
      rw [Finset.sum_range]
      calc ∑ i : Fin L, (c (i : ℕ) (x - xz z)) ^ 2 ≤ ∑ _i : Fin L, ρ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [map_sub]
            exact sq_le_sq' (by linarith [abs_lt.1 (hcoord i)]) (by linarith [abs_lt.1 (hcoord i)])
        _ = L * ρ ^ 2 := by simp
    have htail : sa9_tail c L (x - xz z) ≤ 4 * (ε ^ 2 / 8) := by
      refine (sa9_tail_sub_le hc L x (xz z)).trans ?_
      have h1 := hx.2 k
      have h2 := hxzA.2 k
      linarith
    have hLρ : (L : ℝ) * ρ ^ 2 ≤ ε ^ 2 / 4 := by
      rw [hρ, div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith [sq_nonneg ε, mul_nonneg (sq_nonneg ε) hL0, mul_nonneg (sq_nonneg ε) (sq_nonneg (L : ℝ))]
    have hlt : ‖x - xz z‖ ^ 2 < ε ^ 2 := by nlinarith [sq_nonneg ε]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
  exact htb.closure.isCompact_of_isClosed isClosed_closure

end Abstract

section Prob

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] {c : ℕ → H →L[ℝ] ℝ}
  {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]

/-- A positive extended real is bounded below by `ofReal r` with `r > 0`, `r ≤ 1`. -/
theorem sa9_exists_real (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ ε := by
  refine ⟨(min ε 1).toReal, ?_, ?_⟩
  · exact ENNReal.toReal_pos (lt_min hε one_pos).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
  · rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    exact min_le_left _ _

theorem sa9_tightFam_of_tails (hc : Sa9Parseval c) (J : Set ℕ) (F : ∀ N, Ω N → H)
    (hF : ∀ N ∈ J, Measurable (F N)) {B : ℝ}
    (hB : ∀ N ∈ J, ∫⁻ ζ, ENNReal.ofReal (‖F N ζ‖ ^ 2) ∂(P N) ≤ ENNReal.ofReal B)
    (htail : ∀ η : ℝ, 0 < η → ∃ L : ℕ, ∀ N ∈ J,
      ∫⁻ ζ, ENNReal.ofReal (sa9_tail c L (F N ζ)) ∂(P N) ≤ ENNReal.ofReal η) :
    Sa9TightFam J P F := by
  intro ε hε
  obtain ⟨r, hr, hrε⟩ := sa9_exists_real ε hε
  set Rsq : ℝ := 4 * (max B 0 + 1) / r with hRsq
  have hRsq0 : 0 < Rsq := by have := le_max_right B 0; positivity
  set R : ℝ := Real.sqrt Rsq with hR
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hδ
  have hδ0 : ∀ k, 0 < δ k := fun k => by simp only [hδ]; positivity
  have hδt : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set η : ℕ → ℝ := fun k => r * δ k / 2 ^ (k + 2) with hη
  have hη0 : ∀ k, 0 < η k := fun k => by simp only [hη]; have := hδ0 k; positivity
  choose Lk hLk using fun k => htail (η k) (hη0 k)
  refine ⟨closure {x : H | ‖x‖ ≤ R ∧ ∀ k, sa9_tail c (Lk k) x ≤ δ k},
    sa9_isCompact_closure hc R Lk δ hδt, fun N hN => ?_⟩
  set A : Set H := {x : H | ‖x‖ ≤ R ∧ ∀ k, sa9_tail c (Lk k) x ≤ δ k} with hA
  have hsub : {ζ | F N ζ ∉ closure A} ⊆ {ζ | ENNReal.ofReal Rsq ≤ ENNReal.ofReal (‖F N ζ‖ ^ 2)} ∪
      ⋃ k, {ζ | ENNReal.ofReal (δ k) ≤ ENNReal.ofReal (sa9_tail c (Lk k) (F N ζ))} := by
    intro ζ hζ
    have hnA : F N ζ ∉ A := fun h => hζ (subset_closure h)
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, not_le] at hcon
    apply hnA
    refine ⟨?_, fun k => ?_⟩
    · by_contra hlt
      push Not at hlt
      have h2 : Rsq ≤ ‖F N ζ‖ ^ 2 := by
        have := mul_self_lt_mul_self (Real.sqrt_nonneg Rsq) hlt
        rw [Real.mul_self_sqrt hRsq0.le] at this
        nlinarith
      exact absurd (ENNReal.ofReal_le_ofReal h2) (not_le.2 hcon.1)
    · have := (hcon.2 k)
      by_contra hlt
      push Not at hlt
      exact absurd (ENNReal.ofReal_le_ofReal hlt.le) (not_le.2 this)
  have hnorm : P N {ζ | ENNReal.ofReal Rsq ≤ ENNReal.ofReal (‖F N ζ‖ ^ 2)} ≤ ENNReal.ofReal (r / 4) := by
    have hm : AEMeasurable (fun ζ => ENNReal.ofReal (‖F N ζ‖ ^ 2)) (P N) :=
      (ENNReal.measurable_ofReal.comp ((hF N hN).norm.pow_const 2)).aemeasurable
    refine (meas_ge_le_lintegral_div hm (ENNReal.ofReal_pos.2 hRsq0).ne' ENNReal.ofReal_ne_top).trans ?_
    refine (ENNReal.div_le_div_right (hB N hN) _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos hRsq0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hRsq, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := le_max_left B 0
    have := le_max_right B 0
    nlinarith
  have hk : ∀ k, P N {ζ | ENNReal.ofReal (δ k) ≤ ENNReal.ofReal (sa9_tail c (Lk k) (F N ζ))} ≤
      ENNReal.ofReal r * (2⁻¹) ^ (k + 2) := by
    intro k
    have hm : AEMeasurable (fun ζ => ENNReal.ofReal (sa9_tail c (Lk k) (F N ζ))) (P N) :=
      (ENNReal.measurable_ofReal.comp ((sa9_tail_continuous (c := c) (Lk k)).measurable.comp
        (hF N hN))).aemeasurable
    refine (meas_ge_le_lintegral_div hm (ENNReal.ofReal_pos.2 (hδ0 k)).ne' ENNReal.ofReal_ne_top).trans ?_
    refine (ENNReal.div_le_div_right (hLk k N hN) _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos (hδ0 k)]
    have : η k / δ k = r * (2⁻¹ : ℝ) ^ (k + 2) := by
      have := (hδ0 k).ne'
      simp only [hη, inv_pow]; field_simp
    have e : ENNReal.ofReal (2⁻¹ : ℝ) = 2⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
    rw [this, ENNReal.ofReal_mul hr.le, ENNReal.ofReal_pow (by norm_num), e]
  have hsum : ∑' k : ℕ, ENNReal.ofReal r * (2⁻¹ : ℝ≥0∞) ^ (k + 2) = ENNReal.ofReal r / 2 := by
    have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have hterm : ∀ k : ℕ, ENNReal.ofReal r * (2⁻¹ : ℝ≥0∞) ^ (k + 2) =
        (ENNReal.ofReal r * 2⁻¹ ^ 2) * 2⁻¹ ^ k := fun k => by rw [pow_add]; ring
    rw [tsum_congr hterm]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    have key : (2⁻¹ : ℝ≥0∞) ^ 2 * 2 = 2⁻¹ := by
      rw [pow_two, mul_assoc, ENNReal.inv_mul_cancel h2 h2', mul_one]
    rw [mul_assoc, key, ENNReal.div_eq_inv_mul, mul_comm]
  calc P N {ζ | F N ζ ∉ closure A}
      ≤ P N ({ζ | ENNReal.ofReal Rsq ≤ ENNReal.ofReal (‖F N ζ‖ ^ 2)} ∪
        ⋃ k, {ζ | ENNReal.ofReal (δ k) ≤ ENNReal.ofReal (sa9_tail c (Lk k) (F N ζ))}) := measure_mono hsub
    _ ≤ P N {ζ | ENNReal.ofReal Rsq ≤ ENNReal.ofReal (‖F N ζ‖ ^ 2)} +
        P N (⋃ k, {ζ | ENNReal.ofReal (δ k) ≤ ENNReal.ofReal (sa9_tail c (Lk k) (F N ζ))}) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (r / 4) + ∑' k, ENNReal.ofReal r * (2⁻¹) ^ (k + 2) :=
        add_le_add hnorm ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hk))
    _ = ENNReal.ofReal (r / 4) + ENNReal.ofReal r / 2 := by rw [hsum]
    _ ≤ ENNReal.ofReal r := by
        have h4 : ENNReal.ofReal (r / 4) ≤ ENNReal.ofReal r / 4 := by
          rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_div_of_pos (by norm_num)]
        calc ENNReal.ofReal (r / 4) + ENNReal.ofReal r / 2 ≤ ENNReal.ofReal r / 4 + ENNReal.ofReal r / 2 :=
              add_le_add h4 le_rfl
          _ ≤ ENNReal.ofReal r / 2 + ENNReal.ofReal r / 2 := by
              gcongr
              norm_num
          _ = ENNReal.ofReal r := ENNReal.add_halves _
    _ ≤ ε := hrε

end Prob

section Combine

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))

theorem sa9_tightFam_add {H : Type*} [AddCommGroup H] [TopologicalSpace H] [ContinuousAdd H]
    {J : Set ℕ} {A B : ∀ N, Ω N → H} (hA : Sa9TightFam J P A) (hB : Sa9TightFam J P B) :
    Sa9TightFam J P (fun N ζ => A N ζ + B N ζ) := by
  intro ε hε
  obtain ⟨K₁, hK₁, h₁⟩ := hA (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨K₂, hK₂, h₂⟩ := hB (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨K₁ + K₂, hK₁.add hK₂, fun N hN => ?_⟩
  calc P N {ζ | A N ζ + B N ζ ∉ K₁ + K₂}
      ≤ P N ({ζ | A N ζ ∉ K₁} ∪ {ζ | B N ζ ∉ K₂}) := by
        refine measure_mono fun ζ hζ => ?_
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
        exact hζ (Set.add_mem_add hcon.1 hcon.2)
    _ ≤ P N {ζ | A N ζ ∉ K₁} + P N {ζ | B N ζ ∉ K₂} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (h₁ N hN) (h₂ N hN)
    _ = ε := ENNReal.add_halves ε

theorem sa9_tightFam_mono {H : Type*} [TopologicalSpace H] {J J' : Set ℕ} {F : ∀ N, Ω N → H}
    (h : Sa9TightFam J P F) (hJ : J' ⊆ J) : Sa9TightFam J' P F := fun ε hε => by
  obtain ⟨K, hK, hKe⟩ := h ε hε
  exact ⟨K, hK, fun N hN => hKe N (hJ hN)⟩

theorem sa9_tightFam_union {H : Type*} [TopologicalSpace H] {J₁ J₂ : Set ℕ} {F : ∀ N, Ω N → H}
    (h₁ : Sa9TightFam J₁ P F) (h₂ : Sa9TightFam J₂ P F) : Sa9TightFam (J₁ ∪ J₂) P F := by
  intro ε hε
  obtain ⟨K₁, hK₁, e₁⟩ := h₁ ε hε
  obtain ⟨K₂, hK₂, e₂⟩ := h₂ ε hε
  refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun N hN => ?_⟩
  rcases hN with hN | hN
  · exact (measure_mono fun ζ (hζ : F N ζ ∉ K₁ ∪ K₂) => (fun h => hζ (Or.inl h) : F N ζ ∉ K₁)).trans (e₁ N hN)
  · exact (measure_mono fun ζ (hζ : F N ζ ∉ K₁ ∪ K₂) => (fun h => hζ (Or.inr h) : F N ζ ∉ K₂)).trans (e₂ N hN)

/-- A single random element of a Polish space is tight. -/
theorem sa9_tightFam_single {H : Type*} [MetricSpace H] [SecondCountableTopology H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [∀ N, IsProbabilityMeasure (P N)] (N : ℕ) (F : ∀ N, Ω N → H)
    (hF : Measurable (F N)) : Sa9TightFam {N} P F := by
  intro ε hε
  have h := (isTightMeasureSet_singleton (μ := (P N).map (F N)))
  obtain ⟨K, hK, hKe⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 h ε hε
  refine ⟨K, hK, fun N' hN' => ?_⟩
  rw [Set.mem_singleton_iff] at hN'
  subst hN'
  have := hKe ((P N').map (F N')) rfl
  rwa [Measure.map_apply hF hK.isClosed.measurableSet.compl] at this

theorem sa9_tightFam_finite {H : Type*} [MetricSpace H] [SecondCountableTopology H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [∀ N, IsProbabilityMeasure (P N)] (F : ∀ N, Ω N → H)
    {J : Set ℕ} (hJ : J.Finite) (hF : ∀ N ∈ J, Measurable (F N)) : Sa9TightFam J P F := by
  revert hF
  induction J, hJ using Set.Finite.induction_on with
  | empty =>
    intro _ ε hε
    exact ⟨∅, isCompact_empty, fun N hN => absurd hN (Set.notMem_empty N)⟩
  | insert ha hs ih =>
    intro hF
    rw [Set.insert_eq]
    exact sa9_tightFam_union P (sa9_tightFam_single P _ F (hF _ (Set.mem_insert _ _)))
      (ih fun N hN => hF N (Set.mem_insert_of_mem _ hN))

end Combine

section L1

open scoped BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace H] [BorelSpace H]
  {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]

/-- If `E‖G_N‖ ≤ c_N → 0` then the laws of `G_N` converge weakly to `δ₀`. -/
theorem sa9_weak_zero (G : ∀ N, Ω N → H) (hG : ∀ N, Measurable (G N)) (c : ℕ → ℝ)
    (hc : Tendsto c atTop (𝓝 0)) (hc0 : ∀ N, 0 ≤ c N)
    (hL1 : ∀ N, ∫⁻ ζ, ‖G N ζ‖ₑ ∂(P N) ≤ ENNReal.ofReal (c N)) (f : H →ᵇ ℝ) :
    Tendsto (fun N => ∫ x, f x ∂((P N).map (G N))) atTop (𝓝 (∫ x, f x ∂(Measure.dirac (0 : H)))) := by
  rw [integral_dirac]
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨ρ, hρ, hfρ⟩ := Metric.continuous_iff.1 f.continuous 0 (η / 4) (by positivity)
  have hfn : 0 ≤ ‖f‖ := norm_nonneg f
  have hev : ∀ᶠ N in atTop, c N < ρ * η / (8 * (‖f‖ + 1)) := by
    refine hc.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN => ?_⟩
  have hcN := hN₀ N hN
  rw [Real.dist_eq, integral_map (hG N).aemeasurable f.continuous.aestronglyMeasurable]
  set E : Set (Ω N) := {ζ | ρ ≤ ‖G N ζ‖} with hE
  have hEm : MeasurableSet E := measurableSet_le measurable_const (hG N).norm
  have hPE : (P N).real E ≤ c N / ρ := by
    have h1 : (P N) E ≤ ENNReal.ofReal (c N) / ENNReal.ofReal ρ := by
      have hm : AEMeasurable (fun ζ => ‖G N ζ‖ₑ) (P N) := (hG N).enorm.aemeasurable
      have := meas_ge_le_lintegral_div hm (ENNReal.ofReal_pos.2 hρ).ne' ENNReal.ofReal_ne_top
      refine le_trans (measure_mono fun ζ hζ => ?_) (this.trans (ENNReal.div_le_div_right (hL1 N) _))
      simp only [Set.mem_ofPred_eq] at hζ ⊢
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal hζ
    rw [← ENNReal.ofReal_div_of_pos hρ] at h1
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (by have := hc0 N; positivity)] at this
  have hint : Integrable (fun ζ => f (G N ζ)) (P N) :=
    Integrable.of_bound (f.continuous.measurable.comp (hG N)).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun ζ => f.norm_coe_le_norm _)
  have hbound : ∀ ζ, |f (G N ζ) - f 0| ≤ η / 4 + 2 * ‖f‖ * E.indicator (fun _ => (1 : ℝ)) ζ := by
    intro ζ
    by_cases hζ : ζ ∈ E
    · rw [Set.indicator_of_mem hζ]
      have := f.norm_coe_le_norm (G N ζ)
      have := f.norm_coe_le_norm 0
      rw [Real.norm_eq_abs] at *
      have := abs_sub (f (G N ζ)) (f 0)
      nlinarith
    · rw [Set.indicator_of_notMem hζ]
      have hlt : ‖G N ζ‖ < ρ := not_le.1 hζ
      have := hfρ (G N ζ) (by simpa [dist_zero_right] using hlt)
      rw [Real.dist_eq] at this
      linarith
  calc |∫ ζ, f (G N ζ) ∂(P N) - f 0|
      = |∫ ζ, (f (G N ζ) - f 0) ∂(P N)| := by
        rw [integral_sub hint (integrable_const _), integral_const]; simp
    _ ≤ ∫ ζ, |f (G N ζ) - f 0| ∂(P N) := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P N) (fun ζ => f (G N ζ) - f 0)
    _ ≤ ∫ ζ, (η / 4 + 2 * ‖f‖ * E.indicator (fun _ => (1 : ℝ)) ζ) ∂(P N) :=
        integral_mono_of_nonneg (ae_of_all _ fun ζ => abs_nonneg _)
          ((integrable_const _).add (((integrable_const (1 : ℝ)).indicator hEm).const_mul _))
          (ae_of_all _ hbound)
    _ = η / 4 + 2 * ‖f‖ * (P N).real E := by
        rw [integral_add (integrable_const _) (((integrable_const (1 : ℝ)).indicator hEm).const_mul _),
          integral_const, integral_const_mul, integral_indicator hEm]
        simp [Measure.real]
    _ < η := by
        have h1 : 2 * ‖f‖ * (P N).real E ≤ 2 * ‖f‖ * (c N / ρ) :=
          mul_le_mul_of_nonneg_left hPE (by positivity)
        have h2 : 2 * ‖f‖ * (c N / ρ) < η / 2 := by
          rw [← mul_div_assoc, div_lt_iff₀ hρ]
          have hcN' : c N * (8 * (‖f‖ + 1)) < ρ * η := by
            rwa [lt_div_iff₀ (by positivity)] at hcN
          nlinarith [hc0 N]
        linarith

theorem sa9_tightFam_of_l1 (J : Set ℕ) (F : ∀ N, Ω N → H) (hF : ∀ N ∈ J, Measurable (F N)) (c : ℕ → ℝ)
    (hc : Tendsto c atTop (𝓝 0))
    (hL1 : ∀ N ∈ J, ∫⁻ ζ, ‖F N ζ‖ₑ ∂(P N) ≤ ENNReal.ofReal (c N)) : Sa9TightFam J P F := by
  classical
  let G : ∀ N, Ω N → H := fun N ζ => if N ∈ J then F N ζ else 0
  have hG : ∀ N, Measurable (G N) := fun N => by
    by_cases hN : N ∈ J
    · simpa [G, hN] using hF N hN
    · simp [G, hN]
  set c' : ℕ → ℝ := fun N => if N ∈ J then max (c N) 0 else 0 with hc'
  have hc'0 : ∀ N, 0 ≤ c' N := fun N => by
    simp only [hc']; split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hc't : Tendsto c' atTop (𝓝 0) := by
    refine squeeze_zero (fun N => hc'0 N) (fun N => ?_) (by simpa using hc.max (tendsto_const_nhds (x := (0 : ℝ))))
    simp only [hc']; split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  have hL1' : ∀ N, ∫⁻ ζ, ‖G N ζ‖ₑ ∂(P N) ≤ ENNReal.ofReal (c' N) := fun N => by
    by_cases hN : N ∈ J
    · simp only [G, hc', hN, if_true]
      exact (hL1 N hN).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · simp [G, hc', hN]
  have hw := fun f => sa9_weak_zero P G hG c' hc't hc'0 hL1' f
  have htight := HRS.MS.IidInit.sa27_tight_of_tendsto (fun N => (P N).map (G N)) (Measure.dirac (0 : H)) hw
  intro ε hε
  obtain ⟨K, hK, hKe⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 htight ε hε
  refine ⟨K, hK, fun N hN => ?_⟩
  have := hKe ((P N).map (G N)) ⟨N, rfl⟩
  rw [Measure.map_apply (hG N) hK.isClosed.measurableSet.compl] at this
  convert this using 2
  ext ζ
  simp [G, hN]

end L1

end HRS.MS.MainRdPath
