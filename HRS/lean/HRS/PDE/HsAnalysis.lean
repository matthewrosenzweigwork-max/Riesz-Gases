import HRS.PDE.Fourier

/-!
# Weighted-`ℓ²` analysis for the Sobolev scale `H^m` of coefficient sequences

Auxiliary file of the torus PDE layer (package ADJ-01), used for the strong continuity
`forward_strong_continuity` and for the passage to the limit `galerkin_limit` in
`HRS/PDE/WellPosed.lean`.  It contains

* elementary facts on `sobWeight`, `MemHs`, `hsNormSq`;
* two abstract convergence lemmas: a *pairing* lemma (bounded + coordinatewise convergent
  sequences converge weakly against a fixed `ℓ²` sequence) and a *tail* lemma (bounded +
  coordinatewise null sequences are null in a weaker weighted norm);
* boundedness of weakly continuous paths (uniform boundedness principle);
* weak continuity of bounded, coordinatewise continuous paths;
* the proof of the strong continuity statement.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### Elementary facts about the weights -/

lemma one_le_sobBase (k : Lattice d) : 1 ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  have : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
  linarith

lemma sobWeight_pos (m : ℝ) (k : Lattice d) : 0 < sobWeight m k :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_sobBase k)) _

lemma sobWeight_mono {m m' : ℝ} (h : m' ≤ m) (k : Lattice d) : sobWeight m' k ≤ sobWeight m k :=
  Real.rpow_le_rpow_of_exponent_le (one_le_sobBase k) h

lemma sobWeight_add (a b : ℝ) (k : Lattice d) :
    sobWeight (a + b) k = sobWeight a k * sobWeight b k :=
  Real.rpow_add (lt_of_lt_of_le one_pos (one_le_sobBase k)) _ _

lemma sobWeight_one (k : Lattice d) :
    sobWeight 1 k = 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := Real.rpow_one _

lemma MemHs.mono {m m' : ℝ} (h : m' ≤ m) {c : Coeff d} (hc : MemHs m c) : MemHs m' c :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_right (sobWeight_mono h k) (sq_nonneg _)) hc

lemma hsNormSq_nonneg (m : ℝ) (c : Coeff d) : 0 ≤ hsNormSq m c :=
  tsum_nonneg fun k => mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _)

lemma hsNormSq_mono {m m' : ℝ} (h : m' ≤ m) {c : Coeff d} (hc : MemHs m c) :
    hsNormSq m' c ≤ hsNormSq m c :=
  (hc.mono h).tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (sobWeight_mono h k) (sq_nonneg _))
    hc

lemma sobWeight_mul_sq_le_hsNormSq {m : ℝ} {c : Coeff d} (hc : MemHs m c) (k : Lattice d) :
    sobWeight m k * ‖c k‖ ^ 2 ≤ hsNormSq m c :=
  hc.le_tsum k fun j _ => mul_nonneg (sobWeight_pos _ j).le (sq_nonneg _)

lemma memHs_of_sum_le {m : ℝ} {c : Coeff d} {C : ℝ}
    (h : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight m k * ‖c k‖ ^ 2 ≤ C) :
    MemHs m c ∧ hsNormSq m c ≤ C := by
  have hs : MemHs m c :=
    summable_of_sum_le (fun k => mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _)) h
  exact ⟨hs, hs.tsum_le_of_sum_le h⟩

lemma sum_le_hsNormSq {m : ℝ} {c : Coeff d} (hc : MemHs m c) (S : Finset (Lattice d)) :
    ∑ k ∈ S, sobWeight m k * ‖c k‖ ^ 2 ≤ hsNormSq m c :=
  hc.sum_le_tsum S fun j _ => mul_nonneg (sobWeight_pos _ j).le (sq_nonneg _)

lemma finite_enorm_le (R : ℝ) : {k : Lattice d | Lattice.enorm k ≤ R}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-⌈R⌉) ⌈R⌉)
    (fun _ => Set.finite_Icc _ _)).subset ?_
  intro k hk i _
  have h1 : |(k i : ℝ)| ≤ Lattice.enorm k := by
    have := PiLp.norm_apply_le (Lattice.toEuc k) i
    simpa [Lattice.toEuc, Lattice.enorm] using this
  have h3 : |k i| ≤ ⌈R⌉ := by
    have h2 : ((|k i| : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by
      rw [Int.cast_abs]; exact (h1.trans hk).trans (Int.le_ceil R)
    exact_mod_cast h2
  exact abs_le.mp h3

lemma tendsto_sobWeight_cofinite {e : ℝ} (he : e < 0) :
    Tendsto (sobWeight e : Lattice d → ℝ) cofinite (𝓝 0) := by
  have hbase : Tendsto (fun k : Lattice d => 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)
      cofinite atTop := by
    rw [tendsto_atTop]
    intro b
    rw [eventually_cofinite]
    refine (finite_enorm_le (d := d) (|b| + 1)).subset ?_
    intro k hk
    simp only [Set.mem_ofPred_eq, not_le] at hk ⊢
    by_contra hcon
    push Not at hcon
    have h1 : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have h2 : (|b| + 1) ^ 2 < Lattice.enorm k ^ 2 := by
      have := Lattice.enorm k
      exact pow_lt_pow_left₀ hcon (by positivity) two_ne_zero
    nlinarith [le_abs_self b, sq_nonneg (Lattice.enorm k), abs_nonneg b]
  have := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).comp hbase
  have h2 : (sobWeight e : Lattice d → ℝ) = fun k => (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (-(-e)) := by
    funext k; simp [sobWeight]
  rw [h2]; exact this

/-! ### Abstract convergence lemmas -/

section Abstract

variable {ι : Type*}

/-- Cauchy–Schwarz for nonnegative sequences with uniformly bounded partial square sums. -/
lemma summable_mul_of_sq_bound (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (X Y : ℝ) (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hX : ∀ S : Finset ι, ∑ i ∈ S, x i ^ 2 ≤ X ^ 2)
    (hY : ∀ S : Finset ι, ∑ i ∈ S, y i ^ 2 ≤ Y ^ 2) :
    Summable (fun i => x i * y i) ∧ ∑' i, x i * y i ≤ X * Y := by
  have hS : ∀ S : Finset ι, ∑ i ∈ S, x i * y i ≤ X * Y := by
    intro S
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq S x y
    have h2 : (∑ i ∈ S, x i * y i) ^ 2 ≤ (X * Y) ^ 2 := by
      calc _ ≤ (∑ i ∈ S, x i ^ 2) * ∑ i ∈ S, y i ^ 2 := h1
        _ ≤ X ^ 2 * Y ^ 2 :=
          mul_le_mul (hX S) (hY S) (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)
        _ = (X * Y) ^ 2 := by ring
    exact (abs_le_of_sq_le_sq' h2 (mul_nonneg hX0 hY0)).2
  have hsum : Summable (fun i => x i * y i) :=
    summable_of_sum_le (fun i => mul_nonneg (hx i) (hy i)) hS
  exact ⟨hsum, hsum.tsum_le_of_sum_le hS⟩

/-- Tail estimate: split off a finite set `S` and estimate the rest by Cauchy–Schwarz. -/
lemma norm_tsum_mul_le_split (f v : ι → ℂ) (S : Finset ι) (X Y : ℝ) (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hf : ∀ T : Finset ι, ∑ i ∈ T, ‖f i‖ ^ 2 ≤ X ^ 2)
    (hv : ∀ T : Finset ι, Disjoint T S → ∑ i ∈ T, ‖v i‖ ^ 2 ≤ Y ^ 2) :
    Summable (fun i => ‖f i * v i‖) ∧
      ‖∑' i, f i * v i‖ ≤ ∑ i ∈ S, ‖f i‖ * ‖v i‖ + X * Y := by
  classical
  set x : ι → ℝ := fun i => if i ∈ S then 0 else ‖f i‖ with hx
  set y : ι → ℝ := fun i => if i ∈ S then 0 else ‖v i‖ with hy
  have hx0 : ∀ i, 0 ≤ x i := fun i => by simp only [hx]; split_ifs <;> positivity
  have hy0 : ∀ i, 0 ≤ y i := fun i => by simp only [hy]; split_ifs <;> positivity
  have hxX : ∀ T : Finset ι, ∑ i ∈ T, x i ^ 2 ≤ X ^ 2 := by
    intro T
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hf T)
    simp only [hx]; split_ifs <;> simp
  have hyY : ∀ T : Finset ι, ∑ i ∈ T, y i ^ 2 ≤ Y ^ 2 := by
    intro T
    have : ∑ i ∈ T, y i ^ 2 = ∑ i ∈ T.filter (· ∉ S), ‖v i‖ ^ 2 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hy]; split_ifs <;> simp_all
    rw [this]
    refine hv _ ?_
    rw [Finset.disjoint_left]
    intro i hi hiS
    exact (Finset.mem_filter.mp hi).2 hiS
  obtain ⟨hsum, hle⟩ := summable_mul_of_sq_bound x y hx0 hy0 X Y hX0 hY0 hxX hyY
  set A : ι → ℝ := fun i => if i ∈ S then ‖f i‖ * ‖v i‖ else 0 with hA
  have hAsum : Summable A := by
    refine summable_of_ne_finset_zero (s := S) fun i hi => ?_
    simp [hA, hi]
  have hpt : ∀ i, ‖f i * v i‖ = A i + x i * y i := by
    intro i
    simp only [hA, hx, hy, norm_mul]
    split_ifs <;> simp
  have hnorm : Summable (fun i => ‖f i * v i‖) := by
    simp_rw [hpt]; exact hAsum.add hsum
  refine ⟨hnorm, ?_⟩
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  simp_rw [hpt]
  rw [hAsum.tsum_add hsum]
  have : ∑' i, A i = ∑ i ∈ S, ‖f i‖ * ‖v i‖ := by
    rw [tsum_eq_sum (s := S) (fun i hi => by simp [hA, hi])]
    exact Finset.sum_congr rfl fun i hi => by simp [hA, hi]
  rw [this]
  linarith

/-- **Pairing lemma** (weak convergence in `ℓ²`): a family `u a` of sequences with uniformly
bounded partial square sums that converges coordinatewise converges against every fixed `ℓ²`
sequence `v`. -/
lemma tendsto_tsum_mul {α : Type*} {l : Filter α} [l.NeBot] (u : α → ι → ℂ) (u0 v : ι → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ᶠ a in l, ∀ S : Finset ι, ∑ i ∈ S, ‖u a i‖ ^ 2 ≤ B ^ 2)
    (hv : Summable fun i => ‖v i‖ ^ 2)
    (hc : ∀ i, Tendsto (fun a => u a i) l (𝓝 (u0 i))) :
    Tendsto (fun a => ∑' i, u a i * v i) l (𝓝 (∑' i, u0 i * v i)) := by
  classical
  have hu0 : ∀ S : Finset ι, ∑ i ∈ S, ‖u0 i‖ ^ 2 ≤ B ^ 2 := by
    intro S
    refine le_of_tendsto (tendsto_finsetSum S fun i _ => ((hc i).norm).pow 2) ?_
    filter_upwards [hu] with a ha using ha S
  have hVtot : ∀ T : Finset ι, ∑ i ∈ T, ‖v i‖ ^ 2 ≤ ∑' i, ‖v i‖ ^ 2 := fun T =>
    hv.sum_le_tsum T fun i _ => sq_nonneg _
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε / (4 * B + 4) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨S, hS⟩ := (summable_iff_vanishing.mp hv) (Set.Iio (η ^ 2)) (Iio_mem_nhds (by positivity))
  have hvS : ∀ T : Finset ι, Disjoint T S → ∑ i ∈ T, ‖v i‖ ^ 2 ≤ η ^ 2 := fun T hT =>
    (hS T hT).le
  -- the finite part tends to zero
  have hfin : Tendsto (fun a => ∑ i ∈ S, ‖u a i - u0 i‖ * ‖v i‖) l (𝓝 0) := by
    have : Tendsto (fun a => ∑ i ∈ S, ‖u a i - u0 i‖ * ‖v i‖) l (𝓝 (∑ i ∈ S, (0 : ℝ) * ‖v i‖)) :=
      tendsto_finsetSum S fun i _ =>
        (tendsto_iff_norm_sub_tendsto_zero.mp (hc i) |>.mul_const _)
    simpa using this
  have hsmall : ∀ᶠ a in l, ∑ i ∈ S, ‖u a i - u0 i‖ * ‖v i‖ < ε / 2 :=
    hfin.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hu, hsmall] with a ha hsm
  have hw : ∀ T : Finset ι, ∑ i ∈ T, ‖u a i - u0 i‖ ^ 2 ≤ (2 * B) ^ 2 := by
    intro T
    calc ∑ i ∈ T, ‖u a i - u0 i‖ ^ 2
        ≤ ∑ i ∈ T, (2 * ‖u a i‖ ^ 2 + 2 * ‖u0 i‖ ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := norm_sub_le (u a i) (u0 i)
          nlinarith [norm_nonneg (u a i - u0 i), norm_nonneg (u a i), norm_nonneg (u0 i),
            sq_nonneg (‖u a i‖ - ‖u0 i‖)]
      _ = 2 * ∑ i ∈ T, ‖u a i‖ ^ 2 + 2 * ∑ i ∈ T, ‖u0 i‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ (2 * B) ^ 2 := by nlinarith [ha T, hu0 T]
  have hfa : ∀ T : Finset ι, ∑ i ∈ T, ‖u a i‖ ^ 2 ≤ B ^ 2 := ha
  have hsa := (norm_tsum_mul_le_split (u a) v ∅ B (Real.sqrt (∑' i, ‖v i‖ ^ 2)) hB
    (Real.sqrt_nonneg _) ha (fun T _ => by
      rw [Real.sq_sqrt (tsum_nonneg fun i => sq_nonneg _)]; exact hVtot T)).1
  have hs0 := (norm_tsum_mul_le_split u0 v ∅ B (Real.sqrt (∑' i, ‖v i‖ ^ 2)) hB
    (Real.sqrt_nonneg _) hu0 (fun T _ => by
      rw [Real.sq_sqrt (tsum_nonneg fun i => sq_nonneg _)]; exact hVtot T)).1
  have hdiff : ∑' i, u a i * v i - ∑' i, u0 i * v i = ∑' i, (u a i - u0 i) * v i := by
    rw [← Summable.tsum_sub (Summable.of_norm hsa) (Summable.of_norm hs0)]
    simp_rw [sub_mul]
  rw [dist_eq_norm, hdiff]
  have := (norm_tsum_mul_le_split (fun i => u a i - u0 i) v S (2 * B) η (by positivity)
    hη0.le hw hvS).2
  have h2 : 2 * B * η < ε / 2 := by
    have : 2 * B * η = ε * (2 * B / (4 * B + 4)) := by rw [hη]; ring
    rw [this]
    have h3 : 2 * B / (4 * B + 4) < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    nlinarith
  linarith

/-- **Tail lemma**: if `x a i ≥ 0` has uniformly bounded sums and tends to `0` in each coordinate,
and `r i → 0` along cofinite, then `∑ r i * x a i → 0`. -/
lemma tendsto_tsum_weight_zero {α : Type*} {l : Filter α} (x : α → ι → ℝ) (r : ι → ℝ)
    (C : ℝ) (hx0 : ∀ a i, 0 ≤ x a i) (hr0 : ∀ i, 0 ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0))
    (hx : ∀ᶠ a in l, Summable (x a) ∧ ∑' i, x a i ≤ C)
    (hc : ∀ i, Tendsto (fun a => x a i) l (𝓝 0)) :
    Tendsto (fun a => ∑' i, r i * x a i) l (𝓝 0) := by
  classical
  have hC : 0 ≤ C ∨ True := Or.inr trivial
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε / (2 * (|C| + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hfin : {i | ¬ r i < η}.Finite := by
    have := (Metric.tendsto_nhds.mp hr) η hη0
    rw [eventually_cofinite] at this
    refine this.subset ?_
    intro i hi
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (hr0 i)] at hi ⊢
    exact hi
  set S : Finset ι := hfin.toFinset with hS
  have hfinT : Tendsto (fun a => ∑ i ∈ S, r i * x a i) l (𝓝 0) := by
    have : Tendsto (fun a => ∑ i ∈ S, r i * x a i) l (𝓝 (∑ i ∈ S, r i * 0)) :=
      tendsto_finsetSum S fun i _ => (hc i).const_mul _
    simpa using this
  have hsm : ∀ᶠ a in l, ∑ i ∈ S, r i * x a i < ε / 2 :=
    hfinT.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hx, hsm] with a ha hsa
  obtain ⟨hsum, hbd⟩ := ha
  set A : ι → ℝ := fun i => if i ∈ S then r i * x a i else 0 with hA
  have hAsum : Summable A := summable_of_ne_finset_zero (s := S) fun i hi => by simp [hA, hi]
  have hpt : ∀ i, r i * x a i ≤ A i + η * x a i := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hA, hi, ite_true]
      nlinarith [hx0 a i, hη0]
    · have : r i < η := by
        by_contra h
        exact hi (by rw [hS, Set.Finite.mem_toFinset]; exact h)
      simp only [hA, hi, ite_false, zero_add]
      exact mul_le_mul_of_nonneg_right this.le (hx0 a i)
  have hsum1 : Summable (fun i => r i * x a i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hr0 i) (hx0 a i)) hpt
      (hAsum.add (hsum.mul_left η))
  have hle := hsum1.tsum_le_tsum hpt (hAsum.add (hsum.mul_left η))
  rw [hAsum.tsum_add (hsum.mul_left η), tsum_mul_left] at hle
  have hA' : ∑' i, A i = ∑ i ∈ S, r i * x a i := by
    rw [tsum_eq_sum (s := S) (fun i hi => by simp [hA, hi])]
    exact Finset.sum_congr rfl fun i hi => by simp [hA, hi]
  rw [hA'] at hle
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun i => mul_nonneg (hr0 i) (hx0 a i))]
  have h3 : η * ∑' i, x a i ≤ η * (|C| + 1) :=
    mul_le_mul_of_nonneg_left (hbd.trans (by linarith [le_abs_self C])) hη0.le
  have h4 : η * (|C| + 1) = ε / 2 := by rw [hη]; field_simp
  linarith

end Abstract


/-! ### Weakly continuous paths: coordinates, boundedness -/

/-- The sequence `⟨k⟩^m c(k)` (an `ℓ²` sequence iff `c ∈ H^m`). -/
def wseq (m : ℝ) (c : Coeff d) : Lattice d → ℂ :=
  fun k => ((Real.sqrt (sobWeight m k) : ℝ) : ℂ) * c k

lemma norm_wseq_sq (m : ℝ) (c : Coeff d) (k : Lattice d) :
    ‖wseq m c k‖ ^ 2 = sobWeight m k * ‖c k‖ ^ 2 := by
  simp only [wseq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow, Real.sq_sqrt (sobWeight_pos m k).le]

lemma memℓp_wseq {m : ℝ} {c : Coeff d} (hc : MemHs m c) : Memℓp (wseq m c) 2 := by
  rw [memℓp_gen_iff (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact hc.congr fun k => (norm_wseq_sq m c k).symm

lemma deltaCoeff_memHs (m : ℝ) (k₀ : Lattice d) : MemHs m (deltaCoeff k₀) := by
  refine summable_of_ne_finset_zero (s := {k₀}) fun k hk => ?_
  have : k ≠ k₀ := by simpa using hk
  simp [deltaCoeff, this]

lemma hsInner_deltaCoeff (m : ℝ) (c : Coeff d) (k₀ : Lattice d) :
    hsInner m c (deltaCoeff k₀) = (sobWeight m k₀ : ℂ) * c k₀ := by
  unfold hsInner
  rw [tsum_eq_single k₀]
  · simp [deltaCoeff]
  · intro k hk
    simp [deltaCoeff, hk]

lemma continuousOn_coord_of_weak {m : ℝ} {t : ℝ} {F : ℝ → Coeff d} (hF : WeakContinuousInHs m F t)
    (k : Lattice d) : ContinuousOn (fun τ => F τ k) (Set.Icc 0 t) := by
  have h := continuousOn_const.mul (hF.2 (deltaCoeff k) (deltaCoeff_memHs m k)) (f := fun _ => 
    (((sobWeight m k : ℝ) : ℂ))⁻¹)
  refine h.congr fun τ _ => ?_
  have hw : ((sobWeight m k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sobWeight_pos m k).ne'
  simp only [Pi.mul_apply, hsInner_deltaCoeff]
  field_simp

/-- **Boundedness of weakly continuous paths** (uniform boundedness principle). -/
lemma bounded_of_weakContinuous {m : ℝ} {t : ℝ} {F : ℝ → Coeff d}
    (hF : WeakContinuousInHs m F t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ ∈ Set.Icc (0 : ℝ) t, hsNormSq m (F τ) ≤ B ^ 2 := by
  classical
  let u : Set.Icc (0 : ℝ) t → lp (fun _ : Lattice d => ℂ) 2 :=
    fun τ => ⟨wseq m (F τ), memℓp_wseq (hF.1 τ τ.2)⟩
  let g : Set.Icc (0 : ℝ) t → (lp (fun _ : Lattice d => ℂ) 2) →L[ℂ] ℂ :=
    fun τ => innerSL ℂ (u τ)
  have h : ∀ x : lp (fun _ : Lattice d => ℂ) 2, ∃ C, ∀ τ, ‖g τ x‖ ≤ C := by
    intro x
    set G : Coeff d := fun k => (((Real.sqrt (sobWeight m k))⁻¹ : ℝ) : ℂ) * x k with hGdef
    have hwk : ∀ k, sobWeight m k * ‖G k‖ ^ 2 = ‖x k‖ ^ 2 := by
      intro k
      have hs := Real.sqrt_pos.mpr (sobWeight_pos m k)
      simp only [hGdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_pow, inv_pow, Real.sq_sqrt (sobWeight_pos m k).le]
      field_simp [(sobWeight_pos m k).ne']
    have hG : MemHs m G := by
      have hx : Memℓp (x : Lattice d → ℂ) 2 := x.2
      rw [memℓp_gen_iff (by simp)] at hx
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx
      exact hx.congr fun k => (hwk k).symm
    have hcont := hF.2 G hG
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    refine ⟨C, fun τ => ?_⟩
    have h1 : inner ℂ x (u τ) = hsInner m (F τ) G := by
      rw [lp.inner_eq_tsum]
      unfold hsInner
      refine tsum_congr fun k => ?_
      have hs : (Real.sqrt (sobWeight m k) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos m k)).ne'
      have hsq : (Real.sqrt (sobWeight m k) : ℂ) * (Real.sqrt (sobWeight m k) : ℂ) =
          (sobWeight m k : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt (sobWeight_pos m k).le
      simp only [RCLike.inner_apply, u, hGdef, wseq, map_mul, Complex.conj_ofReal]
      show (((Real.sqrt (sobWeight m k) : ℝ) : ℂ) * F τ k) * (starRingEnd ℂ) (x k) = _
      rw [← hsq]
      push_cast
      field_simp
    calc ‖g τ x‖ = ‖inner ℂ (u τ) x‖ := by simp [g]
      _ = ‖inner ℂ x (u τ)‖ := norm_inner_symm _ _
      _ = ‖hsInner m (F τ) G‖ := by rw [h1]
      _ ≤ C := hC τ τ.2
  obtain ⟨C', hC'⟩ := banach_steinhaus h
  refine ⟨max C' 0, le_max_right _ _, fun τ hτ => ?_⟩
  have h1 : ‖g ⟨τ, hτ⟩‖ = ‖u ⟨τ, hτ⟩‖ := innerSL_apply_norm ℂ _
  have h2 : ‖u ⟨τ, hτ⟩‖ ^ 2 = hsNormSq m (F τ) := by
    have := lp.norm_rpow_eq_tsum (by simp) (u ⟨τ, hτ⟩)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
    rw [this]
    unfold hsNormSq
    refine tsum_congr fun k => ?_
    exact norm_wseq_sq m (F τ) k
  have h3 : ‖u ⟨τ, hτ⟩‖ ≤ max C' 0 := (h1 ▸ hC' ⟨τ, hτ⟩).trans (le_max_left _ _)
  rw [← h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2


/-- A path that is bounded in `H^m` on `[0,t]` and has continuous coordinates is weakly
continuous in `H^m`. -/
lemma weakContinuous_of_bdd {m t : ℝ} {G : ℝ → Coeff d}
    (hmem : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs m (G τ)) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ τ ∈ Set.Icc (0 : ℝ) t, hsNormSq m (G τ) ≤ B ^ 2)
    (hc : ∀ k, ContinuousOn (fun τ => G τ k) (Set.Icc 0 t)) : WeakContinuousInHs m G t := by
  refine ⟨hmem, fun H hH => ?_⟩
  intro τ₀ hτ₀
  have : (𝓝[Set.Icc 0 t] τ₀).NeBot := nhdsWithin_neBot_of_mem hτ₀
  have hmain : Tendsto (fun τ => ∑' k, wseq m (G τ) k *
      (((Real.sqrt (sobWeight m k) : ℝ) : ℂ) * conj (H k))) (𝓝[Set.Icc 0 t] τ₀)
      (𝓝 (∑' k, wseq m (G τ₀) k * (((Real.sqrt (sobWeight m k) : ℝ) : ℂ) * conj (H k)))) := by
    refine tendsto_tsum_mul (fun τ => wseq m (G τ)) (wseq m (G τ₀)) _ B hB0 ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with τ hτ S
      calc ∑ k ∈ S, ‖wseq m (G τ) k‖ ^ 2 = ∑ k ∈ S, sobWeight m k * ‖G τ k‖ ^ 2 :=
            Finset.sum_congr rfl fun k _ => norm_wseq_sq m _ k
        _ ≤ hsNormSq m (G τ) := sum_le_hsNormSq (hmem τ hτ) S
        _ ≤ B ^ 2 := hB τ hτ
    · refine hH.congr fun k => ?_
      rw [norm_mul, mul_pow, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (sobWeight_pos m k).le]
    · intro k
      exact (((hc k) τ₀ hτ₀).tendsto).const_mul _
  have hcongr : ∀ τ, ∑' k, wseq m (G τ) k *
      (((Real.sqrt (sobWeight m k) : ℝ) : ℂ) * conj (H k)) = hsInner m (G τ) H := by
    intro τ
    unfold hsInner
    refine tsum_congr fun k => ?_
    have hsq : (Real.sqrt (sobWeight m k) : ℂ) * (Real.sqrt (sobWeight m k) : ℂ) =
        (sobWeight m k : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (sobWeight_pos m k).le
    simp only [wseq]
    rw [← hsq]; ring
  simp only [hcongr] at hmain
  exact hmain

/-- **Strong continuity in lower norms**: a weakly continuous `H^m` path is norm-continuous in
`H^{m'}` for every `m' < m`. -/
theorem continuousInHs_of_weak {m : ℝ} {t : ℝ} {F : ℝ → Coeff d}
    (hF : WeakContinuousInHs m F t) : ∀ m' : ℝ, m' < m → ContinuousInHs m' F t := by
  intro m' hm'
  obtain ⟨B, hB0, hB⟩ := bounded_of_weakContinuous hF
  refine ⟨fun τ hτ => (hF.1 τ hτ).mono hm'.le, fun τ₀ hτ₀ => ?_⟩
  have : (𝓝[Set.Icc 0 t] τ₀).NeBot := nhdsWithin_neBot_of_mem hτ₀
  set x : ℝ → Lattice d → ℝ := fun τ k => sobWeight m k * ‖F τ k - F τ₀ k‖ ^ 2 with hx
  have hsq : Tendsto (fun τ => hsNormSq m' (F τ - F τ₀)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0) := by
    have hform : ∀ τ, hsNormSq m' (F τ - F τ₀) = ∑' k, sobWeight (m' - m) k * x τ k := by
      intro τ
      unfold hsNormSq
      refine tsum_congr fun k => ?_
      simp only [hx, Pi.sub_apply]
      have : sobWeight m' k = sobWeight (m' - m) k * sobWeight m k := by
        rw [← sobWeight_add]; ring_nf
      rw [this, mul_assoc]
    simp_rw [hform]
    refine tendsto_tsum_weight_zero x (sobWeight (m' - m)) (4 * B ^ 2)
      (fun τ k => mul_nonneg (sobWeight_pos m k).le (sq_nonneg _))
      (fun k => (sobWeight_pos _ k).le) (tendsto_sobWeight_cofinite (by linarith)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      have h := memHs_of_sum_le (m := m) (c := F τ - F τ₀) (C := 4 * B ^ 2) (fun S => by
        calc ∑ k ∈ S, sobWeight m k * ‖(F τ - F τ₀) k‖ ^ 2
            ≤ ∑ k ∈ S, (2 * (sobWeight m k * ‖F τ k‖ ^ 2) +
                2 * (sobWeight m k * ‖F τ₀ k‖ ^ 2)) := by
              refine Finset.sum_le_sum fun k _ => ?_
              have h0 := norm_sub_le (F τ k) (F τ₀ k)
              have hw := (sobWeight_pos m k).le
              simp only [Pi.sub_apply]
              have h1 : ‖F τ k - F τ₀ k‖ ^ 2 ≤ 2 * ‖F τ k‖ ^ 2 + 2 * ‖F τ₀ k‖ ^ 2 := by
                nlinarith [norm_nonneg (F τ k - F τ₀ k), norm_nonneg (F τ k),
                  norm_nonneg (F τ₀ k), sq_nonneg (‖F τ k‖ - ‖F τ₀ k‖)]
              nlinarith [mul_le_mul_of_nonneg_left h1 hw]
          _ = 2 * ∑ k ∈ S, sobWeight m k * ‖F τ k‖ ^ 2 +
                2 * ∑ k ∈ S, sobWeight m k * ‖F τ₀ k‖ ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ ≤ 2 * B ^ 2 + 2 * B ^ 2 :=
              add_le_add (mul_le_mul_of_nonneg_left
                ((sum_le_hsNormSq (hF.1 τ hτ) S).trans (hB τ hτ)) (by norm_num))
                (mul_le_mul_of_nonneg_left
                ((sum_le_hsNormSq (hF.1 τ₀ hτ₀) S).trans (hB τ₀ hτ₀)) (by norm_num))
          _ = 4 * B ^ 2 := by ring)
      exact ⟨h.1, by have := h.2; unfold hsNormSq at this; simpa [hx, Pi.sub_apply] using this⟩
    · intro k
      have hk := ((continuousOn_coord_of_weak hF k) τ₀ hτ₀).tendsto
      have : Tendsto (fun τ => ‖F τ k - F τ₀ k‖) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0) := by
        have := (hk.sub_const (F τ₀ k)).norm
        simpa using this
      have h2 := (this.pow 2).const_mul (sobWeight m k)
      simpa using h2
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [hsNorm, Function.comp_def] using this

end HRS.PDE
