import Mathlib

/-!
# S8.8.M01: finite dyadic `L²` maximal inequality

`s88_dyadic_maximal`: from `E|Y_0|² ≤ B` and `E|Y_s - Y_t|² ≤ D (s-t)²` on `[0,T]`,
`E max_{j ≤ 2^n} |Y_{Tj/2^n}|² ≤ 64 (B + T² D)`.

Route (no maxima are analysed): for every `ω` and every dyadic point, a chaining decomposition through the
dyadic ancestors gives `|Y_{n,j}| ≤ x₀ + ∑_{k<n} r_k`, with `x₀² ≤ 3Y_0² + 2(Y_T-Y_0)²` and `r_k² ≤` the sum of squares of
the `2^k` new increments of level `k+1`.  A weighted Cauchy-Schwarz inequality (weights `(3/4)^k`, total `≤ 4`) bounds the
square by `4 (a₂ + ∑ (4/3)^{k+1} s_k)`; this finite sum of `L¹` functions is integrated with the hypotheses.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

/-- Weighted Cauchy-Schwarz. -/
lemma s88_wcs (x0 : ℝ) (r : ℕ → ℝ) (n : ℕ) :
    (x0 + ∑ k ∈ Finset.range n, r k) ^ 2 ≤
      4 * (x0 ^ 2 + ∑ k ∈ Finset.range n, (4 / 3 : ℝ) ^ (k + 1) * r k ^ 2) := by
  set f : ℕ → ℝ := fun k => if k = 0 then x0 else r (k - 1) with hf
  set g : ℕ → ℝ := fun k => (3 / 4 : ℝ) ^ k with hg
  have hgpos : ∀ k ∈ Finset.range (n + 1), 0 < g k := fun k _ => by positivity
  have h1 := Finset.sq_sum_div_le_sum_sq_div (Finset.range (n + 1)) f hgpos
  have hsum_f : ∑ k ∈ Finset.range (n + 1), f k = x0 + ∑ k ∈ Finset.range n, r k := by
    rw [Finset.sum_range_succ']; simp [hf, add_comm]
  have hsum_q : ∑ k ∈ Finset.range (n + 1), f k ^ 2 / g k =
      x0 ^ 2 + ∑ k ∈ Finset.range n, (4 / 3 : ℝ) ^ (k + 1) * r k ^ 2 := by
    rw [Finset.sum_range_succ']
    have : ∀ k ∈ Finset.range n, f (k + 1) ^ 2 / g (k + 1) = (4 / 3 : ℝ) ^ (k + 1) * r k ^ 2 := by
      intro k _
      simp only [hf, hg, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      rw [div_eq_mul_inv, ← inv_pow, show ((3 / 4 : ℝ))⁻¹ = 4 / 3 by norm_num]
      ring
    rw [Finset.sum_congr rfl this]
    simp [hf, hg, add_comm]
  have hgeo : ∀ N : ℕ, ∑ k ∈ Finset.range N, g k = 4 - 4 * (3 / 4 : ℝ) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; simp only [hg]; ring
  have hg4 : ∑ k ∈ Finset.range (n + 1), g k ≤ 4 := by
    rw [hgeo]; have : 0 ≤ (3 / 4 : ℝ) ^ (n + 1) := by positivity
    linarith
  have hgp : 0 < ∑ k ∈ Finset.range (n + 1), g k :=
    Finset.sum_pos hgpos ⟨0, by simp⟩
  rw [hsum_f, hsum_q] at h1
  rw [div_le_iff₀ hgp] at h1
  have hq0 : 0 ≤ x0 ^ 2 + ∑ k ∈ Finset.range n, (4 / 3 : ℝ) ^ (k + 1) * r k ^ 2 := by
    positivity
  calc _ ≤ _ := h1
    _ ≤ _ := by nlinarith

/-- Chaining along the dyadic ancestors. -/
lemma s88_chain (y : ℝ → ℝ) (T x0 : ℝ) (r : ℕ → ℝ) (hr0 : ∀ j, 0 ≤ r j)
    (h0 : |y 0| ≤ x0) (hT : |y T| ≤ x0)
    (hr : ∀ j i : ℕ, i < 2 ^ j →
      |y (T * ((2 * i + 1 : ℕ) : ℝ) / 2 ^ (j + 1)) - y (T * ((2 * i : ℕ) : ℝ) / 2 ^ (j + 1))| ≤ r j) :
    ∀ n j : ℕ, j ≤ 2 ^ n → |y (T * (j : ℝ) / 2 ^ n)| ≤ x0 + ∑ k ∈ Finset.range n, r k := by
  intro n
  induction n with
  | zero =>
    intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simpa using h0
    · simpa using hT
  | succ n ih =>
    intro j hj
    rw [Finset.sum_range_succ]
    have hrn := hr0 n
    have hpt : ∀ i : ℕ, T * ((2 * i : ℕ) : ℝ) / 2 ^ (n + 1) = T * (i : ℝ) / 2 ^ n := by
      intro i; push_cast; rw [pow_succ]; field_simp
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [show T * ((2 * i : ℕ) : ℝ) / 2 ^ (n + 1) = T * (i : ℝ) / 2 ^ n from hpt i]
      have := ih i (by rw [pow_succ] at hj; omega)
      linarith
    · have hi : i < 2 ^ n := by rw [pow_succ] at hj; omega
      have h1 := ih i (by omega)
      have h2 := hr n i hi
      rw [hpt i] at h2
      have h3 : |y (T * ((2 * i + 1 : ℕ) : ℝ) / 2 ^ (n + 1))| ≤
          |y (T * (i : ℝ) / 2 ^ n)| + r n := by
        calc _ = |(y (T * ((2 * i + 1 : ℕ) : ℝ) / 2 ^ (n + 1)) - y (T * (i : ℝ) / 2 ^ n)) +
              y (T * (i : ℝ) / 2 ^ n)| := by ring_nf
          _ ≤ _ := (abs_add_le _ _).trans (by linarith)
      linarith

lemma s88_geo2 (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ (j + 1) ≤ 1 := by
  have : ∀ N : ℕ, ∑ j ∈ Finset.range N, (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ (j + 1) =
      1 - (2 / 3 : ℝ) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  rw [this]
  have : 0 ≤ (2 / 3 : ℝ) ^ n := by positivity
  linarith

theorem s88_dyadic_maximal {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T B D : ℝ)
    (hT : 0 < T) (hB : 0 ≤ B) (hD : 0 ≤ D) (Y : ℝ → Ω → ℝ)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (Y t) 2 P)
    (hbase : (∫⁻ z, ENNReal.ofReal ((Y 0 z) ^ 2) ∂P) ≤ ENNReal.ofReal B)
    (hinc : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ z, ENNReal.ofReal ((Y s z - Y t z) ^ 2) ∂P) ≤
        ENNReal.ofReal (D * (s - t) ^ 2)) :
    ∀ n : ℕ,
      (∫⁻ z, (⨆ j : Fin (2 ^ n + 1),
        ENNReal.ofReal ((Y (T * ((j : ℕ) : ℝ) / (2 : ℝ) ^ n) z) ^ 2)) ∂P) ≤
          ENNReal.ofReal (64 * (B + T ^ 2 * D)) := by
  intro n
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hpt : ∀ j k : ℕ, k ≤ 2 ^ j → T * (k : ℝ) / 2 ^ j ∈ Set.Icc (0 : ℝ) T := by
    intro j k hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have : (k : ℝ) ≤ 2 ^ j := by exact_mod_cast hk
    nlinarith
  have hsqI : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z => Y t z ^ 2) P :=
    fun t ht => (hmem t ht).integrable_sq
  have hdI : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z => (Y s z - Y t z) ^ 2) P := fun s hs t ht => by
    have : MemLp (fun z => Y s z - Y t z) 2 P := (hmem s hs).sub (hmem t ht)
    exact this.integrable_sq
  have hbase' : ∫ z, Y 0 z ^ 2 ∂P ≤ B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hsqI 0 h0)
      (Filter.Eventually.of_forall fun z => sq_nonneg _)] at hbase
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 hbase
  have hinc' : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ z, (Y s z - Y t z) ^ 2 ∂P ≤ D * (s - t) ^ 2 := by
    intro s hs t ht
    have := hinc s hs t ht
    rw [← ofReal_integral_eq_lintegral_ofReal (hdI s hs t ht)
      (Filter.Eventually.of_forall fun z => sq_nonneg _)] at this
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  -- the dominating function
  set a2 : Ω → ℝ := fun z => 3 * Y 0 z ^ 2 + 2 * (Y T z - Y 0 z) ^ 2 with ha2
  set sj : ℕ → Ω → ℝ := fun j z => ∑ i ∈ Finset.range (2 ^ j),
    (Y (T * ((2 * i + 1 : ℕ) : ℝ) / 2 ^ (j + 1)) z - Y (T * ((2 * i : ℕ) : ℝ) / 2 ^ (j + 1)) z) ^ 2
    with hsj
  set G : Ω → ℝ := fun z => 4 * (a2 z + ∑ j ∈ Finset.range n, (4 / 3 : ℝ) ^ (j + 1) * sj j z)
    with hG
  have hsj0 : ∀ j z, 0 ≤ sj j z := fun j z => Finset.sum_nonneg fun i _ => sq_nonneg _
  have ha20 : ∀ z, 0 ≤ a2 z := fun z => by simp only [ha2]; positivity
  -- pointwise domination
  have hpw : ∀ (z : Ω) (j : Fin (2 ^ n + 1)),
      Y (T * ((j : ℕ) : ℝ) / (2 : ℝ) ^ n) z ^ 2 ≤ G z := by
    intro z j
    have hy0 : |Y 0 z| ≤ Real.sqrt (a2 z) := Real.abs_le_sqrt (by simp only [ha2]; nlinarith [sq_nonneg (Y T z - Y 0 z)])
    have hyT : |Y T z| ≤ Real.sqrt (a2 z) := Real.abs_le_sqrt (by
      simp only [ha2]; nlinarith [sq_nonneg (Y T z - 2 * Y 0 z), sq_nonneg (Y 0 z)])
    have hr : ∀ j' i : ℕ, i < 2 ^ j' →
        |Y (T * ((2 * i + 1 : ℕ) : ℝ) / 2 ^ (j' + 1)) z - Y (T * ((2 * i : ℕ) : ℝ) / 2 ^ (j' + 1)) z| ≤
          Real.sqrt (sj j' z) := by
      intro j' i hi
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun i => (Y (T * ((2 * i + 1 : ℕ) : ℝ) / 2 ^ (j' + 1)) z -
        Y (T * ((2 * i : ℕ) : ℝ) / 2 ^ (j' + 1)) z) ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_range.2 hi)
    have hch := s88_chain (fun t => Y t z) T (Real.sqrt (a2 z)) (fun j' => Real.sqrt (sj j' z))
      (fun j' => Real.sqrt_nonneg _) hy0 hyT hr n (j : ℕ) (Nat.lt_succ_iff.1 j.2)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hch 2
    rw [sq_abs] at h2
    refine h2.trans ?_
    refine (s88_wcs _ _ n).trans ?_
    rw [Real.sq_sqrt (ha20 z)]
    simp only [hG]
    refine le_of_eq ?_
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.sq_sqrt (hsj0 k z)]
  -- integrability and integral of the dominating function
  have hIa2 : Integrable a2 P :=
    ((hsqI 0 h0).const_mul 3).add ((hdI T hTm 0 h0).const_mul 2)
  have hIsj : ∀ j, Integrable (sj j) P := by
    intro j
    refine integrable_finset_sum _ fun i hi => hdI _ ?_ _ ?_
    · exact hpt (j + 1) (2 * i + 1) (by have := Finset.mem_range.1 hi; rw [pow_succ]; omega)
    · exact hpt (j + 1) (2 * i) (by have := Finset.mem_range.1 hi; rw [pow_succ]; omega)
  have hIG : Integrable G P :=
    (hIa2.add (integrable_finset_sum _ fun j _ => (hIsj j).const_mul _)).const_mul 4
  have hint_a2 : ∫ z, a2 z ∂P ≤ 3 * B + 2 * (D * T ^ 2) := by
    simp only [ha2]
    rw [integral_add ((hsqI 0 h0).const_mul 3) ((hdI T hTm 0 h0).const_mul 2),
      integral_const_mul, integral_const_mul]
    have := hinc' T hTm 0 h0
    nlinarith
  have hint_sj : ∀ j, ∫ z, sj j z ∂P ≤ 2 ^ j * (D * (T / 2 ^ (j + 1)) ^ 2) := by
    intro j
    simp only [hsj]
    rw [integral_finset_sum _ (fun i hi => hdI _ (hpt (j + 1) (2 * i + 1)
      (by have := Finset.mem_range.1 hi; rw [pow_succ]; omega)) _ (hpt (j + 1) (2 * i)
      (by have := Finset.mem_range.1 hi; rw [pow_succ]; omega)))]
    calc _ ≤ ∑ i ∈ Finset.range (2 ^ j), D * (T / 2 ^ (j + 1)) ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have := hinc' _ (hpt (j + 1) (2 * i + 1) (by rw [pow_succ]; omega)) _
            (hpt (j + 1) (2 * i) (by rw [pow_succ]; omega))
          refine this.trans (le_of_eq ?_)
          congr 1
          push_cast
          ring
      _ = _ := by simp
  have hint_G : ∫ z, G z ∂P ≤ 4 * (3 * B + 2 * (D * T ^ 2) + D * T ^ 2) := by
    simp only [hG]
    rw [integral_const_mul, integral_add hIa2 (integrable_finset_sum _ fun j _ =>
      (hIsj j).const_mul _), integral_finset_sum _ (fun j _ => (hIsj j).const_mul _)]
    simp_rw [integral_const_mul]
    have hterm : ∀ j ∈ Finset.range n, (4 / 3 : ℝ) ^ (j + 1) * ∫ z, sj j z ∂P ≤
        D * T ^ 2 * ((1 / 2 : ℝ) * (2 / 3 : ℝ) ^ (j + 1)) := by
      intro j _
      calc _ ≤ (4 / 3 : ℝ) ^ (j + 1) * (2 ^ j * (D * (T / 2 ^ (j + 1)) ^ 2)) :=
            mul_le_mul_of_nonneg_left (hint_sj j) (by positivity)
        _ = _ := by
            have e1 : (4 / 3 : ℝ) ^ (j + 1) = (2 / 3 : ℝ) ^ (j + 1) * 2 ^ (j + 1) := by
              rw [← mul_pow]; norm_num
            have hx : (0 : ℝ) < 2 ^ j := by positivity
            rw [e1, div_pow, pow_succ (2 : ℝ) j]
            field_simp
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have h3 := mul_le_mul_of_nonneg_left (s88_geo2 n) (by positivity : 0 ≤ D * T ^ 2)
    have : 4 * (∫ z, a2 z ∂P + ∑ j ∈ Finset.range n, (4 / 3 : ℝ) ^ (j + 1) * ∫ z, sj j z ∂P) ≤
        4 * (3 * B + 2 * (D * T ^ 2) + D * T ^ 2) := by
      nlinarith
    exact this
  -- conclusion
  calc (∫⁻ z, (⨆ j : Fin (2 ^ n + 1),
        ENNReal.ofReal ((Y (T * ((j : ℕ) : ℝ) / (2 : ℝ) ^ n) z) ^ 2)) ∂P)
      ≤ ∫⁻ z, ENNReal.ofReal (G z) ∂P :=
        lintegral_mono fun z => iSup_le fun j => ENNReal.ofReal_le_ofReal (hpw z j)
    _ = ENNReal.ofReal (∫ z, G z ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hIG (Filter.Eventually.of_forall fun z => by
          simp only [hG]; have := ha20 z
          have : 0 ≤ ∑ j ∈ Finset.range n, (4 / 3 : ℝ) ^ (j + 1) * sj j z :=
            Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hsj0 j z)
          positivity)).symm
    _ ≤ ENNReal.ofReal (64 * (B + T ^ 2 * D)) := by
        refine ENNReal.ofReal_le_ofReal (hint_G.trans ?_)
        nlinarith [mul_nonneg (sq_nonneg T) hD]

end HRS.MS.S88Breakdown
