import HRS.MC.S7FCW12A
import HRS.Uniform.Q45Ten1

/-!
# FC-E packet, part B: the particle zeta window (prefix `s7fcw12_`)

* `s7fcw12_ofSeq_continuousOn`: `t ↦ ofSeq m (c t)` is continuous on `S` when the coordinates are, uniformly bounded.
* `s7fcw12_zetaAt_eq`: `zetaAt` in coordinates.
* `s7fcw12_zetaAt_measurable`, `s7fcw12_zetaAt_continuousOn`: measurability in `ω`, a.s. continuity in `t`.
* `s7fcw12_aemeasurable_zetaWin`: `zetaWin r T 0 P X` is `AEMeasurable`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.S7FCW12

open HRS HRS.Sec7

variable {d : ℕ}

/-- Coefficient-wise continuity of `ofSeq` in `E_m` (`2m > d`) for uniformly bounded coefficients. -/
theorem s7fcw12_ofSeq_continuousOn {m : ℝ} (hm : (d : ℝ) < 2 * m) (c : ℝ → NonzeroLattice d → ℝ) (S : Set ℝ)
    (hc : ∀ k, ContinuousOn (fun t => c t k) S) (C : ℝ) (hC : ∀ t ∈ S, ∀ k, |c t k| ≤ C) :
    ContinuousOn (fun t => NegSobolev.ofSeq m (c t)) S := by
  intro t₀ ht₀
  have hpow : ∀ a : ℝ, 0 < a → (a ^ (-m)) ^ 2 = a ^ (-(2 * m)) := by
    intro a ha
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    push_cast
    ring
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  -- squared distance formula, valid for `t ∈ S`
  have hdist : ∀ t ∈ S, ‖NegSobolev.ofSeq m (c t) - NegSobolev.ofSeq m (c t₀)‖ ^ 2 =
      ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) * (c t k - c t₀ k) ^ 2 := by
    intro t ht
    have hmt : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c t k) 2 :=
      NegSobolev.memℓp_of_bounded hm (c t) ⟨C, hC t ht⟩
    have hm0 : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c t₀ k) 2 :=
      NegSobolev.memℓp_of_bounded hm (c t₀) ⟨C, hC t₀ ht₀⟩
    have h1 := NegSobolev.coord_sq (NegSobolev.ofSeq m (c t) - NegSobolev.ofSeq m (c t₀))
    rw [h1.2]
    have hco : ∀ k, NegSobolev.coord (NegSobolev.ofSeq m (c t) - NegSobolev.ofSeq m (c t₀)) k =
        Lattice.jp k.1 ^ (-m) * c t k - Lattice.jp k.1 ^ (-m) * c t₀ k := by
      intro k
      rw [show NegSobolev.coord (NegSobolev.ofSeq m (c t) - NegSobolev.ofSeq m (c t₀)) k =
          NegSobolev.coord (NegSobolev.ofSeq m (c t)) k - NegSobolev.coord (NegSobolev.ofSeq m (c t₀)) k from rfl]
      rw [NegSobolev.coord_ofSeq_of_mem _ hmt, NegSobolev.coord_ofSeq_of_mem _ hm0]
    simp only [hco]
    congr 1
    funext k
    rw [← mul_sub, mul_pow, hpow _ (hjp k)]
  have hsum : Summable fun k : NonzeroLattice d => (2 * C) ^ 2 * Lattice.jp k.1 ^ (-(2 * m)) :=
    (summable_jp_rpow (d := d) m hm).mul_left _
  have hT : Tendsto (fun t => ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) * (c t k - c t₀ k) ^ 2)
      (𝓝[S] t₀) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[S] t₀) (g := fun _ => (0 : ℝ))
      (f := fun t k => Lattice.jp k.1 ^ (-(2 * m)) * (c t k - c t₀ k) ^ 2)
      (bound := fun k => (2 * C) ^ 2 * Lattice.jp k.1 ^ (-(2 * m))) hsum ?_ ?_
    · simpa using this
    · intro k
      have hk := ((hc k) t₀ ht₀).tendsto
      have h2 : Tendsto (fun t => Lattice.jp k.1 ^ (-(2 * m)) * (c t k - c t₀ k) ^ 2) (𝓝[S] t₀)
          (𝓝 (Lattice.jp k.1 ^ (-(2 * m)) * (c t₀ k - c t₀ k) ^ 2)) :=
        (hk.sub_const _).pow 2 |>.const_mul _
      simpa using h2
    · filter_upwards [self_mem_nhdsWithin] with t ht k
      have hjk := hjp k
      have hpos : 0 ≤ Lattice.jp k.1 ^ (-(2 * m)) := Real.rpow_nonneg hjk.le _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos (sq_nonneg _))]
      have ha := hC t ht k
      have hb := hC t₀ ht₀ k
      have hd : (c t k - c t₀ k) ^ 2 ≤ (2 * C) ^ 2 := by
        have : |c t k - c t₀ k| ≤ 2 * C := by
          calc |c t k - c t₀ k| ≤ |c t k| + |c t₀ k| := abs_sub _ _
            _ ≤ C + C := add_le_add ha hb
            _ = 2 * C := by ring
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      have := mul_le_mul_of_nonneg_left hd hpos
      linarith
  have hEq : ∀ᶠ t in 𝓝[S] t₀, ‖NegSobolev.ofSeq m (c t) - NegSobolev.ofSeq m (c t₀)‖ =
      Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) * (c t k - c t₀ k) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hdist t ht, Real.sqrt_sq (norm_nonneg _)]
  unfold ContinuousWithinAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := (Real.continuous_sqrt.tendsto 0).comp hT
  rw [Real.sqrt_zero] at hs
  exact Tendsto.congr' (hEq.mono fun t ht => ht.symm) hs

/-! ### The empirical coefficients of `zetaAt` -/

/-- The centred empirical coefficient `k ↦ N⁻¹∑_i e_k(X_i^t) - E[N⁻¹∑_i e_k(X_i^t)]` of `zetaAt` (without `√N`). -/
def s7fcw12_coef {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (k : NonzeroLattice d) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (t : ℝ) (ω : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X t.toNNReal ω i) -
    (N : ℝ)⁻¹ * ∑ i, ∫ ω', Torus.realMode k (X t.toNNReal ω' i) ∂P

theorem s7fcw12_abs_sum_le (k : NonzeroLattice d) {N : ℕ} (Y : Config d N) :
    |(N : ℝ)⁻¹ * ∑ i, Torus.realMode k (Y i)| ≤ Real.sqrt 2 := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
    have hs : |∑ i, Torus.realMode k (Y i)| ≤ N * Real.sqrt 2 := by
      calc |∑ i, Torus.realMode k (Y i)| ≤ ∑ i, |Torus.realMode k (Y i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, Real.sqrt 2 := Finset.sum_le_sum fun i _ => Torus.abs_realMode_le k (Y i)
        _ = N * Real.sqrt 2 := by simp
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hN.le)]
    calc (N : ℝ)⁻¹ * |∑ i, Torus.realMode k (Y i)| ≤ (N : ℝ)⁻¹ * (N * Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hs (inv_nonneg.2 hN.le)
      _ = Real.sqrt 2 := by field_simp

theorem s7fcw12_abs_mean_le (k : NonzeroLattice d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (Y : Ω → Config d N) (hY : ∀ i, Measurable fun ω => Y ω i) :
    |(N : ℝ)⁻¹ * ∑ i, ∫ ω', Torus.realMode k (Y ω' i) ∂P| ≤ Real.sqrt 2 := by
  have hb : ∀ i, |∫ ω', Torus.realMode k (Y ω' i) ∂P| ≤ Real.sqrt 2 := by
    intro i
    have h := norm_integral_le_of_norm_le_const (μ := P) (C := Real.sqrt 2)
      (f := fun ω' => Torus.realMode k (Y ω' i))
      (Eventually.of_forall fun ω' => by
        rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le k _)
    rw [Real.norm_eq_abs] at h
    simpa using h
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
    have hs : |∑ i, ∫ ω', Torus.realMode k (Y ω' i) ∂P| ≤ N * Real.sqrt 2 := by
      calc |∑ i, ∫ ω', Torus.realMode k (Y ω' i) ∂P| ≤ ∑ i, |∫ ω', Torus.realMode k (Y ω' i) ∂P| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, Real.sqrt 2 := Finset.sum_le_sum fun i _ => hb i
        _ = N * Real.sqrt 2 := by simp
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hN.le)]
    calc (N : ℝ)⁻¹ * |∑ i, ∫ ω', Torus.realMode k (Y ω' i) ∂P| ≤ (N : ℝ)⁻¹ * (N * Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hs (inv_nonneg.2 hN.le)
      _ = Real.sqrt 2 := by field_simp

theorem s7fcw12_abs_coef_le (k : NonzeroLattice d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (t : ℝ) (ω : Ω) :
    |s7fcw12_coef k P X t ω| ≤ 2 * Real.sqrt 2 := by
  have h1 := s7fcw12_abs_sum_le k (X t.toNNReal ω)
  have h2 := s7fcw12_abs_mean_le k P (fun ω' => X t.toNNReal ω')
    (fun i => (measurable_pi_apply i).comp (hadapt _))
  unfold s7fcw12_coef
  calc _ ≤ |(N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X t.toNNReal ω i)| +
        |(N : ℝ)⁻¹ * ∑ i, ∫ ω', Torus.realMode k (X t.toNNReal ω' i) ∂P| := abs_sub _ _
    _ ≤ Real.sqrt 2 + Real.sqrt 2 := add_le_add h1 h2
    _ = 2 * Real.sqrt 2 := by ring

theorem s7fcw12_coef_measurable (k : NonzeroLattice d) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t)) (t : ℝ) :
    Measurable fun ω => s7fcw12_coef k P X t ω := by
  unfold s7fcw12_coef
  refine Measurable.sub (measurable_const.mul ?_) measurable_const
  exact Finset.measurable_sum _ fun i _ =>
    (continuous_realMode' k).measurable.comp ((measurable_pi_apply i).comp (hadapt _))

theorem s7fcw12_ofSeq_smul (m : ℝ) {s : ℝ} (hs : 0 < s) (c : NonzeroLattice d → ℝ) :
    NegSobolev.ofSeq m (fun k => s * c k) = s • NegSobolev.ofSeq m c := by
  by_cases h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) 2
  · have h' : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (s * c k)) 2 := by
      have hf : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (s * c k)) =
          s • (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) := by
        funext k
        change Lattice.jp k.1 ^ (-m) * (s * c k) = s * (Lattice.jp k.1 ^ (-m) * c k)
        ring
      rw [hf]; exact h.const_smul s
    rw [NegSobolev.ofSeq_of_mem (fun k => s * c k) h', NegSobolev.ofSeq_of_mem c h]
    apply Subtype.ext
    funext k
    change Lattice.jp k.1 ^ (-m) * (s * c k) = s * (Lattice.jp k.1 ^ (-m) * c k)
    ring
  · have h' : ¬ Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (s * c k)) 2 := by
      intro h''
      apply h
      have hf : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * c k) =
          s⁻¹ • (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (s * c k)) := by
        funext k
        change Lattice.jp k.1 ^ (-m) * c k = s⁻¹ * (Lattice.jp k.1 ^ (-m) * (s * c k))
        field_simp
      rw [hf]; exact h''.const_smul s⁻¹
    simp [NegSobolev.ofSeq, h, h']

theorem s7fcw12_zetaAt_eq {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (m : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t)) (hN : 0 < N) (t : ℝ) (ω : Ω) :
    zetaAt m P X t ω = NegSobolev.ofSeq m (fun k => Real.sqrt N * s7fcw12_coef k P X t ω) := by
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hmap : ∀ (k : NonzeroLattice d) (i : Fin N),
      ∫ Y : Config d N, Torus.realMode k (Y i) ∂(P.map (X t.toNNReal)) =
        ∫ ω', Torus.realMode k (X t.toNNReal ω' i) ∂P := fun k i =>
    integral_map (hadapt _).aemeasurable
      ((continuous_realMode' k).comp (continuous_apply i)).aestronglyMeasurable
  have hcoef : ∀ k : NonzeroLattice d,
      Torus.measureRealCoeff (empirical (X t.toNNReal ω)) k -
        Torus.measureRealCoeff (meanEmpirical (P.map (X t.toNNReal))) k = s7fcw12_coef k P X t ω := by
    intro k
    unfold Torus.measureRealCoeff s7fcw12_coef
    rw [integral_empirical _ (continuous_realMode' k), integral_meanEmpirical _ (continuous_realMode' k)]
    simp only [hmap]
  unfold zetaAt zetaE NegSobolev.ofMeasureDiff
  rw [show (fun k : NonzeroLattice d => Torus.measureRealCoeff (empirical (X t.toNNReal ω)) k -
      Torus.measureRealCoeff (meanEmpirical (P.map (X t.toNNReal))) k) =
      fun k => s7fcw12_coef k P X t ω from funext hcoef]
  exact (s7fcw12_ofSeq_smul m hs _).symm

theorem s7fcw12_zetaAt_measurable (m : ℝ) {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hN : 0 < N) (t : ℝ) : Measurable fun ω => zetaAt m P X t ω := by
  have h : (fun ω => zetaAt m P X t ω) =
      fun ω => NegSobolev.ofSeq m (fun k => Real.sqrt N * s7fcw12_coef k P X t ω) :=
    funext fun ω => s7fcw12_zetaAt_eq m P X hadapt hN t ω
  rw [h]
  exact s7fcw12_measurable_ofSeq (fun ω k => Real.sqrt N * s7fcw12_coef k P X t ω)
    fun k => measurable_const.mul (s7fcw12_coef_measurable k P X hadapt t)

theorem s7fcw12_mean_continuousOn {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (k : NonzeroLattice d) (i : Fin N)
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℝ → Ω → Config d N) (hm : ∀ t, Measurable (Y t))
    (hc : ∀ᵐ ω ∂P, ∀ j, Continuous fun t => Y t ω j) (S : Set ℝ) :
    ContinuousOn (fun t => ∫ ω', Torus.realMode k (Y t ω' i) ∂P) S := by
  refine continuousOn_of_dominated (bound := fun _ => Real.sqrt 2) (fun t _ => ?_)
    (fun t _ => Eventually.of_forall fun ω => ?_) (integrable_const _) ?_
  · exact ((continuous_realMode' k).measurable.comp ((measurable_pi_apply i).comp (hm t))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le k _
  · filter_upwards [hc] with ω hω
    exact ((continuous_realMode' k).comp (hω i)).continuousOn

theorem s7fcw12_coef_continuousOn (k : NonzeroLattice d) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) (ω : Ω)
    (hω : ∀ i, Continuous fun t : ℝ => X t.toNNReal ω i) (S : Set ℝ) :
    ContinuousOn (fun t => s7fcw12_coef k P X t ω) S := by
  have hcR : ∀ᵐ ω' ∂P, ∀ j, Continuous fun t : ℝ => X t.toNNReal ω' j :=
    hcont.mono fun ω' hω' j => (hω' j).comp continuous_real_toNNReal
  unfold s7fcw12_coef
  refine ContinuousOn.sub (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
      ((continuous_realMode' k).comp (hω i)).continuousOn))
    (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
      s7fcw12_mean_continuousOn k i P (fun t => X t.toNNReal) (fun t => hadapt _) hcR S))

theorem s7fcw12_zetaAt_continuousOn (m : ℝ) (hm : (d : ℝ) < 2 * m) {Ω : Type} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) (hN : 0 < N) (ω : Ω)
    (hω : ∀ i, Continuous fun t : ℝ => X t.toNNReal ω i) (S : Set ℝ) :
    ContinuousOn (fun t => zetaAt m P X t ω) S := by
  have hfun : (fun t => zetaAt m P X t ω) =
      fun t => NegSobolev.ofSeq m (fun k => Real.sqrt N * s7fcw12_coef k P X t ω) :=
    funext fun t => s7fcw12_zetaAt_eq m P X hadapt hN t ω
  rw [hfun]
  refine s7fcw12_ofSeq_continuousOn hm (fun t k => Real.sqrt N * s7fcw12_coef k P X t ω) S
    (fun k => continuousOn_const.mul (s7fcw12_coef_continuousOn k P X hadapt hcont ω hω S))
    (Real.sqrt N * (2 * Real.sqrt 2)) (fun t _ k => ?_)
  show |Real.sqrt N * s7fcw12_coef k P X t ω| ≤ _
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (s7fcw12_abs_coef_le k P X hadapt t ω) (Real.sqrt_nonneg _)

/-- `zetaWin` is `AEMeasurable` (its window is a.s. continuous, the values are measurable). -/
theorem s7fcw12_aemeasurable_zetaWin (m T : ℝ) (hT : 0 < T) (hm : (d : ℝ) < 2 * m) {Ω : Type}
    [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hadapt : ∀ t : ℝ≥0, Measurable (X t)) (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i)
    (hN : 0 < N) : AEMeasurable (zetaWin m T 0 P X) P := by
  have hcR : ∀ᵐ ω ∂P, ∀ j, Continuous fun t : ℝ => X t.toNNReal ω j :=
    hcont.mono fun ω hω j => (hω j).comp continuous_real_toNNReal
  have hY : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (fun ω => zetaAt m P X t ω) P := fun t _ =>
    (s7fcw12_zetaAt_measurable m P X hadapt hN t).aemeasurable
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => zetaAt m P X t ω) (Set.Icc 0 T) :=
    hcR.mono fun ω hω => s7fcw12_zetaAt_continuousOn m hm P X hadapt hcont hN ω hω _
  have hW : zetaWin m T 0 P X = HRS.Uniform.windowPath 0 T (fun t ω => zetaAt m P X t ω) := by
    funext ω
    rfl
  rw [hW]
  exact HRS.Uniform.Q45.aemeasurable_windowPath' P hT (fun t ω => zetaAt m P X t ω) hY hc

end HRS.MC.Sec7.S7FCW12
