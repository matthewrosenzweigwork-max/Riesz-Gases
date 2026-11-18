import HRS.MS.S111K4I

/-!
# S11.1 / T01 (S11K4), part J: `wick_difference_L2`

Pro `S11.1-Tensor` `T01` (frozen skeleton statement, `HRS.Whole` names).  The route: the finite Wick difference is bounded by
`8 B² δ² ∑_{i,j<n} A_ij²` (`k4_finite_wick`, the standard-Gaussian representation of the finite family), Bessel gives
`∑_{i,j<n} A_ij² ≤ ‖k‖²_{L²(μ⊗μ)}`, and `k4_l2_limit_bound` passes to the `L²` limits `Q, Q̃`.  This is a sharper constant (8) than the
stated 16.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.S111K4

open HRS (Euc)

theorem k4_wick_difference_L2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (a : ℕ → Euc d → ℝ) (ha : HRS.Whole.IsR2ZeroMeanONB mu a)
    (z zb : ℕ → Ω → ℝ) (hz : ∀ i, AEMeasurable (z i) P) (hzb : ∀ i, AEMeasurable (zb i) P)
    (hG : ∀ n : ℕ, HRS.IsCenteredGaussian
      (P.map fun w (i : Fin 2 × Fin n) => if i.1 = 0 then z i.2 w else zb i.2 w))
    (B delta : ℝ) (hB : 0 ≤ B) (hdelta : 0 ≤ delta)
    (hvar : ∀ n : ℕ, ∀ c : Fin n → ℝ,
      (∫ w, (∑ i, c i * z i w) ^ 2 ∂P) ≤ B ^ 2 * ∑ i, c i ^ 2 ∧
      (∫ w, (∑ i, c i * zb i w) ^ 2 ∂P) ≤ B ^ 2 * ∑ i, c i ^ 2 ∧
      (∫ w, (∑ i, c i * (z i w - zb i w)) ^ 2 ∂P) ≤
        delta ^ 2 * ∑ i, c i ^ 2)
    (k : Euc d → Euc d → ℝ) (hk : MemLp (Function.uncurry k) 2 (mu.prod mu))
    (Q Qb : Ω → ℝ)
    (hQ : HRS.Whole.IsR2WickChaos P mu a z k Q) (hQb : HRS.Whole.IsR2WickChaos P mu a zb k Qb)
    (hQ2 : MemLp Q 2 P) (hQb2 : MemLp Qb 2 P) :
    (∫ w, (Q w - Qb w) ^ 2 ∂P) ≤
      16 * B ^ 2 * delta ^ 2 * ∫ xy, k xy.1 xy.2 ^ 2 ∂(mu.prod mu) := by
  classical
  set A : ℕ → ℕ → ℝ := fun i j => HRS.Whole.r2WickCoeff mu a k i j with hA
  set Xn : (n : ℕ) → Ω → (Fin 2 × Fin n → ℝ) := fun n w i => if i.1 = 0 then z i.2 w else zb i.2 w with hXn
  have hXm : ∀ n, AEMeasurable (Xn n) P := fun n => aemeasurable_pi_iff.2 fun i => by
    by_cases h : i.1 = 0
    · simpa [hXn, h] using hz i.2
    · simpa [hXn, h] using hzb i.2
  have hX0 : ∀ n (i : Fin n) w, Xn n w (0, i) = z i w := by intro n i w; simp [hXn]
  have hX1 : ∀ n (i : Fin n) w, Xn n w (1, i) = zb i w := by intro n i w; simp [hXn]
  have hGs : HRS.MS.R2Chaos.S94GSeq P z (B ^ 2) := fun n => by
    refine ⟨?_, fun α => ?_⟩
    · have := k4_gfam P n (Xn n) (hXm n) (hG n) 0
      simpa [hX0] using this
    · have := (hvar n α).1
      simpa [HRS.MS.R2Chaos.s94q, HRS.MS.R2Chaos.s94lin] using this
  have hGsb : HRS.MS.R2Chaos.S94GSeq P zb (B ^ 2) := fun n => by
    refine ⟨?_, fun α => ?_⟩
    · have := k4_gfam P n (Xn n) (hXm n) (hG n) 1
      simpa [hX1] using this
    · have := (hvar n α).2.1
      simpa [HRS.MS.R2Chaos.s94q, HRS.MS.R2Chaos.s94lin] using this
  -- the sections and their differences
  set Qn : ℕ → Ω → ℝ := fun n => HRS.MS.R2Chaos.s94Sec P z A n with hQn
  set Qbn : ℕ → Ω → ℝ := fun n => HRS.MS.R2Chaos.s94Sec P zb A n with hQbn
  have hmem : ∀ n, MemLp (Qn n) 2 P := fun n => HRS.MS.R2Chaos.s94_sec_memLp hGs A n
  have hmemb : ∀ n, MemLp (Qbn n) 2 P := fun n => HRS.MS.R2Chaos.s94_sec_memLp hGsb A n
  have hbessel : ∀ n, ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 ≤ ∫ q, (k q.1 q.2) ^ 2 ∂(mu.prod mu) := by
    intro n
    have := k4_bessel mu a ha k hk (Finset.range n ×ˢ Finset.range n)
    rw [Finset.sum_product] at this
    simpa [Finset.sum_range, hA] using this
  have hbound : ∀ n, ∫ w, (Qn n w - Qbn n w) ^ 2 ∂P ≤
      8 * B ^ 2 * delta ^ 2 * ∫ q, (k q.1 q.2) ^ 2 ∂(mu.prod mu) := by
    intro n
    have h := k4_finite_wick P n (Xn n) (hXm n) (hG n) B delta
      (fun c => by simpa [hX0] using (hvar n c).1) (fun c => by simpa [hX1] using (hvar n c).2.1)
      (fun c => by simpa [hX0, hX1] using (hvar n c).2.2) (Matrix.of fun i j : Fin n => A i j)
    have e : ∀ w, Qn n w - Qbn n w = (∑ i : Fin n, ∑ j : Fin n, A i j * (z i w * z j w - ∫ η, z i η * z j η ∂P)) -
        ∑ i : Fin n, ∑ j : Fin n, A i j * (zb i w * zb j w - ∫ η, zb i η * zb j η ∂P) := by
      intro w
      simp only [hQn, hQbn, HRS.MS.R2Chaos.s94Sec, Finset.sum_range]
    simp_rw [e]
    simp only [hX0, hX1, Matrix.of_apply] at h
    refine h.trans ?_
    have hk0 : 0 ≤ 8 * B ^ 2 * delta ^ 2 := by positivity
    have : HRS.MS.S111K4.k4fr (Matrix.of fun i j : Fin n => A i j) ≤ ∫ q, (k q.1 q.2) ^ 2 ∂(mu.prod mu) := by
      simpa [HRS.MS.S111K4.k4fr] using hbessel n
    exact mul_le_mul_of_nonneg_left this hk0 |> fun h' => by linarith [h']
  have hD : ∀ n, MemLp (fun w => Qn n w - Qbn n w) 2 P := fun n => (hmem n).sub (hmemb n)
  have hl1 := k4_tendsto_int P Qn Q hmem hQ2 hQ
  have hl2 := k4_tendsto_int P Qbn Qb hmemb hQb2 hQb
  have hlim : Tendsto (fun n => ∫ w, ((Qn n w - Qbn n w) - (Q w - Qb w)) ^ 2 ∂P) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => 2 * ∫ w, (Qn n w - Q w) ^ 2 ∂P + 2 * ∫ w, (Qbn n w - Qb w) ^ 2 ∂P) atTop
        (𝓝 (2 * 0 + 2 * 0)) := (hl1.const_mul 2).add (hl2.const_mul 2)
    rw [mul_zero, add_zero] at hsum
    refine squeeze_zero (fun n => integral_nonneg fun w => sq_nonneg _) (fun n => ?_) hsum
    have i1 : Integrable (fun w => (Qn n w - Q w) ^ 2) P := ((hmem n).sub hQ2).integrable_sq
    have i2 : Integrable (fun w => (Qbn n w - Qb w) ^ 2) P := ((hmemb n).sub hQb2).integrable_sq
    have i3 : Integrable (fun w => ((Qn n w - Qbn n w) - (Q w - Qb w)) ^ 2) P :=
      ((hD n).sub (hQ2.sub hQb2)).integrable_sq
    calc ∫ w, ((Qn n w - Qbn n w) - (Q w - Qb w)) ^ 2 ∂P
        ≤ ∫ w, (2 * (Qn n w - Q w) ^ 2 + 2 * (Qbn n w - Qb w) ^ 2) ∂P :=
          integral_mono i3 ((i1.const_mul 2).add (i2.const_mul 2)) fun w => by
            nlinarith [sq_nonneg ((Qn n w - Q w) + (Qbn n w - Qb w))]
      _ = _ := by rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
  have hfin := k4_l2_limit_bound P (fun n w => Qn n w - Qbn n w) (fun w => Q w - Qb w) hD (hQ2.sub hQb2) hlim
    (8 * B ^ 2 * delta ^ 2 * ∫ q, (k q.1 q.2) ^ 2 ∂(mu.prod mu)) hbound
  have hnn : 0 ≤ B ^ 2 * delta ^ 2 * ∫ q, (k q.1 q.2) ^ 2 ∂(mu.prod mu) :=
    mul_nonneg (by positivity) (integral_nonneg fun q => sq_nonneg _)
  calc ∫ w, (Q w - Qb w) ^ 2 ∂P ≤ 8 * B ^ 2 * delta ^ 2 * ∫ q, (k q.1 q.2) ^ 2 ∂(mu.prod mu) := hfin
    _ ≤ 16 * B ^ 2 * delta ^ 2 * ∫ xy, k xy.1 xy.2 ^ 2 ∂(mu.prod mu) := by nlinarith [hnn]

end HRS.MS.S111K4
