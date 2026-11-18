import HRS.MS.Fp81S21JointClose2

/-! The numerical cutoff bound and its sequential limit. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Filter Topology
namespace HRS.Fp81.S21

/-- The cutoff index `r` stands for the physical cutoff `r + 1`. -/
def fp81s21_jointClose_cutoffBound
    (s : ℕ → ℝ) (t c K : ℕ → ℕ → ℝ) (M : ℝ) (d : ℕ → ℝ)
    (m k r N : ℕ) : ℝ :=
  s m + t m k + c m k / Real.sqrt (N : ℝ) +
    2 * Real.sqrt ((K m k) ^ 2 *
      ((1 + 2 * ((r : ℝ) + 1)) ^ 2 * (2 * ((r : ℝ) + 1)) * d N +
        64 * (1 + M) / ((r : ℝ) + 1) ^ 2))

/-- The exact cutoff expression tends to zero after taking the infimum,
with the spatial, rank, cutoff, and particle limits taken in that order. -/
theorem fp81s21_jointClose_cutoff_profile
    (s : ℕ → ℝ) (t c K : ℕ → ℕ → ℝ) (M : ℝ) (d : ℕ → ℝ)
    (hs : ∀ m, 0 ≤ s m) (ht : ∀ m k, 0 ≤ t m k)
    (hc : ∀ m k, 0 ≤ c m k) (hM : 0 ≤ M) (hd : ∀ N, 0 ≤ d N)
    (hs0 : Tendsto s atTop (𝓝 0))
    (ht0 : ∀ m, Tendsto (t m) atTop (𝓝 0))
    (hd0 : Tendsto d atTop (𝓝 0)) :
    (∀ N, 0 ≤ fp81s21_jointClose_profile (fp81s21_jointClose_cutoffBound s t c K M d) N) ∧
      Tendsto (fp81s21_jointClose_profile (fp81s21_jointClose_cutoffBound s t c K M d))
        atTop (𝓝 0) := by
  let bN : ℕ → ℕ → ℕ → ℝ := fun m k r =>
    s m + t m k + 2 * Real.sqrt ((K m k) ^ 2 *
      (64 * (1 + M) / ((r : ℝ) + 1) ^ 2))
  let bR : ℕ → ℕ → ℝ := fun m k => s m + t m k
  let bK : ℕ → ℝ := s
  apply fp81s21_jointClose_sequential_profile _ bN bR bK
  · intro m k r N
    dsimp [fp81s21_jointClose_cutoffBound]
    exact add_nonneg (add_nonneg (add_nonneg (hs m) (ht m k))
      (div_nonneg (hc m k) (Real.sqrt_nonneg _))) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  · intro m k r
    let A : ℝ := (1 + 2 * ((r : ℝ) + 1)) ^ 2 * (2 * ((r : ℝ) + 1))
    let B : ℝ := 64 * (1 + M) / ((r : ℝ) + 1) ^ 2
    have hinv : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hdiag : Tendsto (fun N : ℕ => c m k / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hinv.const_mul (c m k)
    have hprod : Tendsto (fun N => A * d N) atTop (𝓝 0) := by
      simpa using hd0.const_mul A
    have hinside : Tendsto (fun N => (K m k) ^ 2 * (A * d N + B))
        atTop (𝓝 ((K m k) ^ 2 * B)) := by
      simpa using (hprod.add_const B).const_mul ((K m k) ^ 2)
    have hroot : Tendsto (fun N => Real.sqrt ((K m k) ^ 2 * (A * d N + B)))
        atTop (𝓝 (Real.sqrt ((K m k) ^ 2 * B))) := hinside.sqrt
    have hbase : Tendsto (fun _ : ℕ => s m + t m k) atTop (𝓝 (s m + t m k)) :=
      tendsto_const_nhds
    have hsum := (hbase.add hdiag).add (hroot.const_mul 2)
    change Tendsto (fun N : ℕ => fp81s21_jointClose_cutoffBound s t c K M d m k r N)
      atTop (𝓝 (bN m k r))
    simpa [fp81s21_jointClose_cutoffBound, bN, A, B] using hsum
  · intro m k
    have hinv : Tendsto (fun r : ℕ => (((r : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
      simpa [one_div, add_comm] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hdiv : Tendsto (fun r : ℕ => 64 * (1 + M) / ((r : ℝ) + 1) ^ 2)
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, inv_pow] using (hinv.pow 2).const_mul (64 * (1 + M))
    have hinside : Tendsto (fun r : ℕ => (K m k) ^ 2 *
        (64 * (1 + M) / ((r : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
      simpa using hdiv.const_mul ((K m k) ^ 2)
    have hroot : Tendsto (fun r : ℕ => Real.sqrt ((K m k) ^ 2 *
        (64 * (1 + M) / ((r : ℝ) + 1) ^ 2))) atTop (𝓝 0) := by
      simpa using hinside.sqrt
    have hbase : Tendsto (fun _ : ℕ => s m + t m k) atTop (𝓝 (s m + t m k)) :=
      tendsto_const_nhds
    simpa [bN, bR] using hbase.add (hroot.const_mul 2)
  · intro m
    simpa [bR, bK] using (ht0 m).const_add (s m)
  · exact hs0

#print axioms fp81s21_jointClose_cutoffBound
#print axioms fp81s21_jointClose_cutoff_profile
end HRS.Fp81.S21
end
