import HRS.MC.S7PIS1Mat

/-!
# Packet S1, part 2: the matrix action `(U^{u,t}φ)^_j = ∑_k φ̂_k T_{jk}` as an unconditional sum
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS1

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV

variable {d : ℕ}

/-- the Sobolev norm of the remainder tends to `0` along the finsets -/
lemma S7PIS1_rem_tendsto {J : ℕ} {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Tendsto (fun K : Finset (NonzeroLattice d) => sobolevNorm (J : ℝ) (S7PIS1_rem φ K)) atTop (𝓝 0) := by
  classical
  have hdom : Dom J φ := dom_smooth hφ
  set s : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (2 * (J : ℝ)) * Torus.funRealCoeff φ k ^ 2 with hs
  have hsum : Summable s := hdom.2.2
  have hsnn : ∀ k, 0 ≤ s k := fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hnorm : ∀ K : Finset (NonzeroLattice d), sobolevNorm (J : ℝ) (S7PIS1_rem φ K) =
      Real.sqrt (∑' k, s k - ∑ k ∈ K, s k) := by
    intro K
    unfold sobolevNorm
    rw [S7PIS1_mean_rem hdom.1 K]
    congr 1
    have h1 : ∀ k, Lattice.jp k.1 ^ (2 * (J : ℝ)) * Torus.funRealCoeff (S7PIS1_rem φ K) k ^ 2 =
        s k - (if k ∈ K then s k else 0) := by
      intro k
      rw [S7PIS1_coeff_rem hdom.1 K k]
      by_cases hk : k ∈ K
      · simp [hk]
      · simp [hk, hs]
    have h2 : Summable fun k => (if k ∈ K then s k else 0) :=
      summable_of_ne_finset_zero (s := K) fun k hk => by simp [hk]
    rw [tsum_congr h1, hsum.tsum_sub h2]
    have : ∑' k, (if k ∈ K then s k else 0) = ∑ k ∈ K, s k := by
      rw [tsum_eq_sum (s := K) (fun k hk => by simp [hk])]
      exact Finset.sum_congr rfl fun k hk => by simp [hk]
    rw [this]; simp
  simp_rw [hnorm]
  have ht : Tendsto (fun K : Finset (NonzeroLattice d) => ∑' k, s k - ∑ k ∈ K, s k) atTop
      (𝓝 (∑' k, s k - ∑' k, s k)) :=
    tendsto_const_nhds.sub hsum.hasSum
  rw [sub_self] at ht
  have h3 := (Real.continuous_sqrt.tendsto 0).comp ht
  rw [Real.sqrt_zero] at h3
  exact h3

/-- **matrix action** -/
lemma S7PIS1_hasSum {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htT : t ≤ T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (j : NonzeroLattice d) :
    HasSum (fun k => Torus.funRealCoeff φ k * pieT D μ u t j k)
      (Torus.funRealCoeff (propagator D μ u t φ) j) := by
  classical
  rcases (hu.trans hut).eq_or_lt with h0 | hpos
  · have ht0 : t = 0 := h0.symm
    subst ht0
    have hu0 : u = 0 := le_antisymm hut hu
    subst hu0
    rw [S7PIS1_prop_zero H hφ]
    have e : (fun k => Torus.funRealCoeff φ k * pieT D μ 0 0 j k) =
        fun k => if k = j then Torus.funRealCoeff φ j else 0 := by
      funext k
      rw [S7PIDV_pieT_zero H j k]
      by_cases hk : k = j
      · subst hk; simp
      · have : ¬ (j = k) := fun h => hk h.symm
        simp [hk, this]
    rw [e]
    exact hasSum_ite_eq j _
  · have ht : t ∈ Set.Ioc 0 T := ⟨hpos, htT⟩
    have hu' : u ∈ Set.Icc 0 t := ⟨hu, hut⟩
    have hJ1 : 1 ≤ J := by
      obtain ⟨hd, hJ, -⟩ := H
      have := ClassicalPart.three_le_mStar d
      omega
    obtain ⟨C, hC0, hC⟩ := pie_level_bound H J hJ1 le_rfl
    have hdom : Dom J φ := dom_smooth hφ
    have hdec : ∀ K : Finset (NonzeroLattice d), Torus.funRealCoeff (propagator D μ u t φ) j =
        ∑ k ∈ K, Torus.funRealCoeff φ k * pieT D μ u t j k +
          Torus.funRealCoeff (propagator D μ u t (S7PIS1_rem φ K)) j := by
      intro K
      have e : (fun x => 1 * S7PIS1_psi φ K x + 1 * S7PIS1_rem φ K x) = φ := by
        funext x; simp only [S7PIS1_rem]; ring
      have hl := pie_prop_lin H ht hu' (S7PIS1_dom_psi J φ K) (S7PIS1_dom_rem hdom K) 1 1
      rw [e] at hl
      rw [hl, pie_funRealCoeff_lin (pie_prop_continuous H ht hu' (S7PIS1_dom_psi J φ K))
        (pie_prop_continuous H ht hu' (S7PIS1_dom_rem hdom K)), S7PIS1_coeff_prop_psi H ht hu']
      ring
    -- the remainder coefficient tends to zero
    have hr : Tendsto (fun K : Finset (NonzeroLattice d) =>
        Torus.funRealCoeff (propagator D μ u t (S7PIS1_rem φ K)) j) atTop (𝓝 0) := by
      have hn := (S7PIS1_rem_tendsto (J := J) hφ).const_mul C
      rw [mul_zero] at hn
      refine squeeze_zero_norm (fun K => ?_) hn
      obtain ⟨hmem, hb⟩ := hC t ht u hu' _ (S7PIS1_dom_rem hdom K)
      rw [Real.norm_eq_abs]
      exact (S7PIS1_abs_coeff_le (by positivity) hmem j).trans hb
    have hlim : Tendsto (fun K : Finset (NonzeroLattice d) =>
        ∑ k ∈ K, Torus.funRealCoeff φ k * pieT D μ u t j k) atTop
        (𝓝 (Torus.funRealCoeff (propagator D μ u t φ) j)) := by
      have := (tendsto_const_nhds (x := Torus.funRealCoeff (propagator D μ u t φ) j)).sub hr
      rw [sub_zero] at this
      refine this.congr fun K => ?_
      rw [hdec K]; ring
    exact hlim

end HRS.MC.Sec7.S7PIS1

end
