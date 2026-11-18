import HRS.MC.S7FCDefs

/-!
# Block E of the F5 packet: continuity of `ofMeasureDiff` (proof of `fcf5_E1a_ofMeasureDiff_cont`)

Route: the coordinates of `ofMeasureDiff r (ν t) (ν' t)` are `⟨k⟩^{-r} (m_k(ν t) - m_k(ν' t))` with `|m_k| ≤ √2`
(`ν t` probability measures), so `‖F t - F t₀‖² = ∑_k ⟨k⟩^{-2r} (D_k(t))²` with `D_k(t) → 0` and the summable majorant
`32 ⟨k⟩^{-2r}` (`2r > d`); dominated convergence (`tendsto_tsum_of_dominated_convergence`) gives the limit.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5B

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

/-- **E1a (continuity of `ofMeasureDiff` in weakly continuous probability measures)**, proof. -/
theorem fcf5_E1a_ofMeasureDiff_cont_proof (r : ℝ) (hr : (d : ℝ) < 2 * r) (ν ν' : ℝ → Measure (Torus d))
    (J : Set ℝ)
    (hν : ∀ t ∈ J, IsProbabilityMeasure (ν t)) (hν' : ∀ t ∈ J, IsProbabilityMeasure (ν' t))
    (hc : ∀ k : NonzeroLattice d, ContinuousOn (fun t => Torus.measureRealCoeff (ν t) k) J)
    (hc' : ∀ k : NonzeroLattice d, ContinuousOn (fun t => Torus.measureRealCoeff (ν' t) k) J) :
    ContinuousOn (fun t => NegSobolev.ofMeasureDiff r (ν t) (ν' t)) J := by
  set F : ℝ → NegSobolev d r := fun t => NegSobolev.ofMeasureDiff r (ν t) (ν' t) with hF
  -- uniform bound on the coefficients of the difference
  have hbd : ∀ t ∈ J, ∀ k : NonzeroLattice d,
      |Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k| ≤ 2 * Real.sqrt 2 := by
    intro t ht k
    haveI := hν t ht
    haveI := hν' t ht
    have hm1 : (ν t Set.univ).toReal = 1 := by rw [measure_univ]; simp
    have hm2 : (ν' t Set.univ).toReal = 1 := by rw [measure_univ]; simp
    have h1 := Torus.abs_measureRealCoeff_le (ν t) k
    have h2 := Torus.abs_measureRealCoeff_le (ν' t) k
    rw [hm1, mul_one] at h1
    rw [hm2, mul_one] at h2
    calc |Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k|
        ≤ |Torus.measureRealCoeff (ν t) k| + |Torus.measureRealCoeff (ν' t) k| := abs_sub _ _
      _ ≤ 2 * Real.sqrt 2 := by linarith
  -- membership in `ℓ²` and the coordinates of `F t`
  have hcoord : ∀ t ∈ J, ∀ k : NonzeroLattice d,
      NegSobolev.coord (F t) k =
        Lattice.jp k.1 ^ (-r) * (Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k) := by
    intro t ht k
    have hmem : Memℓp (fun k : NonzeroLattice d =>
        Lattice.jp k.1 ^ (-r) * (Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k)) 2 :=
      NegSobolev.memℓp_of_bounded hr _ ⟨2 * Real.sqrt 2, fun k => hbd t ht k⟩
    exact NegSobolev.coord_ofSeq_of_mem _ hmem k
  have hsub : ∀ (G H : NegSobolev d r) (k : NonzeroLattice d),
      NegSobolev.coord (G - H) k = NegSobolev.coord G k - NegSobolev.coord H k := fun G H k => rfl
  intro t0 ht0
  show Tendsto F (𝓝[J] t0) (𝓝 (F t0))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- the squared norm of the difference is a series of dominated terms
  have hD : ∀ k : NonzeroLattice d,
      Tendsto (fun t => (Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k) -
        (Torus.measureRealCoeff (ν t0) k - Torus.measureRealCoeff (ν' t0) k)) (𝓝[J] t0) (𝓝 0) := by
    intro k
    have h1 : Tendsto (fun t => Torus.measureRealCoeff (ν t) k) (𝓝[J] t0)
        (𝓝 (Torus.measureRealCoeff (ν t0) k)) := hc k t0 ht0
    have h2 : Tendsto (fun t => Torus.measureRealCoeff (ν' t) k) (𝓝[J] t0)
        (𝓝 (Torus.measureRealCoeff (ν' t0) k)) := hc' k t0 ht0
    have h := (h1.sub h2).sub
      (tendsto_const_nhds (x := Torus.measureRealCoeff (ν t0) k - Torus.measureRealCoeff (ν' t0) k))
    rw [sub_self] at h
    exact h
  have hlim : Tendsto (fun t => ∑' k : NonzeroLattice d,
      (Lattice.jp k.1 ^ (-r) * ((Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k) -
        (Torus.measureRealCoeff (ν t0) k - Torus.measureRealCoeff (ν' t0) k))) ^ 2)
      (𝓝[J] t0) (𝓝 (∑' k : NonzeroLattice d, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun k : NonzeroLattice d => 32 * Lattice.jp k.1 ^ (-(2 * r)))
      ((HRS.summable_jp_rpow (d := d) r hr).mul_left 32) (fun k => ?_)
      (eventually_mem_nhdsWithin.mono fun t ht k => ?_)
    · have := ((tendsto_const_nhds (x := Lattice.jp k.1 ^ (-r))).mul (hD k)).pow 2
      simpa using this
    · -- the uniform majorant
      have hDabs : |(Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k) -
          (Torus.measureRealCoeff (ν t0) k - Torus.measureRealCoeff (ν' t0) k)| ≤ 4 * Real.sqrt 2 := by
        have := abs_sub (Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k)
          (Torus.measureRealCoeff (ν t0) k - Torus.measureRealCoeff (ν' t0) k)
        have ha := hbd t ht k
        have hb := hbd t0 ht0 k
        linarith
      have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsqD : ((Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k) -
          (Torus.measureRealCoeff (ν t0) k - Torus.measureRealCoeff (ν' t0) k)) ^ 2 ≤ 32 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg ((Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k) -
          (Torus.measureRealCoeff (ν t0) k - Torus.measureRealCoeff (ν' t0) k))]
      have hjpos : 0 ≤ Lattice.jp k.1 ^ (-(2 * r)) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
      have hexp : (Lattice.jp k.1 ^ (-r) * ((Torus.measureRealCoeff (ν t) k -
          Torus.measureRealCoeff (ν' t) k) - (Torus.measureRealCoeff (ν t0) k -
          Torus.measureRealCoeff (ν' t0) k))) ^ 2 =
          Lattice.jp k.1 ^ (-(2 * r)) * (((Torus.measureRealCoeff (ν t) k -
          Torus.measureRealCoeff (ν' t) k) - (Torus.measureRealCoeff (ν t0) k -
          Torus.measureRealCoeff (ν' t0) k))) ^ 2 := by
        rw [mul_pow, Torus.jp_rpow_sq, show 2 * (-r) = -(2 * r) by ring]
      rw [Real.norm_of_nonneg (sq_nonneg _), hexp]
      nlinarith [mul_le_mul_of_nonneg_left hsqD hjpos]
  -- the squared norm of `F t - F t₀` tends to `0`
  have hsq : Tendsto (fun t => ‖F t - F t0‖ ^ 2) (𝓝[J] t0) (𝓝 0) := by
    have hfun : ∀ t ∈ J, ‖F t - F t0‖ ^ 2 = ∑' k : NonzeroLattice d,
        (Lattice.jp k.1 ^ (-r) * ((Torus.measureRealCoeff (ν t) k - Torus.measureRealCoeff (ν' t) k) -
          (Torus.measureRealCoeff (ν t0) k - Torus.measureRealCoeff (ν' t0) k))) ^ 2 := by
      intro t ht
      rw [(NegSobolev.coord_sq _).2]
      refine tsum_congr fun k => ?_
      rw [hsub, hcoord t ht k, hcoord t0 ht0 k]
      ring
    rw [tsum_zero] at hlim
    exact hlim.congr' (eventually_mem_nhdsWithin.mono fun t ht => (hfun t ht).symm)
  have hnorm := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hnorm
  refine hnorm.congr' ?_
  filter_upwards with t
  simp [Real.sqrt_sq (norm_nonneg _)]

end HRS.MC.Sec7.S7FCF5B

end
