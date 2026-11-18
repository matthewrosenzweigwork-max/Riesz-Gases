import HRS.MS.R26T8AA01u

/-!
# S8.2 T8A A01 (part v): `∫ tripleG(x,y,·) dμ = 0`
Exterior-region exhaustion: the eleven pieces of `3 ρ tripleG`; limits via the force PV (A01l), `oneJ` PV (A01m),
the centred rows (A01r), P11g (a) and the canonical pair `pairJ`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 12800000 in
theorem r26t8a_a01_zero (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {f : Euc d → ℝ} {A : ℝ}
    (hA : 0 ≤ A) {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) {x y : Euc d} (hxy : x ≠ y) :
    ∫ z, tripleG (critCoeff d a beta rho) rho Q x y z ∂(HRS.Whole.withDensityReal rho) = 0 := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  haveI := s85_isProb hprob
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal rho with hμ
  set C0 := critCoeff d a beta rho with hC0
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hbeta hrho).1
  have hρc : Continuous rho := hρs.continuous
  have hρi : Integrable rho := Integrable.of_integral_ne_zero (by rw [hprob.integral_one]; norm_num)
  have hrho0 : ∀ t, 0 ≤ rho t := hprob.nonneg
  have hsymm := hQ.symmetric
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hQt : Conormal (4 + 2) 1 M (criticalS d - 2) A Q := hQ.tangential
  have hFc : Continuous (forceMean rho) := (r26t8a_thermal_force d hd a beta ha hbeta rho hrho).1.continuous
  set Ω : ℝ → Set (Euc d) := fun ε => {z | ε < ‖x - z‖ ∧ ε < ‖y - z‖} with hΩ
  have hmeasΩ : ∀ ε, MeasurableSet (Ω ε) := fun ε =>
    (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm).inter
      (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm)
  have hΩ' : ∀ ε, {z : Euc d | ε < ‖y - z‖ ∧ ε < ‖x - z‖} = Ω ε := fun ε => r26t8a_a01_omega_comm x y ε
  -- the means
  set m : Euc d → ℝ := fun w => ∫ t, oneJ C0 (fun u => Q u w) t ∂μ with hm
  have hmI : ∀ w, ∫ z, rho z * inner ℝ (forceMean rho z) (pairGradX Q z w) = -m w := by
    intro w
    have := (r26t8a_g5_row d hd 4 1 a beta M (criticalS d) ha hbeta hM hsd rho hrho Q A hA hQt w).2
    rw [r26t8a_f25_wd_integral hprob, r26t8a_f25_wd_integral hprob] at this
    simp only [hm]
    rw [r26t8a_f25_wd_integral hprob, this]
    ring
  set Jxy := pairJ C0 μ Q x y with hJxy
  have hdec := r26t8a_a01_pairJ_decomp C0 μ hsymm x y
  -- integrable global pieces
  have iF5 := r26t8a_a01_Fgrad_int hd a beta M A ha hbeta hM hA hrho hQ x
  have iF8 := r26t8a_a01_Fgrad_int hd a beta M A ha hbeta hM hA hrho hQ y
  have hJrow : ∀ u, Integrable (fun z => rho z * pairJ C0 μ Q u z) := fun u =>
    (r26t8a_f25_wd_integrable hprob _).1 (hQ.nonlocal.1.2.1 u)
  have hJ0 : ∀ u, ∫ z, rho z * pairJ C0 μ Q u z = 0 := fun u => by
    rw [← r26t8a_f25_wd_integral hprob]; exact hQ.nonlocal.1.2.2.2 u
  have hG := r26t8a_a01_integrable d hd a beta M ha hbeta hM hrho hA hQ hxy
  have hGρ : Integrable (fun z => rho z * (3 * tripleG C0 rho Q x y z)) :=
    (((r26t8a_f25_wd_integrable hprob _).1 hG).const_mul 3).congr
      (Filter.Eventually.of_forall fun z => by ring)
  -- the eleven pieces
  set F : Euc d → Euc d := forceMean rho with hFdef
  set g : Euc d → Euc d := rieszKernelGrad d (criticalS d) with hgdef
  set Q1 : Euc d → ℝ := fun z => -(rho z * inner ℝ (g (x - z) - F x) (pairGradX Q x y)) with hQ1
  set Q2 : Euc d → ℝ := fun z => -(rho z * inner ℝ (g (y - z) - F y) (pairGradX Q y x)) with hQ2d
  set Q3 : Euc d → ℝ := fun z => -(rho z * inner ℝ (g (x - y) - F x) (pairGradX Q x z)) with hQ3
  set Q4 : Euc d → ℝ := fun z => rho z * inner ℝ (g (y - z)) (pairGradX Q z x) with hQ4
  set Q5 : Euc d → ℝ := fun z => rho z * inner ℝ (F z) (pairGradX Q z x) with hQ5
  set Q6 : Euc d → ℝ := fun z => -(rho z * inner ℝ (g (y - x) - F y) (pairGradX Q y z)) with hQ6
  set Q7 : Euc d → ℝ := fun z => rho z * inner ℝ (g (x - z)) (pairGradX Q z y) with hQ7
  set Q8 : Euc d → ℝ := fun z => rho z * inner ℝ (F z) (pairGradX Q z y) with hQ8
  set Q9 : Euc d → ℝ := fun z => -(rho z * Jxy) with hQ9
  set Q10 : Euc d → ℝ := fun z => -(rho z * pairJ C0 μ Q x z) with hQ10
  set Q11 : Euc d → ℝ := fun z => -(rho z * pairJ C0 μ Q y z) with hQ11
  have hsum : ∀ z, rho z * (3 * tripleG C0 rho Q x y z) =
      Q1 z + Q2 z + Q3 z + Q4 z + Q5 z + Q6 z + Q7 z + Q8 z + Q9 z + Q10 z + Q11 z := by
    intro z
    have := r26t8a_a01_ungrouped (a := a) (beta := beta) (rho := rho) hsymm x y z
    simp only [hQ1, hQ2d, hQ3, hQ4, hQ5, hQ6, hQ7, hQ8, hQ9, hQ10, hQ11, hFdef, hgdef, hJxy]
    rw [mul_comm (rho z) _, this]
    simp only [inner_add_left, inner_sub_left, hC0]
    ring
  -- integrability of the indicator pieces
  have hmeasW : ∀ (W : Euc d → Euc d), AEStronglyMeasurable W volume → AEStronglyMeasurable (fun z => rho z * ‖W z‖) volume :=
    fun W hW => hρc.aestronglyMeasurable.mul hW.norm
  have hI1 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q1) := fun ε hε => by
    have := (r26t8a_a01_limFc hd ha hbeta hrho hxy (pairGradX Q x y)).1 ε hε
    exact r26t8a_a01_ind_neg_int this
  have hI2 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q2) := fun ε hε => by
    have := (r26t8a_a01_limFc hd ha hbeta hrho hxy.symm (pairGradX Q y x)).1 ε hε
    rw [hΩ'] at this
    exact r26t8a_a01_ind_neg_int this
  have hI3 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q3) := fun ε hε => by
    have := (r26t8a_a01_limDx hd a beta M A ha hbeta hM hA hrho hQ x (g (x - y) - F x) x y).1 ε hε
    exact r26t8a_a01_ind_neg_int this
  have hI6 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q6) := fun ε hε => by
    have := (r26t8a_a01_limDx hd a beta M A ha hbeta hM hA hrho hQ y (g (y - x) - F y) x y).1 ε hε
    exact r26t8a_a01_ind_neg_int this
  have hgradc : ∀ w : Euc d, AEStronglyMeasurable (fun z => pairGradX Q z w) volume := fun w =>
    r26t8a_a01_aesm_vec hd w (r26t8a_a01_gradX_cont_fst hQ2 w)
  have hI4 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q4) := fun ε hε =>
    r26t8a_a01_ext_int_inner hd hrho0 hρc.aestronglyMeasurable (W := fun z => pairGradX Q z x) (hgradc x)
      (r26t8a_a01_grad_int hd a beta M A ha hbeta hM hA hrho hQ x).1 y hε (Ω ε) (hmeasΩ ε) (fun z hz => hz.2)
  have hI7 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q7) := fun ε hε =>
    r26t8a_a01_ext_int_inner hd hrho0 hρc.aestronglyMeasurable (W := fun z => pairGradX Q z y) (hgradc y)
      (r26t8a_a01_grad_int hd a beta M A ha hbeta hM hA hrho hQ y).1 x hε (Ω ε) (hmeasΩ ε) (fun z hz => hz.1)
  have hI5 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q5) := fun ε _ => iF5.indicator (hmeasΩ ε)
  have hI8 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q8) := fun ε _ => iF8.indicator (hmeasΩ ε)
  have iQ9 : Integrable Q9 := (hρi.mul_const Jxy).neg
  have iQ10 : Integrable Q10 := (hJrow x).neg
  have iQ11 : Integrable Q11 := (hJrow y).neg
  have hI9 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q9) := fun ε _ => iQ9.indicator (hmeasΩ ε)
  have hI10 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q10) := fun ε _ => iQ10.indicator (hmeasΩ ε)
  have hI11 : ∀ ε, 0 < ε → Integrable (Set.indicator (Ω ε) Q11) := fun ε _ => iQ11.indicator (hmeasΩ ε)
  -- the limits
  have hL1 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q1 z) (𝓝[>] 0) (𝓝 0) := by
    simpa using r26t8a_a01_ind_neg_tendsto (S := Ω) (r26t8a_a01_limFc hd ha hbeta hrho hxy (pairGradX Q x y)).2
  have hL2 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q2 z) (𝓝[>] 0) (𝓝 0) := by
    have := (r26t8a_a01_limFc hd ha hbeta hrho hxy.symm (pairGradX Q y x)).2
    simp only [hΩ'] at this
    simpa using r26t8a_a01_ind_neg_tendsto (S := Ω) this
  have hL3 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q3 z) (𝓝[>] 0) (𝓝 0) := by
    simpa using r26t8a_a01_ind_neg_tendsto (S := Ω)
      (r26t8a_a01_limDx hd a beta M A ha hbeta hM hA hrho hQ x (g (x - y) - F x) x y).2
  have hL6 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q6 z) (𝓝[>] 0) (𝓝 0) := by
    simpa using r26t8a_a01_ind_neg_tendsto (S := Ω)
      (r26t8a_a01_limDx hd a beta M A ha hbeta hM hA hrho hQ y (g (y - x) - F y) x y).2
  have hL4 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q4 z) (𝓝[>] 0)
      (𝓝 (oneJ C0 (fun t => Q t x) y)) := by
    have := r26t8a_a01_limJ hd a beta M A ha hbeta hM hA hrho hQ hxy.symm
    simp only [hΩ'] at this
    exact this
  have hL7 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q7 z) (𝓝[>] 0)
      (𝓝 (oneJ C0 (fun t => Q t y) x)) :=
    r26t8a_a01_limJ hd a beta M A ha hbeta hM hA hrho hQ hxy
  have hL5 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q5 z) (𝓝[>] 0) (𝓝 (-m x)) := by
    have := r26t8a_a01_limint hd x y iF5
    rw [hmI x] at this; exact this
  have hL8 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q8 z) (𝓝[>] 0) (𝓝 (-m y)) := by
    have := r26t8a_a01_limint hd x y iF8
    rw [hmI y] at this; exact this
  have hL9 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q9 z) (𝓝[>] 0) (𝓝 (-Jxy)) := by
    have := r26t8a_a01_limint hd x y iQ9
    have e : ∫ z, Q9 z = -Jxy := by
      simp only [hQ9]; rw [integral_neg, integral_mul_const, hprob.integral_one, one_mul]
    rwa [e] at this
  have hL10 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q10 z) (𝓝[>] 0) (𝓝 0) := by
    have := r26t8a_a01_limint hd x y iQ10
    have e : ∫ z, Q10 z = 0 := by simp only [hQ10]; rw [integral_neg, hJ0 x, neg_zero]
    rwa [e] at this
  have hL11 : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) Q11 z) (𝓝[>] 0) (𝓝 0) := by
    have := r26t8a_a01_limint hd x y iQ11
    have e : ∫ z, Q11 z = 0 := by simp only [hQ11]; rw [integral_neg, hJ0 y, neg_zero]
    rwa [e] at this
  -- the sum
  have hTot := ((((((((((hL1.add hL2).add hL3).add hL4).add hL5).add hL6).add hL7).add hL8).add hL9).add hL10).add hL11)
  have hfin : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) (fun z => rho z * (3 * tripleG C0 rho Q x y z)) z)
      (𝓝[>] 0) (𝓝 (∫ z, rho z * (3 * tripleG C0 rho Q x y z))) := r26t8a_a01_limint hd x y hGρ
  have hlimit : (0 + 0 + 0 + oneJ C0 (fun t => Q t x) y + -m x + 0 + oneJ C0 (fun t => Q t y) x + -m y + -Jxy + 0 + 0 : ℝ) = 0 := by
    have := hdec
    simp only [← hm] at this
    rw [← hJxy] at this
    linarith
  rw [hlimit] at hTot
  have hTot' : Tendsto (fun ε => ∫ z, Set.indicator (Ω ε) (fun z => rho z * (3 * tripleG C0 rho Q x y z)) z)
      (𝓝[>] 0) (𝓝 0) := by
    refine hTot.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hsplit : Set.indicator (Ω ε) (fun z => rho z * (3 * tripleG C0 rho Q x y z)) =
        fun z => Set.indicator (Ω ε) Q1 z + Set.indicator (Ω ε) Q2 z + Set.indicator (Ω ε) Q3 z +
          Set.indicator (Ω ε) Q4 z + Set.indicator (Ω ε) Q5 z + Set.indicator (Ω ε) Q6 z +
          Set.indicator (Ω ε) Q7 z + Set.indicator (Ω ε) Q8 z + Set.indicator (Ω ε) Q9 z +
          Set.indicator (Ω ε) Q10 z + Set.indicator (Ω ε) Q11 z := by
      funext z
      by_cases hz : z ∈ Ω ε
      · simp only [Set.indicator_of_mem hz]; exact hsum z
      · simp [Set.indicator_of_notMem hz]
    rw [hsplit]
    have i1 := hI1 ε hε; have i2 := hI2 ε hε; have i3 := hI3 ε hε; have i4 := hI4 ε hε
    have i5 := hI5 ε hε; have i6 := hI6 ε hε; have i7 := hI7 ε hε; have i8 := hI8 ε hε
    have i9 := hI9 ε hε; have i10 := hI10 ε hε; have i11 := hI11 ε hε
    have s1 : Integrable (fun z => Set.indicator (Ω ε) Q1 z + Set.indicator (Ω ε) Q2 z) := i1.add i2
    have s2 : Integrable (fun z => Set.indicator (Ω ε) Q1 z + Set.indicator (Ω ε) Q2 z + Set.indicator (Ω ε) Q3 z) := s1.add i3
    have s3 : Integrable (fun z => Set.indicator (Ω ε) Q1 z + Set.indicator (Ω ε) Q2 z + Set.indicator (Ω ε) Q3 z +
        Set.indicator (Ω ε) Q4 z) := s2.add i4
    have s4 : Integrable (fun z => Set.indicator (Ω ε) Q1 z + Set.indicator (Ω ε) Q2 z + Set.indicator (Ω ε) Q3 z +
        Set.indicator (Ω ε) Q4 z + Set.indicator (Ω ε) Q5 z) := s3.add i5
    have s5 : Integrable (fun z => Set.indicator (Ω ε) Q1 z + Set.indicator (Ω ε) Q2 z + Set.indicator (Ω ε) Q3 z +
        Set.indicator (Ω ε) Q4 z + Set.indicator (Ω ε) Q5 z + Set.indicator (Ω ε) Q6 z) := s4.add i6
    have s6 : Integrable (fun z => Set.indicator (Ω ε) Q1 z + Set.indicator (Ω ε) Q2 z + Set.indicator (Ω ε) Q3 z +
        Set.indicator (Ω ε) Q4 z + Set.indicator (Ω ε) Q5 z + Set.indicator (Ω ε) Q6 z +
        Set.indicator (Ω ε) Q7 z) := s5.add i7
    have s7 : Integrable (fun z => Set.indicator (Ω ε) Q1 z + Set.indicator (Ω ε) Q2 z + Set.indicator (Ω ε) Q3 z +
        Set.indicator (Ω ε) Q4 z + Set.indicator (Ω ε) Q5 z + Set.indicator (Ω ε) Q6 z +
        Set.indicator (Ω ε) Q7 z + Set.indicator (Ω ε) Q8 z) := s6.add i8
    have s8 : Integrable (fun z => Set.indicator (Ω ε) Q1 z + Set.indicator (Ω ε) Q2 z + Set.indicator (Ω ε) Q3 z +
        Set.indicator (Ω ε) Q4 z + Set.indicator (Ω ε) Q5 z + Set.indicator (Ω ε) Q6 z +
        Set.indicator (Ω ε) Q7 z + Set.indicator (Ω ε) Q8 z + Set.indicator (Ω ε) Q9 z) := s7.add i9
    have s9 : Integrable (fun z => Set.indicator (Ω ε) Q1 z + Set.indicator (Ω ε) Q2 z + Set.indicator (Ω ε) Q3 z +
        Set.indicator (Ω ε) Q4 z + Set.indicator (Ω ε) Q5 z + Set.indicator (Ω ε) Q6 z +
        Set.indicator (Ω ε) Q7 z + Set.indicator (Ω ε) Q8 z + Set.indicator (Ω ε) Q9 z +
        Set.indicator (Ω ε) Q10 z) := s8.add i10
    rw [integral_add s9 i11, integral_add s8 i10, integral_add s7 i9, integral_add s6 i8, integral_add s5 i7,
      integral_add s4 i6, integral_add s3 i5, integral_add s2 i4, integral_add s1 i3, integral_add i1 i2]
  have h3 : ∫ z, rho z * (3 * tripleG C0 rho Q x y z) = 0 := tendsto_nhds_unique hfin hTot'
  have h4 : ∫ z, rho z * tripleG C0 rho Q x y z = 0 := by
    have : ∫ z, rho z * (3 * tripleG C0 rho Q x y z) = 3 * ∫ z, rho z * tripleG C0 rho Q x y z := by
      rw [← integral_const_mul]; congr 1; funext z; ring
    linarith
  rw [r26t8a_f25_wd_integral hprob]
  exact h4

end HRS.MS.R26T8A
