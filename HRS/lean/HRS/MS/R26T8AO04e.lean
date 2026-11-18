import HRS.MS.R26T8AO04d

/-!
# S8.2 T8A O04 (part e): the noise energy at a fixed time `r ∈ [0,b]`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d N : ℕ}

set_option maxHeartbeats 12800000 in
theorem r26t8a_o04_energy_at (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) {Omega : Type} [mOmega : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (F : Filtration ℝ mOmega) (W' : ℝ≥0 → Omega → (Fin N×Fin d) → ℝ)
    (hfilt : IsWholeFilteredSolution P F W' W X) (alpha : MultiIndex d) (j : ℕ) (hj : j≤1)
    (b r : ℝ) (hr0 : 0 ≤ r) (hrb : r ≤ b) :
    ∫⁻ w, ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X j b r w i‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal ((2 / beta) * (C * Cf * HRS.MS.S82BD.s82Weight d m alpha) ^ 2 / (N : ℝ) *
        Real.exp (-2 * c * (b - r))) := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  set t : ℝ≥0 := r.toNNReal with ht
  have hlaw : law P (X t) = canonicalP d N a beta :=
    hX.invariant P (t : ℝ) X0 W X hX.brownian hX.indep hX.init (hX.solution t) t le_rfl
  have hXm : Measurable (X t) := (hfilt.adapted t).mono (F.le _) le_rfl
  -- the profile at this time
  set g : EucConfig d N → ℝ≥0∞ := fun x => ∑ i : Fin N × Fin d,
    ‖r26t8a_o04_G d N a beta m rho Psi alpha j b r x i‖ₑ ^ 2 with hg
  have hgm : Measurable g := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have := r26t8a_o04_G_meas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha j hj i
    exact (this.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).enorm.pow_const 2
  have hrt : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  have h1 : ∫⁻ w, ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X j b r w i‖ₑ ^ 2 ∂P =
      ∫⁻ x, g x ∂(canonicalP d N a beta) := by
    rw [← hlaw, lintegral_map hgm hXm]
    rfl
  rw [h1]
  -- the test function and its bounds
  have hbd := horb.bound alpha (b - r) (sub_nonneg.2 hrb) j (by omega)
  set A : ℝ := Cf * HRS.MS.S82BD.s82Weight d m alpha * Real.exp (-c * (b - r)) with hA
  have hA0 : 0 ≤ A := r26t8a_o03b_tb_nonneg (by unfold testOrder; omega) hbd
  have hcore := (hPsi.bound N hN _ A hA0 hbd).2
  set I : ℝ≥0∞ := ∫⁻ x, ∑ i : Fin N, ‖Phase2S82.configGrad
    (r26t8a_correctedQ (N := N) a beta Psi (r26t8a_ageTest a beta m rho alpha j (b - r))) x i‖ₑ ^ 2
    ∂(canonicalP d N a beta) with hI
  have hI12 : I ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
    (le_add_self.trans le_self_add).trans hcore
  have hy0 : 0 ≤ C * A * (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg hC hA0) (Real.rpow_nonneg hN0.le _)
  have hI2 : I ≤ ENNReal.ofReal ((C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) := by
    calc I = (I ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by rw [← ENNReal.rpow_mul]; norm_num
      _ ≤ (ENNReal.ofReal (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hI12 (by norm_num)
      _ = ENNReal.ofReal ((C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hy0 (by norm_num), Real.rpow_two]
  -- pointwise comparison with the configuration gradient
  have hpt : ∀ x : EucConfig d N, g x ≤ ENNReal.ofReal (2 / beta) * ∑ i : Fin N,
      ‖Phase2S82.configGrad (r26t8a_correctedQ (N := N) a beta Psi
        (r26t8a_ageTest a beta m rho alpha j (b - r))) x i‖ₑ ^ 2 := by
    intro x
    by_cases hx : 0 ≤ r ∧ r ≤ b ∧ x ∉ eucCollisionSet d N
    · have hG : ∀ i : Fin N × Fin d, r26t8a_o04_G d N a beta m rho Psi alpha j b r x i =
          Real.sqrt (2 / beta) * Phase2S82.configGrad (r26t8a_correctedQ (N := N) a beta Psi
            (r26t8a_ageTest a beta m rho alpha j (b - r))) x i.1 i.2 := fun i => by
        unfold r26t8a_o04_G
        rw [if_pos hx]
        rfl
      simp only [hg, hG]
      rw [Fintype.sum_prod_type]
      simp_rw [r26t8a_o04_enorm_sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / beta), ← Finset.mul_sum,
        r26t8a_o04_sum_enorm_sq]
      rw [Finset.mul_sum]
    · have : g x = 0 := by
        simp only [hg]
        refine Finset.sum_eq_zero fun i _ => ?_
        unfold r26t8a_o04_G
        rw [if_neg hx]
        simp
      rw [this]; exact zero_le
  have h2 : ∫⁻ x, g x ∂(canonicalP d N a beta) ≤
      ENNReal.ofReal (2 / beta) * I := by
    calc ∫⁻ x, g x ∂(canonicalP d N a beta) ≤ ∫⁻ x, ENNReal.ofReal (2 / beta) * ∑ i : Fin N,
          ‖Phase2S82.configGrad (r26t8a_correctedQ (N := N) a beta Psi
            (r26t8a_ageTest a beta m rho alpha j (b - r))) x i‖ₑ ^ 2 ∂(canonicalP d N a beta) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 / beta) * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  refine h2.trans ?_
  calc ENNReal.ofReal (2 / beta) * I ≤ ENNReal.ofReal (2 / beta) *
        ENNReal.ofReal ((C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) := mul_le_mul_of_nonneg_left hI2 (zero_le)
    _ = ENNReal.ofReal ((2 / beta) * (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = _ := by
        congr 1
        have hNrt : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          norm_num
          exact Real.rpow_neg_one _
        have hexp : Real.exp (-c * (b - r)) ^ 2 = Real.exp (-2 * c * (b - r)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [mul_pow, hNrt, hA, mul_pow, mul_pow, hexp]
        field_simp

end HRS.MS.R26T8A

end
