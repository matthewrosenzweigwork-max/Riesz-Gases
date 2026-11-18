import HRS.MS.Fp81S21InitialUncentered11

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc MemCb)
open HRS.MS.R26T3

/-- The uncentered mean response at the actual initial law. The velocity in the pair energy is
the compatible physical velocity `γ⁻¹ ∇χ`; the deleted particle diagonal is retained exactly. -/
theorem fp81s21_initial_mean_pairEnergy
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ) {N : ℕ} (hN : 2 ≤ N)
    {ψ χ : Euc p.d → ℝ} {Bχ : ℝ}
    (hχ : S47.S47Feat p.d p.s (R.ρ 0) p.γ ψ χ Bχ)
    (hψ : MemCb 1 ψ) :
    ∫ X, Real.sqrt (N : ℝ) *
        (HRS.Whole.pair (HRS.Whole.empirical X) ψ -
          HRS.Whole.pair (r26t3_mu R 0) ψ) ∂(r26t3_Q R N) =
      -(p.γ / Real.sqrt (N : ℝ)) *
        ∫ X, (N : ℝ) * HRS.Whole.pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s
            (fun x => p.γ⁻¹ • gradient χ x)) X (r26t3_mu R 0) ∂(r26t3_Q R N) := by
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let P : Measure (EucConfig p.d N) := S47.s47_P p.d p.s (R.ρ 0) p.γ N
  let h : Euc p.d → Euc p.d → ℝ :=
    HRS.Whole.commutatorKernel p.d p.s (gradient χ)
  let v : Euc p.d → Euc p.d := fun x => p.γ⁻¹ • gradient χ x
  let hphys : Euc p.d → Euc p.d → ℝ := HRS.Whole.commutatorKernel p.d p.s v
  let U : Euc p.d → ℝ := HRS.Whole.convMeasure (HRS.Whole.rieszKernel p.d p.s) μ
  let row : Euc p.d → ℝ := fun x => ∫ y, h x y ∂μ
  let w : Euc p.d → ℝ := fun x =>
    ((p.a * p.β) / p.γ) * ⟪x, gradient χ x⟫ -
      p.γ⁻¹ * ⟪E.Bd x + p.γ • gradient U x, gradient χ x⟫
  let G : EucConfig p.d N → ℝ := fun X =>
    (∑ k, S45.s45_div (gradient χ) (X k)) -
      ((∑ i, (p.a * p.β * ⟪X i, gradient χ (X i)⟫ -
        (⟪E.Bd (X i), gradient χ (X i)⟫ +
          p.γ * ⟪gradient U (X i), gradient χ (X i)⟫))) +
        p.γ * ((1 / (N : ℝ)) *
          ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            ⟪HRS.Whole.rieszKernelGrad p.d p.s (X i - X j),
              gradient χ (X i) - gradient χ (X j)⟫))
  let S1 : EucConfig p.d N → ℝ := fun X =>
    (∑ k, Laplacian.laplacian χ (X k)) -
      p.γ * (∑ k, w (X k)) -
        (p.γ / (N : ℝ)) *
          ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), h (X i) (X j)
  have hNpos : 0 < N := by omega
  have hN1 : 1 ≤ N := Nat.le_trans (by omega) hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    have hd2 : (p.d : ℝ) / 2 ≤ (p.d : ℝ) := by nlinarith
    exact lt_of_lt_of_le p.hs hd2
  have hT : S47.TRef p.d p.s (R.ρ 0) (p.a * p.β) E.C E.c E.BU E.BB E.Bd := E.reference
  haveI hμprob : IsProbabilityMeasure μ := by
    dsimp [μ, r26t3_mu]
    exact HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hPprob : IsProbabilityMeasure P := E.static N hN |>.prob
  letI : IsProbabilityMeasure P := hPprob
  have hsd0 : 0 ≤ p.s := p.hs0
  have hγw : ∀ x, p.γ * w x =
      p.a * p.β * ⟪x, gradient χ x⟫ -
        ⟪E.Bd x + p.γ • gradient U x, gradient χ x⟫ := by
    intro x
    dsimp [w]
    field_simp [hγ.ne']
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ.smooth
  have hB20 : 0 ≤ Bχ := (norm_nonneg _).trans (hχ.B1 0)
  let Λ : ℝ≥0 := ⟨Bχ, hB20⟩
  have hLip : LipschitzWith Λ (gradient χ) :=
    lipschitzWith_of_nnnorm_fderiv_le (hv1.differentiable (by norm_num)) (fun x => by
      have hx := hχ.B2 x
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hx)
  have hhm : Measurable (Function.uncurry h) :=
    HRS.MS.Comm.comm_meas (s := p.s) (gradient χ) hv1.continuous.measurable
  have hDm : Measurable (fun X : EucConfig p.d N =>
      HRS.Whole.centeredPairFunctional h X μ) :=
    HRS.MS.Wr.wr14a_measurable_D hhm μ
  obtain ⟨hQVB, -⟩ := (E.static N hN).comm Λ (gradient χ) hLip
  have hvar := hQVB.2.2
  have hvarTop : ProbabilityTheory.evariance
      (fun X : EucConfig p.d N => HRS.Whole.centeredPairFunctional h X μ) P < ⊤ :=
    lt_of_le_of_lt hvar ENNReal.ofReal_lt_top
  have hDmem : MemLp (fun X : EucConfig p.d N =>
      HRS.Whole.centeredPairFunctional h X μ) 2 P :=
    (evariance_lt_top_iff_memLp hDm.aestronglyMeasurable).1 hvarTop
  have hDint : Integrable (fun X : EucConfig p.d N =>
      HRS.Whole.centeredPairFunctional h X μ) P := hDmem.integrable one_le_two
  have hpairEnergy : ∀ X : EucConfig p.d N,
      HRS.Whole.pairEnergy h X μ =
        (1 / 2) * HRS.Whole.centeredPairFunctional h X μ := by
    intro X
    rw [S99.s99_pairE_decomp hN1 h X μ μ]
    simp [HRS.Whole.pair]
  have hEhalf : Integrable (fun X : EucConfig p.d N =>
      (1 / 2 : ℝ) * HRS.Whole.centeredPairFunctional h X μ) P := hDint.const_mul _
  have hEintP : Integrable (fun X : EucConfig p.d N =>
      HRS.Whole.pairEnergy h X μ) P :=
    hEhalf.congr (Filter.Eventually.of_forall fun X => (hpairEnergy X).symm)
  have hEintQ : Integrable (fun X : EucConfig p.d N =>
      HRS.Whole.pairEnergy h X μ) (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact hEintP
  obtain ⟨Bψ, hBψ⟩ := hψ.2 0 (by omega)
  have hψbd : ∀ x, |ψ x| ≤ Bψ := by
    intro x
    have hx := hBψ (Set.mem_range_self x)
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hx
  have hψm : Measurable ψ := hψ.1.continuous.measurable
  have hEmpm : Measurable (fun X : EucConfig p.d N =>
      HRS.Whole.pair (HRS.Whole.empirical X) ψ) :=
    S45.s45_measurable_pair_empirical hN1 hψm
  have hEmpB : ∀ X : EucConfig p.d N,
      |HRS.Whole.pair (HRS.Whole.empirical X) ψ| ≤ Bψ :=
    s45_abs_pair_empirical_le hN1 hψbd
  let diff : EucConfig p.d N → ℝ := fun X =>
    HRS.Whole.pair (HRS.Whole.empirical X) ψ - HRS.Whole.pair μ ψ
  have hEmpInt : Integrable (fun X : EucConfig p.d N =>
      HRS.Whole.pair (HRS.Whole.empirical X) ψ) P :=
    Integrable.of_bound hEmpm.aestronglyMeasurable Bψ
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        exact hEmpB X)
  have hdiffIntP : Integrable diff P := by
    exact hEmpInt.sub (integrable_const (HRS.Whole.pair μ ψ))
  have hdiffIntQ : Integrable diff (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact hdiffIntP
  have hcfun := fp81s21_initial_c0_identity E hγ hχ hψ
  obtain ⟨c0, hc0, hstar⟩ := hcfun
  have hγwstar : ∀ x,
      p.γ * w x = p.a * p.β * ⟪x, gradient χ x⟫ -
        ⟪E.Bd x + p.γ • gradient U x, gradient χ x⟫ := hγw
  have hstar' : ∀ᵐ x ∂(volume : Measure (Euc p.d)),
      Laplacian.laplacian χ x - p.γ * w x - p.γ * row x = -p.γ * ψ x + c0 := by
    filter_upwards [hstar] with x hx
    have hwx : p.γ * w x = p.a * p.β * ⟪x, gradient χ x⟫ -
        (⟪E.Bd x, gradient χ x⟫ +
          p.γ * ⟪gradient U x, gradient χ x⟫) := by
      simpa only [inner_add_left, real_inner_smul_left] using hγwstar x
    rw [hwx]
    dsimp [row, μ, U] at hx ⊢
    simp only [inner_add_left, real_inner_smul_left] at hx
    linarith
  have hstarP := S45.s45_ae_P (g := HRS.Whole.rieszKernel p.d p.s)
    (V := S47.s47_V0 p.d p.s (R.ρ 0) p.γ) (β := p.γ) (N := N) hstar'
  have hstarQ : ∀ᵐ X ∂(r26t3_Q R N), ∀ k, 
      Laplacian.laplacian χ (X k) - p.γ * w (X k) - p.γ * row (X k) =
        -p.γ * ψ (X k) + c0 := by
    rw [← E.law_eq N]
    exact hstarP
  have hsym : ∀ x y, h x y = h y x := HRS.MS.Comm.comm_symm (gradient χ)
  have hGzero : ∫ X, G X ∂(r26t3_Q R N) = 0 := by
    simpa [G, U, μ, r26t3_mu] using fp81s21_initial_gibbs_ibp_one E hγ hN hχ
  have hG_eq_S1 : ∀ X : EucConfig p.d N, G X = S1 X := by
    intro X
    have hdiv : ∑ k, S45.s45_div (gradient χ) (X k) =
        ∑ k, Laplacian.laplacian χ (X k) := by
      exact Finset.sum_congr rfl fun k _ => s45_div_gradient hχ.smooth (X k)
    have hdrift :
        (∑ i, (p.a * p.β * ⟪X i, gradient χ (X i)⟫ -
          (⟪E.Bd (X i), gradient χ (X i)⟫ +
            p.γ * ⟪gradient U (X i), gradient χ (X i)⟫))) =
          p.γ * (∑ i, w (X i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi := (hγw (X i)).symm
      simpa only [inner_add_left, real_inner_smul_left] using hi
    have hpair : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ⟪HRS.Whole.rieszKernelGrad p.d p.s (X i - X j),
          gradient χ (X i) - gradient χ (X j)⟫ =
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), h (X i) (X j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      dsimp [h, HRS.Whole.commutatorKernel]
      exact real_inner_comm _ _
    dsimp [G, S1]
    rw [hdiv, hdrift, hpair]
    ring
  have hS1zero : ∫ X, S1 X ∂(r26t3_Q R N) = 0 := by
    calc
      _ = ∫ X, G X ∂(r26t3_Q R N) :=
        integral_congr_ae (Filter.Eventually.of_forall fun X => (hG_eq_S1 X).symm)
      _ = 0 := hGzero
  have hkernel : h = fun x y => p.γ * hphys x y := by
    funext x y
    dsimp [h, hphys, v, HRS.Whole.commutatorKernel]
    have hv : p.γ⁻¹ • gradient χ x - p.γ⁻¹ • gradient χ y =
        p.γ⁻¹ • (gradient χ x - gradient χ y) := by rw [smul_sub]
    rw [hv, real_inner_smul_left]
    field_simp [hγ.ne']
  have henergyScale : ∀ X : EucConfig p.d N,
      HRS.Whole.pairEnergy h X μ = p.γ * HRS.Whole.pairEnergy hphys X μ := by
    intro X
    rw [hkernel]
    unfold HRS.Whole.pairEnergy
    simp only [integral_const_mul, ← Finset.mul_sum]
    ring
  have hphysIntQ : Integrable (fun X : EucConfig p.d N =>
      HRS.Whole.pairEnergy hphys X μ) (r26t3_Q R N) := by
    have hscaled : Integrable (fun X : EucConfig p.d N =>
        p.γ⁻¹ * HRS.Whole.pairEnergy h X μ) (r26t3_Q R N) := hEintQ.const_mul _
    have heq : (fun X : EucConfig p.d N => p.γ⁻¹ *
        HRS.Whole.pairEnergy h X μ) =ᵐ[r26t3_Q R N]
          fun X => HRS.Whole.pairEnergy hphys X μ := by
      filter_upwards with X
      rw [henergyScale X]
      field_simp [hγ.ne']
    exact hscaled.congr heq
  have hdiffScale : Integrable (fun X : EucConfig p.d N =>
      Real.sqrt (N : ℝ) * diff X) (r26t3_Q R N) := hdiffIntQ.const_mul _
  have hphysScale : Integrable (fun X : EucConfig p.d N =>
      (N : ℝ) * HRS.Whole.pairEnergy hphys X μ) (r26t3_Q R N) := hphysIntQ.const_mul _
  have hpoint : ∀ᵐ X ∂(r26t3_Q R N),
      S1 X = -(p.γ * (N : ℝ)) * diff X -
        (p.γ * (N : ℝ)) * HRS.Whole.pairEnergy h X μ := by
    filter_upwards [hstarQ] with X hX
    have hA := S45.s45_claimA hN1 hsym (ν := μ)
      (Lap := Laplacian.laplacian χ) (w := w) (Hm := row) (φ := ψ)
      (β := p.γ) (c0 := c0) (ED := 0) X hX
    have hA' : S1 X =
        (N : ℝ) * (-p.γ * diff X + p.γ *
          ((HRS.Whole.pair (HRS.Whole.empirical X) (fun _ => (0 : ℝ)) -
              HRS.Whole.pair μ (fun _ => (0 : ℝ))) -
            (1 / 2) * (HRS.Whole.centeredPairFunctional h X μ - 0))) +
          (N : ℝ) * (c0 - p.γ * HRS.Whole.pair μ ψ +
            p.γ * HRS.Whole.pair μ (fun _ => (0 : ℝ)) -
            (p.γ / 2) * 0 + (p.γ / 2) *
              ∫ x, ∫ y, h x y ∂μ ∂μ) := by
      simpa [S1, row] using hA
    have hconst0 : c0 - p.γ * HRS.Whole.pair μ ψ +
        (p.γ / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ = 0 := by
      rw [hc0]
      simp [HRS.Whole.pair, h, μ]
      ring
    have hzeroEmp : HRS.Whole.pair (HRS.Whole.empirical X) (fun _ => (0 : ℝ)) = 0 := by
      simp [HRS.Whole.pair]
    have hzeroMu : HRS.Whole.pair μ (fun _ => (0 : ℝ)) = 0 := by
      simp [HRS.Whole.pair]
    rw [hzeroEmp, hzeroMu] at hA'
    simp only [mul_zero, sub_zero, add_zero] at hA'
    rw [hconst0] at hA'
    simp only [zero_sub, mul_neg, mul_one, add_zero] at hA'
    rw [← hpairEnergy X] at hA'
    have hAeq0 : S1 X =
        (N : ℝ) * (-p.γ * diff X + -(p.γ * HRS.Whole.pairEnergy h X μ)) := by
      simpa only [mul_zero, add_zero] using hA'
    have hA'' : S1 X = -(p.γ * (N : ℝ)) * diff X -
        (p.γ * (N : ℝ)) * HRS.Whole.pairEnergy h X μ := by
      calc
        _ = (N : ℝ) * (-p.γ * diff X + -(p.γ * HRS.Whole.pairEnergy h X μ)) := hAeq0
        _ = _ := by ring
    exact hA''
  have hrawMean :
      ∫ X, -(p.γ * (N : ℝ)) * diff X -
        (p.γ * (N : ℝ)) * HRS.Whole.pairEnergy h X μ ∂(r26t3_Q R N) = 0 := by
    calc
      _ = ∫ X, S1 X ∂(r26t3_Q R N) :=
        (integral_congr_ae hpoint).symm
      _ = 0 := hS1zero
  have hsplit :
      ∫ X, -(p.γ * (N : ℝ)) * diff X -
        (p.γ * (N : ℝ)) * HRS.Whole.pairEnergy h X μ ∂(r26t3_Q R N) =
        -(p.γ * (N : ℝ)) * ∫ X, diff X ∂(r26t3_Q R N) -
          (p.γ * (N : ℝ)) * ∫ X, HRS.Whole.pairEnergy h X μ
            ∂(r26t3_Q R N) := by
    rw [integral_sub (hdiffIntQ.const_mul _) (hEintQ.const_mul _),
      integral_const_mul, integral_const_mul]
  have hsum :
      (∫ X, diff X ∂(r26t3_Q R N)) +
        (∫ X, HRS.Whole.pairEnergy h X μ ∂(r26t3_Q R N)) = 0 := by
    have hEq := hsplit.symm.trans hrawMean
    have hγNne : p.γ * (N : ℝ) ≠ 0 := mul_ne_zero hγ.ne' (by exact_mod_cast hNpos.ne')
    have hfac : (p.γ * (N : ℝ)) *
        ((∫ X, diff X ∂(r26t3_Q R N)) +
          (∫ X, HRS.Whole.pairEnergy h X μ ∂(r26t3_Q R N))) = 0 := by
      nlinarith [hEq]
    exact (mul_eq_zero.mp hfac).resolve_left hγNne
  have hscaleIntegral :
      (∫ X, HRS.Whole.pairEnergy h X μ ∂(r26t3_Q R N)) =
        p.γ * ∫ X, HRS.Whole.pairEnergy hphys X μ ∂(r26t3_Q R N) := by
    calc
      _ = ∫ X, p.γ * HRS.Whole.pairEnergy hphys X μ ∂(r26t3_Q R N) :=
        integral_congr_ae (Filter.Eventually.of_forall fun X => henergyScale X)
      _ = _ := integral_const_mul p.γ (fun X : EucConfig p.d N =>
        HRS.Whole.pairEnergy hphys X μ)
  have hleft :
      ∫ X, Real.sqrt (N : ℝ) * diff X ∂(r26t3_Q R N) =
        Real.sqrt (N : ℝ) * ∫ X, diff X ∂(r26t3_Q R N) :=
    integral_const_mul (Real.sqrt (N : ℝ)) diff
  have hright :
      ∫ X, (N : ℝ) * HRS.Whole.pairEnergy hphys X μ ∂(r26t3_Q R N) =
        (N : ℝ) * ∫ X, HRS.Whole.pairEnergy hphys X μ ∂(r26t3_Q R N) :=
    integral_const_mul (N : ℝ) (fun X => HRS.Whole.pairEnergy hphys X μ)
  have hsqrtN : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hfinalScalar :
      Real.sqrt (N : ℝ) * ∫ X, diff X ∂(r26t3_Q R N) =
        -(p.γ / Real.sqrt (N : ℝ)) *
          ((N : ℝ) * ∫ X, HRS.Whole.pairEnergy hphys X μ ∂(r26t3_Q R N)) := by
    have hAB := hsum
    rw [hscaleIntegral] at hAB
    have hA := congrArg (fun z : ℝ => Real.sqrt (N : ℝ) * z) (by linarith [hAB] :
      (∫ X, diff X ∂(r26t3_Q R N)) =
        -p.γ * ∫ X, HRS.Whole.pairEnergy hphys X μ ∂(r26t3_Q R N))
    rw [hA]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hNreal)]
    rw [hsqrtN]
    ring
  calc
    ∫ X, Real.sqrt (N : ℝ) * diff X ∂(r26t3_Q R N) =
        Real.sqrt (N : ℝ) * ∫ X, diff X ∂(r26t3_Q R N) := hleft
    _ = -(p.γ / Real.sqrt (N : ℝ)) *
          ((N : ℝ) * ∫ X, HRS.Whole.pairEnergy hphys X μ ∂(r26t3_Q R N)) := hfinalScalar
    _ = -(p.γ / Real.sqrt (N : ℝ)) *
          ∫ X, (N : ℝ) * HRS.Whole.pairEnergy hphys X μ ∂(r26t3_Q R N) := by rw [hright]

#print axioms fp81s21_initial_mean_pairEnergy

end HRS.Fp81.S21

end
