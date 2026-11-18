import HRS.MS.QprepAux8

/-!
# S4.6 packet A9: the `R` and `T` bounds, uniform in `(a, β, γ₀)`

Copies of `s45_Hd_L2`, `s45_R_bound`, `s45_T_bound` for `Q_{N,γ₀}`, with the constants quantified before the parameters:
`K_R = √C_s (C_W (s+1) C_s + 1)` depends on `C_s` and `C_W(d, s, C)` only; `K_T = √C_s + C_s`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S46

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s46_Hd_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (C : ℝ) :
    ∃ CW : ℝ, 0 ≤ CW ∧ ∀ {a β c BU : ℝ} (hT : ThermalData d s a β C c BU) {Λ : ℝ≥0} {v : Euc d → Euc d}
      (hv : LipschitzWith Λ v)
      {φN : Euc d → ℝ} {Cs : ℝ} (hφb : ∀ x, 0 ≤ φN x ∧ φN x ≤ Cs) (hφm : Measurable φN)
      (hφ2 : MemLp (fun x => φN x - 1) 2 (thermalMeasure d s a β))
      (ν : Measure (Euc d)) (hν : ν = (thermalMeasure d s a β).withDensity
        (fun x => ENNReal.ofReal (φN x))) (r : ℝ),
      l2Norm (thermalMeasure d s a β) (fun x => φN x - 1) ≤ r → 0 ≤ r →
      ∫ x, ((∫ y, commutatorKernel d s v x y ∂(thermalMeasure d s a β)) -
        ∫ y, commutatorKernel d s v x y ∂ν) ^ 2 ∂(thermalMeasure d s a β) ≤
        (CW * ((s + 1) * (Λ : ℝ)) * r) ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨CW, hCW0, hCW⟩ := HRS.MS.Wr.wr13c_schur_W_real hd1 hs0 hsd C
  refine ⟨CW, hCW0, fun {a β c BU} hT {Λ v} hv {φN Cs} hφb hφm hφ2 ν hν r hr hr0 => ?_⟩
  have hM := s45_thermal_le hT
  haveI hμprob : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨Mρ, hMρ0, hrow⟩ := HRS.MS.S53.s53_rowConst hd1 hs0 hsd hT.prob hM
  have hΛ : (0 : ℝ) ≤ Λ := NNReal.coe_nonneg Λ
  have hhm : Measurable (fun p : Euc d × Euc d => commutatorKernel d s v p.1 p.2) :=
    HRS.MS.Comm.comm_meas (s := s) v hv.continuous.measurable
  have hbd : ∀ x y, x ≠ y → |commutatorKernel d s v x y| ≤
      ((s + 1) * (Λ : ℝ)) * (1 + rieszWeight s (x - y)) := fun x y _ => by
    exact HRS.MS.S53.s53_comm_bound hs0 hv x y
  have hf2 : MemLp (fun x => φN x - 1) 2 (withDensityReal (thermalDensity d s a β)) := hφ2
  obtain ⟨-, hS⟩ := hCW (thermalDensity d s a β) hT.prob hM ((s + 1) * (Λ : ℝ)) (by positivity)
    (fun x y => commutatorKernel d s v x y) hhm hbd (fun x => φN x - 1)
    (hφm.sub measurable_const) hf2
  have hrowrep : ∀ x, ((∫ y, commutatorKernel d s v x y ∂(thermalMeasure d s a β)) -
      ∫ y, commutatorKernel d s v x y ∂ν) =
      -∫ y, commutatorKernel d s v x y * (φN y - 1) ∂(withDensityReal (thermalDensity d s a β)) := by
    intro x
    obtain ⟨hi, -⟩ := HRS.MS.S53.s53_ker_row hs0 hv hrow x
    have hint2 : Integrable (fun y => φN y * commutatorKernel d s v x y)
        (withDensityReal (thermalDensity d s a β)) := by
      have hCs0 : 0 ≤ Cs := (hφb 0).1.trans (hφb 0).2
      refine hi.bdd_mul (c := Cs) (hφm.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hφb y).1]; exact (hφb y).2
    rw [hν, integral_withDensity_eq_integral_toReal_smul hφm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hφb _).1]
    have e : ∀ y, commutatorKernel d s v x y * (φN y - 1) =
        φN y * commutatorKernel d s v x y - commutatorKernel d s v x y := fun y => by ring
    simp_rw [e]
    rw [integral_sub hint2 hi]
    have hμ : thermalMeasure d s a β = withDensityReal (thermalDensity d s a β) := rfl
    rw [hμ]
    ring
  simp_rw [hrowrep, neg_sq]
  refine hS.trans ?_
  have hint : ∫ y, (φN y - 1) ^ 2 ∂(withDensityReal (thermalDensity d s a β)) ≤ r ^ 2 := by
    have : l2Norm (thermalMeasure d s a β) (fun x => φN x - 1) =
        Real.sqrt (∫ y, (φN y - 1) ^ 2 ∂(withDensityReal (thermalDensity d s a β))) := rfl
    rw [this] at hr
    have h0 : 0 ≤ ∫ y, (φN y - 1) ^ 2 ∂(withDensityReal (thermalDensity d s a β)) :=
      integral_nonneg fun _ => sq_nonneg _
    calc _ = Real.sqrt (∫ y, (φN y - 1) ^ 2 ∂(withDensityReal (thermalDensity d s a β))) ^ 2 :=
          (Real.sq_sqrt h0).symm
      _ ≤ r ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hr 2
  calc (CW * ((s + 1) * (Λ : ℝ))) ^ 2 * ∫ y, (φN y - 1) ^ 2 ∂(withDensityReal (thermalDensity d s a β))
      ≤ (CW * ((s + 1) * (Λ : ℝ))) ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by ring


theorem s46_R_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (C Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a β γ c BU : ℝ}, ThermalData d s a β C c BU →
      (∀ N : ℕ, 2 ≤ N → S46Static d s a β γ Cs N) →
      ∀ (N : ℕ), 2 ≤ N → ∀ {χ : Euc d → ℝ}, ContDiff ℝ 2 χ → ∀ {B2 : ℝ},
      (∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) →
      Real.sqrt N * ∫ X, |s45_Rp (thermalMeasure d s a β) (s46_nu d s a β γ N) (s46_P d s a β γ N)
          (commutatorKernel d s (gradient χ)) X| ∂(s46_P d s a β γ N) ≤
        K * B2 * Real.sqrt (HRS.deltaN d s N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨CW, hCW0, hCW⟩ := s46_Hd_L2 hd hs0 hsd C
  refine ⟨Real.sqrt Cs * (CW * (s + 1) * Cs + 1), by positivity,
    fun {a β γ c BU} hT hS N hN {χ} hχ {B2} hB2 => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hSN := hS N hN
  set P := s46_P d s a β γ N with hPdef
  set μ := thermalMeasure d s a β with hμdef
  set v := gradient χ with hvdef
  set h := commutatorKernel d s v with hhdef
  haveI hP : IsProbabilityMeasure P := hSN.prob
  set ν := firstMarginal P with hνdef
  haveI hνprob : IsProbabilityMeasure ν := by
    have : ν = P.map (fun X : EucConfig d N => X ⟨0, by omega⟩) := by
      rw [hνdef]; unfold firstMarginal; rw [dif_pos (by omega)]
    rw [this]
    constructor
    rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
    simp
  haveI hμprob : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hv1 : ContDiff ℝ 1 v := s45_contDiff_gradient hχ
  have hvd : Differentiable ℝ v := hv1.differentiable (by norm_num)
  set Λ : ℝ≥0 := ⟨B2, hB20⟩ with hΛdef
  have hLip : LipschitzWith Λ v := lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
    have := hB2 x
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact this)
  have hhm : Measurable (Function.uncurry h) :=
    HRS.MS.Comm.comm_meas (s := s) v hv1.continuous.measurable
  obtain ⟨φN, hφNm, hνeq, hφNb, hφN2, hφNn⟩ := hSN.marg
  obtain ⟨Bh, hBh0, hBh⟩ := s45_Hbounds hd hs0 hsd hT hLip hφNb hφNm ν hνeq
  have hδ0 : 0 ≤ HRS.deltaN d s N := HRS.deltaN_nonneg s hN1
  have hδ1 : HRS.deltaN d s N ≤ 1 := HRS.WeakRef.deltaN_le_one hd1 hs0 hsd hN1
  set δ := HRS.deltaN d s N with hδ
  have hCsδ : 0 ≤ Cs * δ := mul_nonneg hCs hδ0
  have hHd_meas : Measurable fun x => (∫ y, h x y ∂μ) - ∫ y, h x y ∂ν :=
    ((hhm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable).sub
      (hhm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hHd_bd : ∀ x, |(∫ y, h x y ∂μ) - ∫ y, h x y ∂ν| ≤ 2 * Bh := fun x => by
    obtain ⟨h1, h2⟩ := hBh x
    calc _ ≤ |∫ y, h x y ∂μ| + |∫ y, h x y ∂ν| := abs_sub _ _
      _ ≤ 2 * Bh := by linarith
  have hHd2 : MemLp (fun x => (∫ y, h x y ∂μ) - ∫ y, h x y ∂ν) 2 μ :=
    MemLp.of_bound hHd_meas.aestronglyMeasurable (2 * Bh)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hHd_bd x)
  -- `L²` bound of the row difference
  have hL2 := hCW hT hLip hφNb hφNm hφN2 ν hνeq (Cs * δ) hφNn hCsδ
  -- variance of the linear statistic
  have hvar1 : variance (fun X : EucConfig d N => pair (empirical X) (fun x => (∫ y, h x y ∂μ) -
      ∫ y, h x y ∂ν)) P ≤ Cs / N * ((CW * ((s + 1) * (Λ : ℝ)) * (Cs * δ)) ^ 2) := by
    have hl := hSN.linear _ hHd2
    have hb : 0 ≤ Cs / N * ∫ x, ((∫ y, h x y ∂μ) - ∫ y, h x y ∂ν) ^ 2 ∂μ :=
      mul_nonneg (div_nonneg hCs hN0.le) (integral_nonneg fun _ => sq_nonneg _)
    have : variance (fun X : EucConfig d N => pair (empirical X) (fun x => (∫ y, h x y ∂μ) -
        ∫ y, h x y ∂ν)) P ≤ Cs / N * ∫ x, ((∫ y, h x y ∂μ) - ∫ y, h x y ∂ν) ^ 2 ∂μ := by
      unfold variance
      refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hl).trans ?_
      rw [ENNReal.toReal_ofReal hb]
    exact this.trans (mul_le_mul_of_nonneg_left hL2 (div_nonneg hCs hN0.le))
  -- the pair functional
  set D : EucConfig d N → ℝ := fun X => centeredPairFunctional h X ν with hD
  have hDm : Measurable D := HRS.MS.Wr.wr14a_measurable_D hhm ν
  obtain ⟨-, hq⟩ := hSN.comm Λ v hLip
  have hDL2 : MemLp D 2 P := by
    have hlt : evariance D P < ⊤ := lt_of_le_of_lt hq.2.2 ENNReal.ofReal_lt_top
    exact (evariance_lt_top_iff_memLp hDm.aestronglyMeasurable).1 hlt
  have hbq : 0 ≤ Cs * (Λ : ℝ) ^ 2 * δ / N := by positivity
  have hvar2 : variance D P ≤ Cs / N * ((Λ : ℝ) * Real.sqrt δ) ^ 2 := by
    unfold variance
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hq.2.2).trans ?_
    rw [ENNReal.toReal_ofReal hbq, mul_pow, Real.sq_sqrt hδ0]
    apply le_of_eq; field_simp
  have hDi : Integrable D P := hDL2.integrable one_le_two
  -- the linear statistic
  set Hd : Euc d → ℝ := fun x => (∫ y, h x y ∂μ) - ∫ y, h x y ∂ν with hHd
  have hYL2 : MemLp (fun X : EucConfig d N => pair (empirical X) Hd) 2 P :=
    MemLp.of_bound (s45_measurable_pair_empirical hN1 hHd_meas).aestronglyMeasurable (2 * Bh)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact s45_abs_pair_empirical_le hN1 hHd_bd X)
  have hYmean : ∫ X, pair (empirical X) Hd ∂P = pair ν Hd :=
    s45_E_pair_empirical hN1 hSN.exch hHd_meas hHd_bd
  have hYi : Integrable (fun X : EucConfig d N => pair (empirical X) Hd) P := hYL2.integrable one_le_two
  -- the two `L¹` bounds
  have e1 := s45_l1_le_sqrt hYL2
  rw [hYmean] at e1
  have e2 := s45_l1_le_sqrt hDL2
  have hx : 0 ≤ CW * ((s + 1) * (Λ : ℝ)) * (Cs * δ) := by positivity
  have hx' : 0 ≤ (Λ : ℝ) * Real.sqrt δ := by positivity
  have f1 : Real.sqrt N * ∫ X, |pair (empirical X) Hd - pair ν Hd| ∂P ≤
      Real.sqrt Cs * (CW * ((s + 1) * (Λ : ℝ)) * (Cs * δ)) := by
    rw [← s45_sqrt_aux hN0 hCs hx]
    exact mul_le_mul_of_nonneg_left (e1.trans (Real.sqrt_le_sqrt hvar1)) (Real.sqrt_nonneg _)
  have f2 : Real.sqrt N * ∫ X, |D X - ∫ X', D X' ∂P| ∂P ≤ Real.sqrt Cs * ((Λ : ℝ) * Real.sqrt δ) := by
    rw [← s45_sqrt_aux hN0 hCs hx']
    exact mul_le_mul_of_nonneg_left (e2.trans (Real.sqrt_le_sqrt hvar2)) (Real.sqrt_nonneg _)
  -- combine
  have hRbi : Integrable (fun X : EucConfig d N => |pair (empirical X) Hd - pair ν Hd|) P :=
    (hYi.sub (integrable_const _)).abs
  have hDci : Integrable (fun X : EucConfig d N => |D X - ∫ X', D X' ∂P|) P :=
    (hDi.sub (integrable_const _)).abs
  have hcomb : ∫ X, |s45_Rp μ ν P h X| ∂P ≤ ∫ X, (|pair (empirical X) Hd - pair ν Hd| +
      (1 / 2) * |D X - ∫ X', D X' ∂P|) ∂P := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => abs_nonneg _)
      (hRbi.add (hDci.const_mul _)) (Filter.Eventually.of_forall fun X => ?_)
    unfold s45_Rp
    calc _ ≤ |pair (empirical X) Hd - pair ν Hd| + |(1 / 2) * (D X - ∫ X', D X' ∂P)| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [integral_add hRbi (hDci.const_mul _), integral_const_mul] at hcomb
  have hsq : δ ≤ Real.sqrt δ := by
    calc δ = Real.sqrt δ ^ 2 := (Real.sq_sqrt hδ0).symm
      _ ≤ Real.sqrt δ * 1 := by
          rw [sq]; exact mul_le_mul_of_nonneg_left (Real.sqrt_le_one.2 hδ1) (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have hΛ0 : (0 : ℝ) ≤ Λ := NNReal.coe_nonneg Λ
  have hΛe : (Λ : ℝ) = B2 := rfl
  calc Real.sqrt N * ∫ X, |s45_Rp μ ν P h X| ∂P
      ≤ Real.sqrt N * (∫ X, |pair (empirical X) Hd - pair ν Hd| ∂P +
        (1 / 2) * ∫ X, |D X - ∫ X', D X' ∂P| ∂P) :=
        mul_le_mul_of_nonneg_left hcomb (Real.sqrt_nonneg _)
    _ = Real.sqrt N * ∫ X, |pair (empirical X) Hd - pair ν Hd| ∂P +
        (1 / 2) * (Real.sqrt N * ∫ X, |D X - ∫ X', D X' ∂P| ∂P) := by ring
    _ ≤ Real.sqrt Cs * (CW * ((s + 1) * (Λ : ℝ)) * (Cs * δ)) +
        (1 / 2) * (Real.sqrt Cs * ((Λ : ℝ) * Real.sqrt δ)) := add_le_add f1 (by gcongr)
    _ ≤ Real.sqrt Cs * (CW * (s + 1) * Cs + 1) * B2 * Real.sqrt δ := by
        rw [hΛe]
        have hs1 : 0 ≤ s + 1 := by linarith
        have h1 : CW * ((s + 1) * B2) * (Cs * δ) ≤ CW * (s + 1) * Cs * B2 * Real.sqrt δ := by
          have : CW * ((s + 1) * B2) * (Cs * δ) = (CW * (s + 1) * Cs * B2) * δ := by ring
          rw [this]; exact mul_le_mul_of_nonneg_left hsq (by positivity)
        have h2 : 0 ≤ Real.sqrt Cs * (B2 * Real.sqrt δ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg Cs)]


/-- `E|μ_N(f) - μ(f)| ≤ K B_f √δ_N` for bounded measurable `f`. -/
theorem s46_T_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a β γ C c BU : ℝ}, ThermalData d s a β C c BU →
      (∀ N : ℕ, 2 ≤ N → S46Static d s a β γ Cs N) →
      ∀ (N : ℕ), 2 ≤ N → ∀ {f : Euc d → ℝ}, Measurable f → ∀ {Bf : ℝ},
      (∀ x, |f x| ≤ Bf) →
      ∫ X, |pair (empirical X) f - pair (thermalMeasure d s a β) f| ∂(s46_P d s a β γ N) ≤
        K * Bf * Real.sqrt (HRS.deltaN d s N) := by
  have hd1 : 1 ≤ d := by omega
  refine ⟨Real.sqrt Cs + Cs, by positivity, fun {a β γ C c BU} hT hS N hN {f} hf {Bf} hBf => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0)
  have hSN := hS N hN
  set P := s46_P d s a β γ N with hPdef
  set μ := thermalMeasure d s a β with hμdef
  haveI hP : IsProbabilityMeasure P := hSN.prob
  haveI hμprob : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  set ν := firstMarginal P with hνdef
  obtain ⟨φN, hφNm, hνeq, hφNb, hφN2, hφNn⟩ := hSN.marg
  have hδ0 : 0 ≤ HRS.deltaN d s N := HRS.deltaN_nonneg s hN1
  have hδ1 : HRS.deltaN d s N ≤ 1 := HRS.WeakRef.deltaN_le_one hd1 hs0 hsd hN1
  have hδN : (N : ℝ)⁻¹ ≤ HRS.deltaN d s N := HRS.WeakRef.inv_le_deltaN hd1 hs0 hsd hN1
  set δ := HRS.deltaN d s N with hδ
  have hsq : δ ≤ Real.sqrt δ := by
    calc δ = Real.sqrt δ ^ 2 := (Real.sq_sqrt hδ0).symm
      _ ≤ Real.sqrt δ * 1 := by
          rw [sq]; exact mul_le_mul_of_nonneg_left (Real.sqrt_le_one.2 hδ1) (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have hf2 : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable Bf
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBf x)
  -- (a) fluctuations of `μ_N(f)` around `ν(f)`
  have hYL2 : MemLp (fun X : EucConfig d N => pair (empirical X) f) 2 P :=
    MemLp.of_bound (s45_measurable_pair_empirical hN1 hf).aestronglyMeasurable Bf
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact s45_abs_pair_empirical_le hN1 hBf X)
  have hYmean : ∫ X, pair (empirical X) f ∂P = pair ν f := s45_E_pair_empirical hN1 hSN.exch hf hBf
  have e1 := s45_l1_le_sqrt hYL2
  rw [hYmean] at e1
  have hvar : variance (fun X : EucConfig d N => pair (empirical X) f) P ≤ Cs / N * Bf ^ 2 := by
    have hl := hSN.linear f hf2
    have hI : ∫ x, f x ^ 2 ∂μ ≤ Bf ^ 2 := by
      calc ∫ x, f x ^ 2 ∂μ ≤ ∫ _x, Bf ^ 2 ∂μ := by
            refine integral_mono hf2.integrable_sq (integrable_const _) fun x => ?_
            have := hBf x
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = Bf ^ 2 := by simp
    have hb : 0 ≤ Cs / N * ∫ x, f x ^ 2 ∂μ := mul_nonneg (div_nonneg hCs hN0.le)
      (integral_nonneg fun _ => sq_nonneg _)
    unfold variance
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hl).trans ?_
    rw [ENNReal.toReal_ofReal hb]
    exact mul_le_mul_of_nonneg_left hI (div_nonneg hCs hN0.le)
  have hA : ∫ X, |pair (empirical X) f - pair ν f| ∂P ≤ Real.sqrt Cs * Bf * Real.sqrt δ := by
    have h1 := e1.trans (Real.sqrt_le_sqrt hvar)
    refine h1.trans ?_
    have : Cs / N * Bf ^ 2 = Cs * (N : ℝ)⁻¹ * Bf ^ 2 := by ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_mul hCs, Real.sqrt_sq hBf0]
    have hinv : Real.sqrt (N : ℝ)⁻¹ ≤ Real.sqrt δ := Real.sqrt_le_sqrt hδN
    calc Real.sqrt Cs * Real.sqrt (N : ℝ)⁻¹ * Bf ≤ Real.sqrt Cs * Real.sqrt δ * Bf := by gcongr
      _ = _ := by ring
  -- (b) bias `ν(f) - μ(f)`
  have hbias : |pair ν f - pair μ f| ≤ Bf * (Cs * δ) := by
    have hνf : pair ν f = ∫ x, φN x * f x ∂μ := by
      have hνeq' : ν = μ.withDensity (fun x => ENNReal.ofReal (φN x)) := hνeq
      unfold pair
      rw [hνeq', integral_withDensity_eq_integral_toReal_smul hφNm.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (hφNb _).1]
    have hφf : Integrable (fun x => φN x * f x) μ :=
      Integrable.of_bound ((hφNm.mul hf).aestronglyMeasurable) (Cs * Bf)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφNb x).1]
          exact mul_le_mul (hφNb x).2 (hBf x) (abs_nonneg _) hCs)
    have hfi : Integrable f μ := hf2.integrable one_le_two
    have hd0 : pair ν f - pair μ f = ∫ x, (φN x - 1) * f x ∂μ := by
      rw [hνf]; unfold pair
      rw [← integral_sub hφf hfi]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hd0]
    have hg1 : Integrable (fun x => |φN x - 1|) μ := (hφN2.integrable one_le_two).abs
    calc |∫ x, (φN x - 1) * f x ∂μ| ≤ ∫ x, |(φN x - 1) * f x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, Bf * |φN x - 1| ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) (hg1.const_mul _)
            (Filter.Eventually.of_forall fun x => by
              show |(φN x - 1) * f x| ≤ Bf * |φN x - 1|
              rw [abs_mul]; nlinarith [abs_nonneg (φN x - 1), hBf x])
      _ = Bf * ∫ x, |φN x - 1| ∂μ := integral_const_mul _ _
      _ ≤ Bf * (Cs * δ) := mul_le_mul_of_nonneg_left ((s45_l1_le_l2 hφN2).trans hφNn) hBf0
  -- combine
  have hYi : Integrable (fun X : EucConfig d N => pair (empirical X) f) P := hYL2.integrable one_le_two
  have hRbi : Integrable (fun X : EucConfig d N => |pair (empirical X) f - pair ν f|) P :=
    (hYi.sub (integrable_const _)).abs
  calc ∫ X, |pair (empirical X) f - pair μ f| ∂P
      ≤ ∫ X, (|pair (empirical X) f - pair ν f| + |pair ν f - pair μ f|) ∂P :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => abs_nonneg _)
          (hRbi.add (integrable_const _)) (Filter.Eventually.of_forall fun X => by
            calc |pair (empirical X) f - pair μ f|
                = |(pair (empirical X) f - pair ν f) + (pair ν f - pair μ f)| := by ring_nf
              _ ≤ _ := abs_add_le _ _)
    _ = ∫ X, |pair (empirical X) f - pair ν f| ∂P + |pair ν f - pair μ f| := by
        rw [integral_add hRbi (integrable_const _), integral_const]; simp
    _ ≤ Real.sqrt Cs * Bf * Real.sqrt δ + Bf * (Cs * δ) := add_le_add hA hbias
    _ ≤ (Real.sqrt Cs + Cs) * Bf * Real.sqrt δ := by
        have : Bf * (Cs * δ) ≤ Cs * Bf * Real.sqrt δ := by
          have := mul_le_mul_of_nonneg_left hsq (mul_nonneg hBf0 hCs)
          nlinarith
        nlinarith


end S46

end
