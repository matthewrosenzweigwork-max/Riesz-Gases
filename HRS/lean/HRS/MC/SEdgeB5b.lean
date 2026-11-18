import HRS.MC.SEdgeB5a

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B5b

open HRS.Sec7

section Aux
variable {d : ℕ} {N : ℕ}

theorem b5b_pair_meas (hN : 1 ≤ N) {f : Torus d → ℝ} (hf : Measurable f) :
    Measurable (fun X : Config d N => pair (empirical X) f) := by
  have : (fun X : Config d N => pair (empirical X) f) = fun X => (N : ℝ)⁻¹ * ∑ i, f (X i) :=
    funext fun X => pair_empirical (by omega) X f
  rw [this]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i))

theorem b5b_pair_bdd (hN : 1 ≤ N) {f : Torus d → ℝ} {M : ℝ} (hf : ∀ x, |f x| ≤ M)
    (X : Config d N) : |pair (empirical X) f| ≤ M := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [pair_empirical (by omega) X f, abs_mul, abs_of_pos (inv_pos.2 hNp)]
  have h1 : |∑ i, f (X i)| ≤ N * M := by
    calc |∑ i, f (X i)| ≤ ∑ i, |f (X i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, M := Finset.sum_le_sum fun i _ => hf _
      _ = N * M := by simp
  calc (N : ℝ)⁻¹ * |∑ i, f (X i)| ≤ (N : ℝ)⁻¹ * (N * M) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hNp.le)
    _ = M := by field_simp

theorem b5b_line (hN : 1 ≤ N) {p : ℕ} {φ : Fin p → Torus d → ℝ} (hφ : ∀ a, Torus.IsSmooth (φ a))
    {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψd : Differentiable ℝ ψ)
    (Q : Measure (Config d N)) (i : Fin N) (k : Fin d) (Y : Config d N) :
    HasDerivAt (fun τ : ℝ => ψ (centeredStat Q φ (Q84d.lineCfg i k Y τ)))
      (∑ c, (Real.sqrt N)⁻¹ * Torus.partialDeriv k (φ c) (Y i) *
        fderiv ℝ ψ (centeredStat Q φ Y) (stdVec c)) 0 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  -- derivative of the sum of a test along the line
  have hS : ∀ a, HasDerivAt (fun τ : ℝ => ∑ j, φ a ((Q84d.lineCfg i k Y τ) j))
      (Torus.partialDeriv k (φ a) (Y i)) 0 := by
    intro a
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin N)), HasDerivAt
        (fun τ : ℝ => φ a ((Q84d.lineCfg i k Y τ) j))
        (if j = i then Torus.partialDeriv k (φ a) (Y i) else 0) 0 := by
      intro j _
      by_cases hji : j = i
      · subst hji
        have := HRS.Q66.q66_scalar_line_deriv (HRS.Q66.q66_isCk_of_smooth (hφ a) 1) (Y j) k
        simpa [Q84d.lineCfg] using this
      · simp only [hji, if_false]
        have : (fun τ : ℝ => φ a ((Q84d.lineCfg i k Y τ) j)) = fun _ => φ a (Y j) := by
          funext τ; simp [Q84d.lineCfg, Function.update_of_ne hji]
        rw [this]
        exact hasDerivAt_const _ _
    have := HasDerivAt.fun_sum hj
    simpa using this
  have hF : ∀ a, HasDerivAt (fun τ : ℝ => Real.sqrt N *
      (pair (empirical (Q84d.lineCfg i k Y τ)) (φ a) - ∫ Z, pair (empirical Z) (φ a) ∂Q))
      (Real.sqrt N * ((N : ℝ)⁻¹ * Torus.partialDeriv k (φ a) (Y i))) 0 := by
    intro a
    have e : (fun τ : ℝ => Real.sqrt N *
        (pair (empirical (Q84d.lineCfg i k Y τ)) (φ a) - ∫ Z, pair (empirical Z) (φ a) ∂Q)) =
        fun τ => Real.sqrt N * ((N : ℝ)⁻¹ * ∑ j, φ a ((Q84d.lineCfg i k Y τ) j) -
          ∫ Z, pair (empirical Z) (φ a) ∂Q) := by
      funext τ
      rw [pair_empirical (by omega)]
    rw [e]
    exact (((hS a).const_mul (N : ℝ)⁻¹).sub_const _).const_mul _
  have hW : HasDerivAt (fun τ : ℝ => centeredStat Q φ (Q84d.lineCfg i k Y τ))
      (WithLp.toLp 2 fun a => Real.sqrt N * ((N : ℝ)⁻¹ * Torus.partialDeriv k (φ a) (Y i))) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => fun a : Fin p => Real.sqrt N *
        (pair (empirical (Q84d.lineCfg i k Y τ)) (φ a) - ∫ Z, pair (empirical Z) (φ a) ∂Q))
        (fun a => Real.sqrt N * ((N : ℝ)⁻¹ * Torus.partialDeriv k (φ a) (Y i))) 0 :=
      hasDerivAt_pi.2 hF
    have h2 := ((EuclideanSpace.equiv (Fin p) ℝ).symm.hasFDerivAt).comp_hasDerivAt (0 : ℝ) h1
    exact h2
  have h3 : HasDerivAt (fun τ : ℝ => ψ (centeredStat Q φ (Q84d.lineCfg i k Y τ)))
      (fderiv ℝ ψ (centeredStat Q φ Y)
        (WithLp.toLp 2 fun a => Real.sqrt N * ((N : ℝ)⁻¹ * Torus.partialDeriv k (φ a) (Y i)))) 0 := by
    have hpt : centeredStat Q φ (Q84d.lineCfg i k Y 0) = centeredStat Q φ Y := by
      simp [Q84d.lineCfg_zero]
    have := (hψd (centeredStat Q φ (Q84d.lineCfg i k Y 0))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hW
    rw [hpt] at this
    exact this
  convert h3 using 1
  have hvec : (WithLp.toLp 2 fun a => Real.sqrt N * ((N : ℝ)⁻¹ * Torus.partialDeriv k (φ a) (Y i)) :
      EuclideanSpace ℝ (Fin p)) = ∑ c, (Real.sqrt N * ((N : ℝ)⁻¹ * Torus.partialDeriv k (φ c) (Y i))) • stdVec c := by
    ext a
    simp [stdVec, Pi.single_apply, Finset.sum_apply]
  rw [hvec, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, smul_eq_mul]
  have : Real.sqrt N * (N : ℝ)⁻¹ = (Real.sqrt N)⁻¹ := by
    have hsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hNp.le).symm
    field_simp
    nlinarith [hsq]
  rw [← this]
  ring

end Aux

section Moments

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

theorem sed_B5b_stein_centred_proof {N : ℕ} (hN : 1 ≤ N) {w r : Torus d → ℝ} (hr : Torus.IsSmooth r)
    {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * r x))
    (hresp : ∀ x, r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x =
      projMean (withDensityReal ρ) w x)
    (hint : Integrable
      (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))
      (sed_Q d s N β ρ))
    {p : ℕ} {φ : Fin p → Torus d → ℝ} (hφ : ∀ a, Torus.IsSmooth (φ a))
    {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 1 ψ) :
    ∫ X, sed_Y (sed_Q d s N β ρ) w X * ψ (centeredStat (sed_Q d s N β ρ) φ X) ∂(sed_Q d s N β ρ) =
      ∑ c, ∫ X, sed_A v (φ c) X * fderiv ℝ ψ (centeredStat (sed_Q d s N β ρ) φ X) (stdVec c)
          ∂(sed_Q d s N β ρ) -
        β / Real.sqrt N * ∫ X, sed_B d s ρ β v X * ψ (centeredStat (sed_Q d s N β ρ) φ X)
          ∂(sed_Q d s N β ρ) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  haveI hQ : IsProbabilityMeasure (sed_Q d s N β ρ) := B5a.b5a_Q_prob hd hs0 hs hβ hρ hN
  obtain ⟨hwm, Mw, hwb⟩ := B5a.b5a_w_facts hd hs0 hs hρ hr hresp
  have hφc : ∀ a, Continuous (φ a) := fun a => HRS.Q66.q66_cont_of_smooth (hφ a)
  choose Mφ hMφ using fun a => HRS.Q66.q66_bound_of_smooth (hφ a)
  have hvc : ∀ k, Continuous (v k) := fun k => HRS.Q66.q66_cont_of_smooth (hv k)
  -- the statistic
  have hWm : Measurable (centeredStat (sed_Q d s N β ρ) φ) := by
    unfold centeredStat
    exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a =>
      measurable_const.mul ((b5b_pair_meas hN (hφc a).measurable).sub measurable_const))
  obtain ⟨M0, hM0⟩ := hψ.2 0 (Nat.zero_le _)
  obtain ⟨M1, hM1⟩ := hψ.2 1 le_rfl
  have hψb : ∀ z, |ψ z| ≤ M0 := fun z => by
    have := hM0 ⟨z, rfl⟩
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hdψb : ∀ z, ‖fderiv ℝ ψ z‖ ≤ M1 := fun z => by
    have := hM1 ⟨z, rfl⟩
    simpa using this
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hdψc : Continuous (fderiv ℝ ψ) := hψ.1.continuous_fderiv (by simp)
  have hDm : ∀ c, Measurable (fun X : Config d N =>
      fderiv ℝ ψ (centeredStat (sed_Q d s N β ρ) φ X) (stdVec c)) := fun c =>
    ((ContinuousLinearMap.apply ℝ ℝ (stdVec c)).continuous.measurable).comp
      (hdψc.measurable.comp hWm)
  have hDb : ∀ c X, |fderiv ℝ ψ (centeredStat (sed_Q d s N β ρ) φ X) (stdVec c)| ≤ M1 := by
    intro c X
    have h1 := (fderiv ℝ ψ (centeredStat (sed_Q d s N β ρ) φ X)).le_opNorm (stdVec c)
    have h2 : ‖stdVec (p := p) c‖ = 1 := by simp [stdVec]
    rw [h2, mul_one] at h1
    rw [← Real.norm_eq_abs]
    exact h1.trans (hdψb _)
  -- partial derivatives of the tests
  have hpdS : ∀ c k, Torus.IsSmooth (Torus.partialDeriv k (φ c)) := fun c k =>
    HRS.Q66.q66_isSmooth_partialDeriv (hφ c) k
  choose Mp hMp using fun c k => HRS.Q66.q66_bound_of_smooth (hpdS c k)
  set Q := sed_Q d s N β ρ with hQdef
  have hΨm : Measurable (fun X : Config d N => ψ (centeredStat Q φ X)) :=
    hψ.1.continuous.measurable.comp hWm
  have hpdc : ∀ c k, Continuous (Torus.partialDeriv k (φ c)) := fun c k =>
    HRS.Q66.q66_cont_of_smooth (hpdS c k)
  have hdΨm : ∀ (i : Fin N) (k : Fin d), Measurable (fun X : Config d N =>
      ∑ c, (Real.sqrt N)⁻¹ * Torus.partialDeriv k (φ c) (X i) *
        fderiv ℝ ψ (centeredStat Q φ X) (stdVec c)) := fun i k =>
    Finset.measurable_sum _ fun c _ =>
      (measurable_const.mul ((hpdc c k).measurable.comp (measurable_pi_apply i))).mul (hDm c)
  have hM1nn : 0 ≤ M1 := (norm_nonneg _).trans (hdψb 0)
  have hdΨb : ∃ M, ∀ (i : Fin N) (k : Fin d) (X : Config d N), |∑ c, (Real.sqrt N)⁻¹ *
      Torus.partialDeriv k (φ c) (X i) * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c)| ≤ M := by
    refine ⟨∑ c, ∑ k', (Real.sqrt N)⁻¹ * |Mp c k'| * M1, fun i k X => ?_⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    have hterm : ∀ k', 0 ≤ (Real.sqrt N)⁻¹ * |Mp c k'| * M1 := fun k' => by positivity
    refine le_trans ?_ (Finset.single_le_sum (f := fun k' => (Real.sqrt N)⁻¹ * |Mp c k'| * M1)
      (fun k' _ => hterm k') (Finset.mem_univ k))
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hsN)]
    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hsN.le)) (hDb c X)
      (abs_nonneg _) (by positivity)
    exact (hMp c k (X i)).trans (le_abs_self _)
  have h1 := B5a.sed_B5a_stein_raw_proof hd hs0 hs hβ hρ hN hr hv hdiv hresp hint
    (Ψ := fun X : Config d N => ψ (centeredStat Q φ X))
    (dΨ := fun (i : Fin N) (k : Fin d) (X : Config d N) => ∑ c, (Real.sqrt N)⁻¹ *
      Torus.partialDeriv k (φ c) (X i) * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c))
    hΨm ⟨M0, fun X => hψb _⟩ hdΨm hdΨb (fun i k Y _ => b5b_line hN hφ hψd Q i k Y)
  have h2 := B5a.sed_B5a_stein_raw_proof hd hs0 hs hβ hρ hN hr hv hdiv hresp hint
    (Ψ := fun _ : Config d N => (1 : ℝ))
    (dΨ := fun (_ : Fin N) (_ : Fin d) (_ : Config d N) => (0 : ℝ))
    measurable_const ⟨1, fun _ => by simp⟩ (fun _ _ => measurable_const) ⟨0, fun _ _ _ => by simp⟩
    (fun i k Y _ => by simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ))
  -- the pieces of the left-hand sides
  set u : ℝ := pair (withDensityReal ρ) w with hu
  set a0 : ℝ := ∫ X, pair (empirical X) w ∂Q with ha0
  set e0 : ℝ := ∫ X, modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) ∂Q with he0
  have hPm := b5b_pair_meas hN hwm
  have hPi : Integrable (fun X : Config d N => pair (empirical X) w) Q :=
    Integrable.of_bound hPm.aestronglyMeasurable Mw
      (Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using b5b_pair_bdd hN hwb X)
  have hK : (N : ℝ) * (a0 - u) + β * ((N : ℝ) * e0) = 0 := by
    have h2' : ∫ X, (1 : ℝ) * ((N : ℝ) * (pair (empirical X) w - u) +
        β * ((N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))) ∂Q = 0 := by
      simpa using h2
    simp_rw [one_mul] at h2'
    have hI1 : Integrable (fun X : Config d N => (N : ℝ) * (pair (empirical X) w - u)) Q :=
      (hPi.sub (integrable_const u)).const_mul _
    have hI2 : Integrable (fun X : Config d N => β * ((N : ℝ) *
        modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))) Q :=
      (hint.const_mul _).const_mul _
    rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sub hPi (integrable_const u)] at h2'
    simpa [ha0, he0] using h2'
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hwb 0)
  have hM00 : 0 ≤ M0 := (abs_nonneg _).trans (hψb 0)
  -- Y and B
  have hYm : Measurable (fun X : Config d N => sed_Y Q w X) := by
    unfold sed_Y
    exact measurable_const.mul (hPm.sub measurable_const)
  have hYΨi : Integrable (fun X : Config d N => sed_Y Q w X * ψ (centeredStat Q φ X)) Q := by
    refine Integrable.of_bound (hYm.mul hΨm).aestronglyMeasurable
      (Real.sqrt N * (Mw + |a0|) * M0) (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ?_ (hψb _) (abs_nonneg _)
      (mul_nonneg hsN.le (add_nonneg hMw0 (abs_nonneg a0)))
    unfold sed_Y
    rw [abs_mul, abs_of_pos hsN]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
      (add_le_add (b5b_pair_bdd hN hwb X) le_rfl)) hsN.le
  have hBΨi : Integrable (fun X : Config d N => sed_B d s ρ β v X * ψ (centeredStat Q φ X)) Q := by
    have : Integrable (fun X : Config d N => sed_B d s ρ β v X) Q :=
      (hint.sub (integrable_const e0)).const_mul (N : ℝ)
    exact this.mul_bdd hΨm.aestronglyMeasurable (c := M0)
      (Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hψb _)
  -- the main identity, left side
  have hL : ∫ X, ψ (centeredStat Q φ X) * ((N : ℝ) * (pair (empirical X) w - u) +
        β * ((N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))) ∂Q =
      Real.sqrt N * ∫ X, sed_Y Q w X * ψ (centeredStat Q φ X) ∂Q +
        β * ∫ X, sed_B d s ρ β v X * ψ (centeredStat Q φ X) ∂Q := by
    have hpt : ∀ X : Config d N, ψ (centeredStat Q φ X) * ((N : ℝ) * (pair (empirical X) w - u) +
        β * ((N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))) =
        Real.sqrt N * (sed_Y Q w X * ψ (centeredStat Q φ X)) +
          β * (sed_B d s ρ β v X * ψ (centeredStat Q φ X)) +
          ((N : ℝ) * (a0 - u) + β * ((N : ℝ) * e0)) * ψ (centeredStat Q φ X) := by
      intro X
      have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNp.le
      have hYdef : sed_Y Q w X = Real.sqrt N * (pair (empirical X) w - a0) := rfl
      have hBdef : sed_B d s ρ β v X = (N : ℝ) * (modulatedEnergy (Q66.q66_hv d s v) X
          (withDensityReal ρ) - e0) := rfl
      rw [hYdef, hBdef]
      linear_combination (-(ψ (centeredStat Q φ X) * (pair (empirical X) w - a0))) * hsq
    simp_rw [hpt, hK, zero_mul, add_zero]
    rw [integral_add (hYΨi.const_mul _) (hBΨi.const_mul _), integral_const_mul, integral_const_mul]
  -- right side
  have hdriftc : ∀ c, Continuous (sed_drift v (φ c)) := fun c => by
    unfold sed_drift
    exact continuous_finset_sum _ fun k _ => (hvc k).mul (hpdc c k)
  have hAm : ∀ c, Measurable (fun X : Config d N => sed_A v (φ c) X) := fun c =>
    b5b_pair_meas hN (hdriftc c).measurable
  have hdbd : ∀ c, ∃ M : ℝ, ∀ x, |sed_drift v (φ c) x| ≤ M := fun c => by
    obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn
      (hdriftc c).continuousOn
    exact ⟨M, fun x => by simpa using hM x (Set.mem_univ _)⟩
  choose Md hMd using hdbd
  have hADi : ∀ c, Integrable (fun X : Config d N => sed_A v (φ c) X *
      fderiv ℝ ψ (centeredStat Q φ X) (stdVec c)) Q := fun c => by
    refine Integrable.of_bound ((hAm c).mul (hDm c)).aestronglyMeasurable (Md c * M1)
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (b5b_pair_bdd hN (hMd c) X) (hDb c X) (abs_nonneg _)
      ((abs_nonneg _).trans (hMd c 0))
  have swap3 : ∀ f : Fin N → Fin d → Fin p → ℝ,
      ∑ i, ∑ k, ∑ c, f i k c = ∑ c, ∑ i, ∑ k, f i k c := fun f =>
    calc _ = ∑ i, ∑ c, ∑ k, f i k c := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hpt2 : ∀ X : Config d N, ∑ i, ∑ k, v k (X i) * ∑ c, (Real.sqrt N)⁻¹ *
      Torus.partialDeriv k (φ c) (X i) * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) =
      Real.sqrt N * ∑ c, sed_A v (φ c) X * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) := by
    intro X
    have hA : ∀ c, sed_A v (φ c) X =
        (N : ℝ)⁻¹ * ∑ i, ∑ k, v k (X i) * Torus.partialDeriv k (φ c) (X i) := by
      intro c
      unfold sed_A sed_drift
      rw [pair_empirical (by omega)]
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNp.le
    have e1 : ∀ i k, v k (X i) * ∑ c, (Real.sqrt N)⁻¹ * Torus.partialDeriv k (φ c) (X i) *
        fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) = ∑ c, (Real.sqrt N)⁻¹ *
        fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) * (v k (X i) * Torus.partialDeriv k (φ c) (X i)) := by
      intro i k
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    simp_rw [e1]
    rw [swap3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hA c]
    simp only [← Finset.mul_sum]
    have hinv : Real.sqrt N * (N : ℝ)⁻¹ = (Real.sqrt N)⁻¹ := by
      field_simp
      nlinarith [hsq]
    rw [← hinv]
    ring
  have hR : ∫ X, ∑ i, ∑ k, v k (X i) * ∑ c, (Real.sqrt N)⁻¹ *
      Torus.partialDeriv k (φ c) (X i) * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q =
      Real.sqrt N * ∑ c, ∫ X, sed_A v (φ c) X * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q := by
    simp_rw [hpt2]
    rw [integral_const_mul, integral_finsetSum _ (fun c _ => hADi c)]
  have h3 := hL.symm.trans (h1.trans hR)
  field_simp
  linarith

end Moments


end HRS.MC.SEdge.B5b
