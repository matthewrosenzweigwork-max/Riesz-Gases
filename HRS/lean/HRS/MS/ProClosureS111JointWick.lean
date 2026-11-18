import HRS.MS.ProClosureS111PhysicalWick
import HRS.MS.R2ChaosAux32

/-!
Actual jointly measurable Wick representatives on the physical continuous
path space. Finite Wick sections are jointly measurable, and the accepted
measurable L2-limit theorem gives a representative correct at every time.
This does not assert a single probability-null set valid at all real times.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R2Chaos HRS.MS.R26T6 HRS.MS.S111T HRS.MS.S111X1

variable {d : ℕ}

theorem pairedProcess_joint_continuous (d : ℕ) (m H : ℝ) (hH : 0 ≤ H) (i : Fin 2) :
    Continuous (fun p : ℝ × PathPair d m H => pairedProcess d m H hH i p.1 p.2) := by
  have hc : Continuous (fun t : ℝ => clippedTime H hH t) := by
    unfold clippedTime
    fun_prop
  let path : ℝ × PathPair d m H → OscPath d m H := fun p =>
    if i = 0 then p.2.1 else p.2.2
  have hp : Continuous path := by
    by_cases hi : i = 0
    · simp [path, hi]
      fun_prop
    · simp [path, hi]
      fun_prop
  have hp' : Continuous (fun p : ℝ × PathPair d m H =>
      (show ContinuousMap (Icc (0 : ℝ) H) (OscDual d m) from path p)) := hp
  exact continuous_eval.comp (hp'.prodMk (hc.comp continuous_fst))

theorem paired_observation_joint_measurable (d : ℕ) (m H : ℝ) (hH : 0 ≤ H)
    (i : Fin 2) (phi : oscSub d m) :
    Measurable (fun p : ℝ × PathPair d m H =>
      OscDual.eval (pairedProcess d m H hH i p.1 p.2) (phi : Euc d → ℝ)) := by
  have h := (gaussianOscEval phi).continuous.comp (pairedProcess_joint_continuous d m H hH i)
  have he : (fun p : ℝ × PathPair d m H =>
      OscDual.eval (pairedProcess d m H hH i p.1 p.2) (phi : Euc d → ℝ)) =
      (gaussianOscEval phi) ∘ (fun p : ℝ × PathPair d m H =>
        pairedProcess d m H hH i p.1 p.2) := by
    funext p
    exact (gaussianOscEval_apply phi _).symm
  rw [he]
  exact h.measurable

section Joint

variable {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]

def jointWickSection (z : ℕ → ℝ × Omega → ℝ) (A : ℕ → ℕ → ℝ)
    (n : ℕ) (p : ℝ × Omega) : ℝ :=
  s94Sec P (fun i w => z i (p.1,w)) A n p.2

theorem jointWickSection_measurable (z : ℕ → ℝ × Omega → ℝ)
    (hz : ∀ i, Measurable (z i)) (A : ℕ → ℕ → ℝ) (n : ℕ) :
    Measurable (jointWickSection P z A n) := by
  unfold jointWickSection s94Sec
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have hij : Measurable (fun t : ℝ => ∫ w, z i (t,w) * z j (t,w) ∂P) :=
    (((hz i).mul (hz j)).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  exact measurable_const.mul (((hz i).mul (hz j)).sub (hij.comp measurable_fst))

/-- A genuine joint representative from an actual Gaussian sequence and
an actual symmetric square-integrable kernel. All-time correctness is
sectional L2 correctness, without an uncountable common-null-set claim. -/
theorem joint_wick_of_sequence (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (basis : ℕ → Euc d → ℝ) (hbasis : HRS.Whole.IsR2ZeroMeanONB mu basis)
    (z : ℕ → ℝ × Omega → ℝ) (hz : ∀ i, Measurable (z i))
    (H L : ℝ) (hL : 0 ≤ L)
    (hseq : ∀ t ∈ Icc (0 : ℝ) H, S94GSeq P (fun i w => z i (t,w)) L)
    (k : Euc d → Euc d → ℝ)
    (hkm : Measurable (fun xy : Euc d × Euc d => k xy.1 xy.2))
    (hks : ∀ x y, k x y = k y x)
    (hk2 : MemLp (fun xy : Euc d × Euc d => k xy.1 xy.2) 2 (mu.prod mu)) :
    ∃ Q : ℝ × Omega → ℝ, Measurable Q ∧ ∀ t ∈ Icc (0 : ℝ) H,
      MemLp (fun w => Q (t,w)) 2 P ∧
      HRS.Whole.IsR2WickChaos P mu basis (fun i w => z i (t,w)) k (fun w => Q (t,w)) ∧
      (∫ w, Q (t,w)^2 ∂P) ≤ 2*L^2 * ∫ xy : Euc d × Euc d, k xy.1 xy.2 ^ 2 ∂mu.prod mu := by
  let A : ℕ → ℕ → ℝ := HRS.Whole.r2WickCoeff mu basis k
  let Phi : ℕ → ℝ × Omega → ℝ := jointWickSection P z A
  have hPhi : ∀ n, Measurable (Phi n) := jointWickSection_measurable P z hz A
  have hPhi2 : ∀ n, ∀ t ∈ Icc (0 : ℝ) H, MemLp (fun w => Phi n (t,w)) 2 P :=
    fun n t ht => s94_sec_memLp (hseq t ht) A n
  have hex : ∀ t ∈ Icc (0 : ℝ) H, ∃ Q0 : Omega → ℝ,
      s94WickL2 P mu basis (fun i w => z i (t,w)) k Q0 ∧
      (∫ w, Q0 w^2 ∂P) ≤ 2*L^2 * ∫ xy : Euc d × Euc d, k xy.1 xy.2 ^ 2 ∂mu.prod mu :=
    fun t ht => s94_wick_exists (hseq t ht) hL hbasis.1 hbasis.2.1 hkm hks hk2
  have hcau : ∀ t ∈ Icc (0 : ℝ) H, ∀ eps : ℝ≥0∞, 0 < eps →
      ∃ M : ℕ, ∀ n, M ≤ n → ∀ n', M ≤ n' →
        eLpNorm (fun w => Phi n (t,w) - Phi n' (t,w)) 2 P < eps := by
    intro t ht eps heps
    obtain ⟨Q0, hQ0, _⟩ := hex t ht
    have hlim : Tendsto (fun n => eLpNorm (fun w => Phi n (t,w)-Q0 w) 2 P) atTop (𝓝 0) :=
      HRS.TendstoL2.tendsto_eLpNorm (fun n => (hPhi2 n t ht).aestronglyMeasurable)
        (s94WickL2.isWick (hseq t ht) hQ0)
    obtain ⟨M, hM⟩ := eventually_atTop.1
      (hlim.eventually_lt_const (ENNReal.half_pos heps.ne'))
    refine ⟨M, fun n hn n' hn' => ?_⟩
    have he : (fun w => Phi n (t,w) - Phi n' (t,w)) =
        (fun w => Phi n (t,w) - Q0 w) - (fun w => Phi n' (t,w) - Q0 w) := by
      funext w
      simp
    rw [he]
    refine (eLpNorm_sub_le (by norm_num)).trans_lt ?_
    exact (ENNReal.add_lt_add (hM n hn) (hM n' hn')).trans_eq (ENNReal.add_halves eps)
  obtain ⟨Q, hQm, hQlim⟩ := s94_measurable_L2_limit measurableSet_Icc hPhi hPhi2 hcau
  refine ⟨Q, hQm, fun t ht => ?_⟩
  have hW : HRS.Whole.IsR2WickChaos P mu basis (fun i w => z i (t,w)) k (fun w => Q (t,w)) := by
    refine ⟨(hQlim t ht).1.aestronglyMeasurable, ?_⟩
    change Tendsto (fun n => ∫⁻ w, ‖Phi n (t,w)-Q (t,w)‖ₑ^2 ∂P) atTop (𝓝 0)
    have he : ∀ n, (∫⁻ w, ‖Phi n (t,w)-Q (t,w)‖ₑ^2 ∂P) =
        eLpNorm (fun w => Phi n (t,w)-Q (t,w)) 2 P ^ 2 := fun n =>
      HRS.lintegral_enorm_sq_eq ((hPhi2 n t ht).aestronglyMeasurable.sub
        (hQlim t ht).1.aestronglyMeasurable)
    simp_rw [he]
    have hpow := ((ENNReal.continuous_pow 2).tendsto 0).comp (hQlim t ht).2
    simpa only [Function.comp_def, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hpow
  obtain ⟨Q0, hQ0, hb0⟩ := hex t ht
  have hae : (fun w => Q (t,w)) =ᵐ[P] Q0 :=
    HRS.TendstoL2.ae_unique (fun n => (hPhi2 n t ht).aestronglyMeasurable)
      hW (s94WickL2.isWick (hseq t ht) hQ0)
  exact ⟨(hQlim t ht).1, hW,
    (integral_congr_ae (hae.fun_comp (fun x : ℝ => x^2))).trans_le hb0⟩

end Joint

/-- The joint scalar Wick construction with its uniform covariance
constant supplied by the physical thermal estimates. Joint measurability
of the underlying process is automatically available for `pairedProcess`.
-/
theorem physical_joint_wick_uniform (hd : 2 ≤ d)
    (s a beta : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ)/2)
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ L : ℝ, 0 < L ∧ ∀ rho : Euc d → ℝ,
      HRS.Whole.IsThermalEquilibrium d s a beta rho → ∀ gamma : ℝ, 0 ≤ gamma →
      ∀ (Omega : Type*) [MeasurableSpace Omega] (P : Measure Omega)
        [IsProbabilityMeasure P] (H : ℝ) (Z : ℝ → Omega → OscDual d (wholeSpaceIndex d)),
      IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
        (wholeSpaceIndex d) beta⁻¹ H
        (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma) Z →
      Measurable (fun p : ℝ × Omega => Z p.1 p.2) →
      ∀ basis : ℕ → Euc d → ℝ,
      HRS.Whole.IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis →
      ∀ k : Euc d → Euc d → ℝ,
      Measurable (fun xy : Euc d × Euc d => k xy.1 xy.2) →
      (∀ x y, k x y = k y x) →
      MemLp (fun xy : Euc d × Euc d => k xy.1 xy.2) 2
        ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho)) →
      ∃ Q : ℝ × Omega → ℝ, Measurable Q ∧ ∀ t ∈ Icc (0 : ℝ) H,
        MemLp (fun w => Q (t,w)) 2 P ∧
        HRS.Whole.IsR2WickChaos P (HRS.Whole.withDensityReal rho) basis
          (fun i w => OscDual.eval (Z t w) (basis i)) k (fun w => Q (t,w)) ∧
        (∫ w, Q (t,w)^2 ∂P) ≤ 2*L^2 * ∫ xy : Euc d × Euc d,
          k xy.1 xy.2 ^ 2 ∂((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho)) := by
  obtain ⟨L, hL, hseq⟩ := physical_gaussian_sequence_uniform hd s a beta hs0 hs ha hbeta
  refine ⟨L, hL, fun rho hrho gamma hgamma Omega _ P _ H Z hZ hZm basis hbasis k hkm hks hk2 => ?_⟩
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  have hz : ∀ j, Measurable (fun p : ℝ × Omega => OscDual.eval (Z p.1 p.2) (basis j)) := by
    intro j
    let phi : oscSub d (wholeSpaceIndex d) := ⟨basis j, r2Test_isOscTest _ (hbasis.1 j)⟩
    have hm := (gaussianOscEval phi).continuous.measurable.comp hZm
    have he : (fun p : ℝ × Omega => OscDual.eval (Z p.1 p.2) (basis j)) =
        (gaussianOscEval phi) ∘ (fun p : ℝ × Omega => Z p.1 p.2) := by
      funext p
      exact (gaussianOscEval_apply phi _).symm
    rw [he]
    exact hm
  exact joint_wick_of_sequence P (HRS.Whole.withDensityReal rho) basis hbasis _ hz H L hL.le
    (hseq rho hrho gamma hgamma Omega P H Z hZ basis hbasis) k hkm hks hk2

#print axioms joint_wick_of_sequence
#print axioms physical_joint_wick_uniform

end HRS.MS.ProClosureS111
