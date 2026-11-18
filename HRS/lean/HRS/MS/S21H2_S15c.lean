import HRS.MS.S21H2_S15cA

/-!
# S21H2 S15c -- infinite Hilbert-Schmidt Gaussian tilt (R26-T3.S15c), VERBATIM contract

Route: `Q` is the L2 chaos limit of the diagonal Hilbert-Schmidt matrix `diag λ` (`chaos_tendsto`).  The partial sums
`V_N = γ Q_N` converge to `V = γ Q` in probability, hence in distribution jointly with the fixed vector of the first `n`
coordinates; the finite stage (part A) gives `E exp(-2 V_N) ≤ C` uniformly and the law of the tilt, and S15a
(`s21g2_s15a_int_lim`, `s21g2_s15a_conv`, `r26t3_tilt_limit`) passes to the limit.  Helper prefix `s21h2_s15c_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS

theorem s21h2_s15c_hs {lam : ℕ → ℝ} (hlam2 : Summable fun j => lam j ^ 2) :
    IsSymmetricHS (fun i j => if i = j then lam i else 0) := by
  refine ⟨fun i j => by by_cases h : i = j <;> simp [h, eq_comm], ?_⟩
  have hinj : Function.Injective (fun i : ℕ => (i, i)) := fun a b h => (Prod.mk.inj h).1
  refine (hinj.summable_iff (f := fun p : ℕ × ℕ => (if p.1 = p.2 then lam p.1 else 0) ^ 2) ?_).1 ?_
  · intro p hp
    have : p.1 ≠ p.2 := fun h => hp ⟨p.1, Prod.ext rfl h⟩
    simp [this]
  · simpa [Function.comp_def] using hlam2

theorem s21h2_s15c_section {Ω : Type*} (ξ : ℕ → Ω → ℝ) (lam : ℕ → ℝ) :
    chaosSection (fun i j => if i = j then lam i else 0) ξ = s21h2_s15c_Qn ξ lam := by
  funext n ω
  unfold chaosSection s21h2_s15c_Qn
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · simp only [if_true]; ring
  · intro j _ hji; simp [Ne.symm hji]
  · intro h; exact absurd hi h

theorem s21h2_s15c_inprob {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (lam : ℕ → ℝ) {Q : Ω → ℝ}
    (hT : TendstoL2 P (s21h2_s15c_Qn ξ lam) Q) (γ : ℝ) (n : ℕ) :
    TendstoInDistribution (fun N ω => ((fun j : Fin n => ξ j ω), γ * s21h2_s15c_Qn ξ lam N ω)) atTop
      (fun ω => ((fun j : Fin n => ξ j ω), γ * Q ω)) (fun _ => P) P := by
  have hmQ : ∀ N, AEStronglyMeasurable (s21h2_s15c_Qn ξ lam N) P := fun N =>
    (s21h2_s15c_aemeas_Qn hξ lam N).aestronglyMeasurable
  have h1 := hT.tendsto_eLpNorm hmQ
  have hmeasV : ∀ N, AEMeasurable (fun ω => ((fun j : Fin n => ξ j ω), γ * s21h2_s15c_Qn ξ lam N ω)) P :=
    fun N => (AEMeasurable.of_eval fun j : Fin n => hξ.aemeasurable (j : ℕ)).prodMk
      ((hmQ N).aemeasurable.const_mul γ)
  have h2 : Tendsto (fun N => eLpNorm ((fun ω => γ * s21h2_s15c_Qn ξ lam N ω) - fun ω => γ * Q ω) 2 P)
      atTop (𝓝 0) := by
    have e : ∀ N, ((fun ω => γ * s21h2_s15c_Qn ξ lam N ω) - fun ω => γ * Q ω) =
        γ • (s21h2_s15c_Qn ξ lam N - Q) := fun N => by
      funext ω; simp [mul_sub]
    simp_rw [e, eLpNorm_const_smul]
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr enorm_ne_top)
  have h3 := tendstoInMeasure_of_tendsto_eLpNorm (μ := P) (p := 2) (by norm_num) h2
  refine TendstoInMeasure.tendstoInDistribution ?_ hmeasV
  intro ε hε
  simpa [Prod.edist_eq] using h3 ε hε

theorem r26t3_hs_gaussian_tilt {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℝ) (hξ : HRS.IsStdGaussianSeq P ξ)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0≤lam j) (hlam2 : Summable (fun j => lam j^2))
    (γ : ℝ) (hγ : 0≤γ) :
    ∃ Q : Ω → ℝ, HRS.TendstoL2 P
      (fun n ω => (1/2)*∑ j ∈ Finset.range n, lam j*(ξ j ω^2-1)) Q ∧
      Integrable (fun ω => Real.exp (-γ*Q ω)) P ∧
      (∫ ω, Real.exp (-γ*Q ω) ∂P)=Real.exp ((1/2)*∑' j, (γ*lam j-Real.log (1+γ*lam j))) ∧
      ∀ n, law (r26t3_tilt P (fun ω => γ*Q ω)) (fun ω (j : Fin n) => ξ j ω)=
        Measure.pi (fun j : Fin n => gaussianReal 0 ((1+γ*lam j)⁻¹).toNNReal) := by
  classical
  have hA := s21h2_s15c_hs hlam2
  have hT0 := chaos_tendsto P _ hA ξ hξ
  rw [s21h2_s15c_section ξ lam] at hT0
  set Q := chaos P (fun i j => if i = j then lam i else 0) ξ with hQ
  have hT : TendstoL2 P (s21h2_s15c_Qn ξ lam) Q := hT0
  refine ⟨Q, hT, ?_⟩
  set C : ℝ := Real.exp ((1/2) * ∑' j, (2 * γ * lam j - Real.log (1 + 2 * γ * lam j))) with hC
  have h2γ : 0 ≤ 2 * γ := by linarith
  have e2 : ∀ N ω, Real.exp (-2 * (γ * s21h2_s15c_Qn ξ lam N ω)) =
      Real.exp (-((2 * γ) * s21h2_s15c_Qn ξ lam N ω)) := fun N ω => by ring_nf
  have hb : ∀ N, ∫ ω, Real.exp (-2 * (γ * s21h2_s15c_Qn ξ lam N ω)) ∂P ≤ C := fun N => by
    simp_rw [e2]
    exact s21h2_s15c_Eexp_le hξ lam hlam hlam2 h2γ N
  have hi : ∀ N, Integrable (fun ω => Real.exp (-2 * (γ * s21h2_s15c_Qn ξ lam N ω))) P := fun N => by
    simp_rw [e2]
    exact (s21h2_s15c_Eexp hξ lam hlam h2γ N).1
  have hlim : ∀ n, TendstoInDistribution
      (fun N ω => ((fun j : Fin n => ξ j ω), γ * s21h2_s15c_Qn ξ lam N ω)) atTop
      (fun ω => ((fun j : Fin n => ξ j ω), γ * Q ω)) (fun _ => P) P :=
    fun n => s21h2_s15c_inprob hξ lam hT γ n
  have hmeas : ∀ n, (∀ N, AEMeasurable
      (fun ω => ((fun j : Fin n => ξ j ω), γ * s21h2_s15c_Qn ξ lam N ω)) P) ∧
      AEMeasurable (fun ω => ((fun j : Fin n => ξ j ω), γ * Q ω)) P :=
    fun n => ⟨(hlim n).forall_aemeasurable, (hlim n).aemeasurable_limit⟩
  have hint := s21g2_s15a_int_lim (Ω := fun _ => Ω) (P := fun _ => P) (P' := P)
    (Y := fun _ ω (j : Fin 0) => ξ j ω) (V := fun N ω => γ * s21h2_s15c_Qn ξ lam N ω)
    (Y' := fun ω (j : Fin 0) => ξ j ω) (V' := fun ω => γ * Q ω)
    (hmeas 0) (hlim 0) (r := 2) (C := C) (by norm_num) hb hi
  have hconv := s21g2_s15a_conv (Ω := fun _ => Ω) (P := fun _ => P) (P' := P)
    (Y := fun _ ω (j : Fin 0) => ξ j ω) (V := fun N ω => γ * s21h2_s15c_Qn ξ lam N ω)
    (Y' := fun ω (j : Fin 0) => ξ j ω) (V' := fun ω => γ * Q ω)
    (hmeas 0) (hlim 0) (r := 2) (C := C) (by norm_num) hb hi
    (g := fun _ => (1 : ℝ)) continuous_const (c := 1) (fun _ => by simp)
  simp only [one_mul] at hconv
  have hS : Summable fun j => γ * lam j - Real.log (1 + γ * lam j) :=
    s21f_log_sub_summable hγ lam hlam hlam2
  have hseq : Tendsto (fun N => ∫ ω, Real.exp (-(γ * s21h2_s15c_Qn ξ lam N ω)) ∂P) atTop
      (𝓝 (Real.exp ((1/2) * ∑' j, (γ * lam j - Real.log (1 + γ * lam j))))) := by
    simp_rw [(fun N => (s21h2_s15c_Eexp hξ lam hlam hγ N).2)]
    exact (Real.continuous_exp.tendsto _).comp
      ((hS.hasSum.tendsto_sum_nat).const_mul (1/2))
  have hval := tendsto_nhds_unique hconv hseq
  refine ⟨by simpa only [neg_mul] using hint, by simpa only [neg_mul] using hval, fun n => ?_⟩
  obtain ⟨-, -, -, hprob', hg⟩ := r26t3_tilt_limit (Ω := fun _ => Ω) (fun _ => P) P
    (fun _ ω (j : Fin n) => ξ j ω) (fun N ω => γ * s21h2_s15c_Qn ξ lam N ω)
    (fun ω (j : Fin n) => ξ j ω) (fun ω => γ * Q ω) (hmeas n) (hlim n) 2 C (by norm_num) hb hi
  have hV' : AEMeasurable (fun ω => γ * Q ω) P := (hmeas n).2.snd
  have hY : AEMeasurable (fun ω (j : Fin n) => ξ j ω) P :=
    AEMeasurable.of_eval fun j => hξ.aemeasurable j
  have hac : r26t3_tilt P (fun ω => γ * Q ω) ≪ P := by
    unfold r26t3_tilt
    intro s hs
    simp [withDensity_absolutelyContinuous P _ hs]
  have hYt : AEMeasurable (fun ω (j : Fin n) => ξ j ω) (r26t3_tilt P (fun ω => γ * Q ω)) :=
    hY.mono_ac hac
  unfold HRS.law
  have hintQ : Integrable (fun ω => Real.exp (-(γ * Q ω))) P := by simpa only [neg_mul] using hint
  haveI : IsProbabilityMeasure (r26t3_tilt P (fun ω => γ * Q ω)) := r26t3_tilt_isProb P hV' hintQ
  haveI : IsProbabilityMeasure ((r26t3_tilt P (fun ω => γ * Q ω)).map (fun ω (j : Fin n) => ξ j ω)) :=
    (Measure.isProbabilityMeasure_map_iff hYt).2 inferInstance
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  rw [integral_map hYt g.continuous.aestronglyMeasurable]
  refine tendsto_nhds_unique (hg g) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop n] with N hN
  exact (s21h2_s15c_tilt_marg hξ lam hlam hγ hN g.continuous).symm

end HRS.MS.R26T3
