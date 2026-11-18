import HRS.MC.S7FCW7Aux

/-!
# FC-F3 mode identity (packet `S7FCW7`): proof of `s7_FC_F3_mode_identity`

The proof combines three inputs: the empirical Itô identity on each horizon `[0,n]`
(`empirical_ito_of_contact`) with the time-independent test `f`, the mean-field weak form
(`Regime.mf`) with the continuity of its drift on `[0,n]` (from the coefficient solution), and the
pointwise drift identity `s7fcw7_alg`.  The martingale is `√N` times the Itô integral of the
horizon-free integrand `s7fcw7_Φ`, which agrees with the horizon-`n` empirical noise up to time `n`.
Namespace `HRS.MC.Sec7.S7FCW7`, prefix `s7fcw7_`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW7

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

theorem s7fcw7_cont {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Continuous f :=
  HRS.PDE.continuous_of_isCkU (s7fcw7_isCk2 hf)

theorem s7fcw7_int_cont {g : Torus d → ℝ} (hg : Continuous g) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] : Integrable g μ := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hg.continuousOn
  exact Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ fun x => hC x (Set.mem_univ x))

/-- The Itô-drift coefficient of the mean-field equation for a fixed test function. -/
theorem s7fcw7_L0_cont (R : Regime d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Continuous (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x)) :=
  ((continuous_const.mul (HRS.PDE.MFApriori.continuous_laplacian_of_isCk (s7fcw7_isCk2 hf))).sub
    ((HRS.Duality.grad_continuous (s7fcw7_isCk2 R.hV)).inner
      (HRS.Duality.grad_continuous (s7fcw7_isCk2 hf))))

theorem s7fcw7_sol (R : Regime d) : ∃ K : ℕ, (d : ℝ) / 2 + 6 < K ∧ ∃ ρc : ℝ → PDE.Coeff d,
    PDE.IsMFSolutionHK d R.D.s R.D.V R.β⁻¹ (K : ℝ) R.ρ₀ ρc ∧
      ∀ t : ℝ, 0 ≤ t → R.ρ t = PDE.mfPath ρc t := by
  have hK : (d : ℝ) / 2 + 6 < ((⌊(d : ℝ) / 2 + 6⌋₊ + 1 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one ((d : ℝ) / 2 + 6)
    push_cast; exact this
  obtain ⟨ρc, hρc, hρ⟩ := R.sol _ hK
  refine ⟨_, hK, ρc, ?_, hρ⟩
  rw [R.hDβ] at hρc
  exact hρc

theorem s7fcw7_key (R : Regime d) :
    R.D = PDE.mfData d R.D.s R.D.hs0 R.D.hsd R.D.V R.β R.hβ := by
  have key : ∀ D : DynData d, D.M = -1 → D.invβ = R.β⁻¹ →
      D = PDE.mfData d D.s D.hs0 D.hsd D.V R.β R.hβ := by
    rintro ⟨s, M, V, iβ, h1, h2, h3⟩ h4 h5
    simp only at h4 h5
    subst h4 h5
    rfl
  exact key R.D R.hM R.hDβ

/-- The mean-field drift `u ↦ ⟨ρ^u, L0⟩ + ⟨ρ^u, ⟨ρ^u, h_f⟩⟩` is continuous on `[0,T]`. -/
theorem s7fcw7_G_cont (R : Regime d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (T : ℝ) :
    ContinuousOn (fun τ => pair (withDensityReal (R.ρ τ)) (fun x => R.D.invβ * Torus.laplacian f x -
        inner ℝ (Torus.grad R.D.V x) (Torus.grad f x)) +
      interactionPairing R.D f (withDensityReal (R.ρ τ)) (withDensityReal (R.ρ τ))) (Set.Icc 0 T) := by
  obtain ⟨K, hK, ρc, hρc, hρ⟩ := s7fcw7_sol R
  have hK2 : (d : ℝ) / 2 + 2 < (K : ℝ) := by linarith
  have hreal : ∀ t : ℝ, 0 ≤ t → PDE.IsRealCoeff (ρc t) :=
    HRS.PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK (by have := R.hd; omega) R.D.s R.β R.β K R.D.V R.ρ₀
      (R.finiteRegHyp K hK) R.β ⟨le_rfl, le_rfl⟩ ρc hρc
  have H : HRS.PDE.MFApriori.MFSolRealOn d R.D.s R.D.V R.β⁻¹ K R.ρ₀ ρc T :=
    ⟨HRS.PDE.MFApriori.IsMFSolutionHK.toSolOn hρc T, fun t ht => hreal t ht.1⟩
  have hcont := (HRS.PDE.MFWeak.continuousOn_pairings (by have := R.hd; omega) R.D.s R.D.hs0 R.D.hsd K hK2
    R.D.V R.ρ₀ (R.finiteRegHyp K hK).hV R.β⁻¹ ρc H f (s7fcw7_cont hf)).2
  obtain ⟨m0, M0, hm0, hb⟩ := R.bounds
  refine ContinuousOn.congr hcont (fun τ hτ => ?_)
  have hτ0 : 0 ≤ τ := hτ.1
  have hρτ : R.ρ τ = PDE.toFun (ρc τ) := by rw [hρ τ hτ0]; rfl
  have hw := HRS.PDE.MFWeak.weak_integrand_eq (by have := R.hd; omega) R.D.s R.D.hs0 R.D.hsd (K : ℝ) hK2
    R.D.V (s7fcw7_isCk2 R.hV) (HRS.PDE.MFSemigroup.memHs_of_isSmooth R.hV (K : ℝ)) R.β R.hβ (ρc τ)
    (hρc.cont.1 τ (Set.mem_Ici.2 hτ0)) (hreal τ hτ0)
    (fun x => by
      have := (hb τ hτ0 x).1
      rw [hρτ] at this
      linarith) f (s7fcw7_isCk2 hf)
  rw [s7fcw7_key R, hρτ]
  exact hw.symm

/-- The weak mean-field identity on `[a,τ] ⊆ [0,n]` in integrated form. -/
theorem s7fcw7_mf_diff (R : Regime d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) {n : ℕ} (hn : 0 < n)
    {a τ : ℝ} (ha : 0 ≤ a) (haτ : a ≤ τ) (hτ : τ ≤ n) :
    pair (withDensityReal (R.ρ τ)) f - pair (withDensityReal (R.ρ a)) f =
      ∫ r in a..τ, (pair (withDensityReal (R.ρ r)) (fun x => R.D.invβ * Torus.laplacian f x -
        inner ℝ (Torus.grad R.D.V x) (Torus.grad f x)) +
        interactionPairing R.D f (withDensityReal (R.ρ r)) (withDensityReal (R.ρ r))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hM := R.mf n hnpos
  have hGc := s7fcw7_G_cont R hf (n : ℝ)
  have hw : ∀ t ∈ Set.Icc (0 : ℝ) n, pair (withDensityReal (R.ρ t)) f - pair (withDensityReal (R.ρ 0)) f =
      ∫ r in (0 : ℝ)..t, (pair (withDensityReal (R.ρ r)) (fun x => R.D.invβ * Torus.laplacian f x -
        inner ℝ (Torus.grad R.D.V x) (Torus.grad f x)) +
        interactionPairing R.D f (withDensityReal (R.ρ r)) (withDensityReal (R.ρ r))) := by
    intro t ht
    have hwk := hM.weak f (s7fcw7_isCk2 hf) t ht
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc] at hwk
    rw [intervalIntegral.integral_of_le ht.1]
    exact hwk
  have hτn : (0 : ℝ) ≤ τ := ha.trans haτ
  have hIτ : IntervalIntegrable (fun r => pair (withDensityReal (R.ρ r)) (fun x => R.D.invβ *
      Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x)) +
      interactionPairing R.D f (withDensityReal (R.ρ r)) (withDensityReal (R.ρ r))) MeasureTheory.volume 0 τ :=
    (hGc.mono (Set.Icc_subset_Icc le_rfl hτ)).intervalIntegrable_of_Icc hτn
  have hIa : IntervalIntegrable (fun r => pair (withDensityReal (R.ρ r)) (fun x => R.D.invβ *
      Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x)) +
      interactionPairing R.D f (withDensityReal (R.ρ r)) (withDensityReal (R.ρ r))) MeasureTheory.volume 0 a :=
    (hGc.mono (Set.Icc_subset_Icc le_rfl (haτ.trans hτ))).intervalIntegrable_of_Icc ha
  rw [← intervalIntegral.integral_interval_sub_left hIτ hIa, ← hw τ ⟨hτn, hτ⟩, ← hw a ⟨ha, haτ.trans hτ⟩]
  ring

/-- The empirical Itô identity on the horizon `[0,n]` for the time-independent test `f`. -/
theorem s7fcw7_ito {Ω : Type} [mΩ : MeasurableSpace Ω] {N : ℕ} (R : Regime d) (hN : 2 ≤ N)
    {P : Measure Ω} [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hsol : ∀ T : ℝ, IsStrongSolution P R.D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ τ ∈ Set.Icc (0 : ℝ) n,
      IntegrableOn (fun r => pair (empirical (X (Real.toNNReal r) ω))
          (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
          + interactionPairing R.D f (empirical (X (Real.toNNReal r) ω))
              (empirical (X (Real.toNNReal r) ω))) (Set.Icc 0 τ) ∧
      pair (empirical (X (Real.toNNReal τ) ω)) f
        = pair (empirical (X 0 ω)) f
          + (∫ r in (0:ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
              (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
              + interactionPairing R.D f (empirical (X (Real.toNNReal r) ω))
                  (empirical (X (Real.toNNReal r) ω))))
          + empiricalMartingale P ℱ W' R.D n (fun _ => f) X (Real.toNNReal τ) ω := by
  have hV : Torus.IsCk 2 R.D.V := s7fcw7_isCk2 R.hV
  have hC12 : IsC12Test (n : ℝ) (fun _ => f) (fun _ _ => (0 : ℝ)) :=
    { c2 := fun _ _ => s7fcw7_isCk2 hf
      cont_c2 := fun j hj => by
        have hck : ContDiff ℝ 2 (Torus.lift f) := s7fcw7_isCk2 hf
        exact (hck.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp continuous_snd
      time_deriv := fun x r _ => hasDerivAt_const r (f x)
      cont_time_deriv := continuous_const }
  have h := (empirical_ito_of_contact hN hV (hsol n).toContact hF
    (Or.inr (HRS.KID.nullContact_of_strong (hsol n)))
    (t := (n : ℝ)) ⟨Nat.cast_nonneg n, le_rfl⟩ hC12).2
  filter_upwards [h] with ω hω
  intro τ hτ
  simpa only [zero_add] using hω τ hτ

/-- The horizon-free integrand: `c ∂_j f(X_i(s))` for `s ≥ 0`, zero for `s < 0`. -/
def s7fcw7_Φ {Ω : Type} {N : ℕ} (R : Regime d) (f : Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) :
    ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun s ω k => if 0 ≤ s then
    (Real.sqrt (2 * R.D.invβ) / N) * (Torus.grad f (X (Real.toNNReal s) ω k.1)) k.2 else 0

theorem s7fcw7_stop_eq {Ω : Type} {N : ℕ} (R : Regime d) (f : Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N)
    (n : ℕ) :
    stopIntegrand (s7fcw7_Φ R f X) (fun _ : Ω => ((n : ℝ) : WithTop ℝ)) =
      empiricalNoiseIntegrand R.D n (fun _ => f) X := by
  funext s ω k
  unfold stopIntegrand s7fcw7_Φ empiricalNoiseIntegrand
  have hiff : ((s : ℝ) : WithTop ℝ) ≤ ((n : ℝ) : WithTop ℝ) ↔ s ≤ n := WithTop.coe_le_coe
  by_cases h1 : s ≤ n <;> by_cases h0 : 0 ≤ s <;>
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hiff, h0, h1, Set.mem_Icc, and_self,
      not_true_eq_false, not_false_eq_true, if_true, if_false, ite_apply, Pi.zero_apply, and_true,
      true_and, and_false, false_and]

theorem s7fcw7_mart_val {Ω : Type} [mΩ : MeasurableSpace Ω] {N : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (R : Regime d) (f : Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) (hW : IsBrownianFiltration P ℱ W')
    (hΦ : IsProgressiveL2 P ℱ (s7fcw7_Φ R f X)) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ τ : ℝ, 0 ≤ τ → τ ≤ n →
      empiricalMartingale P ℱ W' R.D n (fun _ => f) X (Real.toNNReal τ) ω =
        itoIntegral P ℱ W' (s7fcw7_Φ R f X) τ ω := by
  have hst := itoIntegral_stopIntegrand hW hΦ (isStoppingTime_const ℱ (n : ℝ))
  filter_upwards [hst] with ω hω
  intro τ hτ0 hτn
  unfold empiricalMartingale
  rw [Real.coe_toNNReal τ hτ0, ← s7fcw7_stop_eq R f X n, hω τ]
  unfold stoppedProcess
  rw [min_eq_left (WithTop.coe_le_coe.2 hτn)]
  rfl

theorem s7fcw7_Φ_prog {Ω : Type} [mΩ : MeasurableSpace Ω] {N : ℕ} (R : Regime d) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {X : ℝ≥0 → Ω → Config d N}
    (hF : IsFilteredSolution P ℱ W' W X) : IsProgressive ℱ (s7fcw7_Φ R f X) := by
  have hg : Continuous (Torus.grad f) := HRS.Duality.grad_continuous (s7fcw7_isCk2 hf)
  let g : ℝ → Config d N → (Fin N × Fin d → ℝ) := fun s x k =>
    if 0 ≤ s then (Real.sqrt (2 * R.D.invβ) / N) * (Torus.grad f (x k.1)) k.2 else 0
  have hgm : Measurable (Function.uncurry g) := by
    refine _root_.measurable_pi_iff.2 fun k => ?_
    refine Measurable.ite (measurableSet_le measurable_const measurable_fst) ?_ measurable_const
    refine measurable_const.mul ?_
    have hc : Measurable (fun v : Euc d => v k.2) :=
      (EuclideanSpace.proj k.2 : Euc d →L[ℝ] ℝ).continuous.measurable
    exact hc.comp (hg.measurable.comp ((measurable_pi_apply k.1).comp measurable_snd))
  exact isProgressive_comp_measurable' (ofNNRealTime X) hF.progressive g hgm

theorem s7fcw7_Φ_L2 {Ω : Type} [mΩ : MeasurableSpace Ω] {N : ℕ} (R : Regime d) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {X : ℝ≥0 → Ω → Config d N} (hprog : IsProgressive ℱ (s7fcw7_Φ R f X)) :
    IsProgressiveL2 P ℱ (s7fcw7_Φ R f X) := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn
    (HRS.Duality.grad_continuous (s7fcw7_isCk2 hf)).continuousOn
  refine IsProgressiveL2.of_bounded P hprog (|Real.sqrt (2 * R.D.invβ) / N| * max B 0) fun s ω k => ?_
  simp only [s7fcw7_Φ]
  split_ifs with hs
  · have h1 : |(Torus.grad f (X (Real.toNNReal s) ω k.1)) k.2| ≤
        ‖Torus.grad f (X (Real.toNNReal s) ω k.1)‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (Torus.grad f (X (Real.toNNReal s) ω k.1)) k.2
    have h2 := hB _ (Set.mem_univ (X (Real.toNNReal s) ω k.1))
    exact (abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left
      (h1.trans (h2.trans (le_max_left _ _))) (abs_nonneg _))
  · simp only [abs_zero]
    exact mul_nonneg (abs_nonneg _) (le_max_right _ _)

theorem s7fcw7_ae_nat {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : ℕ → Ω → Prop} (h : ∀ n : ℕ, ∀ᵐ ω ∂P, p n ω) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, p n ω :=
  ae_all_iff.2 h

theorem s7_FC_F3_mode_identity_proof (R : Regime d) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
      X₀ W X)
    (f : Torus d → ℝ) (hf : Torus.IsSmooth f) :
    ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X ∧
      ∃ M : ℝ → Ω → ℝ, Martingale M ℱ P ∧ (∀ t : ℝ, t ≤ 0 → M t = 0) ∧
        (∀ᵐ ω ∂P, Continuous fun t => M t ω) ∧
        ∀ᵐ ω ∂P, ∀ a τ : ℝ, 0 ≤ a → a ≤ τ →
          Real.sqrt N * (pair (empirical (X τ.toNNReal ω)) f - pair (withDensityReal (R.ρ τ)) f) -
            Real.sqrt N * (pair (empirical (X a.toNNReal ω)) f - pair (withDensityReal (R.ρ a)) f) =
          (M τ ω - M a ω) + ∫ u in a..τ,
            (Real.sqrt N * (pair (empirical (X u.toNNReal ω)) (fcGen R u f) -
                pair (withDensityReal (R.ρ u)) (fcGen R u f)) -
              (Real.sqrt N)⁻¹ * ((N : ℝ) * modulatedEnergy (hTransport d R.D.s f) (X u.toNNReal ω)
                (withDensityReal (R.ρ u)))) := by
  obtain ⟨ℱ, W', hF⟩ := hreal.filtered
  have hsol : ∀ T : ℝ, IsStrongSolution P R.D T X₀ W X := hreal.solution
  have hW : IsBrownianFiltration P ℱ W' := hF.brownian
  have hΦprog : IsProgressive ℱ (s7fcw7_Φ R f X) := s7fcw7_Φ_prog R hf hF
  have hΦ : IsProgressiveL2 P ℱ (s7fcw7_Φ R f X) := s7fcw7_Φ_L2 R hf hΦprog
  refine ⟨ℱ, W', hF, fun t ω => Real.sqrt N * itoIntegral P ℱ W' (s7fcw7_Φ R f X) t ω, ?_, ?_, ?_, ?_⟩
  · exact martingale_smul_fun (Real.sqrt N) (martingale_itoIntegral hW hΦ)
  · intro t ht
    funext ω
    simp [itoIntegral_of_nonpos P ℱ W' _ ht ω]
  · exact ae_of_all _ fun ω => continuous_const.mul (continuous_itoIntegral P ℱ W' _ ω)
  have hstop := s7fcw7_ae_nat (fun n : ℕ => s7fcw7_mart_val R f X hW hΦ n)
  have hito := s7fcw7_ae_nat (fun n : ℕ => s7fcw7_ito R hN hsol hF hf n)
  filter_upwards [hstop, hito] with ω hω2 hω1
  intro a τ ha haτ
  have hτ0 : 0 ≤ τ := ha.trans haτ
  obtain ⟨n, hτn, hnpos⟩ : ∃ n : ℕ, τ ≤ (n : ℝ) ∧ 0 < n :=
    ⟨⌈τ⌉₊ + 1, by push_cast; linarith [Nat.le_ceil τ], Nat.succ_pos _⟩
  have han : a ≤ (n : ℝ) := haτ.trans hτn
  obtain ⟨hIτ, eτ⟩ := hω1 n τ ⟨hτ0, hτn⟩
  obtain ⟨hIa, ea⟩ := hω1 n a ⟨ha, han⟩
  rw [hω2 n τ hτ0 hτn] at eτ
  rw [hω2 n a ha han] at ea
  have hmf := s7fcw7_mf_diff R hf hnpos ha haτ hτn
  have hGc := s7fcw7_G_cont R hf (n : ℝ)
  have h0τ : IntervalIntegrable (fun r => pair (empirical (X (Real.toNNReal r) ω))
      (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
      + interactionPairing R.D f (empirical (X (Real.toNNReal r) ω))
          (empirical (X (Real.toNNReal r) ω))) MeasureTheory.volume 0 τ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hτ0).2 hIτ
  have h0a : IntervalIntegrable (fun r => pair (empirical (X (Real.toNNReal r) ω))
      (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
      + interactionPairing R.D f (empirical (X (Real.toNNReal r) ω))
          (empirical (X (Real.toNNReal r) ω))) MeasureTheory.volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha).2 hIa
  have hFaτ : IntervalIntegrable (fun r => pair (empirical (X (Real.toNNReal r) ω))
      (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
      + interactionPairing R.D f (empirical (X (Real.toNNReal r) ω))
          (empirical (X (Real.toNNReal r) ω))) MeasureTheory.volume a τ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le haτ).2 (hIτ.mono_set (Set.Icc_subset_Icc ha le_rfl))
  have hGaτ : IntervalIntegrable (fun r => pair (withDensityReal (R.ρ r)) (fun x => R.D.invβ *
      Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x)) +
      interactionPairing R.D f (withDensityReal (R.ρ r)) (withDensityReal (R.ρ r)))
      MeasureTheory.volume a τ :=
    (hGc.mono (Set.Icc_subset_Icc ha hτn)).intervalIntegrable_of_Icc haτ
  have hint : ∫ u in a..τ, (Real.sqrt N * (pair (empirical (X u.toNNReal ω)) (fcGen R u f) -
      pair (withDensityReal (R.ρ u)) (fcGen R u f)) -
      (Real.sqrt N)⁻¹ * ((N : ℝ) * modulatedEnergy (hTransport d R.D.s f) (X u.toNNReal ω)
        (withDensityReal (R.ρ u)))) =
      Real.sqrt N * ((∫ r in a..τ, (pair (empirical (X (Real.toNNReal r) ω))
      (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
      + interactionPairing R.D f (empirical (X (Real.toNNReal r) ω))
          (empirical (X (Real.toNNReal r) ω)))) -
        ∫ r in a..τ, (pair (withDensityReal (R.ρ r)) (fun x => R.D.invβ * Torus.laplacian f x -
          inner ℝ (Torus.grad R.D.V x) (Torus.grad f x)) +
          interactionPairing R.D f (withDensityReal (R.ρ r)) (withDensityReal (R.ρ r)))) := by
    rw [← intervalIntegral.integral_sub hFaτ hGaτ, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le haτ] at hu
    have hu0 : 0 ≤ u := ha.trans hu.1
    have hun : u ≤ (n : ℝ) := hu.2.trans hτn
    have hdens := (R.mf (n : ℝ) (by exact_mod_cast hnpos)).density u ⟨hu0, hun⟩
    haveI := HRS.isProb_withDensityReal hdens
    obtain ⟨m0, M0, hm0, hb⟩ := R.bounds
    have hH := s7fcw7_H_integrable R.hd R.D.hs0 R.hs hf hdens (fun y => (hb u hu0 y).2)
    have hL := s7fcw7_int_cont (s7fcw7_L0_cont R hf) (withDensityReal (R.ρ u))
    exact s7fcw7_alg (N := N) (by omega) (s7fcw7_sd R.hd R.hs) R.D R.hM rfl f hf (X u.toNNReal ω)
      (withDensityReal (R.ρ u))
      (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
      (s7fcw7_L0_cont R hf).measurable hL hH
  have eF : ∫ r in a..τ, (pair (empirical (X (Real.toNNReal r) ω))
      (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
      + interactionPairing R.D f (empirical (X (Real.toNNReal r) ω))
          (empirical (X (Real.toNNReal r) ω))) =
      (∫ r in (0:ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
        (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
        + interactionPairing R.D f (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω)))) -
        ∫ r in (0:ℝ)..a, (pair (empirical (X (Real.toNNReal r) ω))
        (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
        + interactionPairing R.D f (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω))) :=
    (intervalIntegral.integral_interval_sub_left h0τ h0a).symm
  have e1 : pair (empirical (X τ.toNNReal ω)) f - pair (empirical (X a.toNNReal ω)) f =
      (∫ r in a..τ, (pair (empirical (X (Real.toNNReal r) ω))
        (fun x => R.D.invβ * Torus.laplacian f x - inner ℝ (Torus.grad R.D.V x) (Torus.grad f x))
        + interactionPairing R.D f (empirical (X (Real.toNNReal r) ω))
            (empirical (X (Real.toNNReal r) ω)))) +
        (itoIntegral P ℱ W' (s7fcw7_Φ R f X) τ ω - itoIntegral P ℱ W' (s7fcw7_Φ R f X) a ω) := by
    linarith [eτ, ea, eF]
  rw [hint]
  linear_combination (Real.sqrt N) * e1 - (Real.sqrt N) * hmf

end HRS.MC.Sec7.S7FCW7

end
