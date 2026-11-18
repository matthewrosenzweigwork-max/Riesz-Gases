import HRS.MS.Fp81S21MovingStd
import HRS.MS.Fp81S21AdjointAll
import HRS.MS.R2InterpAux108
import HRS.MS.R2InterpAux125

/-!
# HRS S2.1(iii), packet 8.3: moving-reference measurability

Consumer obligations collected from the stationary interpolation files:

* `R2InterpAux108.s102_eta_JMeas`: for every pair of finite dual-test combinations, the
  covariance integrand formed from their propagated gradients must be a.e.-measurable in time.
  In the moving case this includes the moving density factor and its centering integral.
* `R2InterpAux83.s102_quad_prodInt`, `R2InterpAux96.s102_bdc_prog_int`, and
  `R2InterpAux87.orbit_zeta`: the pair energy of a jointly measurable, time-dependent kernel
  against the moving reference must be jointly measurable in time and configuration, and its
  particle expectation must be measurable in time.
* `R2InterpAux121.s102_Env_meas` and `R2InterpAux125.s102_M1`: the S10.2 polynomial envelope
  needs the same joint measurability, including its moving row and double spatial integrals,
  and its expectation under the particle law must be measurable in time.
* `R2InterpAux122.s102_gk_int`, `R2InterpAux122.s102_Env_bound`, and
  `R2InterpAux83.s102_quad_prodInt`: the spatial rows and double integral of the polynomial
  envelope must be integrable under each moving reference; the envelope itself must be
  integrable under each particle marginal with a uniform bound, hence on time × probability.
  The latter uses the moving actual-density and particle-moment inputs, not measurability alone.
* `R2InterpAux116.s102_cylA_meas` and `R2InterpAux117.s102_cylJ_meas`: after the preceding
  families are available, the drift and covariance cylindrical integrands and their time
  integrals must be measurable in the particle outcome.

This file proves the parameterized spatial-integral, pair-energy, envelope, and particle-
expectation measurability obligations, moving `R2JIntegrandMeas`, and the moving spatial-row
integrability of the polynomial envelope. It also records the remaining particle-law and
cylindrical obligations below; those are not silently inferred from measurability.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2Interp
open HRS.MS.R26T3

private theorem fp81s21_moving_density_joint_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    Continuous fun z : ℝ≥0 × Euc p.d => R.ρ z.1 z.2 := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρβc : Continuous R.ρβ := by
    obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ']
    exact ψ'.continuous
  have hρβpos : ∀ x, 0 < R.ρβ x := fun x => HRS.Whole.u4_thermal_pos R.thermal x
  have hm : (p.d : ℝ) / 2 < ((102 * p.d + 1020 : ℕ) : ℝ) := by
    rw [HRS.MS.R2WinOrbNL.s103n_cast_m]
    nlinarith
  have hclass := HRS.MS.R2WinOrbNL.s103n_small_class R.resulting
    (r := p.C₁ * δ) le_rfl
  exact HRS.MS.R2S11.s11_class_continuous hρβc hρβpos hm hclass

private def fp81s21_clipped_time (T : ℝ) (u : ℝ) : ℝ≥0 :=
  ⟨max 0 (min u T), le_max_left _ _⟩

private theorem fp81s21_clipped_time_mem (T : ℝ) (hT : 0 < T) (u : ℝ) :
    (fp81s21_clipped_time T u : ℝ) ∈ Set.Icc (0 : ℝ) T := by
  constructor
  · exact (fp81s21_clipped_time T u).property
  · change max 0 (min u T) ≤ T
    exact max_le hT.le (min_le_right _ _)

/-- Measurability and nonnegativity of the trajectory density extended by clamping time to a
fixed finite horizon. -/
private theorem fp81s21_clipped_density_data
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hT : 0 < T) :
    Measurable (fun q : ℝ × Euc p.d =>
      R.ρ (fp81s21_clipped_time T q.1) q.2) ∧
      ∀ u x, 0 ≤ R.ρ (fp81s21_clipped_time T u) x := by
  have hjoint := fp81s21_moving_density_joint_continuous p R hδ hδh
  have hclip : Continuous (fp81s21_clipped_time T) := by
    change Continuous (fun u : ℝ =>
      (⟨max 0 (min u T), le_max_left _ _⟩ : ℝ≥0))
    fun_prop
  have hmap : Continuous fun q : ℝ × Euc p.d =>
      (fp81s21_clipped_time T q.1, q.2) := by
    fun_prop
  have hmeas : Measurable (fun q : ℝ × Euc p.d =>
      R.ρ (fp81s21_clipped_time T q.1) q.2) := (hjoint.comp hmap).measurable
  have hsol := R.resulting.global T
  have hnn : ∀ u x, 0 ≤ R.ρ (fp81s21_clipped_time T u) x := by
    intro u x
    exact (hsol.density (fp81s21_clipped_time T u)
      (fp81s21_clipped_time_mem T hT u)).nonneg x
  exact ⟨hmeas, hnn⟩

/-- Joint measurability of the moving density on the physical time-space cylinder, derived from
the trajectory's joint continuity. -/
theorem fp81s21_moving_density_joint_meas
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    Measurable (fun q : Set.Icc (0 : ℝ) H × Euc p.d => R.ρ q.1 q.2) := by
  have hjoint := fp81s21_moving_density_joint_continuous p R hδ hδh
  have hmap : Continuous
      (fun q : Set.Icc (0 : ℝ) H × Euc p.d =>
        ((⟨q.1.1, q.1.2.1⟩ : ℝ≥0), q.2)) := by
    fun_prop
  exact (hjoint.comp hmap).measurable

private theorem fp81s21_moving_density_integral_meas
    {d : ℕ} {U : Type} [MeasurableSpace U]
    {ρ : U → Euc d → ℝ} (hρ : Measurable (fun q : U × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ u x, 0 ≤ ρ u x)
    {f : U → Euc d → ℝ} (hf : Measurable (fun q : U × Euc d => f q.1 q.2)) :
    Measurable fun u => ∫ x, f u x ∂(HRS.Whole.withDensityReal (ρ u)) := by
  have hweighted : Measurable (fun q : U × Euc d => f q.1 q.2 * ρ q.1 q.2) := hf.mul hρ
  have hbase : Measurable fun u => ∫ x, f u x * ρ u x :=
    (hweighted.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have heq : (fun u => ∫ x, f u x ∂(HRS.Whole.withDensityReal (ρ u))) =
      fun u => ∫ x, f u x * ρ u x := by
    funext u
    calc
      (∫ x, f u x ∂(HRS.Whole.withDensityReal (ρ u))) = ∫ x, ρ u x * f u x :=
        HRS.MP.RdRem.mrr_integral_withDensityReal (ρ u)
          (hρ.comp (measurable_const.prodMk measurable_id)) (hρ0 u) (f u)
      _ = ∫ x, f u x * ρ u x := by
        congr 1
        funext x
        ring
  rw [heq]
  exact hbase

/-- A moving-density analogue of a single spatial parameter integral. -/
theorem fp81s21_moving_spatial_integral_meas
    {d : ℕ} {U : Type} [MeasurableSpace U]
    {ρ : U → Euc d → ℝ} (hρ : Measurable (fun q : U × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ u x, 0 ≤ ρ u x)
    {f : U → Euc d → ℝ} (hf : Measurable (fun q : U × Euc d => f q.1 q.2)) :
    Measurable fun u => ∫ x, f u x ∂(HRS.Whole.withDensityReal (ρ u)) :=
  fp81s21_moving_density_integral_meas hρ hρ0 hf

private theorem fp81s21_moving_pair_row_meas
    {d : ℕ} {ρ : ℝ → Euc d → ℝ} {k : ℝ → Euc d → Euc d → ℝ}
    (hρ : Measurable (fun q : ℝ × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ u x, 0 ≤ ρ u x)
    (hk : Measurable fun q : ℝ × Euc d × Euc d => k q.1 q.2.1 q.2.2) :
    Measurable fun q : ℝ × Euc d =>
      ∫ y, k q.1 q.2 y ∂(HRS.Whole.withDensityReal (ρ q.1)) := by
  let ρ' : (ℝ × Euc d) → Euc d → ℝ := fun q y => ρ q.1 y
  let f : (ℝ × Euc d) → Euc d → ℝ := fun q y => k q.1 q.2 y
  have hρ' : Measurable (fun q : (ℝ × Euc d) × Euc d => ρ' q.1 q.2) := by
    exact hρ.comp (measurable_fst.fst.prodMk measurable_snd)
  have hρ'0 : ∀ q y, 0 ≤ ρ' q y := fun q y => hρ0 q.1 y
  have hf : Measurable (fun q : (ℝ × Euc d) × Euc d => f q.1 q.2) := by
    exact hk.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd))
  have hr := fp81s21_moving_density_integral_meas
    (ρ := ρ') hρ' hρ'0 (f := f) hf
  change Measurable (fun q : ℝ × Euc d =>
    ∫ y, k q.1 q.2 y ∂(HRS.Whole.withDensityReal (fun y => ρ q.1 y))) at hr
  exact hr

private theorem fp81s21_moving_config_row_meas
    {d N : ℕ} {ρ : ℝ → Euc d → ℝ} {k : ℝ → Euc d → Euc d → ℝ}
    (hρ : Measurable (fun q : ℝ × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ u x, 0 ≤ ρ u x)
    (hk : Measurable fun q : ℝ × Euc d × Euc d => k q.1 q.2.1 q.2.2)
    (i : Fin N) :
    Measurable fun q : ℝ × EucConfig d N =>
      ∫ y, k q.1 (q.2 i) y ∂(HRS.Whole.withDensityReal (ρ q.1)) := by
  let ρ' : (ℝ × EucConfig d N) → Euc d → ℝ := fun q y => ρ q.1 y
  let f : (ℝ × EucConfig d N) → Euc d → ℝ := fun q y => k q.1 (q.2 i) y
  have hρ' : Measurable
      (fun q : (ℝ × EucConfig d N) × Euc d => ρ' q.1 q.2) := by
    exact hρ.comp (measurable_fst.fst.prodMk measurable_snd)
  have hρ'0 : ∀ q y, 0 ≤ ρ' q y := fun q y => hρ0 q.1 y
  have hXi : Measurable fun q : (ℝ × EucConfig d N) × Euc d => q.1.2 i :=
    (measurable_pi_apply i).comp measurable_fst.snd
  have hf : Measurable
      (fun q : (ℝ × EucConfig d N) × Euc d => f q.1 q.2) := by
    exact hk.comp (measurable_fst.fst.prodMk (hXi.prodMk measurable_snd))
  have hr := fp81s21_moving_density_integral_meas
    (ρ := ρ') hρ' hρ'0 (f := f) hf
  change Measurable (fun q : ℝ × EucConfig d N =>
    ∫ y, k q.1 (q.2 i) y ∂(HRS.Whole.withDensityReal (fun y => ρ q.1 y))) at hr
  exact hr

/-- Pair energies are jointly measurable when both the kernel and reference density move. -/
theorem fp81s21_moving_pairEnergy_joint_meas
    {d N : ℕ} {ρ : ℝ → Euc d → ℝ} {k : ℝ → Euc d → Euc d → ℝ}
    (hρ : Measurable (fun q : ℝ × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ u x, 0 ≤ ρ u x)
    (hk : Measurable fun q : ℝ × Euc d × Euc d => k q.1 q.2.1 q.2.2) :
    Measurable fun q : ℝ × EucConfig d N =>
      HRS.Whole.pairEnergy (k q.1) q.2 (HRS.Whole.withDensityReal (ρ q.1)) := by
  classical
  have hrow : Measurable (fun q : ℝ × Euc d =>
      ∫ y, k q.1 q.2 y ∂(HRS.Whole.withDensityReal (ρ q.1))) :=
    fp81s21_moving_pair_row_meas hρ hρ0 hk
  have hdouble : Measurable (fun u : ℝ =>
      ∫ x, (∫ y, k u x y ∂(HRS.Whole.withDensityReal (ρ u)))
        ∂(HRS.Whole.withDensityReal (ρ u))) :=
    fp81s21_moving_density_integral_meas hρ hρ0 hrow
  have hpp : Measurable fun q : ℝ × EucConfig d N =>
      ∑ i, ∑ j ∈ Finset.univ.erase i, k q.1 (q.2 i) (q.2 j) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    have hi : Measurable fun q : ℝ × EucConfig d N => q.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    have hj : Measurable fun q : ℝ × EucConfig d N => q.2 j :=
      (measurable_pi_apply j).comp measurable_snd
    have hmap : Measurable (fun q : ℝ × EucConfig d N => (q.1, (q.2 i, q.2 j))) :=
      measurable_fst.prodMk (hi.prodMk hj)
    exact hk.comp hmap
  have hrows : Measurable fun q : ℝ × EucConfig d N =>
      ∑ i, ∫ y, k q.1 (q.2 i) y ∂(HRS.Whole.withDensityReal (ρ q.1)) := by
    exact Finset.measurable_sum _ fun i _ =>
      fp81s21_moving_config_row_meas hρ hρ0 hk i
  change Measurable (fun q : ℝ × EucConfig d N =>
    (1 / (2 * (N : ℝ) ^ 2)) *
        (∑ i, ∑ j ∈ Finset.univ.erase i, k q.1 (q.2 i) (q.2 j)) -
      (1 / (N : ℝ)) *
        (∑ i, ∫ y, k q.1 (q.2 i) y ∂(HRS.Whole.withDensityReal (ρ q.1))) +
      (1 / 2) *
        (∫ x, ∫ y, k q.1 x y ∂(HRS.Whole.withDensityReal (ρ q.1))
          ∂(HRS.Whole.withDensityReal (ρ q.1))))
  exact ((hpp.const_mul _).sub (hrows.const_mul _)).add
    ((hdouble.comp measurable_fst).const_mul _)

/-- The moving S10.2 envelope has the same joint measurability, including its two background
integrals. -/
theorem fp81s21_moving_envelope_joint_meas
    {d N : ℕ} {ρ : ℝ → Euc d → ℝ} {g : ℝ → Euc d → Euc d → ℝ}
    (hρ : Measurable (fun q : ℝ × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ u x, 0 ≤ ρ u x)
    (hg : Measurable fun q : ℝ × Euc d × Euc d => g q.1 q.2.1 q.2.2) :
    Measurable fun q : ℝ × EucConfig d N =>
      s102_Env (g q.1) q.2 (HRS.Whole.withDensityReal (ρ q.1)) := by
  classical
  have hp := fp81s21_moving_pairEnergy_joint_meas (N := N) hρ hρ0 hg
  have hrow : Measurable (fun q : ℝ × Euc d =>
      ∫ y, g q.1 q.2 y ∂(HRS.Whole.withDensityReal (ρ q.1))) :=
    fp81s21_moving_pair_row_meas hρ hρ0 hg
  have hrows : Measurable fun q : ℝ × EucConfig d N =>
      ∑ i, ∫ y, g q.1 (q.2 i) y ∂(HRS.Whole.withDensityReal (ρ q.1)) := by
    exact Finset.measurable_sum _ fun i _ =>
      fp81s21_moving_config_row_meas hρ hρ0 hg i
  have heq : (fun q : ℝ × EucConfig d N =>
      s102_Env (g q.1) q.2 (HRS.Whole.withDensityReal (ρ q.1))) =
      fun q => HRS.Whole.pairEnergy (g q.1) q.2 (HRS.Whole.withDensityReal (ρ q.1)) +
        (2 / (N : ℝ)) * ∑ i, ∫ y, g q.1 (q.2 i) y
          ∂(HRS.Whole.withDensityReal (ρ q.1)) := by
    funext q
    exact s102_Env_eq (g q.1) q.2 (HRS.Whole.withDensityReal (ρ q.1))
  rw [heq]
  exact hp.add (measurable_const.mul hrows)

/-- Total expectation integral of any jointly measurable moving family. Apply this after the
pair-energy or envelope joint-measurability theorem to obtain the corresponding expectation
integral measurability used in Aux87/Aux125. -/
theorem fp81s21_moving_total_integral_meas
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {F : ℝ × Ω → ℝ} (hF : Measurable F) :
    Measurable (fun u : ℝ => ∫ ω, F (u, ω) ∂P) := by
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := P)).measurable

/-- The Gaussian envelope gives moving-reference spatial integrability of all polynomial rows
used by `s102_Env`; the bound is uniform in time. -/
theorem fp81s21_moving_envelope_rows_integrable
    {d : ℕ} {H : ℝ}
    (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {M L C₀ c₀ : ℝ} (hc₀ : 0 < c₀) {Pw : ℝ} (hPw : 0 ≤ Pw)
    {ρ : ℝ → Euc d → ℝ} (hρ : ∀ u ∈ Icc (0 : ℝ) H, IsRound2Density d s M L (ρ u))
    (hG : ∀ u ∈ Icc (0 : ℝ) H, ∀ x,
      ρ u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u ∈ Icc (0 : ℝ) H,
      (∀ x, Integrable (s102_gk s Pw x) (HRS.Whole.withDensityReal (ρ u))) ∧
      Integrable (fun x => ∫ y, s102_gk s Pw x y
        ∂(HRS.Whole.withDensityReal (ρ u))) (HRS.Whole.withDensityReal (ρ u)) ∧
      ∀ x, ∫ y, s102_gk s Pw x y ∂(HRS.Whole.withDensityReal (ρ u)) ≤ A * jbracket x ^ Pw := by
  obtain ⟨A, hA0, hA⟩ := s102_gk_int hd hs0 hs M C₀ c₀ hc₀ hPw
  refine ⟨A, hA0, fun u hu => ?_⟩
  have hρu := hρ u hu
  have hGu := hG u hu
  have hresult := hA (ρ u) hρu.prob hρu.bdd hGu
  exact hresult

/-- Moving-reference analogue of `s102_eta_JMeas`. The centered particle field uses the actual
time-dependent reference `r26t3_mu R u`; finite Hermite combinations have classical adjoints,
their gradients are jointly measurable and bounded, and the reference density is jointly
measurable after clipping to the physical horizon. -/
theorem fp81s21_moving_eta_JIntegrandMeas
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hT : 0 < T)
    {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → EucConfig p.d N) (ζ : Ω)
    (hcz : ∀ k, Continuous fun t : ℝ≥0 => X t ζ k) :
    HRS.Whole.R2JIntegrandMeas (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) T
      (fun u f => Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ζ)) f -
          HRS.Whole.pair (r26t3_mu R u) f)) := by
  classical
  obtain ⟨hρclip, hρclip0⟩ :=
    fp81s21_clipped_density_data p R hδ hδh hT
  let ρclip : ℝ → Euc p.d → ℝ :=
    fun u x => R.ρ (fp81s21_clipped_time T u) x
  let C : WholeCoeff p.d := r26t3_coeff R
  intro ta tb φa φb hφa hφb hta htb
  obtain ⟨fa, hfa⟩ := fp81s21_adjoint_of_hermite_combo p R hφa hta.1
  obtain ⟨fb, hfb⟩ := fp81s21_adjoint_of_hermite_combo p R hφb htb.1
  have hFa : IsClassicalAdjointW C ta φa (fun u => propagatorW C u ta φa) := by
    exact s102_propagator_classical ⟨fa, by simpa [C] using hfa⟩
  have hFb : IsClassicalAdjointW C tb φb (fun u => propagatorW C u tb φb) := by
    exact s102_propagator_classical ⟨fb, by simpa [C] using hfb⟩
  obtain ⟨Ba, hBa⟩ := s102_grad_bdd hFa
  obtain ⟨Bb, hBb⟩ := s102_grad_bdd hFb
  let Va : ℝ × Euc p.d → Euc p.d := fun q =>
    if q.1 ∈ Icc (0 : ℝ) ta then gradient (propagatorW C q.1 ta φa) q.2 else 0
  let Vb : ℝ × Euc p.d → Euc p.d := fun q =>
    if q.1 ∈ Icc (0 : ℝ) tb then gradient (propagatorW C q.1 tb φb) q.2 else 0
  have hVam : Measurable Va := by
    exact s102_gradJoint_meas hFa
  have hVbm : Measurable Vb := by
    exact s102_gradJoint_meas hFb
  let G : ℝ × Euc p.d → ℝ := fun q => inner ℝ (Va q) (Vb q)
  have hGm : Measurable G := by
    exact hVam.inner hVbm
  let η : ℝ → (Euc p.d → ℝ) → ℝ := fun u f => Real.sqrt N *
    (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ζ)) f -
      HRS.Whole.pair (r26t3_mu R u) f)
  let center : ℝ → ℝ := fun u =>
    ∫ x, G (u, x) ∂(HRS.Whole.withDensityReal (ρclip u))
  have hcenterm : Measurable center := by
    exact fp81s21_moving_spatial_integral_meas
      (ρ := ρclip) hρclip hρclip0
      (f := fun u x => G (u, x)) hGm
  have hsum : Measurable fun u : ℝ =>
      ∑ k : Fin N, G (u, X u.toNNReal ζ k) := by
    refine Finset.measurable_sum _ fun k _ => ?_
    have hpath : Measurable fun u : ℝ => X u.toNNReal ζ k :=
      ((hcz k).comp continuous_real_toNNReal).measurable
    exact hGm.comp (measurable_id.prodMk hpath)
  let F : ℝ → ℝ := fun u => Real.sqrt N *
    ((N : ℝ)⁻¹ * ∑ k : Fin N, G (u, X u.toNNReal ζ k) - center u)
  have hFm : Measurable F := by
    exact measurable_const.mul ((measurable_const.mul hsum).sub hcenterm)
  have hEq : ∀ u ∈ Icc (0 : ℝ) (min ta tb),
      η u (fun x => inner ℝ (gradient (propagatorW C u ta φa) x)
        (gradient (propagatorW C u tb φb) x)) = F u := by
    intro u hu
    have huTa : u ∈ Icc (0 : ℝ) ta := ⟨hu.1, hu.2.trans (min_le_left _ _)⟩
    have huTb : u ∈ Icc (0 : ℝ) tb := ⟨hu.1, hu.2.trans (min_le_right _ _)⟩
    have huT : u ∈ Icc (0 : ℝ) T :=
      ⟨hu.1, le_trans hu.2 ((min_le_left ta tb).trans hta.2)⟩
    have hGslice : (fun x => inner ℝ
        (gradient (propagatorW C u ta φa) x)
        (gradient (propagatorW C u tb φb) x)) = fun x => G (u, x) := by
      funext x
      simp only [G, Va, Vb, if_pos huTa, if_pos huTb]
    have hclipEq : ρclip u = R.ρ u := by
      funext x
      change R.ρ (max 0 (min u T)) x = R.ρ u x
      simp [max_eq_right hu.1, min_eq_left huT.2]
    have hμ : HRS.Whole.withDensityReal (ρclip u) = r26t3_mu R u := by
      rw [hclipEq]
      rfl
    have hpair : HRS.Whole.pair (r26t3_mu R u) (fun x => G (u, x)) = center u := by
      rw [← hμ]
      rfl
    simp only [η, F, HRS.Whole.pair_empirical hN, hGslice, hpair]
  refine hFm.aemeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2
    (Eventually.of_forall fun u hu => (hEq u hu).symm)

/-!
The remaining consumer obligations are intentionally not packaged as proved here: (i) a uniform
particle-expectation bound for the moving envelope from `HasR2ActualDensity` plus the moving
particle moment, followed by its time × probability integrability; and (ii) moving cylindrical
`cylA`/`cylJ` integrability and the outcome-measurability results of Aux116-117. The generic
total-integral measurability theorem and `R2JIntegrandMeas` supply the corresponding measurability
components proved here, but not those independent bounds or the outcome-measurability wrappers.
-/

#print axioms HRS.Fp81.S21.fp81s21_moving_spatial_integral_meas
#print axioms HRS.Fp81.S21.fp81s21_moving_density_joint_meas
#print axioms HRS.Fp81.S21.fp81s21_moving_pairEnergy_joint_meas
#print axioms HRS.Fp81.S21.fp81s21_moving_envelope_joint_meas
#print axioms HRS.Fp81.S21.fp81s21_moving_total_integral_meas
#print axioms HRS.Fp81.S21.fp81s21_moving_envelope_rows_integrable
#print axioms HRS.Fp81.S21.fp81s21_moving_eta_JIntegrandMeas

end HRS.Fp81.S21

end
