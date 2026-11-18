import HRS.MS.Fp81S21RespRecon19
import HRS.MS.Fp81S21InitRecon
import HRS.MS.Fp81S21InitialIid
import HRS.MS.S21H2_S30C
import HRS.MS.R2InterpAux13

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc cbNorm)
open HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas HRS.MS.S21E HRS.MS.S21

/-- At zero preparation strength the actual response vector is the iid
centered feature vector under the actual initial law. -/
theorem fp81s21_respIid_vector_eq_centered
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) (a : ℝ) (ha : 0 ≤ a)
    (x : Euc p.d)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a)) :
    fp81s21_initial_ellv R (r26t3_qwin R a) x =
      s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_s09_prob hδ hδh R
  apply lp.ext (funext fun j => ?_)
  have hmem := s21h2_memℓp hq (r26t3_mu R 0) x
  have hleft : Memℓp (fun k => r26t3_a R (r26t3_qwin R a k) x) 2 := by
    rw [show (fun k => r26t3_a R (r26t3_qwin R a k) x) =
        (fun k => r26t3_qwin R a k x - HRS.Whole.pair
          (r26t3_mu R 0) (r26t3_qwin R a k)) by
          funext k
          exact fp81s21_initial_iid_response (R := R) hγ
            (r26t3_qwin R a k) x]
    exact hmem
  change SeqL2.coord (SeqL2.ofSeq
      (fun k => r26t3_a R (r26t3_qwin R a k) x)) j =
    SeqL2.coord (s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x) j
  rw [S45.s45_coord_ofSeq hleft j,
    s21h2_coord hq (r26t3_mu R 0) x j]
  exact fp81s21_initial_iid_response (R := R) hγ
    (r26t3_qwin R a j) x

/-- The centered endpoint response vector has the deterministic feature-sum
bound required by the path and tensor transports. -/
theorem fp81s21_respIid_vector_bounds
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) (a : ℝ) (ha : 0 ≤ a)
    (x : Euc p.d)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a)) :
    Memℓp (fun j => r26t3_a R (r26t3_qwin R a j) x) 2 ∧
    (∀ j, SeqL2.coord (fp81s21_initial_ellv R (r26t3_qwin R a) x) j =
      r26t3_a R (r26t3_qwin R a j) x) ∧
    ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ ≤
      2 * featureSum (r26t3_J p.d) (r26t3_qwin R a) := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_s09_prob hδ hδh R
  have hy := s21h2_memℓp hq (r26t3_mu R 0) x
  have hmem : Memℓp (fun k => r26t3_a R (r26t3_qwin R a k) x) 2 := by
    rw [show (fun k => r26t3_a R (r26t3_qwin R a k) x) =
      (fun k => r26t3_qwin R a k x - HRS.Whole.pair
        (r26t3_mu R 0) (r26t3_qwin R a k)) by
          funext k
          exact fp81s21_initial_iid_response (R := R) hγ
            (r26t3_qwin R a k) x]
    exact hy
  have hcoord : ∀ j, SeqL2.coord
      (fp81s21_initial_ellv R (r26t3_qwin R a) x) j =
        r26t3_qwin R a j x - HRS.Whole.pair
          (r26t3_mu R 0) (r26t3_qwin R a j) := by
    intro j
    unfold fp81s21_initial_ellv
    rw [S45.s45_coord_ofSeq hmem j]
    exact fp81s21_initial_iid_response (R := R) hγ
      (r26t3_qwin R a j) x
  have hnorm := S45.s45_norm_le_tsum
    (z := fp81s21_initial_ellv R (r26t3_qwin R a) x) (hq.2.mul_left 2) (fun j => by
    rw [hcoord j]
    exact s21h2_abs_le hq (r26t3_mu R 0) x j)
  refine ⟨?_, ?_, ?_⟩
  · exact hmem
  · intro j
    rw [hcoord j]
    exact (fp81s21_initial_iid_response (R := R) hγ
      (r26t3_qwin R a j) x).symm
  · calc
      ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ ≤
          ∑' j, 2 * cbNorm (r26t3_J p.d) (r26t3_qwin R a j) := hnorm
      _ = 2 * featureSum (r26t3_J p.d) (r26t3_qwin R a) := by
          rw [featureSum, ← tsum_mul_left]

/-- The endpoint response vector is continuous and has an integrable cubic
norm under the actual one-particle initial law. -/
theorem fp81s21_respIid_vector_regular
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) (a : ℝ) (ha : 0 ≤ a)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a)) :
    Continuous (fp81s21_initial_ellv R (r26t3_qwin R a)) ∧
    Integrable (fun x => ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ *
      ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ *
      ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖) (r26t3_mu R 0) := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_s09_prob hδ hδh R
  have hvec := fp81s21_respIid_vector_eq_centered hδ hδh R hγ a ha
    (0 : Euc p.d) hq
  have hcont : Continuous (s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0)) :=
    s21h2_continuous hq (r26t3_mu R 0)
  have hYcont : Continuous (fun x =>
      fp81s21_initial_ellv R (r26t3_qwin R a) x) := by
    rw [show fp81s21_initial_ellv R (r26t3_qwin R a) =
      s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) from funext fun x =>
        fp81s21_respIid_vector_eq_centered hδ hδh R hγ a ha x hq]
    exact hcont
  obtain ⟨C, hC⟩ := s21h2_norm_le hq (r26t3_mu R 0)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine ⟨hYcont, ?_⟩
  have hnorm : Continuous (fun x =>
      ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖) := hYcont.norm
  apply Integrable.of_bound (C := C * C * C)
  · exact ((hnorm.mul hnorm).mul hnorm).aestronglyMeasurable
  · filter_upwards with x
    have hv := hC x
    have hv0 : 0 ≤ ‖s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x‖ := norm_nonneg _
    rw [show fp81s21_initial_ellv R (r26t3_qwin R a) x =
      s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x from
        fp81s21_respIid_vector_eq_centered hδ hδh R hγ a ha x hq]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hv0 hv0) hv0)]
    calc
      ‖s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x‖ *
          ‖s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x‖ *
          ‖s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x‖ ≤
          C * C * ‖s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0) x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul hv hv hv0 hC0) hv0
      _ ≤ C * C * C := mul_le_mul_of_nonneg_left hv (mul_nonneg hC0 hC0)

private theorem fp81s21_respIid_initial_moment
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) :
    Integrable (fun x : Euc p.d =>
      HRS.Whole.jbracket x ^ (wholeSpaceIndex p.d : ℝ)) (r26t3_mu R 0) := by
  obtain ⟨-, -, hdensity, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href (wholeSpaceIndex p.d)
  have hgauss : HRS.Whole.HasR2GaussianUpper M c (R.ρ 0) := ⟨hc, hTc.gauss⟩
  obtain ⟨CM, hCM⟩ := HRS.MS.R2Chaos.s94_moment_rpow hTc.prob hgauss
    (a := (wholeSpaceIndex p.d : ℝ)) (by positivity)
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu (hdensity 0 le_rfl).1
  let f : Euc p.d → ℝ := fun x => HRS.Whole.jbracket x ^ (wholeSpaceIndex p.d : ℝ)
  have hfmeas : Measurable f := by
    dsimp [f]
    exact (((by
      unfold HRS.Whole.jbracket
      fun_prop : Continuous fun x : Euc p.d => HRS.Whole.jbracket x).rpow_const
        (fun x => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne')).measurable)
  have hfnonneg : ∀ x, 0 ≤ f x := fun x => Real.rpow_nonneg
    (by have := HRS.MS.R2Poly.s95_one_le_jb x; positivity) _
  refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfnonneg)]
  exact lt_of_le_of_lt hCM ENNReal.ofReal_lt_top

private theorem fp81s21_respIid_functional_S102Z
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) (x : Euc p.d) :
    S102Z (2 * p.d + 8) (wholeSpaceIndex p.d : ℝ)
      (fun f => r26t3_a R f x) := by
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hP0 : 0 ≤ (wholeSpaceIndex p.d : ℝ) := by positivity
  have hr : (p.d : ℝ) / 2 < (2 * p.d + 8 : ℕ) := by
    push_cast
    nlinarith [show 0 ≤ (p.d : ℝ) by positivity]
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let X : EucConfig p.d 1 := fun _ => x
  have hpair : ∀ f : Euc p.d → ℝ, HRS.Whole.pair (HRS.Whole.empirical X) f = f x := by
    intro f
    rw [HRS.Whole.pair_empirical (by norm_num) X f]
    simp [X]
  have hZ := HRS.MS.R2Interp.s102_Z_fluct hd1 hP0 (2 * p.d + 8) hr
    (N := 1) (by norm_num) X μ
    (fp81s21_respIid_initial_moment hδ hδh R) 1
  have heq : (fun f => r26t3_a R f x) =
      (fun f => 1 * (HRS.Whole.pair (HRS.Whole.empirical X) f -
        HRS.Whole.pair μ f)) := by
    funext f
    rw [fp81s21_initial_iid_response R hγ f x, hpair f]
    ring
  rw [heq]
  exact hZ

/-- The endpoint response evaluation is an admissible weighted functional on
the test class used to construct the propagated oscillator vector. -/
theorem fp81s21_respIid_functional_admissible
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) (x : Euc p.d) :
    S102Z (2 * p.d + 8) (wholeSpaceIndex p.d : ℝ)
      (fun f => r26t3_a R f x) :=
  fp81s21_respIid_functional_S102Z hδ hδh R hγ x

private theorem fp81s21_respIid_S102Lin
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {H : ℝ} :
    S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H := by
  intro u t hu hut _ φ ψ c hφ hψ
  have h := fp81s21_U_linear_of_hermite_combo p R hφ hψ c
    (t := t) (r := u) (le_trans hu hut) ⟨hu, hut⟩
  have hfun : φ + c • ψ = (fun x => φ x + c * ψ x) := by
    funext x
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  funext x
  change propagatorW (r26t3_coeff R) u t (φ + c • ψ) x = _
  rw [hfun]
  exact congrFun h x

/-- At zero preparation strength, the response window is genuine: the
oscillator vector obtained from the response functional has the propagated
test coordinates at every spatial point and every window time. -/
theorem fp81s21_respIid_responseWindow_genuine (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        p.γ = 0 → ∀ b : ℝ, (hb : 0 ≤ b) → ∀ x : Euc p.d,
          ∃ hpath : Continuous (fun t : Icc (0 : ℝ) p.T =>
              r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
                (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)),
            responseWindow R b x =
              (⟨fun t : Icc (0 : ℝ) p.T =>
                  r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
                    (b + (t : ℝ)) 0 (fun f => r26t3_a R f x),
                hpath⟩ : Window p) ∧
            (∀ t : Icc (0 : ℝ) p.T, ∀ α : MultiIndex p.d,
              OscDual.coord (OscPath.at' (responseWindow R b x) t) α =
                r26t3_a R (propagatorW (r26t3_coeff R) 0
                  (b + (t : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x) := by
  obtain ⟨δ0, hδ0, hδhalf, hOrbit⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R hγ b hb x => ?_⟩
  have hδh : δ ≤ 1 / 2 := hδle.trans hδhalf
  let H : ℝ := b + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, hb]
  obtain ⟨Co', co', hco', hcsum, horbits⟩ := hOrbit δ hδ hδle R
  have hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) (fp81s21_uniform_orbit_coefficient p Co') := horbits H hH
  have hP : (p.d : ℝ) < 2 * (wholeSpaceIndex p.d : ℝ) := by
    dsimp [HRS.Whole.wholeSpaceIndex]
    push_cast
    nlinarith [p.hd]
  have hz := fp81s21_respIid_functional_S102Z hδ hδh R hγ x
  have hlin := fp81s21_respIid_S102Lin R (H := H)
  have hu : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
  have hVcont := s102_Vprop_continuousOn hP hD hz hlin hu
  let θ : Icc (0 : ℝ) p.T → Icc (0 : ℝ) H := fun t =>
    ⟨b + (t : ℝ), ⟨add_nonneg hb t.2.1, by dsimp [H]; linarith [t.2.2]⟩⟩
  have hθ : Continuous θ := by
    change Continuous (fun t : Icc (0 : ℝ) p.T =>
      (⟨b + (t : ℝ), _⟩ : Icc (0 : ℝ) H))
    fun_prop
  have hpath : Continuous (fun t : Icc (0 : ℝ) p.T =>
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) (b + (t : ℝ)) 0
        (fun f => r26t3_a R f x)) := by
    change Continuous (fun t =>
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) (θ t) 0
        (fun f => r26t3_a R f x))
    exact (continuousOn_iff_continuous_restrict.mp hVcont).comp hθ
  have hWindow : responseWindow R b x =
      (⟨fun t : Icc (0 : ℝ) p.T =>
          r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (b + (t : ℝ)) 0 (fun f => r26t3_a R f x), hpath⟩ : Window p) := by
    unfold responseWindow windowPathOf
    exact dif_pos hpath
  refine ⟨hpath, hWindow, ?_⟩
  intro t α
  rw [hWindow]
  have ht : b + (t : ℝ) ∈ Icc (0 : ℝ) H := by
    constructor
    · linarith [hb, t.2.1]
    · dsimp [H]
      linarith [t.2.2]
  have hcoord := s102_Vprop_coord hP hD hz hlin hu ht α
  change (OscDual.coord
      (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (b + (t : ℝ)) 0 (fun f => r26t3_a R f x)) α) = _
  simpa [r26t3_U] using hcoord

#print axioms fp81s21_respIid_vector_eq_centered
#print axioms fp81s21_respIid_vector_bounds
#print axioms fp81s21_respIid_vector_regular
#print axioms fp81s21_respIid_functional_admissible
#print axioms fp81s21_respIid_responseWindow_genuine

end HRS.Fp81.S21
end
