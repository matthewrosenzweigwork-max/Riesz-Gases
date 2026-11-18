import HRS.MS.Fp81S21InitialWindow
import HRS.MS.Fp81S21InitialStein3
import HRS.MS.Fp81S21Uniform2
import HRS.MS.Fp81S21PropagatorOsc
import HRS.MS.R2InterpAux11

/-!
# S2.1(iii): genuine initial windows and oscillator coordinates

The actual preparation marginal has the moments needed for the weighted
Sobolev orbit argument.  The resulting coordinate majorant is square
summable, so `r2Vprop` and its `OscDual.ofSeq` are genuine vectors and the
`windowPathOf` fallback is not selected.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.CovMeas HRS.MS.R2Interp

private theorem fp81s21_initial_windowPathOf_eq {d : ℕ} {m T : ℝ}
    (f : ℝ → OscDual d m) (g : C(Icc (0 : ℝ) T, OscDual d m))
    (hg : ∀ t : Icc (0 : ℝ) T, f (0 + (t : ℝ)) = g t) :
    windowPathOf m T 0 f = (show OscPath d m T from g) := by
  have h : Continuous (fun t : Icc (0 : ℝ) T => f (0 + (t : ℝ))) :=
    g.continuous.congr fun t => (hg t).symm
  unfold windowPathOf
  simp only [h, ↓reduceDIte]
  apply ContinuousMap.ext
  intro t
  exact hg t

private theorem fp81s21_initial_mean_moment
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (E : InitialSteinEnv R) :
    Integrable (fun x : Euc p.d =>
      jbracket x ^ (wholeSpaceIndex p.d : ℝ))
      (HRS.Whole.meanEmpirical (r26t3_Q R N)) := by
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let P : Measure (EucConfig p.d N) := r26t3_Q R N
  let f : Euc p.d → ℝ := fun x => jbracket x ^ (wholeSpaceIndex p.d : ℝ)
  let S := E.static N hN
  haveI hμ : IsProbabilityMeasure μ :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hρupper : ∀ x : Euc p.d,
      R.ρ 0 x ≤ E.C * Real.exp (-E.c * ‖x‖ ^ 2) := by
    intro x
    exact (le_abs_self _).trans (E.reference.h0 x)
  have hgauss : HasR2GaussianUpper E.C E.c (R.ρ 0) :=
    ⟨E.reference.hc, hρupper⟩
  obtain ⟨CM, hCM⟩ := HRS.MS.R2Chaos.s94_moment_rpow
    E.reference.prob hgauss (a := (wholeSpaceIndex p.d : ℝ)) (by positivity)
  have hfmeas : Measurable f := by
    dsimp [f]
    exact (((by
      unfold jbracket
      fun_prop : Continuous fun x : Euc p.d => jbracket x).rpow_const
        (fun x => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne')).measurable)
  have hfnonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact Real.rpow_nonneg (by
      have := HRS.MS.R2Poly.s95_one_le_jb x
      positivity) _
  have hfμ : Integrable f μ := by
    refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfnonneg)]
    exact lt_of_le_of_lt hCM ENNReal.ofReal_lt_top
  obtain ⟨φ, hφm, hνeq, hφb, -, -⟩ := S.marg
  have hφnonneg : ∀ x, 0 ≤ φ x := fun x => (hφb x).1
  have hφμ : Integrable (fun x => φ x * f x) μ := by
    refine Integrable.mono' (hfμ.mul_const E.Cs)
      ((hφm.mul hfmeas).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφnonneg x) (hfnonneg x))]
    calc φ x * f x = f x * φ x := by ring
      _ ≤ f x * E.Cs := mul_le_mul_of_nonneg_left (hφb x).2 (hfnonneg x)
  have hνint : Integrable f
      ((μ).withDensity (fun x => ENNReal.ofReal (φ x))) := by
    rw [integrable_withDensity_iff_integrable_smul' hφm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    convert hφμ using 1
    funext x
    simp [smul_eq_mul, ENNReal.toReal_ofReal (hφnonneg x)]
  letI : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (r26t3_Q R N)
    rw [← E.law_eq N]
    exact S.prob
  have hmean : HRS.Whole.meanEmpirical P =
      (μ).withDensity (fun x => ENNReal.ofReal (φ x)) := by
    have hExch : HRS.Whole.IsExchangeable P := by
      change HRS.Whole.IsExchangeable (r26t3_Q R N)
      rw [← E.law_eq N]
      exact S.exch
    have hfirst : HRS.Whole.meanEmpirical P = HRS.Whole.firstMarginal P :=
      HRS.Whole.meanEmpirical_eq_firstMarginal P hExch (by omega)
    have hνP : S47.s47_nu p.d p.s (R.ρ 0) p.γ N = HRS.Whole.firstMarginal P := by
      change S47.s47_nu p.d p.s (R.ρ 0) p.γ N =
        HRS.Whole.firstMarginal (r26t3_Q R N)
      rw [← E.law_eq N]
    calc HRS.Whole.meanEmpirical P = HRS.Whole.firstMarginal P := hfirst
      _ = S47.s47_nu p.d p.s (R.ρ 0) p.γ N := hνP.symm
      _ = (μ).withDensity (fun x => ENNReal.ofReal (φ x)) := hνeq
  rw [show HRS.Whole.meanEmpirical (r26t3_Q R N) = HRS.Whole.meanEmpirical P by rfl, hmean]
  exact hνint

private theorem fp81s21_initial_functional_S102Z
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (hMoment : Integrable
      (fun x : Euc p.d => jbracket x ^ (wholeSpaceIndex p.d : ℝ))
      (HRS.Whole.meanEmpirical (r26t3_Q R N)))
    (X : EucConfig p.d N) :
    S102Z (2 * p.d + 8) (wholeSpaceIndex p.d : ℝ)
      (initialFunctional R N X) := by
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hP0 : 0 ≤ (wholeSpaceIndex p.d : ℝ) := by positivity
  have hdreal : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
  have hr : (p.d : ℝ) / 2 < (2 * p.d + 8 : ℕ) := by
    push_cast
    nlinarith [hdreal]
  have hNpos : 0 < N := by omega
  change S102Z (2 * p.d + 8) (wholeSpaceIndex p.d : ℝ)
    (fun f => Real.sqrt N *
      (HRS.Whole.pair (HRS.Whole.empirical X) f -
        HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N)) f))
  exact s102_Z_fluct hd1 hP0 (2 * p.d + 8) hr hNpos X
    (HRS.Whole.meanEmpirical (r26t3_Q R N)) hMoment (Real.sqrt N)

private theorem fp81s21_initial_S102Lin
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {H : ℝ} :
    S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H := by
  intro u t hu hut _ht φ ψ c hφ hψ
  have h := fp81s21_U_linear_of_hermite_combo p R hφ hψ c
    (t := t) (r := u) (le_trans hu hut) ⟨hu, hut⟩
  have hfun : φ + c • ψ = (fun x => φ x + c * ψ x) := by
    funext x
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  funext x
  change propagatorW (r26t3_coeff R) u t (φ + c • ψ) x = _
  rw [hfun]
  exact congrFun h x

private theorem fp81s21_initial_r2InitFun_eq_Vprop
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (H : ℝ)
    {c : MultiIndex p.d → ℝ}
    (hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
    (hZ : ∀ X : EucConfig p.d N,
      S102Z (2 * p.d + 8) (wholeSpaceIndex p.d : ℝ)
        (initialFunctional R N X))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) H) (X : EucConfig p.d N) :
    r2InitFun (r26t3_coeff R) (wholeSpaceIndex p.d)
        (r26t3_Q R N) X s =
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) s 0
        (initialFunctional R N X) := by
  have hP : (p.d : ℝ) < 2 * (wholeSpaceIndex p.d : ℝ) := by
    dsimp [HRS.Whole.wholeSpaceIndex]
    push_cast
    nlinarith [p.hd]
  have hH : 0 ≤ H := hs.1.trans hs.2
  have hu : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH⟩
  apply HRS.MS.CovMeas.s101_ellVec_ext
  intro α
  have hmem := s102_z_orbit_memℓp hP hD (hZ X)
    (u := 0) hu hs
  change OscDual.coord
      (ellVec (wholeSpaceIndex p.d)
        (fun β => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X)
              (propagatorW (r26t3_coeff R) 0 s
                (oscTestFun (wholeSpaceIndex p.d) β)) -
            HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N))
              (propagatorW (r26t3_coeff R) 0 s
                (oscTestFun (wholeSpaceIndex p.d) β))))) α =
    OscDual.coord
      (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) s 0
        (initialFunctional R N X)) α
  rw [HRS.MS.CovMeas.s101_ellVec_coord (by
    simpa [initialFunctional] using hmem)]
  rw [s102_Vprop_coord hP hD (hZ X) hlin
    (u := 0) hu hs α]
  rfl

/-- For a radius chosen before the trajectory, every configuration has a
genuine initial window.  The coordinate formula is the exact `r2InitFun`
formula, and `r2Vprop` equals `r2InitFun` as an oscillator vector whenever
the scalar sequence is in `ℓ²`; that compatibility is proved here from the
same Sobolev orbit majorant. -/
theorem fp81s21_initialWindow_genuine (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        0 < p.γ → ∀ N : ℕ, 2 ≤ N → ∀ b : ℝ, (hb : 0 ≤ b) →
          ∀ X : EucConfig p.d N,
            ∃ hpath : Continuous (fun t : Icc (0 : ℝ) p.T =>
                r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
                  (b + (t : ℝ)) 0 (initialFunctional R N X)),
              initialWindow R N b X =
                (⟨fun t : Icc (0 : ℝ) p.T =>
                    r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
                      (b + (t : ℝ)) 0 (initialFunctional R N X),
                  hpath⟩ : Window p) ∧
              (∀ t : Icc (0 : ℝ) p.T, ∀ α : MultiIndex p.d,
                OscDual.coord (OscPath.at' (initialWindow R N b X) t) α =
                  Real.sqrt N *
                    (HRS.Whole.pair (HRS.Whole.empirical X)
                        (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
                          (oscTestFun (wholeSpaceIndex p.d) α)) -
                      HRS.Whole.pair
                        (HRS.Whole.meanEmpirical (r26t3_Q R N))
                        (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
                          (oscTestFun (wholeSpaceIndex p.d) α)))) ∧
              (∀ s : ℝ, s ∈ Icc (0 : ℝ) (b + p.T) →
                r2InitFun (r26t3_coeff R) (wholeSpaceIndex p.d)
                    (r26t3_Q R N) X s =
                  r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) s 0
                    (initialFunctional R N X)) ∧
              HRS.MS.ProClosureS111.physicalWindowRestriction
                  (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
                  (u := b) (H := b + p.T) hb le_rfl
                  (r2InitPath (r26t3_coeff R) (wholeSpaceIndex p.d)
                    (b + p.T) (r26t3_Q R N) X) =
                initialWindow R N b X := by
  classical
  obtain ⟨δ0, hδ0, hδhalf, hOrbit⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R hγ N hN b hb X => ?_⟩
  have hδhalf' : δ ≤ 1 / 2 := hδle.trans hδhalf
  obtain ⟨Co, co, hco, hcsum, horbits⟩ := hOrbit δ hδ hδle R
  let H : ℝ := b + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, hb]
  have hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) (fp81s21_uniform_orbit_coefficient p Co) := horbits H hH
  obtain ⟨E⟩ := initialSteinEnv_exists hδ hδhalf' R hγ
  have hMoment := fp81s21_initial_mean_moment R hN E
  have hP : (p.d : ℝ) < 2 * (wholeSpaceIndex p.d : ℝ) := by
    dsimp [HRS.Whole.wholeSpaceIndex]
    push_cast
    nlinarith [p.hd]
  have hZ : ∀ X : EucConfig p.d N,
      S102Z (2 * p.d + 8) (wholeSpaceIndex p.d : ℝ)
        (initialFunctional R N X) := fun X =>
          fp81s21_initial_functional_S102Z R hN hMoment X
  have hlin := fp81s21_initial_S102Lin R (H := H)
  let z : (Euc p.d → ℝ) → ℝ := initialFunctional R N X
  have hVcont : ContinuousOn
      (fun s => r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) s 0 z)
      (Icc (0 : ℝ) H) :=
    s102_Vprop_continuousOn hP hD (hZ X) hlin
      (u := 0) ⟨le_rfl, hH.le⟩
  let θ : Icc (0 : ℝ) p.T → Icc (0 : ℝ) H := fun t =>
    ⟨b + (t : ℝ), ⟨add_nonneg hb t.2.1, by
      dsimp [H]
      linarith [t.2.2]⟩⟩
  have hθ : Continuous θ := by
    change Continuous (fun t : Icc (0 : ℝ) p.T =>
      (⟨b + (t : ℝ), _⟩ : Icc (0 : ℝ) H))
    fun_prop
  have hpath : Continuous (fun t : Icc (0 : ℝ) p.T =>
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (b + (t : ℝ)) 0 z) := by
    change Continuous (fun t =>
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) (θ t) 0 z)
    exact (continuousOn_iff_continuous_restrict.mp hVcont).comp hθ
  have hWindow : initialWindow R N b X =
      (⟨fun t : Icc (0 : ℝ) p.T =>
          r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (b + (t : ℝ)) 0 (initialFunctional R N X), hpath⟩ : Window p) := by
    unfold initialWindow windowPathOf
    change (if h : Continuous (fun t : Icc (0 : ℝ) p.T =>
        r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (b + (t : ℝ)) 0 (initialFunctional R N X)) then
        (⟨fun t : Icc (0 : ℝ) p.T =>
          r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (b + (t : ℝ)) 0 (initialFunctional R N X), h⟩ : Window p)
      else 0) = _
    exact dif_pos hpath
  refine ⟨hpath, hWindow, ?_, ?_, ?_⟩
  · intro t α
    rw [hWindow]
    change OscDual.coord
      (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (b + (t : ℝ)) 0 (initialFunctional R N X)) α = _
    have hs : b + (t : ℝ) ∈ Icc (0 : ℝ) H := by
      constructor
      · linarith [hb, t.2.1]
      · dsimp [H]
        linarith [t.2.2]
    have hcoord := s102_Vprop_coord hP hD (hZ X) hlin
      (u := 0) ⟨le_rfl, hH.le⟩ hs α
    rw [hcoord]
    exact fp81s21_initial_functional_formula R N X (b + (t : ℝ)) α
  · intro s hs
    exact fp81s21_initial_r2InitFun_eq_Vprop R hN H
      (c := fp81s21_uniform_orbit_coefficient p Co) hD hlin hZ hs X
  · have hEq :
        (fun s : Icc (0 : ℝ) H =>
          r2InitFun (r26t3_coeff R) (wholeSpaceIndex p.d)
            (r26t3_Q R N) X (s : ℝ)) =
        (fun s : Icc (0 : ℝ) H =>
          r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (s : ℝ) 0 (initialFunctional R N X)) := by
      funext s
      exact fp81s21_initial_r2InitFun_eq_Vprop R hN H
        (c := fp81s21_uniform_orbit_coefficient p Co) hD hlin hZ
        s.property X
    have hlongcont : Continuous (fun s : Icc (0 : ℝ) H =>
        r2InitFun (r26t3_coeff R) (wholeSpaceIndex p.d)
          (r26t3_Q R N) X (s : ℝ)) := by
      rw [hEq]
      exact (continuousOn_iff_continuous_restrict.mp hVcont)
    have hlongShift : Continuous (fun s : Icc (0 : ℝ) H =>
        r2InitFun (r26t3_coeff R) (wholeSpaceIndex p.d)
          (r26t3_Q R N) X (0 + (s : ℝ))) := by
      simpa only [zero_add] using hlongcont
    have hLongPath :
        r2InitPath (r26t3_coeff R) (wholeSpaceIndex p.d) H
          (r26t3_Q R N) X =
        (⟨fun s : Icc (0 : ℝ) H =>
          r2InitFun (r26t3_coeff R) (wholeSpaceIndex p.d)
            (r26t3_Q R N) X (0 + (s : ℝ)), hlongShift⟩ :
          OscPath p.d (wholeSpaceIndex p.d) H) := by
      exact fp81s21_initial_windowPathOf_eq
        (m := wholeSpaceIndex p.d) (T := H)
        (r2InitFun (r26t3_coeff R) (wholeSpaceIndex p.d)
          (r26t3_Q R N) X)
        (⟨fun s : Icc (0 : ℝ) H =>
          r2InitFun (r26t3_coeff R) (wholeSpaceIndex p.d)
            (r26t3_Q R N) X (0 + (s : ℝ)), hlongShift⟩)
        (fun _ => rfl)
    change HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
        (u := b) (H := H) hb (by dsimp [H]; rfl)
        (r2InitPath (r26t3_coeff R) (wholeSpaceIndex p.d) H
          (r26t3_Q R N) X) = initialWindow R N b X
    rw [hWindow]
    apply ContinuousMap.ext
    intro t
    change OscPath.at'
      (HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
        (u := b) (H := H) hb (by dsimp [H]; exact le_rfl)
        (r2InitPath (r26t3_coeff R) (wholeSpaceIndex p.d) H
          (r26t3_Q R N) X)) t =
      OscPath.at'
        (⟨fun t : Icc (0 : ℝ) p.T =>
          r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (b + (t : ℝ)) 0 (initialFunctional R N X), hpath⟩ : Window p) t
    rw [HRS.MS.ProClosureS111.physicalWindowRestriction_apply
      (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
      (u := b) (H := H) hb (by dsimp [H]; exact le_rfl)]
    rw [hLongPath]
    have hs : b + (t : ℝ) ∈ Icc (0 : ℝ) H := by
      constructor
      · linarith [hb, t.2.1]
      · dsimp [H]
        linarith [t.2.2]
    have hcompat := fp81s21_initial_r2InitFun_eq_Vprop R hN H
      (c := fp81s21_uniform_orbit_coefficient p Co) hD hlin hZ hs X
    change r2InitFun (r26t3_coeff R) (wholeSpaceIndex p.d)
        (r26t3_Q R N) X (0 + (b + (t : ℝ))) =
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (b + (t : ℝ)) 0 (initialFunctional R N X)
    simpa only [zero_add] using hcompat

/-- The restriction identity also holds almost surely under the exact initial
preparation law.  The preceding theorem proves the stronger pointwise
statement for every configuration. -/
theorem fp81s21_initialWindow_restriction_Q_ae (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        0 < p.γ → ∀ N : ℕ, 2 ≤ N → ∀ b : ℝ, (hb : 0 ≤ b) →
          ∀ᵐ X ∂(r26t3_Q R N),
            HRS.MS.ProClosureS111.physicalWindowRestriction
                (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
                (u := b) (H := b + p.T) hb le_rfl
                (r2InitPath (r26t3_coeff R) (wholeSpaceIndex p.d)
                  (b + p.T) (r26t3_Q R N) X) =
              initialWindow R N b X := by
  obtain ⟨δ0, hδ0, hδhalf, hpoint⟩ :=
    fp81s21_initialWindow_genuine p
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R hγ N hN b hb => ?_⟩
  exact Filter.Eventually.of_forall fun X => by
    rcases hpoint δ hδ hδle R hγ N hN b hb X with
      ⟨hpath, hWindow, hcoords, hcompat, hrestrict⟩
    exact hrestrict

#print axioms HRS.Fp81.S21.fp81s21_initialWindow_genuine
#print axioms HRS.Fp81.S21.fp81s21_initialWindow_restriction_Q_ae

end HRS.Fp81.S21

end
