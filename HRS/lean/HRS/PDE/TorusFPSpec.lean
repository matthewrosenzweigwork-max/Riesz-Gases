import HRS.PDE.TorusFPAdapter
import HRS.PDE.WellPosed
import HRS.Energy.StaticLimitGauss

/-!
# Packet D1 (specification): the Fokker–Planck equation on the torus `𝕋^n` with gradient drift

Context.  Proposition B.15 (`sde_entropy_law`, TeX M L12140-12235) needs, in Step 2 of its proof, the
following *global* parabolic theory for the smooth gradient SDE `dX = -∇U(X) dt + √(2κ) dW` on the
torus `𝕋^n`, `n = N d` (via the adapter `d1_configEquiv` of `HRS/PDE/TorusFPAdapter.lean`):

* **D1** (this file): the forward Fokker–Planck equation `∂_t u = κ Δu - div(b u)`, `b = -∇U`, is well
  posed for probability measures as initial data (existence, uniqueness in the class of narrowly
  continuous measure-valued weak solutions), its solution is smooth and nonnegative for positive time,
  it conserves mass, and it satisfies the weak maximum principle `c G ≤ u_0 ≤ C G ⇒ c G ≤ u_t ≤ C G`
  (`G = e^{-U/κ}`) and the entropy dissipation inequality of `B:eq:selected-regularized-entropy`.
* **D2** (separate packet): Itô duality identifies `Law(X_t)` with the D1 solution.  D2 proves that the
  laws are a `D1ConfigWeakSolution` (Itô for `φ(X_t)`, `φ ∈ C²`, `ito_formula_additive_time_independent`)
  and then uses `d1_config_law_eq` (uniqueness) below.
* **D3** (separate packet): the entropy statement `d1_fp_entropy`.

## Why gradient drift and smooth `U`

* For `b = -∇U` the equation is the Doob (ground state) transform of an existing, fully proved theory:
  `w = u/G` solves `∂_t w = κΔw - ∇U·∇w`, which is `forwardGen (d1_dyn κ U) (fun _ => 1)` of
  `HRS/PDE/ForwardEq.lean` (`M = 0`, `V = U`, `ν = κ`, no nonlocal term).  `adjoint_torus_classical`
  (`HRS/PDE/WellPosed.lean`, proved) therefore already provides the classical backward solution
  (`d1_backward_classical`, proved below).  This only covers `V ∈ C^{m+3}`, `m ≥ mStar n`; we state
  everything for `Torus.IsSmooth U`.  Proposition B.15 has `V ∈ C²`: packet E must mollify `V`
  (`V_δ → V` in `C²`, the entropy inequality passing to the limit by the same lower semicontinuity
  argument as Steps 3-4 of the TeX proof).  No smoothness of a general (non-gradient) vector field `b`
  is needed by B.15 and none is claimed here.
* `n = N d ≥ 1`.  (`adjoint_torus` needs `1 ≤ d`; regime R1 requires `s = 0 ≤ n - 2`, i.e. `n ≥ 2`, and
  for `n = 1` the regime R2a (`M = 0` is antisymmetric) is used instead.)

Status: statements marked `SPEC (sorried, to be reviewed)` are specifications only.  Proved here:
`d1_backwardGenerator_eq`, `d1_mass_conserved`, `d1_isProbabilityMeasure`, `d1_weakSolution_of_config`,
`d1_gen_config`, `d1_exists_regime`, `d1_backward_classical` (all with the three standard axioms) and
`d1_fp_unique` (duality with `d1_backward_classical` plus `d1_measure_ext_of_smooth`), and
`d1_config_law_eq` (proved from `d1_fp_unique`).  Sorried specs: `d1_fp_exists`,
`d1_fp_smooth`, `d1_fp_smooth_general` (optional), `d1_fp_comparison`, `d1_fp_entropy`, and the D2
helper `d1_isC12On_of_isC12Test`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

/-! ### Definitions -/

/-- The gradient drift `b = -∇U`. -/
def d1_gradDrift (U : Torus n → ℝ) : Torus n → Euc n := fun x => -(Torus.grad U x)

/-- The (backward) generator `L φ = κ Δφ + b·∇φ` of `dX = b dt + √(2κ) dW`. -/
def d1_gen (κ : ℝ) (b : Torus n → Euc n) (φ : Torus n → ℝ) (x : Torus n) : ℝ :=
  κ * Torus.laplacian φ x + inner ℝ (b x) (Torus.grad φ x)

/-- Measure-valued weak solutions of the forward equation `∂_t μ = L^* μ` on `[0,T]`: finite measures,
narrowly continuous in `t ∈ [0,T]`, and the weak formulation against time-dependent `C^{1,2}` test
functions on every `[0,τ]`, `τ ∈ [0,T]`: for `f` with time derivative `ft` in the class `IsC12Test τ f ft`
(`HRS/Stochastic/SelectedFlow.lean`; exactly the regularity of the classical backward solutions
`D1BackwardSolution`, and of what Itô's formula for `f(s, X_s)` needs)
`∫ f_τ dμ_τ = ∫ f_0 dμ_0 + ∫_0^τ ∫ (∂_s f + L f_s) dμ_s ds`.
Time-independent tests are the special case `f_s = φ`, `ft = 0` (`D1WeakSolution.eq_const`); using
time-dependent tests in the definition makes uniqueness a direct duality argument.  No mass or sign
condition: `∫ 1 dμ_t` is conserved (`d1_mass_conserved`). -/
structure D1WeakSolution (κ : ℝ) (b : Torus n → Euc n) (T : ℝ) (μ : ℝ → Measure (Torus n)) : Prop where
  finite : ∀ t ∈ Set.Icc 0 T, IsFiniteMeasure (μ t)
  narrow : ∀ ψ : Torus n → ℝ, Continuous ψ →
    ContinuousOn (fun t => ∫ x, ψ x ∂(μ t)) (Set.Icc 0 T)
  eqT : ∀ τ ∈ Set.Icc 0 T, ∀ f ft : ℝ → Torus n → ℝ, IsC12Test τ f ft →
    ∫ x, f τ x ∂(μ τ) = ∫ x, f 0 x ∂(μ 0) +
      ∫ s in Set.Icc 0 τ, ∫ x, (ft s x + d1_gen κ b (f s) x) ∂(μ s)

theorem d1_isC12Test_const {τ : ℝ} {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ) :
    IsC12Test τ (fun _ => φ) (fun _ _ => 0) where
  c2 _ _ := hφ
  cont_c2 j hj := by
    have h := hφ.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)
    exact h.comp continuous_snd
  time_deriv x r _ := hasDerivAt_const r (φ x)
  cont_time_deriv := continuous_const

/-- Time-independent `C²` tests (the form of the weak equation used by `IsMeanFieldSolution`). -/
theorem D1WeakSolution.eq_const {κ : ℝ} {b : Torus n → Euc n} {T : ℝ} {μ : ℝ → Measure (Torus n)}
    (h : D1WeakSolution κ b T μ) {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    ∫ x, φ x ∂(μ t) = ∫ x, φ x ∂(μ 0) + ∫ s in Set.Icc 0 t, ∫ x, d1_gen κ b φ x ∂(μ s) := by
  simpa using h.eqT t ht (fun _ => φ) (fun _ _ => 0) (d1_isC12Test_const hφ)

/-- The (unnormalised) Gibbs weight `G = exp(-U/κ)`, `κ = β⁻¹`. -/
def d1_gibbsWeight (κ : ℝ) (U : Torus n → ℝ) (x : Torus n) : ℝ := Real.exp (-(κ⁻¹ * U x))

/-- `G dx`. -/
def d1_gibbsRaw (κ : ℝ) (U : Torus n → ℝ) : Measure (Torus n) :=
  (volume : Measure (Torus n)).withDensity fun x => ENNReal.ofReal (d1_gibbsWeight κ U x)

/-- The normalised Gibbs measure `Z⁻¹ G dx`. -/
def d1_gibbsMeasure (κ : ℝ) (U : Torus n → ℝ) : Measure (Torus n) :=
  (∫⁻ x, ENNReal.ofReal (d1_gibbsWeight κ U x))⁻¹ • d1_gibbsRaw κ U

/-- The relative Fisher information `𝓘_G(P)` with `G = e^{-U/κ}` (`B:eq:selected-fisher-variational`,
TeX M L12205-12209, specialised to a smooth potential on the whole torus):
`sup_ζ ∫ (-2 Div ζ - 2 ζ·∇log G - |ζ|²) dP`, `ζ` smooth vector fields on `𝕋^n`, `∇ log G = -κ⁻¹ ∇U`.
(For `n = N d` and the regularised smooth interaction this is the packet-A0 generalisation of
`fisherInfo` with a potential argument; test fields supported off the collision set are a subclass.) -/
def d1_fisherInfo (κ : ℝ) (U : Torus n → ℝ) (P : Measure (Torus n)) : ℝ≥0∞ :=
  ⨆ (ζ : Torus n → Euc n) (_ : Torus.IsSmooth ζ),
    ENNReal.ofReal (∫ x, (-2 * Torus.div ζ x + 2 * κ⁻¹ * inner ℝ (ζ x) (Torus.grad U x)
      - ‖ζ x‖ ^ 2) ∂P)

/-! ### The dynamical data `M = 0`, `V = U`, `ν = κ` of `HRS/PDE` and the bridge to `d1_gen` -/

/-- The data of `HRS/PDE` encoding the generator `κΔ - ∇U·∇`: `s = 0`, `M = 0`, `V = U`, `invβ = κ`. -/
def d1_dyn (hn : 1 ≤ n) (κ : ℝ) (hκ : 0 ≤ κ) (U : Torus n → ℝ) : DynData n where
  s := 0
  M := 0
  V := U
  invβ := κ
  hs0 := le_rfl
  hsd := by exact_mod_cast hn
  hβ := hκ

theorem d1_backwardGenerator_eq (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) (U : Torus n → ℝ)
    (ρ φ : Torus n → ℝ) (x : Torus n) :
    backwardGenerator (d1_dyn hn κ hκ U) ρ φ x = d1_gen κ (d1_gradDrift U) φ x := by
  have h1 : meanFieldDrift (d1_dyn hn κ hκ U) ρ x = d1_gradDrift U x := by
    simp [meanFieldDrift, d1_dyn, d1_gradDrift, Torus.matVec]
  have h2 : ∀ j : Fin n, (convGradConv (periodicRieszGrad n (d1_dyn hn κ hκ U).s)
      (fun y => ρ y * (Torus.matVec (d1_dyn hn κ hκ U).M.transpose (Torus.grad φ y)) j) x) j = 0 := by
    intro j
    simp [convGradConv, d1_dyn, Torus.matVec]
  unfold backwardGenerator d1_gen
  rw [h1, Finset.sum_eq_zero fun j _ => h2 j]
  simp [d1_dyn]

/-! ### Mass conservation (proved) -/

theorem d1_mass_conserved {κ : ℝ} {b : Torus n → Euc n} {T : ℝ} {μ : ℝ → Measure (Torus n)}
    (h : D1WeakSolution κ b T μ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) : μ t Set.univ = μ 0 Set.univ := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  haveI := h.finite t ht
  haveI := h.finite 0 h0
  have hc : Torus.IsCk 2 (fun _ : Torus n => (1 : ℝ)) := by
    unfold Torus.IsCk Torus.lift
    exact contDiff_const
  have := h.eq_const hc ht
  have hgen : ∀ x : Torus n, d1_gen κ b (fun _ => (1 : ℝ)) x = 0 := by
    intro x
    have hl : Torus.laplacian (fun _ : Torus n => (1 : ℝ)) x = 0 := by
      have : Torus.lift (fun _ : Torus n => (1 : ℝ)) = fun _ => (1 : ℝ) := rfl
      simp [Torus.laplacian, this]
    have hg : Torus.grad (fun _ : Torus n => (1 : ℝ)) x = 0 := by
      have : Torus.lift (fun _ : Torus n => (1 : ℝ)) = fun _ => (1 : ℝ) := rfl
      simp [Torus.grad, this]
    simp [d1_gen, hl, hg]
  simp only [hgen, integral_zero, integral_const, smul_eq_mul, mul_one, add_zero] at this
  simp only [Measure.real] at this
  rwa [ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)] at this

theorem d1_isProbabilityMeasure {κ : ℝ} {b : Torus n → Euc n} {T : ℝ} {μ : ℝ → Measure (Torus n)}
    (h : D1WeakSolution κ b T μ) [IsProbabilityMeasure (μ 0)] {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    IsProbabilityMeasure (μ t) :=
  ⟨by rw [d1_mass_conserved h ht]; exact measure_univ⟩


/-! ### Measures are determined by smooth test functions (proved) -/

theorem d1_isSmooth_cosMode (k : Lattice n) : Torus.IsSmooth (Torus.cosMode k) := by
  unfold Torus.IsSmooth Torus.IsCk
  have : Torus.lift (Torus.cosMode k) = fun y => Real.cos (2 * Real.pi * Lattice.dot k y) :=
    funext fun y => Torus.cosMode_mk k y
  rw [this]
  refine Real.contDiff_cos.comp (contDiff_const.mul ?_)
  unfold Lattice.dot
  exact ContDiff.sum fun i _ => contDiff_const.mul (EuclideanSpace.proj i : Euc n →L[ℝ] ℝ).contDiff

theorem d1_isSmooth_sinMode (k : Lattice n) : Torus.IsSmooth (Torus.sinMode k) := by
  unfold Torus.IsSmooth Torus.IsCk
  have : Torus.lift (Torus.sinMode k) = fun y => Real.sin (2 * Real.pi * Lattice.dot k y) :=
    funext fun y => Torus.sinMode_mk k y
  rw [this]
  refine Real.contDiff_sin.comp (contDiff_const.mul ?_)
  unfold Lattice.dot
  exact ContDiff.sum fun i _ => contDiff_const.mul (EuclideanSpace.proj i : Euc n →L[ℝ] ℝ).contDiff

theorem d1_isSmooth_const (c : ℝ) : Torus.IsSmooth (fun _ : Torus n => c) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift
  exact contDiff_const

theorem d1_isSmooth_comb (a b : ℝ) {φ ψ : Torus n → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) : Torus.IsSmooth (fun x => a * φ x + b * ψ x) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := hφ
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ) := hψ
  exact (contDiff_const.mul h1).add (contDiff_const.mul h2)

/-- Real and imaginary parts of trigonometric polynomials are smooth. -/
theorem d1_smooth_re_im_of_mem_span (g : C(UnitAddTorus (Fin n), ℂ))
    (hg : g ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin n)))) :
    Torus.IsSmooth (fun x : Torus n => (g x).re) ∧ Torus.IsSmooth (fun x : Torus n => (g x).im) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    exact ⟨d1_isSmooth_cosMode k, d1_isSmooth_sinMode k⟩
  | zero =>
    have h0 : Torus.IsSmooth (fun _ : Torus n => (0 : ℝ)) := d1_isSmooth_const 0
    exact ⟨by simpa using h0, by simpa using h0⟩
  | add g h _ _ ihg ihh =>
    exact ⟨by simpa using d1_isSmooth_comb 1 1 ihg.1 ihh.1,
      by simpa using d1_isSmooth_comb 1 1 ihg.2 ihh.2⟩
  | smul c g _ ihg =>
    refine ⟨?_, ?_⟩
    · have e : (fun x : Torus n => ((c • g) x).re) = fun x => c.re * (g x).re + (-c.im) * (g x).im := by
        funext x; simp [ContinuousMap.smul_apply]; try ring
      rw [e]; exact d1_isSmooth_comb _ _ ihg.1 ihg.2
    · have e : (fun x : Torus n => ((c • g) x).im) = fun x => c.re * (g x).im + c.im * (g x).re := by
        funext x; simp [ContinuousMap.smul_apply]
      rw [e]; exact d1_isSmooth_comb _ _ ihg.2 ihg.1

/-- Uniform approximation of continuous functions by smooth ones. -/
theorem d1_exists_smooth_approx {f : Torus n → ℝ} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Torus n → ℝ, Torus.IsSmooth ψ ∧ ∀ x, |f x - ψ x| ≤ ε := by
  let F : C(UnitAddTorus (Fin n), ℂ) := ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp hf⟩
  have hF : F ∈ closure ((Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin n)))) :
      Set C(UnitAddTorus (Fin n), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, UnitAddTorus.span_mFourier_closure_eq_top]; trivial
  rw [Metric.mem_closure_iff] at hF
  obtain ⟨g, hg, hdist⟩ := hF ε hε
  refine ⟨fun x => (g x).re, (d1_smooth_re_im_of_mem_span g hg).1, fun x => ?_⟩
  have h1 : ‖F x - g x‖ ≤ ‖F - g‖ := ContinuousMap.norm_coe_le_norm (F - g) x
  have h2 : ‖F - g‖ < ε := by rwa [← dist_eq_norm]
  calc |f x - (g x).re| = |(F x - g x).re| := by simp [F]
    _ ≤ ‖F x - g x‖ := Complex.abs_re_le_norm _
    _ ≤ ε := (h1.trans h2.le)

/-- Finite measures on `𝕋^n` with the same integrals against all smooth functions are equal. -/
theorem d1_measure_ext_of_smooth {μ ν : Measure (Torus n)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ ψ : Torus n → ℝ, Torus.IsSmooth ψ → ∫ x, ψ x ∂μ = ∫ x, ψ x ∂ν) : μ = ν := by
  have h1 : μ.real Set.univ = ν.real Set.univ := by
    have := h (fun _ => 1) (d1_isSmooth_const 1)
    simpa [Measure.real] using this
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hc : Continuous f := f.continuous
  have key : ∀ ε : ℝ, 0 < ε → |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ 2 * ε * μ.real Set.univ := by
    intro ε hε
    obtain ⟨ψ, hψ, hψf⟩ := d1_exists_smooth_approx hc hε
    have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
    have hb : ∀ (ρ : Measure (Torus n)) [IsFiniteMeasure ρ],
        |∫ x, f x ∂ρ - ∫ x, ψ x ∂ρ| ≤ ε * ρ.real Set.univ := by
      intro ρ _
      rw [← integral_sub (f.integrable ρ) (hψc.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
      calc |∫ x, (f x - ψ x) ∂ρ| ≤ ∫ x, |f x - ψ x| ∂ρ := abs_integral_le_integral_abs
        _ ≤ ∫ _x, ε ∂ρ := integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _)
            (integrable_const ε) (ae_of_all _ hψf)
        _ = ε * ρ.real Set.univ := by simp [mul_comm]
    have hm := hb μ
    have hn := hb ν
    rw [← h1] at hn
    rw [h ψ hψ] at hm
    calc |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ |∫ x, f x ∂μ - ∫ x, ψ x ∂ν| + |∫ x, f x ∂ν - ∫ x, ψ x ∂ν| := by
          rw [← abs_neg (∫ x, f x ∂ν - ∫ x, ψ x ∂ν)]
          refine (abs_add_le _ _).trans' (le_of_eq ?_)
          congr 1; ring
      _ ≤ 2 * ε * μ.real Set.univ := by linarith
  have h0 : 0 ≤ μ.real Set.univ := measureReal_nonneg
  by_contra hne
  have hpos : 0 < |∫ x, f x ∂μ - ∫ x, f x ∂ν| := abs_pos.2 (sub_ne_zero.2 hne)
  by_cases hm0 : μ.real Set.univ = 0
  · have := key 1 one_pos
    rw [hm0] at this
    linarith
  · have hm' : 0 < μ.real Set.univ := lt_of_le_of_ne h0 (Ne.symm hm0)
    have := key (|∫ x, f x ∂μ - ∫ x, f x ∂ν| / (4 * μ.real Set.univ)) (by positivity)
    have e : 2 * (|∫ x, f x ∂μ - ∫ x, f x ∂ν| / (4 * μ.real Set.univ)) * μ.real Set.univ =
        |∫ x, f x ∂μ - ∫ x, f x ∂ν| / 2 := by field_simp; ring
    rw [e] at this
    linarith

/-! ### The backward equation: classical solutions (proved from `adjoint_torus_classical`) -/

theorem d1_exists_regime (hn : 1 ≤ n) :
    ∃ R : PDE.Regime, ∀ (M : Matrix (Fin n) (Fin n) ℝ), M = 0 → ∀ (invβ ν₀ T : ℝ)
      (μ : ℝ → Torus n → ℝ), R.Holds n 0 M invβ ν₀ T μ := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have hn1 : n = 1 := by omega
    subst hn1
    refine ⟨.R2a, fun M hM _ _ _ _ => ?_⟩
    subst hM
    refine ⟨by norm_num, ?_⟩
    simp [Torus.symPart]
  · exact ⟨.R1, fun M _ _ _ _ _ => by
      show (0 : ℝ) ≤ (n : ℝ) - 2
      have : (2 : ℝ) ≤ n := by exact_mod_cast h
      linarith⟩



/-- Classical solutions of the backward equation `∂_r f + L f = 0`, `f(t) = φ`, with `L = d1_gen κ b`
(the structure of `IsClassicalAdjointSolution` in the `d1_gen` form). -/
structure D1BackwardSolution (κ : ℝ) (b : Torus n → Euc n) (t : ℝ) (φ : Torus n → ℝ)
    (f : ℝ → Torus n → ℝ) : Prop where
  c2 : ∀ r ∈ Set.Icc 0 t, Torus.IsCk 2 (f r)
  cont_c2 : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) t × Euc n =>
    iteratedFDeriv ℝ j (Torus.lift (f p.1)) p.2
  terminal : f t = φ
  time_deriv : ∀ x : Torus n, ∀ r ∈ Set.Ioo 0 t,
    HasDerivAt (fun r' => f r' x) (-(d1_gen κ b (f r) x)) r
  cont_time_deriv : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n => d1_gen κ b (f p.1) p.2

/-- **Classical backward solutions (proved)**: for smooth `U`, smooth terminal datum `φ` and `t > 0`
there is `f ∈ C([0,t]; C²)` with `∂_r f = -(κΔf - ∇U·∇f)`, `f(t) = φ`.  This is
`adjoint_torus_classical` with `D = d1_dyn κ U` (`M = 0`) and the constant density path `μ ≡ 1`.
(`f = U^{·,t}φ` is the Markov semigroup applied to `φ`; this is the dual object used for uniqueness,
positivity, and for Itô duality in D2: `E φ(X_t) = ∫ f(0) dLaw(X_0)`.) -/
theorem d1_backward_classical (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {t : ℝ} (ht : 0 < t) {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ f : ℝ → Torus n → ℝ, D1BackwardSolution κ (d1_gradDrift U) t φ f := by
  classical
  set m : ℕ := PDE.mStar n with hm
  obtain ⟨R, hR⟩ := d1_exists_regime hn
  have hs0 : (0 : ℝ) ≤ 0 := le_rfl
  have hsd : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨C, Cs, -, -, h⟩ := PDE.adjoint_torus_classical hn 0 hs0 hsd m le_rfl R 0
    (Torus.cbNorm (m + 3) (fun _ : Torus n => (1 : ℝ))) (Torus.cbNorm (m + 3) U)
  have hle : ((m : WithTop ℕ∞) + 3 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h0 : (((m + 3 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.2 le_top
    push_cast at h0 ⊢
    exact h0
  have hUm : Torus.IsCk ((m : WithTop ℕ∞) + 3) U :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift U) from hU).of_le hle
  have hconst : Torus.IsCk ((m : WithTop ℕ∞) + 3) (fun _ : Torus n => (1 : ℝ)) := by
    unfold Torus.IsCk Torus.lift
    exact contDiff_const
  let D := d1_dyn hn κ hκ.le U
  have hA : PDE.AdjointData 0 m R 0 (Torus.cbNorm (m + 3) (fun _ : Torus n => (1 : ℝ)))
      (Torus.cbNorm (m + 3) U) D 0 t (fun _ _ => (1 : ℝ)) :=
    { hs := rfl
      hM := fun i j => by simp [PDE.MatBound, D, d1_dyn]
      hV := ⟨hUm, le_rfl⟩
      hμ := { prob := fun r _ => ⟨fun _ => zero_le_one, measurable_const, by simp⟩
              smooth := fun r _ => hconst
              bound := fun r _ => le_rfl
              cont := fun ψ _ => by simpa using continuousOn_const }
      hT := ht
      regime := hR D.M rfl D.invβ 0 t _ }
  have hcont : Continuous φ := StaticLimitAux.continuous_of_smooth hφ
  have hmem : MemSobolev (m : ℝ) φ :=
    ⟨hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
      StaticLimitAux.summable_weighted_smooth (m : ℝ) hφ⟩
  obtain ⟨hcl, -⟩ := h D 0 t (fun _ _ => (1 : ℝ)) hA t ⟨ht, le_rfl⟩ φ hcont hmem
  refine ⟨fun r x => PDE.toFun (PDE.propagatorCoeff D (fun _ _ => (1 : ℝ)) m t (PDE.coeffOf φ) (t - r)) x, ?_⟩
  have hgen : ∀ (g : Torus n → ℝ) (x : Torus n),
      backwardGenerator D (fun _ => (1 : ℝ)) g x = d1_gen κ (d1_gradDrift U) g x :=
    fun g x => d1_backwardGenerator_eq hn hκ.le U _ g x
  refine ⟨hcl.c2, hcl.cont_c2, hcl.terminal, fun x r hr => ?_, ?_⟩
  · have := hcl.time_deriv x r hr
    rwa [hgen] at this
  · exact hcl.cont_time_deriv.congr fun p => hgen _ _

theorem D1BackwardSolution.isC12Test {κ : ℝ} {b : Torus n → Euc n} {t : ℝ} {φ : Torus n → ℝ}
    {f : ℝ → Torus n → ℝ} (h : D1BackwardSolution κ b t φ f) :
    IsC12Test t f (fun r x => -(d1_gen κ b (f r) x)) where
  c2 := h.c2
  cont_c2 := h.cont_c2
  time_deriv := h.time_deriv
  cont_time_deriv := h.cont_time_deriv.neg

/-- **Uniqueness (proved).**  Measure-valued weak solutions with the same initial datum coincide:
duality with the classical backward solution `d1_backward_classical` of terminal datum `ψ` and
`eqT` give `∫ ψ dμ_τ = ∫ (U^{0,τ}ψ) dμ_0`; smooth functions determine finite measures
(`d1_measure_ext_of_smooth`).  Uniqueness holds in the class `D1WeakSolution`: finite nonnegative
measure-valued, narrowly continuous on `[0,T]` solutions against time-dependent `IsC12Test` tests, the class
that D2 produces (D2 owes the time-dependent Itô formula for `Φ(s, X_s)` with mean-zero martingale part,
via `IsC12On` and `d1_isC12On_of_isC12Test`). -/
theorem d1_fp_unique (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} {μ ν : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) (hν : D1WeakSolution κ (d1_gradDrift U) T ν)
    (h0 : μ 0 = ν 0) : ∀ t ∈ Set.Icc 0 T, μ t = ν t := by
  intro τ hτ
  rcases hτ.1.eq_or_lt with rfl | hτpos
  · exact h0
  haveI := hμ.finite τ hτ
  haveI := hν.finite τ hτ
  refine d1_measure_ext_of_smooth fun ψ hψ => ?_
  obtain ⟨f, hf⟩ := d1_backward_classical hn hκ hU hτpos hψ
  have hC := hf.isC12Test
  have e1 := hμ.eqT τ hτ f _ hC
  have e2 := hν.eqT τ hτ f _ hC
  have hz : ∀ (ρ : ℝ → Measure (Torus n)), ∀ s : ℝ,
      ∫ x, (-(d1_gen κ (d1_gradDrift U) (f s) x) + d1_gen κ (d1_gradDrift U) (f s) x) ∂(ρ s) = 0 := by
    intro ρ s; simp
  simp only [hz, integral_zero, add_zero] at e1 e2
  rw [hf.terminal] at e1 e2
  have h00 : μ 0 = ν 0 := h0
  rw [e1, e2, h00]

/-! ### SPEC (sorried, to be reviewed): the D1 theory for `∂_t u = κΔu - div(b u)`, `b = -∇U` -/

/-- **SPEC (sorried, to be reviewed).** Existence: for every probability measure `μ₀` on `𝕋^n` there is a
measure-valued weak solution (`D1WeakSolution`) of the forward equation with `μ 0 = μ₀`.  The solution is
nonnegative (a family of measures) and has total mass `1` for all `t` (`d1_isProbabilityMeasure`).
Regime: `κ > 0`, `U ∈ C^∞(𝕋^n)`, `n ≥ 1`.  Intended proof: duality with the classical backward solution
`d1_backward_classical` (Riesz representation of `ψ ↦ ∫ (U^{0,t}ψ) dμ₀`; positivity and `U^{0,t}1 = 1` by the
weak maximum principle for the classical backward solution). -/
theorem d1_fp_exists (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) (μ₀ : Measure (Torus n)) [IsProbabilityMeasure μ₀] :
    ∃ μ : ℝ → Measure (Torus n), D1WeakSolution κ (d1_gradDrift U) T μ ∧ μ 0 = μ₀ := by
  sorry

/-- **SPEC (sorried, to be reviewed).** Smoothing, positivity and the classical equation for positive
time, for *bounded* data (the case consumed by D3 and B.15, whose TeX proof treats "bounded strictly
positive data, then density"): if `μ` is a weak solution with probability initial datum
`μ 0 ≤ C·G dx` (`G = e^{-U/κ}`, i.e. `u₀/G ∈ L^∞`), then for `t ∈ (0,T]` the measure `μ t` has a smooth
nonnegative density `u t` of mass `1`; `u` is jointly `C^∞` on `(0,T] × 𝕋^n` (through the covering
`Torus.mk`), and solves `∂_t u = κΔu - div(u b)` classically on `(0,T) × 𝕋^n`.
Intended proof: Doob transform `u = G w`; `w` solves the backward-type equation
`∂_t w = κΔw - ∇U·∇w` (`forwardGen (d1_dyn ..)`) with `w₀ ∈ L^∞ ⊂ L²(G)`; parabolic
`L² → H^m` smoothing (time-weighted energy estimates for the Galerkin approximations of
`adjoint_torus`, all `m`) and Sobolev embedding. -/
theorem d1_fp_smooth (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)] {C : ℝ≥0}
    (hC : μ 0 ≤ (C : ℝ≥0∞) • d1_gibbsRaw κ U) :
    ∃ u : ℝ → Torus n → ℝ,
      (∀ t ∈ Set.Ioc 0 T, μ t = withDensityReal (u t) ∧ (∀ x, 0 ≤ u t x) ∧ Torus.IsSmooth (u t) ∧
        ∫ x, u t x = 1) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Euc n => u p.1 (Torus.mk p.2))
        (Set.Ioc 0 T ×ˢ Set.univ) ∧
      ∀ t ∈ Set.Ioo 0 T, ∀ x : Torus n,
        HasDerivAt (fun s => u s x)
          (κ * Torus.laplacian (u t) x - Torus.div (fun y => u t y • d1_gradDrift U y) x) t := by
  sorry

/-- **SPEC (sorried, OPTIONAL, expensive).** The same conclusion for arbitrary probability data
(`L¹ → C^∞` smoothing, i.e. ultracontractivity / heat-kernel bounds for the Markov semigroup).  Not used
by B.15 (the bounded-data `d1_fp_smooth` plus approximation suffices); stated for completeness only. -/
theorem d1_fp_smooth_general (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)] :
    ∃ u : ℝ → Torus n → ℝ,
      (∀ t ∈ Set.Ioc 0 T, μ t = withDensityReal (u t) ∧ (∀ x, 0 ≤ u t x) ∧ Torus.IsSmooth (u t) ∧
        ∫ x, u t x = 1) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Euc n => u p.1 (Torus.mk p.2))
        (Set.Ioc 0 T ×ˢ Set.univ) ∧
      ∀ t ∈ Set.Ioo 0 T, ∀ x : Torus n,
        HasDerivAt (fun s => u s x)
          (κ * Torus.laplacian (u t) x - Torus.div (fun y => u t y • d1_gradDrift U y) x) t := by
  sorry

/-- **SPEC (sorried, to be reviewed).** Weak maximum principle (comparison with the Gibbs measure
`G dx`, `G = e^{-U/κ}`; positivity preservation and preservation of strict positivity for data
`c G ≤ u₀ ≤ C G`): if `c·G dx ≤ μ 0 ≤ C·G dx` as measures then `c·G dx ≤ μ t ≤ C·G dx` for all
`t ∈ [0,T]`.  (With `c = 0` this is the `L^∞(G)` bound; with `c > 0` it gives the bounded strictly
positive solutions used in the "bounded strictly positive data, then density" step of the TeX proof of
B.15, Step 2.)  Intended proof: `w = u/G` solves the backward-type equation and the Markov semigroup
`P_t` preserves `[c,C]`. -/
theorem d1_fp_comparison (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) {c C : ℝ≥0}
    (hc : (c : ℝ≥0∞) • d1_gibbsRaw κ U ≤ μ 0) (hC : μ 0 ≤ (C : ℝ≥0∞) • d1_gibbsRaw κ U) :
    ∀ t ∈ Set.Icc 0 T, (c : ℝ≥0∞) • d1_gibbsRaw κ U ≤ μ t ∧ μ t ≤ (C : ℝ≥0∞) • d1_gibbsRaw κ U := by
  sorry

/-- **SPEC (sorried, to be reviewed).** Entropy dissipation (D3; `B:eq:selected-regularized-entropy`,
TeX M L12195-12200).  Let `G = e^{-U/κ}`, `Q = Z⁻¹ G dx` the Gibbs probability measure, `μ` a weak solution
with probability initial datum of finite relative entropy.  Then for all `t ∈ [0,T]`
`H(μ_t | Q) + κ ∫_0^t 𝓘_G(μ_r) dr ≤ H(μ_0 | Q)` in `[0,∞]` (`relEntropy = klDiv`; this is
`𝓗_G(f^t) + β⁻¹ ∫_0^t 𝓘_G(f^r) dr ≤ 𝓗_G(f^0)` after subtracting `log Z`, which is finite).  In particular
`μ_t ≪ Q ≪ dx`.  Intended proof: `d/dt ∫ u log(u/G) = -κ ∫ |∇ log(u/G)|² u` for the smooth solutions of
`d1_fp_smooth` with regularisation `φ_δ`, identification of `𝓘_G` of a smooth density with the integral,
then approximation of the initial datum (bounded strictly positive data via `d1_fp_comparison`,
stability by uniqueness and lower semicontinuity of `H` and `𝓘`).  Note (statement review 2026-10-16):
`d1_fp_smooth` only gives dissipation on `(0,T]`; reaching `t = 0` needs `limsup_{s→0} H(μ_s|Q) ≤ H(μ_0|Q)`,
e.g. the contraction `H(μ_s|Q) ≤ H(μ_0|Q)` (Jensen for the Markov semigroup of `w = u/G`), which lower
semicontinuity alone does not give; prove it as an internal lemma.
Bridges owed by later packets (not changes to this statement): B.15 has `V ∈ C²`, so packet E mollifies
`V_δ → V` in `C²` and takes `δ → 0` then `ε → 0` (stability of the SDE, convergence of `H(μ_0|Q_{ε,δ})`,
lower semicontinuity of `H` and `𝓘`); `b15_fisherInfoGen invβ U P ≤ d1_fisherInfo` transported by
`d1_configEquiv` (inequality only: `C_c^∞(Ω_N)` fields are a subclass); `gibbsEntropy D = H(·|Q) - log Z`
and invariance of `klDiv` under `d1_configEquiv`. -/
theorem d1_fp_entropy (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    (hfin : relEntropy (μ 0) (d1_gibbsMeasure κ U) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (μ t) (d1_gibbsMeasure κ U) +
        ENNReal.ofReal κ * ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ U (μ r)
      ≤ relEntropy (μ 0) (d1_gibbsMeasure κ U) := by
  sorry

/-! ### The configuration-space side (interface for D2), proved via the adapter -/

section Config

variable {d N : ℕ}

/-- The generator `κ Δ_X Φ + D Φ[bC]` of `dX = bC(X) dt + √(2κ) dW` on `Config d N`, in the shape of
`fkeGenerator` (second derivatives and drift computed through the lift at `Y = rep ∘ X`). -/
def d1_configGen (κ : ℝ) (bC : Config d N → Fin N → Euc d) (Φ : Config d N → ℝ) (X : Config d N) : ℝ :=
  κ * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (configLift (fun _ => Φ) 0))
      (fun i => Torus.rep (X i)) (configBasis d N k) (configBasis d N k)
    + fderiv ℝ (configLift (fun _ => Φ) 0) (fun i => Torus.rep (X i)) (bC X)

/-- Weak solutions of the forward equation on `Config d N` (what Itô's formula for `Φ(s, X_s)` delivers
for the law of `dX = bC(X) dt + √(2κ) dW`; this is D2's target form).  The test class is the
`IsC12Test` class of the transported functions `Φ_s ∘ e⁻¹` on `𝕋^{N d}`; D2 converts it to Itô's class
`IsC12On T univ (configLift Φ)` by `d1_isC12On_of_isC12Test`. -/
structure D1ConfigWeakSolution (κ : ℝ) (bC : Config d N → Fin N → Euc d) (T : ℝ)
    (ν : ℝ → Measure (Config d N)) : Prop where
  finite : ∀ t ∈ Set.Icc 0 T, IsFiniteMeasure (ν t)
  narrow : ∀ ψ : Config d N → ℝ, Continuous ψ →
    ContinuousOn (fun t => ∫ X, ψ X ∂(ν t)) (Set.Icc 0 T)
  eqT : ∀ τ ∈ Set.Icc 0 T, ∀ Φ Φt : ℝ → Config d N → ℝ,
    IsC12Test τ (fun r => Φ r ∘ (d1_configEquiv d N).symm) (fun r => Φt r ∘ (d1_configEquiv d N).symm) →
    ∫ X, Φ τ X ∂(ν τ) = ∫ X, Φ 0 X ∂(ν 0) +
      ∫ s in Set.Icc 0 τ, ∫ X, (Φt s X + d1_configGen κ bC (Φ s) X) ∂(ν s)

theorem d1_gen_config (κ : ℝ) (bC : Config d N → Fin N → Euc d) (φ : Torus (N * d) → ℝ)
    (X : Config d N) :
    d1_gen κ (d1_pushField bC) φ (d1_configEquiv d N X) =
      d1_configGen κ bC (φ ∘ d1_configEquiv d N) X := by
  unfold d1_gen d1_configGen
  rw [d1_laplacian]
  congr 1
  have h := d1_fderiv_cl_eq_inner φ X (bC X)
  have hb : d1_pushField bC (d1_configEquiv d N X) = d1_eucEquiv d N (bC X) := by
    simp [d1_pushField]
  rw [hb, real_inner_comm]
  exact h.symm

/-- Transfer: the push-forward of a configuration-space weak solution along the adapter is a
`D1WeakSolution` on `𝕋^{N d}` with the transported drift. -/
theorem d1_weakSolution_of_config {κ : ℝ} {bC : Config d N → Fin N → Euc d} {T : ℝ}
    {ν : ℝ → Measure (Config d N)} (h : D1ConfigWeakSolution κ bC T ν) :
    D1WeakSolution κ (d1_pushField bC) T (fun t => (ν t).map (d1_configEquiv d N)) where
  finite t ht := by
    haveI := h.finite t ht
    exact Measure.isFiniteMeasure_map _ _
  narrow ψ hψ := by
    have := h.narrow (ψ ∘ d1_configEquiv d N) (hψ.comp (d1_configEquiv_continuous d N))
    refine this.congr fun t _ => ?_
    exact integral_map_equiv (d1_configEquiv d N) ψ
  eqT τ hτ f ft hf := by
    have key := h.eqT τ hτ (fun r => f r ∘ d1_configEquiv d N) (fun r => ft r ∘ d1_configEquiv d N)
      (by simpa [Function.comp_def] using hf)
    have e1 : ∀ (s : ℝ), ∫ x, f s x ∂((ν s).map (d1_configEquiv d N)) =
        ∫ X, (f s ∘ d1_configEquiv d N) X ∂(ν s) :=
      fun s => integral_map_equiv (d1_configEquiv d N) (f s)
    have e2 : ∀ s : ℝ, ∫ x, (ft s x + d1_gen κ (d1_pushField bC) (f s) x)
        ∂((ν s).map (d1_configEquiv d N)) =
        ∫ X, ((ft s ∘ d1_configEquiv d N) X + d1_configGen κ bC (f s ∘ d1_configEquiv d N) X) ∂(ν s) :=
      fun s => by
      rw [integral_map_equiv (d1_configEquiv d N) (fun x => ft s x + d1_gen κ (d1_pushField bC) (f s) x)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun X => by
        simp only [Function.comp_apply]
        rw [d1_gen_config])
    simp only [e1, e2]
    exact key

/-- **Identification interface for D2** (proved from `d1_fp_unique`): a configuration-space weak solution
(e.g. the law of the smooth gradient SDE, by Itô) whose initial law corresponds to the initial datum `μ 0`
of a `D1WeakSolution` agrees with it at all times: `(ν t).map e = μ t`. -/
theorem d1_config_law_eq (hn : 1 ≤ N * d) {κ : ℝ} (hκ : 0 < κ) {U : Torus (N * d) → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} {bC : Config d N → Fin N → Euc d}
    (hb : ∀ x, d1_pushField bC x = d1_gradDrift U x) {ν : ℝ → Measure (Config d N)}
    (hν : D1ConfigWeakSolution κ bC T ν) {μ : ℝ → Measure (Torus (N * d))}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) (h0 : μ 0 = (ν 0).map (d1_configEquiv d N)) :
    ∀ t ∈ Set.Icc 0 T, (ν t).map (d1_configEquiv d N) = μ t := by
  have hb' : d1_pushField bC = d1_gradDrift U := funext hb
  have h1 := d1_weakSolution_of_config hν
  rw [hb'] at h1
  intro t ht
  exact (d1_fp_unique hn hκ hU hμ h1 h0 t ht).symm

/-- **SPEC (sorried, D2 helper).** The `IsC12Test` class on `𝕋^{N d}`, read on the covering space of the
configuration space through `d1_cl`, is contained in Itô's class `IsC12On T univ` (with the time
derivative `ft`).  Needed to feed `ito_formula_additive` with the test functions of
`D1ConfigWeakSolution.eqT`.  (Size S–M: continuity of the iterated derivatives `iteratedFDeriv ℝ j`,
`j ≤ 2`, through the continuous linear equivalence `d1_eucEquiv`, and `fderiv_eq_curry`,
`fderiv_fderiv_eq_curry2` of `HRS/Stochastic/EmpiricalIto.lean`.) -/
theorem d1_isC12On_of_isC12Test {τ : ℝ} (hτ : 0 < τ) {f ft : ℝ → Torus (N * d) → ℝ}
    (hf : IsC12Test τ f ft) :
    IsC12On τ Set.univ (fun r => d1_cl (f r)) ∧
      ∀ r ∈ Set.Icc 0 τ, ∀ Y : Fin N → Euc d,
        derivWithin (fun r' => d1_cl (f r') Y) (Set.Icc 0 τ) r =
          ft r (d1_configEquiv d N fun i => Torus.mk (Y i)) := by
  sorry

end Config

end HRS
