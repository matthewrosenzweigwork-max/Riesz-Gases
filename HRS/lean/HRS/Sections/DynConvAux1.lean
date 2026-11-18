import HRS.Energy.Coercivity
import HRS.PDE.MeanFieldVelocity
import HRS.PDE.KernelInputsD1
import HRS.Commutator.Torus.External
import HRS.PDE.Uniqueness
import HRS.PDE.ClassicalPart
import HRS.PDE.EnergyR2Fn

/-!
# DYNCONV: statement checks and chain plans for `dynamic_convergence` and `transport_bound_uniform`

## (2) `transport_bound_uniform` (Proposition 3.41, last sentence)

Statement check (no defect found).
* `HasTransportBound d s v K` is an existential statement (`L F` with `IsLipschitzVF L v`, and for
  `s < d - 2` a function `w` with `IsFracDeriv ((d+1)/2) v w`, `‖w‖_{L^{2d/(d-1)}} ≤ F`), so there is no
  junk value.  For `d ≤ 2` the fractional clause is vacuous (`0 ≤ s < d-2` forces `d ≥ 3`); `d = 1` is
  covered by the Lipschitz clause only.
* `Λ < 0`, or `Λ < lam₀`, makes the family of densities empty: vacuous, constants are chosen after
  `Λ lam₀ ΛV σ₀`.  `IsProbDensity` is not needed.  `mfeTransport D ρ = invβ ∇log ρ + ∇g*ρ + ∇V` is the
  honest `u_V` (the cancellation convention `convGradConv` is a genuine `C^{m_*+1}` field, KernelInputs).
* Regularity count: `m_* = ⌊d/2⌋ + 3`, `n := m_* + 1 = ⌊d/2⌋ + 4 ≥ (d+2)/2 + 3`, which is more than
  needed (`‖v‖_*` needs `n ≥ (d+2)/2`, see below).

Chain.
1. `u = invβ • (ρ⁻¹ • ∇ρ) + G + ∇V` with `G = ∇g*ρ` (`PDE.convGradConv_cbNorm_of_one_le`, `m = n`):
   `C^n`, `cbNorm n ≤ A(Λ, lam₀, ΛV, σ₀)` by `MFVelocity.exists_cbNorm_inv_le`, `exists_cbNorm_smul_le`,
   `cbNorm_grad_le`, `cbNorm_const_smul_le_vec`, `cbNorm_add_le_vec`, `grad_log_eq`.
2. `dynconv_lipschitzVF`: `C^1` vector field is Lipschitz for `tdist` with constant `cbNorm 1`.
3. `dynconv_fracDeriv_scalar` (`d ≥ 3`): scalar `C^n` `v` has a function `w` with the Fourier
   coefficients `(2π|k|)^{(d+1)/2} v̂(k)` and `‖w‖_{L^p} ≤ C cbNorm n v`, `p = 2d/(d-1)`:
   `c_k = (2π|k|)^{(d+2)/2} v̂(k)` is in `ℓ²` (`ClassicalPart.memHs_coeffOf_cbNorm`), `exists_L2_fun` gives
   `f ∈ L²` (real part), then Hardy-Littlewood-Sobolev on the torus (`hls_T`, `p = 2 → q = p`, `σ = 1/2`).
4. Assemble components and sum the three pieces.

## (1) `dynamic_convergence` (Proposition 5.4, last paragraph)

Statement check: no defect found (hypotheses `hSF`, `hfin`, `hB`, `hlaw`, `hY` are the faithful ones; `d ≥ 2`,
`T ≥ 0`; the target path functionals are `flucPath`/`toPath`, which are measurable-or-zero conventions that
do not affect convergence in law).  The statement is true but its proof is the full path-space limit theorem.

Chain plan (status: NOT proved here; XL, see ISSUES.md entry DYNCONV).
(a) finite-dimensional laws: `dynamic_comparison_proof'` + `hlaw` + independence of the Gaussian part
    (`IsLinearFluctuationSolution`) give `(⟨φ_a, η_N^{t_a}⟩)_a ⇒ (⟨f_a^0, η°⟩ + G)_a` once `B_N/√N → 0`.
(b) identification: the right side is the law of `(⟨φ_a, Y^{t_a}⟩)_a` by the mild form of `hY`.
(c) tightness of `η_N` in `C([0,T]; H^{-m})`, `m > d+4`: needs `E‖·‖_{H^{-m'}}` moment bounds (`m' < m`)
    of the martingale part, uniform in time and k (quantitative adjoint bounds `∇U^{r,t}e_k`, as for the
    open `moving_integrated_forcing`), the remainder `√N ∫ C_N` in `L¹` (`B_N/√N`) summed over `k`,
    time-modulus (Kolmogorov / Aldous) estimates for the path, and tightness of the initial law (`hlaw`).
    None of these is in the repository; they are several thousand lines.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

open KernelGrad in
/-- A `C^1` vector field on the torus is Lipschitz for `tdist` with constant `cbNorm 1`. -/
theorem dynconv_lipschitzVF {v : Torus d → Euc d} (hv : Torus.IsCk 1 v) :
    IsLipschitzVF (Torus.cbNorm 1 v) v := by
  have hv' : Torus.IsCk ((1 : ℕ) : WithTop ℕ∞) v := by exact_mod_cast hv
  have hL : ∀ y, ‖fderiv ℝ (Torus.lift v) y‖ ≤ Torus.cbNorm 1 v := fun y => by
    have e : ‖iteratedFDeriv ℝ 1 (Torus.lift v) y‖ = ‖fderiv ℝ (Torus.lift v) y‖ := by
      rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0), norm_iteratedFDeriv_zero]
    rw [← e]
    exact norm_iteratedFDeriv_le_cbNorm hv' le_rfl y
  have h1 : Differentiable ℝ (Torus.lift v) := hv.differentiable one_ne_zero
  intro x y
  set r := centeredRep (x - y) with hr
  have hmk : Torus.mk (Torus.rep y + r) = x := by
    rw [mk_add, Torus.mk_rep, hr, mk_centeredRep]; abel
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := Torus.lift v) (fun u _ => h1 u)
    (fun u _ => hL u) convex_univ (Set.mem_univ (Torus.rep y)) (Set.mem_univ (Torus.rep y + r))
  have e1 : Torus.lift v (Torus.rep y + r) = v x := by simp [Torus.lift, hmk]
  have e2 : Torus.lift v (Torus.rep y) = v y := by simp [Torus.lift, Torus.mk_rep]
  rw [e1, e2, add_sub_cancel_left] at this
  exact this

/-- A real `L²` function with prescribed Hermitian square-summable Fourier coefficients. -/
theorem dynconv_exists_real_L2 (c : PDE.Coeff d) (hc : PDE.MemHs 0 c) (hr : PDE.IsRealCoeff c) :
    ∃ f : Torus d → ℝ, MemLp f 2 volume ∧ (∀ k, Torus.fcoef f k = c k) ∧
      eLpNorm f 2 volume ≤ ENNReal.ofReal (Real.sqrt (∑' k, ‖c k‖ ^ 2)) := by
  obtain ⟨u, hu, hcu⟩ := PDE.exists_L2_fun c hc
  refine ⟨fun x => (u x).re, hu.re, fun k => ?_, ?_⟩
  · have hint : ∀ l : Lattice d, Integrable (fun x => Torus.mode l x * u x) volume := fun l => by
      have h1 : MemLp (fun x => Torus.mode l x * u x) 2 volume := by
        refine hu.of_le_mul (c := 1)
          ((Torus.continuous_mode l).aestronglyMeasurable.mul hu.aestronglyMeasurable) ?_
        refine Filter.Eventually.of_forall fun x => ?_
        simp [Torus.norm_mode]
      exact h1.integrable one_le_two
    have hint2 : Integrable (fun x => Torus.mode (-k) x * (starRingEnd ℂ) (u x)) volume := by
      have : (fun x => Torus.mode (-k) x * (starRingEnd ℂ) (u x)) =
          fun x => (starRingEnd ℂ) (Torus.mode k x * u x) := by
        funext x
        rw [map_mul]
        congr 1
        have := UnitAddTorus.mFourier_neg (n := k) (x := x)
        simpa [Torus.mode] using this
      rw [this]
      exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (hint k)
    have e1 : ∫ x, Torus.mode (-k) x * (starRingEnd ℂ) (u x) = c k := by
      have : (fun x => Torus.mode (-k) x * (starRingEnd ℂ) (u x)) =
          fun x => (starRingEnd ℂ) (Torus.mode k x * u x) := by
        funext x
        rw [map_mul]
        congr 1
        have := UnitAddTorus.mFourier_neg (n := k) (x := x)
        simpa [Torus.mode] using this
      rw [this, integral_conj]
      have h2 : ∫ x, Torus.mode k x * u x = c (-k) := by
        rw [← hcu (-k), PDE.funFourierCoeff_eq_int]
        simp [Torus.mode]
      rw [h2, hr k, Complex.conj_conj]
    have e2 : ∫ x, Torus.mode (-k) x * u x = c k := by
      rw [← hcu k, PDE.funFourierCoeff_eq_int]; rfl
    unfold Torus.fcoef
    have : ∀ x, Torus.mode (-k) x * (((u x).re : ℝ) : ℂ) =
        (1 / 2 : ℂ) * (Torus.mode (-k) x * u x +
          Torus.mode (-k) x * (starRingEnd ℂ) (u x)) := by
      intro x
      rw [Complex.re_eq_add_conj]
      push_cast
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_add (hint (-k)) hint2, e1, e2]
    ring
  · have hmem := hu
    have h2 : eLpNorm (fun x => (u x).re) 2 volume ≤ eLpNorm u 2 volume :=
      eLpNorm_mono (hu.re.aestronglyMeasurable) fun x => by simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (u x)
    refine h2.trans (le_of_eq ?_)
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    congr 1
    have hP := PDE.parseval_sq u hu
    have : ∀ x, ‖u x‖ ^ (2 : ℝ) = ‖u x‖ ^ 2 := fun x => Real.rpow_two _
    simp_rw [this]
    have h3 : ∑' k, ‖c k‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
      have := hP.tsum_eq
      simpa [hcu] using this
    rw [h3, Real.sqrt_eq_rpow, one_div]

theorem dynconv_fcoef_eq_coeffOf (φ : Torus d → ℝ) (k : Lattice d) :
    Torus.fcoef φ k = PDE.coeffOf φ k := by
  unfold Torus.fcoef PDE.coeffOf
  rw [PDE.funFourierCoeff_eq_int]
  rfl

theorem dynconv_hls_exps (hd : 3 ≤ d) :
    (1 : ℝ≥0∞) < 2 ∧ (2 : ℝ≥0∞) < ENNReal.ofReal (2 * d / ((d : ℝ) - 1)) ∧
      ENNReal.ofReal (2 * d / ((d : ℝ) - 1)) < ⊤ ∧ (0 : ℝ) < 1 / 2 ∧
      (ENNReal.ofReal (2 * d / ((d : ℝ) - 1)))⁻¹ =
        (2 : ℝ≥0∞)⁻¹ - ENNReal.ofReal ((1 / 2 : ℝ) / d) := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hdpos : 0 < (d : ℝ) := by linarith
  refine ⟨by norm_num, ?_, ENNReal.ofReal_lt_top, by norm_num, ?_⟩
  · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [lt_div_iff₀ hd1]; linarith
  · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    field_simp

/-- For `d ≥ 3` and `n ≥ d/2 + 1`: a scalar `C^n` function `v` has the fractional derivative
`|∇|^{(d+1)/2} v ∈ L^{2d/(d-1)}`, with a norm bound by `cbNorm n v`. -/
theorem dynconv_fracDeriv_scalar (hd : 3 ≤ d) (n : ℕ) (hn : (d : ℝ) / 2 + 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Torus d → ℝ, Torus.IsCk (n : WithTop ℕ∞) v →
      ∃ w : Torus d → ℝ, MemLp w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ∧
        (∀ k : Lattice d, Torus.fcoef w k =
          (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) * Torus.fcoef v k) ∧
        eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤ ENNReal.ofReal (C * Torus.cbNorm n v) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hp1, hpq, hqt, hσ, hrel⟩ := dynconv_hls_exps hd
  obtain ⟨Ch, hChpos, hCh⟩ := HRS.Commutator.TorusNote.hls_T hd1 (1 / 2 : ℝ) 2
    (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) hp1 hpq hqt hσ hrel
  refine ⟨Ch * Real.sqrt ((1 + d : ℝ) ^ n), by positivity, fun v hv => ?_⟩
  obtain ⟨hmem, hbd⟩ := PDE.ClassicalPart.memHs_coeffOf_cbNorm n v hv
  have hcb0 : 0 ≤ Torus.cbNorm n v := KernelGrad.cbNorm_nonneg' v n
  set c : PDE.Coeff d := fun k =>
    (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 2) / 2) : ℝ) : ℂ) * PDE.coeffOf v k with hc
  have hcle : ∀ k, ‖c k‖ ^ 2 ≤ PDE.sobWeight (n : ℝ) k * ‖PDE.coeffOf v k‖ ^ 2 := by
    intro k
    have hx : 0 ≤ 2 * Real.pi * Lattice.enorm k := by
      have : 0 ≤ Lattice.enorm k := norm_nonneg _
      positivity
    rw [hc]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    rw [abs_of_nonneg (Real.rpow_nonneg hx _)]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    have h1 : (2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 2) / 2 * ((2 : ℕ) : ℝ)) =
        (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (((d : ℝ) + 2) / 2) := by
      rw [show (((d : ℝ) + 2) / 2 * ((2 : ℕ) : ℝ)) = 2 * (((d : ℝ) + 2) / 2) by push_cast; ring,
        Real.rpow_mul hx, Real.rpow_two]
      congr 1
      ring
    rw [h1]
    unfold PDE.sobWeight
    have hb : (1 : ℝ) ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
      have : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
      linarith
    calc (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (((d : ℝ) + 2) / 2)
        ≤ (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (((d : ℝ) + 2) / 2) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ ≤ (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  have hsum : Summable fun k => ‖c k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hcle hmem
  have hc0 : PDE.MemHs 0 c := (PDE.memHs_zero_iff c).2 hsum
  have hreal : PDE.IsRealCoeff c := by
    have hr := PDE.isRealCoeff_coeffOf_of_isCk hv
    intro k
    simp only [hc]
    rw [map_mul, Complex.conj_ofReal, HRS.enorm_neg, hr k]
  obtain ⟨f, hf2, hfc, hfn⟩ := dynconv_exists_real_L2 c hc0 hreal
  have hf0 : Torus.fcoef f 0 = 0 := by
    rw [hfc 0]
    have : Lattice.enorm (0 : Lattice d) = 0 := by
      unfold Lattice.enorm
      have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      rw [this, norm_zero]
    simp [hc, this, Real.zero_rpow (show ((d : ℝ) + 2) / 2 ≠ 0 by positivity)]
  obtain ⟨h, hh2, hh0, hhk, hhn⟩ := hCh f hf2 hf0
  refine ⟨h, hh2, fun k => ?_, ?_⟩
  · by_cases hk : k = 0
    · subst hk
      have : Lattice.enorm (0 : Lattice d) = 0 := by
        unfold Lattice.enorm
        have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
        rw [this, norm_zero]
      rw [hh0]
      simp [this, Real.zero_rpow (show ((d : ℝ) + 1) / 2 ≠ 0 by positivity)]
    · rw [hhk k hk, hfc k, dynconv_fcoef_eq_coeffOf v k]
      simp only [hc]
      have hten : 0 < 2 * Real.pi * Lattice.enorm k := by
        have := HRS.one_le_enorm k hk
        positivity
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hten]
      congr 3
      ring
  · refine hhn.trans ?_
    have hS : ∑' k, ‖c k‖ ^ 2 ≤ (1 + d : ℝ) ^ n * Torus.cbNorm n v ^ 2 :=
      (hsum.tsum_le_tsum hcle hmem).trans hbd
    have hS' : Real.sqrt (∑' k, ‖c k‖ ^ 2) ≤ Real.sqrt ((1 + d : ℝ) ^ n) * Torus.cbNorm n v := by
      calc Real.sqrt (∑' k, ‖c k‖ ^ 2) ≤ Real.sqrt ((1 + d : ℝ) ^ n * Torus.cbNorm n v ^ 2) :=
            Real.sqrt_le_sqrt hS
        _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hcb0]
    calc ENNReal.ofReal Ch * eLpNorm f 2 volume
        ≤ ENNReal.ofReal Ch * ENNReal.ofReal (Real.sqrt (∑' k, ‖c k‖ ^ 2)) :=
          mul_le_mul_right hfn _
      _ ≤ ENNReal.ofReal Ch * ENNReal.ofReal (Real.sqrt ((1 + d : ℝ) ^ n) * Torus.cbNorm n v) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hS') _
      _ = ENNReal.ofReal (Ch * Real.sqrt ((1 + d : ℝ) ^ n) * Torus.cbNorm n v) := by
          rw [← ENNReal.ofReal_mul hChpos.le, mul_assoc]

theorem dynconv_proj_le (j : Fin d) : ‖(EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) j : Euc d →L[ℝ] ℝ)‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using PiLp.norm_apply_le v j

theorem dynconv_comp_isCk {n : ℕ} {v : Torus d → Euc d} (hv : Torus.IsCk (n : WithTop ℕ∞) v)
    (j : Fin d) :
    Torus.IsCk (n : WithTop ℕ∞) (fun x => v x j) ∧
      Torus.cbNorm n (fun x => v x j) ≤ Torus.cbNorm n v := by
  have h1 := PDE.cbNorm_clm_comp_le (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) n v hv
  refine ⟨?_, ?_⟩
  · unfold Torus.IsCk
    have e : Torus.lift (fun x => v x j) =
        (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) ∘ Torus.lift v := rfl
    rw [e]
    exact (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).contDiff.comp hv
  · calc Torus.cbNorm n (fun x => v x j)
        ≤ ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖ * Torus.cbNorm n v := h1
      _ ≤ 1 * Torus.cbNorm n v :=
          mul_le_mul_of_nonneg_right (dynconv_proj_le j) (KernelGrad.cbNorm_nonneg' _ _)
      _ = _ := one_mul _

/-- For `d ≥ 3`, `n ≥ d/2+1`: a `C^n` vector field has the fractional derivative of order `(d+1)/2`
in `L^{2d/(d-1)}`, bounded by `C cbNorm n v`. -/
theorem dynconv_fracDeriv_vec (hd : 3 ≤ d) (n : ℕ) (hn : (d : ℝ) / 2 + 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Torus d → Euc d, Torus.IsCk (n : WithTop ℕ∞) v →
      ∃ w : Torus d → Euc d, IsFracDeriv (((d : ℝ) + 1) / 2) v w ∧
        eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤
          ENNReal.ofReal (C * Torus.cbNorm n v) := by
  classical
  obtain ⟨Cs, hCs0, hCs⟩ := dynconv_fracDeriv_scalar hd n hn
  obtain ⟨hp1, hpq, hqt, -, -⟩ := dynconv_hls_exps hd
  refine ⟨d * Cs, by positivity, fun v hv => ?_⟩
  have hex : ∀ j : Fin d, ∃ w : Torus d → ℝ,
      MemLp w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ∧
        (∀ k : Lattice d, Torus.fcoef w k =
          (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) *
            Torus.fcoef (fun x => v x j) k) ∧
        eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤
          ENNReal.ofReal (Cs * Torus.cbNorm n v) := fun j => by
    obtain ⟨hvj, hcbj⟩ := dynconv_comp_isCk hv j
    obtain ⟨w, hw, hwc, hwn⟩ := hCs _ hvj
    refine ⟨w, hw, hwc, hwn.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact mul_le_mul_of_nonneg_left hcbj hCs0
  choose h hmem hcoef hhn using hex
  refine ⟨fun x => WithLp.toLp 2 (fun j => h j x), ?_, ?_⟩
  · intro j k
    have hfun : (fun x => (WithLp.toLp 2 (fun j => h j x) : Euc d) j) = h j := by
      funext x; simp
    rw [hfun]
    exact hcoef j k
  · have hwm : AEStronglyMeasurable (fun x => (WithLp.toLp 2 (fun j => h j x) : Euc d)) volume := by
      refine AEMeasurable.aestronglyMeasurable ?_
      exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
        (aemeasurable_pi_iff.2 fun j => (hmem j).aemeasurable)
    have hle : ∀ x, ‖(WithLp.toLp 2 (fun j => h j x) : Euc d)‖ ≤
        ‖(∑ j : Fin d, fun x => ‖h j x‖) x‖ := by
      intro x
      have h1 := HRS.Commutator.Whole.cmxHLS_norm_toLp_le (d := d) (fun j => h j x)
      refine h1.trans (le_of_eq ?_)
      rw [Finset.sum_apply, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
      simp [Real.norm_eq_abs]
    calc eLpNorm (fun x => (WithLp.toLp 2 (fun j => h j x) : Euc d))
          (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume
        ≤ eLpNorm (∑ j : Fin d, fun x => ‖h j x‖) (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume :=
          eLpNorm_mono hwm hle
      _ ≤ ∑ j : Fin d, eLpNorm (fun x => ‖h j x‖) (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume :=
          eLpNorm_sum_le (hp1.trans hpq).le
      _ ≤ ∑ _j : Fin d, ENNReal.ofReal (Cs * Torus.cbNorm n v) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [eLpNorm_norm _ (hmem j).aestronglyMeasurable]
          exact hhn j
      _ = ENNReal.ofReal (d * Cs * Torus.cbNorm n v) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring

/-- A `C^n` vector field with `cbNorm n v ≤ B` has transport seminorm `≤ cT B`. -/
theorem dynconv_transport_of_cbNorm (n : ℕ) (hn1 : 1 ≤ n) (hn : (d : ℝ) / 2 + 1 ≤ n) :
    ∃ cT : ℝ, 0 ≤ cT ∧ ∀ (s : ℝ), 0 ≤ s → ∀ (v : Torus d → Euc d) (B : ℝ),
      Torus.IsCk (n : WithTop ℕ∞) v → Torus.cbNorm n v ≤ B → HasTransportBound d s v (cT * B) := by
  classical
  obtain ⟨Cf, hCf0, hCf⟩ : ∃ Cf : ℝ, 0 ≤ Cf ∧ (3 ≤ d → ∀ v : Torus d → Euc d,
      Torus.IsCk (n : WithTop ℕ∞) v → ∃ w : Torus d → Euc d,
        IsFracDeriv (((d : ℝ) + 1) / 2) v w ∧
        eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤
          ENNReal.ofReal (Cf * Torus.cbNorm n v)) := by
    by_cases hd3 : 3 ≤ d
    · obtain ⟨C, hC0, hC⟩ := dynconv_fracDeriv_vec hd3 n hn
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hd3⟩
  refine ⟨1 + Cf, by positivity, fun s hs0 v B hv hB => ?_⟩
  have hv1 : Torus.IsCk 1 v := by
    have : Torus.IsCk ((n : ℕ) : WithTop ℕ∞) v := hv
    exact this.of_le (by exact_mod_cast hn1)
  have hcb1 : Torus.cbNorm 1 v ≤ Torus.cbNorm n v := KernelGrad.cbNorm_mono hn1
  have hcn0 : 0 ≤ Torus.cbNorm n v := KernelGrad.cbNorm_nonneg' v n
  have hcb10 : 0 ≤ Torus.cbNorm 1 v := KernelGrad.cbNorm_nonneg' v 1
  refine ⟨Torus.cbNorm 1 v, Cf * Torus.cbNorm n v, hcb10, mul_nonneg hCf0 hcn0,
    dynconv_lipschitzVF hv1, fun hs => ?_, ?_⟩
  · have hd3 : 3 ≤ d := by
      by_contra h
      push Not at h
      have : (d : ℝ) ≤ 2 := by exact_mod_cast (by omega : d ≤ 2)
      linarith
    exact hCf hd3 v hv
  · split_ifs with hs
    · nlinarith [mul_le_mul_of_nonneg_left hB hCf0]
    · nlinarith

/-- The `C^{m_*+1}` bound of the transport field `u_V = β⁻¹∇log ρ + ∇g*ρ + ∇V`, uniform in the data. -/
theorem dynconv_mfeTransport_cbNorm (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (Λ lam₀ ΛV σ₀ : ℝ) (hlam₀ : 0 < lam₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (D : DynData d), D.s = s → 0 < D.invβ → D.invβ ≤ σ₀ →
      Torus.IsCk (PDE.mStar d + 2) D.V → Torus.cbNorm (PDE.mStar d + 2) D.V ≤ ΛV →
      ∀ ρ : Torus d → ℝ, Torus.IsCk (PDE.mStar d + 2) ρ →
        Torus.cbNorm (PDE.mStar d + 2) ρ ≤ Λ → (∀ x, lam₀ ≤ ρ x) →
        Torus.IsCk ((PDE.mStar d + 1 : ℕ) : WithTop ℕ∞) (mfeTransport D ρ) ∧
          Torus.cbNorm (PDE.mStar d + 1) (mfeTransport D ρ) ≤ B := by
  set j : ℕ := PDE.mStar d + 1 with hj
  set cU : ℝ := max Λ lam₀ with hcU
  obtain ⟨Ci, hCi0, hCi⟩ := PDE.MFVelocity.exists_cbNorm_inv_le (d := d) j lam₀ cU hlam₀ (le_max_right _ _)
  obtain ⟨Cs, hCs0, hCs⟩ := PDE.MFVelocity.exists_cbNorm_smul_le (d := d) j
  obtain ⟨CG, hCG⟩ := PDE.convGradConv_cbNorm_of_one_le (d := d) (s := s) hd hs0 hsd j
  refine ⟨|σ₀| * (Cs * (Ci * (1 + |Λ|) ^ j) * |Λ|) + |CG| * |Λ| + |ΛV|, by positivity,
    fun D hDs hβ hβ' hV hVb ρ hρ hρb hlow => ?_⟩
  have hρj1 : Torus.IsCk ((j + 1 : ℕ) : WithTop ℕ∞) ρ := by
    have : Torus.IsCk (((PDE.mStar d + 2 : ℕ)) : WithTop ℕ∞) ρ := by exact_mod_cast hρ
    exact this
  have hVj1 : Torus.IsCk ((j + 1 : ℕ) : WithTop ℕ∞) D.V := by
    have : Torus.IsCk (((PDE.mStar d + 2 : ℕ)) : WithTop ℕ∞) D.V := by exact_mod_cast hV
    exact this
  have hρb' : Torus.cbNorm (j + 1) ρ ≤ Λ := hρb
  have hVb' : Torus.cbNorm (j + 1) D.V ≤ ΛV := hVb
  have hρj : Torus.IsCk (j : WithTop ℕ∞) ρ := PDE.MFVelocity.isCk_of_le (Nat.le_succ j) hρj1
  have hn0 : ∀ (φ : Torus d → ℝ) (k : ℕ), 0 ≤ Torus.cbNorm k φ := fun φ k => KernelGrad.cbNorm_nonneg' φ k
  have hΛ0 : 0 ≤ Λ := le_trans (hn0 ρ _) hρb'
  have hρ1 : Torus.cbNorm j ρ ≤ Λ := (KernelGrad.cbNorm_mono (Nat.le_succ j)).trans hρb'
  have hbd : ∀ x, lam₀ ≤ ρ x ∧ ρ x ≤ cU := fun x => ⟨hlow x, by
    have := PDE.R2Aux.abs_le_cbNorm hρj1 x
    exact (le_abs_self _).trans (this.trans (hρb'.trans (le_max_left _ _)))⟩
  have hpos : ∀ x, 0 < ρ x := fun x => lt_of_lt_of_le hlam₀ (hlow x)
  obtain ⟨hi, hib⟩ := hCi ρ hρj hbd
  have hgρ : Torus.IsCk (j : WithTop ℕ∞) (Torus.grad ρ) := PDE.isCk_grad j ρ hρj1
  have hgρb : Torus.cbNorm j (Torus.grad ρ) ≤ Λ := (PDE.cbNorm_grad_le j ρ hρj1).trans hρb'
  obtain ⟨hT, hTb⟩ := hCs (fun x => (ρ x)⁻¹) (Torus.grad ρ) hi hgρ
  obtain ⟨hT', hTb'⟩ := PDE.MFVelocity.cbNorm_const_smul_le_vec j D.invβ _ hT
  obtain ⟨hG, hGb⟩ := hCG ρ hρj1
  have hgV : Torus.IsCk (j : WithTop ℕ∞) (Torus.grad D.V) := PDE.isCk_grad j D.V hVj1
  have hgVb : Torus.cbNorm j (Torus.grad D.V) ≤ ΛV := (PDE.cbNorm_grad_le j D.V hVj1).trans hVb'
  have e : mfeTransport D ρ =
      ((fun x => D.invβ • ((ρ x)⁻¹ • Torus.grad ρ x)) + convGradConv (periodicRieszGrad d D.s) ρ) +
        Torus.grad D.V := by
    funext x
    simp only [mfeTransport, Pi.add_apply]
    rw [(PDE.MFVelocity.grad_log_eq ρ (hρj1.of_le (by exact_mod_cast (by omega : 1 ≤ j + 1))) hpos).2 x]
  have hG' : Torus.IsCk (j : WithTop ℕ∞) (convGradConv (periodicRieszGrad d D.s) ρ) := by
    rw [hDs]; exact hG
  have hGb' : Torus.cbNorm j (convGradConv (periodicRieszGrad d D.s) ρ) ≤ |CG| * |Λ| := by
    rw [hDs]
    calc _ ≤ CG * Torus.cbNorm (j + 1) ρ := hGb
      _ ≤ |CG| * |Λ| := by
        refine mul_le_mul (le_abs_self _) (hρb'.trans (le_abs_self _)) (KernelGrad.cbNorm_nonneg' _ _) (abs_nonneg _)
  rw [e]
  refine ⟨PDE.MFVelocity.isCk_add_vec j _ _ (PDE.MFVelocity.isCk_add_vec j _ _ hT' hG') hgV, ?_⟩
  have h1 := PDE.MFVelocity.cbNorm_add_le_vec j _ _ (PDE.MFVelocity.isCk_add_vec j _ _ hT' hG') hgV
  have h2 := PDE.MFVelocity.cbNorm_add_le_vec j _ _ hT' hG'
  -- the first term
  have hib' : Torus.cbNorm j (fun x => (ρ x)⁻¹) ≤ Ci * (1 + |Λ|) ^ j := by
    refine hib.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hn0 ρ j]) ?_ j) hCi0)
    linarith [le_abs_self Λ]
  have hT1 : Torus.cbNorm j (fun x => D.invβ • ((ρ x)⁻¹ • Torus.grad ρ x)) ≤
      |σ₀| * (Cs * (Ci * (1 + |Λ|) ^ j) * |Λ|) := by
    refine hTb'.trans ?_
    have hinv : |D.invβ| ≤ |σ₀| := by
      rw [abs_of_pos hβ]; exact hβ'.trans (le_abs_self _)
    have hb2 : Cs * Torus.cbNorm j (fun x => (ρ x)⁻¹) * Torus.cbNorm j (Torus.grad ρ) ≤
        Cs * (Ci * (1 + |Λ|) ^ j) * |Λ| := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hib' hCs0) (hgρb.trans (le_abs_self _))
        (KernelGrad.cbNorm_nonneg' _ _) (by positivity)
    exact mul_le_mul hinv (hTb.trans hb2) (KernelGrad.cbNorm_nonneg' _ _) (abs_nonneg _)
  linarith [hgVb.trans (le_abs_self ΛV)]

end HRS
