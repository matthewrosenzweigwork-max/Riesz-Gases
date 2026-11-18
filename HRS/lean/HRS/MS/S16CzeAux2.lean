import HRS.MS.S16CzeAux1
import HRS.MS.CzSymAux3
import HRS.MS.CzMikExtAux2

/-!
# S16-CZE, part 2: even Calderon-Zygmund `D² Δ⁻¹` on `L^p` (input E2 of S.A.16)

Packet S16-CZE (`docs/CZ_PLAN.md`, row S16-CZ E2).  Notation: `d ≥ 2`, `g = rieszKernel d ((d:ℝ) - 2)`
(`g = |x|^{2-d}` for `d ≥ 3`, `g = -log|x|` for `d = 2`), `convFun g u (x) = ∫ g(x-y) u(y) dy` (the convolution
of the repo, `HRS.Whole.convFun`), `e_j = EuclideanSpace.single j 1`, and for a real Schwartz function `u` the
second derivative `∂_i ∂_j (g * u)` is the genuine iterated Fréchet derivative
`fderiv ℝ (fun y => fderiv ℝ (convFun g u) y e_j) x e_i` (part 1 proves differentiability, so there is no
`fderiv = 0` junk value).

**What is proved.**

* `s16cze_fourier_rep`: there is `κ < 0` (depending on `d` only) such that for all `i j`, real Schwartz `u` and
  all `x`: `∂_i ∂_j (g * u)(x) = κ · (T_{m_{ij}} u)(x)` with `m_{ij}(ξ) = ξ_i ξ_j / |ξ|²` and
  `T_m u = 𝓕⁻(m 𝓕u)` (`mik2_T`, an absolutely convergent Fourier integral).  Here `κ = -(2π)² c`, where
  `c > 0` is the constant of `kg_fourier_h_proof` for `s = d - 2` (the symbol of `g` is `c |ξ|^{-2}` up to the
  factor `(2π)^{-2}` coming from `∂ ↔ 2πi ξ`).  The case `d = 2`, `g = -log|x|` is covered by the same
  statement (`kg_fourier_h_proof` handles `s = 0` by the limit `s → 0⁺`); it does not need the odd-force route
  sketched in the plan note after the table.
* `s16cze_even_cz` (**the `L^p` bound**): for `d ≥ 2`, `1 < p < ∞` there is `C ≥ 0` depending only on `d, p`
  such that for all `i j` and every real Schwartz `u`:
  `‖∂_i ∂_j (g * u)‖_{L^p} ≤ C ‖u‖_{L^p}` (`eLpNorm`, values in `ℝ≥0∞`, no finiteness assumption).
* `s16cze_Lp_extend` (**the `L^p` extension**): with `Fact (1 ≤ ofReal p)`: there is `C ≥ 0` (depending on
  `d, p`) such that for every `i j` there is a continuous `ℂ`-linear map `T : L^p(ℂ) → L^p(ℂ)` with
  `‖T‖ ≤ C`, `T [u] = [∂_i ∂_j (g * u)]` a.e. for every real Schwartz `u` (`[u]` = class of the complexified
  `u`), `T [w] = [κ T_{m_{ij}} w]` for every complex Schwartz `w`, and `T [k ⋆ w] = k ⋆ (κ T_{m_{ij}} w)` a.e.
  for every `k ∈ L¹`, complex Schwartz `w`.  Uniqueness of such `T` follows from density of Schwartz functions
  (`mikhlin_Lp_extend_unique` of MIK-2 applied to `κ⁻¹ T`).  No claim is made that `∂_i ∂_j (g * u)` makes sense
  pointwise for non-Schwartz `u ∈ L^p` (`g * u` need not converge); the extension is the operator `T` itself.

Nothing is assumed besides `2 ≤ d`, `1 < p`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff FourierTransform SchwartzMap

noncomputable section

namespace HRS.S16Cze

open HRS.Whole HRS.MH.Screened HRS.CZ.Mik HRS.Commutator.Whole.XLI

variable {d : ℕ}

/-- the even Riesz symbol `m_{ij}(ξ) = ξ_i ξ_j / |ξ|²` -/
def s16cze_m (d : ℕ) (i j : Fin d) (ξ : Euc d) : ℂ := ((ξ i * ξ j / ‖ξ‖ ^ 2 : ℝ) : ℂ)

lemma s16cze_ft_pd (u : 𝓢(Euc d, ℝ)) (j : Fin d) (ξ : Euc d) :
    𝓕 (fun y : Euc d => ((s16cze_pd u j y : ℝ) : ℂ)) ξ =
      (2 * Real.pi * Complex.I * (ξ j : ℂ)) * 𝓕 (fun y : Euc d => ((u y : ℝ) : ℂ)) ξ := by
  have hF := HRS.Commutator.Whole.cmxMY_fourier_partial (s3Cx u) j ξ
  have hD : (fun ζ : Euc d => fderiv ℝ (s3Cx u) ζ (EuclideanSpace.single j (1 : ℝ))) =
      fun y : Euc d => ((s16cze_pd u j y : ℝ) : ℂ) := by
    funext ζ
    have h1 : fderiv ℝ (s3Cx u) ζ (EuclideanSpace.single j (1 : ℝ)) = s3D u j ζ := by
      unfold s3D; rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [h1, s3D_apply, s16cze_pd_apply]
  rw [hD] at hF
  exact hF

/-- Fourier representation of `g * ∂_i ∂_j u` -/
theorem s16cze_fourier_rep (hd : 2 ≤ d) :
    ∃ κ : ℝ, κ < 0 ∧ ∀ (i j : Fin d) (u : 𝓢(Euc d, ℝ)) (x : Euc d),
      ((HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (⇑(s16cze_pd (s16cze_pd u j) i)) x : ℝ) : ℂ) =
        (κ : ℂ) * mik2_T (s16cze_m d i j) (s3Cx u) x := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨c, hc, h⟩ := kg_fourier_h_proof hd1 (s := (d : ℝ) - 2) (by linarith) (by linarith)
  refine ⟨-((2 * Real.pi) ^ 2 * c), ?_, fun i j u x => ?_⟩
  · have : 0 < (2 * Real.pi) ^ 2 * c := by positivity
    linarith
  have h1 := (h i (s16cze_pd u j) x).2
  have e1 : HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2))
      (fun z => fderiv ℝ (⇑(s16cze_pd u j)) z (EuclideanSpace.single i (1 : ℝ))) x =
      HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (⇑(s16cze_pd (s16cze_pd u j) i)) x := by
    congr 1
  rw [e1] at h1
  rw [h1, mik2_T_apply, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [s16cze_ft_pd, smul_eq_mul]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) =
      Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) := by
    rw [real_inner_comm]; congr 1; push_cast; ring
  have hpow : ‖ξ‖ ^ ((d : ℝ) - 2 - (d : ℝ)) = (‖ξ‖ ^ 2)⁻¹ := by
    have : ((d : ℝ) - 2 - (d : ℝ)) = -2 := by ring
    rw [this, Real.rpow_neg (norm_nonneg _), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hexp, hpow]
  unfold s16cze_m
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hs : (⇑(s3Cx u) : Euc d → ℂ) = fun y : Euc d => ((u y : ℝ) : ℂ) := rfl
  rw [hs]
  generalize 𝓕 (fun y : Euc d => ((u y : ℝ) : ℂ)) ξ = F
  generalize Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) = E
  push_cast
  rw [div_eq_mul_inv]
  linear_combination ((c : ℂ) * (2 * (Real.pi : ℂ)) ^ 2 * (ξ i : ℂ) * (ξ j : ℂ) *
    ((‖ξ‖ : ℂ) ^ 2)⁻¹ * F * E) * hI

lemma s16cze_contDiff_conv_cont (hd : 2 ≤ d) (φ : 𝓢(Euc d, ℝ)) :
    Continuous (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (⇑φ)) :=
  continuous_iff_continuousAt.2 fun x => (s16cze_hasFDerivAt_conv hd φ x).continuousAt

lemma s16cze_eLpNorm_ofReal {f : Euc d → ℝ} (hf : AEStronglyMeasurable f volume) (p : ENNReal) :
    eLpNorm (fun x => ((f x : ℝ) : ℂ)) p volume = eLpNorm f p volume := by
  refine eLpNorm_congr_enorm_ae (Complex.continuous_ofReal.comp_aestronglyMeasurable hf) hf ?_
  exact Eventually.of_forall fun x => by
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

/-- **`s16cze_even_cz`**: the `L^p` bound for the even Calderon-Zygmund operator `∂_i ∂_j (-Δ)⁻¹`-type
`∂_i ∂_j (g * ·)`, `g = rieszKernel d (d-2)`, on Schwartz functions. -/
theorem s16cze_even_cz (hd : 2 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin d) (u : 𝓢(Euc d, ℝ)),
      eLpNorm (fun x => fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (⇑u)) y
          (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)))
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * eLpNorm (⇑u) (ENNReal.ofReal p) volume := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨κ, hκ, hrep⟩ := s16cze_fourier_rep hd
  obtain ⟨A, hA, hMik⟩ := HRS.CZ.Sym.isMikhlin_riesz2 d
  obtain ⟨C0, hC0, hT⟩ := mik2_eLpNorm_T_le hd1 hp
  refine ⟨|κ| * C0.toReal * A, by positivity, fun i j u => ?_⟩
  have hfun : (fun x => fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (⇑u)) y
          (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ))) =
      HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (⇑(s16cze_pd (s16cze_pd u j) i)) := by
    funext x
    exact (s16cze_second_deriv_conv hd u i j x).2.2.2
  rw [hfun, ← s16cze_eLpNorm_ofReal (s16cze_contDiff_conv_cont hd _).aestronglyMeasurable]
  have hcongr : (fun x => ((HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2))
      (⇑(s16cze_pd (s16cze_pd u j) i)) x : ℝ) : ℂ)) =
      (κ : ℂ) • mik2_T (s16cze_m d i j) (s3Cx u) := by
    funext x
    rw [hrep i j u x]; rfl
  rw [hcongr, eLpNorm_const_smul]
  have hmain := hT A (s16cze_m d i j) hA (hMik i j) (s3Cx u)
  have hu : eLpNorm (⇑(s3Cx u)) (ENNReal.ofReal p) volume = eLpNorm (⇑u) (ENNReal.ofReal p) volume := by
    exact s16cze_eLpNorm_ofReal u.continuous.aestronglyMeasurable _
  rw [hu] at hmain
  calc ‖(κ : ℂ)‖ₑ * eLpNorm (mik2_T (s16cze_m d i j) (s3Cx u)) (ENNReal.ofReal p) volume
      ≤ ‖(κ : ℂ)‖ₑ * (C0 * ENNReal.ofReal A * eLpNorm (⇑u) (ENNReal.ofReal p) volume) := by
        gcongr
    _ = ENNReal.ofReal (|κ| * C0.toReal * A) * eLpNorm (⇑u) (ENNReal.ofReal p) volume := by
        have hk : ‖(κ : ℂ)‖ₑ = ENNReal.ofReal |κ| := by
          rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
        rw [hk, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal hC0]
        ring

/-- **`s16cze_Lp_extend`**: bounded-operator extension of `u ↦ ∂_i ∂_j (g * u)` from Schwartz functions to
`L^p`, together with the a.e. identification on Schwartz functions and the commutation with `L¹` convolutions. -/
theorem s16cze_Lp_extend (hd : 2 ≤ d) {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ (κ : ℝ) (C : ℝ), κ < 0 ∧ 0 ≤ C ∧ ∀ i j : Fin d,
      ∃ T : Lp ℂ (ENNReal.ofReal p) (volume : Measure (Euc d)) →L[ℂ]
          Lp ℂ (ENNReal.ofReal p) (volume : Measure (Euc d)),
        ‖T‖ ≤ C ∧
        (∀ u : 𝓢(Euc d, ℝ), T ((s3Cx u).toLp (ENNReal.ofReal p) volume) =ᵐ[volume]
          fun x => ((fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 2)) (⇑u)) y
            (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) : ℝ) : ℂ)) ∧
        (∀ w : 𝓢(Euc d, ℂ), T (w.toLp (ENNReal.ofReal p) volume) =ᵐ[volume]
          fun x => (κ : ℂ) * mik2_T (s16cze_m d i j) w x) ∧
        (∀ (k : Euc d → ℂ) (hk : Integrable k) (w : 𝓢(Euc d, ℂ)),
          T ((mik2_memLp_cv_schwartz hk hp w).toLp (cv k w)) =ᵐ[volume]
            fun x => ∫ y, k y * ((κ : ℂ) * mik2_T (s16cze_m d i j) w (x - y))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨κ, hκ, hrep⟩ := s16cze_fourier_rep hd
  obtain ⟨A, hA, hMik⟩ := HRS.CZ.Sym.isMikhlin_riesz2 d
  obtain ⟨C1, hC1, hext⟩ := mikhlin_Lp_extend hd1 hp
  refine ⟨κ, |κ| * C1 * A, hκ, by positivity, fun i j => ?_⟩
  obtain ⟨Tm, hTm, hTmu⟩ := hext A (s16cze_m d i j) hA (hMik i j)
  refine ⟨(κ : ℂ) • Tm, ?_, ?_, ?_, ?_⟩
  · calc ‖(κ : ℂ) • Tm‖ ≤ ‖(κ : ℂ)‖ * ‖Tm‖ := (norm_smul _ _).le
      _ ≤ |κ| * (C1 * A) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        gcongr
      _ = _ := by ring
  · intro u
    have h1 := hTmu (s3Cx u)
    filter_upwards [Lp.coeFn_smul (κ : ℂ) (Tm ((s3Cx u).toLp (ENNReal.ofReal p) volume)), h1] with x hx1 hx2
    rw [smul_apply, hx1, Pi.smul_apply, hx2, smul_eq_mul]
    rw [(s16cze_second_deriv_conv hd u i j x).2.2.2, hrep i j u x]
  · intro w
    have h1 := hTmu w
    filter_upwards [Lp.coeFn_smul (κ : ℂ) (Tm (w.toLp (ENNReal.ofReal p) volume)), h1] with x hx1 hx2
    rw [smul_apply, hx1, Pi.smul_apply, hx2, smul_eq_mul]
  · intro k hk w
    have h1 : ((Tm ((mik2_memLp_cv_schwartz hk hp w).toLp (cv k w)) :
        Lp ℂ (ENNReal.ofReal p) (volume : Measure (Euc d))) : Euc d → ℂ) =ᵐ[volume]
        cv k (mik2_T (s16cze_m d i j) w) :=
      mikhlin_comm_conv hd1 hp hA (hMik i j) Tm hTmu hk w (mik2_memLp_cv_schwartz hk hp w)
    filter_upwards [Lp.coeFn_smul (κ : ℂ) (Tm ((mik2_memLp_cv_schwartz hk hp w).toLp (cv k w))), h1]
      with x hx1 hx2
    rw [smul_apply, hx1, Pi.smul_apply, hx2, smul_eq_mul, cv_apply,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring

end HRS.S16Cze
