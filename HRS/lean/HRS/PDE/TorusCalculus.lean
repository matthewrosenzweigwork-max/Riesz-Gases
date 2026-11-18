import HRS.Torus.Basic

/-!
# Calculus on the torus: integration by parts and Fourier coefficients of derivatives

Auxiliary file of the torus PDE layer (package ADJ-01).  Every energy estimate of Section 3.2
of the main manuscript (`B:sec:adjoint-apriori`, L1853–1940) integrates by parts on `𝕋^d`, and
the identification of the Sobolev norm `B:eq:sobolev-def` (L10060–10062) with weighted sums of
`L²` norms of derivatives uses `(∂_j φ)^(k) = 2πi k_j φ̂(k)`.  Derivatives are those of the
periodic lift (`HRS.Torus.partialDeriv`, `HRS.Torus.IsCk`).
-/

noncomputable section

open MeasureTheory

namespace HRS.PDE

variable {d : ℕ}

private lemma mk_add (x y : Euc d) : Torus.mk (x + y) = Torus.mk x + Torus.mk y := by
  funext i
  simp [Torus.mk]

private lemma mk_toEuc (n : Lattice d) : Torus.mk (Lattice.toEuc n) = 0 := by
  funext i
  simp only [Torus.mk, Lattice.toEuc, PiLp.toLp_apply, Pi.zero_apply]
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n i, by simp⟩

private lemma mk_rep' (x : Torus d) : Torus.mk (Torus.rep x) = x := by
  funext i
  simp only [Torus.mk, Torus.rep, PiLp.toLp_apply]
  exact AddCircle.coe_equivIco

private lemma exists_int_of_mk_eq {x y : Euc d} (h : Torus.mk x = Torus.mk y) :
    ∃ n : Lattice d, x = y + Lattice.toEuc n := by
  have : ∀ i, ∃ m : ℤ, x i = y i + m := by
    intro i
    have h1 : ((x i : ℝ) : UnitAddCircle) = ((y i : ℝ) : UnitAddCircle) := congrFun h i
    have h2 := (QuotientAddGroup.eq (a := x i) (b := y i)).1 h1
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 h2
    refine ⟨-m, ?_⟩
    simp at hm
    push_cast
    linarith
  choose n hn using this
  refine ⟨n, ?_⟩
  ext i
  simp [Lattice.toEuc, hn i]

private lemma lift_add_toEuc {E : Type*} (H : Torus d → E) (y : Euc d) (n : Lattice d) :
    Torus.lift H (y + Lattice.toEuc n) = Torus.lift H y := by
  simp [Torus.lift, mk_add, mk_toEuc]

private lemma fderiv_lift_of_mk_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Torus d → E) {x y : Euc d} (h : Torus.mk x = Torus.mk y) :
    fderiv ℝ (Torus.lift H) x = fderiv ℝ (Torus.lift H) y := by
  obtain ⟨n, rfl⟩ := exists_int_of_mk_eq h
  rw [← fderiv_comp_add_right]
  congr 1
  funext z
  exact lift_add_toEuc H z n

private lemma isOpenQuotientMap_mk : IsOpenQuotientMap (Torus.mk : Euc d → Torus d) := by
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have h2 := h1.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  exact h2


private lemma continuous_of_lift {E : Type*} [TopologicalSpace E] {f : Torus d → E}
    (h : Continuous (Torus.lift f)) : Continuous f :=
  isOpenQuotientMap_mk.isQuotientMap.continuous_iff.2 h

private abbrev dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (j : Fin d)
    (H : Torus d → E) (x : Torus d) : E :=
  fderiv ℝ (Torus.lift H) (Torus.rep x) (EuclideanSpace.single j 1)

private lemma dirDeriv_mk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (j : Fin d)
    (H : Torus d → E) (x : Euc d) :
    dirDeriv j H (Torus.mk x) = fderiv ℝ (Torus.lift H) x (EuclideanSpace.single j 1) := by
  simp only [dirDeriv]
  rw [fderiv_lift_of_mk_eq H (mk_rep' (Torus.mk x))]

private lemma continuous_dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Fin d) (H : Torus d → E) (hH : ContDiff ℝ 1 (Torus.lift H)) :
    Continuous (dirDeriv j H) := by
  apply continuous_of_lift
  have : Torus.lift (dirDeriv j H) =
      fun x => fderiv ℝ (Torus.lift H) x (EuclideanSpace.single j 1) := by
    funext x
    exact dirDeriv_mk j H x
  rw [this]
  exact (hH.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The partial derivative of a `C¹` function on the torus is continuous. -/
theorem continuous_partialDeriv (j : Fin d) (φ : Torus d → ℝ) (hφ : Torus.IsCk 1 φ) :
    Continuous (Torus.partialDeriv j φ) :=
  continuous_dirDeriv j φ hφ

/-- The partial derivative computed through the lift: `∂_j (φ ∘ mk) = (∂_j φ) ∘ mk`
everywhere on `ℝ^d` (periodicity of the lift). -/
theorem partialDeriv_mk (j : Fin d) (φ : Torus d → ℝ) (hφ : Torus.IsCk 1 φ) (x : Euc d) :
    Torus.partialDeriv j φ (Torus.mk x) =
      fderiv ℝ (Torus.lift φ) x (EuclideanSpace.single j 1) := by
  have _ := hφ
  exact dirDeriv_mk j φ x


private lemma integral_dirDeriv_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (j : Fin d) (H : Torus d → E) (hH : ContDiff ℝ 1 (Torus.lift H)) :
    ∫ x, dirDeriv j H x = 0 := by
  set e : Euc d := EuclideanSpace.single j 1 with he
  set a : ℝ → Torus d := fun t => Torus.mk (t • e) with ha
  have hHc : Continuous H := continuous_of_lift hH.continuous
  have hGc := continuous_dirDeriv j H hH
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖dirDeriv j H x‖ ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hGc.continuousOn
    exact ⟨C, fun x => hC x (Set.mem_univ x)⟩
  have hF : ∀ t x, Torus.lift H (Torus.rep x + t • e) = H (x + a t) := by
    intro t x
    simp [Torus.lift, mk_add, mk_rep', a]
  have hF' : ∀ t x, fderiv ℝ (Torus.lift H) (Torus.rep x + t • e) e = dirDeriv j H (x + a t) := by
    intro t x
    rw [he, ← dirDeriv_mk, mk_add, mk_rep']
  have hI : ∀ t, ∫ x, H (x + a t) = ∫ x, H x := fun t => integral_add_right_eq_self H (a t)
  have hcont : ∀ t, Continuous fun x : Torus d => H (x + a t) := fun t => by fun_prop
  have hcont' : ∀ t, Continuous fun x : Torus d => dirDeriv j H (x + a t) := fun t => hGc.comp (continuous_id.add continuous_const)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Torus d)))
    (𝕜 := ℝ) (x₀ := 0) (s := Set.univ) (F := fun t x => H (x + a t))
    (F' := fun t x => dirDeriv j H (x + a t)) (bound := fun _ => C) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hcont t).aestronglyMeasurable)
    ((hcont 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hcont' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t _ => by simpa using hC (x + a t))
    (integrable_const C)
    (Filter.Eventually.of_forall fun x t _ => by
      have h1 : HasDerivAt (fun t : ℝ => Torus.rep x + t • e) e t := by
        simpa using ((hasDerivAt_id t).smul_const e).const_add (Torus.rep x)
      have h2 : DifferentiableAt ℝ (Torus.lift H) (Torus.rep x + t • e) :=
        (hH.differentiable one_ne_zero) _
      have h3 := h2.hasFDerivAt.comp_hasDerivAt t h1
      have h4 : (fun t : ℝ => H (x + a t)) = (Torus.lift H) ∘ fun t : ℝ => Torus.rep x + t • e := by
        funext t; exact (hF t x).symm
      rw [h4, ← hF' t x]
      exact h3)
  have hconst : (fun t => ∫ x : Torus d, H (x + a t)) = fun _ => ∫ x, H x := funext hI
  have := key.2
  rw [hconst] at this
  have h0 : a 0 = 0 := by
    funext i
    simp [a, Torus.mk]
  have := (hasDerivAt_const (0:ℝ) (∫ x : Torus d, H x)).unique this
  simpa [h0] using this.symm


/-- Integration by parts on `𝕋^d`: `∫ ∂_j φ · ψ = -∫ φ · ∂_j ψ` for `C¹` functions. -/
theorem integral_partialDeriv_mul (j : Fin d) (φ ψ : Torus d → ℝ)
    (hφ : Torus.IsCk 1 φ) (hψ : Torus.IsCk 1 ψ) :
    ∫ x, Torus.partialDeriv j φ x * ψ x = -∫ x, φ x * Torus.partialDeriv j ψ x := by
  have h := integral_dirDeriv_eq_zero j (fun x => φ x * ψ x) (hφ.mul hψ)
  have hpt : ∀ x, dirDeriv j (fun x => φ x * ψ x) x =
      Torus.partialDeriv j φ x * ψ x + φ x * Torus.partialDeriv j ψ x := by
    intro x
    have e1 : Torus.lift (fun x => φ x * ψ x) = fun y => Torus.lift φ y * Torus.lift ψ y := rfl
    simp only [dirDeriv]
    rw [e1, fderiv_fun_mul ((hφ.differentiable one_ne_zero) _) ((hψ.differentiable one_ne_zero) _)]
    simp [Torus.partialDeriv, Torus.lift, mk_rep']
    ring
  have cφ : Continuous φ := continuous_of_lift hφ.continuous
  have cψ : Continuous ψ := continuous_of_lift hψ.continuous
  have i1 : Integrable (fun x => Torus.partialDeriv j φ x * ψ x) :=
    ((continuous_partialDeriv j φ hφ).mul cψ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun x => φ x * Torus.partialDeriv j ψ x) :=
    (cφ.mul (continuous_partialDeriv j ψ hψ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [hpt] at h
  rw [integral_add i1 i2] at h
  linarith


/-- The real-linear functional `y ↦ ∑ i, n i * y i`, valued in `ℂ`. -/
private def linFun (n : Lattice d) : Euc d →L[ℝ] ℂ :=
  ∑ i, ((n i : ℂ)) • (Complex.ofRealCLM.comp (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ))

private lemma linFun_apply (n : Lattice d) (y : Euc d) :
    linFun n y = ∑ i, (n i : ℂ) * (y i : ℂ) := by
  simp [linFun]

private lemma linFun_single (n : Lattice d) (j : Fin d) :
    linFun n (EuclideanSpace.single j 1) = (n j : ℂ) := by
  rw [linFun_apply]
  simp [PiLp.single_apply, apply_ite]

private lemma lift_mFourier (n : Lattice d) (y : Euc d) :
    Torus.lift (UnitAddTorus.mFourier n) y =
      Complex.exp (2 * Real.pi * Complex.I * linFun n y) := by
  simp only [Torus.lift, Function.comp, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Torus.mk,
    linFun_apply, fourier_coe_apply]
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Complex.ofReal_one, div_one]
  congr 1
  ring

private lemma hasFDerivAt_lift_mFourier (n : Lattice d) (y : Euc d) :
    HasFDerivAt (Torus.lift (UnitAddTorus.mFourier n))
      (Torus.lift (UnitAddTorus.mFourier n) y • ((2 * Real.pi * Complex.I) • linFun n)) y := by
  have h1 := ((linFun n).hasFDerivAt (x := y)).const_mul (2 * Real.pi * Complex.I)
  have h2 := (Complex.hasDerivAt_exp (2 * Real.pi * Complex.I * linFun n y)).comp_hasFDerivAt y h1
  have : Torus.lift (UnitAddTorus.mFourier n) =
      Complex.exp ∘ fun y => 2 * Real.pi * Complex.I * linFun n y := by
    funext z; exact lift_mFourier n z
  rw [this]
  exact h2


/-- `mFourierCoeff` is computed with `haarAddCircle` on each factor; it agrees with the integral
against the product of the `volume` measures on `UnitAddCircle` (total mass one). -/
private lemma funFourierCoeff_eq (f : Torus d → ℂ) (k : Lattice d) :
    Torus.funFourierCoeff f k = ∫ x, UnitAddTorus.mFourier (-k) x * f x := by
  unfold Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
  have hm : (@volume (UnitAddTorus (Fin d))
      (@MeasureSpace.pi (Fin d) _ (fun _ => UnitAddCircle) fun _ => instMeasureSpaceUnitAddCircle)) =
      (volume : Measure (Torus d)) := by
    show Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))
    congr 1
    funext i
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hm]
  simp [smul_eq_mul]

/-- Fourier coefficients of a derivative: `(∂_j φ)^(k) = 2πi k_j φ̂(k)` for real `C¹` `φ`. -/
theorem funFourierCoeff_partialDeriv (j : Fin d) (φ : Torus d → ℝ) (hφ : Torus.IsCk 1 φ)
    (k : Lattice d) :
    Torus.funFourierCoeff (fun x => (Torus.partialDeriv j φ x : ℂ)) k =
      (2 * Real.pi * Complex.I * (k j : ℂ)) * Torus.funFourierCoeff (fun x => (φ x : ℂ)) k := by
  rw [funFourierCoeff_eq, funFourierCoeff_eq]
  set m : Torus d → ℂ := fun x => UnitAddTorus.mFourier (-k) x with hm
  set b : ℂ := 2 * Real.pi * Complex.I * ((-k : Lattice d) j : ℂ) with hb
  have hlm : ContDiff ℝ 1 (Torus.lift m) := by
    have : Torus.lift m = fun y => Complex.exp (2 * Real.pi * Complex.I * linFun (-k) y) := by
      funext y; exact lift_mFourier (-k) y
    rw [this]
    exact Complex.contDiff_exp.comp (contDiff_const.mul (linFun (-k)).contDiff)
  have hlφ : ContDiff ℝ 1 (Torus.lift (fun x => (φ x : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp hφ
  set H : Torus d → ℂ := fun x => (φ x : ℂ) * m x with hH
  have hlH : ContDiff ℝ 1 (Torus.lift H) := hlφ.mul hlm
  have h := integral_dirDeriv_eq_zero j H hlH
  have hpt : ∀ x, dirDeriv j H x = m x * (Torus.partialDeriv j φ x : ℂ) + b * (m x * φ x) := by
    intro x
    have e1 : Torus.lift H = fun y => Torus.lift (fun x => (φ x : ℂ)) y * Torus.lift m y := rfl
    simp only [dirDeriv]
    rw [e1, fderiv_fun_mul ((hlφ.differentiable one_ne_zero) _) ((hlm.differentiable one_ne_zero) _)]
    have h1 : fderiv ℝ (Torus.lift m) (Torus.rep x) =
        Torus.lift m (Torus.rep x) • ((2 * Real.pi * Complex.I) • linFun (-k)) :=
      (hasFDerivAt_lift_mFourier (-k) (Torus.rep x)).fderiv
    have h3 : Torus.lift m (Torus.rep x) = m x := by simp [Torus.lift, mk_rep']
    have h4 : Torus.lift (fun x => (φ x : ℂ)) (Torus.rep x) = φ x := by
      simp [Torus.lift, mk_rep']
    have h2 : fderiv ℝ (Torus.lift (fun x => (φ x : ℂ))) (Torus.rep x) (EuclideanSpace.single j 1)
        = (Torus.partialDeriv j φ x : ℂ) := by
      have := (Complex.ofRealCLM.hasFDerivAt.comp (Torus.rep x)
        ((hφ.differentiable one_ne_zero) (Torus.rep x)).hasFDerivAt).fderiv
      simp only [Torus.partialDeriv]
      rw [show Torus.lift (fun x => (φ x : ℂ)) = Complex.ofRealCLM ∘ Torus.lift φ from rfl, this]
      simp
    rw [h1]
    simp only [add_apply, smul_apply, smul_eq_mul, h2, h3,
      h4, linFun_single, hb]
    ring
  have cm : Continuous m := (UnitAddTorus.mFourier (-k)).continuous
  have cφ : Continuous φ := continuous_of_lift hφ.continuous
  have i1 : Integrable (fun x => m x * (Torus.partialDeriv j φ x : ℂ)) :=
    (cm.mul (Complex.continuous_ofReal.comp (continuous_partialDeriv j φ hφ))
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun x => b * (m x * φ x)) :=
    (continuous_const.mul (cm.mul (Complex.continuous_ofReal.comp cφ))
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [hpt] at h
  rw [integral_add i1 i2, integral_const_mul] at h
  have hb' : b = -(2 * Real.pi * Complex.I * (k j : ℂ)) := by simp [hb]
  show ∫ x, m x * (Torus.partialDeriv j φ x : ℂ) = _ * ∫ x, m x * (φ x : ℂ)
  rw [hb'] at h
  linear_combination h

end HRS.PDE
