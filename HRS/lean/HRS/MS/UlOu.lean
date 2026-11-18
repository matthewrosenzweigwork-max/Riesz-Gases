import HRS.MS.UlOuAux2
import HRS.MS.LcKolmAux2
import HRS.Stochastic.Wiener

/-!
# UL-2: the OU semigroup `ouSg`, its identification with `lcSg`, and the Kolmogorov equation

Infrastructure packet UL-2 for S5.1 (`ul_adjoint_fixed_viscosity`); not a manuscript row.  Everything is
for the base semigroup of `∂_τ u = ν Δu - ⟨Qx, ∇u⟩` with constant viscosity `ν ≥ 0`
(`LcHyp Q 2 0 0 (fun _ => 0) (fun _ _ => 0)`: OU data `c = 0`, `B = 0`).

Definitions (in `UlOuAux1`): `ouExp`, `ouCov`, `ouLaw`, `ouSg`; bounds `ouCov_bounds`, `ouCov_posDef`;
`ou_charFun`, `ou_charFun_integral`; `ouLaw_eq_map` (image of `stdGaussian` under `Σ^{1/2}`, the form
UL-3 needs instead of a density, since Mathlib has none for `multivariateGaussian`).

Results of this file.
* `ou_law_shift`: for `0 ≤ r`, `0 ≤ τ`, the shift `lcU Q G r (r+τ)` of the noise `G = lcNoiseE W (fun _ => ν)`
  restarted at `r` has law `ouLaw Q ν τ` (the case `r = 0` is `ou_law`, `UlOuAux2`).
* `lcSg_ou`: `lcSg P W (fun _ => ν) Q (fun _ => 0) (fun _ _ => 0) r (r+τ) h x = ouSg Q ν τ h x` for
  `0 ≤ r`, `0 ≤ τ`, `h` measurable (the hypothesis `Measurable h` is needed: for a non-measurable `h`
  both sides are junk-valued Bochner integrals).
* `ou_backward`: for `h ∈ C²` with `h, Dh, D²h` bounded, `r ↦ ouSg Q ν (t - r) h` is an
  `IsLocalBackwardSolution` with viscosity `fun _ => ν` and drift `-Qx`, terminal datum `h`
  (from `lc_backward`; the probability space comes from `exists_isBrownianFiltration_type`).
* `ou_backward_hasDerivAt` (the `∂_r` form) and `ou_forward_hasDerivAt`
  (`∂_τ ouSg τ h x = ν Δ(ouSg τ h) x + ⟨-Qx, ∇ ouSg τ h x⟩` for `τ > 0`).
* `ouLaw_zero`, `ouSg_zero`: `ouLaw Q ν 0 = δ_0`, `ouSg Q ν 0 h = h`.

Statement adjustments relative to the plan sketch: `ouSg` uses the continuous linear map `ouExp Q τ = e^{-τ Q}`
instead of `Torus.matVec (exp ...)`; `ν ≥ 0` is allowed (not only `ν > 0`) wherever the proof does not
need strict positivity; the identification `lcSg_ou` is for `r ≥ 0` (the flow is only defined for
`r ≥ 0`).  Helper lemmas carry the prefix `ul2_`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped InnerProduct ENNReal NNReal Matrix

noncomputable section

namespace HRS.MS.Ul

open HRS HRS.MS.Lc HRS.Whole HRS.MD.EQLawPath

variable {d : ℕ}

/-! ### The zero data -/

theorem ul2_lcHyp_zero (Q : Matrix (Fin d) (Fin d) ℝ) :
    LcHyp Q 2 0 0 (fun _ => (0 : Euc d)) (fun _ _ => (0 : Euc d)) where
  c_cont := continuousOn_const
  B_cont := continuousOn_const
  c_bd := fun v _ => by simp
  B_smooth := fun v _ => contDiff_const
  B_bd := fun v _ j _ x => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hj)]
      simp

/-! ### The linear ODE `Z' = -QZ` -/

/-- For the OU data the pathwise ODE solution is `e^{-τQ} x`. -/
theorem ul2_lcZ_eq (Q : Matrix (Fin d) (Fin d) ℝ) {g : ℝ → Euc d} (hg : Continuous g) {r : ℝ}
    (hr : 0 ≤ r) (x : Euc d) {τ : ℝ} (hτ : 0 ≤ τ) :
    lcZ (lcDrift Q (fun _ => (0 : Euc d)) (fun _ _ => (0 : Euc d)) g r) x τ = ouExp Q τ x := by
  set D := lcDrift Q (fun _ => (0 : Euc d)) (fun _ _ => (0 : Euc d)) g r with hD
  have hLip : IsLipschitzDrift D := lcDrift_isLipschitz (ul2_lcHyp_zero Q) hg hr
  have hflow := lcZ_isNegDriftFlow hLip hτ
  have hDz : ∀ s (z : Euc d), D s z = -(lcQ Q z) := by
    intro s z
    simp [hD, lcDrift]
  set z : ℝ → Euc d := fun s => lcZ D x s with hz
  -- `w s = e^{sQ} z s` has zero derivative
  have hw : ∀ s ∈ Ico (0 : ℝ) τ, HasDerivWithinAt
      (fun s => (NormedSpace.exp (s • lcQ Q)) (z s)) 0 (Ici s) s := by
    intro s hs
    have h1 := hflow.eqn x s ⟨hs.1, hs.2.le⟩
    have h2 : HasDerivWithinAt z (-(lcQ Q (z s))) (Icc 0 τ) s := by
      have := h1
      simp only [neg_neg, hDz] at this
      simpa [hz, hDz] using this
    have h3 : HasDerivWithinAt z (-(lcQ Q (z s))) (Ici s) s :=
      h2.mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))
    have h4 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (lcQ Q) s).hasDerivWithinAt (s := Ici s)
    have h5 := h4.clm_apply h3
    refine h5.congr_deriv ?_
    have hc0 : Commute (s • lcQ Q) (lcQ Q) := by simpa using lc1_commute (lcQ Q) s 1
    have hc : Commute (NormedSpace.exp (s • lcQ Q)) (lcQ Q) := hc0.exp_left
    have : (NormedSpace.exp (s • lcQ Q)) (lcQ Q (z s)) = (lcQ Q) ((NormedSpace.exp (s • lcQ Q)) (z s)) := by
      rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, hc.eq]
    simp [mul_apply_eq_comp, this]
  have hcont : ContinuousOn (fun s => (NormedSpace.exp (s • lcQ Q)) (z s)) (Icc 0 τ) := by
    have h1 : Continuous fun s : ℝ => NormedSpace.exp (s • lcQ Q) :=
      NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    exact (h1.continuousOn).clm_apply (lcZ_cont hLip x hτ)
  have hconst := constant_of_has_deriv_right_zero hcont hw τ ⟨hτ, le_rfl⟩
  have h0 : (NormedSpace.exp ((0 : ℝ) • lcQ Q)) (z 0) = x := by
    rw [zero_smul ℝ (lcQ Q), NormedSpace.exp_zero]
    simp [hz, lcZ_zero hLip]
  rw [h0] at hconst
  have hneg : ouExp Q τ ((NormedSpace.exp (τ • lcQ Q)) (z τ)) = z τ := by
    have : ouExp Q τ * NormedSpace.exp (τ • lcQ Q) = 1 := by
      have := ul2_exp_mul_neg Q τ
      unfold ouExp at this ⊢
      rwa [neg_neg] at this
    rw [← mul_apply_eq_comp, this, one_apply_eq_self]
  rw [hconst] at hneg
  exact hneg.symm

/-- The OU flow: `lcFlow = e^{-τQ} x + lcU`. -/
theorem ul2_lcFlow_ou (Q : Matrix (Fin d) (Fin d) ℝ) {g : ℝ → Euc d} (hg : Continuous g) {r : ℝ}
    (hr : 0 ≤ r) (x : Euc d) {τ : ℝ} (hτ : 0 ≤ τ) :
    lcFlow Q (fun _ => (0 : Euc d)) (fun _ _ => (0 : Euc d)) g r (r + τ) x =
      ouExp Q τ x + lcU Q g r (r + τ) := by
  rw [lcFlow_add, ul2_lcZ_eq Q hg hr x hτ]

/-! ### Restarting the noise -/

/-- `lcU` only depends on the path on `[0,τ]`. -/
theorem ul2_lcU_congr (Q : Matrix (Fin d) (Fin d) ℝ) {g g' : ℝ → Euc d} {τ : ℝ} (hτ : 0 ≤ τ)
    (h : ∀ s ∈ Icc 0 τ, g s = g' s) : lcU Q g 0 τ = lcU Q g' 0 τ := by
  unfold lcU
  rw [h τ ⟨hτ, le_rfl⟩, h 0 ⟨le_rfl, hτ⟩]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hτ] at hu
  rw [h u hu]

/-- `lcU Q g r (r+τ) = lcU Q (g(r+·) - g r) 0 τ`. -/
theorem ul2_lcU_shift (Q : Matrix (Fin d) (Fin d) ℝ) (g : ℝ → Euc d) (r τ : ℝ) :
    lcU Q g r (r + τ) = lcU Q (fun s => g (r + s) - g r) 0 τ := by
  unfold lcU
  simp only [add_zero, sub_self, sub_zero]
  congr 1
  have := intervalIntegral.integral_comp_add_left (a := 0) (b := τ)
    (fun u : ℝ => (NormedSpace.exp ((-(r + τ - u)) • lcQ Q)) (lcQ Q (g u - g r))) r
  simp only [add_zero] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun u _ => ?_
  congr 3
  ring

section Prob

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ} {ν : ℝ} (Q : Matrix (Fin d) (Fin d) ℝ)

/-- The restarted OU shift has the same law `ouLaw Q ν τ`. -/
theorem ou_law_shift [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (hν : 0 ≤ ν)
    {r τ : ℝ} (hr : 0 ≤ r) (hτ : 0 ≤ τ) :
    HasLaw (fun ω => lcU Q (fun v => lcNoiseE W (fun _ => ν) v ω) r (r + τ)) (ouLaw Q ν τ) P := by
  have hc : Continuous fun _ : ℝ => ν := continuous_const
  obtain ⟨hW', hshift⟩ := lc_noise_shift hW hc (fun _ => hν) hr
  have key := ou_law Q τ hW' hν hτ
  have heq : (fun ω => lcU Q (fun v => lcNoiseE W (fun _ => ν) v ω) r (r + τ)) =
      fun ω => lcU Q (fun v => lcNoiseE (shiftProc W (lcTau (fun _ => ν) r).toNNReal)
        (fun _ => ν) v ω) 0 τ := by
    funext ω
    rw [ul2_lcU_shift]
    refine ul2_lcU_congr Q hτ fun s hs => ?_
    have := hshift s hs.1 ω
    simp only [lcNoiseE]
    rw [this, ← WithLp.toLp_sub]
  rw [heq]
  exact key

/-- **`lcSg_ou`.**  The engine semigroup with the OU data is the Mehler semigroup `ouSg`:
`lcSg … r (r+τ) h x = ouSg Q ν τ h x` for `0 ≤ r`, `0 ≤ τ`, `h` measurable. -/
theorem lcSg_ou [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (hν : 0 ≤ ν)
    {r τ : ℝ} (hr : 0 ≤ r) (hτ : 0 ≤ τ) {h : Euc d → ℝ} (hh : Measurable h) (x : Euc d) :
    lcSg P W (fun _ => ν) Q (fun _ => (0 : Euc d)) (fun _ _ => (0 : Euc d)) r (r + τ) h x =
      ouSg Q ν τ h x := by
  have hc : Continuous fun _ : ℝ => ν := continuous_const
  have hGc : ∀ ω, Continuous fun v => lcNoiseE W (fun _ => ν) v ω := fun ω => lc_noiseE_cont hW hc ω
  unfold lcSg ouSg
  have h1 : ∀ ω, h (lcFlow Q (fun _ => (0 : Euc d)) (fun _ _ => (0 : Euc d))
      (fun v => lcNoiseE W (fun _ => ν) v ω) r (r + τ) x) =
      h (ouExp Q τ x + lcU Q (fun v => lcNoiseE W (fun _ => ν) v ω) r (r + τ)) := fun ω => by
    rw [ul2_lcFlow_ou Q (hGc ω) hr x hτ]
  simp_rw [h1]
  have := (ou_law_shift Q hW hν hr hτ).integral_comp
    (f := fun y => h (ouExp Q τ x + y)) ((hh.comp (measurable_const_add _)).aestronglyMeasurable)
  exact this

end Prob

/-! ### Kolmogorov equation -/

section Kolm

variable (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ}

/-- `IsLocalBackwardSolution` only depends on the drift and on `u` on `[0,t]`. -/
theorem ul2_solution_congr {ν : ℝ → ℝ} {b b' : ℝ → Euc d → Euc d} {t : ℝ} {f : Euc d → ℝ}
    {u u' : ℝ → Euc d → ℝ} (ht0 : 0 ≤ t) (hbb : ∀ r ∈ Icc 0 t, ∀ x, b r x = b' r x)
    (huu : ∀ r ∈ Icc 0 t, u r = u' r) (h : IsLocalBackwardSolution ν b t f u) :
    IsLocalBackwardSolution ν b' t f u' where
  c2 r hr := by rw [← huu r hr]; exact h.c2 r hr
  bdd := by
    obtain ⟨B, hB⟩ := h.bdd
    exact ⟨B, fun r hr x => by rw [← huu r hr]; exact hB r hr x⟩
  cont := by
    have : (fun p : Icc (0 : ℝ) t × Euc d => u' p.1 p.2) = fun p => u p.1 p.2 := by
      funext p
      rw [huu p.1 p.1.2]
    rw [this]
    exact h.cont
  terminal := by rw [← huu t ⟨ht0, le_rfl⟩]; exact h.terminal
  time_deriv x r hr := by
    have h1 := h.time_deriv x r hr
    have hev : (fun r' => u r' x) =ᶠ[𝓝 r] fun r' => u' r' x := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr'
      rw [huu r' ⟨hr'.1.le, hr'.2.le⟩]
    rw [huu r ⟨hr.1.le, hr.2.le⟩, hbb r ⟨hr.1.le, hr.2.le⟩ x] at h1
    exact h1.congr_of_eventuallyEq hev.symm

/-- **`ou_backward`.**  For `h ∈ C²` with `h, Dh, D²h` bounded and `ν ≥ 0`, `0 ≤ t`, the function
`r ↦ ouSg Q ν (t - r) h` (the autonomous reparametrisation of `τ ↦ ouSg Q ν τ h`) is a bounded classical
backward solution of `∂_r u + ν Δu - ⟨Qx, ∇u⟩ = 0`, `u t = h`. -/
theorem ou_backward (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) {h : Euc d → ℝ} (hf : ContDiff ℝ 2 h)
    {M : ℝ} (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) :
    IsLocalBackwardSolution (fun _ => ν) (fun _ x => -(Torus.matVec Q x)) t h
      (fun r => ouSg Q ν (t - r) h) := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  have := hP
  have hsol := lc_backward hW (continuous_const : Continuous fun _ : ℝ => ν) (fun _ => hν)
    (fun _ => le_rfl) (ul2_lcHyp_zero Q) ht hf hM
  refine ul2_solution_congr ht (fun r _ x => by simp) (fun r hr => ?_) hsol
  funext x
  have := lcSg_ou Q hW hν hr.1 (sub_nonneg.2 hr.2) hf.continuous.measurable x
  rwa [add_sub_cancel] at this

/-- **`ou_backward`, `∂_r` form.**  For `r ∈ (0,t)`:
`∂_r [ouSg Q ν (t - r) h x] = -(ν Δ(ouSg Q ν (t-r) h)(x) + ⟨-Qx, ∇ ouSg Q ν (t-r) h (x)⟩)`. -/
theorem ou_backward_hasDerivAt (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) {h : Euc d → ℝ}
    (hf : ContDiff ℝ 2 h) {M : ℝ} (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) {r : ℝ}
    (hr : r ∈ Ioo 0 t) (x : Euc d) :
    HasDerivAt (fun r' => ouSg Q ν (t - r') h x)
      (-(ν * Laplacian.laplacian (ouSg Q ν (t - r) h) x +
        inner ℝ (-(Torus.matVec Q x)) (gradient (ouSg Q ν (t - r) h) x))) r :=
  (ou_backward Q hν ht hf hM).time_deriv x r hr

/-- **Forward Kolmogorov equation.**  For `τ > 0`:
`∂_τ ouSg Q ν τ h x = ν Δ(ouSg Q ν τ h)(x) + ⟨-Qx, ∇(ouSg Q ν τ h)(x)⟩`. -/
theorem ou_forward_hasDerivAt (hν : 0 ≤ ν) {h : Euc d → ℝ} (hf : ContDiff ℝ 2 h) {M : ℝ}
    (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) {τ : ℝ} (hτ : 0 < τ) (x : Euc d) :
    HasDerivAt (fun s => ouSg Q ν s h x)
      (ν * Laplacian.laplacian (ouSg Q ν τ h) x +
        inner ℝ (-(Torus.matVec Q x)) (gradient (ouSg Q ν τ h) x)) τ := by
  set t : ℝ := 2 * τ with ht
  have ht0 : 0 ≤ t := by positivity
  have hr : t - τ ∈ Ioo 0 t := ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
  have hd := ou_backward_hasDerivAt Q hν ht0 hf hM hr x
  rw [sub_sub_cancel] at hd
  have hc := hd.scomp τ ((hasDerivAt_id τ).const_sub t)
  have e : ((fun r' => ouSg Q ν (t - r') h x) ∘ (HSub.hSub t : ℝ → ℝ)) =
      fun s => ouSg Q ν s h x := by
    funext s
    simp [sub_sub_cancel]
  rw [e] at hc
  refine hc.congr_deriv ?_
  simp

/-! ### The semigroup at time zero -/

theorem ouLaw_zero (hν : 0 ≤ ν) : ouLaw Q ν 0 = Measure.dirac 0 := by
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  have h0 : ouCov Q ν 0 = 0 := by
    ext i j
    simp [ouCov]
  rw [ou_charFun Q hν le_rfl, charFun_dirac, h0]
  simp

theorem ouSg_zero (hν : 0 ≤ ν) (h : Euc d → ℝ) (x : Euc d) : ouSg Q ν 0 h x = h x := by
  unfold ouSg
  rw [ouLaw_zero Q hν, integral_dirac, ouExp_zero]
  simp

end Kolm

end HRS.MS.Ul
