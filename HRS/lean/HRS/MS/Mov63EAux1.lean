import HRS.MS.Mov63CAux15
import HRS.MS.Mov63DAux3

/-!
# S6.3, packet N6 (part 1): per-packet plan, statement checks, and the Hermite-coefficient identity of a mild solution

Namespace `HRS.MS.Mov63`, helper prefix `mne_` (`MneMild`, `mneF`, ...).  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`); not manuscript rows.
Files `Mov63EAux1` ... `Mov63EAux12` (about 2,900 lines).  Input: the mild solution of `mov63_mild_existence` (N5);
output: everything about `ρ_t = ρ₀ + √ρ₀ V_t` (`V_t` = the unique `C³` representative of `v_t ∈ Σ^m`, `mn_repFun 3`) that does not
need positivity, plus the weak identity for ALL `ψ ∈ C_b²`, with the nonnegativity `ρ_t ≥ 0` isolated as a single hypothesis.

## Checks against the real definitions (all done before any proof; no statement was false, no hypothesis was found insufficient)

* `IsWholeMeanFieldSolution D T ρ` (`Dynamics.lean:128`): `density` (`IsProbDensity`: **`nonneg`**, `measurable`, `integral_one`) and `second_moment`
  for `t ∈ [0,T]`, and `weak`: for every `ψ` with `MemCb 2 ψ` and `t ∈ [0,T]`,
  `pair (withDensityReal (ρ t)) ψ - pair (withDensityReal (ρ 0)) ψ = ∫_{[0,t]} (pair (ρ r) (β⁻¹Δψ - ⟨∇V,∇ψ⟩) + interactionPairingW D ψ (ρ r) (ρ r))`.
  `withDensityReal ρ = volume.withDensity (ofReal ∘ ρ)` and the Bochner integrals ignore signs/integrability, so the weak identity is only meaningful
  for `ρ_r ≥ 0` (then `pair = ∫ ρ_r f`, and `interactionPairingW` is the symmetrised pairing, `self_pairing_rd_proof`).  Hence N6a is stated
  with the hypothesis `hnn : ∀ t ≥ 0, ∀ x, 0 ≤ mneP t x`.
* `MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ` (`Moving.lean:248`): `solution` (all `T`), `init` (pointwise `ρ 0 x = ρ₀ x (1 + f0 x)`, with
  `f0 = V_0/√ρ₀ = mneF0fun`), `weighted` (`MemOsc m (movV ρ₀ ρ t)`, norm `≤ r e^{-c₀t}`), `cont` (`ofFun m (movV ρ₀ ρ ·)` continuous on `[0,∞)`),
  `regular` (`ρ t` continuous).  `movV ρ₀ (mneP) t = V_t` pointwise, `ofFun m V_t = v_t` (`mne_movV`, `mneV_ofFun`), so `weighted`/`cont` are the data of `v`.
  For `t < 0` the class says nothing: `mneP t := mneP (max t 0)`.
* Mass: `MovMassZero ρ (v t)` (N5) is `∫ √ρ₀ V_t = 0`, hence `∫ ρ_t = 1` (`mne_mass_zero`, `mne_isProb`).
* Everything in `IsWholeMeanFieldSolution` except `nonneg` is proved (`mne_class`, `mne_second_moment`, `mne_weak`); positivity is N7.

## How N7 / N9 combine with this packet

N7 (maximum principle) needs the classical equation: `mne_Q_hasDeriv` (`∂_t Q = νΔQ + ⟨ν∇log ρ₀ + F_t, ∇Q⟩ + (div F_t + ⟨∇log ρ₀, F_t⟩) Q`,
`Q_t = ρ_t/ρ₀ = 1 + V_t/√ρ₀`, `F_t = ∇g*(√ρ₀ V_t)` = `mneFo`, right derivative at `t = 0`, two-sided for `t > 0`, no positivity used),
the regularity `ρ_t ∈ C³` (`mne_rho_cd`), `mneQ_cd`, the joint continuity of `(t,x) ↦ V_t, ∇h_t, Δh_t, F_t, div F_t, div Y_t` on `[0,∞)×ℝ^d`
(`mne_joint`, `mne_e_joint`), and the Gaussian bounds (`mne_flux_bound`, `mnc_h_gauss`).  N7 concludes `∀ t ≥ 0, ∀ x, 0 ≤ mneP t x`.
N9 then applies `mov63_signed_solution` (assembly with N5): given the nonnegativity (N7) it gets `MovInSmallClass d s q β ρ₀ m (C‖x₀‖) (c/2) f0 (mneP ..)` with
`c` the decay rate of N5; the remaining conjuncts of `MovNonlinearConclusion` (`MovInitialClass` for `f0`, `MovDecayBounds`, `ψ`-class) are N8/N9.

## Route (deviations from `SC63_REPORT` 2.4, all recorded)

1. (`Aux1`) Mild ⇒ coefficient identity.  Instead of "mild ⇒ `S₀`-Duhamel by the Volterra identity" the scalar functionals `⟨h̃_α,·⟩` are applied to
   the Volterra equation of `mov2d_G` (`mne_G_pair`, scalar Volterra with continuous data) and the abstract convolution/Fubini identity
   `mne_voc_abstract` (triangle swap `mne_tri_swap`) gives `⟨h̃_α,v_t⟩ = e^{-tq|α|}⟨h̃_α,v_0⟩ + ∫ e^{-(t-τ)q|α|}⟨h̃_α,F(v_τ)⟩`,
   `F(v) = -Rv + B(v,v)`; then `mne_voc_integral` (FTC) gives the integral form `mne_coeff_int` (reverse of `mnc_diff_coeff`).
2. (`Aux2`) Coefficients ⇒ all `φ ∈ C_c^∞`: `mne_weak_lin` (partial sums over `degree ≤ N`, dilated Parseval `mne_parseval_d`, Bessel bound
   `mne_pair_partial`, dominated convergence in time; `S₀` acts as `q|α|` on the coefficients of `φ` by `mov2d_dcoeff_S0`).
3. (`Aux3`) `mne_pair_e`: for `ψ = φ/√ρ₀`, `∫ ψ div Y_u = -⟨S₀φ,u⟩ + ⟨φ,-Ru + B(u,u)⟩` (all `u ∈ Σ^m`, no positivity), `Y_u = ν∇ρ_u + ρ_u(qx + ∇g*ρ_u)`:
   signed copy of `mnc_decomp` (`mne_decomp_signed`) + `mnc_lin_osc`/`mnc_quad_osc` + two integrations by parts.
4. (`Aux4`,`Aux5`) Joint continuity (`mne_joint_lin`, `mne_joint`, explicit divergence `mne_e_formula`, `mne_e_joint`) and the **pointwise Duhamel formula**
   `h_t(x) - h_0(x) = ∫_0^t div Y_s(x) ds` (`mne_pointwise`), by testing against `C_c^∞` and the fundamental lemma of the calculus of variations.
   This replaces the planned "N2b pointwise identification of `R`, `S`, `B_ext`" (done through test functions) and the planned approximation of `ψ ∈ C_b²`
   by `C_c^∞` (not needed: see 5).
5. (`Aux6`..`Aux8`) `C_b²` tests: Gaussian majorants (`mne_flux_bound`), global integration by parts via the cutoffs of `Mov63CAux8` (`mne_ibp_glob`), `mne_J`, `mne_integrand`
   (with `self_pairing_rd_proof`), global Fubini, and `mne_weak` = the `weak` field for all `ψ ∈ C_b²`.
6. (`Aux9`) `mne_class` (`MovInSmallClass`), (`Aux10`,`Aux11`) classical derivative `mne_hasDeriv(At)` and the `Q`-equation `mne_Q_eq`, `mne_Q_hasDeriv(At)`,
   (`Aux12`) `mov63_signed_solution`.

## Not done (gaps)

* `v ∈ C^1([0,∞); Σ^{m-2})` as a statement about the `Σ`-valued path is NOT proved (it needs `S₀ : Σ^m → Σ^{m-2}` as a bounded operator, absent from the
  repository); the pointwise time derivative (`mne_hasDeriv`) is proved instead, which is what the maximum principle uses.
* Positivity `ρ_t ≥ 0` (N7); `MovInitialClass`/decay bounds/`ψ`-class conjunct (N8, N9).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Scalar
open intervalIntegral

lemma mne_tri_swap_cont {t : ℝ} (ht : 0 ≤ t) {K : ℝ → ℝ → ℝ} (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2)) :
    ∫ u in (0:ℝ)..t, ∫ w in (0:ℝ)..(t - u), K u w = ∫ τ in (0:ℝ)..t, ∫ u in (0:ℝ)..τ, K u (τ - u) := by
  classical
  set Φ : ℝ → ℝ → ℝ := fun u τ => if u ≤ τ then K u (τ - u) else 0 with hΦ
  have hmeasK : Measurable (fun p : ℝ × ℝ => K p.1 p.2) := hK.measurable
  have hmeas : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable (fun p : ℝ × ℝ => K p.1 (p.2 - p.1)) :=
      hmeasK.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst))
    have h2 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
    exact Measurable.ite h2 h1 measurable_const
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := t)).prod (isCompact_Icc (a := (0:ℝ)) (b := t)) |>.exists_bound_of_continuousOn
    hK.continuousOn
  have hΦb : ∀ u ∈ Icc (0:ℝ) t, ∀ τ ∈ Icc (0:ℝ) t, |Φ u τ| ≤ max M 0 := by
    intro u hu τ hτ
    simp only [hΦ]
    split_ifs with h
    · have := hM (u, τ - u) ⟨hu, ⟨by linarith, by linarith [hu.1, hτ.2]⟩⟩
      exact (by simpa using this : |K u (τ - u)| ≤ M).trans (le_max_left _ _)
    · simp
  have hint : IntegrableOn (Function.uncurry Φ) (uIoc 0 t ×ˢ uIoc 0 t) := by
    rw [uIoc_of_le ht]
    refine Measure.integrableOn_of_bounded (M := max M 0) ?_ hmeas.aestronglyMeasurable ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact (ENNReal.mul_lt_top (by simp) (by simp)).ne
    · refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).2 (Eventually.of_forall fun p hp => ?_)
      have := hΦb p.1 ⟨hp.1.1.le, hp.1.2⟩ p.2 ⟨hp.2.1.le, hp.2.2⟩
      rw [Real.norm_eq_abs]; exact this
  have swap := intervalIntegral_intervalIntegral_swap hint
  have secI : ∀ g : ℝ → ℝ, Measurable g → (∀ x ∈ Icc (0:ℝ) t, |g x| ≤ max M 0) → IntervalIntegrable g volume 0 t := by
    intro g hg hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    refine Measure.integrableOn_of_bounded (M := max M 0) (by simp) hg.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
    simpa using hb x ⟨hx.1.le, hx.2⟩
  -- inner integral over τ
  have e1 : ∀ u ∈ Icc (0:ℝ) t, ∫ τ in (0:ℝ)..t, Φ u τ = ∫ w in (0:ℝ)..(t - u), K u w := by
    intro u hu
    have hI : ∀ a b, a ∈ Icc (0:ℝ) t → b ∈ Icc (0:ℝ) t → IntervalIntegrable (Φ u) volume a b := by
      intro a b ha hb
      have h0 : IntervalIntegrable (Φ u) volume 0 t :=
        secI _ (hmeas.comp (measurable_const.prodMk measurable_id)) (fun x hx => hΦb u hu x hx)
      exact (h0.mono_set (by
        rw [uIcc_of_le ht]
        exact uIcc_subset_Icc ha hb))
    rw [← integral_add_adjacent_intervals (hI 0 u ⟨le_rfl, ht⟩ hu) (hI u t hu ⟨ht, le_rfl⟩ |> fun h => h)]
    have z1 : ∫ τ in (0:ℝ)..u, Φ u τ = 0 := by
      rw [intervalIntegral.integral_of_le hu.1]
      have : ∀ᵐ τ ∂(volume.restrict (Ioc 0 u)), Φ u τ = 0 := by
        have hne : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ u := by
          simp [ae_iff]
        refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
        filter_upwards [hne] with τ hτ hτm
        have : τ < u := lt_of_le_of_ne hτm.2 hτ
        simp [hΦ, not_le.2 this]
      rw [integral_congr_ae this]; simp
    have z2 : ∫ τ in u..t, Φ u τ = ∫ τ in u..t, K u (τ - u) := by
      refine intervalIntegral.integral_congr (fun τ hτ => ?_)
      rw [uIcc_of_le hu.2] at hτ
      simp [hΦ, hτ.1]
    rw [z1, z2, zero_add]
    have := intervalIntegral.integral_comp_sub_right (fun w => K u w) (a := u) (b := t) u
    simpa using this
  have e2 : ∀ τ ∈ Icc (0:ℝ) t, ∫ u in (0:ℝ)..t, Φ u τ = ∫ u in (0:ℝ)..τ, K u (τ - u) := by
    intro τ hτ
    have hI : ∀ a b, a ∈ Icc (0:ℝ) t → b ∈ Icc (0:ℝ) t → IntervalIntegrable (fun u => Φ u τ) volume a b := by
      intro a b ha hb
      have h0 : IntervalIntegrable (fun u => Φ u τ) volume 0 t :=
        secI _ (hmeas.comp (measurable_id.prodMk measurable_const)) (fun x hx => hΦb x hx τ hτ)
      exact (h0.mono_set (by
        rw [uIcc_of_le ht]
        exact uIcc_subset_Icc ha hb))
    rw [← integral_add_adjacent_intervals (hI 0 τ ⟨le_rfl, ht⟩ hτ) (hI τ t hτ ⟨ht, le_rfl⟩)]
    have z1 : ∫ u in τ..t, Φ u τ = 0 := by
      rw [intervalIntegral.integral_of_le hτ.2]
      have : ∀ᵐ u ∂(volume.restrict (Ioc τ t)), Φ u τ = 0 := by
        refine ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => ?_)
        simp [hΦ, not_le.2 hu.1]
      rw [integral_congr_ae this]; simp
    have z2 : ∫ u in (0:ℝ)..τ, Φ u τ = ∫ u in (0:ℝ)..τ, K u (τ - u) := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [uIcc_of_le hτ.1] at hu
      simp [hΦ, hu.2]
    rw [z1, z2, add_zero]
  calc ∫ u in (0:ℝ)..t, ∫ w in (0:ℝ)..(t - u), K u w
      = ∫ u in (0:ℝ)..t, ∫ τ in (0:ℝ)..t, Φ u τ := by
        refine intervalIntegral.integral_congr (fun u hu => ?_)
        rw [uIcc_of_le ht] at hu
        exact (e1 u hu).symm
    _ = ∫ τ in (0:ℝ)..t, ∫ u in (0:ℝ)..t, Φ u τ := swap
    _ = _ := by
        refine intervalIntegral.integral_congr (fun τ hτ => ?_)
        rw [uIcc_of_le ht] at hτ
        exact e2 τ hτ

lemma mne_tri_swap {t : ℝ} (ht : 0 ≤ t) {K : ℝ → ℝ → ℝ}
    (hK : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Icc 0 t ×ˢ Icc 0 t)) :
    ∫ u in (0:ℝ)..t, ∫ w in (0:ℝ)..(t - u), K u w = ∫ τ in (0:ℝ)..t, ∫ u in (0:ℝ)..τ, K u (τ - u) := by
  set c : ℝ → ℝ := fun x => max 0 (min x t) with hcdef
  have hc : Continuous c := by fun_prop
  have hcm : ∀ x, c x ∈ Icc (0:ℝ) t := fun x => ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩
  have hcid : ∀ x ∈ Icc (0:ℝ) t, c x = x := fun x hx => by
    simp only [hcdef]; rw [min_eq_left hx.2, max_eq_right hx.1]
  have hK' : Continuous (fun p : ℝ × ℝ => K (c p.1) (c p.2)) :=
    hK.comp_continuous ((hc.comp continuous_fst).prodMk (hc.comp continuous_snd)) (fun p => ⟨hcm _, hcm _⟩)
  have := mne_tri_swap_cont (K := fun u w => K (c u) (c w)) ht hK'
  convert this using 1
  · refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [uIcc_of_le ht] at hu
    refine intervalIntegral.integral_congr (fun w hw => ?_)
    rw [uIcc_of_le (by linarith [hu.2])] at hw
    rw [hcid u hu, hcid w ⟨hw.1, by linarith [hu.1, hw.2]⟩]
  · refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    rw [uIcc_of_le ht] at hτ
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [uIcc_of_le hτ.1] at hu
    rw [hcid u ⟨hu.1, by linarith [hu.2, hτ.2]⟩, hcid (τ - u) ⟨by linarith [hu.2], by linarith [hu.1, hτ.2]⟩]

/-- Variation of constants (integral form) implies the integral form of the ODE `c' = -λ c + g`. -/
lemma mne_voc_integral {lam T : ℝ} (hT : 0 ≤ T) {c g : ℝ → ℝ} (hc : ContinuousOn c (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T))
    (h : ∀ t ∈ Icc (0:ℝ) T, c t = Real.exp (-lam * t) * c 0 + ∫ x in Icc (0:ℝ) t, Real.exp (-lam * (t - x)) * g x) :
    ∀ t ∈ Icc (0:ℝ) T, c t - c 0 = ∫ x in Icc (0:ℝ) t, (-lam * c x + g x) := by
  intro t ht
  set E : ℝ → ℝ := fun y => c 0 + ∫ x in (0:ℝ)..y, Real.exp (lam * x) * g x with hE
  have hgE : ContinuousOn (fun x => Real.exp (lam * x) * g x) (Icc 0 T) :=
    ((continuous_const.mul continuous_id).rexp.continuousOn).mul hg
  have hcE : ∀ y ∈ Icc (0:ℝ) T, c y = Real.exp (-lam * y) * E y := by
    intro y hy
    rw [h y hy]
    simp only [hE]
    have e : ∫ x in Icc (0:ℝ) y, Real.exp (-lam * (y - x)) * g x =
        Real.exp (-lam * y) * ∫ x in (0:ℝ)..y, Real.exp (lam * x) * g x := by
      rw [intervalIntegral.integral_of_le hy.1, ← integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [← mul_assoc, ← Real.exp_add]
      congr 2; ring
    rw [e]; ring
  have hder : ∀ y ∈ Ioo (0:ℝ) T, HasDerivAt c (-lam * c y + g y) y := by
    intro y hy
    have hnh : Icc (0:ℝ) T ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
    have hint : IntervalIntegrable (fun x => Real.exp (lam * x) * g x) volume 0 y :=
      (hgE.mono (Icc_subset_Icc le_rfl hy.2.le)).intervalIntegrable_of_Icc hy.1.le
    have hcont : ContinuousAt (fun x => Real.exp (lam * x) * g x) y := hgE.continuousAt hnh
    have hd := intervalIntegral.integral_hasDerivAt_right hint
      ((hgE.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo y hy) hcont
    have hE' : HasDerivAt E (Real.exp (lam * y) * g y) y := by
      simpa [hE] using hd.const_add (c 0)
    have h1 : HasDerivAt (fun x => Real.exp (-lam * x)) (Real.exp (-lam * y) * (-lam)) y := by
      simpa using ((hasDerivAt_id y).const_mul (-lam)).exp
    have h2 := h1.mul hE'
    have h3 : HasDerivAt (fun x => Real.exp (-lam * x) * E x)
        (-lam * c y + g y) y := by
      convert h2 using 1
      rw [hcE y ⟨hy.1.le, hy.2.le⟩]
      have : Real.exp (-lam * y) * Real.exp (lam * y) = 1 := by rw [← Real.exp_add]; simp
      linear_combination (-(g y)) * this
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hnh] with x hx
    exact hcE x hx
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0; simp
  · have hsub : Icc (0:ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    have hf : ContinuousOn (fun x => -lam * c x + g x) (Icc 0 t) :=
      ((continuousOn_const.mul (hc.mono hsub)).add (hg.mono hsub))
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpos.le (hc.mono hsub)
      (fun x hx => hder x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩) (hf.intervalIntegrable_of_Icc hpos.le)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpos.le, this]


end Scalar

section Levels

lemma mne_a_bounds (H : Mov2dTh d s β q ρ) : 1 ≤ movA d s ∧ movA d s < 2 :=
  ⟨le_max_left _ _, (mov2d_a_bounds d H.hd H.hsd).2⟩

lemma mne_lvl2 (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) :
    0 ≤ m - movA d s - movA d s := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast H.hd
  have := (mne_a_bounds H).2
  linarith

lemma mne_ipL_j {f : Euc d → ℝ} {r r' : ℝ} (h : r' ≤ r) (hr' : 0 ≤ r') (y : OscSpace d r) :
    mnc_ipL f hr' (mov2d_j h y) = mnc_ipL f (hr'.trans h) y := by
  simp only [mnc_ipL, ContinuousLinearMap.comp_apply]
  rw [movlin_j_comp h hr' y]

lemma mne_ipL_Sm (hβ : 0 < β) (hq : 0 < q) {r r' : ℝ} (h : r' ≤ r) (hr' : 0 ≤ r')
    (α : MultiIndex d) {τ : ℝ} (hτ : 0 < τ) (y : OscSpace d r') :
    mnc_ipL (mnc_hα d β q α) (hr'.trans h) (mov2d_Sm β q h τ y) =
      Real.exp (-(τ * q * (α.degree : ℝ))) * mnc_ipL (mnc_hα d β q α) hr' y := by
  obtain ⟨f, hf, rfl⟩ := mnc_exists_fun_real hr' y
  have hα2 : MemLp (mnc_hα d β q α) 2 (volume : Measure (Euc d)) := (mnc_hα_good hβ hq α).1.l2
  rw [mov2d_Sm_ofFun hβ hq h (Or.inl hτ) hf, max_eq_left hτ.le]
  obtain ⟨K, -, hK⟩ := mov2d_expS0_bdd (d := d) hβ hq h hτ.le (Or.inl hτ)
  have hmem := (hK f hf).1
  rw [mnc_ipL_ofFun hα2 _ hmem, mnc_ipL_ofFun hα2 _ hf]
  have hd := mov_expS0_dcoeff hβ hq hτ.le hf.1 α
  unfold mov2b_dcoeff at hd
  have e1 : ∫ x, mnc_hα d β q α x * mov_expS0 β q τ f x =
      ∫ x, mov_expS0 β q τ f x * (Real.sqrt (mov_dil β q ^ d) * hermiteFunD α (mov_dil β q • x)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [mnc_hα]; ring)
  have e2 : ∫ x, mnc_hα d β q α x * f x =
      ∫ x, f x * (Real.sqrt (mov_dil β q ^ d) * hermiteFunD α (mov_dil β q • x)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [mnc_hα]; ring)
  rw [e1, e2, hd]

variable (H : Mov2dTh d s β q ρ)

/-- The pairing of the Volterra solution `G(σ) y` with `h̃_α`: scalar Volterra equation. -/
lemma mne_G_pair (r : ℝ) (hr : 0 ≤ r) (hr2 : 0 ≤ r - movA d s) (α : MultiIndex d) {σ : ℝ} (hσ : 0 ≤ σ)
    (y : OscSpace d r) :
    mnc_ipL (mnc_hα d β q α) hr (mov2d_G H r σ y) =
      Real.exp (-(σ * q * (α.degree : ℝ))) * mnc_ipL (mnc_hα d β q α) hr y -
        ∫ w in (0 : ℝ)..σ, Real.exp (-((σ - w) * q * (α.degree : ℝ))) *
          mnc_ipL (mnc_hα d β q α) hr2 (mov2d_R d s β q ρ r (mov2d_G H r w y)) := by
  have hβ := H.hβ
  have hq := H.hq
  have ha := mov2d_a_bounds d H.hd H.hsd
  rw [mov2d_G_duhamel H r hσ y, map_sub]
  congr 1
  · rcases hσ.eq_or_lt with h0 | hpos
    · subst h0
      rw [mov2d_Sm_zero hβ hq]
      simp
    · exact mne_ipL_Sm hβ hq (le_refl r) hr α hpos y
  · set T0 : ℝ := σ + 1 with hT0def
    have hT0 : 0 < T0 := by positivity
    obtain ⟨Kc, hK⟩ := mov2c_K_ker (mov2d_hyp' H hT0) ha.1 r
    have hθ : 0 < 1 - movA d s / 2 := by linarith [ha.2]
    have hθ1 : 1 - movA d s / 2 ≤ 1 := by linarith [ha.1]
    have hint := mov2c_vol_int hK hθ hθ1 (y := fun w => mov2d_G H r w y)
      ((mov2d_G_cont H r y).mono Icc_subset_Ici_self) (t := σ) ⟨hσ, by linarith⟩
    have hint' : IntervalIntegrable (fun u => mov2d_Sm β q (sub_le_self r ha.1) (σ - u)
        (mov2d_R d s β q ρ r (mov2d_G H r u y))) volume 0 σ := hint
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm (mnc_ipL (mnc_hα d β q α) hr) hint']
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ σ := by simp [ae_iff]
    filter_upwards [hne] with u hu hmem
    rw [uIoc_of_le hσ] at hmem
    have hlt : u < σ := lt_of_le_of_ne hmem.2 hu
    exact mne_ipL_Sm hβ hq (sub_le_self r ha.1) hr2 α (by linarith) _

/-- Joint continuity of `(w,u) ↦ G(w) f(u)`. -/
lemma mne_G_joint (r T : ℝ) {S : Set ℝ} {f : ℝ → OscSpace d r} (hf : ContinuousOn f S) :
    ContinuousOn (fun p : ℝ × ℝ => mov2d_G H r p.1 (f p.2)) (Icc 0 T ×ˢ S) := by
  obtain ⟨N, hN⟩ := mov2d_G_bound H r T
  intro p0 hp0
  obtain ⟨w0, u0⟩ := p0
  obtain ⟨hw0, hu0⟩ := hp0
  have hf2 : ContinuousWithinAt (fun p : ℝ × ℝ => f p.2) (Icc 0 T ×ˢ S) (w0, u0) :=
    (hf u0 hu0).comp continuousWithinAt_snd (fun p hp => hp.2)
  have hsub : Tendsto (fun p : ℝ × ℝ => ‖f p.2 - f u0‖) (𝓝[Icc 0 T ×ˢ S] (w0, u0)) (𝓝 0) := by
    have := (hf2.sub (continuousWithinAt_const (b := f u0))).norm
    simpa [ContinuousWithinAt] using this
  have h1 : Tendsto (fun p : ℝ × ℝ => mov2d_G H r p.1 (f p.2 - f u0)) (𝓝[Icc 0 T ×ˢ S] (w0, u0)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun p : ℝ × ℝ => N * ‖f p.2 - f u0‖) ?_ (by simpa using hsub.const_mul N)
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact ((mov2d_G H r p.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hN p.1 hp.1) (norm_nonneg _))
  have h2 : ContinuousWithinAt (fun p : ℝ × ℝ => mov2d_G H r p.1 (f u0)) (Icc 0 T ×ˢ S) (w0, u0) :=
    ContinuousWithinAt.comp (g := fun w : ℝ => mov2d_G H r w (f u0)) (f := Prod.fst)
      (((mov2d_G_cont H r (f u0)).mono Icc_subset_Ici_self) w0 hw0) continuousWithinAt_fst
      (fun p (hp : p ∈ Icc 0 T ×ˢ S) => hp.1)
  have e : (fun p : ℝ × ℝ => mov2d_G H r p.1 (f p.2)) =
      fun p => mov2d_G H r p.1 (f p.2 - f u0) + mov2d_G H r p.1 (f u0) := by
    funext p
    rw [← map_add]
    congr 1
    abel
  rw [ContinuousWithinAt, e]
  simpa using h1.add h2

end Levels

section Abstract

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Abstract variation of constants (mild ⇒ scalar `S₀`-Duhamel for a functional).**  -/
lemma mne_voc_abstract (E : ℝ → ℝ) (hE : Continuous E) (ℓ1 : X →L[ℝ] ℝ) (ℓ2 : Y →L[ℝ] ℝ) (R : X →L[ℝ] Y)
    (G : ℝ → X →L[ℝ] X) (f jv : ℝ → X) {t : ℝ} (ht : 0 ≤ t)
    (hA1 : ∀ y : X, ∀ σ ∈ Icc (0 : ℝ) t,
      ℓ1 (G σ y) = E σ * ℓ1 y - ∫ w in (0 : ℝ)..σ, E (σ - w) * ℓ2 (R (G w y)))
    (hfc : ContinuousOn (fun p : ℝ × ℝ => ℓ2 (R (G p.1 (f p.2)))) (Icc 0 t ×ˢ Icc 0 t))
    (hf1 : ContinuousOn (fun u => ℓ1 (f u)) (Icc 0 t))
    (hκ0 : ContinuousOn (fun w => ℓ2 (R (G w (jv 0)))) (Icc 0 t))
    (hjv : ContinuousOn (fun τ => ℓ2 (R (jv τ))) (Icc 0 t))
    (hmild : ∀ τ ∈ Icc (0 : ℝ) t, IntervalIntegrable (fun u => G (τ - u) (f u)) volume 0 τ ∧
        jv τ = G τ (jv 0) + ∫ u in (0 : ℝ)..τ, G (τ - u) (f u)) :
    ℓ1 (jv t) = E t * ℓ1 (jv 0) + ∫ τ in (0 : ℝ)..t, E (t - τ) * (ℓ1 (f τ) - ℓ2 (R (jv τ))) := by
  have hEc : ∀ a : ℝ, Continuous fun τ => E (a - τ) := fun a => hE.comp (continuous_const.sub continuous_id)
  have cI : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 t) → IntervalIntegrable g volume 0 t := fun g hg =>
    hg.intervalIntegrable_of_Icc ht
  obtain ⟨hint, heq⟩ := hmild t ⟨ht, le_rfl⟩
  have hL : IntervalIntegrable (fun u => ℓ1 (G (t - u) (f u))) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at hint ⊢
    exact ℓ1.integrable_comp hint
  set P : ℝ → ℝ := fun u => E (t - u) * ℓ1 (f u) with hP
  set κ : ℝ → ℝ → ℝ := fun w u => ℓ2 (R (G w (f u))) with hκ
  set K : ℝ → ℝ → ℝ := fun u w => E ((t - u) - w) * κ w u with hK
  set I : ℝ → ℝ := fun u => ∫ w in (0 : ℝ)..(t - u), K u w with hI
  have hPc : ContinuousOn P (Icc 0 t) := (hEc t).continuousOn.mul hf1
  have hPint : IntervalIntegrable P volume 0 t := cI _ hPc
  have hGe : ∀ u ∈ Icc (0 : ℝ) t, ℓ1 (G (t - u) (f u)) = P u - I u := by
    intro u hu
    have := hA1 (f u) (t - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    rw [this]
  have hIint : IntervalIntegrable I volume 0 t := by
    refine (hPint.sub hL).congr (fun u hu => ?_)
    rw [uIoc_of_le ht] at hu
    have := hGe u ⟨hu.1.le, hu.2⟩
    show P u - ℓ1 (G (t - u) (f u)) = I u
    rw [this]; ring
  have hsplit : ∫ u in (0 : ℝ)..t, ℓ1 (G (t - u) (f u)) = (∫ u in (0 : ℝ)..t, P u) - ∫ u in (0 : ℝ)..t, I u := by
    rw [← intervalIntegral.integral_sub hPint hIint]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [uIcc_of_le ht] at hu
    exact hGe u hu
  -- the triangle
  have hKc : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Icc 0 t ×ˢ Icc 0 t) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => κ p.2 p.1) (Icc 0 t ×ˢ Icc 0 t) :=
      hfc.comp continuous_swap.continuousOn (fun p hp => ⟨hp.2, hp.1⟩)
    have h2 : Continuous (fun p : ℝ × ℝ => E ((t - p.1) - p.2)) :=
      hE.comp ((continuous_const.sub continuous_fst).sub continuous_snd)
    exact h2.continuousOn.mul h1
  have htri := mne_tri_swap ht hKc
  -- inner integrals
  have hin : ∀ τ ∈ Icc (0 : ℝ) t, ∫ u in (0 : ℝ)..τ, K u (τ - u) =
      E (t - τ) * (ℓ2 (R (jv τ)) - ℓ2 (R (G τ (jv 0)))) := by
    intro τ hτ
    obtain ⟨hintτ, heqτ⟩ := hmild τ hτ
    have e1 : ∫ u in (0 : ℝ)..τ, K u (τ - u) = E (t - τ) * ∫ u in (0 : ℝ)..τ, ℓ2 (R (G (τ - u) (f u))) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      simp only [hK, hκ]
      have : (t - u) - (τ - u) = t - τ := by ring
      rw [this]
    have e2 : ∫ u in (0 : ℝ)..τ, ℓ2 (R (G (τ - u) (f u))) =
        ℓ2 (R (∫ u in (0 : ℝ)..τ, G (τ - u) (f u))) := by
      have := ContinuousLinearMap.intervalIntegral_comp_comm (ℓ2.comp R) hintτ
      simpa using this
    have e3 : ∫ u in (0 : ℝ)..τ, G (τ - u) (f u) = jv τ - G τ (jv 0) := by
      rw [heqτ]; abel
    rw [e1, e2, e3, map_sub, map_sub]
  have hrhs1 : ∫ u in (0 : ℝ)..t, I u = ∫ τ in (0 : ℝ)..t, E (t - τ) * (ℓ2 (R (jv τ)) - ℓ2 (R (G τ (jv 0)))) := by
    rw [hI]
    simp only
    rw [htri]
    refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    rw [uIcc_of_le ht] at hτ
    exact hin τ hτ
  -- the free term
  have hG0 := hA1 (jv 0) t ⟨ht, le_rfl⟩
  have hjc : ContinuousOn (fun τ => E (t - τ) * ℓ2 (R (jv τ))) (Icc 0 t) := (hEc t).continuousOn.mul hjv
  have hkc : ContinuousOn (fun τ => E (t - τ) * ℓ2 (R (G τ (jv 0)))) (Icc 0 t) := (hEc t).continuousOn.mul hκ0
  have hfcont : ContinuousOn (fun τ => E (t - τ) * ℓ1 (f τ)) (Icc 0 t) := hPc
  calc ℓ1 (jv t) = ℓ1 (G t (jv 0)) + ∫ u in (0 : ℝ)..t, ℓ1 (G (t - u) (f u)) := by
        rw [heq, map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm ℓ1 hint]
    _ = E t * ℓ1 (jv 0) + ∫ τ in (0 : ℝ)..t, E (t - τ) * (ℓ1 (f τ) - ℓ2 (R (jv τ))) := by
        rw [hG0, hsplit, hrhs1]
        have h1 : ∫ τ in (0 : ℝ)..t, E (t - τ) * (ℓ2 (R (jv τ)) - ℓ2 (R (G τ (jv 0)))) =
            (∫ τ in (0 : ℝ)..t, E (t - τ) * ℓ2 (R (jv τ))) - ∫ τ in (0 : ℝ)..t, E (t - τ) * ℓ2 (R (G τ (jv 0))) := by
          rw [← intervalIntegral.integral_sub (cI _ hjc) (cI _ hkc)]
          refine intervalIntegral.integral_congr (fun τ _ => ?_)
          ring
        have h2 : ∫ τ in (0 : ℝ)..t, E (t - τ) * (ℓ1 (f τ) - ℓ2 (R (jv τ))) =
            (∫ τ in (0 : ℝ)..t, P τ) - ∫ τ in (0 : ℝ)..t, E (t - τ) * ℓ2 (R (jv τ)) := by
          rw [← intervalIntegral.integral_sub hPint (cI _ hjc)]
          refine intervalIntegral.integral_congr (fun τ _ => ?_)
          simp only [hP]; ring
        rw [h1, h2]
        have h3 : ∫ w in (0 : ℝ)..t, E (t - w) * ℓ2 (R (G w (jv 0))) =
            ∫ τ in (0 : ℝ)..t, E (t - τ) * ℓ2 (R (G τ (jv 0))) := rfl
        rw [h3]
        ring

end Abstract

section StepA

variable (H : Mov2dTh d s β q ρ) {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)

/-- The data of a mild solution (the conclusion of `mov63_mild_existence`, with `x₀ = v 0`). -/
structure MneMild (v : ℝ → OscSpace d (m : ℝ)) : Prop where
  cont : ContinuousOn v (Ici 0)
  mass : ∀ t, 0 ≤ t → MovMassZero ρ (mnd_m_nonneg hm) (v t)
  mild : ∀ t, 0 ≤ t →
    IntervalIntegrable (fun u => mov2d_G H ((m : ℝ) - movA d s) (t - u) (mov_B_ext H hm (v u) (v u)))
      volume 0 t ∧
    movJa H (m : ℝ) (v t) = mov2d_G H ((m : ℝ) - movA d s) t (movJa H (m : ℝ) (v 0)) +
      ∫ u in (0 : ℝ)..t, mov2d_G H ((m : ℝ) - movA d s) (t - u) (mov_B_ext H hm (v u) (v u))

/-- The right-hand side `F(v) = -R v + B(v,v) ∈ Σ^{m-a}`. -/
def mneF (v : ℝ → OscSpace d (m : ℝ)) (u : ℝ) : OscSpace d ((m : ℝ) - movA d s) :=
  -(mov2d_R d s β q ρ (m : ℝ) (v u)) + mov_B_ext H hm (v u) (v u)

variable {H hm}

lemma mneF_cont {v : ℝ → OscSpace d (m : ℝ)} (hv : ContinuousOn v (Ici 0)) :
    ContinuousOn (mneF H hm v) (Ici 0) := by
  unfold mneF
  have h1 := (mov2d_R d s β q ρ (m : ℝ)).continuous.comp_continuousOn hv
  have h2 : ContinuousOn (fun u => mov_B_ext H hm (v u)) (Ici 0) := (mov_B_ext H hm).continuous.comp_continuousOn hv
  exact h1.neg.add (h2.clm_apply hv)

/-- **Mild ⇒ coefficient variation of constants** for every dilated Hermite functional. -/
theorem mne_coeff_voc {v : ℝ → OscSpace d (m : ℝ)} (hmild : MneMild H hm v) (α : MultiIndex d) {t : ℝ}
    (ht : 0 ≤ t) :
    mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (v t) =
      Real.exp (-(t * q * (α.degree : ℝ))) * mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (v 0) +
      ∫ τ in (0 : ℝ)..t, Real.exp (-((t - τ) * q * (α.degree : ℝ))) *
        mnc_ipL (mnc_hα d β q α) (mnb_sub_a_nonneg H hm) (mneF H hm v τ) := by
  have ha := mne_a_bounds H
  have hr0 : 0 ≤ (m : ℝ) - movA d s := mnb_sub_a_nonneg H hm
  have hr2 : 0 ≤ (m : ℝ) - movA d s - movA d s := mne_lvl2 H hm
  have hmle : (m : ℝ) - movA d s ≤ (m : ℝ) := sub_le_self _ (by linarith [ha.1])
  have hvc := hmild.cont
  have hvT : ContinuousOn v (Icc 0 t) := hvc.mono Icc_subset_Ici_self
  have hfcont : ContinuousOn (fun u => mov_B_ext H hm (v u) (v u)) (Icc 0 t) :=
    (((mov_B_ext H hm).continuous.comp_continuousOn hvT).clm_apply hvT)
  have hj1c : ContinuousOn (fun τ => movJa H (m : ℝ) (v τ)) (Icc 0 t) :=
    (movJa H (m : ℝ)).continuous.comp_continuousOn hvT
  have key := mne_voc_abstract (fun τ => Real.exp (-(τ * q * (α.degree : ℝ))))
    (by fun_prop) (mnc_ipL (mnc_hα d β q α) hr0) (mnc_ipL (mnc_hα d β q α) hr2)
    (mov2d_R d s β q ρ ((m : ℝ) - movA d s)) (mov2d_G H ((m : ℝ) - movA d s))
    (fun u => mov_B_ext H hm (v u) (v u)) (fun τ => movJa H (m : ℝ) (v τ)) ht
    (fun y σ hσ => mne_G_pair H _ hr0 hr2 α hσ.1 y)
    ((mnc_ipL (mnc_hα d β q α) hr2).continuous.comp_continuousOn
      ((mov2d_R d s β q ρ ((m : ℝ) - movA d s)).continuous.comp_continuousOn
        (mne_G_joint H ((m : ℝ) - movA d s) t hfcont)))
    ((mnc_ipL (mnc_hα d β q α) hr0).continuous.comp_continuousOn hfcont)
    ((mnc_ipL (mnc_hα d β q α) hr2).continuous.comp_continuousOn
      ((mov2d_R d s β q ρ ((m : ℝ) - movA d s)).continuous.comp_continuousOn
        ((mov2d_G_cont H ((m : ℝ) - movA d s) (movJa H (m : ℝ) (v 0))).mono Icc_subset_Ici_self)))
    ((mnc_ipL (mnc_hα d β q α) hr2).continuous.comp_continuousOn
      ((mov2d_R d s β q ρ ((m : ℝ) - movA d s)).continuous.comp_continuousOn hj1c))
    (fun τ hτ => hmild.mild τ hτ.1)
  -- translate the three pairings
  have e0 : ∀ τ, mnc_ipL (mnc_hα d β q α) hr0 (movJa H (m : ℝ) (v τ)) =
      mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (v τ) := fun τ =>
    mne_ipL_j (f := mnc_hα d β q α) hmle hr0 (v τ)
  have e1 : ∀ τ, mnc_ipL (mnc_hα d β q α) hr2 (mov2d_R d s β q ρ ((m : ℝ) - movA d s) (movJa H (m : ℝ) (v τ))) =
      mnc_ipL (mnc_hα d β q α) hr0 (mov2d_R d s β q ρ (m : ℝ) (v τ)) := by
    intro τ
    have hc := mov2d_R_compat H hmle (v τ)
    rw [← mne_ipL_j (f := mnc_hα d β q α) (sub_le_self ((m : ℝ) - movA d s) (by linarith [ha.1])) hr2
      (mov2d_R d s β q ρ (m : ℝ) (v τ))]
    have : mov2d_j (sub_le_sub_right hmle (movA d s)) (mov2d_R d s β q ρ (m : ℝ) (v τ)) =
        mov2d_R d s β q ρ ((m : ℝ) - movA d s) (movJa H (m : ℝ) (v τ)) := hc
    rw [this]
  simp only [e0, e1] at key
  rw [key]
  congr 1
  refine intervalIntegral.integral_congr (fun τ _ => ?_)
  simp only [mneF, map_add, map_neg]
  ring


/-- **Mild ⇒ coefficient ODE (integral form)**: `⟨h̃_α, v_t⟩ - ⟨h̃_α, v_0⟩ = ∫_0^t (-q|α| ⟨h̃_α, v_x⟩ + ⟨h̃_α, F(v_x)⟩) dx`. -/
theorem mne_coeff_int {v : ℝ → OscSpace d (m : ℝ)} (hmild : MneMild H hm v) (α : MultiIndex d) {t : ℝ}
    (ht : 0 ≤ t) :
    mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (v t) - mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (v 0) =
      ∫ x in Icc (0 : ℝ) t, (-(q * (α.degree : ℝ)) * mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (v x) +
        mnc_ipL (mnc_hα d β q α) (mnb_sub_a_nonneg H hm) (mneF H hm v x)) := by
  have hvT : ContinuousOn v (Icc 0 t) := hmild.cont.mono Icc_subset_Ici_self
  have hF : ContinuousOn (mneF H hm v) (Icc 0 t) := (mneF_cont hmild.cont).mono Icc_subset_Ici_self
  refine mne_voc_integral (lam := q * (α.degree : ℝ)) ht (c := fun τ => mnc_ipL (mnc_hα d β q α) (Nat.cast_nonneg m) (v τ))
    (g := fun τ => mnc_ipL (mnc_hα d β q α) (mnb_sub_a_nonneg H hm) (mneF H hm v τ))
    ((mnc_ipL _ _).continuous.comp_continuousOn hvT) ((mnc_ipL _ _).continuous.comp_continuousOn hF) ?_ t ⟨ht, le_rfl⟩
  intro t' ht'
  have := mne_coeff_voc hmild α ht'.1
  rw [this]
  have e1 : Real.exp (-(t' * q * (α.degree : ℝ))) = Real.exp (-(q * (α.degree : ℝ)) * t') := by
    congr 1; ring
  rw [e1]
  congr 1
  rw [intervalIntegral.integral_of_le ht'.1, integral_Icc_eq_integral_Ioc]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  congr 2; ring

end StepA

end HRS.MS.Mov63

end
