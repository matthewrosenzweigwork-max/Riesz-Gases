import HRS.MS.AdjVerifAux1

/-!
# AD-2, part 2: the Ito verification theorem `ad_verification` for classical adjoint solutions (S4.12)

Infrastructure for `adjoint_decay` (S4.12), consumed by AD-3 (`adjoint_decay_proof`); not a manuscript row.
Route (S4_PLAN section 2.2, step 5): VERIFY, do not construct.  Let `f` be ANY classical adjoint solution
(`IsClassicalAdjointW C t φ f`, in particular `f_u = propagatorW C u t φ` whenever one exists).  The adjoint
equation `-∂_u f = generatorW C u f_u` reads `∂_u f + νΔf + b_u·∇f = S_u`, where `b_u = C.drift u` and `S_u`
is the nonlocal term (`S_u = Div g*(ρ_u Mᵀ ∇f_u)`).  Ito's formula for `f(v, X_v)` along the pathwise flow of
the LC engine gives the representation formula
`f(r,x) = E φ(X_t^{r,x}) - E ∫_r^t S_u(X_u^{r,x}) du`.

**Statement** (`ad_verification`).  `(P, ℱ, W)` Brownian filtration, `Q, c, B` the data of the engine with
`LcHyp Q k Λc ΛB c B`, `X^{r,x}_u = lcFlow Q c B G r u x` with `G = lcNoiseE W (fun _ => ν)` (the SAME noise as
`lcSg P W (fun _ => ν) Q c B`).  Hypotheses: `0 < C.ν` (`ν = C.ν`), `C.drift u y = B u y - lcQ Q y - c u` for
`u ∈ [0,t]` (AD-3: `B_u = matVec M (convGradConvW ..)`, `gradient (quadV Q c) y = matVec Q y + c` by
`ad_gradient_quadV`, `lcQ_apply`), `hf : IsClassicalAdjointW C t φ f`, and a source `S` with
`generatorW C u (f u) y = ν Δ(f u)(y) + ⟨C.drift u y, ∇(f u)(y)⟩ - S u y` for `u ∈ [0,t]` (AD-3 supplies `S`
from `ad_generator_split`/`ad_source_bound`).  Conclusions, for `0 ≤ r ≤ t`: (1) a.s. the path `u ↦ S u (X_u)` is
interval integrable on `[r,t]` (so the Bochner integral below is genuine); (2) `φ(X_t)` and
`ω ↦ ∫_r^t S_u(X_u) du` are integrable; (3)
`f r x = lcSg P W (fun _ => ν) Q c B r t φ x - E ∫_r^t S_u(X_u^{r,x}) du`.

Normalisation of the noise.  For the constant viscosity `ν`, `G_v - G_u` (`G = lcNoiseE W (fun _ => ν)`) is centred
Gaussian with variance `2ν (v - u)` per coordinate, i.e. diffusion coefficient `σ = √(2ν)`, which is the
viscosity `ν` of `generatorW` (`νΔ = ½ σ² Δ`).  In the proof the equation is run in the time scale
`s = 2ν (v - r)` of the unit Brownian motion `W_{2νr+·} - W_{2νr}` (`ad2_sdrift`, `ad2_isC12On_reparam`).

Proof.  Strong solution `Y` of the scaled equation (`exists_sde_solution_global_exists`), the Dynkin form
`ad2_dynkin` for `f̃(s,y) = f(r + s/(2ν), y)` (`C^{1,2}` by `ad2_isC12On`, bounded gradient): the Ito
remainder `M` is integrable with mean zero.  The drift of Ito's formula equals `(2ν)⁻¹ S_{r+s/2ν}(Y_s)`
(`ad2_drift_identity`), `Y_{2ντ} = X_{r+τ}` a.s. (`ad2_strong_eq_flow`), and the change of variables
`ad2_cv` gives the representation.  Integrability of `∫ S(X)` follows from the identity itself (no moment
estimate on `X` is needed here).

**Semigroup form** (`ad_verification_sg`).  Fubini (joint integrability from the linear growth of `S`, `ad2_S_bound`,
the pathwise comparability `lc2_flow_comp` and `lc_sup_moment`) gives, for `0 ≤ r ≤ t`, that
`u ↦ lcSg P W (fun _ => ν) Q c B r u (S u) x` is interval integrable on `[r,t]` and
`f r x = lcSg P W (fun _ => ν) Q c B r t φ x - ∫_r^t lcSg P W (fun _ => ν) Q c B r u (S u) x du`,
which is the form to which `lc_engine` applies termwise (for `φ` and for every `S u`).  `ad2_S_cont`,
`ad2_S_bound`: `S` is jointly continuous on `[0,t] × ℝ^d` and of linear growth (from `hS`, `IsClassicalAdjointW`).

Statement adjustments relative to the plan sketch: `ν > 0` is assumed (the manuscript's `ν = 1/β > 0`);
the source `S` is an arbitrary function related to `generatorW` by `hS` (so that no convention lemma enters
here); the representation is for the LC-engine flow rather than for an abstract strong solution.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.MS.Lc HRS.MS.PoisKolm HRS.MD.EQLawPath

noncomputable section
namespace HRS.MS.AdjVerif

variable {d : ℕ}

/-- The Ito drift of the time-scaled function along the scaled drift is `a⁻¹ S`. -/
theorem ad2_drift_identity {Q : Matrix (Fin d) (Fin d) ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d}
    (C : WholeCoeff d) (hν : 0 < C.ν) {t r : ℝ} (hr : 0 ≤ r) (hrt : r < t) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    (hdrift : ∀ u ∈ Icc 0 t, ∀ y, C.drift u y = B u y - lcQ Q y - c u)
    (S : ℝ → Euc d → ℝ)
    (hS : ∀ u ∈ Icc 0 t, ∀ y, generatorW C u (f u) y = C.ν * Laplacian.laplacian (f u) y +
      inner ℝ (C.drift u y) (gradient (f u) y) - S u y)
    {s : ℝ} (hs : s ∈ Icc 0 (2 * C.ν * (t - r))) (y : Euc d) :
    derivWithin (fun r' => f (r + r' / (2 * C.ν)) y) (Icc 0 (2 * C.ν * (t - r))) s +
      fderiv ℝ (f (r + s / (2 * C.ν))) y (ad2_sdrift Q c B r (2 * C.ν) s y) +
      (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (f (r + s / (2 * C.ν)))) y (lcSigma d k) (lcSigma d k) =
    (2 * C.ν)⁻¹ * S (r + s / (2 * C.ν)) y := by
  have ha : 0 < 2 * C.ν := by positivity
  have hv : r + s / (2 * C.ν) ∈ Icc 0 t := ad2_theta_maps hr ha hs
  have ht : 0 < t := by linarith
  rw [(ad2_isC12On_reparam (ad2_isC12On ht hf) hr ha hrt).2 y s hs,
    ad2_derivWithin_eq ht hf y hv]
  have hdr : ad2_sdrift Q c B r (2 * C.ν) s y = (2 * C.ν)⁻¹ • C.drift (r + s / (2 * C.ν)) y := by
    simp only [ad2_sdrift, lcB, hdrift _ hv y]
    congr 1
    abel
  have hlap : ∑ k, fderiv ℝ (fderiv ℝ (f (r + s / (2 * C.ν)))) y (lcSigma d k) (lcSigma d k) =
      Laplacian.laplacian (f (r + s / (2 * C.ν))) y := (kl_laplacian_eq _ y).symm
  rw [hdr, hlap, map_smul, smul_eq_mul, ← kl_inner_gradient]
  have hG := hS _ hv y
  rw [hG]
  field_simp
  ring


/-! ### Change of variables `s = a (u - r)` -/

theorem ad2_cv {a r t : ℝ} (ha : 0 < a) (hrt : r ≤ t) (h : ℝ → ℝ) :
    ∫ s in Icc (0 : ℝ) (a * (t - r)), a⁻¹ * h (r + s / a) = ∫ u in r..t, h u := by
  have hT : 0 ≤ a * (t - r) := mul_nonneg ha.le (sub_nonneg.2 hrt)
  rw [setIntegral_Icc_eq_interval hT]
  have h1 := intervalIntegral.integral_comp_div (a := 0) (b := a * (t - r))
    (fun s : ℝ => h (r + s)) ha.ne'
  have e : a * (t - r) / a = t - r := by field_simp
  rw [e, zero_div] at h1
  have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := t - r) h r
  rw [add_zero, add_sub_cancel] at h2
  rw [intervalIntegral.integral_const_mul]
  simp only [smul_eq_mul] at h1
  rw [h1, h2]
  field_simp

theorem ad2_cv_int {a r t : ℝ} (ha : 0 < a) (hrt : r ≤ t) (h : ℝ → ℝ)
    (hint : IntegrableOn (fun s => a⁻¹ * h (r + s / a)) (Icc 0 (a * (t - r)))) :
    IntervalIntegrable h volume r t := by
  have hT : 0 ≤ a * (t - r) := mul_nonneg ha.le (sub_nonneg.2 hrt)
  have h0 : IntervalIntegrable (fun s => a⁻¹ * h (r + s / a)) volume 0 (a * (t - r)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]; exact hint
  have h1 := (h0.const_mul a).comp_mul_left (c := a) enorm_ne_top enorm_ne_top
  have e : a * (t - r) / a = t - r := by field_simp
  rw [e, zero_div] at h1
  have h2 : IntervalIntegrable (fun τ => h (r + τ)) volume 0 (t - r) := by
    refine h1.congr (fun τ _ => ?_)
    show a * (a⁻¹ * h (r + a * τ / a)) = h (r + τ)
    rw [mul_div_cancel_left₀ _ ha.ne', ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  have h3 := h2.comp_add_left (-r) enorm_ne_top
  simpa using h3


/-! ### The verification theorem -/

/-- **AD-2 (Ito verification for classical adjoint solutions).**  See the file docstring. -/
theorem ad_verification {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ)
    (hW : IsBrownianFiltration P ℱ W) (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (Λc ΛB : ℝ)
    (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d) (H : LcHyp Q k Λc ΛB c B)
    (C : WholeCoeff d) (hν : 0 < C.ν) {t : ℝ}
    (hdrift : ∀ u ∈ Icc 0 t, ∀ y, C.drift u y = B u y - lcQ Q y - c u)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    (S : ℝ → Euc d → ℝ)
    (hS : ∀ u ∈ Icc 0 t, ∀ y, generatorW C u (f u) y = C.ν * Laplacian.laplacian (f u) y +
      inner ℝ (C.drift u y) (gradient (f u) y) - S u y)
    {r : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (x : Euc d) :
    (∀ᵐ ω ∂P, IntervalIntegrable (fun u => S u
        (lcFlow Q c B (fun v => lcNoiseE W (fun _ => C.ν) v ω) r u x)) volume r t) ∧
    Integrable (fun ω => φ (lcFlow Q c B (fun v => lcNoiseE W (fun _ => C.ν) v ω) r t x)) P ∧
    Integrable (fun ω => ∫ u in r..t, S u
        (lcFlow Q c B (fun v => lcNoiseE W (fun _ => C.ν) v ω) r u x)) P ∧
    f r x = lcSg P W (fun _ => C.ν) Q c B r t φ x -
      ∫ ω, (∫ u in r..t, S u
        (lcFlow Q c B (fun v => lcNoiseE W (fun _ => C.ν) v ω) r u x)) ∂P := by
  have hGc : ∀ ω, Continuous fun v => lcNoiseE W (fun _ => C.ν) v ω := fun ω =>
    lc_noiseE_cont hW continuous_const ω
  rcases hrt.eq_or_lt with h | hlt
  · subst h
    have hself : ∀ ω, lcFlow Q c B (fun v => lcNoiseE W (fun _ => C.ν) v ω) r r x = x :=
      fun ω => lcFlow_self H (hGc ω) hr x
    have hfx : f r x = φ x := by rw [hf.terminal]
    simp only [hself, intervalIntegral.integral_same, integral_zero, sub_zero, lcSg]
    refine ⟨ae_of_all _ fun ω => IntervalIntegrable.refl, integrable_const _, integrable_const _, ?_⟩
    simp [hfx]
  have ht' : 0 < t := lt_of_le_of_lt hr hlt
  set ν := C.ν with hνdef
  have ha : 0 < 2 * ν := by positivity
  set X : ℝ → Ω → Euc d := fun u ω =>
    lcFlow Q c B (fun v => lcNoiseE W (fun _ => ν) v ω) r u x with hXdef
  have hf12 := ad2_isC12On ht' hf
  obtain ⟨hft, -⟩ := ad2_isC12On_reparam hf12 hr ha hlt
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  have hC : ∀ s ∈ Icc 0 (2 * ν * (t - r)), ∀ y,
      ‖fderiv ℝ (f (r + s / (2 * ν))) y‖ ≤ B1 := by
    intro s hs y
    have := hB1 (r + s / (2 * ν)) (ad2_theta_maps hr ha hs) y
    rwa [norm_iteratedFDeriv_one] at this
  have hW' := isBrownianFiltration_shift hW (2 * ν * r).toNNReal
  have hb := ad2_sdrift_isLipschitz H hr ha
  obtain ⟨Y, hY⟩ := exists_sde_solution_global_exists hW' (ad2_sdrift Q c B r (2 * ν)) hb
    (lcSigma d) (Y₀ := fun _ => x) (fun _ => measurable_const)
  have hT' : 0 ≤ 2 * ν * (t - r) := mul_nonneg ha.le (by linarith)
  obtain ⟨M, hMint, hM0, hMae⟩ := ad2_dynkin hW' hb hY hT' hft hC
  have hid := ad2_strong_eq_flow hW H hν hr x hY
  set T' : ℝ := 2 * ν * (t - r) with hT'def
  have hrT : r + T' / (2 * ν) = t := by rw [hT'def]; field_simp; ring
  have hYX : ∀ ω, (∀ τ : ℝ, 0 ≤ τ → Y (2 * ν * τ) ω = X (r + τ) ω) →
      ∀ s ∈ Icc 0 T', Y s ω = X (r + s / (2 * ν)) ω := by
    intro ω h s hs
    have e : 2 * ν * (s / (2 * ν)) = s := by field_simp
    have := h (s / (2 * ν)) (div_nonneg hs.1 ha.le)
    rwa [e] at this
  have hXY : ∀ ω, (∀ τ : ℝ, 0 ≤ τ → Y (2 * ν * τ) ω = X (r + τ) ω) → Y T' ω = X t ω := by
    intro ω h
    have := h (t - r) (sub_nonneg.2 hrt)
    rwa [add_sub_cancel] at this
  have hmain : ∀ᵐ ω ∂P, IntervalIntegrable (fun u => S u (X u ω)) volume r t ∧
      φ (X t ω) = f r x + (∫ u in r..t, S u (X u ω)) + M ω := by
    filter_upwards [hid, hMae] with ω h1 h2
    obtain ⟨hI, hEq⟩ := h2
    have hdr : ∀ s ∈ Icc 0 T', (derivWithin (fun r' => f (r + r' / (2 * ν)) (Y s ω))
        (Icc 0 T') s + fderiv ℝ (f (r + s / (2 * ν))) (Y s ω)
          (ad2_sdrift Q c B r (2 * ν) s (Y s ω)) +
        (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (f (r + s / (2 * ν)))) (Y s ω) (lcSigma d k)
          (lcSigma d k)) = (2 * ν)⁻¹ * S (r + s / (2 * ν)) (X (r + s / (2 * ν)) ω) := by
      intro s hs
      exact (ad2_drift_identity (Q := Q) (c := c) (B := B) C hν hr hlt hf hdrift S hS hs
        (Y s ω)).trans (by rw [hYX ω h1 s hs])
    have hI' : IntegrableOn (fun s => (2 * ν)⁻¹ * S (r + s / (2 * ν)) (X (r + s / (2 * ν)) ω))
        (Icc 0 T') := hI.congr_fun hdr measurableSet_Icc
    refine ⟨ad2_cv_int ha hlt.le (fun u => S u (X u ω)) hI', ?_⟩
    have hEq' := hEq
    simp only [hrT, hXY ω h1, zero_div, add_zero] at hEq'
    rw [setIntegral_congr_fun measurableSet_Icc hdr,
      ad2_cv ha hlt.le (fun u => S u (X u ω)), hf.terminal] at hEq'
    exact hEq'
  have hYT : Measurable (Y T') := (hY.adapted T').mono ((shiftFil ℱ _).le _) le_rfl
  have hφc : Continuous φ := by
    rw [← hf.terminal]; exact (hf.c2 t ⟨ht'.le, le_rfl⟩).continuous
  obtain ⟨B0, hB0⟩ := hf.bdd 0 (by norm_num)
  have hφb : ∀ y, ‖φ y‖ ≤ B0 := fun y => by
    have := hB0 t ⟨ht'.le, le_rfl⟩ y
    rwa [norm_iteratedFDeriv_zero, hf.terminal] at this
  have hφint : Integrable (fun ω => φ (Y T' ω)) P :=
    Integrable.of_bound (hφc.measurable.comp hYT).aestronglyMeasurable B0
      (ae_of_all _ fun ω => hφb _)
  have hφX : Integrable (fun ω => φ (X t ω)) P := by
    refine hφint.congr ?_
    filter_upwards [hid] with ω h1
    simp only [hXY ω h1]
  have hIint : Integrable (fun ω => ∫ u in r..t, S u (X u ω)) P := by
    have := (hφX.sub (integrable_const (f r x))).sub hMint
    refine this.congr ?_
    filter_upwards [hmain] with ω h
    simp only [Pi.sub_apply]
    rw [h.2]; ring
  refine ⟨hmain.mono fun ω h => h.1, hφX, hIint, ?_⟩
  have h1 : ∫ ω, φ (X t ω) ∂P = ∫ ω, (f r x + (∫ u in r..t, S u (X u ω)) + M ω) ∂P :=
    integral_congr_ae (by filter_upwards [hmain] with ω h using h.2)
  have hE : ∫ ω, φ (X t ω) ∂P = f r x + ∫ ω, (∫ u in r..t, S u (X u ω)) ∂P := by
    have hA : Integrable (fun ω => f r x + ∫ u in r..t, S u (X u ω)) P :=
      (integrable_const _).add hIint
    rw [h1, integral_add hA hMint, integral_add (integrable_const _) hIint, hM0]
    simp
  show f r x = ∫ ω, φ (X t ω) ∂P - ∫ ω, (∫ u in r..t, S u (X u ω)) ∂P
  rw [hE]; ring

/-! ### Regularity and growth of the source `S` -/

theorem ad2_S_cont {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
    {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B) (C : WholeCoeff d) {t : ℝ} (ht : 0 < t)
    (hdrift : ∀ u ∈ Icc 0 t, ∀ y, C.drift u y = B u y - lcQ Q y - c u)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) (S : ℝ → Euc d → ℝ)
    (hS : ∀ u ∈ Icc 0 t, ∀ y, generatorW C u (f u) y = C.ν * Laplacian.laplacian (f u) y +
      inner ℝ (C.drift u y) (gradient (f u) y) - S u y) :
    ContinuousOn (fun p : ℝ × Euc d => S p.1 p.2) (Icc 0 t ×ˢ univ) := by
  have hf12 := ad2_isC12On ht hf
  have hG := ad2_continuousOn_of_subtype (F := fun s y => generatorW C s (f s) y) hf.cont_time_deriv
  have hdr : ContinuousOn (fun p : ℝ × Euc d => C.drift p.1 p.2) (Icc 0 t ×ˢ univ) := by
    have h1 : ContinuousOn (fun p : ℝ × Euc d => B p.1 p.2 - lcQ Q p.2 - c p.1)
        (Icc 0 t ×ˢ univ) := by
      have hB : ContinuousOn (fun p : ℝ × Euc d => B p.1 p.2) (Icc 0 t ×ˢ univ) :=
        H.B_cont.mono (prod_mono (fun u hu => hu.1) subset_rfl)
      have hc : ContinuousOn (fun p : ℝ × Euc d => c p.1) (Icc 0 t ×ˢ univ) :=
        H.c_cont.comp continuousOn_fst (fun p hp => hp.1.1)
      exact (hB.sub ((lcQ Q).continuous.comp_continuousOn continuousOn_snd)).sub hc
    exact h1.congr fun p hp => hdrift p.1 hp.1 p.2
  have hlap : ContinuousOn (fun p : ℝ × Euc d => Laplacian.laplacian (f p.1) p.2)
      (Icc 0 t ×ˢ univ) := by
    have : ContinuousOn (fun p : ℝ × Euc d => ∑ i : Fin d, fderiv ℝ (fderiv ℝ (f p.1)) p.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) (Icc 0 t ×ˢ univ) :=
      continuousOn_finsetSum _ fun i _ =>
        (hf12.cont_fderiv₂.clm_apply continuousOn_const).clm_apply continuousOn_const
    exact this.congr fun p _ => kl_laplacian_eq _ _
  have hin : ContinuousOn (fun p : ℝ × Euc d => inner ℝ (C.drift p.1 p.2) (gradient (f p.1) p.2))
      (Icc 0 t ×ˢ univ) := by
    have : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (f p.1) p.2 (C.drift p.1 p.2))
        (Icc 0 t ×ˢ univ) := hf12.cont_fderiv.clm_apply hdr
    exact this.congr fun p _ => kl_inner_gradient _ _ _
  have : ContinuousOn (fun p : ℝ × Euc d => C.ν * Laplacian.laplacian (f p.1) p.2 +
      inner ℝ (C.drift p.1 p.2) (gradient (f p.1) p.2) - generatorW C p.1 (f p.1) p.2)
      (Icc 0 t ×ˢ univ) := ((continuousOn_const.mul hlap).add hin).sub hG
  refine this.congr fun p hp => ?_
  have := hS p.1 hp.1 p.2
  linarith

theorem ad2_S_bound {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
    {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B) (C : WholeCoeff d) {t : ℝ}
    (hdrift : ∀ u ∈ Icc 0 t, ∀ y, C.drift u y = B u y - lcQ Q y - c u)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) (S : ℝ → Euc d → ℝ)
    (hS : ∀ u ∈ Icc 0 t, ∀ y, generatorW C u (f u) y = C.ν * Laplacian.laplacian (f u) y +
      inner ℝ (C.drift u y) (gradient (f u) y) - S u y) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ Icc 0 t, ∀ y, |S u y| ≤ K * (1 + ‖y‖) := by
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hf.bdd 2 le_rfl
  obtain ⟨Bg, hBg⟩ := hf.bdd_time_deriv
  have hΛB := H.ΛB_nonneg
  have hΛc := H.Λc_nonneg
  set K : ℝ := |C.ν| * (d * |B2|) + |B1| * (ΛB + Λc + ‖lcQ Q‖) + |Bg| with hK
  refine ⟨K, by positivity, fun u hu y => ?_⟩
  have hSu : S u y = C.ν * Laplacian.laplacian (f u) y +
      inner ℝ (C.drift u y) (gradient (f u) y) - generatorW C u (f u) y := by
    have := hS u hu y; linarith
  have hu' : u ∈ Icc 0 t := hu
  -- Laplacian bound
  have hlap : |Laplacian.laplacian (f u) y| ≤ d * |B2| := by
    rw [kl_laplacian_eq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hi : ∀ i : Fin d, |fderiv ℝ (fderiv ℝ (f u)) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)| ≤ |B2| := by
      intro i
      have e : fderiv ℝ (fderiv ℝ (f u)) y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
          iteratedFDeriv ℝ 2 (f u) y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i 1] := by
        rw [iteratedFDeriv_two_apply]; rfl
      rw [e, ← Real.norm_eq_abs]
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        EuclideanSpace.norm_single, norm_one, mul_one]
      exact (hB2 u hu' y).trans (le_abs_self _)
    calc ∑ i : Fin d, |fderiv ℝ (fderiv ℝ (f u)) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single i 1)| ≤ ∑ _i : Fin d, |B2| := Finset.sum_le_sum fun i _ => hi i
      _ = d * |B2| := by simp
  -- drift term
  have hdn : ‖C.drift u y‖ ≤ (ΛB + Λc + ‖lcQ Q‖) * (1 + ‖y‖) := by
    rw [hdrift u hu' y]
    have h1 : ‖B u y‖ ≤ ΛB := by
      have := H.B_bd u hu.1 0 (Nat.zero_le _) y
      rwa [norm_iteratedFDeriv_zero] at this
    have h2 : ‖lcQ Q y‖ ≤ ‖lcQ Q‖ * ‖y‖ := (lcQ Q).le_opNorm y
    have h3 := H.c_bd u hu.1
    have h4 := norm_sub_le (B u y - lcQ Q y) (c u)
    have h5 := norm_sub_le (B u y) (lcQ Q y)
    have hy := norm_nonneg y
    nlinarith [mul_nonneg (add_nonneg hΛB hΛc) hy, norm_nonneg (lcQ Q)]
  have hin : |inner ℝ (C.drift u y) (gradient (f u) y)| ≤ |B1| * ((ΛB + Λc + ‖lcQ Q‖) * (1 + ‖y‖)) := by
    rw [kl_inner_gradient, ← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have h1 : ‖fderiv ℝ (f u) y‖ ≤ |B1| := by
      have := hB1 u hu' y
      rw [norm_iteratedFDeriv_one] at this
      exact this.trans (le_abs_self _)
    exact mul_le_mul h1 hdn (norm_nonneg _) (abs_nonneg _)
  have hgen : |generatorW C u (f u) y| ≤ |Bg| * (1 + ‖y‖) :=
    (hBg u hu' y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  rw [hSu]
  have hy1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hlap' : |C.ν * Laplacian.laplacian (f u) y| ≤ |C.ν| * (d * |B2|) * (1 + ‖y‖) := by
    rw [abs_mul]
    calc |C.ν| * |Laplacian.laplacian (f u) y| ≤ |C.ν| * (d * |B2|) :=
          mul_le_mul_of_nonneg_left hlap (abs_nonneg _)
      _ ≤ |C.ν| * (d * |B2|) * (1 + ‖y‖) := le_mul_of_one_le_right (by positivity) hy1
  have := abs_sub (C.ν * Laplacian.laplacian (f u) y + inner ℝ (C.drift u y) (gradient (f u) y))
    (generatorW C u (f u) y)
  have h2 := abs_add_le (C.ν * Laplacian.laplacian (f u) y) (inner ℝ (C.drift u y) (gradient (f u) y))
  calc _ ≤ |C.ν * Laplacian.laplacian (f u) y + inner ℝ (C.drift u y) (gradient (f u) y)| +
        |generatorW C u (f u) y| := abs_sub _ _
    _ ≤ (|C.ν| * (d * |B2|) * (1 + ‖y‖)) + (|B1| * ((ΛB + Λc + ‖lcQ Q‖) * (1 + ‖y‖))) +
        |Bg| * (1 + ‖y‖) := by linarith
    _ = K * (1 + ‖y‖) := by rw [hK]; ring


/-! ### The representation through `lcSg` (Fubini) -/

universe u

theorem ad2_meas_flow_x {Ω : Type*} [MeasurableSpace Ω] {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ}
    {Λc ΛB : ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B)
    {G : Ω → ℝ → Euc d} (hGm : ∀ v, Measurable fun ω => G ω v) (hGc : ∀ ω, Continuous (G ω))
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (x : Euc d) :
    Measurable fun ω => lcFlow Q c B (G ω) r s x := by
  have h := lc4_meas_flow H hGm hGc hr hrs
  have h2 : Measurable fun ω : Ω => (ω, x) := measurable_id.prodMk measurable_const
  have h3 := h.comp h2
  exact h3


/-- **AD-2 (Ito verification, semigroup form).**  Same hypotheses as `ad_verification`; Fubini turns
`E ∫_r^t S_u(X_u^{r,x}) du` into `∫_r^t lcSg r u (S u) x du`, so that the engine `lc_engine` applies to each
`S u`.  The joint integrability comes from the linear growth of `S` (`ad2_S_bound`), the pathwise
comparability `lc2_flow_comp`, and `lc_sup_moment`. -/
theorem ad_verification_sg {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ)
    (hW : IsBrownianFiltration P ℱ W) (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (Λc ΛB : ℝ)
    (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d) (H : LcHyp Q k Λc ΛB c B)
    (C : WholeCoeff d) (hν : 0 < C.ν) {t : ℝ}
    (hdrift : ∀ u ∈ Icc 0 t, ∀ y, C.drift u y = B u y - lcQ Q y - c u)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    (S : ℝ → Euc d → ℝ)
    (hS : ∀ u ∈ Icc 0 t, ∀ y, generatorW C u (f u) y = C.ν * Laplacian.laplacian (f u) y +
      inner ℝ (C.drift u y) (gradient (f u) y) - S u y)
    {r : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (x : Euc d) :
    IntervalIntegrable (fun u => lcSg P W (fun _ => C.ν) Q c B r u (S u) x) volume r t ∧
    f r x = lcSg P W (fun _ => C.ν) Q c B r t φ x -
      ∫ u in r..t, lcSg P W (fun _ => C.ν) Q c B r u (S u) x := by
  obtain ⟨-, -, -, hrep⟩ := ad_verification P ℱ W hW Q k Λc ΛB c B H C hν hdrift hf S hS hr hrt x
  rcases hrt.eq_or_lt with h | hlt
  · subst h
    refine ⟨IntervalIntegrable.refl, ?_⟩
    rw [hrep]; simp
  have ht' : 0 < t := lt_of_le_of_lt hr hlt
  obtain ⟨K, hK0, hK⟩ := ad2_S_bound H C hdrift hf S hS
  have hSc := ad2_S_cont H C ht' hdrift hf S hS
  set ν := C.ν with hνdef
  obtain ⟨G, hGdef⟩ : ∃ G : Ω → ℝ → Euc d, G = fun ω v => lcNoiseE W (fun _ => ν) v ω := ⟨_, rfl⟩
  have hGc : ∀ ω, Continuous (G ω) := fun ω => by
    subst hGdef; exact lc_noiseE_cont hW continuous_const ω
  have hGm : ∀ v, Measurable fun ω => G ω v := fun v => by
    subst hGdef; exact lc_noiseE_measurable hW v
  set X : ℝ → Ω → Euc d := fun u ω => lcFlow Q c B (G ω) r u x with hXdef
  -- the moment bound
  obtain ⟨Cm, hCm⟩ := lc_sup_moment.{u} d 1 t ν
  obtain ⟨hSint, -⟩ := hCm P ℱ W (fun _ => ν) hW continuous_const (fun _ => ⟨hν.le, le_rfl⟩)
  obtain ⟨Cu, hCu0, hCu⟩ := lc_U_bound Q t
  set Sup : Ω → ℝ := fun ω => ⨆ v ∈ Icc (0 : ℝ) t, ‖lcNoiseE W (fun _ => ν) v ω‖ with hSup
  have hSup0 : ∀ ω, 0 ≤ Sup ω := fun ω => lc3_sup_nonneg (g := fun v => lcNoiseE W (fun _ => ν) v ω) t
  have hSupG : ∀ ω, Sup ω = ⨆ w ∈ Icc (0 : ℝ) t, ‖G ω w‖ := fun ω => by
    subst hGdef; rfl
  set E : ℝ := Real.exp (lcLam Q Λc ΛB * t) with hE
  have hpt : ∀ ω, ∀ u ∈ Icc r t, 1 + ‖X u ω‖ ≤ (1 + Cu) * E * (1 + ‖x‖) * (1 + Sup ω) := by
    intro ω u hu
    have hκ : ∀ u' ∈ Icc r u, ‖lcU Q (G ω) r u'‖ ≤ Cu * Sup ω := fun u' hu' => by
      rw [hSupG ω]; exact hCu (hGc ω) r u' hr hu'.1 (hu'.2.trans hu.2)
    have h1 := (lc2_flow_comp H (hGc ω) hr hu.1 hκ x).1
    have hexp : Real.exp (lcLam Q Λc ΛB * (u - r)) ≤ E :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hu.2]) H.lam_nonneg)
    have hs := hSup0 ω
    have hx := norm_nonneg x
    have hE0 := Real.exp_pos (lcLam Q Λc ΛB * (u - r))
    calc 1 + ‖X u ω‖ ≤ (1 + Cu * Sup ω) * Real.exp (lcLam Q Λc ΛB * (u - r)) * (1 + ‖x‖) := h1
      _ ≤ ((1 + Cu) * (1 + Sup ω)) * E * (1 + ‖x‖) := by
          gcongr
          nlinarith [mul_nonneg hCu0 hs]
      _ = _ := by ring
  set g : Ω → ℝ := fun ω => K * ((1 + Cu) * E * (1 + ‖x‖)) * (1 + Sup ω) with hg
  have hgint : Integrable g P := by
    refine (hSint.const_mul (K * ((1 + Cu) * E * (1 + ‖x‖)))).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [pow_one]
    rfl
  -- the clamped integrand
  set cl : ℝ → ℝ := fun u => max r (min u t) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ u, cl u ∈ Icc r t := fun u =>
    ⟨le_max_left _ _, max_le hrt (min_le_right _ _)⟩
  have hclid : ∀ u ∈ Ioc r t, cl u = u := fun u hu => by
    simp only [hcl]; rw [min_eq_left hu.2, max_eq_right hu.1.le]
  set F' : ℝ × Ω → ℝ := fun p => S (cl p.1) (X (cl p.1) p.2) with hF'
  have hXm : Measurable (fun p : ℝ × Ω => X (cl p.1) p.2) := by
    have hcont : ∀ ω, Continuous fun u : ℝ => lcFlow Q c B (G ω) r (cl u) x := fun ω => by
      have := (lcFlowExt_continuous_v H (hGc ω) hr x).comp hclc
      refine this.congr (fun u => ?_)
      exact lcFlowExt_of_ge (hclm u).1 x
    have hmeas : ∀ u, Measurable fun ω => lcFlow Q c B (G ω) r (cl u) x := fun u =>
      ad2_meas_flow_x H hGm hGc hr (hclm u).1 x
    exact measurable_uncurry_of_continuous_of_measurable
      (u := fun (u : ℝ) (ω : Ω) => lcFlow Q c B (G ω) r (cl u) x) hcont hmeas
  have hSc' : Continuous fun q : ℝ × Euc d => S (cl q.1) q.2 := by
    have hq : Continuous fun q : ℝ × Euc d => (cl q.1, q.2) :=
      (hclc.comp continuous_fst).prodMk continuous_snd
    exact ContinuousOn.comp_continuous hSc hq
      (fun q => ⟨⟨hr.trans (hclm q.1).1, (hclm q.1).2⟩, mem_univ _⟩)
  have hF'm : Measurable F' := hSc'.measurable.comp (measurable_fst.prodMk hXm)
  have hF'b : ∀ p, ‖F' p‖ ≤ g p.2 := by
    intro p
    have hu := hclm p.1
    have h1 := hK (cl p.1) ⟨hr.trans hu.1, hu.2⟩ (X (cl p.1) p.2)
    have h2 := hpt p.2 (cl p.1) hu
    rw [Real.norm_eq_abs]
    refine h1.trans ?_
    calc K * (1 + ‖X (cl p.1) p.2‖) ≤ K * ((1 + Cu) * E * (1 + ‖x‖) * (1 + Sup p.2)) :=
          mul_le_mul_of_nonneg_left h2 hK0
      _ = g p.2 := by rw [hg]; ring
  set μ : Measure ℝ := volume.restrict (Ioc r t) with hμ
  have : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hFint : Integrable F' (μ.prod P) :=
    Integrable.mono' (hgint.comp_snd μ) hF'm.aestronglyMeasurable (ae_of_all _ hF'b)
  have hI1 : ∀ ω, (∫ u in r..t, S u (X u ω)) = ∫ u, F' (u, ω) ∂μ := by
    intro ω
    rw [intervalIntegral.integral_of_le hrt, hμ]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    simp only [hF', hclid u hu]
  have hI2 : ∀ u ∈ Ioc r t, ∫ ω, F' (u, ω) ∂P = lcSg P W (fun _ => ν) Q c B r u (S u) x := by
    intro u hu
    simp only [hF', hclid u hu, lcSg, hXdef, hGdef]
  have hsw := integral_integral_swap (μ := μ) (ν := P) (f := fun u ω => F' (u, ω)) hFint
  have hint1 : Integrable (fun u => ∫ ω, F' (u, ω) ∂P) μ := hFint.integral_prod_left
  have hint2 : IntegrableOn (fun u => lcSg P W (fun _ => ν) Q c B r u (S u) x) (Ioc r t) := by
    refine hint1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu using hI2 u hu
  have hEq : ∫ ω, (∫ u in r..t, S u (X u ω)) ∂P =
      ∫ u in r..t, lcSg P W (fun _ => ν) Q c B r u (S u) x := by
    calc ∫ ω, (∫ u in r..t, S u (X u ω)) ∂P = ∫ ω, ∫ u, F' (u, ω) ∂μ ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hI1)
      _ = ∫ u, ∫ ω, F' (u, ω) ∂P ∂μ := hsw.symm
      _ = ∫ u in Ioc r t, lcSg P W (fun _ => ν) Q c B r u (S u) x := by
          refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => hI2 u hu)
      _ = _ := (intervalIntegral.integral_of_le hrt).symm
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hrt).2 hint2, ?_⟩
  rw [← hEq]
  have hXeq : ∀ u ω, X u ω = lcFlow Q c B (fun v => lcNoiseE W (fun _ => ν) v ω) r u x := by
    intro u ω; simp only [hXdef, hGdef]
  simp only [hXeq]
  exact hrep

end HRS.MS.AdjVerif
