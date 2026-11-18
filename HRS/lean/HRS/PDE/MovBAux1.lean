import HRS.PDE.MovAFinal
import HRS.Energy.KIDAux2
import HRS.PDE.TorusFPExistAux15

/-!
# MOVB: chain plan for `movT_reg_ineq` (MovSpec1.lean:486), relocated proof `movT_reg_ineq_proof` in `MovBFinal.lean`

Route (fixed kernel level `M`, `V ∈ C²` mollified; `κ = D.invβ`, `β = κ⁻¹`, `n = N*d`, `e = d1_configEquiv d N`):

* The reference `Q^M_r = movT_Q (g_M) D N ρ r` does not depend on `V`.  For a smooth `V_k` put `D_k = b15e_withV D V_k`.
  The level-`k` tilt is `ψ^r = ∑_i movT_phi D_k M ρ r (x_i)` (`= mova_bigPsi` on `𝕋^n`), for which
  `d1_gibbsMeasure κ (d3_tiltPot κ (b15d_U D_k M) ψ^r) = Q^M_r.map e` (`mova_weight_eq` + normalisation) and
  `d3_source + E_q ψt = movT_srcReg D_k N M ρ ρt r` (`mova_gen_sum`, `d1_gen_config`).  No mean-field equation for `D_k`
  is needed: D3 holds for every `C^{1,2}` tilt.
* Level `k`: D2 (`b15e_law_eq_fp`, `d1_fp_exists_proof`) + `d3_entropy_moving_proof` (`0 < T`).
* `k → ∞`: `d1_exists_C2_approx` (value, gradient, Laplacian within `ε_k`), Gronwall `Y^k → Y`
  (`b15e_sde_stability`, `b15e_marginal_tendsto_unif`), lsc of `H(·|Q_t)` (`b15b_klDiv_liminf_le`, constant reference),
  `S_k → S` uniformly on `[0,T] × Config` (`movb_srcReg_withV_diff`), continuity in `r` of `∫ S dlaw_r`, dominated convergence.
* `T = 0`: `t = 0`, `Icc 0 0` null, conclusions from `hfin` and continuity of `srcReg` at `r = 0` (`ρt 0` continuous
  by `cont_time_deriv`), no D3 needed.  (No defect found in the statement for `T = 0`.)

## Sub-lemmas and sizes (prefix `movb_`)

* MovBAux1 (tilt regularity, big torus): `movb_isC12Test_add/smul/const`, `movb_isC12Test_convFun` (smooth even kernel,
  `convL/convD` of KIDAux2, clamped joint continuity, differentiation under `∫` in `r`) [L], `movb_isC12Test_log` (explicit
  `j = 0,1,2` Faa di Bruno) [L], `movb_phi_isC12Test` [S], `movb_bigPsi_isC12Test` (iteratedFDeriv of a one-body sum) [M-L].
* MovBAux2 (bridges): `movb_Q_eq_gibbs` (`Q^M_r.map e = d1_gibbsMeasure κ (tilt)`) [M], `movb_source_eq`
  (`d3_source` + `E_q ψt` = `movT_srcReg ∘ e⁻¹`) [M], relEntropy transfer [S].
* MovBAux3 (level `k`): `movb_reg_ineq_smooth` = D2 + D3 in `selectedLaw`/`movT_Q` language, with the integrability
  conclusions [L].
* MovBAux4 (analysis of `S`): joint continuity of `movT_srcReg` on `[0,T] × Config`, bound, continuity of
  `r ↦ ∫ S_r dlaw_r`, `movb_srcReg_withV_diff` (`|S_k - S| ≤ C ε_k`) [L].
* MovBAux5 (limit `k → ∞`): approximants, Gronwall, lsc, dominated convergence, `movb_reg_ineq_main` [L].
* MovBFinal: `movT_reg_ineq_proof` verbatim + `example := (@movT_reg_ineq_proof : type_of% @HRS.movT_reg_ineq)` [S].

STATUS: ALL DONE.  MovBAux1 (tilt regularity), MovBAux2 (bridges), MovBAux3 (level-k D2+D3), MovBAux4 (source analysis, `|S[V_k]-S[V]| <= C eps`),
MovBAux5 (limit k -> infinity), MovBFinal (`movT_reg_ineq_proof`, tied, standard axioms).
-/

noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS
variable {d : ℕ}

theorem movb_iter2_eq (G : Euc d → ℝ) (w : Euc d) :
    iteratedFDeriv ℝ 2 G w =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => Euc d) ℝ).symm
        ((((continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).symm :
            (Euc d →L[ℝ] ℝ) ≃ₗᵢ[ℝ] _).toContinuousLinearEquiv : _ ≃L[ℝ] _).toContinuousLinearMap.comp
          (fderiv ℝ (fderiv ℝ G) w)) := by
  rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
  have h : iteratedFDeriv ℝ 1 G =
      (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).symm ∘ fderiv ℝ G :=
    funext fun z => by simp [fderiv_eq_curry]
  rw [h, LinearIsometryEquiv.comp_fderiv]

theorem movb_iter_cont_of {ι : Type*} [TopologicalSpace ι] {F : ι → Euc d → ℝ}
    (h0 : Continuous fun p : ι × Euc d => F p.1 p.2)
    (h1 : Continuous fun p : ι × Euc d => fderiv ℝ (F p.1) p.2)
    (h2 : Continuous fun p : ι × Euc d => fderiv ℝ (fderiv ℝ (F p.1)) p.2) :
    ∀ j ≤ 2, Continuous fun p : ι × Euc d => iteratedFDeriv ℝ j (F p.1) p.2 := by
  intro j hj
  interval_cases j
  · have := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.continuous.comp h0
    refine this.congr fun p => ?_
    simp [iteratedFDeriv_zero_eq_comp]
  · have := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).symm.continuous.comp h1
    refine this.congr fun p => ?_
    simp [fderiv_eq_curry]
  · have := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => Euc d) ℝ).symm.continuous.comp
      (continuous_const.clm_comp h2 :
        Continuous fun p : ι × Euc d => (((continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).symm :
            (Euc d →L[ℝ] ℝ) ≃ₗᵢ[ℝ] _).toContinuousLinearEquiv : _ ≃L[ℝ] _).toContinuousLinearMap.comp
          (fderiv ℝ (fderiv ℝ (F p.1)) p.2))
    refine this.congr fun p => ?_
    simp only [Function.comp_apply]
    rw [movb_iter2_eq]

/-- `IsC12Test` in terms of the continuity of `F`, `DF`, `D²F` (`F = lift f`). -/
structure MovbC12 (T : ℝ) (f ft : ℝ → Torus d → ℝ) : Prop where
  c2 : ∀ r ∈ Set.Icc 0 T, Torus.IsCk 2 (f r)
  c0 : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => Torus.lift (f p.1) p.2
  c1 : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => fderiv ℝ (Torus.lift (f p.1)) p.2
  c2' : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => fderiv ℝ (fderiv ℝ (Torus.lift (f p.1))) p.2
  td : ∀ x, ∀ r ∈ Set.Ioo 0 T, HasDerivAt (fun r => f r x) (ft r x) r
  ctd : Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => ft p.1 p.2

theorem movb_c12_iff {T : ℝ} {f ft : ℝ → Torus d → ℝ} :
    IsC12Test T f ft ↔ MovbC12 T f ft := by
  constructor
  · intro hf
    refine ⟨hf.c2, hf.continuous_lift_f, ?_, ?_, hf.time_deriv, hf.cont_time_deriv⟩
    · have := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp (hf.cont_c2 1 (by norm_num))
      refine this.congr fun p => ?_
      simp [fderiv_eq_curry]
    · have := (continuous_curry2 d).comp (hf.cont_c2 2 le_rfl)
      refine this.congr fun p => ?_
      simp [fderiv_fderiv_eq_curry2]
  · intro h
    exact ⟨h.c2, movb_iter_cont_of (F := fun (r : Set.Icc (0:ℝ) T) => Torus.lift (f r)) h.c0 h.c1 h.c2', h.td, h.ctd⟩


theorem movb_cd_d1 {A : Euc d → ℝ} (hA : ContDiff ℝ 2 A) : Differentiable ℝ A :=
  hA.differentiable (by norm_num)

theorem movb_cd_d2 {A : Euc d → ℝ} (hA : ContDiff ℝ 2 A) : Differentiable ℝ (fderiv ℝ A) :=
  (hA.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero

theorem MovbC12.add {T : ℝ} {f ft g gt : ℝ → Torus d → ℝ} (hf : MovbC12 T f ft) (hg : MovbC12 T g gt) :
    MovbC12 T (fun r x => f r x + g r x) (fun r x => ft r x + gt r x) where
  c2 r hr := mova_isCk_add (hf.c2 r hr) (hg.c2 r hr)
  c0 := hf.c0.add hg.c0
  c1 := by
    refine (hf.c1.add hg.c1).congr fun p => ?_
    have h1 : ContDiff ℝ 2 (Torus.lift (f p.1)) := hf.c2 p.1 p.1.2
    have h2 : ContDiff ℝ 2 (Torus.lift (g p.1)) := hg.c2 p.1 p.1.2
    exact (fderiv_add (movb_cd_d1 h1 p.2) (movb_cd_d1 h2 p.2)).symm
  c2' := by
    refine (hf.c2'.add hg.c2').congr fun p => ?_
    have h1 : ContDiff ℝ 2 (Torus.lift (f p.1)) := hf.c2 p.1 p.1.2
    have h2 : ContDiff ℝ 2 (Torus.lift (g p.1)) := hg.c2 p.1 p.1.2
    have e : fderiv ℝ (fun w => Torus.lift (fun x => f p.1 x + g p.1 x) w) =
        fun w => fderiv ℝ (Torus.lift (f p.1)) w + fderiv ℝ (Torus.lift (g p.1)) w := by
      funext w
      exact fderiv_add (movb_cd_d1 h1 w) (movb_cd_d1 h2 w)
    show _ = fderiv ℝ (fderiv ℝ (fun w => Torus.lift (fun x => f p.1 x + g p.1 x) w)) p.2
    rw [e]
    exact (fderiv_add (movb_cd_d2 h1 p.2) (movb_cd_d2 h2 p.2)).symm
  td x r hr := (hf.td x r hr).add (hg.td x r hr)
  ctd := hf.ctd.add hg.ctd

theorem MovbC12.const_mul {T : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : MovbC12 T f ft) (c : ℝ) :
    MovbC12 T (fun r x => c * f r x) (fun r x => c * ft r x) where
  c2 r hr := mova_isCk_const_mul c (hf.c2 r hr)
  c0 := continuous_const.mul hf.c0
  c1 := by
    refine ((continuous_const (y := c)).smul hf.c1).congr fun p => ?_
    have h1 : ContDiff ℝ 2 (Torus.lift (f p.1)) := hf.c2 p.1 p.1.2
    exact (fderiv_const_mul (movb_cd_d1 h1 p.2) c).symm
  c2' := by
    refine ((continuous_const (y := c)).smul hf.c2').congr fun p => ?_
    have h1 : ContDiff ℝ 2 (Torus.lift (f p.1)) := hf.c2 p.1 p.1.2
    have e : fderiv ℝ (fun w => Torus.lift (fun x => c * f p.1 x) w) =
        fun w => c • fderiv ℝ (Torus.lift (f p.1)) w := by
      funext w
      exact fderiv_const_mul (movb_cd_d1 h1 w) c
    show _ = fderiv ℝ (fderiv ℝ (fun w => Torus.lift (fun x => c * f p.1 x) w)) p.2
    rw [e]
    exact (fderiv_const_smul (movb_cd_d2 h1 p.2) c).symm
  td x r hr := (hf.td x r hr).const_mul c
  ctd := continuous_const.mul hf.ctd

theorem MovbC12.of_const {T : ℝ} {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    MovbC12 T (fun _ => φ) (fun _ _ => 0) :=
  movb_c12_iff.1 (d1_isC12Test_const hφ)


open HRS.KID in
theorem movb_continuous_convD {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (k : ℕ) {g : P → Torus d → ℝ}
    {B : ℝ} (hgb : ∀ r z, |g r z| ≤ B) (hgm : ∀ r, Measurable (g r))
    (hgc : ∀ z, Continuous fun r => g r z) :
    Continuous fun p : P × Euc d => convD (Torus.lift h) (g p.1) k p.2 := by
  have hck : ∀ j : ℕ, Torus.IsCk (j : WithTop ℕ∞) h := fun j =>
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift h) from hsm)
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  have hbd : ∀ y, ‖iteratedFDeriv ℝ k (Torus.lift h) y‖ ≤ Torus.cbNorm k h := fun y =>
    HRS.KernelGrad.norm_iteratedFDeriv_le_cbNorm (hck k) le_rfl y
  have hcdi : Continuous (iteratedFDeriv ℝ k (Torus.lift h)) :=
    (show ContDiff ℝ k (Torus.lift h) from hck k).continuous_iteratedFDeriv (le_refl _)
  have hrep := measurable_torusRep d
  unfold convD
  refine continuous_of_dominated (bound := fun _ => B * Torus.cbNorm k h) ?_ ?_ (integrable_const _) ?_
  · intro p
    exact ((hgm p.1).aestronglyMeasurable).smul
      (hcdi.comp_aestronglyMeasurable (measurable_const.sub hrep).aestronglyMeasurable)
  · intro p
    refine Eventually.of_forall fun z => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hgb _ _) (hbd _) (norm_nonneg _) ((abs_nonneg _).trans (hgb (p.1) z))
  · refine Eventually.of_forall fun z => ?_
    exact ((hgc z).comp continuous_fst).smul (hcdi.comp (continuous_snd.sub continuous_const))

theorem movb_lift_convFun (g f : Torus d → ℝ) (w : Euc d) :
    Torus.lift (convFun g f) w = HRS.KID.convL (Torus.lift g) f w := by
  simp only [Torus.lift, Function.comp, convFun, HRS.KID.convL]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [mul_comm, HRS.KernelGrad.mk_sub, Torus.mk_rep]


theorem movb_slice_cont {T : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test T f ft) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) : Continuous (f r) :=
  hf.continuous_f.comp (continuous_const.prodMk continuous_id : Continuous fun y : Torus d =>
    ((⟨r, hr⟩ : Set.Icc (0 : ℝ) T), y))

theorem movb_slice_cont_t {T : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test T f ft) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) : Continuous (ft r) :=
  hf.cont_time_deriv.comp (continuous_const.prodMk continuous_id : Continuous fun y : Torus d =>
    ((⟨r, hr⟩ : Set.Icc (0 : ℝ) T), y))

theorem movb_hasDerivAt_convFun {T : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test T f ft)
    {g : Torus d → ℝ} (hg : Continuous g) (x : Torus d) {r : ℝ} (hr : r ∈ Set.Ioo 0 T) :
    HasDerivAt (fun r => convFun g (f r) x) (convFun g (ft r) x) r := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T × Torus d)).exists_bound_of_continuousOn
    hf.cont_time_deriv.continuousOn
  obtain ⟨Cg, hCg⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hg.continuousOn
  have hsub : ∀ s ∈ Metric.ball r (min r (T - r)), s ∈ Set.Ioo 0 T := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have h1 : -(min r (T - r)) < s - r := hs.1
    have h2 : s - r < min r (T - r) := hs.2
    have := min_le_left r (T - r)
    have := min_le_right r (T - r)
    constructor <;> linarith [hr.1, hr.2]
  have hε : 0 < min r (T - r) := lt_min hr.1 (by linarith [hr.2])
  have hIcc : ∀ s ∈ Set.Ioo (0 : ℝ) T, s ∈ Set.Icc 0 T := fun s hs => ⟨hs.1.le, hs.2.le⟩
  have hmeasF : ∀ s ∈ Set.Icc (0 : ℝ) T, AEStronglyMeasurable
      (fun y : Torus d => g (x - y) * f s y) volume := fun s hs =>
    ((hg.comp (continuous_const.sub continuous_id)).mul (movb_slice_cont hf hs)).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Torus d)))
    (F := fun s y => g (x - y) * f s y) (F' := fun s y => g (x - y) * ft s y)
    (x₀ := r) (bound := fun _ => max Cg 0 * max C 0) (Metric.ball_mem_nhds r hε)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds r hε) fun s hs => hmeasF s (hIcc s (hsub s hs)))
    (by
      have : Continuous fun y : Torus d => g (x - y) * f r y :=
        (hg.comp (continuous_const.sub continuous_id)).mul (movb_slice_cont hf (hIcc r hr))
      exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (((hg.comp (continuous_const.sub continuous_id)).mul
      (movb_slice_cont_t hf (hIcc r hr))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y s hs => by
      have hs' := hIcc s (hsub s hs)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |g (x - y)| ≤ max Cg 0 := by
        have := hCg (x - y) (Set.mem_univ _); rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)
      have h2 : |ft s y| ≤ max C 0 := by
        have := hC (⟨s, hs'⟩, y) (Set.mem_univ _); rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)
      exact mul_le_mul h1 h2 (abs_nonneg _) (le_max_right _ _))
    (integrable_const _)
    (Filter.Eventually.of_forall fun y s hs => (hf.time_deriv y s (hsub s hs)).const_mul _)
  simpa [convFun] using key.2

theorem movb_isC12Test_convFun {T : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test T f ft)
    {g : Torus d → ℝ} (hg : Torus.IsSmooth g) :
    IsC12Test T (fun r => convFun g (f r)) (fun r => convFun g (ft r)) := by
  have hint : ∀ r ∈ Set.Icc (0 : ℝ) T, Integrable (f r) := fun r hr =>
    (movb_slice_cont hf hr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgc : Continuous g := mova_continuous_of_isCk hg
  have hlift : ∀ r, Torus.lift (convFun g (f r)) = HRS.KID.convL (Torus.lift g) (f r) :=
    fun r => funext (movb_lift_convFun g (f r))
  refine ⟨fun r hr => ?_, fun j hj => ?_, fun x r hr => movb_hasDerivAt_convFun hf hgc x hr, ?_⟩
  · show ContDiff ℝ 2 _
    rw [hlift]
    exact (HRS.KID.contDiff_convL hg (hint r hr)).of_le HRS.KID.two_le_top
  · obtain ⟨B, hB⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T × Torus d)).exists_bound_of_continuousOn
      hf.continuous_f.continuousOn
    have hcd := movb_continuous_convD (P := Set.Icc (0 : ℝ) T) hg j (g := fun q => f q)
      (B := max B 0) (fun q z => by
        have := hB (q, z) (Set.mem_univ _); rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _))
      (fun q => (movb_slice_cont hf q.2).measurable)
      (fun z => hf.continuous_f.comp (continuous_id.prodMk continuous_const))
    refine hcd.congr fun p => ?_
    show _ = iteratedFDeriv ℝ j (Torus.lift (convFun g (f p.1))) p.2
    rw [hlift, HRS.KID.iteratedFDeriv_convL hg (hint p.1 p.1.2)]
  · exact mova_continuous_convFun_param (P := Set.Icc (0 : ℝ) T) (f := fun q => ft q)
      (mova_integrable_of_continuous hgc) hf.cont_time_deriv


theorem movb_fderiv_log {A : Euc d → ℝ} (hA : ContDiff ℝ 2 A) (hpos : ∀ w, 0 < A w) (w : Euc d) :
    fderiv ℝ (fun y => Real.log (A y)) w = (A w)⁻¹ • fderiv ℝ A w := by
  exact ((movb_cd_d1 hA w).hasFDerivAt.log (hpos w).ne').fderiv

theorem movb_fderiv2_log {A : Euc d → ℝ} (hA : ContDiff ℝ 2 A) (hpos : ∀ w, 0 < A w) (w : Euc d) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (A y))) w =
      (A w)⁻¹ • fderiv ℝ (fderiv ℝ A) w +
        ((-((A w) ^ 2)⁻¹) • fderiv ℝ A w).smulRight (fderiv ℝ A w) := by
  have h1 : fderiv ℝ (fun y => Real.log (A y)) = fun y => (A y)⁻¹ • fderiv ℝ A y :=
    funext fun y => movb_fderiv_log hA hpos y
  rw [h1]
  have hc : HasFDerivAt (fun y => (A y)⁻¹) ((-((A w) ^ 2)⁻¹) • fderiv ℝ A w) w :=
    (hasDerivAt_inv (hpos w).ne').comp_hasFDerivAt w (movb_cd_d1 hA w).hasFDerivAt
  have hf : HasFDerivAt (fderiv ℝ A) (fderiv ℝ (fderiv ℝ A) w) w := (movb_cd_d2 hA w).hasFDerivAt
  exact (hc.smul hf).fderiv

theorem movb_isC12Test_log {T : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test T f ft)
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < f r x) :
    IsC12Test T (fun r x => Real.log (f r x)) (fun r x => ft r x / f r x) := by
  have hm := movb_c12_iff.1 hf
  have hposl : ∀ p : Set.Icc (0 : ℝ) T × Euc d, 0 < Torus.lift (f p.1) p.2 := fun p => hpos p.1 p.1.2 _
  have hne : ∀ p : Set.Icc (0 : ℝ) T × Euc d, Torus.lift (f p.1) p.2 ≠ 0 := fun p => (hposl p).ne'
  have hcd : ∀ p : Set.Icc (0 : ℝ) T × Euc d, ContDiff ℝ 2 (Torus.lift (f p.1)) := fun p => hm.c2 p.1 p.1.2
  apply movb_c12_iff.2
  refine ⟨fun r hr => mova_isCk_log (hm.c2 r hr) (hpos r hr), ?_, ?_, ?_, ?_, ?_⟩
  · exact hm.c0.log hne
  · refine (hm.c0.inv₀ hne).smul hm.c1 |>.congr fun p => ?_
    exact (movb_fderiv_log (hcd p) (fun w => hpos p.1 p.1.2 _) p.2).symm
  · have hc3 : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
        (-((Torus.lift (f p.1) p.2) ^ 2)⁻¹) • fderiv ℝ (Torus.lift (f p.1)) p.2 :=
      (((hm.c0.pow 2).inv₀ (fun p => pow_ne_zero 2 (hne p))).neg).smul hm.c1
    have := ((hm.c0.inv₀ hne).smul hm.c2').add
      (((ContinuousLinearMap.smulRightL ℝ (Euc d) (Euc d →L[ℝ] ℝ)).continuous.comp hc3).clm_apply hm.c1)
    refine this.congr fun p => ?_
    exact (movb_fderiv2_log (hcd p) (fun w => hpos p.1 p.1.2 _) p.2).symm
  · intro x r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
    exact (hm.td x r hr).log (hpos r hr' x).ne'
  · refine hm.ctd.div ?_ fun p => (hpos p.1 p.1.2 p.2).ne'
    exact (movb_c12_iff.2 hm |> IsC12Test.continuous_f)


theorem movb_phi_isC12Test (D : DynData d) (hV : Torus.IsCk 2 D.V) (M : ℝ) {T : ℝ}
    {ρ ρt : ℝ → Torus d → ℝ} (hρt : IsC12Test T ρ ρt)
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) :
    IsC12Test T (movT_phi D M ρ) (movT_phit D M ρ ρt) := by
  have hg : Torus.IsSmooth (b15c_gReg d D.s M) :=
    b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M
  have h1 : MovbC12 T (fun _ => D.V) (fun _ _ => 0) := MovbC12.of_const hV
  have h2 := movb_c12_iff.1 (movb_isC12Test_convFun hρt hg)
  have h4 := movb_c12_iff.1 (movb_isC12Test_log hρt hpos)
  have h5 := ((h1.add h2).const_mul D.invβ⁻¹).add h4
  have e1 : movT_phi D M ρ = fun r x => D.invβ⁻¹ * (D.V x + convFun (b15c_gReg d D.s M) (ρ r) x) +
      Real.log (ρ r x) := rfl
  have e2 : movT_phit D M ρ ρt = fun r x => D.invβ⁻¹ * (0 + convFun (b15c_gReg d D.s M) (ρt r) x) +
      ρt r x / ρ r x := by
    funext r x; simp [movT_phit]
  rw [e1, e2]
  exact movb_c12_iff.2 h5

/-- The linear map `Euc (N d) → Euc d` reading the `i`-th particle. -/
def movb_Li (d N : ℕ) (i : Fin N) : Euc (N * d) →L[ℝ] Euc d :=
  (ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d).comp
    ((d1_eucEquiv d N).symm : Euc (N * d) ≃L[ℝ] (Fin N → Euc d)).toContinuousLinearMap

theorem movb_lift_bigPsi {N : ℕ} (φ : Torus d → ℝ) (z : Euc (N * d)) :
    Torus.lift (mova_bigPsi (N := N) φ) z = ∑ i, Torus.lift φ (movb_Li d N i z) := by
  simp [Torus.lift, mova_bigPsi, d1_configEquiv_symm_mk, movb_Li]

theorem movb_isC12Test_bigPsi {N : ℕ} {T : ℝ} {φ φt : ℝ → Torus d → ℝ} (hφ : IsC12Test T φ φt) :
    IsC12Test T (fun r => mova_bigPsi (N := N) (φ r)) (fun r => mova_bigPsi (N := N) (φt r)) := by
  refine ⟨fun r hr => mova_bigPsi_isCk (hφ.c2 r hr), fun j hj => ?_, fun x r hr => ?_, ?_⟩
  · have hterm : ∀ (p : Set.Icc (0 : ℝ) T × Euc (N * d)),
        iteratedFDeriv ℝ j (Torus.lift (mova_bigPsi (N := N) (φ p.1))) p.2 =
          ∑ i, (iteratedFDeriv ℝ j (Torus.lift (φ p.1)) (movb_Li d N i p.2)).compContinuousLinearMap
            (fun _ => movb_Li d N i) := by
      intro p
      have hc : ContDiff ℝ 2 (Torus.lift (φ p.1)) := hφ.c2 p.1 p.1.2
      have e : Torus.lift (mova_bigPsi (N := N) (φ p.1)) =
          fun z => ∑ i, Torus.lift (φ p.1) (movb_Li d N i z) :=
        funext (movb_lift_bigPsi (φ p.1))
      rw [e, iteratedFDeriv_fun_sum_apply (f := fun i z => Torus.lift (φ p.1) (movb_Li d N i z))
        (u := Finset.univ) (fun i _ =>
        ((hc.comp (movb_Li d N i).contDiff).of_le (by exact_mod_cast hj)).contDiffAt)]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (movb_Li d N i).iteratedFDeriv_comp_right hc p.2 (by exact_mod_cast hj)
    simp_rw [hterm]
    refine continuous_finset_sum _ fun i _ => ?_
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin j => movb_Li d N i)).continuous.comp
      ((hφ.cont_c2 j hj).comp (continuous_fst.prodMk ((movb_Li d N i).continuous.comp continuous_snd)))
  · simp only [mova_bigPsi]
    exact HasDerivAt.fun_sum fun i _ => hφ.time_deriv _ r hr
  · simp only [mova_bigPsi]
    refine continuous_finset_sum _ fun i _ => ?_
    exact hφ.cont_time_deriv.comp (continuous_fst.prodMk
      ((continuous_apply i).comp ((d1_configEquiv_symm_continuous d N).comp continuous_snd)))

end HRS
