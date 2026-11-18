import Mathlib
import HRS.MS.PoisGradAux1
import HRS.MS.PoisMaxAux1
import HRS.MS.PoisMollAux2

/-!
# POIS-GRADSM (part 2): regularity in time, the Bernstein maximum principle, closing

Supplement foundation packet POIS-GRADSM, S1 (`pois_gradsmooth`): `‖D (sg t f)‖_∞ ≤ C t^{-1/2} ‖f‖_∞`
for `0 < t ≤ 1`, `C = √(Mb + 1)`, `Mb` the bound of `‖B‖`, `‖DB‖`.

Route (Bernstein).  For a smooth drift `B` (`HasCbBound 3 M3 B` with `‖B‖, ‖DB‖ ≤ Mb`) and smooth compactly
supported data `f`, put `u(s, z) = sg s f z`, `g = L f` (`kolmL`).
* `gs_K3`: `P_t (L f) = L (P_t f)` (Markov property `sg_markov_C2` plus the Kolmogorov equation for `P_t f`
  at time `0`, uniqueness of the one-sided derivative).
* `gs_package`: joint continuity of `u`, `∂_e u` and the time derivatives
  `∂_s u = L u`, `∂_s ∂_e u = ∂_e L u` on `[0,1] × ℝ^d`.  The second one is obtained by differentiating the
  Duhamel formula `u(s) = f + ∫_0^s P_r (L f) dr` in `x` under the integral sign (`kl_hasFDerivAt_intervalIntegral`;
  this is where compact support of `f` is used: `L f ∈ C_c^∞` has bounded derivatives, so `pois_kolmogorov`
  applies to it) and the fundamental theorem of calculus (`pf_hasDerivWithinAt_of_integral`).
* `gs_bernstein_dir`: `A u² + s (∂_e u)² ≤ A ‖f‖²_∞` (`A = Mb + 1`, `‖e‖ = 1`) by the penalised maximum
  principle `pm_penalized_max` (D0(b)) with the pointwise inequality of `PoisGradAux1`.

Then (see the end of the file): `gs_grad_smooth_drift` (all unit directions), the data variable by
`pois_moll_close_data` (cut-off `χ(·/n) f`), and the drift variable by `pois_moll_close_drift`
(`B_n = B * η_n` of `pois_moll_drift`), giving `pois_gradsmooth` for `B` with `HasCbBound m Mb B`.

Statement adjustments relative to the packet sketch (documented, harmless): the Bernstein function is taken
in a fixed unit direction `e` instead of `|∇u|²`; the data are `C^∞` with bounded derivatives up to order
`2` (the closing lemma needs `C^k`, `k ≤ m`); the constant is `√(Mb + 1)` (independent of `q`) because the
term `-q |∇u|²` has a good sign; the noise is a Brownian filtration (as in `pois_kolmogorov`).
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Interval RealInnerProductSpace ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisGrad HRS.MS.PoisMax HRS.MS.PoisMoll

noncomputable section

universe u

namespace HRS.MS.PoisGrad

variable {d : ℕ}

section Reg

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

theorem gs_flow_zero {q Mb : ℝ} (hq : 0 ≤ q) {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) (hW : SgNoise W) (a : Ω) (x : Euc d) :
    flowMap q B (fun s => W s a) 0 x = x := by
  have H : PfHyp q Mb m B (fun s => W s a) := ⟨hq, hm, hB, hW.cont a, hW.zero a⟩
  unfold flowMap
  rw [pf_Z_zero H x, pf_ou_zero (hW.zero a)]
  simp

theorem gs_sg_zero [IsProbabilityMeasure P] {q Mb : ℝ} (hq : 0 ≤ q) {m : ℕ} (hm : 1 ≤ m)
    {B : Euc d → Euc d} (hB : HasCbBound m Mb B) (hW : SgNoise W) (h : Euc d → ℝ) (x : Euc d) :
    sg P W q B 0 h x = h x := by
  unfold sg
  simp [gs_flow_zero hq hm hB hW]



theorem gs_cd_inf {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euc d → F}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) :=
  hf.fderiv_right (by simp)

theorem gs_g_smooth {q : ℝ} {B : Euc d → Euc d} (hB : ContDiff ℝ 2 B) {f : Euc d → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 (kolmL q B f) := by
  have e : kolmL q B f = fun y => (∑ i : Fin d, fderiv ℝ (fderiv ℝ f) y (gsE i) (gsE i)) +
      fderiv ℝ f y (-q • y + B y) := funext (kl_L_eq q B f)
  rw [e]
  have h1 : ContDiff ℝ 2 (fderiv ℝ f) := (gs_cd_inf hf).of_le (by norm_num)
  have h2 : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ f)) :=
    (gs_cd_inf (gs_cd_inf hf)).of_le (by norm_num)
  refine (ContDiff.sum fun i _ => ?_).add (h1.clm_apply ?_)
  · exact (h2.clm_apply contDiff_const).clm_apply contDiff_const
  · exact ((contDiff_id.const_smul (-q) : ContDiff ℝ 2 fun y : Euc d => -q • y)).add hB

theorem gs_g_support {q : ℝ} {B : Euc d → Euc d} {f : Euc d → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (kolmL q B f) := by
  refine HasCompactSupport.intro hfc fun y hy => ?_
  have hz : f =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.1 hy
  have h1 : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (0 : Euc d → ℝ) := hz.fderiv
  have h1y : fderiv ℝ f y = 0 := by simpa using h1.self_of_nhds
  have h2y : fderiv ℝ (fderiv ℝ f) y = 0 := by
    have := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) h1
    simpa using this
  rw [kl_L_eq, h1y, h2y]
  simp

theorem gs_g_bounds {q : ℝ} {B : Euc d → Euc d} (hB : ContDiff ℝ 2 B) {f : Euc d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (∃ M0 : ℝ, ∀ y, ‖kolmL q B f y‖ ≤ M0) ∧ (∃ M1 : ℝ, ∀ y, ‖fderiv ℝ (kolmL q B f) y‖ ≤ M1) ∧
      ∃ M2 : ℝ, ∀ y, ‖iteratedFDeriv ℝ 2 (kolmL q B f) y‖ ≤ M2 := by
  have hg := gs_g_smooth (q := q) hB hf
  have hgc := gs_g_support (q := q) (B := B) hfc
  refine ⟨(hg.continuous).bounded_above_of_compact_support hgc, ?_, ?_⟩
  · exact (hg.continuous_fderiv (by norm_num)).bounded_above_of_compact_support (hgc.fderiv (𝕜 := ℝ))
  · exact (hg.continuous_iteratedFDeriv (by norm_num)).bounded_above_of_compact_support
      (hgc.iteratedFDeriv (𝕜 := ℝ) 2)


theorem gs_sg_cd [IsProbabilityMeasure P] {q M3 : ℝ} (hq : 0 < q) {B : Euc d → Euc d}
    (hB : HasCbBound 3 M3 B) (hW : SgNoise W) {f : Euc d → ℝ} {k : ℕ} (hk : k ≤ 3)
    (hf : ContDiff ℝ (k : WithTop ℕ∞) f) {M : ℝ} (hM : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ M)
    {T : ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ (k : WithTop ℕ∞) (sg P W q B t f) ∧
      ∃ M' : ℝ, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (sg P W q B t f) x‖ ≤ M' := by
  obtain ⟨C, -, hC⟩ := sg_contDiff (d := d) q M3 hq 3 (by norm_num) T (ht.1.trans ht.2) k hk
  obtain ⟨h1, -, h3⟩ := hC P W hW B hB f hf M hM t ht
  exact ⟨h1, C * M, h3⟩

theorem gs_K3 [IsProbabilityMeasure P] {q M3 : ℝ} (hq : 0 < q) {B : Euc d → Euc d}
    (hB : HasCbBound 3 M3 B) (hW : IsBrownianFiltration P ℱ W) {f : Euc d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    sg P W q B t (kolmL q B f) x = kolmL q B (sg P W q B t f) x := by
  have hWs := sgNoise_of_brownian hW
  obtain ⟨C, -, hC⟩ := hfc.exists_bound_iteratedFDeriv hf 3
  have hf3 : ContDiff ℝ 3 f := hf.of_le (by norm_num)
  have hM1 : ∀ y, ‖fderiv ℝ f y‖ ≤ C := fun y => by
    have := hC 1 (by norm_num) y
    rwa [norm_iteratedFDeriv_one] at this
  have hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ C := fun y => hC 2 (by norm_num) y
  have hkf := (pois_kolmogorov hq (m := 3) (by norm_num) hB hW (hf.of_le (by norm_num)) hM1 hM2).2.1 x t ht
  obtain ⟨hφ, M', hM'⟩ := gs_sg_cd (P := P) (W := W) hq hB hWs (k := 2) (by norm_num)
    (hf.of_le (by norm_num)) (M := C) (fun i hi => hC i (by omega)) (T := t) (t := t) ⟨ht, le_rfl⟩
  have hφ1 : ∀ y, ‖fderiv ℝ (sg P W q B t f) y‖ ≤ M' := fun y => by
    have := hM' 1 (by norm_num) y
    rwa [norm_iteratedFDeriv_one] at this
  have hkφ := (pois_kolmogorov hq (m := 3) (by norm_num) hB hW hφ hφ1
    (fun y => hM' 2 le_rfl y)).2.1 x 0 le_rfl
  rw [gs_sg_zero hq.le (by norm_num) hB hWs] at hkφ
  have inner : HasDerivWithinAt (fun s : ℝ => s + t) 1 (Ici 0) 0 :=
    (hasDerivWithinAt_id (0 : ℝ) (Ici 0)).add_const t
  have hkf' : HasDerivWithinAt (fun s => sg P W q B s f x) (sg P W q B t (kolmL q B f) x) (Ici 0)
      ((fun s : ℝ => s + t) 0) := by simpa using hkf
  have hcomp := hkf'.comp (0 : ℝ) inner (fun s hs => by
    have : (0:ℝ) ≤ s := hs
    show (0:ℝ) ≤ s + t
    linarith)
  have hcomp' : HasDerivWithinAt (fun s : ℝ => sg P W q B s (sg P W q B t f) x)
      (sg P W q B t (kolmL q B f) x) (Ici 0) 0 := by
    refine (by simpa using hcomp : HasDerivWithinAt ((fun s => sg P W q B s f x) ∘ fun s : ℝ => s + t)
      (sg P W q B t (kolmL q B f) x) (Ici 0) 0).congr (fun s hs => ?_) (by simp [gs_sg_zero hq.le (by norm_num) hB hWs])
    have hs0 : (0:ℝ) ≤ s := hs
    exact (sg_markov_C2 hW hq.le (m := 3) (by norm_num) hB (hf.of_le (by norm_num))
      (M := C) (fun i hi => hC i (by omega)) hs0 ht x).symm
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hcomp' hkφ


theorem gs_package [IsProbabilityMeasure P] {q M3 : ℝ} (hq : 0 < q) {B : Euc d → Euc d}
    (hB : HasCbBound 3 M3 B) (hW : IsBrownianFiltration P ℱ W) {f : Euc d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (e : Euc d) :
    ContinuousOn (fun p : ℝ × Euc d => sg P W q B p.1 f p.2) (Icc 0 1 ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (sg P W q B p.1 f) p.2 e) (Icc 0 1 ×ˢ univ) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ z, HasDerivWithinAt (fun s => sg P W q B s f z)
      (kolmL q B (sg P W q B t f) z) (Icc 0 1) t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ z, HasDerivWithinAt (fun s => fderiv ℝ (sg P W q B s f) z e)
      (gsD e (kolmL q B (sg P W q B t f)) z) (Icc 0 1) t) := by
  have hWs := sgNoise_of_brownian hW
  obtain ⟨C, -, hC⟩ := hfc.exists_bound_iteratedFDeriv hf 3
  have hM1 : ∀ y, ‖fderiv ℝ f y‖ ≤ C := fun y => by
    have := hC 1 (by norm_num) y
    rwa [norm_iteratedFDeriv_one] at this
  have hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ C := fun y => hC 2 (by norm_num) y
  have hKf := pois_kolmogorov hq (m := 3) (by norm_num) hB hW (hf.of_le (by norm_num)) hM1 hM2
  have hB2 : ContDiff ℝ 2 B := hB.1.of_le (by norm_num)
  obtain ⟨⟨M0g, hM0g⟩, ⟨M1g, hM1g⟩, ⟨M2g, hM2g⟩⟩ := gs_g_bounds (q := q) hB2 hf hfc
  have hgs := gs_g_smooth (q := q) hB2 hf
  have hM0g' : ∀ y, ‖kolmL q B f y‖ ≤ M0g := hM0g
  have hKg := pois_kolmogorov hq (m := 3) (by norm_num) hB hW hgs hM1g
    (fun y => by simpa using hM2g y)
  have hI := hKg.2.2.2 1 one_pos
  have hcont : ContinuousOn (fun p : ℝ × Euc d => sg P W q B p.1 f p.2) (Icc 0 1 ×ˢ univ) :=
    (hKf.2.2.2 1 one_pos).cont
  have hcontD : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (sg P W q B p.1 f) p.2)
      (Icc 0 1 ×ˢ univ) := (hKf.2.2.2 1 one_pos).cont_fderiv
  refine ⟨hcont, ?_, ?_, ?_⟩
  · exact (ContinuousLinearMap.apply ℝ ℝ e).continuous.comp_continuousOn hcontD
  · intro t ht z
    have := (hKf.2.1 z t ht.1).mono (fun r (hr : r ∈ Icc (0:ℝ) 1) => hr.1)
    rwa [gs_K3 hq hB hW hf hfc ht.1 z] at this
  · intro t ht z
    -- the integral representation of `fderiv (sg s f) z e`
    have hK1 := hKf.1
    have hKg1 := hKg.1
    have hcg : ContinuousOn (fun p : ℝ × Euc d => sg P W q B p.1 (kolmL q B f) p.2)
        (Icc 0 1 ×ˢ univ) := hI.cont
    have hdg : ∀ s ∈ Icc (0 : ℝ) 1, Differentiable ℝ (sg P W q B s (kolmL q B f)) :=
      fun s hs y => (hI.hasFDerivAt s hs y (mem_univ _)).differentiableAt
    have hbd : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, ‖fderiv ℝ (sg P W q B s (kolmL q B f)) y‖ ≤
        Real.exp (q + M3) * M1g := by
      intro s hs y
      have hM3 : 0 ≤ M3 := (norm_nonneg _).trans (by simpa using hB.2 0 (Nat.zero_le _) 0)
      have := sg_fderiv_bound q M3 hq 3 (by norm_num) P W hWs B hB (kolmL q B f)
        (hgs.of_le (by norm_num)) M0g M1g hM0g' hM1g s hs.1 y
      refine this.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) ?_)
      · nlinarith [hs.2, hs.1]
      · exact (norm_nonneg _).trans (hM1g 0)
    have hpair : ContinuousOn (fun r : ℝ => (r, z)) (Icc (0:ℝ) 1) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hc : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (sg P W q B p.1 (kolmL q B f)) p.2)
        (Icc 0 1 ×ˢ univ) := hI.cont_fderiv
    have hcD : ContinuousOn (fun r : ℝ => fderiv ℝ (sg P W q B r (kolmL q B f)) z) (Icc 0 1) :=
      ContinuousOn.comp (g := fun p : ℝ × Euc d => fderiv ℝ (sg P W q B p.1 (kolmL q B f)) p.2)
        (f := fun r : ℝ => (r, z)) hc hpair (fun r hr => ⟨hr, mem_univ _⟩)
    have hRep : ∀ s ∈ Icc (0 : ℝ) 1, fderiv ℝ (sg P W q B s f) z e =
        fderiv ℝ f z e + ∫ r in (0 : ℝ)..s, fderiv ℝ (sg P W q B r (kolmL q B f)) z e := by
      intro s hs
      have hF := kl_hasFDerivAt_intervalIntegral (d := d) zero_le_one
        (fun r y => sg P W q B r (kolmL q B f) y) hcg hdg hbd hs z
      have hsF : sg P W q B s f = fun y => f y + ∫ r in (0 : ℝ)..s, sg P W q B r (kolmL q B f) y :=
        funext (hK1 s hs.1)
      have hdf : DifferentiableAt ℝ f z := hf.differentiable (by simp) z
      have h3 : HasFDerivAt (sg P W q B s f) (fderiv ℝ f z +
          ∫ r in (0 : ℝ)..s, fderiv ℝ (sg P W q B r (kolmL q B f)) z) z := by
        rw [hsF]
        exact hdf.hasFDerivAt.add hF
      rw [h3.fderiv]
      have hint : IntervalIntegrable (fun r => fderiv ℝ (sg P W q B r (kolmL q B f)) z) volume 0 s := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hs.1]
        exact hcD.mono (fun r hr => ⟨hr.1, hr.2.trans hs.2⟩)
      simp only [ContinuousLinearMap.add_apply]
      rw [ContinuousLinearMap.intervalIntegral_apply hint]
    have hFc : ContinuousOn (fun r => fderiv ℝ (sg P W q B r (kolmL q B f)) z e) (Icc 0 1) :=
      (ContinuousLinearMap.apply ℝ ℝ e).continuous.comp_continuousOn hcD
    have := pf_hasDerivWithinAt_of_integral (E := ℝ) (T := 1) (F := fun r => fderiv ℝ (sg P W q B r (kolmL q B f)) z e)
      (Z := fun s => fderiv ℝ (sg P W q B s f) z e) (x := fderiv ℝ f z e) hFc
      (fun s hs => by
        rw [hRep s hs, intervalIntegral.integral_of_le hs.1, integral_Icc_eq_integral_Ioc]) t ht
    have e2 : sg P W q B t (kolmL q B f) = kolmL q B (sg P W q B t f) :=
      funext (gs_K3 hq hB hW hf hfc ht.1)
    rw [e2] at this
    exact this


/-- `|sg t f| ≤ M0` for a bounded `f`. -/
theorem gs_sg_abs_le [IsProbabilityMeasure P] {q : ℝ} {B : Euc d → Euc d} {f : Euc d → ℝ}
    {M0 : ℝ} (hM0 : ∀ y, ‖f y‖ ≤ M0) (t : ℝ) (x : Euc d) :
    ‖sg P W q B t f x‖ ≤ M0 := by
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun a => f (flowMap q B (fun s => W s a) t x)) (C := M0)
    (Eventually.of_forall fun a => hM0 _)
  unfold sg
  simpa using this

/-- **Bernstein estimate for a smooth drift and compactly supported smooth data.**
`A u² + t (∂_e u)² ≤ A ‖f‖²_∞` on `[0,1] × ℝ^d`, `A = Mb + 1`. -/
theorem gs_bernstein_dir [IsProbabilityMeasure P] {q M3 Mb : ℝ} (hq : 0 < q) {B : Euc d → Euc d}
    (hB : HasCbBound 3 M3 B) (hB0 : ∀ y, ‖B y‖ ≤ Mb) (hB1 : ∀ y, ‖fderiv ℝ B y‖ ≤ Mb)
    (hW : IsBrownianFiltration P ℱ W) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {M0 : ℝ} (hM0 : ∀ y, ‖f y‖ ≤ M0) {e : Euc d} (he : ‖e‖ = 1) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, (Mb + 1) * sg P W q B s f z ^ 2 +
      s * (fderiv ℝ (sg P W q B s f) z e) ^ 2 ≤ (Mb + 1) * M0 ^ 2 := by
  have hWs := sgNoise_of_brownian hW
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (hB0 0)
  have hM3 : 0 ≤ M3 := (norm_nonneg _).trans (by simpa using hB.2 0 (Nat.zero_le _) 0)
  obtain ⟨C, -, hC⟩ := hfc.exists_bound_iteratedFDeriv hf 3
  obtain ⟨hc1, hc2, hderU, hderV⟩ := gs_package (P := P) (W := W) hq hB hW hf hfc e
  set A : ℝ := Mb + 1 with hA
  set lam : ℝ := 2 * d + Mb + 1 with hlam
  have hu3 : ∀ s ∈ Icc (0 : ℝ) 1, ContDiff ℝ 3 (sg P W q B s f) := fun s hs =>
    (gs_sg_cd (P := P) (W := W) hq hB hWs (k := 3) le_rfl (hf.of_le (by norm_num)) (M := C)
      (fun i hi => hC i hi) (T := 1) hs).1
  -- the growth bound for the derivative
  have hK : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, ‖fderiv ℝ (sg P W q B s f) z‖ ≤
      Real.exp (q + M3) * C := by
    intro s hs z
    have hM1 : ∀ y, ‖fderiv ℝ f y‖ ≤ C := fun y => by
      have := hC 1 (by norm_num) y
      rwa [norm_iteratedFDeriv_one] at this
    have hM0' : ∀ y, ‖f y‖ ≤ C := fun y => by
      have := hC 0 (by norm_num) y
      rwa [norm_iteratedFDeriv_zero] at this
    have := sg_fderiv_bound q M3 hq 3 (by norm_num) P W hWs B hB f (hf.of_le (by norm_num)) C C
      hM0' hM1 s hs.1 z
    refine this.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) ((norm_nonneg _).trans (hM1 0)))
    nlinarith [hs.2, hs.1]
  let G : ℝ → Euc d → ℝ := fun s z => A * sg P W q B s f z ^ 2 +
      s * (fderiv ℝ (sg P W q B s f) z e) ^ 2 - A * M0 ^ 2
  let Gt : ℝ → Euc d → ℝ := fun s z =>
    2 * A * sg P W q B s f z * kolmL q B (sg P W q B s f) z + (gsD e (sg P W q B s f) z) ^ 2 +
      2 * s * gsD e (sg P W q B s f) z * gsD e (kolmL q B (sg P W q B s f)) z
  have hmain : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, G s z ≤ 0 := by
    have hAnn : 0 ≤ A := by positivity
    refine pm_penalized_max (E := Euc d) G Gt 1 ?_ ?_ ?_ ?_ ?_
    · have := ((continuousOn_const (c := A)).mul (hc1.pow 2)).add
        ((continuousOn_fst).mul (hc2.pow 2)) |>.sub (continuousOn_const (c := A * M0 ^ 2))
      exact this
    · intro t ht z
      have hu := hderU t ht z
      have hv := hderV t ht z
      have := (((hu.pow 2).const_mul A).add ((hasDerivWithinAt_id t (Icc 0 1)).mul (hv.pow 2))).sub_const
        (A * M0 ^ 2)
      refine this.congr_deriv ?_
      simp only [Gt, gsD, id, Pi.pow_apply]
      ring
    · intro z
      show A * sg P W q B 0 f z ^ 2 + 0 * (fderiv ℝ (sg P W q B 0 f) z e) ^ 2 - A * M0 ^ 2 ≤ 0
      rw [gs_sg_zero hq.le (by norm_num) hB hWs]
      have h1 : f z ^ 2 ≤ M0 ^ 2 := by
        rw [← sq_abs]
        have := hM0 z
        rw [Real.norm_eq_abs] at this
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      nlinarith
    · intro δ hδ
      refine ⟨(Real.exp (q + M3) * C) ^ 2, fun s hs z => ?_⟩
      show A * sg P W q B s f z ^ 2 + s * (fderiv ℝ (sg P W q B s f) z e) ^ 2 - A * M0 ^ 2 ≤ _
      have h1 : sg P W q B s f z ^ 2 ≤ M0 ^ 2 := by
        rw [← sq_abs]
        have := gs_sg_abs_le (P := P) (W := W) (q := q) (B := B) hM0 s z
        rw [Real.norm_eq_abs] at this
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      have h2 : (fderiv ℝ (sg P W q B s f) z e) ^ 2 ≤ (Real.exp (q + M3) * C) ^ 2 := by
        rw [← sq_abs]
        have h3 := (fderiv ℝ (sg P W q B s f) z).le_opNorm e
        rw [he, mul_one, Real.norm_eq_abs] at h3
        exact pow_le_pow_left₀ (abs_nonneg _) (h3.trans (hK s hs z)) 2
      have h4 : 0 ≤ δ * ‖z‖ ^ 2 := by positivity
      have h5 : s * (fderiv ℝ (sg P W q B s f) z e) ^ 2 ≤ (Real.exp (q + M3) * C) ^ 2 := by
        have := hs.2
        have h6 : 0 ≤ (fderiv ℝ (sg P W q B s f) z e) ^ 2 := sq_nonneg _
        nlinarith [hs.1]
      nlinarith
    · refine ⟨lam, fun ε hε s hs z _ hmax => ?_⟩
      have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
      set φ := sg P W q B s f with hφdef
      have hφ3 : ContDiff ℝ 3 φ := hu3 s hs1
      have hφ2 : ContDiff ℝ 2 φ := hφ3.of_le (by norm_num)
      have hv2 : ContDiff ℝ 2 (gsD e φ) := gs_D_contDiff (n := 2) hφ3 e
      set κ : ℝ := ε * Real.exp (lam * s) with hκ
      have hκpos : 0 < κ := by positivity
      let Ws : Euc d → ℝ := fun y => A * φ y ^ 2 + s * (gsD e φ y) ^ 2
      have hWc : ContDiff ℝ 2 Ws := by
        have := ((hφ2.pow 2).const_smul A).add ((hv2.pow 2).const_smul s)
        simpa [Ws, smul_eq_mul] using this
      have hmaxW : IsLocalMax (fun y => Ws y - κ * (1 + ‖y‖ ^ 2)) z := by
        refine Eventually.of_forall fun y => ?_
        have := hmax y
        simp only [G] at this
        show Ws y - κ * (1 + ‖y‖ ^ 2) ≤ Ws z - κ * (1 + ‖z‖ ^ 2)
        simp only [Ws, gsD, hκ]
        nlinarith
      have h1 := gs_max_step q B hWc hmaxW
      have h2 := gs_bernstein_point (q := q) (Mb := Mb) (hB.1.of_le (by norm_num)) hφ3 he
        (hB1 z) hs.1.le hs.2 (le_refl A) hq.le
      have h3 : inner ℝ z (-q • z + B z) ≤ ‖z‖ * Mb := by
        rw [inner_add_right, inner_smul_right]
        have h4 : inner ℝ z (B z) ≤ ‖z‖ * ‖B z‖ := real_inner_le_norm _ _
        have h6 : -q * inner ℝ z z ≤ 0 := by
          rw [real_inner_self_eq_norm_sq]; nlinarith [sq_nonneg ‖z‖]
        nlinarith [mul_le_mul_of_nonneg_left (hB0 z) (norm_nonneg z)]
      have h7 : Gt s z ≤ κ * (2 * d + 2 * (‖z‖ * Mb)) := by
        refine le_trans h2 (h1.trans ?_)
        exact mul_le_mul_of_nonneg_left (by linarith) hκpos.le
      have h8 : 2 * (d : ℝ) + 2 * (‖z‖ * Mb) < lam * (1 + ‖z‖ ^ 2) := by
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith [sq_nonneg (‖z‖ - 1), mul_nonneg hMb (sq_nonneg (‖z‖ - 1)), sq_nonneg ‖z‖,
          mul_nonneg hd0 (sq_nonneg ‖z‖)]
      calc Gt s z ≤ κ * (2 * d + 2 * (‖z‖ * Mb)) := h7
        _ < κ * (lam * (1 + ‖z‖ ^ 2)) := mul_lt_mul_of_pos_left h8 hκpos
        _ = ε * lam * (1 + ‖z‖ ^ 2) * Real.exp (lam * s) := by rw [hκ]; ring
  intro s hs z
  have := hmain s hs z
  simp only [G] at this
  linarith


/-- **Gradient smoothing for a smooth drift and compactly supported smooth data.** -/
theorem gs_grad_smooth_drift [IsProbabilityMeasure P] {q M3 Mb : ℝ} (hq : 0 < q) {B : Euc d → Euc d}
    (hB : HasCbBound 3 M3 B) (hB0 : ∀ y, ‖B y‖ ≤ Mb) (hB1 : ∀ y, ‖fderiv ℝ B y‖ ≤ Mb)
    (hW : IsBrownianFiltration P ℱ W) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {M0 : ℝ} (hM0 : ∀ y, ‖f y‖ ≤ M0) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (x : Euc d) :
    ‖fderiv ℝ (sg P W q B t f) x‖ ≤ Real.sqrt (Mb + 1) * M0 / Real.sqrt t := by
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (hB0 0)
  have hM00 : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun e he => ?_
  have hb := gs_bernstein_dir hq hB hB0 hB1 hW hf hfc hM0 he t ⟨ht0.le, ht1⟩ x
  set v := fderiv ℝ (sg P W q B t f) x e with hv
  have h1 : t * v ^ 2 ≤ (Mb + 1) * M0 ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ Mb + 1) (sq_nonneg (sg P W q B t f x))]
  have h2 : (|v| * Real.sqrt t) ^ 2 ≤ (Real.sqrt (Mb + 1) * M0) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt ht0.le, Real.sq_sqrt (by linarith)]
    linarith
  have h3 : |v| * Real.sqrt t ≤ Real.sqrt (Mb + 1) * M0 :=
    (sq_le_sq₀ (by positivity) (by positivity)).1 h2
  rw [Real.norm_eq_abs, le_div_iff₀ hst]
  exact h3


/-- the cut-off `χ_n`, `1` on the ball of radius `n + 1`, supported in the ball of radius `n + 2`. -/
def gsCut (d n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩

theorem gs_cut_data {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {M0 : ℝ} (hM0 : ∀ y, ‖f y‖ ≤ M0) (n : ℕ) :
    ContDiff ℝ ∞ (fun y => gsCut d n y * f y) ∧ HasCompactSupport (fun y => gsCut d n y * f y) ∧
      (∀ y, ‖gsCut d n y * f y‖ ≤ M0) := by
  refine ⟨(gsCut d n).contDiff.mul hf, ?_, fun y => ?_⟩
  · exact (gsCut d n).hasCompactSupport.mul_right
  · rw [norm_mul]
    have h1 : ‖gsCut d n y‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg ((gsCut d n).nonneg)]; exact (gsCut d n).le_one
    calc ‖gsCut d n y‖ * ‖f y‖ ≤ 1 * M0 := mul_le_mul h1 (hM0 y) (norm_nonneg _) zero_le_one
      _ = M0 := one_mul _

theorem gs_cut_tendsto (f : Euc d → ℝ) (y : Euc d) :
    Tendsto (fun n : ℕ => gsCut d n y * f y) atTop (𝓝 (f y)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
  have h1 : y ∈ Metric.closedBall (0 : Euc d) (gsCut d n).rIn := by
    rw [mem_closedBall_zero_iff]
    show ‖y‖ ≤ (n : ℝ) + 1
    have := Nat.le_ceil ‖y‖
    have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [(gsCut d n).one_of_mem_closedBall h1, one_mul]


/-- Smooth drift, general bounded smooth data (closing in the data variable). -/
theorem gs_grad_smooth_data [IsProbabilityMeasure P] {q M3 Mb : ℝ} (hq : 0 < q) {m : ℕ}
    (hm : 2 ≤ m) {B : Euc d → Euc d} (hBm : HasCbBound m Mb B) (hB : HasCbBound 3 M3 B)
    (hW : IsBrownianFiltration P ℱ W) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {M0 : ℝ}
    (hM0 : ∀ y, ‖f y‖ ≤ M0) (hfM : ∃ M : ℝ, ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ M)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (x : Euc d) :
    ‖fderiv ℝ (sg P W q B t f) x‖ ≤ Real.sqrt (Mb + 1) * M0 / Real.sqrt t := by
  have hWs := sgNoise_of_brownian hW
  have hB0 : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hBm.2 0 (by omega) y
  have hB1 : ∀ y, ‖fderiv ℝ B y‖ ≤ Mb := fun y => by
    have := hBm.2 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  obtain ⟨M, hM⟩ := hfM
  set Bd : ℝ := Real.sqrt (Mb + 1) * M0 / Real.sqrt t with hBd
  have key := pois_moll_close_data (P := P) q Mb hq m hm 2 (by omega) 1 (by norm_num) hBm W hWs
    (hn := fun n y => gsCut d n y * f y)
    (fun n => ((gs_cut_data hf hM0 n).1).of_le (by norm_num))
    (fun n => by
      obtain ⟨C, -, hC⟩ := (gs_cut_data hf hM0 n).2.1.exists_bound_iteratedFDeriv
        (gs_cut_data hf hM0 n).1 2
      exact ⟨C, fun i hi y => hC i hi y⟩)
    (hf.of_le (by norm_num)) hM (fun y => gs_cut_tendsto f y) (fun n y => (gs_cut_data hf hM0 n).2.2 y)
    ht0.le (C := fun i => if i = 0 then M0 else Bd) (fun n i hi y => ?_) 1 le_rfl x
  · rw [norm_iteratedFDeriv_one] at key
    simpa using key
  · interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      simpa using gs_sg_abs_le (P := P) (W := W) (q := q) (B := B) (gs_cut_data hf hM0 n).2.2 t y
    · rw [norm_iteratedFDeriv_one]
      simpa using gs_grad_smooth_drift hq hB hB0 hB1 hW (gs_cut_data hf hM0 n).1
        (gs_cut_data hf hM0 n).2.1 (gs_cut_data hf hM0 n).2.2 ht0 ht1 y


/-- **POIS-GRADSM (S1).**  Gradient smoothing of the semigroup: for `B` with `HasCbBound m Mb B`
(`2 ≤ m`), `q > 0`, a Brownian filtration, and smooth data `f` (`C^∞`, `|f| ≤ M0`, derivatives up to
order `2` bounded), `‖D (sg t f)(x)‖ ≤ √(Mb + 1) M0 / √t` for `0 < t ≤ 1` and all `x`. -/
theorem pois_gradsmooth [IsProbabilityMeasure P] {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m)
    {B : Euc d → Euc d} (hB : HasCbBound m Mb B) (hW : IsBrownianFiltration P ℱ W)
    {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {M0 : ℝ} (hM0 : ∀ y, ‖f y‖ ≤ M0)
    (hfM : ∃ M : ℝ, ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ M) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (x : Euc d) :
    ‖fderiv ℝ (sg P W q B t f) x‖ ≤ Real.sqrt (Mb + 1) * M0 / Real.sqrt t := by
  have hWs := sgNoise_of_brownian hW
  obtain ⟨M, hM⟩ := hfM
  obtain ⟨Bn, -, hBnm, hBn3, -, hclose⟩ := pois_moll q Mb hq m hm hB
  have key := hclose P W hWs 2 hm 1 (by norm_num) f (hf.of_le (by norm_num)) M hM t ht0.le
    (fun i => if i = 0 then M0 else Real.sqrt (Mb + 1) * M0 / Real.sqrt t) (fun n i hi y => ?_) 1
    le_rfl x
  · rw [norm_iteratedFDeriv_one] at key
    simpa using key
  · obtain ⟨M3, hM3⟩ := hBn3 n 3
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      simpa using gs_sg_abs_le (P := P) (W := W) (q := q) (B := Bn n) hM0 t y
    · rw [norm_iteratedFDeriv_one]
      simpa using gs_grad_smooth_data hq hm (hBnm n) hM3 hW hf hM0 ⟨M, hM⟩ ht0 ht1 y

/-- The packet form: `‖D sg t f‖_∞ ≤ C t^{-1/2} ‖f‖_∞` with `C = √(Mb + 1)` depending only on `Mb`. -/
theorem pois_gradsmooth_rpow [IsProbabilityMeasure P] {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m)
    {B : Euc d → Euc d} (hB : HasCbBound m Mb B) (hW : IsBrownianFiltration P ℱ W)
    {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {M0 : ℝ} (hM0 : ∀ y, ‖f y‖ ≤ M0)
    (hfM : ∃ M : ℝ, ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ M) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (x : Euc d) :
    ‖fderiv ℝ (sg P W q B t f) x‖ ≤ Real.sqrt (Mb + 1) * t ^ (-(1 / 2 : ℝ)) * M0 := by
  have h := pois_gradsmooth hq hm hB hW hf hM0 hfM ht0 ht1 x
  have e : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg ht0.le, Real.sqrt_eq_rpow]
  rw [e]
  calc _ ≤ _ := h
    _ = _ := by rw [div_eq_mul_inv]; ring

end Reg

end HRS.MS.PoisGrad
