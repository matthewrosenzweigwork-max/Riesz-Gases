import HRS.MS.UniqE1b

/-!
# E1 of `UniqPlan.md`, part 3: continuity in `x`, Carathéodory measurability, Lipschitz in `τ`

* `e1_cont_x` : for `LocMass B u` and `σ ∈ [0,t]`, `x ↦ forwardPairing D ρ t σ u (η_ε(x - ·))` is continuous.
* `e1_caratheodory` : a function `f(σ,x)` that is a.e.-measurable in `σ` (for each `x`, w.r.t. the
  restricted Lebesgue measure on `[0,t]`) and continuous in `x` for each `σ ∈ [0,t]` agrees, for a.e. `σ`
  and **all** `x`, with a jointly measurable function.
* `e1_measurable` : the consequence for `f_ε`.
* `e1_bound_lipschitz` : the bound `|f_ε(σ,x)| ≤ C B (1+|x|)` for solutions, and the Lipschitz bound
  `|z_ε(τ,x) - z_ε(τ',x)| ≤ C B (1+|x|) |τ - τ'|`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqE1

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3

variable {d : ℕ}

/-! ### Continuity of `x ↦ ∫ u Φ(x,·)` -/

theorem e1_wt_lower (y : Euc d) {L : ℝ} (hL : 1 + ‖y‖ ≤ L) : 1 ≤ L ^ ((d : ℝ) + 2) * wt d y := by
  have h0 : 0 < 1 + ‖y‖ := by positivity
  have hL0 : 0 < L := lt_of_lt_of_le h0 hL
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : L ^ (-((d : ℝ) + 2)) ≤ wt d y :=
    Real.rpow_le_rpow_of_nonpos h0 hL (by linarith)
  calc (1 : ℝ) = L ^ ((d : ℝ) + 2) * L ^ (-((d : ℝ) + 2)) := by
        rw [← Real.rpow_add hL0]; simp
    _ ≤ _ := by gcongr

/-- Local domination: a kernel vanishing for `|y - x| > ε`, bounded by `H(x)`, is dominated near `x₀`
by a multiple of `wt`. -/
theorem e1_local_dom {ε : ℝ} (hε : 0 < ε) {Φ : Euc d → Euc d → ℝ} {H : Euc d → ℝ}
    (hvan : ∀ x y, ε < ‖y - x‖ → Φ x y = 0) (hH : ∀ x y, |Φ x y| ≤ H x) (x0 : Euc d) {H0 : ℝ}
    (hH0 : ∀ x, ‖x - x0‖ < 1 → H x ≤ H0) :
    ∀ x, ‖x - x0‖ < 1 → ∀ y, |Φ x y| ≤ (H0 * (2 + ‖x0‖ + ε) ^ ((d : ℝ) + 2)) * wt d y := by
  intro x hx y
  have hH00 : 0 ≤ H0 := (abs_nonneg _).trans ((hH x y).trans (hH0 x hx))
  have hL : 0 < 2 + ‖x0‖ + ε := by positivity
  by_cases hy : ε < ‖y - x‖
  · rw [hvan x y hy, abs_zero]
    exact mul_nonneg (mul_nonneg hH00 (Real.rpow_nonneg hL.le _)) (wt_pos y).le
  · have hyx : 1 + ‖y‖ ≤ 2 + ‖x0‖ + ε := by
      have h1 := norm_le_norm_add_norm_sub' y x
      have h2 := norm_le_norm_add_norm_sub' x x0
      linarith [not_lt.1 hy]
    have h3 := e1_wt_lower y hyx
    calc |Φ x y| ≤ H0 := (hH x y).trans (hH0 x hx)
      _ = H0 * 1 := (mul_one _).symm
      _ ≤ H0 * ((2 + ‖x0‖ + ε) ^ ((d : ℝ) + 2) * wt d y) := by gcongr
      _ = _ := by ring

theorem e1_cont_aux {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u) {Φ : Euc d → Euc d → ℝ}
    (hΦ : Continuous (fun p : Euc d × Euc d => Φ p.1 p.2))
    (hdom : ∀ x0 : Euc d, ∃ C : ℝ, ∀ x, ‖x - x0‖ < 1 → ∀ y, |Φ x y| ≤ C * wt d y) :
    Continuous (fun x => ∫ y, u y * Φ x y) := by
  have hΦy : ∀ x, Continuous (Φ x) := fun x => hΦ.comp (continuous_const.prodMk continuous_id)
  have hΦx : ∀ y, Continuous (fun x => Φ x y) := fun y =>
    hΦ.comp (continuous_id.prodMk continuous_const)
  refine continuous_iff_continuousAt.2 fun x0 => ?_
  obtain ⟨C, hC⟩ := hdom x0
  refine continuousAt_of_dominated (bound := fun y => C * (‖u y‖ * wt d y)) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => hu.1.mul (hΦy x).aestronglyMeasurable
  · have : {x : Euc d | ‖x - x0‖ < 1} ∈ 𝓝 x0 := by
      have := ball_mem_nhds x0 one_pos
      simpa [Metric.ball, dist_eq_norm] using this
    filter_upwards [this] with x hx
    refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |u y| * |Φ x y| ≤ |u y| * (C * wt d y) := by gcongr; exact hC x hx y
      _ = _ := by ring
  · exact (uw_int hu.1 (B ^ 2) hu.2).const_mul C
  · exact Filter.Eventually.of_forall fun y => ((hΦx y).continuousAt).const_mul (u y)

/-! ### (c0) Continuity in `x` -/

theorem e1_cont_x (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε)
    {u : Euc d → ℝ} {B : ℝ} (hu : LocMass B u) {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) t) :
    Continuous (fun x : Euc d => forwardPairing D ρ t σ u (fun y => eta d ε (x - y))) := by
  have hr : t - σ ∈ Set.Icc (0 : ℝ) T :=
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  obtain ⟨hbs, hb1, hb0, hρs, hρ0, hρ1⟩ := e1_coeff hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef hr
  have hCb0 : 0 ≤ HRS.MS.UniqC1.c1Cb d D.s m MB Λ ΛV G₀ :=
    e1_Cb_nonneg hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef (ht.1.trans ht.2)
  set ρt : Euc d → ℝ := ρ (t - σ) with hρt
  set b : Fin d → Euc d → ℝ := fun i y => meanFieldDriftW D ρt y i with hbdef
  have hθ := th_cc (d := d) hε
  obtain ⟨Θ, hΘ0, hΘ0', hΘ1, hΘ2⟩ := th_bounds (d := d) hε
  obtain ⟨CK, hCK0, hCK1, hCK2⟩ := th_conv_bounds (d := d) hs0 hsd hε
  have hfun : (fun x : Euc d => forwardPairing D ρ t σ u (fun y => eta d ε (x - y))) = fun x =>
      D.invβ * (∫ y, u y * R1 (th d ε) x y) - (∫ y, u y * R2 b (th d ε) x y) -
        ∑ i, ∑ j, D.M j i * (∫ y, u y * R3 D.s ρt (th d ε) i j x y) := by
    funext x; exact e1_fp_eq D ρ t σ hs0 hsd hbs hρs u hε x
  rw [hfun]
  have hsub : Continuous (fun p : Euc d × Euc d => p.2 - p.1) := continuous_snd.sub continuous_fst
  -- term 1
  have c1 : Continuous (fun x : Euc d => ∫ y, u y * R1 (th d ε) x y) := by
    refine e1_cont_aux hu ?_ fun x0 => ?_
    · simp only [R1]
      exact continuous_finset_sum _ fun i _ => ((hθ.D1 i).D1 i).cont.comp hsub
    · exact ⟨_, e1_local_dom hε (H := fun _ => d * Θ) (fun x y hy => e1_R1_vanish hε hy)
        (fun x y => e1_R1_abs hΘ2 x y) x0 (H0 := d * Θ) (fun _ _ => le_rfl)⟩
  -- term 2
  have c2 : Continuous (fun x : Euc d => ∫ y, u y * R2 b (th d ε) x y) := by
    refine e1_cont_aux hu ?_ fun x0 => ?_
    · simp only [R2]
      refine continuous_finset_sum _ fun i _ => ?_
      have hDb : Continuous (D1 i (b i)) :=
        ((hbs i).continuous_fderiv one_ne_zero).clm_apply continuous_const
      exact ((hDb.comp continuous_snd).mul ((hθ.cont).comp hsub)).add
        (((hbs i).continuous.comp continuous_snd).mul ((hθ.D1 i).cont.comp hsub))
    · refine ⟨_, e1_local_dom hε (H := fun x => (d * (HRS.MS.UniqC1.c1Cb d D.s m MB Λ ΛV G₀ * Θ * (2 + ε))) *
        (1 + ‖x‖)) (fun x y hy => e1_R2_vanish hε b hy)
        (fun x y => e1_R2_abs hε hΘ0 hCb0 hΘ0' hΘ1 b hb1 hb0 x y) x0
        (H0 := (d * (HRS.MS.UniqC1.c1Cb d D.s m MB Λ ΛV G₀ * Θ * (2 + ε))) * (2 + ‖x0‖))
        (fun x hx => ?_)⟩
      have hxn : ‖x‖ ≤ ‖x0‖ + 1 := by
        have := norm_le_norm_add_norm_sub' x x0
        linarith
      have : 0 ≤ (d : ℝ) * (HRS.MS.UniqC1.c1Cb d D.s m MB Λ ΛV G₀ * Θ * (2 + ε)) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) this
  -- term 3
  have c3 : ∀ i j, Continuous (fun x : Euc d => ∫ y, u y * R3 D.s ρt (th d ε) i j x y) := by
    intro i j
    refine e1_cont_aux hu ?_ fun x0 => ?_
    · have k1 : Continuous (D1 j ρt) :=
        (hρs.continuous_fderiv one_ne_zero).clm_apply continuous_const
      have k2 : Continuous (HRS.Whole.convFun (rieszKernel d D.s) (D1 i (th d ε))) :=
        K_cont hs0 hsd (hθ.D1 i).cont (hθ.D1 i).supp
      have k3 : Continuous (HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i (th d ε)))) :=
        K_cont hs0 hsd ((hθ.D1 i).D1 j).cont ((hθ.D1 i).D1 j).supp
      simp only [R3]
      exact ((k1.comp continuous_snd).mul (k2.comp hsub)).add
        ((hρs.continuous.comp continuous_snd).mul (k3.comp hsub))
    · refine ⟨HRS.MS.UniqC1.c1A d m Λ * (CK + CK) * (2 + ‖x0‖), fun x hx y => ?_⟩
      have h := e1_R3_abs hρ0 hρ1 hCK1 hCK2 i j x y
      have hxn : 1 + ‖x‖ ≤ 2 + ‖x0‖ := by
        have := norm_le_norm_add_norm_sub' x x0
        linarith
      have hA0 := e1_A_nonneg (d := d) m Λ
      refine h.trans ?_
      have : 0 ≤ HRS.MS.UniqC1.c1A d m Λ * (CK + CK) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxn this) (wt_pos y).le
  exact ((continuous_const.mul c1).sub c2).sub
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => continuous_const.mul (c3 i j))

/-! ### Carathéodory with an `x`-dependent null set -/

theorem e1_caratheodory {t : ℝ} {f : ℝ → Euc d → ℝ}
    (hmeas : ∀ x, AEStronglyMeasurable (fun σ => f σ x) (volume.restrict (Set.Icc 0 t)))
    (hcont : ∀ σ ∈ Set.Icc (0 : ℝ) t, Continuous (f σ)) :
    ∃ F : ℝ → Euc d → ℝ, Measurable (Function.uncurry F) ∧
      ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) t)), ∀ x, F σ x = f σ x := by
  classical
  set q : ℕ → Euc d := TopologicalSpace.denseSeq (Euc d) with hqdef
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq _
  have hg : ∀ n, ∃ g : ℝ → ℝ, Measurable g ∧
      (fun σ => f σ (q n)) =ᵐ[volume.restrict (Set.Icc 0 t)] g :=
    fun n => ⟨(hmeas (q n)).mk _, (hmeas (q n)).stronglyMeasurable_mk.measurable,
      (hmeas (q n)).ae_eq_mk⟩
  choose g hgm hgae using hg
  have hall : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) t)), ∀ n, f σ (q n) = g n σ :=
    ae_all_iff.2 hgae
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (s := {σ | ¬ ∀ n, f σ (q n) = g n σ})
    (ae_iff.1 hall)
  set E : Set ℝ := Set.Icc 0 t \ N with hE
  have hEm : MeasurableSet E := measurableSet_Icc.diff hNm
  set G : ℝ → Euc d → ℝ := fun σ x => if σ ∈ E then f σ x else 0 with hG
  have hGE : ∀ σ ∈ E, ∀ n, f σ (q n) = g n σ := fun σ hσ n => by
    by_contra h
    exact hσ.2 (hNsub (fun h' => h (h' n)))
  have hGmeas : ∀ x, Measurable (fun σ => G σ x) := by
    intro x
    have hx : x ∈ closure (Set.range q) := by rw [hq.closure_range]; exact Set.mem_univ _
    obtain ⟨a, ha, hat⟩ := mem_closure_iff_seq_limit.1 hx
    choose n hn using ha
    refine measurable_of_tendsto_metrizable (f := fun k => E.indicator (g (n k)))
      (fun k => (hgm (n k)).indicator hEm) (tendsto_pi_nhds.2 fun σ => ?_)
    by_cases hσ : σ ∈ E
    · have hcσ := hcont σ hσ.1
      have h1 : Tendsto (fun k => f σ (q (n k))) atTop (𝓝 (f σ x)) := by
        have : Tendsto (fun k => q (n k)) atTop (𝓝 x) := by
          simpa [hn] using hat
        exact (hcσ.tendsto x).comp this
      simp only [Set.indicator_of_mem hσ, hG, if_pos hσ]
      simpa [hGE σ hσ] using h1
    · simp [Set.indicator_of_notMem hσ, hG, if_neg hσ]
  have hGcont : ∀ σ, Continuous (fun x => G σ x) := by
    intro σ
    by_cases hσ : σ ∈ E
    · simp only [hG, if_pos hσ]; exact hcont σ hσ.1
    · simp only [hG, if_neg hσ]; exact continuous_const
  have hU : Measurable (Function.uncurry (fun (x : Euc d) (σ : ℝ) => G σ x)) :=
    measurable_uncurry_of_continuous_of_measurable (fun σ => hGcont σ) hGmeas
  refine ⟨G, ?_, ?_⟩
  · exact hU.comp measurable_swap
  · have hN0' : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) t)), σ ∉ N := by
      rw [ae_iff]; simpa using hN0
    filter_upwards [hN0', ae_restrict_mem measurableSet_Icc] with σ hσN hσI x
    simp only [hG, if_pos (show σ ∈ E from ⟨hσI, hσN⟩)]

/-! ### The conclusions for `f_ε` -/

/-- **(c)** Joint measurability of `f_ε`: there is a jointly Borel measurable `F : ℝ → ℝ^d → ℝ` with
`F(σ,x) = f_ε(σ,x)` for all `x` and a.e. `σ ∈ [0,t]` (Lebesgue); in particular
`(σ,x) ↦ f_ε(σ,x)` is `AEStronglyMeasurable` for `(volume.restrict (Icc 0 t)).prod volume`
(`e1_aestronglyMeasurable`). -/
theorem e1_measurable (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {B : ℝ}
    (hzB : ∀ τ ∈ Set.Icc (0 : ℝ) t, LocMass B (z τ)) :
    ∃ F : ℝ → Euc d → ℝ, Measurable (Function.uncurry F) ∧
      ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) t)), ∀ x, F σ x = fEps D ρ t z ε σ x := by
  refine e1_caratheodory (f := fun σ x => fEps D ρ t z ε σ x) (fun x => ?_) (fun σ hσ => ?_)
  · exact (hz.integrable _ (psi_contDiff ε x) (psi_compact hε x)).aestronglyMeasurable
  · exact e1_cont_x hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε (hzB σ hσ) hσ

theorem e1_aestronglyMeasurable (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {B : ℝ}
    (hzB : ∀ τ ∈ Set.Icc (0 : ℝ) t, LocMass B (z τ)) :
    AEStronglyMeasurable (fun p : ℝ × Euc d => fEps D ρ t z ε p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) t)).prod volume) := by
  obtain ⟨F, hF, hae⟩ := e1_measurable hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε hz hzB
  refine hF.aestronglyMeasurable.congr ?_
  have h1 : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) t)).prod (volume : Measure (Euc d))),
      ∀ x, F p.1 x = fEps D ρ t z ε p.1 x :=
    Measure.quasiMeasurePreserving_fst.ae hae
  filter_upwards [h1] with p hp using hp p.2

/-! ### The bound and the Lipschitz estimate -/

/-- **(b)** For a forward solution `z` with `LocMass B (z τ)` on `[0,t]`: `f_ε(·,x)` is integrable on `[0,t]`,
`|f_ε(σ,x)| ≤ C B (1+|x|)` for `σ ∈ [0,t]` (everywhere), and `z_ε(·,x)` is Lipschitz on `[0,t]`:
`|z_ε(τ,x) - z_ε(τ',x)| ≤ C B (1+|x|) |τ - τ'|`.  `C = C(d, D, ε, m, MB, Λ, ΛV, G₀) ≥ 0`
does not depend on `z, B, x, σ, τ`. -/
theorem e1_bound_lipschitz (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℝ → Euc d → ℝ), IsForwardDistSolutionW D ρ t z → ∀ B : ℝ, 0 ≤ B →
      (∀ τ ∈ Set.Icc (0 : ℝ) t, LocMass B (z τ)) →
      (∀ x, IntegrableOn (fun σ => fEps D ρ t z ε σ x) (Set.Icc 0 t)) ∧
      (∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ x, |fEps D ρ t z ε σ x| ≤ C * B * (1 + ‖x‖)) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ τ' ∈ Set.Icc (0 : ℝ) t, ∀ x,
        |moll d ε (z τ) x - moll d ε (z τ') x| ≤ C * B * (1 + ‖x‖) * |τ - τ'|) := by
  obtain ⟨C, hC0, hC⟩ := e1_bound hd hs0 hsd m MB Λ ΛV G₀ hMB hV hcoef ht hε
  refine ⟨C, hC0, fun z hz B hB hzB => ?_⟩
  have hint : ∀ x, IntegrableOn (fun σ => fEps D ρ t z ε σ x) (Set.Icc 0 t) := fun x =>
    hz.integrable _ (psi_contDiff ε x) (psi_compact hε x)
  have hbd : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ x, |fEps D ρ t z ε σ x| ≤ C * B * (1 + ‖x‖) :=
    fun σ hσ x => hC (z σ) B hB (hzB σ hσ) σ hσ x
  refine ⟨hint, hbd, fun τ hτ τ' hτ' x => ?_⟩
  have hrep : ∀ τ ∈ Set.Icc (0 : ℝ) t, moll d ε (z τ) x = ∫ σ in (0 : ℝ)..τ, fEps D ρ t z ε σ x := by
    intro τ hτ
    rw [e1_time_rep hz hε hτ x, intervalIntegral.integral_of_le hτ.1, integral_Icc_eq_integral_Ioc]
  have hii : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      IntervalIntegrable (fun σ => fEps D ρ t z ε σ x) volume 0 τ := by
    intro τ hτ
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact (hint x).mono_set (Set.Icc_subset_Icc le_rfl hτ.2)
  rw [hrep τ hτ, hrep τ' hτ', intervalIntegral.integral_interval_sub_left (hii τ hτ) (hii τ' hτ')]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := τ') (b := τ)
    (f := fun σ => fEps D ρ t z ε σ x) (C := C * B * (1 + ‖x‖)) (fun σ hσ => by
      have hσ' : σ ∈ Set.Icc (0 : ℝ) t :=
        Set.uIcc_subset_Icc hτ' hτ (Set.uIoc_subset_uIcc hσ)
      rw [Real.norm_eq_abs]; exact hbd σ hσ' x)
  rw [Real.norm_eq_abs] at this
  exact this

end HRS.MS.UniqE1
