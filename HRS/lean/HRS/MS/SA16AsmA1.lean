import HRS.MS.SA16StrongSL8
import HRS.MS.SA16StrongSL10Aux
import HRS.MS.SA16StrongSL5
import HRS.MS.SA16StrongSL3
import HRS.MS.SA16StrongLimit
import HRS.MS.SA16EvolDefs

/-!
# S.A.16 A1: `strong_path_lp_class`

The weak solution class of a norm-continuous path in `WmpSpace`: weak continuity is SL8, the bound is SL6 with
compactness of `[0,t]`, and the local continuity in `W^{m',p}` follows from the boundedness of multiplication by a
translated smooth compactly supported cutoff `W^{m,p} → W^{m',p}` (`sa16y_cm`): first for compact smooth jets
(Leibniz), then for the whole closed space by density and the limit lemma `sa16y_wnorm_limit`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Assembly
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution

section A1
variable {d : ℕ}

/-- a subsequence of an `L^p`-convergent sequence of lifts converges almost everywhere -/
lemma sa16y_wrep_subseq (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (G : ℕ → WmpSpace d m p) (G' : WmpSpace d m p)
    (hG : Tendsto G atTop (𝓝 G')) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂(volume : Measure (Euc d)),
      Tendsto (fun i => wrep d m p (G (ns i)) x) atTop (𝓝 (wrep d m p G' x)) := by
  have hp1 : (1 : ℝ) ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have hpe : ENNReal.ofReal p ≠ 0 := by simpa using (by linarith : 0 < p)
  have hzmeas : ∀ n, AEStronglyMeasurable (wrep d m p (G n)) volume := fun n =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : WIndex d m => ℝ) (wZero d m)).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (G n : WLp d m p))
  have hz'meas : AEStronglyMeasurable (wrep d m p G') volume :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : WIndex d m => ℝ) (wZero d m)).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (G' : WLp d m p))
  have hle : ∀ n, eLpNorm (wrep d m p (G n) - wrep d m p G') (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ‖G n - G'‖ := by
    intro n
    have hnorm' : ‖G n - G'‖ = (eLpNorm (fun x => ((((G n - G' : WmpSpace d m p) : WLp d m p) :
        Euc d → (WIndex d m → ℝ)) x)) (ENNReal.ofReal p) volume).toReal := by
      have : ‖G n - G'‖ = ‖((G n - G' : WmpSpace d m p) : WLp d m p)‖ := rfl
      rw [this, Lp.norm_def]
    have hfin' : eLpNorm (fun x => ((((G n - G' : WmpSpace d m p) : WLp d m p) :
        Euc d → (WIndex d m → ℝ)) x)) (ENNReal.ofReal p) volume < ⊤ := Lp.eLpNorm_lt_top _
    rw [hnorm', ENNReal.ofReal_toReal hfin'.ne]
    refine eLpNorm_mono_ae ((hzmeas n).sub hz'meas) ?_
    have h := Lp.coeFn_sub (G n : WLp d m p) (G' : WLp d m p)
    filter_upwards [h] with x hx
    have : (((G n - G' : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x =
      ((G n : WLp d m p) : Euc d → (WIndex d m → ℝ)) x - ((G' : WLp d m p) : Euc d → (WIndex d m → ℝ)) x := hx
    rw [this]
    exact norm_le_pi_norm (((G n : WLp d m p) : Euc d → (WIndex d m → ℝ)) x -
      ((G' : WLp d m p) : Euc d → (WIndex d m → ℝ)) x) (wZero d m)
  have hzT : Tendsto (fun n => eLpNorm (wrep d m p (G n) - wrep d m p G') (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
    have hnT : Tendsto (fun n => ‖G n - G'‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hG
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hle
    have : Tendsto (fun n => ENNReal.ofReal ‖G n - G'‖) atTop (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.tendsto_ofReal hnT
    simpa using this
  exact (tendstoInMeasure_of_tendsto_eLpNorm hpe hzT).exists_seq_tendsto_ae

/-- `wNormE` only depends on the almost-everywhere class -/
lemma sa16y_wNormE_congr (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {f g : Euc d → ℝ} (h : f =ᵐ[volume] g) :
    wNormE m p f = wNormE m p g := by
  have key : ∀ {f g : Euc d → ℝ}, f =ᵐ[volume] g → wNormE m p g ≤ wNormE m p f := by
    intro f g h
    unfold wNormE
    refine le_iInf₂ fun G hG => ?_
    refine iInf₂_le_of_le G ?_ le_rfl
    filter_upwards [hG, h] with x hx1 hx2
    rw [hx1, hx2]
  exact le_antisymm (key h.symm) (key h)

/-- the cutoff estimate for compact smooth jets -/
lemma sa16y_cm_smooth (m m' : ℕ) (p : ℝ) [Fact (2 ≤ p)] (hm' : m' ≤ m) (a u : 𝓢(Euc d, ℝ)) {B : ℝ}
    (hB : ∀ i ≤ m', ∀ x, ‖iteratedFDeriv ℝ i (⇑a) x‖ ≤ B) (G : WmpSpace d m p)
    (hG : ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (⇑u)) :
    wNormE m' p (⇑(sa16y_mulS a u)) ≤
      ENNReal.ofReal (B * ((d : ℝ) + 1) ^ m') * ENNReal.ofReal ‖G‖ := by
  refine (sa16y_mulS_wnorm m' p a u hB).trans (mul_le_mul' le_rfl ?_)
  refine (sa16y_wnorm_mono_level hm' p u).trans (le_of_eq ?_)
  refine (wNormE_eq_lift_norm d m p G (⇑u) ?_).symm.symm
  filter_upwards [hG] with x hx
  rw [hx]
  simp only [wJet, wZero]
  exact sa16j_pd_zero _ _ x

lemma sa16y_wJet_sub (m : ℕ) (a b : 𝓢(Euc d, ℝ)) :
    wJet m (⇑(a - b)) = fun x => wJet m (⇑a) x - wJet m (⇑b) x := by
  have ha : ContDiff ℝ ∞ (⇑a) := a.smooth'
  have hb : ContDiff ℝ ∞ (⇑b) := b.smooth'
  have hab : ⇑(a - b) = fun y => a y - b y := by funext y; simp
  funext x τ
  simp only [wJet, Pi.sub_apply]
  rw [hab, sa16y_pd_sub ha hb]

/-- the cutoff estimate on the whole closed space -/
lemma sa16y_cm (m m' : ℕ) (p : ℝ) [Fact (2 ≤ p)] (hm' : m' ≤ m) (a : 𝓢(Euc d, ℝ)) {B : ℝ}
    (hB : ∀ i ≤ m', ∀ x, ‖iteratedFDeriv ℝ i (⇑a) x‖ ≤ B) (H : WmpSpace d m p) (ε : ℝ) (hε : 0 < ε) :
    wNormE m' p (fun x => a x * wrep d m p H x) ≤
      ENNReal.ofReal (B * ((d : ℝ) + 1) ^ m') * ENNReal.ofReal (‖H‖ + ε) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  set c : ℝ := B * ((d : ℝ) + 1) ^ m' with hc
  have hc0 : 0 ≤ c := by positivity
  have hdense := wmp_smooth_dense d m p
  obtain ⟨Gs, hGs, hGlim⟩ := mem_closure_iff_seq_limit.1 (hdense H)
  choose u hu hGu using hGs
  set uS : ℕ → 𝓢(Euc d, ℝ) := fun k => (hu k).2.toSchwartzMap (hu k).1 with huS
  have huSe : ∀ k, ⇑(uS k) = u k := fun k => rfl
  obtain ⟨ns, hns, hae⟩ := sa16y_wrep_subseq m p Gs H hGlim
  have hGlim' : Tendsto (fun i => Gs (ns i)) atTop (𝓝 H) := hGlim.comp hns.tendsto_atTop
  have hnorm_ev : ∀ᶠ i in atTop, ‖Gs (ns i)‖ < ‖H‖ + ε := by
    have := hGlim'.norm
    exact this.eventually (gt_mem_nhds (by linarith : ‖H‖ < ‖H‖ + ε))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hnorm_ev
  set G' : ℕ → WmpSpace d m p := fun i => Gs (ns (i + N0)) with hG'
  have hG'lim : Tendsto G' atTop (𝓝 H) := hGlim'.comp (tendsto_add_atTop_nat N0)
  set F : ℕ → Euc d → ℝ := fun i x => a x * u (ns (i + N0)) x with hF
  set F' : Euc d → ℝ := fun x => a x * wrep d m p H x with hF'
  have hFe : ∀ i, F i = ⇑(sa16y_mulS a (uS (ns (i + N0)))) := by
    intro i; rw [sa16y_mulS_apply]; rfl
  have hbd : ∀ i, wNormE m' p (F i) ≤ ENNReal.ofReal c * ENNReal.ofReal (‖H‖ + ε) := by
    intro i
    rw [hFe i]
    refine (sa16y_cm_smooth m m' p hm' a (uS (ns (i + N0))) hB (Gs (ns (i + N0)))
      (hGu (ns (i + N0)))).trans ?_
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hN0 _ (by omega)).le)
  have hlim : ∀ᵐ x ∂(volume : Measure (Euc d)), Tendsto (fun i => F i x) atTop (𝓝 (F' x)) := by
    have hz : ∀ᵐ x ∂(volume : Measure (Euc d)), ∀ k, wrep d m p (Gs k) x = u k x := by
      rw [ae_all_iff]
      intro k
      filter_upwards [hGu k] with x hx
      show ((Gs k : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u k x
      rw [hx]
      simp only [wJet, wZero]
      exact sa16j_pd_zero _ _ x
    filter_upwards [hae, hz] with x hx1 hx2
    have h1 : Tendsto (fun i => wrep d m p (Gs (ns (i + N0))) x) atTop (𝓝 (wrep d m p H x)) :=
      hx1.comp (tendsto_add_atTop_nat N0)
    have h2 : Tendsto (fun i => a x * wrep d m p (Gs (ns (i + N0))) x) atTop (𝓝 (a x * wrep d m p H x)) :=
      h1.const_mul _
    refine h2.congr fun i => ?_
    simp only [hF, hx2]
  have hC : ∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ n ≥ N, ∀ l ≥ N,
      wNormE m' p (fun x => F n x - F l x) ≤ ENNReal.ofReal ε' := by
    intro ε' hε'
    have hev := (Metric.tendsto_atTop.1 hG'lim) (ε' / (2 * (c + 1))) (by positivity)
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn l hl => ?_⟩
    have hfun : (fun x => F n x - F l x) =
        ⇑(sa16y_mulS a (uS (ns (n + N0)) - uS (ns (l + N0)))) := by
      funext x
      rw [sa16y_mulS_apply]
      simp only [hF]
      show a x * u (ns (n + N0)) x - a x * u (ns (l + N0)) x = a x * (u (ns (n + N0)) x - u (ns (l + N0)) x)
      ring
    rw [hfun]
    have hGsub : ((((G' n - G' l : WmpSpace d m p) : WLp d m p)) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume]
        wJet m (⇑(uS (ns (n + N0)) - uS (ns (l + N0)))) := by
      rw [sa16y_wJet_sub]
      have h := Lp.coeFn_sub (G' n : WLp d m p) (G' l : WLp d m p)
      filter_upwards [h, hGu (ns (n + N0)), hGu (ns (l + N0))] with x hx h1 h2
      have : (((G' n - G' l : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x =
        ((G' n : WLp d m p) : Euc d → (WIndex d m → ℝ)) x - ((G' l : WLp d m p) : Euc d → (WIndex d m → ℝ)) x := hx
      rw [this]
      show ((Gs (ns (n + N0)) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x -
        ((Gs (ns (l + N0)) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x = _
      rw [h1, h2]
      rfl
    refine (sa16y_cm_smooth m m' p hm' a _ hB (G' n - G' l) hGsub).trans ?_
    rw [← ENNReal.ofReal_mul hc0]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hN n hn
    have h2 := hN l hl
    rw [dist_eq_norm] at h1 h2
    have hnn : ‖G' n - G' l‖ ≤ ε' / (c + 1) := by
      have := norm_sub_le_norm_sub_add_norm_sub (G' n) H (G' l)
      rw [norm_sub_rev H] at this
      have e : ε' / (2 * (c + 1)) + ε' / (2 * (c + 1)) = ε' / (c + 1) := by field_simp; ring
      linarith
    calc c * ‖G' n - G' l‖ ≤ c * (ε' / (c + 1)) := mul_le_mul_of_nonneg_left hnn hc0
      _ ≤ ε' := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  exact sa16y_wnorm_limit m' p F F' _ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    hbd hlim hC

theorem strong_path_lp_class (d m : ℕ) (p t : ℝ) [Fact (2 ≤ p)]
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (coeff : WholeCoeff d) (φ : Euc d → ℝ)
    (G₀ : WmpSpace d m p) (h₀ : wrep d m p G₀ =ᵐ[volume] φ)
    (G : ℝ → WmpSpace d m p) (hG : ContinuousOn G (Icc (0 : ℝ) t))
    (hsol : IsForwardSolutionRd coeff t (wrep d m p G₀) (fun τ => wrep d m p (G τ))) :
    IsLpSolutionRd m p χ coeff t φ (fun τ => wrep d m p (G τ)) ∧
      ∀ τ ∈ Icc (0 : ℝ) t, wNormE m p (wrep d m p (G τ))=ENNReal.ofReal ‖G τ‖ := by
  have hnorm : ∀ τ ∈ Icc (0 : ℝ) t, wNormE m p (wrep d m p (G τ)) = ENNReal.ofReal ‖G τ‖ :=
    fun τ _ => wNormE_eq_lift_norm d m p (G τ) _ (Eventually.of_forall fun x => rfl)
  refine ⟨⟨⟨hsol.integrable_x, hsol.integrable_σ, ?_⟩, ?_, ?_, ?_⟩, hnorm⟩
  · intro ψ hψ τ hτ
    rw [hsol.eq ψ hψ τ hτ]
    congr 1
    exact integral_congr_ae (h₀.mono fun x hx => by simp only [hx])
  · exact strong_lift_isWmpWeaklyContinuous d m p t _ G hG (fun τ _ => Eventually.of_forall fun x => rfl)
  · obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
    refine ⟨B, fun τ hτ => ?_⟩
    rw [hnorm τ hτ]
    exact ENNReal.ofReal_le_ofReal (hB τ hτ)
  · intro m' hm' z τ₀ hτ₀ ε hε
    have hcs : HasCompactSupport (fun x => χ (x - z)) :=
      hχ.2.1.comp_homeomorph (Homeomorph.subRight z)
    have hsm : ContDiff ℝ ∞ (fun x => χ (x - z)) := hχ.1.comp (contDiff_id.sub contDiff_const)
    set a : 𝓢(Euc d, ℝ) := hcs.toSchwartzMap hsm with ha
    have hae : ⇑a = fun x => χ (x - z) := rfl
    obtain ⟨Bc, hBc0, hBc⟩ := hcs.exists_bound_iteratedFDeriv hsm m'
    set c : ℝ := Bc * ((d : ℝ) + 1) ^ m' with hc
    have hc0 : 0 ≤ c := by positivity
    set η : ℝ := ε / (2 * (c + 1)) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨δ, hδ, hδG⟩ := Metric.continuousOn_iff.1 hG τ₀ hτ₀ η hη0
    refine ⟨δ, hδ, fun τ hτ hτδ => ?_⟩
    have hd : dist (G τ) (G τ₀) < η := hδG τ hτ (by rwa [Real.dist_eq])
    set H : WmpSpace d m p := G τ - G τ₀ with hH
    have hHn : ‖H‖ < η := by rwa [dist_eq_norm] at hd
    have hrep : (fun x => χ (x - z) * (wrep d m p (G τ) x - wrep d m p (G τ₀) x)) =ᵐ[volume]
        fun x => a x * wrep d m p H x := by
      have h := Lp.coeFn_sub (G τ : WLp d m p) (G τ₀ : WLp d m p)
      filter_upwards [h] with x hx
      have : wrep d m p H x = wrep d m p (G τ) x - wrep d m p (G τ₀) x := by
        show (((G τ - G τ₀ : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = _
        have e : (((G τ - G τ₀ : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x =
          ((G τ : WLp d m p) : Euc d → (WIndex d m → ℝ)) x - ((G τ₀ : WLp d m p) : Euc d → (WIndex d m → ℝ)) x := hx
        rw [e]; rfl
      rw [this, hae]
    rw [sa16y_wNormE_congr m' p hrep]
    refine (sa16y_cm m m' p hm'.le a (B := Bc) (fun i hi x => hBc i hi x) H η hη0).trans ?_
    rw [← ENNReal.ofReal_mul hc0]
    refine ENNReal.ofReal_le_ofReal ?_
    calc c * (‖H‖ + η) ≤ c * (η + η) := mul_le_mul_of_nonneg_left (by linarith) hc0
      _ ≤ ε := by
          rw [hη, show c * (ε / (2 * (c + 1)) + ε / (2 * (c + 1))) = ε * (c / (c + 1)) by
            field_simp; ring]
          have : c / (c + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          nlinarith [hε]

end A1

end HRS.Whole.AppendixA.Phase2SA16Assembly
