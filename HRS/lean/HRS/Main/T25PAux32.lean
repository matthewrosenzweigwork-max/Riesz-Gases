import HRS.Main.T25PAux31

/-!
# T25P, part 32: the window law of the re-based solution
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45 HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_rebase_law {m : ℝ} {T a : ℝ} (hT : 0 < T) (ha : 0 ≤ a)
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hplain : IsPlainEvolution Vev (a + T)) {Cr : ℝ} (hCr : 0 ≤ Cr)
    (hb : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Vev t 0‖ ≤ Cr)
    {Ω' : Type} [mΩ' : MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y₀ : Ω' → NegSobolev d m) (hY₀ : Measurable Y₀) (Y : ℝ → Ω' → NegSobolev d m)
    (hYm : ∀ t, Measurable (Y t)) (hYc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) :
    ∃ γ : Measure (PathSp T (NegSobolev d m)), IsProbabilityMeasure γ ∧
      ∀ (κ : Measure (NegSobolev d m)) [IsProbabilityMeasure κ],
        law (P'.prod κ) (Uniform.windowPath a T
            (fun t (w : Ω' × NegSobolev d m) => Y t w.1 - Vev t 0 (Y₀ w.1) + Vev t 0 w.2)) =
          (κ.prod γ).map (fun q : NegSobolev d m × PathSp T (NegSobolev d m) =>
            t25p_L ha Vev hplain.2.2 hCr hb q.1 + q.2) := by
  set Zp : ℝ → Ω' → NegSobolev d m := fun t ω => Y t ω - Vev t 0 (Y₀ ω) with hZp
  have hZm : ∀ t, Measurable (Zp t) := fun t =>
    (hYm t).sub ((Vev t 0).continuous.measurable.comp hY₀)
  have hZc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Zp t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hYc] with ω hω
    exact hω.sub (HRS.Uniform.Comp28.continuousOn_V_zero Vev hplain.2.2 (Y₀ ω))
  have hwin : AEMeasurable (Uniform.windowPath a T Zp) P' :=
    HRS.Uniform.Comp28.aem_wp_a P' ha hT.le Zp (fun t _ => hZm t) hZc
  set winZ : Ω' → PathSp T (NegSobolev d m) := hwin.mk _ with hwinZ
  have hmk : Measurable winZ := hwin.measurable_mk
  have hae : Uniform.windowPath a T Zp =ᵐ[P'] winZ := hwin.ae_eq_mk
  refine ⟨P'.map winZ, inferInstance, fun κ _ => ?_⟩
  have key : (fun w : Ω' × NegSobolev d m => Uniform.windowPath a T
      (fun t (w : Ω' × NegSobolev d m) => Y t w.1 - Vev t 0 (Y₀ w.1) + Vev t 0 w.2) w) =ᵐ[P'.prod κ]
      fun w => t25p_L ha Vev hplain.2.2 hCr hb w.2 + winZ w.1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hZc,
      Measure.quasiMeasurePreserving_fst.ae hae] with w h1 h2
    have e : (fun t (w : Ω' × NegSobolev d m) => Y t w.1 - Vev t 0 (Y₀ w.1) + Vev t 0 w.2) =
        fun t w => Vev t 0 w.2 + Zp t w.1 := by
      funext t w; simp only [hZp]; abel
    have h3 := t25p_win_add ha Vev hplain.2.2 hCr hb hT.le w.2
      (fun t (w' : Ω' × NegSobolev d m) => Zp t w'.1) (ω := w) h1
    rw [e]
    refine (show Uniform.windowPath a T (fun t (w' : Ω' × NegSobolev d m) => Vev t 0 w'.2 + Zp t w'.1) w =
      Uniform.windowPath a T (fun t (w' : Ω' × NegSobolev d m) => Vev t 0 w.2 + Zp t w'.1) w from rfl).trans
      (h3.trans ?_)
    congr 1
  unfold law
  rw [Measure.map_congr key]
  have hΦ : Measurable (fun q : NegSobolev d m × PathSp T (NegSobolev d m) =>
      t25p_L ha Vev hplain.2.2 hCr hb q.1 + q.2) :=
    ((t25p_L ha Vev hplain.2.2 hCr hb).continuous.measurable.comp measurable_fst).add measurable_snd
  have hpair : Measurable (fun w : Ω' × NegSobolev d m => (w.2, winZ w.1)) :=
    measurable_snd.prodMk (hmk.comp measurable_fst)
  have e2 : (fun w : Ω' × NegSobolev d m => t25p_L ha Vev hplain.2.2 hCr hb w.2 + winZ w.1) =
      (fun q : NegSobolev d m × PathSp T (NegSobolev d m) =>
        t25p_L ha Vev hplain.2.2 hCr hb q.1 + q.2) ∘ (fun w => (w.2, winZ w.1)) := rfl
  rw [e2, ← Measure.map_map hΦ hpair]
  congr 1
  have e3 : (fun w : Ω' × NegSobolev d m => (w.2, winZ w.1)) =
      Prod.map (id : NegSobolev d m → NegSobolev d m) winZ ∘ Prod.swap := rfl
  rw [e3, ← Measure.map_map (measurable_id.prodMap hmk) measurable_swap, Measure.prod_swap,
    ← Measure.map_prod_map κ P' measurable_id hmk, Measure.map_id]

end HRS.T25P
