import HRS.MC.CepP3

/-!
# Packet P4, Aux1: the space-time identity `(★)` and the measurable modification of the density
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP4

open HRS HRS.MC.CepP3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

/-- The measurable modification of `g p = f p.1 (mkC p.2)`, equal to `g` on `(0,T) × liftedFree` and `0` elsewhere. -/
def ghat (f : ℝ → Config d N → ℝ) (T : ℝ) (p : ℝ × (Fin N → Euc d)) : ℝ :=
  (Ioo 0 T ×ˢ liftedFree d N).indicator (fun p => f p.1 (mkC p.2)) p

/-- The corresponding measurable function on `ℝ × Config d N`. -/
def fhat (f : ℝ → Config d N → ℝ) (T : ℝ) (q : ℝ × Config d N) : ℝ := ghat f T (q.1, repC q.2)

theorem measurable_ghat {f : ℝ → Config d N → ℝ} {T : ℝ}
    (hfs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N})) :
    Measurable (ghat f T) := by
  have hO : IsOpen (Ioo 0 T ×ˢ liftedFree d N : Set (ℝ × (Fin N → Euc d))) :=
    isOpen_Ioo.prod (isOpen_liftedFree d N)
  classical
  have hc : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => f p.1 (mkC p.2))
      (Ioo 0 T ×ˢ liftedFree d N) := hfs.continuousOn
  have := hc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
    hO.measurableSet
  convert this using 1
  funext x
  by_cases hx : x ∈ (Ioo 0 T ×ˢ liftedFree d N : Set (ℝ × (Fin N → Euc d))) <;> simp [ghat, hx]

theorem measurable_fhat {f : ℝ → Config d N → ℝ} {T : ℝ}
    (hfs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N})) :
    Measurable (fhat f T) :=
  (measurable_ghat hfs).comp (measurable_fst.prodMk (measurable_repC.comp measurable_snd))

theorem measurable_fhat' {f : ℝ → Config d N → ℝ} {T : ℝ} (hg : Measurable (ghat f T)) :
    Measurable (fhat f T) :=
  hg.comp (measurable_fst.prodMk (measurable_repC.comp measurable_snd))

theorem fhat_eq {f : ℝ → Config d N → ℝ} {T : ℝ} {t : ℝ} (ht : t ∈ Ioo 0 T) {x : Config d N}
    (hx : x ∉ collisionSet d N) : fhat f T (t, x) = f t x := by
  have h : (t, repC x) ∈ (Ioo 0 T ×ˢ liftedFree d N : Set (ℝ × (Fin N → Euc d))) := by
    refine ⟨ht, ?_⟩
    have e : (fun i => Torus.mk (repC x i)) = x := mk_repC x
    show (fun i => Torus.mk (repC x i)) ∉ collisionSet d N
    rw [e]; exact hx
  unfold fhat ghat
  rw [Set.indicator_of_mem h]
  show f t (mkC (repC x)) = f t x
  rw [show mkC (repC x) = x from mk_repC x]

theorem lintegral_rhoM [IsProbabilityMeasure P] (T : ℝ) {X : ℝ≥0 → Ω → Config d N}
    (hm : Measurable (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2))
    (hX : ∀ t : ℝ, Measurable (X (Real.toNNReal t)))
    {G : ℝ × Config d N → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ q, G q ∂(rhoM P T X) = ∫⁻ t in Ioo 0 T, ∫⁻ x, G (t, x) ∂(selectedLaw P X t) := by
  unfold rhoM
  rw [lintegral_map hG (measurable_rhoMap hm),
    lintegral_prod (fun q : ℝ × Ω => G (q.1, X (Real.toNNReal q.1) q.2))
      (hG.comp (measurable_rhoMap hm)).aemeasurable]
  refine lintegral_congr fun t => ?_
  unfold selectedLaw law
  exact (lintegral_map (hG.comp measurable_prodMk_left) (hX t)).symm

end HRS.MC.CepP4
