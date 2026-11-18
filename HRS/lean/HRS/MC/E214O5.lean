import HRS.MC.E214O4
import HRS.MC.E214G6

/-!
# Packet E214O, part 5: the covariance-tensor comparison hypothesis `WinJCompare` and measurability helpers
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214O

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

/-- **The covariance-tensor comparison `winJ_compare` of `E214Plan`, as a `Prop`** (body VERBATIM the conclusion of
`HRS.MC.E214Plan.winJ_compare`; the only unproved analytic input of the corollary). -/
def WinJCompare {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE) (T : ℝ)
    (_hT : 0 < T) : Prop :=
  ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (zr : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 zr) →
      IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖zr v‖) (Set.Ioc 0 (a + T)) →
      ‖winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) -
          winJ (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T))‖ ≤
        C * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖zr v‖

/-- A path continuous on `[0,∞)` has measurable `nearCoef 0`. -/
theorem o_nearCoef_measurable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {b : ℝ → E} (hb : ContinuousOn b (Set.Ici 0)) : Measurable (nearCoef 0 b) := by
  have h := hb.measurable_piecewise (continuousOn_const (c := (0 : E)) (s := (Set.Ici (0 : ℝ))ᶜ))
    measurableSet_Ici
  convert h using 1
  funext v
  by_cases hv : 0 ≤ v
  · simp [nearCoef, Set.piecewise, hv]
  · simp [nearCoef, Set.piecewise, hv]

/-- An `ℝ`-valued process measurable in `ω` for each `t` and a.s. continuous on `[0,∞)` is a.e.-jointly measurable
on `Ω × (0,n]` (for the product with Lebesgue measure). -/
theorem o_aemeasurable_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] (f : ℝ → Ω → ℝ)
    (hm : ∀ t, Measurable (f t)) (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => f t ω) (Set.Ici 0)) (n : ℝ) :
    AEMeasurable (fun x : Ω × ℝ => f x.2 x.1) (P.prod (volume.restrict (Set.Ioc 0 n))) := by
  classical
  have hnull : P {ω | ¬ ContinuousOn (fun t => f t ω) (Set.Ici 0)} = 0 := by
    simpa [ae_iff] using hc
  obtain ⟨t, hst, hts, htn⟩ := exists_measurable_superset_of_null hnull
  set G : Set Ω := tᶜ with hG
  have hGm : MeasurableSet G := hts.compl
  have hGc : ∀ ω ∈ G, ContinuousOn (fun s => f s ω) (Set.Ici 0) := by
    intro ω hω
    by_contra hcon
    exact hω (hst hcon)
  set u : ℝ → Ω → ℝ := fun s ω => G.piecewise (f (max s 0)) (fun _ => 0) ω with hu
  have hu_meas : ∀ s, Measurable (u s) := fun s => Measurable.piecewise hGm (hm _) measurable_const
  have hu_cont : ∀ ω, Continuous fun s => u s ω := by
    intro ω
    by_cases hω : ω ∈ G
    · have : (fun s => u s ω) = (fun s => f s ω) ∘ (fun s : ℝ => max s 0) := by
        funext s; simp [hu, Set.piecewise, hω]
      rw [this]
      exact (hGc ω hω).comp_continuous (continuous_id.max continuous_const) (fun s => le_max_right s 0)
    · have : (fun s => u s ω) = fun _ => 0 := by
        funext s; simp [hu, Set.piecewise, hω]
      rw [this]; exact continuous_const
  have hmeas : Measurable (Function.uncurry u) := measurable_uncurry_of_continuous_of_measurable hu_cont hu_meas
  have hmeas' : Measurable fun x : Ω × ℝ => u x.2 x.1 := hmeas.comp measurable_swap
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) n)) := ⟨by simp⟩
  refine hmeas'.aemeasurable.congr ?_
  have h1 : ∀ᵐ x ∂(P.prod (volume.restrict (Set.Ioc 0 n))), x.1 ∈ G :=
    Measure.quasiMeasurePreserving_fst.ae (by simpa [ae_iff, hG] using htn)
  have h2 : ∀ᵐ x ∂(P.prod (volume.restrict (Set.Ioc 0 n))), x.2 ∈ Set.Ioc 0 n :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [h1, h2] with x hx1 hx2
  simp [hu, Set.piecewise, hx1, max_eq_left hx2.1.le]

theorem o_norm_add_le' {G : Type*} [NormedAddCommGroup G] (x y : G) {a b : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖x + y‖ ≤ a + b := (norm_add_le x y).trans (add_le_add hx hy)

/-- Pathwise bound for the covariance-tensor difference (linearity, `winJ_L1`, comparison, block decomposition);
the coefficients are continuous on `[0,∞)` (hence bounded on compacts). -/
theorem o_J_det {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)
    (T : ℝ) (hT : 0 < T) {C₁ c₁ C₂ c₂ κ : ℝ} (hC₂ : 0 ≤ C₂) (hc₂ : 0 ≤ c₂) (hκ : 0 ≤ κ)
    (hL1 : ∀ (a : ℝ) (ha : 0 ≤ a) (zr : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 zr) →
      IntegrableOn (fun v => Real.exp (-c₁ * (a - v)) * ‖zr v‖) (Set.Ioc 0 (a + T)) →
      (∃ J, IsJValue (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T)
          (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) J) ∧
      ‖winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T))‖ ≤
        C₁ * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c₁ * (a - v)) * ‖zr v‖)
    (hcmp : ∀ (a : ℝ) (ha : 0 ≤ a) (zr : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 zr) →
      IntegrableOn (fun v => Real.exp (-c₂ * (a - v)) * ‖zr v‖) (Set.Ioc 0 (a + T)) →
      ‖winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) -
          winJ (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T))‖ ≤
        C₂ * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c₂ * (a - v)) * Real.exp (-κ * v) * ‖zr v‖)
    (a : ℝ) (ha : 0 ≤ a) (b1 b2 : ℝ → NegSobolev d (rLvl d))
    (hb1 : ContinuousOn b1 (Set.Ici 0)) (hb2 : ContinuousOn b2 (Set.Ici 0)) (N : ℕ) (hN : a + T ≤ N)
    (Y : ℕ → ℝ) (hY : ∀ k < N, ∀ v ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1), ‖b2 v‖ ≤ Y k) :
    ‖winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (b1 v)) (Set.Ioc 0 (a + T)) -
        winJ (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (b2 v)) (Set.Ioc 0 (a + T))‖ ≤
      C₁ * (∫ v in Set.Ioc 0 (a + T), Real.exp (-c₁ * (a - v)) * ‖b1 v - b2 v‖) +
        C₂ * (Real.exp (c₂ * T) * Real.exp (-(min c₂ κ) * a)) * ∑ k ∈ Finset.range N, Y k := by
  have hH : 0 ≤ a + T := by linarith
  have hsub : Set.Ioc (0 : ℝ) (a + T) ⊆ Set.Icc 0 (a + T) := Set.Ioc_subset_Icc_self
  set δ : ℝ → NegSobolev d (rLvl d) := fun v => b1 v - b2 v with hδ
  have hδc : ContinuousOn δ (Set.Ici 0) := hb1.sub hb2
  have hδm : Measurable (nearCoef 0 δ) := o_nearCoef_measurable hδc
  have hb2m : Measurable (nearCoef 0 b2) := o_nearCoef_measurable hb2
  have hcI : IsCompact (Set.Icc (0 : ℝ) (a + T)) := isCompact_Icc
  obtain ⟨Mδ, hMδ⟩ := hcI.exists_bound_of_continuousOn (hδc.mono (fun v hv => hv.1))
  obtain ⟨M₂, hM₂⟩ := hcI.exists_bound_of_continuousOn (hb2.mono (fun v hv => hv.1))
  have hadd := HRS.MC.E213U2.winJ_add_proof hE T hT a ha δ b2 hδm hb2m Mδ M₂ hMδ hM₂ 0 (a + T) le_rfl hH le_rfl
  have hb1' : (fun v => NegSobolev.embed m (δ v + b2 v)) = fun v => NegSobolev.embed m (b1 v) := by
    funext v; simp [hδ]
  rw [hb1'] at hadd
  have key : winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (b1 v)) (Set.Ioc 0 (a + T)) -
        winJ (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (b2 v)) (Set.Ioc 0 (a + T)) =
      winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (δ v)) (Set.Ioc 0 (a + T)) +
        (winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (b2 v)) (Set.Ioc 0 (a + T)) -
          winJ (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (b2 v)) (Set.Ioc 0 (a + T))) := by
    rw [hadd]; abel
  have wint : ∀ (c : ℝ) (φ : ℝ → NegSobolev d (rLvl d)), ContinuousOn φ (Set.Ici 0) →
      IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖φ v‖) (Set.Ioc 0 (a + T)) := by
    intro c φ hφ
    have hc : ContinuousOn (fun v => Real.exp (-c * (a - v)) * ‖φ v‖) (Set.Icc 0 (a + T)) :=
      (o_cont_weight c a).continuousOn.mul ((hφ.mono (fun v hv => hv.1)).norm)
    exact (hc.integrableOn_Icc).mono_set hsub
  have hφi : IntegrableOn (fun v => ‖b2 v‖) (Set.Icc 0 (N : ℝ)) :=
    ((hb2.mono (fun v hv => hv.1)).norm).integrableOn_Icc
  have hblk : ∫ v in Set.Ioc 0 (a + T), Real.exp (-c₂ * (a - v)) * Real.exp (-κ * v) * ‖b2 v‖ ≤
      Real.exp (c₂ * T) * Real.exp (-(min c₂ κ) * a) * ∑ k ∈ Finset.range N, Y k := by
    refine o_block_weighted hc₂ hκ ha hT.le (fun v => norm_nonneg _) hN hφi (fun k hk => ?_)
    have hk1 : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    have hkk : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hii : IntervalIntegrable (fun v => ‖b2 v‖) volume (k : ℝ) ((k : ℝ) + 1) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hkk]
      exact hφi.mono_set (Set.Icc_subset_Icc (Nat.cast_nonneg k) hk1)
    calc ∫ x in (k : ℝ)..((k : ℝ) + 1), ‖b2 x‖ ≤ ∫ x in (k : ℝ)..((k : ℝ) + 1), Y k :=
          intervalIntegral.integral_mono_on hkk hii intervalIntegrable_const (hY k hk)
      _ = Y k := by simp
  rw [key]
  have h1 := (hL1 a ha δ hδm (wint c₁ δ hδc)).2
  have h2 := hcmp a ha b2 hb2m (wint c₂ b2 hb2)
  have h3 : C₂ * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c₂ * (a - v)) * Real.exp (-κ * v) * ‖b2 v‖ ≤
      C₂ * (Real.exp (c₂ * T) * Real.exp (-(min c₂ κ) * a)) * ∑ k ∈ Finset.range N, Y k := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hblk hC₂
  exact o_norm_add_le' (G := TensorDual (PathSpace d m T) 2) _ _ h1 (h2.trans h3)

end HRS.MC.E214O

end
