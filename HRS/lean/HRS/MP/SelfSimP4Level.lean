import HRS.MP.SelfSimP4Spec

/-!
# MP-SSP4LEVEL: `p4_level_bookkeeping` (`ε → 0`, Fatou, `δ → 0`)

Namespace `HRS.MP.SelfSimP4Impl`, helpers `p4lev_`.  Theorem `p4_level_bookkeeping_proof`, tied to
`HRS.MP.SelfSimP4.p4_level_bookkeeping`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4Impl

theorem p4lev_coe_mul {c : ℝ} (hc : 0 ≤ c) {J : ℝ≥0∞} (hJ : J ≠ ⊤) :
    ((ENNReal.ofReal c * J : ℝ≥0∞) : EReal) = ((c * J.toReal : ℝ) : EReal) := by
  have : ENNReal.ofReal c * J = ENNReal.ofReal (c * J.toReal) := by
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hJ]
  rw [this, EReal.coe_ennreal_ofReal, max_eq_left (mul_nonneg hc ENNReal.toReal_nonneg)]

/-- The `ENNReal` liminf passes through the coercion to `EReal`. -/
theorem p4lev_coe_liminf (a : ℕ → ℝ≥0∞) :
    ((liminf a atTop : ℝ≥0∞) : EReal) = liminf (fun n => (a n : EReal)) atTop := by
  have hm : Monotone (fun x : ℝ≥0∞ => (x : EReal)) := fun x y h =>
    EReal.coe_ennreal_le_coe_ennreal_iff.2 h
  exact hm.map_liminf_of_continuousAt (F := atTop) a continuous_coe_ennreal_ereal.continuousAt

/-- Core of the fixed-`(t, δ)` step: `liminf F` and the Fisher term against the limit of the bounds. -/
theorem p4lev_core {Fn : ℕ → ℝ} {Jn : ℕ → ℝ≥0∞} {b : ℕ → ℝ} {h0 c : ℝ} (hc : 0 ≤ c)
    (hJ : ∀ n, Jn n ≠ ⊤) (hb : Tendsto b atTop (𝓝 h0))
    (hle : ∀ n, Fn n + c * (Jn n).toReal ≤ b n) {Ht : EReal}
    (hH : Ht ≤ liminf (fun n => (Fn n : EReal)) atTop) :
    Ht + ((ENNReal.ofReal c * liminf Jn atTop : ℝ≥0∞) : EReal) ≤ (h0 : EReal) := by
  have h1 : ((ENNReal.ofReal c * liminf Jn atTop : ℝ≥0∞) : EReal) ≤
      liminf (fun n => ((ENNReal.ofReal c * Jn n : ℝ≥0∞) : EReal)) atTop := by
    have h := ENNReal.le_liminf_mul (f := atTop) (u := fun _ : ℕ => ENNReal.ofReal c) (v := Jn)
    rw [liminf_const] at h
    rw [← Function.comp_def (fun x : ℝ≥0∞ => (x : EReal)) (fun n => ENNReal.ofReal c * Jn n),
      ← Monotone.map_liminf_of_continuousAt (F := atTop)
        (fun x y h => EReal.coe_ennreal_le_coe_ennreal_iff.2 h) (fun n => ENNReal.ofReal c * Jn n)
        continuous_coe_ennreal_ereal.continuousAt]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 h
  have h2 : Ht + ((ENNReal.ofReal c * liminf Jn atTop : ℝ≥0∞) : EReal) ≤
      liminf (fun n => (Fn n : EReal)) atTop +
        liminf (fun n => ((ENNReal.ofReal c * Jn n : ℝ≥0∞) : EReal)) atTop :=
    add_le_add hH h1
  refine h2.trans ((EReal.le_liminf_add).trans ?_)
  have hb' : Tendsto (fun n => (b n : EReal)) atTop (𝓝 (h0 : EReal)) :=
    (continuous_coe_real_ereal.tendsto h0).comp hb
  rw [← hb'.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  simp only [Pi.add_apply]
  rw [p4lev_coe_mul hc (hJ n), ← EReal.coe_add]
  exact_mod_cast hle n

theorem p4lev_fatou {T : ℝ} {Dv : ℝ → ℝ → ℝ≥0∞} {v : ℕ → ℝ}
    (hDm : ∀ n, AEMeasurable (Dv (v n)) (volume.restrict (Set.Icc (0 : ℝ) T))) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ r in Set.Icc (0 : ℝ) t, liminf (fun n => Dv (v n) r) atTop ≤
      liminf (fun n => ∫⁻ r in Set.Icc (0 : ℝ) t, Dv (v n) r) atTop := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc_right ht.2
  exact lintegral_liminf_le' fun n => (hDm n).mono_measure (Measure.restrict_mono hsub le_rfl)

/-- The final `δ → 0`. -/
theorem p4lev_delta {θ : ℝ} (hθ : 0 < θ) {Ht : EReal} {J : ℝ≥0∞} {h0 : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → δ < 1 → Ht + ((ENNReal.ofReal (θ * (1 - δ)) * J : ℝ≥0∞) : EReal) ≤ (h0 : EReal)) :
    Ht + ((ENNReal.ofReal θ * J : ℝ≥0∞) : EReal) ≤ (h0 : EReal) := by
  have hhalf := h (1 / 2) (by norm_num) (by norm_num)
  have hc0 : (0 : ℝ) < θ * (1 - 1 / 2) := by nlinarith
  induction Ht using EReal.rec with
  | bot => simp
  | top =>
    exfalso
    rw [EReal.top_add_of_ne_bot (EReal.coe_ennreal_nonneg _ |>.trans_lt' (EReal.bot_lt_zero) |>.ne')] at hhalf
    exact absurd hhalf (by simp)
  | coe a =>
    by_cases hJ : J = ⊤
    · exfalso
      subst hJ
      rw [ENNReal.mul_top (by simpa using hc0), EReal.coe_ennreal_top, EReal.coe_add_top] at hhalf
      exact absurd hhalf (by simp)
    · rw [p4lev_coe_mul hθ.le hJ, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h' : ∀ δ : ℝ, 0 < δ → δ < 1 → a + θ * (1 - δ) * J.toReal ≤ h0 := by
        intro δ h1 h2
        have := h δ h1 h2
        rw [p4lev_coe_mul (by nlinarith) hJ, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
        linarith
      have hlim : Tendsto (fun δ : ℝ => a + θ * (1 - δ) * J.toReal) (𝓝[>] 0)
          (𝓝 (a + θ * (1 - 0) * J.toReal)) :=
        (((continuous_const.add ((continuous_const.mul (continuous_const.sub continuous_id)).mul
          continuous_const)).tendsto 0)).mono_left nhdsWithin_le_nhds
      have := le_of_tendsto hlim (by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ using
          h' δ hδ.1 hδ.2)
      simpa using this

theorem p4_level_bookkeeping_proof {θ T C : ℝ} (hθ : 0 < θ)
    {F : ℝ → ℝ → ℝ} {Dv : ℝ → ℝ → ℝ≥0∞} {H : ℝ → EReal} {I : ℝ → ℝ≥0∞} {e : ℝ → ℝ}
    (hDm : ∀ v : ℝ, 0 < v → AEMeasurable (Dv v) (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hmol : ∀ v : ℝ, 0 < v → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ r in Set.Icc (0 : ℝ) t, Dv v r ≠ ⊤ ∧
      F v t + θ * (1 - δ) * (∫⁻ r in Set.Icc (0 : ℝ) t, Dv v r).toReal ≤ F v 0 + t * (C * v / δ))
    (he : Tendsto e (𝓝[>] 0) (𝓝 0))
    (hinit : ∀ v : ℝ, 0 < v → ((F v 0 : ℝ) : EReal) ≤ H 0 + ((e v : ℝ) : EReal))
    (hlscH : ∀ t ∈ Set.Icc (0 : ℝ) T,
      H t ≤ liminf (fun n : ℕ => ((F (1 / ((n : ℝ) + 1)) t : ℝ) : EReal)) atTop)
    (hlscI : ∀ r ∈ Set.Icc (0 : ℝ) T, I r ≤ liminf (fun n : ℕ => Dv (1 / ((n : ℝ) + 1)) r) atTop) :
    ∃ D : ℝ → ℝ≥0∞, AEMeasurable D (volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) T, I r ≤ D r) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        H t + ((ENNReal.ofReal θ * ∫⁻ r in Set.Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal) ≤ H 0 := by
  set v : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hvdef
  have hv : ∀ n, 0 < v n := fun n => by positivity
  have hv0 : Tendsto v atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hv0' : Tendsto v atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hv0, Eventually.of_forall hv⟩
  have hev : Tendsto (fun n => e (v n)) atTop (𝓝 0) := he.comp hv0'
  refine ⟨fun r => liminf (fun n => Dv (v n) r) atTop,
    AEMeasurable.liminf fun n => hDm (v n) (hv n), hlscI, ?_⟩
  intro t ht
  -- `H 0` is a real number or `⊤`
  have hH0 : H 0 ≠ ⊥ := by
    intro h
    have := hinit 1 one_pos
    rw [h, EReal.bot_add] at this
    exact absurd (le_bot_iff.1 this) (EReal.coe_ne_bot _)
  have hH0t : H 0 ≠ ⊤ ∨ H 0 = ⊤ := by tauto
  rcases hH0t with hH0t | hH0t
  swap
  · rw [hH0t]; exact le_top
  obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, H 0 = (r0 : EReal) := ⟨(H 0).toReal, (EReal.coe_toReal hH0t hH0).symm⟩
  rw [hr0]
  refine p4lev_delta hθ fun δ hδ0 hδ1 => ?_
  have hc : 0 ≤ θ * (1 - δ) := mul_nonneg hθ.le (by linarith)
  have hF := p4lev_fatou (Dv := Dv) (v := v) (fun n => hDm (v n) (hv n)) ht
  have hmono : ((ENNReal.ofReal (θ * (1 - δ)) * ∫⁻ r in Set.Icc (0 : ℝ) t, liminf (fun n => Dv (v n) r) atTop : ℝ≥0∞) : EReal) ≤
      ((ENNReal.ofReal (θ * (1 - δ)) * liminf (fun n => ∫⁻ r in Set.Icc (0 : ℝ) t, Dv (v n) r) atTop : ℝ≥0∞) : EReal) :=
    EReal.coe_ennreal_le_coe_ennreal_iff.2 (mul_le_mul_right hF _)
  refine (add_le_add_right hmono _).trans ?_
  refine p4lev_core (Fn := fun n => F (v n) t) (b := fun n => r0 + e (v n) + t * (C * v n / δ)) hc
    (fun n => (hmol (v n) (hv n) δ hδ0 hδ1 t ht).1) ?_ ?_ (hlscH t ht)
  · have h1 : Tendsto (fun n => t * (C * v n / δ)) atTop (𝓝 (t * (C * 0 / δ))) :=
      (((tendsto_const_nhds.mul hv0).div_const δ).const_mul t)
    have := (tendsto_const_nhds (x := r0)).add hev |>.add h1
    simpa using this
  · intro n
    have h1 := (hmol (v n) (hv n) δ hδ0 hδ1 t ht).2
    have h2 := hinit (v n) (hv n)
    rw [hr0, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    linarith

example := (@p4_level_bookkeeping_proof : type_of% @HRS.MP.SelfSimP4.p4_level_bookkeeping)

end HRS.MP.SelfSimP4Impl
