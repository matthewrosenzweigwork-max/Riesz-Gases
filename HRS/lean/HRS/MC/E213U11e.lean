import HRS.MC.E213U11d
import HRS.MC.E213U11c

/-!
# Packet e213u11, file e: the linear map `Λ` behind `J_a` (measurability and membership)

`w ↦ 𝒥_{a}(embed ∘ cp w; (0,a+T])` is an additive map `C([0,L];E_r) → 𝒳_{m,T}^{⊗2 *}` bounded by `C‖w‖`,
hence a continuous linear map; `J_a = Λ (η^{0+·})` a.s.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U11

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-- The path `w` extended to all of `ℝ` by clamping the time to `[0,L]`. -/
def u11_cp {r L : ℝ} (hL : 0 ≤ L) (w : PathSpace d r L) (v : ℝ) : NegSobolev d r :=
  PathSpace.at' w (Set.projIcc 0 L hL v)

theorem u11_cp_continuous {r L : ℝ} (hL : 0 ≤ L) (w : PathSpace d r L) : Continuous (u11_cp hL w) :=
  (ContinuousMap.continuous (show C(Set.Icc (0 : ℝ) L, NegSobolev d r) from w)).comp continuous_projIcc

theorem u11_cp_norm_le {r L : ℝ} (hL : 0 ≤ L) (w : PathSpace d r L) (v : ℝ) : ‖u11_cp hL w v‖ ≤ ‖w‖ :=
  HRS.MC.Sec7.S7FCH4.S7FCH4_norm_at_le w _

theorem u11_cp_add {r L : ℝ} (hL : 0 ≤ L) (w w' : PathSpace d r L) (v : ℝ) :
    u11_cp hL (w + w') v = u11_cp hL w v + u11_cp hL w' v := rfl

theorem u11_cp_of_mem {r L : ℝ} (hL : 0 ≤ L) (w : PathSpace d r L) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) L) :
    u11_cp hL w v = PathSpace.at' w ⟨v, hv⟩ := by
  unfold u11_cp
  rw [Set.projIcc_of_mem _ hv]

theorem u11_measurable_nearCoef_of_continuous {r : ℝ} {z : ℝ → NegSobolev d r} (hz : Continuous z) :
    Measurable (nearCoef 0 z) := by
  unfold nearCoef
  exact Measurable.ite measurableSet_Ici hz.measurable measurable_const

section Lambda

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u11_cp_bounds {r L : ℝ} (hL : 0 ≤ L) (w : PathSpace d r L) (A B : ℝ) :
    (∀ v ∈ Set.Icc A B, ‖u11_cp hL w v‖ ≤ ‖w‖) := fun v _ => u11_cp_norm_le hL w v

theorem u11_winJ_cp_mem (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {L : ℝ}
    (hL0 : 0 ≤ L) (w : PathSpace d (rLvl d) L) :
    winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (u11_cp hL0 w v)) (Set.Ioc 0 (a + T)) ∈
      projTensor (PathSpace d m T) 2 := by
  obtain ⟨K₁, K₂, c, -, -, -, h⟩ := u11_winJ_bound (S := S) (β₀ := β₀) hE T hT
  obtain ⟨⟨J, hJ⟩, -⟩ := h a ha (u11_cp hL0 w) (u11_measurable_nearCoef_of_continuous (u11_cp_continuous hL0 w))
    ‖w‖ ‖w‖ (u11_cp_bounds hL0 w _ _) (u11_cp_bounds hL0 w _ _)
  unfold winJ
  rw [HRS.MC.E213U2.e213u2_jTensor_eq _ _ _ _ _ _ hJ]
  exact HRS.MC.E213U2.e213u2_tensorPow'_mem 2 _ hJ.1

theorem u11_exists_Lambda (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : a + T ≤ L) :
    ∃ Λ : PathSpace d (rLvl d) L →L[ℝ] TensorDual (PathSpace d m T) 2,
      ∀ w, Λ w = winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (u11_cp hL0 w v))
        (Set.Ioc 0 (a + T)) := by
  classical
  obtain ⟨K₁, K₂, c, hK₁, hK₂, hc, hbd⟩ := u11_winJ_bound (S := S) (β₀ := β₀) hE T hT
  set H : ℝ := a + T with hH
  have hHpos : 0 < H := by rw [hH]; linarith
  have hadd : ∀ w w' : PathSpace d (rLvl d) L,
      winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (u11_cp hL0 (w + w') v)) (Set.Ioc 0 H) =
        winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (u11_cp hL0 w v)) (Set.Ioc 0 H) +
        winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (u11_cp hL0 w' v)) (Set.Ioc 0 H) := by
    intro w w'
    exact HRS.MC.E213U2.winJ_add_proof hE T hT a ha (u11_cp hL0 w) (u11_cp hL0 w')
      (u11_measurable_nearCoef_of_continuous (u11_cp_continuous hL0 w))
      (u11_measurable_nearCoef_of_continuous (u11_cp_continuous hL0 w')) ‖w‖ ‖w'‖
      (u11_cp_bounds hL0 w _ _) (u11_cp_bounds hL0 w' _ _) 0 H le_rfl hHpos.le le_rfl
  let f : PathSpace d (rLvl d) L →+ TensorDual (PathSpace d m T) 2 :=
    AddMonoidHom.mk' (fun w => winJ (regime S β₀ hE) m T a ha
      (fun v => NegSobolev.embed m (u11_cp hL0 w v)) (Set.Ioc 0 H)) hadd
  have hbound : ∀ w, ‖f w‖ ≤ (K₁ + K₂ * (Real.exp (c * T) * H)) * ‖w‖ := by
    intro w
    obtain ⟨-, hn⟩ := hbd a ha (u11_cp hL0 w) (u11_measurable_nearCoef_of_continuous (u11_cp_continuous hL0 w))
      ‖w‖ ‖w‖ (u11_cp_bounds hL0 w _ _) (u11_cp_bounds hL0 w _ _)
    refine hn.trans ?_
    have hs : (volume : Measure ℝ) (Set.Ioc 0 H ∩ Set.Iio (max (a - 1) 0)) < ⊤ :=
      lt_of_le_of_lt (measure_mono Set.inter_subset_left) (by simp)
    have hI := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
      (f := fun v => Real.exp (-c * (a - v)) * ‖u11_cp hL0 w v‖) (C := Real.exp (c * T) * ‖w‖) hs (fun v hv => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
        refine mul_le_mul ?_ (u11_cp_norm_le hL0 w v) (norm_nonneg _) (Real.exp_pos _).le
        exact Real.exp_le_exp.2 (by nlinarith [hv.1.2]))
    have hvol : (volume : Measure ℝ).real (Set.Ioc 0 H ∩ Set.Iio (max (a - 1) 0)) ≤ H := by
      refine (measureReal_mono Set.inter_subset_left (by simp)).trans ?_
      rw [Real.volume_real_Ioc_of_le hHpos.le]; simp
    have h1 : ∫ v in Set.Ioc 0 H ∩ Set.Iio (max (a - 1) 0), Real.exp (-c * (a - v)) * ‖u11_cp hL0 w v‖ ≤
        Real.exp (c * T) * ‖w‖ * H :=
      (Real.le_norm_self _).trans (hI.trans (mul_le_mul_of_nonneg_left hvol
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))))
    nlinarith [mul_le_mul_of_nonneg_left h1 hK₂.le]
  have hcont : Continuous f := AddMonoidHomClass.continuous_of_bound f _ hbound
  let Lm : PathSpace d (rLvl d) L →L[ℝ] TensorDual (PathSpace d m T) 2 :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c x => map_real_smul f hcont c x
      cont := hcont }
  exact ⟨Lm, fun w => rfl⟩

end Lambda

section JwinAE

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u11_eta_cont (L : ℝ) : ∀ᵐ ω ∂gd.P₀, ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 L) := by
  obtain ⟨Y₀, -, hsol⟩ := gd.limit
  exact (hsol L).cont

theorem u11_procWin_at {r : ℝ} {Ω : Type} (η : ℝ → Ω → NegSobolev d r) (R s : ℝ) (ω : Ω)
    (hc : ContinuousOn (fun t => η t ω) (Set.Icc s (s + R))) (hs : 0 ≤ R) (t : Set.Icc (0 : ℝ) R) :
    PathSpace.at' (procWin r R s η ω) t = η (s + t) ω := by
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) R => η (s + (t : ℝ)) ω := by
    have h1 : Continuous fun t : Set.Icc (0 : ℝ) R => s + (t : ℝ) := continuous_const.add continuous_subtype_val
    exact hc.comp_continuous h1 (fun t => ⟨by linarith [t.2.1], by linarith [t.2.2]⟩)
  have h : procWin r R s η ω = (show PathSpace d r R from
      (⟨fun t => η (s + (t : ℝ)) ω, hcont⟩ : C(Set.Icc (0 : ℝ) R, NegSobolev d r))) := by
    unfold procWin HRS.toPath
    exact dif_pos hcont
  rw [h]
  rfl

theorem u11_procWin_norm_ge {r : ℝ} {Ω : Type} (η : ℝ → Ω → NegSobolev d r) (R s : ℝ) (ω : Ω)
    (hc : ContinuousOn (fun t => η t ω) (Set.Icc s (s + R))) (hs : 0 ≤ R) {v : ℝ}
    (hv : v ∈ Set.Icc s (s + R)) : ‖η v ω‖ ≤ ‖procWin r R s η ω‖ := by
  have ht : v - s ∈ Set.Icc (0 : ℝ) R := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have h := u11_procWin_at η R s ω hc hs ⟨v - s, ht⟩
  have h2 := HRS.MC.Sec7.S7FCH4.S7FCH4_norm_at_le (procWin r R s η ω) ⟨v - s, ht⟩
  rw [h] at h2
  simpa using h2

theorem u11_Jwin_eq (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Λ : PathSpace d (rLvl d) (a + T + 1) →L[ℝ] TensorDual (PathSpace d m T) 2)
    (hΛ : ∀ w, Λ w = winJ (regime S β₀ hE) m T a ha
      (fun v => NegSobolev.embed m (u11_cp (show (0 : ℝ) ≤ a + T + 1 by linarith) w v)) (Set.Ioc 0 (a + T))) :
    ∀ᵐ ω ∂gd.P₀, gd.Jwin T a ω = Λ (procWin (rLvl d) (a + T + 1) 0 gd.η ω) := by
  filter_upwards [u11_eta_cont gd (a + T + 1)] with ω hc
  have hc' : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 (0 + (a + T + 1))) := by simpa using hc
  unfold GaussData.Jwin
  rw [dif_pos ha, hΛ]
  unfold winJ
  congr 1
  refine u11_jTensor_congr _ m (a + T) measurableSet_Ioc (fun u hu hu0 => ?_)
  have hu1 : u ∈ Set.Icc (0 : ℝ) (a + T + 1) := ⟨hu0, by linarith [hu.2]⟩
  rw [u11_cp_of_mem _ _ hu1, u11_procWin_at gd.η (a + T + 1) 0 ω hc' (by linarith)]
  simp

theorem u11_Jwin_aesm_mem (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    AEStronglyMeasurable (gd.Jwin T a) gd.P₀ ∧
      ∀ᵐ ω ∂gd.P₀, gd.Jwin T a ω ∈ projTensor (PathSpace d m T) 2 := by
  have hL0 : (0 : ℝ) ≤ a + T + 1 := by linarith
  obtain ⟨Λ, hΛ⟩ := u11_exists_Lambda (S := S) (β₀ := β₀) hE T hT a ha hL0 (by linarith)
  have heq := u11_Jwin_eq gd T hT a ha Λ hΛ
  refine ⟨?_, ?_⟩
  · obtain ⟨C, -, hC⟩ := u11_eta_moment gd (a + T + 1) (by linarith) 1 le_rfl
    have hm := (hC 0 le_rfl).1
    exact (Λ.continuous.comp_aestronglyMeasurable hm.aestronglyMeasurable).congr (heq.mono fun ω h => h.symm)
  · filter_upwards [heq] with ω h
    rw [h, hΛ]
    exact u11_winJ_cp_mem hE T hT a ha hL0 _

end JwinAE

end HRS.MC.E213U11

end
