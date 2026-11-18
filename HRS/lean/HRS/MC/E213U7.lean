import HRS.MC.E213U1a
import HRS.MC.E213U1b
import HRS.MC.E213U2
import HRS.MC.S7PIG2
import HRS.MC.S7PIS1Drift
import HRS.MC.S7PIS1Path2
import HRS.Sections.Q17Aux2

/-!
# Packet e213u7: the deterministic near/far splitting `rs_split_drift`, `rs_split_J`

Core lemmas (existence of the Riemann--Stieltjes integrals of the near and far parts, additivity) with the regularity of
the window heat function as an explicit hypothesis `e213u7_Reg` (the conclusion of `Ucan_regular`).
Namespace `HRS.MC.E213U7`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U7

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U1 HRS.MC.E213U2

variable {d : ℕ}

/-! ### Riemann--Stieltjes calculus (copies of the short proofs of the Plan) -/

theorem e213u7_isRS_add {T : ℝ} {S₁ S₂ : ℝ → ℝ → ℝ → ℝ} {I₁ I₂ : ℝ} (h₁ : IsRS T S₁ I₁) (h₂ : IsRS T S₂ I₂) :
    IsRS T (fun τ u u' => S₁ τ u u' + S₂ τ u u') (I₁ + I₂) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, H₁⟩ := h₁ (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, H₂⟩ := h₂ (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun n u τ hu hu0 huT htag hmesh => ?_⟩
  have e₁ := H₁ n u τ hu hu0 huT htag (fun i => lt_of_lt_of_le (hmesh i) (min_le_left _ _))
  have e₂ := H₂ n u τ hu hu0 huT htag (fun i => lt_of_lt_of_le (hmesh i) (min_le_right _ _))
  rw [Finset.sum_add_distrib]
  calc |∑ i : Fin n, S₁ (τ i) (u i.castSucc) (u i.succ) + ∑ i : Fin n, S₂ (τ i) (u i.castSucc) (u i.succ)
        - (I₁ + I₂)|
      = |(∑ i : Fin n, S₁ (τ i) (u i.castSucc) (u i.succ) - I₁)
          + (∑ i : Fin n, S₂ (τ i) (u i.castSucc) (u i.succ) - I₂)| := by ring_nf
    _ ≤ |∑ i : Fin n, S₁ (τ i) (u i.castSucc) (u i.succ) - I₁|
          + |∑ i : Fin n, S₂ (τ i) (u i.castSucc) (u i.succ) - I₂| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add e₁ e₂
    _ = ε := by ring

theorem e213u7_rsLim_eq {T : ℝ} (hT : 0 < T) {S : ℝ → ℝ → ℝ → ℝ} {I : ℝ} (h : IsRS T S I) : rsLim T S = I := by
  classical
  have hex : ∃ I, IsRS T S I := ⟨I, h⟩
  unfold rsLim
  rw [dif_pos hex]
  exact isRS_unique_proof hT hex.choose_spec h

/-- `IsRS` only sees the summands on tagged sub-intervals of `[0,T]`. -/
theorem e213u7_isRS_congr {T : ℝ} {S S' : ℝ → ℝ → ℝ → ℝ} {I : ℝ} (h : IsRS T S I)
    (hSS : ∀ τ u u' : ℝ, 0 ≤ u → u ≤ τ → τ ≤ u' → u' ≤ T → S τ u u' = S' τ u u') : IsRS T S' I := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := h ε hε
  refine ⟨δ, hδ, fun n u τ hu hu0 huT htag hmesh => ?_⟩
  have hmono : Monotone u := hu.monotone
  have key : ∀ i : Fin n, S' (τ i) (u i.castSucc) (u i.succ) = S (τ i) (u i.castSucc) (u i.succ) := by
    intro i
    refine (hSS _ _ _ ?_ (htag i).1 (htag i).2 ?_).symm
    · rw [← hu0]; exact hmono (Fin.zero_le _)
    · rw [← huT]; exact hmono (Fin.le_last _)
  simp only [key]
  exact H n u τ hu hu0 huT htag hmesh

/-- Continuity of `τ ↦ F τ (Y τ)` from continuity of `Y`, pointwise continuity of `F · y`, uniform Lipschitz in `y`. -/
theorem e213u7_cont_comp {X V : Type*} [NormedAddCommGroup X] [NormedAddCommGroup V] {S : Set ℝ}
    (F : ℝ → X → V) (Y : ℝ → X) (K : ℝ) (hY : ContinuousOn Y S)
    (hpt : ∀ y, ContinuousOn (fun τ => F τ y) S)
    (hL : ∀ τ ∈ S, ∀ y y', ‖F τ y - F τ y'‖ ≤ K * ‖y - y'‖) :
    ContinuousOn (fun τ => F τ (Y τ)) S := by
  intro τ0 h0
  have h1 : Tendsto (fun τ => F τ (Y τ0)) (𝓝[S] τ0) (𝓝 (F τ0 (Y τ0))) := hpt _ τ0 h0
  have h3 : Tendsto (fun τ => K * ‖Y τ - Y τ0‖) (𝓝[S] τ0) (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 (hY τ0 h0))).const_mul K
    simpa using this
  have h2 : Tendsto (fun τ => F τ (Y τ) - F τ (Y τ0)) (𝓝[S] τ0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h3
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact hL τ hτ _ _
  have := h2.add h1
  simp only [zero_add, sub_add_cancel] at this
  exact this

/-- Lipschitz bound for `iteratedFDeriv ℝ j f` from a bound on `iteratedFDeriv ℝ (j+1) f`. -/
theorem e213u7_lip_iFD {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → ℝ} (hf : ContDiff ℝ 5 f)
    (j : ℕ) (hj : j + 1 ≤ 5) (K : ℝ) (hK : ∀ y, ‖iteratedFDeriv ℝ (j + 1) f y‖ ≤ K) (y y' : X) :
    ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f y'‖ ≤ K * ‖y - y'‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ j f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast (by omega : j < 5))
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := iteratedFDeriv ℝ j f) (s := Set.univ)
    (C := K) (fun x _ => hd x) (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hK x) convex_univ
    (Set.mem_univ y') (Set.mem_univ y)
  exact this

section Reg

variable {S : PreparedData d} {β₀ m : ℝ}

/-- The conclusion of `Ucan_regular` (hypothesis of the core lemmas; discharged by `Ucan_regular_proof`). -/
def e213u7_Reg (hE : EdgeworthHyp S β₀ m) (T : ℝ) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) : Prop :=
  (∀ τ ∈ Set.Icc (0 : ℝ) (a + T), MemCb 5 (Ucan hE T a ha Φ τ)) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) (a + T), ∀ j ≤ 5, ∀ y, ‖iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) y‖ ≤ cbNorm 5 Φ) ∧
    (∀ y, ∀ j ≤ 3, ContinuousOn (fun τ => iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) y) (Set.Icc 0 (a + T)))

/-- The predicted window is continuous in the time. -/
theorem e213u7_Y_cont (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (w : PathSpace d m (a + T)) :
    ContinuousOn (fun τ => winPred (regime S β₀ hE) m T a ha w τ) (Set.Icc 0 (a + T)) := by
  have hH : 0 < a + T := by linarith
  have h := (HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof (regime S β₀ hE) m hE.m_gt (a + T) hH).2.2 w
  have h2 : ContinuousOn (fun τ => predicted (regime S β₀ hE).D (regime S β₀ hE).ρ w τ) (Set.Icc 0 (a + T)) :=
    continuousOn_iff_continuous_domRestrict.2 h
  exact (winRestr a ha).continuous.comp_continuousOn h2

theorem e213u7_iFD_cont (hE : EdgeworthHyp S β₀ m) (T : ℝ) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hreg : e213u7_Reg hE T a ha Φ) (Y : ℝ → PathSpace d m T) (hY : ContinuousOn Y (Set.Icc 0 (a + T)))
    (j : ℕ) (hj : j ≤ 2) :
    ContinuousOn (fun τ => iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) (Y τ)) (Set.Icc 0 (a + T)) := by
  obtain ⟨h1, h2, h3⟩ := hreg
  refine e213u7_cont_comp (fun τ y => iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) y) Y (cbNorm 5 Φ) hY
    (fun y => h3 y j (by omega)) (fun τ hτ y y' => ?_)
  exact e213u7_lip_iFD (h1 τ hτ).1 j (by omega) _ (fun y => h2 τ hτ (j + 1) (by omega) y) y y'

theorem e213u7_curry_iter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E) :
    continuousMultilinearCurryFin1 ℝ E ℝ (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
  ext δ
  simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]

theorem e213u7_fderiv_cont (hE : EdgeworthHyp S β₀ m) (T : ℝ) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hreg : e213u7_Reg hE T a ha Φ) (Y : ℝ → PathSpace d m T) (hY : ContinuousOn Y (Set.Icc 0 (a + T))) :
    ContinuousOn (fun τ => fderiv ℝ (Ucan hE T a ha Φ τ) (Y τ)) (Set.Icc 0 (a + T)) := by
  have h := e213u7_iFD_cont hE T a ha Φ hreg Y hY 1 (by norm_num)
  have h' := (continuousMultilinearCurryFin1 ℝ (PathSpace d m T) ℝ).continuous.comp_continuousOn h
  refine h'.congr (fun τ _ => ?_)
  exact (e213u7_curry_iter (Ucan hE T a ha Φ τ) (Y τ)).symm

end Reg

section Exists

variable {S : PreparedData d} {β₀ m : ℝ}

/-- Existence of the RS integral of the drift summand against the window drift of an `L¹` coefficient. -/
theorem e213u7_drift_exists (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (A : ℝ → (PathSpace d m T →L[ℝ] ℝ)) (hA : ContinuousOn A (Set.Icc 0 (a + T)))
    (c : ℝ → NegSobolev d m) (hc : MemLp c 1 (volume.restrict (Set.Icc (0 : ℝ) (a + T)))) :
    ∃ I : ℝ, IsRS (a + T) (fun τ u u' => A τ (winDrift (regime S β₀ hE) m T a ha c u u')) I := by
  have hH : 0 < a + T := by linarith
  set R := regime S β₀ hE with hR
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7PIS1.s7_PIS_drift_facts_proof R m hE.m_gt (a + T) hH
  obtain ⟨-, hadd, hbd, -, -⟩ := hC c hc
  have hci : IntegrableOn (fun u => ‖c u‖) (Set.Icc (0 : ℝ) (a + T)) :=
    (hc.integrable le_rfl).norm
  set G : ℝ → PathSpace d m T := fun s => winRestr a ha (driftInc R.D R.ρ m (a + T) c 0 s) with hG
  have hinc : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ a + T →
      G y - G x = winDrift R m T a ha c x y := by
    intro x y hx hxy hy
    have := hadd 0 x y le_rfl hx hxy hy
    unfold winDrift
    simp only [hG]
    rw [← map_sub, ← this]
    congr 1
    abel
  have hIoc : ∀ x y : ℝ, 0 ≤ x → y ≤ a + T → IntegrableOn (fun u => ‖c u‖) (Set.Ioc x y) := fun x y hx hy =>
    hci.mono_set (fun u hu => ⟨hx.trans hu.1.le, hu.2.trans hy⟩)
  obtain ⟨I, hI⟩ := q17_exists (a + T) hH A G (fun x y => C * ∫ u in Set.Ioc x y, ‖c u‖)
    (fun x y hx hxy hy => by
      rw [hinc x y hx hxy hy]
      calc ‖winDrift R m T a ha c x y‖ ≤ ‖(winRestr (d := d) (m := m) (T := T) a ha)‖ *
            ‖driftInc R.D R.ρ m (a + T) c x y‖ := (winRestr a ha).le_opNorm _
        _ ≤ 1 * ‖driftInc R.D R.ρ m (a + T) c x y‖ :=
            mul_le_mul_of_nonneg_right (winRestr_norm_le a ha) (norm_nonneg _)
        _ ≤ C * ∫ u in Set.Ioc x y, ‖c u‖ := by rw [one_mul]; exact hbd x y hx hxy hy)
    (fun x u y hx hxu huy hy => by
      have h1 := hIoc x u hx (huy.trans hy)
      have h2 := hIoc u y (hx.trans hxu) hy
      rw [← mul_add, ← setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc h1 h2,
        Set.Ioc_union_Ioc_eq_Ioc hxu huy])
    hA
  refine ⟨I, e213u7_isRS_congr hI (fun τ u u' hu huτ hτu' hu'T => ?_)⟩
  show A τ (G u' - G u) = A τ (winDrift R m T a ha c u u')
  rw [hinc u u' hu (huτ.trans hτu') hu'T]

set_option maxSynthPendingDepth 3 in
/-- Existence of the RS integral of the covariance summand against `winJ` of a bounded measurable coefficient. -/
theorem e213u7_J_exists (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (M : ℝ → (PathSpace d m T [×2]→L[ℝ] ℝ)) (hM : ContinuousOn M (Set.Icc 0 (a + T)))
    (z : ℝ → NegSobolev d m) (zr : ℝ → NegSobolev d (rLvl d)) (hz : ∀ v, 0 ≤ v → z v = NegSobolev.embed m (zr v))
    (hzr : Measurable zr) (K : ℝ) (hK : ∀ u ∈ Set.Icc (0 : ℝ) (a + T), ‖zr u‖ ≤ K) :
    ∃ I : ℝ, IsRS (a + T)
      (fun τ u u' => winJ (regime S β₀ hE) m T a ha z (Set.Ioc u u') (M τ)) I := by
  have hH : 0 < a + T := by linarith
  set R := regime S β₀ hE with hR
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7PIG1.s7_PIG_J_measure_proof R m hE.m_gt (a + T) hH
  obtain ⟨Jc, -, hJc⟩ := hC zr hzr K hK
  set P := (winRestr (d := d) (m := m) (T := T) a ha) with hP
  set G : ℝ → TensorDual (PathSpace d m T) 2 := fun s => tensorPow' 2 P (Jc s) with hG
  have hinc : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ a + T →
      G y - G x = winJ R m T a ha z (Set.Ioc x y) := by
    intro x y hx hxy hy
    have h1 := e213u2_isJValue_congr R.D R.ρ m (a + T) _ z _ measurableSet_Ioc (fun v hv => (hz v hv).symm) _
      (hJc x y hx hxy hy).1
    unfold winJ
    rw [e213u2_jTensor_eq R m (a + T) z _ _ h1, ← map_sub]
  let B : ℝ → (TensorDual (PathSpace d m T) 2 →L[ℝ] ℝ) := fun τ => ContinuousLinearMap.apply ℝ ℝ (M τ)
  have hB : ContinuousOn B (Set.Icc 0 (a + T)) :=
    (ContinuousLinearMap.apply ℝ ℝ : _ →L[ℝ] _).continuous.comp_continuousOn hM
  obtain ⟨I, hI⟩ := q17_exists (a + T) hH B G (fun x y => C * K * (y - x))
    (fun x y hx hxy hy => by
      calc ‖G y - G x‖ = ‖tensorPow' 2 P (Jc y - Jc x)‖ := by rw [hG, map_sub]
        _ ≤ ‖P‖ ^ 2 * ‖Jc y - Jc x‖ := tensorPow'_norm_le _ _ _
        _ ≤ 1 * ‖Jc y - Jc x‖ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) (winRestr_norm_le a ha)) (norm_nonneg _)
        _ ≤ C * K * (y - x) := by rw [one_mul]; exact (hJc x y hx hxy hy).2.1)
    (fun x u y hx hxu huy hy => by linarith) hB
  refine ⟨I, e213u7_isRS_congr hI (fun τ u u' hu huτ hτu' hu'T => ?_)⟩
  show B τ (G u' - G u) = _
  rw [hinc u u' hu (huτ.trans hτu') hu'T]
  rfl

end Exists

section Coef

variable {S : PreparedData d} {β₀ m : ℝ}

theorem e213u7_embed_zero (hE : EdgeworthHyp S β₀ m) : NegSobolev.embed m (0 : NegSobolev d (rLvl d)) = 0 :=
  (HRS.MD.EQInterp.embedCLM (rLvl_le hE)).map_zero

theorem e213u7_near_embed (hE : EdgeworthHyp S β₀ m) (b : ℝ) (f : ℝ → NegSobolev d (rLvl d)) :
    nearCoef b (fun v => NegSobolev.embed m (f v)) = fun v => NegSobolev.embed m (nearCoef b f v) := by
  funext v
  unfold nearCoef
  split_ifs
  · rfl
  · exact (e213u7_embed_zero hE).symm

theorem e213u7_far_embed (hE : EdgeworthHyp S β₀ m) (b : ℝ) (f : ℝ → NegSobolev d (rLvl d)) :
    farCoef b (fun v => NegSobolev.embed m (f v)) = fun v => NegSobolev.embed m (farCoef b f v) := by
  funext v
  unfold farCoef
  split_ifs
  · rfl
  · exact (e213u7_embed_zero hE).symm

theorem e213u7_meas_near {b : ℝ} (hb : 0 ≤ b) {f : ℝ → NegSobolev d (rLvl d)} (hf : Measurable (nearCoef 0 f)) :
    Measurable (nearCoef 0 (nearCoef b f)) := by
  have : nearCoef 0 (nearCoef b f) = fun v => if b ≤ v then nearCoef 0 f v else 0 := by
    funext v
    unfold nearCoef
    by_cases h1 : b ≤ v
    · simp only [if_pos h1, if_pos (hb.trans h1)]
    · simp only [if_neg h1]; split_ifs <;> rfl
  rw [this]
  exact Measurable.ite measurableSet_Ici hf measurable_const

theorem e213u7_meas_far {b : ℝ} {f : ℝ → NegSobolev d (rLvl d)} (hf : Measurable (nearCoef 0 f)) :
    Measurable (nearCoef 0 (farCoef b f)) := by
  have : nearCoef 0 (farCoef b f) = fun v => if v < b then nearCoef 0 f v else 0 := by
    funext v
    unfold nearCoef farCoef
    by_cases h0 : 0 ≤ v
    · simp only [if_pos h0]
    · simp only [if_neg h0]; split_ifs <;> rfl
  rw [this]
  exact Measurable.ite measurableSet_Iio hf measurable_const

theorem e213u7_norm_near_le (b : ℝ) (f : ℝ → NegSobolev d (rLvl d)) (v : ℝ) : ‖nearCoef b f v‖ ≤ ‖f v‖ := by
  unfold nearCoef; split_ifs
  · exact le_rfl
  · simp

theorem e213u7_norm_far_le (b : ℝ) (f : ℝ → NegSobolev d (rLvl d)) (v : ℝ) : ‖farCoef b f v‖ ≤ ‖f v‖ := by
  unfold farCoef; split_ifs
  · exact le_rfl
  · simp

theorem e213u7_nc0_apply (f : ℝ → NegSobolev d (rLvl d)) {v : ℝ} (hv : 0 ≤ v) : nearCoef 0 f v = f v := by
  unfold nearCoef; rw [if_pos hv]

theorem e213u7_memLp_embed (hE : EdgeworthHyp S β₀ m) (L : ℝ) {f g : ℝ → NegSobolev d (rLvl d)}
    (hf : Measurable (nearCoef 0 f)) (hbi : IntegrableOn (fun v => ‖g v‖) (Set.Icc 0 L))
    (hle : ∀ v, ‖f v‖ ≤ ‖g v‖) :
    MemLp (fun v => NegSobolev.embed m (f v)) 1 (volume.restrict (Set.Icc (0 : ℝ) L)) := by
  have hae : AEStronglyMeasurable f (volume.restrict (Set.Icc (0 : ℝ) L)) :=
    u1_aesm_of_nearCoef hf measurableSet_Icc (fun v hv => Set.mem_Ici.2 hv.1)
  have hι := HRS.MD.EQInterp.embedCLM (d := d) (rLvl_le hE)
  have hae2 : AEStronglyMeasurable (fun v => NegSobolev.embed m (f v)) (volume.restrict (Set.Icc (0 : ℝ) L)) :=
    (HRS.MD.EQInterp.embedCLM (d := d) (rLvl_le hE)).continuous.comp_aestronglyMeasurable hae
  rw [memLp_one_iff_integrable]
  refine Integrable.mono' hbi hae2 (Filter.Eventually.of_forall fun v => ?_)
  exact (NegSobolev.norm_embed_le m (rLvl_le hE) (f v)).trans (hle v)

theorem e213u7_integrableOn_norm (L : ℝ) {f g : ℝ → NegSobolev d (rLvl d)}
    (hf : Measurable (nearCoef 0 f)) (hbi : IntegrableOn (fun v => ‖g v‖) (Set.Icc 0 L))
    (hle : ∀ v, ‖f v‖ ≤ ‖g v‖) : IntegrableOn (fun v => ‖f v‖) (Set.Icc 0 L) := by
  have hae : AEStronglyMeasurable f (volume.restrict (Set.Icc (0 : ℝ) L)) :=
    u1_aesm_of_nearCoef hf measurableSet_Icc (fun v hv => Set.mem_Ici.2 hv.1)
  refine Integrable.mono' hbi hae.norm (Filter.Eventually.of_forall fun v => ?_)
  rw [norm_norm]; exact hle v

end Coef

section Cores

variable {S : PreparedData d} {β₀ m : ℝ}

theorem e213u7_rs_split_drift_core (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hreg : e213u7_Reg hE T a ha Φ) (w : PathSpace d m (a + T))
    (bq : ℝ → NegSobolev d (rLvl d)) (hbm : Measurable (nearCoef 0 bq))
    (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T))) (b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    IsRS (a + T)
      (rsSumD (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
        (fun u u' => winDrift (regime S β₀ hE) m T a ha (nearCoef b (fun v => NegSobolev.embed m (bq v))) u u'))
      (rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (nearCoef b (fun v => NegSobolev.embed m (bq v)))) ∧
    IsRS (a + T)
      (rsSumD (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
        (fun u u' => winDrift (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (bq v))) u u'))
      (rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b (fun v => NegSobolev.embed m (bq v)))) ∧
    rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (bq v)) =
      rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (nearCoef b (fun v => NegSobolev.embed m (bq v))) +
      rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b (fun v => NegSobolev.embed m (bq v))) := by
  have hH : 0 < a + T := by linarith
  have hA := e213u7_fderiv_cont hE T a ha Φ hreg (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
    (e213u7_Y_cont hE T hT a ha w)
  rw [e213u7_near_embed hE b bq, e213u7_far_embed hE b bq]
  have hmN := e213u7_meas_near hb hbm
  have hmF := e213u7_meas_far (b := b) hbm
  have lpN := e213u7_memLp_embed hE (a + T) hmN hbi (e213u7_norm_near_le b bq)
  have lpF := e213u7_memLp_embed hE (a + T) hmF hbi (e213u7_norm_far_le b bq)
  have lpW := e213u7_memLp_embed hE (a + T) hbm hbi (fun v => le_rfl)
  have iN := e213u7_integrableOn_norm (a + T) hmN hbi (e213u7_norm_near_le b bq)
  have iF := e213u7_integrableOn_norm (a + T) hmF hbi (e213u7_norm_far_le b bq)
  obtain ⟨In, hIn⟩ := e213u7_drift_exists hE T hT a ha _ hA _ lpN
  obtain ⟨If, hIf⟩ := e213u7_drift_exists hE T hT a ha _ hA _ lpF
  have hrN : rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (nearCoef b bq v)) = In :=
    e213u7_rsLim_eq hH hIn
  have hrF : rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (farCoef b bq v)) = If :=
    e213u7_rsLim_eq hH hIf
  have hsum : ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
      winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) u u' =
        winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (nearCoef b bq v)) u u' +
        winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (farCoef b bq v)) u u' := by
    intro u u' hu huu hu'
    have h := winDrift_add_proof hE T hT a ha (nearCoef b bq) (farCoef b bq) hmN hmF iN iF u u' hu huu hu'
    have e2 : (fun v => NegSobolev.embed m (nearCoef b bq v + farCoef b bq v)) =
        fun v => NegSobolev.embed m (bq v) := by
      funext v; exact congrArg _ (congrFun (nearCoef_add_farCoef b bq) v)
    rw [e2] at h
    exact h
  have hIW : IsRS (a + T) (fun τ u u' => fderiv ℝ (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha w τ)
      (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) u u')) (In + If) := by
    refine e213u7_isRS_congr (e213u7_isRS_add hIn hIf) (fun τ u u' hu huτ hτu' hu'T => ?_)
    beta_reduce
    rw [hsum u u' hu (huτ.trans hτu') hu'T, map_add]
  have hrW : rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (bq v)) = In + If :=
    e213u7_rsLim_eq hH hIW
  refine ⟨?_, ?_, ?_⟩
  · rw [hrN]; exact hIn
  · rw [hrF]; exact hIf
  · rw [hrW, hrN, hrF]

set_option maxSynthPendingDepth 3 in
theorem e213u7_rs_split_J_core (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hreg : e213u7_Reg hE T a ha Φ) (w : PathSpace d m (a + T))
    (zq : ℝ → NegSobolev d (rLvl d)) (hzm : Measurable (nearCoef 0 zq)) (M : ℝ)
    (hM : ∀ v ∈ Set.Icc 0 (a + T), ‖zq v‖ ≤ M)
    (b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    IsRS (a + T)
      (rsSumJ (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
        (fun u u' => winJ (regime S β₀ hE) m T a ha (nearCoef b (fun v => NegSobolev.embed m (zq v))) (Set.Ioc u u')))
      (rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (nearCoef b (fun v => NegSobolev.embed m (zq v)))) ∧
    IsRS (a + T)
      (rsSumJ (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
        (fun u u' => winJ (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (zq v))) (Set.Ioc u u')))
      (rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b (fun v => NegSobolev.embed m (zq v)))) ∧
    rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (zq v)) =
      rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (nearCoef b (fun v => NegSobolev.embed m (zq v))) +
      rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b (fun v => NegSobolev.embed m (zq v))) := by
  have hH : 0 < a + T := by linarith
  have hMc := e213u7_iFD_cont hE T a ha Φ hreg (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
    (e213u7_Y_cont hE T hT a ha w) 2 le_rfl
  rw [e213u7_near_embed hE b zq, e213u7_far_embed hE b zq]
  have hmN := e213u7_meas_near hb hzm
  have hmF := e213u7_meas_far (b := b) hzm
  have hbd : ∀ (f : ℝ → NegSobolev d (rLvl d)), (∀ v, ‖f v‖ ≤ ‖zq v‖) →
      ∀ v ∈ Set.Icc (0 : ℝ) (a + T), ‖nearCoef 0 f v‖ ≤ M := fun f hf v hv => by
    rw [e213u7_nc0_apply f hv.1]; exact (hf v).trans (hM v hv)
  obtain ⟨In, hIn⟩ := e213u7_J_exists hE T hT a ha _ hMc (fun v => NegSobolev.embed m (nearCoef b zq v))
    (nearCoef 0 (nearCoef b zq)) (fun v hv => by rw [e213u7_nc0_apply _ hv]) hmN M
    (hbd _ (e213u7_norm_near_le b zq))
  obtain ⟨If, hIf⟩ := e213u7_J_exists hE T hT a ha _ hMc (fun v => NegSobolev.embed m (farCoef b zq v))
    (nearCoef 0 (farCoef b zq)) (fun v hv => by rw [e213u7_nc0_apply _ hv]) hmF M
    (hbd _ (e213u7_norm_far_le b zq))
  have hrN : rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (nearCoef b zq v)) = In :=
    e213u7_rsLim_eq hH hIn
  have hrF : rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (farCoef b zq v)) = If :=
    e213u7_rsLim_eq hH hIf
  have hM0 : ∀ f : ℝ → NegSobolev d (rLvl d), (∀ v, ‖f v‖ ≤ ‖zq v‖) →
      ∀ v ∈ Set.Icc (0 : ℝ) (a + T), ‖f v‖ ≤ M := fun f hf v hv => (hf v).trans (hM v hv)
  have hsum : ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
      winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zq v)) (Set.Ioc u u') =
        winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (nearCoef b zq v)) (Set.Ioc u u') +
        winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (farCoef b zq v)) (Set.Ioc u u') := by
    intro u u' hu huu hu'
    have h := winJ_add_proof hE T hT a ha (nearCoef b zq) (farCoef b zq) hmN hmF M M
      (hM0 _ (e213u7_norm_near_le b zq)) (hM0 _ (e213u7_norm_far_le b zq)) u u' hu huu hu'
    have e2 : (fun v => NegSobolev.embed m (nearCoef b zq v + farCoef b zq v)) =
        fun v => NegSobolev.embed m (zq v) := by
      funext v; exact congrArg _ (congrFun (nearCoef_add_farCoef b zq) v)
    rw [e2] at h
    exact h
  have hIW : IsRS (a + T) (fun τ u u' => winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zq v))
      (Set.Ioc u u') (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha w τ))) (In + If) := by
    refine e213u7_isRS_congr (e213u7_isRS_add hIn hIf) (fun τ u u' hu huτ hτu' hu'T => ?_)
    beta_reduce
    rw [hsum u u' hu (huτ.trans hτu') hu'T, ContinuousLinearMap.add_apply]
  have hrW : rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (zq v)) = In + If :=
    e213u7_rsLim_eq hH hIW
  refine ⟨?_, ?_, ?_⟩
  · rw [hrN]; exact hIn
  · rw [hrF]; exact hIf
  · rw [hrW, hrN, hrF]

end Cores

end HRS.MC.E213U7

end
