import HRS.MC.E213U4
import HRS.MC.S7PIL5
import HRS.MC.E213O1
import HRS.MC.S7PIS1Path2

/-!
# Packet e213u5 (Theorem 2.13, Wave 2): `Ucan_regular`

Differentiation under the integral sign for `Ucan τ y = ∫ Φ(y + R_a z) dγ_τ(z)` (`MemCb 5`, derivative bounds), and
the continuity in `τ` of `D^j Ucan τ y` from the Lipschitz bound `s7_PIB_lip_proof` of PI-B (marginals only), through the
identity `Ucan τ = heatFn γ (Φ ∘ R_a) τ ∘ E_a` for the extension `E_a` (a right inverse of `R_a`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U5

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section HeatDeriv

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
  [SecondCountableTopology Z]

/-- Differentiation under the integral sign: `y ↦ ∫ Φ(y + R z) dν(z)` is `C^5` with `D^j = ∫ D^jΦ(y + R z) dν`. -/
theorem e213u5_heat_deriv (ν : Measure Z) [IsProbabilityMeasure ν] (R : Z →L[ℝ] B) {Φ : B → ℝ}
    (hΦ : MemCb 5 Φ) :
    ContDiff ℝ 5 (fun y => ∫ z, Φ (y + R z) ∂ν) ∧
      ∀ j ≤ 5, ∀ y, iteratedFDeriv ℝ j (fun y => ∫ z, Φ (y + R z) ∂ν) y =
        ∫ z, iteratedFDeriv ℝ j Φ (y + R z) ∂ν := by
  have hGc : ∀ m : ℕ, m ≤ 5 → Continuous (iteratedFDeriv ℝ m Φ) := fun m hm =>
    hΦ.1.continuous_iteratedFDeriv (by exact_mod_cast hm)
  have hcd : ∀ z : Z, ContDiff ℝ ((5 : ℕ) : WithTop ℕ∞) (fun y => Φ (y + R z)) :=
    fun z => by
      have := hΦ.1.comp (contDiff_id.add (contDiff_const (c := R z)))
      simpa [Function.comp_def] using this
  have key := contDiff_integral_dominated (B := B) ν
    (fun z y => Φ (y + R z)) 5 (by norm_num) hcd
    (fun x => by
      have hGcont : Continuous Φ := by simpa using hΦ.1.continuous
      refine Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ 0 Φ z‖) ?_ ?_
      · exact (hGcont.comp (by fun_prop : Continuous fun z => x + R z)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun z => ?_
        have := HRS.MC.Sec7.S7PIS3.S7PIS3_cb_bound hΦ (j := 0) (Nat.zero_le _) (x + R z)
        simpa using this)
    (fun m hm x => by
      have h : (fun z => iteratedFDeriv ℝ m (fun y => Φ (y + R z)) x) =
          fun z => iteratedFDeriv ℝ m Φ (x + R z) := by
        funext z; exact iteratedFDeriv_comp_add_right m (R z) x
      rw [h]
      exact ((hGc m hm).comp (by fun_prop : Continuous fun z => x + R z)).aestronglyMeasurable)
    (fun m _ => ⨆ z, ‖iteratedFDeriv ℝ m Φ z‖) (fun m _ _ => integrable_const _)
    (fun m _ hmj z x => by
      rw [iteratedFDeriv_comp_add_right]
      exact HRS.MC.Sec7.S7PIS3.S7PIS3_cb_bound hΦ hmj _)
  refine ⟨by simpa using key.1, fun j hj y => ?_⟩
  rw [key.2 j hj y]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact iteratedFDeriv_comp_add_right j (R z) y

end HeatDeriv

section Ext

/-- The extension `E_a : 𝒳_{m,T} →L 𝒳_{m,a+T}`, `(E_a y)(t) = y(clamp (t - a))` (constant before `a`); a right inverse of `winRestr a`. -/
def e213u5_extLM {m T : ℝ} (a : ℝ) (hT : 0 < T) :
    PathSpace d m T →ₗ[ℝ] PathSpace d m (a + T) where
  toFun y := (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from y).comp
    ⟨fun t : Set.Icc (0 : ℝ) (a + T) => Set.projIcc (0 : ℝ) T hT.le (t.1 - a),
      continuous_projIcc.comp (continuous_subtype_val.sub continuous_const)⟩
  map_add' y y' := ContinuousMap.ext fun t => rfl
  map_smul' c y := ContinuousMap.ext fun t => rfl

def e213u5_ext {m T : ℝ} (a : ℝ) (hT : 0 < T) : PathSpace d m T →L[ℝ] PathSpace d m (a + T) :=
  LinearMap.mkContinuous (e213u5_extLM a hT) 1 (fun y => by
    rw [one_mul]
    refine ContinuousMap.norm_le _ (norm_nonneg _) |>.2 (fun t => ?_)
    exact ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from y)
      (Set.projIcc (0 : ℝ) T hT.le (t.1 - a)))

theorem e213u5_winRestr_ext {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) (hT : 0 < T) (y : PathSpace d m T) :
    winRestr a ha (e213u5_ext a hT y) = y := by
  refine ContinuousMap.ext fun t => ?_
  show (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from y) (Set.projIcc (0 : ℝ) T hT.le ((a + t.1) - a)) =
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from y) t
  have : Set.projIcc (0 : ℝ) T hT.le ((a + t.1) - a) = t := by
    rw [add_sub_cancel_left]
    exact Set.projIcc_val hT.le t
  rw [this]

end Ext

section Main

variable {S : PreparedData d} {β₀ m : ℝ}

theorem e213u5_canonFut_spec (hE : EdgeworthHyp S β₀ m) (H : ℝ) (hH : 0 < H) :
    ∀ u ∈ Set.Icc (0 : ℝ) H,
      IsFutureGaussian (regime S β₀ hE).D (regime S β₀ hE).ρ m H u (canonFut hE H u) ∧
        IsProbabilityMeasure (canonFut hE H u) := by
  classical
  have h := HRS.MC.E213U4.exists_futureGaussians_proof hE H hH
  unfold canonFut
  rw [dif_pos h]
  exact h.choose_spec

theorem e213u5_sup_le_cbNorm {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    {Φ : B → ℝ} {j : ℕ} (hj : j ≤ 5) : (⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) ≤ cbNorm 5 Φ := by
  unfold cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))

theorem Ucan_regular_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) :
    (∀ τ ∈ Set.Icc (0 : ℝ) (a + T), MemCb 5 (Ucan hE T a ha Φ τ)) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) (a + T), ∀ j ≤ 5, ∀ y,
      ‖iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) y‖ ≤ cbNorm 5 Φ) ∧
    (∀ y, ∀ j ≤ 3, ContinuousOn (fun τ => iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) y) (Set.Icc 0 (a + T))) := by
  have hH : 0 < a + T := by linarith
  have hspec := e213u5_canonFut_spec hE (a + T) hH
  -- derivative formula and bounds
  have hD : ∀ τ ∈ Set.Icc (0 : ℝ) (a + T), ContDiff ℝ 5 (Ucan hE T a ha Φ τ) ∧
      ∀ j ≤ 5, ∀ y, iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) y =
        ∫ z, iteratedFDeriv ℝ j Φ (y + winRestr a ha z) ∂(canonFut hE (a + T) τ) := by
    intro τ hτ
    haveI := (hspec τ hτ).2
    exact e213u5_heat_deriv (canonFut hE (a + T) τ) (winRestr a ha) hΦ
  have hB : ∀ τ ∈ Set.Icc (0 : ℝ) (a + T), ∀ j ≤ 5, ∀ y,
      ‖iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) y‖ ≤ cbNorm 5 Φ := by
    intro τ hτ j hj y
    haveI := (hspec τ hτ).2
    rw [(hD τ hτ).2 j hj y]
    refine (norm_integral_le_of_norm_le_const (C := cbNorm 5 Φ) (Filter.Eventually.of_forall fun z => ?_)).trans
      (by simp)
    exact (HRS.MC.Sec7.S7PIS3.S7PIS3_cb_bound hΦ hj _).trans (e213u5_sup_le_cbNorm hj)
  refine ⟨fun τ hτ => ⟨(hD τ hτ).1, fun j hj => ⟨cbNorm 5 Φ, ?_⟩⟩, hB, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hB τ hτ j hj y
  -- time regularity
  have hΨcb : MemCb 5 (fun w => Φ (winRestr a ha w)) := (winRestr_memCb a ha hΦ).1
  have hclamp : ∀ u ∈ Set.Icc (0 : ℝ) (a + T), max 0 (min u (a + T)) = u := fun u hu => by
    rw [min_eq_left hu.2, max_eq_right hu.1]
  have hmem : ∀ u : ℝ, max 0 (min u (a + T)) ∈ Set.Icc (0 : ℝ) (a + T) := fun u =>
    ⟨le_max_left _ _, max_le hH.le (min_le_right _ _)⟩
  have hγ : ∀ u ∈ Set.Icc (0 : ℝ) (a + T), IsFutureGaussian (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T) u
      ((fun u => canonFut hE (a + T) (max 0 (min u (a + T)))) u) := by
    intro u hu
    have := (hspec u hu).1
    simp only [hclamp u hu]
    exact this
  have hγp : ∀ u, IsProbabilityMeasure ((fun u => canonFut hE (a + T) (max 0 (min u (a + T)))) u) :=
    fun u => (hspec _ (hmem u)).2
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7PIL.s7_PIB_lip_proof (regime S β₀ hE) m hE.m_gt (a + T) hH
    (fun u => canonFut hE (a + T) (max 0 (min u (a + T)))) hγ hγp
  have hheat : ∀ u ∈ Set.Icc (0 : ℝ) (a + T),
      heatFn (fun u => canonFut hE (a + T) (max 0 (min u (a + T)))) (fun w => Φ (winRestr a ha w)) u =
        heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) u := by
    intro u hu
    funext y
    simp only [heatFn, hclamp u hu]
  have hC' := fun u hu v hv j hj y => by
    have := hC (fun w => Φ (winRestr a ha w)) hΨcb u hu v hv j hj y
    rwa [hheat u hu, hheat v hv] at this
  set E := e213u5_ext (d := d) (m := m) a hT with hEdef
  have hUE : ∀ τ y', Ucan hE T a ha Φ τ y' =
      heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) τ (E y') := by
    intro τ y'
    rw [heatFn_comp_winRestr hE T a ha Φ τ (E y'), hEdef, e213u5_winRestr_ext a ha hT y']
  have hheatCD : ∀ τ ∈ Set.Icc (0 : ℝ) (a + T),
      ContDiff ℝ 5 (heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) τ) := by
    intro τ hτ
    have : heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) τ =
        fun y => Ucan hE T a ha Φ τ (winRestr a ha y) := funext (heatFn_comp_winRestr hE T a ha Φ τ)
    rw [this]
    exact (hD τ hτ).1.comp (winRestr a ha).contDiff
  have hder : ∀ τ ∈ Set.Icc (0 : ℝ) (a + T), ∀ j ≤ 3, ∀ y',
      iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) y' =
        (iteratedFDeriv ℝ j (heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) τ) (E y')
          ).compContinuousLinearMap (fun _ => E) := by
    intro τ hτ j hj y'
    have : Ucan hE T a ha Φ τ =
        fun y' => heatFn (canonFut hE (a + T)) (fun w => Φ (winRestr a ha w)) τ (E y') := funext (hUE τ)
    rw [this]
    exact E.iteratedFDeriv_comp_right (hheatCD τ hτ) y' (by exact_mod_cast hj.trans (by norm_num))
  intro y j hj
  have hK : ∀ τ ∈ Set.Icc (0 : ℝ) (a + T), ∀ τ' ∈ Set.Icc (0 : ℝ) (a + T),
      dist (iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) y) (iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ') y) ≤
        (C * cbNorm 5 (fun w => Φ (winRestr a ha w)) * ‖E‖ ^ j) * dist τ τ' := by
    intro τ hτ τ' hτ'
    rw [dist_eq_norm, hder τ hτ j hj y, hder τ' hτ' j hj y]
    have hsub : ∀ (A A' : (PathSpace d m (a + T)) [×j]→L[ℝ] ℝ),
        A.compContinuousLinearMap (fun _ => E) - A'.compContinuousLinearMap (fun _ => E) =
          (A - A').compContinuousLinearMap (fun _ => E) := by
      intro A A'
      ext v
      simp
    rw [hsub]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 := hC' τ hτ τ' hτ' j hj (E y)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Real.dist_eq]
    calc _ ≤ (C * cbNorm 5 (fun w => Φ (winRestr a ha w)) * |τ - τ'|) * ‖E‖ ^ j :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  have hLip : LipschitzOnWith (Real.toNNReal (C * cbNorm 5 (fun w => Φ (winRestr a ha w)) * ‖E‖ ^ j))
      (fun τ => iteratedFDeriv ℝ j (Ucan hE T a ha Φ τ) y) (Set.Icc 0 (a + T)) := by
    refine LipschitzOnWith.of_dist_le_mul fun τ hτ τ' hτ' => ?_
    refine (hK τ hτ τ' hτ').trans ?_
    exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg
  exact hLip.continuousOn

/-- The hidden obligation of `Ucan_regular` (review finding F7): `τ ↦ winPred w τ` is continuous in `𝒳_{m,T}`
(from `s7_PIS_path_facts_proof` (c) and the continuity of `winRestr`). -/
theorem e213u5_winPred_cont (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (w : PathSpace d m (a + T)) :
    Continuous fun τ : Set.Icc (0 : ℝ) (a + T) => winPred (regime S β₀ hE) m T a ha w τ := by
  have hH : 0 < a + T := by linarith
  exact (winRestr a ha).continuous.comp
    ((HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof (regime S β₀ hE) m hE.m_gt (a + T) hH).2.2 w)

end Main

end HRS.MC.E213U5

end
