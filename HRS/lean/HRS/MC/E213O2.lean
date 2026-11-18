import HRS.MC.E213D
import HRS.MC.E213O1
import HRS.MD.EQInterpHolder

/-!
# Packet E213O2: initial-term decay `‖I_a‖ ≤ C e^{-c a}` (item C2)

`initWinFun D ρ m r T a z = pathOf m T (t ↦ V^{a+t,0} ι z)` for `z ∈ E_r`, `ι : E_r ↪ E_m` (`r ≤ m`).
`initWin_decay`: for the regime of a prepared datum there are `C, c > 0` such that for every `a ≥ 0` the map
`initWinFun` is a continuous linear map `E_r →L 𝒳_{m,T}` of operator norm `≤ C e^{-c a}`.
-/

noncomputable section

open HRS HRS.Main HRS.Sec7 HRS.Uniform

namespace HRS.MC.E213O

variable {d : ℕ}

/-- `I_a z := (t ↦ V^{a+t,0} z)` as an element of `𝒳_{m,T}` (`z ∈ E_r` embedded into `E_m`; junk `0` if the path is
not continuous). -/
def initWinFun (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m r T a : ℝ) (z : NegSobolev d r) : PathSpace d m T :=
  pathOf m T fun t => Vprop D ρ m (a + t) 0 (NegSobolev.embed m z)

/-- The dual evolution of the regime at level `m`, with continuity and decay. -/
theorem e213o_vev (S : PreparedData d) (β₀ : ℝ) {m₀ : ℝ} (hE : EdgeworthHyp S β₀ m₀) (m : ℝ) :
    ∃ Cm cm : ℝ, 0 < Cm ∧ 0 < cm ∧ ∃ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ F : NegSobolev d m,
        Vprop (E213A.regimeOfPrepared S β₀ hE).D (E213A.regimeOfPrepared S β₀ hE).ρ m t u F = Vev t u F) ∧
      (∀ T' : ℝ, 0 ≤ T' → ∀ F : NegSobolev d m,
        ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 F) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'}) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cm * Real.exp (-cm * (t - u))) := by
  obtain ⟨Cr, cr, hC, hc, Vev, hdual, hplain, hdec, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd (E213A.isSmoothPositiveTrajectory_of_prepared S) m
  have hdual' : IsDualEvolution (E213A.regimeOfPrepared S β₀ hE).D (E213A.regimeOfPrepared S β₀ hE).ρ m Vev :=
    hdual
  exact ⟨Cr, cr, hC, hc, Vev, fun u t hu hut F => E213D.vprop_eq_vev _ _ m Vev hdual' hu hut F,
    fun T' hT' F => (hplain T' hT').2.2 F, hdec⟩

/-- `t ↦ V^{t,0} F` is continuous on `[0,T']` (all `T' ≥ 0`). -/
theorem vprop_continuousOn_zero (S : PreparedData d) (β₀ : ℝ) {m₀ : ℝ} (hE : EdgeworthHyp S β₀ m₀) (m : ℝ)
    (T' : ℝ) (hT' : 0 ≤ T') (F : NegSobolev d m) :
    ContinuousOn (fun t : ℝ =>
      Vprop (E213A.regimeOfPrepared S β₀ hE).D (E213A.regimeOfPrepared S β₀ hE).ρ m t 0 F) (Set.Icc 0 T') := by
  obtain ⟨Cm, cm, -, -, Vev, hV, hcont, -⟩ := e213o_vev S β₀ hE m
  have h1 : ContinuousOn (fun t : ℝ => Vev t 0 F) (Set.Icc 0 T') := by
    have := (hcont T' hT' F).comp (f := fun t : ℝ => (t, (0 : ℝ))) (by fun_prop)
      (s := Set.Icc 0 T') (fun t ht => ⟨le_rfl, ht.1, ht.2⟩)
    exact this
  refine h1.congr (fun t ht => hV 0 t le_rfl ht.1 F)

/-- **(C2)** The initial-term operator `I_a : E_r →L 𝒳_{m,T}`, `(I_a z)(t) = V^{a+t,0} z`, exists and
`‖I_a‖ ≤ C e^{-c a}` with `C, c > 0` independent of `a ≥ 0` (and of `T`, `r ≤ m`). -/
theorem initWin_decay (S : PreparedData d) (β₀ : ℝ) {m₀ : ℝ} (hE : EdgeworthHyp S β₀ m₀) (r m T : ℝ)
    (hrm : r ≤ m) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a →
      ∃ I : NegSobolev d r →L[ℝ] PathSpace d m T,
        (∀ z : NegSobolev d r, I z =
          initWinFun (E213A.regimeOfPrepared S β₀ hE).D (E213A.regimeOfPrepared S β₀ hE).ρ m r T a z) ∧
        ‖I‖ ≤ C * Real.exp (-c * a) := by
  obtain ⟨Cm, cm, hC, hc, Vev, hV, hcont, hdec⟩ := e213o_vev S β₀ hE m
  refine ⟨Cm, cm, hC, hc, fun a ha => ?_⟩
  -- the continuous path for each `z`
  have hpath : ∀ z : NegSobolev d r, Continuous fun t : Set.Icc (0 : ℝ) T =>
      Vev (a + t) 0 (NegSobolev.embed m z) := by
    intro z
    by_cases hT : 0 ≤ T
    · have h1 : ContinuousOn (fun t : ℝ => Vev (a + t) 0 (NegSobolev.embed m z)) (Set.Icc 0 T) := by
        have := (hcont (a + T) (by linarith) (NegSobolev.embed m z)).comp
          (f := fun t : ℝ => (a + t, (0 : ℝ))) (by fun_prop) (s := Set.Icc 0 T)
          (fun t ht => ⟨le_rfl, by linarith [ht.1], by linarith [ht.2]⟩)
        exact this
      exact continuousOn_iff_continuous_domRestrict.1 h1
    · have : IsEmpty (Set.Icc (0 : ℝ) T) := ⟨fun t => hT (t.2.1.trans t.2.2)⟩
      exact continuous_of_discreteTopology
  let L : NegSobolev d r →ₗ[ℝ] PathSpace d m T :=
    { toFun := fun z => (⟨fun t : Set.Icc (0 : ℝ) T => Vev (a + t) 0 (NegSobolev.embed m z), hpath z⟩ :
        C(Set.Icc (0 : ℝ) T, NegSobolev d m))
      map_add' := fun z z' => by
        refine e213o_ext (fun t => ?_)
        show Vev (a + t) 0 (NegSobolev.embed m (z + z')) = _
        have : NegSobolev.embed m (z + z') = NegSobolev.embed m z + NegSobolev.embed m z' :=
          (HRS.MD.EQInterp.embedCLM hrm).map_add z z'
        rw [this, map_add]; rfl
      map_smul' := fun c z => by
        refine e213o_ext (fun t => ?_)
        show Vev (a + t) 0 (NegSobolev.embed m (c • z)) = _
        have : NegSobolev.embed m (c • z) = c • NegSobolev.embed m z :=
          (HRS.MD.EQInterp.embedCLM hrm).map_smul c z
        rw [this, map_smul]; rfl }
  have hbound : ∀ z, ‖L z‖ ≤ Cm * Real.exp (-cm * a) * ‖z‖ := by
    intro z
    have h0 : 0 ≤ Cm * Real.exp (-cm * a) * ‖z‖ := by positivity
    refine (ContinuousMap.norm_le _ h0).2 (fun t => ?_)
    show ‖Vev (a + t) 0 (NegSobolev.embed m z)‖ ≤ _
    have h1 := hdec 0 (a + t) le_rfl (by linarith [t.2.1])
    calc ‖Vev (a + t) 0 (NegSobolev.embed m z)‖ ≤ ‖Vev (a + t) 0‖ * ‖NegSobolev.embed m z‖ :=
          (Vev (a + t) 0).le_opNorm _
      _ ≤ (Cm * Real.exp (-cm * (a + t - 0))) * ‖z‖ :=
          mul_le_mul h1 (NegSobolev.norm_embed_le m hrm z) (norm_nonneg _) (by positivity)
      _ ≤ Cm * Real.exp (-cm * a) * ‖z‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC.le) (norm_nonneg _)
          apply Real.exp_le_exp.2
          nlinarith [t.2.1]
  refine ⟨LinearMap.mkContinuous L (Cm * Real.exp (-cm * a)) hbound, fun z => ?_, ?_⟩
  · refine e213o_ext (fun t => ?_)
    have hc' : Continuous fun t : Set.Icc (0 : ℝ) T =>
        Vprop (E213A.regimeOfPrepared S β₀ hE).D (E213A.regimeOfPrepared S β₀ hE).ρ m (a + t) 0
          (NegSobolev.embed m z) := by
      have : (fun t : Set.Icc (0 : ℝ) T =>
          Vprop (E213A.regimeOfPrepared S β₀ hE).D (E213A.regimeOfPrepared S β₀ hE).ρ m (a + t) 0
            (NegSobolev.embed m z)) = fun t : Set.Icc (0 : ℝ) T => Vev (a + (t : ℝ)) 0 (NegSobolev.embed m z) := by
        funext t
        exact hV 0 (a + t) le_rfl (by linarith [t.2.1]) _
      rw [this]; exact hpath z
    unfold initWinFun
    rw [e213o_pathOf_at' _ hc' t]
    exact (hV 0 (a + t) le_rfl (by linarith [t.2.1]) _).symm
  · exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- `initWinFun` is the window restriction of the horizon-`a+T` initial propagation (`initProp`). -/
theorem initWinFun_eq_winRestr_initProp (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m r T a : ℝ) (ha : 0 ≤ a)
    (z : NegSobolev d r)
    (h : ContinuousOn (fun t : ℝ => Vprop D ρ m t 0 (NegSobolev.embed m z)) (Set.Icc 0 (a + T))) :
    initWinFun D ρ m r T a z = winRestr a ha (initProp D ρ m (a + T) (NegSobolev.embed m z)) :=
  winRestr_pathOf a ha _ h

end HRS.MC.E213O

end
