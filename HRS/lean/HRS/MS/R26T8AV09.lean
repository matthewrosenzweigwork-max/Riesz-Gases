import HRS.MS.R26T8AD01
import HRS.MS.IidInitAux1

/-!
# S8.2 observed-time layer, packet T8A.V09: continuous-path representatives of a window and its reversal

Route: on a measurable full-measure event the path is continuous and agrees with fixed measurable versions at all
dyadic times in `[0,T]`; there `Y w t` is the limit of the measurable versions at the dyadic floors of `t`, hence each
evaluation is measurable.  `Yrev` is the time reflection of `Y`.  The laws agree because finite-dimensional
distributions determine a law on `C([0,T]; E)` (`sa27_path_ext`, coordinate functionals) and `hrev` gives them.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_v09_genE (d : ℕ) :
    (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d))) =
      ⨆ j : Fin d, MeasurableSpace.comap (fun x : EuclideanSpace ℝ (Fin d) => x j)
        (inferInstance : MeasurableSpace ℝ) := by
  apply le_antisymm
  · let e := (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph.toMeasurableEquiv
    have h1 : (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d))) ≤
        MeasurableSpace.comap e (MeasurableSpace.pi : MeasurableSpace (Fin d → ℝ)) :=
      fun s hs => ⟨e.symm ⁻¹' s, e.symm.measurable hs, by ext x; simp⟩
    refine h1.trans ?_
    show MeasurableSpace.comap e (⨆ j : Fin d, MeasurableSpace.comap (fun y : Fin d → ℝ => y j)
      (inferInstance : MeasurableSpace ℝ)) ≤ _
    rw [MeasurableSpace.comap_iSup]
    refine iSup_mono fun j => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_rfl
  · exact iSup_le fun j => (measurable_iff_comap_le).1 ((EuclideanSpace.proj j).continuous.measurable)

theorem r26t8a_v09_gen (d N : ℕ) :
    (inferInstance : MeasurableSpace (EucConfig d N)) =
      ⨆ ij : Fin N × Fin d, MeasurableSpace.comap (fun X : EucConfig d N => X ij.1 ij.2)
        (inferInstance : MeasurableSpace ℝ) := by
  show (⨆ i : Fin N, MeasurableSpace.comap (fun X : Fin N → EuclideanSpace ℝ (Fin d) => X i)
    (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d)))) = _
  rw [iSup_prod]
  refine iSup_congr fun i => ?_
  rw [r26t8a_v09_genE d, MeasurableSpace.comap_iSup]
  refine iSup_congr fun j => ?_
  rw [MeasurableSpace.comap_comp]
  rfl

/-- the dyadic floor of `t` -/
def r26t8a_v09_fl (k : ℕ) (t : ℝ) : ℝ := (⌊(2 : ℝ) ^ k * t⌋₊ : ℝ) / (2 : ℝ) ^ k

theorem r26t8a_v09_fl_le {k : ℕ} {t : ℝ} (ht : 0 ≤ t) : r26t8a_v09_fl k t ≤ t := by
  unfold r26t8a_v09_fl
  rw [div_le_iff₀ (by positivity)]
  have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ k * t by positivity)
  linarith

theorem r26t8a_v09_fl_tendsto {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun k => r26t8a_v09_fl k t) atTop (𝓝 t) := by
  have h0 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : Tendsto (fun k : ℕ => t - (1 / 2 : ℝ) ^ k) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds (fun k => ?_)
    (fun k => r26t8a_v09_fl_le ht)
  unfold r26t8a_v09_fl
  have h2 := Nat.lt_floor_add_one ((2 : ℝ) ^ k * t)
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [le_div_iff₀ hp, sub_mul]
  have : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  linarith

theorem r26t8a_window_path_law {d N : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] (X : ℝ≥0 → Omega → EucConfig d N)
    (hm : ∀ t, AEMeasurable (X t) P) (hc : ∀ᵐ w ∂P, Continuous fun t => X t w)
    (hrev : r26t8a_ReversibleWindows P X) (u T : ℝ) (hu : 0≤u) (hT : 0≤T) :
    ∃ Y Yrev : Omega → C(Set.Icc (0:ℝ) T,EucConfig d N),
      Measurable Y ∧ Measurable Yrev ∧ P.map Y=P.map Yrev ∧
      (∀ᵐ w ∂P, ∀ t : Set.Icc (0:ℝ) T,
        Y w t=X (u+t).toNNReal w ∧ Yrev w t=X (u+T-t).toNNReal w) := by
  classical
  let Z : ℝ → Omega → EucConfig d N := fun r => (hm (u + r).toNNReal).mk (X (u + r).toNNReal)
  have hZm : ∀ r, Measurable (Z r) := fun r => (hm _).measurable_mk
  have hZae : ∀ r, X (u + r).toNNReal =ᵐ[P] Z r := fun r => (hm _).ae_eq_mk
  let Dset : Set ℝ := {r | ∃ p : ℕ × ℕ, r = (p.2 : ℝ) / 2 ^ p.1}
  have hDc : Dset.Countable :=
    (Set.countable_range (fun p : ℕ × ℕ => (p.2 : ℝ) / 2 ^ p.1)).mono (by
      rintro r ⟨p, rfl⟩; exact ⟨p, rfl⟩)
  have hD : ∀ᵐ w ∂P, ∀ r ∈ Dset, X (u + r).toNNReal w = Z r w :=
    (ae_ball_iff hDc).2 fun r _ => hZae r
  have hcomb : ∀ᵐ w ∂P, (Continuous fun t => X t w) ∧ ∀ r ∈ Dset, X (u + r).toNNReal w = Z r w := by
    filter_upwards [hc, hD] with w h1 h2 using ⟨h1, h2⟩
  obtain ⟨N0, hN0sub, hN0m, hN00⟩ := exists_measurable_superset_of_null (ae_iff.1 hcomb)
  set Om2 : Set Omega := N0ᶜ with hOm2
  have hOm2m : MeasurableSet Om2 := hN0m.compl
  have hOm2mem : ∀ w ∈ Om2, (Continuous fun t => X t w) ∧ ∀ r ∈ Dset, X (u + r).toNNReal w = Z r w := by
    intro w hw
    by_contra h
    exact hw (hN0sub h)
  have hcontR : ∀ w ∈ Om2, Continuous fun s : ℝ => X (u + s).toNNReal w := fun w hw =>
    (hOm2mem w hw).1.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))
  let Y : Omega → C(Set.Icc (0:ℝ) T, EucConfig d N) := fun w =>
    if hw : w ∈ Om2 then ⟨fun t => X (u + t).toNNReal w,
      (hcontR w hw).comp continuous_subtype_val⟩ else 0
  have hYeval : ∀ w (t : Set.Icc (0:ℝ) T), Y w t = if w ∈ Om2 then X (u + t).toNNReal w else 0 := by
    intro w t
    by_cases hw : w ∈ Om2 <;> simp [Y, hw]
  have hYt : ∀ t : Set.Icc (0:ℝ) T, Measurable (fun w => Y w t) := by
    intro t
    have hlim : ∀ w ∈ Om2, Y w t = limUnder atTop (fun k => Z (r26t8a_v09_fl k t) w) := by
      intro w hw
      rw [hYeval, if_pos hw]
      symm
      refine Tendsto.limUnder_eq ?_
      have hf := ((hcontR w hw).tendsto (t : ℝ)).comp (r26t8a_v09_fl_tendsto t.2.1)
      refine hf.congr fun k => ?_
      have hmemD : r26t8a_v09_fl k t ∈ Dset := ⟨(k, ⌊(2 : ℝ) ^ k * t⌋₊), rfl⟩
      exact (hOm2mem w hw).2 _ hmemD
    have hmeasZ : Measurable fun w => limUnder atTop (fun k => Z (r26t8a_v09_fl k t) w) :=
      (StronglyMeasurable.limUnder (fun k => (hZm _).stronglyMeasurable)).measurable
    have : (fun w => Y w t) =
        fun w => if w ∈ Om2 then limUnder atTop (fun k => Z (r26t8a_v09_fl k t) w) else 0 := by
      funext w
      by_cases hw : w ∈ Om2
      · rw [if_pos hw]; exact hlim w hw
      · rw [if_neg hw, hYeval, if_neg hw]
    rw [this]
    exact Measurable.ite hOm2m hmeasZ measurable_const
  have hYm : Measurable Y := ContinuousMap.measurable_iff_eval.2 hYt
  have hrm : ∀ t : Set.Icc (0:ℝ) T, T - (t : ℝ) ∈ Set.Icc (0:ℝ) T := fun t =>
    ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
  let rm : C(Set.Icc (0:ℝ) T, Set.Icc (0:ℝ) T) :=
    ⟨fun t => ⟨T - t, hrm t⟩,
      Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) hrm⟩
  let Yrev : Omega → C(Set.Icc (0:ℝ) T, EucConfig d N) := fun w => (Y w).comp rm
  have hYrm : Measurable Yrev := (ContinuousMap.continuous_precomp rm).measurable.comp hYm
  have hae : ∀ᵐ w ∂P, ∀ t : Set.Icc (0:ℝ) T,
      Y w t = X (u + t).toNNReal w ∧ Yrev w t = X (u + T - t).toNNReal w := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN00] with w hw t
    have hw' : w ∈ Om2 := hw
    refine ⟨by rw [hYeval, if_pos hw'], ?_⟩
    show Y w (rm t) = _
    rw [hYeval, if_pos hw']
    show X (u + (T - (t : ℝ))).toNNReal w = _
    rw [add_sub_assoc]
  refine ⟨Y, Yrev, hYm, hYrm, ?_, hae⟩
  have hgen := r26t8a_v09_gen d N
  refine IidInit.sa27_path_ext T (fun (ij : Fin N × Fin d) (Xc : EucConfig d N) => Xc ij.1 ij.2)
    hgen _ _ fun p g => ?_
  have hfd := IidInit.sa27_fd_measurable
    (IidInit.sa27_pathF T (fun (ij : Fin N × Fin d) (Xc : EucConfig d N) => Xc ij.1 ij.2))
    (IidInit.sa27_path_gen T (fun (ij : Fin N × Fin d) (Xc : EucConfig d N) => Xc ij.1 ij.2) hgen) g
  let Φ : (Fin p → EucConfig d N) → EuclideanSpace ℝ (Fin p) :=
    fun x => WithLp.toLp 2 (fun a => x a (g a).2.1 (g a).2.2)
  have hΦ : Measurable Φ := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a => ?_)
    exact (EuclideanSpace.proj ((g a).2.2)).continuous.measurable.comp
      ((measurable_pi_apply ((g a).2.1)).comp (measurable_pi_apply a))
  have key : ∀ (Yy : Omega → C(Set.Icc (0:ℝ) T, EucConfig d N)) (hYy : Measurable Yy)
      (tup : Omega → Fin p → EucConfig d N) (htup : AEMeasurable tup P)
      (hyt : ∀ᵐ w ∂P, ∀ a, Yy w (g a).1 = tup w a),
      (P.map Yy).map (IidInit.sa27_fd (IidInit.sa27_pathF T
        (fun (ij : Fin N × Fin d) (Xc : EucConfig d N) => Xc ij.1 ij.2)) g) =
        (P.map tup).map Φ := by
    intro Yy hYy tup htup hyt
    rw [Measure.map_map hfd hYy, AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable htup]
    refine Measure.map_congr ?_
    filter_upwards [hyt] with w hw
    show Φ (fun a => Yy w (g a).1) = Φ (tup w)
    congr 1
    funext a
    exact hw a
  have htupX : AEMeasurable (fun w (a : Fin p) => X (u + ((g a).1 : ℝ)).toNNReal w) P :=
    aemeasurable_pi_iff.2 fun a => hm _
  have htupXr : AEMeasurable (fun w (a : Fin p) => X (u + T - ((g a).1 : ℝ)).toNNReal w) P :=
    aemeasurable_pi_iff.2 fun a => hm _
  rw [key Y hYm _ htupX (by filter_upwards [hae] with w hw a using (hw (g a).1).1),
    key Yrev hYrm _ htupXr (by filter_upwards [hae] with w hw a using (hw (g a).1).2)]
  rw [hrev u T hu hT p (fun a => (g a).1)]

end HRS.MS.R26T8A

end
