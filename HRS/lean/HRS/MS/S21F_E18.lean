import HRS.MS.S21F_E10
import HRS.MS.S21F_E11
import HRS.MS.S21F_E12

/-!
# S21F, packet R26-T3.E18: global filtered modification in the full singularity range

Given a family of strong solutions (every horizon) whose original `.adapted` field is only ordinary measurability, we
construct on the lifted Brownian filtration (frozen at negative times) the version `X' t = lim_M Ys M t` of the globally
Lipschitz cutoff solutions.  Each `Ys M` is adapted and continuous, hence progressive; the limit (`limUnder`, measurable
without any convergence assumption) is adapted and progressive; by `r26t3_cutoff_identification` on each integer horizon
it is a.s. EQUAL to `X` at every time simultaneously, so every strong-solution clause transfers.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

/-- continuity on `[0,t]` for every `t ≥ 0` gives continuity of `s ↦ f (max s 0)` on `ℝ`. -/
theorem s21f_cont_max {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (h : ∀ t : ℝ, 0 ≤ t → ContinuousOn f (Set.Icc 0 t)) : Continuous fun s : ℝ => f (max s 0) := by
  have hI : ContinuousOn f (Set.Ici 0) := by
    intro x hx
    have hx' : (0 : ℝ) ≤ x := hx
    have := (h (x + 1) (by linarith)) x ⟨hx', by linarith⟩
    refine this.mono_of_mem_nhdsWithin (mem_nhdsWithin.2 ⟨Set.Iio (x + 1), isOpen_Iio,
      by simp, fun y hy => ⟨hy.2, hy.1.le⟩⟩)
  exact hI.comp_continuous (continuous_id.max continuous_const) fun s => Set.mem_Ici.2 (le_max_right _ _)

theorem s21f_shift_max {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) (t : ℝ) :
    HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ (max t 0) = HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ t := by
  simp [HRS.MP.SelfSimP4Impl.p4r_shiftFil_apply]

theorem s21f_shift_neg {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) {t : ℝ} (ht : t ≤ 0) :
    HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ t = HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ 0 := by
  simp [HRS.MP.SelfSimP4Impl.p4r_shiftFil_apply, max_eq_right ht]

theorem r26t3_global_filtered_version (d N : ℕ) (s a β : ℝ) (hd : 2 ≤ d)
    (hs : 0 ≤ s) (hsd : s < (d : ℝ)) (ha : 0 < a) (hβ : 0 < β)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω t => W t ω) P)
    (hX : ∀ H : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) H X₀ W X) :
    ∃ (ℱ : Filtration ℝ mΩ) (Wc : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
      (X' : ℝ≥0 → Ω → EucConfig d N),
      IsWholeFilteredSolution P ℱ Wc W X' ∧
      (∀ t : ℝ, t ≤ 0 → ℱ t = ℱ 0) ∧
      (∀ H : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) H X₀ W X') ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, X' t ω = X t ω) := by
  have _ := hd
  have _ := hsd
  have hind' : IndepFun (X 0) (fun ζ t => W t ζ) P :=
    hind.congr ((hX 0).init.mono fun ζ h => h.symm) Filter.EventuallyEq.rfl
  obtain ⟨ℱ, W', hB, hX0, hcoord⟩ := r26t3_brownian_lift P (X 0) ((hX 0).adapted 0) W hW hind'
  obtain ⟨Ys, hYs, hmeas, -⟩ := r26t3_cutoff_laws (N := N) s a β hs ha hβ P ℱ W' hB (X 0) hX0
  obtain ⟨B, hPot⟩ := HRS.MS.S81G.s81g_pot (d := d) a
  have hae : ∀ n : ℕ, ∀ᵐ ζ ∂P, ∀ᶠ M : ℕ in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ (n : ℝ) + 1 →
      Ys M (t : ℝ) ζ = X t ζ := fun n =>
    r26t3_cutoff_identification (quadraticGradientDyn d s a β) rfl hPot (by positivity)
      (hX ((n : ℝ) + 1)) hB hcoord (gM := r26t3_regKernel d s)
      (fun M => HRS.MS.MfeConf.sb1kM_isKernel (d := d) s hs M) hYs
  have hall := ae_all_iff.2 hae
  set X' : ℝ≥0 → Ω → EucConfig d N := fun t ζ => limUnder atTop (fun M => Ys M (t : ℝ) ζ) with hX'
  have heq : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, X' t ζ = X t ζ := by
    filter_upwards [hall] with ζ h t
    obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
    have hev : ∀ᶠ M : ℕ in atTop, Ys M (t : ℝ) ζ = X t ζ :=
      (h n).mono fun M hM => hM t (by linarith)
    exact (tendsto_const_nhds.congr' (hev.mono fun M hM => hM.symm)).limUnder_eq
  -- measurability and progressive measurability
  have hadapt : ∀ t : ℝ≥0, Measurable[HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ t] (X' t) := fun t => by
    let _ := HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ t
    exact (StronglyMeasurable.limUnder (fun M => ((hYs M).adapted (t : ℝ)).stronglyMeasurable)).measurable
  have hZ : ∀ M : ℕ, IsProgressive (HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ)
      (fun (t : ℝ) ζ => Ys M (max t 0) ζ) := fun M => by
    refine (StronglyAdapted.isStronglyProgressive_of_continuous (fun t => ?_) (fun ζ => ?_)).isProgressive
    · have h := (hYs M).adapted (max t 0)
      rw [s21f_shift_max] at h
      exact h.stronglyMeasurable
    · exact s21f_cont_max fun t ht => (hYs M).cont ζ t ht (WithTop.coe_lt_top t)
  have hprog : IsProgressive (HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ) (ofNNRealTime X') := by
    intro i
    let _ : MeasurableSpace (Set.Iic i × Ω) :=
      Subtype.instMeasurableSpace.prod (HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ i)
    have : (fun p : Set.Iic i × Ω => ofNNRealTime X' (p.1 : ℝ) p.2) =
        fun p => limUnder atTop (fun M => Ys M (max (p.1 : ℝ) 0) p.2) := by
      funext p
      simp only [ofNNRealTime_apply, hX', Real.coe_toNNReal']
    rw [this]
    exact (StronglyMeasurable.limUnder (fun M => (hZ M i).stronglyMeasurable)).measurable
  have hF : IsWholeFilteredSolution P (HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ) W' W X' :=
    ⟨HRS.MP.SelfSimP4Impl.p4r_shiftFil_brownian hB, hcoord, hadapt, hprog⟩
  refine ⟨HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ, W', X', hF, fun t ht => s21f_shift_neg ℱ ht,
    fun H => ?_, heq⟩
  have hXH := hX H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [heq, hXH.init] with ζ h1 h2
    rw [h1, h2]
  · filter_upwards [heq, hXH.eqn] with ζ h1 h2
    simpa only [h1] using h2
  · filter_upwards [heq, hXH.cont] with ζ h1 h2
    simpa only [h1] using h2
  · exact fun t => (hadapt t).mono ((HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ).le _) le_rfl
  · filter_upwards [heq, hXH.no_collision] with ζ h1 h2
    simpa only [h1] using h2

end HRS.MS.R26T3
