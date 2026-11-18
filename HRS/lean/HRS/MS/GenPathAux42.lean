import HRS.MS.GenPathAux41
import HRS.Uniform.Q54cAux1

/-!
# S5.6 packet P8a: the law of a continuous `B_m`-valued process is determined by the law of its coordinate array
at a dense sequence of times (OscDual version of `Q54c.toPath_law_eq`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

variable {d : ℕ}

/-- The coordinate array `w ↦ (coord (w (s n)) α)_{n,α}` of a path at a dense sequence of times. -/
def s56PathCoords (m T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) : OscPath d m T → (ℕ × MultiIndex d → ℝ) :=
  fun w i => OscDual.coord (OscPath.at' w (s i.1)) i.2

theorem s56_continuous_coord (m : ℝ) (α : MultiIndex d) :
    Continuous fun F : OscDual d m => OscDual.coord F α := by
  unfold OscDual.coord
  have hl : LipschitzWith 1 fun F : lp (fun _ : MultiIndex d => ℝ) 2 => F α := by
    refine LipschitzWith.of_dist_le_mul fun F G => ?_
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (F - G) α
    simpa using this
  exact hl.continuous

theorem s56_measurable_pathCoords (m T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) :
    Measurable (s56PathCoords (d := d) m T s) := by
  refine measurable_pi_iff.2 fun i => ?_
  have h1 : Continuous fun w : OscPath d m T => OscPath.at' w (s i.1) := by
    have : Continuous fun w : C(Set.Icc (0 : ℝ) T, OscDual d m) => w (s i.1) :=
      continuous_eval_const (s i.1)
    exact this
  exact ((s56_continuous_coord m i.2).comp h1).measurable

theorem s56_pathCoords_injective (m T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s) :
    Function.Injective (s56PathCoords (d := d) m T s) := by
  intro w w' h
  have hpt : ∀ n, OscPath.at' w (s n) = OscPath.at' w' (s n) := by
    intro n
    have hk : ∀ k, OscDual.coord (OscPath.at' w (s n)) k = OscDual.coord (OscPath.at' w' (s n)) k :=
      fun k => congrFun h (n, k)
    refine Subtype.ext (funext fun k => ?_)
    exact hk k
  have hc : Continuous fun t => OscPath.at' w t :=
    (show C(Set.Icc (0 : ℝ) T, OscDual d m) from w).continuous
  have hc' : Continuous fun t => OscPath.at' w' t :=
    (show C(Set.Icc (0 : ℝ) T, OscDual d m) from w').continuous
  have hfun : (fun t => OscPath.at' w t) = fun t => OscPath.at' w' t :=
    hs.equalizer hc hc' (funext hpt)
  exact ContinuousMap.ext fun t => congrFun hfun t

theorem s56_measurableEmbedding_pathCoords (m T : ℝ) (s : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s) :
    MeasurableEmbedding (s56PathCoords (d := d) m T s) := by
  have : PolishSpace (OscPath d m T) := inferInstanceAs (PolishSpace C(Set.Icc (0 : ℝ) T, OscDual d m))
  exact (s56_measurable_pathCoords m T s).measurableEmbedding (s56_pathCoords_injective m T s hs)

theorem s56_pathCoords_windowPathOf {m T : ℝ} (s : ℕ → Set.Icc (0 : ℝ) T) {Ω : Type*}
    (Y : ℝ → Ω → OscDual d m) {ζ : Ω} (h : ContinuousOn (fun t => Y t ζ) (Set.Icc 0 T)) :
    s56PathCoords (d := d) m T s (windowPathOf m T 0 (fun t => Y t ζ)) =
      fun i => OscDual.coord (Y (s i.1) ζ) i.2 := by
  funext i
  unfold s56PathCoords OscPath.at'
  have := s56_wpo_apply (m := m) (T := T) (f := fun t => Y t ζ) h (s i.1)
  rw [this]

theorem s56_path_law_eq {m T : ℝ} (hT : 0 ≤ T) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Y : ℝ → Ω → OscDual d m) (Y' : ℝ → Ω' → OscDual d m)
    (hm : ∀ t, Measurable (Y t)) (hm' : ∀ t, Measurable (Y' t))
    (hc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Y t ζ) (Set.Icc 0 T))
    (hc' : ∀ᵐ ζ ∂P', ContinuousOn (fun t => Y' t ζ) (Set.Icc 0 T))
    (s : ℕ → Set.Icc (0 : ℝ) T) (hs : DenseRange s)
    (hlaw : P.map (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Y (s i.1) ζ) i.2) =
      P'.map (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Y' (s i.1) ζ) i.2)) :
    law P (fun ζ => windowPathOf m T 0 (fun t => Y t ζ)) =
      law P' (fun ζ => windowPathOf m T 0 (fun t => Y' t ζ)) := by
  have hemb := s56_measurableEmbedding_pathCoords (d := d) m T s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  set Ψ₀ : Ω → (ℕ × MultiIndex d → ℝ) := fun ζ i => OscDual.coord (Y (s i.1) ζ) i.2 with hΨ₀
  set Ψ₀' : Ω' → (ℕ × MultiIndex d → ℝ) := fun ζ i => OscDual.coord (Y' (s i.1) ζ) i.2 with hΨ₀'
  have hΨm : Measurable Ψ₀ := measurable_pi_iff.2 fun i => (s56_continuous_coord m i.2).measurable.comp (hm _)
  have hΨm' : Measurable Ψ₀' := measurable_pi_iff.2 fun i => (s56_continuous_coord m i.2).measurable.comp (hm' _)
  have hae : (fun ζ => windowPathOf m T 0 (fun t => Y t ζ)) =ᵐ[P] fun ζ => g (Ψ₀ ζ) := by
    filter_upwards [hc] with ζ h
    have := s56_pathCoords_windowPathOf (d := d) s Y h
    have h2 := congrFun hg (windowPathOf m T 0 (fun t => Y t ζ))
    simp only [Function.comp, id] at h2
    rw [← h2, this]
  have hae' : (fun ζ => windowPathOf m T 0 (fun t => Y' t ζ)) =ᵐ[P'] fun ζ => g (Ψ₀' ζ) := by
    filter_upwards [hc'] with ζ h
    have := s56_pathCoords_windowPathOf (d := d) s Y' h
    have h2 := congrFun hg (windowPathOf m T 0 (fun t => Y' t ζ))
    simp only [Function.comp, id] at h2
    rw [← h2, this]
  unfold law
  rw [Measure.map_congr hae, Measure.map_congr hae']
  have h1 : (fun ζ => g (Ψ₀ ζ)) = g ∘ Ψ₀ := rfl
  have h2 : (fun ζ => g (Ψ₀' ζ)) = g ∘ Ψ₀' := rfl
  rw [h1, h2, ← Measure.map_map hgm hΨm, ← Measure.map_map hgm hΨm', hlaw]

end HRS.MS.GenPath
