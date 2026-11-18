import HRS.MS.FinNoiseAux3

/-!
# S8.6 `finite_noise`, packet P1c (S86): measurability of the feature in `(r, x)`

`s86_feat_meas_r`: for fixed `x`, `r ↦ gradFeature C m Hz i (max r 0) x ∈ 𝒦` is Borel;
(The joint statement `s86_feat_meas` on `ℝ × ℝ^d` via Carathéodory is still to be added, see HANDOFF_S86.md.)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole HRS.MS.S52B

variable {d : ℕ} {m : ℝ} (C : WholeCoeff d) {Hz : ℝ}

/-- Pairing of a test vector with the feature, in terms of a measurable representative `g` of the profile. -/
theorem s86_pair_eq (h : S86Feat C m Hz) (hHz : 0 ≤ Hz) (i : Fin d) (x : Euc d)
    (g : ℝ → OscDual d m)
    (hg : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Icc (0 : ℝ) Hz →
      (if 0 < s then s86_prof C m i x s else 0) = g s)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) Hz) (b : KSpace d m Hz) :
    inner ℝ b (gradFeature C m Hz i r x) =
      inner ℝ b.A₀ (ellVec m fun α => gradComp i (oscTestFun m α) x) +
      (∫ t in Icc (0 : ℝ) Hz, inner ℝ (b.A' t) (if r < t then g (t - r) else 0)) +
      inner ℝ b.B (ellVec m fun α => gradComp i (oscTestFun m α) x) := by
  classical
  have hmem := (h.feat i r hr x).2.2
  have hfe : gradFeature C m Hz i r x = KSpace.mk (ellVec m fun α => gradComp i (oscTestFun m α) x)
      (hmem.toLp _) (ellVec m fun α => gradComp i (oscTestFun m α) x) := by
    unfold gradFeature orbitFeature
    dsimp only
    rw [dif_pos hmem]
  rw [hfe, s86_inner_mk]
  congr 2
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  have h1 := s86_orbit_ae C Hz h i x r hr
  have h2 : ∀ᵐ t ∂(volume : Measure ℝ), (t - r) ∈ Icc (0 : ℝ) Hz →
      (if 0 < t - r then s86_prof C m i x (t - r) else 0) = g (t - r) :=
    (measurePreserving_sub_right (volume : Measure ℝ) r).quasiMeasurePreserving.ae hg
  have h3 : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) Hz)),
      (if r < t then s86_prof C m i x (t - r) else 0) = (if r < t then g (t - r) else 0) := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h2] with t ht htI
    by_cases hrt : r < t
    · have hs : (t - r) ∈ Icc (0 : ℝ) Hz := ⟨by linarith, by linarith [htI.2, hr.1]⟩
      have := ht hs
      simp only [hrt, ite_true]
      rwa [if_pos (by linarith : (0 : ℝ) < t - r)] at this
    · simp [hrt]
  filter_upwards [hmem.coeFn_toLp, h1, h3] with t e1 e2 e3
  rw [e1, e2, e3]

theorem s86_feat_meas_r (h : S86Feat C m Hz) (hHz : 0 ≤ Hz) (i : Fin d) (x : Euc d) :
    Measurable fun r : ℝ => gradFeature C m Hz i (max r 0) x := by
  classical
  obtain ⟨ι, hι, bb, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := KSpace d m Hz)
  have := hι
  -- a measurable representative of the profile
  have hp : AEStronglyMeasurable (fun s : ℝ => if 0 < s then s86_prof C m i x s else 0)
      (volume.restrict (Icc (0 : ℝ) Hz)) := by
    have h0 : MemLp _ 2 (volume.restrict (Icc (0 : ℝ) Hz)) := (h.feat i 0 ⟨le_rfl, hHz⟩ x).2.2
    have := s86_orbit_ae C Hz h i x 0 ⟨le_rfl, hHz⟩
    refine (h0.aestronglyMeasurable.congr this).congr ?_
    simp
  set g : ℝ → OscDual d m := hp.mk _ with hgdef
  have hgm : Measurable g := hp.stronglyMeasurable_mk.measurable
  have hg : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Icc (0 : ℝ) Hz →
      (if 0 < s then s86_prof C m i x s else 0) = g s := by
    exact (ae_restrict_iff' measurableSet_Icc).1 hp.ae_eq_mk
  refine measurable_of_inner_basis bb fun j => ?_
  set b : KSpace d m Hz := bb j with hb
  set Ψ : ℝ → ℝ := fun r => inner ℝ b.A₀ (ellVec m fun α => gradComp i (oscTestFun m α) x) +
      (∫ t in Icc (0 : ℝ) Hz, inner ℝ (b.A' t) (if r < t then g (t - r) else 0)) +
      inner ℝ b.B (ellVec m fun α => gradComp i (oscTestFun m α) x) with hΨ
  have key : ∀ r : ℝ, inner ℝ b (gradFeature C m Hz i (max r 0) x) = Ψ (min (max r 0) Hz) := by
    intro r
    by_cases hr : Hz ≤ max r 0
    · rw [s86_feat_clamp C m Hz i x _ hr, min_eq_right hr]
      exact s86_pair_eq C h hHz i x g hg Hz ⟨hHz, le_rfl⟩ b
    · rw [min_eq_left (not_le.1 hr).le]
      exact s86_pair_eq C h hHz i x g hg _ ⟨le_max_right _ _, (not_le.1 hr).le⟩ b
  simp only [key]
  have hAp : Measurable (b.A' : ℝ → OscDual d m) := (Lp.stronglyMeasurable b.A').measurable
  have hint : Measurable (Function.uncurry fun (r t : ℝ) =>
      inner ℝ (b.A' t) (if r < t then g (t - r) else 0)) := by
    have hF : Measurable fun p : ℝ × ℝ => if p.1 < p.2 then g (p.2 - p.1) else 0 :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
        (hgm.comp (measurable_snd.sub measurable_fst)) measurable_const
    exact (hAp.comp measurable_snd).inner hF
  have hI := (hint.stronglyMeasurable).integral_prod_right (ν := volume.restrict (Icc (0 : ℝ) Hz))
  have hΨm : Measurable Ψ := (measurable_const.add hI.measurable).add measurable_const
  exact hΨm.comp ((measurable_id.max measurable_const).min measurable_const)

end HRS.MS.FinNoise
