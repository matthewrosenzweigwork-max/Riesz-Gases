import HRS.MS.CovMeasAux15

/-!
# S10.1 (worker S101B), part 16: a Borel set of full measure on which `D_τ` is genuinely measurable

`S101Good C m T z G`: `G ⊆ [0,T]` Borel of full measure such that `τ ↦ 1_G(τ) D_τ(u,v)` is measurable for all `u, v ∈ 𝒦`.
`s101_exists_good`: such a `G` exists (countable dense subset of the span of the generators, a.e.-measurable pairings, a Borel null
superset of the exceptional set, density and continuity of the bilinear forms).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ}

open Classical in
/-- `G` is a Borel subset of `[0,T]` of full measure on which `D_τ` is measurable. -/
def S101Good (C : WholeCoeff d) (m T : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (G : Set ℝ) : Prop :=
  MeasurableSet G ∧ G ⊆ Icc 0 T ∧ volume (Icc 0 T \ G) = 0 ∧
    ∀ u v : KSpace d m T, Measurable (fun τ => if τ ∈ G then s101D C m T z τ u v else 0)

theorem s101_exists_good (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) : ∃ G, S101Good C m T z G := by
  classical
  set S : Submodule ℝ (KSpace d m T) := Submodule.span ℝ (s101Gen m T) with hS
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense (↥S)
  set 𝒟 : Set (KSpace d m T) := Subtype.val '' s with h𝒟
  have h𝒟c : 𝒟.Countable := hsc.image _
  have h𝒟S : ∀ u ∈ 𝒟, u ∈ S := by rintro _ ⟨x, _, rfl⟩; exact x.2
  have hSdense : Dense (S : Set (KSpace d m T)) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hS, s101_span_dense hT]
    rfl
  have h𝒟d : Dense 𝒟 := by
    have hdr : DenseRange (Subtype.val : S → KSpace d m T) := by
      unfold DenseRange; rw [Subtype.range_coe]; exact hSdense
    exact hdr.dense_image continuous_subtype_val hsd
  have : Countable ↥𝒟 := h𝒟c.to_subtype
  have hpair : ∀ p : ↥𝒟 × ↥𝒟,
      AEMeasurable (fun τ => s101D C m T z τ p.1 p.2) (volume.restrict (Icc 0 T)) :=
    fun p => s101_D_span_aem A hT (h𝒟S _ p.1.2) (h𝒟S _ p.2.2)
  choose h hhm hhe using hpair
  have hall : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ p : ↥𝒟 × ↥𝒟, s101D C m T z τ p.1 p.2 = h p τ :=
    ae_all_iff.2 hhe
  obtain ⟨B', hBB', hB'm, hB'0⟩ := exists_measurable_superset_of_null (ae_iff.1 hall)
  set G : Set ℝ := Icc 0 T \ B' with hG
  have hGm : MeasurableSet G := measurableSet_Icc.diff hB'm
  have hGsub : G ⊆ Icc 0 T := fun τ hτ => hτ.1
  have hGnull : volume (Icc (0 : ℝ) T \ G) = 0 := by
    have : Icc (0 : ℝ) T \ G = B' ∩ Icc 0 T := by
      ext τ; simp only [hG, mem_diff, mem_inter_iff, not_and, not_not]; tauto
    rw [this]
    rw [Measure.restrict_apply hB'm] at hB'0
    exact hB'0
  refine ⟨G, hGm, hGsub, hGnull, fun u v => ?_⟩
  obtain ⟨x, hx𝒟, hxu⟩ := mem_closure_iff_seq_limit.1 (h𝒟d u)
  obtain ⟨y, hy𝒟, hyv⟩ := mem_closure_iff_seq_limit.1 (h𝒟d v)
  refine measurable_of_tendsto_metrizable (f := fun n τ => if τ ∈ G then s101D C m T z τ (x n) (y n) else 0)
    (fun n => ?_) ?_
  · have : (fun τ => if τ ∈ G then s101D C m T z τ (x n) (y n) else 0) =
        fun τ => if τ ∈ G then h (⟨x n, hx𝒟 n⟩, ⟨y n, hy𝒟 n⟩) τ else 0 := by
      funext τ
      by_cases hτ : τ ∈ G
      · have hτB : τ ∉ B' := hτ.2
        have : ∀ p : ↥𝒟 × ↥𝒟, s101D C m T z τ p.1 p.2 = h p τ := by
          by_contra hcon
          exact hτB (hBB' hcon)
        simp only [hτ, if_true]
        exact this (⟨x n, hx𝒟 n⟩, ⟨y n, hy𝒟 n⟩)
      · simp [hτ]
    rw [this]
    exact Measurable.ite hGm (hhm _) measurable_const
  · refine tendsto_pi_nhds.2 fun τ => ?_
    by_cases hτ : τ ∈ G
    · simp only [hτ, if_true]
      have hcont : Continuous fun p : KSpace d m T × KSpace d m T => s101D C m T z τ p.1 p.2 :=
        (s101D C m T z τ).continuous₂ |>.comp continuous_id
      exact (hcont.tendsto (u, v)).comp (hxu.prodMk_nhds hyv)
    · simp [hτ]

end HRS.MS.CovMeas
