import Mathlib
import HRS.MC.CepN3Aux2
import HRS.MC.CepN1
import HRS.Prob.HilbertMartingale

/-!
# Packet CEPN3, auxiliary 3: Brownian tube independent of `ℱ₀`

For an `ℱ₀`-measurable event `E` of positive probability, a continuous target path `w` and `δ > 0`,
there is an `ℱ_{T'}`-event `F` on which the Brownian path stays `δ`-close to `w` on `[0,T']` such that
`P (E ∩ F) > 0`.  We use the closed tube over a countable dense set of times so that `F` is a countable
intersection, together with `indep_zero_pathSigmaFin` and `cep_N1_bm_tube_proof`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN3

open HRS HRS.MC.CepN4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

lemma cepn3_ofCoords_eq (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (t : ℝ≥0) :
    (fun ω => ofCoords W' t ω) =
      (fun x : Fin N × Fin 1 → ℝ => fun i : Fin N => (WithLp.toLp 2 (fun j : Fin 1 => x (i, j)) : Euc 1)) ∘
        W' t := rfl

lemma cepn3_cont_phi : Continuous
    (fun x : Fin N × Fin 1 → ℝ => fun i : Fin N => (WithLp.toLp 2 (fun j : Fin 1 => x (i, j)) : Euc 1)) := by
  refine continuous_pi fun i => ?_
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => continuous_apply (i, j))

theorem cepn3_tube_inter [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {w : ℝ → Fin N → Euc 1} (hw : Continuous w) (hw0 : w 0 = 0) {T' δ : ℝ} (hT' : 0 < T') (hδ : 0 < δ)
    {E : Set Ω} (hE : MeasurableSet[ℱ 0] E) (hPE : 0 < P E) :
    ∃ F : Set Ω, MeasurableSet[ℱ T'] F ∧
      (∀ ω ∈ F, ∀ t : ℝ≥0, (t : ℝ) ≤ T' → ‖ofCoords W' t ω - w t‖ ≤ δ) ∧ 0 < P (E ∩ F) := by
  classical
  set Φ : (Fin N × Fin 1 → ℝ) → (Fin N → Euc 1) :=
    fun x : Fin N × Fin 1 → ℝ => fun i : Fin N => (WithLp.toLp 2 (fun j : Fin 1 => x (i, j)) : Euc 1) with hΦ
  have hΦc : Continuous Φ := cepn3_cont_phi
  set T'' : ℝ≥0 := Real.toNNReal T' with hT''
  have hT''r : (T'' : ℝ) = T' := Real.coe_toNNReal _ hT'.le
  let m : ℕ → ℝ≥0 := fun n => min (TopologicalSpace.denseSeq ℝ≥0 n) T''
  let F : Set Ω := ⋂ n, {ω | ‖ofCoords W' (m n) ω - w (m n)‖ ≤ δ}
  have hmle : ∀ n, ((m n : ℝ≥0) : ℝ) ≤ T' := fun n => by
    rw [← hT''r]; exact_mod_cast min_le_right _ _
  have hFmeas_n : ∀ n, MeasurableSet[ℱ T'] {ω | ‖ofCoords W' (m n) ω - w (m n)‖ ≤ δ} := fun n => by
    have h1 : Measurable[ℱ (m n)] (fun ω => ofCoords W' (m n) ω) :=
      hΦc.measurable.comp (hW'.adapted (m n))
    have hg : Continuous fun x : Fin N → Euc 1 => ‖x - w (m n)‖ :=
      (continuous_id.sub continuous_const).norm
    have h2 : Measurable[ℱ (m n)] (fun ω => ‖ofCoords W' (m n) ω - w (m n)‖) :=
      hg.measurable.comp h1
    have h3 : Measurable[ℱ T'] (fun ω => ‖ofCoords W' (m n) ω - w (m n)‖) :=
      h2.mono (ℱ.mono (hmle n)) le_rfl
    exact h3 measurableSet_Iic
  refine ⟨F, @MeasurableSet.iInter _ _ (ℱ T') _ _ hFmeas_n, ?_, ?_⟩
  · intro ω hω t ht
    -- continuity + density
    have hcont : Continuous fun s : ℝ≥0 => ‖ofCoords W' (min s T'') ω - w (min s T'')‖ := by
      have h1 : Continuous fun s : ℝ≥0 => ofCoords W' (min s T'') ω :=
        hΦc.comp ((hW'.cont ω).comp (continuous_id.min continuous_const))
      have h2 : Continuous fun s : ℝ≥0 => w ((min s T'' : ℝ≥0) : ℝ) :=
        hw.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
      exact (h1.sub h2).norm
    have hclosed : IsClosed {s : ℝ≥0 | ‖ofCoords W' (min s T'') ω - w (min s T'')‖ ≤ δ} :=
      isClosed_le hcont continuous_const
    have hsub : Set.range (TopologicalSpace.denseSeq ℝ≥0) ⊆
        {s : ℝ≥0 | ‖ofCoords W' (min s T'') ω - w (min s T'')‖ ≤ δ} := by
      rintro _ ⟨n, rfl⟩
      exact Set.mem_iInter.1 hω n
    have hall : ∀ s : ℝ≥0, ‖ofCoords W' (min s T'') ω - w (min s T'')‖ ≤ δ := by
      intro s
      have : s ∈ closure (Set.range (TopologicalSpace.denseSeq ℝ≥0)) := by
        rw [(TopologicalSpace.denseRange_denseSeq ℝ≥0).closure_range]; trivial
      exact closure_minimal hsub hclosed this
    have htT : t ≤ T'' := by
      rw [← NNReal.coe_le_coe, hT''r]; exact ht
    have := hall t
    have e1 : min t T'' = t := min_eq_left htT
    have e2 : min (t : ℝ) (T'' : ℝ) = t := min_eq_left (NNReal.coe_le_coe.2 htT)
    simpa only [e1, e2] using this
  · -- positivity via independence
    set M : Finset ℝ≥0 → MeasurableSpace Ω := fun T => pathSigmaFin W' T with hM
    have hMle : ∀ T, M T ≤ mΩ := fun T =>
      iSup₂_le fun τ _ => (((hW'.adapted τ).mono (ℱ.le _) le_rfl)).comap_le
    have hind : Indep (⨆ T, M T) (ℱ 0) P :=
      indep_iSup_of_directed_le (fun T => (indep_zero_pathSigmaFin hW' T).symm) hMle (ℱ.le 0)
        (fun T T' => ⟨T ∪ T', pathSigmaFin_mono Finset.subset_union_left,
          pathSigmaFin_mono Finset.subset_union_right⟩)
    have hFm : MeasurableSet[⨆ T, M T] F := by
      refine @MeasurableSet.iInter _ _ (⨆ T, M T) _ _ fun n => ?_
      have h1 : Measurable[MeasurableSpace.comap (W' (m n)) inferInstance] (W' (m n)) :=
        comap_measurable _
      have h1' : Measurable[⨆ T, M T] (W' (m n)) :=
        h1.mono (le_iSup_of_le {m n} (le_iSup₂_of_le (f := fun τ (_ : τ ∈ ({m n} : Finset ℝ≥0)) =>
          MeasurableSpace.comap (W' τ) inferInstance) (m n) (Finset.mem_singleton_self _) le_rfl)) le_rfl
      have hg : Continuous fun x : Fin N → Euc 1 => ‖x - w (m n)‖ :=
        (continuous_id.sub continuous_const).norm
      have h2 : Measurable[⨆ T, M T] (fun ω => ‖ofCoords W' (m n) ω - w (m n)‖) :=
        hg.measurable.comp (hΦc.measurable.comp h1')
      exact h2 measurableSet_Iic
    have hEF : P (E ∩ F) = P E * P F := by
      have := (Indep_iff _ _ _).1 hind.symm E F hE hFm
      exact this
    have hFpos : 0 < P F := by
      have hW : IsVectorBrownian P (ofCoords W') := isVectorBrownian_of_isBrownianFiltration P ℱ W' hW'
      have hN1 := HRS.MC.CepN1.cep_N1_bm_tube_proof hW hw hw0 hT' hδ
      refine lt_of_lt_of_le hN1 (measure_mono ?_)
      intro ω hω
      refine Set.mem_iInter.2 fun n => ?_
      exact (hω (m n) (hmle n)).le
    rw [hEF]
    exact ENNReal.mul_pos hPE.ne' hFpos.ne'

end HRS.MC.CepN3
