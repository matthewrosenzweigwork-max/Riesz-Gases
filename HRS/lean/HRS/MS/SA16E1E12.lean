import HRS.MS.SA16E1E12a

/-!
# S.A.16 E12: joint measurability of the inverse of `charFlow`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.Whole.AppendixALemmas

theorem e12_sInf_eq_iff (S : Set ℕ) (k : ℕ) :
    sInf S = k ↔ (k ∈ S ∧ ∀ m < k, m ∉ S) ∨ (S = ∅ ∧ k = 0) := by
  constructor
  · intro h
    by_cases hS : S.Nonempty
    · left
      subst h
      exact ⟨Nat.sInf_mem hS, fun m hm => Nat.notMem_of_lt_sInf hm⟩
    · right
      rw [Set.not_nonempty_iff_eq_empty] at hS
      subst hS
      exact ⟨rfl, by simpa using h.symm⟩
  · rintro (⟨hk, hlt⟩ | ⟨rfl, rfl⟩)
    · refine le_antisymm (Nat.sInf_le hk) ?_
      by_contra hlt'
      push Not at hlt'
      exact hlt _ hlt' (Nat.sInf_mem ⟨k, hk⟩)
    · simp

/-- E12: a separate measurability producer for the inverse flow.
Picard iterations give the forward map; rational inverse approximations
and the uniform inverse Lipschitz bound give this joint map. -/
theorem charFlow_inverse_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (d : ℕ) (hd : 1 ≤ d) (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ)
    (hW : IsBrownianFiltration P ℱ W) (B ν : ℝ) (hν : 0 ≤ ν)
    (b : ℝ → Euc d → Euc d) (hb : DriftBounds d 1 B b) :
    Measurable (fun q : (ℝ × Ω) × Euc d =>
      Function.invFun (charFlow d b ν (fun r => W r q.1.2) q.1.1) q.2) := by
  classical
  have hk : 1 ≤ 1 := le_rfl
  -- forward map: joint measurability in `(t, ω)` at a fixed point
  have hfwd : ∀ r : Euc d, Measurable (fun p : ℝ × Ω =>
      charFlow d b ν (fun s => W s p.2) p.1 r) := by
    intro r
    have hu : Measurable (Function.uncurry (fun (t : ℝ) (u : Ω) =>
        charFlow d b ν (fun s => W s u) t r)) := by
      refine measurable_uncurry_of_continuous_of_measurable (fun u => ?_) (fun t => ?_)
      · exact e1_flow_cont hk hb ν (hW.cont u) r
      · have := measurable_picardLim hW (fun r y => -b r y) (e1_isLip hk hb)
          (e1Sig d ν) (Y₀ := fun _ => r) (fun _ => measurable_const) t
        exact this.mono (ℱ.le t) le_rfl
    exact hu
  let D : ℕ → Euc d := TopologicalSpace.denseSeq (Euc d)
  have hD : DenseRange D := TopologicalSpace.denseRange_denseSeq (Euc d)
  let g : ℕ → (ℝ × Ω) × Euc d → Euc d := fun n q =>
    charFlow d b ν (fun s => W s q.1.2) q.1.1 (D n) - q.2
  have hg : ∀ n, Measurable (g n) := fun n =>
    ((hfwd (D n)).comp measurable_fst).sub measurable_snd
  let cond : ℕ → ℕ → (ℝ × Ω) × Euc d → Prop := fun N n q => ‖g n q‖ < 1 / ((N : ℝ) + 1)
  have hcond : ∀ N n, MeasurableSet {q | cond N n q} := fun N n =>
    measurableSet_lt (hg n).norm measurable_const
  let idx : ℕ → (ℝ × Ω) × Euc d → ℕ := fun N q => sInf {n | cond N n q}
  have hidx : ∀ N, Measurable (idx N) := by
    intro N
    refine measurable_to_countable' fun k => ?_
    have : idx N ⁻¹' {k} = ({q | cond N k q} ∩ ⋂ m, ⋂ (_ : m < k), {q | ¬ cond N m q}) ∪
        ({q | k = 0} ∩ ⋂ m, {q | ¬ cond N m q}) := by
      ext q
      simp only [mem_preimage, mem_singleton_iff, idx, e12_sInf_eq_iff, mem_union, mem_inter_iff,
        mem_setOf_eq, mem_iInter, Set.eq_empty_iff_forall_notMem]
      tauto
    rw [this]
    refine ((hcond N k).inter (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
      (hcond N m).compl)).union ?_
    refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun m => (hcond N m).compl)
    by_cases hk0 : k = 0
    · simp [hk0]
    · simp [hk0]
  let IN : ℕ → (ℝ × Ω) × Euc d → Euc d := fun N q => D (idx N q)
  have hIN : ∀ N, Measurable (IN N) := fun N =>
    (measurable_from_nat (f := D)).comp (hidx N)
  refine measurable_of_tendsto_metrizable (f := IN) hIN (tendsto_pi_nhds.2 fun q => ?_)
  -- pointwise convergence
  obtain ⟨hbij, hXc, L, hL0, hL⟩ := e12_inv_lip d hd hb hν (hW.cont q.1.2) (hW.zero q.1.2) q.1.1
  set X := charFlow d b ν (fun s => W s q.1.2) q.1.1 with hX
  have hinj : Function.Injective X := hbij.1
  set y0 : Euc d := Function.invFun X q.2 with hy0
  have hXy : X y0 = q.2 := Function.invFun_eq (hbij.2 q.2)
  have hex : ∀ N : ℕ, ∃ n, cond N n q := by
    intro N
    have hε : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hXc.continuousAt _ hε
    obtain ⟨n, hn⟩ := hD.exists_dist_lt y0 hδ
    refine ⟨n, ?_⟩
    have := hδ' (x := D n) (by rwa [dist_comm])
    rw [hXy] at this
    simpa [cond, g, dist_eq_norm, hX] using this
  have hbound : ∀ N : ℕ, ‖IN N q - y0‖ ≤ L * (1 / ((N : ℝ) + 1)) := by
    intro N
    have hc : cond N (idx N q) q := Nat.sInf_mem (hex N)
    have h1 : ‖X (D (idx N q)) - q.2‖ < 1 / ((N : ℝ) + 1) := by
      simpa [cond, g, hX] using hc
    have h2 : IN N q = Function.invFun X (X (D (idx N q))) :=
      (Function.leftInverse_invFun hinj _).symm
    calc ‖IN N q - y0‖ = ‖Function.invFun X (X (D (idx N q))) - Function.invFun X q.2‖ := by
          rw [← h2]
      _ ≤ L * ‖X (D (idx N q)) - q.2‖ := hL _ _
      _ ≤ L * (1 / ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left h1.le hL0
  have hlim : Tendsto (fun N : ℕ => L * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul L
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun N => norm_nonneg _) hbound hlim)

end HRS.Whole.AppendixA.Phase2SA16Evolution
