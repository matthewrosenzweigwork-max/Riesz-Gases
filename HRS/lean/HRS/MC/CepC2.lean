import HRS.MC.CepC1

/-!
# Packet CEPC2: noncollision of a contact flow on `[0,T]` is non-explosion of the maximal solution

Both directions use `cep_C1_agree_until_contact_proof` (agreement before the first contact) and continuity of
`X`; `(→)` uses the collision alternative `hcol` at the explosion time, `(←)` the continuity of `Y` on `[0,τ)`.
This file does not import the spec file `HRS/MC/CepaSpec.lean`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepC2

open HRS HRS.MC.CepC1

section Det

variable {Ω : Type*} {d N : ℕ}

/-- Deterministic core of `(←)`: if `Y` is continuous on `[0,τ)` and agrees with `X` before the first contact,
and `T < τ`, then `X` has no contact on `[0,T]`. -/
theorem cepc2_noncollision_det {X : ℝ≥0 → Ω → Config d N} {Y : ℝ → Ω → (Fin N → Euc d)}
    {τ : Ω → WithTop ℝ} {T : ℝ} (ω : Ω)
    (hX0 : X 0 ω ∉ collisionSet d N)
    (hXc : ∀ i, Continuous fun t => X t ω i)
    (hag : ∀ σ : WithTop ℝ, cep_NoContactBefore X ω σ → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (((t : ℝ)) : WithTop ℝ) < σ → (((t : ℝ)) : WithTop ℝ) < τ ω →
        X t ω = fun i => Torus.mk (Y (t : ℝ) ω i))
    (hYc : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ ω → ContinuousOn (fun s => Y s ω) (Set.Icc 0 t))
    (hYm : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ ω → Y t ω ∈ liftedFree d N)
    (hT : ((T : ℝ) : WithTop ℝ) < τ ω) :
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet d N := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨t1, ht1, hc1⟩ := hcon
  set S : Set ℝ≥0 := {t | (t : ℝ) ≤ T ∧ X t ω ∈ collisionSet d N} with hS
  have hXcont : Continuous fun t : ℝ≥0 => X t ω := continuous_pi hXc
  have hSc : IsClosed S := by
    have h1 : IsClosed {t : ℝ≥0 | (t : ℝ) ≤ T} := isClosed_le NNReal.continuous_coe continuous_const
    exact h1.inter ((isClosed_collisionSet d N).preimage hXcont)
  have hSne : S.Nonempty := ⟨t1, ht1, hc1⟩
  set ts : ℝ≥0 := sInf S with hts_def
  have hts : ts ∈ S := hSc.csInf_mem hSne (OrderBot.bddBelow S)
  have hlt : ∀ t, t < ts → X t ω ∉ collisionSet d N := fun t ht hc => by
    have : ts ≤ t := csInf_le (OrderBot.bddBelow S)
      ⟨le_trans (NNReal.coe_le_coe.2 ht.le) hts.1, hc⟩
    exact absurd ht (not_lt.2 this)
  have hts0 : ts ≠ 0 := fun h => by
    rw [h] at hts
    exact hX0 hts.2
  have hnc : cep_NoContactBefore X ω (((ts : ℝ)) : WithTop ℝ) := fun t ht =>
    hlt t (by exact_mod_cast ht)
  have hτ : ∀ t : ℝ≥0, (t : ℝ) ≤ T → (((t : ℝ)) : WithTop ℝ) < τ ω := fun t ht =>
    lt_of_le_of_lt (by exact_mod_cast ht) hT
  have hag' : ∀ t : ℝ≥0, t < ts → X t ω = fun i => Torus.mk (Y (t : ℝ) ω i) := fun t ht =>
    hag _ hnc t (le_trans (NNReal.coe_le_coe.2 ht.le) hts.1) (by exact_mod_cast ht)
      (hτ t (le_trans (NNReal.coe_le_coe.2 ht.le) hts.1))
  have hYts := hYc (ts : ℝ) ts.2 (hτ ts hts.1)
  have hg : ContinuousWithinAt (fun t : ℝ≥0 => fun i => Torus.mk (Y (t : ℝ) ω i)) (Set.Iio ts) ts := by
    have h1 : ContinuousOn (fun t : ℝ≥0 => Y (t : ℝ) ω) (Set.Iic ts) :=
      hYts.comp NNReal.continuous_coe.continuousOn
        (fun t ht => ⟨t.2, NNReal.coe_le_coe.2 ht⟩)
    have h2 := (continuous_mkPi d N).comp_continuousOn h1
    exact (h2.continuousWithinAt (Set.mem_Iic.2 le_rfl)).mono Set.Iio_subset_Iic_self
  have hf : ContinuousWithinAt (fun t : ℝ≥0 => X t ω) (Set.Iio ts) ts :=
    hXcont.continuousAt.continuousWithinAt
  haveI : (𝓝[<] ts).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 hts0⟩
  have heq : (fun t : ℝ≥0 => X t ω) =ᶠ[𝓝[<] ts] fun t : ℝ≥0 => fun i => Torus.mk (Y (t : ℝ) ω i) :=
    eventually_nhdsWithin_of_forall fun t ht => hag' t ht
  have hXts : X ts ω = fun i => Torus.mk (Y (ts : ℝ) ω i) :=
    tendsto_nhds_unique_of_eventuallyEq hf hg heq
  exact hYm (ts : ℝ) ts.2 (hτ ts hts.1) (hXts ▸ hts.2)

/-- Deterministic core of `(→)`. -/
theorem cepc2_explosion_det {X : ℝ≥0 → Ω → Config d N} {Y : ℝ → Ω → (Fin N → Euc d)}
    {τ : Ω → WithTop ℝ} {T : ℝ} (ω : Ω)
    (hnc : ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet d N)
    (hXc : ∀ i, Continuous fun t => X t ω i)
    (hag : ∀ σ : WithTop ℝ, cep_NoContactBefore X ω σ → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (((t : ℝ)) : WithTop ℝ) < σ → (((t : ℝ)) : WithTop ℝ) < τ ω →
        X t ω = fun i => Torus.mk (Y (t : ℝ) ω i))
    (hτpos : 0 < τ ω)
    (hcol : τ ω < ⊤ → ∀ ε : ℝ, 0 < ε → ∀ t₀ : ℝ, 0 ≤ t₀ → (t₀ : WithTop ℝ) < τ ω →
      ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ω ∧
        ∃ i j : Fin N, i ≠ j ∧ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < ε) :
    ((T : ℝ) : WithTop ℝ) < τ ω := by
  by_contra hnot
  push_neg at hnot
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hnot
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hne
  have hsT : s ≤ T := by rw [← hs] at hnot; exact_mod_cast hnot
  have hs0 : 0 < s := by
    have := hτpos
    rw [← hs] at this
    exact_mod_cast this
  set sn : ℝ≥0 := s.toNNReal with hsn_def
  have hsn : (sn : ℝ) = s := Real.coe_toNNReal _ hs0.le
  have hnc' : cep_NoContactBefore X ω (s : WithTop ℝ) := fun t ht => hnc t (by
    have : (t : ℝ) < s := by exact_mod_cast ht
    linarith)
  have hag' : ∀ t : ℝ≥0, (t : ℝ) < s → X t ω = fun i => Torus.mk (Y (t : ℝ) ω i) := fun t ht =>
    hag _ hnc' t (by linarith) (by exact_mod_cast ht) (by rw [← hs]; exact_mod_cast ht)
  have hXsn : X sn ω ∉ collisionSet d N := hnc sn (by rw [hsn]; exact hsT)
  have hne' : ∀ i j : Fin N, i ≠ j → X sn ω i ≠ X sn ω j := fun i j hij h => hXsn ⟨i, j, hij, h⟩
  have hpos : ∀ i j : Fin N, i ≠ j → 0 < Torus.tdist (X sn ω i) (X sn ω j) / 2 := fun i j hij =>
    half_pos (Torus.tdist_pos_of_ne (hne' i j hij))
  -- a uniform separation level `ε`
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j : Fin N, i ≠ j →
      ε < Torus.tdist (X sn ω i) (X sn ω j) / 2 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun ε h => (h hij).elim
    · exact ((gt_mem_nhds (hpos i j hij)).filter_mono nhdsWithin_le_nhds).mono fun ε h _ => h
  obtain ⟨ε, hε, hε0⟩ := (hev.and eventually_mem_nhdsWithin).exists
  have hε0' : 0 < ε := hε0
  -- time-continuity of the gaps
  have hevt : ∀ᶠ t in 𝓝 sn, ∀ i j : Fin N, i ≠ j →
      Torus.tdist (X sn ω i) (X sn ω j) / 2 < Torus.tdist (X t ω i) (X t ω j) := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun t h => (h hij).elim
    · have hc := Torus.continuous_tdist_comp (hXc i) (hXc j)
      have hlt : Torus.tdist (X sn ω i) (X sn ω j) / 2 < Torus.tdist (X sn ω i) (X sn ω j) :=
        half_lt_self (Torus.tdist_pos_of_ne (hne' i j hij))
      exact (Filter.Tendsto.eventually hc.continuousAt (lt_mem_nhds hlt)).mono fun t h _ => h
  obtain ⟨δ, hδ, hδt⟩ := Metric.eventually_nhds_iff.1 hevt
  obtain ⟨t, ht0, htτ, i, j, hij, htd⟩ := hcol (by rw [← hs]; exact WithTop.coe_lt_top _) ε hε0'
    (max 0 (s - δ)) (le_max_left _ _)
    (by rw [← hs]; exact_mod_cast max_lt hs0 (by linarith))
  have hts : t < s := by rw [← hs] at htτ; exact_mod_cast htτ
  have ht0' : 0 ≤ t := le_trans (le_max_left _ _) ht0.le
  have hty : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht0'
  have hdist : dist t.toNNReal sn < δ := by
    rw [NNReal.dist_eq, hty, hsn, abs_sub_comm, abs_of_pos (by linarith)]
    have := lt_of_le_of_lt (le_max_right 0 (s - δ)) ht0
    linarith
  have h1 := hδt hdist i j hij
  rw [hag' t.toNNReal (by rw [hty]; exact hts), hty] at h1
  have h2 := hε i j hij
  linarith

end Det

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

/-- **C2 (noncollision of a contact flow on `[0,T]` is non-explosion of the maximal solution)**. -/
theorem cep_C2_noncollision_iff_nonexplosion_proof [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
    (hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z))
    {T : ℝ} (hT : 0 ≤ T) {X₀ : Ω → Config d N} (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet d N)
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hW : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j) (hW'c : ∀ ω, Continuous fun t => W' t ω)
    (hX : IsContactStrongSolution P D T X₀ W X) (hXc : ∀ᵐ ω ∂P, ∀ i, Continuous fun t => X t ω i)
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    (hY₀ : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω)
    (hcol : ∀ᵐ ω ∂P, τ ω < ⊤ → ∀ ε : ℝ, 0 < ε → ∀ t₀ : ℝ, 0 ≤ t₀ → (t₀ : WithTop ℝ) < τ ω →
      ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ω ∧
        ∃ i j : Fin N, i ≠ j ∧ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < ε) :
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet d N) ↔
      ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) < τ ω := by
  have hC1 := cep_C1_agree_until_contact_proof hb hW hW'c hX hY hY₀
  constructor
  · intro h
    filter_upwards [h, hC1, hcol, hXc] with ω hω hag hc hXω
    exact cepc2_explosion_det ω hω hXω hag (hY.pos ω) hc
  · intro h
    filter_upwards [h, hC1, hdist, hX.init, hXc, hY.sol.isPathSolution] with ω hTω hag hd hi hXω hps
    exact cepc2_noncollision_det ω (by rw [hi]; exact hd) hXω hag
      (fun t ht htτ => (hps.2 t ht htτ).1) (fun t ht htτ => hY.mem ω t ht htτ) hTω

end Main

end HRS.MC.CepC2
