import HRS.ME.UIPath
import HRS.ME.RetPathLaw
import HRS.ME.RetGlueB
import HRS.MD.EQFrozen29Rest
import HRS.MD.EQLawPath
import HRS.Sections.AdjKGlue

/-!
# Packet P2 of `HRS.ui_path_tight`: stationary identification of the windows

Statement copied verbatim from `HRS/ME/UIPathTightSpec.lean` (the spec file is unfinished
and is not imported here).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathTight

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

theorem p_up2_sum_pair_identity {N : ℕ} (H : Fin N → Fin N → ℝ) (hH : ∀ i j, H i j = H j i) :
    ∑ i, ∑ j, H i j =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), H i j + ∑ i, H i i := by
  simp only [Finset.sum_filter]
  have hpt : ∀ i j, H i j = (if i < j then H i j else 0) + (if j < i then H i j else 0) +
      (if i = j then H i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, if_neg (not_lt.2 h.le), if_neg h.ne]; ring
    · simp
    · rw [if_neg (not_lt.2 h.le), if_pos h, if_neg h.ne']; ring
  have hB : ∑ i, ∑ j, (if j < i then H i j else 0) = ∑ i, ∑ j, (if i < j then H i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hH]
  have hD : ∑ i, ∑ j, (if i = j then H i j else 0) = ∑ i, H i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hsplit : ∑ i, ∑ j, H i j = (∑ i, ∑ j, (if i < j then H i j else 0)) +
      (∑ i, ∑ j, (if j < i then H i j else 0)) + ∑ i, ∑ j, (if i = j then H i j else 0) := by
    have hrow : ∀ i, ∑ j, H i j = (∑ j, (if i < j then H i j else 0)) +
        (∑ j, (if j < i then H i j else 0)) + ∑ j, (if i = j then H i j else 0) := fun i => by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hpt i j
    simp only [hrow, Finset.sum_add_distrib]
  rw [hsplit, hB, hD]
  ring

theorem p_up2_pairSum_perm {N : ℕ} (H : Fin N → Fin N → ℝ) (hH : ∀ i j, H i j = H j i)
    (σ : Equiv.Perm (Fin N)) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), H (σ i) (σ j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), H i j := by
  have h1 := p_up2_sum_pair_identity (fun i j => H (σ i) (σ j)) (fun i j => hH _ _)
  have h2 := p_up2_sum_pair_identity H hH
  have hF : ∑ i, ∑ j, H (σ i) (σ j) = ∑ i, ∑ j, H i j := by
    calc ∑ i, ∑ j, H (σ i) (σ j) = ∑ i, ∑ j, H (σ i) j :=
          Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (H (σ i))
      _ = ∑ i, ∑ j, H i j := Equiv.sum_comp σ (fun i => ∑ j, H i j)
  have hD : ∑ i, H (σ i) (σ i) = ∑ i, H i i := Equiv.sum_comp σ (fun i => H i i)
  linarith

theorem p_up2_canonicalHamiltonian_comp_perm {d N : ℕ} (g V : Torus d → ℝ) (hg : ∀ x, g (-x) = g x)
    (X : Config d N) (σ : Equiv.Perm (Fin N)) :
    HRS.canonicalHamiltonian g V (X ∘ σ) = HRS.canonicalHamiltonian g V X := by
  unfold HRS.canonicalHamiltonian
  have hH : ∀ i j : Fin N, g (X i - X j) = g (X j - X i) := fun i j => by
    rw [← hg (X i - X j), neg_sub]
  have hp := p_up2_pairSum_perm (fun i j => g (X i - X j)) hH σ
  have hv : ∑ i, V ((X ∘ σ) i) = ∑ i, V (X i) := Equiv.sum_comp σ (fun i => V (X i))
  have hp' : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g ((X ∘ σ) i - (X ∘ σ) j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j) := hp
  rw [hv, hp']

theorem p_up2_canonicalGibbs_isExchangeable {d N : ℕ} (g V : Torus d → ℝ) (hg : ∀ x, g (-x) = g x)
    (β : ℝ) : HRS.IsExchangeable (HRS.canonicalGibbs g V N β) := by
  intro σ
  have hmeas : AEMeasurable (fun X : Config d N => X ∘ σ)
      ((volume : Measure (Config d N)).withDensity fun X =>
        ENNReal.ofReal (Real.exp (-β * HRS.canonicalHamiltonian g V X))) :=
    (HRS.permMeasEquiv σ).measurable.aemeasurable
  have hvol : (volume : Measure (Config d N)) =
      Measure.pi fun _ : Fin N => (volume : Measure (Torus d)) := rfl
  unfold HRS.canonicalGibbs
  rw [Measure.map_smul _ hmeas]
  congr 1
  rw [hvol]
  refine HRS.map_withDensity_perm _ σ _ fun X => ?_
  simp only [p_up2_canonicalHamiltonian_comp_perm g V hg X σ]

/-- Pointwise identity: for any law `P` on configurations whose mean empirical measure is `μ`,
`η_N(X; μ) = ζ_N(X; P)`. -/
theorem p_up2_etaE_eq_zetaE {N : ℕ} (m : ℝ) (P : Measure (Config d N)) (μ : Measure (Torus d))
    (hμ : HRS.meanEmpirical P = μ) (X : Config d N) :
    HRS.etaE m X μ = HRS.zetaE m P X := by
  unfold HRS.etaE HRS.flucE HRS.zetaE
  rw [hμ]

/-- **P2** (stationary identification; scope note 1.1 step 1).  Along a stationary Gibbs flow on the
horizon `u + T` the window centred at the FIXED Gibbs first marginal `μ_N^*` is, pointwise in `ω`, the window
`windowZeta` centred at the actual mean empirical measure (both centres are `μ_N^*`, since
`P.map (X (u+t)) = G_N` for `0 ≤ t ≤ T` and `G_N` is exchangeable).  Route:
`md_stat_gibbs_flow_stationary_proof`, `canonicalGibbs_isExchangeable`, `meanEmpirical_eq_firstMarginal`,
then `dite` congruence on the equal functions of `t ∈ [0,T]`. -/
theorem windowGibbs_eq_windowZeta (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {m : ℝ} (hm : (d : ℝ) < 2 * m) (T u : ℝ) (hu : 0 ≤ u)
    {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) :
    windowGibbs m T u (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) X =
      Main.windowZeta m T u P X := by
  have hN1 : 1 ≤ N := by omega
  haveI hG : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) :=
    HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd hV hβ hN1
  have hExch : HRS.IsExchangeable (canonicalGibbs (periodicRiesz d s) V N β) :=
    p_up2_canonicalGibbs_isExchangeable (periodicRiesz d s) V (fun x => periodicRiesz_neg x) β
  have hmean : HRS.meanEmpirical (canonicalGibbs (periodicRiesz d s) V N β) =
      firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) :=
    HRS.meanEmpirical_eq_firstMarginal _ hExch hN1
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ (u + T) hN
    P X₀ W X hX
  have hpt : ∀ t : Set.Icc (0 : ℝ) T,
      P.map (X (Real.toNNReal (u + t))) = canonicalGibbs (periodicRiesz d s) V N β := by
    intro t
    apply hstat
    rw [Real.coe_toNNReal _ (by linarith [t.2.1])]
    linarith [t.2.2]
  have hfun : ∀ ω : Ω,
      (fun t : Set.Icc (0 : ℝ) T =>
        HRS.etaE m (X (Real.toNNReal (u + t)) ω) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β))) =
      (fun t : Set.Icc (0 : ℝ) T =>
        HRS.zetaE m (P.map (X (Real.toNNReal (u + t)))) (X (Real.toNNReal (u + t)) ω)) := by
    intro ω
    funext t
    have hμ : HRS.meanEmpirical (P.map (X (Real.toNNReal (u + t)))) =
        firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) := by
      rw [hpt t]
      exact hmean
    exact (p_up2_etaE_eq_zetaE m (P.map (X (Real.toNNReal (u + t))))
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) hμ (X (Real.toNNReal (u + t)) ω))
  funext ω
  unfold HRS.windowGibbs HRS.Main.windowZeta
  rw [hfun ω]

end HRS.ME.UIPathTight
