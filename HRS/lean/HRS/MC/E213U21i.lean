import HRS.MC.E213U21h

/-!
# Packet e213u21 (part i): assembly of `core_bound` from the heat identity

`u21_core_bound_aux` is the single-`hE` form; `core_bound_of_heat` has exactly the binders of
`HRS.MC.E213Plan.GaussData.core_bound` plus the hypothesis `hheat` (the statement of `gaussian_heat_identity`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U21

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section Aux

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u21_core_bound_aux (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE)
    (fam : PrepFamily S β₀ hE)
    (hheat : ∀ (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ),
      ∫ ω, Φ (gd.Zwin T a ω) ∂gd.P₀ = ∫ ω, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (gd.η 0 ω)) ∂gd.P₀) :
    ∃ (A B C : ℕ → ℝ) (e : ℕ → ℕ → ℝ), Tendsto A atTop (𝓝 0) ∧ Tendsto B atTop (𝓝 0) ∧
      (∀ R : ℕ, 1 ≤ R → Tendsto (e R) atTop (𝓝 0)) ∧ (∀ N, 0 ≤ A N) ∧ (∀ R, 0 ≤ B R) ∧
      (∀ R N, 0 ≤ C R * e R N) ∧
      ∀ R : ℕ, 1 ≤ R → ∀ N : ℕ, 2 ≤ N → ∀ (a : ℝ), 0 ≤ a → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        gd.errVal T N a Φ (fam.P N) (fam.X N) ≤ A N + B R + C R * e R N := by
  classical
  -- the initial term
  have hinit := HRS.MC.E213U9.init_term_proof hE T hT gd
  obtain ⟨If, hIf⟩ : ∃ f : ℕ → (a : ℝ) → 0 ≤ a → (PathSpace d m T → ℝ) → ℝ, ∀ N a ha Φ, f N a ha Φ =
      |Real.sqrt N *
          (∫ X, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a
              (zetaE (rLvl d) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) X))
              ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) -
            ∫ F, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a F) ∂(gd.P₀.map (gd.η 0))) -
        (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 (fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z)) F
            ![ellVec S β₀ x, ellVec S β₀ x, ellVec S β₀ x] ∂S.μ0 ∂(gd.P₀.map (gd.η 0))| :=
    ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨CK, hCK⟩ := HRS.MC.E213U11.Kproj_bounded_proof gd T hT
  obtain ⟨A, n0, hA0, hAt, hAV, hAg⟩ := u21_sup_construction
    (fun N => {x | ∃ (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ), Φ ∈ CbUnitBall (PathSpace d m T) 5 ∧
      x = If N a ha Φ})
    (by
      rintro N x ⟨a, ha, Φ, -, rfl⟩
      rw [hIf]
      exact abs_nonneg _)
    (by
      intro ε hε
      obtain ⟨N₀, hN₀⟩ := hinit ε hε
      refine ⟨max N₀ 1, fun N hN x => ?_⟩
      rintro ⟨a, ha, Φ, hΦ, rfl⟩
      rw [hIf]
      exact hN₀ N ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN) a ha Φ hΦ)
    (fun N => 2 * Real.sqrt N + max CK 0 / 6)
    (fun N => by positivity)
  -- far estimates
  obtain ⟨C1, c1, hC1, hc1, hfp⟩ := HRS.MC.E213U12.far_particle_proof hE T hT
  obtain ⟨C2, c2, hC2, hc2, hfg⟩ := HRS.MC.E213U14.far_gauss_proof hE T hT gd
  -- near estimates
  have hnear : ∀ R : ℕ, ∃ (C : ℝ) (e : ℕ → ℝ), 0 ≤ C ∧ (∀ n, 0 ≤ e n) ∧ (1 ≤ R → Tendsto e atTop (𝓝 0)) ∧
      (1 ≤ R → ∀ (N : ℕ), 2 ≤ N → ∀ (a : ℝ) (ha : 0 ≤ a), ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        |∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
            (nearCoef (max (a - R) 0) (fun v => quadFieldAt m (regime S β₀ hE).D.s
              (fun t => withDensityReal ((regime S β₀ hE).ρ t)) (fam.P N) (fam.X N) v ω)) ∂(fam.P N) -
          ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
            (nearCoef (max (a - R) 0) (fun v => NegSobolev.embed m (gd.B v ω))) ∂gd.P₀| +
        (1 / 2) * |∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
            (nearCoef (max (a - R) 0) (fun v => etaE m ((fam.X N) v.toNNReal ω)
              (withDensityReal ((regime S β₀ hE).ρ v)))) ∂(fam.P N) -
          ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
            (nearCoef (max (a - R) 0) (fun v => NegSobolev.embed m (gd.η v ω))) ∂gd.P₀| ≤ C * e N) := by
    intro R
    by_cases hR : 1 ≤ R
    · have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
      obtain ⟨C, e, he, hbd⟩ := HRS.MC.E213U10.near_estimate_proof hE T hT gd fam (R : ℝ) hR0
      refine ⟨|C|, fun n => |e n|, abs_nonneg _, fun n => abs_nonneg _, fun _ => ?_, fun _ N hN a ha Φ hΦ => ?_⟩
      · simpa using he.abs
      · refine (hbd N hN a ha Φ hΦ).trans ?_
        exact (le_abs_self _).trans_eq (abs_mul _ _)
    · exact ⟨0, fun _ => 0, le_rfl, fun _ => le_rfl, fun h => absurd h hR, fun h => absurd h hR⟩
  choose Cf ef hC0 he0 hetend hnb using hnear
  refine ⟨A, fun R => C1 * Real.exp (-c1 * R) + C2 * Real.exp (-c2 * R), Cf, ef, hAt, ?_, hetend, hA0,
    fun R => by positivity, fun R N => mul_nonneg (hC0 R) (he0 R N), ?_⟩
  · have := ((u21_tendsto_exp hc1).const_mul C1).add ((u21_tendsto_exp hc2).const_mul C2)
    simpa using this
  intro R hR N hN a ha Φ hΦ
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hB0 : 0 ≤ C1 * Real.exp (-c1 * R) + C2 * Real.exp (-c2 * R) := by positivity
  have hCe : 0 ≤ Cf R * ef R N := mul_nonneg (hC0 R) (he0 R N)
  by_cases hNn : n0 ≤ N
  · have key := u21_err_le hE T hT gd fam hheat N hN a ha Φ hΦ _ _ _ _ _ _ _ _
      (u21_int_split_PA hE T hT fam (R : ℝ) hRpos hN a ha Φ hΦ)
      (u21_int_split_PJ hE T hT gd fam (R : ℝ) hRpos hN a ha Φ hΦ)
      (u21_int_split_GA hE T hT gd (R : ℝ) hRpos a ha Φ hΦ)
      (u21_int_split_GJ hE T hT gd (R : ℝ) hRpos a ha Φ hΦ)
    have hi := hAV N hNn (If N a ha Φ) ⟨a, ha, Φ, hΦ, rfl⟩
    rw [hIf] at hi
    have hn := hnb R hR N hN a ha Φ hΦ
    have hp := hfp N hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) (fam.hreal N (by omega)) a ha (R : ℝ)
      hRpos.le Φ hΦ
    have hg := hfg a ha (R : ℝ) hRpos.le Φ hΦ
    linarith
  · have h1 := u21_err_crude gd T (max CK 0) (fun a ha => (hCK a ha).trans (le_max_left _ _)) (fam.P N)
      (fam.X N) a ha Φ hΦ
    have h2 := hAg N (not_le.1 hNn)
    linarith

end Aux

section Main

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- `HRS.MC.E213Plan.GaussData.core_bound` with the extra hypothesis `hheat`
(the statement of `HRS.MC.E213Plan.GaussData.gaussian_heat_identity`). -/
theorem core_bound_of_heat (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (fam : PrepFamily S β₀ hE)
    (hheat : ∀ (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ),
      ∫ ω, Φ (gd.Zwin T a ω) ∂gd.P₀ = ∫ ω, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (gd.η 0 ω)) ∂gd.P₀) :
    ∃ (A B C : ℕ → ℝ) (e : ℕ → ℕ → ℝ), Tendsto A atTop (𝓝 0) ∧ Tendsto B atTop (𝓝 0) ∧
      (∀ R : ℕ, 1 ≤ R → Tendsto (e R) atTop (𝓝 0)) ∧ (∀ N, 0 ≤ A N) ∧ (∀ R, 0 ≤ B R) ∧
      (∀ R N, 0 ≤ C R * e R N) ∧
      ∀ R : ℕ, 1 ≤ R → ∀ N : ℕ, 2 ≤ N → ∀ (a : ℝ), 0 ≤ a → ∀ Φ ∈ CbUnitBall (PathSpace d m T) 5,
        gd.errVal T N a Φ (fam.P N) (fam.X N) ≤ A N + B R + C R * e R N :=
  u21_core_bound_aux hE T hT gd fam hheat

end Main

end HRS.MC.E213U21

end
