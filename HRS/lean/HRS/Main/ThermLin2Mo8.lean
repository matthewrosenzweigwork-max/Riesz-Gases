import HRS.Main.ThermLin2Mo7

/-!
# THERMLIN2 Mo8: `tl2_Zw_moment` (C1)

`E ‖Zw^r‖²_{E_{m-a₀}} = ∑_k ⟨k⟩^{-2m'} E ⟨Zw^r, e_k⟩²` (`m' = m - a₀`), each term bounded by `A ⟨k⟩²` (Mo7, via the
`H¹` operator bound of the frozen propagator), and `∑_k ⟨k⟩^{2-2m'} < ∞` since `2m' - 2 > d`.
The plain-evolution bound `K` of `Wev` is intrinsic: `Wev = W₀` (`t25p_dual_unique`), `W₀` from `thermlin_stationary_evolution`.
No plan statement is used as a black box (the Gaussian second moment is `t25p_Zb_gaussian` with `p = 1`, i.e. the diagonal
case of `tl2_cov_mixed`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

open HRS.Uniform.Q54c in
/-- C1 (proof). -/
theorem tl2_Zw_moment_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {T' : ℝ}, 0 < T' →
      ∀ (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
        IsDualEvolution S.dyn (fun _ => ρβ) m Wev → IsPlainEvolution Wev T' →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
        (G : ℝ → Ω → NegSobolev d m),
        IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r) →
        (∀ ω, Continuous fun s => G s ω) → (∀ ω, G 0 ω = 0) →
      ∀ (Zw : ℝ → Ω → NegSobolev d m),
        (∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t)) →
        (∀ t, Measurable (Zw t)) →
        ∀ r ∈ Set.Icc (0 : ℝ) T', ∫⁻ ω, tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω) ^ 2 ∂P ≤ ENNReal.ofReal M := by
  classical
  obtain ⟨Cm, cm, hCm, hcm, W₀, hW₀d, -, hW₀dec⟩ := HRS.ThermLin.thermlin_stationary_evolution S h m
  obtain ⟨C₁, c₁, hC₁, hc₁, W₁, hW₁d, -, hW₁dec⟩ := HRS.ThermLin.thermlin_stationary_evolution S h 1
  obtain ⟨C₂, κ, hC₂, hκ, hρ⟩ := tl2_rho_sup_decay_proof S h
  obtain ⟨hsm, -⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hβc : Continuous ρβ := HRS.StaticLimitAux.continuous_of_smooth hsm
  obtain ⟨Bβ, hBβ⟩ := (isCompact_univ.bddAbove_image hβc.continuousOn : BddAbove (ρβ '' Set.univ))
  set Λ : ℝ := max Bβ 0 + C₂ with hΛdef
  have hΛ0 : 0 ≤ Λ := add_nonneg (le_max_right _ _) hC₂
  have hΛ : ∀ σ : ℝ, 0 ≤ σ → ∀ x, S.ρ σ x ≤ Λ := by
    intro σ hσ x
    have h1 := hρ σ hσ x
    have h2 : ρβ x ≤ Bβ := hBβ ⟨x, Set.mem_univ _, rfl⟩
    have h3 : Real.exp (-κ * σ) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have h4 : C₂ * Real.exp (-κ * σ) ≤ C₂ := by nlinarith
    have := (abs_le.1 h1).2
    have := le_max_left Bβ 0
    linarith
  set b : ℝ := PDE.MFAdjoint.aExp d S.s with hb
  obtain ⟨hb1, hb2, -⟩ := PDE.MFAdjoint.aExp_spec (d := d) S.s S.hsd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast S.hd
  have hlt : (d : ℝ) < 2 * (m - b - 1) := by linarith
  set A : ℝ := 2 * S.β⁻¹ * Λ * C₁ ^ 2 / (2 * c₁) with hA
  have hq : 0 ≤ S.β⁻¹ := inv_nonneg.2 S.hβ.le
  have hA0 : 0 ≤ A := by positivity
  set F : NonzeroLattice d → ℝ := fun k => A * Lattice.jp k.1 ^ (-(2 * (m - b - 1))) with hF
  have hFnn : ∀ k, 0 ≤ F k := fun k => mul_nonneg hA0 (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
  have hFs : Summable F := (summable_jp_rpow_aux (m - b - 1) hlt).mul_left A
  refine ⟨∑' k, F k, tsum_nonneg hFnn, ?_⟩
  intro T' hT' Wev hWd hWp Ω mΩ P _ ℱ G hG hGc hGz Zw hZw hZm r hr
  have hKb : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T' → ‖Wev t u‖ ≤ Cm := by
    intro u t hu hut _
    rw [t25p_dual_unique hWd hW₀d hu hut]
    refine (hW₀dec u t hu hut).trans ?_
    have : Real.exp (-cm * (t - u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    nlinarith
  have hm' : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- the pointwise (in `k`) second moment bound
  have hk : ∀ k : NonzeroLattice d, ∫⁻ ω, ENNReal.ofReal ((NegSobolev.eval (Zw r ω) (Torus.realMode k)) ^ 2) ∂P ≤
      ENNReal.ofReal (A * Lattice.jp k.1 ^ 2) := by
    intro k
    have := tl2Mo7_moment_bound S h hm hT' hWd hWp hCm.le hKb hW₁d hC₁.le hc₁ hW₁dec hΛ0 hΛ P G hG hGc hGz Zw hZw hZm hr
      (HRS.Uniform.Q48b.q48b_isSmooth_realMode k)
    rw [tl2Mo7_lp1_realMode] at this
    refine this.trans (le_of_eq ?_)
    congr 1
  -- coordinates of `Zw` through the pairing with `e_k`
  have hcoord : ∀ (z : NegSobolev d m) (k : NonzeroLattice d),
      Lattice.jp k.1 ^ (2 * b) * NegSobolev.coord z k ^ 2 =
        (Lattice.jp k.1 ^ (2 * b) * (Lattice.jp k.1 ^ (-m)) ^ 2) * (NegSobolev.eval z (Torus.realMode k)) ^ 2 := by
    intro z k
    have hj := Torus.jp_pos k.1
    have e1 : NegSobolev.coord z k = Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff z k := by
      unfold NegSobolev.fourierCoeff
      rw [← mul_assoc, ← Real.rpow_add hj]; simp
    rw [eval_realMode, e1]; ring
  have hsq : ∀ z : NegSobolev d m, tl2NormShift m b z ^ 2 =
      ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (2 * b) * NegSobolev.coord z k ^ 2) := by
    intro z
    unfold tl2NormShift
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hmeas : ∀ k : NonzeroLattice d, Measurable fun ω =>
      ENNReal.ofReal ((NegSobolev.eval (Zw r ω) (Torus.realMode k)) ^ 2) := by
    intro k
    have hmem : MemSobolev m (Torus.realMode k) :=
      HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (HRS.Uniform.Q48b.q48b_isSmooth_realMode k) m
    exact (((continuous_eval_const hmem).measurable.comp (hZm r)).pow_const 2).ennreal_ofReal
  simp_rw [hsq]
  rw [lintegral_tsum (fun k => ?_)]
  swap
  · simp_rw [hcoord, ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (sq_nonneg _))]
    exact ((hmeas k).const_mul _).aemeasurable
  calc ∑' k : NonzeroLattice d, ∫⁻ ω, ENNReal.ofReal (Lattice.jp k.1 ^ (2 * b) * NegSobolev.coord (Zw r ω) k ^ 2) ∂P
      ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal (F k) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        have hj := Torus.jp_pos k.1
        have hck : 0 ≤ Lattice.jp k.1 ^ (2 * b) * (Lattice.jp k.1 ^ (-m)) ^ 2 :=
          mul_nonneg (Real.rpow_nonneg hj.le _) (sq_nonneg _)
        simp_rw [hcoord, ENNReal.ofReal_mul hck]
        rw [lintegral_const_mul _ (hmeas k)]
        calc ENNReal.ofReal (Lattice.jp k.1 ^ (2 * b) * (Lattice.jp k.1 ^ (-m)) ^ 2) *
              ∫⁻ ω, ENNReal.ofReal ((NegSobolev.eval (Zw r ω) (Torus.realMode k)) ^ 2) ∂P
            ≤ ENNReal.ofReal (Lattice.jp k.1 ^ (2 * b) * (Lattice.jp k.1 ^ (-m)) ^ 2) *
              ENNReal.ofReal (A * Lattice.jp k.1 ^ 2) := mul_le_mul_right (hk k) _
          _ = ENNReal.ofReal (F k) := by
              rw [← ENNReal.ofReal_mul hck]
              congr 1
              rw [hF]
              simp only []
              have e1 : (Lattice.jp k.1 ^ (-m)) ^ 2 = Lattice.jp k.1 ^ (2 * -m) := Torus.jp_rpow_sq _ _
              have e2 : Lattice.jp k.1 ^ 2 = Lattice.jp k.1 ^ (2 : ℝ) := (Real.rpow_two _).symm
              have e3 : Lattice.jp k.1 ^ (2 * b) * Lattice.jp k.1 ^ (2 * -m) * Lattice.jp k.1 ^ (2 : ℝ) =
                  Lattice.jp k.1 ^ (-(2 * (m - b - 1))) := by
                rw [← Real.rpow_add hj, ← Real.rpow_add hj]; congr 1; ring
              rw [e1, e2]
              calc Lattice.jp k.1 ^ (2 * b) * Lattice.jp k.1 ^ (2 * -m) * (A * Lattice.jp k.1 ^ (2 : ℝ))
                  = A * (Lattice.jp k.1 ^ (2 * b) * Lattice.jp k.1 ^ (2 * -m) * Lattice.jp k.1 ^ (2 : ℝ)) := by ring
                _ = _ := by rw [e3]
    _ = ENNReal.ofReal (∑' k, F k) := (ENNReal.ofReal_tsum_of_nonneg hFnn hFs).symm

example := (@tl2_Zw_moment_proof : type_of% @tl2_Zw_moment)

end HRS.ThermLin.Plan2
