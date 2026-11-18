import HRS.Main.GFB2Aux1
import HRS.Main.GFB1Aux1
import HRS.Energy.StaticLimitJoint

/-!
# Packet GFB2, part 2: continuity and measurability of the fluctuation path (`gf_fluc_continuous`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-- Continuity of an `E_m`-valued map from coordinatewise continuity and a uniform summable domination. -/
theorem gfb2_continuous_of_coords {α : Type*} [TopologicalSpace α] {m : ℝ} (f : α → NegSobolev d m)
    (b : NonzeroLattice d → ℝ) (hb : Summable b) (hg : ∀ a k, NegSobolev.coord (f a) k ^ 2 ≤ b k)
    (hc : ∀ k, Continuous fun a => NegSobolev.coord (f a) k) : Continuous f := by
  classical
  have hcl := StaticLimitAux.continuous_mkLp (Z := α) (ι := NonzeroLattice d)
    (fun a k => NegSobolev.coord (f a) k) b hb hg hc
  have e : f = fun a => (show NegSobolev d m from
      (StaticLimitAux.mkLp (fun k => NegSobolev.coord (f a) k) b hb (hg a) :
        lp (fun _ : NonzeroLattice d => ℝ) 2)) :=
    funext fun a => StaticLimitAux.NegSobolev.ext_coord' (fun k => rfl)
  rw [e]
  exact hcl

/-- Coordinates of `ofMeasureDiff` are dominated when both masses are at most one. -/
theorem gfb2_coord_sq_le {m : ℝ} (hm : (d : ℝ) < 2 * m) (μ ν : Measure (Torus d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : (μ Set.univ).toReal ≤ 1) (hν : (ν Set.univ).toReal ≤ 1)
    (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofMeasureDiff m μ ν) k ^ 2 ≤ 8 * Lattice.jp k.1 ^ (-(2 * m)) := by
  rw [show NegSobolev.coord (NegSobolev.ofMeasureDiff m μ ν) k = _ from
    coord_ofMeasureDiff hm μ ν k, mul_pow, Torus.jp_rpow_sq,
    show 2 * -m = -(2 * m) by ring]
  have h1 := Torus.abs_measureRealCoeff_le μ k
  have h2 := Torus.abs_measureRealCoeff_le ν k
  have h1' : |Torus.measureRealCoeff μ k| ≤ Real.sqrt 2 := h1.trans (by
    calc Real.sqrt 2 * (μ Set.univ).toReal ≤ Real.sqrt 2 * 1 :=
          mul_le_mul_of_nonneg_left hμ (Real.sqrt_nonneg _)
      _ = _ := mul_one _)
  have h2' : |Torus.measureRealCoeff ν k| ≤ Real.sqrt 2 := h2.trans (by
    calc Real.sqrt 2 * (ν Set.univ).toReal ≤ Real.sqrt 2 * 1 :=
          mul_le_mul_of_nonneg_left hν (Real.sqrt_nonneg _)
      _ = _ := mul_one _)
  have h3 : |Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k| ≤ 2 * Real.sqrt 2 := by
    calc _ ≤ _ := abs_sub _ _
      _ ≤ Real.sqrt 2 + Real.sqrt 2 := add_le_add h1' h2'
      _ = _ := by ring
  have h4 : (Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k) ^ 2 ≤ 8 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h3 2
    rw [sq_abs] at this
    calc _ ≤ _ := this
      _ = 8 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hj : 0 ≤ Lattice.jp k.1 ^ (-(2 * m)) := Real.rpow_nonneg (Torus.jp_pos _).le _
  nlinarith

theorem gfb2_empirical_mass {N : ℕ} (X : Config d N) : (empirical X) Set.univ ≤ 1 := by
  unfold empirical
  simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, measure_univ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  · rw [ENNReal.inv_mul_cancel (by exact_mod_cast hpos.ne') (by simp)]

instance gfb2_empirical_finite {N : ℕ} (X : Config d N) : IsFiniteMeasure (empirical X) :=
  ⟨lt_of_le_of_lt (gfb2_empirical_mass X) ENNReal.one_lt_top⟩


theorem gfb2_weak (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ) :
    ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun t => ∫ x, ψ x * S.ρ N t x) (Set.Icc 0 S.T) := by
  obtain ⟨hMFN, hReg⟩ := hMF N
  have hK : d + 1 ≤ S.γ + 2 * d + 12 := by omega
  have hV : Torus.IsCk 1 (S.dynM M N).V := by
    have h1 : (1 : WithTop ℕ∞) ≤ ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (show 1 ≤ S.γ + 2 * d + 12 by omega)
    exact ContDiff.of_le S.V_reg h1
  have hd1 : 1 ≤ d := by have := S.hd; omega
  exact Q54c.weak_continuity (S.dynM M N) hd1 S.T S.Λ S.hT.le (S.γ + 2 * d + 12) hK (S.ρ N) hMFN hReg hV

theorem gfb2_two_m {S : GeneralSetup d} {m : ℝ} (hm : (S.γ : ℝ) ≤ m) : (d : ℝ) < 2 * m := by
  have h' : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast S.hγ
  push_cast at h'
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem gfb2_fluc_cont_path (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (m : ℝ) (hm : (S.γ : ℝ) ≤ m) {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) (σ : ℝ) (ω : Ω)
    (hc : ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    Continuous fun t : Set.Icc (0 : ℝ) S.T => flucProc m σ X (S.ρ N) t ω := by
  have hm2 := gfb2_two_m hm
  obtain ⟨hMFN, hReg⟩ := hMF N
  have hweak := gfb2_weak S M hMF N
  have hprob : ∀ t : Set.Icc (0 : ℝ) S.T, IsProbabilityMeasure (withDensityReal (S.ρ N t)) :=
    fun t => isProb_withDensityReal (hMFN.density t.1 t.2)
  have hb : Summable fun k : NonzeroLattice d => σ ^ 2 * (8 * Lattice.jp k.1 ^ (-(2 * m))) :=
    ((summable_jp_rpow (d := d) m hm2).mul_left 8).mul_left (σ ^ 2)
  -- coordinates
  have hcoord : ∀ (t : Set.Icc (0 : ℝ) S.T) (k : NonzeroLattice d),
      NegSobolev.coord (flucProc m σ X (S.ρ N) t ω) k =
        σ * (Lattice.jp k.1 ^ (-m) * ((N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X (Real.toNNReal t) ω i) -
          ∫ x, Torus.realMode k x * S.ρ N t x)) := by
    intro t k
    haveI := hprob t
    unfold flucProc
    have h1 : NegSobolev.coord (σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
        (withDensityReal (S.ρ N t))) k =
        σ * NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
        (withDensityReal (S.ρ N t))) k := rfl
    rw [h1, coord_ofMeasureDiff hm2]
    congr 2
    congr 1
    · unfold Torus.measureRealCoeff
      exact integral_empirical _ (continuous_realMode' k)
    · unfold Torus.measureRealCoeff
      rw [integral_withDensityReal_eq _ (hMFN.density t.1 t.2).measurable (hMFN.density t.1 t.2).nonneg]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  refine gfb2_continuous_of_coords _ _ hb (fun t k => ?_) (fun k => ?_)
  · haveI := hprob t
    haveI : IsFiniteMeasure (empirical (X (Real.toNNReal t) ω)) := inferInstance
    have := gfb2_coord_sq_le (m := m) hm2 (empirical (X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t))
      (by
        have := gfb2_empirical_mass (X (Real.toNNReal t) ω)
        have h2 := ENNReal.toReal_mono ENNReal.one_ne_top this
        simpa using h2)
      (by simp) k
    have e : NegSobolev.coord (flucProc m σ X (S.ρ N) t ω) k =
        σ * NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
          (withDensityReal (S.ρ N t))) k := rfl
    rw [e, mul_pow]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg σ)
  · simp only [hcoord]
    refine continuous_const.mul (continuous_const.mul (Continuous.sub ?_ ?_))
    · refine continuous_const.mul (continuous_finset_sum _ fun i _ => ?_)
      exact (continuous_realMode' k).comp ((hc i).comp (continuous_real_toNNReal.comp continuous_subtype_val))
    · exact (hweak (Torus.realMode k) (continuous_realMode' k)).comp_continuous continuous_subtype_val
        (fun t => t.2)


theorem gf_fluc_continuous_proof (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (m : ℝ) (hm : (S.γ : ℝ) ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X) (σ : ℝ) :
    (∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) S.T => flucProc m σ X (S.ρ N) t ω) ∧
      AEMeasurable (flucPath m S.T σ X (S.ρ N)) P := by
  classical
  have hm2 := gfb2_two_m hm
  have hcont : ∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) S.T => flucProc m σ X (S.ρ N) t ω := by
    filter_upwards [hX.cont] with ω hω using gfb2_fluc_cont_path S M hMF N m hm X σ ω hω
  refine ⟨hcont, ?_⟩
  obtain ⟨Nn, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  let g : Ω → PathSpace d m S.T := fun ω => if ω ∈ Nn then 0 else flucPath m S.T σ X (S.ρ N) ω
  have hmeas : ∀ s : ℝ, Measurable fun ω => flucProc m σ X (S.ρ N) s ω := by
    intro s
    unfold flucProc
    refine (measurable_const_smul σ).comp ?_
    exact (gf_measurable_ofMeasureDiff_proof (N := N) m (by linarith) _).comp (hX.adapted _)
  have hg : Measurable g := by
    refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
    have hfun : (fun ω => (show C(Set.Icc (0 : ℝ) S.T, NegSobolev d m) from g ω) s) =
        fun ω => if ω ∈ Nn then 0 else flucProc m σ X (S.ρ N) s ω := by
      funext ω
      by_cases hω : ω ∈ Nn
      · simp [g, hω]
        rfl
      · have hc : Continuous fun t : Set.Icc (0 : ℝ) S.T => flucProc m σ X (S.ρ N) t ω := by
          by_contra hnc
          exact hω (hNsub hnc)
        simp only [g, hω, if_false]
        have e : flucPath m S.T σ X (S.ρ N) ω = (show PathSpace d m S.T from
            (⟨fun t : Set.Icc (0 : ℝ) S.T => σ • NegSobolev.ofMeasureDiff m
              (empirical (X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)), hc⟩ :
              C(Set.Icc (0 : ℝ) S.T, NegSobolev d m))) := by
          unfold flucPath
          exact dif_pos hc
        rw [e]
        rfl
    rw [hfun]
    exact Measurable.ite hNm measurable_const (hmeas s)
  refine ⟨g, hg, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  simp [g, hω]

example := (@gf_fluc_continuous_proof : type_of% @HRS.GF.gf_fluc_continuous)

end HRS.GF
