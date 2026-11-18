import HRS.MS.MainRdFieldAux15
import HRS.MS.PathFidiAux6
import HRS.MS.SuppU2Aux11

/-!
# S.A.9, packet P1a: the particle field path at the index `q = Γ + 2`

* `sa9_TestBd`: the smooth tests of `H^q` are bounded and Lipschitz, with constants proportional to `‖φ‖_{H^q}` (from
  the adjoint input at `r = t = 0`, where `U^{0,0}φ = φ`);
* `sa9_exists_Psi`: Lipschitz Riesz representatives `Ψ_N(X)` of the empirical measures;
* `sa9_exists_Dd`: Riesz representatives of the mean-field densities, continuous in `t` (dominated convergence for
  `∫ |ρ^s - ρ^t|`, from the time-derivative bound and the weighted bound of `MeanFieldRegularityRd`);
* `sa9_exists_Zf`: the field `Z_N^t = σ_N(Ψ_N(X_N^t) - D_N^t)`, measurable in `ζ` for each `t`, a.s. continuous in `t`,
  with the pairing identity for **every** `ζ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MS.MainRdField

variable {d : ℕ}

/-- The smooth tests of `H^q` are bounded and Lipschitz with constant `K‖φ‖_{H^q}`. -/
def sa9_TestBd (d q : ℕ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
    (∀ x, |φ x| ≤ K * HRS.Whole.sobolevNorm (q : ℝ) φ) ∧
      ∀ x y, |φ x - φ y| ≤ K * HRS.Whole.sobolevNorm (q : ℝ) φ * ‖x - y‖

theorem sa9_testBd_of_adj {Cf : WholeCoeff d} {T Kd : ℝ} {q j : ℕ} (hT : 0 ≤ T) (hj : 1 ≤ j)
    (hadj : AdjointInputOneD (q : ℝ) j Cf T Kd) : sa9_TestBd d q ((d + 1) * |Kd|) := by
  refine ⟨by positivity, fun φ hφ => ?_⟩
  obtain ⟨hex, hcd, -, hb⟩ := hadj 0 0 le_rfl le_rfl hT φ hφ
  have hterm : propagatorW Cf 0 0 φ = φ := sa6_prop_terminal hex
  rw [hterm] at hcd hb
  have hn : 0 ≤ HRS.Whole.sobolevNorm (q : ℝ) φ := Real.sqrt_nonneg _
  have hKa : Kd * HRS.Whole.sobolevNorm (q : ℝ) φ ≤ |Kd| * HRS.Whole.sobolevNorm (q : ℝ) φ :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hn
  set B : ℝ := |Kd| * HRS.Whole.sobolevNorm (q : ℝ) φ with hB
  have hB0 : 0 ≤ B := by positivity
  have h0 : ∀ x, |φ x| ≤ B := fun x => by
    have := hb 0 (Nat.zero_le _) (fun l => Fin.elim0 l) x
    have e : HRS.Whole.partialDeriv (fun l : Fin 0 => Fin.elim0 l) φ x = φ x := by
      unfold partialDeriv
      rw [iteratedFDeriv_zero_apply]
    rw [e] at this
    exact this.trans hKa
  have h1 : ∀ k : Fin d, ∀ x, |fderiv ℝ φ x (EuclideanSpace.single k (1 : ℝ))| ≤ B := fun k x => by
    have := hb 1 hj (fun _ => k) x
    have e : HRS.Whole.partialDeriv (fun _ : Fin 1 => k) φ x =
        fderiv ℝ φ x (EuclideanSpace.single k (1 : ℝ)) := by
      unfold partialDeriv
      rw [iteratedFDeriv_one_apply]
    rw [e] at this
    exact this.trans hKa
  have hder : ∀ x, ‖fderiv ℝ φ x‖ ≤ d * B := fun x => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hv : v = ∑ k : Fin d, v k • (EuclideanSpace.single k (1 : ℝ)) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
      simp [EuclideanSpace.basisFun_apply]
    calc ‖fderiv ℝ φ x v‖
        = ‖∑ k : Fin d, v k * fderiv ℝ φ x (EuclideanSpace.single k (1 : ℝ))‖ := by
          conv_lhs => rw [hv]
          simp [map_sum]
      _ ≤ ∑ k : Fin d, ‖v k * fderiv ℝ φ x (EuclideanSpace.single k (1 : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin d, ‖v‖ * B := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, Real.norm_eq_abs (fderiv ℝ φ x _)]
          exact mul_le_mul (PiLp.norm_apply_le v k) (h1 k x) (abs_nonneg _) (norm_nonneg _)
      _ = d * B * ‖v‖ := by simp; ring
  have hdiff : Differentiable ℝ φ := hcd.differentiable (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hj))
  have hdB : d * B ≤ (d + 1) * |Kd| * HRS.Whole.sobolevNorm (q : ℝ) φ := by
    rw [hB]; nlinarith [mul_nonneg (abs_nonneg Kd) hn, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hBle : B ≤ (d + 1) * |Kd| * HRS.Whole.sobolevNorm (q : ℝ) φ := by
    rw [hB]; nlinarith [mul_nonneg (abs_nonneg Kd) hn, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  refine ⟨fun x => (h0 x).trans hBle, fun x y => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := φ) (s := Set.univ)
    (fun z _ => hdiff z) (fun z _ => hder z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  rw [Real.norm_eq_abs] at this
  calc |φ x - φ y| = |φ y - φ x| := abs_sub_comm _ _
    _ ≤ d * B * ‖y - x‖ := this
    _ ≤ (d + 1) * |Kd| * HRS.Whole.sobolevNorm (q : ℝ) φ * ‖x - y‖ := by
        rw [norm_sub_rev y x]
        exact mul_le_mul_of_nonneg_right hdB (norm_nonneg _)

/-! ### Riesz representatives of the empirical measures -/

section Riesz

variable {q : ℕ} {K : ℝ}

theorem sa9_rep_meas (hB : sa9_TestBd d q K) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    ∃ k : HNeg d (q : ℝ), (∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ → HNeg.pairing φ k = ∫ x, φ x ∂μ) := by
  exact sa6_riesz_meas (fun φ hφ x => (hB.2 φ hφ).1 x) μ

theorem sa9_norm_le_of_pairing_diff (hB : sa9_TestBd d q K) {μ ν : Measure (Euc d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k₁ k₂ : HNeg d (q : ℝ)}
    (h1 : ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ → HNeg.pairing φ k₁ = ∫ x, φ x ∂μ)
    (h2 : ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ → HNeg.pairing φ k₂ = ∫ x, φ x ∂ν) {c : ℝ}
    (hc : 0 ≤ c)
    (hd : ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
      |(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν| ≤ c * HRS.Whole.sobolevNorm (q : ℝ) φ) : ‖k₁ - k₂‖ ≤ c := by
  refine hneg_norm_le_of_pairing _ c hc fun φ hφ => ?_
  rw [mhn_pairing_sub hφ, h1 φ hφ, h2 φ hφ]
  exact hd φ hφ

/-- The Riesz representatives of the empirical measures, Lipschitz in the configuration. -/
theorem sa9_exists_Psi (hB : sa9_TestBd d q K) :
    ∃ Ψ : ∀ N : ℕ, EucConfig d N → HNeg d (q : ℝ), ∀ N : ℕ, 1 ≤ N →
      (∀ (X : EucConfig d N) (φ : Euc d → ℝ), IsSobolevTest (q : ℝ) φ →
        HNeg.pairing φ (Ψ N X) = HRS.Whole.pair (HRS.Whole.empirical X) φ) ∧
      ∀ X Y : EucConfig d N, ‖Ψ N X - Ψ N Y‖ ≤ K * ‖X - Y‖ := by
  classical
  have hex : ∀ N : ℕ, ∃ Ψ : EucConfig d N → HNeg d (q : ℝ), 1 ≤ N →
      ∀ (X : EucConfig d N) (φ : Euc d → ℝ), IsSobolevTest (q : ℝ) φ →
        HNeg.pairing φ (Ψ X) = HRS.Whole.pair (HRS.Whole.empirical X) φ := by
    intro N
    by_cases hN : 1 ≤ N
    · have hex' : ∀ X : EucConfig d N, ∃ k : HNeg d (q : ℝ), ∀ φ : Euc d → ℝ,
          IsSobolevTest (q : ℝ) φ → HNeg.pairing φ k = HRS.Whole.pair (HRS.Whole.empirical X) φ := by
        intro X
        haveI := HRS.Whole.empirical_isProbabilityMeasure (show 0 < N from hN) X
        exact sa9_rep_meas hB _
      choose Ψ hΨ using hex'
      exact ⟨Ψ, fun _ X φ hφ => hΨ X φ hφ⟩
    · exact ⟨fun _ => 0, fun h => absurd h hN⟩
  choose Ψ hΨ using hex
  refine ⟨Ψ, fun N hN => ⟨hΨ N hN, fun X Y => ?_⟩⟩
  have hN0 : 0 < N := hN
  haveI := HRS.Whole.empirical_isProbabilityMeasure hN0 X
  haveI := HRS.Whole.empirical_isProbabilityMeasure hN0 Y
  refine hneg_norm_le_of_pairing _ _ (mul_nonneg hB.1 (norm_nonneg _)) fun φ hφ => ?_
  rw [mhn_pairing_sub hφ, hΨ N hN X φ hφ, hΨ N hN Y φ hφ, HRS.Whole.pair_empirical hN0,
    HRS.Whole.pair_empirical hN0, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN0
  rw [abs_of_pos (inv_pos.2 hNp)]
  have hlip := (hB.2 φ hφ).2
  calc (N : ℝ)⁻¹ * |∑ i, (φ (X i) - φ (Y i))|
      ≤ (N : ℝ)⁻¹ * ∑ i : Fin N, |φ (X i) - φ (Y i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hNp.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, K * HRS.Whole.sobolevNorm (q : ℝ) φ * ‖X - Y‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (inv_nonneg.2 hNp.le)
        refine (hlip _ _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB.1 (Real.sqrt_nonneg _))
        have := norm_le_pi_norm (X - Y) i
        simpa using this
    _ = K * ‖X - Y‖ * HRS.Whole.sobolevNorm (q : ℝ) φ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

end Riesz

/-! ### The mean-field densities in `H^{-q}` -/

section Dens

variable {S : WholeMainData d} {r : ℕ} {Λ : ℝ}

/-- The weighted bound of the density: `⟨x⟩^{d+3} |ρ^t(x)| ≤ max Λ 0`. -/
theorem sa9_rho_bound {ρ : ℝ → Euc d → ℝ} {s : ℝ} {T : ℝ} (h : IsRegularMFRd s r Λ T ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    jbracket x ^ ((d : ℝ) + 3) * |ρ t x| ≤ max Λ 0 := by
  obtain ⟨-, hws, hle⟩ := h.1 t ht
  have hcb : 0 ≤ cbNorm r (ρ t) :=
    Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hle' : (weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal ≤ Λ := by linarith
  have hw : weightedSupE r ((d : ℝ) + 3) (ρ t) ≤
      ENNReal.ofReal (weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal := (ENNReal.ofReal_toReal hws.ne).ge
  have := HRS.Whole.u2_wse_bound hw 0 (Nat.zero_le _) (fun l => Fin.elim0 l) x
  have e : HRS.Whole.partialDeriv (fun l : Fin 0 => Fin.elim0 l) (ρ t) x = ρ t x := by
    unfold partialDeriv
    rw [iteratedFDeriv_zero_apply]
  rw [e] at this
  refine this.trans ?_
  exact max_le_max hle' le_rfl

theorem sa9_rho_abs_le {ρ : ℝ → Euc d → ℝ} {s : ℝ} {T : ℝ} (h : IsRegularMFRd s r Λ T ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    |ρ t x| ≤ max Λ 0 * jbracket x ^ (-((d : ℝ) + 3)) := by
  have hj : 0 < jbracket x := by unfold jbracket; positivity
  have h1 := sa9_rho_bound h ht x
  rw [Real.rpow_neg hj.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hj _)]
  linarith [mul_comm |ρ t x| (jbracket x ^ ((d : ℝ) + 3))]

/-- `L¹`-continuity of the mean-field density in time (dominated convergence). -/
theorem sa9_dens_L1 (hMF : MeanFieldRegularityRd S r Λ) {N : ℕ} (hN : 1 ≤ N) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) S.T) :
    Tendsto (fun s : ℝ => ∫ x, |S.ρ N s x - S.ρ N t₀ x|) (𝓝[Set.Icc (0 : ℝ) S.T] t₀) (𝓝 0) := by
  obtain ⟨B, ρt, hder⟩ := hMF.time_derivative
  have hreg := hMF.regular N hN
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Euc d,
      |S.ρ N s x - S.ρ N t₀ x| ≤ 2 * max Λ 0 * jbracket x ^ (-((d : ℝ) + 3)) := by
    intro s hs x
    have h1 := sa9_rho_abs_le hreg hs x
    have h2 := sa9_rho_abs_le hreg ht₀ x
    calc |S.ρ N s x - S.ρ N t₀ x| ≤ |S.ρ N s x| + |S.ρ N t₀ x| := abs_sub _ _
      _ ≤ 2 * max Λ 0 * jbracket x ^ (-((d : ℝ) + 3)) := by linarith
  have hint : Integrable (fun x : Euc d => 2 * max Λ 0 * jbracket x ^ (-((d : ℝ) + 3))) :=
    (HRS.MS.PathFidi.sa26_jb_integrable (d := d)).const_mul _
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
    (l := 𝓝[Set.Icc (0 : ℝ) S.T] t₀)
    (F := fun (s : ℝ) (x : Euc d) => |S.ρ N s x - S.ρ N t₀ x|) (f := fun _ => (0 : ℝ))
    (fun x : Euc d => 2 * max Λ 0 * jbracket x ^ (-((d : ℝ) + 3))) ?_ ?_ hint ?_
  · simpa using hlim
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have c1 : Continuous (S.ρ N s) := ((hreg.1 s hs).1.1).continuous
    have c2 : Continuous (S.ρ N t₀) := ((hreg.1 t₀ ht₀).1.1).continuous
    exact (c1.sub c2).abs.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      exact hbound s hs x
  · refine Eventually.of_forall fun x => ?_
    have hc : ContinuousWithinAt (fun u => S.ρ N u x) (Set.Icc (0 : ℝ) S.T) t₀ :=
      ((hder N hN).1 t₀ ht₀ x).continuousWithinAt
    have := ((hc.sub_const (S.ρ N t₀ x)).abs)
    simpa using this

end Dens

section Field

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ} {q : ℕ} {K : ℝ}

/-- Riesz representatives of the mean-field densities, continuous in time. -/
theorem sa9_exists_Dd (hMF : MeanFieldRegularityRd S r Λ) (hB : sa9_TestBd d q K) :
    ∃ Dd : ℕ → ℝ → HNeg d (q : ℝ), ∀ N : ℕ, 1 ≤ N →
      (∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
        HNeg.pairing φ (Dd N t) = HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) φ) ∧
      ContinuousOn (Dd N) (Set.Icc (0 : ℝ) S.T) := by
  classical
  have hex : ∀ (N : ℕ) (t : ℝ), ∃ k : HNeg d (q : ℝ), 1 ≤ N → t ∈ Set.Icc (0 : ℝ) S.T →
      ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
        HNeg.pairing φ k = HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) φ := by
    intro N t
    by_cases h : 1 ≤ N ∧ t ∈ Set.Icc (0 : ℝ) S.T
    · haveI := HRS.Whole.Q09A.measure_isProb ((hMF.solution N h.1).density t h.2)
      obtain ⟨k, hk⟩ := sa9_rep_meas hB (HRS.Whole.withDensityReal (S.ρ N t))
      exact ⟨k, fun _ _ φ hφ => hk φ hφ⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Dd hDd using hex
  refine ⟨Dd, fun N hN => ⟨fun t ht => hDd N t hN ht, ?_⟩⟩
  intro t₀ ht₀
  have hpr : ∀ t ∈ Set.Icc (0 : ℝ) S.T, HRS.Whole.IsProbDensity (S.ρ N t) := fun t ht =>
    (hMF.solution N hN).density t ht
  have hnorm : ∀ s ∈ Set.Icc (0 : ℝ) S.T, ‖Dd N s - Dd N t₀‖ ≤ K * ∫ x, |S.ρ N s x - S.ρ N t₀ x| := by
    intro s hs
    haveI := HRS.Whole.Q09A.measure_isProb (hpr s hs)
    haveI := HRS.Whole.Q09A.measure_isProb (hpr t₀ ht₀)
    have hI0 : 0 ≤ ∫ x, |S.ρ N s x - S.ρ N t₀ x| := integral_nonneg fun x => abs_nonneg _
    refine hneg_norm_le_of_pairing _ _ (mul_nonneg hB.1 hI0) fun φ hφ => ?_
    rw [mhn_pairing_sub hφ, hDd N s hN hs φ hφ, hDd N t₀ hN ht₀ φ hφ,
      HRS.Whole.Q09A.pair_withDensityReal (hpr s hs), HRS.Whole.Q09A.pair_withDensityReal (hpr t₀ ht₀)]
    have hi1 := HRS.MS.PathFidi.sa26_probDensity_integrable (hpr s hs)
    have hi2 := HRS.MS.PathFidi.sa26_probDensity_integrable (hpr t₀ ht₀)
    have hφc : Continuous φ := hφ.1.continuous
    have hbd := (hB.2 φ hφ).1
    have hbd' : ∀ x, ‖φ x‖ ≤ K * HRS.Whole.sobolevNorm (q : ℝ) φ := fun x => by
      simpa [Real.norm_eq_abs] using hbd x
    have hi1' : Integrable (fun x => S.ρ N s x * φ x) :=
      (hi1.bdd_mul hφc.aestronglyMeasurable (ae_of_all _ hbd')).congr (ae_of_all _ fun x => mul_comm _ _)
    have hi2' : Integrable (fun x => S.ρ N t₀ x * φ x) :=
      (hi2.bdd_mul hφc.aestronglyMeasurable (ae_of_all _ hbd')).congr (ae_of_all _ fun x => mul_comm _ _)
    rw [← integral_sub hi1' hi2']
    have hdi : Integrable (fun x => |S.ρ N s x - S.ρ N t₀ x|) := (hi1.sub hi2).abs
    have hmaj : Integrable (fun x => K * HRS.Whole.sobolevNorm (q : ℝ) φ * |S.ρ N s x - S.ρ N t₀ x|) :=
      hdi.const_mul _
    have := norm_integral_le_of_norm_le (f := fun x => S.ρ N s x * φ x - S.ρ N t₀ x * φ x) hmaj (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, ← mul_sub_right_distrib (S.ρ N s x) (S.ρ N t₀ x) (φ x), abs_mul]
      calc |S.ρ N s x - S.ρ N t₀ x| * |φ x| ≤ |S.ρ N s x - S.ρ N t₀ x| * (K * HRS.Whole.sobolevNorm (q : ℝ) φ) :=
            mul_le_mul_of_nonneg_left (hbd x) (abs_nonneg _)
        _ = _ := mul_comm _ _)
    rw [Real.norm_eq_abs, integral_const_mul] at this
    calc _ ≤ K * HRS.Whole.sobolevNorm (q : ℝ) φ * ∫ x, |S.ρ N s x - S.ρ N t₀ x| := this
      _ = _ := by ring
  have hlim := (sa9_dens_L1 hMF hN ht₀).const_mul K
  rw [mul_zero] at hlim
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs using hnorm s hs

/-- The particle field `Z_N^t = σ_N(Ψ_N(X_N^t) - D_N^t)` at the index `q`, with the pairing identity for every `ζ`. -/
theorem sa9_exists_Zf (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hB : sa9_TestBd d q K) :
    ∃ Z : ∀ N, ℝ → (R N).Ω → HNeg d (q : ℝ),
      (∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t)) ∧
      (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ζ, ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
        HNeg.pairing φ (Z N t ζ) = S.sigma N *
          (HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) φ -
            HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) φ)) ∧
      (∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(R N).P, Continuous fun t : Set.Icc (0 : ℝ) S.T => Z N t.1 ζ) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := sa9_exists_Psi hB
  obtain ⟨Dd, hDd⟩ := sa9_exists_Dd hS.mean_field hB
  have hT0 : 0 ≤ S.T := S.hT.le
  refine ⟨fun N t ζ => S.sigma N • (Ψ N ((R N).X (Real.toNNReal (mrrClamp S.T t)) ζ) -
    Dd N (mrrClamp S.T t)), fun N hN t => ?_, fun N hN t ht ζ φ hφ => ?_, fun N hN => ?_⟩
  · have hΨc : Continuous (Ψ N) := by
      refine LipschitzWith.continuous (K := ⟨|K|, abs_nonneg K⟩) (LipschitzWith.of_dist_le_mul fun X Y => ?_)
      rw [dist_eq_norm, dist_eq_norm]
      exact ((hΨ N hN).2 X Y).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _))
    exact ((hΨc.measurable.comp
      (Q09A.selectedFlow_measurable (hS.flow N hN) _)).sub measurable_const).const_smul (S.sigma N)
  · have hc : mrrClamp S.T t = t := mrrClamp_of_mem ht
    show HNeg.pairing φ (S.sigma N • (Ψ N ((R N).X (Real.toNNReal (mrrClamp S.T t)) ζ) -
      Dd N (mrrClamp S.T t))) = _
    rw [hc, mrm_pairing_smul hφ, mhn_pairing_sub hφ, (hΨ N hN).1 _ φ hφ, (hDd N hN).1 t ht φ hφ]
  · have hΨc : Continuous (Ψ N) := by
      refine LipschitzWith.continuous (K := ⟨|K|, abs_nonneg K⟩) (LipschitzWith.of_dist_le_mul fun X Y => ?_)
      rw [dist_eq_norm, dist_eq_norm]
      exact ((hΨ N hN).2 X Y).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _))
    filter_upwards [mrm_flow_cont (hS.flow N hN)] with ζ hζ
    have hX : Continuous fun t : ℝ≥0 => (R N).X t ζ := continuous_pi hζ
    have hDc : Continuous fun t : Set.Icc (0 : ℝ) S.T => Dd N t.1 :=
      (continuousOn_iff_continuous_restrict.1 (hDd N hN).2)
    have heq : (fun t : Set.Icc (0 : ℝ) S.T => S.sigma N • (Ψ N ((R N).X (Real.toNNReal (mrrClamp S.T t.1)) ζ) -
        Dd N (mrrClamp S.T t.1))) = fun t => S.sigma N • (Ψ N ((R N).X (Real.toNNReal t.1) ζ) - Dd N t.1) := by
      funext t; rw [mrrClamp_of_mem t.2]
    show Continuous fun t : Set.Icc (0 : ℝ) S.T => S.sigma N • (Ψ N ((R N).X (Real.toNNReal (mrrClamp S.T t.1)) ζ) -
        Dd N (mrrClamp S.T t.1))
    rw [heq]
    exact ((hΨc.comp (hX.comp (continuous_real_toNNReal.comp continuous_subtype_val))).sub hDc).const_smul (S.sigma N)

end Field

end HRS.MS.MainRdPath
