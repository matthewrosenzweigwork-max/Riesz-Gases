import HRS.MD.EQRemBridge
import HRS.MD.EQRemL2
import HRS.MD.EQStatLinear
import HRS.PDE.MeanFieldPairSeries
import HRS.Uniform.Q54cAux53

/-!
# EQ-REM (a), part 2: the test-function bound `‖𝓡_{N,stat}(φ)‖_{L²(ℙ_{N,β})} ≤ C ε_N ‖φ‖_{C²}`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29

variable {d : ℕ} {s : ℝ}

/-- `‖𝓡_{N,stat}(φ)‖_{L²(ℙ_{N,β})} ≤ C √δ_N ‖φ‖_{C²}`, `C` chosen before `β, ρβ, N`. -/
theorem eqrem_static_test (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N → ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ →
        eLpNorm (statRemainder d s V β ρβ (N := N) φ) 2 (canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal (C * Real.sqrt (deltaN d s N) * Torus.cbNorm 2 φ) := by
  obtain ⟨Cl, hCl0, hCl⟩ := EQStat.eq_static_linear_proof hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨Cq, hCq0, hCq⟩ := EQStat.eq_static_quadratic_proof hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨Cψ, hCψ0, hCψ⟩ := eqrem_psi_L2 hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨B₀, hB₀0, hB₀⟩ := eqrem_pairKernel_env hd hs0 hsd
  refine ⟨Real.sqrt (Cl * Cψ) + Real.sqrt Cq * B₀ / 2 + 1, by positivity, ?_⟩
  intro β hβ ρβ hρ N hN φ hφ
  have hβ0 : 0 < βm := hβm
  have hβpos : 0 < β := lt_of_lt_of_le hβm hβ.1
  obtain ⟨hprob, hμm, hmm, ⟨Bψ, hBψ⟩, hqint⟩ := eqrem_context hd hs0 hsd V hV hβpos hρ hN hφ
  obtain ⟨hρs, Λ, hΛ0, hΛ, hP⟩ := eqrem_setup hd hs0 hsd V hV hβpos hρ
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hδ0 : 0 ≤ deltaN d s N := by
    have := MarginalAux.inv_le_deltaN (d := d) hs0 N (by omega)
    exact (inv_nonneg.2 hNR.le).trans this
  have hδ1 : deltaN d s N ≤ 1 := MarginalAux.deltaN_le_one hs0 hsd (by omega) N (by omega)
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  set μ := withDensityReal ρβ with hμdef
  set m := firstMarginal G with hmdef
  set h := pairKernel d s φ with hh
  set L : ℝ := Torus.cbNorm 2 φ with hL
  have hL0 : 0 ≤ L := eqrem_cbNorm_nonneg 2 φ
  set ψ : Torus d → ℝ := fun x => kernelField h μ x - kernelField h m x with hψ
  have hψm : Measurable ψ := hμm.sub hmm
  have hμfin : IsFiniteMeasure μ := Commutator.absConv_isFiniteMeasure hΛ
  have hmi : ∀ i : Fin N, G.map (fun X : Config d N => X i) = m := by
    intro i
    have := eqrem_marginal_eq hN0 (periodicRiesz d s) (fun x => periodicRiesz_neg x) β μ i
    rw [← hP N] at this
    exact this
  -- the two terms
  set T1 : Config d N → ℝ := fun X => Real.sqrt N * (∫ x, ψ x ∂(empirical X) - ∫ x, ψ x ∂m) with hT1
  set T2 : Config d N → ℝ := fun X => (Real.sqrt N / 2) * (quadStat h m X - ∫ Y, quadStat h m Y ∂G) with hT2
  have hstat : statRemainder d s V β ρβ (N := N) φ = fun X => T1 X - T2 X := rfl
  have hemp : ∀ X : Config d N, ∫ x, ψ x ∂(empirical X) = (1 / (N : ℝ)) * ∑ i, ψ (X i) := by
    intro X
    have := pair_empirical hN0 X ψ
    unfold pair at this
    rw [one_div]
    exact this
  have hT1m : Measurable T1 := by
    have : T1 = fun X => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, ψ (X i) - ∫ x, ψ x ∂m) := by
      funext X; simp only [hT1, hemp]
    rw [this]
    exact measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      hψm.comp (measurable_pi_apply i))).sub measurable_const)
  have hqm := eqrem_quadStat_meas (N := N) (eqrem_pairKernel_meas hsd hφ) hmm
  have hT2m : Measurable T2 := measurable_const.mul (hqm.sub measurable_const)
  -- bound for T1
  have hψ2 : ∫ x, ψ x ^ 2 ∂μ ≤ Cψ * L ^ 2 * deltaN d s N ^ 2 := by
    have hQ := hCψ β hβ ρβ hρ N hN φ hφ
    have hint : Integrable (fun x => ψ x ^ 2) μ :=
      Integrable.of_bound (hψm.pow_const 2).aestronglyMeasurable (Bψ ^ 2)
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hBψ x) 2)
    have e : ENNReal.ofReal (∫ x, ψ x ^ 2 ∂μ) = ∫⁻ x, ‖ψ x‖ₑ ^ 2 ∂μ := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => sq_nonneg _)]
      refine lintegral_congr fun x => ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have hE0 : 0 ≤ Cψ * L ^ 2 * deltaN d s N ^ 2 := by positivity
    have hQ' : ∫⁻ x, ‖ψ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (Cψ * L ^ 2 * deltaN d s N ^ 2) := hQ
    rw [← e] at hQ'
    exact (ENNReal.ofReal_le_ofReal_iff hE0).1 hQ'
  have hψmem : MemLp ψ 2 μ :=
    MemLp.of_bound hψm.aestronglyMeasurable Bψ (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hBψ x)
  have hlin := hCl β hβ ρβ hρ N hN ψ hψm hψmem
  have hamean : ∫ X, pair (empirical X) ψ ∂G = ∫ x, ψ x ∂m := by
    have := eqrem_avg_integral hN0 hmi hψm hBψ
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun X => ?_)
    simp only
    rw [pair_empirical hN0, one_div]
  have hsqrtN : ‖Real.sqrt N‖ₑ ^ 2 = ENNReal.ofReal N := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _), ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt hNR.le]
  have hT1sq : ∫⁻ X, ‖T1 X‖ₑ ^ 2 ∂G =
      ENNReal.ofReal N * evariance (fun X : Config d N => pair (empirical X) ψ) G := by
    have hc : ∀ X, ‖T1 X‖ₑ ^ 2 = ENNReal.ofReal N *
        ‖pair (empirical X) ψ - (G[fun X : Config d N => pair (empirical X) ψ])‖ₑ ^ 2 := by
      intro X
      have : T1 X = Real.sqrt N * (pair (empirical X) ψ - (G[fun X : Config d N => pair (empirical X) ψ])) := by
        rw [hamean]; rfl
      rw [this, enorm_mul, mul_pow, hsqrtN]
    calc ∫⁻ X, ‖T1 X‖ₑ ^ 2 ∂G = ∫⁻ X, ENNReal.ofReal N *
          ‖pair (empirical X) ψ - (G[fun X : Config d N => pair (empirical X) ψ])‖ₑ ^ 2 ∂G :=
          lintegral_congr hc
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hS1 : 0 ≤ Real.sqrt (Cl * Cψ) * L * deltaN d s N := by positivity
  have hT1b : ∫⁻ X, ‖T1 X‖ₑ ^ 2 ∂G ≤ ENNReal.ofReal ((Real.sqrt (Cl * Cψ) * L * deltaN d s N) ^ 2) := by
    rw [hT1sq]
    refine (mul_le_mul' le_rfl hlin).trans ?_
    rw [← ENNReal.ofReal_mul hNR.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hCl' : Cl * ∫ x, ψ x ^ 2 ∂μ ≤ Cl * (Cψ * L ^ 2 * deltaN d s N ^ 2) :=
      mul_le_mul_of_nonneg_left hψ2 hCl0.le
    have e1 : (N : ℝ) * (Cl * (N : ℝ)⁻¹ * ∫ x, ψ x ^ 2 ∂μ) = Cl * ∫ x, ψ x ^ 2 ∂μ := by
      field_simp
    have e2 : (Real.sqrt (Cl * Cψ) * L * deltaN d s N) ^ 2 = Cl * (Cψ * L ^ 2 * deltaN d s N ^ 2) := by
      have := Real.sq_sqrt (mul_nonneg hCl0.le hCψ0)
      calc (Real.sqrt (Cl * Cψ) * L * deltaN d s N) ^ 2 = (Real.sqrt (Cl * Cψ)) ^ 2 * L ^ 2 * deltaN d s N ^ 2 := by ring
        _ = _ := by rw [this]; ring
    rw [e1, e2]; exact hCl'
  have hE1 : eLpNorm T1 2 G ≤ ENNReal.ofReal (Real.sqrt (Cl * Cψ) * L * deltaN d s N) := by
    have := eqrem_eLpNorm_two_le hT1m.aestronglyMeasurable (sq_nonneg _) hT1b
    rwa [Real.sqrt_sq hS1] at this
  -- bound for T2
  obtain ⟨hvarB⟩ : Nonempty (True) := ⟨trivial⟩
  have hvar := hCq β hβ ρβ hρ (B₀ * L) h (eqrem_pairKernel_meas hsd hφ) (eqrem_pairKernel_symm hsd φ)
    (fun x y hxy => by simpa [hL, mul_assoc] using hB₀ φ hφ x y hxy) N hN m (Or.inr rfl)
  have hsqrtN2 : ‖Real.sqrt N / 2‖ₑ ^ 2 = ENNReal.ofReal (1 / 4) * (N : ℝ≥0∞) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity), ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [div_pow, Real.sq_sqrt hNR.le]; ring
  have hT2sq : ∫⁻ X, ‖T2 X‖ₑ ^ 2 ∂G =
      ENNReal.ofReal (1 / 4) * ((N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h m X) G) := by
    have hc : ∀ X, ‖T2 X‖ₑ ^ 2 = (ENNReal.ofReal (1 / 4) * (N : ℝ≥0∞)) *
        ‖quadStat h m X - ∫ Y, quadStat h m Y ∂G‖ₑ ^ 2 := by
      intro X
      simp only [hT2]
      rw [enorm_mul, mul_pow, hsqrtN2]
    calc ∫⁻ X, ‖T2 X‖ₑ ^ 2 ∂G = ∫⁻ X, (ENNReal.ofReal (1 / 4) * (N : ℝ≥0∞)) *
          ‖quadStat h m X - ∫ Y, quadStat h m Y ∂G‖ₑ ^ 2 ∂G := lintegral_congr hc
      _ = (ENNReal.ofReal (1 / 4) * (N : ℝ≥0∞)) * ∫⁻ X, ‖quadStat h m X - ∫ Y, quadStat h m Y ∂G‖ₑ ^ 2 ∂G :=
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top N))
      _ = _ := by rw [mul_assoc]; rfl
  have hS2 : 0 ≤ Real.sqrt Cq * B₀ * L * Real.sqrt (deltaN d s N) / 2 := by positivity
  have hT2b : ∫⁻ X, ‖T2 X‖ₑ ^ 2 ∂G ≤
      ENNReal.ofReal ((Real.sqrt Cq * B₀ * L * Real.sqrt (deltaN d s N) / 2) ^ 2) := by
    rw [hT2sq]
    refine (mul_le_mul' le_rfl hvar).trans ?_
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have h1 := Real.sq_sqrt hCq0.le
    have h2 := Real.sq_sqrt hδ0
    calc 1 / 4 * (Cq * (B₀ * L) ^ 2 * deltaN d s N)
        = (Real.sqrt Cq) ^ 2 * B₀ ^ 2 * L ^ 2 * (Real.sqrt (deltaN d s N)) ^ 2 / 4 := by rw [h1, h2]; ring
      _ = _ := by ring
  have hE2 : eLpNorm T2 2 G ≤ ENNReal.ofReal (Real.sqrt Cq * B₀ * L * Real.sqrt (deltaN d s N) / 2) := by
    have := eqrem_eLpNorm_two_le hT2m.aestronglyMeasurable (sq_nonneg _) hT2b
    rwa [Real.sqrt_sq hS2] at this
  -- assemble
  have hsub : eLpNorm (statRemainder d s V β ρβ (N := N) φ) 2 G ≤ eLpNorm T1 2 G + eLpNorm T2 2 G := by
    rw [hstat]
    exact eLpNorm_sub_le (f := T1) (g := T2) (by norm_num)
  refine hsub.trans ?_
  refine (add_le_add hE1 hE2).trans ?_
  rw [← ENNReal.ofReal_add hS1 hS2]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq0 := Real.sqrt_nonneg (deltaN d s N)
  have hδsq : deltaN d s N ≤ Real.sqrt (deltaN d s N) := by
    calc deltaN d s N = Real.sqrt (deltaN d s N) * Real.sqrt (deltaN d s N) := (Real.mul_self_sqrt hδ0).symm
      _ ≤ Real.sqrt (deltaN d s N) * 1 := by
          gcongr
          rw [Real.sqrt_le_one]; exact hδ1
      _ = _ := mul_one _
  have hA : 0 ≤ Real.sqrt (Cl * Cψ) := Real.sqrt_nonneg _
  have hBn : 0 ≤ Real.sqrt Cq * B₀ := by positivity
  calc Real.sqrt (Cl * Cψ) * L * deltaN d s N + Real.sqrt Cq * B₀ * L * Real.sqrt (deltaN d s N) / 2
      ≤ Real.sqrt (Cl * Cψ) * L * Real.sqrt (deltaN d s N) + Real.sqrt Cq * B₀ * L * Real.sqrt (deltaN d s N) / 2 := by
        gcongr
    _ ≤ (Real.sqrt (Cl * Cψ) + Real.sqrt Cq * B₀ / 2 + 1) * Real.sqrt (deltaN d s N) * L := by
        have : 0 ≤ L * Real.sqrt (deltaN d s N) := mul_nonneg hL0 hsq0
        nlinarith [mul_nonneg hBn this, this]


/-- `‖e_k‖_{C²} ≤ 3 √2 ⟨k⟩²`. -/
theorem eqrem_realMode_cb (k : NonzeroLattice d) :
    Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ) ≤ 3 * Real.sqrt 2 * Lattice.jp k.1 ^ 2 := by
  by_cases hp : Lattice.IsPosHalf k.1
  · have h1 : (Torus.realMode k : Torus d → ℝ) = PDE.MFPair.trigTerm (Real.sqrt 2) 0 k.1 := by
      funext x
      simp [Torus.realMode, PDE.MFPair.trigTerm, hp]
    rw [h1]
    have := PDE.MFPair.cbNorm_trigTerm_le (Real.sqrt 2) 0 k.1 2
    refine this.trans (le_of_eq ?_)
    simp only [abs_zero, add_zero, abs_of_nonneg (Real.sqrt_nonneg 2)]
    push_cast; ring
  · have h1 : (Torus.realMode k : Torus d → ℝ) = PDE.MFPair.trigTerm 0 (Real.sqrt 2) k.1 := by
      funext x
      simp [Torus.realMode, PDE.MFPair.trigTerm, hp]
    rw [h1]
    have := PDE.MFPair.cbNorm_trigTerm_le 0 (Real.sqrt 2) k.1 2
    refine this.trans (le_of_eq ?_)
    simp only [abs_zero, zero_add, abs_of_nonneg (Real.sqrt_nonneg 2)]
    push_cast; ring

/-- Measurability of the stationary remainder in the configuration. -/
theorem eqrem_statRemainder_meas (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 2 ≤ N) {φ : Torus d → ℝ}
    (hφ : Torus.IsCk 2 φ) : Measurable (statRemainder d s V β ρβ (N := N) φ) := by
  obtain ⟨hprob, hμm, hmm, ⟨Bψ, hBψ⟩, hqint⟩ := eqrem_context hd hs0 hsd V hV hβ hρ hN hφ
  have hN0 : 0 < N := by omega
  have hψm : Measurable (fun x => kernelField (pairKernel d s φ) (withDensityReal ρβ) x -
      kernelField (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) x) := hμm.sub hmm
  have hqm := eqrem_quadStat_meas (N := N) (eqrem_pairKernel_meas hsd hφ) hmm
  unfold statRemainder
  have hemp : ∀ X : Config d N, ∫ x, (kernelField (pairKernel d s φ) (withDensityReal ρβ) x -
      kernelField (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) x) ∂(empirical X) =
      (1 / (N : ℝ)) * ∑ i, (kernelField (pairKernel d s φ) (withDensityReal ρβ) (X i) -
      kernelField (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) (X i)) := by
    intro X
    have := pair_empirical hN0 X (fun x => kernelField (pairKernel d s φ) (withDensityReal ρβ) x -
      kernelField (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) x)
    unfold pair at this
    rw [one_div]
    exact this
  simp_rw [hemp]
  exact (measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    hψm.comp (measurable_pi_apply i))).sub measurable_const)).sub (measurable_const.mul (hqm.sub measurable_const))

/-- (Packet EQ-REM (a), TeX `P:eq:stationary-R-test` L4034-4038 and `P:eq:stationary-R-field` L4041-4044.) -/
theorem eq_rem_static_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (M : ℝ) (hM : (d : ℝ) / 2 + 2 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      (∀ φ : Torus d → ℝ, Torus.IsCk 2 φ →
        eLpNorm (statRemainder d s V β ρβ (N := N) φ) 2 (canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal (C * Real.sqrt (deltaN d s N) * Torus.cbNorm 2 φ)) ∧
      ∫⁻ X, coordEnergy M (fun k => statRemainder d s V β ρβ (N := N) (Torus.realMode k) X)
          ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨C₁, hC₁, hC₁b⟩ := eqrem_static_test hd hs0 hsd V hV βm βp hβm hββ
  have hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * (M - 2))) :=
    summable_jp_rpow (d := d) (M - 2) (by linarith)
  set S : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (M - 2))) with hS
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hS0 : 0 ≤ S := tsum_nonneg fun k => Real.rpow_nonneg (hjp k).le _
  refine ⟨max C₁ (18 * C₁ ^ 2 * S + 1), lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro β hβ ρβ hρ N hN
  have hβpos : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hN0 : 0 < N := by omega
  have hδ0 : 0 ≤ deltaN d s N := by
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
    exact (inv_nonneg.2 hNR.le).trans (MarginalAux.inv_le_deltaN (d := d) hs0 N (by omega))
  refine ⟨fun φ hφ => ?_, ?_⟩
  · refine (hC₁b β hβ ρβ hρ N hN φ hφ).trans (ENNReal.ofReal_le_ofReal ?_)
    have := eqrem_cbNorm_nonneg 2 φ
    have := Real.sqrt_nonneg (deltaN d s N)
    gcongr
    exact le_max_left _ _
  · set G := canonicalGibbs (periodicRiesz d s) V N β with hG
    haveI : IsProbabilityMeasure G := eqrem_gibbs_prob hd hs0 hsd V hV hβpos hρ hN0
    have hck : ∀ k : NonzeroLattice d, Torus.IsCk 2 (Torus.realMode k : Torus d → ℝ) := fun k => by
      have := Uniform.Q54c.isCk_realMode k 2
      exact_mod_cast this
    -- per mode
    have hmode : ∀ k : NonzeroLattice d,
        ∫⁻ X, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * M) * (statRemainder d s V β ρβ (N := N) (Torus.realMode k) X) ^ 2)
          ∂G ≤ ENNReal.ofReal (18 * C₁ ^ 2 * deltaN d s N * Lattice.jp k.1 ^ (-(2 * (M - 2)))) := by
      intro k
      set q := Lattice.jp k.1 with hq
      have hqpos : 0 < q := hjp k
      set R : Config d N → ℝ := statRemainder d s V β ρβ (N := N) (Torus.realMode k) with hR
      have hRm : Measurable R := eqrem_statRemainder_meas hd hs0 hsd V hV hβpos hρ hN (hck k)
      have ha : 0 ≤ q ^ (-2 * M) := Real.rpow_nonneg hqpos.le _
      have e1 : ∀ X, ENNReal.ofReal (q ^ (-2 * M) * R X ^ 2) = ENNReal.ofReal (q ^ (-2 * M)) * ‖R X‖ₑ ^ 2 := by
        intro X
        rw [ENNReal.ofReal_mul ha, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      have hL2 := hC₁b β hβ ρβ hρ N hN _ (hck k)
      have hcb := eqrem_realMode_cb k
      have hcb0 := eqrem_cbNorm_nonneg 2 (Torus.realMode k : Torus d → ℝ)
      calc ∫⁻ X, ENNReal.ofReal (q ^ (-2 * M) * R X ^ 2) ∂G
          = ENNReal.ofReal (q ^ (-2 * M)) * ∫⁻ X, ‖R X‖ₑ ^ 2 ∂G := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            exact lintegral_congr e1
        _ = ENNReal.ofReal (q ^ (-2 * M)) * eLpNorm R 2 G ^ 2 := by
            rw [eqrem_lintegral_sq_eq hRm.aestronglyMeasurable]
        _ ≤ ENNReal.ofReal (q ^ (-2 * M)) *
              ENNReal.ofReal (C₁ * Real.sqrt (deltaN d s N) * Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ)) ^ 2 :=
            mul_le_mul' le_rfl (pow_le_pow_left' hL2 2)
        _ = ENNReal.ofReal (q ^ (-2 * M) *
              (C₁ * Real.sqrt (deltaN d s N) * Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ)) ^ 2) := by
            rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul ha]
        _ ≤ ENNReal.ofReal (18 * C₁ ^ 2 * deltaN d s N * q ^ (-(2 * (M - 2)))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hq4 : q ^ (-(2 * (M - 2))) = q ^ (-2 * M) * q ^ 4 := by
              rw [show -(2 * (M - 2)) = -2 * M + ((4 : ℕ) : ℝ) by push_cast; ring,
                Real.rpow_add hqpos, Real.rpow_natCast]
            have hbound : Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ) ≤ 3 * Real.sqrt 2 * q ^ 2 := hcb
            have hsqd := Real.sq_sqrt hδ0
            have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
            have h1 : (C₁ * Real.sqrt (deltaN d s N) * Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ)) ^ 2 ≤
                (C₁ * Real.sqrt (deltaN d s N) * (3 * Real.sqrt 2 * q ^ 2)) ^ 2 := by
              apply pow_le_pow_left₀ (by positivity)
              exact mul_le_mul_of_nonneg_left hbound (by positivity)
            have h2 : (C₁ * Real.sqrt (deltaN d s N) * (3 * Real.sqrt 2 * q ^ 2)) ^ 2 =
                18 * C₁ ^ 2 * deltaN d s N * q ^ 4 := by
              calc _ = C₁ ^ 2 * (Real.sqrt (deltaN d s N)) ^ 2 * 9 * (Real.sqrt 2) ^ 2 * q ^ 4 := by ring
                _ = _ := by rw [hsqd, hsq2]; ring
            rw [hq4]
            calc q ^ (-2 * M) * (C₁ * Real.sqrt (deltaN d s N) * Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ)) ^ 2
                ≤ q ^ (-2 * M) * (18 * C₁ ^ 2 * deltaN d s N * q ^ 4) := by
                  rw [← h2]; exact mul_le_mul_of_nonneg_left h1 ha
              _ = _ := by ring
    have hfun : ∀ X, coordEnergy M (fun k => statRemainder d s V β ρβ (N := N) (Torus.realMode k) X) =
        ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * M) *
          (statRemainder d s V β ρβ (N := N) (Torus.realMode k) X) ^ 2) := fun X => rfl
    have hmeas : ∀ k : NonzeroLattice d, AEMeasurable (fun X => ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * M) *
        (statRemainder d s V β ρβ (N := N) (Torus.realMode k) X) ^ 2)) G := fun k =>
      (ENNReal.measurable_ofReal.comp (measurable_const.mul
        ((eqrem_statRemainder_meas hd hs0 hsd V hV hβpos hρ hN (hck k)).pow_const 2))).aemeasurable
    have hnn : ∀ k : NonzeroLattice d, 0 ≤ 18 * C₁ ^ 2 * deltaN d s N * Lattice.jp k.1 ^ (-(2 * (M - 2))) :=
      fun k => by have := Real.rpow_nonneg (hjp k).le (-(2 * (M - 2))); positivity
    have hsum' : Summable fun k : NonzeroLattice d => 18 * C₁ ^ 2 * deltaN d s N * Lattice.jp k.1 ^ (-(2 * (M - 2))) :=
      hsum.mul_left _
    calc ∫⁻ X, coordEnergy M (fun k => statRemainder d s V β ρβ (N := N) (Torus.realMode k) X) ∂G
        = ∫⁻ X, ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * M) *
            (statRemainder d s V β ρβ (N := N) (Torus.realMode k) X) ^ 2) ∂G := lintegral_congr hfun
      _ = ∑' k : NonzeroLattice d, ∫⁻ X, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * M) *
            (statRemainder d s V β ρβ (N := N) (Torus.realMode k) X) ^ 2) ∂G := lintegral_tsum hmeas
      _ ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal (18 * C₁ ^ 2 * deltaN d s N * Lattice.jp k.1 ^ (-(2 * (M - 2)))) :=
          ENNReal.tsum_le_tsum hmode
      _ = ENNReal.ofReal (∑' k : NonzeroLattice d, 18 * C₁ ^ 2 * deltaN d s N * Lattice.jp k.1 ^ (-(2 * (M - 2)))) :=
          (ENNReal.ofReal_tsum_of_nonneg hnn hsum').symm
      _ ≤ ENNReal.ofReal (max C₁ (18 * C₁ ^ 2 * S + 1) * deltaN d s N) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [tsum_mul_left]
          calc 18 * C₁ ^ 2 * deltaN d s N * S = (18 * C₁ ^ 2 * S) * deltaN d s N := by ring
            _ ≤ (18 * C₁ ^ 2 * S + 1) * deltaN d s N := by gcongr; linarith
            _ ≤ _ := by gcongr; exact le_max_right _ _

end HRS.MD.EQRem

end
