import HRS.MS.WsStatAux3
import HRS.MS.QsfStat1
import HRS.MS.WrEnt

/-!
# S21 packet C: stationary energy and second moments for S2.1 (i)

For a random configuration `Y` with `law P Y = P_{N,beta} = HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N beta`
(this is what `GibbsInvariant` gives for `Y = X t`, `t <= T`):

* `s21_canonical_eq`: `P_{N,beta} = HRS.Whole.modulatedGibbs (rieszKernel d s) N beta (thermalMeasure d s a beta)`, all `0 <= s < d`;
* `s21_energy_integral_stationary`: `E |F_N(Y, rho_beta)| <= K deltaN` with `K = K(d,s,a,beta)`, with integrability
  (`euclidean_pair_entropy_self` at `f = P_{N,beta}`, `relEntropy f f = 0`; no junk value: `Integrable` is part of the claim);
* `s21_lintegral_energy_le`: for the completed energy `F + o >= 0` a.s.: `E|F + o| <= E|F| + o` (as `ENNReal`);
* `s21_second_moment_stationary`: `E_P pair(empirical Y, |x|^2) <= M2` and `pair(rho_beta, |x|^2) <= M2`, `M2 = M2(d,s,a,beta)`
  (exchangeability, `S45.s45_static_all`: the first marginal has a bounded density against the thermal measure).

Used by the trace comparison `s56_trace_moment` (hypotheses `E_{N,1} != top`, second moments `<= M2`) and for the rate
`E_{N,1} <= C o_N` (`s21_deltaN_le_oN`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s21_canonical_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (N : ℕ) :
    HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β =
      HRS.Whole.modulatedGibbs (rieszKernel d s) N β (thermalMeasure d s a β) := by
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    exact HRS.MS.Can2.logThermal_canonical_proof hd a β ha hβ N
  · exact (HRS.MS.Can2.euc_thermal_canonical_proof hd h0 hsd a β ha hβ).1 N

theorem s21_lintegral_energy_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {G : Ω → ℝ} (o A : ℝ) (hG : Integrable G P)
    (hnn : ∀ᵐ ζ ∂P, 0 ≤ G ζ + o) (hA : ∫ ζ, |G ζ| ∂P ≤ A) :
    ∫⁻ ζ, ENNReal.ofReal |G ζ + o| ∂P ≤ ENNReal.ofReal (A + o) := by
  have hGo : Integrable (fun ζ => G ζ + o) P := hG.add (integrable_const o)
  have e1 : ∫⁻ ζ, ENNReal.ofReal |G ζ + o| ∂P = ∫⁻ ζ, ENNReal.ofReal (G ζ + o) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnn] with ζ hζ
    rw [abs_of_nonneg hζ]
  rw [e1, ← ofReal_integral_eq_lintegral_ofReal hGo hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_add hG (integrable_const o), integral_const]
  simp only [probReal_univ, one_smul]
  have : ∫ ζ, G ζ ∂P ≤ ∫ ζ, |G ζ| ∂P := integral_mono hG hG.abs fun ζ => le_abs_self _
  linarith

theorem s21_energy_integral_stationary (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Y : Ω → EucConfig d N), Measurable Y →
        law P Y = HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β →
        Integrable (fun ζ => |rieszModulatedEnergy d s (Y ζ) (HRS.Whole.withDensityReal ρβ)|) P ∧
        ∫ ζ, |rieszModulatedEnergy d s (Y ζ) (HRS.Whole.withDensityReal ρβ)| ∂P ≤ K * HRS.deltaN d s N := by
  by_cases hex : ∃ ρ₁ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ₁
  · obtain ⟨ρ₁, h₁⟩ := hex
    obtain ⟨Λ, hΛ⟩ := s21_thermal_bounded hd hs0 hsd ha hβ
    obtain ⟨hp1, hb1, hl1⟩ := hΛ ρ₁ h₁
    obtain ⟨c, hc, C, hall⟩ := HRS.MS.Wr.euclidean_pair_entropy_self_proof hd hs0 hsd Λ
      (∫ x, Real.log (2 + ‖x‖) ∂(HRS.Whole.withDensityReal ρ₁)) (β / 2) (2 * β) (by positivity) (by linarith)
    refine ⟨max C 0, le_max_right _ _, fun ρβ hρβ N hN Ω _ P _ Y hY hlaw => ?_⟩
    have hρeq : ρβ = ρ₁ := (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ).trans
      (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ h₁).symm
    subst hρeq
    obtain ⟨-, hf⟩ := hall ρβ hp1 hb1 (fun _ => ⟨hl1, le_rfl⟩) N hN β
      ⟨by linarith, by linarith⟩
    have hprob : IsProbabilityMeasure (law P Y) := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
    have hρT : ρβ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ
    have hmod : HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρβ) =
        HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β := by
      rw [s21_canonical_eq hd hs0 hsd ha hβ N, hρT]; rfl
    have hrel : relEntropy (law P Y) (HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρβ)) = 0 := by
      have hprobC : IsProbabilityMeasure (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β) := by
        rw [← hlaw]; exact hprob
      rw [hmod, hlaw]
      exact InformationTheory.klDiv_self _
    obtain ⟨hI, hB⟩ := hf (law P Y) hprob (by rw [hrel]; exact ENNReal.zero_lt_top)
    rw [hrel] at hB
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hmeas : AEStronglyMeasurable (fun X : EucConfig d N =>
        (N : ℝ) * |HRS.Whole.modulatedEnergy (rieszKernel d s) X (HRS.Whole.withDensityReal ρβ)|) (Measure.map Y P) := hI.1
    have hI' : Integrable (fun ζ => (N : ℝ) * |rieszModulatedEnergy d s (Y ζ) (HRS.Whole.withDensityReal ρβ)|) P :=
      (integrable_map_measure hmeas hY.aemeasurable).1 hI
    have hI'' : Integrable (fun ζ => |rieszModulatedEnergy d s (Y ζ) (HRS.Whole.withDensityReal ρβ)|) P := by
      have := hI'.const_mul (N : ℝ)⁻¹
      refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
      simp only
      field_simp
    refine ⟨hI'', ?_⟩
    have h1 : ∫ ζ, (N : ℝ) * |rieszModulatedEnergy d s (Y ζ) (HRS.Whole.withDensityReal ρβ)| ∂P ≤
        C * ((0 : ℝ≥0∞).toReal + N * HRS.deltaN d s N) := by
      have := integral_map hY.aemeasurable hmeas
      refine le_of_eq_of_le ?_ hB
      exact this.symm
    simp only [ENNReal.toReal_zero, zero_add] at h1
    rw [integral_const_mul] at h1
    have hδ := s21_deltaN_pos hs0 hsd N (by omega)
    have h2 : ∫ ζ, |rieszModulatedEnergy d s (Y ζ) (HRS.Whole.withDensityReal ρβ)| ∂P ≤ C * HRS.deltaN d s N := by
      have : (N : ℝ) * ∫ ζ, |rieszModulatedEnergy d s (Y ζ) (HRS.Whole.withDensityReal ρβ)| ∂P ≤
          (N : ℝ) * (C * HRS.deltaN d s N) := by linarith
      exact le_of_mul_le_mul_left this hN0
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le)
  · refine ⟨0, le_rfl, fun ρβ hρβ => ?_⟩
    exact absurd ⟨ρβ, hρβ⟩ hex

theorem s21_thermal_second_integrable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) :
    Integrable (fun x : Euc d => ‖x‖ ^ 2) (thermalMeasure d s a β) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have hμ : thermalMeasure d s a β = HRS.Whole.withDensityReal (thermalDensity d s a β) := rfl
  obtain ⟨Cp, hCp0, hCp⟩ := S45.s45_poly_le (c := c / 4) (by have := hT.hc; positivity)
  rw [hμ, HRS.MS.TcR.tc2_integrable_nu hT.prob]
  have hg := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d (b := c / 2) (by have := hT.hc; positivity)
  refine Integrable.mono' (hg.const_mul (C * Cp ^ 2))
    ((hT.prob.measurable.mul (measurable_norm.pow_const 2)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  have hn := norm_nonneg y
  have hl1 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith
  have hl2 : (1 + ‖y‖) ^ 2 ≤ (Cp * Real.exp (c / 4 * ‖y‖ ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (hCp ‖y‖ hn) 2
  have e : (Cp * Real.exp (c / 4 * ‖y‖ ^ 2)) ^ 2 = Cp ^ 2 * Real.exp (c / 2 * ‖y‖ ^ 2) := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have e2 : Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2) =
      Real.exp (-(c / 2 * ‖y‖ ^ 2)) := by rw [← Real.exp_add]; congr 1; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hT.prob.nonneg y) (sq_nonneg _))]
  calc thermalDensity d s a β y * ‖y‖ ^ 2
      ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (Cp ^ 2 * Real.exp (c / 2 * ‖y‖ ^ 2)) := by
        refine mul_le_mul ?_ ((hl1.trans hl2).trans e.le) (sq_nonneg _) (by have := hT.C0; positivity)
        exact (le_abs_self _).trans (hT.h0 y)
    _ = (C * Cp ^ 2) * (Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
    _ = _ := by rw [e2]

theorem s21_second_moment_stationary (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) :
    ∃ M₂ : ℝ, 0 ≤ M₂ ∧
      (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
        HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) (fun x => ‖x‖ ^ 2) ≤ M₂) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Y : Ω → EucConfig d N), Measurable Y →
        law P Y = HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β →
        ∫⁻ ζ, ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) (fun x => ‖x‖ ^ 2)) ∂P ≤ ENNReal.ofReal M₂ := by
  obtain ⟨C, hC0, hCs⟩ := S45.s45_static_all hd hs0 hsd ha hβ
  have hint := s21_thermal_second_integrable hd hs0 hsd ha hβ
  set m₂ : ℝ := ∫ x, ‖x‖ ^ 2 ∂(thermalMeasure d s a β) with hm₂
  have hm₂0 : 0 ≤ m₂ := integral_nonneg fun x => sq_nonneg _
  refine ⟨(C + 1) * m₂, by positivity, ?_, ?_⟩
  · intro ρβ hρβ
    have hρeq : ρβ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ
    subst hρeq
    show ∫ x, ‖x‖ ^ 2 ∂(thermalMeasure d s a β) ≤ _
    nlinarith
  · intro N hN Ω _ P _ Y hY hlaw
    obtain ⟨hprob, hexch, -, ⟨φ, hφm, hφeq, hφb, -, -⟩, -⟩ := hCs N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hexch' : HRS.External.Entropy.IsExchangeable
        (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β) := fun σ => hexch σ
    have hmarg : ∀ i : Fin N, ∫⁻ ζ, ENNReal.ofReal (‖Y ζ i‖ ^ 2) ∂P ≤ ENNReal.ofReal (C * m₂) := by
      intro i
      have h1 : P.map (fun ζ => Y ζ i) = HRS.Whole.firstMarginal
          (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β) := by
        unfold HRS.Whole.firstMarginal
        rw [dif_pos (by omega : 0 < N)]
        have h0 := hexch'.marginal_eq i ⟨0, by omega⟩
        have hg : Measurable (fun ζ => Y ζ i) := (measurable_pi_apply i).comp hY
        have e1 : P.map (fun ζ => Y ζ i) = (P.map Y).map (fun x => x i) :=
          (Measure.map_map (measurable_pi_apply i) hY).symm
        have hlaw' : P.map Y = HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β := hlaw
        rw [e1, hlaw']
        exact h0
      have hm : Measurable fun x : Euc d => ENNReal.ofReal (‖x‖ ^ 2) :=
        ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)
      have h2 : ∫⁻ ζ, ENNReal.ofReal (‖Y ζ i‖ ^ 2) ∂P =
          ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(P.map (fun ζ => Y ζ i)) :=
        (lintegral_map hm ((measurable_pi_apply i).comp hY)).symm
      rw [h2, h1, hφeq, lintegral_withDensity_eq_lintegral_mul₀ ?_ ?_]
      · have h3 : ∀ x : Euc d, (ENNReal.ofReal (φ x) * ENNReal.ofReal (‖x‖ ^ 2)) ≤
            ENNReal.ofReal C * ENNReal.ofReal (‖x‖ ^ 2) := fun x =>
          mul_le_mul' (ENNReal.ofReal_le_ofReal (hφb x).2) le_rfl
        calc ∫⁻ x, (fun x => ENNReal.ofReal (φ x)) x * ENNReal.ofReal (‖x‖ ^ 2) ∂(thermalMeasure d s a β)
            ≤ ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (‖x‖ ^ 2) ∂(thermalMeasure d s a β) :=
              lintegral_mono fun x => h3 x
          _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(thermalMeasure d s a β) :=
              lintegral_const_mul _ hm
          _ = ENNReal.ofReal (C * m₂) := by
              rw [hm₂, ← ofReal_integral_eq_lintegral_ofReal hint
                (Filter.Eventually.of_forall fun x => sq_nonneg _), ENNReal.ofReal_mul hC0]
      · exact (ENNReal.measurable_ofReal.comp hφm).aemeasurable
      · exact hm.aemeasurable
    have e : ∀ ζ, HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) (fun x => ‖x‖ ^ 2) = (N : ℝ)⁻¹ * ∑ i, ‖Y ζ i‖ ^ 2 :=
      fun ζ => HRS.Whole.pair_empirical (by omega) _ _
    simp_rw [e]
    have e2 : ∀ ζ, ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, ‖Y ζ i‖ ^ 2) =
        ENNReal.ofReal (N : ℝ)⁻¹ * ∑ i, ENNReal.ofReal (‖Y ζ i‖ ^ 2) := fun ζ => by
      rw [ENNReal.ofReal_mul (inv_nonneg.2 hN0.le),
        ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    simp_rw [e2]
    have hmi : ∀ i : Fin N, Measurable fun ζ => ENNReal.ofReal (‖Y ζ i‖ ^ 2) := fun i =>
      ENNReal.measurable_ofReal.comp (((measurable_pi_apply i).comp hY).norm.pow_const 2)
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hmi i),
      lintegral_finsetSum _ fun i _ => hmi i]
    calc ENNReal.ofReal (N : ℝ)⁻¹ * ∑ i, ∫⁻ ζ, ENNReal.ofReal (‖Y ζ i‖ ^ 2) ∂P
        ≤ ENNReal.ofReal (N : ℝ)⁻¹ * ∑ _i : Fin N, ENNReal.ofReal (C * m₂) :=
          mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hmarg i)
      _ = ENNReal.ofReal (C * m₂) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (inv_nonneg.2 hN0.le),
            inv_mul_cancel₀ hN0.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal ((C + 1) * m₂) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)

end HRS.MS.S21
