import HRS.MC.S7S7dAux6
import HRS.MC.S7S7c

/-!
# Packet `s7_S7d_uniform_limits`, helper 7: finite-dimensional core of (R2)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_core_R2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {p : ℕ} (κ : Fin p → NonzeroLattice d)
    {w : Torus d → ℝ} (hw : Torus.IsSmooth w) {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ f : NegSobolev d r → ℝ, s7d_Cl f → ∀ u u' : NegSobolev d r,
      ‖u‖ ≤ 1 → ‖u'‖ ≤ 1 →
      |∫ X, sed_Y (sed_Q d s N γ ρ) w X *
            iteratedFDeriv ℝ 2 f (HRS.MC.Sec7.S7c.s7c_iota r κ
              (centeredStat (sed_Q d s N γ ρ) (fun a => s7_phi r (κ a)) X)) ![u, u'] ∂(sed_Q d s N γ ρ) -
        ∑ c, (∫ x, w x * responseInverse (periodicRiesz d s) (withDensityReal ρ) γ (s7_phi r (κ c)) x
            ∂(withDensityReal ρ)) *
          ∫ z, iteratedFDeriv ℝ 3 f (HRS.MC.Sec7.S7c.s7c_iota r κ z) ![u, u', s7_eps r (κ c)]
            ∂(multivariateGaussian 0 (sed_Cmat d s γ ρ (fun a => s7_phi r (κ a))))| ≤ η := by
  classical
  set φ : Fin p → Torus d → ℝ := fun a => s7_phi r (κ a) with hφdef
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.MC.Sec7.S7a.s7a_phi_smooth r (κ a)
  set φ' : Fin (p + 1) → Torus d → ℝ := Fin.cons w φ with hφ'def
  have hφ' : ∀ a, Torus.IsSmooth (φ' a) := s7d_cons_smooth hw hφ
  have hQ : ∀ n : ℕ, IsProbabilityMeasure (sed_Q d s (n + 1) γ ρ) := fun n =>
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ (n + 1) (by omega)
  have hmeas : ∀ n : ℕ, Measurable (centeredStat (sed_Q d s (n + 1) γ ρ) φ') := fun n =>
    HRS.MC.SEdge.B10b.b10b_meas hd hs0 hs hγ hρ (by omega) hφ' _
  let μ : ℕ → Measure (EuclideanSpace ℝ (Fin (p + 1))) := fun n =>
    (sed_Q d s (n + 1) γ ρ).map (centeredStat (sed_Q d s (n + 1) γ ρ) φ')
  haveI hμ : ∀ n, IsProbabilityMeasure (μ n) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hmeas n).aemeasurable).2 (hQ n)
  set ν : Measure (EuclideanSpace ℝ (Fin (p + 1))) :=
    multivariateGaussian 0 (sed_Cmat d s γ ρ φ') with hν
  have hweak : ∀ F : EuclideanSpace ℝ (Fin (p + 1)) → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun n => ∫ x, F x ∂(μ n)) atTop (𝓝 (∫ x, F x ∂ν)) := by
    intro F hF hb
    have h1 := (HRS.MC.SEdge.B10b.sed_B10b_clt_proof hd hs0 hs hγ hρ hφ' hF hb).comp
      (tendsto_add_atTop_nat 1)
    refine h1.congr fun n => ?_
    simp only [Function.comp]
    exact (integral_map (hmeas n).aemeasurable hF.aestronglyMeasurable).symm
  obtain ⟨C4, hC4⟩ := s7d_fourth_moment hd hs0 hs hγ hρ hφ'
  have hmom : ∀ n, Integrable (fun x : EuclideanSpace ℝ (Fin (p + 1)) => ‖x‖ ^ ((2 : ℝ) + 2)) (μ n) ∧
      ∫ x, ‖x‖ ^ ((2 : ℝ) + 2) ∂(μ n) ≤ C4 := by
    intro n
    obtain ⟨h1, h2⟩ := hC4 (n + 1) (by omega)
    have hc : Continuous fun x : EuclideanSpace ℝ (Fin (p + 1)) => ‖x‖ ^ ((2 : ℝ) + 2) := by
      simp only [s7d_rpow_four]; fun_prop
    refine ⟨?_, ?_⟩
    · exact (integrable_map_measure hc.aestronglyMeasurable (hmeas n).aemeasurable).2 h1
    · rw [integral_map (hmeas n).aemeasurable hc.aestronglyMeasurable]
      exact h2
  set ι := HRS.MC.Sec7.S7c.s7c_iota r κ with hι
  set T := s7d_tail p with hT
  set h : EuclideanSpace ℝ (Fin (p + 1)) →L[ℝ] ℝ := EuclideanSpace.proj 0 with hh
  obtain ⟨n₀, hn₀⟩ := s7d_uniform_ident μ ν hweak hmom h zero_le_one (‖ι‖₊ * ‖T‖₊) hη
  refine ⟨n₀ + 1, fun N hN hN1 f hf u u' hu hu' => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : n ≥ n₀ := by omega
  set Ψ := s7d_Psi2 f ι u u' with hΨ
  have hΨc : Continuous Ψ := (s7d_Psi2_contDiff hf.1 ι u u').continuous
  have hb : ∀ x, |Ψ (T x)| ≤ 1 := by
    intro x
    refine (s7d_Psi2_bdd hf ι u u' (T x)).trans ?_
    calc ‖u‖ * ‖u'‖ ≤ 1 * 1 := mul_le_mul hu hu' (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hl : LipschitzWith (‖ι‖₊ * ‖T‖₊) (fun x => Ψ (T x)) := by
    have h1 := (s7d_Psi2_lip hf ι u u').comp T.lipschitzWith
    refine h1.weaken ?_
    have : ‖u‖₊ * ‖u'‖₊ ≤ 1 := by
      have a1 : ‖u‖₊ ≤ 1 := by exact_mod_cast hu
      have a2 : ‖u'‖₊ ≤ 1 := by exact_mod_cast hu'
      calc ‖u‖₊ * ‖u'‖₊ ≤ 1 * 1 := mul_le_mul' a1 a2
        _ = 1 := one_mul 1
    calc ‖ι‖₊ * (‖u‖₊ * ‖u'‖₊) * ‖T‖₊ ≤ ‖ι‖₊ * 1 * ‖T‖₊ := by gcongr
      _ = ‖ι‖₊ * ‖T‖₊ := by rw [mul_one]
  -- the pointwise limit (B13b)
  have hB := HRS.MC.SEdge.B13b.sed_B13b_linear_limit_proof hd hs0 hs hγ hρ hφ hw
    (ψ := Ψ) (s7d_Psi2_memCb hf ι u u')
  have hB' := hB.comp (tendsto_add_atTop_nat 1)
  have hcongr : ∀ m : ℕ, ∫ x, h x * Ψ (T x) ∂(μ m) =
      ∫ X, sed_Y (sed_Q d s (m + 1) γ ρ) w X *
        Ψ (centeredStat (sed_Q d s (m + 1) γ ρ) φ X) ∂(sed_Q d s (m + 1) γ ρ) := by
    intro m
    have hc : Continuous fun x : EuclideanSpace ℝ (Fin (p + 1)) => h x * Ψ (T x) :=
      h.continuous.mul (hΨc.comp T.continuous)
    rw [integral_map (hmeas m).aemeasurable hc.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    have e0 : (EuclideanSpace.proj (0 : Fin (p + 1)) : EuclideanSpace ℝ (Fin (p + 1)) →L[ℝ] ℝ)
        (centeredStat (sed_Q d s (m + 1) γ ρ) φ' X) = sed_Y (sed_Q d s (m + 1) γ ρ) w X :=
      s7d_cs_cons_zero _ w φ X
    have e1 : s7d_tail p (centeredStat (sed_Q d s (m + 1) γ ρ) φ' X) =
        centeredStat (sed_Q d s (m + 1) γ ρ) φ X := s7d_cs_cons _ w φ X
    show (EuclideanSpace.proj (0 : Fin (p + 1)) : EuclideanSpace ℝ (Fin (p + 1)) →L[ℝ] ℝ)
        (centeredStat (sed_Q d s (m + 1) γ ρ) φ' X) *
      Ψ (s7d_tail p (centeredStat (sed_Q d s (m + 1) γ ρ) φ' X)) = _
    rw [e0, e1]
  have hB'' : Tendsto (fun m : ℕ => ∫ x, h x * Ψ (T x) ∂(μ m)) atTop (𝓝 _) :=
    hB'.congr fun m => (hcongr m).symm
  have key := hn₀ n hn (fun x => Ψ (T x)) hb hl _ hB''
  rw [hcongr n] at key
  have hlim_eq : ∀ c : Fin p, ∫ z, fderiv ℝ Ψ z (stdVec c) ∂(multivariateGaussian 0 (sed_Cmat d s γ ρ φ)) =
      ∫ z, iteratedFDeriv ℝ 3 f (ι z) ![u, u', s7_eps r (κ c)]
        ∂(multivariateGaussian 0 (sed_Cmat d s γ ρ φ)) := by
    intro c
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show fderiv ℝ (s7d_Psi2 f ι u u') z (stdVec c) = _
    rw [s7d_Psi2_std (hf.1.of_le (by norm_num)) ι u u' z c,
      show ι (stdVec c) = s7_eps r (κ c) from HRS.MC.Sec7.S7c.s7c_iota_std r κ c]
  simp only [hlim_eq] at key
  exact key

end HRS.MC.Sec7.S7d

end
