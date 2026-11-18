import HRS.MS.DecStatAux3

/-!
# SA4, packet 4: the remainder `R = σ ∫ ½ Comm_N(Mᵀ∇U^{r,t_a}φ_a)` with the additive error `c₂ e_N`

`Sa4Rem`: the pathwise bound `|g_a(rr)| ≤ κ_a (F + o + ce)` of the integrand of the remainder (in `ofReal` form);
`sa4_rem_ae`, `sa4_rem_L1`, `sa4_rem_L2`: a.s. bound of the remainder by `∑ σ κ_a (∫ (F+o) + ce T)`, and the `L¹`, `L²` moment bounds
`≤ ∑ σ κ_a ((𝔈 + ce) T)`, `≤ ∑ σ κ_a ((𝔈' + ce) T)` (copies of `sa2_rem_*` of the S.A.2 engine with the extra constant `ce`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.MainRdStat HRS.MS.ZeroTemp
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.DecStat

variable {d : ℕ}

/-- The pathwise bound of the remainder integrand. -/
def Sa4Rem (S : WholeMainData d) (N : ℕ) (C₀c Λ ce : ℝ) {q : ℕ} (ts : Fin q → ℝ) (φ : Fin q → Euc d → ℝ)
    (κ : Fin q → ℝ) : Prop :=
  ∀ a : Fin q, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), ∀ X : EucConfig d N, Function.Injective X →
    ENNReal.ofReal |flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) rr (ts a) (φ a)) X (S.ρ N rr)| ≤
      ENNReal.ofReal (κ a) *
        (ENNReal.ofReal (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N rr)) +
          oNΛ d S.s C₀c (max Λ 1) N) + ENNReal.ofReal ce)

section Rem

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ}

/-- the a.s. bound of the remainder vector by the energy integral -/
theorem sa4_rem_ae {N : ℕ} {C₀c ce : ℝ} (hce : 0 ≤ ce) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) {κ : Fin q → ℝ} (hκ : ∀ a, 0 ≤ κ a)
    (hrem : Sa4Rem S N C₀c Λ ce ts φ κ)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal rr) ζ)) :
    ∀ᵐ ζ ∂(R N).P, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ≤
      ENNReal.ofReal (∑ a, S.sigma N * κ a) *
        ((∫⁻ rr in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr)) +
          ENNReal.ofReal ce * ENNReal.ofReal S.T) := by
  filter_upwards [hinj] with ζ hζ
  set G : ℝ≥0∞ := ∫⁻ rr in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) with hG
  set k : ℝ≥0∞ := ENNReal.ofReal ce * ENNReal.ofReal S.T with hk
  have hσ := sa2_sigma_nonneg S N
  have hcoef : ∀ a, 0 ≤ S.sigma N * κ a := fun a => mul_nonneg hσ (hκ a)
  have hone : ∀ a, ENNReal.ofReal |(sa2Rem S R N ts φ ζ) a| ≤
      ENNReal.ofReal (S.sigma N * κ a) * (G + k) := by
    intro a
    have hta := hts a
    have hsub : Set.Icc (0 : ℝ) (ts a) ⊆ Set.Icc (0 : ℝ) S.T := Set.Icc_subset_Icc_right hta.2
    simp only [sa2Rem, PiLp.toLp_apply]
    set g : ℝ → ℝ := fun rr => flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) rr (ts a) (φ a))
      ((R N).X (Real.toNNReal rr) ζ) (S.ρ N rr) with hg
    rw [abs_mul, abs_of_nonneg hσ, ENNReal.ofReal_mul hσ]
    have h1 : ENNReal.ofReal |∫ rr in Set.Icc (0 : ℝ) (ts a), g rr| ≤
        ∫⁻ rr in Set.Icc (0 : ℝ) (ts a), ENNReal.ofReal |g rr| := by
      have := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Set.Icc (0 : ℝ) (ts a))) g
      simpa [Real.enorm_eq_ofReal_abs] using this
    have hae : ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) (ts a))),
        ENNReal.ofReal |g rr| ≤ ENNReal.ofReal (κ a) *
          (ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) + ENNReal.ofReal ce) := by
      have h2 := ae_restrict_of_ae_restrict_of_subset hsub hζ
      filter_upwards [h2, ae_restrict_mem measurableSet_Icc] with rr hinjr hrr
      have hrT := hsub hrr
      have := hrem a rr hrr _ hinjr
      simpa [sa2En, HRS.MP.RdRem.mrrClamp_of_mem hrT] using this
    have hint : ∫⁻ rr in Set.Icc (0 : ℝ) (ts a), ENNReal.ofReal (κ a) *
        (ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) + ENNReal.ofReal ce) ≤ ENNReal.ofReal (κ a) * (G + k) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine mul_le_mul' le_rfl ?_
      rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      refine add_le_add (lintegral_mono_set hsub) ?_
      rw [hk]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (by linarith [hta.2]))
    calc ENNReal.ofReal (S.sigma N) * ENNReal.ofReal |∫ rr in Set.Icc (0 : ℝ) (ts a), g rr|
        ≤ ENNReal.ofReal (S.sigma N) * ∫⁻ rr in Set.Icc (0 : ℝ) (ts a), ENNReal.ofReal |g rr| := by
          gcongr
      _ ≤ ENNReal.ofReal (S.sigma N) * ∫⁻ rr in Set.Icc (0 : ℝ) (ts a), ENNReal.ofReal (κ a) *
            (ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) + ENNReal.ofReal ce) :=
          mul_le_mul' le_rfl (lintegral_mono_ae hae)
      _ ≤ ENNReal.ofReal (S.sigma N) * (ENNReal.ofReal (κ a) * (G + k)) := mul_le_mul' le_rfl hint
      _ = ENNReal.ofReal (S.sigma N * κ a) * (G + k) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hσ]
  calc ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖
      ≤ ENNReal.ofReal (∑ a, |(sa2Rem S R N ts φ ζ) a|) :=
        ENNReal.ofReal_le_ofReal (HRS.Main.A8P.a8p_norm_le_sum_abs _)
    _ = ∑ a, ENNReal.ofReal |(sa2Rem S R N ts φ ζ) a| :=
        ENNReal.ofReal_sum_of_nonneg fun a _ => abs_nonneg _
    _ ≤ ∑ a, ENNReal.ofReal (S.sigma N * κ a) * (G + k) := Finset.sum_le_sum fun a _ => hone a
    _ = ENNReal.ofReal (∑ a, S.sigma N * κ a) * (G + k) := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun a _ => hcoef a]

theorem sa4_rem_L1 (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hd : 1 ≤ d)
    {N : ℕ} (hN : 2 ≤ N) {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {C₀c ce : ℝ} (hC₀c : 0 ≤ C₀c) (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) (hce : 0 ≤ ce) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) {κ : Fin q → ℝ} (hκ : ∀ a, 0 ≤ κ a)
    (hrem : Sa4Rem S N C₀c Λ ce ts φ κ)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal rr) ζ)) :
    ∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ∂(R N).P ≤
      ENNReal.ofReal (∑ a, S.sigma N * κ a) *
        (ENNReal.ofReal (𝔈 N) * ENNReal.ofReal S.T + ENNReal.ofReal ce * ENNReal.ofReal S.T) := by
  haveI := (R N).isProb
  refine (lintegral_mono_ae (sa4_rem_ae hce ts hts φ hκ hrem hinj)).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine mul_le_mul' le_rfl ?_
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  exact add_le_add (sa2_G_moment hS hd hN hprog hC₀c hC₀) le_rfl

theorem sa4_rem_L2 (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hd : 1 ≤ d)
    {N : ℕ} (hN : 2 ≤ N) {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {C₀c ce : ℝ} (hC₀c : 0 ≤ C₀c) (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) (hce : 0 ≤ ce) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) {κ : Fin q → ℝ} (hκ : ∀ a, 0 ≤ κ a)
    (hrem : Sa4Rem S N C₀c Λ ce ts φ κ)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal rr) ζ))
    {χ : Euc d → ℝ} {m₀ : ℕ} {Ψ : ℕ → Set (Euc d → ℝ)} {𝔈' ε2 : ℕ → ℝ}
    (hE2 : EnergySmallness2Rd S R C₀ Λ χ m₀ Ψ 𝔈' ε2) :
    (∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (∑ a, S.sigma N * κ a) *
        (ENNReal.ofReal (𝔈' N) * ENNReal.ofReal S.T + ENNReal.ofReal ce * ENNReal.ofReal S.T) := by
  haveI := (R N).isProb
  have hN1 : 1 ≤ N := by omega
  set c : ℝ≥0∞ := ENNReal.ofReal (∑ a, S.sigma N * κ a) with hc
  set G : (R N).Ω → ℝ≥0∞ := fun ζ => ∫⁻ rr in Set.Icc (0 : ℝ) S.T,
    ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) with hG
  set k : ℝ≥0∞ := ENNReal.ofReal ce * ENNReal.ofReal S.T with hk
  have hae := sa4_rem_ae hce ts hts φ hκ hrem hinj
  have hGm : Measurable G := by
    have h := (sa2_en_meas hS hN1 hprog C₀c).comp (measurable_swap (α := ℝ) (β := (R N).Ω))
    exact sa11_lintegral_meas S.T (fun (r : ℝ) (ζ : (R N).Ω) => sa2En S R N C₀c Λ ζ r) h
  have h1 : ∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ^ (2 : ℝ) ∂(R N).P ≤
      ∫⁻ ζ, (c * (G ζ + k)) ^ (2 : ℝ) ∂(R N).P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with ζ hζ
    exact ENNReal.rpow_le_rpow hζ (by norm_num)
  have h2 : ∫⁻ ζ, (c * (G ζ + k)) ^ (2 : ℝ) ∂(R N).P = c ^ (2 : ℝ) * ∫⁻ ζ, (G ζ + k) ^ (2 : ℝ) ∂(R N).P := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun ζ => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  have h3 := sa2_G_moment2 hS hd hN hprog hC₀c hC₀ hE2
  have hmink := ENNReal.lintegral_Lp_add_le (μ := (R N).P) (p := 2) hGm.aemeasurable
    (measurable_const (a := k)).aemeasurable (by norm_num)
  have hk2 : (∫⁻ _ζ, k ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ) = k := by
    rw [lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul]
    norm_num
  rw [hk2] at hmink
  calc (∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ)
      ≤ (c ^ (2 : ℝ) * ∫⁻ ζ, (G ζ + k) ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ) := by
        gcongr
        exact h1.trans h2.le
    _ = c * (∫⁻ ζ, (G ζ + k) ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul]
        norm_num
    _ ≤ c * ((∫⁻ ζ, (G ζ) ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ) + k) := mul_le_mul' le_rfl hmink
    _ ≤ c * (ENNReal.ofReal (𝔈' N) * ENNReal.ofReal S.T + k) := mul_le_mul' le_rfl (add_le_add h3 le_rfl)

end Rem

end HRS.MS.DecStat
