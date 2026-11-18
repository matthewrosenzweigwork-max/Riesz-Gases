import HRS.MS.MfeConfAux133

/-!
# S.B.1 (SB5), packet R3 (part 0): the converse of the tilting identity

`sb1_kl_tilted_conv`: if `f` is bounded above, `ν ≪ P.tilted f` has finite relative entropy against the tilted law, then
`H(ν|P) < ∞` and `f ∈ L¹(ν)`.  `sb1_Q_conv`: for the modulated Gibbs reference `Q_k`, `H(ν|Q_k) < ∞` implies
`H(ν|μ^{⊗N}) < ∞` and `En_k ∈ L¹(ν)` (no dimension restriction; this replaces `sb1_relEntropy_split` for the premise of `SbMovEnt`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_kl_tilted_conv {α : Type*} [MeasurableSpace α] (P ν : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] {f : α → ℝ} (hexp : Integrable (fun x => Real.exp (f x)) P) {C : ℝ}
    (hC : ∀ x, f x ≤ C) (h : klDiv ν (P.tilted f) ≠ ⊤) : klDiv ν P ≠ ⊤ ∧ Integrable f ν := by
  obtain ⟨hνQ, hint⟩ := klDiv_ne_top_iff.1 h
  have hνP : ν ≪ P := hνQ.trans (tilted_absolutelyContinuous P f)
  have e := llr_tilted_right hνP hexp
  set c : ℝ := Real.log (∫ z, Real.exp (f z) ∂P) with hc
  have hneg : Integrable (fun x => Real.exp (-llr ν P x)) ν :=
    (Measure.integrable_toReal_rnDeriv (μ := P) (ν := ν)).congr (exp_neg_llr hνP).symm
  have hgm : AEStronglyMeasurable (llr ν P) ν := (measurable_llr ν P).aestronglyMeasurable
  have hbd : ∀ᵐ x ∂ν, ‖llr ν P x‖ ≤ (|llr ν (P.tilted f) x| + |C - c|) + Real.exp (-llr ν P x) := by
    filter_upwards [e] with x hx
    have h1 : llr ν P x ≤ llr ν (P.tilted f) x + C - c := by
      have := hC x
      -- llr ν Q = -f + c + llr ν P
      linarith
    have h2 : llr ν (P.tilted f) x + C - c ≤ |llr ν (P.tilted f) x| + |C - c| := by
      have := le_abs_self (llr ν (P.tilted f) x)
      have := le_abs_self (C - c)
      linarith
    have h3 : -llr ν P x ≤ Real.exp (-llr ν P x) := by linarith [Real.add_one_le_exp (-llr ν P x)]
    have h4 := Real.exp_pos (-llr ν P x)
    have h5 := abs_nonneg (llr ν (P.tilted f) x)
    have h6 := abs_nonneg (C - c)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hg : Integrable (llr ν P) ν :=
    Integrable.mono' ((hint.abs.add (integrable_const _)).add hneg) hgm hbd
  refine ⟨klDiv_ne_top hνP hg, ?_⟩
  have : Integrable (fun x => llr ν P x - llr ν (P.tilted f) x + c) ν := (hg.sub hint).add (integrable_const _)
  refine this.congr ?_
  filter_upwards [e] with x hx
  rw [hx]; ring

variable {s : ℝ} {ρ0 : Euc d → ℝ} {Cρ M1 : ℝ} {k : Euc d → ℝ}

theorem sb1_Q_conv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β)
    (hk : Sb1KerU d s k) (R : Sb1Rho ρ0 Cρ M1) {ν : Measure (Whole.EucConfig d N)} [IsProbabilityMeasure ν]
    (hν : relEntropy ν (Whole.modulatedGibbs k N β (Whole.withDensityReal ρ0)) ≠ ⊤) :
    relEntropy ν (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) ≠ ⊤ ∧
      Integrable (sb1En k ρ0 : Whole.EucConfig d N → ℝ) ν := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  have hK : 0 < Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ0) := by
    rw [sb1_K_eq R]; exact sb1_Kpi_pos' hd hs0 hsd hN hβ.le hk R
  have hexp : Integrable (fun X : Whole.EucConfig d N =>
      Real.exp (-β * N * Whole.modulatedEnergy k X (Whole.withDensityReal ρ0)))
      (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) := by
    refine Integrable.of_bound (C := sb1CwR d s Cρ M1 β N)
      (Real.measurable_exp.comp ((sb1_measurable_modulatedEnergy hk.meas _).const_mul _)).aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sb1_modEnergy_eq R.dens]
    exact sb1_E_le hd hs0 hsd hN hβ.le hk R X
  have hC : ∀ X : Whole.EucConfig d N, -β * N * Whole.modulatedEnergy k X (Whole.withDensityReal ρ0) ≤
      β * N * (sb1CG d s Cρ M1 + sb1kap s * M1) := by
    intro X
    have := sb1_E_le hd hs0 hsd hN hβ.le hk R X
    rw [← sb1_modEnergy_eq R.dens] at this
    exact Real.exp_le_exp.1 this
  rw [sb1_modGibbs_tilted R hK] at hν
  obtain ⟨h1, h2⟩ := sb1_kl_tilted_conv _ ν hexp hC (by simpa only [relEntropy] using hν)
  refine ⟨by simpa only [relEntropy] using h1, ?_⟩
  have h3 : Integrable (fun X : Whole.EucConfig d N => -β * N * sb1En k ρ0 X) ν := by
    refine h2.congr (Eventually.of_forall fun X => ?_)
    simp only [sb1_modEnergy_eq R.dens]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : (-β * N) ≠ 0 := by
    have : 0 < β * N := mul_pos hβ hn
    intro h; linarith
  have := h3.const_mul (-β * N)⁻¹
  refine this.congr (Eventually.of_forall fun X => ?_)
  simp only
  field_simp
