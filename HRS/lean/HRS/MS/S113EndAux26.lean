import HRS.MS.S113EndAux25

/-!
# S11.3 endpoint (worker S11X), part 26: the exponential moment of the source for almost every time (X1b, a.e. version)

`S113XSourceAE`: the statement of `S113XSource` (measurability, vanishing when `L(t) = 0`, exponential moment) for almost every `t > 0`.
`s113x_source_of_identity_ae`: it follows from the a.e. source identity `S113XSourceIdentityAE` and S3.1 (copy of `s113x_source_of_identity`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-- X1 for almost every time. -/
def S113XSourceAE (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  ∃ cL C₀ : ℝ, 0 < cL ∧ 0 ≤ C₀ ∧
    ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
      ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ᵐ t : ℝ, 0 < t →
        Measurable (s113x_source d s q β N ρ t) ∧
        (r2MovL d s q β ρ t = 0 → ∀ X, s113x_source d s q β N ρ t X = 0) ∧
        (0 < r2MovL d s q β ρ t →
          ∫⁻ X, ENNReal.ofReal (Real.exp ((cL / r2MovL d s q β ρ t) * |s113x_source d s q β N ρ t X|))
              ∂(s113x_Q d s β ρ N t) ≤ ENNReal.ofReal (Real.exp C₀))

variable {d : ℕ}

open Classical in
theorem s113x_source_of_identity_ae (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {q β : ℝ}
    (hβ : 0 < β) (hq : 0 < q) {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ}
    {εstar r c₀ c C₁ : ℝ} (hj : 1 ≤ j) (hC₁ : 0 < C₁) (hε : 0 < εstar) (hc : 0 < c) (hc₀ : 0 < c₀)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁)
    (hid : S113XSourceIdentityAE d s q β ρ₀ j m εstar r c₀) :
    S113XSourceAE d s q β ρ₀ j m εstar r c₀ := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨M, Lm, E, c₁, hM1, hc₁, hE, hfam⟩ :=
    HRS.MS.MovEnt.s66_fam_exists hd hs0 hsd hq hβ hρ₀ hC₁ hc₀.le hNL
  obtain ⟨cp, hcp, Cp, hent⟩ := HRS.MS.Wr.euclidean_pair_entropy_proof hd hs0 hsd M Lm (β / 2) (2 * β) ((s + 1) * 1)
    (by positivity) (by linarith)
  set A : ℝ := Real.exp Cp with hA
  have hA0 : 0 < A := Real.exp_pos _
  refine ⟨cp / β, Real.log (A * Real.exp (A - 1) + 1), by positivity, ?_, ?_⟩
  · exact Real.log_nonneg (by have := mul_pos hA0 (Real.exp_pos (A - 1)); linarith)
  intro f0 hf0 ρ hρ' N hN
  filter_upwards [hid f0 hf0 ρ hρ' N hN] with t hidt ht0
  have ht : 0 ≤ t := ht0.le
  have hfm := hfam f0 hf0 ρ hρ'
  have hround : IsRound2Density d s M Lm (ρ t) := ⟨hfm.prob t ht, hfm.bound t ht, hfm.logm t ht⟩
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal (ρ t)) := HRS.MS.R2Mt.s92_isProb_mu hround.prob
  haveI hQp : IsProbabilityMeasure (s113x_Q d s β ρ N t) :=
    s113x_Q_prob hd hs0 hs hβ hq hρ₀ hC₁ hc₀ hNL hf0 hρ' hN ht
  set u : Euc d → Euc d := movU d s q β (ρ t) with hu
  have hdiff : Differentiable ℝ u := s113x_movU_diff hj hNL hc₀ hf0 hρ' ht
  have hfin : (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ u x‖) < ⊤ :=
    s113x_L_sup_lt_top hj hNL hC₁ hε hc₀ hf0 hρ' ht
  set Lt : ℝ := r2MovL d s q β ρ t with hLt
  have hLt0 : 0 ≤ Lt := by rw [hLt]; unfold r2MovL; exact ENNReal.toReal_nonneg
  have hb : ∀ x, ‖fderiv ℝ u x‖ ≤ Lt := fun x => by
    have : ENNReal.ofReal ‖fderiv ℝ u x‖ ≤ ⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ u x‖ := le_iSup (fun x : Euc d => ENNReal.ofReal ‖fderiv ℝ u x‖) x
    exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 this
  have hLip : LipschitzWith Lt.toNNReal u := by
    refine lipschitzWith_of_nnnorm_fderiv_le hdiff fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hLt0]
    exact hb x
  have hGu := (S99.s99_comm_isBounded (d := d) hs0 Lt.toNNReal hLip).measurable
  set F : EucConfig d N → ℝ := fun X =>
    pairEnergy (commutatorKernel d s u) X (HRS.Whole.withDensityReal (ρ t)) with hF
  have hFm : Measurable F := HRS.MS.Wr.wr9_measurable_pairEnergy hGu
  have hcoll : MeasurableSet (eucCollisionSet d N) := HRS.MP.RdRem.mrr_measurableSet_coll N
  have hsrc : s113x_source d s q β N ρ t = fun X =>
      if X ∈ eucCollisionSet d N then 0 else -β * N * (F X - ∫ Y, F Y ∂(s113x_Q d s β ρ N t)) := by
    funext X
    by_cases hX : X ∈ eucCollisionSet d N
    · simp [s113x_source, hX]
    · simp only [hX, ite_false]
      exact hidt ht0 X hX
  refine ⟨?_, ?_, ?_⟩
  · rw [hsrc]
    exact Measurable.ite hcoll measurable_const
      (measurable_const.mul (hFm.sub measurable_const))
  · intro h0
    have hconst := s113x_zero_lipschitz hdiff (fun x => by rw [← h0]; exact hb x)
    have hk0 : commutatorKernel d s u = fun _ _ => 0 := by
      funext x y
      unfold commutatorKernel
      rw [hconst x y, sub_self, inner_zero_left]
    have hF0 : F = fun _ => 0 := by
      funext X
      simp only [hF]
      rw [hk0]
      unfold pairEnergy
      simp
    intro X
    rw [hsrc]
    by_cases hX : X ∈ eucCollisionSet d N
    · simp [hX]
    · simp [hX, hF0]
  · intro hpos
    have hLpos : 0 < Lt := hpos
    set v : Euc d → Euc d := fun x => Lt⁻¹ • u x with hv
    have hvLip : LipschitzWith 1 v := s113x_unit_lipschitz hdiff hLpos hb
    have hK : IsBoundedPairKernel s ((s + 1) * 1) (commutatorKernel d s v) := by
      simpa using S99.s99_comm_isBounded (d := d) hs0 1 hvLip
    obtain ⟨⟨hint, hlog⟩, -⟩ := hent (ρ t) hround.prob hround.bdd hround.logMoment _ hK N hN β
      ⟨by linarith, by linarith⟩
    set Fv : EucConfig d N → ℝ := fun X =>
      pairEnergy (commutatorKernel d s v) X (HRS.Whole.withDensityReal (ρ t)) with hFv
    have hFvm : Measurable Fv := HRS.MS.Wr.wr9_measurable_pairEnergy hK.measurable
    set G : EucConfig d N → ℝ := fun X => (N : ℝ) * Fv X with hG
    have hGm : Measurable G := measurable_const.mul hFvm
    have hcongr : ∀ X : EucConfig d N, cp * (N : ℝ) * |Fv X| = cp * |G X| := fun X => by
      simp only [hG]
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N), mul_assoc]
    have hIpos := integral_exp_pos hint
    rw [mul_assoc, HRS.MS.R2Mt.s92_mul_deltaN hs hN, mul_one] at hlog
    have hIle := (Real.log_le_iff_le_exp hIpos).1 hlog
    have e : (fun X : EucConfig d N => Real.exp (cp * (N : ℝ) * |Fv X|)) =
        fun X => Real.exp (cp * |G X|) := by
      funext X; rw [hcongr X]
    have hint' : Integrable (fun X => Real.exp (cp * |G X|)) (s113x_Q d s β ρ N t) := by
      rw [← e]; exact hint
    have hIle' : ∫ X, Real.exp (cp * |G X|) ∂(s113x_Q d s β ρ N t) ≤ A := by
      rw [← e]; exact hIle
    have hcen := s113x_centered_exp (s113x_Q d s β ρ N t) G hGm hcp hint' hIle'
    -- the source in terms of `Fv`
    have hcomm : commutatorKernel d s u = fun x y => Lt * commutatorKernel d s v x y := by
      have := s113x_comm_smul (d := d) s Lt v
      rw [← this]
      congr 1
      funext x
      simp only [hv, smul_smul, mul_inv_cancel₀ hLpos.ne', one_smul]
    have hFF : ∀ X, F X = Lt * Fv X := fun X => by
      simp only [hF, hFv]
      rw [hcomm]
      exact s113x_pairEnergy_smul Lt _ X _
    have hGint : ∫ X, G X ∂(s113x_Q d s β ρ N t) = (N : ℝ) * ∫ X, Fv X ∂(s113x_Q d s β ρ N t) := by
      simp only [hG]; rw [integral_const_mul]
    have hFint : ∫ X, F X ∂(s113x_Q d s β ρ N t) = Lt * ∫ X, Fv X ∂(s113x_Q d s β ρ N t) := by
      simp only [hFF]; rw [integral_const_mul]
    have hpt : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
        (cp / β / Lt) * |s113x_source d s q β N ρ t X| =
          cp * |G X - ∫ Y, G Y ∂(s113x_Q d s β ρ N t)| := by
      intro X hX
      rw [hsrc]
      simp only [hX, ite_false]
      rw [hFF X, hFint, hGint]
      have e1 : -β * (N : ℝ) * (Lt * Fv X - Lt * ∫ X, Fv X ∂(s113x_Q d s β ρ N t)) =
          -(β * (N : ℝ) * Lt) * (Fv X - ∫ X, Fv X ∂(s113x_Q d s β ρ N t)) := by ring
      have e2 : G X - (N : ℝ) * ∫ X, Fv X ∂(s113x_Q d s β ρ N t) =
          (N : ℝ) * (Fv X - ∫ X, Fv X ∂(s113x_Q d s β ρ N t)) := by simp only [hG]; ring
      set D : ℝ := Fv X - ∫ X, Fv X ∂(s113x_Q d s β ρ N t) with hD
      have h3 : |-(β * (N : ℝ) * Lt) * D| = β * (N : ℝ) * Lt * |D| := by
        rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
      have h4 : |(N : ℝ) * D| = (N : ℝ) * |D| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      rw [e1, e2, h3, h4]
      field_simp
    have hbd : ∀ X : EucConfig d N, ENNReal.ofReal (Real.exp ((cp / β / Lt) * |s113x_source d s q β N ρ t X|)) ≤
        ENNReal.ofReal (Real.exp (cp * |G X - ∫ Y, G Y ∂(s113x_Q d s β ρ N t)|)) + 1 := by
      intro X
      by_cases hX : X ∈ eucCollisionSet d N
      · have : s113x_source d s q β N ρ t X = 0 := by
          rw [hsrc]; simp [hX]
        rw [this]
        simp
      · rw [hpt X hX]
        exact le_self_add
    calc ∫⁻ X, ENNReal.ofReal (Real.exp ((cp / β / Lt) * |s113x_source d s q β N ρ t X|))
          ∂(s113x_Q d s β ρ N t)
        ≤ ∫⁻ X, (ENNReal.ofReal (Real.exp (cp * |G X - ∫ Y, G Y ∂(s113x_Q d s β ρ N t)|)) + 1)
          ∂(s113x_Q d s β ρ N t) := lintegral_mono hbd
      _ = ∫⁻ X, ENNReal.ofReal (Real.exp (cp * |G X - ∫ Y, G Y ∂(s113x_Q d s β ρ N t)|))
            ∂(s113x_Q d s β ρ N t) + 1 := by
          rw [lintegral_add_right _ measurable_const]
          simp
      _ ≤ ENNReal.ofReal (A * Real.exp (A - 1)) + 1 := by gcongr
      _ = ENNReal.ofReal (Real.exp (Real.log (A * Real.exp (A - 1) + 1))) := by
          have hpos' : 0 < A * Real.exp (A - 1) + 1 := by
            have := mul_pos hA0 (Real.exp_pos (A - 1)); linarith
          rw [Real.exp_log hpos', ENNReal.ofReal_add (mul_pos hA0 (Real.exp_pos _)).le zero_le_one,
            ENNReal.ofReal_one]

end HRS.MS.S113BD
