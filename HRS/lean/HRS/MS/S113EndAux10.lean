import HRS.MS.S113EndAux9
import HRS.MS.R2SeAux1
import HRS.MS.R2MtAux1
import HRS.MS.S113EndAux7

/-!
# S11.3 endpoint (worker S113X), part 10: the exponential moment of the source from the source identity and S3.1 (X1b)

The source identity `W:r2mov:source-identity` (`R_N^t = -βN(F_N^{h_{u^t}} - E_{Q_N^t}F_N^{h_{u^t}})`) is the core `S113XSourceIdentity`
(calculus for non-translated trajectories, not in the library).  Given it, the exponential-moment core `S113XSource` is proved here
from the pressure theorem S3.1 (`euclidean_pair_entropy_proof`, kernel `h_u/L(t)`, the commutator kernel of a 1-Lipschitz field).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

section Centered

variable {α : Type*} [MeasurableSpace α]

/-- Centering costs a bounded factor in the exponential moment. -/
theorem s113x_centered_exp (Q : Measure α) [IsProbabilityMeasure Q] (G : α → ℝ) (hGm : Measurable G) {c A : ℝ}
    (hc : 0 < c) (hint : Integrable (fun x => Real.exp (c * |G x|)) Q)
    (hle : ∫ x, Real.exp (c * |G x|) ∂Q ≤ A) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * |G x - ∫ y, G y ∂Q|)) ∂Q ≤ ENNReal.ofReal (A * Real.exp (A - 1)) := by
  have hGi : Integrable (fun x => |G x|) Q := by
    refine Integrable.mono' (hint.const_mul (c⁻¹)) hGm.abs.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have := Real.add_one_le_exp (c * |G x|)
    have h2 : c * |G x| ≤ Real.exp (c * |G x|) := by linarith
    calc |G x| = c⁻¹ * (c * |G x|) := by field_simp
      _ ≤ c⁻¹ * Real.exp (c * |G x|) := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hc.le)
  have hE : c * |∫ y, G y ∂Q| ≤ A - 1 := by
    have h1 : |∫ y, G y ∂Q| ≤ ∫ y, |G y| ∂Q := abs_integral_le_integral_abs
    have h2 : c * ∫ y, |G y| ∂Q ≤ (∫ y, Real.exp (c * |G y|) ∂Q) - 1 := by
      have : ∫ y, (Real.exp (c * |G y|) - 1) ∂Q ≥ ∫ y, c * |G y| ∂Q := by
        refine integral_mono (hGi.const_mul c) (hint.sub (integrable_const 1)) fun y => ?_
        have := Real.add_one_le_exp (c * |G y|)
        linarith
      rw [integral_sub hint (integrable_const 1), integral_const_mul] at this
      simpa using this
    nlinarith
  have hpt : ∀ x, Real.exp (c * |G x - ∫ y, G y ∂Q|) ≤ Real.exp (c * |G x|) * Real.exp (A - 1) := by
    intro x
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : |G x - ∫ y, G y ∂Q| ≤ |G x| + |∫ y, G y ∂Q| := abs_sub _ _
    nlinarith
  have hA0 : 0 ≤ ∫ x, Real.exp (c * |G x|) ∂Q := integral_nonneg fun x => (Real.exp_pos _).le
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (c * |G x - ∫ y, G y ∂Q|)) ∂Q
      ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (c * |G x|) * Real.exp (A - 1)) ∂Q :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (∫ x, Real.exp (c * |G x|) * Real.exp (A - 1) ∂Q) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint.mul_const _)
          (Filter.Eventually.of_forall fun x => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le)]
    _ ≤ ENNReal.ofReal (A * Real.exp (A - 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le

end Centered

variable {d N : ℕ}

theorem s113x_pairEnergy_smul (c : ℝ) (h : Euc d → Euc d → ℝ) (X : EucConfig d N) (μ : Measure (Euc d)) :
    pairEnergy (fun x y => c * h x y) X μ = c * pairEnergy h X μ := by
  unfold pairEnergy
  simp only [integral_const_mul, ← Finset.mul_sum]
  ring

theorem s113x_comm_smul (s : ℝ) (c : ℝ) (v : Euc d → Euc d) :
    commutatorKernel d s (fun x => c • v x) = fun x y => c * commutatorKernel d s v x y := by
  funext x y
  unfold commutatorKernel
  rw [← smul_sub, real_inner_smul_left]

/-- The source identity `W:r2mov:source-identity` (S L8927-8933): `R_N^t = -βN(𝖥_N^{h_{u^t}} - E_{Q_N^t}𝖥_N^{h_{u^t}})`,
`h_u = (u(x)-u(y))·∇g(x-y)`, off the collision set. -/
def S113XSourceIdentity (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
    ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      s113x_source d s q β N ρ t X =
        -β * N * (pairEnergy (commutatorKernel d s (movU d s q β (ρ t))) X (HRS.Whole.withDensityReal (ρ t)) -
          ∫ Y, pairEnergy (commutatorKernel d s (movU d s q β (ρ t))) Y (HRS.Whole.withDensityReal (ρ t))
            ∂(s113x_Q d s β ρ N t))

theorem s113x_unit_lipschitz {u : Euc d → Euc d} (hu : Differentiable ℝ u) {L : ℝ} (hL : 0 < L)
    (hb : ∀ x, ‖fderiv ℝ u x‖ ≤ L) : LipschitzWith 1 (fun x => L⁻¹ • u x) := by
  have hv : Differentiable ℝ (fun x => L⁻¹ • u x) := fun x => (DifferentiableAt.const_smul (hu x) L⁻¹ : DifferentiableAt ℝ (fun x => L⁻¹ • u x) x)
  refine lipschitzWith_of_nnnorm_fderiv_le hv fun x => ?_
  have : fderiv ℝ (fun x => L⁻¹ • u x) x = L⁻¹ • fderiv ℝ u x := fderiv_const_smul (hu x) L⁻¹
  rw [this]
  have h1 : ‖L⁻¹ • fderiv ℝ u x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hL.le)]
    calc L⁻¹ * ‖fderiv ℝ u x‖ ≤ L⁻¹ * L := mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.2 hL.le)
      _ = 1 := inv_mul_cancel₀ hL.ne'
  exact_mod_cast h1

theorem s113x_zero_lipschitz {u : Euc d → Euc d} (hu : Differentiable ℝ u)
    (hb : ∀ x, ‖fderiv ℝ u x‖ ≤ 0) : ∀ x y, u x = u y := by
  have hz : ∀ x, fderiv ℝ u x = 0 := fun x => norm_le_zero_iff.1 (hb x)
  intro x y
  exact is_const_of_fderiv_eq_zero hu hz x y

theorem s113x_movU_diff {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ c C₁ : ℝ} (hj : 1 ≤ j)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) (hc₀ : 0 < c₀) {f0 : Euc d → ℝ}
    (hf0 : MovInitialClass ρ₀ j m εstar f0) {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) {t : ℝ} (ht : 0 ≤ t) :
    Differentiable ℝ (movU d s q β (ρ t)) := by
  obtain ⟨-, -, -, hdec⟩ := HRS.MS.MovEnt.s66_class_props hNL hf0 hρ hc₀.le t ht
  obtain ⟨-, -, hcd, -⟩ := hdec t ht
  exact hcd.differentiable (by exact_mod_cast (by omega : j ≠ 0))

open Classical in
theorem s113x_source_of_identity (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {q β : ℝ}
    (hβ : 0 < β) (hq : 0 < q) {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ}
    {εstar r c₀ c C₁ : ℝ} (hj : 1 ≤ j) (hC₁ : 0 < C₁) (hε : 0 < εstar) (hc : 0 < c) (hc₀ : 0 < c₀)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁)
    (hid : S113XSourceIdentity d s q β ρ₀ j m εstar r c₀) :
    S113XSource d s q β ρ₀ j m εstar r c₀ := by
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
  intro f0 hf0 ρ hρ' N hN t ht
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
      exact hid f0 hf0 ρ hρ' N hN t ht X hX
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
