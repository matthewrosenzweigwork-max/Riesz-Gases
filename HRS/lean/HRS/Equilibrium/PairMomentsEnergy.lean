/-
# HRS.Equilibrium.PairMomentsEnergy -- the energy term `E ∑_i |∇_i F_N(ψ)|²` (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsAssemble
import HRS.Equilibrium.PairMomentsLemmaD
import HRS.Equilibrium.PairMomentsTT

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

section AeRef

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- Under the pinned ensemble the coordinates are a.s. pairwise distinct (`μ` atomless). -/
theorem ae_distinct_pinned (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hatom : ∀ z : Torus d, μ {z} = 0) :
    ∀ᵐ X ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)),
      ∀ a b : Fin (n + 1), a ≠ b → X a ≠ X b := by
  rw [ae_all_iff]
  intro a
  rw [ae_all_iff]
  intro b
  by_cases hab : a = b
  · exact Eventually.of_forall fun X h => (h hab).elim
  · set h : Torus d → Torus d → ℝ := fun x z => if x = z then 1 else 0 with hh
    have hm : Measurable (Function.uncurry h) := by
      have hms : MeasurableSet {p : Torus d × Torus d | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
      have : Function.uncurry h = {p : Torus d × Torus d | p.1 = p.2}.indicator (fun _ => (1 : ℝ)) := by
        funext p; simp [hh, Set.indicator, Function.uncurry]
      rw [this]; exact measurable_const.indicator hms
    have hW : ∀ x : Torus d, ∫⁻ z, ‖h x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z)) ∂μ ≤ 0 := by
      intro x
      have hae : ∀ᵐ z ∂μ, z ≠ x := HRS.External.PoleVar.ae_ne_pt hatom x
      refine le_of_eq ?_
      rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)), lintegral_zero]
      filter_upwards [hae] with z hz
      simp [hh, Ne.symm hz]
    have h0 := pair_lintegral_le V hβ a b hab hm hW
    have h1 : ∫⁻ Y, ‖h (Y a) (Y b)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) = 0 :=
      le_antisymm h0 bot_le
    have hmeas : Measurable fun Y : Fin (n + 1) → Torus d => ‖h (Y a) (Y b)‖ₑ ^ 2 :=
      ((measurable_h_pair hm a b).enorm).pow_const 2
    have h2 := (lintegral_eq_zero_iff hmeas).1 h1
    filter_upwards [h2] with X hX _ heq
    simp [hh, heq] at hX

theorem ae_coord_pinned (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (i : Fin (n + 1))
    {P : Torus d → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ X ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)), P (X i) := by
  have hcard : n + 1 + Fintype.card Empty ≤ n + 1 := by simp
  have hdom := pinned_marginal_le_density (B := Empty) V hβ (N := n + 1) (n := n + 1) (Nat.succ_pos n) hcard
    (fun e : Empty => e.elim) i
  have hac : (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map (fun Y => Y i) ≪ μ :=
    (Measure.absolutelyContinuous_of_le hdom).trans (withDensity_absolutelyContinuous μ _)
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable (hac.ae_le hP)

end AeRef

section Corrected

/-- The row-centred gradient kernel `v_m(x,y) = ∂_{x_m}ψ(x,y) - ∫ ∂_{x_m}ψ(x,z) μ(dz)`. -/
def vcorr (μ : Measure (Torus d)) (ψ : Torus d → Torus d → ℝ) (m : Fin d) (x y : Torus d) : ℝ :=
  gradK ψ m x y - ∫ z, gradK ψ m x z ∂μ

theorem corrected_kernel (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {BA : ℝ} (hBA0 : 0 ≤ BA)
    (hBA : ∀ x, ∫⁻ y, ENNReal.ofReal (gradEnv s x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal BA)
    {ψ : Torus d → Torus d → ℝ} {K : ℝ}
    (hcan : ∀ x, Integrable (ψ x) (withDensityReal ρ) ∧ ∫ y, ψ x y ∂(withDensityReal ρ) = 0)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    (hgrad : ∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
      K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s))) (m : Fin d) :
    Measurable (Function.uncurry (vcorr (withDensityReal ρ) ψ m)) ∧
    IsCanonicalPair (withDensityReal ρ) (vcorr (withDensityReal ρ) ψ m) ∧
    (∀ x y, x ≠ y → |vcorr (withDensityReal ρ) ψ m x y| ≤ (|K| * (1 + BA)) * gradEnv s x y) ∧
    (∀ᵐ x ∂(withDensityReal ρ), ∫ z, gradK ψ m x z ∂(withDensityReal ρ) = 0) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hcm : Measurable fun x : Torus d => ∫ y, gradK ψ m x y ∂(withDensityReal ρ) :=
    ((measurable_gradK ψ m).stronglyMeasurable.integral_prod_right' (ν := withDensityReal ρ)).measurable
  refine ⟨?_, ?_, ?_, gradK_integral_ae_zero hd hρ hcan hsm hgrad hBA0 hBA m⟩
  · exact (measurable_gradK ψ m).sub (hcm.comp measurable_fst)
  · intro x
    have hi := integrable_gradK hgrad hatom m hBA x
    refine ⟨hi.sub (integrable_const _), ?_⟩
    unfold vcorr
    rw [integral_sub hi (integrable_const _), integral_const]
    simp
  · intro x y hxy
    have h1 : |gradK ψ m x y| ≤ K * gradEnv s x y := gradK_bound hgrad m hxy
    have h2 := abs_integral_gradK_le hgrad hatom m hBA0 hBA x
    have h3 : 1 ≤ gradEnv s x y := by
      unfold gradEnv
      have := Real.rpow_nonneg (PairCorrAux.rTrunc_nonneg x y) (1 - s)
      linarith
    unfold vcorr
    calc |gradK ψ m x y - ∫ z, gradK ψ m x z ∂(withDensityReal ρ)|
        ≤ |gradK ψ m x y| + |∫ z, gradK ψ m x z ∂(withDensityReal ρ)| := abs_sub _ _
      _ ≤ |K| * gradEnv s x y + |K| * BA * gradEnv s x y := by
          have e1 : K * gradEnv s x y ≤ |K| * gradEnv s x y :=
            mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
          have e2 : |K| * BA ≤ |K| * BA * gradEnv s x y := by
            have : 0 ≤ |K| * BA := by positivity
            nlinarith
          linarith
      _ = _ := by ring

end Corrected

section EnergyIdent

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

theorem energy_ae_eq (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hatom : ∀ z : Torus d, μ {z} = 0) {ψ : Torus d → Torus d → ℝ} (hsymm : ∀ x y, ψ x y = ψ y x)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    (hc0 : ∀ m : Fin d, ∀ᵐ x ∂μ, ∫ z, gradK ψ m x z ∂μ = 0) :
    ∀ᵐ X ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)),
      ∀ i : Fin (n + 1), ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 =
        ∑ m : Fin d, ENNReal.ofReal (4 * (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2) *
          ‖∑ j ∈ Finset.univ.erase i, vcorr μ ψ m (X i) (X j)‖ₑ ^ 2 := by
  have hall : ∀ᵐ X ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)),
      ∀ i : Fin (n + 1), ∀ m : Fin d, ∫ z, gradK ψ m (X i) z ∂μ = 0 := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro m
    exact ae_coord_pinned V hβ i (hc0 m)
  filter_upwards [ae_distinct_pinned V hβ hatom, hall] with X hX hc i
  rw [configGrad_norm_sq hsymm hsm X hX i]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hrow : ∑ j ∈ Finset.univ.erase i, gradK ψ m (X i) (X j) =
      ∑ j ∈ Finset.univ.erase i, vcorr μ ψ m (X i) (X j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold vcorr
    rw [hc i m, sub_zero]
  rw [hrow]
  set S : ℝ := ∑ j ∈ Finset.univ.erase i, vcorr μ ψ m (X i) (X j) with hS
  have e1 : ‖S‖ₑ ^ 2 = ENNReal.ofReal (S ^ 2) := by
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  rw [e1, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end EnergyIdent

section EnergyLarge

theorem energy_ref_large (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c Mmax M'max γmax Cq : ℝ) (Cu : ℝ) (hCu : 0 ≤ Cu)
    (δC C1 : ℝ) (hδC : 0 ≤ δC) (hC1 : 0 ≤ C1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V →
      (∀ x y : Torus d, x ≠ y → V.q x y ≤ Cu * wEnv s x y) → ∀ n : ℕ, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      RefDens V β n (δC * deltaN d s (n + 1)) C1 →
      ∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), (∀ x y, ψ x y = ψ y x) →
      IsCanonicalPair (withDensityReal ρ) ψ →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d) →
      (∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
        K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s))) →
        ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
            ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * K ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  obtain ⟨BA, BB, BC, hBA0, hBB0, hBC0, hEnv⟩ := gradEnv_bounds (d := d) hd hcrit Cu hCu ρ hΛ hΛ0.le
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set Cm : ℝ := δC * BA + C1 * BC with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set Vc : ℝ := E0 * BB with hVc
  have hVc0 : 0 ≤ Vc := by positivity
  refine ⟨d * (8 * Vc + 16 * Cm ^ 2) * (1 + BA) ^ 2, by positivity,
    fun V hV hVu n hn hκ hRD K ψ hsymm hcan hsm hgrad => ?_⟩
  set N : ℕ := n + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnR : (n : ℝ) ≤ N := by simp [hNdef]
  haveI : NeZero n := ⟨by omega⟩
  have hL2 := logEN_sq_le (N := N) hN1
  have hL0 : 0 ≤ logEN N := by linarith [logEN_pos' (N := N) hN1]
  set K' : ℝ := |K| * (1 + BA) with hK'
  have hker := fun m : Fin d => corrected_kernel hd hcrit hρ hBA0 hEnv.A hcan hsm hgrad m
  have hae := energy_ae_eq V hβ.le (n := n) hatom hsymm hsm (fun m => (hker m).2.2.2)
  have hrow : ∀ (m : Fin d) (i : Fin (n + 1)),
      ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal (2 * n) * ENNReal.ofReal (K' ^ 2 * Vc) + ENNReal.ofReal ((|K'| * Cm * logEN N) ^ 2) := by
    intro m i
    obtain ⟨hm, hcm, hbd, -⟩ := hker m
    obtain ⟨hV1, hM1⟩ := rowData_noLog hd β hβ ρ hρ c Mmax M'max γmax Cq Cu hCu δC C1 hδC hC1 hcrit V hV hVu hn hRD
      (measurable_gradEnv s) hBA0 hBB0 hBC0 hEnv K' hm hcm hbd
    exact row_moment_le V hβ.le hκ hm i (Eventually.of_forall hV1) (Eventually.of_forall hM1)
  have hmeasRow : ∀ (m : Fin d) (i : Fin (n + 1)), Measurable fun Y : Config d (n + 1) =>
      ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2 :=
    fun m i => (measurable_rowSum (hker m).1 i).enorm.pow_const 2
  set a2 : ℝ := 4 * (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 with ha2
  set Bd : ℝ≥0∞ := ENNReal.ofReal (2 * n) * ENNReal.ofReal (K' ^ 2 * Vc) +
    ENNReal.ofReal ((|K'| * Cm * logEN N) ^ 2) with hBd
  calc ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      = ∫⁻ X, ∑ i : Fin (n + 1), ∑ m : Fin d, ENNReal.ofReal a2 *
          ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (X i) (X j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with X hX
        exact Finset.sum_congr rfl fun i _ => hX i
    _ = ∑ i : Fin (n + 1), ∑ m : Fin d, ENNReal.ofReal a2 * ∫⁻ X,
          ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (X i) (X j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
        rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ fun m _ => (hmeasRow m i).const_mul _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ (fun m _ => (hmeasRow m i).const_mul _)]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [lintegral_const_mul _ (hmeasRow m i)]
    _ ≤ ∑ _i : Fin (n + 1), ∑ _m : Fin d, ENNReal.ofReal a2 * Bd := by
        gcongr with i _ m _
        exact hrow m i
    _ = ENNReal.ofReal (a2 * ((N : ℝ) * d * (2 * n * (K' ^ 2 * Vc) + (|K'| * Cm * logEN N) ^ 2))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : (0 : ℝ) ≤ 2 * n := by positivity
        rw [hBd, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [show ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by rw [ENNReal.ofReal_natCast],
          show ((d : ℕ) : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) by rw [ENNReal.ofReal_natCast]]
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := real_psi (N : ℝ) (n : ℝ) Vc K' (logEN N) (|K'| * Cm * logEN N) Cm (by exact_mod_cast hN1)
          (Nat.cast_nonneg n) hnR hVc0 hL2 hCm0 (by positivity) le_rfl
        have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 3 := by
          rw [rpow_sq_neg N (by omega)]
          have : (2 * (3 / 2 : ℝ)) = ((3 : ℕ) : ℝ) := by norm_num
          rw [this, Real.rpow_natCast]
        have hK'2 : K' ^ 2 = K ^ 2 * (1 + BA) ^ 2 := by
          rw [hK', mul_pow, sq_abs]
        rw [ha2, hc2]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have e : 4 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * d * (2 * n * (K' ^ 2 * Vc) + (|K'| * Cm * logEN N) ^ 2)) =
            (d / 2) * (8 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * (2 * n * (K' ^ 2 * Vc) + (|K'| * Cm * logEN N) ^ 2))) := by
          ring
        rw [e]
        calc (d / 2) * (8 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * (2 * n * (K' ^ 2 * Vc) + (|K'| * Cm * logEN N) ^ 2)))
            ≤ (d / 2) * ((16 * Vc + 32 * Cm ^ 2) * K' ^ 2 / N) := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = d * (8 * Vc + 16 * Cm ^ 2) * (1 + BA) ^ 2 * K ^ 2 / N := by rw [hK'2]; ring

end EnergyLarge

section EnergyCrude

theorem energy_ref_crude (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c Mmax M'max γmax Cq : ℝ) (Cu : ℝ) (hCu : 0 ≤ Cu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ n : ℕ, 1 ≤ n →
      ∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), (∀ x y, ψ x y = ψ y x) →
      IsCanonicalPair (withDensityReal ρ) ψ →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d) →
      (∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
        K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s))) →
        ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
            ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * K ^ 2) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  obtain ⟨BA, BB, BC, hBA0, hBB0, hBC0, hEnv⟩ := gradEnv_bounds (d := d) hd hcrit Cu hCu ρ hΛ hΛ0.le
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  set Vc : ℝ := E0 * BB with hVc
  have hVc0 : 0 ≤ Vc := by positivity
  refine ⟨4 * d * Vc * (1 + BA) ^ 2, by positivity, fun V hV n hn K ψ hsymm hcan hsm hgrad => ?_⟩
  set N : ℕ := n + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnR : (n : ℝ) ≤ N := by simp [hNdef]
  set K' : ℝ := |K| * (1 + BA) with hK'
  have hker := fun m : Fin d => corrected_kernel hd hcrit hρ hBA0 hEnv.A hcan hsm hgrad m
  have hae := energy_ae_eq V hβ.le (n := n) hatom hsymm hsm (fun m => (hker m).2.2.2)
  have hrow : ∀ (m : Fin d) (i : Fin (n + 1)),
      ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal ((n : ℝ) ^ 2) * ENNReal.ofReal (K' ^ 2 * Vc) := by
    intro m i
    obtain ⟨hm, hcm, hbd, -⟩ := hker m
    have hW : ∀ x : Torus d, ∫⁻ z, ‖vcorr (withDensityReal ρ) ψ m x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z)) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (K' ^ 2 * Vc) := fun x =>
      varInt_noLog hd β hβ ρ hρ c Mmax M'max γmax Cq hN1 V hV hBB0 hEnv K' hbd x _ rfl
    have hmeasP : ∀ a b : Fin (n + 1), Measurable fun Y : Config d (n + 1) =>
        ‖vcorr (withDensityReal ρ) ψ m (Y a) (Y b)‖ₑ ^ 2 :=
      fun a b => ((measurable_h_pair hm a b).enorm).pow_const 2
    calc ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
        ≤ ∫⁻ Y, ENNReal.ofReal ((Finset.univ.erase i).card : ℝ) *
            ∑ j ∈ Finset.univ.erase i, ‖vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
          lintegral_mono fun Y => enorm_sq_sum_le _ _
      _ = ENNReal.ofReal ((Finset.univ.erase i).card : ℝ) * ∑ j ∈ Finset.univ.erase i, ∫⁻ Y,
            ‖vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
          rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j _ => hmeasP i j),
            lintegral_finsetSum _ (fun j _ => hmeasP i j)]
      _ ≤ ENNReal.ofReal ((Finset.univ.erase i).card : ℝ) * ∑ _j ∈ Finset.univ.erase i,
            ENNReal.ofReal (K' ^ 2 * Vc) := by
          gcongr with j hj
          exact pair_lintegral_le V hβ.le i j (Finset.ne_of_mem_erase hj).symm hm hW
      _ = ENNReal.ofReal ((n : ℝ) ^ 2) * ENNReal.ofReal (K' ^ 2 * Vc) := by
          have hcard : (Finset.univ.erase i).card = n := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]; rfl
          rw [Finset.sum_const, hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring
  have hmeasRow : ∀ (m : Fin d) (i : Fin (n + 1)), Measurable fun Y : Config d (n + 1) =>
      ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (Y i) (Y j)‖ₑ ^ 2 :=
    fun m i => (measurable_rowSum (hker m).1 i).enorm.pow_const 2
  set a2 : ℝ := 4 * (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 with ha2
  calc ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      = ∫⁻ X, ∑ i : Fin (n + 1), ∑ m : Fin d, ENNReal.ofReal a2 *
          ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (X i) (X j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with X hX
        exact Finset.sum_congr rfl fun i _ => hX i
    _ = ∑ i : Fin (n + 1), ∑ m : Fin d, ENNReal.ofReal a2 * ∫⁻ X,
          ‖∑ j ∈ Finset.univ.erase i, vcorr (withDensityReal ρ) ψ m (X i) (X j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
        rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ fun m _ => (hmeasRow m i).const_mul _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ (fun m _ => (hmeasRow m i).const_mul _)]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [lintegral_const_mul _ (hmeasRow m i)]
    _ ≤ ∑ _i : Fin (n + 1), ∑ _m : Fin d, ENNReal.ofReal a2 *
          (ENNReal.ofReal ((n : ℝ) ^ 2) * ENNReal.ofReal (K' ^ 2 * Vc)) := by
        gcongr with i _ m _
        exact hrow m i
    _ = ENNReal.ofReal (a2 * ((N : ℝ) * d * ((n : ℝ) ^ 2 * (K' ^ 2 * Vc)))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_mul (by positivity)]
        rw [show ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by rw [ENNReal.ofReal_natCast],
          show ((d : ℕ) : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) by rw [ENNReal.ofReal_natCast]]
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 3 := by
          rw [rpow_sq_neg N (by omega)]
          have : (2 * (3 / 2 : ℝ)) = ((3 : ℕ) : ℝ) := by norm_num
          rw [this, Real.rpow_natCast]
        have hK'2 : K' ^ 2 = K ^ 2 * (1 + BA) ^ 2 := by
          rw [hK', mul_pow, sq_abs]
        rw [ha2, hc2]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hn2 : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hn0 hnR 2
        have hP : 0 ≤ d * (K' ^ 2 * Vc) := by positivity
        have e : 4 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * d * ((n : ℝ) ^ 2 * (K' ^ 2 * Vc))) =
            4 * ((n : ℝ) ^ 2 / (N : ℝ) ^ 2) * (d * (K' ^ 2 * Vc)) := by
          field_simp
        rw [e]
        have h5 : (n : ℝ) ^ 2 / (N : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]; exact hn2
        calc 4 * ((n : ℝ) ^ 2 / (N : ℝ) ^ 2) * (d * (K' ^ 2 * Vc)) ≤ 4 * 1 * (d * (K' ^ 2 * Vc)) := by
              gcongr
          _ = 4 * d * Vc * (1 + BA) ^ 2 * K ^ 2 := by rw [hK'2]; ring

end EnergyCrude

section EnergyAll

/-- The energy term of statement (psi) of Proposition 4.12 for `Q_{N,β}(μ)`, all `N ≥ 2`. -/
theorem energy_all (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), (∀ x y, ψ x y = ψ y x) →
      IsCanonicalPair (withDensityReal ρ) ψ →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d) →
      (∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
        K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s))) → ∀ N : ℕ, 2 ≤ N →
        ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
            ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * K ^ 2 / N) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρs.density
  obtain ⟨c, Cq, Mmax, M'max, γmax, N₁, KQ, δC, C1, Cu, C2, Vf, hc, hCq, hN₁, hKQ, hδC, hC1, hCu, hC2, hVu, hbd,
    hprob, hcrude, hlarge, hlarge2⟩ := exists_setting hd hcrit β hβ ρ hρs
  obtain ⟨Cl, hCl0, hCl⟩ := energy_ref_large hd hcrit β hβ ρ hρs c Mmax M'max γmax Cq Cu hCu δC C1 hδC hC1
  obtain ⟨Cc, hCc0, hCc⟩ := energy_ref_crude hd hcrit β hβ ρ hρs c Mmax M'max γmax Cq Cu hCu
  choose K' hK'pos hK'le using hcrude
  set Csum : ℝ := ∑ n ∈ Finset.range N₁, K' n * Cc * (N₁ : ℝ) with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun n _ => by have := hK'pos n; positivity
  refine ⟨max (KQ * Cl) Csum, le_trans (by positivity) (le_max_left _ _),
    fun K ψ hsymm hcan hsm hgrad N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  haveI := hprob n
  have hNp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  by_cases hbig : N₁ ≤ n + 1
  · obtain ⟨hle, hκ, hRD⟩ := hlarge n hbig
    have h1 := hCl (Vf n) (hbd n) (hVu n) n (by omega) hκ hRD K ψ hsymm hcan hsm hgrad
    calc ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
          ∂(modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        ≤ ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 ∂(ENNReal.ofReal KQ •
          pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
          lintegral_mono' hle le_rfl
      _ = ENNReal.ofReal KQ * ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
          ∂(pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal KQ * ENNReal.ofReal (Cl * K ^ 2 / ((n + 1 : ℕ) : ℝ)) := mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (KQ * (Cl * K ^ 2 / ((n + 1 : ℕ) : ℝ))) := (ENNReal.ofReal_mul hKQ.le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← mul_div_assoc, ← mul_assoc]
          refine div_le_div_of_nonneg_right ?_ hNp.le
          nlinarith [mul_le_mul_of_nonneg_right (le_max_left (KQ * Cl) Csum) (sq_nonneg K)]
  · push Not at hbig
    have hNlt : n + 1 < N₁ := hbig
    have hle := hK'le n
    have h1 := hCc (Vf n) (hbd n) n (by omega) K ψ hsymm hcan hsm hgrad
    calc ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
          ∂(modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        ≤ ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 ∂(ENNReal.ofReal (K' n) •
          pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
          lintegral_mono' hle le_rfl
      _ = ENNReal.ofReal (K' n) * ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
          ∂(pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal (K' n) * ENNReal.ofReal (Cc * K ^ 2) := mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (K' n * (Cc * K ^ 2)) := (ENNReal.ofReal_mul (hK'pos n).le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hKn := hK'pos n
          have hterm : K' n * Cc * (N₁ : ℝ) ≤ Csum := by
            rw [hCsum]
            exact Finset.single_le_sum (f := fun n => K' n * Cc * (N₁ : ℝ))
              (fun n _ => by have := hK'pos n; positivity) (Finset.mem_range.2 (by omega))
          have hNN1 : ((n + 1 : ℕ) : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hNlt.le
          rw [le_div_iff₀ hNp]
          have h3 : 0 ≤ K' n * Cc * K ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right (hterm.trans (le_max_right (KQ * Cl) Csum)) (sq_nonneg K),
            mul_le_mul_of_nonneg_left hNN1 h3]

end EnergyAll

end HRS.PairMom

end
