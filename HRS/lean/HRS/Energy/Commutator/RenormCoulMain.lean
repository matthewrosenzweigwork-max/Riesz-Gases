import HRS.Energy.Commutator.RenormRadii

/-!
# Route S, packet S4: the master inequality for the Coulomb slice
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.Renorm

variable {d : ℕ}

/-- the radial weight `r^{2-d}` -/
def rho2 (d : ℕ) (r : ℝ) : ℝ := r * (r ^ (d - 1))⁻¹

theorem T_alg (hd : 1 ≤ d) {N : ℕ} (hN : 0 < N) {r ω e L : ℝ} (hr : 0 < r) (hω : 0 < ω) :
    2 * (1 / (N : ℝ)) * (L * r * (2 ^ d / (2 * d) * ((1 / (N : ℝ)) * (r ^ (d - 1))⁻¹) +
      2 ^ d / (2 * ((1 / (N : ℝ)) * (r ^ (d - 1))⁻¹) * d * ω * r ^ d) * e)) =
      L * ((2 ^ d / d) * ((1 / (N : ℝ)) ^ 2 * rho2 d r) + (2 ^ d / (d * ω)) * e) := by
  unfold rho2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : r ^ d = r ^ (d - 1) * r := by
    rw [← pow_succ]; congr 1; omega
  have hp0 : 0 < r ^ (d - 1) := pow_pos hr _
  rw [hp]
  field_simp

set_option maxHeartbeats 4000000 in
theorem coulomb_master (hd : 2 ≤ d) :
    ∃ CQ Cs K2 M₁ Cw ω : ℝ, 0 ≤ CQ ∧ 0 ≤ Cs ∧ 0 ≤ K2 ∧ 0 ≤ M₁ ∧ 0 ≤ Cw ∧ 0 < ω ∧
    ∀ {N : ℕ} (hN : 2 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρΛ : ∀ x, ρ x ≤ Λ)
      {X : Config d N} (hX : X ∉ collisionSet d N) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
      (hv : IsLipschitzVF L v),
      ∃ η : Fin N → ℝ, (∀ i, smearRadius Λ X i / 2 < η i ∧ η i < smearRadius Λ X i) ∧
        |offDiagPairing (commKernel (SliceAux.sgv 0) v) X (withDensityReal ρ)| ≤ L * (
          CQ * (2 * modulatedEnergyKernel (sliceG d 0) X (withDensityReal ρ) +
            (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η i) + (2 * Λ / N) * ∑ i, η i ^ 2 / (2 * d)) +
          (2 ^ d / (d * ω)) * (2 * (2 * modulatedEnergyKernel (sliceG d 0) X (withDensityReal ρ) +
            (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (smearRadius Λ X i / 4) +
              (2 * Λ / N) * ∑ i, (smearRadius Λ X i / 4) ^ 2 / (2 * d)) +
            2 * Cw * ((1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (smearRadius Λ X i))) +
          (2 ^ d / d) * ((1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (smearRadius Λ X i)) +
          (if d = 2 then K2 * (1 / (N : ℝ))
            else Cs * ((1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η i)) + 2 * Jl d 0 * (1 / (N : ℝ))) +
          2 * (1 / (N : ℝ)) * Λ * M₁ * ∑ i, η i ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨CQ, hCQ, hQ⟩ := Q_bound d hd1
  obtain ⟨Cs, hCs, hSB⟩ := selfB_bound d hd1
  obtain ⟨Kd, hKd, hsg⟩ := sgv0_bound hd
  obtain ⟨Kb, hKb0, hWb⟩ := Wb0_bound hd
  obtain ⟨Kt, hKt0, hWt⟩ := Wt0_bound hd
  obtain ⟨Cw, hCw0, hCw⟩ := annulus_w2_bound hd
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hωpos : 0 < ((volume : Measure (Euc d)) (Metric.ball 0 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  refine ⟨CQ, Cs, 2 * Kd, 5 * Kt + 2 * Kb, Cw, ((volume : Measure (Euc d)) (Metric.ball 0 1)).toReal,
    hCQ.le, hCs.le, by positivity, by positivity, hCw0, hωpos, ?_⟩
  intro N hN Λ hΛ ρ hρ hρΛ X hX L hL v hv
  have hN0 : N ≠ 0 := by omega
  have hNpos : 0 < N := by omega
  set μ := withDensityReal ρ with hμdef
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ
  have hc : ENNReal.ofReal Λ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := withDensityReal_le_smul' hρΛ
  have hμ1 : μ Set.univ = 1 := measure_univ
  have hX' : ∀ i j, i ≠ j → X i ≠ X j := fun i j hij h => hX ⟨i, j, hij, h⟩
  obtain ⟨hr0, hrl, hr8, hsep⟩ := radii_facts hd1 hN hΛ X hX'
  set r : Fin N → ℝ := fun i => smearRadius Λ X i with hr
  have hΛ0 : 0 ≤ Λ := by linarith
  -- auxiliary charges `η⁰ = r/4`
  set η0 : Fin N → ℝ := fun i => r i / 4 with hη0def
  have hη0 : ∀ i, 0 < η0 i ∧ η0 i < 1 / 2 := fun i => ⟨by have := hr0 i; simp only [hη0def]; positivity,
    by have := hr8 i; simp only [hη0def, hr]; linarith⟩
  have hdisj0 : ∀ i j, i ≠ j → η0 i + η0 j < KernelGrad.tdist (X i) (X j) := fun i j hij => by
    have := hsep i j hij; have := hr0 i; have := hr0 j; simp only [hη0def]; linarith
  have hS0 := sliceCharges_coulomb hd hη0 hdisj0
  obtain ⟨hint0, hsum0⟩ := local_field_energy_ann hd1 hN0 (le_refl (0 : ℝ)) hS0 (r := r)
    (fun i => by simp only [hη0def]; linarith [hr0 i]) hr0 hsep hc hμ hμ1
  -- choice of the radii
  set ω : ℝ := ((volume : Measure (Euc d)) (Metric.ball 0 1)).toReal with hω
  have hpick : ∀ i, ∃ ηi : ℝ, r i / 2 < ηi ∧ ηi < r i ∧
      |fieldT 0 v X (chC d ηi (X i)) μ i| ≤ L * r i * (2 ^ d / (2 * d) * ((1 / (N : ℝ)) * (r i ^ (d - 1))⁻¹) +
        2 ^ d / (2 * ((1 / (N : ℝ)) * (r i ^ (d - 1))⁻¹) * d * ω * r i ^ d) *
          ∫ x : Torus d, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
            then ‖fieldF 0 X μ i x‖ ^ 2 else 0)) := by
    intro i
    have hε : 0 < (1 / (N : ℝ)) * (r i ^ (d - 1))⁻¹ := by
      have := hr0 i; have : (0 : ℝ) < N := by exact_mod_cast hNpos
      positivity
    obtain ⟨η, h1, h2, h3⟩ := T_pick hd1 (hr0 i) (by linarith [hr8 i]) (X i) (measurable_fieldF 0 X μ i)
      (hint0 i) hε hL hv
    exact ⟨η, h1, h2, h3⟩
  choose η hη1 hη2 hT using hpick
  refine ⟨η, fun i => ⟨hη1 i, hη2 i⟩, ?_⟩
  have hηpos : ∀ i, 0 < η i := fun i => by linarith [hη1 i, hr0 i]
  have hη8 : ∀ i, η i ≤ 1 / 8 := fun i => by linarith [hη2 i, hr8 i]
  have hη : ∀ i, 0 < η i ∧ η i < 1 / 2 := fun i => ⟨hηpos i, by linarith [hη8 i]⟩
  have hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j) := fun i j hij => by
    have := hsep i j hij; have := hη2 i; have := hη2 j; linarith
  have hS := sliceCharges_coulomb hd hη hdisj
  have hdec := slice_decomp hd1 hN0 (le_refl (0 : ℝ)) hS hc hμ hL hv
  have hQb := hQ hN0 (le_refl (0 : ℝ)) hS hc hμ hμ1 hL hv
  have hE := coulomb_energy hd hN0 hη hdisj hΛ0 hμ hμ1
  have hE0 := coulomb_energy hd hN0 hη0 hdisj0 hΛ0 hμ hμ1
  have hmass : ∀ i, (chC d (η i) (X i)).real Set.univ = 1 := fun i => by
    simp [Measure.real, chC_univ hd1]
  -- self blocks
  have hSBi : ∀ i, |selfB 0 v (chC d (η i) (X i))| ≤
      (if d = 2 then L * (2 * Kd) else Cs * L * S0 d (η i) + 2 * L * Jl d 0) := by
    intro i
    haveI := isFiniteMeasure_chC hd1 (η i) (X i)
    by_cases h2 : d = 2
    · rw [if_pos h2]
      have hK2 : ∀ z : Torus d, KernelGrad.tdist z 0 ≤ 2 * η i →
          KernelGrad.tdist z 0 * ‖SliceAux.sgv 0 z‖ ≤ 2 * Kd := by
        intro z hz
        by_cases hz0 : z = 0
        · subst hz0
          rw [CoercAux.tdist_self, zero_mul]; positivity
        · have h := hsg z hz0
          have ht : 0 < KernelGrad.tdist z 0 := KernelGrad.tdist_pos hz0
          have hd1' : d - 1 = 1 := by omega
          rw [hd1', pow_one] at h
          have ht4 : KernelGrad.tdist z 0 ≤ 1 := by linarith [hη8 i]
          calc KernelGrad.tdist z 0 * ‖SliceAux.sgv 0 z‖
              ≤ KernelGrad.tdist z 0 * (Kd * ((KernelGrad.tdist z 0)⁻¹ + 1)) :=
                mul_le_mul_of_nonneg_left h ht.le
            _ = Kd * (1 + KernelGrad.tdist z 0) := by field_simp
            _ ≤ 2 * Kd := by nlinarith
      have h := selfB_pointwise (le_refl (0 : ℝ)) hL hv (a := X i) (η := η i)
        (chC_supp hd1 (hηpos i) (hη i).2 (X i)) hK2
      rw [hmass i] at h
      calc |selfB 0 v (chC d (η i) (X i))| ≤ L * (2 * Kd) * 1 ^ 2 := h
        _ = L * (2 * Kd) := by ring
    · rw [if_neg h2]
      have h := hSB (le_refl (0 : ℝ)) hL hv (σ := chC d (η i) (X i))
        (fun h' => chC_atom hd (hηpos i) (hη i).2 (X i)) (hS.Gii i)
      rw [quadForm_chC hd (hηpos i) (hη i).2, hmass i] at h
      calc |selfB 0 v (chC d (η i) (X i))| ≤ Cs * L * S0 d (η i) + 2 * L * 1 ^ 2 * Jl d 0 := h
        _ = Cs * L * S0 d (η i) + 2 * L * Jl d 0 := by ring
  -- the `μ`-term inside the ball
  have hMUi : ∀ i, |muB 0 v (chC d (η i) (X i)) μ (X i)| ≤ Λ * L * (5 * Kt + 2 * Kb) * η i ^ 2 := by
    intro i
    haveI := isFiniteMeasure_chC hd1 (η i) (X i)
    have h := muB_bound hd1 (le_refl (0 : ℝ)) hL hv (a := X i) (hηpos i).le
      (σ := chC d (η i) (X i)) (chC_supp hd1 (hηpos i) (hη i).2 (X i))
      (fun y hy => chC_repro hd (hηpos i) (hη i).2 (X i) hy) hc hμ
    rw [ENNReal.toReal_ofReal hΛ0, hmass i] at h
    have h1 := hWt (η i) (hηpos i) (by linarith [hη8 i])
    have h2 := hWt (2 * η i) (by linarith [hηpos i]) (by linarith [hη8 i])
    have h3 := hWb (2 * η i) (by linarith [hηpos i]) (by linarith [hη8 i])
    refine h.trans ?_
    have hΛL : 0 ≤ Λ * L := mul_nonneg hΛ0 hL
    have h4 : Wt d 0 (η i) + 1 * (Wt d 0 (2 * η i) + η i * Wb d 0 (2 * η i)) ≤ (5 * Kt + 2 * Kb) * η i ^ 2 := by
      have h5 : η i * Wb d 0 (2 * η i) ≤ η i * (Kb * (2 * η i)) :=
        mul_le_mul_of_nonneg_left h3 (hηpos i).le
      nlinarith [h1, h2, h5]
    calc Λ * L * (Wt d 0 (η i) + 1 * (Wt d 0 (2 * η i) + η i * Wb d 0 (2 * η i)))
        ≤ Λ * L * ((5 * Kt + 2 * Kb) * η i ^ 2) := mul_le_mul_of_nonneg_left h4 hΛL
      _ = Λ * L * (5 * Kt + 2 * Kb) * η i ^ 2 := by ring
  -- the field term
  set e : Fin N → ℝ := fun i => ∫ x : Torus d, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
    then ‖fieldF 0 X μ i x‖ ^ 2 else 0) with he
  have hTi : ∀ i, 2 * (1 / (N : ℝ)) * |fieldT 0 v X (chC d (η i) (X i)) μ i| ≤
      L * ((2 ^ d / d) * ((1 / (N : ℝ)) ^ 2 * rho2 d (r i)) + (2 ^ d / (d * ω)) * e i) := by
    intro i
    have h := mul_le_mul_of_nonneg_left (hT i) (by positivity : (0 : ℝ) ≤ 2 * (1 / (N : ℝ)))
    rw [T_alg hd1 hNpos (hr0 i) hωpos] at h
    exact h
  have hWi : ∀ i, ∫ x : Torus d, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
      then ‖SliceAux.sgv 0 (x - X i)‖ ^ 2 else 0) ≤ Cw * rho2 d (r i) := by
    intro i
    set g : Torus d → ℝ := fun z => if r i / 2 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < r i
      then ‖SliceAux.sgv 0 z‖ ^ 2 else 0 with hg
    have e1 : ∀ x : Torus d, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
        then ‖SliceAux.sgv 0 (x - X i)‖ ^ 2 else 0) = g (x - X i) := by
      intro x; simp only [hg]; rw [EnergyAux.tdist_def x (X i)]
    simp_rw [e1]
    rw [integral_sub_right_eq_self g (X i)]
    exact hCw (r i) (hr0 i) (by linarith [hr8 i])
  have hesum : ∑ i, e i ≤ 2 * quadForm (fun x y => sliceGfull d 0 (x - y)) (avgM fun i => chC d (η0 i) (X i)) μ +
      2 * (1 / (N : ℝ)) ^ 2 * (Cw * ∑ i, rho2 d (r i)) := by
    refine hsum0.trans ?_
    have h2 : 0 ≤ (1 / (N : ℝ)) ^ 2 := by positivity
    have h3 : ∑ i, ∫ x : Torus d, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
        then ‖SliceAux.sgv 0 (x - X i)‖ ^ 2 else 0) ≤ ∑ i, Cw * rho2 d (r i) :=
      Finset.sum_le_sum fun i _ => hWi i
    rw [← Finset.mul_sum] at h3
    nlinarith [mul_le_mul_of_nonneg_left h3 h2]
  have hlin : ∀ a b c d' : ℝ, |a - b - c + d'| ≤ |a| + |b| + |c| + |d'| := by
    intro a b c d'
    rw [abs_le]
    constructor <;> nlinarith [neg_abs_le a, neg_abs_le b, neg_abs_le c, neg_abs_le d', le_abs_self a,
      le_abs_self b, le_abs_self c, le_abs_self d']
  have hu0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  rw [hdec]
  refine (hlin _ _ _ _).trans ?_
  -- term A
  have hA := hQb
  -- term B
  have hB : |(1 / (N : ℝ)) ^ 2 * ∑ i, selfB 0 v (chC d (η i) (X i))| ≤
      (1 / (N : ℝ)) ^ 2 * ∑ i, |selfB 0 v (chC d (η i) (X i))| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  have hB2 : (1 / (N : ℝ)) ^ 2 * ∑ i, |selfB 0 v (chC d (η i) (X i))| ≤
      L * (if d = 2 then 2 * Kd * (1 / (N : ℝ)) else
        Cs * ((1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η i)) + 2 * Jl d 0 * (1 / (N : ℝ))) := by
    have h1 : ∑ i, |selfB 0 v (chC d (η i) (X i))| ≤
        ∑ i, (if d = 2 then L * (2 * Kd) else Cs * L * S0 d (η i) + 2 * L * Jl d 0) :=
      Finset.sum_le_sum fun i _ => hSBi i
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)
    refine h2.trans (le_of_eq ?_)
    by_cases h2' : d = 2
    · simp only [if_pos h2', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · simp only [if_neg h2', Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum]
      field_simp
  -- term C
  have hC : |(2 / (N : ℝ)) * ∑ i, muB 0 v (chC d (η i) (X i)) μ (X i)| ≤
      L * (2 * (1 / (N : ℝ)) * Λ * (5 * Kt + 2 * Kb) * ∑ i, η i ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have h1 : |∑ i, muB 0 v (chC d (η i) (X i)) μ (X i)| ≤ ∑ i, Λ * L * (5 * Kt + 2 * Kb) * η i ^ 2 :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hMUi i)
    calc (2 / (N : ℝ)) * |∑ i, muB 0 v (chC d (η i) (X i)) μ (X i)|
        ≤ (2 / (N : ℝ)) * ∑ i, Λ * L * (5 * Kt + 2 * Kb) * η i ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = L * (2 * (1 / (N : ℝ)) * Λ * (5 * Kt + 2 * Kb) * ∑ i, η i ^ 2) := by
          rw [← Finset.mul_sum]; ring
  -- term D
  have hD : |(2 / (N : ℝ)) * ∑ i, fieldT 0 v X (chC d (η i) (X i)) μ i| ≤
      L * ((2 ^ d / d) * ((1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (r i)) + (2 ^ d / (d * ω)) * ∑ i, e i) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have h1 : |∑ i, fieldT 0 v X (chC d (η i) (X i)) μ i| ≤ ∑ i, |fieldT 0 v X (chC d (η i) (X i)) μ i| :=
      Finset.abs_sum_le_sum_abs _ _
    calc (2 / (N : ℝ)) * |∑ i, fieldT 0 v X (chC d (η i) (X i)) μ i|
        ≤ (2 / (N : ℝ)) * ∑ i, |fieldT 0 v X (chC d (η i) (X i)) μ i| :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ∑ i, 2 * (1 / (N : ℝ)) * |fieldT 0 v X (chC d (η i) (X i)) μ i| := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ ≤ ∑ i, L * ((2 ^ d / d) * ((1 / (N : ℝ)) ^ 2 * rho2 d (r i)) + (2 ^ d / (d * ω)) * e i) :=
          Finset.sum_le_sum fun i _ => hTi i
      _ = L * ((2 ^ d / d) * ((1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (r i)) + (2 ^ d / (d * ω)) * ∑ i, e i) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  -- combine
  set F0 := modulatedEnergyKernel (sliceG d 0) X μ with hF0
  set E1 := quadForm (fun x y => sliceGfull d 0 (x - y)) (avgM fun i => chC d (η i) (X i)) μ with hE1
  set E0 := quadForm (fun x y => sliceGfull d 0 (x - y)) (avgM fun i => chC d (η0 i) (X i)) μ with hE0def
  have hcoef1 : 0 ≤ CQ * L := mul_nonneg hCQ.le hL
  have h1 : CQ * L * E1 ≤ L * (CQ * (2 * F0 + (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η i) +
      (2 * Λ / N) * ∑ i, η i ^ 2 / (2 * d))) := by
    have := mul_le_mul_of_nonneg_left hE hcoef1
    linarith
  have hcoef2 : 0 ≤ L * (2 ^ d / (d * ω)) := mul_nonneg hL (by positivity)
  have h2 : L * ((2 ^ d / (d * ω)) * ∑ i, e i) ≤ L * ((2 ^ d / (d * ω)) * (2 * (2 * F0 +
      (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η0 i) + (2 * Λ / N) * ∑ i, η0 i ^ 2 / (2 * d)) +
        2 * Cw * ((1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (r i)))) := by
    have h3 : ∑ i, e i ≤ 2 * (2 * F0 + (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η0 i) + (2 * Λ / N) * ∑ i, η0 i ^ 2 / (2 * d)) +
        2 * Cw * ((1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (r i)) := by
      have := hesum
      nlinarith [hE0]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) hL
  have hsum : |quadForm (commKernel (SliceAux.sgv 0) v) (avgM fun i => chC d (η i) (X i)) μ| +
      |(1 / (N : ℝ)) ^ 2 * ∑ i, selfB 0 v (chC d (η i) (X i))| +
      |(2 / (N : ℝ)) * ∑ i, muB 0 v (chC d (η i) (X i)) μ (X i)| +
      |(2 / (N : ℝ)) * ∑ i, fieldT 0 v X (chC d (η i) (X i)) μ i| ≤
      CQ * L * E1 + L * (if d = 2 then 2 * Kd * (1 / (N : ℝ)) else
        Cs * ((1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η i)) + 2 * Jl d 0 * (1 / (N : ℝ))) +
      L * (2 * (1 / (N : ℝ)) * Λ * (5 * Kt + 2 * Kb) * ∑ i, η i ^ 2) +
      L * ((2 ^ d / d) * ((1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (r i)) + (2 ^ d / (d * ω)) * ∑ i, e i) :=
    add_le_add (add_le_add (add_le_add hA (hB.trans hB2)) hC) hD
  refine hsum.trans ?_
  linarith [h1, h2]

end HRS.Commutator.Renorm
