import HRS.Sections.AdjKDAux3
import HRS.Sections.DynCmpAux2
import HRS.Energy.PressureProof
import HRS.PDE.MovSXAux4
import HRS.PDE.MeanFieldLinearLoss

/-!
# ADJKD, part 4: pathwise mode expansion of the commutator forcing (ingredient of packet B2)

For a configuration `Y` and a bounded density `ρ`, the functional `ψ ↦ F_N^{h_{∇ψ}}(Y, μ)` is linear in the
vector field `∇ψ` and bounded by `A · Lip(∇ψ) · Θ(Y)`; hence for `ψ ∈ C²` with `∑_j ⟨j⟩^{2m'} ψ̂_j² < ∞`,
`m' > d/2 + 2`, it equals `∑_j ψ̂_j F_N^{h_{∇e_j}}(Y, μ)` (`adjkd_forcing_expansion`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

/-! ### Linearity of `commKernel` in the vector field -/

theorem adjkd_commKernel_sub (G v w : Torus d → Euc d) (x y : Torus d) :
    commKernel G (fun z => v z - w z) x y = commKernel G v x y - commKernel G w x y := by
  by_cases h : x = y
  · simp [commKernel, h]
  · simp only [commKernel, h, if_false]
    rw [← inner_sub_left]
    congr 1
    abel

theorem adjkd_commKernel_sum {ι : Type*} (S : Finset ι) (a : ι → ℝ) (w : ι → Torus d → Euc d)
    (G : Torus d → Euc d) (x y : Torus d) :
    commKernel G (fun z => ∑ j ∈ S, a j • w j z) x y = ∑ j ∈ S, a j * commKernel G (w j) x y := by
  by_cases h : x = y
  · simp [commKernel, h]
  · simp only [commKernel, h, if_false]
    rw [← Finset.sum_sub_distrib, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_sub, real_inner_smul_left]

/-! ### Sums of `RowOK` kernels -/

theorem adjkd_rowOK_sum {μ : Measure (Torus d)} [IsFiniteMeasure μ] {ι : Type*} (S : Finset ι)
    (a : ι → ℝ) (k : ι → Torus d → Torus d → ℝ) (hk : ∀ j, RowOK μ (k j)) :
    RowOK μ (fun x y => ∑ j ∈ S, a j * k j x y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using RowOK.const (μ := μ) 0
  | insert j S hj ih =>
    simp_rw [Finset.sum_insert hj]
    exact ((hk j).smul (a j)).add ih

theorem adjkd_modEn_zero {N : ℕ} (Y : Config d N) (μ : Measure (Torus d)) :
    modulatedEnergy (fun _ _ => (0 : ℝ)) Y μ = 0 := by
  simp [modulatedEnergy]

theorem adjkd_modEn_sum {N : ℕ} {μ : Measure (Torus d)} [IsFiniteMeasure μ] {ι : Type*}
    (S : Finset ι) (a : ι → ℝ) (k : ι → Torus d → Torus d → ℝ) (hk : ∀ j, RowOK μ (k j))
    (Y : Config d N) :
    modulatedEnergy (fun x y => ∑ j ∈ S, a j * k j x y) Y μ =
      ∑ j ∈ S, a j * modulatedEnergy (k j) Y μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using adjkd_modEn_zero Y μ
  | insert j S hj ih =>
    simp_rw [Finset.sum_insert hj]
    have h1 := modulatedEnergy_add (N := N) ((hk j).smul (a j)) (adjkd_rowOK_sum S a k hk) Y
    have h2 := modulatedEnergy_smul (N := N) (a j) (hk j) Y
    rw [h1, h2, ih]

/-! ### Row bounds and the pathwise bound for the commutator forcing -/

theorem adjkd_rowOK_lip (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {cstar A : ℝ}
    (hdom : ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v → ∀ x y : Torus d,
      |commKernel (periodicRieszGrad d s) v x y| ≤ (A * L) * (periodicRiesz d s (x - y) + cstar))
    {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hΛ₀ : 0 ≤ Λ₀) (hρ : ∀ x, ρ x ≤ Λ₀) {L : ℝ} (hL : 0 ≤ L)
    {v : Torus d → Euc d} (hv : IsLipschitzVF L v) :
    RowOK (withDensityReal ρ) (commKernel (periodicRieszGrad d s) v) ∧
      ∀ x, ∫ y, |commKernel (periodicRieszGrad d s) v x y| ∂(withDensityReal ρ) ≤
        Λ₀ * ∫ z, (A * L) * (periodicRiesz d s z + cstar) := by
  have hgi := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hW : Integrable (fun z => (A * L) * (periodicRiesz d s z + cstar)) :=
    (hgi.add (integrable_const _)).const_mul _
  have hvc : Continuous v := Commutator.IsLipschitzVF.continuous hL hv
  have hm := dyncmp_commKernel_measurable
    (KernelGrad.measurable_periodicRieszGrad (by exact_mod_cast hsd)) hvc.measurable
  exact rowOK_of_dom hΛ₀ hρ hW hm (fun x y => hdom L v hL hv x y)

theorem adjkd_isFiniteMeasure_withDensityReal {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hρ : ∀ x, ρ x ≤ Λ₀) :
    IsFiniteMeasure (withDensityReal ρ) :=
  haveI : IsFiniteMeasure (ENNReal.ofReal Λ₀ • (volume : Measure (Torus d))) :=
    Measure.smul_finite (volume : Measure (Torus d)) ENNReal.ofReal_ne_top
  isFiniteMeasure_of_le _ (withDensityReal_le_smul hρ)

/-- Pathwise bound `|F_N^{h_v}(Y, μ)| ≤ A L Θ` with `Θ` independent of the `L`-Lipschitz field `v`. -/
theorem adjkd_modEn_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {cstar A : ℝ}
    (hA : 0 ≤ A)
    (hdom : ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v → ∀ x y : Torus d,
      |commKernel (periodicRieszGrad d s) v x y| ≤ (A * L) * (periodicRiesz d s (x - y) + cstar))
    {N : ℕ} (Y : Config d N) {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hΛ₀ : 0 ≤ Λ₀) (hρ : ∀ x, ρ x ≤ Λ₀) :
    ∃ Θ : ℝ, ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
      |modulatedEnergy (commKernel (periodicRieszGrad d s) v) Y (withDensityReal ρ)| ≤ A * L * Θ := by
  haveI := adjkd_isFiniteMeasure_withDensityReal hρ
  have hgi := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  set I₁ : ℝ := ∫ z, (periodicRiesz d s z + cstar) with hI₁
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  refine ⟨(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
      (periodicRiesz d s (Y i - Y j) + cstar) + Λ₀ * I₁ + (1 / 2) * (Λ₀ * I₁ * (μ Set.univ).toReal), ?_⟩
  intro L v hL hv
  obtain ⟨hrow, hbd⟩ := adjkd_rowOK_lip hd hs0 hsd hdom hΛ₀ hρ hL hv
  have hAL : 0 ≤ A * L := mul_nonneg hA hL
  have hint : ∫ z, (A * L) * (periodicRiesz d s z + cstar) = (A * L) * I₁ := by
    rw [integral_const_mul]
  rw [hint] at hbd
  set k := commKernel (periodicRieszGrad d s) v with hk
  set K : ℝ := Λ₀ * ((A * L) * I₁) with hK
  have hK0 : 0 ≤ K := le_trans (integral_nonneg fun y => abs_nonneg _) (hbd 0)
  have hN2 : (0 : ℝ) ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
  -- term 1
  have hT1 : |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (Y i) (Y j)| ≤
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (A * L) * (periodicRiesz d s (Y i - Y j) + cstar) := by
    rw [abs_mul, abs_of_nonneg hN2]
    refine mul_le_mul_of_nonneg_left ?_ hN2
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact hdom L v hL hv _ _
  -- term 2
  have hrowInt : ∀ x, |∫ y, k x y ∂μ| ≤ K := fun x =>
    (abs_integral_le_integral_abs).trans (hbd x)
  have hT2 : |(1 / (N : ℝ)) * ∑ i, ∫ y, k (Y i) y ∂μ| ≤ K := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simpa using hK0
    · have hNr : (0 : ℝ) < N := by exact_mod_cast hpos
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
      calc 1 / (N : ℝ) * |∑ i, ∫ y, k (Y i) y ∂μ|
          ≤ 1 / (N : ℝ) * ∑ i : Fin N, K := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hrowInt _)
        _ = K := by simp; field_simp
  -- term 3
  have hT3 : |(1 / 2 : ℝ) * ∫ x, ∫ y, k x y ∂μ ∂μ| ≤ (1 / 2) * (K * (μ Set.univ).toReal) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ∫ y, k x y ∂μ) (C := K)
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hrowInt x)
    simpa [Measure.real, Real.norm_eq_abs] using this
  have hfin : |modulatedEnergy k Y μ| ≤
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (A * L) * (periodicRiesz d s (Y i - Y j) + cstar) + K + (1 / 2) * (K * (μ Set.univ).toReal) := by
    unfold modulatedEnergy
    have h1 := abs_add_le ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (Y i) (Y j) -
            (1 / (N : ℝ)) * ∑ i, ∫ y, k (Y i) y ∂μ) ((1 / 2 : ℝ) * ∫ x, ∫ y, k x y ∂μ ∂μ)
    have h2 := abs_sub ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (Y i) (Y j))
            ((1 / (N : ℝ)) * ∑ i, ∫ y, k (Y i) y ∂μ)
    linarith
  refine hfin.trans (le_of_eq ?_)
  simp only [← Finset.mul_sum]
  rw [hK]
  ring


/-! ### Gradients of finite mode sums -/

theorem adjkd_isCk_of_smooth {φ : Torus d → ℝ} (n : ℕ) (h : Torus.IsSmooth φ) : Torus.IsCk n φ := by
  have h' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := h
  exact h'.of_le (by exact_mod_cast le_top)

theorem adjkd_grad_add {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) (x : Torus d) :
    Torus.grad (fun y => f y + g y) x = Torus.grad f x + Torus.grad g x := by
  have hf' : ContDiff ℝ 1 (Torus.lift f) := hf
  have hg' : ContDiff ℝ 1 (Torus.lift g) := hg
  unfold Torus.grad
  have : Torus.lift (fun y => f y + g y) = fun z => Torus.lift f z + Torus.lift g z := rfl
  rw [this]
  unfold gradient
  rw [fderiv_fun_add (hf'.differentiable one_ne_zero _) (hg'.differentiable one_ne_zero _), map_add]

theorem adjkd_grad_const_mul {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (c : ℝ) (x : Torus d) :
    Torus.grad (fun y => c * f y) x = c • Torus.grad f x := by
  have hf' : ContDiff ℝ 1 (Torus.lift f) := hf
  unfold Torus.grad
  have : Torus.lift (fun y => c * f y) = fun z => c * Torus.lift f z := rfl
  rw [this]
  unfold gradient
  rw [fderiv_const_mul (hf'.differentiable one_ne_zero _) c, map_smul]

theorem adjkd_isCk_sum {ι : Type*} {k : WithTop ℕ∞} (S : Finset ι) (a : ι → ℝ) (f : ι → Torus d → ℝ)
    (hf : ∀ j, Torus.IsCk k (f j)) : Torus.IsCk k (fun y => ∑ j ∈ S, a j * f j y) := by
  have : Torus.lift (fun y => ∑ j ∈ S, a j * f j y) = fun z => ∑ j ∈ S, a j * Torus.lift (f j) z := rfl
  show ContDiff ℝ k (Torus.lift (fun y => ∑ j ∈ S, a j * f j y))
  rw [this]
  exact ContDiff.sum fun j _ => contDiff_const.mul (hf j)

theorem adjkd_grad_sum {ι : Type*} (S : Finset ι) (a : ι → ℝ) (f : ι → Torus d → ℝ)
    (hf : ∀ j, Torus.IsCk 1 (f j)) (x : Torus d) :
    Torus.grad (fun y => ∑ j ∈ S, a j * f j y) x = ∑ j ∈ S, a j • Torus.grad (f j) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : Torus.grad (fun _ : Torus d => (0 : ℝ)) x = 0 := by
      unfold Torus.grad
      have : Torus.lift (fun _ : Torus d => (0 : ℝ)) = fun _ => (0 : ℝ) := rfl
      rw [this]
      simp [gradient]
    exact this
  | insert j S hj ih =>
    simp_rw [Finset.sum_insert hj]
    have h1 : Torus.IsCk 1 (fun y => a j * f j y) := by
      have : Torus.lift (fun y => a j * f j y) = fun z => a j * Torus.lift (f j) z := rfl
      show ContDiff ℝ 1 (Torus.lift (fun y => a j * f j y))
      rw [this]
      exact contDiff_const.mul (hf j)
    rw [adjkd_grad_add h1 (adjkd_isCk_sum S a f hf), adjkd_grad_const_mul (hf j), ih]

/-! ### The tail function `χ_S = ψ - ψ̄ - ∑_{j∈S} ψ̂_j e_j` -/

def adjkdChi (ψ : Torus d → ℝ) (S : Finset (NonzeroLattice d)) : Torus d → ℝ :=
  fun x => ψ x - Torus.mean ψ - ∑ j ∈ S, Torus.funRealCoeff ψ j * Torus.realMode j x

theorem adjkd_int_cont {f : Torus d → ℝ} (hc : Continuous f) : Integrable f :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem adjkd_chi_continuous {ψ : Torus d → ℝ} (hψ : Continuous ψ) (S : Finset (NonzeroLattice d)) :
    Continuous (adjkdChi ψ S) := by
  unfold adjkdChi
  refine (hψ.sub continuous_const).sub (continuous_finsetSum _ fun j _ => ?_)
  exact continuous_const.mul (Torus.continuous_realMode j)

theorem adjkd_chi_mean {ψ : Torus d → ℝ} (hψ : Continuous ψ) (S : Finset (NonzeroLattice d)) :
    Torus.mean (adjkdChi ψ S) = 0 := by
  unfold Torus.mean adjkdChi
  have hi : ∀ j, Integrable (fun x => Torus.funRealCoeff ψ j * Torus.realMode j x) := fun j =>
    adjkd_int_cont (continuous_const.mul (Torus.continuous_realMode j))
  have h1 : Integrable (fun x => ψ x - Torus.mean ψ) := (adjkd_int_cont hψ).sub (integrable_const _)
  have h2 : Integrable (fun x => ∑ j ∈ S, Torus.funRealCoeff ψ j * Torus.realMode j x) :=
    integrable_finsetSum _ fun j _ => hi j
  rw [integral_sub h1 h2, integral_sub (adjkd_int_cont hψ) (integrable_const _),
    integral_finset_sum _ fun j _ => hi j]
  simp only [integral_const_mul, Torus.integral_realMode, mul_zero, Finset.sum_const_zero, integral_const]
  simp [Torus.mean]

theorem adjkd_chi_coeff {ψ : Torus d → ℝ} (hψ : Continuous ψ) (S : Finset (NonzeroLattice d))
    (j : NonzeroLattice d) :
    Torus.funRealCoeff (adjkdChi ψ S) j = if j ∈ S then 0 else Torus.funRealCoeff ψ j := by
  classical
  unfold Torus.funRealCoeff adjkdChi
  set a : NonzeroLattice d → ℝ := fun i => ∫ x, Torus.realMode i x * ψ x with ha
  have hc : Continuous (Torus.realMode j) := Torus.continuous_realMode j
  have e : (fun x => Torus.realMode j x * (ψ x - Torus.mean ψ - ∑ i ∈ S, a i * Torus.realMode i x)) =
      fun x => (Torus.realMode j x * ψ x - Torus.mean ψ * Torus.realMode j x) -
        ∑ i ∈ S, a i * (Torus.realMode j x * Torus.realMode i x) := by
    funext x
    rw [mul_sub, mul_sub, Finset.mul_sum]
    have : ∀ i, Torus.realMode j x * (a i * Torus.realMode i x) =
        a i * (Torus.realMode j x * Torus.realMode i x) := fun i => by ring
    simp_rw [this]
    ring
  have hi1 : Integrable (fun x => Torus.realMode j x * ψ x) := adjkd_int_cont (hc.mul hψ)
  have hi2 : Integrable (fun x => Torus.mean ψ * Torus.realMode j x) :=
    adjkd_int_cont (continuous_const.mul hc)
  have hi3 : ∀ i, Integrable (fun x => a i * (Torus.realMode j x * Torus.realMode i x)) := fun i =>
    adjkd_int_cont (continuous_const.mul (hc.mul (Torus.continuous_realMode i)))
  show ∫ x, Torus.realMode j x * (ψ x - Torus.mean ψ - ∑ i ∈ S, a i * Torus.realMode i x) = _
  have hi4 : Integrable (fun x => Torus.realMode j x * ψ x - Torus.mean ψ * Torus.realMode j x) :=
    hi1.sub hi2
  have hi5 : Integrable (fun x => ∑ i ∈ S, a i * (Torus.realMode j x * Torus.realMode i x)) :=
    integrable_finsetSum _ fun i _ => hi3 i
  rw [e, integral_sub hi4 hi5, integral_sub hi1 hi2, integral_finset_sum _ fun i _ => hi3 i]
  simp only [integral_const_mul, Torus.integral_realMode, mul_zero, sub_zero, Torus.realMode_orthonormal]
  have : ∑ i ∈ S, a i * (if j = i then (1 : ℝ) else 0) = if j ∈ S then a j else 0 := by
    simp_rw [mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_eq S j a
  rw [this]
  by_cases h : j ∈ S <;> simp [h, ha, Torus.funRealCoeff]


/-! ### Sobolev control of the tail -/

theorem adjkd_cbNorm_nonneg (k : ℕ) (φ : Torus d → ℝ) : 0 ≤ Torus.cbNorm k φ := by
  unfold Torus.cbNorm
  exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun x => norm_nonneg _

theorem adjkd_chi_sobolev {ψ : Torus d → ℝ} (hψ : Continuous ψ) {m' : ℝ}
    (hsum : Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (2 * m') * Torus.funRealCoeff ψ j ^ 2)
    (S : Finset (NonzeroLattice d)) : MemSobolev m' (adjkdChi ψ S) := by
  classical
  refine ⟨?_, ?_⟩
  · have hc := adjkd_chi_continuous hψ S
    exact hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hnn : ∀ (φ : Torus d → ℝ) (j : NonzeroLattice d),
        0 ≤ Lattice.jp j.1 ^ (2 * m') * Torus.funRealCoeff φ j ^ 2 := fun φ j =>
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
    refine Summable.of_nonneg_of_le (fun j => hnn _ j) (fun j => ?_) hsum
    rw [adjkd_chi_coeff hψ S j]
    by_cases h : j ∈ S
    · simp only [h, ite_true]
      simpa using hnn ψ j
    · simp [h]

theorem adjkd_chi_sobolev_tendsto {ψ : Torus d → ℝ} (hψ : Continuous ψ) {m' : ℝ}
    (hsum : Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (2 * m') * Torus.funRealCoeff ψ j ^ 2) :
    Tendsto (fun S : Finset (NonzeroLattice d) => sobolevNorm m' (adjkdChi ψ S)) atTop (𝓝 0) := by
  classical
  set u : NonzeroLattice d → ℝ := fun j => Lattice.jp j.1 ^ (2 * m') * Torus.funRealCoeff ψ j ^ 2 with hu
  have hS : ∀ S : Finset (NonzeroLattice d), sobolevNorm m' (adjkdChi ψ S) =
      Real.sqrt (∑' j, u j - ∑ j ∈ S, u j) := by
    intro S
    unfold sobolevNorm
    rw [adjkd_chi_mean hψ S]
    have h0 : HasSum (fun j => if j ∈ S then u j else 0) (∑ j ∈ S, (if j ∈ S then u j else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
    have h1 : HasSum (fun j => if j ∈ S then u j else 0) (∑ j ∈ S, u j) := by
      have e : (∑ j ∈ S, (if j ∈ S then u j else 0)) = ∑ j ∈ S, u j :=
        Finset.sum_congr rfl (fun j hj => by simp [hj])
      rwa [e] at h0
    have h2 := hsum.hasSum.sub h1
    have h3 : (fun j => u j - (if j ∈ S then u j else 0)) =
        fun j => Lattice.jp j.1 ^ (2 * m') * Torus.funRealCoeff (adjkdChi ψ S) j ^ 2 := by
      funext j
      rw [adjkd_chi_coeff hψ S j]
      by_cases h : j ∈ S <;> simp [h, hu]
    rw [h3] at h2
    rw [h2.tsum_eq]
    simp
  simp_rw [hS]
  have : Tendsto (fun S : Finset (NonzeroLattice d) => ∑' j, u j - ∑ j ∈ S, u j) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ∑' j, u j)).sub hsum.hasSum
    simpa using this
  have h4 : Tendsto (fun S : Finset (NonzeroLattice d) =>
      Real.sqrt (∑' j, u j - ∑ j ∈ S, u j)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp this
  rwa [Real.sqrt_zero] at h4


/-! ### The mode expansion of the commutator forcing -/

theorem adjkd_forcing_expansion (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ}
    (Y : Config d N) {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hΛ₀ : 0 ≤ Λ₀) (hρ : ∀ x, ρ x ≤ Λ₀)
    {m' : ℝ} (hm' : (d : ℝ) / 2 + 2 < m') {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ)
    (hsum : Summable fun j : NonzeroLattice d =>
      Lattice.jp j.1 ^ (2 * m') * Torus.funRealCoeff ψ j ^ 2) :
    HasSum (fun j : NonzeroLattice d => Torus.funRealCoeff ψ j *
        modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) Y
          (withDensityReal ρ))
      (modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad ψ)) Y (withDensityReal ρ)) := by
  classical
  obtain ⟨cstar, A, hA, hw, hw0, hdom⟩ := movsx_hdom hd hs0 hsd
  haveI := adjkd_isFiniteMeasure_withDensityReal hρ
  obtain ⟨Θ, hΘ⟩ := adjkd_modEn_bound hd hs0 hsd hA hdom Y hΛ₀ hρ
  obtain ⟨Cs, hCs⟩ := cbNorm_le_sobolevNorm (d := d) 2 m' (by exact_mod_cast hm')
  have hψ' : ContDiff ℝ 2 (Torus.lift ψ) := hψ
  have hψc : Continuous ψ := Torus.continuous_of_continuous_lift hψ'.continuous
  set G : Torus d → Euc d := periodicRieszGrad d s with hG
  set a : NonzeroLattice d → ℝ := fun j => Torus.funRealCoeff ψ j with ha
  have heC : ∀ n : ℕ, ∀ j : NonzeroLattice d, Torus.IsCk n (Torus.realMode j) := fun n j =>
    adjkd_isCk_of_smooth n (adjkd_isSmooth_realMode j)
  have hLip : ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ →
      IsLipschitzVF ((d : ℝ) * Torus.cbNorm 2 φ) (Torus.grad φ) := fun φ hφ => dyncmp_lip_grad hφ
  have hL0 : ∀ φ : Torus d → ℝ, 0 ≤ (d : ℝ) * Torus.cbNorm 2 φ := fun φ =>
    mul_nonneg (Nat.cast_nonneg d) (adjkd_cbNorm_nonneg 2 φ)
  have hrow : ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ →
      RowOK (withDensityReal ρ) (commKernel G (Torus.grad φ)) := fun φ hφ =>
    (adjkd_rowOK_lip hd hs0 hsd hdom hΛ₀ hρ (hL0 φ) (hLip φ hφ)).1
  have hrowE : ∀ j : NonzeroLattice d, RowOK (withDensityReal ρ)
      (commKernel G (Torus.grad (Torus.realMode j))) := fun j => hrow _ (heC 2 j)
  -- the identity for finite sets
  have hgradχ : ∀ (S : Finset (NonzeroLattice d)) (x : Torus d),
      Torus.grad (adjkdChi ψ S) x = Torus.grad ψ x - ∑ j ∈ S, a j • Torus.grad (Torus.realMode j) x := by
    intro S x
    have h1 : Torus.IsCk 1 (fun y => ψ y - Torus.mean ψ) :=
      PDE.MFLinear.isCk_sub_const (ContDiff.of_le hψ' (by norm_num)) (Torus.mean ψ)
    have h2 : Torus.IsCk 1 (fun y => ∑ j ∈ S, a j * Torus.realMode j y) :=
      adjkd_isCk_sum S a _ (fun j => heC 1 j)
    have e : adjkdChi ψ S = fun y => (ψ y - Torus.mean ψ) - ∑ j ∈ S, a j * Torus.realMode j y := rfl
    rw [e, PDE.MFLinear.grad_sub h1 h2, PDE.MFLinear.grad_sub_const ψ (Torus.mean ψ) x,
      adjkd_grad_sum S a _ (fun j => heC 1 j)]
  have hχ2 : ∀ S : Finset (NonzeroLattice d), Torus.IsCk 2 (adjkdChi ψ S) := by
    intro S
    have h1 : Torus.IsCk 2 (fun y => ψ y - Torus.mean ψ) := PDE.MFLinear.isCk_sub_const hψ _
    have h2 : Torus.IsCk 2 (fun y => ∑ j ∈ S, a j * Torus.realMode j y) :=
      adjkd_isCk_sum S a _ (fun j => heC 2 j)
    exact PDE.MFLinear.isCk_sub h1 h2
  have key : ∀ S : Finset (NonzeroLattice d),
      modulatedEnergy (commKernel G (Torus.grad ψ)) Y (withDensityReal ρ) -
          ∑ j ∈ S, a j * modulatedEnergy (commKernel G (Torus.grad (Torus.realMode j))) Y (withDensityReal ρ) =
        modulatedEnergy (commKernel G (Torus.grad (adjkdChi ψ S))) Y (withDensityReal ρ) := by
    intro S
    have hker : commKernel G (Torus.grad (adjkdChi ψ S)) = fun x y =>
        commKernel G (Torus.grad ψ) x y -
          ∑ j ∈ S, a j * commKernel G (Torus.grad (Torus.realMode j)) x y := by
      funext x y
      have e : Torus.grad (adjkdChi ψ S) = fun z => Torus.grad ψ z -
          ∑ j ∈ S, a j • Torus.grad (Torus.realMode j) z := funext (hgradχ S)
      rw [e, adjkd_commKernel_sub, adjkd_commKernel_sum]
    rw [hker, modulatedEnergy_sub (hrow ψ hψ)
      (adjkd_rowOK_sum S a (fun j => commKernel G (Torus.grad (Torus.realMode j))) hrowE),
      adjkd_modEn_sum S a (fun j => commKernel G (Torus.grad (Torus.realMode j))) hrowE]
  -- the bound
  have bound : ∀ S : Finset (NonzeroLattice d),
      |modulatedEnergy (commKernel G (Torus.grad (adjkdChi ψ S))) Y (withDensityReal ρ)| ≤
        A * ((d : ℝ) * (Cs * sobolevNorm m' (adjkdChi ψ S))) * |Θ| := by
    intro S
    have h1 := hΘ _ (Torus.grad (adjkdChi ψ S)) (hL0 _) (hLip _ (hχ2 S))
    have h2 := hCs (adjkdChi ψ S) (adjkd_chi_sobolev hψc hsum S) (hχ2 S)
    have h3 : (d : ℝ) * Torus.cbNorm 2 (adjkdChi ψ S) ≤
        (d : ℝ) * (Cs * sobolevNorm m' (adjkdChi ψ S)) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d)
    refine h1.trans ?_
    have hΘ0 : Θ ≤ |Θ| := le_abs_self Θ
    calc A * ((d : ℝ) * Torus.cbNorm 2 (adjkdChi ψ S)) * Θ
        ≤ A * ((d : ℝ) * Torus.cbNorm 2 (adjkdChi ψ S)) * |Θ| :=
          mul_le_mul_of_nonneg_left hΘ0 (mul_nonneg hA (hL0 _))
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hA) (abs_nonneg _)
  have hlim : Tendsto (fun S : Finset (NonzeroLattice d) =>
      A * ((d : ℝ) * (Cs * sobolevNorm m' (adjkdChi ψ S))) * |Θ|) atTop (𝓝 0) := by
    have := ((((adjkd_chi_sobolev_tendsto hψc hsum).const_mul Cs).const_mul (d : ℝ)).const_mul A).mul_const |Θ|
    simpa using this
  rw [HasSum]
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun S => norm_nonneg _) (fun S => ?_) hlim
  rw [Real.norm_eq_abs, abs_sub_comm, key S]
  exact bound S

end HRS.AdjK
