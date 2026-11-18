import HRS.Sections.Q38bAux2

/-!
# Packet Q38b, part 3: the homogeneous classical adjoint solution and equilibrium semigroup

For `V = 0`, `ρ_β = 1`: `U^{0,τ} e_k = exp(-λ_k τ) e_k` and `S_β(τ) e_k = exp(-λ_k τ) e_k`,
`λ_k = (2π|k|)²(β⁻¹ + ĝ(k))`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

variable {d : ℕ}

/-- The homogeneous thermal density: `ρ = 1` solves the thermal equation for `V = 0`. -/
theorem q38b_isThermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) :
    IsThermalDensity (periodicRiesz d s) (fun _ : Torus d => (0 : ℝ)) β (fun _ => (1 : ℝ)) := by
  have hρ : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one, measurable_const, by simp⟩
  refine ⟨hρ, fun x => ?_⟩
  have h0 : ∀ x : Torus d, convFun (periodicRiesz d s) (fun _ : Torus d => (1 : ℝ)) x = 0 := by
    intro x
    unfold convFun
    simp only [mul_one]
    rw [integral_sub_left_eq_self (fun y => periodicRiesz d s y) (μ := (volume : Measure (Torus d))) x]
    exact (integral_periodicRiesz hd hs0 hsd).2
  simp [h0]

/-- The rate `λ_k = (2π|k|)²(β⁻¹ + ĝ(k))`. -/
def q38b_rate (d : ℕ) (s β : ℝ) (k : NonzeroLattice d) : ℝ :=
  (2 * Real.pi * Lattice.enorm k.1) ^ 2 * (β⁻¹ + rieszCoeff d s k.1)

/-- The backward generator of the homogeneous mean-field dynamics on a multiple of a real mode. -/
theorem q38b_bg (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : NonzeroLattice d) (c : ℝ) (x : Torus d) :
    backwardGenerator (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ) (fun _ => (1 : ℝ))
      (fun y => c * Torus.realMode k y) x = -(q38b_rate d s β k * (c * Torus.realMode k x)) := by
  have hρ1 : Torus.IsCk 1 (fun _ : Torus d => (1 : ℝ)) := contDiff_const
  have hρ2 : Torus.IsCk 2 (fun _ : Torus d => (1 : ℝ)) := contDiff_const
  have hV2 : Torus.IsCk 2 (fun _ : Torus d => (0 : ℝ)) := contDiff_const
  have hf2 : Torus.IsCk 2 (fun y => c * Torus.realMode k y) :=
    q38b_isCk_const_mul (by simpa using q38b_isCk_realMode k 2) c
  have hgen := PDE.MFOneLe.generator_eq (by omega : 1 ≤ d)
    (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ) rfl β hβ rfl hV2 (fun _ => (1 : ℝ))
    (q38b_isThermal hd hs0 hsd β) hρ2 (fun _ => one_pos) (fun y => c * Torus.realMode k y) hf2 x
  rw [hgen]
  have hLop : Lop (fun _ : Torus d => (1 : ℝ)) (fun y => c * Torus.realMode k y) x =
      (2 * Real.pi * Lattice.enorm k.1) ^ 2 * (c * Torus.realMode k x) := by
    unfold Lop
    rw [PDE.MFAux.div_smul_grad _ _ hρ1 hf2 x]
    have := q38b_div_realMode k c x
    simp only [inv_one, neg_mul, one_mul] at this ⊢
    rw [this]
    ring
  rw [hLop]
  have hconv : convFun (periodicRiesz d (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ).s)
      (fun y => ∑ j, Torus.partialDeriv j (fun y' => (fun _ : Torus d => (1 : ℝ)) y' *
        Torus.partialDeriv j (fun y => c * Torus.realMode k y) y') y) x =
      -((2 * Real.pi * Lattice.enorm k.1) ^ 2 * c) * rieszCoeff d s k.1 * Torus.realMode k x := by
    have e : (fun y => ∑ j, Torus.partialDeriv j (fun y' => (fun _ : Torus d => (1 : ℝ)) y' *
        Torus.partialDeriv j (fun y => c * Torus.realMode k y) y') y) =
        fun y => (-((2 * Real.pi * Lattice.enorm k.1) ^ 2 * c)) * Torus.realMode k y := by
      funext y
      rw [q38b_div_realMode]
      ring
    rw [e]
    exact q38b_convFun_c_realMode hd hs0 hsd k _ x
  rw [hconv]
  unfold q38b_rate
  show -(β⁻¹ * _) + _ = _
  ring

/-- `r ↦ exp(-λ(T-r)) e_k` is a classical adjoint solution on `[0,T]` with terminal datum `e_k`. -/
theorem q38b_isClassical (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : NonzeroLattice d) (T : ℝ) :
    IsClassicalAdjointSolution (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
      (fun _ => (fun _ : Torus d => (1 : ℝ))) T (Torus.realMode k)
      (fun r y => Real.exp (-(q38b_rate d s β k) * (T - r)) * Torus.realMode k y) := by
  have he2 : Torus.IsCk 2 (Torus.realMode k) := by simpa using q38b_isCk_realMode k 2
  refine ⟨fun r _ => q38b_isCk_const_mul he2 _, fun j hj => ?_, ?_, ?_, ?_⟩
  · have hcont : Continuous fun y : Euc d => iteratedFDeriv ℝ j (Torus.lift (Torus.realMode k)) y :=
      he2.continuous_iteratedFDeriv (by exact_mod_cast hj)
    have hfun : ∀ r : ℝ, Torus.lift (fun y => Real.exp (-(q38b_rate d s β k) * (T - r)) *
        Torus.realMode k y) =
        fun z => Real.exp (-(q38b_rate d s β k) * (T - r)) • Torus.lift (Torus.realMode k) z :=
      fun r => rfl
    have hcd : ContDiff ℝ 2 (Torus.lift (Torus.realMode k)) := he2
    have hcdn : ∀ z, ContDiffAt ℝ j (Torus.lift (Torus.realMode k)) z := fun z =>
      (hcd.of_le (by exact_mod_cast hj)).contDiffAt
    have hexp : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d =>
        Real.exp (-(q38b_rate d s β k) * (T - p.1.1)) := by fun_prop
    refine (hexp.smul (hcont.comp continuous_snd)).congr fun p => ?_
    rw [hfun, iteratedFDeriv_const_smul_apply' (hcdn p.2)]
    rfl
  · funext y
    simp
  · intro x r hr
    have h1 : HasDerivAt (fun r' : ℝ => -(q38b_rate d s β k) * (T - r')) (q38b_rate d s β k) r := by
      have := ((hasDerivAt_id r).const_sub T).const_mul (-(q38b_rate d s β k))
      simpa using this
    have h2 := (h1.exp).mul_const (Torus.realMode k x)
    convert h2 using 1
    rw [q38b_bg hd hs0 hsd hβ k]
    ring
  · have hc : Continuous fun p : Set.Icc (0 : ℝ) T × Torus d =>
        -(q38b_rate d s β k * (Real.exp (-(q38b_rate d s β k) * (T - p.1.1)) *
          Torus.realMode k p.2)) := by
      have := q38b_continuous_realMode k
      fun_prop
    refine hc.congr fun p => ?_
    exact (q38b_bg hd hs0 hsd hβ k _ _).symm

/-- `U^{0,τ} e_k = exp(-λ_k τ) e_k` for the homogeneous frozen dynamics. -/
theorem q38b_propagator (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : NonzeroLattice d) (τ : ℝ) (hτ : 0 ≤ τ) :
    propagator (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ) (fun _ => (fun _ : Torus d => (1 : ℝ)))
      0 τ (Torus.realMode k) =
      fun y => Real.exp (-(q38b_rate d s β k) * τ) * Torus.realMode k y := by
  set D := PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ with hD
  rcases eq_or_lt_of_le hτ with h0 | hpos
  · subst h0
    have hK : PDE.ClassicalAux.ConvKernelFacts d D.s :=
      PDE.ClassicalAux.convKernelFacts_of_two_le hd D.hs0 D.hsd
    have hV1 : Torus.IsCk 1 D.V := contDiff_const
    have hρ1 : Torus.IsCk 1 ((fun _ => (fun _ : Torus d => (1 : ℝ))) (0 : ℝ)) := contDiff_const
    have he2 : Torus.IsCk 2 (Torus.realMode k) := by simpa using q38b_isCk_realMode k 2
    rw [PDE.MFSemigroup.propagator_zero D hK hV1 _ hρ1 he2]
    funext y
    simp
  · have hprob : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
      ⟨fun _ => zero_le_one, measurable_const, by simp⟩
    have hsm : Torus.IsSmooth (fun _ : Torus d => (1 : ℝ)) := by
      unfold Torus.IsSmooth Torus.IsCk; exact contDiff_const
    have hsm0 : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) := by
      unfold Torus.IsSmooth Torus.IsCk; exact contDiff_const
    obtain ⟨R, MB, Λ, VB, hA⟩ := PDE.MFSemigroup.adjointData_frozen s hs0 hsd β hβ
      (fun _ => (0 : ℝ)) hsm0 (fun _ => (1 : ℝ)) hprob hsm (fun _ => one_pos) (PDE.mStar d)
    have hF := q38b_isClassical hd hs0 hsd hβ k τ
    have := PDE.MFSemigroup.propagator_frozen_eq hd s hs0 hsd (PDE.mStar d)
      (by unfold PDE.mStar; omega) R MB Λ VB D 0 τ (fun _ => (1 : ℝ)) (hA 0 τ hpos)
      (T' := τ) ⟨hpos, le_rfl⟩ hF (τ := τ) ⟨hpos, le_rfl⟩
    rw [this]
    funext y
    simp

/-- `S_β(τ) e_k = exp(-λ_k τ) e_k` for `τ ≥ 0`, homogeneous case. -/
theorem q38b_equilibriumSemigroup (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (k : NonzeroLattice d) (τ : ℝ) (hτ : 0 ≤ τ) :
    PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
      (fun _ => (1 : ℝ)) τ (Torus.realMode k) =
      fun y => Real.exp (-(q38b_rate d s β k) * τ) * Torus.realMode k y := by
  unfold PDE.equilibriumSemigroup
  rw [q38b_propagator hd hs0 hsd hβ k τ hτ]
  funext y
  unfold projMean pair
  have hvol : (withDensityReal (fun _ : Torus d => (1 : ℝ))) = (volume : Measure (Torus d)) := by
    unfold withDensityReal
    simp
  rw [hvol, q38b_int_c_realMode, sub_zero]

end HRS
