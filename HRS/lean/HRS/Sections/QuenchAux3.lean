import HRS.Sections.QuenchAux2

/-!
# Packet QUENCH (Q27), part 3: the Gaussian field on modes

Susceptibility covariance on real modes; the explicit covariance matrix of the Gaussian part of
`IsGaussianLimitField` on modes (`covMat`); `ModeField`: the data extracted from
`IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z` for the gradient dynamics on the homogeneous torus.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

lemma eval_mode {m : ℝ} (F : NegSobolev d m) (c : ℝ) (j : NonzeroLattice d) :
    NegSobolev.eval F (fun y => c * Torus.realMode j y) = c * NegSobolev.fourierCoeff F j := by
  classical
  unfold NegSobolev.eval
  rw [tsum_eq_single j]
  · rw [funRealCoeff_mode]; simp [mul_comm]
  · intro k hk
    rw [funRealCoeff_mode, if_neg hk]; simp

lemma eval_mode_one {m : ℝ} (F : NegSobolev d m) (j : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode j) = NegSobolev.fourierCoeff F j := by
  have : Torus.realMode j = fun y => 1 * Torus.realMode j y := by funext y; simp
  rw [this, eval_mode, one_mul]

theorem susc_modes (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (j j' : NonzeroLattice d) :
    susceptibilityCov (periodicRiesz d s) (volume : Measure (Torus d)) β (Torus.realMode j)
      (Torus.realMode j') = if j = j' then (1 + β * rieszCoeff d s j.1)⁻¹ else 0 := by
  unfold susceptibilityCov l2Inner
  have hp : projMean (volume : Measure (Torus d)) (Torus.realMode j) = Torus.realMode j := by
    funext x
    unfold projMean pair
    rw [Torus.integral_realMode, sub_zero]
  rw [hp]
  have hf : (Torus.realMode j') = fun y => (1 : ℝ) * Torus.realMode j' y := by
    funext y; simp
  have hae := q38b_responseInverse_eq hd hs0 hsd hβ j' 1
  rw [← hf] at hae
  have : ∫ x : Torus d, Torus.realMode j x *
      responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β (Torus.realMode j') x =
      ∫ x : Torus d, (1 + β * rieszCoeff d s j'.1)⁻¹ *
        (Torus.realMode j x * Torus.realMode j' x) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
    ring
  rw [this, integral_const_mul, Torus.realMode_orthonormal j j']
  by_cases h : j = j'
  · subst h; simp
  · simp [h]

/-- `U^{r,τ} e_k = e^{-λ_k(τ-r)} e_k`. -/
theorem propagator_mode' (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : NonzeroLattice d) {r τ : ℝ} (hr : 0 ≤ r) (hrτ : r ≤ τ) :
    propagator (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ) (fun _ => (fun _ : Torus d => (1 : ℝ)))
      r τ (Torus.realMode k) =
      fun y => Real.exp (-(q38b_rate d s β k) * (τ - r)) * Torus.realMode k y := by
  have h := propagator_mode hd hs0 hsd hβ k 1 hr hrτ
  have e : (fun y => (1 : ℝ) * Torus.realMode k y) = Torus.realMode k := by funext y; simp
  rw [e] at h
  rw [h]
  funext y
  simp

theorem noise_entry (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (j j' : NonzeroLattice d) {ta tb : ℝ} (ha : 0 ≤ ta) (hb : 0 ≤ tb) :
    2 * β⁻¹ * ∫ r in Set.Icc (0 : ℝ) (min ta tb), ∫ x : Torus d,
      inner ℝ (Torus.grad (propagator (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
          (fun _ => (fun _ : Torus d => (1 : ℝ))) r ta (Torus.realMode j)) x)
        (Torus.grad (propagator (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
          (fun _ => (fun _ : Torus d => (1 : ℝ))) r tb (Torus.realMode j')) x) * 1 =
      if j = j' then varMode d s β j.1 * ouK (lamMode d s β j.1) ta tb else 0 := by
  have hcongr : ∀ r ∈ Set.Icc (0 : ℝ) (min ta tb), ∫ x : Torus d,
      inner ℝ (Torus.grad (propagator (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
          (fun _ => (fun _ : Torus d => (1 : ℝ))) r ta (Torus.realMode j)) x)
        (Torus.grad (propagator (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
          (fun _ => (fun _ : Torus d => (1 : ℝ))) r tb (Torus.realMode j')) x) * 1 =
      if j = j' then Real.exp (-(q38b_rate d s β j) * (ta - r)) * Real.exp (-(q38b_rate d s β j') * (tb - r)) *
        (2 * Real.pi * Lattice.enorm j.1) ^ 2 else 0 := by
    intro r hr
    have hra : r ≤ ta := hr.2.trans (min_le_left _ _)
    have hrb : r ≤ tb := hr.2.trans (min_le_right _ _)
    rw [propagator_mode' hd hs0 hsd hβ j hr.1 hra, propagator_mode' hd hs0 hsd hβ j' hr.1 hrb]
    simp only [mul_one]
    rw [int_grad_modes]
  rw [setIntegral_congr_fun measurableSet_Icc hcongr]
  by_cases h : j = j'
  · subst h
    simp only [ite_true]
    have hl : 0 < q38b_rate d s β j := lamMode_pos hd hs0 hsd hβ j
    have h1 : ∫ r in Set.Icc (0 : ℝ) (min ta tb), Real.exp (-(q38b_rate d s β j) * (ta - r)) *
        Real.exp (-(q38b_rate d s β j) * (tb - r)) * (2 * Real.pi * Lattice.enorm j.1) ^ 2 =
        ouK (q38b_rate d s β j) ta tb / (2 * q38b_rate d s β j) * (2 * Real.pi * Lattice.enorm j.1) ^ 2 := by
      rw [integral_mul_const, int_exp_Icc hl ha hb]
    rw [h1]
    have hv := lamMode_mul_varMode hd hs0 hsd hβ j
    have hlv : lamMode d s β j.1 = q38b_rate d s β j := rfl
    rw [hlv] at hv ⊢
    have hl0 := hl.ne'
    have : β⁻¹ * (2 * Real.pi * Lattice.enorm j.1) ^ 2 = q38b_rate d s β j * varMode d s β j.1 := hv.symm
    calc 2 * β⁻¹ * (ouK (q38b_rate d s β j) ta tb / (2 * q38b_rate d s β j) *
          (2 * Real.pi * Lattice.enorm j.1) ^ 2)
        = (β⁻¹ * (2 * Real.pi * Lattice.enorm j.1) ^ 2) * ouK (q38b_rate d s β j) ta tb /
          q38b_rate d s β j := by field_simp
      _ = _ := by rw [this]; field_simp
  · simp [h]

/-! ### The mode field -/

section ModeField

variable {s β β₀ m : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-- The noise coordinate `G_j(t) = Z^t(e_j) - e^{-λ_j t} Z^0(e_j)` (with `Z^0` replaced by `Y`). -/
def ncoord (s β : ℝ) (Y : Ω → NegSobolev d m) (Z : ℝ → Ω → NegSobolev d m)
    (j : NonzeroLattice d) (t : ℝ) (ω : Ω) : ℝ :=
  NegSobolev.fourierCoeff (Z t ω) j -
    Real.exp (-(lamMode d s β j.1) * t) * NegSobolev.fourierCoeff (Y ω) j

/-- The data of a Gaussian limit field on the modes of the homogeneous torus. -/
structure ModeField (d : ℕ) (s β β₀ m : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → Ω → NegSobolev d m) (Y : Ω → NegSobolev d m) : Prop where
  meas : ∀ t, Measurable (Z t)
  cont : ∀ᵐ ω ∂P, ∀ T : ℝ, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)
  init : ∀ᵐ ω ∂P, Z 0 ω = Y ω
  measY : AEMeasurable Y P
  cenY : IsCenteredGaussian (P.map Y)
  covY : ∀ j j' : NonzeroLattice d, ∫ ω, NegSobolev.fourierCoeff (Y ω) j * NegSobolev.fourierCoeff (Y ω) j' ∂P =
    if j = j' then varMode d s β₀ j.1 else 0
  gp : ∀ (p : ℕ) (js : Fin p → NonzeroLattice d) (ts : Fin p → ℝ), (∀ a, 0 ≤ ts a) →
    IndepFun (fun ω => (WithLp.toLp 2 (fun a => ncoord s β Y Z (js a) (ts a) ω) : EuclideanSpace ℝ (Fin p))) Y P ∧
    P.map (fun ω => (WithLp.toLp 2 (fun a => ncoord s β Y Z (js a) (ts a) ω) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (covMat (fun j => varMode d s β j.1) (fun j => lamMode d s β j.1) js ts)

theorem modeField_of_limit (hd : 2 ≤ d) (hβ : 0 < β) (hβ₀ : 0 < β₀) (D : DynData d)
    (hD : IsGradientData D s β (fun _ => 0)) (P : Measure Ω)
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z) :
    ∃ Y : Ω → NegSobolev d m, ModeField d s β β₀ m P Z Y := by
  have hs0 : 0 ≤ s := hD.1 ▸ D.hs0
  have hsd : s < d := hD.1 ▸ D.hsd
  obtain rfl := dyn_eq hβ hs0 hsd D hD
  obtain ⟨Y, hY, hsol⟩ := hZ
  refine ⟨Y, ?_⟩
  have hmeas : ∀ t, Measurable (Z t) := fun t => (hsol 0).meas t
  have hinit : ∀ᵐ ω ∂P, Z 0 ω = Y ω := (hsol 0).init
  have hmY : AEMeasurable Y P := (hmeas 0).aemeasurable.congr hinit
  refine ⟨hmeas, ?_, hinit, hmY, hY.1, ?_, ?_⟩
  · have : ∀ᵐ ω ∂P, ∀ n : ℕ, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (n : ℝ)) :=
      ae_all_iff.2 fun n => (hsol n).cont
    filter_upwards [this] with ω hω T
    obtain ⟨n, hn⟩ := exists_nat_ge T
    exact (hω n).mono (Set.Icc_subset_Icc le_rfl hn)
  · intro j j'
    have hmeasf : ∀ k : NonzeroLattice d, Measurable (fun F : NegSobolev d m => NegSobolev.fourierCoeff F k) := by
      intro k
      have := q38b_measurable_eval_realMode (m := m) k
      have e : (fun F : NegSobolev d m => NegSobolev.fourierCoeff F k) =
          fun F => NegSobolev.eval F (Torus.realMode k) := by
        funext F; exact (eval_mode_one F k).symm
      rw [e]; exact this
    have h1 : ∫ ω, NegSobolev.fourierCoeff (Y ω) j * NegSobolev.fourierCoeff (Y ω) j' ∂P =
        ∫ F, NegSobolev.fourierCoeff F j * NegSobolev.fourierCoeff F j' ∂(P.map Y) := by
      exact (integral_map hmY (f := fun F : NegSobolev d m => NegSobolev.fourierCoeff F j *
        NegSobolev.fourierCoeff F j') (((hmeasf j).mul (hmeasf j')).aestronglyMeasurable)).symm
    rw [h1]
    have h2 := hY.2 (Torus.realMode j) (Torus.realMode j') (q38b_isSmooth_realMode j)
      (q38b_isSmooth_realMode j')
    simp only [eval_mode_one] at h2
    rw [h2]
    exact susc_modes hd hs0 hsd hβ₀ j j'
  · intro p js ts ht
    obtain ⟨T, hT0, hT⟩ : ∃ T : ℝ, 0 ≤ T ∧ ∀ a, ts a ≤ T := ⟨∑ a, |ts a|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
      fun a => by
        calc ts a ≤ |ts a| := le_abs_self _
          _ ≤ ∑ a, |ts a| := Finset.single_le_sum (f := fun a => |ts a|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ a)⟩
    have h := (hsol T).gaussian_part p ts (fun a => Torus.realMode (js a)) (fun a => ⟨ht a, hT a⟩)
      (fun a => q38b_isSmooth_realMode (js a))
    have hG : (fun ω => (WithLp.toLp 2 (fun a => NegSobolev.eval (Z (ts a) ω) (Torus.realMode (js a)) -
          NegSobolev.eval (Y ω) (propagator (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
            (fun _ => (fun _ : Torus d => (1 : ℝ))) 0 (ts a) (Torus.realMode (js a)))) :
          EuclideanSpace ℝ (Fin p))) =
        fun ω => (WithLp.toLp 2 (fun a => ncoord s β Y Z (js a) (ts a) ω) : EuclideanSpace ℝ (Fin p)) := by
      funext ω
      congr 1
      funext a
      rw [propagator_mode' hd hs0 hsd hβ (js a) le_rfl (ht a), eval_mode, eval_mode_one]
      simp only [ncoord, sub_zero, lamMode, q38b_rate]
    rw [← hG]
    refine ⟨h.1, h.2.trans ?_⟩
    congr 1
    ext a b
    simp only [covMat, Matrix.of_apply]
    exact noise_entry hd hs0 hsd hβ (js a) (js b) (ht a) (ht b)

end ModeField

end Qch

end HRS
