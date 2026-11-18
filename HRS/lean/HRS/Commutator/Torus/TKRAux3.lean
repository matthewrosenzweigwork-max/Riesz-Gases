import HRS.Commutator.Torus.TKRAux2

/-!
# T-KR helpers, part 3: Fourier series of `Ψ_η`, of `∇g_{≤}` and of `∇g_{>}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s η : ℝ}

/-- The coefficient of the `i`-th component of `∇g`: `2πi k_i ĝ(k)`. -/
def tkrCI (d : ℕ) (s : ℝ) (i : Fin d) (k : Lattice d) : ℂ :=
  (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)

/-- The low-pass multiplier `χ(ηk)`. -/
def tkrChi (η : ℝ) (k : Lattice d) : ℝ := Whole.chi (η • Lattice.toEuc k)

lemma tkrChi_eq_zero {k : Lattice d} (h : 2 ≤ η * Lattice.enorm k) (hη : 0 < η) : tkrChi η k = 0 := by
  unfold tkrChi
  apply Whole.cmxFB_chi_zero
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  exact h

lemma tkrChi_eq_one {k : Lattice d} (h : η * Lattice.enorm k ≤ 1) (hη : 0 < η) : tkrChi η k = 1 := by
  unfold tkrChi
  apply Whole.cmxFB_chi_one
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  exact h

lemma tkr_isTrigPoly (hη : 0 < η) {c : Lattice d → ℂ} (hc : ∀ k, c k ≠ 0 → tkrChi η k ≠ 0) :
    HRS.PDE.IsTrigPoly ⌈2 / η⌉₊ c := by
  refine HRS.HDB.isTrigPoly_of_enorm_lt (fun k hk => ?_)
  have h1 := hc k hk
  by_contra hcon
  push Not at hcon
  apply h1
  apply tkrChi_eq_zero _ hη
  rw [div_le_iff₀ hη] at hcon
  linarith

/-- A continuous function with summable Fourier coefficients is the sum of its Fourier series. -/
lemma tkr_series {F : Torus d → ℂ} (hF : Continuous F)
    (hsum : Summable fun k : Lattice d => ‖∫ x, Torus.mode (-k) x * F x‖) (z : Torus d) :
    HasSum (fun k : Lattice d => (∫ x, Torus.mode (-k) x * F x) * Torus.mode k z) (F z) := by
  set f : C(Torus d, ℂ) := ⟨F, hF⟩ with hf
  have hco : ∀ k : Lattice d, UnitAddTorus.mFourierCoeff f k = ∫ x, Torus.mode (-k) x * F x := by
    intro k
    have := HRS.PDE.funFourierCoeff_eq_int F k
    exact this
  have hs : Summable (UnitAddTorus.mFourierCoeff f) := by
    refine Summable.of_norm ?_
    simpa [hco] using hsum
  have := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs z
  simp only [hco, smul_eq_mul] at this
  exact this

lemma tkr_mode_sub (k : Lattice d) (x y : Torus d) :
    Torus.mode k (x - y) = Torus.mode k x * Torus.mode (-k) y := by
  have h1 := HRS.ResponseAux.mode_sub_pt k x y
  have h2 := Torus.mode_neg_lattice k y
  calc Torus.mode k (x - y) = Torus.mode k (x - y) * (Torus.mode (-k) y * Torus.mode k y) := by
        rw [h2, mul_one]
    _ = (Torus.mode k (x - y) * Torus.mode k y) * Torus.mode (-k) y := by ring
    _ = _ := by rw [← h1]

/-- Fourier series of `Ψ_η`. -/
lemma tkr_perio_psi_eq (hη : 0 < η) (z : Torus d) :
    ((perio (Whole.psiL η⁻¹ : Euc d → ℝ) z : ℝ) : ℂ) =
      HRS.PDE.Kern.trig (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ)) z := by
  have hL : 0 < η⁻¹ := inv_pos.2 hη
  set Ψ : Torus d → ℝ := perio (Whole.psiL η⁻¹ : Euc d → ℝ) with hΨ
  have hco : ∀ k : Lattice d, ∫ x, Torus.mode (-k) x * ((Ψ x : ℝ) : ℂ) = ((tkrChi η k : ℝ) : ℂ) := by
    intro k
    have := tkr_fcoef_perio_psi hL k
    unfold Torus.fcoef at this
    rw [this]
    unfold tkrChi
    rw [inv_inv]
  have hT : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊ (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ)) :=
    tkr_isTrigPoly hη (fun k hk => by simpa using hk)
  have hsum : Summable fun k : Lattice d => ‖∫ x, Torus.mode (-k) x * ((Ψ x : ℝ) : ℂ)‖ := by
    simp_rw [hco]
    refine summable_of_ne_finset_zero (s := HRS.PDE.Kern.boxF d ⌈2 / η⌉₊) fun k hk => ?_
    have : ((tkrChi η k : ℝ) : ℂ) = 0 := by
      by_contra h
      exact hk (HRS.PDE.Kern.mem_boxF.2 (hT k h))
    simp [this]
  have hser := tkr_series (F := fun x => ((Ψ x : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (tkr_perio_psi_continuous hL)) hsum z
  simp_rw [hco] at hser
  rw [← hser.tsum_eq]
  rfl

end HRS.Commutator.TorusNote
