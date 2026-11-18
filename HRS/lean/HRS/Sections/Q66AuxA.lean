import HRS.PDE.MeanFieldThermalReg
import HRS.PDE.MeanFieldAprioriClassical
import HRS.Equilibrium.PoleCavity

/-!
# Packet Q66 (static Edgeworth, Lemma 7.4): regularity of the one-body response, part A

Prefix `q66_`.  Fourier-side facts for the response equation `h + β K_μ h = P_μ φ`:
coefficients of convolutions with integrable kernels, `ĝ ∈ ℓ²` for `s < d/2`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.Q66

open HRS.PDE HRS.PDE.MFAux

variable {d : ℕ}

/-- Fourier coefficients of a convolution of two integrable functions (the `L¹` version of
`MFAux.funFourierCoeff_convFun`). -/
theorem q66_funFourierCoeff_convFun {g h : Torus d → ℝ} (hg : Integrable g) (hhi : Integrable h)
    (k : Lattice d) :
    Torus.funFourierCoeff (fun x => (convFun g h x : ℂ)) k =
      Torus.funFourierCoeff (fun x => (g x : ℂ)) k * Torus.funFourierCoeff (fun x => (h x : ℂ)) k := by
  rw [funFourierCoeff_eq_int, funFourierCoeff_eq_int, funFourierCoeff_eq_int]
  set e : Torus d → ℂ := fun x => UnitAddTorus.mFourier (-k) x with he
  have hnorm : ∀ x, ‖e x‖ = 1 := fun x => by simpa [he, Torus.mode] using Torus.norm_mode (-k) x
  have hadd : ∀ x y, e x = e (x - y) * e y := by
    intro x y
    have := Torus.mode_add_arg (-k) (x - y) y
    simp only [Torus.mode, sub_add_cancel] at this
    simpa [he] using this
  have hec : Continuous e := (UnitAddTorus.mFourier (-k)).continuous
  have hI : Integrable (fun p : Torus d × Torus d => h p.2 * g (p.1 - p.2)) (volume.prod volume) :=
    Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hhi hg
  have hF : Integrable (fun p : Torus d × Torus d => e p.1 * (((g (p.1 - p.2) * h p.2 : ℝ)) : ℂ))
      (volume.prod volume) := by
    have h1 : Integrable (fun p : Torus d × Torus d => (((h p.2 * g (p.1 - p.2) : ℝ)) : ℂ))
        (volume.prod volume) := hI.ofReal
    refine (h1.bdd_mul (hec.comp continuous_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => (hnorm _).le)).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [mul_comm (h p.2) (g (p.1 - p.2))]
    rfl
  have step1 : ∀ x, e x * ((convFun g h x : ℝ) : ℂ) = ∫ y, e x * (((g (x - y) * h y : ℝ)) : ℂ) := by
    intro x
    rw [integral_const_mul, integral_complex_ofReal]
    rfl
  show ∫ x, e x * ((convFun g h x : ℝ) : ℂ) = (∫ x, e x * (g x : ℂ)) * ∫ x, e x * (h x : ℂ)
  simp_rw [step1]
  rw [integral_integral_swap hF]
  have step2 : ∀ y, ∫ x, e x * (((g (x - y) * h y : ℝ)) : ℂ) =
      (∫ x, e x * (g x : ℂ)) * (e y * (h y : ℂ)) := by
    intro y
    have : ∀ x, e x * (((g (x - y) * h y : ℝ)) : ℂ) =
        (e y * (h y : ℂ)) * (e (x - y) * (g (x - y) : ℂ)) := by
      intro x
      rw [hadd x y]
      push_cast
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_sub_right_eq_self (fun x => e x * (g x : ℂ))]
    ring
  simp_rw [step2]
  rw [integral_const_mul]

/-- `ĝ ∈ ℓ²` exactly when `s < d/2`. -/
theorem q66_rieszCoeff_sq_summable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    Summable fun k : Lattice d => rieszCoeff d s k ^ 2 := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  rw [Torus.summable_lattice_iff]
  have hm : (d : ℝ) < 2 * ((d : ℝ) - s) := by linarith
  have h1 := summable_jp_rpow (d := d) ((d : ℝ) - s) hm
  set C0 : ℝ := |rieszConst d s| * (2 : ℝ) ^ (((d : ℝ) - s) / 2) with hC0
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (h1.mul_left (C0 ^ 2))
  have hb := HRS.PDE.MFThermalReg.abs_rieszCoeff_le_sobWeight (d := d) s hsd k.1
  have hw : sobWeight (-(((d : ℝ) - s) / 2)) k.1 = Lattice.jp k.1 ^ (-((d : ℝ) - s)) := by
    rw [sobWeight_eq_jp]; congr 1; ring
  rw [hw] at hb
  have hj0 : 0 ≤ Lattice.jp k.1 ^ (-((d : ℝ) - s)) := by
    unfold Lattice.jp; positivity
  have : rieszCoeff d s k.1 ^ 2 = |rieszCoeff d s k.1| ^ 2 := (sq_abs _).symm
  rw [this]
  calc |rieszCoeff d s k.1| ^ 2 ≤ (C0 * Lattice.jp k.1 ^ (-((d : ℝ) - s))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = C0 ^ 2 * Lattice.jp k.1 ^ (-(2 * ((d : ℝ) - s))) := by
        have hjp : 0 ≤ Lattice.jp k.1 := by unfold Lattice.jp; positivity
        have e : (Lattice.jp k.1 ^ (-((d : ℝ) - s))) ^ 2 = Lattice.jp k.1 ^ (-(2 * ((d : ℝ) - s))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hjp]; congr 1; push_cast; ring
        rw [mul_pow, e]

end HRS.Q66

end
