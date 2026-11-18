import HRS.Sections.Q66AuxC
import HRS.PDE.MeanFieldThermalReg
import HRS.PDE.MeanFieldInputs

/-!
# Packet Q66: regularity of the one-body response, part D (smoothness of the response)

For a smooth positive probability density `ρ`, a smooth test `φ` and `0 ≤ s < d/2`, `β ≥ 0`, the
response `h = R_{β,μ}P_μ φ` has a smooth representative `r`, which satisfies the response equation
at every point.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate BoundedContinuousFunction

noncomputable section

namespace HRS.Q66

open HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder HRS.PDE.MFThermalReg

variable {d : ℕ}

theorem q66_isCk_of_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Torus d → E}
    (h : Torus.IsSmooth f) (n : ℕ) : Torus.IsCk (n : WithTop ℕ∞) f :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from h)
    (by exact_mod_cast le_top)

/-- The Sobolev bootstrap for `r = φ - β (g * (ρ r) - m)` (all `r ∈ H^N`). -/
theorem q66_bootstrap (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (β c : ℝ) {r : Torus d → ℝ} (hrc : Continuous r)
    (hr : ∀ x, r x = φ x - β * convFun (periodicRiesz d s) (fun y => ρ y * r y) x + c) :
    Torus.IsSmooth r := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have F : MFInputs.MFKernelFacts d s := MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  have hρc : Continuous ρ := q66_cont_of_smooth hρ.smooth
  have hφc : Continuous φ := q66_cont_of_smooth hφ
  have hδ : (1 : ℝ) ≤ (d : ℝ) - s := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set G : Torus d → ℝ := convFun (periodicRiesz d s) (fun y => ρ y * r y) with hG
  have hGc : Continuous G := continuous_convFun F.integrable (hρc.mul hrc)
  have hrG : r = fun x => 1 * φ x + (-β) * G x + c := by
    funext x; rw [hr x]; ring
  have hφH : ∀ n : ℕ, MemHs (n : ℝ) (coeffOf φ) := fun n =>
    memHs_of_isCk n φ (q66_isCk_of_smooth hφ n)
  have hρH : ∀ n : ℕ, MemHs (n : ℝ) (coeffOf ρ) := fun n =>
    memHs_of_isCk n ρ (q66_isCk_of_smooth hρ.smooth n)
  have hind : ∀ n : ℕ, MemHs (n : ℝ) (coeffOf r) := by
    intro n
    induction n with
    | zero =>
      have := (coeffOf_memHs_zero hrc).1
      simpa using this
    | succ n ih =>
      -- product with `ρ`
      obtain ⟨C, -, hC⟩ := MFProduct.exists_product_bound (d := d) ((n + d : ℕ) : ℝ) (n : ℝ) (n : ℝ)
        (Nat.cast_nonneg n) (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) le_rfl
        (by push_cast; have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
            linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      have hmul : coeffOf (fun y => ρ y * r y) = mulCoeff (coeffOf ρ) (coeffOf r) :=
        coeffOf_mul ρ r (MFProduct.memLp_two_real hρc) (MFProduct.memLp_two_real hrc)
      have hρr : MemHs (n : ℝ) (coeffOf (fun y => ρ y * r y)) := by
        rw [hmul]; exact (hC _ _ (hρH (n + d)) ih).1
      have hGH : MemHs ((n : ℝ) + ((d : ℝ) - s)) (coeffOf G) :=
        memHs_convFun hsd F (hρc.mul hrc) (n : ℝ) hρr
      have hGH' : MemHs ((n + 1 : ℕ) : ℝ) (coeffOf G) := by
        refine hGH.mono ?_
        push_cast; linarith
      have := memHs_lincomb hφc hGc (hφH (n + 1)) hGH' 1 (-β) c
      rw [hrG]
      exact this
  have hr' : IsRealCoeff (coeffOf r) :=
    isRealCoeff_coeffOf r (hrc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hsum : Summable fun k => ‖coeffOf r k‖ :=
    summable_norm_of_memHs ((d + 1 : ℕ) : ℝ)
      (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) _ (hind (d + 1))
  have := isSmooth_toFun_of_decay (coeffOf r) hr' hind
  rwa [toFun_coeffOf hrc hsum] at this

end HRS.Q66

end
