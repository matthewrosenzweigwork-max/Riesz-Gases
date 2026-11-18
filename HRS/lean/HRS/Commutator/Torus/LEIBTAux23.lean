import HRS.Commutator.Torus.LEIBTAux22

/-!
# LEIB-T helpers, part 23: two-sided `L^p` comparison for the Bessel derivative of a cut-off lift
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_bessel_upper (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (α : ℝ) (M : ℕ) {N N' : ℝ}
    (hN : N = ((M : ℝ) + 1 / 2) / η) (hN1 : 1 ≤ N)
    (hN' : N' = ((((2 * d * M + d : ℕ)) : ℝ) + 1 / 2) / η) {e : ℕ} (he : 1 ≤ e)
    (W : SchwartzMap 𝔼 ℂ) {G₀ : Torus d → ℝ} (hG₀ : Continuous G₀) {S : ℝ} (hS : 0 ≤ S) (K : ℕ)
    (hE : ∀ x : 𝔼, ‖HRS.Commutator.Whole.XLI.Fm α W x -
        ((G₀ (Torus.mk (η • x)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • x)‖ ≤
        S * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (HRS.Commutator.Whole.XLI.Fm α W) p volume ≤
      leibt_Lam d N' p * eLpNorm G₀ p volume +
        ENNReal.ofReal (S * N⁻¹) * (leibt_Lam d N p * eLpNorm (leibt_wt d K) p volume) := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; simp at hp
  set A : 𝔼 → ℂ := fun y => ((G₀ (Torus.mk (η • y)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • y) with hA
  set E : 𝔼 → ℂ := fun x => HRS.Commutator.Whole.XLI.Fm α W x - A x with hEdef
  have hsum : (HRS.Commutator.Whole.XLI.Fm α W : 𝔼 → ℂ) = A + E := by
    funext x; simp [hEdef]
  rw [hsum]
  refine (eLpNorm_add_le hp).trans ?_
  gcongr
  · exact leibt_cut_le hd hη M hN hN' he hG₀ hp0
  · exact leibt_err_norm_le hd α hN1 he W hG₀ hS K hE p

lemma leibt_bessel_lower (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (α : ℝ) (M : ℕ) {N : ℝ}
    (hN : N = ((M : ℝ) + 1 / 2) / η) (hN1 : 1 ≤ N) {e : ℕ} (he : 1 ≤ e)
    (W : SchwartzMap 𝔼 ℂ) {G₀ : Torus d → ℝ} (hG₀ : Continuous G₀) {S : ℝ} (hS : 0 ≤ S) (K : ℕ)
    (hE : ∀ x : 𝔼, ‖HRS.Commutator.Whole.XLI.Fm α W x -
        ((G₀ (Torus.mk (η • x)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • x)‖ ≤
        S * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    leibt_Lam d N p * eLpNorm G₀ p volume ≤
      eLpNorm (HRS.Commutator.Whole.XLI.Fm α W) p volume +
        ENNReal.ofReal (S * N⁻¹) * (leibt_Lam d N p * eLpNorm (leibt_wt d K) p volume) := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; simp at hp
  set A : 𝔼 → ℂ := fun y => ((G₀ (Torus.mk (η • y)) : ℝ) : ℂ) * leibt_chi hd he (N⁻¹ • y) with hA
  refine (leibt_cut_ge hd hη M hN he hG₀ hp0 hpt).trans ?_
  have hsub : A = (HRS.Commutator.Whole.XLI.Fm α W : 𝔼 → ℂ) -
      (fun x => HRS.Commutator.Whole.XLI.Fm α W x - A x) := by
    funext x; simp
  have h1 := eLpNorm_sub_le (f := (HRS.Commutator.Whole.XLI.Fm α W : 𝔼 → ℂ))
    (g := fun x => HRS.Commutator.Whole.XLI.Fm α W x - A x) (μ := volume) hp
  rw [← hsub] at h1
  refine h1.trans ?_
  gcongr
  exact leibt_err_norm_le hd α hN1 he W hG₀ hS K hE p

end HRS.Commutator.TorusNote
