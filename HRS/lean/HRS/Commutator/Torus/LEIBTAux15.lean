import HRS.Commutator.Torus.LEIBTAux14

/-!
# LEIB-T helpers, part 15: the Bessel derivative of a smooth function is represented by a continuous real function
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {g : Torus d → E}
    (hg : Continuous g) : Integrable g :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma leibt_fcoef_neg (f : Torus d → ℝ) (k : Lattice d) :
    Torus.fcoef f (-k) = conj (Torus.fcoef f k) := by
  unfold Torus.fcoef
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [neg_neg, map_mul, Torus.mode_neg, Complex.conj_conj, Complex.conj_ofReal]

lemma leibt_m_neg (α : ℝ) (ξ : 𝔼) : leibt_m α (-ξ) = leibt_m α ξ := by
  unfold leibt_m HRS.Commutator.Whole.XLI.bsymX
  rw [norm_neg]

lemma leibt_m_conj (α : ℝ) (ξ : 𝔼) : conj (leibt_m α ξ) = leibt_m α ξ := by
  unfold leibt_m HRS.Commutator.Whole.XLI.bsymX
  exact Complex.conj_ofReal _

lemma leibt_bc_neg (α η : ℝ) (f : Torus d → ℝ) (k : Lattice d) :
    leibt_bc α η f (-k) = conj (leibt_bc α η f k) := by
  unfold leibt_bc
  have : leibt_lam η (-k) = -leibt_lam η k := by
    unfold leibt_lam
    rw [Torus.toEuc_neg, smul_neg]
  rw [this, leibt_m_neg, map_mul, leibt_m_conj, leibt_fcoef_neg]

lemma leibt_Fc_real {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (α : ℝ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (x : Torus d) : (leibt_Fc α η f x).im = 0 := by
  have h0 := leibt_Fc_hasSum hη hη1 α hf x
  have h1 := h0.star
  have h2 : HasSum (fun k : Lattice d => leibt_bc α η f k * Torus.mode k x) (conj (leibt_Fc α η f x)) := by
    rw [← (Equiv.neg (Lattice d)).hasSum_iff]
    convert h1 using 1
    · funext k
      simp only [Function.comp, Equiv.neg_apply, leibt_bc_neg, Torus.mode_neg, star_mul', Complex.star_def]
    · rfl
  exact Complex.conj_eq_iff_im.1 (h2.unique h0)

end HRS.Commutator.TorusNote
