import HRS.Commutator.Torus.LEIBTAux16

/-!
# LEIB-T helpers, part 17: cut-offs, and the pointwise estimate for one function
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The lift of a torus function at scale `η`, as a complex function on `ℝ^d`. -/
def leibt_u (η : ℝ) (f : Torus d → ℝ) (y : 𝔼) : ℂ := ((f (Torus.mk (η • y)) : ℝ) : ℂ)

lemma leibt_u_contDiff {η : ℝ} {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ContDiff ℝ ∞ (leibt_u η f) := by
  have h1 : ContDiff ℝ ∞ (Torus.lift f) := hf
  have h2 : ContDiff ℝ ∞ (fun y : 𝔼 => Torus.lift f (η • y)) := h1.comp (contDiff_const_smul η)
  exact Complex.ofRealCLM.contDiff.comp h2

lemma leibt_exists_cut {η : ℝ} {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (χ : SchwartzMap 𝔼 ℂ)
    (hχc : HasCompactSupport (⇑χ)) {N : ℝ} (hN : 0 < N) :
    ∃ W : SchwartzMap 𝔼 ℂ, ∀ y, W y = leibt_u η f y * χ (N⁻¹ • y) := by
  have hsm : ContDiff ℝ ∞ (fun y : 𝔼 => leibt_u η f y * χ (N⁻¹ • y)) :=
    (leibt_u_contDiff hf).mul ((χ.smooth (⊤ : ℕ∞)).comp (contDiff_const_smul N⁻¹))
  have hcs : HasCompactSupport (fun y : 𝔼 => leibt_u η f y * χ (N⁻¹ • y)) := by
    have := (hχc.comp_smul (inv_ne_zero hN.ne')).mul_left (f := leibt_u η f)
    exact this
  exact ⟨hcs.toSchwartzMap hsm, fun y => rfl⟩

theorem leibt_one_fn (α : ℝ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (χ : SchwartzMap 𝔼 ℂ)
    (hχc : HasCompactSupport (⇑χ)) (K : ℕ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ N : ℝ, 1 ≤ N → ∃ W : SchwartzMap 𝔼 ℂ,
      (∀ y, W y = leibt_u η f y * χ (N⁻¹ • y)) ∧
      ∀ x : 𝔼, ‖HRS.Commutator.Whole.XLI.Fm α W x -
          ((leibt_F0 α η f (Torus.mk (η • x)) : ℝ) : ℂ) * χ (N⁻¹ • x)‖ ≤
        S * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹ := by
  obtain ⟨C, k, hC, herr⟩ := leibt_error_bound (d := d) α χ K
  have hc : ∀ p : ℕ, Summable fun i : Lattice d => ‖Torus.fcoef f i‖ * (1 + ‖leibt_lam η i‖) ^ p :=
    fun p => leibt_coef_summable hη hη1 hf p
  refine ⟨C * ∑' i : Lattice d, ‖Torus.fcoef f i‖ * (1 + ‖leibt_lam η i‖) ^ k,
    mul_nonneg hC (tsum_nonneg fun i => by positivity), fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  obtain ⟨W, hW⟩ := leibt_exists_cut (η := η) hf χ hχc hN0
  refine ⟨W, hW, fun x => ?_⟩
  have hG : ∀ y : 𝔼, HasSum (fun i : Lattice d => Torus.fcoef f i * leibt_m α (leibt_lam η i) *
      leibt_e (leibt_lam η i) y) (((leibt_F0 α η f (Torus.mk (η • y)) : ℝ) : ℂ)) := by
    intro y
    rw [leibt_F0_cast hη hη1 α hf]
    have := leibt_Fc_hasSum hη hη1 α hf (Torus.mk (η • y))
    convert this using 1
    funext i
    simp only [leibt_bc, leibt_mode_eq]
    ring
  have hW' : ∀ y : 𝔼, HasSum (fun i : Lattice d => Torus.fcoef f i *
      (leibt_e (leibt_lam η i) y * χ (N⁻¹ • y))) ((W : 𝔼 → ℂ) y) := by
    intro y
    rw [hW y]
    have := (leibt_f_series hη hη1 hf y).mul_right (χ (N⁻¹ • y))
    have e : ∀ i : Lattice d, Torus.fcoef f i * (leibt_e (leibt_lam η i) y * χ (N⁻¹ • y)) =
        Torus.fcoef f i * leibt_e (leibt_lam η i) y * χ (N⁻¹ • y) := fun i => by ring
    simp_rw [e]
    exact this
  have := herr (fun i => Torus.fcoef f i) (leibt_lam η) hc
    (fun y => ((leibt_F0 α η f (Torus.mk (η • y)) : ℝ) : ℂ)) (⇑W) W rfl hG hN hW' x
  simpa [mul_assoc, mul_comm, mul_left_comm] using this

end HRS.Commutator.TorusNote
