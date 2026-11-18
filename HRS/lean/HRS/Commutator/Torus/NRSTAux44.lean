import HRS.Commutator.Torus.NRSTAux43
import HRS.Commutator.Whole.XNRSAux13

/-!
# NRS-T, part 44: the lifted vector field and the Fourier transform of `v·∇W`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_fourier_mod (F : 𝔼 → ℂ) (a ζ : 𝔼) :
    𝓕 (fun x : 𝔼 => leibt_e a x * F x) ζ = 𝓕 F (ζ - a) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  unfold leibt_e
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [inner_sub_right, real_inner_comm a x]
  push_cast
  ring

/-- The lift of the vector field `vOf V` to `ℝ^d`. -/
def nrstr_v (V : Fin d → NRST.TPA d) (y : 𝔼) : 𝔼 := WithLp.toLp 2 fun c => (nrstr_u (V c) y).re

lemma nrstr_v_apply (V : Fin d → NRST.TPA d) (y : 𝔼) (c : Fin d) :
    nrstr_v V y c = (nrstr_u (V c) y).re := rfl

lemma nrstr_v_xtvf (V : Fin d → NRST.TPA d) : HRS.Commutator.Whole.XNRS.XTVF (nrstr_v V) := fun c =>
  (Complex.reCLM.hasTemperateGrowth).comp (nrstr_u_temperate (V c))

lemma nrstr_v_xlip (V : Fin d → NRST.TPA d) {L : ℝ} (hL0 : 0 ≤ L) (hLip : IsLipschitzVF L (NRST.vOf V)) :
    HRS.Commutator.Whole.XNRS.XLip (nrstr_v V) L := fun x y =>
  (hLip (Torus.mk x) (Torus.mk y)).trans
    (mul_le_mul_of_nonneg_left (NRST.tdist_mk_le x y) hL0)

/-- The modulated derivative `e_j ∂_c W` as a Schwartz function. -/
def nrstr_g (j : Lattice d) (c : Fin d) (W : SchwartzMap 𝔼 ℂ) : SchwartzMap 𝔼 ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : 𝔼 => leibt_e (Lattice.toEuc j) x) (HRS.Commutator.Whole.XNRS.xdr c W)

lemma nrstr_g_apply (j : Lattice d) (c : Fin d) (W : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    nrstr_g j c W x = leibt_e (Lattice.toEuc j) x * HRS.Commutator.Whole.XNRS.xdr c W x := by
  unfold nrstr_g
  rw [SchwartzMap.smulLeftCLM_apply_apply (nrstr_e_temperate _), smul_eq_mul]

lemma nrstr_xadv_eq (V : Fin d → NRST.TPA d) (hVr : ∀ j x, (NRST.ev (V j) x).im = 0)
    (W : SchwartzMap 𝔼 ℂ) :
    HRS.Commutator.Whole.XNRS.xadv (nrstr_v V) W =
      ∑ c, ∑ j ∈ (V c).coeff.support, (V c).coeff j • nrstr_g j c W := by
  ext x
  rw [HRS.Commutator.Whole.XNRS.xadv_apply (nrstr_v_xtvf V) W x, SchwartzMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [SchwartzMap.sum_apply]
  have hre : (((nrstr_v V x c : ℝ)) : ℂ) = ∑ j ∈ (V c).coeff.support, (V c).coeff j * leibt_e (Lattice.toEuc j) x := by
    rw [nrstr_v_apply, ← nrstr_u_eq]
    exact NRST.ev_re_cast (V c) (hVr c) _
  rw [hre, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [SchwartzMap.smul_apply, nrstr_g_apply, smul_eq_mul]
  ring

lemma nrstr_fourier_xadv (V : Fin d → NRST.TPA d) (hVr : ∀ j x, (NRST.ev (V j) x).im = 0)
    (W : SchwartzMap 𝔼 ℂ) (ζ : 𝔼) :
    𝓕 (⇑(HRS.Commutator.Whole.XNRS.xadv (nrstr_v V) W)) ζ =
      ∑ c, ∑ j ∈ (V c).coeff.support, (V c).coeff j *
        ((2 * Real.pi * Complex.I * ((ζ - Lattice.toEuc j) c : ℝ)) * 𝓕 (⇑W) (ζ - Lattice.toEuc j)) := by
  have h1 : 𝓕 (⇑(HRS.Commutator.Whole.XNRS.xadv (nrstr_v V) W)) ζ =
      (𝓕 (HRS.Commutator.Whole.XNRS.xadv (nrstr_v V) W) : SchwartzMap 𝔼 ℂ) ζ := by
    rw [SchwartzMap.fourier_coe]
  rw [h1, nrstr_xadv_eq V hVr W, ← SchwartzMap.fourierTransformCLM_apply ℂ]
  simp only [map_sum, map_smul, SchwartzMap.fourierTransformCLM_apply, SchwartzMap.sum_apply,
    SchwartzMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [SchwartzMap.fourier_coe]
  have : (⇑(nrstr_g j c W)) = fun x => leibt_e (Lattice.toEuc j) x * HRS.Commutator.Whole.XNRS.xdr c W x :=
    funext (nrstr_g_apply j c W)
  rw [this, nrstr_fourier_mod]
  exact HRS.Commutator.Whole.XNRS.fourier_xdr c W _

end HRS.Commutator.TorusNote
