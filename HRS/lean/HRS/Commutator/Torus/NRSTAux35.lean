import HRS.Commutator.Torus.NRSTAux34
import HRS.Commutator.Torus.TEXTAux19
import HRS.Commutator.Torus.LEIBTAux27

/-!
# NRS-T, part 35: real parts of real trigonometric polynomials, Bessel representatives, `L^∞` bound
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

lemma nrstr_isRealT_mulSeq {mm : Lattice d → ℂ} (hmm : ∀ k, mm (-k) = (starRingEnd ℂ) (mm k))
    {f : NRST.TPA d} (hf : NRST.IsRealT f) : NRST.IsRealT (NRST.mulSeq mm f) := by
  intro k
  rw [NRST.coeff_mulSeq, NRST.coeff_mulSeq, hmm, hf k, map_mul]

lemma nrstr_isRealT_Jb (τ : ℝ) {f : NRST.TPA d} (hf : NRST.IsRealT f) : NRST.IsRealT (nrstr_Jb τ f) :=
  nrstr_isRealT_mulSeq (fun k => by rw [nrstr_jb_neg]; simp) hf

lemma nrstr_isRealT_lam (σ : ℝ) {f : NRST.TPA d} (hf : NRST.IsRealT f) : NRST.IsRealT (NRST.lam σ f) :=
  nrstr_isRealT_mulSeq (fun k => by rw [NRST.lw_neg]; simp) hf

lemma nrstr_ev_im {f : NRST.TPA d} (hf : NRST.IsRealT f) (x : Torus d) : (NRST.ev f x).im = 0 :=
  NRST.ev_real_of_symm f hf x

lemma nrstr_eLpNorm_re {f : NRST.TPA d} (hf : NRST.IsRealT f) (p : ℝ≥0∞) :
    eLpNorm (fun x => (NRST.ev f x).re) p volume = eLpNorm (NRST.ev f) p volume := by
  refine eLpNorm_congr_norm_ae
    ((Complex.continuous_re.comp (NRST.continuous_ev f)).aestronglyMeasurable)
    (NRST.continuous_ev f).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have h := NRST.ev_re_cast f (nrstr_ev_im hf) x
  conv_rhs => rw [← h]
  rw [Complex.norm_real]

lemma nrstr_fcoef_re {f : NRST.TPA d} (hf : NRST.IsRealT f) (k : Lattice d) :
    Torus.fcoef (fun x => (NRST.ev f x).re) k = f.coeff k := by
  rw [NRST.fcoef_eq_coeffOf]
  exact NRST.coeffOf_re_ev f (nrstr_ev_im hf) k

lemma nrstr_besselRep {f : NRST.TPA d} (hf : NRST.IsRealT f) (τ : ℝ) :
    IsBesselRepT 1 τ (fun x => (NRST.ev f x).re) (fun x => (NRST.ev (nrstr_Jb τ f) x).re) := by
  intro k
  rw [nrstr_fcoef_re hf, nrstr_fcoef_re (nrstr_isRealT_Jb τ hf)]
  unfold nrstr_Jb
  rw [NRST.coeff_mulSeq]
  unfold nrstr_jb
  simp

lemma nrstr_re_ev_mul {f g : NRST.TPA d} (hf : NRST.IsRealT f) (hg : NRST.IsRealT g) (x : Torus d) :
    (NRST.ev (f * g) x).re = (NRST.ev f x).re * (NRST.ev g x).re := by
  rw [NRST.ev_mul, Pi.mul_apply, Complex.mul_re, nrstr_ev_im hf, nrstr_ev_im hg]; ring

lemma nrstr_isRealT_mul {f g : NRST.TPA d} (hf : NRST.IsRealT f) (hg : NRST.IsRealT g) :
    NRST.IsRealT (f * g) := by
  intro k
  rw [← NRST.ev_coeff (f * g) (-k), ← NRST.ev_coeff (f * g) k, neg_neg]
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Torus.mode_neg]
  have h1 : (starRingEnd ℂ) (NRST.ev (f * g) x) = NRST.ev (f * g) x := by
    have := NRST.ev_mul_real f g (nrstr_ev_im hf) (nrstr_ev_im hg) x
    exact Complex.conj_eq_iff_im.2 this
  rw [h1, Complex.conj_conj]

lemma nrstr_isSmooth_re (f : NRST.TPA d) : Torus.IsSmooth (fun x => (NRST.ev f x).re) :=
  NRST.isCk_aOf f _

lemma nrstr_eLpNorm_top_re_le {f : NRST.TPA d} {L : ℝ} (hL : ∀ x, ‖NRST.ev f x‖ ≤ L) :
    eLpNorm (fun x => (NRST.ev f x).re) ⊤ volume ≤ ENNReal.ofReal L := by
  have hm : AEStronglyMeasurable (fun x => (NRST.ev f x).re) volume :=
    (Complex.continuous_re.comp (NRST.continuous_ev f)).aestronglyMeasurable
  rw [eLpNorm_exponent_top hm]
  refine eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun x => ?_)
  exact (Complex.abs_re_le_norm _).trans (hL x)

end HRS.Commutator.TorusNote
