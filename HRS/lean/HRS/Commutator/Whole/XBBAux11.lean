import HRS.Commutator.Whole.XBBAux10

/-!
# Packet XBB, part 11: Schwartz approximants of `w_c ∈ L^p` and the convolution error bound
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Schwartz approximants of an `L^p` function -/
lemma xbb_approx_wc {f : 𝔼 → ℂ} {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∃ wk : ℕ → 𝓢(𝔼, ℂ), ∀ k : ℕ,
      eLpNorm (fun z => f z - wk k z) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have h : ∀ k : ℕ, ∃ (s : 𝓢(𝔼, ℂ)), eLpNorm (fun z => f z - s z) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro k
    obtain ⟨g, hgc, hgs, hg⟩ := hf.exist_eLpNorm_sub_le ENNReal.ofReal_ne_top hp1
      (ε := 1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨hgc.toSchwartzMap hgs, hg⟩
  choose s hs using h
  exact ⟨s, hs⟩

lemma xbb_wk_norm {f : 𝔼 → ℂ} {p F : ℝ} (hp : 1 < p) (hfF : eLpNorm f (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F)
    (s : 𝓢(𝔼, ℂ)) {δ : ℝ} (hs : eLpNorm (fun z => f z - s z) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal δ) :
    eLpNorm (⇑s) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F + ENNReal.ofReal δ := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have e : (⇑s : 𝔼 → ℂ) = f - fun z => f z - s z := by funext z; simp
  rw [e]
  exact (eLpNorm_sub_le hp1).trans (add_le_add hfF hs)


lemma xbb_cv_eq_int (K u : 𝔼 → ℂ) (x : 𝔼) : cv K u x = ∫ z, K (x - z) * u z := by
  rw [cv_apply]
  have := integral_sub_left_eq_self (fun z : 𝔼 => K (x - z) * u z) volume x
  simpa using this

lemma xbb_integrable_cv_Lp {Φ : 𝓢(𝔼, ℂ)} {h : 𝔼 → ℂ} (hm : Measurable h) {p : ℝ} (hp : 1 < p)
    (hh : MemLp h (ENNReal.ofReal p) volume) (x : 𝔼) : Integrable (fun y => Φ y * h (x - y)) := by
  have hconj : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have hq0 : 0 < p.conjExponent := hconj.symm.pos
  have hΦq : MemLp (⇑Φ) (ENNReal.ofReal p.conjExponent) volume := Φ.memLp _
  have hhx : MemLp (fun y : 𝔼 => h (x - y)) (ENNReal.ofReal p) volume :=
    hh.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hHC : (ENNReal.ofReal p.conjExponent).HolderConjugate (ENNReal.ofReal p) :=
    Real.HolderConjugate.ennrealOfReal hconj.symm
  exact MemLp.integrable_mul hΦq hhx


lemma xbb_norm_le_of_enorm_le {z : ℂ} {X : ℝ≥0∞} (hX : X ≠ ⊤) (h : ‖z‖ₑ ≤ X) : ‖z‖ ≤ X.toReal := by
  rw [← ofReal_norm] at h
  exact (ENNReal.ofReal_le_iff_le_toReal hX).1 h

/-- one approximant: `g_k = Φ ⋆ w_k` is within `‖Φ‖_{q} ‖w_c - w_k‖_p` of `Φ ⋆ w_c` -/
lemma xbb_cv_approx_bound {Φ : 𝓢(𝔼, ℂ)} {f : 𝔼 → ℂ} {p : ℝ} (hp : 1 < p) (hfm : Measurable f)
    (hf : MemLp f (ENNReal.ofReal p) volume) (s : 𝓢(𝔼, ℂ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : eLpNorm (fun z => f z - s z) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal δ) (x : 𝔼) :
    ‖cv ⇑Φ ⇑s x - cv ⇑Φ f x‖ ≤
      (eLpNorm (⇑Φ) (ENNReal.ofReal p.conjExponent) volume).toReal * δ := by
  have hconj : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have hsL : MemLp (⇑s) (ENNReal.ofReal p) volume := s.memLp _
  have hI1 := xbb_integrable_cv_Lp (Φ := Φ) hfm hp hf x
  have hI2 := xbb_integrable_cv_Lp (Φ := Φ) s.continuous.measurable hp hsL x
  have hdiff : cv ⇑Φ ⇑s x - cv ⇑Φ f x = -cv ⇑Φ (fun z => f z - s z) x := by
    simp only [cv_apply]
    rw [← integral_sub hI2 hI1, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  rw [hdiff, norm_neg]
  have hΦtop : eLpNorm (⇑Φ) (ENNReal.ofReal p.conjExponent) volume ≠ ⊤ := (Φ.memLp _).eLpNorm_ne_top
  have h1 := xbb_cv_holder (Φ := ⇑Φ) (h := fun z => f z - s z) Φ.continuous.measurable
    (hfm.sub s.continuous.measurable) hconj x
  have h2 : ‖cv ⇑Φ (fun z => f z - s z) x‖ₑ ≤
      eLpNorm (⇑Φ) (ENNReal.ofReal p.conjExponent) volume * ENNReal.ofReal δ :=
    h1.trans (by gcongr)
  have h3 := xbb_norm_le_of_enorm_le (ENNReal.mul_ne_top hΦtop ENNReal.ofReal_ne_top) h2
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ] at h3

end HRS.Commutator.Whole.XBB
