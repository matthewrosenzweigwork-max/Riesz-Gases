import HRS.Commutator.Whole.PRODAux4

/-!
# CMX-PROD helper file 5: distributional Bessel identities and density of Schwartz functions
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.PROD

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

/-- `f` has the Bessel derivative `W` in the sense of distributions (complex version). -/
def ProdBes (α : ℝ) (f W : Euc d → ℂ) : Prop :=
  ∀ φ : SchwartzMap (Euc d) ℂ, ∫ x, f x * besselS α φ x = ∫ x, W x * φ x

lemma prod_cor_eq_conv_neg (K h : Euc d → ℂ) :
    prod_cor K h = prod_conv (fun t => K (-t)) h := by
  funext y
  unfold prod_cor prod_conv
  rw [← integral_neg_eq_self (fun t => K t * h (y + t)) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [sub_eq_add_neg]

lemma prod_eLpNorm_cor_le {p : ℝ} (hp : 1 < p) {K h : Euc d → ℂ} (hK : Integrable K)
    (hh : AEStronglyMeasurable h volume) :
    eLpNorm (prod_cor K h) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (∫ t, ‖K t‖) * eLpNorm h (ENNReal.ofReal p) volume := by
  rw [prod_cor_eq_conv_neg]
  have := prod_eLpNorm_conv_le hp (K := fun t => K (-t)) hK.comp_neg hh
  have e : ∫ t, ‖K (-t)‖ = ∫ t, ‖K t‖ := integral_neg_eq_self (fun t => ‖K t‖) volume
  rwa [e] at this

/-- Pointwise bound of the correlation of an `L^p` function with a Schwartz kernel. -/
lemma prod_cor_bound (K : SchwartzMap (Euc d) ℂ) {p : ℝ} (hp : 1 < p) {h : Euc d → ℂ}
    (hh : MemLp h (ENNReal.ofReal p) volume) : ∃ M : ℝ, ∀ y, ‖prod_cor K h y‖ ≤ M := by
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  haveI hH : (ENNReal.ofReal p).HolderConjugate (ENNReal.conjExponent (ENNReal.ofReal p)) :=
    ENNReal.HolderConjugate.conjExponent hP1
  have hMtop : eLpNorm h (ENNReal.ofReal p) volume *
      eLpNorm K (ENNReal.conjExponent (ENNReal.ofReal p)) volume ≠ ⊤ :=
    (ENNReal.mul_lt_top hh.eLpNorm_lt_top (K.memLp _).eLpNorm_lt_top).ne
  refine ⟨(eLpNorm h (ENNReal.ofReal p) volume *
      eLpNorm K (ENNReal.conjExponent (ENNReal.ofReal p)) volume).toReal, fun y => ?_⟩
  have hy := enorm_conv_le (p' := ENNReal.conjExponent (ENNReal.ofReal p)) hh K y
  rw [← ofReal_norm] at hy
  exact (ENNReal.ofReal_le_iff_le_toReal hMtop).1 hy

/-- A.e. equality from pairing with all Schwartz functions (bounded functions). -/
lemma prod_ae_eq_of_test {F G : Euc d → ℂ} (hFm : AEStronglyMeasurable F volume)
    (hGm : AEStronglyMeasurable G volume) {M : ℝ} (hFb : ∀ x, ‖F x‖ ≤ M) (hGb : ∀ x, ‖G x‖ ≤ M)
    (h : ∀ ψ : SchwartzMap (Euc d) ℂ, ∫ x, ψ x * F x = ∫ x, ψ x * G x) : F =ᵐ[volume] G := by
  have hHm : AEStronglyMeasurable (fun x => F x - G x) volume := hFm.sub hGm
  have hHb : ∀ x, ‖F x - G x‖ ≤ M + M := fun x => (norm_sub_le _ _).trans (add_le_add (hFb x) (hGb x))
  have hHloc : LocallyIntegrable (fun x => F x - G x) volume :=
    (memLp_top_of_bound hHm _ (Filter.Eventually.of_forall hHb)).locallyIntegrable le_top
  have hzero : ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (F x - G x) = 0 := by
    intro g hg hgc
    have hgc' : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) :=
      hgc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    have hsm : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    let ψ : SchwartzMap (Euc d) ℂ := hgc'.toSchwartzMap hsm
    have hψ : ∀ x, ψ x = ((g x : ℝ) : ℂ) := fun x => rfl
    have hI1 : Integrable (fun x => ψ x * F x) :=
      (ψ.integrable).mul_bdd hFm (Filter.Eventually.of_forall hFb)
    have hI2 : Integrable (fun x => ψ x * G x) :=
      (ψ.integrable).mul_bdd hGm (Filter.Eventually.of_forall hGb)
    have e1 : ∫ x, g x • (F x - G x) = (∫ x, ψ x * F x) - ∫ x, ψ x * G x := by
      rw [← integral_sub hI1 hI2]
      congr 1
      ext x
      rw [Complex.real_smul, hψ]
      ring
    rw [e1, h ψ, sub_self]
  have hF := ae_eq_zero_of_integral_contDiff_smul_eq_zero hHloc hzero
  filter_upwards [hF] with y hy
  exact sub_eq_zero.1 hy

/-- The key identity: `(J K) ⋆ f = K ⋆ W` for `f` with Bessel derivative `W`. -/
theorem prod_cor_identity {p : ℝ} (hp : 1 < p) {α : ℝ} {f W : Euc d → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hW : MemLp W (ENNReal.ofReal p) volume)
    (hrep : ProdBes α f W) (K : SchwartzMap (Euc d) ℂ) :
    prod_cor (prod_J α K) f =ᵐ[volume] prod_cor K W := by
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  haveI hH : (ENNReal.ofReal p).HolderConjugate (ENNReal.conjExponent (ENNReal.ofReal p)) :=
    ENNReal.HolderConjugate.conjExponent hP1
  obtain ⟨M₁, hM₁⟩ := prod_cor_bound (prod_J α K) hp hf
  obtain ⟨M₂, hM₂⟩ := prod_cor_bound K hp hW
  refine prod_ae_eq_of_test (prod_aesm_cor (prod_J α K).continuous.aestronglyMeasurable
    hf.aestronglyMeasurable) (prod_aesm_cor K.continuous.aestronglyMeasurable
    hW.aestronglyMeasurable) (M := max M₁ M₂) (fun x => (hM₁ x).trans (le_max_left _ _))
    (fun x => (hM₂ x).trans (le_max_right _ _)) fun ψ => ?_
  have p1 := pairing_identity (p' := ENNReal.conjExponent (ENNReal.ofReal p)) hf (prod_J α K) ψ
  have p2 := pairing_identity (p' := ENNReal.conjExponent (ENNReal.ofReal p)) hW K ψ
  have e1 : ∫ x, f x * (∫ t, prod_J α K t * ψ (x - t)) =
      ∫ x, f x * besselS α (prod_sconv K ψ) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [prod_besselS_eq, prod_J_sconv, prod_sconv_apply]
    rfl
  have e2 := hrep (prod_sconv K ψ)
  have e3 : ∫ x, W x * (prod_sconv K ψ) x = ∫ x, W x * (∫ t, K t * ψ (x - t)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [prod_sconv_apply]
    rfl
  have : ∫ y, ψ y * prod_cor (prod_J α K) f y = ∫ y, ψ y * prod_cor K W y := by
    unfold prod_cor
    rw [← p1, e1, e2, e3, p2]
  exact this

/-- A band-limited `L^p` function has a Bessel derivative given by a Schwartz correlation. -/
theorem prod_bandlimited_rep {p : ℝ} (hp : 1 < p) (α : ℝ) {a : Euc d → ℂ}
    (ha : MemLp a (ENNReal.ofReal p) volume) (K : SchwartzMap (Euc d) ℂ)
    (hK : ∀ ξ : Euc d, ‖ξ‖ < 2 + 1 → 𝓕 (⇑K) ξ = 1)
    (hsupp : ∀ G : SchwartzMap (Euc d) ℂ,
      Disjoint (tsupport (𝓕 (⇑G))) (closedBall (0 : Euc d) 2) → ∫ x, a x * G x = 0) :
    ProdBes α a (prod_cor (prod_J α K) a) := by
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  haveI hH : (ENNReal.ofReal p).HolderConjugate (ENNReal.conjExponent (ENNReal.ofReal p)) :=
    ENNReal.HolderConjugate.conjExponent hP1
  intro φ
  have h1 := fourier_supp_test (p' := ENNReal.conjExponent (ENNReal.ofReal p)) (R := 2) K hK ha
    hsupp (prod_J α φ)
  have p1 := pairing_identity (p' := ENNReal.conjExponent (ENNReal.ofReal p)) ha (prod_J α K) φ
  have hx : ∀ x, (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K (prod_J α φ)) x =
      ∫ t, prod_J α K t * φ (x - t) := fun x => by
    have := congrArg (fun F : SchwartzMap (Euc d) ℂ => F x) (prod_sconv_J α K φ)
    rw [show (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K (prod_J α φ)) x =
      prod_sconv K (prod_J α φ) x from rfl, this, prod_sconv_apply]
    rfl
  rw [prod_besselS_eq, h1]
  simp_rw [hx]
  rw [p1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [prod_cor]
  ring

/-- Density of Schwartz functions in `L^p`. -/
lemma prod_schwartz_dense {p : ℝ} (hp : 1 < p) {f : Euc d → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : SchwartzMap (Euc d) ℂ, eLpNorm (fun x => s x - f x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ε := by
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨hP1⟩
  have hd := SchwartzMap.denseRange_toLpCLM (E := Euc d) (F := ℂ) (p := ENNReal.ofReal p)
    ENNReal.ofReal_ne_top (μ := (volume : Measure (Euc d)))
  obtain ⟨s, hs⟩ := (Metric.denseRange_iff.1 hd) (hf.toLp f) ε hε
  refine ⟨s, ?_⟩
  set S : Lp ℂ (ENNReal.ofReal p) volume := s.toLp (ENNReal.ofReal p) volume with hS
  have hs' : dist (hf.toLp f) S < ε := by simpa [SchwartzMap.toLpCLM_apply] using hs
  have hn : ‖hf.toLp f - S‖ < ε := by
    rw [← dist_eq_norm]; exact hs'
  rw [Lp.norm_def] at hn
  have hae : (fun x => s x - f x) =ᵐ[volume] ⇑S - ⇑(hf.toLp f) := by
    filter_upwards [SchwartzMap.coeFn_toLp s (ENNReal.ofReal p) (volume : Measure (Euc d)),
      MemLp.coeFn_toLp hf] with x h1 h2
    simp only [Pi.sub_apply]
    rw [h1, h2]
  have hae2 : eLpNorm (fun x => s x - f x) (ENNReal.ofReal p) volume =
      eLpNorm ⇑(hf.toLp f - S) (ENNReal.ofReal p) volume := by
    rw [eLpNorm_congr_ae hae, eLpNorm_sub_comm]
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (hf.toLp f) S] with x hx
    rw [hx]
  rw [hae2]
  have hfin := Lp.eLpNorm_lt_top (hf.toLp f - S)
  rw [← ENNReal.ofReal_toReal hfin.ne]
  exact ENNReal.ofReal_le_ofReal hn.le

end HRS.Commutator.Whole.PROD
