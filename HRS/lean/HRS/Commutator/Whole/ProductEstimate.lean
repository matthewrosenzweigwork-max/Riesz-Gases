import HRS.Commutator.Whole.PRODAux10

/-!
# CMX-PROD: the product estimate `(3.product)` (`[N] L501-512`)

`product_estimate_aesm` is `Local.product_estimate` with the one extra hypothesis that `u` is a.e.
strongly measurable.  Without it the statement of `Local.product_estimate` is false: `FourierSuppIn`
is vacuous for a non-measurable `u` (the Bochner integral of a non-integrable function is `0`), while
the conclusion `MemLp (v_{>1}·u) 2` needs measurability of `v_{>1}·u`.

Proof: Li's fractional Leibniz rule (`li_leibniz`) for Schwartz functions, extended by the density
argument of `PRODAux1`-`PRODAux9` (Schwartz approximants `g_n → f`, `⟨∇⟩^α g_n → ⟨∇⟩^α f` in `L^p`
via the mollifier and the correlation identity `(⟨∇⟩^α K) ⋆ f = K ⋆ ⟨∇⟩^α f`; Plancherel and Fatou
for the `H^α` norm of the `L²` limit), and Lemma 3.2 (`vhi_Lp`, `vhi_bounded`) for `v_{>1}`; the
band-limited `u` is handled by `FourierSuppIn` with a Schwartz kernel `K`, `K̂ = 1` on `B(0,3)`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

open HRS HRS.Whole HRS.Commutator.Whole.PROD

variable {d : ℕ} {s : ℝ}

theorem product_estimate_aesm (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (L : ℝ≥0) (w : Euc d → Euc d) (F : ℝ),
      HasFracData d s v L w F → ∀ u : Euc d → Euc d, AEStronglyMeasurable u volume →
      MemLp (fun x => ‖u x‖) (ENNReal.ofReal (p2E d s)) volume →
      (∀ i, FourierSuppIn 2 (fun x => u x i)) →
        MemLp (fun x => inner ℝ (Pgt 1 v x) (u x)) 2 volume ∧
        (sobSqE (alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 (fun x => inner ℝ (Pgt 1 v x) (u x)))) ^
            ((1 : ℝ) / 2) ≤
          ENNReal.ofReal (C * F) *
            eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (p2E d s)) volume := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hα1, hαd, hα0, hp1, hαp⟩ := SAMP1.exponents hd hs0 hsd
  have hq1 : 1 < p2E d s := prod_p2_gt_one hd hsd hs0
  have hpq := prod_exponent_identity hd hsd hs0
  obtain ⟨C₁, hC₁, hmain⟩ := prod_main_limit hd1 hp1 hq1 hpq hα0
  obtain ⟨CV, hCV, hV⟩ := vhi_Lp hd hs0 hsd
  obtain ⟨Cb, hCb, hbd⟩ := vhi_bounded (d := d) hd
  obtain ⟨K, hK⟩ := exists_kernel_fourier_one (d := d) (2 + 1) (by norm_num)
  set cK : ℝ := ∫ t, ‖prod_J (alphaE d s) K t‖ with hcK
  have hcK0 : 0 ≤ cK := integral_nonneg fun t => norm_nonneg _
  refine ⟨C₁ * d * (1 + cK) * CV, by positivity, ?_⟩
  intro v L w F hF u hum hmem hsupp
  set α := alphaE d s with hα
  set P := ENNReal.ofReal (p1E d s) with hP
  set Q := ENNReal.ofReal (p2E d s) with hQ
  obtain ⟨W, hWrep, hWnorm⟩ := hV v L w F hF
  have hPc : Continuous (Pgt 1 v) := (hbd v L hF.lip).1
  have hP1' : 1 ≤ P := (ENNReal.one_lt_ofReal.2 hp1).le
  have hQ1' : 1 ≤ Q := (ENNReal.one_lt_ofReal.2 hq1).le
  set X : ℝ≥0∞ := ENNReal.ofReal (CV * F) with hX
  set Nu : ℝ≥0∞ := eLpNorm (fun x => ‖u x‖) Q volume with hNu
  have hPgtm : AEStronglyMeasurable (fun x => ‖Pgt 1 v x‖) volume := hPc.norm.aestronglyMeasurable
  have hPgtL : eLpNorm (fun x => ‖Pgt 1 v x‖) P volume ≤ X :=
    le_trans le_add_self hWnorm
  have hWL : eLpNorm (fun x => ‖W x‖) P volume ≤ X := le_trans le_self_add hWnorm
  have hXtop : X ≠ ⊤ := ENNReal.ofReal_ne_top
  -- measurability of the components of `W`
  have hWc : ∀ i, AEStronglyMeasurable (fun x => ((W x i : ℝ) : ℂ)) volume := fun i =>
    prod_aesm_of_integrable_mul fun φ => (hWrep i φ).2.1
  have hWm : AEStronglyMeasurable (fun x => ‖W x‖) volume := by
    have : AEStronglyMeasurable W volume := by
      have : AEMeasurable W volume :=
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
          (aemeasurable_pi_iff.2 fun i => by
            have := (hWc i).re.aemeasurable
            simpa using this)
      exact this.aestronglyMeasurable
    exact this.norm
  -- the components
  set fC : Fin d → Euc d → ℂ := fun i x => ((Pgt 1 v x i : ℝ) : ℂ) with hfC
  set aC : Fin d → Euc d → ℂ := fun i x => ((u x i : ℝ) : ℂ) with haC
  set Wc : Fin d → Euc d → ℂ := fun i x => ((W x i : ℝ) : ℂ) with hWc'
  set Ac : Fin d → Euc d → ℂ := fun i => prod_cor (prod_J α K) (aC i) with hAc
  have hcomp : ∀ (z : Euc d) (i : Fin d), ‖((z i : ℝ) : ℂ)‖ ≤ ‖z‖ := fun z i => by
    rw [Complex.norm_real]
    simpa using PiLp.norm_apply_le z i
  have hfm : ∀ i, AEStronglyMeasurable (fC i) volume := fun i =>
    (Complex.continuous_ofReal.comp ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp
      hPc)).aestronglyMeasurable
  have hamC : ∀ i, AEStronglyMeasurable (aC i) volume := fun i =>
    (Complex.continuous_ofReal.comp
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous).comp_aestronglyMeasurable hum
  have hfL : ∀ i, eLpNorm (fC i) P volume ≤ X := fun i => by
    refine le_trans ?_ hPgtL
    refine eLpNorm_mono_ae (hfm i) (Filter.Eventually.of_forall fun x => ?_)
    exact (hcomp (Pgt 1 v x) i).trans_eq (norm_norm _).symm
  have hWL' : ∀ i, eLpNorm (Wc i) P volume ≤ X := fun i => by
    refine le_trans ?_ hWL
    refine eLpNorm_mono_ae (hWc i) (Filter.Eventually.of_forall fun x => ?_)
    exact (hcomp (W x) i).trans_eq (norm_norm _).symm
  have haL : ∀ i, eLpNorm (aC i) Q volume ≤ Nu := fun i => by
    refine eLpNorm_mono_ae (hamC i) (Filter.Eventually.of_forall fun x => ?_)
    exact (hcomp (u x) i).trans_eq (norm_norm _).symm
  have hAL : ∀ i, eLpNorm (Ac i) Q volume ≤ ENNReal.ofReal cK * Nu := fun i => by
    refine (prod_eLpNorm_cor_le hq1 (prod_J α K).integrable (hamC i)).trans ?_
    gcongr
    exact haL i
  have hNutop : Nu ≠ ⊤ := hmem.eLpNorm_lt_top.ne
  -- memberships
  have hfmem : ∀ i, MemLp (fC i) P volume := fun i =>
    lt_of_le_of_lt (hfL i) ENNReal.ofReal_lt_top
  have hWmem : ∀ i, MemLp (Wc i) P volume := fun i =>
    lt_of_le_of_lt (hWL' i) ENNReal.ofReal_lt_top
  have hamem : ∀ i, MemLp (aC i) Q volume := fun i =>
    lt_of_le_of_lt (haL i) (lt_top_iff_ne_top.2 hNutop)
  have hAmem : ∀ i, MemLp (Ac i) Q volume := fun i =>
    lt_of_le_of_lt (hAL i) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hNutop))
  -- Bessel representations
  have hbf : ∀ i, ProdBes α (fC i) (Wc i) := fun i φ => (hWrep i φ).2.2
  have hba : ∀ i, ProdBes α (aC i) (Ac i) := fun i =>
    prod_bandlimited_rep hq1 α (hamem i) K hK (hsupp i)
  obtain ⟨hL2, hbound⟩ := hmain (fun i x => Pgt 1 v x i) (fun i x => u x i) Wc Ac hfmem hamem
    hWmem hAmem hbf hba
  have hfun : (fun x => inner ℝ (Pgt 1 v x) (u x)) = fun x => ∑ i, Pgt 1 v x i * u x i := by
    funext x
    simp [PiLp.inner_apply, mul_comm]
  rw [hfun]
  refine ⟨hL2, hbound.trans ?_⟩
  -- the numerical bound
  have hsum : ∑ i : Fin d, (eLpNorm (Wc i) P volume * eLpNorm (aC i) Q volume +
      eLpNorm (Ac i) Q volume * eLpNorm (fC i) P volume) ≤
      ∑ i : Fin d, (X * Nu + (ENNReal.ofReal cK * Nu) * X) := by
    refine Finset.sum_le_sum fun i _ => ?_
    gcongr
    · exact hWL' i
    · exact haL i
    · exact hAL i
    · exact hfL i
  refine (mul_le_mul_right hsum _).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e1 : ENNReal.ofReal (C₁ * d * (1 + cK) * CV * F) =
      ENNReal.ofReal C₁ * (d : ℝ≥0∞) * (1 + ENNReal.ofReal cK) * ENNReal.ofReal CV *
        ENNReal.ofReal F := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_add (by norm_num) hcK0, ENNReal.ofReal_one]
  have e2 : X = ENNReal.ofReal CV * ENNReal.ofReal F := by
    rw [hX, ENNReal.ofReal_mul hCV.le]
  rw [e1, e2]
  ring

end HRS.Commutator.Whole

/-- `(3.product)`: the repaired frozen statement `product_estimate` (Local.lean) is exactly `product_estimate_aesm`. -/
example := (@HRS.Commutator.Whole.product_estimate_aesm : type_of% @HRS.Commutator.Whole.product_estimate)
