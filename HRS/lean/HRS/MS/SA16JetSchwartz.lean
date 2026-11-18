import HRS.MS.SA16JetConvDiff

/-!
# S.A.16: bridges between operator norms of iterated derivatives and coordinate jets
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section Bridge
variable {d : ℕ}

lemma sa16j_ml {j : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ) :
    ‖L‖ ≤ ∑ r : Fin j → Fin d, |L (fun l => EuclideanSpace.single (r l) (1 : ℝ))| := by
  classical
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) (fun m => ?_)
  have hm : m = fun l => ∑ i : Fin d, (m l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    funext l
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : L m = ∑ r : Fin j → Fin d,
      L (fun l => (m l (r l)) • (EuclideanSpace.single (r l) (1 : ℝ) : Euc d)) := by
    conv_lhs => rw [hm]
    exact L.map_sum (fun l i => (m l i) • (EuclideanSpace.single i (1 : ℝ) : Euc d))
  have h2 : ∀ r : Fin j → Fin d,
      ‖L (fun l => (m l (r l)) • (EuclideanSpace.single (r l) (1 : ℝ) : Euc d))‖
      ≤ |L (fun l => EuclideanSpace.single (r l) (1 : ℝ))| * ∏ l, ‖m l‖ := by
    intro r
    rw [L.map_smul_univ, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod]
    have : ∏ l, |m l (r l)| ≤ ∏ l, ‖m l‖ :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun l _ => by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (m l) (r l))
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  rw [h1]
  calc ‖∑ r : Fin j → Fin d, L (fun l => (m l (r l)) • (EuclideanSpace.single (r l) (1 : ℝ) : Euc d))‖
      ≤ ∑ r : Fin j → Fin d, ‖L (fun l => (m l (r l)) • (EuclideanSpace.single (r l) (1 : ℝ) : Euc d))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r : Fin j → Fin d, |L (fun l => EuclideanSpace.single (r l) (1 : ℝ))| * ∏ l, ‖m l‖ :=
        Finset.sum_le_sum fun r _ => h2 r
    _ = (∑ r : Fin j → Fin d, |L (fun l => EuclideanSpace.single (r l) (1 : ℝ))|) * ∏ l, ‖m l‖ := by
        rw [Finset.sum_mul]

open LineDeriv in
/-- coordinate derivatives of a Schwartz function are Schwartz -/
lemma sa16j_pd_schwartz (u : 𝓢(Euc d, ℝ)) {j : ℕ} (idx : Fin j → Fin d) :
    partialDeriv idx (⇑u) =
      ⇑(∂^{fun l => (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)} u) := by
  funext x
  unfold partialDeriv
  exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv.symm

lemma sa16j_norm_iter_le (g : Euc d → ℝ) (x : Euc d) (j : ℕ) :
    ‖iteratedFDeriv ℝ j g x‖ ≤ ∑ r : Fin j → Fin d, |partialDeriv r g x| :=
  sa16j_ml (iteratedFDeriv ℝ j g x)

lemma sa16j_S_le (m : ℕ) (g : Euc d → ℝ) (x : Euc d) :
    sa16j_S d m g x ≤ ∑ j ∈ Finset.range (m + 1), ∑ r : Fin j → Fin d, |partialDeriv r g x| :=
  Finset.sum_le_sum fun j _ => sa16j_norm_iter_le g x j

lemma sa16j_pd_le_jet (m : ℕ) (g : Euc d → ℝ) (x : Euc d) {j : ℕ} (hj : j ≤ m)
    (r : Fin j → Fin d) : |partialDeriv r g x| ≤ ‖wJet m g x‖ := by
  have := norm_le_pi_norm (wJet m g x) (⟨⟨j, by omega⟩, r⟩ : WIndex d m)
  simpa [wJet, Real.norm_eq_abs] using this

/-- the derivative of a coordinate derivative is bounded by the next iterated derivative -/
lemma sa16j_fderiv_pd_le {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) {j : ℕ} (idx : Fin j → Fin d)
    (x : Euc d) : ‖fderiv ℝ (partialDeriv idx g) x‖ ≤ ‖iteratedFDeriv ℝ (j + 1) g x‖ := by
  have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ j g) x :=
    (hg.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast WithTop.coe_lt_top _)) x
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
  have h1 : fderiv ℝ (partialDeriv idx g) x w =
      iteratedFDeriv ℝ (j + 1) g x (Fin.cons w (fun l => EuclideanSpace.single (idx l) (1 : ℝ))) := by
    unfold partialDeriv
    rw [fderiv_continuousMultilinear_apply_const hD, iteratedFDeriv_succ_apply_left]
    rfl
  rw [h1, Real.norm_eq_abs]
  have h2 := (iteratedFDeriv ℝ (j + 1) g x).le_opNorm
    (Fin.cons w (fun l => EuclideanSpace.single (idx l) (1 : ℝ)))
  rw [Fin.prod_univ_succ] at h2
  simp only [Fin.cons_zero, Fin.cons_succ, EuclideanSpace.norm_single, norm_one, Finset.prod_const_one,
    mul_one] at h2
  simpa [Real.norm_eq_abs, mul_comm] using h2

open LineDeriv in
lemma sa16j_S_memLp (m : ℕ) (p : ℝ) (u : 𝓢(Euc d, ℝ)) :
    MemLp (sa16j_S d m u) (ENNReal.ofReal p) volume := by
  have hg : MemLp (fun x => ∑ j ∈ Finset.range (m + 1), ∑ r : Fin j → Fin d, |partialDeriv r (⇑u) x|)
      (ENNReal.ofReal p) volume := by
    refine memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun r _ => ?_
    rw [sa16j_pd_schwartz u r]
    exact (SchwartzMap.memLp (∂^{fun l => (EuclideanSpace.single (r l) (1 : ℝ) : Euc d)} u)
      (ENNReal.ofReal p) (volume : Measure (Euc d))).norm
  refine hg.mono' (sa16j_S_cont u.smooth' m).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d m (⇑u) x)]
  exact sa16j_S_le m u x

/-- for smooth `f` with `L^p` derivatives, `wNormE` is the `L^p` norm of the jet -/
theorem sa16j_wNormE_eq (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hS : MemLp (sa16j_S d m f) (ENNReal.ofReal p) volume) :
    wNormE m p f = eLpNorm (wJet m f) (ENNReal.ofReal p) volume := by
  obtain ⟨G, hG⟩ := sa16j_jet_mem d m p hf hS
  have hz : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = f x := by
    filter_upwards [hG] with x hx
    rw [hx]
    simp only [wJet, wZero, partialDeriv]
    exact iteratedFDeriv_zero_apply _
  rw [wNormE_eq_lift_norm d m p G f hz]
  have hnorm : ‖G‖ = ‖(G : WLp d m p)‖ := rfl
  rw [hnorm, Lp.norm_def, eLpNorm_congr_ae hG]
  exact ENNReal.ofReal_toReal (by
    have := Lp.eLpNorm_lt_top (G : WLp d m p)
    rw [eLpNorm_congr_ae hG] at this
    exact this.ne)

lemma sa16j_schwartz_bdd (s : 𝓢(Euc d, ℝ)) : ∃ B : ℝ, ∀ x, |s x| ≤ B := by
  obtain ⟨C, hC⟩ := s.decay 0 0
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC.2 x⟩

open LineDeriv in
lemma sa16j_pd_conv_bound {m : ℕ} (hd : 1 ≤ d) (p : ℝ) [Fact (2 ≤ p)] {k : Euc d → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hk : Measurable k) (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hk1 : Integrable k)
    (hkm : Integrable (fun z => |k z| * ‖z‖)) (hodd : ∀ z, k (-z) = -k z) (u : 𝓢(Euc d, ℝ))
    {j : ℕ} (hj : j ≤ m) (idx : Fin j → Fin d) :
    eLpNorm (partialDeriv idx (sa16j_conv k (⇑u))) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((∫ z, |k z| * ‖z‖) * (d : ℝ) ^ (m + 1)) *
        eLpNorm (wJet (m + 1) (⇑u)) (ENNReal.ofReal p) volume := by
  have hp1 : 1 ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have hu : ContDiff ℝ ∞ (⇑u) := u.smooth'
  have hw : ContDiff ℝ ∞ (partialDeriv idx (⇑u)) := sa16j_pd_smooth hu idx
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x, |partialDeriv idx (⇑u) x| ≤ B := by
    rw [sa16j_pd_schwartz u idx]
    exact sa16j_schwartz_bdd _
  have hgain := sa16j_odd_gain hp1 hk hk1 hkm hodd (hw.of_le (by exact_mod_cast le_top))
    (B := B) (fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hL : partialDeriv idx (sa16j_conv k (⇑u)) = fun x => ∫ z, k z • partialDeriv idx (⇑u) (x - z) := by
    rw [sa16j_conv_pd hksupp hR hk1 j idx u hu]
    funext x
    simp [sa16j_conv]
  rw [hL]
  refine hgain.trans ?_
  rw [ENNReal.ofReal_mul (integral_nonneg fun z => by positivity), mul_assoc]
  refine mul_le_mul' le_rfl ?_
  have hdp : (0 : ℝ) ≤ (d : ℝ) ^ (m + 1) := by positivity
  have hpt : ∀ x, ‖fderiv ℝ (partialDeriv idx (⇑u)) x‖ ≤ (d : ℝ) ^ (m + 1) * ‖wJet (m + 1) (⇑u) x‖ := by
    intro x
    refine (sa16j_fderiv_pd_le hu idx x).trans ?_
    refine (sa16j_norm_iter_le (⇑u) x (j + 1)).trans ?_
    have h1 : ∀ r : Fin (j + 1) → Fin d, |partialDeriv r (⇑u) x| ≤ ‖wJet (m + 1) (⇑u) x‖ :=
      fun r => sa16j_pd_le_jet (m + 1) (⇑u) x (by omega) r
    calc ∑ r : Fin (j + 1) → Fin d, |partialDeriv r (⇑u) x|
        ≤ ∑ r : Fin (j + 1) → Fin d, ‖wJet (m + 1) (⇑u) x‖ := Finset.sum_le_sum fun r _ => h1 r
      _ = (d : ℝ) ^ (j + 1) * ‖wJet (m + 1) (⇑u) x‖ := by
          simp [Finset.sum_const, Fintype.card_fun]
      _ ≤ (d : ℝ) ^ (m + 1) * ‖wJet (m + 1) (⇑u) x‖ := by
          refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast hd) (by omega))
            (norm_nonneg _)
  have hmeas : AEStronglyMeasurable (fun x => ‖fderiv ℝ (partialDeriv idx (⇑u)) x‖) volume :=
    ((hw.continuous_fderiv (by simp)).norm).aestronglyMeasurable
  refine (eLpNorm_mono_ae_real hmeas (Eventually.of_forall fun x => (norm_norm _).le.trans (hpt x))).trans ?_
  have : (fun x => (d : ℝ) ^ (m + 1) * ‖wJet (m + 1) (⇑u) x‖) =
      (d : ℝ) ^ (m + 1) • (fun x => ‖wJet (m + 1) (⇑u) x‖) := by
    funext x; simp
  rw [this, eLpNorm_const_smul, eLpNorm_norm _ (sa16j_jet_cont hu (m + 1)).aestronglyMeasurable]
  refine le_of_eq ?_
  rw [Real.enorm_eq_ofReal hdp]

lemma sa16j_jet_memLp (d m : ℕ) (p : ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hS : MemLp (sa16j_S d m f) (ENNReal.ofReal p) volume) :
    MemLp (wJet m f) (ENNReal.ofReal p) volume :=
  hS.mono' (sa16j_jet_cont hf m).aestronglyMeasurable
    (Eventually.of_forall fun x => sa16j_jet_norm_le m f x)

open LineDeriv in
/-- the generic odd-kernel estimate in the weak norm -/
theorem sa16j_odd_wnorm (d : ℕ) (hd : 1 ≤ d) (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {k : Euc d → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hk : Measurable k) (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hk1 : Integrable k)
    (hkm : Integrable (fun z => |k z| * ‖z‖)) (hodd : ∀ z, k (-z) = -k z) (u : 𝓢(Euc d, ℝ)) :
    wNormE m p (sa16j_conv k (⇑u)) ≤
      ENNReal.ofReal ((Fintype.card (WIndex d m) : ℝ) * ((∫ z, |k z| * ‖z‖) * (d : ℝ) ^ (m + 1))) *
        wNormE (m + 1) p (⇑u) := by
  have hp1 : 1 ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have hu : ContDiff ℝ ∞ (⇑u) := u.smooth'
  have hc := sa16j_conv_contDiff hksupp hR hk1 hu
  have hSu : MemLp (sa16j_S d (m + 1) (⇑u)) (ENNReal.ofReal p) volume := sa16j_S_memLp (m + 1) p u
  have hW1 : wNormE (m + 1) p (⇑u) = eLpNorm (wJet (m + 1) (⇑u)) (ENNReal.ofReal p) volume :=
    sa16j_wNormE_eq d (m + 1) p hu hSu
  have hW1fin : eLpNorm (wJet (m + 1) (⇑u)) (ENNReal.ofReal p) volume < ⊤ :=
    (sa16j_jet_memLp d (m + 1) p hu hSu).eLpNorm_lt_top
  set Mk : ℝ := ∫ z, |k z| * ‖z‖ with hMk
  have hMk0 : 0 ≤ Mk := integral_nonneg fun z => by positivity
  have hbound : ∀ {j : ℕ}, j ≤ m → ∀ idx : Fin j → Fin d,
      eLpNorm (partialDeriv idx (sa16j_conv k (⇑u))) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (Mk * (d : ℝ) ^ (m + 1)) *
          eLpNorm (wJet (m + 1) (⇑u)) (ENNReal.ofReal p) volume := fun hj idx =>
    sa16j_pd_conv_bound hd p hR hk hksupp hk1 hkm hodd u hj idx
  have hpdmem : ∀ {j : ℕ}, j ≤ m → ∀ idx : Fin j → Fin d,
      MemLp (partialDeriv idx (sa16j_conv k (⇑u))) (ENNReal.ofReal p) volume := by
    intro j hj idx
    exact lt_of_le_of_lt (hbound hj idx) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW1fin)
  have hSc : MemLp (sa16j_S d m (sa16j_conv k (⇑u))) (ENNReal.ofReal p) volume := by
    have hg : MemLp (fun x => ∑ j ∈ Finset.range (m + 1), ∑ r : Fin j → Fin d,
        |partialDeriv r (sa16j_conv k (⇑u)) x|) (ENNReal.ofReal p) volume := by
      refine memLp_finsetSum _ fun j hj => memLp_finsetSum _ fun r _ => ?_
      exact (hpdmem (by have := Finset.mem_range.1 hj; omega) r).norm
    refine hg.mono' (sa16j_S_cont hc m).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d m _ x)]
    exact sa16j_S_le m _ x
  rw [sa16j_wNormE_eq d m p hc hSc, hW1]
  -- jet sup norm ≤ sum of the coordinate derivatives
  have hpt : ∀ x, ‖wJet m (sa16j_conv k (⇑u)) x‖ ≤
      ∑ τ : WIndex d m, |partialDeriv τ.2 (sa16j_conv k (⇑u)) x| := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun τ => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun τ : WIndex d m => |partialDeriv τ.2 (sa16j_conv k (⇑u)) x|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  have hgm : ∀ τ ∈ (Finset.univ : Finset (WIndex d m)),
      AEStronglyMeasurable (fun x => |partialDeriv τ.2 (sa16j_conv k (⇑u)) x|) volume :=
    fun τ _ => ((sa16j_pd_smooth hc τ.2).continuous.abs).aestronglyMeasurable
  have hjc : AEStronglyMeasurable (wJet m (sa16j_conv k (⇑u))) volume :=
    (sa16j_jet_cont hc m).aestronglyMeasurable
  calc eLpNorm (wJet m (sa16j_conv k (⇑u))) (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x => ∑ τ : WIndex d m, |partialDeriv τ.2 (sa16j_conv k (⇑u)) x|)
          (ENNReal.ofReal p) volume :=
        eLpNorm_mono_ae_real hjc (Eventually.of_forall hpt)
    _ = eLpNorm (∑ τ : WIndex d m, fun x => |partialDeriv τ.2 (sa16j_conv k (⇑u)) x|)
          (ENNReal.ofReal p) volume := by
        congr 1
        funext x
        simp [Finset.sum_apply]
    _ ≤ ∑ τ : WIndex d m, eLpNorm (fun x => |partialDeriv τ.2 (sa16j_conv k (⇑u)) x|)
          (ENNReal.ofReal p) volume := by
        refine eLpNorm_sum_le (by simpa using hp1 : 1 ≤ ENNReal.ofReal p)
    _ ≤ ∑ τ : WIndex d m, ENNReal.ofReal (Mk * (d : ℝ) ^ (m + 1)) *
          eLpNorm (wJet (m + 1) (⇑u)) (ENNReal.ofReal p) volume := by
        refine Finset.sum_le_sum fun τ _ => ?_
        have := hbound (by have := τ.1.2; omega : (τ.1 : ℕ) ≤ m) τ.2
        refine le_trans (le_of_eq ?_) this
        exact eLpNorm_norm _ (sa16j_pd_smooth hc τ.2).continuous.aestronglyMeasurable
    _ = ENNReal.ofReal ((Fintype.card (WIndex d m) : ℝ) * (Mk * (d : ℝ) ^ (m + 1))) *
          eLpNorm (wJet (m + 1) (⇑u)) (ENNReal.ofReal p) volume := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_assoc, ENNReal.ofReal_natCast]

end Bridge

end HRS.Whole.AppendixA.Phase2SA16
