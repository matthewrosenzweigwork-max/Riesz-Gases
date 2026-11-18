import HRS.Whole.Adjoint
import HRS.Whole.AppendixBEnergy

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.MS.SuppU15

open HRS HRS.Whole

variable {d : ℕ}

lemma u15_matVec_apply (N : Matrix (Fin d) (Fin d) ℝ) (y : Euc d) (i : Fin d) :
    Torus.matVec N y i = ∑ j, N i j * y j := by
  unfold Torus.matVec
  simp [Matrix.mulVec, dotProduct]

/-- operator norm constant of `matVec N`. -/
def u15_cM (N : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)‖

lemma u15_cM_nonneg (N : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ u15_cM N := norm_nonneg _

lemma u15_matVec_norm_le (N : Matrix (Fin d) (Fin d) ℝ) (y : Euc d) :
    ‖Torus.matVec N y‖ ≤ u15_cM N * ‖y‖ :=
  (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)).le_opNorm y

lemma u15_matVec_lip (N : Matrix (Fin d) (Fin d) ℝ) :
    LipschitzWith (⟨u15_cM N, u15_cM_nonneg N⟩ : ℝ≥0) (Torus.matVec N) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have : Torus.matVec N x - Torus.matVec N y = Torus.matVec N (x - y) := by
    unfold Torus.matVec; simp
  rw [dist_eq_norm, dist_eq_norm, this]
  exact u15_matVec_norm_le N (x - y)

lemma u15_norm_le_sum (y : Euc d) : ‖y‖ ≤ ∑ j, |y j| := by
  have : y = ∑ j, y j • EuclideanSpace.single j (1 : ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_smul, EuclideanSpace.norm_single]; simp

/-- Finite linear combinations of fractional derivative representatives. -/
lemma u15_frac_sum {ι : Type*} (S : Finset ι) (α : ℝ) (a : ι → ℝ) (g w : ι → Euc d → ℝ)
    (h : ∀ j ∈ S, IsFracDerivRep α (g j) (w j)) :
    IsFracDerivRep α (fun x => ∑ j ∈ S, a j * g j x) (fun x => ∑ j ∈ S, a j * w j x) := by
  intro φ
  set T : Euc d → ℂ := fun x => 𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x
    with hT
  have e1 : (fun x => ((∑ j ∈ S, a j * g j x : ℝ) : ℂ) * T x) =
      fun x => ∑ j ∈ S, (a j : ℂ) * (((g j x : ℝ) : ℂ) * T x) := by
    ext x; push_cast; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
  have e2 : (fun x => ((∑ j ∈ S, a j * w j x : ℝ) : ℂ) * φ x) =
      fun x => ∑ j ∈ S, (a j : ℂ) * (((w j x : ℝ) : ℂ) * φ x) := by
    ext x; push_cast; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
  have hh := fun j (hj : j ∈ S) => h j hj φ
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    exact integrable_finset_sum _ fun j hj => ((hh j hj).1).const_mul _
  · rw [e2]
    exact integrable_finset_sum _ fun j hj => ((hh j hj).2.1).const_mul _
  · rw [e1, e2, integral_finset_sum _ fun j hj => ((hh j hj).1).const_mul _,
      integral_finset_sum _ fun j hj => ((hh j hj).2.1).const_mul _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_const_mul, integral_const_mul, (hh j hj).2.2]

lemma u15_gradient_diff {F : Euc d → ℝ} (hF : ContDiff ℝ 2 F) (z : Euc d) :
    DifferentiableAt ℝ (gradient F) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
  have hgrad : gradient F = (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap ∘
      (fderiv ℝ F) := rfl
  rw [hgrad]
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap.differentiableAt).comp z hd

lemma u15_fderiv_gradient_le {F : Euc d → ℝ} (hF : ContDiff ℝ 2 F) (z : Euc d) :
    ‖fderiv ℝ (gradient F) z‖ ≤ ‖fderiv ℝ (fderiv ℝ F) z‖ := by
  have hfd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt
  have he' := ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap.hasFDerivAt).comp z hfd
  have hgrad : gradient F = (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap ∘
      (fderiv ℝ F) := rfl
  have hg : fderiv ℝ (gradient F) z = ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap).comp
      (fderiv ℝ (fderiv ℝ F) z) := by
    rw [hgrad, he'.fderiv]
  rw [hg]
  have hn : ‖(InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simp)
  calc ‖((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap).comp
        (fderiv ℝ (fderiv ℝ F) z)‖
      ≤ ‖(InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap‖ *
          ‖fderiv ℝ (fderiv ℝ F) z‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ F) z‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg (fderiv ℝ (fderiv ℝ F) z))
    _ = ‖fderiv ℝ (fderiv ℝ F) z‖ := one_mul _

lemma u15_grad_lip {F : Euc d → ℝ} (hF : ContDiff ℝ 2 F) {σ : ℝ}
    (hσ : ∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ σ) (x y : Euc d) :
    ‖gradient F x - gradient F y‖ ≤ σ * ‖x - y‖ := by
  have hb : ∀ z ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (gradient F) z‖ ≤ σ := by
    intro z _
    refine (u15_fderiv_gradient_le hF z).trans ?_
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := z) (n := 1)
    have h2 := norm_iteratedFDeriv_one (𝕜 := ℝ) (x := z) (fderiv ℝ F)
    rw [← h2, h1]
    exact hσ z
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => u15_gradient_diff hF z) hb convex_univ (Set.mem_univ y) (Set.mem_univ x)
  exact h

lemma u15_eucVec_decomp (y : Euc d) : y = ∑ j, y j • EuclideanSpace.single j (1 : ℝ) := by
  ext i; simp [Finset.sum_apply, Pi.single_apply]

/-- The transport bound for `v = N ∇f` from the `S4.13` data. -/
lemma u15_transport (Nm : Matrix (Fin d) (Fin d) ℝ) {α p : ℝ} (hp : 1 ≤ p) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) {w : Fin d → Euc d → ℝ}
    (hw : ∀ i, IsFracDerivRep α (fun x => gradient f x i) (w i))
    (hmem : ∀ i, MemLp (w i) (ENNReal.ofReal p) volume)
    (hS : (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
      ∑ i, eLpNorm (w i) (ENNReal.ofReal p) volume ≠ ⊤) :
    HasFracTransportBound α p (fun x => Torus.matVec Nm (gradient f x))
      (u15_cM Nm * ((⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
        ∑ i, eLpNorm (w i) (ENNReal.ofReal p) volume).toReal) := by
  set sup : ℝ≥0∞ := ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖ with hsup_def
  set sm : ℝ≥0∞ := ∑ i, eLpNorm (w i) (ENNReal.ofReal p) volume with hsm_def
  have hsup : sup ≠ ⊤ := fun h => hS (by rw [h]; simp)
  have hsm : sm ≠ ⊤ := fun h => hS (by rw [h]; simp)
  set σ : ℝ := sup.toReal with hσ_def
  have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
  have hσ : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ σ := fun z =>
    (ENNReal.ofReal_le_iff_le_toReal hsup).1 (le_iSup (fun x : Euc d => ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) z)
  set cM := u15_cM Nm with hcM
  have hcM0 : 0 ≤ cM := u15_cM_nonneg Nm
  have hq1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  -- Lipschitz
  have hgl : LipschitzWith σ.toNNReal (gradient f) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hσ0]
    exact u15_grad_lip hf hσ x y
  obtain ⟨cN, hcN⟩ : ∃ cN : ℝ≥0, (cN : ℝ) = cM := ⟨⟨cM, hcM0⟩, rfl⟩
  have hvl : LipschitzWith (cN * σ.toNNReal) (fun x => Torus.matVec Nm (gradient f x)) := by
    have h0 : LipschitzWith cN (Torus.matVec Nm) := by
      have := u15_matVec_lip Nm
      have e : (⟨u15_cM Nm, u15_cM_nonneg Nm⟩ : ℝ≥0) = cN := NNReal.eq (by show u15_cM Nm = (cN : ℝ); rw [hcN])
      rwa [e] at this
    exact h0.comp hgl
  -- the representative
  set W : Euc d → Euc d := fun x => WithLp.toLp 2 (fun j => w j x) with hW
  have hWdec : ∀ x, W x = ∑ j, w j x • EuclideanSpace.single j (1 : ℝ) := fun x => u15_eucVec_decomp (W x)
  have hWmeas : AEStronglyMeasurable W volume := by
    have : W = fun x => ∑ j, w j x • EuclideanSpace.single j (1 : ℝ) := funext hWdec
    rw [this]
    exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hmem j).aestronglyMeasurable.smul_const _
  have hw'meas : AEStronglyMeasurable (fun x => Torus.matVec Nm (W x)) volume :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Nm)).continuous.comp_aestronglyMeasurable hWmeas
  have hpt : ∀ x, ‖Torus.matVec Nm (W x)‖ ≤ cM * ∑ j, ‖w j x‖ := by
    intro x
    refine (u15_matVec_norm_le Nm (W x)).trans (mul_le_mul_of_nonneg_left ?_ hcM0)
    refine (u15_norm_le_sum (W x)).trans (le_of_eq ?_)
    simp [hW]
  have hnorm : eLpNorm (fun x => ‖Torus.matVec Nm (W x)‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (cM * sm.toReal) := by
    calc eLpNorm (fun x => ‖Torus.matVec Nm (W x)‖) (ENNReal.ofReal p) volume
        ≤ eLpNorm (fun x => cM * ∑ j, ‖w j x‖) (ENNReal.ofReal p) volume :=
          eLpNorm_mono_real hw'meas.norm (fun x => by
            rw [Real.norm_of_nonneg (norm_nonneg _)]
            exact hpt x)
      _ = eLpNorm (cM • ∑ j, (fun x => ‖w j x‖)) (ENNReal.ofReal p) volume := by
          congr 1; ext x; simp [Finset.sum_apply]
      _ ≤ ‖cM‖ₑ * eLpNorm (∑ j, (fun x => ‖w j x‖)) (ENNReal.ofReal p) volume :=
          eLpNorm_const_smul_le
      _ ≤ ‖cM‖ₑ * ∑ j, eLpNorm (fun x => ‖w j x‖) (ENNReal.ofReal p) volume :=
          mul_le_mul_right (eLpNorm_sum_le hq1) _
      _ = ENNReal.ofReal cM * sm := by
          rw [Real.enorm_of_nonneg hcM0, hsm_def]
          congr 1
          exact Finset.sum_congr rfl fun j _ => eLpNorm_norm _ (hmem j).aestronglyMeasurable
      _ = ENNReal.ofReal (cM * sm.toReal) := by
          rw [ENNReal.ofReal_mul hcM0, ENNReal.ofReal_toReal hsm]
  refine ⟨cN * σ.toNNReal, cM * sm.toReal, by positivity, hvl,
    ⟨fun x => Torus.matVec Nm (W x), ?_, hnorm⟩, ?_⟩
  · intro i
    have h1 := u15_frac_sum (Finset.univ : Finset (Fin d)) α (fun j => Nm i j)
      (fun j x => gradient f x j) (fun j x => w j x) (fun j _ => hw j)
    have e1 : (fun x => Torus.matVec Nm (gradient f x) i) = fun x => ∑ j ∈ Finset.univ, Nm i j * gradient f x j := by
      ext x; exact u15_matVec_apply Nm _ i
    have e2 : (fun x => Torus.matVec Nm (W x) i) = fun x => ∑ j ∈ Finset.univ, Nm i j * w j x := by
      ext x; rw [u15_matVec_apply]
    rw [e1, e2]; exact h1
  · have hc : ((cN * σ.toNNReal : ℝ≥0) : ℝ) = cM * σ := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ hσ0, hcN]
    rw [hc, ← mul_add, ENNReal.toReal_add hsup hsm]

end HRS.MS.SuppU15
