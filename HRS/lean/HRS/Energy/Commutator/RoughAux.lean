import HRS.Energy.Commutator.FourierAux
import HRS.Energy.Commutator.StressAux

/-!
# Regularised stress inequality for rough charges (packet CM-S3 helpers)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate
open HRS HRS.KernelAux HRS.Commutator.FourierAux

namespace HRS.Commutator.RoughAux

variable {d : ℕ}

/-- Gaussian decay hypothesis for a weight. -/
def GaussDecay (w : Lattice d → ℝ) : Prop :=
  ∃ ε C : ℝ, 0 < ε ∧ ∀ k, |w k| ≤ C * Real.exp (-ε * Lattice.enorm k ^ 2)

theorem GaussDecay.summable {w : Lattice d → ℝ} (h : GaussDecay w) : Summable fun k => |w k| := by
  obtain ⟨ε, C, hε, hw⟩ := h
  exact Summable.of_nonneg_of_le (fun k => abs_nonneg _) hw ((summable_gauss_lattice d ε hε).mul_left C)

theorem GaussDecay.mul {wF wG : Lattice d → ℝ} (hF : GaussDecay wF) (hG : GaussDecay wG) :
    GaussDecay (fun k => wF k * wG k) := by
  obtain ⟨ε, C, hε, hw⟩ := hF
  obtain ⟨ε', C', hε', hw'⟩ := hG
  refine ⟨ε + ε', C * C', by positivity, fun k => ?_⟩
  rw [abs_mul]
  calc |wF k| * |wG k| ≤ (C * Real.exp (-ε * Lattice.enorm k ^ 2)) * (C' * Real.exp (-ε' * Lattice.enorm k ^ 2)) :=
        mul_le_mul (hw k) (hw' k) (abs_nonneg _) ((abs_nonneg _).trans (hw k))
    _ = C * C' * Real.exp (-(ε + ε') * Lattice.enorm k ^ 2) := by
        rw [show -(ε + ε') * Lattice.enorm k ^ 2 = -ε * Lattice.enorm k ^ 2 + -ε' * Lattice.enorm k ^ 2 by ring,
          Real.exp_add]; ring

theorem GaussDecay.bound {w : Lattice d → ℝ} (h : GaussDecay w) (x : Torus d) :
    |ser w x| ≤ ∑' k, |w k| := by
  have hs := h.summable
  have hle : ∀ k, |w k * Torus.cosMode k x| ≤ |w k| := fun k => by
    rw [abs_mul]
    calc |w k| * |Torus.cosMode k x| ≤ |w k| * 1 := by gcongr; exact HRS.abs_cosMode_le k x
      _ = _ := mul_one _
  have hsum1 : Summable fun k => ‖w k * Torus.cosMode k x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by simpa using hle k) hs
  have h1 := norm_tsum_le_tsum_norm hsum1
  unfold ser
  simp only [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  exact Summable.tsum_le_tsum hle (by simpa using hsum1) hs

/-- Convolution of two cosine series is the cosine series of the product of the weights. -/
theorem convS_ser_ser {wF wG : Lattice d → ℝ} (hF : GaussDecay wF) (hG : GaussDecay wG)
    (hFe : ∀ k, wF (-k) = wF k) (hGe : ∀ k, wG (-k) = wG k) :
    convS (ser wF) volume (ser wG) = ser (fun k => wF k * wG k) := by
  have hFs : Summable fun k => |wF k| := hF.summable
  have hGs : Summable fun k => |wG k| := hG.summable
  have hmeas : Measurable (ser wG) := (continuous_ser hGs).measurable
  have hbd : ∀ y, |ser wG y| ≤ ∑' k, |wG k| := hG.bound
  rw [convS_ser_eq hFs hFe volume hmeas hbd]
  have hprod := hF.mul hG
  rw [ser_eq_toFun hprod.summable]
  congr 1
  funext k
  simp only [cfs, cf]
  have : shat volume (ser wG) k = (wG k : ℂ) := by
    have h1 := coeffOf_ser hGs hGe
    have h2 := congrFun h1 k
    rw [PDE.coeffOf_eq_fcoef] at h2
    unfold shat
    exact h2
  rw [this]
  push_cast; ring


/-- Reflection: `∫ F(x-y) G(x-z) dx = (F ⋆ G)(y - z)` for even `F`. -/
theorem integral_kernel_pair {F G : Torus d → ℝ} (hFe : ∀ x, F (-x) = F x) (y z : Torus d) :
    ∫ x, F (x - y) * G (x - z) = convS F volume G (y - z) := by
  unfold convS
  have h := integral_add_right_eq_self (μ := (volume : Measure (Torus d)))
    (fun x => F (x - y) * G (x - z)) z
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [add_sub_cancel_right]
  rw [← hFe (u + z - y)]
  congr 2
  abel


theorem isCk_ser' (j : ℕ) {w : Lattice d → ℝ} (h : GaussDecay w) (heven : ∀ k, w (-k) = w k) :
    Torus.IsCk j (ser w) := by
  obtain ⟨ε, C, hε, hw⟩ := h
  exact isCk_ser j hε hw heven

/-- Convolution commutes with differentiation of the kernel. -/
theorem convS_ser_partialDeriv (i : Fin d) {wF wG : Lattice d → ℝ} (hF : GaussDecay wF)
    (hG : GaussDecay wG) (hFe : ∀ k, wF (-k) = wF k) (hGe : ∀ k, wG (-k) = wG k) :
    convS (ser wF) volume (Torus.partialDeriv i (ser wG)) =
      Torus.partialDeriv i (ser (fun k => wF k * wG k)) := by
  have hFs : Summable fun k => |wF k| := hF.summable
  have hGs : Summable fun k => |wG k| := hG.summable
  have hP := hF.mul hG
  have hPs := hP.summable
  have hPe : ∀ k, (wF k * wG k) = (wF (-k) * wG (-k)) := fun k => by rw [hFe, hGe]
  have hG1 : Torus.IsCk 1 (ser wG) := isCk_ser' 1 hG hGe
  have hP1 : Torus.IsCk 1 (ser fun k => wF k * wG k) := isCk_ser' 1 hP (fun k => (hPe k).symm)
  have hcg : Continuous (Torus.partialDeriv i (ser wG)) := PDE.continuous_partialDeriv i _ hG1
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hcg.continuousOn
  have hbd : ∀ y, |Torus.partialDeriv i (ser wG) y| ≤ B := fun y => by
    simpa using hB y (mem_univ _)
  have hc1 : Continuous (convS (ser wF) volume (Torus.partialDeriv i (ser wG))) :=
    continuous_convS (continuous_ser hFs) volume hcg.measurable hbd
  have hc2 : Continuous (Torus.partialDeriv i (ser fun k => wF k * wG k)) :=
    PDE.continuous_partialDeriv i _ hP1
  have hco1 : PDE.coeffOf (convS (ser wF) volume (Torus.partialDeriv i (ser wG))) =
      PDE.derivCoeff i (cf fun k => wF k * wG k) := by
    funext k
    rw [PDE.coeffOf_eq_fcoef, coeff_convS (continuous_ser hFs) volume hcg.measurable hbd k]
    have h2 : shat volume (Torus.partialDeriv i (ser wG)) k =
        PDE.coeffOf (Torus.partialDeriv i (ser wG)) k := by
      rw [PDE.coeffOf_eq_fcoef]; rfl
    rw [h2, PDE.coeffOf_partialDeriv i _ hG1, coeffOf_ser hGs hGe, ← PDE.coeffOf_eq_fcoef,
      coeffOf_ser hFs hFe]
    simp [PDE.derivCoeff, cf]
    ring
  have hco2 : PDE.coeffOf (Torus.partialDeriv i (ser fun k => wF k * wG k)) =
      PDE.derivCoeff i (cf fun k => wF k * wG k) := by
    rw [PDE.coeffOf_partialDeriv i _ hP1, coeffOf_ser hPs (fun k => (hPe k).symm)]
  have hsum : Summable fun k => ‖PDE.coeffOf (convS (ser wF) volume (Torus.partialDeriv i (ser wG))) k‖ := by
    rw [hco1]
    obtain ⟨ε, C, hε, hw⟩ := hP
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((summable_deriv_gauss hε hw i).mul_left (2 * Real.pi))
    simp only [PDE.derivCoeff, cf, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      Complex.norm_intCast, Complex.norm_ofNat]
    have hp : |Real.pi| = Real.pi := abs_of_pos Real.pi_pos
    rw [hp]
    rw [abs_mul]
    exact le_of_eq (by ring)
  exact eq_of_coeffOf_eq hc1 hc2 hsum (hco1.trans hco2.symm)


/-! ### Energy identity for `C²` functions -/

theorem energy_by_parts {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) (l : ℝ) :
    ∫ x, (l * φ x ^ 2 + ‖Torus.grad φ x‖ ^ 2) = ∫ x, φ x * (l * φ x - Torus.laplacian φ x) := by
  have h1 : Torus.IsCk 1 φ := hφ.of_le (by norm_num)
  have hc : Continuous φ := HRS.Torus.continuous_of_continuous_lift h1.continuous
  have hw1 : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j φ) := fun j => PDE.isCk_one_partialDeriv j φ hφ
  have hwc : ∀ j, Continuous (Torus.partialDeriv j φ) := fun j => PDE.continuous_partialDeriv j φ h1
  have hww : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j φ)) := fun j =>
    PDE.continuous_partialDeriv j _ (hw1 j)
  have hlap : ∀ x, Torus.laplacian φ x = ∑ j, Torus.partialDeriv j (Torus.partialDeriv j φ) x :=
    PDE.laplacian_eq_sum φ hφ
  have hnorm : ∀ x, ‖Torus.grad φ x‖ ^ 2 = ∑ j, Torus.partialDeriv j φ x * Torus.partialDeriv j φ x :=
    StressAux.norm_grad_sq φ
  have hibp : ∀ j, ∫ x, Torus.partialDeriv j φ x * Torus.partialDeriv j φ x =
      -∫ x, φ x * Torus.partialDeriv j (Torus.partialDeriv j φ) x := fun j =>
    PDE.integral_partialDeriv_mul j φ (Torus.partialDeriv j φ) h1 (hw1 j)
  have hint1 : ∀ j, Integrable fun x => Torus.partialDeriv j φ x * Torus.partialDeriv j φ x :=
    fun j => StressAux.int_of_cont ((hwc j).mul (hwc j))
  have hint2 : ∀ j, Integrable fun x => φ x * Torus.partialDeriv j (Torus.partialDeriv j φ) x :=
    fun j => StressAux.int_of_cont (hc.mul (hww j))
  have hi0 : Integrable fun x => l * φ x ^ 2 :=
    StressAux.int_of_cont (continuous_const.mul (hc.pow 2))
  have e1 : ∫ x, (l * φ x ^ 2 + ‖Torus.grad φ x‖ ^ 2) =
      (∫ x, l * φ x ^ 2) + ∫ x, ‖Torus.grad φ x‖ ^ 2 := by
    refine integral_add hi0 ?_
    simp_rw [hnorm]
    exact integrable_finset_sum _ fun j _ => hint1 j
  have e2 : ∫ x, ‖Torus.grad φ x‖ ^ 2 = -∫ x, φ x * Torus.laplacian φ x := by
    simp_rw [hnorm, hlap]
    rw [integral_finset_sum _ fun j _ => hint1 j]
    simp_rw [Finset.mul_sum]
    rw [integral_finset_sum _ fun j _ => hint2 j, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hibp j
  have e3 : ∫ x, φ x * (l * φ x - Torus.laplacian φ x) =
      (∫ x, l * φ x ^ 2) - ∫ x, φ x * Torus.laplacian φ x := by
    have : ∀ x, φ x * (l * φ x - Torus.laplacian φ x) = l * φ x ^ 2 - φ x * Torus.laplacian φ x := fun x => by ring
    simp_rw [this]
    refine integral_sub hi0 ?_
    have : Continuous (Torus.laplacian φ) := by
      have h : Torus.laplacian φ = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j φ) x :=
        funext hlap
      rw [h]; exact continuous_finsetSum _ fun j _ => hww j
    exact StressAux.int_of_cont (hc.mul this)
  rw [e1, e2, e3]; ring


/-! ### Fubini for products of two kernel potentials -/

theorem fubini_pair (ρ : Measure (Torus d)) [IsFiniteMeasure ρ] {s : Torus d → ℝ} (hsm : Measurable s)
    {B : ℝ} (hs : ∀ y, |s y| ≤ B) {f g : Torus d → Torus d → ℝ}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) {M : ℝ}
    (hfM : ∀ x y, |f x y| ≤ M) (hgM : ∀ x y, |g x y| ≤ M) :
    ∫ x, (∫ y, f x y * s y ∂ρ) * (∫ z, g x z * s z ∂ρ) =
      ∫ p, s p.1 * s p.2 * (∫ x, f x p.1 * g x p.2) ∂(ρ.prod ρ) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hs 0)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfM 0 0)
  have hmeas : Measurable fun q : Torus d × (Torus d × Torus d) =>
      f q.1 q.2.1 * s q.2.1 * (g q.1 q.2.2 * s q.2.2) := by
    have h1 : Measurable fun q : Torus d × (Torus d × Torus d) => f q.1 q.2.1 :=
      hf.comp (measurable_fst.prodMk (measurable_snd.fst))
    have h2 : Measurable fun q : Torus d × (Torus d × Torus d) => g q.1 q.2.2 :=
      hg.comp (measurable_fst.prodMk (measurable_snd.snd))
    exact (h1.mul (hsm.comp measurable_snd.fst)).mul (h2.mul (hsm.comp measurable_snd.snd))
  have hint : Integrable (fun q : Torus d × (Torus d × Torus d) =>
      f q.1 q.2.1 * s q.2.1 * (g q.1 q.2.2 * s q.2.2))
      ((volume : Measure (Torus d)).prod (ρ.prod ρ)) := by
    refine Integrable.mono' (integrable_const (M * B * (M * B))) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hfM _ _) (hs _) (abs_nonneg _) hM)
      (mul_le_mul (hgM _ _) (hs _) (abs_nonneg _) hM) (by positivity) (by positivity)
  have h1 : ∀ x : Torus d, (∫ y, f x y * s y ∂ρ) * (∫ z, g x z * s z ∂ρ) =
      ∫ p, f x p.1 * s p.1 * (g x p.2 * s p.2) ∂(ρ.prod ρ) := fun x =>
    (integral_prod_mul (μ := ρ) (ν := ρ) (fun y => f x y * s y) (fun z => g x z * s z)).symm
  simp_rw [h1]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only []
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []; ring

end HRS.Commutator.RoughAux
