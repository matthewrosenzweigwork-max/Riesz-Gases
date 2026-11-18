import HRS.Commutator.Torus.TKRAux1
import HRS.Commutator.Torus.TPOSAux12

/-!
# T-KR helpers, part 2: the periodised kernel `Ψ_η = perio ψ_{1/η}` is a trigonometric polynomial
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s η : ℝ}

section Psi

variable {L : ℝ}

lemma tkr_om_norm (hL : 0 < L) (z : Euc d) :
    ‖Whole.cmxFB_Om (d := d) L hL z‖ = |Whole.psiL L z| := by
  rw [Whole.cmxFB_Om_apply, Complex.norm_real, Real.norm_eq_abs]

lemma tkr_psi_continuous (hL : 0 < L) : Continuous (Whole.psiL L : Euc d → ℝ) := by
  have : Continuous fun x : Euc d => (Whole.cmxFB_Om (d := d) L hL x).re :=
    Complex.continuous_re.comp (Whole.cmxFB_Om (d := d) L hL).continuous
  simpa [Whole.cmxFB_Om_apply] using this

lemma tkr_psi_integrable (hL : 0 < L) : Integrable (Whole.psiL L : Euc d → ℝ) := by
  have h2 : Integrable (fun x : Euc d => |Whole.psiL L x|) := by
    refine (((Whole.cmxFB_Om (d := d) L hL).integrable (μ := (volume : Measure (Euc d)))).norm).congr
      (Eventually.of_forall fun x => ?_)
    simp [tkr_om_norm hL]
  exact (integrable_norm_iff (tkr_psi_continuous hL).aestronglyMeasurable).1
    (by simpa [Real.norm_eq_abs] using h2)

lemma tkr_psi_decay (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Euc d, z ≠ 0 →
      |Whole.psiL L z| ≤ C * ‖z‖ ^ (-((d : ℝ) + 1)) := by
  obtain ⟨C, hC0, hC⟩ := (Whole.cmxFB_Om (d := d) L hL).decay (d + 1) 0
  refine ⟨C, hC0.le, fun z hz => ?_⟩
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h1 := hC z
  rw [norm_iteratedFDeriv_zero, tkr_om_norm hL] at h1
  have h2 : ‖z‖ ^ (-((d : ℝ) + 1)) = (‖z‖ ^ (d + 1))⁻¹ := by
    rw [Real.rpow_neg hz0.le]
    congr 1
    rw [← Real.rpow_natCast]; push_cast; rfl
  rw [h2, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

lemma tkr_psi_summable (hL : 0 < L) (y : Euc d) :
    Summable (fun m : Lattice d => Whole.psiL L (y + Lattice.toEuc m)) := by
  obtain ⟨C, hC0, hC⟩ := tkr_psi_decay (d := d) hL
  exact tpos_summable_shift hC0 (by linarith : (d : ℝ) < (d : ℝ) + 1) hC y

lemma tkr_perio_psi_continuous (hL : 0 < L) :
    Continuous (perio (Whole.psiL L : Euc d → ℝ) : Torus d → ℝ) := by
  refine Torus.continuous_of_continuous_lift ?_
  have hfun : Torus.lift (perio (Whole.psiL L : Euc d → ℝ)) =
      fun y : Euc d => ∑' m : Lattice d, Whole.psiL L (y + Lattice.toEuc m) := by
    funext y
    exact tpos_perio_mk _ y
  rw [hfun]
  rw [continuous_iff_continuousAt]
  intro y0
  classical
  obtain ⟨C, hC0, hC⟩ := tkr_psi_decay (d := d) hL
  have hcont := tkr_psi_continuous (d := d) hL
  set T : Finset (Lattice d) := (tpos_finite_norm_le (d := d) (‖y0‖ + 1)).toFinset with hT
  have hy0 : ∀ m : Lattice d, m ∉ T → y0 + Lattice.toEuc m ≠ 0 := by
    intro m hm h0
    apply hm
    simp only [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have : Lattice.toEuc m = -y0 := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0
    rw [this, norm_neg]; linarith [norm_nonneg y0]
  have hmain := tpos_continuousAt_latsum (h := Whole.psiL L) hC0 (by linarith : (d : ℝ) < (d : ℝ) + 1)
    (fun z hz => hC z hz) hcont.continuousOn T y0 hy0
  have hfin : Continuous fun y : Euc d => ∑ m ∈ T, Whole.psiL L (y + Lattice.toEuc m) :=
    continuous_finset_sum _ fun m _ => hcont.comp (continuous_id.add continuous_const)
  have hsplit : ∀ y : Euc d, ∑' m : Lattice d, Whole.psiL L (y + Lattice.toEuc m) =
      (∑' m : Lattice d, if m ∈ T then 0 else Whole.psiL L (y + Lattice.toEuc m)) +
        ∑ m ∈ T, Whole.psiL L (y + Lattice.toEuc m) := by
    intro y
    have hs := tkr_psi_summable (d := d) hL y
    have h1 := hs.sum_add_tsum_compl (s := T)
    set S : Set (Lattice d) := (↑T)ᶜ with hS
    rw [← h1]
    have h2 : ∑' m : Lattice d, (if m ∈ T then 0 else Whole.psiL L (y + Lattice.toEuc m)) =
        ∑' m : ↥(S), Whole.psiL L (y + Lattice.toEuc m.1) := by
      rw [tsum_subtype S (fun m => Whole.psiL L (y + Lattice.toEuc m))]
      refine tsum_congr fun m => ?_
      by_cases hm : m ∈ T <;> simp [S, Set.indicator, hm]
    rw [h2]; ring
  simp_rw [hsplit]
  exact hmain.add hfin.continuousAt

lemma tkr_psi_measurable (hL : 0 < L) : Measurable (Whole.psiL L : Euc d → ℝ) :=
  (tkr_psi_continuous hL).measurable

lemma tkr_fcoef_perio_psi (hL : 0 < L) (k : Lattice d) :
    Torus.fcoef (perio (Whole.psiL L : Euc d → ℝ) : Torus d → ℝ) k =
      ((Whole.chi (L⁻¹ • Lattice.toEuc k) : ℝ) : ℂ) := by
  rw [tpos_fcoef_perio (tkr_psi_measurable hL) (tkr_psi_integrable hL) (tkr_psi_summable hL)]
  have h1 : (fun y : Euc d => ((Whole.psiL L y : ℝ) : ℂ)) = ⇑(Whole.cmxFB_Om (d := d) L hL) := by
    funext y; exact (Whole.cmxFB_Om_apply hL y).symm
  rw [h1]
  have h2 := congrArg (fun T : SchwartzMap (Euc d) ℂ => T (Lattice.toEuc k))
    (Whole.cmxFB_fourier_Om (d := d) hL)
  simp only [SchwartzMap.fourier_coe] at h2
  rw [h2]
  rfl

end Psi

end HRS.Commutator.TorusNote
