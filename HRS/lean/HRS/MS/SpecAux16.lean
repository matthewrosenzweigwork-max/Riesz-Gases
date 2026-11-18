import HRS.MS.SpecAux15

/-!
# S8P: the bounded symmetric bilinear form `q(v,w) = ∬ g(x-y) √ρ(x) v(x) √ρ(y) w(y)` on `L²(dx)` (S8.7, packet E1)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_qbil`: a continuous bilinear form on `Lp ℝ 2 volume` with
`|q(v,w)| ≤ K ‖v‖ ‖w‖`, symmetric, and `q(v,v) ≥ 0` (from `riesz_energy_nonneg`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HRS.MS.Spec

open HRS HRS.Whole

variable {d : ℕ}

/-- The bilinear expression `∬ k(x,y) v(x) w(y)`. -/
def s8p_qf (s : ℝ) (ρ : Euc d → ℝ) (v w : Lp ℝ 2 (volume : Measure (Euc d))) : ℝ :=
  ∫ p : Euc d × Euc d, s8p_kern d s ρ p * (v p.1 * w p.2) ∂(volume.prod volume)

/-- Standing hypotheses on `ρ`. -/
structure S8pRho (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (M : ℝ) : Prop where
  hs0 : 0 < s
  hsd : s < d
  meas : Measurable ρ
  nonneg : ∀ x, 0 ≤ ρ x
  le : ∀ x, ρ x ≤ M
  int : Integrable ρ
  one : ∫ x, ρ x = 1

theorem s8p_lintegral_sq (v : Lp ℝ 2 (volume : Measure (Euc d))) :
    ∫⁻ x, ENNReal.ofReal (v x ^ 2) = ENNReal.ofReal (‖v‖ ^ 2) := by
  have hint : Integrable (fun x => v x ^ 2) := (Lp.memLp v).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

theorem s8p_ae_fst {f g : Euc d → ℝ} (h : f =ᵐ[volume] g) :
    (fun p : Euc d × Euc d => f p.1) =ᵐ[volume.prod volume] fun p => g p.1 :=
  (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Euc d)))
    (ν := (volume : Measure (Euc d)))).ae_eq_comp h

theorem s8p_ae_snd {f g : Euc d → ℝ} (h : f =ᵐ[volume] g) :
    (fun p : Euc d × Euc d => f p.2) =ᵐ[volume.prod volume] fun p => g p.2 :=
  (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Euc d)))
    (ν := (volume : Measure (Euc d)))).ae_eq_comp h

/-- The constant `C₁ = M ∫_{B_1} g + 1` as a real number. -/
def s8p_C1 (d : ℕ) (s M : ℝ) : ℝ := (ENNReal.ofReal M * s8p_Iball d s + 1).toReal

theorem s8p_qf_bound {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M)
    (v w : Lp ℝ 2 (volume : Measure (Euc d))) :
    ∫⁻ p : Euc d × Euc d, ‖s8p_kern d s ρ p * (v p.1 * w p.2)‖ₑ ∂(volume.prod volume) ≤
      ENNReal.ofReal (s8p_C1 d s M * (‖v‖ ^ 2 + ‖w‖ ^ 2)) := by
  have hv : AEMeasurable (v : Euc d → ℝ) := (Lp.aestronglyMeasurable v).aemeasurable
  have hw : AEMeasurable (w : Euc d → ℝ) := (Lp.aestronglyMeasurable w).aemeasurable
  have h1 := s8p_schur_double h.hs0 h.hsd ρ h.meas h.nonneg h.le h.int h.one v w hv hw
  have hC : ENNReal.ofReal M * s8p_Iball d s + 1 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (s8p_Iball_lt_top h.hs0.le h.hsd).ne, ENNReal.one_ne_top⟩
  have heq : ∀ p : Euc d × Euc d, ‖s8p_kern d s ρ p * (v p.1 * w p.2)‖ₑ =
      ENNReal.ofReal (s8p_kern d s ρ p * (|v p.1| * |w p.2|)) := by
    intro p
    rw [← ofReal_norm_eq_enorm, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (s8p_kern_nonneg h.hs0 ρ p)]
  simp_rw [heq]
  refine h1.trans ?_
  rw [s8p_lintegral_sq, s8p_lintegral_sq, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  rw [s8p_C1, ← ENNReal.ofReal_toReal hC, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  simp

theorem s8p_qf_integrable {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M)
    (v w : Lp ℝ 2 (volume : Measure (Euc d))) :
    Integrable (fun p : Euc d × Euc d => s8p_kern d s ρ p * (v p.1 * w p.2))
      (volume.prod volume) := by
  refine ⟨?_, ?_⟩
  · have hv1 : AEStronglyMeasurable (fun p : Euc d × Euc d => (v : Euc d → ℝ) p.1)
        (volume.prod volume) :=
      (Lp.aestronglyMeasurable v).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have hw2 : AEStronglyMeasurable (fun p : Euc d × Euc d => (w : Euc d → ℝ) p.2)
        (volume.prod volume) :=
      (Lp.aestronglyMeasurable w).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    exact (s8p_kern_meas s h.meas).aestronglyMeasurable.mul (hv1.mul hw2)
  · exact lt_of_le_of_lt (s8p_qf_bound h v w) ENNReal.ofReal_lt_top

theorem s8p_qf_abs_le {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M)
    (v w : Lp ℝ 2 (volume : Measure (Euc d))) :
    |s8p_qf s ρ v w| ≤ s8p_C1 d s M * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have hI := s8p_qf_integrable h v w
  have h1 : |s8p_qf s ρ v w| ≤ ∫ p : Euc d × Euc d, ‖s8p_kern d s ρ p * (v p.1 * w p.2)‖
      ∂(volume.prod volume) := by
    rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
  refine h1.trans ?_
  rw [integral_norm_eq_lintegral_enorm hI.aestronglyMeasurable]
  have := s8p_qf_bound h v w
  have hC : 0 ≤ s8p_C1 d s M * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
    unfold s8p_C1; positivity
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top this).trans (by rw [ENNReal.toReal_ofReal hC])

theorem s8p_qf_add_left {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M)
    (v v' w : Lp ℝ 2 (volume : Measure (Euc d))) :
    s8p_qf s ρ (v + v') w = s8p_qf s ρ v w + s8p_qf s ρ v' w := by
  unfold s8p_qf
  rw [← integral_add (s8p_qf_integrable h v w) (s8p_qf_integrable h v' w)]
  refine integral_congr_ae ?_
  filter_upwards [s8p_ae_fst (Lp.coeFn_add v v')] with p hp
  simp only [Pi.add_apply] at hp ⊢
  rw [hp]; ring

theorem s8p_qf_smul_left {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M) (c : ℝ)
    (v w : Lp ℝ 2 (volume : Measure (Euc d))) :
    s8p_qf s ρ (c • v) w = c * s8p_qf s ρ v w := by
  unfold s8p_qf
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [s8p_ae_fst (Lp.coeFn_smul c v)] with p hp
  simp only [Pi.smul_apply, smul_eq_mul] at hp ⊢
  rw [hp]; ring

theorem s8p_qf_add_right {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M)
    (v w w' : Lp ℝ 2 (volume : Measure (Euc d))) :
    s8p_qf s ρ v (w + w') = s8p_qf s ρ v w + s8p_qf s ρ v w' := by
  unfold s8p_qf
  rw [← integral_add (s8p_qf_integrable h v w) (s8p_qf_integrable h v w')]
  refine integral_congr_ae ?_
  filter_upwards [s8p_ae_snd (Lp.coeFn_add w w')] with p hp
  simp only [Pi.add_apply] at hp ⊢
  rw [hp]; ring

theorem s8p_qf_smul_right {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M) (c : ℝ)
    (v w : Lp ℝ 2 (volume : Measure (Euc d))) :
    s8p_qf s ρ v (c • w) = c * s8p_qf s ρ v w := by
  unfold s8p_qf
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [s8p_ae_snd (Lp.coeFn_smul c w)] with p hp
  simp only [Pi.smul_apply, smul_eq_mul] at hp ⊢
  rw [hp]; ring

theorem s8p_qf_symm {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M)
    (v w : Lp ℝ 2 (volume : Measure (Euc d))) : s8p_qf s ρ v w = s8p_qf s ρ w v := by
  unfold s8p_qf
  rw [← integral_prod_swap]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap, s8p_kern]
  have : rieszKernel d s (p.2 - p.1) = rieszKernel d s (p.1 - p.2) := by
    rw [← rieszKernel_neg (d := d) (s := s) (p.1 - p.2), neg_sub]
  rw [this]; ring

end HRS.MS.Spec
