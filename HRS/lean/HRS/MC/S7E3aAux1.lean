import HRS.MC.S7E1Aux4
import HRS.PDE.MeanFieldLinearResponse

/-!
# Packets `s7_E3a/b`, file 1: Bessel inequality and the tail of a bounded-kernel convolution

For an orthonormal family `e` in `L^2(mu)`: Bessel's inequality in the function form
`sum_{i<L} (int G e_i)^2 <= int G^2`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.E3Aux1

open HRS HRS.Sec7

variable {d : ℕ} {ρ : Torus d → ℝ}

theorem e3_orthonormal [IsProbabilityMeasure (withDensityReal ρ)] {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) :
    Orthonormal ℝ (fun i => (he.memLp i).toLp (e i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [PDE.MFLinear.innerLp_eq_l2Inner]
  have := he.orthonormal i j
  unfold l2Inner at this ⊢
  rw [← this]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (he.memLp i), MemLp.coeFn_toLp (he.memLp j)] with x h1 h2
  rw [h1, h2]

/-- Bessel's inequality in function form. -/
theorem e3_bessel [IsProbabilityMeasure (withDensityReal ρ)] {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) {G : Torus d → ℝ} (hG : MemLp G 2 (withDensityReal ρ))
    (L : ℕ) :
    ∑ i ∈ Finset.range L, (∫ y, G y * e i y ∂(withDensityReal ρ)) ^ 2 ≤
      ∫ y, G y ^ 2 ∂(withDensityReal ρ) := by
  have hu := e3_orthonormal he
  have h := hu.sum_inner_products_le (hG.toLp G) (s := Finset.range L)
  have e1 : ∀ i, ⟪(he.memLp i).toLp (e i), hG.toLp G⟫ = ∫ y, e i y * G y ∂(withDensityReal ρ) :=
    fun i => E1Aux2.e1b_inner_toLp (he.memLp i) hG
  have e2 : ‖hG.toLp G‖ ^ 2 = ∫ y, G y ^ 2 ∂(withDensityReal ρ) := by
    rw [Lp.norm_toLp]; exact E0b.e0b_sq_eq hG
  rw [e2] at h
  refine le_of_eq_of_le ?_ h
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e1, Real.norm_eq_abs, sq_abs]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mul_comm]


/-! ### Clamping a kernel -/

/-- `max (-M) (min M (g z))`. -/
def e3Clamp (M : ℝ) (g : Torus d → ℝ) (z : Torus d) : ℝ := max (-M) (min M (g z))

theorem e3Clamp_abs_le {M : ℝ} (hM : 0 ≤ M) (g : Torus d → ℝ) (z : Torus d) :
    |e3Clamp M g z| ≤ M := by
  unfold e3Clamp
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem e3Clamp_even {M : ℝ} {g : Torus d → ℝ} (hge : ∀ z, g (-z) = g z) (z : Torus d) :
    e3Clamp M g (-z) = e3Clamp M g z := by
  unfold e3Clamp; rw [hge]

theorem e3Clamp_aesm {M : ℝ} {g : Torus d → ℝ} (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (e3Clamp M g) volume := by
  unfold e3Clamp
  exact (continuous_const.max (continuous_const.min continuous_id)).comp_aestronglyMeasurable hg

theorem e3Clamp_sub_abs_le {M : ℝ} (hM : 0 ≤ M) (g : Torus d → ℝ) (z : Torus d) :
    |g z - e3Clamp M g z| ≤ |g z| := by
  unfold e3Clamp
  set t := g z
  rcases le_total t M with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-M) t with h2 | h2
    · rw [max_eq_right h2]; simp
    · rw [max_eq_left h2]
      rw [abs_le]; constructor <;> cases abs_cases t <;> linarith
  · rw [min_eq_left h1, max_eq_right (by linarith)]
    rw [abs_le]; constructor <;> cases abs_cases t <;> linarith

theorem e3Clamp_eq_self {M : ℝ} {g : Torus d → ℝ} {z : Torus d} (h : |g z| ≤ M) :
    e3Clamp M g z = g z := by
  unfold e3Clamp
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

theorem e3Clamp_tendsto {g : Torus d → ℝ} (hg : Integrable g) :
    Tendsto (fun n : ℕ => ∫⁻ z, ‖g z - e3Clamp (n : ℝ) g z‖ₑ) atTop (𝓝 0) := by
  have hae : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  have := tendsto_lintegral_of_dominated_convergence' (μ := (volume : Measure (Torus d)))
    (F := fun (n : ℕ) z => ‖g z - e3Clamp (n : ℝ) g z‖ₑ) (f := fun _ => (0 : ℝ≥0∞))
    (bound := fun z => ‖g z‖ₑ) ?_ ?_ ?_ ?_
  · simpa using this
  · intro n
    exact (hae.sub (e3Clamp_aesm hae)).enorm
  · intro n
    refine Filter.Eventually.of_forall fun z => ?_
    beta_reduce
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using e3Clamp_sub_abs_le (Nat.cast_nonneg n) g z)
  · exact hg.hasFiniteIntegral.ne
  · refine Filter.Eventually.of_forall fun z => ?_
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨n0, hn0⟩ := exists_nat_ge |g z|
    filter_upwards [Filter.eventually_ge_atTop n0] with n hn
    rw [e3Clamp_eq_self (hn0.trans (by exact_mod_cast hn))]
    simp


/-! ### Tail of a bounded-kernel convolution along an orthonormal family -/

theorem e3_slice_aesm {G : Torus d → ℝ} (hG : AEStronglyMeasurable G volume) (ρ : Torus d → ℝ)
    (a : Torus d) : AEStronglyMeasurable (fun y => G (a - y)) (withDensityReal ρ) := by
  have hac : withDensityReal ρ ≪ (volume : Measure (Torus d)) := withDensity_absolutelyContinuous _ _
  have := PDE.MFLinear.negInv (d := d)
  have := hG.comp_measurePreserving (Measure.measurePreserving_sub_left volume a)
  exact this.mono_ac hac

theorem e3_phi_sum {gM : Torus d → ℝ} {Λ M : ℝ} (H : PDE.MFLinear.KS gM ρ Λ)
    (hb : ∀ z, |gM z| ≤ M) {e : ℕ → Torus d → ℝ} (he : IsONBL2Zero (withDensityReal ρ) e)
    (L : ℕ) (x : ℕ → ℝ) (a : Torus d) :
    PDE.MFLinear.Phi gM ρ (fun y => ∑ i ∈ Finset.range L, x i * e i y) a =
      ∑ i ∈ Finset.range L, x i * PDE.MFLinear.Phi gM ρ (e i) a := by
  have := H.isProb
  unfold PDE.MFLinear.Phi
  have hint : ∀ i, Integrable (fun y => gM (a - y) * (x i * e i y)) (withDensityReal ρ) := by
    intro i
    have h1 : Integrable (fun y => x i * e i y) (withDensityReal ρ) :=
      ((he.memLp i).integrable one_le_two).const_mul _
    exact h1.bdd_mul (e3_slice_aesm H.int.aestronglyMeasurable ρ a) (c := M)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hb (a - y))
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem e3_bounded_tail [IsProbabilityMeasure (withDensityReal ρ)] {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) {gM : Torus d → ℝ} {Λ M : ℝ}
    (H : PDE.MFLinear.KS gM ρ Λ) (hM : 0 ≤ M) (hb : ∀ z, |gM z| ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (L : ℕ) (x : ℕ → ℝ), (∀ i, i < N → x i = 0) →
      ∫ a, (PDE.MFLinear.Phi gM ρ (fun y => ∑ i ∈ Finset.range L, x i * e i y) a) ^ 2
          ∂(withDensityReal ρ) ≤ δ * ∑ i ∈ Finset.range L, x i ^ 2 := by
  set μ := withDensityReal ρ with hμ
  set b : ℕ → Torus d → ℝ := fun i => PDE.MFLinear.Phi gM ρ (e i) with hb_def
  have hbm : ∀ i, MemLp (b i) 2 μ := fun i => (PDE.MFLinear.memLp_Phi H (he.memLp i)).1
  have hbd : ∀ a L, ∑ i ∈ Finset.range L, (b i a) ^ 2 ≤ M ^ 2 := by
    intro a L
    have hGm : MemLp (fun y => gM (a - y)) 2 μ :=
      MemLp.of_bound (e3_slice_aesm H.int.aestronglyMeasurable ρ a) M
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hb (a - y))
    refine (e3_bessel he hGm L).trans ?_
    calc ∫ y, gM (a - y) ^ 2 ∂μ ≤ ∫ _y, M ^ 2 ∂μ :=
          integral_mono hGm.integrable_sq (integrable_const _) (fun y => by
            have := hb (a - y)
            simp only
            nlinarith [abs_nonneg (gM (a - y)), sq_abs (gM (a - y))])
      _ = M ^ 2 := by simp
  set s : ℕ → ℝ := fun i => ∫ a, (b i a) ^ 2 ∂μ with hs_def
  have hs0 : ∀ i, 0 ≤ s i := fun i => integral_nonneg fun a => sq_nonneg _
  have hsum : ∀ L, ∑ i ∈ Finset.range L, s i ≤ M ^ 2 := by
    intro L
    have h1 : ∑ i ∈ Finset.range L, s i = ∫ a, ∑ i ∈ Finset.range L, (b i a) ^ 2 ∂μ :=
      (integral_finsetSum _ (fun i _ => (hbm i).integrable_sq)).symm
    rw [h1]
    calc _ ≤ ∫ _a, M ^ 2 ∂μ :=
          integral_mono (integrable_finsetSum _ fun i _ => (hbm i).integrable_sq)
            (integrable_const _) (fun a => hbd a L)
      _ = M ^ 2 := by simp
  have hsumm : Summable s := summable_of_sum_range_le hs0 hsum
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑' k, s (k + N) < δ :=
    ((tendsto_order.1 (tendsto_sum_nat_add s)).2 δ hδ).exists
  refine ⟨N, fun L x hx => ?_⟩
  have htail : ∑ i ∈ Finset.Ico N L, s i ≤ δ := by
    rw [Finset.sum_Ico_eq_sum_range]
    have := Summable.sum_le_tsum (Finset.range (L - N)) (fun k _ => hs0 (k + N))
      ((summable_nat_add_iff N).2 hsumm)
    simp only [add_comm N] at *
    linarith
  set X2 := ∑ i ∈ Finset.range L, x i ^ 2 with hX2
  have hX2nn : 0 ≤ X2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hw : MemLp (fun y => ∑ i ∈ Finset.range L, x i * e i y) 2 μ := by
    have := memLp_finsetSum' (Finset.range L) (fun i _ => (he.memLp i).const_mul (x i))
    refine this.ae_eq (Filter.Eventually.of_forall fun y => ?_)
    simp
  have hF := (PDE.MFLinear.memLp_Phi H hw).1
  have hpt : ∀ a, (PDE.MFLinear.Phi gM ρ (fun y => ∑ i ∈ Finset.range L, x i * e i y) a) ^ 2 ≤
      X2 * ∑ i ∈ Finset.Ico N L, (b i a) ^ 2 := by
    intro a
    rw [e3_phi_sum H hb he L x a]
    have hsub : Finset.Ico N L ⊆ Finset.range L := fun i hi => by
      simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢; omega
    have h1 : ∑ i ∈ Finset.Ico N L, x i * b i a = ∑ i ∈ Finset.range L, x i * b i a := by
      refine Finset.sum_subset hsub fun i hi hni => ?_
      have : i < N := by
        simp only [Finset.mem_Ico, Finset.mem_range, not_and, not_lt] at hi hni
        by_contra hcon
        exact absurd (hni (not_lt.1 hcon)) (by omega)
      rw [hx i this, zero_mul]
    rw [hb_def] at h1
    simp only [hb_def] at *
    rw [← h1]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
  calc ∫ a, (PDE.MFLinear.Phi gM ρ (fun y => ∑ i ∈ Finset.range L, x i * e i y) a) ^ 2 ∂μ
      ≤ ∫ a, X2 * ∑ i ∈ Finset.Ico N L, (b i a) ^ 2 ∂μ :=
        integral_mono hF.integrable_sq
          ((integrable_finsetSum _ fun i _ => (hbm i).integrable_sq).const_mul _) hpt
    _ = X2 * ∑ i ∈ Finset.Ico N L, s i := by
        rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hbm i).integrable_sq)]
    _ ≤ X2 * δ := mul_le_mul_of_nonneg_left htail hX2nn
    _ = δ * X2 := mul_comm _ _

end HRS.MC.Sec7.E3Aux1

end
