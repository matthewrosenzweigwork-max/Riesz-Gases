import HRS.MS.MainRdPathAux7
import HRS.MP.RdInit

/-!
# S.A.9, packet P3b (tools for the tails of the initial field)

* `sa9_varpi_sum_le`: a tail version of `mri_varpi_sum`: `∑_ℓ ‖ψ_ℓ‖²_{H^m(ϖ)} ≤ ∑_z w_z K_c ∫_{B(z,2)} g` whenever
  `∑_ℓ |D^{≤m}ψ_ℓ(x)|² ≤ g(x)`;
* `sa9_tail_cmp`: comparison of tails of two real sequences with square-summable difference;
* `sa9_exists_lam`, `sa9_bessel`: Bessel inequality for the coordinate functionals `g ↦ ∂^α (P φ_g)(x)`;
* `sa9_partial_le_cb`: partial derivatives are bounded by the `C_b^j` norm.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit

variable {d : ℕ}

theorem sa9_varpi_sum_le {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (m : ℕ) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (ψ : ℕ → Euc d → ℝ), (∀ ℓ, ContDiff ℝ m (ψ ℓ)) → ∀ g : Euc d → ℝ≥0∞,
      Measurable g → (∀ x, ∑' ℓ, ENNReal.ofReal (mriG m (ψ ℓ) x) ≤ g x) →
      ∑' ℓ, varpiNormE m χ (ψ ℓ) ^ 2 ≤ ∑' z : Fin d → ℤ,
        ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
          (ENNReal.ofReal Kc * ∫⁻ x in Metric.ball (cellPt d z) 2, g x) := by
  obtain ⟨M, hM0, hM⟩ := mri_cutoff_bound hχ m
  refine ⟨mriKc d m M, mriKc_nonneg d m M, ?_⟩
  intro ψ hψ g hg hb
  have hcell : ∀ ℓ, varpiNormE m χ (ψ ℓ) ^ 2 ≤ ∑' z : Fin d → ℤ,
      ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (mriKc d m M * ∫ x in Metric.ball (cellPt d z) 2, mriG m (ψ ℓ) x) := by
    intro ℓ
    rw [mri_varpi_sq]
    refine ENNReal.tsum_le_tsum fun z => ?_
    refine mul_le_mul' le_rfl ?_
    obtain ⟨hmem, hnn, hle⟩ := mri_cell_bound hχ hM0 m hM (hψ ℓ) (cellPt d z)
    unfold HRS.Whole.sobolevNormE
    simp only [hmem, ite_true]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hnn]
    exact ENNReal.ofReal_le_ofReal hle
  have hint : ∀ ℓ z, IntegrableOn (mriG m (ψ ℓ)) (Metric.ball (cellPt d z) 2) volume := fun ℓ z =>
    ((mriG_continuous (hψ ℓ)).continuousOn.integrableOn_compact (isCompact_closedBall _ 2)).mono_set
      Metric.ball_subset_closedBall
  have hl : ∀ ℓ z, ENNReal.ofReal (mriKc d m M * ∫ x in Metric.ball (cellPt d z) 2, mriG m (ψ ℓ) x) =
      ENNReal.ofReal (mriKc d m M) * ∫⁻ x in Metric.ball (cellPt d z) 2, ENNReal.ofReal (mriG m (ψ ℓ) x) := by
    intro ℓ z
    rw [ENNReal.ofReal_mul (mriKc_nonneg d m M),
      ofReal_integral_eq_lintegral_ofReal (hint ℓ z) (ae_of_all _ fun x => mriG_nonneg m _ x)]
  calc ∑' ℓ, varpiNormE m χ (ψ ℓ) ^ 2
      ≤ ∑' ℓ, ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        (ENNReal.ofReal (mriKc d m M) *
          ∫⁻ x in Metric.ball (cellPt d z) 2, ENNReal.ofReal (mriG m (ψ ℓ) x)) :=
        ENNReal.tsum_le_tsum fun ℓ => (hcell ℓ).trans (le_of_eq (tsum_congr fun z => by rw [hl ℓ z]))
    _ = ∑' z : Fin d → ℤ, ∑' ℓ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        (ENNReal.ofReal (mriKc d m M) *
          ∫⁻ x in Metric.ball (cellPt d z) 2, ENNReal.ofReal (mriG m (ψ ℓ) x)) := ENNReal.tsum_comm
    _ = ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        (ENNReal.ofReal (mriKc d m M) *
          ∫⁻ x in Metric.ball (cellPt d z) 2, ∑' ℓ, ENNReal.ofReal (mriG m (ψ ℓ) x)) := by
        refine tsum_congr fun z => ?_
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, lintegral_tsum]
        intro ℓ
        exact (ENNReal.measurable_ofReal.comp (mriG_continuous (hψ ℓ)).measurable).aemeasurable
    _ ≤ _ := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
        exact lintegral_mono fun x => hb x

theorem sa9_tail_cmp (a b : ℕ → ℝ) (L : ℕ) {D : ℝ}
    (hD : ∀ n, ∑ l ∈ Finset.range n, (a l - b l) ^ 2 ≤ D ^ 2) :
    ∑' l, ENNReal.ofReal ((a (l + L)) ^ 2) ≤
      2 * ∑' l, ENNReal.ofReal ((b (l + L)) ^ 2) + 2 * ENNReal.ofReal (D ^ 2) := by
  have hpt : ∀ l, ENNReal.ofReal ((a (l + L)) ^ 2) ≤
      2 * ENNReal.ofReal ((b (l + L)) ^ 2) + 2 * ENNReal.ofReal ((a (l + L) - b (l + L)) ^ 2) := by
    intro l
    have : (a (l + L)) ^ 2 ≤ 2 * (b (l + L)) ^ 2 + 2 * (a (l + L) - b (l + L)) ^ 2 := by
      nlinarith [sq_nonneg (a (l + L) - 2 * b (l + L))]
    calc ENNReal.ofReal ((a (l + L)) ^ 2) ≤ ENNReal.ofReal (2 * (b (l + L)) ^ 2 + 2 * (a (l + L) - b (l + L)) ^ 2) :=
          ENNReal.ofReal_le_ofReal this
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_mul (by norm_num)]
          simp
  have hsum : ∑' l, ENNReal.ofReal ((a l - b l) ^ 2) ≤ ENNReal.ofReal (D ^ 2) := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun n => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => sq_nonneg _]
    exact ENNReal.ofReal_le_ofReal (hD n)
  calc ∑' l, ENNReal.ofReal ((a (l + L)) ^ 2)
      ≤ ∑' l, (2 * ENNReal.ofReal ((b (l + L)) ^ 2) + 2 * ENNReal.ofReal ((a (l + L) - b (l + L)) ^ 2)) :=
        ENNReal.tsum_le_tsum hpt
    _ = 2 * ∑' l, ENNReal.ofReal ((b (l + L)) ^ 2) + 2 * ∑' l, ENNReal.ofReal ((a (l + L) - b (l + L)) ^ 2) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective L)
          (fun l => ENNReal.ofReal ((a l - b l) ^ 2))).trans hsum

theorem sa9_exists_lam {i : ℕ} (P : (Euc d → ℝ) → (Euc d → ℝ)) (idx : Fin i → Fin d) (x : Euc d)
    (hadd : ∀ a b : mhn_Hc d, P (mhn_phi (a + b)) = P (mhn_phi a) + P (mhn_phi b))
    (hsmul : ∀ (c : ℝ) (a : mhn_Hc d), P (mhn_phi (c • a)) = c • P (mhn_phi a))
    (hcd : ∀ a : mhn_Hc d, ContDiff ℝ i (P (mhn_phi a))) :
    ∃ Λ : mhn_Hc d →ₗ[ℝ] ℝ, ∀ g, Λ g = partialDeriv idx (P (mhn_phi g)) x := by
  refine ⟨⟨⟨fun g => partialDeriv idx (P (mhn_phi g)) x, ?_⟩, ?_⟩, fun g => rfl⟩
  · intro a b
    show partialDeriv idx (P (mhn_phi (a + b))) x = _
    rw [hadd, mri_partialDeriv_add (hcd a) (hcd b)]
  · intro c a
    show partialDeriv idx (P (mhn_phi (c • a))) x = c * _
    rw [hsmul, mri_partialDeriv_smul (hcd a)]

theorem sa9_bessel {q : ℕ} (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {i : ℕ} (P : (Euc d → ℝ) → (Euc d → ℝ)) (idx : Fin i → Fin d) (x : Euc d)
    (hadd : ∀ a b : mhn_Hc d, P (mhn_phi (a + b)) = P (mhn_phi a) + P (mhn_phi b))
    (hsmul : ∀ (c : ℝ) (a : mhn_Hc d), P (mhn_phi (c • a)) = c • P (mhn_phi a))
    (hcd : ∀ a : mhn_Hc d, ContDiff ℝ i (P (mhn_phi a))) {C : ℝ}
    (hC : ∀ g : mhn_Hc d, |partialDeriv idx (P (mhn_phi g)) x| ≤ C * HRS.Whole.sobolevNorm ((q : ℕ) : ℝ) (mhn_phi g))
    (n : ℕ) :
    ∑ l ∈ Finset.range n, (partialDeriv idx (P (mhn_phi (h l))) x) ^ 2 ≤ C ^ 2 := by
  obtain ⟨Λ, hΛ⟩ := sa9_exists_lam P idx x hadd hsmul hcd
  have := mri_bessel ((q : ℕ) : ℝ) h hP Λ C (fun g => by rw [hΛ g, mhn_norm_rep]; exact hC g) n
  simpa [hΛ] using this

theorem sa9_partial_le_cb {j : ℕ} {f : Euc d → ℝ} (hf : MemCb j f) {i : ℕ} (hi : i ≤ j) (idx : Fin i → Fin d)
    (x : Euc d) : |partialDeriv idx f x| ≤ cbNorm j f := by
  refine (mri_abs_partialDeriv_le idx f x).trans ?_
  have h0 : ‖iteratedFDeriv ℝ i f x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ i f z‖ :=
    le_ciSup (hf.2 i hi) x
  refine h0.trans ?_
  unfold cbNorm
  exact Finset.single_le_sum (f := fun j' => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j' f z‖)
    (fun j' _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

end HRS.MS.MainRdPath
