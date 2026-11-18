import HRS.Commutator.Torus.TLOWVAux4

/-!
# T-LOWV helpers, part 5: oddness and `L¹` bounds for the force kernels; `L²` norm of the low-frequency
density in terms of `homSqT`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

/-- The statement of `nrs_T` (`(4.knowncomm)`), as a hypothesis. -/
def TlowvNRS (d : ℕ) (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
    ∀ a : Torus d → ℝ, Torus.IsSmooth a → ∫ x, a x = 0 →
      ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) v a| ≤
        ENNReal.ofReal (C * K) * homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef a k)

lemma tlowv_tkrCI_neg (s : ℝ) (i : Fin d) (k : Lattice d) : tkrCI d s i (-k) = -tkrCI d s i k := by
  unfold tkrCI
  rw [rieszCoeff_neg]
  simp only [Pi.neg_apply, Int.cast_neg]
  ring

lemma tlowv_tkrChi_neg (η : ℝ) (k : Lattice d) : tkrChi η (-k) = tkrChi η k := by
  unfold tkrChi
  rw [ten_toEuc_neg, smul_neg, Whole.cmxFB_chi_neg]

/-- `∇g_≤` is odd. -/
lemma tlowv_glo_odd (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    (z : Torus d) : gloForceT s η (-z) = -gloForceT s η z := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  ext i
  have h1 := tkr_glo hd2 hs0 hsd1 hη z i
  have h2 := tkr_glo hd2 hs0 hsd1 hη (-z) i
  change ((gloForceT s η (-z) i : ℝ) : ℂ) = _ at h2
  have h3 : HRS.PDE.Kern.trig (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) (-z) =
      -HRS.PDE.Kern.trig (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) z := by
    unfold HRS.PDE.Kern.trig
    simp_rw [ten2_mode_neg_arg]
    rw [← (Equiv.neg (Lattice d)).tsum_eq (fun k => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k *
      Torus.mode (-k) z)]
    simp only [Equiv.neg_apply, neg_neg, tlowv_tkrChi_neg, tlowv_tkrCI_neg]
    rw [← tsum_neg]
    exact tsum_congr fun k => by ring
  have h4 : ((gloForceT s η (-z) i : ℝ) : ℂ) = ((-gloForceT s η z i : ℝ) : ℂ) := by
    have e1 : ((gloForceT s η z i : ℝ) : ℂ) = _ := h1
    rw [h2, h3, ← e1]
    push_cast; ring
  have := Complex.ofReal_injective h4
  simpa using this

/-- `∇g_>` is odd. -/
lemma tlowv_ghi_odd (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    (z : Torus d) : ghiForceT s η (-z) = -ghiForceT s η z := by
  unfold ghiForceT
  rw [tlowv_glo_odd hd hs0 hsd hη z, HRS.KernelGrad.periodicRieszGrad_neg_of_lt (by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith) z]
  abel

/-- `‖|x|∇g_>‖_{L¹} ≲ η^{d-s}` (`(3.kernelremainder)` with `q = 1`). -/
lemma tlowv_ghi_W (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      Integrable (tlowvW (ghiForceT s η : Torus d → Euc d)) ∧
        ∫ z, tlowvW (ghiForceT s η : Torus d → Euc d) z ≤ C * η ^ ((d : ℝ) - s) := by
  obtain ⟨C, hC, h⟩ := tkr_kernel_remainder_Lq hd hs0 hsd ⊤ 1 (by simp) (by simp)
  refine ⟨C, hC, fun η hη hη1 => ?_⟩
  obtain ⟨hmem, hnorm⟩ := h η hη hη1
  have hint : Integrable (tlowvW (ghiForceT s η : Torus d → Euc d)) :=
    memLp_one_iff_integrable.1 hmem
  refine ⟨hint, ?_⟩
  have hnn : ∀ z, 0 ≤ tlowvW (ghiForceT s η : Torus d → Euc d) z := tlowvW_nonneg _
  have h1 : eLpNorm (tlowvW (ghiForceT s η : Torus d → Euc d)) 1 volume =
      ENNReal.ofReal (∫ z, tlowvW (ghiForceT s η : Torus d → Euc d) z) := by
    rw [eLpNorm_one_eq_lintegral_enorm hint.1,
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
    exact lintegral_congr fun z => Real.enorm_eq_ofReal (hnn z)
  have h2 : eLpNorm (tlowvW (ghiForceT s η : Torus d → Euc d)) 1 volume ≤
      ENNReal.ofReal (C * η ^ ((d : ℝ) - s)) := by
    refine hnorm.trans (le_of_eq ?_)
    simp
  have h3 : ENNReal.ofReal (∫ z, tlowvW (ghiForceT s η : Torus d → Euc d) z) ≤
      ENNReal.ofReal (C * η ^ ((d : ℝ) - s)) := by
    rw [← h1]; exact h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

/-- Parseval for a real continuous function, as an `ℝ≥0∞` identity with `∫ a²`. -/
lemma tlowv_sum_sq {H : Torus d → ℝ} (hH : MemLp H 2 volume) :
    ∑' k : Lattice d, ‖Torus.fcoef H k‖ₑ ^ 2 = ENNReal.ofReal (∫ t, (H t) ^ 2) := by
  have hC : MemLp (fun x => ((H x : ℝ) : ℂ)) 2 volume := hH.ofReal
  have hP := HRS.PDE.hasSum_parseval _ _ hC hC
  have hcoef : ∀ k, Torus.funFourierCoeff (fun x => ((H x : ℝ) : ℂ)) k = Torus.fcoef H k := by
    intro k
    rw [HRS.PDE.funFourierCoeff_eq_int]
    rfl
  have e1 : ∀ k : Lattice d, conj (Torus.funFourierCoeff (fun x => ((H x : ℝ) : ℂ)) k) *
      Torus.funFourierCoeff (fun x => ((H x : ℝ) : ℂ)) k = ((‖Torus.fcoef H k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [hcoef k, Complex.conj_mul']
    push_cast
    ring
  have e2 : ∀ t : Torus d, conj (((H t : ℝ) : ℂ)) * ((H t : ℝ) : ℂ) = (((H t) ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [e1, e2] at hP
  have hP' : HasSum (fun k : Lattice d => ‖Torus.fcoef H k‖ ^ 2) (∫ t, (H t) ^ 2) := by
    rw [integral_complex_ofReal] at hP
    exact Complex.hasSum_ofReal.1 hP
  rw [← hP'.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hP'.summable]
  refine tsum_congr fun k => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- The `L²` norm of a density with coefficients supported in `0 < η|k| < R` and zero mean, in terms of
the homogeneous `Ḣ^{-α}` sum. -/
lemma tlowv_L2_le_hom {a : Torus d → ℝ} (ha : MemLp a 2 volume) {η R : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hc0 : Torus.fcoef a 0 = 0)
    (hsupp : ∀ k : Lattice d, η * Lattice.enorm k ≥ R → Torus.fcoef a k = 0) {e : ℝ} (he : 0 < e) :
    ENNReal.ofReal (∫ t, (a t) ^ 2) ≤
      ENNReal.ofReal ((2 * Real.pi * R / η) ^ e) *
        homSqT (-(e / 2)) (fun k => Torus.fcoef a k) := by
  rw [← tlowv_sum_sq ha]
  unfold homSqT
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [hc0]
  · rw [if_neg hk]
    by_cases hz : Torus.fcoef a k = 0
    · simp [hz]
    · have hlt : η * Lattice.enorm k < R := by
        by_contra hcon
        exact hz (hsupp k (not_lt.1 hcon))
      have hen : 0 < Lattice.enorm k := ten_enorm_pos hk
      have hbase : 0 < 2 * Real.pi * Lattice.enorm k := by positivity
      have hle : 2 * Real.pi * Lattice.enorm k ≤ 2 * Real.pi * R / η := by
        rw [le_div_iff₀ hη]
        have := mul_lt_mul_of_pos_left hlt (by positivity : (0 : ℝ) < 2 * Real.pi)
        nlinarith
      have hmain : 1 ≤ (2 * Real.pi * R / η) ^ e * (2 * Real.pi * Lattice.enorm k) ^ (2 * (-(e / 2))) := by
        have e1 : (2 * Real.pi * Lattice.enorm k) ^ (2 * (-(e / 2))) =
            ((2 * Real.pi * Lattice.enorm k) ^ e)⁻¹ := by
          rw [show 2 * (-(e / 2)) = -e by ring, Real.rpow_neg hbase.le]
        rw [e1]
        have hp : 0 < (2 * Real.pi * Lattice.enorm k) ^ e := Real.rpow_pos_of_pos hbase _
        rw [← div_eq_mul_inv, le_div_iff₀ hp, one_mul]
        exact Real.rpow_le_rpow hbase.le hle he.le
      calc ‖Torus.fcoef a k‖ₑ ^ 2 = ENNReal.ofReal 1 * ‖Torus.fcoef a k‖ₑ ^ 2 := by simp
        _ ≤ ENNReal.ofReal ((2 * Real.pi * R / η) ^ e *
              (2 * Real.pi * Lattice.enorm k) ^ (2 * (-(e / 2)))) * ‖Torus.fcoef a k‖ₑ ^ 2 := by
            gcongr
        _ = _ := by
            rw [ENNReal.ofReal_mul (by positivity), mul_assoc]

end HRS.Commutator.TorusNote
