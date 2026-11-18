import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovInterpAux2
import HRS.MS.MovOscAux5
import HRS.MS.S67NlBD11

/-!
# S6.7 nonlinear breakdown, packet 12: real-order mixed oscillator product

`s67bd_product_real`.  Route: for fixed `u ∈ Σ^b`, Stein interpolation (`mo_interp_osc`) between the integer
orders `⌊r⌋, ⌊r⌋ + 1 ≤ b` (packet 11) for the linear map `f ↦ u f` on the Hermite span gives the bound at order `r`
on the span.  Then `w ∈ Σ^r` is approximated by its Hermite partial sums; the coefficients of `u w_k` converge to
those of `u w` because `u` is essentially bounded (packet 11 sup bound + a.e. subsequence), and the bound passes to
the limit on finite coefficient sets.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- Essential sup bound of an arbitrary `Σ^b` function, `b > d/2`. -/
theorem s67bd12_ess_bound (d : ℕ) (b : ℝ) (hb : (d : ℝ) / 2 < b) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ u : Euc d → ℝ, MemOsc b u →
      ∀ᵐ x ∂(volume : Measure (Euc d)), |u x| ≤ M0 * oscNorm b u := by
  obtain ⟨M0, hM0, hM⟩ := s67bd11_sup_bound d b hb
  refine ⟨M0, hM0, fun u hu => ?_⟩
  have hb0 : 0 ≤ b := le_trans (by positivity) hb.le
  have hu0 : MemOsc 0 u := (mo_mono hb0 hu).1
  choose U hU using fun k => mn_pSum_schwartz u k
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (s67bd11_pSum_L2 hu0)).exists_seq_tendsto_ae
  have hbd : ∀ (k : ℕ) (x : Euc d), |mo_pSum u k x| ≤ M0 * oscNorm b u := by
    intro k x
    have h1 := hM (U k) x
    rw [hU k] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (mo_pSum_oscNorm_le b hu k).2 hM0)
  filter_upwards [hae] with x hx
  exact le_of_tendsto hx.abs (Eventually.of_forall fun k => hbd (ns k) x)

theorem s67bd12_memOsc_span {f : Euc d → ℝ} (hf : f ∈ mo_Hspan d) (m : ℝ) : MemOsc m f := by
  obtain ⟨S, c, rfl⟩ := mova3_exists_comb hf
  exact mo_hsum_memOsc m S c

theorem s67bd_product_real (d : ℕ) (b r : ℝ) (hb : (d : ℝ) / 2 < b)
    (hr : 0 ≤ r) (hrb : r ≤ b - 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u w : Euc d → ℝ, MemOsc b u → MemOsc r w →
      MemOsc r (fun x => u x * w x) ∧
      oscNorm r (fun x => u x * w x) ≤ C * oscNorm b u * oscNorm r w := by
  obtain ⟨M0, hM0, hess⟩ := s67bd12_ess_bound d b hb
  have hn0 : ((⌊r⌋₊ : ℕ) : ℝ) ≤ r := Nat.floor_le hr
  have hn0r : r < ((⌊r⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one r
  obtain ⟨C0, hC0, h0⟩ := s67bd_product_integer d b ⌊r⌋₊ hb (by linarith)
  obtain ⟨C1, hC1, h1⟩ := s67bd_product_integer d b (⌊r⌋₊ + 1) hb (by push_cast; linarith)
  refine ⟨max C0 C1, le_max_of_le_left hC0, fun u w hu hw => ?_⟩
  set C : ℝ := max C0 C1 with hCdef
  have hC : 0 ≤ C := le_max_of_le_left hC0
  have ou : 0 ≤ oscNorm b u := Real.sqrt_nonneg _
  have ow : 0 ≤ oscNorm r w := Real.sqrt_nonneg _
  set Mu : ℝ := C * oscNorm b u with hMu
  have hMu0 : 0 ≤ Mu := mul_nonneg hC ou
  -- step 1: the bound on the Hermite span, by interpolation
  have hA0 : ∀ f ∈ mo_Hspan d, MemOsc ((⌊r⌋₊ : ℕ) : ℝ) (fun x => u x * f x) ∧
      oscNorm ((⌊r⌋₊ : ℕ) : ℝ) (fun x => u x * f x) ≤ Mu * oscNorm ((⌊r⌋₊ : ℕ) : ℝ) f := by
    intro f hf
    obtain ⟨m1, m2⟩ := h0 u f hu (s67bd12_memOsc_span hf _)
    refine ⟨m1, m2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) ou)
      (Real.sqrt_nonneg _)
  have hA1 : ∀ f ∈ mo_Hspan d, MemOsc (((⌊r⌋₊ + 1 : ℕ)) : ℝ) (fun x => u x * f x) ∧
      oscNorm (((⌊r⌋₊ + 1 : ℕ)) : ℝ) (fun x => u x * f x) ≤
        Mu * oscNorm (((⌊r⌋₊ + 1 : ℕ)) : ℝ) f := by
    intro f hf
    obtain ⟨m1, m2⟩ := h1 u f hu (s67bd12_memOsc_span hf _)
    refine ⟨m1, m2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) ou)
      (Real.sqrt_nonneg _)
  have hlin : ∀ f ∈ mo_Hspan d, ∀ g ∈ mo_Hspan d, ∀ a : ℝ,
      (fun x => u x * (a • f + g) x) = a • (fun x => u x * f x) + (fun x => u x * g x) := by
    intro f _ g _ a
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hθ : r - ((⌊r⌋₊ : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hspan := fun f hf => mo_interp_osc (d := d) (T := fun f x => u x * f x)
    (fun f hf g hg a => hlin f hf g hg a) (fun f hf => (hA0 f hf).1.1) hA0 hA1 hθ f hf
  have e : (1 - (r - ((⌊r⌋₊ : ℕ) : ℝ))) * ((⌊r⌋₊ : ℕ) : ℝ) +
      (r - ((⌊r⌋₊ : ℕ) : ℝ)) * (((⌊r⌋₊ + 1 : ℕ)) : ℝ) = r := by push_cast; ring
  have hMpow : Mu ^ (1 - (r - ((⌊r⌋₊ : ℕ) : ℝ))) * Mu ^ (r - ((⌊r⌋₊ : ℕ) : ℝ)) = Mu := by
    rw [← Real.rpow_add' hMu0 (by norm_num)]
    simp
  have hspan' : ∀ f ∈ mo_Hspan d, MemOsc r (fun x => u x * f x) ∧
      oscNorm r (fun x => u x * f x) ≤ Mu * oscNorm r f := by
    intro f hf
    have := hspan f hf
    rw [e, hMpow] at this
    exact this
  -- step 2: extension to `w`
  have hw0 : MemOsc 0 w := (mo_mono hr hw).1
  have hubd : ∀ᵐ x ∂(volume : Measure (Euc d)), |u x| ≤ M0 * oscNorm b u := hess u hu
  set M : ℝ := M0 * oscNorm b u with hMdef
  have hM' : 0 ≤ M := mul_nonneg hM0 ou
  have hQ : MemLp (fun x => u x * w x) 2 (volume : Measure (Euc d)) := by
    refine hw.1.of_le_mul (c := M)
      (hu.1.aestronglyMeasurable.mul hw.1.aestronglyMeasurable) ?_
    filter_upwards [hubd] with x hx
    simpa [Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_right hx (abs_nonneg (w x))
  have hwconv : Tendsto (fun k : ℕ => eLpNorm (mo_pSum w k - w) 2 (volume : Measure (Euc d)))
      atTop (𝓝 0) := s67bd11_pSum_L2 hw0
  have hwconv' : Tendsto (fun k : ℕ =>
      (eLpNorm (mo_pSum w k - w) 2 (volume : Measure (Euc d))).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hwconv
    simpa [Function.comp_def] using this
  have hpw : ∀ k, MemLp (mo_pSum w k) 2 (volume : Measure (Euc d)) :=
    fun k => mova2_hsum_memLp _ _
  have hcoef : ∀ α : MultiIndex d, Tendsto (fun k : ℕ =>
      hermiteCoeff (fun x => u x * mo_pSum w k x) α) atTop
      (𝓝 (hermiteCoeff (fun x => u x * w x) α)) := by
    intro α
    have hG : ∀ k, MemLp (fun x => u x * (mo_pSum w k x - w x)) 2 (volume : Measure (Euc d)) := by
      intro k
      refine ((hpw k).sub hw.1).of_le_mul (c := M)
        (hu.1.aestronglyMeasurable.mul ((hpw k).aestronglyMeasurable.sub hw.1.aestronglyMeasurable)) ?_
      filter_upwards [hubd] with x hx
      simpa [Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_right hx (abs_nonneg (mo_pSum w k x - w x))
    have hsplit : ∀ k, hermiteCoeff (fun x => u x * mo_pSum w k x) α =
        hermiteCoeff (fun x => u x * w x) α +
          hermiteCoeff (fun x => u x * (mo_pSum w k x - w x)) α := by
      intro k
      rw [← s67bd11_coeff_add hQ (hG k)]
      congr 1
      funext x
      ring
    have hGt : Tendsto (fun k : ℕ => hermiteCoeff (fun x => u x * (mo_pSum w k x - w x)) α)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (by simpa using hwconv'.const_mul M)
      rw [Real.norm_eq_abs]
      refine (s67bd11_coeff_le (hG k) α).trans ?_
      have h1 : eLpNorm (fun x => u x * (mo_pSum w k x - w x)) 2 (volume : Measure (Euc d)) ≤
          ENNReal.ofReal M * eLpNorm (mo_pSum w k - w) 2 (volume : Measure (Euc d)) :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hG k).aestronglyMeasurable
          (by
            filter_upwards [hubd] with x hx
            simpa [Real.norm_eq_abs, abs_mul] using
              mul_le_mul_of_nonneg_right hx (abs_nonneg (mo_pSum w k x - w x))) 2
      have h2 : eLpNorm (mo_pSum w k - w) 2 (volume : Measure (Euc d)) ≠ ⊤ :=
        ((hpw k).sub hw.1).eLpNorm_ne_top
      have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2) h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM'] at h3
    have := (tendsto_const_nhds (x := hermiteCoeff (fun x => u x * w x) α)).add hGt
    simpa [hsplit] using this
  set B : ℝ := Mu * oscNorm r w with hB
  have hB0 : 0 ≤ B := mul_nonneg hMu0 ow
  have hP : ∀ k : ℕ, MemOsc r (fun x => u x * mo_pSum w k x) ∧
      oscNorm r (fun x => u x * mo_pSum w k x) ≤ B := by
    intro k
    obtain ⟨m1, m2⟩ := hspan' (mo_pSum w k) (mova3_comb_mem _ _)
    exact ⟨m1, m2.trans (mul_le_mul_of_nonneg_left (mo_pSum_oscNorm_le r hw k).2 hMu0)⟩
  have hnn : ∀ (f : Euc d → ℝ) (α : MultiIndex d),
      0 ≤ oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 := fun f α =>
    mul_nonneg (Real.rpow_nonneg (oscEigenvalue_pos α).le _) (sq_nonneg _)
  have hfin : ∀ S : Finset (MultiIndex d),
      ∑ α ∈ S, oscEigenvalue d α ^ r * hermiteCoeff (fun x => u x * w x) α ^ 2 ≤ B ^ 2 := by
    intro S
    have hlim : Tendsto (fun k : ℕ => ∑ α ∈ S, oscEigenvalue d α ^ r *
        hermiteCoeff (fun x => u x * mo_pSum w k x) α ^ 2) atTop
        (𝓝 (∑ α ∈ S, oscEigenvalue d α ^ r * hermiteCoeff (fun x => u x * w x) α ^ 2)) :=
      tendsto_finsetSum _ fun α _ => ((hcoef α).pow 2).const_mul _
    refine le_of_tendsto' hlim fun k => ?_
    obtain ⟨hm, hk⟩ := hP k
    calc ∑ α ∈ S, oscEigenvalue d α ^ r * hermiteCoeff (fun x => u x * mo_pSum w k x) α ^ 2
        ≤ ∑' α, oscEigenvalue d α ^ r * hermiteCoeff (fun x => u x * mo_pSum w k x) α ^ 2 :=
          hm.2.sum_le_tsum S fun α _ => hnn _ α
      _ = oscNorm r (fun x => u x * mo_pSum w k x) ^ 2 := by
          unfold oscNorm
          rw [Real.sq_sqrt (tsum_nonneg fun α => hnn _ α)]
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hk 2
  have hsum : Summable fun α : MultiIndex d =>
      oscEigenvalue d α ^ r * hermiteCoeff (fun x => u x * w x) α ^ 2 :=
    summable_of_sum_le (fun α => hnn _ α) hfin
  refine ⟨⟨hQ, hsum⟩, ?_⟩
  unfold oscNorm
  calc Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ r *
        hermiteCoeff (fun x => u x * w x) α ^ 2) ≤ Real.sqrt (B ^ 2) :=
        Real.sqrt_le_sqrt (Real.tsum_le_of_sum_le (fun α => hnn _ α) hfin)
    _ = B := Real.sqrt_sq hB0
    _ = _ := by rw [hB, hMu]

end HRS.MS.BreakdownS67
