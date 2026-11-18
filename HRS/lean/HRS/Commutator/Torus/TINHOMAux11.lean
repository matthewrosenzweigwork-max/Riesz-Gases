import HRS.Commutator.Torus.TINHOMAux10

/-!
# T-INHOM, part 11: Lemma 4.2 on the torus for `a ∈ L²` by density of trigonometric polynomials
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

/-- Spectral truncations approximate an `L²` function. -/
lemma tinhom_approx {a : Torus d → ℝ} (ha : MemLp a 2 volume) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℝ) (aN : Torus d → ℝ), Continuous aN ∧
      (∀ k, Torus.fcoef aN k = if Lattice.enorm k ≤ r then Torus.fcoef a k else 0) ∧
      ∫ x, (a x - aN x) ^ 2 ≤ δ := by
  have hai : Integrable a := ha.integrable (by norm_num)
  have hsumA := tlowv_sum_sq ha
  -- the tails
  set f : Lattice d → ℝ≥0∞ := fun k => ‖Torus.fcoef a k‖ₑ ^ 2 with hf
  set F : ℕ → Lattice d → ℝ≥0∞ := fun N k => if Lattice.enorm k ≤ (N : ℝ) then 0 else f k with hF
  have hfin : ∑' k, f k ≠ ⊤ := by rw [hsumA]; exact ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun N : ℕ => ∑' k, F N k) atTop (𝓝 0) := by
    letI : MeasurableSpace (Lattice d) := ⊤
    haveI : MeasurableSingletonClass (Lattice d) := ⟨fun _ => trivial⟩
    have h := tendsto_lintegral_of_dominated_convergence (μ := (Measure.count : Measure (Lattice d)))
      (F := F) (f := fun _ => (0 : ℝ≥0∞)) f (fun N => measurable_from_top)
      (fun N => Eventually.of_forall fun k => by
        simp only [hF]; split_ifs
        · exact bot_le
        · exact le_rfl)
      (by rw [lintegral_count]; exact hfin)
      (Eventually.of_forall fun k => by
        refine tendsto_atTop_of_eventually_const (i₀ := ⌈Lattice.enorm k⌉₊) (fun N hN => ?_)
        have : Lattice.enorm k ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
        simp [hF, this])
    simpa [lintegral_count] using h
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := by simpa using hδ
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
  obtain ⟨aN, haNc, haNco⟩ := tinhom_trunc hai (N : ℝ)
  refine ⟨N, aN, haNc, haNco, ?_⟩
  have haNi : Integrable aN := (HRS.PDE.R2Aux.memLp_of_continuous_real haNc).integrable (by norm_num)
  have hdm : MemLp (fun x => a x - aN x) 2 volume := ha.sub (HRS.PDE.R2Aux.memLp_of_continuous_real haNc)
  have hs := tlowv_sum_sq hdm
  have hco : ∀ k, Torus.fcoef (fun x => a x - aN x) k = if Lattice.enorm k ≤ (N : ℝ) then 0 else Torus.fcoef a k := by
    intro k
    rw [text_fcoef_sub hai haNi k, haNco k]
    split_ifs <;> simp
  have h2 : ENNReal.ofReal (∫ x, (a x - aN x) ^ 2) = ∑' k, F N k := by
    rw [← hs]
    refine tsum_congr fun k => ?_
    rw [hco k]
    simp only [hF, hf]
    split_ifs <;> simp
  have h3 : ENNReal.ofReal (∫ x, (a x - aN x) ^ 2) ≤ ENNReal.ofReal δ := by rw [h2]; exact hN.le
  exact (ENNReal.ofReal_le_ofReal_iff hδ.le).1 h3

theorem tinhom_main (hn : TlowvNRS d s) (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → ∀ a : Torus d → ℝ, MemLp a 2 volume →
        ENNReal.ofReal |CcommFunT (ghiForceT s η) v a| ≤
          ENNReal.ofReal (C * K) *
            (ENNReal.ofReal (η ^ (-s)) * sobSqT η (-Whole.alphaE d s) (fun k => Torus.fcoef a k)) := by
  obtain ⟨Ct, hCt, htrig⟩ := tinhom_trig hn hd hs0 hsd
  obtain ⟨CW, hCW, hW⟩ := tlowv_ghi_W hd hs0 hsd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by linarith
  refine ⟨Ct, hCt, ?_⟩
  intro η hη hη1 v K hT a ha
  have hTc := hT
  obtain ⟨L, F, hL, hF, hLip, -, hLF⟩ := hT
  have hKK : 0 ≤ K := by linarith
  have hvc : Continuous v := tsamp_lip_continuous hLip
  set Sa := tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef a k) with hSa
  -- the target in the form `ofReal (C K η^{d-s}) * Sa`
  have hconv : ENNReal.ofReal (Ct * K) * (ENNReal.ofReal (η ^ (-s)) *
      sobSqT η (-Whole.alphaE d s) (fun k => Torus.fcoef a k)) =
      ENNReal.ofReal (Ct * K * η ^ ((d : ℝ) - s)) * Sa := by
    rw [tinhom_sobSqT_eq]
    have hp1 : 0 ≤ η ^ (-s) := Real.rpow_nonneg hη.le _
    have hp2 : 0 ≤ η ^ d := by positivity
    calc ENNReal.ofReal (Ct * K) * (ENNReal.ofReal (η ^ (-s)) * (ENNReal.ofReal (η ^ d) * Sa))
        = (ENNReal.ofReal (Ct * K) * ENNReal.ofReal (η ^ (-s)) * ENNReal.ofReal (η ^ d)) * Sa := by ring
      _ = ENNReal.ofReal (Ct * K * η ^ (-s) * η ^ d) * Sa := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (Ct * K * η ^ ((d : ℝ) - s)) * Sa := by
          congr 2
          have : η ^ ((d : ℝ) - s) = η ^ (-s) * η ^ d := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hη]
            congr 1; ring
          rw [this]; ring
  rw [hconv]
  obtain ⟨hWi, hWb⟩ := hW η hη hη1
  have hgm := tkr_ghi_measurable hd2 hs0 hsd1 hη
  have hgo := tlowv_ghi_odd hd hs0 hsd hη
  set W₁ : ℝ := ∫ z, tlowvW (ghiForceT s η : Torus d → Euc d) z with hW₁
  have hW₁0 : 0 ≤ W₁ := integral_nonneg (tlowvW_nonneg _)
  have ha2 : Integrable (fun x => a x ^ 2) := ha.integrable_sq
  set A2 : ℝ := ∫ x, a x ^ 2 with hA2
  have hA20 : 0 ≤ A2 := integral_nonneg fun x => sq_nonneg _
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  set M : ℝ := L * W₁ * (1 + A2) with hM
  have hM0 : 0 ≤ M := by positivity
  set ε' : ℝ := (ε : ℝ) / (M + 1) with hε'
  have hε0 : (0 : ℝ) < ε := by exact_mod_cast hε
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨r, aN, haNc, haNco, hδ⟩ := tinhom_approx ha (δ := ε' ^ 2) (by positivity)
  -- Part A for `aN`
  have hAN := htrig η hη hη1 v K hTc aN haNc (r + 1) (fun k hk => by
    rw [haNco k, if_neg (by linarith)])
  have hSN : tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef aN k) ≤ Sa :=
    tinhomS_mono (fun k => tinhom_enorm_trunc_le haNco k)
  have hAN' : ENNReal.ofReal |CcommFunT (ghiForceT s η) v aN| ≤
      ENNReal.ofReal (Ct * K * η ^ ((d : ℝ) - s)) * Sa := hAN.trans (mul_le_mul' le_rfl hSN)
  -- continuity of the form
  have hmemN : MemLp aN 2 volume := HRS.PDE.R2Aux.memLp_of_continuous_real haNc
  have hN2 : Integrable (fun x => aN x ^ 2) := hmemN.integrable_sq
  have hAN2 : ∫ x, aN x ^ 2 ≤ A2 := by
    have e1 := tlowv_sum_sq hmemN
    have e2 := tlowv_sum_sq ha
    have : ENNReal.ofReal (∫ x, aN x ^ 2) ≤ ENNReal.ofReal A2 := by
      rw [← e1, hA2, ← e2]
      refine ENNReal.tsum_le_tsum fun k => ?_
      gcongr
      exact tinhom_enorm_trunc_le haNco k
    exact (ENNReal.ofReal_le_ofReal_iff hA20).1 this
  have hcont := tlowv_Ccomm_cont hgm hgo hWi hL hLip hvc ha.aestronglyMeasurable
    hmemN.aestronglyMeasurable ha2 hN2 hε'0 hδ
  have hbd : |CcommFunT (ghiForceT s η) v a - CcommFunT (ghiForceT s η) v aN| ≤ (ε : ℝ) := by
    refine hcont.trans ?_
    have h1 : L * W₁ * ε' * (2 + A2 + ∫ x, aN x ^ 2) / 2 ≤ M * ε' := by
      rw [hM]
      have : 0 ≤ L * W₁ * ε' := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (show 2 + A2 + ∫ x, aN x ^ 2 ≤ 2 * (1 + A2) by linarith) this]
    refine h1.trans ?_
    rw [hε']
    have hM1 : 0 < M + 1 := by positivity
    rw [mul_div_assoc']
    rw [div_le_iff₀ hM1]
    nlinarith
  have hfinal : |CcommFunT (ghiForceT s η) v a| ≤ |CcommFunT (ghiForceT s η) v aN| + (ε : ℝ) := by
    have := abs_sub_abs_le_abs_sub (CcommFunT (ghiForceT s η) v a) (CcommFunT (ghiForceT s η) v aN)
    linarith
  calc ENNReal.ofReal |CcommFunT (ghiForceT s η) v a|
      ≤ ENNReal.ofReal (|CcommFunT (ghiForceT s η) v aN| + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal |CcommFunT (ghiForceT s η) v aN| + ENNReal.ofReal (ε : ℝ) :=
        ENNReal.ofReal_add (abs_nonneg _) hε0.le
    _ ≤ ENNReal.ofReal (Ct * K * η ^ ((d : ℝ) - s)) * Sa + (ε : ℝ≥0∞) := by
        rw [ENNReal.ofReal_coe_nnreal]
        exact add_le_add hAN' le_rfl

end HRS.Commutator.TorusNote
