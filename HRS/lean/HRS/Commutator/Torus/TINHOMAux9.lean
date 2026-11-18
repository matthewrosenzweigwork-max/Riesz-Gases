import HRS.Commutator.Torus.TINHOMAux8

/-!
# T-INHOM, part 9: the high part `b` of the density (mean zero, Fourier support `η|k| > 1/8`):
`𝒞_{g_>}(v,b) = 𝒞_g(v,b) - 𝒞_{g_≤}(P_≤ v,b) - 𝒞_{g_≤}(P_> v,b)`, each bounded by `K η^{d-s} ‖b‖²_{H^{-α}}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tlowv_commKernel_addV (F : Torus d → Euc d) (V₁ V₂ : Torus d → Euc d) (x y : Torus d) :
    commKernel F (fun z => V₁ z + V₂ z) x y = commKernel F V₁ x y + commKernel F V₂ x y := by
  unfold commKernel
  split_ifs
  · simp
  · have : V₁ x + V₂ x - (V₁ y + V₂ y) = (V₁ x - V₁ y) + (V₂ x - V₂ y) := by abel
    rw [this, inner_add_left]

/-- Additivity of the commutator form in the velocity. -/
lemma tinhom_CcommFun_addV {F : Torus d → Euc d} (hFm : Measurable F) (hodd : ∀ z, F (-z) = -F z)
    (hW : Integrable (tlowvW F)) {V₁ V₂ : Torus d → Euc d} {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hV₁ : IsLipschitzVF L₁ V₁) (hV₂ : IsLipschitzVF L₂ V₂) (hc₁ : Continuous V₁)
    (hc₂ : Continuous V₂) {a : Torus d → ℝ} (hac : Continuous a) :
    CcommFunT F (fun z => V₁ z + V₂ z) a = CcommFunT F V₁ a + CcommFunT F V₂ a := by
  have ha2 : Integrable (fun x => a x ^ 2) :=
    (HRS.PDE.R2Aux.memLp_of_continuous_real hac).integrable_sq
  have hI1 := (tlowv_L2_form hFm hodd hW hL₁ hV₁ hc₁ hac.aestronglyMeasurable hac.aestronglyMeasurable
    ha2 ha2 one_pos).1
  have hI2 := (tlowv_L2_form hFm hodd hW hL₂ hV₂ hc₂ hac.aestronglyMeasurable hac.aestronglyMeasurable
    ha2 ha2 one_pos).1
  have hsum : Integrable (fun p : Torus d × Torus d =>
      commKernel F (fun z => V₁ z + V₂ z) p.1 p.2 * a p.1 * a p.2) (volume.prod volume) := by
    refine (hI1.add hI2).congr (Eventually.of_forall fun p => ?_)
    show commKernel F V₁ p.1 p.2 * a p.1 * a p.2 + commKernel F V₂ p.1 p.2 * a p.1 * a p.2 =
      commKernel F (fun z => V₁ z + V₂ z) p.1 p.2 * a p.1 * a p.2
    rw [tlowv_commKernel_addV]
    ring
  rw [tlowv_CcommFun_eq hsum, tlowv_CcommFun_eq hI1, tlowv_CcommFun_eq hI2, ← integral_add hI1 hI2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tlowv_commKernel_addV]
  ring

lemma tinhom_lowFreq_le {t η L : ℝ} (F : Lattice d → ℂ) :
    homSqT t (lowFreqT η L F) ≤ homSqT t F := by
  refine tinhom_homSqT_mono (fun k => ?_)
  unfold lowFreqT
  rw [enorm_mul]
  have h0 : ‖(((Whole.chi ((η / L) • Lattice.toEuc k) : ℝ)) : ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Whole.cmxFB_chi_nonneg _)]
    exact ENNReal.ofReal_le_one.2 (Whole.cmxFB_chi_le_one _)
  calc _ ≤ 1 * ‖F k‖ₑ := by gcongr
    _ = _ := one_mul _

theorem tinhom_b_part (hn : TlowvNRS d s) (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → ∀ b : Torus d → ℝ, Continuous b → Torus.IsSmooth b →
      ∫ x, b x = 0 → (∀ k : Lattice d, η * Lattice.enorm k ≤ 1 / 8 → Torus.fcoef b k = 0) →
      ENNReal.ofReal |CcommFunT (ghiForceT s η) v b| ≤
        ENNReal.ofReal (C * K * η ^ ((d : ℝ) - s)) *
          tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef b k) := by
  obtain ⟨Cn, hCn, hnrs⟩ := id hn
  obtain ⟨Clv, hClv, hlow⟩ := tlowv_main hn hd hs0 hsd
  obtain ⟨Chi, hChi, hhi⟩ := tinhom_glo_hi hd hs0 hsd
  obtain ⟨C₁, hC₁, hvlo⟩ := tsamp_vlo_core hd hs0 hsd
  obtain ⟨CW, hCW, hW⟩ := tlowv_ghi_W hd hs0 hsd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by linarith
  have hα : 0 < Whole.alphaE d s := by unfold Whole.alphaE; linarith
  set Ch : ℝ := (1 + 1 / (2 * Real.pi * (1 / 8)) ^ 2) ^ (Whole.alphaE d s) with hCh
  have hCh0 : 0 < Ch := by positivity
  refine ⟨(Cn + Clv) * Ch + Chi + 1, by positivity, ?_⟩
  intro η hη hη1 v K hT b hb hbs hmean hsupp
  have hT' := hvlo η hη hη1 v K hT
  have hTc := hT
  obtain ⟨L, F, hL, hF, hLip, -, hLF⟩ := hT
  obtain ⟨L', F', hL', hF', hLip', -, hLF'⟩ := hT'
  have hKK : 0 ≤ K := by linarith
  have hvc : Continuous v := tsamp_lip_continuous hLip
  have hV0c : Continuous (PleqT η v) := tsamp_lip_continuous hLip'
  have hPgtc : Continuous (PgtT η v) := by
    have : PgtT η v = fun z => v z - PleqT η v z := by funext z; unfold PgtT; rfl
    rw [this]; exact hvc.sub hV0c
  have hVL : IsLipschitzVF (L + L') (PgtT η v) := by
    intro x y
    have h1 : PgtT η v x - PgtT η v y = (v x - v y) - (PleqT η v x - PleqT η v y) := by
      unfold PgtT; abel
    rw [h1]
    calc ‖(v x - v y) - (PleqT η v x - PleqT η v y)‖ ≤ ‖v x - v y‖ + ‖PleqT η v x - PleqT η v y‖ :=
          norm_sub_le _ _
      _ ≤ L * KernelGrad.tdist x y + L' * KernelGrad.tdist x y := add_le_add (hLip x y) (hLip' x y)
      _ = (L + L') * KernelGrad.tdist x y := by ring
  -- force splitting `∇g = ∇g_≤ + ∇g_>`
  obtain ⟨hgm, hgW⟩ := tlowv_glo_W hd hs0 hsd hη
  obtain ⟨hWi, hWb⟩ := hW η hη hη1
  have hgh := tkr_ghi_measurable hd2 hs0 hsd1 hη
  have hadd := tlowv_CcommFun_add hgm (tlowv_glo_odd hd hs0 hsd hη) hgW hgh
    (tlowv_ghi_odd hd hs0 hsd hη) hWi hL hLip hvc hb
  have hG : (fun z => gloForceT s η z + ghiForceT s η z) = periodicRieszGrad d s := by
    funext z; unfold ghiForceT; abel
  rw [hG] at hadd
  -- velocity splitting `v = P_≤ v + P_> v`
  have hv_split : (fun z => PleqT η v z + PgtT η v z) = v := by
    funext z; unfold PgtT; abel
  have haddV := tinhom_CcommFun_addV hgm (tlowv_glo_odd hd hs0 hsd hη) hgW hL' (add_nonneg hL hL')
    hLip' hVL hV0c hPgtc hb
  rw [hv_split] at haddV
  -- the three bounds
  obtain ⟨Bb, hBb⟩ := ten_bound_of_continuous hb
  have hBb' : ∀ x, |b x| ≤ Bb := fun x => by simpa using hBb x
  have hfin := tlowv_ofDensity_finite b hb.measurable hBb'
  have hcoef : ∀ k, (SMT.ofDensity b).coef k = Torus.fcoef b k := tlowv_ofDensity_coef b hb.measurable hBb'
  have hmass : (SMT.ofDensity b).mass = 0 := by
    unfold SMT.mass
    rw [ten_int_ofDensity b (fun _ => 1) hb.measurable (by simpa using
      (HRS.PDE.R2Aux.memLp_of_continuous_real hb).integrable (by norm_num))]
    simp [hmean]
  set Sb := tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef b k) with hSb
  have hhom : homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef b k) ≤
      ENNReal.ofReal (Ch * η ^ (2 * Whole.alphaE d s)) * Sb :=
    tinhom_hom_le hη (by norm_num : (0 : ℝ) < 1 / 8) hα (fun k hk => hsupp k hk)
  have hηe : 0 < η ^ ((d : ℝ) - s) := Real.rpow_pos_of_pos hη _
  have h2α : η ^ (2 * Whole.alphaE d s) = η ^ ((d : ℝ) - s) := by
    congr 1; unfold Whole.alphaE; ring
  rw [h2α] at hhom
  -- (i) `𝒞_g(v,b)`
  have hB1 : ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) v b| ≤
      ENNReal.ofReal (Cn * Ch * K * η ^ ((d : ℝ) - s)) * Sb := by
    refine (hnrs v K hTc b hbs hmean).trans ?_
    calc ENNReal.ofReal (Cn * K) * homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef b k)
        ≤ ENNReal.ofReal (Cn * K) * (ENNReal.ofReal (Ch * η ^ ((d : ℝ) - s)) * Sb) := by gcongr
      _ = ENNReal.ofReal (Cn * Ch * K * η ^ ((d : ℝ) - s)) * Sb := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring
  -- (ii) `𝒞_{g_≤}(P_≤ v,b)`
  have hFc := tsamp_gloForce_continuous hd hs0 hsd hη
  have hB2 : ENNReal.ofReal |CcommFunT (gloForceT s η) (PleqT η v) b| ≤
      ENNReal.ofReal (Clv * Ch * K * η ^ ((d : ℝ) - s)) * Sb := by
    rw [← tlowv_pair2_density hFc hL' hLip' hV0c hb]
    refine (hlow η hη hη1 v K hTc (SMT.ofDensity b) hfin hmass).trans ?_
    have e : (SMT.ofDensity b).coef = fun k => Torus.fcoef b k := funext hcoef
    rw [e]
    calc ENNReal.ofReal (Clv * K) * homSqT (-Whole.alphaE d s) (lowFreqT η 4 fun k => Torus.fcoef b k)
        ≤ ENNReal.ofReal (Clv * K) * homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef b k) := by
          gcongr
          exact tinhom_lowFreq_le _
      _ ≤ ENNReal.ofReal (Clv * K) * (ENNReal.ofReal (Ch * η ^ ((d : ℝ) - s)) * Sb) := by gcongr
      _ = ENNReal.ofReal (Clv * Ch * K * η ^ ((d : ℝ) - s)) * Sb := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring
  -- (iii) `𝒞_{g_≤}(P_> v,b)`
  have hB3 := hhi η hη hη1 v K hTc b hb (fun k hk => hsupp k hk)
  -- combination
  have hid : CcommFunT (ghiForceT s η) v b =
      CcommFunT (periodicRieszGrad d s) v b - CcommFunT (gloForceT s η) (PleqT η v) b -
        CcommFunT (gloForceT s η) (PgtT η v) b := by
    linarith
  rw [hid]
  set X := CcommFunT (periodicRieszGrad d s) v b
  set Y := CcommFunT (gloForceT s η) (PleqT η v) b
  set Z := CcommFunT (gloForceT s η) (PgtT η v) b
  have habs : |X - Y - Z| ≤ |X| + |Y| + |Z| := by
    have h1 := abs_sub (X - Y) Z
    have h2 := abs_sub X Y
    linarith
  have h1 : ENNReal.ofReal |X - Y - Z| ≤ ENNReal.ofReal |X| + ENNReal.ofReal |Y| + ENNReal.ofReal |Z| := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal habs
  calc ENNReal.ofReal |X - Y - Z| ≤ ENNReal.ofReal |X| + ENNReal.ofReal |Y| + ENNReal.ofReal |Z| := h1
    _ ≤ ENNReal.ofReal (Cn * Ch * K * η ^ ((d : ℝ) - s)) * Sb +
          ENNReal.ofReal (Clv * Ch * K * η ^ ((d : ℝ) - s)) * Sb +
          ENNReal.ofReal (Chi * K * η ^ ((d : ℝ) - s)) * Sb := add_le_add (add_le_add hB1 hB2) hB3
    _ = ENNReal.ofReal (Cn * Ch * K * η ^ ((d : ℝ) - s) + Clv * Ch * K * η ^ ((d : ℝ) - s) +
          Chi * K * η ^ ((d : ℝ) - s)) * Sb := by
        rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (((Cn + Clv) * Ch + Chi + 1) * K * η ^ ((d : ℝ) - s)) * Sb := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have : 0 ≤ K * η ^ ((d : ℝ) - s) := by positivity
        nlinarith

end HRS.Commutator.TorusNote
