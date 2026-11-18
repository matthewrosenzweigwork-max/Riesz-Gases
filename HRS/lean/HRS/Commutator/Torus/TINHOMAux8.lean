import HRS.Commutator.Torus.TINHOMAux7

/-!
# T-INHOM helpers, part 8: the high-velocity part `𝒞_{g_≤}(P_> v, b)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tinhom_homSqT_mono {t : ℝ} {F G : Lattice d → ℂ} (h : ∀ k, ‖F k‖ₑ ≤ ‖G k‖ₑ) :
    homSqT t F ≤ homSqT t G := by
  unfold homSqT
  refine ENNReal.tsum_le_tsum fun k => ?_
  split_ifs
  · exact le_rfl
  · gcongr
    exact h k

lemma tinhom_glo_fcoef (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    (i : Fin d) (k : Lattice d) :
    Torus.fcoef (fun x => gloForceT s η x i) k = ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k := by
  have hT2 : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊ (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) :=
    tkr_isTrigPoly hη (fun k hk => by
      intro h0; apply hk; simp [h0])
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold Torus.fcoef
  have : ∀ x : Torus d, Torus.mode (-k) x * ((gloForceT s η x i : ℝ) : ℂ) =
      Torus.mode (-k) x * HRS.PDE.Kern.trig
        (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) x := by
    intro x
    have e : ((gloForceT s η x i : ℝ) : ℂ) = HRS.PDE.Kern.trig
        (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) x := tkr_glo hd2 hs0 hsd1 hη x i
    rw [e]
  simp_rw [this]
  exact tkr_integral_trig hT2 k

theorem tinhom_glo_hi (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → ∀ b : Torus d → ℝ, Continuous b →
      (∀ k : Lattice d, η * Lattice.enorm k ≤ 1 / 8 → Torus.fcoef b k = 0) →
      ENNReal.ofReal |CcommFunT (gloForceT s η) (PgtT η v) b| ≤
        ENNReal.ofReal (C * K * η ^ ((d : ℝ) - s)) *
          tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef b k) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₁, hC₁, hvlo⟩ := tsamp_vlo_core hd hs0 hsd
  obtain ⟨CV, hCV, hvhi⟩ := tsamp_vhi_Lp_core hd hs0 hsd
  obtain ⟨Cu, hCu, husamp⟩ := tsamp_usample_core hd hs0 hsd
  obtain ⟨CL, hCL, hcore⟩ := tprod_core hd hs0 hsd
  obtain ⟨Cpot, hCpot, hpot⟩ := tsamp_potential_core hd hs0 hsd
  have hα : 0 < Whole.alphaE d s := by unfold Whole.alphaE; linarith
  set Ch : ℝ := (1 + 1 / (2 * Real.pi * (1 / 8)) ^ 2) ^ (Whole.alphaE d s) with hCh
  have hCh0 : 0 < Ch := by positivity
  set R : ℝ := Cpot * Ch ^ ((1 : ℝ) / 2) with hR
  have hR0 : 0 < R := by positivity
  refine ⟨2 * d * CL * (1 + Cu) * CV * R + 1, by positivity, ?_⟩
  intro η hη hη1 v K hT b hb hsupp
  have hT' := hvlo η hη hη1 v K hT
  obtain ⟨L, F, w, hL, hF, hLip, hrep, hw, hLF⟩ := tinhom_transport_data hT
  obtain ⟨L', F', hL', hF', hLip', -, hLF'⟩ := hT'
  have hKK : 0 ≤ K := by linarith
  have hvc : Continuous v := tsamp_lip_continuous hLip
  have hPleqc : Continuous (PleqT η v) := tsamp_lip_continuous hLip'
  have hVc : Continuous (PgtT η v) := by
    have : PgtT η v = fun z => v z - PleqT η v z := by funext z; unfold PgtT; rfl
    rw [this]; exact hvc.sub hPleqc
  have hVL : IsLipschitzVF (L + L') (PgtT η v) := by
    intro x y
    have h1 : PgtT η v x - PgtT η v y = (v x - v y) - (PleqT η v x - PleqT η v y) := by
      unfold PgtT; abel
    rw [h1]
    calc ‖(v x - v y) - (PleqT η v x - PleqT η v y)‖ ≤ ‖v x - v y‖ + ‖PleqT η v x - PleqT η v y‖ :=
          norm_sub_le _ _
      _ ≤ L * KernelGrad.tdist x y + L' * KernelGrad.tdist x y := add_le_add (hLip x y) (hLip' x y)
      _ = (L + L') * KernelGrad.tdist x y := by ring
  -- the pairing identity
  obtain ⟨hgm, hgW⟩ := tlowv_glo_W hd hs0 hsd hη
  have hFc := tsamp_gloForce_continuous hd hs0 hsd hη
  have hproj : ∀ i : Fin d, Continuous fun z : Euc d => z i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous
  have hgi : ∀ i : Fin d, Integrable (fun x => gloForceT s η x i) := fun i =>
    ((hproj i).comp hFc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP := tinhom_pairing hgm (tlowv_glo_odd hd hs0 hsd hη) hgW hgi (add_nonneg hL hL') hVL hVc hb
  -- the density and `u = ∇g_≤ * b`
  obtain ⟨Bb, hBb⟩ := ten_bound_of_continuous hb
  have hBb' : ∀ x, |b x| ≤ Bb := fun x => by simpa using hBb x
  have hfin := tlowv_ofDensity_finite b hb.measurable hBb'
  set σ : SMT d := SMT.ofDensity b with hσ
  set u : Torus d → Euc d := fun x => σ.convForce (gloForceT s η) x with hu
  have huc : Continuous u := tsamp_convForce_continuous hd hs0 hsd hη σ hfin
  have hui : ∀ i x, u x i = textConv (fun z => gloForceT s η z i) b x := fun i x =>
    tinhom_convForce_eq hd hs0 hsd hη hb x i
  have huic : ∀ i, Continuous fun x => u x i := fun i => (hproj i).comp huc
  have hVic : ∀ i, Continuous fun x => PgtT η v x i := fun i => (hproj i).comp hVc
  set h : Torus d → ℝ := fun x => inner ℝ (PgtT η v x) (u x) with hh
  have hhc : Continuous h := by
    have : h = fun x => ∑ i, PgtT η v x i * u x i := by
      funext x; simp only [hh]; rw [tlowv_inner_eq]
    rw [this]
    exact continuous_finsetSum _ fun i _ => (hVic i).mul (huic i)
  have hcc : CcommFunT (gloForceT s η) (PgtT η v) b = 2 * ∫ x, b x * h x := by
    rw [hP]
    congr 1
    have e : ∀ i : Fin d, ∫ x, b x * (PgtT η v x i * textConv (fun z => gloForceT s η z i) b x) =
        ∫ x, b x * (PgtT η v x i * u x i) := fun i =>
      integral_congr_ae (ae_of_all _ fun x => by beta_reduce; rw [hui i x])
    simp_rw [e]
    have hint : ∀ i : Fin d, Integrable (fun x => b x * (PgtT η v x i * u x i)) := fun i =>
      (hb.mul ((hVic i).mul (huic i))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [← integral_finset_sum _ (fun i _ => hint i)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hh]
    rw [tlowv_inner_eq, Finset.mul_sum]
  -- Fourier support of `u`
  have hsuppu : ∀ i (k : Lattice d), 2 < η * Lattice.enorm k → Torus.fcoef (fun x => u x i) k = 0 := by
    intro i k hk
    have hbi : Integrable b := (HRS.PDE.R2Aux.memLp_of_continuous_real hb).integrable (by norm_num)
    have hKi : Integrable (fun z => gloForceT s η z i) := hgi i
    have e : (fun x => u x i) = textConv (fun z => gloForceT s η z i) b := funext (hui i)
    rw [e, text_fcoef_conv hKi hbi, tinhom_glo_fcoef hd hs0 hsd hη, tkrChi_eq_zero hk.le hη]
    simp
  have hmemu : MemLp (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume := by
    obtain ⟨Bu, hBu⟩ := ten_bound_of_continuous (continuous_norm.comp huc)
    exact MemLp.of_bound (continuous_norm.comp huc).aestronglyMeasurable Bu
      (ae_of_all _ fun x => by simpa using hBu x)
  -- bounds
  obtain ⟨W, hWrep, hWnorm⟩ := hvhi η hη hη1 v L w F hF hL hLip hrep hw
  obtain ⟨U, hUrep, hUnorm, -⟩ := husamp η hη hη1 u huc hmemu hsuppu
  set Nu := eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume with hNu
  obtain ⟨hm2, hbound⟩ := hcore η hη hη1 Cu hCu.le (PgtT η v) W u U
    (ENNReal.ofReal (CV * η ^ (Whole.alphaE d s) * F)) Nu hVc huc hWrep hUrep hsuppu
    (le_trans le_self_add hWnorm) (le_trans le_add_self hWnorm) ENNReal.ofReal_ne_top le_rfl
    hmemu.eLpNorm_lt_top.ne hUnorm
  set Sh := tinhomS η (Whole.alphaE d s) (fun k => Torus.fcoef h k) with hSh
  set Sb := tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef b k) with hSb
  have hShb : Sh ^ ((1 : ℝ) / 2) ≤ (d : ℝ≥0∞) * (ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) *
      ENNReal.ofReal (CV * η ^ (Whole.alphaE d s) * F) * Nu) := by
    have e1 : sobSqT η (Whole.alphaE d s) (fun k => Torus.fcoef h k) = ENNReal.ofReal (η ^ d) * Sh := rfl
    rw [e1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hbound
    have e2 : ENNReal.ofReal (η ^ d) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (η ^ ((d : ℝ) / 2)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
      congr 1; ring
    rw [e2] at hbound
    have hpos : ENNReal.ofReal (η ^ ((d : ℝ) / 2)) ≠ 0 := by
      simpa using Real.rpow_pos_of_pos hη _
    exact (ENNReal.mul_le_mul_iff_right hpos ENNReal.ofReal_ne_top).1 hbound
  -- the potential estimate
  have hpotb := hpot η hη hη1 σ hfin
  have hhom : homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) ≤
      ENNReal.ofReal (Ch * η ^ (2 * Whole.alphaE d s)) * Sb := by
    have hcoef : ∀ k, σ.coef k = Torus.fcoef b k := tlowv_ofDensity_coef b hb.measurable hBb'
    refine (tinhom_homSqT_mono (G := fun k => Torus.fcoef b k) (fun k => ?_)).trans ?_
    · unfold lowFreqT
      rw [enorm_mul, hcoef k]
      have h0 : ‖(((Whole.chi ((η / 4) • Lattice.toEuc k) : ℝ)) : ℂ)‖ₑ ≤ 1 := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Whole.cmxFB_chi_nonneg _)]
        exact ENNReal.ofReal_le_one.2 (Whole.cmxFB_chi_le_one _)
      calc _ ≤ 1 * ‖Torus.fcoef b k‖ₑ := by gcongr
        _ = _ := one_mul _
    · exact tinhom_hom_le hη (by norm_num : (0 : ℝ) < 1 / 8) hα (fun k hk => hsupp k hk)
  have hNu : Nu ≤ ENNReal.ofReal (R * η ^ (Whole.alphaE d s)) * Sb ^ ((1 : ℝ) / 2) := by
    calc Nu ≤ ENNReal.ofReal Cpot * homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) ^ ((1 : ℝ) / 2) :=
          hpotb
      _ ≤ ENNReal.ofReal Cpot * (ENNReal.ofReal (Ch * η ^ (2 * Whole.alphaE d s)) * Sb) ^ ((1 : ℝ) / 2) := by
          gcongr
      _ = ENNReal.ofReal Cpot * (ENNReal.ofReal ((Ch * η ^ (2 * Whole.alphaE d s)) ^ ((1 : ℝ) / 2)) *
            Sb ^ ((1 : ℝ) / 2)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      _ = ENNReal.ofReal (R * η ^ (Whole.alphaE d s)) * Sb ^ ((1 : ℝ) / 2) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCpot.le]
          congr 2
          rw [hR, Real.mul_rpow hCh0.le (Real.rpow_nonneg hη.le _), ← Real.rpow_mul hη.le]
          have : 2 * Whole.alphaE d s * (1 / 2) = Whole.alphaE d s := by ring
          rw [this]; ring
  have hShb2 : Sh ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (d * CL * (1 + Cu) * (CV * η ^ (Whole.alphaE d s) * F) *
      (R * η ^ (Whole.alphaE d s))) * Sb ^ ((1 : ℝ) / 2) := by
    refine hShb.trans ?_
    calc (d : ℝ≥0∞) * (ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) *
          ENNReal.ofReal (CV * η ^ (Whole.alphaE d s) * F) * Nu)
        ≤ (d : ℝ≥0∞) * (ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) *
          ENNReal.ofReal (CV * η ^ (Whole.alphaE d s) * F) *
          (ENNReal.ofReal (R * η ^ (Whole.alphaE d s)) * Sb ^ ((1 : ℝ) / 2))) := by gcongr
      _ = ENNReal.ofReal (d * CL * (1 + Cu) * (CV * η ^ (Whole.alphaE d s) * F) *
            (R * η ^ (Whole.alphaE d s))) * Sb ^ ((1 : ℝ) / 2) := by
          have h1 : (1 : ℝ≥0∞) + ENNReal.ofReal Cu = ENNReal.ofReal (1 + Cu) := by
            rw [ENNReal.ofReal_add (by norm_num) hCu.le, ENNReal.ofReal_one]
          rw [h1]
          have hd0 : (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) := (ENNReal.ofReal_natCast d).symm
          rw [hd0]
          simp (disch := positivity) only [ENNReal.ofReal_mul]
          ring
  -- the final estimate
  have hSb2 : Sb ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2) = Sb := tinhom_sqrt_mul_sqrt Sb
  have hpair := tinhom_pairing_le (HRS.PDE.R2Aux.memLp_of_continuous_real hb) hm2 η (Whole.alphaE d s)
  have hex : (η ^ (Whole.alphaE d s)) * (η ^ (Whole.alphaE d s)) = η ^ ((d : ℝ) - s) := by
    rw [← Real.rpow_add hη]
    congr 1
    unfold Whole.alphaE; ring
  rw [hcc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hηe : 0 < η ^ ((d : ℝ) - s) := Real.rpow_pos_of_pos hη _
  set X : ℝ := d * CL * (1 + Cu) * (CV * η ^ (Whole.alphaE d s) * F) * (R * η ^ (Whole.alphaE d s)) with hX
  have hX0 : 0 ≤ X := by positivity
  calc ENNReal.ofReal 2 * ENNReal.ofReal |∫ x, b x * h x|
      ≤ ENNReal.ofReal 2 * (Sb ^ ((1 : ℝ) / 2) * Sh ^ ((1 : ℝ) / 2)) := by gcongr
    _ ≤ ENNReal.ofReal 2 * (Sb ^ ((1 : ℝ) / 2) *
          (ENNReal.ofReal X * Sb ^ ((1 : ℝ) / 2))) := by gcongr
    _ = ENNReal.ofReal (2 * X) * Sb := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          calc ENNReal.ofReal 2 * (Sb ^ ((1 : ℝ) / 2) * (ENNReal.ofReal X * Sb ^ ((1 : ℝ) / 2)))
              = ENNReal.ofReal 2 * ENNReal.ofReal X * (Sb ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2)) := by ring
            _ = _ := by rw [hSb2]
    _ ≤ ENNReal.ofReal ((2 * d * CL * (1 + Cu) * CV * R + 1) * K * η ^ ((d : ℝ) - s)) * Sb := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have e : 2 * X = 2 * d * CL * (1 + Cu) * CV * R * F * η ^ ((d : ℝ) - s) := by
            rw [hX, ← hex]; ring
          rw [e]
          have h1 : 0 ≤ F * η ^ ((d : ℝ) - s) := by positivity
          have hFK : F ≤ K := by linarith
          have hc : 0 ≤ 2 * d * CL * (1 + Cu) * CV * R := by positivity
          have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFK hηe.le) hc
          nlinarith [mul_nonneg hKK hηe.le]

end HRS.Commutator.TorusNote
