import HRS.Commutator.Torus.TINHOMAux9

/-!
# T-INHOM, part 10: trigonometric polynomials (Lemma 4.2 for finitely many modes)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

/-- Spectral truncation of an integrable real function to `|k| ≤ r`, as a continuous real function. -/
lemma tinhom_trunc {a : Torus d → ℝ} (ha : Integrable a) (r : ℝ) :
    ∃ f : Torus d → ℝ, Continuous f ∧
      ∀ k, Torus.fcoef f k = if Lattice.enorm k ≤ r then Torus.fcoef a k else 0 := by
  set c : Lattice d → ℂ := fun k => if Lattice.enorm k ≤ r then Torus.fcoef a k else 0 with hc
  have hT : HRS.PDE.IsTrigPoly ⌈r + 1⌉₊ c :=
    HRS.HDB.isTrigPoly_of_enorm_lt (R := r + 1) (fun k hk => by
      by_contra hcon
      apply hk
      have : ¬ Lattice.enorm k ≤ r := by linarith
      simp [hc, this])
  have hr : HRS.PDE.IsRealCoeff c := by
    intro k
    simp only [hc, tlowv_enorm_neg]
    split_ifs
    · exact tprod_fcoef_conj ha k
    · simp
  obtain ⟨f, hfc, -, hfco⟩ := tsamp_real_trig hr hT
  exact ⟨f, hfc, fun k => hfco k⟩

lemma tinhom_conv_add {K f g : Torus d → ℝ} (hK : Integrable K) (hf : Continuous f) (hg : Continuous g)
    (x : Torus d) :
    textConv K (fun y => f y + g y) x = textConv K f x + textConv K g x := by
  obtain ⟨Bf, hBf⟩ := ten_bound_of_continuous hf
  obtain ⟨Bg, hBg⟩ := ten_bound_of_continuous hg
  have hK' : Integrable (fun y => K (x - y)) := hK.comp_sub_left x
  have h1 : Integrable (fun y => K (x - y) * f y) :=
    hK'.bdd_mul (c := Bf) hf.aestronglyMeasurable (ae_of_all _ fun y => by simpa using hBf y) |>.congr
      (ae_of_all _ fun y => by simp [mul_comm])
  have h2 : Integrable (fun y => K (x - y) * g y) :=
    hK'.bdd_mul (c := Bg) hg.aestronglyMeasurable (ae_of_all _ fun y => by simpa using hBg y) |>.congr
      (ae_of_all _ fun y => by simp [mul_comm])
  unfold textConv
  rw [← integral_add h1 h2]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  ring

lemma tinhom_enorm_trunc_le {a f : Torus d → ℝ} {r : ℝ}
    (hf : ∀ k, Torus.fcoef f k = if Lattice.enorm k ≤ r then Torus.fcoef a k else 0) (k : Lattice d) :
    ‖Torus.fcoef f k‖ₑ ≤ ‖Torus.fcoef a k‖ₑ := by
  rw [hf k]
  split_ifs
  · exact le_rfl
  · simp

theorem tinhom_trig (hn : TlowvNRS d s) (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → ∀ a : Torus d → ℝ, Continuous a → ∀ R : ℝ,
      (∀ k : Lattice d, R ≤ Lattice.enorm k → Torus.fcoef a k = 0) →
      ENNReal.ofReal |CcommFunT (ghiForceT s η) v a| ≤
        ENNReal.ofReal (C * K * η ^ ((d : ℝ) - s)) *
          tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef a k) := by
  obtain ⟨Cb, hCb, hbpart⟩ := tinhom_b_part hn hd hs0 hsd
  obtain ⟨Cc, hCc, hcross⟩ := tinhom_cross_bound hd hs0 hsd
  obtain ⟨CW, hCW, hW⟩ := tlowv_ghi_W hd hs0 hsd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by linarith
  refine ⟨Cb + 2 * Cc, by positivity, ?_⟩
  intro η hη hη1 v K hT a ha R hR
  have hTc := hT
  obtain ⟨L, F, hL, hF, hLip, -, hLF⟩ := hT
  have hKK : 0 ≤ K := by linarith
  have hvc : Continuous v := tsamp_lip_continuous hLip
  have hai : Integrable a := (HRS.PDE.R2Aux.memLp_of_continuous_real ha).integrable (by norm_num)
  -- the low part `a₀` and the high part `b`
  obtain ⟨a₀, ha₀c, ha₀co⟩ := tinhom_trunc hai ((1 / 8) / η)
  have hle : ∀ k : Lattice d, Lattice.enorm k ≤ (1 / 8) / η ↔ η * Lattice.enorm k ≤ 1 / 8 := by
    intro k
    rw [le_div_iff₀ hη, mul_comm]
  set b : Torus d → ℝ := fun x => a x - a₀ x with hb
  have hbc : Continuous b := ha.sub ha₀c
  have ha₀i : Integrable a₀ := (HRS.PDE.R2Aux.memLp_of_continuous_real ha₀c).integrable (by norm_num)
  have hbi : Integrable b := hai.sub ha₀i
  have hbco : ∀ k, Torus.fcoef b k = if Lattice.enorm k ≤ (1 / 8) / η then 0 else Torus.fcoef a k := by
    intro k
    rw [text_fcoef_sub hai ha₀i k, ha₀co k]
    split_ifs <;> simp
  have hbsupp : ∀ k : Lattice d, η * Lattice.enorm k ≤ 1 / 8 → Torus.fcoef b k = 0 := by
    intro k hk
    rw [hbco k, if_pos ((hle k).2 hk)]
  have ha₀supp : ∀ k : Lattice d, 1 / 8 < η * Lattice.enorm k → Torus.fcoef a₀ k = 0 := by
    intro k hk
    rw [ha₀co k, if_neg (by rw [hle k]; linarith)]
  have hbsm : Torus.IsSmooth b := by
    refine tprod_smooth_of_box hbc ⌈R⌉₊ (fun k hk => ?_)
    rw [hbco k]
    split_ifs with h1
    · rfl
    · by_contra hne
      apply hk
      have hlt : Lattice.enorm k < R := by
        by_contra hcon
        exact hne (hR k (not_lt.1 hcon))
      intro i
      have h2 : |(k i : ℝ)| ≤ Lattice.enorm k := HRS.KernelAux.abs_coord_le_enorm k i
      have h3 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
      have : |(k i : ℝ)| ≤ (⌈R⌉₊ : ℝ) := by linarith [h2, hlt, h3]
      exact_mod_cast this
  have hbmean : ∫ x, b x = 0 := by
    have h0 := Torus.fcoef_zero b
    rw [hbco 0] at h0
    have hen : Lattice.enorm (0 : Lattice d) = 0 := text_enorm_zero
    rw [if_pos (by rw [hen]; positivity)] at h0
    have : Torus.mean b = 0 := by exact_mod_cast h0.symm
    exact this
  -- the identity `𝒞(a) = 𝒞(b) + 2 · cross`
  obtain ⟨hWi, hWb⟩ := hW η hη hη1
  have hgm := tkr_ghi_measurable hd2 hs0 hsd1 hη
  have hgo := tlowv_ghi_odd hd hs0 hsd hη
  have hKi : ∀ i : Fin d, Integrable (fun x => ghiForceT s η x i) := fun i => tinhom_ghi_int hd hs0 hsd hη i
  have hpa := tinhom_pairing hgm hgo hWi hKi hL hLip hvc ha
  have hpb := tinhom_pairing hgm hgo hWi hKi hL hLip hvc hbc
  have hcv : ∀ i : Fin d, ∀ᵐ x ∂(volume : Measure (Torus d)),
      textConv (fun z => ghiForceT s η z i) a x = textConv (fun z => ghiForceT s η z i) b x := by
    intro i
    have h0 := tinhom_conv_low_ae hd hs0 hsd hη i ha₀i (fun k hk => ha₀supp k (by linarith))
    filter_upwards [h0] with x hx
    have e : a = fun y => a₀ y + b y := by funext y; simp only [hb]; ring
    have := tinhom_conv_add (tinhom_ghi_int hd hs0 hsd hη i) ha₀c hbc x
    rw [e, this]
    simpa using hx
  have hproj : ∀ i : Fin d, Continuous fun z : Euc d => z i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous
  have hdiff : ∀ i : Fin d, (∫ x, a x * (v x i * textConv (fun z => ghiForceT s η z i) a x)) -
      (∫ x, b x * (v x i * textConv (fun z => ghiForceT s η z i) b x)) =
      ∫ x, a₀ x * (v x i * textConv (fun z => ghiForceT s η z i) b x) := by
    intro i
    set cvb := textConv (fun z => ghiForceT s η z i) b with hcvb
    have hKm := tinhom_ghi_meas hd hs0 hsd hη i
    obtain ⟨Bb, hBb⟩ := ten_bound_of_continuous hbc
    have hBb' : ∀ x, |b x| ≤ Bb := fun x => by simpa using hBb x
    have hcvm : Measurable cvb := tinhom_conv_meas hKm hbc.measurable
    have hcvb : ∀ x, |cvb x| ≤ (∫ z, |ghiForceT s η z i|) * Bb := fun x =>
      tinhom_conv_bdd (tinhom_ghi_int hd hs0 hsd hη i) hBb' x
    have hvi : Continuous fun x => v x i := (hproj i).comp hvc
    have I1 := tinhom_int3 ha hvi hcvm hcvb
    have I2 := tinhom_int3 hbc hvi hcvm hcvb
    have e1 : ∫ x, a x * (v x i * textConv (fun z => ghiForceT s η z i) a x) =
        ∫ x, a x * (v x i * cvb x) :=
      integral_congr_ae ((hcv i).mono fun x hx => by beta_reduce; rw [hx])
    rw [e1, ← integral_sub I1 I2]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hb]
    ring
  have hid : CcommFunT (ghiForceT s η) v a = CcommFunT (ghiForceT s η) v b +
      2 * ∑ i, ∫ x, a₀ x * (v x i * textConv (fun z => ghiForceT s η z i) b x) := by
    rw [hpa, hpb, ← Finset.sum_congr rfl (fun i _ => hdiff i), Finset.sum_sub_distrib]
    ring
  -- bounds
  have hB := hbpart η hη hη1 v K hTc b hbc hbsm hbmean hbsupp
  have hX := hcross η hη hη1 v K hTc a₀ b ha₀c hbc ha₀supp
  set Sa := tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef a k) with hSa
  have hS0 : tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef a₀ k) ≤ Sa :=
    tinhomS_mono (fun k => tinhom_enorm_trunc_le ha₀co k)
  have hSb : tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef b k) ≤ Sa := by
    refine tinhomS_mono (fun k => ?_)
    rw [hbco k]
    split_ifs
    · simp
    · exact le_rfl
  have hQ : tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef a₀ k) ^ ((1 : ℝ) / 2) *
      tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef b k) ^ ((1 : ℝ) / 2) ≤ Sa := by
    calc _ ≤ Sa ^ ((1 : ℝ) / 2) * Sa ^ ((1 : ℝ) / 2) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hS0 (by norm_num)) (ENNReal.rpow_le_rpow hSb (by norm_num))
      _ = Sa := tinhom_sqrt_mul_sqrt Sa
  set Cr := ∑ i, ∫ x, a₀ x * (v x i * textConv (fun z => ghiForceT s η z i) b x) with hCr
  have hηe : 0 < η ^ ((d : ℝ) - s) := Real.rpow_pos_of_pos hη _
  rw [hid]
  have h1 : ENNReal.ofReal |CcommFunT (ghiForceT s η) v b + 2 * Cr| ≤
      ENNReal.ofReal |CcommFunT (ghiForceT s η) v b| + ENNReal.ofReal 2 * ENNReal.ofReal |Cr| := by
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((abs_add_le _ _).trans ?_)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc ENNReal.ofReal |CcommFunT (ghiForceT s η) v b + 2 * Cr|
      ≤ ENNReal.ofReal |CcommFunT (ghiForceT s η) v b| + ENNReal.ofReal 2 * ENNReal.ofReal |Cr| := h1
    _ ≤ ENNReal.ofReal (Cb * K * η ^ ((d : ℝ) - s)) * Sa +
          ENNReal.ofReal 2 * (ENNReal.ofReal (Cc * K * η ^ ((d : ℝ) - s)) * Sa) := by
        refine add_le_add (hB.trans ?_) (mul_le_mul' le_rfl (hX.trans ?_))
        · exact mul_le_mul' le_rfl hSb
        · exact mul_le_mul' le_rfl hQ
    _ = ENNReal.ofReal (Cb * K * η ^ ((d : ℝ) - s) + 2 * (Cc * K * η ^ ((d : ℝ) - s))) * Sa := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (p := 2) (by norm_num)]
        ring
    _ = ENNReal.ofReal ((Cb + 2 * Cc) * K * η ^ ((d : ℝ) - s)) * Sa := by
        congr 2; ring

end HRS.Commutator.TorusNote
