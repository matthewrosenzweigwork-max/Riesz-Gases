import HRS.Commutator.Torus.TINHOMAux5

/-!
# T-INHOM helpers, part 6: the cross term `∑_i ∫ a₀ v_i (K_i * b)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tinhom_int3 {a f g : Torus d → ℝ} (ha : Continuous a) (hf : Continuous f) (hg : Measurable g)
    {Bg : ℝ} (hBg : ∀ x, |g x| ≤ Bg) : Integrable (fun x => a x * (f x * g x)) := by
  obtain ⟨Ba, hBa⟩ := ten_bound_of_continuous ha
  obtain ⟨Bf, hBf⟩ := ten_bound_of_continuous hf
  refine ten_integrable_of_bdd (μ := volume) (ha.measurable.mul (hf.measurable.mul hg))
    (Ba * (Bf * Bg)) (fun x => ?_)
  have h1 : |a x| ≤ Ba := by simpa using hBa x
  have h2 : |f x| ≤ Bf := by simpa using hBf x
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul h1 (mul_le_mul h2 (hBg x) (abs_nonneg _) ((abs_nonneg _).trans h2))
    (by positivity) ((abs_nonneg _).trans h1)

lemma tinhom_transport_data {v : Torus d → Euc d} {K : ℝ} (h : TorusSubTransport d s v K) :
    ∃ (L F : ℝ) (w : Torus d → Euc d), 0 ≤ L ∧ 0 ≤ F ∧ IsLipschitzVF L v ∧
      IsFracDeriv (Whole.alphaE d s) v w ∧
      eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal (Whole.p1E d s)) volume ≤ ENNReal.ofReal F ∧
      L + F ≤ K := by
  obtain ⟨L, F, hL, hF, hLip, ⟨w, hrep, hn⟩, hLF⟩ := h
  refine ⟨L, F, w, hL, hF, hLip, hrep, ?_, hLF⟩
  have hwm : AEStronglyMeasurable w volume := by
    by_contra hcon
    rw [eLpNorm_of_not_aestronglyMeasurable hcon] at hn
    exact absurd hn (by simp)
  rw [eLpNorm_norm w hwm]
  exact hn

lemma tinhom_p2_ge_two (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    (2 : ℝ≥0∞) ≤ ENNReal.ofReal (Whole.p2E d s) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have : (2 : ℝ) ≤ Whole.p2E d s := by
    unfold Whole.p2E
    rw [le_div_iff₀ (by linarith)]
    linarith
  calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal this

lemma tinhom_bern_exp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    -(d : ℝ) * (((2 : ℝ≥0∞)⁻¹).toReal - ((ENNReal.ofReal (Whole.p2E d s))⁻¹).toReal) =
      -(Whole.alphaE d s - 1) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : 0 < s + 2 := by linarith
  have hP : 0 ≤ Whole.p2E d s := by unfold Whole.p2E; positivity
  rw [ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_ofReal hP]
  simp only [ENNReal.toReal_ofNat]
  unfold Whole.p2E Whole.alphaE
  field_simp
  ring

/-- `N₀ N₁ ≤ √(ab) (S₀^{1/2} S₁^{1/2})` from `N₀² ≤ a S₀`, `N₁² ≤ b S₁`. -/
lemma tinhom_prod_bound {N₀ N₁ S₀ S₁ : ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h0 : N₀ ^ 2 ≤ ENNReal.ofReal a * S₀) (h1 : N₁ ^ 2 ≤ ENNReal.ofReal b * S₁) :
    N₀ * N₁ ≤ ENNReal.ofReal ((a * b) ^ ((1 : ℝ) / 2)) * (S₀ ^ ((1 : ℝ) / 2) * S₁ ^ ((1 : ℝ) / 2)) := by
  have e0 := tinhom_sqrt_of_sq h0
  have e1 := tinhom_sqrt_of_sq h1
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg ha (by norm_num)] at e0
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg hb (by norm_num)] at e1
  calc N₀ * N₁ ≤ (ENNReal.ofReal (a ^ ((1 : ℝ) / 2)) * S₀ ^ ((1 : ℝ) / 2)) *
        (ENNReal.ofReal (b ^ ((1 : ℝ) / 2)) * S₁ ^ ((1 : ℝ) / 2)) := mul_le_mul' e0 e1
    _ = ENNReal.ofReal (a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2)) * (S₀ ^ ((1 : ℝ) / 2) * S₁ ^ ((1 : ℝ) / 2)) := by
        rw [ENNReal.ofReal_mul (by positivity)]; ring
    _ = _ := by rw [Real.mul_rpow ha hb]

theorem tinhom_cross_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → ∀ a₀ b : Torus d → ℝ, Continuous a₀ → Continuous b →
      (∀ k : Lattice d, 1 / 8 < η * Lattice.enorm k → Torus.fcoef a₀ k = 0) →
      ENNReal.ofReal |∑ i, ∫ x, a₀ x * (v x i * textConv (fun z => ghiForceT s η z i) b x)| ≤
        ENNReal.ofReal (C * K * η ^ ((d : ℝ) - s)) *
          (tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef a₀ k) ^ ((1 : ℝ) / 2) *
            tinhomS η (-Whole.alphaE d s) (fun k => Torus.fcoef b k) ^ ((1 : ℝ) / 2)) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨CM, hCM, hsplit⟩ := tinhom_vsplit hd1
  obtain ⟨CV, hCV, hvhi⟩ := tsamp_vhi_Lp_core hd hs0 hsd
  obtain ⟨CB, hCB, hbern⟩ := text_bernstein_main hd1 (1 / 8) (by norm_num) 2
    (ENNReal.ofReal (Whole.p2E d s)) (by norm_num) (tinhom_p2_ge_two hd hs0 hsd)
  obtain ⟨CK, hCK, hKb⟩ := tinhom_Kb_L2 hd hs0 hsd
  have hα : 0 < Whole.alphaE d s := by unfold Whole.alphaE; linarith
  set Cθ : ℝ := (1 + 4 * Real.pi ^ 2 * (1 / 8) ^ 2) ^ (Whole.alphaE d s) with hCθ
  have hCθ0 : 0 < Cθ := by positivity
  set R : ℝ := (Cθ * CK) ^ ((1 : ℝ) / 2) with hR
  have hR0 : 0 < R := by positivity
  refine ⟨d * (CM + CB * CV) * R + 1, by positivity, ?_⟩
  intro η hη hη1 v K hT a₀ b ha₀ hb hsupp
  obtain ⟨L, F, w, hL, hF, hLip, hrep, hw, hLF⟩ := tinhom_transport_data hT
  obtain ⟨vlo, M, hPl, hvloc, hMc, hMb, B, c, hvlo, hc⟩ := hsplit η hη hη1 v L hL hLip
  have hvc : Continuous v := tsamp_lip_continuous hLip
  obtain ⟨W, -, hWn⟩ := hvhi η hη hη1 v L w F hF hL hLip hrep hw
  set α := Whole.alphaE d s with hαdef
  set S₀ := tinhomS η (-α) (fun k => Torus.fcoef a₀ k) with hS₀
  set Sb := tinhomS η (-α) (fun k => Torus.fcoef b k) with hSb
  -- norm bounds for `a₀`
  have hN0sq : eLpNorm a₀ 2 volume ^ 2 ≤ ENNReal.ofReal Cθ * S₀ :=
    tinhom_a0_L2 ha₀ hη hα.le hsupp
  have hMem0 : MemLp a₀ 2 volume := HRS.PDE.R2Aux.memLp_of_continuous_real ha₀
  -- Bernstein: `‖a₀‖_{p₂} ≲ η^{-(α-1)} ‖a₀‖₂`
  obtain ⟨-, hbern0⟩ := hbern η hη hη1 a₀ hMem0 (fun k hk => by
    by_contra hne
    have := hsupp k (by exact hk)
    exact hne this)
  rw [tinhom_bern_exp hd hs0 hsd] at hbern0
  -- the pieces
  have hPgtc : Continuous (PgtT η v) := by
    have : PgtT η v = fun z => v z - (vlo z + M z) := by
      funext z; unfold PgtT; rw [hPl z]
    rw [this]
    exact hvc.sub (hvloc.add hMc)
  have hvdecomp : ∀ z i, v z i = vlo z i + M z i + PgtT η v z i := by
    intro z i
    have h1 : v z = (vlo z + M z) + PgtT η v z := by
      unfold PgtT; rw [← hPl z]; abel
    rw [h1]
    simp [PiLp.add_apply]
  have hKK : 0 ≤ K := by linarith
  have hLK : L ≤ K := by linarith
  have hFK : F ≤ K := by linarith
  have hηe : 0 < η ^ ((d : ℝ) - s) := Real.rpow_pos_of_pos hη _
  have hRη : (Cθ * (CK * η ^ (2 * ((d : ℝ) - s) - 2))) ^ ((1 : ℝ) / 2) =
      R * η ^ ((d : ℝ) - s - 1) := by
    rw [hR, ← mul_assoc, Real.mul_rpow (mul_pos hCθ0 hCK).le (Real.rpow_pos_of_pos hη _).le,
      ← Real.rpow_mul hη.le]
    congr 2
    ring
  have hper : ∀ i : Fin d, ENNReal.ofReal |∫ x, a₀ x * (v x i * textConv (fun z => ghiForceT s η z i) b x)| ≤
      ENNReal.ofReal ((CM + CB * CV) * K * R * η ^ ((d : ℝ) - s)) * (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2)) := by
    intro i
    set Ki : Torus d → ℝ := fun z => ghiForceT s η z i with hKi
    set cv : Torus d → ℝ := textConv Ki b with hcv
    have hK : Integrable Ki := tinhom_ghi_int hd hs0 hsd hη i
    have hKm : Measurable Ki := tinhom_ghi_meas hd hs0 hsd hη i
    obtain ⟨Bb, hBb⟩ := ten_bound_of_continuous hb
    have hBb' : ∀ x, |b x| ≤ Bb := fun x => by simpa using hBb x
    have hcvm : Measurable cv := tinhom_conv_meas hKm hb.measurable
    have hcvb : ∀ x, |cv x| ≤ (∫ z, |Ki z|) * Bb := fun x => tinhom_conv_bdd hK hBb' x
    have hNb : eLpNorm cv 2 volume ^ 2 ≤ ENNReal.ofReal (CK * η ^ (2 * ((d : ℝ) - s) - 2)) * Sb :=
      hKb η hη i b hb
    have hproj : Continuous fun z : Euc d => z i := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous
    have hvi : Continuous fun x => v x i := hproj.comp hvc
    have hvloi : Continuous fun x => vlo x i := hproj.comp hvloc
    have hMi : Continuous fun x => M x i := hproj.comp hMc
    have hPi : Continuous fun x => PgtT η v x i := hproj.comp hPgtc
    have I1 : Integrable (fun x => a₀ x * (vlo x i * cv x)) := tinhom_int3 ha₀ hvloi hcvm hcvb
    have I2 : Integrable (fun x => a₀ x * (M x i * cv x)) := tinhom_int3 ha₀ hMi hcvm hcvb
    have I3 : Integrable (fun x => a₀ x * (PgtT η v x i * cv x)) := tinhom_int3 ha₀ hPi hcvm hcvb
    have I12 : Integrable (fun x => a₀ x * (vlo x i * cv x) + a₀ x * (M x i * cv x)) := I1.add I2
    have hdecomp : ∫ x, a₀ x * (v x i * cv x) =
        (∫ x, a₀ x * (vlo x i * cv x)) + (∫ x, a₀ x * (M x i * cv x)) +
          ∫ x, a₀ x * (PgtT η v x i * cv x) := by
      have e : ∫ x, a₀ x * (v x i * cv x) = ∫ x, (a₀ x * (vlo x i * cv x) + a₀ x * (M x i * cv x) +
          a₀ x * (PgtT η v x i * cv x)) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [hvdecomp x i]
        ring
      rw [e, integral_add I12 I3, integral_add I1 I2]
    have hlo : ∫ x, a₀ x * (vlo x i * cv x) = 0 :=
      tinhom_cross_lo hd hs0 hsd hη ha₀ hb hsupp B c hvlo hc i
    rw [hdecomp, hlo, zero_add]
    -- the product of norms
    have hNN : eLpNorm a₀ 2 volume * eLpNorm cv 2 volume ≤
        ENNReal.ofReal (R * η ^ ((d : ℝ) - s - 1)) * (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2)) := by
      have := tinhom_prod_bound hCθ0.le (mul_pos hCK (Real.rpow_pos_of_pos hη _)).le hN0sq hNb
      rwa [hRη] at this
    have ha0m : AEStronglyMeasurable a₀ volume := ha₀.aestronglyMeasurable
    -- the `M` part
    have hMpart : ENNReal.ofReal |∫ x, a₀ x * (M x i * cv x)| ≤
        ENNReal.ofReal (CM * L * R * η ^ ((d : ℝ) - s)) * (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2)) := by
      have e1 : ∫ x, a₀ x * (M x i * cv x) = ∫ x, (a₀ x * M x i) * cv x :=
        integral_congr_ae (ae_of_all _ fun x => by ring)
      rw [e1]
      refine (tinhom_holder12 (ha₀.mul hMi).aestronglyMeasurable hcvm.aestronglyMeasurable).trans ?_
      have h1 : eLpNorm (fun x => a₀ x * M x i) 2 volume ≤ ENNReal.ofReal (CM * η * L) * eLpNorm a₀ 2 volume :=
        tinhom_bdd_mul ha0m hMi.aestronglyMeasurable (fun x => by
          calc |M x i| ≤ ‖M x‖ := by simpa using PiLp.norm_apply_le (M x) i
            _ ≤ CM * η * L := hMb x)
      calc eLpNorm (fun x => a₀ x * M x i) 2 volume * eLpNorm cv 2 volume
          ≤ (ENNReal.ofReal (CM * η * L) * eLpNorm a₀ 2 volume) * eLpNorm cv 2 volume := by gcongr
        _ = ENNReal.ofReal (CM * η * L) * (eLpNorm a₀ 2 volume * eLpNorm cv 2 volume) := by ring
        _ ≤ ENNReal.ofReal (CM * η * L) * (ENNReal.ofReal (R * η ^ ((d : ℝ) - s - 1)) *
              (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2))) := by gcongr
        _ = ENNReal.ofReal (CM * L * R * η ^ ((d : ℝ) - s)) * (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            have : η ^ ((d : ℝ) - s) = η * η ^ ((d : ℝ) - s - 1) := by
              rw [← Real.rpow_one_add' hη.le (by
                have : (3 : ℝ) ≤ d := hdR
                linarith)]
              congr 1; ring
            rw [this]; ring
    -- the `P_>` part
    have hPpart : ENNReal.ofReal |∫ x, a₀ x * (PgtT η v x i * cv x)| ≤
        ENNReal.ofReal (CB * CV * F * R * η ^ ((d : ℝ) - s)) * (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2)) := by
      have e1 : ∫ x, a₀ x * (PgtT η v x i * cv x) = ∫ x, (a₀ x * PgtT η v x i) * cv x :=
        integral_congr_ae (ae_of_all _ fun x => by ring)
      rw [e1]
      refine (tinhom_holder12 (ha₀.mul hPi).aestronglyMeasurable hcvm.aestronglyMeasurable).trans ?_
      haveI hT3 : ENNReal.HolderTriple (ENNReal.ofReal (Whole.p2E d s)) (ENNReal.ofReal (Whole.p1E d s)) 2 :=
        ⟨by rw [add_comm]; exact tprod_exponent_identity hd hsd hs0⟩
      have h1 := tinhom_holder_triple (P := ENNReal.ofReal (Whole.p2E d s))
        (Q := ENNReal.ofReal (Whole.p1E d s)) ha0m hPi.aestronglyMeasurable
      have h2 : eLpNorm (fun x => PgtT η v x i) (ENNReal.ofReal (Whole.p1E d s)) volume ≤
          ENNReal.ofReal (CV * η ^ α * F) := by
        refine le_trans ?_ (le_trans le_add_self hWn)
        refine eLpNorm_mono_ae hPi.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
        rw [norm_norm]
        simpa using PiLp.norm_apply_le (PgtT η v x) i
      have h3 : eLpNorm a₀ (ENNReal.ofReal (Whole.p2E d s)) volume ≤
          ENNReal.ofReal (CB * η ^ (-(α - 1))) * eLpNorm a₀ 2 volume := hbern0
      calc eLpNorm (fun x => a₀ x * PgtT η v x i) 2 volume * eLpNorm cv 2 volume
          ≤ (eLpNorm a₀ (ENNReal.ofReal (Whole.p2E d s)) volume *
              eLpNorm (fun x => PgtT η v x i) (ENNReal.ofReal (Whole.p1E d s)) volume) *
              eLpNorm cv 2 volume := by gcongr
        _ ≤ ((ENNReal.ofReal (CB * η ^ (-(α - 1))) * eLpNorm a₀ 2 volume) *
              ENNReal.ofReal (CV * η ^ α * F)) * eLpNorm cv 2 volume := by gcongr
        _ = (ENNReal.ofReal (CB * η ^ (-(α - 1))) * ENNReal.ofReal (CV * η ^ α * F)) *
              (eLpNorm a₀ 2 volume * eLpNorm cv 2 volume) := by ring
        _ ≤ (ENNReal.ofReal (CB * η ^ (-(α - 1))) * ENNReal.ofReal (CV * η ^ α * F)) *
              (ENNReal.ofReal (R * η ^ ((d : ℝ) - s - 1)) *
                (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2))) := by gcongr
        _ = ENNReal.ofReal (CB * CV * F * R * η ^ ((d : ℝ) - s)) *
              (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            have hη' : (0 : ℝ) < η := hη
            have e : η ^ (-(α - 1)) * η ^ α * η ^ ((d : ℝ) - s - 1) = η ^ ((d : ℝ) - s) := by
              rw [← Real.rpow_add hη', ← Real.rpow_add hη']
              congr 1
              rw [hαdef]; unfold Whole.alphaE; ring
            calc CB * η ^ (-(α - 1)) * (CV * η ^ α * F) * (R * η ^ ((d : ℝ) - s - 1))
                = CB * CV * F * R * (η ^ (-(α - 1)) * η ^ α * η ^ ((d : ℝ) - s - 1)) := by ring
              _ = _ := by rw [e]
    calc ENNReal.ofReal |(∫ x, a₀ x * (M x i * cv x)) + ∫ x, a₀ x * (PgtT η v x i * cv x)|
        ≤ ENNReal.ofReal (|∫ x, a₀ x * (M x i * cv x)| + |∫ x, a₀ x * (PgtT η v x i * cv x)|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ = ENNReal.ofReal |∫ x, a₀ x * (M x i * cv x)| + ENNReal.ofReal |∫ x, a₀ x * (PgtT η v x i * cv x)| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ ENNReal.ofReal (CM * L * R * η ^ ((d : ℝ) - s)) * (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2)) +
          ENNReal.ofReal (CB * CV * F * R * η ^ ((d : ℝ) - s)) * (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2)) :=
          add_le_add hMpart hPpart
      _ = ENNReal.ofReal (CM * L * R * η ^ ((d : ℝ) - s) + CB * CV * F * R * η ^ ((d : ℝ) - s)) *
          (S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2)) := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := by
          gcongr
          have h1 : CM * L ≤ CM * K := mul_le_mul_of_nonneg_left hLK hCM.le
          have h2 : CB * CV * F ≤ CB * CV * K := mul_le_mul_of_nonneg_left hFK (by positivity)
          have h3 : 0 < R * η ^ ((d : ℝ) - s) := mul_pos hR0 hηe
          nlinarith [mul_le_mul_of_nonneg_right (add_le_add h1 h2) h3.le]
  -- the sum over `i`
  set Q := S₀ ^ ((1 : ℝ) / 2) * Sb ^ ((1 : ℝ) / 2) with hQ
  set X : ℝ := (CM + CB * CV) * K * R * η ^ ((d : ℝ) - s) with hX
  have hX0 : 0 ≤ X := by positivity
  calc ENNReal.ofReal |∑ i, ∫ x, a₀ x * (v x i * textConv (fun z => ghiForceT s η z i) b x)|
      ≤ ENNReal.ofReal (∑ i, |∫ x, a₀ x * (v x i * textConv (fun z => ghiForceT s η z i) b x)|) :=
        ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, ENNReal.ofReal |∫ x, a₀ x * (v x i * textConv (fun z => ghiForceT s η z i) b x)| :=
        ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ ≤ ∑ _i : Fin d, ENNReal.ofReal X * Q := Finset.sum_le_sum fun i _ => hper i
    _ = (d : ℝ≥0∞) * (ENNReal.ofReal X * Q) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal (d * X) * Q := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal ((d * (CM + CB * CV) * R + 1) * K * η ^ ((d : ℝ) - s)) * Q := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have : 0 ≤ K * η ^ ((d : ℝ) - s) := by positivity
        have e : (d : ℝ) * X = d * (CM + CB * CV) * R * (K * η ^ ((d : ℝ) - s)) := by
          rw [hX]; ring
        rw [e]
        nlinarith

end HRS.Commutator.TorusNote
