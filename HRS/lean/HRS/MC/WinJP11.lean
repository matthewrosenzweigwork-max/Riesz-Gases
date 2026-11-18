import HRS.MC.WinJSpecDefs
import HRS.MC.WinJP8
import HRS.MC.WinJP10

/-!
# WJ11: P11 `p11a_near_diff`, `p11b_block_diff`, `p11c_decay_diff` (near piece, unit blocks, glue for the difference)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

section Packets

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

/-! ## P11a: near piece -/

/-- the horizon `T+1` tensor of the regime restarted at `b₀ = a - s` pushed to the window -/
lemma p_wj11_near_SJW (R : Regime d) (r m T a s b₀ : ℝ) (hb₀def : b₀ = a - s) (hs0 : 0 ≤ s)
    (hsG : s + T ≤ T + 1) (hb₀ : 0 ≤ b₀) (z : ℝ → NegSobolev d r) (α β : ℝ) (hα : b₀ ≤ α)
    (J : TensorDual (PathSpace d m (T + 1)) 2)
    (hJ : SJ (HRS.MC.E213F.shift R b₀ hb₀) r m (T + 1) (fun v => z (b₀ + v))
      (Set.Ioc (α - b₀) (β - b₀)) J) :
    SJW R r m T a z (Set.Ioc α β) (tensorPow' 2 (shiftRestr m T (T + 1) s hs0 hsG) J) := by
  refine ⟨u3_tp_mem _ hJ.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [u3_tp_prodForm]
  have hta' : s + ta ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨by linarith [hta.1], by linarith [hta.2]⟩
  have htb' : s + tb ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨by linarith [htb.1], by linarith [htb.2]⟩
  rw [hJ.2 (s + ta) (s + tb) φa φb _ _ hφa hφb hta' htb'
    (fun w => by
      show l₁ (shiftRestr m T (T + 1) s hs0 hsG w) = _
      rw [hl₁, shiftRestr_pathAt m T (T + 1) s hs0 hsG w hta])
    (fun w => by
      show l₂ (shiftRestr m T (T + 1) s hs0 hsG w) = _
      rw [hl₂, shiftRestr_pathAt m T (T + 1) s hs0 hsG w htb])]
  have hinv : (HRS.MC.E213F.shift R b₀ hb₀).D.invβ = R.D.invβ := rfl
  rw [hinv]
  congr 1
  have hset : (fun x => b₀ + x) ⁻¹' (Set.Ioc α β ∩ Set.Icc 0 (min (a + ta) (a + tb))) =
      Set.Ioc (α - b₀) (β - b₀) ∩ Set.Icc 0 (min (s + ta) (s + tb)) := by
    ext v
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩
  rw [← u3_setIntegral_shift b₀ (fun u => Fser R r m z (a + ta) (a + tb) φa φb u), hset]
  refine setIntegral_congr_fun (measurableSet_Ioc.inter measurableSet_Icc) fun v hv => ?_
  have e1 : b₀ + (s + ta) = a + ta := by rw [hb₀def]; ring
  have e2 : b₀ + (s + tb) = a + tb := by rw [hb₀def]; ring
  have := u3_Fser_shift R r m b₀ hb₀ z (s + ta) (s + tb) φa φb hv.2.1
    (hv.2.2.trans (min_le_left _ _)) (hv.2.2.trans (min_le_right _ _))
  rw [e1, e2] at this
  exact this

/-- **P11a.** -/
theorem p11a_near_diff (sd : StatDatum S β₀ m hE) (T : ℝ) (hT : 0 < T) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ a : ℝ, 0 ≤ a → ∀ z : ℝ → NegSobolev d (rLvl d), Measurable z →
      ∀ α β : ℝ, a - min a 1 ≤ α → α ≤ β → β ≤ a + T → IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) →
      ∃ X X' : TensorDual (PathSpace d m T) 2,
        SJW (regime S β₀ hE) (rLvl d) m T a z (Set.Ioc α β) X ∧
        SJW (regime sd.Ss S.β sd.hEs) (rLvl d) m T a z (Set.Ioc α β) X' ∧
        ‖X - X'‖ ≤ C * Real.exp (-κ * a) * ∫ v in Set.Ioc α β, ‖z v‖ := by
  obtain ⟨C, κ, hC0, hκ, h9⟩ := p9_L1_diff sd (T + 1) (by linarith)
  refine ⟨C * Real.exp κ, κ, by positivity, hκ, fun a ha z hz α β hα hαβ hβ hint => ?_⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = min a 1 := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsdef]; exact le_min ha zero_le_one
  have hsa : s ≤ a := by rw [hsdef]; exact min_le_left _ _
  have hs1 : s ≤ 1 := by rw [hsdef]; exact min_le_right _ _
  have hsG : s + T ≤ T + 1 := by linarith
  obtain ⟨b₀, hb₀def⟩ : ∃ b₀, b₀ = a - s := ⟨_, rfl⟩
  have hb₀ : 0 ≤ b₀ := by rw [hb₀def]; linarith
  rw [← hsdef, ← hb₀def] at hα
  have hI : (fun x => b₀ + x) ⁻¹' Set.Ioc α β = Set.Ioc (α - b₀) (β - b₀) :=
    Set.preimage_const_add_Ioc _ _ _
  have hint' : IntegrableOn (fun v => ‖z (b₀ + v)‖) (Set.Ioc (α - b₀) (β - b₀)) := by
    rw [← hI]; exact (u3_integrableOn_shift b₀ (fun u => ‖z u‖) _).2 hint
  obtain ⟨J, J', hJ, hJ', hJn⟩ := h9 b₀ hb₀ (fun v => z (b₀ + v)) (hz.comp (measurable_const_add b₀))
    (α - b₀) (β - b₀) (by linarith) (by linarith) hint'
  have hint2 : ∫ v in Set.Ioc (α - b₀) (β - b₀), ‖z (b₀ + v)‖ = ∫ v in Set.Ioc α β, ‖z v‖ := by
    rw [← hI]; exact u3_setIntegral_shift b₀ (fun u => ‖z u‖) _
  refine ⟨tensorPow' 2 (shiftRestr m T (T + 1) s hs0 hsG) J,
    tensorPow' 2 (shiftRestr m T (T + 1) s hs0 hsG) J',
    p_wj11_near_SJW (regime S β₀ hE) (rLvl d) m T a s b₀ hb₀def hs0 hsG hb₀ z α β hα J hJ,
    p_wj11_near_SJW (regime sd.Ss S.β sd.hEs) (rLvl d) m T a s b₀ hb₀def hs0 hsG hb₀ z α β hα J' hJ',
    ?_⟩
  have hP := p10a_norm_tensorPow2_sub_le (shiftRestr (d := d) m T (T + 1) s hs0 hsG)
    (shiftRestr (d := d) m T (T + 1) s hs0 hsG) J J'
  rw [sub_self, norm_zero, mul_zero, zero_mul, add_zero] at hP
  have hP1 : ‖shiftRestr (d := d) m T (T + 1) s hs0 hsG‖ * ‖shiftRestr (d := d) m T (T + 1) s hs0 hsG‖ ≤ 1 := by
    have := shiftRestr_norm_le (d := d) m T (T + 1) s hs0 hsG
    nlinarith [norm_nonneg (shiftRestr (d := d) m T (T + 1) s hs0 hsG)]
  have hI0 : 0 ≤ ∫ v in Set.Ioc α β, ‖z v‖ := setIntegral_nonneg measurableSet_Ioc fun v _ => norm_nonneg _
  have hexp : Real.exp (-κ * b₀) ≤ Real.exp κ * Real.exp (-κ * a) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [hb₀def]
    nlinarith [mul_nonneg hκ.le (sub_nonneg.2 hs1)]
  rw [hint2] at hJn
  calc _ ≤ ‖shiftRestr (d := d) m T (T + 1) s hs0 hsG‖ * ‖shiftRestr (d := d) m T (T + 1) s hs0 hsG‖ *
        ‖J - J'‖ := hP
    _ ≤ 1 * ‖J - J'‖ := mul_le_mul_of_nonneg_right hP1 (norm_nonneg _)
    _ ≤ C * Real.exp (-κ * b₀) * ∫ v in Set.Ioc α β, ‖z v‖ := by rw [one_mul]; exact hJn
    _ ≤ C * (Real.exp κ * Real.exp (-κ * a)) * ∫ v in Set.Ioc α β, ‖z v‖ := by
        gcongr
    _ = C * Real.exp κ * Real.exp (-κ * a) * ∫ v in Set.Ioc α β, ‖z v‖ := by ring

/-! ## P11b: unit blocks -/

/-- the horizon-`1` tensor of the regime restarted at `j`, evaluated at time `1` and propagated by `Θ` -/
lemma p_wj11_block_SJW (R : Regime d) (r m T a j : ℝ) (hj : 0 ≤ j) (hja : j + 1 ≤ a)
    (z : ℝ → NegSobolev d r) (α β : ℝ) (hjα : j ≤ α) (hβ : β ≤ j + 1)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hdual : IsDualEvolution R.D R.ρ m Vev)
    (hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T)
    (Θ : NegSobolev d m →L[ℝ] PathSpace d m T)
    (hΘ : ∀ x t, t ∈ Set.Icc (0 : ℝ) T → pathAt (Θ x) t = Vev (a + t) (j + 1) x)
    (J : TensorDual (PathSpace d m 1) 2)
    (hJ : SJ (HRS.MC.E213F.shift R j hj) r m 1 (fun v => z (j + v)) (Set.Ioc (α - j) (β - j)) J) :
    SJW R r m T a z (Set.Ioc α β)
      (tensorPow' 2 (Θ.comp (evAt m 1 1 ⟨zero_le_one, le_rfl⟩)) J) := by
  have hs0 : 0 ≤ j + 1 := by linarith
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨u3_tp_mem _ hJ.1, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [u3_tp_prodForm]
  have hsa : j + 1 ≤ a + ta := by linarith [hta.1]
  have hsb : j + 1 ≤ a + tb := by linarith [htb.1]
  have hψa : Torus.IsSmooth (propagator R.D R.ρ (j + 1) (a + ta) φa) :=
    (HRS.MC.L2C0.l2c0_proof R φa hφa (j + 1) (a + ta) hs0 hsa).1
  have hψb : Torus.IsSmooth (propagator R.D R.ρ (j + 1) (a + tb) φb) :=
    (HRS.MC.L2C0.l2c0_proof R φb hφb (j + 1) (a + tb) hs0 hsb).1
  have hev : ∀ (l : StrongDual ℝ (PathSpace d m T)) (t : ℝ) (φ : Torus d → ℝ), t ∈ Set.Icc (0 : ℝ) T →
      Torus.IsSmooth φ → (∀ w, l w = NegSobolev.eval (pathAt w t) φ) → ∀ w : PathSpace d m 1,
      (l.comp (Θ.comp (evAt m 1 1 h1))) w =
        NegSobolev.eval (pathAt w 1) (propagator R.D R.ρ (j + 1) (a + t) φ) := by
    intro l t φ ht hφ hl w
    show l (Θ (evAt m 1 1 h1 w)) = _
    rw [hl, hΘ _ _ ht, hdual (j + 1) (a + t) hs0 (by linarith [ht.1]) (evAt m 1 1 h1 w) φ hφ, evAt_apply]
  rw [hJ.2 1 1 _ _ _ _ hψa hψb h1 h1 (hev l₁ ta φa hta hφa hl₁) (hev l₂ tb φb htb hφb hl₂)]
  have hinv : (HRS.MC.E213F.shift R j hj).D.invβ = R.D.invβ := rfl
  rw [hinv]
  congr 1
  have hset : (fun x => j + x) ⁻¹' (Set.Ioc α β ∩ Set.Icc 0 (min (a + ta) (a + tb))) =
      Set.Ioc (α - j) (β - j) ∩ Set.Icc 0 (min (1 : ℝ) 1) := by
    ext v
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, le_min_iff, min_self]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith [hta.1], by linarith [htb.1]⟩
  rw [← u3_setIntegral_shift j (fun u => Fser R r m z (a + ta) (a + tb) φa φb u), hset]
  refine setIntegral_congr_fun (measurableSet_Ioc.inter measurableSet_Icc) fun v hv => ?_
  have hv0 : 0 ≤ v := hv.2.1
  have hv1 : v ≤ 1 := by simpa using hv.2.2
  have e1 := u3_Fser_shift R r m j hj z 1 1 (propagator R.D R.ρ (j + 1) (a + ta) φa)
    (propagator R.D R.ρ (j + 1) (a + tb) φb) hv0 hv1 hv1
  rw [e1]
  exact u3_Fser_prop R r m Vev hdual hplain z hsa hsb (by linarith) (by linarith) hφa hφb

/-- the dual evolutions of the two regimes at level `m`, with the decay of the first -/
lemma p_wj11_evs (sd : StatDatum S β₀ m hE) :
    ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧ ∃ Vev Vev' : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      IsDualEvolution (regime S β₀ hE).D (regime S β₀ hE).ρ m Vev ∧
      (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u))) ∧
      IsDualEvolution (regime sd.Ss S.β sd.hEs).D (regime sd.Ss S.β sd.hEs).ρ m Vev' ∧
      (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev' T) := by
  obtain ⟨Cr, cr, hCr, hcr, VR, hVR, hVp, hdec, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd (HRS.MC.E213A.isSmoothPositiveTrajectory_of_prepared S) m
  obtain ⟨-, -, -, -, Wc, hWc, hWp, -⟩ :=
    HRS.ThermLin.thermlin_stationary_evolution S (HRS.MC.E214K.regime_thermal S β₀ hE) m
  refine ⟨Cr, cr, hCr, hcr, VR, Wc, hVR, hVp, hdec, ?_, hWp⟩
  rw [sd.hD, sd.hρ]
  exact hWc

lemma p_wj11_arith (p p' δ jd j' A E I Cr C9 C10 CL : ℝ) (hCr : 0 ≤ Cr) (hC9 : 0 ≤ C9) (hC10 : 0 ≤ C10)
    (hCL : 0 ≤ CL) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hE : 0 ≤ E) (hI : 0 ≤ I) (hp0 : 0 ≤ p)
    (hp : p ≤ Cr * A) (hp'0 : 0 ≤ p') (hp' : p' ≤ (Cr + C10) * A) (hδ0 : 0 ≤ δ) (hδ : δ ≤ C10 * A * E)
    (hjd0 : 0 ≤ jd) (hjd : jd ≤ C9 * E * I) (hj'0 : 0 ≤ j') (hj' : j' ≤ CL * I) :
    p * p * jd + (p + p') * δ * j' ≤ (Cr ^ 2 * C9 + (2 * Cr + C10) * C10 * CL) * A * E * I := by
  have h1 : p * p * jd ≤ (Cr * A) * (Cr * A) * (C9 * E * I) := by gcongr
  have h2 : (p + p') * δ * j' ≤ ((2 * Cr + C10) * A) * (C10 * A * E) * (CL * I) := by
    have hpp : p + p' ≤ (2 * Cr + C10) * A := by nlinarith
    gcongr
  have hAA : A * A ≤ A := by nlinarith
  calc p * p * jd + (p + p') * δ * j'
      ≤ (Cr * A) * (Cr * A) * (C9 * E * I) + ((2 * Cr + C10) * A) * (C10 * A * E) * (CL * I) :=
        add_le_add h1 h2
    _ = (Cr ^ 2 * C9 * E * I + (2 * Cr + C10) * C10 * E * CL * I) * (A * A) := by ring
    _ ≤ (Cr ^ 2 * C9 * E * I + (2 * Cr + C10) * C10 * E * CL * I) * A :=
        mul_le_mul_of_nonneg_left hAA (by positivity)
    _ = (Cr ^ 2 * C9 + (2 * Cr + C10) * C10 * CL) * A * E * I := by ring

/-- **P11b.** -/
theorem p11b_block_diff (sd : StatDatum S β₀ m hE) (T : ℝ) (hT : 0 < T) :
    ∃ C c κ : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 < κ ∧ ∀ a j : ℝ, 0 ≤ j → j + 1 ≤ a → ∀ z : ℝ → NegSobolev d (rLvl d),
      Measurable z → ∀ α β : ℝ, j ≤ α → α ≤ β → β ≤ j + 1 → IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) →
      ∃ X X' : TensorDual (PathSpace d m T) 2,
        SJW (regime S β₀ hE) (rLvl d) m T a z (Set.Ioc α β) X ∧
        SJW (regime sd.Ss S.β sd.hEs) (rLvl d) m T a z (Set.Ioc α β) X' ∧
        ‖X - X'‖ ≤ C * Real.exp (-c * (a - j - 1)) * Real.exp (-κ * j) * ∫ v in Set.Ioc α β, ‖z v‖ := by
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  obtain ⟨C9, κ9, hC90, hκ9, h9⟩ := p9_L1_diff sd 1 one_pos
  obtain ⟨CL, hCL0, hL⟩ := u3_L1 (regime sd.Ss S.β sd.hEs) (rLvl d) rfl m hm 1 one_pos
  obtain ⟨C10, c10, κ10, hC10, hc10, hκ10, h10⟩ := p10c_vev_compare sd
  obtain ⟨Cr, cr, hCr, hcr, Vev, Vev', hdual, hplain, hdec, hdual', hplain'⟩ := p_wj11_evs sd
  obtain ⟨cm, hcmdef⟩ : ∃ cm, cm = min cr c10 := ⟨_, rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = min κ9 κ10 := ⟨_, rfl⟩
  have hcm0 : 0 < cm := by rw [hcmdef]; exact lt_min hcr hc10
  have hκ0 : 0 < κ := by rw [hκdef]; exact lt_min hκ9 hκ10
  have hcmr : cm ≤ cr := by rw [hcmdef]; exact min_le_left _ _
  have hcmc : cm ≤ c10 := by rw [hcmdef]; exact min_le_right _ _
  have hκ9' : κ ≤ κ9 := by rw [hκdef]; exact min_le_left _ _
  have hκ10' : κ ≤ κ10 := by rw [hκdef]; exact min_le_right _ _
  refine ⟨Cr ^ 2 * C9 + (2 * Cr + C10) * C10 * CL, cm, κ, by positivity, hcm0, hκ0,
    fun a j hj hja z hz α β hjα hαβ hβ hint => ?_⟩
  have hs0 : 0 ≤ j + 1 := by linarith
  have hI : (fun x => j + x) ⁻¹' Set.Ioc α β = Set.Ioc (α - j) (β - j) :=
    Set.preimage_const_add_Ioc _ _ _
  have hint' : IntegrableOn (fun v => ‖z (j + v)‖) (Set.Ioc (α - j) (β - j)) := by
    rw [← hI]; exact (u3_integrableOn_shift j (fun u => ‖z u‖) _).2 hint
  have hint2 : ∫ v in Set.Ioc (α - j) (β - j), ‖z (j + v)‖ = ∫ v in Set.Ioc α β, ‖z v‖ := by
    rw [← hI]; exact u3_setIntegral_shift j (fun u => ‖z u‖) _
  have hzs : Measurable fun v => z (j + v) := hz.comp (measurable_const_add j)
  obtain ⟨J, J', hJ, hJ', hJn⟩ := h9 j hj (fun v => z (j + v)) hzs (α - j) (β - j)
    (by linarith) (by linarith) hint'
  obtain ⟨J'', hJ'', hJ''n⟩ := hL j hj (fun v => z (j + v)) hzs (α - j) (β - j)
    (by linarith) (by linarith) hint'
  have hJJ : J'' = J' := u3_SJ_unique (HRS.MC.E213F.shift (regime sd.Ss S.β sd.hEs) j hj) _ _ _ hJ'' hJ'
  rw [hJJ] at hJ''n
  rw [hint2] at hJn hJ''n
  -- the propagation operators
  have hcr0 : 0 ≤ Cr := hCr.le
  obtain ⟨K, hKdef⟩ : ∃ K, K = Cr * Real.exp (-cr * (a - (j + 1))) := ⟨_, rfl⟩
  obtain ⟨K2, hK2def⟩ : ∃ K2, K2 = C10 * Real.exp (-c10 * (a - (j + 1))) * Real.exp (-κ10 * (j + 1)) :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hK20 : 0 ≤ K2 := by rw [hK2def]; positivity
  have hcont : ∀ x : NegSobolev d m, Continuous fun t : Set.Icc (0 : ℝ) T => Vev (a + t) (j + 1) x := by
    intro x
    have h := (hplain (a + T) (by linarith)).2.2 x
    have hmap : Continuous fun t : Set.Icc (0 : ℝ) T => ((a + (t : ℝ), j + 1) : ℝ × ℝ) := by fun_prop
    exact h.comp_continuous hmap (fun t => ⟨hs0, by linarith [t.2.1], by linarith [t.2.2]⟩)
  have hcont' : ∀ x : NegSobolev d m, Continuous fun t : Set.Icc (0 : ℝ) T => Vev' (a + t) (j + 1) x := by
    intro x
    have h := (hplain' (a + T) (by linarith)).2.2 x
    have hmap : Continuous fun t : Set.Icc (0 : ℝ) T => ((a + (t : ℝ), j + 1) : ℝ × ℝ) := by fun_prop
    exact h.comp_continuous hmap (fun t => ⟨hs0, by linarith [t.2.1], by linarith [t.2.2]⟩)
  have hKb : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Vev (a + t) (j + 1)‖ ≤ K := by
    intro t ht
    refine (hdec (j + 1) (a + t) hs0 (by linarith [ht.1])).trans ?_
    rw [hKdef]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hcr0
    nlinarith only [mul_nonneg hcr.le ht.1]
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Vev (a + t) (j + 1) - Vev' (a + t) (j + 1)‖ ≤ K2 := by
    intro t ht
    refine (h10 Vev Vev' hdual hdual' (j + 1) (a + t) hs0 (by linarith [ht.1])).trans ?_
    rw [hK2def]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC10.le)
      (Real.exp_pos _).le
    nlinarith only [mul_nonneg hc10.le ht.1]
  have hKb' : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Vev' (a + t) (j + 1)‖ ≤ K + K2 := by
    intro t ht
    have h := norm_sub_le (Vev (a + t) (j + 1)) (Vev (a + t) (j + 1) - Vev' (a + t) (j + 1))
    rw [sub_sub_cancel] at h
    exact h.trans (add_le_add (hKb t ht) (hdiff t ht))
  obtain ⟨Θ, hΘ, hΘn⟩ := u3_theta_exists m T a (j + 1) hT.le Vev K hcont hKb
  obtain ⟨Θ', hΘ', hΘn'⟩ := u3_theta_exists m T a (j + 1) hT.le Vev' (K + K2) hcont' hKb'
  have hΘd : ‖Θ - Θ'‖ ≤ K2 := p10b_theta_sub_le m T a (j + 1) K2 hK20 Vev Vev' Θ Θ' hΘ hΘ' hdiff
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hE1 := evAt_norm_le (d := d) m 1 1 h1
  refine ⟨tensorPow' 2 (Θ.comp (evAt m 1 1 h1)) J, tensorPow' 2 (Θ'.comp (evAt m 1 1 h1)) J',
    p_wj11_block_SJW (regime S β₀ hE) (rLvl d) m T a j hj hja z α β hjα hβ Vev hdual hplain Θ hΘ J hJ,
    p_wj11_block_SJW (regime sd.Ss S.β sd.hEs) (rLvl d) m T a j hj hja z α β hjα hβ Vev' hdual' hplain' Θ'
      hΘ' J' hJ', ?_⟩
  -- the norm bound
  have hP := p10a_norm_tensorPow2_sub_le (Θ.comp (evAt m 1 1 h1)) (Θ'.comp (evAt m 1 1 h1)) J J'
  obtain ⟨A, hAdef⟩ : ∃ A, A = Real.exp (-cm * (a - j - 1)) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = Real.exp (-κ * j) := ⟨_, rfl⟩
  have hx : 0 ≤ a - j - 1 := by linarith
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hA1 : A ≤ 1 := by
    rw [hAdef]; exact Real.exp_le_one_iff.2 (by nlinarith only [mul_nonneg hcm0.le hx])
  have hI0 : 0 ≤ ∫ v in Set.Ioc α β, ‖z v‖ := setIntegral_nonneg measurableSet_Ioc fun v _ => norm_nonneg _
  have hKA : K ≤ Cr * A := by
    rw [hKdef, hAdef]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hcr0
    nlinarith only [mul_nonneg (sub_nonneg.2 hcmr) hx]
  have hK2A : K2 ≤ C10 * A * E := by
    rw [hK2def, hAdef, hEdef]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC10.le)
      (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
    · nlinarith only [mul_nonneg (sub_nonneg.2 hcmc) hx]
    · nlinarith only [hκ10, mul_nonneg (sub_nonneg.2 hκ10') hj]
  have hK2A' : K2 ≤ C10 * A := by
    refine hK2A.trans ?_
    have : E ≤ 1 := by rw [hEdef]; exact Real.exp_le_one_iff.2 (by nlinarith only [mul_nonneg hκ0.le hj])
    nlinarith only [mul_nonneg hC10.le hA0, this]
  have hE9 : Real.exp (-κ9 * j) ≤ E := by
    rw [hEdef]; exact Real.exp_le_exp.2 (by nlinarith only [mul_nonneg (sub_nonneg.2 hκ9') hj])
  have hPn : ‖Θ.comp (evAt m 1 1 h1)‖ ≤ K :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by calc ‖Θ‖ * ‖evAt (d := d) m 1 1 h1‖ ≤ K * 1 :=
              mul_le_mul hΘn hE1 (norm_nonneg _) hK0
            _ = K := mul_one _)
  have hPn' : ‖Θ'.comp (evAt m 1 1 h1)‖ ≤ K + K2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by calc ‖Θ'‖ * ‖evAt (d := d) m 1 1 h1‖ ≤ (K + K2) * 1 :=
              mul_le_mul hΘn' hE1 (norm_nonneg _) (add_nonneg hK0 hK20)
            _ = K + K2 := mul_one _)
  have hPd : ‖Θ.comp (evAt m 1 1 h1) - Θ'.comp (evAt m 1 1 h1)‖ ≤ K2 := by
    rw [← ContinuousLinearMap.sub_comp]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by calc ‖Θ - Θ'‖ * ‖evAt (d := d) m 1 1 h1‖ ≤ K2 * 1 :=
              mul_le_mul hΘd hE1 (norm_nonneg _) hK20
            _ = K2 := mul_one _)
  have hfin := p_wj11_arith ‖Θ.comp (evAt m 1 1 h1)‖ ‖Θ'.comp (evAt m 1 1 h1)‖
    ‖Θ.comp (evAt m 1 1 h1) - Θ'.comp (evAt m 1 1 h1)‖ ‖J - J'‖ ‖J'‖ A E
    (∫ v in Set.Ioc α β, ‖z v‖) Cr C9 C10 CL hcr0 hC90 hC10.le hCL0 hA0 hA1 hE0 hI0 (norm_nonneg _)
    (hPn.trans hKA) (norm_nonneg _) (by nlinarith only [hPn', hKA, hK2A'])
    (norm_nonneg _) (hPd.trans hK2A) (norm_nonneg _)
    (hJn.trans (by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE9 hI0) hC90 |>.trans_eq' (by ring)
        |>.trans_eq (by ring)))
    (norm_nonneg _) hJ''n
  rw [hAdef, hEdef] at hfin
  exact hP.trans hfin

/-! ## P11c: glue and decay -/

/-- integrability of the weight `e^{-c(a-v)} e^{-κ v} ‖z v‖` -/
lemma p_wj11_wint {r c κ a T : ℝ} (hc : 0 ≤ c) (hκ : 0 ≤ κ) {z : ℝ → NegSobolev d r} (hz : Measurable z)
    {S : Set ℝ} (hSm : MeasurableSet S) (hS : ∀ v ∈ S, 0 ≤ v ∧ v ≤ a + T)
    (hint : IntegrableOn (fun v => ‖z v‖) S) :
    IntegrableOn (fun v => Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖) S := by
  refine Integrable.mono' (hint.const_mul (Real.exp (c * T))) ?_ ?_
  · exact (((Real.continuous_exp.comp (by fun_prop : Continuous fun v : ℝ => -c * (a - v))).mul
      (Real.continuous_exp.comp (by fun_prop : Continuous fun v : ℝ => -κ * v))).aestronglyMeasurable).mul
      hz.norm.aestronglyMeasurable
  · refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun v hv => ?_)
    obtain ⟨hv0, hv'⟩ := hS v hv
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : Real.exp (-c * (a - v)) ≤ Real.exp (c * T) :=
      Real.exp_le_exp.2 (by nlinarith only [mul_nonneg hc (sub_nonneg.2 hv')])
    have h2 : Real.exp (-κ * v) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith only [mul_nonneg hκ hv0])
    calc Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ ≤ Real.exp (c * T) * 1 * ‖z v‖ := by
          gcongr
      _ = Real.exp (c * T) * ‖z v‖ := by rw [mul_one]

lemma p_wj11_good_self (R R' : Regime d) (r m T a C c κ : ℝ) (z : ℝ → NegSobolev d r) (α : ℝ) :
    GoodDiff R R' r m T a C c κ z α α := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · rw [Set.Ioc_self]; exact u3_SJW_empty R r m T a z
  · rw [Set.Ioc_self]; exact u3_SJW_empty R' r m T a z
  · rw [Set.Ioc_self]; simp

lemma p_wj11_glue (R R' : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (a C c κ : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hκ : 0 ≤ κ) (z : ℝ → NegSobolev d r) (hz : Measurable z) {α γ β : ℝ} (h0 : 0 ≤ α) (hαγ : α ≤ γ)
    (hγβ : γ ≤ β) (hβ : β ≤ a + T) (hint : IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β))
    (h₁ : GoodDiff R R' r m T a C c κ z α γ) (h₂ : GoodDiff R R' r m T a C c κ z γ β) :
    GoodDiff R R' r m T a C c κ z α β := by
  obtain ⟨X₁, X₁', hX₁, hX₁', hn₁⟩ := h₁
  obtain ⟨X₂, X₂', hX₂, hX₂', hn₂⟩ := h₂
  have hG : 0 < a + T := by linarith
  have hsub1 : Set.Ioc α γ ⊆ Set.Ioc α β := Set.Ioc_subset_Ioc_right hγβ
  have hsub2 : Set.Ioc γ β ⊆ Set.Ioc α β := Set.Ioc_subset_Ioc_left hαγ
  have hi1 : IntegrableOn (fun v => ‖z v‖) (Set.Ioc α γ) := hint.mono_set hsub1
  have hi2 : IntegrableOn (fun v => ‖z v‖) (Set.Ioc γ β) := hint.mono_set hsub2
  have hm1 : ∀ v ∈ Set.Ioc α γ, 0 < v ∧ v ≤ a + T :=
    fun v hv => ⟨lt_of_le_of_lt h0 hv.1, hv.2.trans (hγβ.trans hβ)⟩
  have hm2 : ∀ v ∈ Set.Ioc γ β, 0 < v ∧ v ≤ a + T :=
    fun v hv => ⟨lt_of_le_of_lt h0 (lt_of_le_of_lt hαγ hv.1), hv.2.trans hβ⟩
  have hdisj : Disjoint (Set.Ioc α γ) (Set.Ioc γ β) :=
    Set.disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1]
  refine ⟨X₁ + X₂, X₁' + X₂', ?_, ?_, ?_⟩
  · have hO1 : IntOK R r m (a + T) z (Set.Ioc α γ) :=
      u3_intOK R r hr m hm (a + T) hG z hz measurableSet_Ioc hm1 hi1
    have hO2 : IntOK R r m (a + T) z (Set.Ioc γ β) :=
      u3_intOK R r hr m hm (a + T) hG z hz measurableSet_Ioc hm2 hi2
    have := u3_SJW_union R r m T a ha hdisj measurableSet_Ioc hX₁ hX₂ hO1 hO2
    rwa [Set.Ioc_union_Ioc_eq_Ioc hαγ hγβ] at this
  · have hO1 : IntOK R' r m (a + T) z (Set.Ioc α γ) :=
      u3_intOK R' r hr m hm (a + T) hG z hz measurableSet_Ioc hm1 hi1
    have hO2 : IntOK R' r m (a + T) z (Set.Ioc γ β) :=
      u3_intOK R' r hr m hm (a + T) hG z hz measurableSet_Ioc hm2 hi2
    have := u3_SJW_union R' r m T a ha hdisj measurableSet_Ioc hX₁' hX₂' hO1 hO2
    rwa [Set.Ioc_union_Ioc_eq_Ioc hαγ hγβ] at this
  · have hw1 := p_wj11_wint hc hκ (a := a) (T := T) hz measurableSet_Ioc
      (fun v hv => ⟨(hm1 v hv).1.le, (hm1 v hv).2⟩) hi1
    have hw2 := p_wj11_wint hc hκ (a := a) (T := T) hz measurableSet_Ioc
      (fun v hv => ⟨(hm2 v hv).1.le, (hm2 v hv).2⟩) hi2
    have hsplit : X₁ + X₂ - (X₁' + X₂') = (X₁ - X₁') + (X₂ - X₂') := by abel
    rw [hsplit]
    calc ‖(X₁ - X₁') + (X₂ - X₂')‖ ≤ ‖X₁ - X₁'‖ + ‖X₂ - X₂'‖ := norm_add_le _ _
      _ ≤ C * (∫ v in Set.Ioc α γ, Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖) +
          C * ∫ v in Set.Ioc γ β, Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ :=
        add_le_add hn₁ hn₂
      _ = C * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ := by
          rw [← mul_add, ← setIntegral_union hdisj measurableSet_Ioc hw1 hw2,
            Set.Ioc_union_Ioc_eq_Ioc hαγ hγβ]

/-- from the block bound to `GoodDiff` -/
lemma p_wj11_good_of_block (R R' : Regime d) (r m T a j Cb cb κb C c κ : ℝ) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hκ : 0 ≤ κ) (hcb : c ≤ cb) (hκb : κ ≤ κb) (hCb : 0 ≤ Cb) (hCC : Cb * Real.exp (c + κ) ≤ C)
    (hj : 0 ≤ j) (hja : j + 1 ≤ a) (z : ℝ → NegSobolev d r) (hz : Measurable z) {α β : ℝ} (hjα : j ≤ α)
    (hβ : β ≤ j + 1) (hint : IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β))
    {X X' : TensorDual (PathSpace d m T) 2} (hX : SJW R r m T a z (Set.Ioc α β) X)
    (hX' : SJW R' r m T a z (Set.Ioc α β) X')
    (hn : ‖X - X'‖ ≤ Cb * Real.exp (-cb * (a - j - 1)) * Real.exp (-κb * j) *
      ∫ v in Set.Ioc α β, ‖z v‖) :
    GoodDiff R R' r m T a C c κ z α β := by
  refine ⟨X, X', hX, hX', ?_⟩
  have hw := p_wj11_wint hc hκ (a := a) (T := T) hz measurableSet_Ioc
    (fun v hv => ⟨hj.trans (hjα.trans hv.1.le), by linarith [hv.2]⟩) hint
  have hx : 0 ≤ a - j - 1 := by linarith
  have key : (Real.exp (-cb * (a - j - 1)) * Real.exp (-κb * j)) * ∫ v in Set.Ioc α β, ‖z v‖ ≤
      Real.exp (c + κ) * ∫ v in Set.Ioc α β,
        Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on (hint.const_mul _) (hw.const_mul _) measurableSet_Ioc (fun v hv => ?_)
    have hv1 : j ≤ v := hjα.trans hv.1.le
    have hv2 : v ≤ j + 1 := hv.2.trans hβ
    have hexp : Real.exp (-cb * (a - j - 1)) * Real.exp (-κb * j) ≤
        Real.exp (c + κ) * (Real.exp (-c * (a - v)) * Real.exp (-κ * v)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith only [mul_nonneg (sub_nonneg.2 hcb) hx, mul_nonneg (sub_nonneg.2 hκb) hj,
        mul_nonneg hc (sub_nonneg.2 hv1), mul_nonneg hκ (sub_nonneg.2 hv2)]
    calc (Real.exp (-cb * (a - j - 1)) * Real.exp (-κb * j)) * ‖z v‖ ≤
        (Real.exp (c + κ) * (Real.exp (-c * (a - v)) * Real.exp (-κ * v))) * ‖z v‖ :=
          mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ = Real.exp (c + κ) * (Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖) := by ring
  have hI0 : 0 ≤ ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ :=
    setIntegral_nonneg measurableSet_Ioc fun v _ => by positivity
  calc ‖X - X'‖ ≤ Cb * Real.exp (-cb * (a - j - 1)) * Real.exp (-κb * j) * ∫ v in Set.Ioc α β, ‖z v‖ := hn
    _ = Cb * ((Real.exp (-cb * (a - j - 1)) * Real.exp (-κb * j)) * ∫ v in Set.Ioc α β, ‖z v‖) := by ring
    _ ≤ Cb * (Real.exp (c + κ) * ∫ v in Set.Ioc α β,
          Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖) := mul_le_mul_of_nonneg_left key hCb
    _ = (Cb * Real.exp (c + κ)) * ∫ v in Set.Ioc α β,
          Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ := by ring
    _ ≤ C * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ :=
        mul_le_mul_of_nonneg_right hCC hI0

/-- from the near bound to `GoodDiff` -/
lemma p_wj11_good_of_near (R R' : Regime d) (r m T a Cn κn C c κ : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hκ : 0 ≤ κ) (hκn : κ ≤ κn) (hCn : 0 ≤ Cn) (hCC : Cn * Real.exp (c + κ * T) ≤ C)
    (z : ℝ → NegSobolev d r) (hz : Measurable z) {α β : ℝ} (hα : a - 1 ≤ α) (hα0 : 0 ≤ α)
    (hβ : β ≤ a + T) (hint : IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β))
    {X X' : TensorDual (PathSpace d m T) 2} (hX : SJW R r m T a z (Set.Ioc α β) X)
    (hX' : SJW R' r m T a z (Set.Ioc α β) X')
    (hn : ‖X - X'‖ ≤ Cn * Real.exp (-κn * a) * ∫ v in Set.Ioc α β, ‖z v‖) :
    GoodDiff R R' r m T a C c κ z α β := by
  refine ⟨X, X', hX, hX', ?_⟩
  have hw := p_wj11_wint hc hκ (a := a) (T := T) hz measurableSet_Ioc
    (fun v hv => ⟨hα0.trans hv.1.le, hv.2.trans hβ⟩) hint
  have key : (Real.exp (-κn * a)) * ∫ v in Set.Ioc α β, ‖z v‖ ≤
      Real.exp (c + κ * T) * ∫ v in Set.Ioc α β,
        Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on (hint.const_mul _) (hw.const_mul _) measurableSet_Ioc (fun v hv => ?_)
    have hv1 : a - 1 ≤ v := hα.trans hv.1.le
    have hv2 : v ≤ a + T := hv.2.trans hβ
    have hexp : Real.exp (-κn * a) ≤
        Real.exp (c + κ * T) * (Real.exp (-c * (a - v)) * Real.exp (-κ * v)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith only [mul_nonneg (sub_nonneg.2 hκn) ha, mul_nonneg hc (sub_nonneg.2 hv1),
        mul_nonneg hκ (sub_nonneg.2 hv2)]
    calc (Real.exp (-κn * a)) * ‖z v‖ ≤
        (Real.exp (c + κ * T) * (Real.exp (-c * (a - v)) * Real.exp (-κ * v))) * ‖z v‖ :=
          mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ = Real.exp (c + κ * T) * (Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖) := by ring
  have hI0 : 0 ≤ ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ :=
    setIntegral_nonneg measurableSet_Ioc fun v _ => by positivity
  calc ‖X - X'‖ ≤ Cn * Real.exp (-κn * a) * ∫ v in Set.Ioc α β, ‖z v‖ := hn
    _ = Cn * ((Real.exp (-κn * a)) * ∫ v in Set.Ioc α β, ‖z v‖) := by ring
    _ ≤ Cn * (Real.exp (c + κ * T) * ∫ v in Set.Ioc α β,
          Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖) := mul_le_mul_of_nonneg_left key hCn
    _ = (Cn * Real.exp (c + κ * T)) * ∫ v in Set.Ioc α β,
          Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ := by ring
    _ ≤ C * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖z v‖ :=
        mul_le_mul_of_nonneg_right hCC hI0

/-- induction over the unit blocks -/
lemma p_wj11_far_ind (R R' : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (a C c κ : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hκ : 0 ≤ κ) (z : ℝ → NegSobolev d r) (hz : Measurable z)
    (hB : ∀ j : ℝ, 0 ≤ j → j + 1 ≤ a → ∀ α β : ℝ, j ≤ α → α ≤ β → β ≤ j + 1 →
      IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) → GoodDiff R R' r m T a C c κ z α β) :
    ∀ n : ℕ, (n : ℝ) ≤ a → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ n →
      IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) → GoodDiff R R' r m T a C c κ z α β := by
  intro n
  induction n with
  | zero =>
    intro hn α β h0 hαβ hβ hint
    have : α = β := by simp at hβ; linarith
    subst this
    exact p_wj11_good_self R R' r m T a C c κ z α
  | succ n ih =>
    intro hn α β h0 hαβ hβ hint
    push_cast at hn hβ
    have hn' : (n : ℝ) ≤ a := by linarith
    have hβT : β ≤ a + T := by linarith
    by_cases h1 : β ≤ n
    · exact ih hn' α β h0 hαβ h1 hint
    · push_neg at h1
      by_cases h2 : (n : ℝ) ≤ α
      · exact hB n (Nat.cast_nonneg n) hn α β h2 hαβ hβ hint
      · push_neg at h2
        exact p_wj11_glue R R' r hr m hm T hT a C c κ ha hc hκ z hz h0 h2.le h1.le hβT hint
          (ih hn' α n h0 h2.le le_rfl (hint.mono_set (Set.Ioc_subset_Ioc_right h1.le)))
          (hB n (Nat.cast_nonneg n) hn n β le_rfl h1.le hβ
            (hint.mono_set (Set.Ioc_subset_Ioc_left h2.le)))

/-- **P11c.** -/
theorem p11c_decay_diff (sd : StatDatum S β₀ m hE) (T : ℝ) (hT : 0 < T) :
    ∃ C c κ : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 < κ ∧ ∀ a : ℝ, 0 ≤ a → ∀ z : ℝ → NegSobolev d (rLvl d), Measurable z →
      ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ a + T → IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) →
      GoodDiff (regime S β₀ hE) (regime sd.Ss S.β sd.hEs) (rLvl d) m T a C c κ z α β := by
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hr : rLvl d = 2 * (d : ℝ) + 6 := rfl
  obtain ⟨Cn, κn, hCn0, hκn, hnear⟩ := p11a_near_diff sd T hT
  obtain ⟨Cb, cb, κb, hCb0, hcb, hκb, hblock⟩ := p11b_block_diff sd T hT
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = min κn κb := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; exact lt_min hκn hκb
  have hκn' : κ ≤ κn := by rw [hκdef]; exact min_le_left _ _
  have hκb' : κ ≤ κb := by rw [hκdef]; exact min_le_right _ _
  refine ⟨Cn * Real.exp (cb + κ * T) + Cb * Real.exp (cb + κ), cb, κ, by positivity, hcb, hκ0,
    fun a ha z hz α β h0 hαβ hβ hint => ?_⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = Cn * Real.exp (cb + κ * T) + Cb * Real.exp (cb + κ) := ⟨_, rfl⟩
  rw [← hCdef]
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hCnC : Cn * Real.exp (cb + κ * T) ≤ C := by
    rw [hCdef]; nlinarith only [mul_nonneg hCb0 (Real.exp_pos (cb + κ)).le]
  have hCbC : Cb * Real.exp (cb + κ) ≤ C := by
    rw [hCdef]; nlinarith only [mul_nonneg hCn0 (Real.exp_pos (cb + κ * T)).le]
  have hN : ∀ α β : ℝ, a - min a 1 ≤ α → α ≤ β → β ≤ a + T →
      IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) →
      GoodDiff (regime S β₀ hE) (regime sd.Ss S.β sd.hEs) (rLvl d) m T a C cb κ z α β := by
    intro α β hα hαβ hβ hint
    obtain ⟨X, X', hX, hX', hn⟩ := hnear a ha z hz α β hα hαβ hβ hint
    have hα0 : 0 ≤ α := by
      have := min_le_left a (1 : ℝ)
      linarith
    exact p_wj11_good_of_near _ _ (rLvl d) m T a Cn κn C cb κ ha hcb.le hκ0.le hκn' hCn0 hCnC z hz
      (by linarith [min_le_right a (1 : ℝ)]) hα0 hβ hint hX hX' hn
  have hBl : ∀ j : ℝ, 0 ≤ j → j + 1 ≤ a → ∀ α β : ℝ, j ≤ α → α ≤ β → β ≤ j + 1 →
      IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) →
      GoodDiff (regime S β₀ hE) (regime sd.Ss S.β sd.hEs) (rLvl d) m T a C cb κ z α β := by
    intro j hj hja α β hjα hαβ hβ hint
    obtain ⟨X, X', hX, hX', hn⟩ := hblock a j hj hja z hz α β hjα hαβ hβ hint
    exact p_wj11_good_of_block _ _ (rLvl d) m T a j Cb cb κb C cb κ hT.le hcb.le hκ0.le le_rfl hκb'
      hCb0 hCbC hj hja z hz hjα hβ hint hX hX' hn
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, n₀ = ⌊a⌋₊ := ⟨_, rfl⟩
  have hn₀a : (n₀ : ℝ) ≤ a := by rw [hn₀]; exact Nat.floor_le ha
  have han₀ : a < n₀ + 1 := by rw [hn₀]; exact Nat.lt_floor_add_one a
  have hn₀m : a - min a 1 ≤ n₀ := by
    rcases min_cases a 1 with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; simp
    · rw [h]; linarith
  have hfar := p_wj11_far_ind (regime S β₀ hE) (regime sd.Ss S.β sd.hEs) (rLvl d) hr m hm T hT a C cb κ
    ha hcb.le hκ0.le z hz hBl n₀ hn₀a
  by_cases h1 : β ≤ n₀
  · exact hfar α β h0 hαβ h1 hint
  · push_neg at h1
    by_cases h2 : (n₀ : ℝ) ≤ α
    · exact hN α β (hn₀m.trans h2) hαβ hβ hint
    · push_neg at h2
      exact p_wj11_glue _ _ (rLvl d) hr m hm T hT a C cb κ ha hcb.le hκ0.le z hz h0 h2.le h1.le hβ hint
        (hfar α n₀ h0 h2.le le_rfl (hint.mono_set (Set.Ioc_subset_Ioc_right h1.le)))
        (hN n₀ β hn₀m h1.le hβ (hint.mono_set (Set.Ioc_subset_Ioc_left h2.le)))

end Packets

end HRS.MC.WinJ

end
