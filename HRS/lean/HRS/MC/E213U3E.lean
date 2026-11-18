import HRS.MC.E213U3D

/-!
# Packet E213U3, part E: the near piece and the pre-window unit blocks

* `u3_near`: for `α ≥ a - min a 1`, the window tensor of `(α,β]` is bounded by `C ∫ ‖z‖` (shift of the regime by
  `b₀ = a - min a 1`, horizon `T + 1`, push forward by `shiftRestr`).
* `u3_block`: for a unit block `(j, j+1] ⊃ (α,β]` with `j + 1 ≤ a`, the window tensor is bounded by
  `C e^{-2c_m (a-j-1)} ∫ ‖z‖` (horizon-`1` tensor of the regime shifted by `j`, evaluated at time `1`,
  propagated to the window by `Θ`; cocycle identity `(⋆)`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U3

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDS HRS.MC.E213O HRS.Uniform

set_option maxSynthPendingDepth 3

variable {d : ℕ}

theorem u3_integrableOn_shift {E : Type*} [NormedAddCommGroup E] (b : ℝ) (f : ℝ → E) (S : Set ℝ) :
    IntegrableOn (fun v => f (b + v)) ((fun x => b + x) ⁻¹' S) ↔ IntegrableOn f S :=
  (measurePreserving_add_left volume b).integrableOn_comp_preimage
    (MeasurableEquiv.addLeft b).measurableEmbedding

/-! ### The near piece -/

theorem u3_near (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → ∀ z : ℝ → NegSobolev d r, Measurable z →
      ∀ α β : ℝ, a - min a 1 ≤ α → α ≤ β → β ≤ a + T → IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) →
      ∃ X : TensorDual (PathSpace d m T) 2, SJW R r m T a z (Set.Ioc α β) X ∧
        ‖X‖ ≤ C * ∫ v in Set.Ioc α β, ‖z v‖ := by
  obtain ⟨C, hC0, hC⟩ := u3_L1 R r hr m hm (T + 1) (by linarith)
  refine ⟨C, hC0, fun a ha z hz α β hα hαβ hβ hint => ?_⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = min a 1 := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsdef]; exact le_min ha zero_le_one
  have hsa : s ≤ a := by rw [hsdef]; exact min_le_left _ _
  have hs1 : s ≤ 1 := by rw [hsdef]; exact min_le_right _ _
  have hsG : s + T ≤ T + 1 := by linarith
  obtain ⟨b₀, hb₀def⟩ : ∃ b₀, b₀ = a - s := ⟨_, rfl⟩
  have hb₀ : 0 ≤ b₀ := by rw [hb₀def]; linarith
  rw [← hsdef, ← hb₀def] at hα
  have hI : (fun x => b₀ + x) ⁻¹' Set.Ioc α β = Set.Ioc (α - b₀) (β - b₀) := Set.preimage_const_add_Ioc _ _ _
  have hint' : IntegrableOn (fun v => ‖z (b₀ + v)‖) (Set.Ioc (α - b₀) (β - b₀)) := by
    rw [← hI]; exact (u3_integrableOn_shift b₀ (fun u => ‖z u‖) _).2 hint
  obtain ⟨J, hJ, hJn⟩ := hC b₀ hb₀ (fun v => z (b₀ + v)) (hz.comp (measurable_const_add b₀))
    (α - b₀) (β - b₀) (by linarith) (by linarith) hint'
  refine ⟨tensorPow' 2 (shiftRestr m T (T + 1) s hs0 hsG) J, ⟨u3_tp_mem _ hJ.1, ?_⟩, ?_⟩
  · intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
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
  · have hP := tensorPow'_norm_le 2 (shiftRestr (d := d) m T (T + 1) s hs0 hsG) J
    have hP1 : ‖shiftRestr (d := d) m T (T + 1) s hs0 hsG‖ ^ 2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (shiftRestr_norm_le _ _ _ _ hs0 hsG)
    have hint2 : ∫ v in Set.Ioc (α - b₀) (β - b₀), ‖z (b₀ + v)‖ = ∫ v in Set.Ioc α β, ‖z v‖ := by
      rw [← hI]; exact u3_setIntegral_shift b₀ (fun u => ‖z u‖) _
    calc ‖tensorPow' 2 (shiftRestr m T (T + 1) s hs0 hsG) J‖
        ≤ ‖shiftRestr (d := d) m T (T + 1) s hs0 hsG‖ ^ 2 * ‖J‖ := hP
      _ ≤ 1 * ‖J‖ := mul_le_mul_of_nonneg_right hP1 (norm_nonneg _)
      _ ≤ C * ∫ v in Set.Ioc α β, ‖z v‖ := by rw [one_mul, ← hint2]; exact hJn

/-! ### The cocycle identity -/

theorem u3_star (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m : ℝ)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hdual : IsDualEvolution D ρ m Vev)
    (hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) {u s t : ℝ} (hu : 0 ≤ u) (hus : u ≤ s)
    (hst : s ≤ t) (F : NegSobolev d m) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    NegSobolev.eval (Vprop D ρ m s u F) (propagator D ρ s t φ) = NegSobolev.eval (Vprop D ρ m t u F) φ := by
  have hs0 : 0 ≤ s := hu.trans hus
  have ht0 : 0 ≤ t := hs0.trans hst
  rw [HRS.MC.E213D.vprop_eq_vev D ρ m Vev hdual hu hus F,
    HRS.MC.E213D.vprop_eq_vev D ρ m Vev hdual hu (hus.trans hst) F]
  have h1 := hdual s t hs0 hst (Vev s u F) φ hφ
  have h2 : (Vev t s).comp (Vev s u) = Vev t u := (hplain t ht0).2.1 u s t hu hus hst le_rfl
  have h3 : Vev t u F = Vev t s (Vev s u F) := by
    rw [← h2]; rfl
  rw [h3, h1]

/-- `(⋆)` for the series. -/
theorem u3_Fser_prop (R : Regime d) (r m : ℝ) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hdual : IsDualEvolution R.D R.ρ m Vev) (hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T)
    (z : ℝ → NegSobolev d r) {s ta tb : ℝ} (hsa : s ≤ ta) (hsb : s ≤ tb) {u : ℝ} (hu : 0 ≤ u) (hus : u ≤ s)
    {φa φb : Torus d → ℝ} (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb) :
    Fser R r m z s s (propagator R.D R.ρ s ta φa) (propagator R.D R.ρ s tb φb) u =
      Fser R r m z ta tb φa φb u := by
  unfold Fser Fterm
  refine tsum_congr fun pr => ?_
  rw [u3_star R.D R.ρ m Vev hdual hplain hu hus hsa _ hφa, u3_star R.D R.ρ m Vev hdual hplain hu hus hsb _ hφb]

/-! ### The unit blocks -/

theorem u3_block (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hdual : IsDualEvolution R.D R.ρ m Vev)
    (hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) (Cm cm : ℝ) (hcm : 0 ≤ cm)
    (hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cm * Real.exp (-cm * (t - u))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a j : ℝ, 0 ≤ j → j + 1 ≤ a → ∀ z : ℝ → NegSobolev d r, Measurable z →
      ∀ α β : ℝ, j ≤ α → α ≤ β → β ≤ j + 1 → IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) →
      ∃ X : TensorDual (PathSpace d m T) 2, SJW R r m T a z (Set.Ioc α β) X ∧
        ‖X‖ ≤ C * Real.exp (-(2 * cm) * (a - j - 1)) * ∫ v in Set.Ioc α β, ‖z v‖ := by
  obtain ⟨C1, hC10, hL⟩ := u3_L1 R r hr m hm 1 one_pos
  have hCm : 0 ≤ Cm := by
    have h := hdec 0 0 le_rfl le_rfl
    rw [sub_self, mul_zero, Real.exp_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  refine ⟨C1 * Cm ^ 2, mul_nonneg hC10 (sq_nonneg _), fun a j hj hja z hz α β hjα hαβ hβ hint => ?_⟩
  have hs0 : 0 ≤ j + 1 := by linarith
  -- the horizon-1 tensor of the regime shifted by `j`
  have hI : (fun x => j + x) ⁻¹' Set.Ioc α β = Set.Ioc (α - j) (β - j) := Set.preimage_const_add_Ioc _ _ _
  have hint' : IntegrableOn (fun v => ‖z (j + v)‖) (Set.Ioc (α - j) (β - j)) := by
    rw [← hI]; exact (u3_integrableOn_shift j (fun u => ‖z u‖) _).2 hint
  obtain ⟨J, hJ, hJn⟩ := hL j hj (fun v => z (j + v)) (hz.comp (measurable_const_add j))
    (α - j) (β - j) (by linarith) (by linarith) hint'
  -- the propagation operator
  obtain ⟨K, hKdef⟩ : ∃ K, K = Cm * Real.exp (-cm * (a - (j + 1))) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hcont : ∀ x : NegSobolev d m, Continuous fun t : Set.Icc (0 : ℝ) T => Vev (a + t) (j + 1) x := by
    intro x
    have h := (hplain (a + T) (by linarith)).2.2 x
    have hmap : Continuous fun t : Set.Icc (0 : ℝ) T => ((a + (t : ℝ), j + 1) : ℝ × ℝ) := by fun_prop
    exact h.comp_continuous hmap (fun t => ⟨hs0, by linarith [t.2.1], by linarith [t.2.2]⟩)
  have hKb : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Vev (a + t) (j + 1)‖ ≤ K := by
    intro t ht
    refine (hdec (j + 1) (a + t) hs0 (by linarith [ht.1]) ).trans ?_
    rw [hKdef]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCm
    nlinarith [ht.1]
  obtain ⟨Θ, hΘ, hΘn⟩ := u3_theta_exists m T a (j + 1) hT.le Vev K hcont hKb
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set E1 : PathSpace d m 1 →L[ℝ] NegSobolev d m := evAt m 1 1 h1 with hE1
  set P : PathSpace d m 1 →L[ℝ] PathSpace d m T := Θ.comp E1 with hP
  refine ⟨tensorPow' 2 P J, ⟨u3_tp_mem _ hJ.1, ?_⟩, ?_⟩
  · intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    rw [u3_tp_prodForm]
    have hsa : j + 1 ≤ a + ta := by linarith [hta.1]
    have hsb : j + 1 ≤ a + tb := by linarith [htb.1]
    have hψa : Torus.IsSmooth (propagator R.D R.ρ (j + 1) (a + ta) φa) :=
      (HRS.MC.L2C0.l2c0_proof R φa hφa (j + 1) (a + ta) hs0 hsa).1
    have hψb : Torus.IsSmooth (propagator R.D R.ρ (j + 1) (a + tb) φb) :=
      (HRS.MC.L2C0.l2c0_proof R φb hφb (j + 1) (a + tb) hs0 hsb).1
    have hev : ∀ (l : StrongDual ℝ (PathSpace d m T)) (t : ℝ) (φ : Torus d → ℝ), t ∈ Set.Icc (0 : ℝ) T →
        Torus.IsSmooth φ → (∀ w, l w = NegSobolev.eval (pathAt w t) φ) → ∀ w : PathSpace d m 1,
        (l.comp P) w = NegSobolev.eval (pathAt w 1) (propagator R.D R.ρ (j + 1) (a + t) φ) := by
      intro l t φ ht hφ hl w
      show l (Θ (E1 w)) = _
      rw [hl, hΘ _ _ ht, hdual (j + 1) (a + t) hs0 (by linarith [ht.1]) (E1 w) φ hφ, hE1, evAt_apply]
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
  · have hPn : ‖P‖ ≤ K := by
      calc ‖P‖ ≤ ‖Θ‖ * ‖E1‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ K * 1 := mul_le_mul hΘn (evAt_norm_le m 1 1 h1) (norm_nonneg _) hK0
        _ = K := mul_one _
    have hTP := tensorPow'_norm_le 2 P J
    have hint2 : ∫ v in Set.Ioc (α - j) (β - j), ‖z (j + v)‖ = ∫ v in Set.Ioc α β, ‖z v‖ := by
      rw [← hI]; exact u3_setIntegral_shift j (fun u => ‖z u‖) _
    have hKsq : K ^ 2 = Cm ^ 2 * Real.exp (-(2 * cm) * (a - j - 1)) := by
      rw [hKdef, mul_pow, sq (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    have hJn' : ‖J‖ ≤ C1 * ∫ v in Set.Ioc α β, ‖z v‖ := by rw [← hint2]; exact hJn
    calc ‖tensorPow' 2 P J‖ ≤ ‖P‖ ^ 2 * ‖J‖ := hTP
      _ ≤ K ^ 2 * (C1 * ∫ v in Set.Ioc α β, ‖z v‖) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hPn 2) hJn' (norm_nonneg _) (sq_nonneg _)
      _ = C1 * Cm ^ 2 * Real.exp (-(2 * cm) * (a - j - 1)) * ∫ v in Set.Ioc α β, ‖z v‖ := by
          rw [hKsq]; ring

end HRS.MC.E213U3

end
