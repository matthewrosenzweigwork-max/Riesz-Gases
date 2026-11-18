import HRS.Commutator.Whole.XBBAux13

/-!
# Packet XBB, part 14: the multiplier bound `XBB`

`xbb_exists : ∃ CB, XBB d s CB` for `3 ≤ d`, `0 ≤ s < d - 2`.  The constant is the sum over the finitely
many pairs `(m, a)` of the constants of `xbb_core` (or `1` when the exponent `α' + m - 1` vanishes).
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma xbb_xhom_zero {v : 𝔼 → 𝔼} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) (a c : Fin d)
    (Γ : 𝓢(𝔼, ℂ)) : xhom 0 (xwmul v a c Γ) ≤ L ^ 2 * xhom 0 Γ := by
  have hx : ∀ h : 𝓢(𝔼, ℂ), xhom 0 h = ∫ x, ‖h x‖ ^ 2 := fun h => by
    unfold xhom
    simp only [mul_zero, Real.rpow_zero, one_mul]
    exact SchwartzMap.integral_norm_sq_fourier h
  rw [hx, hx, ← integral_const_mul]
  refine integral_mono (xint_sq_bdd (xwmul v a c Γ)) ((xint_sq_bdd Γ).const_mul _) fun x => ?_
  show ‖xwmul v a c Γ x‖ ^ 2 ≤ L ^ 2 * ‖Γ x‖ ^ 2
  rw [xwmul_apply hv, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (xw_le hv hL0 hL a c x) 2) (by positivity)


lemma xhom_nonneg {β : ℝ} (g : 𝓢(𝔼, ℂ)) : 0 ≤ xhom β g :=
  integral_nonneg fun ξ => by positivity

/-- from the Sobolev-seminorm bound to the `xhom` bound -/
lemma xbb_xhom_of_N {β : ℝ} (hβ : 0 < β) {v : 𝔼 → 𝔼} (hv : XTVF v) (a c : Fin d) (Γ : 𝓢(𝔼, ℂ))
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {L F : ℝ} (hL : 0 ≤ L) (hF : 0 ≤ F)
    (hN : xbbN β (fun x => ((xw v a c x : ℝ) : ℂ) * Γ x) ≤
      C * (ENNReal.ofReal F + ENNReal.ofReal L) * xbbN β ⇑Γ) :
    xhom β (xwmul v a c Γ) ≤ (C.toReal * (L + F)) ^ 2 * xhom β Γ := by
  have e1 : (⇑(xwmul v a c Γ) : 𝔼 → ℂ) = fun x => ((xw v a c x : ℝ) : ℂ) * Γ x :=
    funext (xwmul_apply hv a c Γ)
  have hQ := xbbQ_eq_ofReal_xhom hβ.le (xwmul v a c Γ)
  rw [e1, xbbQ_eq_N_sq] at hQ
  have hQΓ := xbbQ_eq_ofReal_xhom hβ.le Γ
  rw [xbbQ_eq_N_sq] at hQΓ
  have hCr : C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC).symm
  have hr0 : 0 ≤ C.toReal * (L + F) := by positivity
  have hprod : C * (ENNReal.ofReal F + ENNReal.ofReal L) = ENNReal.ofReal (C.toReal * (L + F)) := by
    rw [← ENNReal.ofReal_add hF hL, add_comm F L, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hC]
  have hmain : ENNReal.ofReal (xhom β (xwmul v a c Γ)) ≤
      ENNReal.ofReal ((C.toReal * (L + F)) ^ 2 * xhom β Γ) := by
    rw [← hQ]
    calc xbbN β (fun x => ((xw v a c x : ℝ) : ℂ) * Γ x) ^ (2 : ℝ)
        ≤ (C * (ENNReal.ofReal F + ENNReal.ofReal L) * xbbN β ⇑Γ) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hN (by norm_num)
      _ = (C * (ENNReal.ofReal F + ENNReal.ofReal L)) ^ (2 : ℝ) * xbbN β ⇑Γ ^ (2 : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = ENNReal.ofReal ((C.toReal * (L + F)) ^ 2) * ENNReal.ofReal (xhom β Γ) := by
          rw [hQΓ, hprod, ENNReal.rpow_two, ← ENNReal.ofReal_pow hr0]
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_le_ofReal_iff (by have := xhom_nonneg (β := β) Γ; positivity)).1 hmain


/-- the constant for one pair `(m, a)` -/
lemma xbb_const (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (k m : ℕ)
    (hk1 : (k : ℝ) ≤ ((d : ℝ) - s) / 2) (hm1 : 1 ≤ m) (hmk : m ≤ k) (a : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (c : Fin d) {v : 𝔼 → 𝔼}, XTVF v → ∀ {L F : ℝ}, 0 ≤ L → 0 ≤ F →
      XLip v L → ∀ {w : 𝔼 → 𝔼},
      (∀ i, HRS.Whole.IsFracDerivRep (((d : ℝ) - s) / 2) (fun x => v x i) (fun x => w x i)) →
      eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal (2 * d / ((d : ℝ) - s - 2))) volume ≤ ENNReal.ofReal F →
      ∀ {ρ : 𝔼 → ℝ}, XGoodCut ρ → ∀ (Γ : 𝓢(𝔼, ℂ)), XInD ρ Γ →
        xhom (((d : ℝ) - s) / 2 - k + m - 1) (xwmul v a c Γ) ≤
          (C.toReal * (L + F)) ^ 2 * xhom (((d : ℝ) - s) / 2 - k + m - 1) Γ := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq2 : 0 < (d : ℝ) - s - 2 := by linarith
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmkR : (m : ℝ) ≤ k := by exact_mod_cast hmk
  set α : ℝ := ((d : ℝ) - s) / 2 with hαdef
  set p : ℝ := 2 * d / ((d : ℝ) - s - 2) with hpdef
  set β : ℝ := α - k + m - 1 with hβdef
  have hβ0 : 0 ≤ β := by rw [hβdef]; linarith
  by_cases hβ : 0 < β
  · set η : ℝ := (k : ℝ) - m with hηdef
    have hη : 0 ≤ η := by rw [hηdef]; linarith
    have hp : 1 < p := by
      rw [hpdef, lt_div_iff₀ hq2]; linarith
    have hα : α = β + η + 1 := by rw [hβdef, hηdef]; ring
    have hβd : 2 * β < d := by
      rw [hβdef, hαdef]; linarith
    have hrel : 1 / p - η / d = β / d := by
      have hdne : (d : ℝ) ≠ 0 := by positivity
      rw [hpdef, hβdef, hηdef, hαdef]
      field_simp
      ring
    obtain ⟨C, hC, hcore⟩ := xbb_core hd hβ hη hp hrel hα hβd a
    refine ⟨C, hC, fun c v hv L F hL hF hLip w hrep hw ρ hρ Γ hΓ => ?_⟩
    obtain ⟨ε, hε, hεΓ⟩ := xInD_fourier_zero_near hρ hΓ
    have hG : XComp β Γ (xlam β ρ Γ) := fun ξ => by
      simpa only [SchwartzMap.fourier_coe] using fourier_xlam_of_inD hρ hΓ β ξ
    exact xbb_xhom_of_N hβ hv a c Γ hC hL hF (hcore c hv hL hF hLip hrep hw Γ (xlam β ρ Γ) hG ε hε hεΓ)
  · have hβ00 : β = 0 := le_antisymm (not_lt.1 hβ) hβ0
    refine ⟨1, ENNReal.one_ne_top, fun c v hv L F hL hF hLip w hrep hw ρ hρ Γ hΓ => ?_⟩
    rw [hβ00]
    refine (xbb_xhom_zero hv hL hLip a c Γ).trans ?_
    rw [ENNReal.toReal_one, one_mul]
    gcongr
    · exact xhom_nonneg Γ
    · linarith


/-- **The multiplier bound `XBB`**: the Kato–Ponce / Hardy–Littlewood–Sobolev input of
Nguyen–Rosenzweig–Serfaty. -/
theorem xbb_exists (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ CB : ℝ, XBB d s CB := by
  have hα0 : 0 ≤ ((d : ℝ) - s) / 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = ⌊((d : ℝ) - s) / 2⌋₊ := ⟨_, rfl⟩
  have hk0 : (k₀ : ℝ) ≤ ((d : ℝ) - s) / 2 := by rw [hk₀]; exact Nat.floor_le hα0
  classical
  set Cf : ℕ → Fin d → ℝ≥0∞ := fun m a =>
    if h : 1 ≤ m ∧ m ≤ k₀ then Classical.choose (xbb_const hd hs0 hsd k₀ m hk0 h.1 h.2 a) else 0 with hCf
  set Ctot : ℝ≥0∞ := ∑ a : Fin d, ∑ m ∈ Finset.range (k₀ + 1), Cf m a with hCtot
  have hCf_top : ∀ m a, Cf m a ≠ ⊤ := by
    intro m a
    simp only [hCf]
    split_ifs with h
    · exact (Classical.choose_spec (xbb_const hd hs0 hsd k₀ m hk0 h.1 h.2 a)).1
    · exact ENNReal.zero_ne_top
  have hCtot_top : Ctot ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun a _ => ENNReal.sum_ne_top.2 fun m _ => hCf_top m a
  refine ⟨Ctot.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro v hv K hK ρ hρ k hk1 hk2 m hm1 hmk a c Γ hΓ
  have hkk : k₀ = k := by rw [hk₀]; exact (Nat.floor_eq_iff hα0).2 ⟨hk1, hk2⟩
  subst hkk
  obtain ⟨L, F, hF0, hLip, ⟨w, hrep, hw⟩, hLF⟩ := hK
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hLipX : XLip v (L : ℝ) := fun x y => by
    have := hLip.dist_le_mul x y
    simpa [dist_eq_norm] using this
  have hmem : 1 ≤ m ∧ m ≤ k₀ := ⟨hm1, hmk⟩
  have hbound := (Classical.choose_spec (xbb_const hd hs0 hsd k₀ m hk0 hmem.1 hmem.2 a)).2 c hv hL0 hF0 hLipX
    hrep hw hρ Γ hΓ
  have hCfm : Cf m a = Classical.choose (xbb_const hd hs0 hsd k₀ m hk0 hmem.1 hmem.2 a) := by
    simp only [hCf]; rw [dif_pos hmem]
  have hle : Cf m a ≤ Ctot := by
    calc Cf m a ≤ ∑ m' ∈ Finset.range (k₀ + 1), Cf m' a :=
          Finset.single_le_sum (f := fun m' => Cf m' a) (fun _ _ => zero_le') (Finset.mem_range.2 (by omega))
      _ ≤ Ctot := Finset.single_le_sum (f := fun a' => ∑ m' ∈ Finset.range (k₀ + 1), Cf m' a')
          (fun _ _ => zero_le') (Finset.mem_univ a)
  have hle' : (Cf m a).toReal ≤ Ctot.toReal := ENNReal.toReal_mono hCtot_top hle
  rw [← hCfm] at hbound
  refine hbound.trans ?_
  have hx : 0 ≤ xhom (((d : ℝ) - s) / 2 - k₀ + m - 1) Γ := xhom_nonneg Γ
  have hCn : 0 ≤ (Cf m a).toReal := ENNReal.toReal_nonneg
  gcongr

end HRS.Commutator.Whole.XBB
