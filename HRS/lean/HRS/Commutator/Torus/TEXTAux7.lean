import HRS.Commutator.Torus.TEXTAux6

/-!
# T-EXT-A helpers, part 7: the multiplier kernel on the torus (proof of `mult_kernel_T`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_alg1 {η r a : ℝ} (hη : 0 < η) (hr : 0 ≤ r) :
    η ^ a * (r / η) ^ a = r ^ a := by
  rw [← Real.mul_rpow hη.le (div_nonneg hr hη.le), mul_div_cancel₀ _ hη.ne']

lemma text_alg2 {η r a : ℝ} (m : ℕ) (hη : 0 < η) (hr : 0 < r) :
    η ^ a * (r / η) ^ (-(m : ℝ)) = η ^ (a + m) * r ^ (-(m : ℝ)) := by
  rw [Real.div_rpow hr.le hη.le, Real.rpow_neg hη.le, Real.rpow_add hη, div_inv_eq_mul]
  ring

lemma text_norm_inv_smul {η : ℝ} (hη : 0 < η) (c : Euc d) : ‖η⁻¹ • c‖ = ‖c‖ / η := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη), inv_mul_eq_div]

theorem text_mult_kernel_main (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) (hγd : γ < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ Cm : ℕ → ℝ, (∀ m, 0 < Cm m) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ K : Torus d → ℝ, Integrable K ∧
        (∀ k : Lattice d, Torus.fcoef K k = ((if k = 0 then 0 else
            (1 - Whole.chi (η • Lattice.toEuc k)) * (2 * Real.pi * Lattice.enorm k) ^ (-γ) : ℝ) : ℂ)) ∧
        (∀ x : Torus d, x ≠ 0 → KernelGrad.tdist x 0 ≤ η →
            |K x| ≤ C * KernelGrad.tdist x 0 ^ (γ - d)) ∧
        (∀ (m : ℕ) (x : Torus d), η ≤ KernelGrad.tdist x 0 →
            |K x| ≤ Cm m * η ^ (γ - d + m) * KernelGrad.tdist x 0 ^ (-(m : ℝ))) := by
  obtain ⟨Kt, hKint, hFT, ⟨C₀, hC₀, hnear⟩, hfar⟩ := Whole.cmxMY_mult_kernel_bounds hd γ hγ hγd
  choose Cf hCf using hfar
  obtain ⟨K', hKm, hae, hnear', hfar'⟩ := text_meas_version hKint hC₀.le hnear Cf
    (fun m => (hCf m).1.le) (fun m => (hCf m).2)
  have hK'int : Integrable K' := hKint.congr (hae.mono fun x hx => hx.symm)
  have hFT' : ∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K' x : ℝ) : ℂ)) ξ =
      (((1 - Whole.chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-γ) : ℝ) : ℂ) := by
    intro ξ
    rw [← hFT ξ]
    simp only [Real.fourier_eq]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  -- constants
  set A : ℕ → ℝ := fun m => C₀ + Cf (m + d + 1) with hA
  have hApos : ∀ m, 0 < A m := fun m => add_pos hC₀ (hCf _).1
  have hglob : ∀ m : ℕ, ∀ z : Euc d, z ≠ 0 →
      |K' z| ≤ A m * ‖z‖ ^ (-((m + d + 1 : ℕ) : ℝ)) := fun m =>
    text_Kt_global hγ hγd hC₀ hnear' (M := m + d + 1) (by omega) (hCf _).1 (hfar' (m + d + 1))
  set S : ℕ → ℝ := fun M => ∑' l : Lattice d, ‖Lattice.toEuc l‖ ^ (-(M : ℝ)) with hS
  have hSnn : ∀ M, 0 ≤ S M := fun M => tsum_nonneg fun l => by positivity
  set E : ℕ → ℝ := fun m => A m * ((2 * d) ^ (m + d + 1) * S (m + d + 1)) with hE
  have hEnn : ∀ m, 0 ≤ E m := fun m => by
    have := hApos m; have := hSnn (m + d + 1); simp only [hE]; positivity
  set q₁ : ℝ := ((d : ℝ) / 2) ^ (γ - d) with hq₁
  have hq₁pos : 0 < q₁ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨C₀ + E 0 / q₁ + 1, by have := hEnn 0; positivity,
    fun m => Cf m + E m * ((d : ℝ) / 2) ^ m + 1, fun m => by
      have := (hCf m).1; have := hEnn m; positivity, ?_⟩
  intro η hη hη1
  set f : Euc d → ℝ := textKeta K' γ η with hf
  have hfm : Measurable f := text_Keta_measurable hKm γ η
  have hfint : Integrable f := text_Keta_integrable hK'int hη γ
  have hfb : ∀ m : ℕ, ∀ z : Euc d, z ≠ 0 →
      |f z| ≤ (A m * η ^ (γ - d + ((m + d + 1 : ℕ) : ℝ))) * ‖z‖ ^ (-((m + d + 1 : ℕ) : ℝ)) :=
    fun m => text_Keta_bound hη (hApos m).le (hglob m)
  have hsum : ∀ y : Euc d, Summable fun l : Lattice d => f (y + Lattice.toEuc l) := by
    intro y
    refine tpos_summable_shift (C := A 0 * η ^ (γ - d + (((0 : ℕ) + d + 1 : ℕ) : ℝ)))
      (r := (((0 : ℕ) + d + 1 : ℕ) : ℝ)) (by have := hApos 0; positivity) ?_ (hfb 0) y
    push_cast; linarith
  have htail : ∀ (m : ℕ) (x : Torus d),
      |perio f x| ≤ |f (KernelGrad.centeredRep x)| + E m * η ^ (γ + m + 1) := by
    intro m x
    have hc : ∀ i, |KernelGrad.centeredRep x i| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le x
    have hx : perio f x = perio f (Torus.mk (KernelGrad.centeredRep x)) := by
      rw [KernelGrad.mk_centeredRep]
    rw [hx]
    have := text_perio_bound hd (f := f) (T := A m * η ^ (γ - d + ((m + d + 1 : ℕ) : ℝ)))
      (M := m + d + 1) (by have := hApos m; positivity) (by omega) (hfb m)
      (KernelGrad.centeredRep x) hc
    refine this.trans (le_of_eq ?_)
    have he : η ^ (γ - d + ((m + d + 1 : ℕ) : ℝ)) = η ^ (γ + m + 1) := by
      congr 1; push_cast; ring
    rw [he]
    simp only [hE, hS]
    ring
  refine ⟨perio f, text_integrable_perio_signed hfm hfint hsum, ?_, ?_, ?_⟩
  · intro k
    rw [tpos_fcoef_perio hfm hfint hsum k, hf, text_fourier_Keta hη K' γ, hFT',
      text_symbol_scale hγ.ne' hη k]
  · intro x hx0 hxη
    set c := KernelGrad.centeredRep x with hcdef
    have hc : ∀ i, |c i| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le x
    have hr : KernelGrad.tdist x 0 = ‖c‖ := KernelGrad.tdist_zero_right x
    have hxc : x = Torus.mk c := (KernelGrad.mk_centeredRep x).symm
    have hc0 : c ≠ 0 := by
      intro h0; apply hx0; rw [hxc, h0]
      ext i; simp [Torus.mk]
    have hrpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
    rw [hr] at hxη ⊢
    have hfc : |f c| ≤ C₀ * ‖c‖ ^ (γ - d) := by
      have hne : η⁻¹ • c ≠ 0 := by
        intro h; apply hc0
        have := congrArg (fun v => η • v) h
        simpa [smul_smul, hη.ne'] using this
      have hn : ‖η⁻¹ • c‖ = ‖c‖ / η := text_norm_inv_smul hη c
      have h1 := hnear' _ hne (by rw [hn, div_le_one hη]; exact hxη)
      rw [hn] at h1
      calc |f c| = η ^ (γ - d) * |K' (η⁻¹ • c)| := by
            simp only [hf, textKeta]
            rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hη _)]
        _ ≤ η ^ (γ - d) * (C₀ * (‖c‖ / η) ^ (γ - d)) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hη _).le
        _ = C₀ * ‖c‖ ^ (γ - d) := by rw [← text_alg1 (a := γ - d) hη hrpos.le]; ring
    have hcle : ‖c‖ ≤ d / 2 := text_cRep_norm_le c hc
    have hq : q₁ ≤ ‖c‖ ^ (γ - d) :=
      Real.rpow_le_rpow_of_nonpos hrpos hcle (by linarith)
    have hηpow : η ^ (γ + (0 : ℕ) + 1) ≤ 1 :=
      Real.rpow_le_one hη.le hη1 (by push_cast; linarith)
    have h1 := htail 0 x
    have hE0 := hEnn 0
    have hrp : 0 ≤ ‖c‖ ^ (γ - d) := by positivity
    calc |perio f x| ≤ |f c| + E 0 * η ^ (γ + ((0 : ℕ) : ℝ) + 1) := h1
      _ ≤ C₀ * ‖c‖ ^ (γ - d) + E 0 * 1 :=
          add_le_add hfc (mul_le_mul_of_nonneg_left hηpow hE0)
      _ ≤ C₀ * ‖c‖ ^ (γ - d) + (E 0 / q₁) * ‖c‖ ^ (γ - d) := by
          refine add_le_add_right ?_ _
          rw [mul_one]
          calc E 0 = (E 0 / q₁) * q₁ := by field_simp
            _ ≤ (E 0 / q₁) * ‖c‖ ^ (γ - d) :=
                mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ (C₀ + E 0 / q₁ + 1) * ‖c‖ ^ (γ - d) := by nlinarith
  · intro m x hxη
    set c := KernelGrad.centeredRep x with hcdef
    have hc : ∀ i, |c i| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le x
    have hr : KernelGrad.tdist x 0 = ‖c‖ := KernelGrad.tdist_zero_right x
    rw [hr] at hxη ⊢
    have hrpos : 0 < ‖c‖ := lt_of_lt_of_le hη hxη
    have hc0 : c ≠ 0 := norm_pos_iff.1 hrpos
    have hfc : |f c| ≤ Cf m * (η ^ (γ - d + m) * ‖c‖ ^ (-(m : ℝ))) := by
      have hn : ‖η⁻¹ • c‖ = ‖c‖ / η := text_norm_inv_smul hη c
      have h1 := hfar' m (η⁻¹ • c) (by rw [hn, le_div_iff₀ hη]; linarith)
      rw [hn] at h1
      calc |f c| = η ^ (γ - d) * |K' (η⁻¹ • c)| := by
            simp only [hf, textKeta]
            rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hη _)]
        _ ≤ η ^ (γ - d) * (Cf m * (‖c‖ / η) ^ (-(m : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hη _).le
        _ = Cf m * (η ^ (γ - d + m) * ‖c‖ ^ (-(m : ℝ))) := by
            rw [← text_alg2 m hη hrpos]; ring
    have hcle : ‖c‖ ≤ d / 2 := text_cRep_norm_le c hc
    have hQ : 1 ≤ ((d : ℝ) / 2) ^ m * ‖c‖ ^ (-(m : ℝ)) := by
      rw [Real.rpow_neg hrpos.le, Real.rpow_natCast, ← div_eq_mul_inv, ← div_pow]
      exact one_le_pow₀ ((one_le_div hrpos).2 hcle)
    have hP : η ^ (γ + (m : ℝ) + 1) ≤ η ^ (γ - d + m) :=
      Real.rpow_le_rpow_of_exponent_ge hη hη1 (by linarith)
    have hPpos : 0 < η ^ (γ - d + m) := Real.rpow_pos_of_pos hη _
    have hQpos : 0 < ‖c‖ ^ (-(m : ℝ)) := Real.rpow_pos_of_pos hrpos _
    have hEm := hEnn m
    have hCfm := (hCf m).1
    have h1 := htail m x
    calc |perio f x| ≤ |f c| + E m * η ^ (γ + (m : ℝ) + 1) := h1
      _ ≤ Cf m * (η ^ (γ - d + m) * ‖c‖ ^ (-(m : ℝ))) + E m * η ^ (γ - d + m) :=
          add_le_add hfc (mul_le_mul_of_nonneg_left hP hEm)
      _ ≤ Cf m * (η ^ (γ - d + m) * ‖c‖ ^ (-(m : ℝ))) +
            E m * (((d : ℝ) / 2) ^ m * ‖c‖ ^ (-(m : ℝ))) * η ^ (γ - d + m) := by
          refine add_le_add_right ?_ _
          have : E m * η ^ (γ - d + m) * 1 ≤
              E m * η ^ (γ - d + m) * (((d : ℝ) / 2) ^ m * ‖c‖ ^ (-(m : ℝ))) :=
            mul_le_mul_of_nonneg_left hQ (by positivity)
          linarith
      _ ≤ (Cf m + E m * ((d : ℝ) / 2) ^ m + 1) * η ^ (γ - d + m) * ‖c‖ ^ (-(m : ℝ)) := by
          have : 0 ≤ η ^ (γ - d + m) * ‖c‖ ^ (-(m : ℝ)) := by positivity
          nlinarith

end HRS.Commutator.TorusNote
