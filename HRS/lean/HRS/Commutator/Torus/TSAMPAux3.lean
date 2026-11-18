import HRS.Commutator.Torus.TSAMPAux2

/-!
# T-SAMP helpers, part 3: the periodised rescaled kernel (generic form)

Torus version of `text_mult_kernel_main`'s second half, for an arbitrary measurable integrable kernel
`K̃` on `ℝ^d` with `|K̃(x)| ≤ C₀|x|^a` (`|x| ≤ 1`, `-d ≤ a ≤ 0`) and `|K̃(x)| ≤ C_m|x|^{-m}` (`|x| ≥ 1`):
`Ψ_η = perio (η^{γ-d} K̃(·/η))`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_Kt_global {a : ℝ} (ha : -(d : ℝ) ≤ a) {Kt : Euc d → ℝ} {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hnear : ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → |Kt x| ≤ C₀ * ‖x‖ ^ a)
    {M : ℕ} (hM : d ≤ M) {Cm : ℝ} (hCm : 0 < Cm)
    (hfar : ∀ x : Euc d, 1 ≤ ‖x‖ → |Kt x| ≤ Cm * ‖x‖ ^ (-(M : ℝ))) :
    ∀ z : Euc d, z ≠ 0 → |Kt z| ≤ (C₀ + Cm) * ‖z‖ ^ (-(M : ℝ)) := by
  intro z hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  by_cases h1 : ‖z‖ ≤ 1
  · have h2 : ‖z‖ ^ a ≤ ‖z‖ ^ (-(M : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_ge hzpos h1 ?_
      have : (d : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have h3 : 0 ≤ ‖z‖ ^ (-(M : ℝ)) := by positivity
    calc |Kt z| ≤ C₀ * ‖z‖ ^ a := hnear z hz h1
      _ ≤ C₀ * ‖z‖ ^ (-(M : ℝ)) := mul_le_mul_of_nonneg_left h2 hC₀.le
      _ ≤ (C₀ + Cm) * ‖z‖ ^ (-(M : ℝ)) := by nlinarith
  · push Not at h1
    have h3 : 0 ≤ ‖z‖ ^ (-(M : ℝ)) := by positivity
    calc |Kt z| ≤ Cm * ‖z‖ ^ (-(M : ℝ)) := hfar z h1.le
      _ ≤ (C₀ + Cm) * ‖z‖ ^ (-(M : ℝ)) := by nlinarith

theorem tsamp_gk (hd : 1 ≤ d) (a γ : ℝ) (ha0 : a ≤ 0) (had : -(d : ℝ) ≤ a) (hγ : 0 ≤ γ)
    {Kt : Euc d → ℝ} (hKm : Measurable Kt) (hKi : Integrable Kt) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hnear : ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → |Kt x| ≤ C₀ * ‖x‖ ^ a)
    (Cf : ℕ → ℝ) (hCf : ∀ m, 0 < Cf m)
    (hfar : ∀ (m : ℕ) (x : Euc d), 1 ≤ ‖x‖ → |Kt x| ≤ Cf m * ‖x‖ ^ (-(m : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∃ Cm : ℕ → ℝ, (∀ m, 0 < Cm m) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        Integrable (perio (textKeta Kt γ η) : Torus d → ℝ) ∧
        (∀ k : Lattice d, Torus.fcoef (perio (textKeta Kt γ η) : Torus d → ℝ) k =
          ((η ^ γ : ℝ) : ℂ) * 𝓕 (fun y : Euc d => ((Kt y : ℝ) : ℂ)) (η • Lattice.toEuc k)) ∧
        (∀ x : Torus d, x ≠ 0 → KernelGrad.tdist x 0 ≤ η →
          |perio (textKeta Kt γ η) x| ≤ C * η ^ (γ - d - a) * KernelGrad.tdist x 0 ^ a) ∧
        (∀ (m : ℕ) (x : Torus d), η ≤ KernelGrad.tdist x 0 →
          |perio (textKeta Kt γ η) x| ≤ Cm m * η ^ (γ - d + m) * KernelGrad.tdist x 0 ^ (-(m : ℝ))) ∧
        ∫⁻ x, ‖perio (textKeta Kt γ η) x‖ₑ ≤ ENNReal.ofReal (η ^ γ * ∫ y, ‖Kt y‖) := by
  classical
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set A : ℕ → ℝ := fun m => C₀ + Cf (m + d + 1) with hA
  have hApos : ∀ m, 0 < A m := fun m => add_pos hC₀ (hCf _)
  have hglob : ∀ m : ℕ, ∀ z : Euc d, z ≠ 0 →
      |Kt z| ≤ A m * ‖z‖ ^ (-((m + d + 1 : ℕ) : ℝ)) := fun m =>
    tsamp_Kt_global had hC₀ hnear (M := m + d + 1) (by omega) (hCf _) (hfar (m + d + 1))
  set S : ℕ → ℝ := fun M => ∑' l : Lattice d, ‖Lattice.toEuc l‖ ^ (-(M : ℝ)) with hS
  have hSnn : ∀ M, 0 ≤ S M := fun M => tsum_nonneg fun l => by positivity
  set E : ℕ → ℝ := fun m => A m * ((2 * d) ^ (m + d + 1) * S (m + d + 1)) with hE
  have hEnn : ∀ m, 0 ≤ E m := fun m => by
    have := hApos m; have := hSnn (m + d + 1); simp only [hE]; positivity
  set q₁ : ℝ := ((d : ℝ) / 2) ^ a with hq₁
  have hq₁pos : 0 < q₁ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨C₀ + E 0 / q₁ + 1, by have := hEnn 0; positivity,
    fun m => Cf m + E m * ((d : ℝ) / 2) ^ m + 1, fun m => by
      have := hCf m; have := hEnn m; positivity, ?_⟩
  intro η hη hη1
  set f : Euc d → ℝ := textKeta Kt γ η with hf
  have hfm : Measurable f := text_Keta_measurable hKm γ η
  have hfint : Integrable f := text_Keta_integrable hKi hη γ
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
  refine ⟨text_integrable_perio_signed hfm hfint hsum, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [tpos_fcoef_perio hfm hfint hsum k, hf, text_fourier_Keta hη Kt γ]
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
    have hfc : |f c| ≤ C₀ * η ^ (γ - d - a) * ‖c‖ ^ a := by
      have hne : η⁻¹ • c ≠ 0 := by
        intro h; apply hc0
        have := congrArg (fun v => η • v) h
        simpa [smul_smul, hη.ne'] using this
      have hn : ‖η⁻¹ • c‖ = ‖c‖ / η := text_norm_inv_smul hη c
      have h1 := hnear _ hne (by rw [hn, div_le_one hη]; exact hxη)
      rw [hn] at h1
      calc |f c| = η ^ (γ - d) * |Kt (η⁻¹ • c)| := by
            simp only [hf, textKeta]
            rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hη _)]
        _ ≤ η ^ (γ - d) * (C₀ * (‖c‖ / η) ^ a) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hη _).le
        _ = C₀ * η ^ (γ - d - a) * ‖c‖ ^ a := by
            rw [← text_alg1 (a := a) hη hrpos.le, show γ - d = (γ - d - a) + a by ring,
              Real.rpow_add hη, show γ - d - a + a - a = γ - d - a by ring]
            ring
    have hcle : ‖c‖ ≤ d / 2 := text_cRep_norm_le c hc
    have hq : q₁ ≤ ‖c‖ ^ a := Real.rpow_le_rpow_of_nonpos hrpos hcle ha0
    have hηpow : η ^ (γ + (0 : ℕ) + 1) ≤ η ^ (γ - d - a) :=
      Real.rpow_le_rpow_of_exponent_ge hη hη1 (by push_cast; linarith)
    have h1 := htail 0 x
    have hE0 := hEnn 0
    have hrp : 0 ≤ ‖c‖ ^ a := by positivity
    have hηp : 0 < η ^ (γ - d - a) := Real.rpow_pos_of_pos hη _
    calc |perio f x| ≤ |f c| + E 0 * η ^ (γ + ((0 : ℕ) : ℝ) + 1) := h1
      _ ≤ C₀ * η ^ (γ - d - a) * ‖c‖ ^ a + E 0 * η ^ (γ - d - a) :=
          add_le_add hfc (mul_le_mul_of_nonneg_left hηpow hE0)
      _ ≤ C₀ * η ^ (γ - d - a) * ‖c‖ ^ a + (E 0 / q₁) * η ^ (γ - d - a) * ‖c‖ ^ a := by
          refine add_le_add_right ?_ _
          calc E 0 * η ^ (γ - d - a) = (E 0 / q₁) * q₁ * η ^ (γ - d - a) := by field_simp
            _ = (E 0 / q₁) * η ^ (γ - d - a) * q₁ := by ring
            _ ≤ (E 0 / q₁) * η ^ (γ - d - a) * ‖c‖ ^ a :=
                mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ (C₀ + E 0 / q₁ + 1) * η ^ (γ - d - a) * ‖c‖ ^ a := by
          have : 0 ≤ η ^ (γ - d - a) * ‖c‖ ^ a := by positivity
          nlinarith
  · intro m x hxη
    set c := KernelGrad.centeredRep x with hcdef
    have hc : ∀ i, |c i| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le x
    have hr : KernelGrad.tdist x 0 = ‖c‖ := KernelGrad.tdist_zero_right x
    rw [hr] at hxη ⊢
    have hrpos : 0 < ‖c‖ := lt_of_lt_of_le hη hxη
    have hc0 : c ≠ 0 := norm_pos_iff.1 hrpos
    have hfc : |f c| ≤ Cf m * (η ^ (γ - d + m) * ‖c‖ ^ (-(m : ℝ))) := by
      have hn : ‖η⁻¹ • c‖ = ‖c‖ / η := text_norm_inv_smul hη c
      have h1 := hfar m (η⁻¹ • c) (by rw [hn, le_div_iff₀ hη]; linarith)
      rw [hn] at h1
      calc |f c| = η ^ (γ - d) * |Kt (η⁻¹ • c)| := by
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
    have hCfm := hCf m
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
  · -- the `L¹` bound
    have hsum' : ∀ y : Euc d, Summable fun l : Lattice d => (fun z => |f z|) (y + Lattice.toEuc l) :=
      fun y => (hsum y).abs
    have hPm : AEStronglyMeasurable (perio f : Torus d → ℝ) volume :=
      (tpos_perio_measurable hfm).aestronglyMeasurable
    have hfn : ∫ y, ‖f y‖ = η ^ γ * ∫ x, ‖Kt x‖ := by
      have h1 : ∀ y : Euc d, ‖f y‖ = η ^ (γ - d) * ‖Kt (η⁻¹ • y)‖ := fun y => by
        simp only [hf, textKeta, norm_mul, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos hη _)]
      simp_rw [h1]
      rw [integral_const_mul, MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
        (μ := (volume : Measure (Euc d))) (fun x : Euc d => ‖Kt x‖) hη.le,
        finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc, Real.rpow_sub hη, Real.rpow_natCast]
      congr 1
      field_simp
    calc ∫⁻ x, ‖perio f x‖ₑ ≤ ∫⁻ x, ENNReal.ofReal (perio (fun z => |f z|) x) := by
          refine lintegral_mono fun x => ?_
          rw [Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          unfold perio
          exact (norm_tsum_le_tsum_norm (hsum _).norm).trans (le_of_eq (by simp))
      _ = ∫⁻ y, ENNReal.ofReal |f y| :=
          tpos_lintegral_perio hfm.abs (fun z => abs_nonneg _) hsum'
      _ = ENNReal.ofReal (∫ y, ‖f y‖) := by
          rw [ofReal_integral_norm_eq_lintegral_enorm hfint]
          refine lintegral_congr fun y => ?_
          rw [Real.enorm_eq_ofReal_abs]
      _ = ENNReal.ofReal (η ^ γ * ∫ y, ‖Kt y‖) := by rw [hfn]

end HRS.Commutator.TorusNote
