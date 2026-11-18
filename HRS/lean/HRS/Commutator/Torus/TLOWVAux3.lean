import HRS.Commutator.Torus.TLOWVAux2

/-!
# T-LOWV helpers, part 3: trigonometric expansions of `P^η_≤ v`, `∇g_≤` and the commutator kernel; the
Fourier-support lemma `𝒞_{g_≤}(P_≤ v, σ)` depends only on `σ̂` at `η|k| < 4`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tlowv_inner_eq (x y : Euc d) : inner ℝ x y = ∑ i, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma tlowv_enorm_add (k m : Lattice d) : Lattice.enorm (k + m) ≤ Lattice.enorm k + Lattice.enorm m := by
  unfold Lattice.enorm
  rw [ten_toEuc_add]
  exact norm_add_le _ _

lemma tlowv_enorm_neg (k : Lattice d) : Lattice.enorm (-k) = Lattice.enorm k := by
  unfold Lattice.enorm
  rw [ten_toEuc_neg, norm_neg]

lemma tlowv_enorm_sub (k m : Lattice d) : Lattice.enorm (k - m) ≤ Lattice.enorm k + Lattice.enorm m := by
  rw [sub_eq_add_neg]
  have := tlowv_enorm_add k (-m)
  rwa [tlowv_enorm_neg] at this

/-- A continuous real function with finitely supported coefficients is its (finite) trigonometric sum. -/
lemma tlowv_trig_of_fcoef {φ : Torus d → ℝ} (hφ : Continuous φ) {n : ℕ} {c : Lattice d → ℂ}
    (hc : HRS.PDE.IsTrigPoly n c) (hco : ∀ k, Torus.fcoef φ k = c k) (z : Torus d) :
    ((φ z : ℝ) : ℂ) = ∑ k ∈ HRS.PDE.Kern.boxF d n, c k * Torus.mode k z := by
  have hs : Summable fun k : Lattice d => ‖∫ x, Torus.mode (-k) x * ((φ x : ℝ) : ℂ)‖ := by
    have := (HRS.PDE.R2Aux.summable_norm_of_trig hc)
    refine this.congr fun k => ?_
    have := hco k
    unfold Torus.fcoef at this
    rw [this]
  have h := tkr_series (F := fun x => ((φ x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hφ) hs z
  have e : ∀ k, (∫ x, Torus.mode (-k) x * ((φ x : ℝ) : ℂ)) = c k := fun k => hco k
  simp_rw [e] at h
  rw [← h.tsum_eq]
  exact HRS.PDE.Kern.trig_eq_sum hc z

/-- Trigonometric expansion of `P^η_≤ v` (components). -/
lemma tlowv_Pleq_trig (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {v : Torus d → Euc d} {L : ℝ}
    (hL : 0 ≤ L) (hv : IsLipschitzVF L v) (i : Fin d) (z : Torus d) :
    ((PleqT η v z i : ℝ) : ℂ) = ∑ k ∈ HRS.PDE.Kern.boxF d ⌈2 / η⌉₊,
      (((tkrChi η k : ℝ) : ℂ) * Torus.fcoef (fun x => v x i) k) * Torus.mode k z := by
  obtain ⟨B, C₁, C₂, hB, hC₁, hC₂, hker⟩ := tsamp_psi_kernel (d := d) hd
  obtain ⟨hKint, hKb, hK1, hKcoef, -⟩ := hker η hη hη1
  set Kη : Torus d → ℝ := perio (Whole.psiL (d := d) η⁻¹) with hKη
  have hKm : Measurable Kη := by
    obtain ⟨hc, -⟩ := text_psiL_props (d := d) η⁻¹ (inv_pos.2 hη)
    exact tpos_perio_measurable hc.measurable
  have hvint : Integrable v := tsamp_integrable_of_lip hL hv
  have hlip := tsamp_conv_lip hKint hL hv
  have hcont : Continuous (tsampConv Kη v) := tsamp_lip_continuous hlip
  have hco : ∀ k, Torus.fcoef (fun x => PleqT η v x i) k =
      ((tkrChi η k : ℝ) : ℂ) * Torus.fcoef (fun x => v x i) k := by
    intro k
    have := tsamp_conv_fcoef_comp hd hKm hKint hKb hvint i k
    rw [hKcoef k] at this
    exact this
  have hT : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊
      (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * Torus.fcoef (fun x => v x i) k) :=
    tkr_isTrigPoly hη (fun k hk => by
      intro h0; apply hk; simp [h0])
  have hcpt : Continuous fun x => PleqT η v x i :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hcont
  exact tlowv_trig_of_fcoef hcpt hT hco z

/-- Trigonometric expansion of `∇g_≤` (components). -/
lemma tlowv_glo_trig (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η)
    (i : Fin d) (z : Torus d) :
    ((gloForceT s η z i : ℝ) : ℂ) = ∑ k ∈ HRS.PDE.Kern.boxF d ⌈2 / η⌉₊,
      (((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) * Torus.mode k z := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hT2 : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊
      (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) :=
    tkr_isTrigPoly hη (fun k hk => by
      intro h0; apply hk; simp [h0])
  have := tkr_glo hd2 hs0 hsd1 hη z i
  rw [HRS.PDE.Kern.trig_eq_sum hT2] at this
  exact this

/-- The commutator kernel of trigonometric polynomials as a sum of products of modes. -/
theorem tlowv_comm_trig_kernel (B : Finset (Lattice d)) (V F : Torus d → Euc d)
    (cV cF : Fin d → Lattice d → ℂ)
    (hV : ∀ i z, ((V z i : ℝ) : ℂ) = ∑ k ∈ B, cV i k * Torus.mode k z)
    (hF : ∀ i z, ((F z i : ℝ) : ℂ) = ∑ m ∈ B, cF i m * Torus.mode m z) (x y : Torus d) :
    ((commKernel F V x y : ℝ) : ℂ) =
      ∑ a ∈ (Finset.univ : Finset (Fin d)) ×ˢ (B ×ˢ (B ×ˢ (Finset.univ : Finset Bool))),
        (cV a.1 a.2.1 * cF a.1 a.2.2.1 * (if a.2.2.2 then 1 else -1)) *
          Torus.mode (if a.2.2.2 then a.2.1 + a.2.2.1 else a.2.2.1) x *
          Torus.mode (if a.2.2.2 then -a.2.2.1 else a.2.1 - a.2.2.1) y := by
  have h1 : ((commKernel F V x y : ℝ) : ℂ) =
      ∑ i, (((V x i : ℝ) : ℂ) - ((V y i : ℝ) : ℂ)) * ((F (x - y) i : ℝ) : ℂ) := by
    unfold commKernel
    split_ifs with h
    · subst h; simp
    · rw [tlowv_inner_eq]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [PiLp.sub_apply]
  have h2 : ∀ i, (((V x i : ℝ) : ℂ) - ((V y i : ℝ) : ℂ)) * ((F (x - y) i : ℝ) : ℂ) =
      ∑ k ∈ B, ∑ m ∈ B, cV i k * cF i m *
        (Torus.mode (k + m) x * Torus.mode (-m) y - Torus.mode m x * Torus.mode (k - m) y) := by
    intro i
    rw [hV i x, hV i y, hF i (x - y), ← Finset.sum_sub_distrib, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
    rw [tkr_mode_sub m x y, Torus.mode_add, sub_eq_add_neg k m, Torus.mode_add]
    ring
  rw [h1]
  simp_rw [h2]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fintype.sum_bool]
  simp only [ite_true, ite_false, Bool.false_eq_true]
  ring

/-- Fourier-support lemma for the commutator pairing with trigonometric `V`, `F`. -/
theorem tlowv_comm_congr (σ τ : SMT d) (hσ : σ.IsFinite) (hτ : τ.IsFinite) (B : Finset (Lattice d))
    (V F : Torus d → Euc d) (cV cF : Fin d → Lattice d → ℂ)
    (hV : ∀ i z, ((V z i : ℝ) : ℂ) = ∑ k ∈ B, cV i k * Torus.mode k z)
    (hF : ∀ i z, ((F z i : ℝ) : ℂ) = ∑ m ∈ B, cF i m * Torus.mode m z) {R : ℝ}
    (hcV : ∀ i k, cV i k ≠ 0 → Lattice.enorm k < R) (hcF : ∀ i m, cF i m ≠ 0 → Lattice.enorm m < R)
    (hστ : ∀ j : Lattice d, Lattice.enorm j < 2 * R → σ.coef j = τ.coef j) :
    CcommT F V σ = CcommT F V τ := by
  unfold CcommT
  refine tlowv_pair2_congr σ τ hσ hτ
    ((Finset.univ : Finset (Fin d)) ×ˢ (B ×ˢ (B ×ˢ (Finset.univ : Finset Bool))))
    (fun a => if a.2.2.2 then a.2.1 + a.2.2.1 else a.2.2.1)
    (fun a => if a.2.2.2 then -a.2.2.1 else a.2.1 - a.2.2.1)
    (fun a => cV a.1 a.2.1 * cF a.1 a.2.2.1 * (if a.2.2.2 then 1 else -1))
    (commKernel F V) (fun x y => tlowv_comm_trig_kernel B V F cV cF hV hF x y) ?_
  intro a ha hγ
  obtain ⟨i, k, m, b⟩ := a
  simp only at hγ ⊢
  have hk : cV i k ≠ 0 := by
    intro h0; apply hγ; rw [h0]; simp
  have hm : cF i m ≠ 0 := by
    intro h0; apply hγ; rw [h0]; simp
  have hk' := hcV i k hk
  have hm' := hcF i m hm
  have hk0 : 0 ≤ Lattice.enorm k := norm_nonneg _
  have hm0 : 0 ≤ Lattice.enorm m := norm_nonneg _
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    refine ⟨hστ _ ?_, hστ _ ?_⟩
    · rw [tlowv_enorm_neg]; linarith
    · rw [tlowv_enorm_neg]
      have := tlowv_enorm_sub k m
      linarith
  · simp only [ite_true]
    refine ⟨hστ _ ?_, hστ _ ?_⟩
    · rw [tlowv_enorm_neg]
      have := tlowv_enorm_add k m
      linarith
    · rw [tlowv_enorm_neg, tlowv_enorm_neg]; linarith

end HRS.Commutator.TorusNote
