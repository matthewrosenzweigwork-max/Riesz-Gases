import HRS.ME.ParxUConormal1
import HRS.Equilibrium.Parametrix.PX4aAuxL

/-!
# Packet P1b (part 1): uniform `psii_conormal` and `snsrc_srcCls`

Uniform versions (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.psii_conormal` (PX4aAuxL:34) and `HRS.Parx.snsrc_srcCls` (PX4aAuxL:98).

The only ρ-dependent constant of `psii_conormal` is `cbNorm2 (m-1) (fun x _ => ρ x)`; it is bounded
by `(m + 0) · |Λ₀|` through the extractor `ParxU.cbNorm2_rho_le` (built from the uniform bound
`iter_lift_le_unif` on the iterated derivatives of `lift ρ` and the projection bound
`HRS.PDE.MFPair.norm_iter_comp_fst_ps`). `snsrc_srcCls` uses `psii_conormal` for its finitely
many components; `gsrc_srcCls` is ρ-free and is used unchanged.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- Extractor: the `C^k` norm of `(x, y) ↦ ρ x` is bounded by `(k + 1) |Λ₀|` for `k ≤ N`. -/
theorem ParxU.cbNorm2_rho_le {β : ℝ} {V ρ : Torus d → ℝ} (U : ParxU d s N νm νp c₀ Λ₀ β V ρ)
    {k : ℕ} (hk : k ≤ N) : PDE.cbNorm2 k (fun x _ => ρ x) ≤ ((k : ℝ) + 1) * |Λ₀| := by
  have hρtop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ) := U.H.rho_smooth.smooth
  have hρs : ContDiff ℝ (N : WithTop ℕ∞) (Torus.lift ρ) :=
    hρtop.of_le (by exact_mod_cast le_top)
  unfold PDE.cbNorm2
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (PDE.lift2 (fun x _ => ρ x)) p‖) ≤ |Λ₀| := by
    intro j hj
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    refine ciSup_le fun p => ?_
    have e : PDE.lift2 (fun x _ => ρ x) = fun q : Euc d × Euc d => Torus.lift ρ q.1 := rfl
    rw [e]
    exact (HRS.PDE.MFPair.norm_iter_comp_fst_ps hρs hjN p).trans (iter_lift_le_unif U hjN p.1)
  calc _ ≤ ∑ _j ∈ Finset.range (k + 1), |Λ₀| := Finset.sum_le_sum hterm
    _ = ((k : ℝ) + 1) * |Λ₀| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- **Uniform version of `psii_conormal`.** The constant depends only on `(d, s, N, Λ₀, m)`
(through `Cm = conormal_mul_smooth_aux` and `cbNorm2 (m-1) ρ ≤ m |Λ₀|`); it is chosen before
`β, V, ρ`. -/
theorem psii_conormal_unif (m : ℕ) (hm : 1 ≤ m) (hN : m ≤ N) (τ : ℝ) (b : ℕ) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (Ψ : Torus d → Torus d → ℝ), 0 ≤ B →
      ConormalL τ (fun _ => b) m B Ψ →
      ConormalL (τ + 1) (fun _ => b) (m - 1) (C * B) (Psii ρ Ψ i) := by
  obtain ⟨Cm, hCm0, hCm⟩ := conormal_mul_smooth_aux (d := d) (m - 1) (τ + 1) (fun _ => b)
  refine ⟨Cm * ((((m - 1 : ℕ) : ℝ) + 1) * |Λ₀|) * 2, by positivity,
    fun β V ρ U B Ψ hB hΨ => ?_⟩
  set a : Torus d → Torus d → ℝ := fun x _ => ρ x with ha
  have hρ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ) := U.H.rho_smooth.smooth
  have haC : PDE.IsCk2 (m - 1) a := by
    unfold PDE.IsCk2
    have : PDE.lift2 a = fun p : Euc d × Euc d => Torus.lift ρ p.1 := rfl
    rw [this]
    exact (hρ'.comp contDiff_fst).of_le (natCast_le_infty (m - 1))
  have hA : PDE.cbNorm2 (m - 1) a ≤ (((m - 1 : ℕ) : ℝ) + 1) * |Λ₀| :=
    U.cbNorm2_rho_le (by omega)
  have hcb0 : 0 ≤ PDE.cbNorm2 (m - 1) a := PDE.MFPair.cbNorm2_nonneg (m - 1) a
  have h1 := conormal_partial_fst_aux hΨ hm i
  have h1' : ConormalL (τ + 1) (fun _ => b) (m - 1) (2 * B)
      (fun x y => Torus.partialDeriv i (fun z => Ψ z y) x) :=
    conormalL_mono_b (by positivity) (fun c => by simp) h1
  have h2 := hCm (2 * B) _ a h1' haC
  have hle : Cm * PDE.cbNorm2 (m - 1) a * (2 * B) ≤
      Cm * ((((m - 1 : ℕ) : ℝ) + 1) * |Λ₀|) * (2 * B) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hCm0) (by positivity)
  have h2' : ConormalL (τ + 1) (fun _ => b) (m - 1) (Cm * PDE.cbNorm2 (m - 1) a * (2 * B))
      (fun x y => a x y * Torus.partialDeriv i (fun z => Ψ z y) x) :=
    conormalL_mono_b (mul_nonneg (mul_nonneg hCm0 hcb0) (by positivity)) (fun c => by simp) h2
  have h3 : ConormalL (τ + 1) (fun _ => b) (m - 1)
      (Cm * ((((m - 1 : ℕ) : ℝ) + 1) * |Λ₀|) * (2 * B))
      (fun x y => a x y * Torus.partialDeriv i (fun z => Ψ z y) x) :=
    conormalL_mono_B h2' (mul_nonneg (mul_nonneg hCm0 hcb0) (by positivity)) hle
  have h4 : ConormalL (τ + 1) (fun _ => b) (m - 1)
      (Cm * ((((m - 1 : ℕ) : ℝ) + 1) * |Λ₀|) * 2 * B)
      (fun x y => a x y * Torus.partialDeriv i (fun z => Ψ z y) x) := by
    have e : Cm * ((((m - 1 : ℕ) : ℝ) + 1) * |Λ₀|) * (2 * B) =
        Cm * ((((m - 1 : ℕ) : ℝ) + 1) * |Λ₀|) * 2 * B := by ring
    rw [e] at h3
    exact h3
  exact h4

/-- **Uniform version of `snsrc_srcCls`.** The constant depends only on `(d, s, N, Λ₀, m')`
and on the level `m' + 2 ≤ N`; it is chosen before `β, V, ρ`. -/
theorem snsrc_srcCls_unif (m' : ℕ) (hN : m' + 2 ≤ N) (τ : ℝ) (b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (Ψ : Torus d → Torus d → ℝ), 0 ≤ B →
      ConormalL τ (fun _ => b) (m' + 2) B Ψ →
      SrcCls d (τ + 2) b m' (K * B) (SNsrc ρ Ψ) ∧
      (∀ X w : Euc d, 1 / 32 < ‖w‖ → SNsrc ρ Ψ (X, w) = 0) ∧
      (∀ X w n : Euc d, IsLat n → SNsrc ρ Ψ (X + n, w) = SNsrc ρ Ψ (X, w)) ∧
      (∀ i : Fin d, SrcCls d (τ + 1) b (m' + 1) (K * B) (Gsrc (Psii ρ Ψ i)) ∧
        (∀ X w : Euc d, 1 / 32 < ‖w‖ → Gsrc (Psii ρ Ψ i) (X, w) = 0) ∧
        (∀ X w n : Euc d, IsLat n → Gsrc (Psii ρ Ψ i) (X + n, w) = Gsrc (Psii ρ Ψ i) (X, w))) := by
  classical
  have hm : 1 ≤ m' + 2 := by omega
  choose C hC0 hC using fun i : Fin d => psii_conormal_unif (d := d) (s := s) (N := N) (νm := νm)
    (νp := νp) (c₀ := c₀) (Λ₀ := Λ₀) (m' + 2) hm hN τ b i
  obtain ⟨K1, hK10, hK1⟩ := gsrc_srcCls (d := d) (m' + 1) (τ + 1) b
  set Cs : ℝ := ∑ i, C i with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun i _ => hC0 i
  have hCle : ∀ i, C i ≤ Cs := fun i =>
    Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ i)
  refine ⟨(d : ℝ) * (K1 * (Cs + 1)), by positivity, fun β V ρ U B Ψ hB hΨ => ?_⟩
  have hPsi : ∀ i : Fin d, Conormal (τ + 1) b (m' + 1) ((Cs + 1) * B) (Psii ρ Ψ i) := by
    intro i
    have h1 := hC i β V ρ U B Ψ hB hΨ
    have e : m' + 2 - 1 = m' + 1 := by omega
    rw [e] at h1
    refine conormalL_mono_B h1 (mul_nonneg (hC0 i) hB) ?_
    nlinarith [hCle i, mul_nonneg hCs0 hB]
  have hG : ∀ i : Fin d, SrcCls d (τ + 1) b (m' + 1) (K1 * ((Cs + 1) * B)) (Gsrc (Psii ρ Ψ i)) ∧
      (∀ X w : Euc d, 1 / 32 < ‖w‖ → Gsrc (Psii ρ Ψ i) (X, w) = 0) ∧
      (∀ X w n : Euc d, IsLat n → Gsrc (Psii ρ Ψ i) (X + n, w) = Gsrc (Psii ρ Ψ i) (X, w)) :=
    fun i => hK1 ((Cs + 1) * B) (Psii ρ Ψ i) (by positivity) (hPsi i)
  have hAeq : K1 * ((Cs + 1) * B) = K1 * (Cs + 1) * B := by ring
  have hS : ∀ i : Fin d, SrcCls d (τ + 2) b m' (K1 * ((Cs + 1) * B) * ‖eVec d i‖)
      (Ssrc (Gsrc (Psii ρ Ψ i)) i) := by
    intro i
    have := (hG i).1.dirD_snd (mul_nonneg hK10 (by positivity)) (eVec d i)
    have e : τ + 1 + 1 = τ + 2 := by ring
    rw [e] at this
    exact this
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · have := SrcCls.sum (σ := τ + 2) (b := b) (m := m') (Finset.univ : Finset (Fin d))
      (fun i => K1 * ((Cs + 1) * B) * ‖eVec d i‖) (fun i => Ssrc (Gsrc (Psii ρ Ψ i)) i)
      (fun i _ => hS i) (fun i _ => by positivity)
    have e : ∑ i : Fin d, K1 * ((Cs + 1) * B) * ‖eVec d i‖ = (d : ℝ) * (K1 * (Cs + 1)) * B := by
      simp only [norm_eVec, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [e] at this
    exact this
  · intro X w hw
    unfold SNsrc Ssrc
    refine Finset.sum_eq_zero fun i _ => ?_
    have hev : Gsrc (Psii ρ Ψ i) =ᶠ[𝓝 (X, w)] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
        (show (1 / 32 : ℝ) < ‖((X, w) : Euc d × Euc d).2‖ from hw)] with p hp
      exact (hG i).2.1 p.1 p.2 hp
    unfold dirD
    rw [hev.fderiv_eq]
    simp
  · intro X w n hn
    unfold SNsrc Ssrc dirD
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Gsrc (Psii ρ Ψ i) = fun p => Gsrc (Psii ρ Ψ i) (p + (n, (0 : Euc d))) := by
      funext p
      obtain ⟨p1, p2⟩ := p
      simpa using ((hG i).2.2 p1 p2 n hn).symm
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := Gsrc (Psii ρ Ψ i)) (x := (X, w)) (n, (0 : Euc d))
    rw [← h1] at this
    simp only [Prod.mk_add_mk, add_zero] at this ⊢
    rw [this]
  · refine ⟨?_, (hG i).2⟩
    have e := (hG i).1
    rw [hAeq] at e
    have hle : K1 * (Cs + 1) * B ≤ (d : ℝ) * (K1 * (Cs + 1)) * B := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast (Fin.pos i)
      have h0 : 0 ≤ K1 * (Cs + 1) * B := by positivity
      nlinarith
    exact e.mono_A (by positivity) hle

end HRS.ME.ParxU

end
