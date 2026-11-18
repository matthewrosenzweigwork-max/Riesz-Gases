import HRS.Equilibrium.Parametrix.PX4aAuxK

/-!
# Packet PX4a auxiliaries L: the sources of the divergence form

`Psii ρ Ψ i = ρ(x) ∂_{x_i} Ψ(x, y)` is conormal of order `τ + 1`; its left chart cut off at
`‖w‖ < 1/32` is a chart source (`gsrc_srcCls`); the `w_i`-derivatives `S_i` are chart sources of
order `τ + 2`, and `SNsrc` is their sum.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma SrcCls.mono_A {σ : ℝ} {b m : ℕ} {A A' : ℝ} {g : Euc d × Euc d → ℝ} (h : SrcCls d σ b m A g)
    (hA : 0 ≤ A) (hAA' : A ≤ A') : SrcCls d σ b m A' g where
  smooth := h.smooth
  supp := h.supp
  bound a c hac X w hw0 := by
    refine (h.bound a c hac X w hw0).trans ?_
    have : 0 ≤ 1 + ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b := by
      have : 0 ≤ ‖w‖ ^ (-(σ + (c : ℝ))) * (1 + |Real.log ‖w‖|) ^ b :=
        mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (by positivity) _)
      linarith
    exact mul_le_mul_of_nonneg_right hAA' this

theorem psii_conormal {ρ : Torus d → ℝ} (hρ : Torus.IsSmooth ρ) (m : ℕ) (hm : 1 ≤ m) (τ : ℝ)
    (b : ℕ) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (Ψ : Torus d → Torus d → ℝ), 0 ≤ B →
      ConormalL τ (fun _ => b) m B Ψ →
      ConormalL (τ + 1) (fun _ => b) (m - 1) (C * B) (Psii ρ Ψ i) := by
  obtain ⟨Cm, hCm0, hCm⟩ := conormal_mul_smooth_aux (d := d) (m - 1) (τ + 1) (fun _ => b)
  set a : Torus d → Torus d → ℝ := fun x _ => ρ x with ha
  have haC : PDE.IsCk2 (m - 1) a := by
    unfold PDE.IsCk2
    have : PDE.lift2 a = fun p : Euc d × Euc d => Torus.lift ρ p.1 := rfl
    rw [this]
    have hρ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ) := hρ
    exact (hρ'.comp contDiff_fst).of_le (natCast_le_infty (m - 1))
  have hcb0 : 0 ≤ PDE.cbNorm2 (m - 1) a := PDE.MFPair.cbNorm2_nonneg (m - 1) a
  refine ⟨Cm * PDE.cbNorm2 (m - 1) a * 2, by positivity, fun B Ψ hB hΨ => ?_⟩
  have h1 := conormal_partial_fst_aux hΨ hm i
  have h1' : ConormalL (τ + 1) (fun _ => b) (m - 1) (2 * B)
      (fun x y => Torus.partialDeriv i (fun z => Ψ z y) x) :=
    conormalL_mono_b (by positivity) (fun c => by simp) h1
  have h2 := hCm (2 * B) _ a h1' haC
  have h3 : ConormalL (τ + 1) (fun _ => b) (m - 1) (Cm * PDE.cbNorm2 (m - 1) a * (2 * B))
      (fun x y => a x y * Torus.partialDeriv i (fun z => Ψ z y) x) :=
    conormalL_mono_b (by positivity) (fun c => by simp) h2
  have e : Cm * PDE.cbNorm2 (m - 1) a * (2 * B) = Cm * PDE.cbNorm2 (m - 1) a * 2 * B := by ring
  rw [e] at h3
  exact h3

theorem gsrc_srcCls (m : ℕ) (σ : ℝ) (b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      SrcCls d σ b m (K * B) (Gsrc F) ∧
      (∀ X w : Euc d, 1 / 32 < ‖w‖ → Gsrc F (X, w) = 0) ∧
      (∀ X w n : Euc d, IsLat n → Gsrc F (X + n, w) = Gsrc F (X, w)) := by
  obtain ⟨K0, hK0, hK⟩ := srcCls_chart' (d := d) σ b m
  refine ⟨(1 + |(1 / 2 : ℝ)|) ^ m * K0, by positivity, fun B F hB hF => ?_⟩
  have h := hK B F hB hF
  have hsh := SrcCls.shear h (mul_nonneg hK0 hB)
    (fun X w hw => srcCls_chart'_zero F X w hw) (1 / 2 : ℝ)
  refine ⟨?_, ?_, fun X w n hn => Gsrc_periodic F X w n hn⟩
  · have e : (1 + |(1 / 2 : ℝ)|) ^ m * (K0 * B) = (1 + |(1 / 2 : ℝ)|) ^ m * K0 * B := by ring
    rw [e] at hsh
    rw [Gsrc_eq_shear]
    exact hsh
  · intro X w hw
    simp only [Gsrc]
    rw [px3a_zeta_eq_zero (by norm_num : (0 : ℝ) < 1 / 32) hw.le, zero_mul]

/-- The direction `e_i`. -/
def eVec (d : ℕ) (i : Fin d) : Euc d := EuclideanSpace.single i (1 : ℝ)

lemma norm_eVec (i : Fin d) : ‖eVec d i‖ = 1 := by simp [eVec]

/-- The derivative sources `∂_{w_i} G_i`. -/
def Ssrc (F : Euc d × Euc d → ℝ) (i : Fin d) : Euc d × Euc d → ℝ :=
  dirD ((0 : Euc d), eVec d i) F

/-- The divergence source `∑_i ∂_{w_i} G_i`. -/
def SNsrc (ρ : Torus d → ℝ) (Ψ : Torus d → Torus d → ℝ) : Euc d × Euc d → ℝ :=
  fun p => ∑ i, Ssrc (Gsrc (Psii ρ Ψ i)) i p

/-- The divergence source of the far part. -/
def SFsrc (ρ : Torus d → ℝ) (Ψ : Torus d → Torus d → ℝ) : Euc d × Euc d → ℝ :=
  fun p => ∑ i, Ssrc (Fsrc (Psii ρ Ψ i)) i p

/-- Chart-source properties of `SNsrc`. -/
theorem snsrc_srcCls {ρ : Torus d → ℝ} (hρ : Torus.IsSmooth ρ) (m' : ℕ) (τ : ℝ) (b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (B : ℝ) (Ψ : Torus d → Torus d → ℝ), 0 ≤ B →
      ConormalL τ (fun _ => b) (m' + 2) B Ψ →
      SrcCls d (τ + 2) b m' (K * B) (SNsrc ρ Ψ) ∧
      (∀ X w : Euc d, 1 / 32 < ‖w‖ → SNsrc ρ Ψ (X, w) = 0) ∧
      (∀ X w n : Euc d, IsLat n → SNsrc ρ Ψ (X + n, w) = SNsrc ρ Ψ (X, w)) ∧
      (∀ i : Fin d, SrcCls d (τ + 1) b (m' + 1) (K * B) (Gsrc (Psii ρ Ψ i)) ∧
        (∀ X w : Euc d, 1 / 32 < ‖w‖ → Gsrc (Psii ρ Ψ i) (X, w) = 0) ∧
        (∀ X w n : Euc d, IsLat n → Gsrc (Psii ρ Ψ i) (X + n, w) = Gsrc (Psii ρ Ψ i) (X, w))) := by
  classical
  have hm : 1 ≤ m' + 2 := by omega
  choose C hC0 hC using fun i : Fin d => psii_conormal hρ (m' + 2) hm τ b i
  obtain ⟨K1, hK10, hK1⟩ := gsrc_srcCls (d := d) (m' + 1) (τ + 1) b
  set Cs : ℝ := ∑ i, C i with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun i _ => hC0 i
  have hCle : ∀ i, C i ≤ Cs := fun i =>
    Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ i)
  refine ⟨(d : ℝ) * (K1 * (Cs + 1)), by positivity, fun B Ψ hB hΨ => ?_⟩
  have hPsi : ∀ i : Fin d, Conormal (τ + 1) b (m' + 1) ((Cs + 1) * B) (Psii ρ Ψ i) := by
    intro i
    have h1 := hC i B Ψ hB hΨ
    have e : m' + 2 - 1 = m' + 1 := by omega
    rw [e] at h1
    refine conormalL_mono_B h1 (mul_nonneg (hC0 i) hB) ?_
    nlinarith [hCle i, mul_nonneg hCs0 hB]
  have hG : ∀ i : Fin d, SrcCls d (τ + 1) b (m' + 1) (K1 * ((Cs + 1) * B)) (Gsrc (Psii ρ Ψ i)) ∧
      (∀ X w : Euc d, 1 / 32 < ‖w‖ → Gsrc (Psii ρ Ψ i) (X, w) = 0) ∧
      (∀ X w n : Euc d, IsLat n → Gsrc (Psii ρ Ψ i) (X + n, w) = Gsrc (Psii ρ Ψ i) (X, w)) :=
    fun i => hK1 ((Cs + 1) * B) (Psii ρ Ψ i) (by positivity) (hPsi i)
  have hAeq : K1 * ((Cs + 1) * B) = K1 * (Cs + 1) * B := by ring
  have hS : ∀ i : Fin d, SrcCls d (τ + 2) b m' (K1 * ((Cs + 1) * B) * ‖eVec d i‖) (Ssrc (Gsrc (Psii ρ Ψ i)) i) := by
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

end HRS.Parx

end
