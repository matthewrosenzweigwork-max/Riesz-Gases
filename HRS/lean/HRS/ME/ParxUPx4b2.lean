import HRS.ME.ParxUPx4b1
import HRS.ME.ParxUKernel2

/-!
# Packet P3a (part 2): uniform `px4b_Y1_class`, `px4b_T1_class`, `px4b_J_class`

Uniform versions (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of the
`HRS.Parx.px4b_Y1_class`, `px4b_T1_class`, `px4b_J_class` lemmas of `Packets.lean`.

* `β⁻¹` is bounded uniformly: `0 < νm ≤ β⁻¹ ≤ νp` (`ParxU.beta_bounds`), so `|β⁻¹|` is replaced by `|νp|`.
* The only ρ-dependent constant in `px4b_T1_class` is `M = ∑ⱼ (cbNorm2 (m-1) (∂ⱼρ/ρ) + …)`; it is
  bounded by `ParxU.partial_div_cbNorm_bound` (and the `cbNorm2` extractors of `ParxUPx4b1`).
* `px4b_J_class` uses `jop_engine_unif` in place of `jop_general`; the identity `s = d/2` (`ParxHyp.crit`)
  is used inside the proof, after the constant has been chosen.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- Uniform bounds on `β⁻¹` from the bundle: `0 < β⁻¹ ≤ νp`, hence `|β⁻¹| ≤ |νp|`. -/
theorem abs_beta_inv_le_of {β : ℝ} {V ρ : Torus d → ℝ} (U : ParxU d s N νm νp c₀ Λ₀ β V ρ) :
    |β⁻¹| ≤ |νp| := by
  have hνm : 0 < νm := U.F.hνm
  have hpos : 0 < β⁻¹ := lt_of_lt_of_le hνm U.beta_bounds.1
  rw [abs_of_pos hpos]
  exact U.beta_bounds.2.1.trans (le_abs_self νp)

/-- **Uniform version of `px4b_Y1_class`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`
and `(σ, b, m)`; it is chosen before `β, V, ρ`. -/
theorem px4b_Y1_class_unif (hd : 2 ≤ d) (hsd : s < d) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m)
    (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C * B)
        (fun x y => (β⁻¹ / 2) * ∑ i : Fin d, px4b_dX i (px4b_dX i (newtonOp d β ρ F)) x y) := by
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b m hN
  refine ⟨|νp| / 2 * ((d : ℝ) * C1), by positivity, fun β V ρ U B F hB hF => ?_⟩
  have hbinv : |β⁻¹| ≤ |νp| := abs_beta_inv_le_of U
  have hb2 : |β⁻¹ / 2| ≤ |νp| / 2 := by
    rw [abs_div, abs_two]
    gcongr
  have hN1 := hC1 β V ρ U B F hB hF
  have h2 : ∀ i : Fin d, ConormalL (σ - 2) (fun _ => b + 1) (m - 1 - 1) (C1 * B)
      (px4b_dX i (px4b_dX i (newtonOp d β ρ F))) := fun i =>
    px4b_dX_conormal (by omega) (px4b_dX_conormal (by omega) hN1 i) i
  have h3 := conormal_finset_sum px4bU_hAdd (σ - 2) (fun _ => b + 1) (m - 1 - 1) Finset.univ
    (fun i => px4b_dX i (px4b_dX i (newtonOp d β ρ F))) (fun _ => C1 * B) (fun i _ => h2 i)
  have h4 := conormalL_smul h3 (β⁻¹ / 2)
  refine px4bU_mono h4 (by positivity) (by linarith) (fun c => by omega) (by omega) ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hX : 0 ≤ (d : ℝ) * C1 * B := by positivity
  calc _ = |β⁻¹ / 2| * ((d : ℝ) * C1 * B) := by ring
    _ ≤ |νp| / 2 * ((d : ℝ) * C1 * B) := mul_le_mul_of_nonneg_right hb2 hX
    _ = _ := by ring

/-- **Uniform version of `px4b_T1_class`.** The drift piece; the constant `M` of the packet proof is
replaced by the uniform bound `Mc` on `∑ⱼ (‖∂ⱼρ/ρ‖ + ‖∂ⱼρ/ρ‖)` (`ParxU.partial_div_cbNorm_bound`). -/
theorem px4b_T1_class_unif (hd : 2 ≤ d) (hsd : s < d) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m)
    (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C * B)
        (fun x y => β⁻¹ * ∑ j : Fin d, ((Torus.partialDeriv j ρ x / ρ x) *
          px4b_K1 j (newtonOp d β ρ F) x y +
          (Torus.partialDeriv j ρ y / ρ y) * px4b_dy j (newtonOp d β ρ F) x y)) := by
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b m hN
  obtain ⟨Cm, hCm0, hCm⟩ := conormal_mul_smooth_aux (d := d) (m - 1) (σ - 2 + 1) (fun _ => b + 1)
  choose Aj hAj0 hAj using fun j : Fin d => ParxU.partial_div_cbNorm_bound (d := d) (s := s)
    (N := N) (νm := νm) (νp := νp) (c₀ := c₀) (Λ₀ := Λ₀) j (m - 1) (by omega)
  obtain ⟨Mc, hMc0, hMcj⟩ : ∃ Mc : ℝ, 0 ≤ Mc ∧ ∀ j : Fin d, Aj j + Aj j ≤ Mc :=
    ⟨∑ j, (Aj j + Aj j), Finset.sum_nonneg fun j _ => by linarith [hAj0 j],
      fun j => Finset.single_le_sum (f := fun j => Aj j + Aj j)
        (fun j _ => by linarith [hAj0 j]) (Finset.mem_univ j)⟩
  refine ⟨|νp| * ((d : ℝ) * (Cm * Mc * (2 * C1))), by positivity,
    fun β V ρ U B F hB hF => ?_⟩
  have hbinv : |β⁻¹| ≤ |νp| := abs_beta_inv_le_of U
  have hq : ∀ j : Fin d, Torus.IsCk ((m - 1 : ℕ) : WithTop ℕ∞)
      (fun u => Torus.partialDeriv j ρ u / ρ u) :=
    fun j => PDE.MFPair.isCk_of_smooth_ps (px4bU_q_smooth U.H.rho_smooth j) _
  have hM : ∀ j : Fin d, PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) +
      PDE.cbNorm2 (m - 1) (fun _ y => Torus.partialDeriv j ρ y / ρ y) ≤ Mc := by
    intro j
    have h1 : PDE.cbNorm2 (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x) ≤
        Torus.cbNorm (m - 1) (fun x => Torus.partialDeriv j ρ x / ρ x) :=
      px4bU_cbNorm2_fst_le (hq j)
    have h2 : PDE.cbNorm2 (m - 1) (fun _ y => Torus.partialDeriv j ρ y / ρ y) ≤
        Torus.cbNorm (m - 1) (fun y => Torus.partialDeriv j ρ y / ρ y) :=
      px4bU_cbNorm2_snd_le (hq j)
    have h3 := hAj j β V ρ U
    linarith [hMcj j]
  have hN1 := hC1 β V ρ U B F hB hF
  have hB1 : 0 ≤ C1 * B := mul_nonneg hC10 hB
  have hK1 : ∀ j : Fin d, ConormalL (σ - 2 + 1) (fun _ => b + 1) (m - 1) (2 * (C1 * B))
      (px4b_K1 j (newtonOp d β ρ F)) := fun j =>
    conormalL_mono_b (by positivity) (fun c => by simp) (px4b_K1_conormal (by omega) hN1 j)
  have hKy : ∀ j : Fin d, ConormalL (σ - 2 + 1) (fun _ => b + 1) (m - 1) (2 * (C1 * B))
      (px4b_dy j (newtonOp d β ρ F)) := fun j =>
    conormalL_mono_b (by positivity) (fun c => by simp) (px4b_dy_conormal (by omega) hN1 j)
  have hterm : ∀ j : Fin d, ConormalL (σ - 2 + 1) (fun _ => b + 1) (m - 1)
      (Cm * Mc * (2 * (C1 * B)))
      (fun x y => (Torus.partialDeriv j ρ x / ρ x) * px4b_K1 j (newtonOp d β ρ F) x y +
        (Torus.partialDeriv j ρ y / ρ y) * px4b_dy j (newtonOp d β ρ F) x y) := by
    intro j
    have a1 := hCm (2 * (C1 * B)) _ (fun x _ => Torus.partialDeriv j ρ x / ρ x) (hK1 j)
      (px4b_isCk2_fst (hq j))
    have a2 := hCm (2 * (C1 * B)) _ (fun _ y => Torus.partialDeriv j ρ y / ρ y) (hKy j)
      (px4b_isCk2_snd (hq j))
    have hsup : (fun c : ℕ => (Finset.range (c + 1)).sup (fun _ : ℕ => b + 1)) =
        fun _ => b + 1 :=
      funext fun c => Finset.sup_const (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero c)) _
    rw [hsup] at a1 a2
    have a3 := conormalL_add a1 a2
    have c1 := PDE.MFPair.cbNorm2_nonneg (m - 1) (fun x _ => Torus.partialDeriv j ρ x / ρ x)
    have c2 := PDE.MFPair.cbNorm2_nonneg (m - 1) (fun _ y => Torus.partialDeriv j ρ y / ρ y)
    have h2C : 0 ≤ 2 * (C1 * B) := by positivity
    refine conormalL_mono_B a3 (add_nonneg (mul_nonneg (mul_nonneg hCm0 c1) h2C)
      (mul_nonneg (mul_nonneg hCm0 c2) h2C)) ?_
    have hcm := mul_le_mul_of_nonneg_left (hM j) hCm0
    nlinarith [mul_le_mul_of_nonneg_right hcm h2C]
  have hsum := conormal_finset_sum px4bU_hAdd (σ - 2 + 1) (fun _ => b + 1) (m - 1) Finset.univ
    (fun j x y => (Torus.partialDeriv j ρ x / ρ x) * px4b_K1 j (newtonOp d β ρ F) x y +
        (Torus.partialDeriv j ρ y / ρ y) * px4b_dy j (newtonOp d β ρ F) x y)
    (fun _ => Cm * Mc * (2 * (C1 * B))) (fun j _ => hterm j)
  have hs2 := conormalL_smul hsum β⁻¹
  refine px4bU_mono hs2 (by positivity) (by linarith) (fun c => by omega) (by omega) ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hX : 0 ≤ (d : ℝ) * (Cm * Mc * (2 * C1)) * B := by positivity
  calc _ = |β⁻¹| * ((d : ℝ) * (Cm * Mc * (2 * C1)) * B) := by ring
    _ ≤ |νp| * ((d : ℝ) * (Cm * Mc * (2 * C1)) * B) := mul_le_mul_of_nonneg_right hbinv hX
    _ = _ := by ring

/-- **Uniform version of `px4b_J_class`.** The nonlocal pieces; the constant depends only on
`(d, s, N, νm, νp, c₀, Λ₀)` and `(σ, b, m)`. -/
theorem px4b_J_class_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ)
    (hm : 2 ≤ m) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C * B)
        (fun x y => offZero (fun x y => Jop d s ρ (fun z => newtonOp d β ρ F z y) x) x y +
          swapK (offZero (fun x y => Jop d s ρ (fun z => swapK (newtonOp d β ρ F) z y) x)) x y) := by
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b m hN
  have hσd : σ - 2 + 2 < d := by linarith
  obtain ⟨C2, hC20, hC2⟩ := jop_engine_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hs0 hsd (τ := σ - 2) hσd (b + 1) (m - 2) (by omega)
  refine ⟨C2 * C1 + C2 * C1, by positivity, fun β V ρ U B F hB hF => ?_⟩
  have hcr : s = (d : ℝ) / 2 := U.H.crit
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hN1 := hC1 β V ρ U B F hB hF
  have hN2 : ConormalL (σ - 2) (fun _ => b + 1) (m - 2 + 2) (C1 * B) (newtonOp d β ρ F) := by
    rw [show m - 2 + 2 = m by omega]
    exact hN1
  have hB1 : 0 ≤ C1 * B := mul_nonneg hC10 hB
  have h1 := hC2 β V ρ U (C1 * B) _ hB1 hN2
  have h2 := conormalL_swap (hC2 β V ρ U (C1 * B) _ hB1 (conormalL_swap hN2))
  have h1' : ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C2 * (C1 * B))
      (offZero fun x y => Jop d s ρ (fun z => newtonOp d β ρ F z y) x) :=
    px4bU_mono h1 (by positivity) (by linarith) (fun c => by omega) le_rfl le_rfl
  have h2' : ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C2 * (C1 * B))
      (swapK (offZero fun x y => Jop d s ρ (fun z => swapK (newtonOp d β ρ F) z y) x)) :=
    px4bU_mono h2 (by positivity) (by linarith) (fun c => by omega) le_rfl le_rfl
  have h3 := conormalL_add h1' h2'
  exact conormalL_mono_B h3 (by positivity) (le_of_eq (by ring))

end HRS.ME.ParxU

end
