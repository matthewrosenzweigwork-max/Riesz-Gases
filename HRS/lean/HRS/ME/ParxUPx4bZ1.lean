import HRS.ME.ParxUPx4b2
import HRS.Equilibrium.Parametrix.Packets

/-!
# Packet P3c (part 1): uniform `px4b_Z0_class`, `px4b_Zv_class`

Uniform versions (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.px4b_Z0_class` and `HRS.Parx.px4b_Zv_class` (Packets:863, :920).

* `Z0` uses only `px4b_N_class_unif`; the factor `|β⁻¹|` of `px4b_Z0` is bounded by `|νp|`
  (`abs_beta_inv_le_of`, ParxUPx4b1).
* `Zv` uses `px4b_G_class_unif`, `px4b_N_class_unif`, `px4b_aa_class_unif` and `px4b_Z0_class_unif`.
  The smooth kernel `px4b_Sm` has the explicit constant `|β⁻¹/2| · d · cbNorm a`, bounded by `|νp|/2`.
  The ρ-free leaves (`px4b_Sm_class`, `px4b_hNeq`, `px4b_Z0_poisson`, `px4b_conormal_vanish`, ...)
  and the ParxHyp-level `px4b_hP` are reused from `Packets.lean` (with `U.H`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `px4b_Z0_class`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`
and `(σ, b, m)`; it is chosen before `β, V, ρ`. -/
theorem px4b_Z0_class_unif (hd : 2 ≤ d) (hsd : s < d) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m)
    (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL σ (fun _ => b + 1) (m - 2) (C * B) (px4b_Z0 β⁻¹ F (newtonOp d β ρ F)) := by
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b m hN
  refine ⟨1 + |νp| * ((d : ℝ) * (4 * C1 + 4 * C1 + C1 / 2)), by positivity,
    fun β V ρ U B F hB hF => ?_⟩
  have hbinv : |β⁻¹| ≤ |νp| := abs_beta_inv_le_of U
  have hN1 := hC1 β V ρ U B F hB hF
  have hB1 : 0 ≤ C1 * B := mul_nonneg hC10 hB
  have hF' : ConormalL σ (fun _ => b + 1) (m - 2) B F :=
    ConormalL.mono hF hB le_rfl (fun c => by omega) (by omega) le_rfl
  have hA : ∀ i : Fin d, ConormalL σ (fun _ => b + 1) (m - 2) (4 * (C1 * B))
      (px4b_K1 i (px4b_K1 i (newtonOp d β ρ F))) := fun i =>
    ConormalL.mono (px4b_K1_conormal (by omega) (px4b_K1_conormal (by omega) hN1 i) i)
      (by positivity) (by linarith) (fun c => by simp) (by omega) (by linarith)
  have hBy : ∀ i : Fin d, ConormalL σ (fun _ => b + 1) (m - 2) (4 * (C1 * B))
      (px4b_dy i (px4b_dy i (newtonOp d β ρ F))) := fun i =>
    ConormalL.mono (px4b_dy_conormal (by omega) (px4b_dy_conormal (by omega) hN1 i) i)
      (by positivity) (by linarith) (fun c => by simp) (by omega) (by linarith)
  have hX : ∀ i : Fin d, ConormalL σ (fun _ => b + 1) (m - 2) (C1 * B)
      (px4b_dX i (px4b_dX i (newtonOp d β ρ F))) := fun i =>
    ConormalL.mono (px4b_dX_conormal (by omega) (px4b_dX_conormal (by omega) hN1 i) i)
      hB1 (by linarith) (fun c => le_rfl) (by omega) le_rfl
  have hterm : ∀ i : Fin d, ConormalL σ (fun _ => b + 1) (m - 2)
      (4 * (C1 * B) + 4 * (C1 * B) + |(-(1 / 2 : ℝ))| * (C1 * B))
      (fun x y => px4b_K1 i (px4b_K1 i (newtonOp d β ρ F)) x y +
        px4b_dy i (px4b_dy i (newtonOp d β ρ F)) x y -
        (1 / 2 : ℝ) * px4b_dX i (px4b_dX i (newtonOp d β ρ F)) x y) := by
    intro i
    have e : (fun x y => px4b_K1 i (px4b_K1 i (newtonOp d β ρ F)) x y +
        px4b_dy i (px4b_dy i (newtonOp d β ρ F)) x y -
        (1 / 2 : ℝ) * px4b_dX i (px4b_dX i (newtonOp d β ρ F)) x y) =
        fun x y => (px4b_K1 i (px4b_K1 i (newtonOp d β ρ F)) x y +
          px4b_dy i (px4b_dy i (newtonOp d β ρ F)) x y) +
          (-(1 / 2 : ℝ)) * px4b_dX i (px4b_dX i (newtonOp d β ρ F)) x y := by
      funext x y; ring
    rw [e]
    exact conormalL_add (conormalL_add (hA i) (hBy i)) (ConormalL.smul (hX i) (-(1 / 2 : ℝ)))
  have hsum := conormal_finset_sum px4b_hAdd σ (fun _ => b + 1) (m - 2) Finset.univ
    (fun i x y => px4b_K1 i (px4b_K1 i (newtonOp d β ρ F)) x y +
        px4b_dy i (px4b_dy i (newtonOp d β ρ F)) x y -
        (1 / 2 : ℝ) * px4b_dX i (px4b_dX i (newtonOp d β ρ F)) x y)
    (fun _ => 4 * (C1 * B) + 4 * (C1 * B) + |(-(1 / 2 : ℝ))| * (C1 * B)) (fun i _ => hterm i)
  have hs2 := ConormalL.smul hsum β⁻¹
  have hall := conormalL_add hF' hs2
  refine conormalL_mono_B hall (by positivity) ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h12 : |(-(1 / 2 : ℝ))| = 1 / 2 := by norm_num
  rw [h12]
  have hY : 0 ≤ (d : ℝ) * (4 * (C1 * B) + 4 * (C1 * B) + 1 / 2 * (C1 * B)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hbinv hY]

/-- **Uniform version of `px4b_Zv_class`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`
and `(σ, b, m)`; it is chosen before `β, V, ρ`. -/
theorem px4b_Zv_class_unif (hd : 2 ≤ d) (hsd : s < d) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hm : 2 ≤ m)
    (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C * B)
        (fun x y => px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y -
          px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  obtain ⟨CZ, hCZ0, hCZ⟩ := px4b_Z0_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b (n + 2) hm hN
  obtain ⟨CA, hCA0, hCA⟩ := px4b_aa_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b (n + 2) hN
  obtain ⟨CG, hCG0, hCG⟩ := px4b_G_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b (n + 2)
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b (n + 2) hN
  refine ⟨px4b_Cvan σ (fun _ => b + 1) n (1 / 32) *
    (CZ + |νp| / 2 * ((d : ℝ) * CA + (d : ℝ) * CA)), ?_, fun β V ρ U B F hB hF => ?_⟩
  · have := px4b_Cvan_ge_one σ (fun _ => b + 1) n (by norm_num : (0 : ℝ) < 1 / 32)
    positivity
  have hZ := hCZ β V ρ U B F hB hF
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hCA β V ρ U B F hB hF
  have hAn : Torus.IsCk (((n + 2 : ℕ)) : WithTop ℕ∞) (px4b_aF d β ρ F) := hA1
  have hA'n : Torus.IsCk (((n + 2 : ℕ)) : WithTop ℕ∞) (px4b_a'F d β ρ F) := hA3
  have hSm := px4b_Sm_class β⁻¹ σ (fun _ => b + 1) hAn hA'n
  have c1 := PDE.cbNorm_nonneg'C (n + 2) (px4b_aF d β ρ F)
  have c2 := PDE.cbNorm_nonneg'C (n + 2) (px4b_a'F d β ρ F)
  have hν : 0 ≤ |β⁻¹ / 2| := abs_nonneg _
  have hSm' : ConormalL σ (fun _ => b + 1) n (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B)))
      (px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F)) :=
    conormalL_mono_B hSm (mul_nonneg hν (add_nonneg (mul_nonneg (Nat.cast_nonneg _) c1)
      (mul_nonneg (Nat.cast_nonneg _) c2)))
      (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hA2 (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hA4 (Nat.cast_nonneg _))) hν)
  have hdiff : ConormalL σ (fun _ => b + 1) n
      (CZ * B + |(-1 : ℝ)| * (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B))))
      (fun x y => px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y -
        px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y) := by
    have e : (fun x y => px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y -
        px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y) =
        fun x y => px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y +
          (-1 : ℝ) * px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y := by
      funext x y; ring
    rw [e]
    exact conormalL_add hZ (ConormalL.smul hSm' (-1))
  have hBnn : 0 ≤ CZ * B + |(-1 : ℝ)| * (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B))) := by
    positivity
  have hvan : ∀ X z : Euc d, z ≠ 0 → ‖z‖ < 1 / 32 →
      toChart (fun x y => px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y -
        px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y) (X, z) = 0 := by
    intro X z hz hzr
    have hN' := (hC1 β V ρ U B F hB hF).smooth
    have hG : ContDiffOn ℝ (2 : ℕ) (lift2 (px4b_G d β F)) (offDiag d) :=
      ((hCG β V ρ U B F hB hF).smooth).of_le (by exact_mod_cast Nat.le_add_left 2 n)
    have ha : ContDiff ℝ 2 (Torus.lift (px4b_aF d β ρ F)) :=
      (show ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (Torus.lift (px4b_aF d β ρ F)) from hAn).of_le
        (by exact_mod_cast Nat.le_add_left 2 n)
    have ha' : ContDiff ℝ 2 (Torus.lift (px4b_a'F d β ρ F)) :=
      (show ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (Torus.lift (px4b_a'F d β ρ F)) from hA'n).of_le
        (by exact_mod_cast Nat.le_add_left 2 n)
    have hpo := px4b_Z0_poisson (ν := β⁻¹) (F := F) (N := newtonOp d β ρ F) (G := px4b_G d β F)
      (a := px4b_aF d β ρ F) (a' := px4b_a'F d β ρ F) (c0 := px4b_c0F d β ρ F) (m := n + 2)
      (X := X) (z := z) hN' hm
      (fun x y hxy => px4b_hNeq F hxy) hG ha ha' (fun X z hz hzr => px4b_hP U.H hσ hm hF X z hz hzr)
      hz hzr
    show px4b_Z0 β⁻¹ F (newtonOp d β ρ F) (Torus.mk (X + (1 / 2 : ℝ) • z)) (Torus.mk (X - (1 / 2 : ℝ) • z)) -
      px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) (Torus.mk (X + (1 / 2 : ℝ) • z))
        (Torus.mk (X - (1 / 2 : ℝ) • z)) = 0
    have hz0 : px4b_Z0 β⁻¹ F (newtonOp d β ρ F) (Torus.mk (X + (1 / 2 : ℝ) • z)) (Torus.mk (X - (1 / 2 : ℝ) • z)) =
        toChart (px4b_Z0 β⁻¹ F (newtonOp d β ρ F)) (X, z) := rfl
    rw [hz0, hpo]
    simp only [px4b_Sm]
    rw [← px4b_laplacian_sum hAn, ← px4b_laplacian_sum hA'n]
    ring
  have hv := px4b_conormal_vanish (σ' := σ - 1) (by norm_num : (0 : ℝ) < 1 / 32) hBnn hdiff hvan
  have hC1' := px4b_Cvan_ge_one σ (fun _ => b + 1) n (by norm_num : (0 : ℝ) < 1 / 32)
  have hvn : 0 ≤ px4b_Cvan σ (fun _ => b + 1) n (1 / 32) *
      (CZ * B + |(-1 : ℝ)| * (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B)))) :=
    mul_nonneg (by linarith) hBnn
  refine conormalL_mono_B (ConormalL.mono hv hvn le_rfl (fun c => by omega) le_rfl le_rfl)
    hvn ?_
  -- the `β`-dependent factor `|β⁻¹ / 2|` is bounded by `|νp| / 2`
  have hb2 : |β⁻¹ / 2| ≤ |νp| / 2 := by
    have hβi : |β⁻¹| ≤ |νp| := abs_beta_inv_le_of U
    rw [abs_div, abs_two]
    linarith
  have hY : 0 ≤ (d : ℝ) * (CA * B) + (d : ℝ) * (CA * B) := by positivity
  have hbz := mul_le_mul_of_nonneg_right hb2 hY
  have hCv : 0 ≤ px4b_Cvan σ (fun _ => b + 1) n (1 / 32) := by linarith
  rw [abs_neg, abs_one]
  calc px4b_Cvan σ (fun _ => b + 1) n (1 / 32) *
        (CZ * B + 1 * (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B))))
      ≤ px4b_Cvan σ (fun _ => b + 1) n (1 / 32) *
        (CZ * B + 1 * (|νp| / 2 * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B)))) := by
        apply mul_le_mul_of_nonneg_left _ hCv
        linarith
    _ = px4b_Cvan σ (fun _ => b + 1) n (1 / 32) *
        (CZ + |νp| / 2 * ((d : ℝ) * CA + (d : ℝ) * CA)) * B := by ring

end HRS.ME.ParxU

end
