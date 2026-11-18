import HRS.ME.ParxUDefect3
import HRS.ME.ParxUKernel2
import HRS.Equilibrium.Parametrix.PX5AuxE

/-!
# Packet P4a (part 1): uniform `px5_psi_bnds`, `jop_general`, `px5_psi_class`

Uniform versions (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of

* `HRS.Parx.px5_psi_bnds` (PX5AuxB:119), by induction on `n` with `parxN_conormal_unif`;
* `HRS.Parx.jop_general` (Packets:270), from `jop_engine_unif`; the exponent identity
  `σ + 2 + s - d = σ + 2 - s` uses `U.H.crit` inside the `∀ β V ρ U` block only;
* `HRS.Parx.px5_N_class` (PX5AuxC:61) and `HRS.Parx.px5_psi_class` (PX5AuxC:88).

The constants depend only on `(d, s, N, νm, νp, c₀, Λ₀)`, on `J` or `m, n, b, σ` and on the parameter
facts `2 ≤ d`, `0 < s`, `s < d`, and on the level bounds `m ≤ N`, `px5m d J ≤ N`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `jop_general`.** The constant depends only on `(d, s, N, Λ₀, σ, b, m)`,
and on `2 ≤ d`, `0 < s < d`, `σ + 2 < d`, `2 ≤ m ≤ N`; it is chosen before `β, V, ρ`. -/
theorem jop_general_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (σ : ℝ) (hσ : σ + 2 < d)
    (b m : ℕ) (hm : 2 ≤ m) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      Conormal (σ + 2 - s) (b + 2) (m - 2) (C * B)
        (offZero fun x y => Jop d s ρ (fun z => F z y) x) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨C2, hC20, hC2⟩ := jop_engine_unif (d := d) (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hs0 hsd hσ b m' (by omega)
  refine ⟨C2, hC20, fun β V ρ U B F hB hF => ?_⟩
  have h2 := hC2 β V ρ U B F hB hF
  have e1 : σ + 2 + s - d = σ + 2 - s := by rw [U.H.crit]; ring
  have e2 : m' + 2 - 2 = m' := by omega
  rw [e1] at h2
  rw [e2]
  exact ConormalL.mono h2 (mul_nonneg hC20 hB) le_rfl (fun c => by omega) le_rfl le_rfl

/-- **Uniform version of `px5_N_class`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`,
on `J` and on `2 ≤ d`, `0 < s < d`, `px5m d J ≤ N`; it is chosen before `β, V, ρ`. -/
theorem px5_N_class_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (J : ℕ) (hN : px5m d J ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ j < parxL d J,
      Conormal (s - 2) 1 (J + 3) (C * posSeminorm (px5m d J + 2) f)
        (newtonOp d β ρ (parxR d s V β ρ f j)) := by
  have h : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (j < parxL d J → ∀ (β : ℝ) (V ρ : Torus d → ℝ),
      ParxU d s N νm νp c₀ Λ₀ β V ρ → ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal (s - 2) 1 (J + 3) (C * posSeminorm (px5m d J + 2) f)
        (newtonOp d β ρ (parxR d s V β ρ f j))) := by
    intro j
    by_cases hj : j < parxL d J
    · obtain ⟨C, hC0, hC⟩ := parxN_conormal_unif hd hs0 hsd (px5m d J) hN j
        (by unfold px5m; omega)
      refine ⟨C, hC0, fun _ β V ρ U f hf => ?_⟩
      have hB0 : 0 ≤ C * posSeminorm (px5m d J + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
      refine ConormalL.mono (hC β V ρ U f hf) hB0 ?_ (fun c => ?_) ?_ le_rfl
      · have : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
        linarith
      · split_ifs <;> simp
      · unfold px5m; omega
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose C hC0 hC using h
  refine ⟨∑ j ∈ Finset.range (parxL d J), C j, Finset.sum_nonneg fun j _ => hC0 j, ?_⟩
  intro β V ρ U f hf j hj
  have hB0 : 0 ≤ C j * posSeminorm (px5m d J + 2) f := mul_nonneg (hC0 j) (posSeminorm_nonneg' _ _)
  refine ConormalL.mono (hC j hj β V ρ U f hf) hB0 le_rfl (fun c => le_rfl) le_rfl ?_
  refine mul_le_mul_of_nonneg_right ?_ (posSeminorm_nonneg' _ _)
  exact Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.mpr hj)

/-- **Uniform version of `px5_psi_class`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`,
on `J` and on the parameter facts; it is chosen before `β, V, ρ`. -/
theorem px5_psi_class_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (J : ℕ) (hN : px5m d J ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal (s - 2) 1 (J + 3) (C * posSeminorm (px5m d J + 2) f)
        (parxPsi d s V β ρ f (parxL d J)) := by
  obtain ⟨C, hC0, hC⟩ := px5_N_class_unif hd hs0 hsd J hN
  refine ⟨(parxL d J : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC0, fun β V ρ U f hf => ?_⟩
  have h := conormal_finset_sum (d := d) px5_conormalAdd (s - 2) (fun _ => 1) (J + 3)
    (Finset.range (parxL d J)) (fun j => newtonOp d β ρ (parxR d s V β ρ f j))
    (fun _ => C * posSeminorm (px5m d J + 2) f)
    (fun j hj => hC β V ρ U f hf j (Finset.mem_range.mp hj))
  have e : (∑ _j ∈ Finset.range (parxL d J), C * posSeminorm (px5m d J + 2) f) =
      (parxL d J : ℝ) * C * posSeminorm (px5m d J + 2) f := by
    simp; ring
  rw [e] at h
  exact h

/-- **Uniform version of `px5_psi_bnds`.** For each `n` with `2 n ≤ m` the constant depends only on
`(d, s, N, νm, νp, c₀, Λ₀)`, on `m, n` and on `2 ≤ d`, `0 < s < d`, `m ≤ N`; it is chosen before
`β, V, ρ`. -/
theorem px5_psi_bnds_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (m : ℕ) (hN : m ≤ N) :
    ∀ n : ℕ, 2 * n ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ),
      ParxU d s N νm νp c₀ Λ₀ β V ρ → ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Px5Bnds s (C * posSeminorm (m + 2) f) (parxPsi d s V β ρ f n) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, le_rfl, fun β V ρ U f hf => ?_⟩
    have e : parxPsi d s V β ρ f 0 = fun _ _ => 0 := by
      funext x y; simp [parxPsi]
    rw [e, zero_mul]
    exact Px5Bnds.zero s
  | succ n ih =>
    intro hn
    obtain ⟨C1, hC1, h1⟩ := ih (by omega)
    obtain ⟨C2, hC2, h2⟩ := parxN_conormal_unif hd hs0 hsd m hN n (by omega)
    obtain ⟨Cw, hCw0, hCw, -⟩ : ∃ Cw : ℝ, 0 ≤ Cw ∧
        Px5W s (s - (n : ℝ) / 2 - 2)
          (fun c => 0 + if s - (n : ℝ) / 2 - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) Cw ∧ True := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact ⟨1, zero_le_one, px5W_sharp hs0, trivial⟩
      · obtain ⟨Cw, hCw0, hCw⟩ := px5W_coarse (s := s) (τ := s - (n : ℝ) / 2 - 2)
          (by
            have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
            linarith)
          (fun c => 0 + if s - (n : ℝ) / 2 - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0)
          (fun c => by split_ifs <;> simp)
        exact ⟨Cw, hCw0, hCw, trivial⟩
    refine ⟨C1 + 16 * (C2 * (1 + Cw)), by positivity, fun β V ρ U f hf => ?_⟩
    have hB0 : 0 ≤ C2 * posSeminorm (m + 2) f := mul_nonneg hC2 (posSeminorm_nonneg' _ _)
    have hN' := Px5Bnds.of_conormal (h2 β V ρ U f hf) (by omega) hB0 hCw0 hCw
    have hsum := (h1 β V ρ U f hf).add hN'
    have e : parxPsi d s V β ρ f (n + 1) = fun x y => parxPsi d s V β ρ f n x y +
        newtonOp d β ρ (parxR d s V β ρ f n) x y := by
      funext x y; simp [parxPsi, Finset.sum_range_succ]
    rw [e]
    have e2 : C1 * posSeminorm (m + 2) f + 16 * (C2 * posSeminorm (m + 2) f * (1 + Cw)) =
        (C1 + 16 * (C2 * (1 + Cw))) * posSeminorm (m + 2) f := by ring
    rw [← e2]
    exact hsum

end HRS.ME.ParxU

end
