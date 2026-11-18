import HRS.MC.S7PIEProp
import HRS.MC.Sec7Vocab

/-!
# Packet PI-E, part 3: `V^{t,u}` is uniformly bounded on `E_m` for real `m`

Interpolation (`pie_interp`) between the two integer levels `n₀ < m ≤ n₀ + 1` and duality (`pie_dual`).
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PIE

open HRS HRS.PDE HRS.A33 HRS.Sec7

variable {d : ℕ}

/-- the coefficients of `V^{t,u}F` are the transposed matrix action on the coefficients of `F` -/
lemma pie_Vprop_coeff (D : DynData d) (μ : ℝ → Torus d → ℝ) (m : ℝ) (t u : ℝ) (F : NegSobolev d m)
    (k : NonzeroLattice d) :
    NegSobolev.eval F (propagator D μ u t (Torus.realMode k)) =
      ∑' j, NegSobolev.fourierCoeff F j * pieT D μ u t j k := rfl

/-- squared-norm bound of `V` from a finite-section bound of the matrix at the exponent `m` -/
theorem pie_Vbound_of_finBd (D : DynData d) (μ : ℝ → Torus d → ℝ) (m : ℝ) (t u : ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hH : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (pieT D μ u t) m) A) (F : NegSobolev d m) :
    ‖Vprop D μ m t u F‖ ≤ A * ‖F‖ := by
  have hw : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hcoord : ∀ j, Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j = NegSobolev.coord F j := by
    intro j
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (hw j)]; simp
  obtain ⟨hF2, hFn⟩ := NegSobolev.coord_sq F
  have ha : Summable fun j : NonzeroLattice d =>
      (Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j) ^ 2 :=
    hF2.congr fun j => by rw [hcoord]
  obtain ⟨hs, hle⟩ := pie_dual hw hA hH (fun j => NegSobolev.fourierCoeff F j) ha
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
      NegSobolev.eval F (propagator D μ u t (Torus.realMode k))) 2 := by
    rw [Torus.memℓp_two_iff]
    exact hs
  have hV : Vprop D μ m t u F = NegSobolev.ofSeq m
      (fun k => NegSobolev.eval F (propagator D μ u t (Torus.realMode k))) := rfl
  obtain ⟨hV2, hVn⟩ := NegSobolev.coord_sq (Vprop D μ m t u F)
  have hcV : ∀ k, NegSobolev.coord (Vprop D μ m t u F) k =
      Lattice.jp k.1 ^ (-m) * ∑' j, NegSobolev.fourierCoeff F j * pieT D μ u t j k := by
    intro k
    rw [hV, NegSobolev.coord_ofSeq_of_mem _ hmem k]
    rfl
  have h1 : ‖Vprop D μ m t u F‖ ^ 2 ≤ (A * ‖F‖) ^ 2 := by
    rw [hVn, mul_pow, hFn]
    calc ∑' k, NegSobolev.coord (Vprop D μ m t u F) k ^ 2
        = ∑' k, (Lattice.jp k.1 ^ (-m) * ∑' j, NegSobolev.fourierCoeff F j * pieT D μ u t j k) ^ 2 :=
          tsum_congr fun k => by rw [hcV]
      _ ≤ A ^ 2 * ∑' j, (Lattice.jp j.1 ^ (-m) * NegSobolev.fourierCoeff F j) ^ 2 := hle
      _ = A ^ 2 * ∑' j, NegSobolev.coord F j ^ 2 := by
          congr 1; exact tsum_congr fun j => by rw [hcoord]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hA (norm_nonneg _)) two_ne_zero).1 h1

/-- uniform bound of `V^{t,u}` on `E_m`, `m` real, between the integer levels `n₀ < m ≤ n₀ + 1` -/
theorem pie_Vbound {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (m : ℝ) (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hJ : n₀ + 1 ≤ J) (hm0 : (n₀ : ℝ) < m) (hm1 : m ≤ n₀ + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc 0 T, ∀ u ∈ Set.Icc 0 t, ∀ F : NegSobolev d m,
      ‖Vprop D μ m t u F‖ ≤ C * ‖F‖ := by
  obtain ⟨C0, hC0, h0⟩ := pie_finBd H n₀ hn₀ (by omega)
  obtain ⟨C1, hC1, h1⟩ := pie_finBd H (n₀ + 1) (by omega) hJ
  set θ : ℝ := m - n₀ with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  refine ⟨C0 ^ (1 - θ) * C1 ^ θ, mul_nonneg (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg hC1 _),
    fun t ht u hu F => ?_⟩
  have hw : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  have hint := pie_interp hw (T := pieT D μ u t) hC0 hC1 (h0 t ht u hu)
    (by simpa using h1 t ht u hu) hθ0 hθ1
  have hσ : (1 - θ) * (n₀ : ℝ) + θ * ((n₀ : ℝ) + 1) = m := by
    simp only [hθ]; ring
  rw [hσ] at hint
  exact pie_Vbound_of_finBd D μ m t u (mul_nonneg (Real.rpow_nonneg hC0 _) (Real.rpow_nonneg hC1 _))
    hint F

end HRS.MC.Sec7.PIE

end
