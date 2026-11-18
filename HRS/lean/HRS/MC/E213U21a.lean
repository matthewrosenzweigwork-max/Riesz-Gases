import Mathlib

/-!
# Packet e213u21 (part a): the real-number algebra of `core_bound`

Scratch comment (the exact algebra of the assembly).  For fixed `N ≥ 2`, `a ≥ 0`, `Φ` in the unit ball, `R ≥ 0`, `b = max (a-R) 0`:

* `x₁ = E Φ(ζ_N^{a+·})`, `x₂ = E Φ(Z_a)`, `s = √N`;
* window identity: `x₁ = i₁ - s⁻¹ A_N + (2s)⁻¹ J_N`  (`i₁ = E U_{a,Φ}(0, I_a ζ_N^0)`);
* heat identity: `x₂ = i₂`  (`i₂ = E U_{a,Φ}(0, I_a η^0)`);
* conditioning removal and contractions: `A_∞ = E[DΦ(Z)[D]] = ½ K_d`, `J_∞ = E⟨D²Φ(Z), J⟩ = K_j`,
  with `K_d = E[(E[D⊗Z⊗Z])(D³Φ(Z))]`, `K_j = E[(E[J⊗Z])(D³Φ(Z))]`;
* initial term: `T₃ = E[(I_a^{⊗3}K₀)(D³Φ(Z))] = K₁`;
* symmetry of `D³Φ` and `symm3`: `E[K_a(D³Φ(Z))] = K₁ - 3 K_d + 3 K_j`;
* near/far splitting of the Riemann--Stieltjes integrals `A_N = A_N^n + A_N^f`, etc.

Then `√N(x₁ - x₂) - (1/6) E K_a(D³Φ) = (s(i₁-i₂) - T₃/6) - (A_N - A_∞) + ½(J_N - J_∞)` and the triangle inequality gives
the bound `u21_alg` below.
-/

namespace HRS.MC.E213U21

theorem u21_alg {s x₁ x₂ i₁ i₂ AN JN AG JG T₃ K₁ Kd Kj EK ANn ANf JNn JNf AGn AGf JGn JGf : ℝ} (hs : 0 < s)
    (h₁ : x₁ = i₁ - s⁻¹ * AN + 1 / (2 * s) * JN) (h₂ : x₂ = i₂)
    (hA : AG = 1 / 2 * Kd) (hJ : JG = Kj) (hT : T₃ = K₁) (hK : EK = K₁ - 3 * Kd + 3 * Kj)
    (sAN : AN = ANn + ANf) (sJN : JN = JNn + JNf) (sAG : AG = AGn + AGf) (sJG : JG = JGn + JGf) :
    |s * (x₁ - x₂) - 1 / 6 * EK| ≤
      |s * (i₁ - i₂) - 1 / 6 * T₃| + (|ANn - AGn| + 1 / 2 * |JNn - JGn|) +
        (|ANf| + 1 / 2 * |JNf|) + (|AGf| + 1 / 2 * |JGf|) := by
  have e : s * (x₁ - x₂) - 1 / 6 * EK =
      (s * (i₁ - i₂) - 1 / 6 * T₃) - ((ANn - AGn) + (ANf - AGf)) + 1 / 2 * ((JNn - JGn) + (JNf - JGf)) := by
    have hsne : s ≠ 0 := hs.ne'
    have h1 : s * (x₁ - x₂) = s * (i₁ - i₂) - AN + 1 / 2 * JN := by
      rw [h₁, h₂]
      field_simp
      ring
    have h2 : 1 / 6 * EK = 1 / 6 * T₃ - AG + 1 / 2 * JG := by
      rw [hK, hT, hJ]
      have : Kd = 2 * AG := by rw [hA]; ring
      rw [this]
      ring
    rw [h1, h2, sAN, sJN]
    rw [sAG, sJG]
    ring
  rw [e]
  set a1 := s * (i₁ - i₂) - 1 / 6 * T₃
  set a2 := ANn - AGn
  set a3 := ANf - AGf
  set a4 := JNn - JGn
  set a5 := JNf - JGf
  have b1 : |a1 - (a2 + a3) + 1 / 2 * (a4 + a5)| ≤ |a1| + |a2| + |a3| + 1 / 2 * |a4| + 1 / 2 * |a5| := by
    have := abs_add_le (a1 - (a2 + a3)) (1 / 2 * (a4 + a5))
    have h2 : |a1 - (a2 + a3)| ≤ |a1| + |a2| + |a3| := by
      calc |a1 - (a2 + a3)| ≤ |a1| + |a2 + a3| := abs_sub _ _
        _ ≤ |a1| + (|a2| + |a3|) := by gcongr; exact abs_add_le _ _
        _ = _ := by ring
    have h3 : |1 / 2 * (a4 + a5)| ≤ 1 / 2 * |a4| + 1 / 2 * |a5| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := abs_add_le a4 a5
      nlinarith
    linarith
  have c1 : |a3| ≤ |ANf| + |AGf| := abs_sub _ _
  have c2 : |a5| ≤ |JNf| + |JGf| := abs_sub _ _
  linarith

end HRS.MC.E213U21
