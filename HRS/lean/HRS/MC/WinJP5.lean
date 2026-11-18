import HRS.MC.WinJSpecDefs
import HRS.MC.WinJP3
import HRS.MC.WinJP4
import HRS.MC.E213J4
import HRS.MC.S7PIDTSys
import HRS.MC.S7PIDTBound
import HRS.MC.S7PIDTNucg
import HRS.MC.S7PIDTPhi
import HRS.MC.S7PIDTVec
import HRS.MC.S7PIDTCore

/-!
# WJ5: P5 `p5_nuc_trunc_diff` (truncated nuclear bound for the difference of the two regimes)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

section P5Abstract

open HRS.MC.Sec7.S7PIDT

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {r : ℕ}

/-- the `L²` data of a dyadic node family at level `ν` (the hypotheses of `S7PIDT_sys`) -/
def p_wj5_Fam (I : Set ℝ) (ν : ℕ) (g : ℕ → ℝ → EuclideanSpace ℝ (Fin r)) (κ : ℝ) : Prop :=
  (∀ i ≤ 2 ^ ν, MemLp (g i) 2 (volume.restrict I)) ∧
  (∀ i j, i ≤ j → j ≤ 2 ^ ν → ∫ u in I, ‖g j u - g i u‖ ^ 2 ≤ κ * (((j : ℝ) - i) / 2 ^ ν)) ∧
  (∀ i ≤ 2 ^ ν, ∫ u in I, ‖g i u‖ ^ 2 ≤ κ)

lemma p_wj5_int (I : Set ℝ) (ν : ℕ) (g g' : ℕ → ℝ → EuclideanSpace ℝ (Fin r)) {κ κ' : ℝ}
    (hF : p_wj5_Fam I ν g κ) (hF' : p_wj5_Fam I ν g' κ')
    (Φ Φ' : (Fin (2 ^ ν + 1) → EuclideanSpace ℝ (Fin r)) →L[ℝ] X) (M : X [×2]→L[ℝ] ℝ) :
    Integrable (fun u => M ![Φ (fun i => g i.1 u), Φ' (fun i => g' i.1 u)]) (volume.restrict I) := by
  obtain ⟨B, hB⟩ := S7PIDT_expand M Φ Φ'
  simp_rw [hB]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    S7PIDT_int_bilin _ (hF.1 i.1 (Nat.lt_succ_iff.1 i.2)) (hF'.1 j.1 (Nat.lt_succ_iff.1 j.2))

theorem p_wj5_level (ν : ℕ) (I : Set ℝ) (g g' : ℕ → ℝ → EuclideanSpace ℝ (Fin r)) {κ κ' : ℝ}
    (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') (hF : p_wj5_Fam I ν g κ) (hF' : p_wj5_Fam I ν g' κ')
    (Φ Φ' : (Fin (2 ^ ν + 1) → EuclideanSpace ℝ (Fin r)) →L[ℝ] X) (Ca Cb : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hΦ : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ i ≤ 2 ^ ν, ‖v i‖ ≤ s) →
      ‖Φ (fun i => v i.1)‖ ≤ Ca * s)
    (hΦ' : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ i ≤ 2 ^ ν, ‖v i‖ ≤ s) →
      ‖Φ' (fun i => v i.1)‖ ≤ Cb * s)
    (W : ℝ) (hW : 0 ≤ W) (hW2 : W ^ 2 = κ * κ') (M : X [×2]→L[ℝ] ℝ) :
    |∫ u in I, M ![Φ (fun i => g i.1 u), Φ' (fun i => g' i.1 u)]| ≤ 162 * (‖M‖ * Ca * Cb * W) := by
  obtain ⟨Ω, hΩ, P, hP, Y, Y', hid, ⟨S, S', hSm, hSm', hS0, hS0', hSb, hSb', hSi, hSi', hSI, hSI'⟩, -⟩ :=
    S7PIDT_sys (X := X) ν I g g' κ κ' hκ hκ' hF.1 hF'.1 hF.2.1 hF'.2.1 hF.2.2 hF'.2.2
  rw [(hid Φ Φ' M).2]
  have h1 := S7PIDT_B1 P M (fun ω => Φ (fun i => Y i.1 ω)) (fun ω => Φ' (fun i => Y' i.1 ω)) 1
    (Ca ^ 2 * κ) (Cb ^ 2 * κ') (Ca * Cb * W) zero_le_one (by positivity)
    (by rw [mul_pow, mul_pow, hW2]; ring)
    (fun ω => Ca * S ω) (fun ω => Cb * S' ω) (hSm.const_mul _) (hSm'.const_mul _)
    (fun ω => mul_nonneg hCa (hS0 ω)) (fun ω => mul_nonneg hCb (hS0' ω))
    (fun ω => by
      rw [one_mul]; exact hΦ (fun i => Y i ω) (S ω) fun i hi => hSb ω i hi)
    (fun ω => by
      rw [one_mul]; exact hΦ' (fun i => Y' i ω) (S' ω) fun i hi => hSb' ω i hi)
    (by simp_rw [mul_pow]; exact hSi.const_mul _) (by simp_rw [mul_pow]; exact hSi'.const_mul _)
    (by
      simp_rw [mul_pow]; rw [integral_const_mul]
      calc Ca ^ 2 * ∫ ω, S ω ^ 2 ∂P ≤ Ca ^ 2 * (162 * κ) := by gcongr
        _ = 162 * (Ca ^ 2 * κ) := by ring)
    (by
      simp_rw [mul_pow]; rw [integral_const_mul]
      calc Cb ^ 2 * ∫ ω, S' ω ^ 2 ∂P ≤ Cb ^ 2 * (162 * κ') := by gcongr
        _ = 162 * (Cb ^ 2 * κ') := by ring)
  refine h1.trans (le_of_eq ?_)
  ring

theorem p_wj5_incr (n : ℕ) (I : Set ℝ) (g g' : ℕ → ℝ → EuclideanSpace ℝ (Fin r)) {κ κ' : ℝ}
    (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') (hF : p_wj5_Fam I (n + 1) g κ) (hF' : p_wj5_Fam I (n + 1) g' κ')
    (Φ Φ' Φ₀ Φ₀' : (Fin (2 ^ (n + 1) + 1) → EuclideanSpace ℝ (Fin r)) →L[ℝ] X)
    (Ca Cb Da Db : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hDa : 0 ≤ Da) (hDb : 0 ≤ Db)
    (hΦ₀ : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ i ≤ 2 ^ (n + 1), ‖v i‖ ≤ s) →
      ‖Φ₀ (fun i => v i.1)‖ ≤ Ca * s)
    (hΦ' : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ i ≤ 2 ^ (n + 1), ‖v i‖ ≤ s) →
      ‖Φ' (fun i => v i.1)‖ ≤ Cb * s)
    (hΔ : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ k < 2 ^ (n + 1), ‖v (k + 1) - v k‖ ≤ s) →
      ‖Φ (fun i => v i.1) - Φ₀ (fun i => v i.1)‖ ≤ Da * s)
    (hΔ' : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ k < 2 ^ (n + 1), ‖v (k + 1) - v k‖ ≤ s) →
      ‖Φ' (fun i => v i.1) - Φ₀' (fun i => v i.1)‖ ≤ Db * s)
    (W : ℝ) (hW : 0 ≤ W) (hW2 : W ^ 2 = κ * κ') (M : X [×2]→L[ℝ] ℝ) :
    |(∫ u in I, M ![Φ (fun i => g i.1 u), Φ' (fun i => g' i.1 u)]) -
        ∫ u in I, M ![Φ₀ (fun i => g i.1 u), Φ₀' (fun i => g' i.1 u)]| ≤
      ‖M‖ * (18 * W * (2 : ℝ) ^ (-(n : ℝ) / 4) * (Da * Cb + Db * Ca)) := by
  obtain ⟨Ω, hΩ, P, hP, Y, Y', hid, ⟨S, S', hSm, hSm', hS0, hS0', hSb, hSb', hSi, hSi', hSI, hSI'⟩,
    ⟨δ, δ', hδm, hδm', hδ0, hδ0', hδb, hδb', hδi, hδi', hδI, hδI'⟩⟩ :=
    S7PIDT_sys (X := X) (n + 1) I g g' κ κ' hκ hκ' hF.1 hF'.1 hF.2.1 hF'.2.1 hF.2.2 hF'.2.2
  obtain ⟨hI1, hE1⟩ := hid Φ Φ' M
  obtain ⟨hI0, hE0⟩ := hid Φ₀ Φ₀' M
  rw [hE1, hE0]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (2 : ℝ) ^ (-(n : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hθ]
  have hθ0 : 0 < θ := by rw [hθ]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hθ4 : θ ^ 4 = 1 / 2 ^ n := by rw [hθ]; exact S7PIDT_theta4 n
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hδ2 : ∫ ω, δ ω ^ 2 ∂P ≤ 2 * κ * θ ^ 2 := by
    refine S7PIDT_le_of_sq (by positivity) (hδI.trans ?_)
    have e1 : (2 * κ * θ ^ 2) ^ 2 = 4 * κ ^ 2 * (1 / 2 ^ n) := by rw [← hθ4]; ring
    have e2 : 3 * κ ^ 2 / 2 ^ (n + 1) = (3 / 2) * κ ^ 2 * (1 / 2 ^ n) := by
      field_simp; ring
    have e3 : 0 ≤ κ ^ 2 * (1 / 2 ^ n) := by positivity
    rw [e1, e2]; linarith
  have hδ2' : ∫ ω, δ' ω ^ 2 ∂P ≤ 2 * κ' * θ ^ 2 := by
    refine S7PIDT_le_of_sq (by positivity) (hδI'.trans ?_)
    have e1 : (2 * κ' * θ ^ 2) ^ 2 = 4 * κ' ^ 2 * (1 / 2 ^ n) := by rw [← hθ4]; ring
    have e2 : 3 * κ' ^ 2 / 2 ^ (n + 1) = (3 / 2) * κ' ^ 2 * (1 / 2 ^ n) := by
      field_simp; ring
    have e3 : 0 ≤ κ' ^ 2 * (1 / 2 ^ n) := by positivity
    rw [e1, e2]; linarith
  have hB := S7PIDT_B2 P M (fun ω => Φ (fun i => Y i.1 ω)) (fun ω => Φ' (fun i => Y' i.1 ω))
    (fun ω => Φ₀ (fun i => Y i.1 ω)) (fun ω => Φ₀' (fun i => Y' i.1 ω)) 1 zero_le_one
    (Da ^ 2 * (2 * κ * θ ^ 2)) (Ca ^ 2 * (162 * κ)) (Db ^ 2 * (2 * κ' * θ ^ 2)) (Cb ^ 2 * (162 * κ'))
    (Da * Cb * (18 * W * θ)) (Db * Ca * (18 * W * θ)) (by positivity) (by positivity)
    (by linear_combination (Da ^ 2 * Cb ^ 2 * 324 * θ ^ 2) * hW2)
    (by linear_combination (Db ^ 2 * Ca ^ 2 * 324 * θ ^ 2) * hW2)
    (fun ω => Ca * S ω) (fun ω => Cb * S' ω) (fun ω => Da * δ ω) (fun ω => Db * δ' ω)
    (hSm.const_mul _) (hSm'.const_mul _) (hδm.const_mul _) (hδm'.const_mul _)
    (fun ω => mul_nonneg hCa (hS0 ω)) (fun ω => mul_nonneg hCb (hS0' ω))
    (fun ω => mul_nonneg hDa (hδ0 ω)) (fun ω => mul_nonneg hDb (hδ0' ω))
    (fun ω => by rw [one_mul]; exact hΦ' (fun i => Y' i ω) (S' ω) fun i hi => hSb' ω i hi)
    (fun ω => by rw [one_mul]; exact hΦ₀ (fun i => Y i ω) (S ω) fun i hi => hSb ω i hi)
    (fun ω => by rw [one_mul]; exact hΔ (fun i => Y i ω) (δ ω) fun k hk => hδb ω k hk)
    (fun ω => by rw [one_mul]; exact hΔ' (fun i => Y' i ω) (δ' ω) fun k hk => hδb' ω k hk)
    (by simp_rw [mul_pow]; exact hSi.const_mul _) (by simp_rw [mul_pow]; exact hSi'.const_mul _)
    (by simp_rw [mul_pow]; exact hδi.const_mul _) (by simp_rw [mul_pow]; exact hδi'.const_mul _)
    (by
      simp_rw [mul_pow]; rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hδ2 (by positivity))
    (by
      simp_rw [mul_pow]; rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hδ2' (by positivity))
    (by
      simp_rw [mul_pow]; rw [integral_const_mul]
      calc Ca ^ 2 * ∫ ω, S ω ^ 2 ∂P ≤ Ca ^ 2 * (162 * κ) := by gcongr
        _ = Ca ^ 2 * (162 * κ) := rfl)
    (by
      simp_rw [mul_pow]; rw [integral_const_mul]
      calc Cb ^ 2 * ∫ ω, S' ω ^ 2 ∂P ≤ Cb ^ 2 * (162 * κ') := by gcongr
        _ = Cb ^ 2 * (162 * κ') := rfl)
    hI1 hI0
  refine hB.trans (le_of_eq ?_)
  ring

/-- the subsampling `i ↦ 2 i` of a fine node vector -/
def p_wj5_sub (n r : ℕ) :
    (Fin (2 ^ (n + 1) + 1) → EuclideanSpace ℝ (Fin r)) →L[ℝ] (Fin (2 ^ n + 1) → EuclideanSpace ℝ (Fin r)) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj
    (⟨2 * j.1, Nat.lt_succ_of_le (by have := Nat.lt_succ_iff.1 j.2; rw [pow_succ]; omega)⟩ :
      Fin (2 ^ (n + 1) + 1))

lemma p_wj5_sub_apply (n r : ℕ) (x : Fin (2 ^ (n + 1) + 1) → EuclideanSpace ℝ (Fin r)) (j : Fin (2 ^ n + 1)) :
    p_wj5_sub n r x j = x ⟨2 * j.1, Nat.lt_succ_of_le (by
      have := Nat.lt_succ_iff.1 j.2; rw [pow_succ]; omega)⟩ := rfl

theorem p_wj5_pair (n : ℕ) (I : Set ℝ) (gn g1 g'n g'1 : ℕ → ℝ → EuclideanSpace ℝ (Fin r)) {κ κ' : ℝ}
    (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (hFn : p_wj5_Fam I n gn κ) (hF1 : p_wj5_Fam I (n + 1) g1 κ)
    (hF'n : p_wj5_Fam I n g'n κ') (hF'1 : p_wj5_Fam I (n + 1) g'1 κ')
    (hd : ∀ j u, gn j u = g1 (2 * j) u) (hd' : ∀ j u, g'n j u = g'1 (2 * j) u)
    (Φn Φ'n : (Fin (2 ^ n + 1) → EuclideanSpace ℝ (Fin r)) →L[ℝ] X)
    (Φ1 Φ'1 : (Fin (2 ^ (n + 1) + 1) → EuclideanSpace ℝ (Fin r)) →L[ℝ] X)
    (Ca Cb Da Db : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hDa : 0 ≤ Da) (hDb : 0 ≤ Db)
    (hΦn : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ i ≤ 2 ^ n, ‖v i‖ ≤ s) →
      ‖Φn (fun i => v i.1)‖ ≤ Ca * s)
    (hΦ'n : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ i ≤ 2 ^ n, ‖v i‖ ≤ s) →
      ‖Φ'n (fun i => v i.1)‖ ≤ Cb * s)
    (hΦ'1 : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ i ≤ 2 ^ (n + 1), ‖v i‖ ≤ s) →
      ‖Φ'1 (fun i => v i.1)‖ ≤ Cb * s)
    (hΔ : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ k < 2 ^ (n + 1), ‖v (k + 1) - v k‖ ≤ s) →
      ‖Φ1 (fun i => v i.1) - Φn (fun j => v (2 * j.1))‖ ≤ Da * s)
    (hΔ' : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ k < 2 ^ (n + 1), ‖v (k + 1) - v k‖ ≤ s) →
      ‖Φ'1 (fun i => v i.1) - Φ'n (fun j => v (2 * j.1))‖ ≤ Db * s)
    (W : ℝ) (hW : 0 ≤ W) (hW2 : W ^ 2 = κ * κ') (M : X [×2]→L[ℝ] ℝ) :
    |∫ u in I, M ![Φn (fun i => gn i.1 u), Φ'n (fun i => g'n i.1 u)]| ≤ 162 * (‖M‖ * Ca * Cb * W) ∧
    |(∫ u in I, M ![Φ1 (fun i => g1 i.1 u), Φ'1 (fun i => g'1 i.1 u)]) -
        ∫ u in I, M ![Φn (fun i => gn i.1 u), Φ'n (fun i => g'n i.1 u)]| ≤
      ‖M‖ * (18 * W * (2 : ℝ) ^ (-(n : ℝ) / 4) * (Da * Cb + Db * Ca)) := by
  refine ⟨p_wj5_level n I gn g'n hκ hκ' hFn hF'n Φn Φ'n Ca Cb hCa hCb hΦn hΦ'n W hW hW2 M, ?_⟩
  have heq : ∫ u in I, M ![Φn (fun i => gn i.1 u), Φ'n (fun i => g'n i.1 u)] =
      ∫ u in I, M ![(Φn.comp (p_wj5_sub n r)) (fun i => g1 i.1 u),
        (Φ'n.comp (p_wj5_sub n r)) (fun i => g'1 i.1 u)] := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show _ = M ![Φn (fun j => g1 (2 * j.1) u), Φ'n (fun j => g'1 (2 * j.1) u)]
    simp only [hd, hd']
  rw [heq]
  exact p_wj5_incr n I g1 g'1 hκ hκ' hF1 hF'1 Φ1 Φ'1 (Φn.comp (p_wj5_sub n r)) (Φ'n.comp (p_wj5_sub n r))
    Ca Cb Da Db hCa hCb hDa hDb
    (fun v s hv => hΦn (fun j => v (2 * j)) s fun i hi => hv _ (by rw [pow_succ]; omega))
    hΦ'1 hΔ hΔ' W hW hW2 M

end P5Abstract

section P5Algebra

variable {d : ℕ}

lemma p_wj5_trunc_sub (m : ℝ) (F : Finset (NonzeroLattice d)) (a b : NegSobolev d m) :
    truncF m F (a - b) = truncF m F a - truncF m F b := by
  refine HRS.MC.Sec7.PIE.pie_ext _ _ fun k => ?_
  simp only [HRS.MC.Sec7.S7PIDT.S7PIDT_coord_sub, HRS.MC.Sec7.S7PIDT.S7PIDT_coord_trunc]
  split_ifs <;> simp

lemma p_wj5_split {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (M : X [×2]→L[ℝ] ℝ)
    (a b a' b' a1 a2 b1 b2 : X) (ha : a - a' = a1 + a2) (hb : b - b' = b1 + b2) :
    M ![a, b] - M ![a', b'] =
      M ![a1, b] + M ![a2, b] + (M ![a', b1] + M ![a', b2]) := by
  have e1 : a = (a1 + a2) + a' := by rw [← ha]; abel
  have e2 : b = (b1 + b2) + b' := by rw [← hb]; abel
  have h1 := HRS.MC.Sec7.S7PIDN.S7PIDN_elem_add_left M (a1 + a2) a' b
  have h2 := HRS.MC.Sec7.S7PIDN.S7PIDN_elem_add_left M a1 a2 b
  have h3 := HRS.MC.Sec7.S7PIDN.S7PIDN_elem_add_right M a' (b1 + b2) b'
  have h4 := HRS.MC.Sec7.S7PIDN.S7PIDN_elem_add_right M a' b1 b2
  rw [← e1] at h1
  rw [← e2] at h3
  have h5 : M ![a, b] = M ![a1 + a2, b] + M ![a', b] := h1
  rw [h5]
  have h6 : M ![a', b] = M ![a', b1 + b2] + M ![a', b'] := by
    have := HRS.MC.Sec7.S7PIDN.S7PIDN_elem_add_right M a' (b1 + b2) b'
    rw [← e2] at this; exact this
  rw [h6, h2, h4]; ring

lemma p_wj5_add {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℝ} {r N : ℕ}
    (emb : EuclideanSpace ℝ (Fin r) →L[ℝ] NegSobolev d m)
    (Φ : (Fin N → NegSobolev d m) →L[ℝ] X) (y y1 y2 : Fin N → EuclideanSpace ℝ (Fin r))
    (h : ∀ i, emb (y i) = emb (y1 i) + emb (y2 i)) :
    (Φ.comp (ContinuousLinearMap.pi fun j => emb.comp (ContinuousLinearMap.proj j))) y =
      (Φ.comp (ContinuousLinearMap.pi fun j => emb.comp (ContinuousLinearMap.proj j))) y1 +
      (Φ.comp (ContinuousLinearMap.pi fun j => emb.comp (ContinuousLinearMap.proj j))) y2 := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [← map_add]
  congr 1
  funext i
  exact h i

/-- the node-family map `Φ ∘ emb^{N+1}` -/
def p_wj5_Psi {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℝ} {r N : ℕ}
    (emb : EuclideanSpace ℝ (Fin r) →L[ℝ] NegSobolev d m) (Φ : (Fin N → NegSobolev d m) →L[ℝ] X) :
    (Fin N → EuclideanSpace ℝ (Fin r)) →L[ℝ] X :=
  Φ.comp (ContinuousLinearMap.pi fun j => emb.comp (ContinuousLinearMap.proj j))

lemma p_wj5_Psi_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℝ} {r N : ℕ}
    (emb : EuclideanSpace ℝ (Fin r) →L[ℝ] NegSobolev d m) (Φ : (Fin N → NegSobolev d m) →L[ℝ] X)
    (y : Fin N → EuclideanSpace ℝ (Fin r)) : p_wj5_Psi emb Φ y = Φ (fun j => emb (y j)) := rfl

lemma p_wj5_Psi_add {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℝ} {r N : ℕ}
    (emb : EuclideanSpace ℝ (Fin r) →L[ℝ] NegSobolev d m)
    (Φ : (Fin N → NegSobolev d m) →L[ℝ] X) (y y1 y2 : Fin N → EuclideanSpace ℝ (Fin r))
    (h : ∀ i, emb (y i) = emb (y1 i) + emb (y2 i)) :
    p_wj5_Psi emb Φ y = p_wj5_Psi emb Φ y1 + p_wj5_Psi emb Φ y2 := by
  simp only [p_wj5_Psi_apply]
  rw [← map_add]
  congr 1
  funext i
  exact h i

theorem p_wj5_four {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℝ} {r : ℕ}
    (emb : EuclideanSpace ℝ (Fin r) →L[ℝ] NegSobolev d m) (ν : ℕ) (I : Set ℝ)
    (gp gs gW hp hs hW : ℕ → ℝ → EuclideanSpace ℝ (Fin r)) {κ1 κ2 κ3 κ4 κ5 κ6 : ℝ}
    (hFgp : p_wj5_Fam I ν gp κ1) (hFgs : p_wj5_Fam I ν gs κ2) (hFgW : p_wj5_Fam I ν gW κ3)
    (hFhp : p_wj5_Fam I ν hp κ4) (hFhs : p_wj5_Fam I ν hs κ5) (hFhW : p_wj5_Fam I ν hW κ6)
    (Φp Φs : (Fin (2 ^ ν + 1) → NegSobolev d m) →L[ℝ] X)
    (hg : ∀ i u, emb (gp i u) = emb (gW i u) + emb (gs i u))
    (hh : ∀ i u, emb (hp i u) = emb (hW i u) + emb (hs i u)) (M : X [×2]→L[ℝ] ℝ) :
    (∫ u in I, M ![p_wj5_Psi emb Φp (fun i => gp i.1 u), p_wj5_Psi emb Φp (fun i => hp i.1 u)]) -
      (∫ u in I, M ![p_wj5_Psi emb Φs (fun i => gs i.1 u), p_wj5_Psi emb Φs (fun i => hs i.1 u)]) =
    (∫ u in I, M ![p_wj5_Psi emb Φp (fun i => gW i.1 u), p_wj5_Psi emb Φp (fun i => hp i.1 u)]) +
    (∫ u in I, M ![(p_wj5_Psi emb Φp - p_wj5_Psi emb Φs) (fun i => gs i.1 u),
        p_wj5_Psi emb Φp (fun i => hp i.1 u)]) +
    ((∫ u in I, M ![p_wj5_Psi emb Φs (fun i => gs i.1 u), p_wj5_Psi emb Φp (fun i => hW i.1 u)]) +
     (∫ u in I, M ![p_wj5_Psi emb Φs (fun i => gs i.1 u),
        (p_wj5_Psi emb Φp - p_wj5_Psi emb Φs) (fun i => hs i.1 u)])) := by
  have i1 := p_wj5_int I ν gp hp hFgp hFhp (p_wj5_Psi emb Φp) (p_wj5_Psi emb Φp) M
  have i2 := p_wj5_int I ν gs hs hFgs hFhs (p_wj5_Psi emb Φs) (p_wj5_Psi emb Φs) M
  have t1 := p_wj5_int I ν gW hp hFgW hFhp (p_wj5_Psi emb Φp) (p_wj5_Psi emb Φp) M
  have t2 := p_wj5_int I ν gs hp hFgs hFhp (p_wj5_Psi emb Φp - p_wj5_Psi emb Φs) (p_wj5_Psi emb Φp) M
  have t3 := p_wj5_int I ν gs hW hFgs hFhW (p_wj5_Psi emb Φs) (p_wj5_Psi emb Φp) M
  have t4 := p_wj5_int I ν gs hs hFgs hFhs (p_wj5_Psi emb Φs) (p_wj5_Psi emb Φp - p_wj5_Psi emb Φs) M
  rw [← integral_sub i1 i2, ← integral_add t3 t4, ← integral_add t1 t2, ← integral_add (t1.fun_add t2) (t3.fun_add t4)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  refine p_wj5_split M _ _ _ _ _ _ _ _ ?_ ?_
  · rw [p_wj5_Psi_add emb Φp (fun i => gp i.1 u) (fun i => gW i.1 u) (fun i => gs i.1 u) fun i => hg i.1 u,
      sub_apply]
    abel
  · rw [p_wj5_Psi_add emb Φp (fun i => hp i.1 u) (fun i => hW i.1 u) (fun i => hs i.1 u) fun i => hh i.1 u,
      sub_apply]
    abel

lemma p_wj5_fam_of {r : ℕ} (c c' : ℝ) (hcc : c ≤ c') (ν : ℕ) (g : ℕ → ℝ → EuclideanSpace ℝ (Fin r))
    (Q Q' : ℝ) (hQ : Q ≤ Q')
    (hmem : ∀ i ≤ 2 ^ ν, MemLp (g i) 2 (volume.restrict (Set.Ioc c c')))
    (hinc : ∀ i j, i ≤ j → j ≤ 2 ^ ν → ∫ u in Set.Ioc c c', ‖g j u - g i u‖ ^ 2 ≤
      Q * (gridPt c c' ν j - gridPt c c' ν i))
    (hmom : ∀ i ≤ 2 ^ ν, ∫ u in Set.Ioc c c', ‖g i u‖ ^ 2 ≤ Q * (c' - c)) :
    p_wj5_Fam (Set.Ioc c c') ν g (Q' * (c' - c)) := by
  have hΔ : 0 ≤ c' - c := sub_nonneg.2 hcc
  refine ⟨hmem, fun i j hij hj => ?_, fun i hi => (hmom i hi).trans ?_⟩
  · refine (hinc i j hij hj).trans ?_
    rw [HRS.MC.Sec7.S7PIDT.S7PIDT_grid_sub]
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have h0 : 0 ≤ ((j : ℝ) - i) / 2 ^ ν := div_nonneg (by linarith) (by positivity)
    have : (c' - c) * ((j : ℝ) - i) / 2 ^ ν = (c' - c) * (((j : ℝ) - i) / 2 ^ ν) := by ring
    rw [this]
    nlinarith [mul_nonneg hΔ h0]
  · exact mul_le_mul_of_nonneg_right hQ hΔ

lemma p_wj5_dbl {m : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ) (c c' : ℝ) (n : ℕ) (pp : ℝ → ℝ)
    (ee : NegSobolev d m) (u : ℝ) (i : ℕ) :
    kernelNodes D ρ m c c' n pp ee u i = kernelNodes D ρ m c c' (n + 1) pp ee u (2 * i) := by
  unfold kernelNodes
  rw [HRS.MC.Sec7.S7PIDT.S7PIDT_grid_double c c' n i]

end P5Algebra

lemma p_wj5_abs4 (a1 a2 a3 a4 b1 b2 b3 b4 : ℝ) :
    |(a1 + a2 + (a3 + a4)) - (b1 + b2 + (b3 + b4))| ≤
      |a1 - b1| + |a2 - b2| + (|a3 - b3| + |a4 - b4|) := by
  have e : (a1 + a2 + (a3 + a4)) - (b1 + b2 + (b3 + b4)) = (a1 - b1) + (a2 - b2) + ((a3 - b3) + (a4 - b4)) := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  exact add_le_add (abs_add_le _ _) (abs_add_le _ _)

lemma p_wj5_abs4' (a1 a2 a3 a4 : ℝ) : |a1 + a2 + (a3 + a4)| ≤ |a1| + |a2| + (|a3| + |a4|) := by
  refine (abs_add_le _ _).trans ?_
  exact add_le_add (abs_add_le _ _) (abs_add_le _ _)

section P5Main

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

/-- the coordinates of the plain kernel nodes -/
def p_wj5_g {r : ℕ} (R : Regime d) (c c' : ℝ) (Gm : NegSobolev d m → EuclideanSpace ℝ (Fin r))
    (pp : ℝ → ℝ) (e : NegSobolev d m) (ν i : ℕ) (u : ℝ) : EuclideanSpace ℝ (Fin r) :=
  Gm (kernelNodes R.D R.ρ m c c' ν pp e u i)

/-- the coordinates of the difference kernel nodes -/
def p_wj5_gW (sd : StatDatum S β₀ m hE) (b : ℝ) (hb : 0 ≤ b) {r : ℕ} (c c' : ℝ)
    (Gm : NegSobolev d m → EuclideanSpace ℝ (Fin r))
    (pp : ℝ → ℝ) (e : NegSobolev d m) (ν i : ℕ) (u : ℝ) : EuclideanSpace ℝ (Fin r) :=
  Gm (kernelNodesW sd b hb c c' ν pp e u i)

end P5Main

section Packets

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

set_option maxHeartbeats 4000000 in
theorem p5_nuc_trunc_diff (sd : StatDatum S β₀ m hE) (T : ℝ) (hT : 0 < T) :
    ∃ K κ : ℝ, 0 ≤ K ∧ 0 < κ ∧ ∀ (b : ℝ) (hb : 0 ≤ b) (p q : ℝ → ℝ) (Bp Bq : ℝ), Measurable p → Measurable q →
      (∀ u, |p u| ≤ Bp) → (∀ u, |q u| ≤ Bq) → ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T →
      ∀ (k l : NonzeroLattice d) (F : Finset (NonzeroLattice d)) (n : ℕ) (M : PathSpace d m T [×2]→L[ℝ] ℝ),
      |nucK (Rp sd b hb) m T c c' n p q k l (truncF m F) M -
          nucK (Rs sd b hb) m T c c' n p q k l (truncF m F) M| ≤
        ‖M‖ * (K * Bp * Bq * Real.exp (-κ * b) * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) *
          (c' - c)) ∧
      |(nucK (Rp sd b hb) m T c c' (n + 1) p q k l (truncF m F) M -
          nucK (Rs sd b hb) m T c c' (n + 1) p q k l (truncF m F) M) -
        (nucK (Rp sd b hb) m T c c' n p q k l (truncF m F) M -
          nucK (Rs sd b hb) m T c c' n p q k l (truncF m F) M)| ≤
        ‖M‖ * (K * Bp * Bq * Real.exp (-κ * b) * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) *
          (c' - c) * (2 : ℝ) ^ (-(n : ℝ) / 4)) := by
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  obtain ⟨K1p, Cbp, hK1p, hCbp, hfamp⟩ := HRS.MC.E213J.e213j_fam (regime S β₀ hE) m hm T hT
  obtain ⟨K1s, Cbs, hK1s, hCbs, hfams⟩ :=
    HRS.MC.E213J.e213j_fam (regime sd.Ss S.β sd.hEs) m sd.hEs.m_gt T hT
  obtain ⟨K1W, CbW, κ3, hK1W, hCbW, hκ3, hfamW⟩ := p3_W_fam sd T hT
  obtain ⟨C1, Cw, κ4, hC1, hCw, hκ4, hpoly⟩ := p4_polyMix_bounds sd T hT
  have hC10 : 0 ≤ C1 := by linarith
  obtain ⟨K1, hK1def⟩ : ∃ K1 : ℝ, K1 = K1p + K1s + K1W := ⟨_, rfl⟩
  have hK1 : 0 ≤ K1 := by rw [hK1def]; positivity
  have hK1p' : K1p ≤ K1 := by rw [hK1def]; linarith
  have hK1s' : K1s ≤ K1 := by rw [hK1def]; linarith
  have hK1W' : K1W ≤ K1 := by rw [hK1def]; linarith
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ, C0 = C1 + Cw := ⟨_, rfl⟩
  have hC00 : 0 ≤ C0 := by rw [hC0def]; positivity
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min κ3 κ4 := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact lt_min hκ3 hκ4
  have hκ3' : κ ≤ κ3 := by rw [hκdef]; exact min_le_left _ _
  have hκ4' : κ ≤ κ4 := by rw [hκdef]; exact min_le_right _ _
  obtain ⟨Kc, hKcdef⟩ : ∃ Kc : ℝ, Kc = 162 * (C1 ^ 2 + C1 * Cw + C0 * C1 + C0 * Cw) +
      18 * (3 * C1 + 2 * Cw + C0) := ⟨_, rfl⟩
  have hKc : 0 ≤ Kc := by rw [hKcdef]; positivity
  refine ⟨K1 * Kc, κ, by positivity, hκ, ?_⟩
  intro b hb p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l F n M
  by_cases hceq : c = c'
  · subst hceq
    have h0 : ∀ (R : Regime d) (μ : ℕ), nucK R m T c c μ p q k l (truncF m F) = 0 := by
      intro R μ
      unfold nucK nuc
      rw [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]
    simp [h0]
  have hlt : c < c' := lt_of_le_of_ne hcc hceq
  have hΔ0 : 0 < c' - c := sub_pos.2 hlt
  have hc'0 : 0 ≤ c' := hc.trans hcc
  have hBp : 0 ≤ Bp := (abs_nonneg _).trans (hpB 0)
  have hBq : 0 ≤ Bq := (abs_nonneg _).trans (hqB 0)
  obtain ⟨r, emb, Gm, hemb, hG1, hG0, hGc, hembG⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_vec' m F
  have hjk : 0 ≤ Lattice.jp k.1 := (Torus.jp_pos k.1).le
  have hjl : 0 ≤ Lattice.jp l.1 := (Torus.jp_pos l.1).le
  obtain ⟨ak, hakdef⟩ : ∃ ak : ℝ, ak = Lattice.jp k.1 ^ (-(m - 1)) := ⟨_, rfl⟩
  obtain ⟨al, haldef⟩ : ∃ al : ℝ, al = Lattice.jp l.1 ^ (-(m - 1)) := ⟨_, rfl⟩
  have hak0 : 0 ≤ ak := by rw [hakdef]; exact Real.rpow_nonneg hjk _
  have hal0 : 0 ≤ al := by rw [haldef]; exact Real.rpow_nonneg hjl _
  have hak2 : Lattice.jp k.1 ^ (-(2 * (m - 1))) = ak ^ 2 := by
    rw [hakdef]; exact (HRS.MC.Sec7.S7PIDI.S7PIDI_rpow_sq _ hjk (m - 1)).symm
  have hal2 : Lattice.jp l.1 ^ (-(2 * (m - 1))) = al ^ 2 := by
    rw [haldef]; exact (HRS.MC.Sec7.S7PIDI.S7PIDI_rpow_sq _ hjl (m - 1)).symm
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (-κ * b) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  have hexp : ∀ κ' : ℝ, κ ≤ κ' → Real.exp (-2 * κ' * b) ≤ E ^ 2 := by
    intro κ' h
    rw [hEdef, sq, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right h hb]
  have hexp4 : Real.exp (-κ4 * (b + c')) ≤ E := by
    rw [hEdef]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right hκ4' hb, mul_nonneg hκ4.le hc'0]
  have hexp1 : Real.exp (-κ4 * (b + c')) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg hκ4.le (add_nonneg hb hc'0)]
  obtain ⟨Wb, hWbdef⟩ : ∃ Wb : ℝ, Wb = Bp * Bq * ak * al * (c' - c) := ⟨_, rfl⟩
  have hWb : 0 ≤ Wb := by rw [hWbdef]; exact mul_nonneg (by positivity) hΔ0.le
  -- the Gaussian data of the six node families, at every level
  have hFpk : ∀ ν, p_wj5_Fam (Set.Ioc c c') ν (p_wj5_g (Rp sd b hb) c c' Gm p (modeVec m k) ν)
      (K1 * Bp ^ 2 * ak ^ 2 * (c' - c)) := by
    intro ν
    obtain ⟨h1, h2, h3, -, -⟩ := hfamp b hb Gm hG1 hG0 hGc p Bp hp hpB c c' hc hcc hc' k ν
    refine p_wj5_fam_of c c' hcc ν _ (K1p * Bp ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1)))) _ ?_ h1 h2 h3
    rw [hak2]; gcongr
  have hFsk : ∀ ν, p_wj5_Fam (Set.Ioc c c') ν (p_wj5_g (Rs sd b hb) c c' Gm p (modeVec m k) ν)
      (K1 * Bp ^ 2 * ak ^ 2 * (c' - c)) := by
    intro ν
    obtain ⟨h1, h2, h3, -, -⟩ := hfams b hb Gm hG1 hG0 hGc p Bp hp hpB c c' hc hcc hc' k ν
    refine p_wj5_fam_of c c' hcc ν _ (K1s * Bp ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1)))) _ ?_ h1 h2 h3
    rw [hak2]; gcongr
  have hFWk : ∀ ν, p_wj5_Fam (Set.Ioc c c') ν (p_wj5_gW sd b hb c c' Gm p (modeVec m k) ν)
      (K1 * Bp ^ 2 * E ^ 2 * ak ^ 2 * (c' - c)) := by
    intro ν
    obtain ⟨h1, h2, h3, -, -⟩ := hfamW b hb Gm hG1 hG0 hGc p Bp hp hpB c c' hc hcc hc' k ν
    refine p_wj5_fam_of c c' hcc ν _
      (K1W * Bp ^ 2 * Real.exp (-2 * κ3 * b) * Lattice.jp k.1 ^ (-(2 * (m - 1)))) _ ?_ h1 h2 h3
    rw [hak2]; gcongr
    exact hexp κ3 hκ3'
  have hFpl : ∀ ν, p_wj5_Fam (Set.Ioc c c') ν (p_wj5_g (Rp sd b hb) c c' Gm q (modeVec m l) ν)
      (K1 * Bq ^ 2 * al ^ 2 * (c' - c)) := by
    intro ν
    obtain ⟨h1, h2, h3, -, -⟩ := hfamp b hb Gm hG1 hG0 hGc q Bq hq hqB c c' hc hcc hc' l ν
    refine p_wj5_fam_of c c' hcc ν _ (K1p * Bq ^ 2 * Lattice.jp l.1 ^ (-(2 * (m - 1)))) _ ?_ h1 h2 h3
    rw [hal2]; gcongr
  have hFsl : ∀ ν, p_wj5_Fam (Set.Ioc c c') ν (p_wj5_g (Rs sd b hb) c c' Gm q (modeVec m l) ν)
      (K1 * Bq ^ 2 * al ^ 2 * (c' - c)) := by
    intro ν
    obtain ⟨h1, h2, h3, -, -⟩ := hfams b hb Gm hG1 hG0 hGc q Bq hq hqB c c' hc hcc hc' l ν
    refine p_wj5_fam_of c c' hcc ν _ (K1s * Bq ^ 2 * Lattice.jp l.1 ^ (-(2 * (m - 1)))) _ ?_ h1 h2 h3
    rw [hal2]; gcongr
  have hFWl : ∀ ν, p_wj5_Fam (Set.Ioc c c') ν (p_wj5_gW sd b hb c c' Gm q (modeVec m l) ν)
      (K1 * Bq ^ 2 * E ^ 2 * al ^ 2 * (c' - c)) := by
    intro ν
    obtain ⟨h1, h2, h3, -, -⟩ := hfamW b hb Gm hG1 hG0 hGc q Bq hq hqB c c' hc hcc hc' l ν
    refine p_wj5_fam_of c c' hcc ν _
      (K1W * Bq ^ 2 * Real.exp (-2 * κ3 * b) * Lattice.jp l.1 ^ (-(2 * (m - 1)))) _ ?_ h1 h2 h3
    rw [hal2]; gcongr
    exact hexp κ3 hκ3'
  -- the node-family maps of the two regimes
  choose Φp hΦp using fun ν => HRS.MC.Sec7.S7PIDT.S7PIDT_Phi (Rp sd b hb) m hm T hT c c' hc hlt hc' ν
  choose Φs hΦs using fun ν => HRS.MC.Sec7.S7PIDT.S7PIDT_Phi (Rs sd b hb) m hm T hT c c' hc hlt hc' ν
  have hP4 := hpoly b hb c c' hc hlt hc'
  have hmix : ∀ (ν : ℕ) (v v' : ℕ → NegSobolev d m),
      polyPathMix (Rp sd b hb).D (Rs sd b hb).D (Rp sd b hb).ρ (Rs sd b hb).ρ m T c c' ν v v' =
        Φp ν (fun i => v i.1) - Φs ν (fun i => v' i.1) := by
    intro ν v v'
    unfold polyPathMix
    rw [hΦp, hΦs]
  have hΦs0 : ∀ ν, Φs ν (fun _ => (0 : NegSobolev d m)) = 0 := fun ν => map_zero (Φs ν)
  have hΦp0 : ∀ ν, Φp ν (fun _ => (0 : NegSobolev d m)) = 0 := fun ν => map_zero (Φp ν)
  have hinc4 : ∀ (ν : ℕ) (v v' : ℕ → NegSobolev d m) (B : ℝ),
      (∀ k < 2 ^ (ν + 1), ‖(v (k + 1) - v' (k + 1)) - (v k - v' k)‖ ≤ B) →
      ‖polyPathMix (Rp sd b hb).D (Rs sd b hb).D (Rp sd b hb).ρ (Rs sd b hb).ρ m T c c' (ν + 1) v v' -
        polyPathMix (Rp sd b hb).D (Rs sd b hb).D (Rp sd b hb).ρ (Rs sd b hb).ρ m T c c' ν
          (fun i => v (2 * i)) (fun i => v' (2 * i))‖ ≤ B := by
    intro ν v v' B hB
    refine (hP4 ν v v' (∑ i ∈ Finset.range (2 ^ ν + 1), ‖v i - v' i‖)
      (∑ i ∈ Finset.range (2 ^ ν + 1), ‖v' i‖) (fun i hi => ?_) (fun i hi => ?_)).2 B hB
    · exact Finset.single_le_sum (f := fun i => ‖v i - v' i‖) (fun j _ => norm_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    · exact Finset.single_le_sum (f := fun i => ‖v' i‖) (fun j _ => norm_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  -- bounds of the node-family maps (from P4)
  have bP : ∀ (ν : ℕ) (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ i ≤ 2 ^ ν, ‖v i‖ ≤ s) →
      ‖p_wj5_Psi emb (Φp ν) (fun i => v i.1)‖ ≤ C1 * s := by
    intro ν v s hv
    have h := (hP4 ν (fun i => emb (v i)) (fun _ => 0) s 0
      (fun i hi => by simpa using (hemb _).trans (hv i hi)) (fun i hi => by simp)).1
    rw [hmix, hΦs0, sub_zero] at h
    rw [p_wj5_Psi_apply]
    simpa using h
  have bS : ∀ (ν : ℕ) (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ i ≤ 2 ^ ν, ‖v i‖ ≤ s) →
      ‖p_wj5_Psi emb (Φs ν) (fun i => v i.1)‖ ≤ C0 * s := by
    intro ν v s hv
    have hs0 : 0 ≤ s := (norm_nonneg _).trans (hv 0 (Nat.zero_le _))
    have h := (hP4 ν (fun _ => 0) (fun i => emb (v i)) s s
      (fun i hi => by simpa using (hemb _).trans (hv i hi))
      (fun i hi => (hemb _).trans (hv i hi))).1
    rw [hmix, hΦp0, zero_sub, norm_neg] at h
    rw [p_wj5_Psi_apply, hC0def]
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_right hexp1 (mul_nonneg hCw hs0)
    nlinarith [mul_nonneg hCw hs0]
  have bA : ∀ (ν : ℕ) (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ i ≤ 2 ^ ν, ‖v i‖ ≤ s) →
      ‖(p_wj5_Psi emb (Φp ν) - p_wj5_Psi emb (Φs ν)) (fun i => v i.1)‖ ≤ (Cw * E) * s := by
    intro ν v s hv
    have hs0 : 0 ≤ s := (norm_nonneg _).trans (hv 0 (Nat.zero_le _))
    have h := (hP4 ν (fun i => emb (v i)) (fun i => emb (v i)) 0 s
      (fun i hi => by simp) (fun i hi => (hemb _).trans (hv i hi))).1
    rw [hmix] at h
    rw [sub_apply, p_wj5_Psi_apply, p_wj5_Psi_apply]
    refine (by simpa using h : _ ≤ C1 * 0 + Cw * Real.exp (-κ4 * (b + c')) * s).trans ?_
    have := mul_le_mul_of_nonneg_right hexp4 (mul_nonneg hCw hs0)
    nlinarith [mul_nonneg hCw hs0]
  have dP : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ k < 2 ^ (n + 1), ‖v (k + 1) - v k‖ ≤ s) →
      ‖p_wj5_Psi emb (Φp (n + 1)) (fun i => v i.1) - p_wj5_Psi emb (Φp n) (fun j => v (2 * j.1))‖ ≤
        1 * s := by
    intro v s hv
    have h := hinc4 n (fun i => emb (v i)) (fun _ => 0) s (fun k hk => by
      have := (hemb (v (k + 1) - v k)).trans (hv k hk)
      rw [map_sub] at this
      simpa using this)
    rw [hmix, hmix, hΦs0, hΦs0] at h
    simp only [p_wj5_Psi_apply]
    simpa using h
  have dS : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ k < 2 ^ (n + 1), ‖v (k + 1) - v k‖ ≤ s) →
      ‖p_wj5_Psi emb (Φs (n + 1)) (fun i => v i.1) - p_wj5_Psi emb (Φs n) (fun j => v (2 * j.1))‖ ≤
        1 * s := by
    intro v s hv
    have h := hinc4 n (fun _ => 0) (fun i => emb (v i)) s (fun k hk => by
      have := (hemb (v (k + 1) - v k)).trans (hv k hk)
      rw [map_sub, ← norm_neg] at this
      refine le_of_eq_of_le ?_ this
      congr 1
      simp only [zero_sub]
      abel)
    rw [hmix, hmix, hΦp0, hΦp0] at h
    simp only [p_wj5_Psi_apply]
    rw [one_mul, ← norm_neg]
    refine le_trans (le_of_eq ?_) h
    congr 1
    abel
  have dA : ∀ (v : ℕ → EuclideanSpace ℝ (Fin r)) (s : ℝ), (∀ k < 2 ^ (n + 1), ‖v (k + 1) - v k‖ ≤ s) →
      ‖(p_wj5_Psi emb (Φp (n + 1)) - p_wj5_Psi emb (Φs (n + 1))) (fun i => v i.1) -
        (p_wj5_Psi emb (Φp n) - p_wj5_Psi emb (Φs n)) (fun j => v (2 * j.1))‖ ≤ 0 * s := by
    intro v s hv
    have h := hinc4 n (fun i => emb (v i)) (fun i => emb (v i)) 0 (fun k hk => by simp)
    rw [hmix, hmix] at h
    simp only [sub_apply, p_wj5_Psi_apply]
    simpa using h
  -- relations between the node families
  have hdp : ∀ (R : Regime d) (pp : ℝ → ℝ) (e : NegSobolev d m) (j : ℕ) (u : ℝ),
      p_wj5_g R c c' Gm pp e n j u = p_wj5_g R c c' Gm pp e (n + 1) (2 * j) u := fun R pp e j u =>
    congrArg Gm (p_wj5_dbl R.D R.ρ c c' n pp e u j)
  have hdW : ∀ (pp : ℝ → ℝ) (e : NegSobolev d m) (j : ℕ) (u : ℝ),
      p_wj5_gW sd b hb c c' Gm pp e n j u = p_wj5_gW sd b hb c c' Gm pp e (n + 1) (2 * j) u := by
    intro pp e j u
    unfold p_wj5_gW kernelNodesW
    rw [p_wj5_dbl (Rp sd b hb).D (Rp sd b hb).ρ c c' n pp e u j,
      p_wj5_dbl (Rs sd b hb).D (Rs sd b hb).ρ c c' n pp e u j]
  have hlin : ∀ (pp : ℝ → ℝ) (e : NegSobolev d m) (ν i : ℕ) (u : ℝ),
      emb (p_wj5_g (Rp sd b hb) c c' Gm pp e ν i u) =
        emb (p_wj5_gW sd b hb c c' Gm pp e ν i u) + emb (p_wj5_g (Rs sd b hb) c c' Gm pp e ν i u) := by
    intro pp e ν i u
    unfold p_wj5_g p_wj5_gW
    rw [hembG, hembG, hembG]
    unfold kernelNodesW
    rw [p_wj5_trunc_sub]
    abel
  -- `nucK` as an integral over the coordinate families
  have PRp := HRS.MC.Sec7.S7PIDT.S7PIDT_nucg (Rp sd b hb) m hm T hT c c' hc hlt hc' F emb Gm hembG hGc p q
    (modeVec m k) (modeVec m l) (max (Bp * (Cbp * ‖modeVec m k‖)) (Bq * (Cbp * ‖modeVec m l‖)))
    (fun ν i hi => (hfamp b hb Gm hG1 hG0 hGc p Bp hp hpB c c' hc hcc hc' k ν).2.2.2.1 i hi)
    (fun ν i hi => (hfamp b hb Gm hG1 hG0 hGc q Bq hq hqB c c' hc hcc hc' l ν).2.2.2.1 i hi)
    (fun ν i hi u hu => ((hfamp b hb Gm hG1 hG0 hGc p Bp hp hpB c c' hc hcc hc' k ν).2.2.2.2 i hi u hu).trans
      (le_max_left _ _))
    (fun ν i hi u hu => ((hfamp b hb Gm hG1 hG0 hGc q Bq hq hqB c c' hc hcc hc' l ν).2.2.2.2 i hi u hu).trans
      (le_max_right _ _))
  have PRs := HRS.MC.Sec7.S7PIDT.S7PIDT_nucg (Rs sd b hb) m hm T hT c c' hc hlt hc' F emb Gm hembG hGc p q
    (modeVec m k) (modeVec m l) (max (Bp * (Cbs * ‖modeVec m k‖)) (Bq * (Cbs * ‖modeVec m l‖)))
    (fun ν i hi => (hfams b hb Gm hG1 hG0 hGc p Bp hp hpB c c' hc hcc hc' k ν).2.2.2.1 i hi)
    (fun ν i hi => (hfams b hb Gm hG1 hG0 hGc q Bq hq hqB c c' hc hcc hc' l ν).2.2.2.1 i hi)
    (fun ν i hi u hu => ((hfams b hb Gm hG1 hG0 hGc p Bp hp hpB c c' hc hcc hc' k ν).2.2.2.2 i hi u hu).trans
      (le_max_left _ _))
    (fun ν i hi u hu => ((hfams b hb Gm hG1 hG0 hGc q Bq hq hqB c c' hc hcc hc' l ν).2.2.2.2 i hi u hu).trans
      (le_max_right _ _))
  have nuc_p : ∀ ν, nucK (Rp sd b hb) m T c c' ν p q k l (truncF m F) M =
      ∫ u in Set.Ioc c c', M ![p_wj5_Psi emb (Φp ν) (fun i => p_wj5_g (Rp sd b hb) c c' Gm p (modeVec m k) ν i.1 u),
        p_wj5_Psi emb (Φp ν) (fun i => p_wj5_g (Rp sd b hb) c c' Gm q (modeVec m l) ν i.1 u)] :=
    fun ν => PRp ν ν (fun i => i) (fun j hj => hj) (Φp ν) (hΦp ν) M
  have nuc_s : ∀ ν, nucK (Rs sd b hb) m T c c' ν p q k l (truncF m F) M =
      ∫ u in Set.Ioc c c', M ![p_wj5_Psi emb (Φs ν) (fun i => p_wj5_g (Rs sd b hb) c c' Gm p (modeVec m k) ν i.1 u),
        p_wj5_Psi emb (Φs ν) (fun i => p_wj5_g (Rs sd b hb) c c' Gm q (modeVec m l) ν i.1 u)] :=
    fun ν => PRs ν ν (fun i => i) (fun j hj => hj) (Φs ν) (hΦs ν) M
  -- the four-term decomposition
  have F4 : ∀ ν, _ := fun ν => p_wj5_four emb ν (Set.Ioc c c')
    (p_wj5_g (Rp sd b hb) c c' Gm p (modeVec m k) ν) (p_wj5_g (Rs sd b hb) c c' Gm p (modeVec m k) ν)
    (p_wj5_gW sd b hb c c' Gm p (modeVec m k) ν)
    (p_wj5_g (Rp sd b hb) c c' Gm q (modeVec m l) ν) (p_wj5_g (Rs sd b hb) c c' Gm q (modeVec m l) ν)
    (p_wj5_gW sd b hb c c' Gm q (modeVec m l) ν)
    (hFpk ν) (hFsk ν) (hFWk ν) (hFpl ν) (hFsl ν) (hFWl ν) (Φp ν) (Φs ν)
    (fun i u => hlin p (modeVec m k) ν i u) (fun i u => hlin q (modeVec m l) ν i u) M
  -- the four pair bounds
  have hk1 : 0 ≤ K1 * Bp ^ 2 * ak ^ 2 * (c' - c) := by positivity
  have hkW1 : 0 ≤ K1 * Bp ^ 2 * E ^ 2 * ak ^ 2 * (c' - c) := by positivity
  have hl1 : 0 ≤ K1 * Bq ^ 2 * al ^ 2 * (c' - c) := by positivity
  have hlW1 : 0 ≤ K1 * Bq ^ 2 * E ^ 2 * al ^ 2 * (c' - c) := by positivity
  have hCwE : 0 ≤ Cw * E := by positivity
  have pr1 := p_wj5_pair n (Set.Ioc c c')
    (p_wj5_gW sd b hb c c' Gm p (modeVec m k) n) (p_wj5_gW sd b hb c c' Gm p (modeVec m k) (n + 1))
    (p_wj5_g (Rp sd b hb) c c' Gm q (modeVec m l) n) (p_wj5_g (Rp sd b hb) c c' Gm q (modeVec m l) (n + 1))
    hkW1 hl1 (hFWk n) (hFWk (n + 1)) (hFpl n) (hFpl (n + 1))
    (fun j u => hdW p (modeVec m k) j u) (fun j u => hdp (Rp sd b hb) q (modeVec m l) j u)
    (p_wj5_Psi emb (Φp n)) (p_wj5_Psi emb (Φp n)) (p_wj5_Psi emb (Φp (n + 1))) (p_wj5_Psi emb (Φp (n + 1)))
    C1 C1 1 1 hC10 hC10 zero_le_one zero_le_one (bP n) (bP n) (bP (n + 1)) dP dP
    (K1 * E * Wb) (by positivity) (by rw [hWbdef]; ring) M
  have pr2 := p_wj5_pair n (Set.Ioc c c')
    (p_wj5_g (Rs sd b hb) c c' Gm p (modeVec m k) n) (p_wj5_g (Rs sd b hb) c c' Gm p (modeVec m k) (n + 1))
    (p_wj5_g (Rp sd b hb) c c' Gm q (modeVec m l) n) (p_wj5_g (Rp sd b hb) c c' Gm q (modeVec m l) (n + 1))
    hk1 hl1 (hFsk n) (hFsk (n + 1)) (hFpl n) (hFpl (n + 1))
    (fun j u => hdp (Rs sd b hb) p (modeVec m k) j u) (fun j u => hdp (Rp sd b hb) q (modeVec m l) j u)
    (p_wj5_Psi emb (Φp n) - p_wj5_Psi emb (Φs n)) (p_wj5_Psi emb (Φp n))
    (p_wj5_Psi emb (Φp (n + 1)) - p_wj5_Psi emb (Φs (n + 1))) (p_wj5_Psi emb (Φp (n + 1)))
    (Cw * E) C1 0 1 hCwE hC10 le_rfl zero_le_one (bA n) (bP n) (bP (n + 1)) dA dP
    (K1 * Wb) (by positivity) (by rw [hWbdef]; ring) M
  have pr3 := p_wj5_pair n (Set.Ioc c c')
    (p_wj5_g (Rs sd b hb) c c' Gm p (modeVec m k) n) (p_wj5_g (Rs sd b hb) c c' Gm p (modeVec m k) (n + 1))
    (p_wj5_gW sd b hb c c' Gm q (modeVec m l) n) (p_wj5_gW sd b hb c c' Gm q (modeVec m l) (n + 1))
    hk1 hlW1 (hFsk n) (hFsk (n + 1)) (hFWl n) (hFWl (n + 1))
    (fun j u => hdp (Rs sd b hb) p (modeVec m k) j u) (fun j u => hdW q (modeVec m l) j u)
    (p_wj5_Psi emb (Φs n)) (p_wj5_Psi emb (Φp n)) (p_wj5_Psi emb (Φs (n + 1))) (p_wj5_Psi emb (Φp (n + 1)))
    C0 C1 1 1 hC00 hC10 zero_le_one zero_le_one (bS n) (bP n) (bP (n + 1)) dS dP
    (K1 * E * Wb) (by positivity) (by rw [hWbdef]; ring) M
  have pr4 := p_wj5_pair n (Set.Ioc c c')
    (p_wj5_g (Rs sd b hb) c c' Gm p (modeVec m k) n) (p_wj5_g (Rs sd b hb) c c' Gm p (modeVec m k) (n + 1))
    (p_wj5_g (Rs sd b hb) c c' Gm q (modeVec m l) n) (p_wj5_g (Rs sd b hb) c c' Gm q (modeVec m l) (n + 1))
    hk1 hl1 (hFsk n) (hFsk (n + 1)) (hFsl n) (hFsl (n + 1))
    (fun j u => hdp (Rs sd b hb) p (modeVec m k) j u) (fun j u => hdp (Rs sd b hb) q (modeVec m l) j u)
    (p_wj5_Psi emb (Φs n)) (p_wj5_Psi emb (Φp n) - p_wj5_Psi emb (Φs n))
    (p_wj5_Psi emb (Φs (n + 1))) (p_wj5_Psi emb (Φp (n + 1)) - p_wj5_Psi emb (Φs (n + 1)))
    C0 (Cw * E) 1 0 hC00 hCwE zero_le_one le_rfl (bS n) (bA n) (bA (n + 1)) dS dA
    (K1 * Wb) (by positivity) (by rw [hWbdef]; ring) M
  -- assembly
  have hZ : 0 ≤ ‖M‖ * K1 * E * Wb := by positivity
  have hKc1 : 162 * (C1 ^ 2 + C1 * Cw + C0 * C1 + C0 * Cw) ≤ Kc := by
    rw [hKcdef]; have : 0 ≤ 18 * (3 * C1 + 2 * Cw + C0) := by positivity
    linarith
  have hKc2 : 18 * (3 * C1 + 2 * Cw + C0) ≤ Kc := by
    rw [hKcdef]; have : 0 ≤ 162 * (C1 ^ 2 + C1 * Cw + C0 * C1 + C0 * Cw) := by positivity
    linarith
  have htgt : ‖M‖ * (K1 * Kc * Bp * Bq * E * ak * al * (c' - c)) = (‖M‖ * K1 * E * Wb) * Kc := by
    rw [hWbdef]; ring
  have hθ0 : 0 < (2 : ℝ) ^ (-(n : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  rw [← hEdef, ← hakdef, ← haldef]
  refine ⟨?_, ?_⟩
  · rw [nuc_p n, nuc_s n, F4 n]
    refine (p_wj5_abs4' _ _ _ _).trans ?_
    have a1 := pr1.1
    have a2 := pr2.1
    have a3 := pr3.1
    have a4 := pr4.1
    have := mul_le_mul_of_nonneg_left hKc1 hZ
    have e : ‖M‖ * (K1 * Kc * Bp * Bq * E * ak * al * (c' - c)) = (‖M‖ * K1 * E * Wb) * Kc := htgt
    calc _ ≤ 162 * (‖M‖ * C1 * C1 * (K1 * E * Wb)) + 162 * (‖M‖ * (Cw * E) * C1 * (K1 * Wb)) +
        (162 * (‖M‖ * C0 * C1 * (K1 * E * Wb)) + 162 * (‖M‖ * C0 * (Cw * E) * (K1 * Wb))) := by linarith
      _ = (‖M‖ * K1 * E * Wb) * (162 * (C1 ^ 2 + C1 * Cw + C0 * C1 + C0 * Cw)) := by ring
      _ ≤ (‖M‖ * K1 * E * Wb) * Kc := this
      _ = _ := htgt.symm
  · rw [nuc_p (n + 1), nuc_s (n + 1), nuc_p n, nuc_s n, F4 (n + 1), F4 n]
    refine (p_wj5_abs4 _ _ _ _ _ _ _ _).trans ?_
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (2 : ℝ) ^ (-(n : ℝ) / 4) := ⟨_, rfl⟩
    rw [← hθ] at hθ0 ⊢
    have a1 := pr1.2
    have a2 := pr2.2
    have a3 := pr3.2
    have a4 := pr4.2
    rw [← hθ] at a1 a2 a3 a4
    have := mul_le_mul_of_nonneg_left hKc2 (mul_nonneg hZ hθ0.le)
    calc _ ≤ ‖M‖ * (18 * (K1 * E * Wb) * θ * (1 * C1 + 1 * C1)) +
          ‖M‖ * (18 * (K1 * Wb) * θ * (0 * C1 + 1 * (Cw * E))) +
          (‖M‖ * (18 * (K1 * E * Wb) * θ * (1 * C1 + 1 * C0)) +
           ‖M‖ * (18 * (K1 * Wb) * θ * (1 * (Cw * E) + 0 * C0))) := by linarith
      _ = ((‖M‖ * K1 * E * Wb) * θ) * (18 * (3 * C1 + 2 * Cw + C0)) := by ring
      _ ≤ ((‖M‖ * K1 * E * Wb) * θ) * Kc := this
      _ = _ := by rw [hWbdef]; ring

end Packets

end HRS.MC.WinJ

end
