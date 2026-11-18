import HRS.MC.CepN4
import HRS.MC.CepK1
import HRS.MC.CepC0
import HRS.Stochastic.Particle

/-!
# Packet CEPN6 (aux 3): circle distance, the good set `U`, and bounded drifts

* `n6_dc`: distance to the nearest integer; `n6_Uo`, `n6_Kc`: the open "good" set and its closed version
  (gap `< gcap`, every relevant pair separated by `> r2`, resp. `≤`, `≥`).
* `n6_drift_bounds`: the drift of a particle which is `r`-separated from every other particle, and the sum of
  the drifts of a pair `p, q` which are `r`-separated from all other particles, are bounded.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators

noncomputable section

namespace HRS.MC.CepN6

open HRS HRS.MC.CepN4 Real

variable {N : ℕ}

/-- Distance to the nearest integer. -/
def n6_dc (x : ℝ) : ℝ := Metric.infDist x (Set.range ((↑) : ℤ → ℝ))

lemma n6_dc_cont : Continuous n6_dc := Metric.continuous_infDist_pt _

lemma n6_dc_le (x : ℝ) (m : ℤ) : n6_dc x ≤ |x - m| := by
  have := Metric.infDist_le_dist_of_mem (x := x)
    (show ((m : ℤ) : ℝ) ∈ Set.range ((↑) : ℤ → ℝ) from ⟨m, rfl⟩)
  rwa [Real.dist_eq] at this

lemma n6_le_dc {r x : ℝ} (h : ∀ m : ℤ, r ≤ |x - m|) : r ≤ n6_dc x := by
  refine (Metric.le_infDist (s := Set.range ((↑) : ℤ → ℝ)) ⟨0, ⟨0, by simp⟩⟩).2 ?_
  rintro _ ⟨m, rfl⟩
  rw [Real.dist_eq]
  exact h m

lemma n6_dc_nonneg (x : ℝ) : 0 ≤ n6_dc x := Metric.infDist_nonneg

lemma n6_dc_neg (x : ℝ) : n6_dc (-x) = n6_dc x := by
  have h1 : ∀ y : ℝ, n6_dc (-y) ≤ n6_dc y := by
    intro y
    refine n6_le_dc fun m => ?_
    have := n6_dc_le (-y) (-m)
    calc n6_dc (-y) ≤ |-y - ((-m : ℤ) : ℝ)| := this
      _ = |y - m| := by rw [← abs_neg]; congr 1; push_cast; ring
  exact le_antisymm (h1 x) (by simpa using h1 (-x))

lemma n6_dc_lip (x y : ℝ) : n6_dc x ≤ n6_dc y + |x - y| := by
  have := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := Set.range ((↑) : ℤ → ℝ))
  rwa [Real.dist_eq] at this

/-- Two particles `k, l` interact "regularly": distinct and not both in the pair `{p0, p1}`. -/
def n6_rel (p0 p1 k l : Fin N) : Prop := k ≠ l ∧ ¬ ((k = p0 ∨ k = p1) ∧ (l = p0 ∨ l = p1))

/-- The open good set. -/
def n6_Uo (p0 p1 : Fin N) (r2 gcap : ℝ) : Set (Fin N → Euc 1) :=
  {y | y p1 0 - y p0 0 < gcap ∧ ∀ k l, n6_rel p0 p1 k l → r2 < n6_dc (y k 0 - y l 0)}

/-- Its closed version. -/
def n6_Kc (p0 p1 : Fin N) (r2 gcap : ℝ) : Set (Fin N → Euc 1) :=
  {y | y p1 0 - y p0 0 ≤ gcap ∧ ∀ k l, n6_rel p0 p1 k l → r2 ≤ n6_dc (y k 0 - y l 0)}

lemma n6_coord_cont (i : Fin N) : Continuous fun y : Fin N → Euc 1 => y i 0 :=
  (EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_apply i)

lemma n6_isOpen_Uo (p0 p1 : Fin N) (r2 gcap : ℝ) : IsOpen (n6_Uo p0 p1 r2 gcap) := by
  have h1 : IsOpen {y : Fin N → Euc 1 | y p1 0 - y p0 0 < gcap} :=
    isOpen_lt ((n6_coord_cont p1).sub (n6_coord_cont p0)) continuous_const
  have h2 : IsOpen {y : Fin N → Euc 1 | ∀ k l, n6_rel p0 p1 k l → r2 < n6_dc (y k 0 - y l 0)} := by
    have : {y : Fin N → Euc 1 | ∀ k l, n6_rel p0 p1 k l → r2 < n6_dc (y k 0 - y l 0)} =
        ⋂ k, ⋂ l, {y | n6_rel p0 p1 k l → r2 < n6_dc (y k 0 - y l 0)} := by
      ext y; simp
    rw [this]
    refine isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l => ?_
    by_cases h : n6_rel p0 p1 k l
    · simp only [h, true_imp_iff]
      exact isOpen_lt continuous_const
        (n6_dc_cont.comp ((n6_coord_cont k).sub (n6_coord_cont l)))
    · simp [h]
  exact h1.inter h2

lemma n6_isClosed_Kc (p0 p1 : Fin N) (r2 gcap : ℝ) : IsClosed (n6_Kc p0 p1 r2 gcap) := by
  have h1 : IsClosed {y : Fin N → Euc 1 | y p1 0 - y p0 0 ≤ gcap} :=
    isClosed_le ((n6_coord_cont p1).sub (n6_coord_cont p0)) continuous_const
  have h2 : IsClosed {y : Fin N → Euc 1 | ∀ k l, n6_rel p0 p1 k l → r2 ≤ n6_dc (y k 0 - y l 0)} := by
    have : {y : Fin N → Euc 1 | ∀ k l, n6_rel p0 p1 k l → r2 ≤ n6_dc (y k 0 - y l 0)} =
        ⋂ k, ⋂ l, {y | n6_rel p0 p1 k l → r2 ≤ n6_dc (y k 0 - y l 0)} := by
      ext y; simp
    rw [this]
    refine isClosed_iInter fun k => isClosed_iInter fun l => ?_
    by_cases h : n6_rel p0 p1 k l
    · simp only [h, true_imp_iff]
      exact isClosed_le continuous_const
        (n6_dc_cont.comp ((n6_coord_cont k).sub (n6_coord_cont l)))
    · simp [h]
  exact h1.inter h2

lemma n6_Uo_subset_Kc (p0 p1 : Fin N) (r2 gcap : ℝ) : n6_Uo p0 p1 r2 gcap ⊆ n6_Kc p0 p1 r2 gcap :=
  fun _ hy => ⟨hy.1.le, fun k l h => (hy.2 k l h).le⟩

lemma n6_closure_Uo_subset (p0 p1 : Fin N) (r2 gcap : ℝ) :
    closure (n6_Uo p0 p1 r2 gcap) ⊆ n6_Kc p0 p1 r2 gcap :=
  closure_minimal (n6_Uo_subset_Kc p0 p1 r2 gcap) (n6_isClosed_Kc p0 p1 r2 gcap)

/-! ### Bounded drifts -/

theorem n6_drift_bounds {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : HRS.MC.CepC0.cep_IsC11 D.V)
    {r : ℝ} (hr : 0 < r) (hN : 0 < N) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧
      (∀ y ∈ liftedFree 1 N, ∀ k : Fin N, (∀ j, j ≠ k → r ≤ n6_dc (y k 0 - y j 0)) →
        |(liftedDrift D y k) 0| ≤ Bd) ∧
      (∀ y ∈ liftedFree 1 N, ∀ p q : Fin N, p ≠ q →
        (∀ j, j ≠ p → j ≠ q → r ≤ n6_dc (y p 0 - y j 0) ∧ r ≤ n6_dc (y q 0 - y j 0)) →
        |(liftedDrift D y p) 0 + (liftedDrift D y q) 0| ≤ Bd) := by
  obtain ⟨ρ, hρsm, hρper, hρodd, hρK⟩ := HRS.MC.CepK1.cep_K1_force_decomp_proof
  obtain ⟨Bρ, hBρ0, hBρ⟩ := cepn4_periodic_bound hρsm.continuous hρper
  obtain ⟨BV, hBV0, hBV⟩ := cepn4_gV_bound hV.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set hb : ℝ := a * (Real.pi / (2 * r) + Bρ) with hhb
  have hb0 : 0 ≤ hb := by rw [hhb]; positivity
  have hhbd : ∀ (u : ℝ), n6_dc u ≥ r → |cepn4_h a ρ u| ≤ hb := fun u hu =>
    cepn4_h_bound ha hBρ hr (fun m => le_trans hu (n6_dc_le u m))
  refine ⟨2 * (hb + BV), by positivity, ?_, ?_⟩
  · intro y hy k hk
    rw [cepn4_drift_comp hs hM hρK hy k]
    unfold cepn4_bdrift
    have hterm : ∀ j ∈ Finset.univ.erase k, |cepn4_h a ρ (y k 0 - y j 0)| ≤ hb := fun j hj =>
      hhbd _ (hk j (Finset.ne_of_mem_erase hj))
    have hsum : |∑ j ∈ Finset.univ.erase k, cepn4_h a ρ (y k 0 - y j 0)| ≤ N * hb := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ hb hterm) ?_
      rw [nsmul_eq_mul]
      have hcard : ((Finset.univ.erase k).card : ℝ) ≤ N := by
        have : (Finset.univ.erase k).card ≤ N := by
          calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.subset_univ _)
            _ = N := by simp
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hcard hb0
    have h1 : |1 / (N : ℝ) * ∑ j ∈ Finset.univ.erase k, cepn4_h a ρ (y k 0 - y j 0)| ≤ hb := by
      rw [abs_mul, abs_of_pos (by positivity)]
      calc 1 / (N : ℝ) * _ ≤ 1 / (N : ℝ) * (N * hb) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = hb := by field_simp
    calc _ ≤ |1 / (N : ℝ) * ∑ j ∈ Finset.univ.erase k, cepn4_h a ρ (y k 0 - y j 0)| +
          |cepn4_gV D.V (y k)| := abs_sub _ _
      _ ≤ hb + BV := add_le_add h1 (hBV _)
      _ ≤ _ := by linarith
  · intro y hy p q hpq hsep
    rw [cepn4_drift_comp hs hM hρK hy p, cepn4_drift_comp hs hM hρK hy q]
    unfold cepn4_bdrift
    have hp : ∑ j ∈ Finset.univ.erase p, cepn4_h a ρ (y p 0 - y j 0) =
        cepn4_h a ρ (y p 0 - y q 0) +
          ∑ j ∈ (Finset.univ.erase p).erase q, cepn4_h a ρ (y p 0 - y j 0) :=
      (Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hpq.symm, Finset.mem_univ _⟩)).symm
    have hq : ∑ j ∈ Finset.univ.erase q, cepn4_h a ρ (y q 0 - y j 0) =
        cepn4_h a ρ (y q 0 - y p 0) +
          ∑ j ∈ (Finset.univ.erase q).erase p, cepn4_h a ρ (y q 0 - y j 0) :=
      (Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hpq, Finset.mem_univ _⟩)).symm
    have hneg : cepn4_h a ρ (y q 0 - y p 0) = - cepn4_h a ρ (y p 0 - y q 0) := by
      rw [← cepn4_h_neg a ρ hρodd]; congr 1; ring
    have hcomm : (Finset.univ.erase q).erase p = (Finset.univ.erase p).erase q :=
      Finset.erase_right_comm
    rw [hp, hq, hneg, hcomm]
    have hterm : ∀ j ∈ (Finset.univ.erase p).erase q,
        |cepn4_h a ρ (y p 0 - y j 0) + cepn4_h a ρ (y q 0 - y j 0)| ≤ 2 * hb := by
      intro j hj
      obtain ⟨hjq, hj'⟩ := Finset.mem_erase.1 hj
      have hjp := Finset.ne_of_mem_erase hj'
      obtain ⟨s1, s2⟩ := hsep j hjp hjq
      calc _ ≤ |cepn4_h a ρ (y p 0 - y j 0)| + |cepn4_h a ρ (y q 0 - y j 0)| := abs_add_le _ _
        _ ≤ 2 * hb := by linarith [hhbd _ s1, hhbd _ s2]
    have hsum : |∑ j ∈ (Finset.univ.erase p).erase q,
        (cepn4_h a ρ (y p 0 - y j 0) + cepn4_h a ρ (y q 0 - y j 0))| ≤ N * (2 * hb) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * hb) hterm) ?_
      rw [nsmul_eq_mul]
      have hcard : (((Finset.univ.erase p).erase q).card : ℝ) ≤ N := by
        have : ((Finset.univ.erase p).erase q).card ≤ N := by
          calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.subset_univ _)
            _ = N := by simp
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    have h1 : |1 / (N : ℝ) * ∑ j ∈ (Finset.univ.erase p).erase q,
        (cepn4_h a ρ (y p 0 - y j 0) + cepn4_h a ρ (y q 0 - y j 0))| ≤ 2 * hb := by
      rw [abs_mul, abs_of_pos (by positivity)]
      calc 1 / (N : ℝ) * _ ≤ 1 / (N : ℝ) * (N * (2 * hb)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 2 * hb := by field_simp
    have heq : (1 / (N : ℝ) * (cepn4_h a ρ (y p 0 - y q 0) +
          ∑ j ∈ (Finset.univ.erase p).erase q, cepn4_h a ρ (y p 0 - y j 0)) - cepn4_gV D.V (y p)) +
        (1 / (N : ℝ) * (-cepn4_h a ρ (y p 0 - y q 0) +
          ∑ j ∈ (Finset.univ.erase p).erase q, cepn4_h a ρ (y q 0 - y j 0)) - cepn4_gV D.V (y q)) =
        1 / (N : ℝ) * ∑ j ∈ (Finset.univ.erase p).erase q,
          (cepn4_h a ρ (y p 0 - y j 0) + cepn4_h a ρ (y q 0 - y j 0)) -
          (cepn4_gV D.V (y p) + cepn4_gV D.V (y q)) := by
      rw [Finset.sum_add_distrib]; ring
    rw [heq]
    calc _ ≤ |1 / (N : ℝ) * ∑ j ∈ (Finset.univ.erase p).erase q,
          (cepn4_h a ρ (y p 0 - y j 0) + cepn4_h a ρ (y q 0 - y j 0))| +
          |cepn4_gV D.V (y p) + cepn4_gV D.V (y q)| := abs_sub _ _
      _ ≤ 2 * hb + 2 * BV := by
        refine add_le_add h1 ?_
        calc _ ≤ |cepn4_gV D.V (y p)| + |cepn4_gV D.V (y q)| := abs_add_le _ _
          _ ≤ 2 * BV := by linarith [hBV (y p), hBV (y q)]
      _ = _ := by ring

end HRS.MC.CepN6
