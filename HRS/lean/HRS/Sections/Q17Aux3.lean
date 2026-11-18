import HRS.Sections.Q17Aux2

/-!
# Q17 auxiliary 3: Remark 7.10 (`measure_projection`, relocated proof)

Relocated proof of `HRS.Sec7.measure_projection` (statement verbatim from `Sec7Fields.lean`).
The budget is the variation function `Wf x y = (eVariationOn F [x,y]).toReal`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Sec7

section Q17Measure

/-- Variation budget of a bounded-variation path. -/
def q17_Wf {E : Type*} [PseudoEMetricSpace E] (F : ℝ → E) (x y : ℝ) : ℝ :=
  (eVariationOn F (Set.Icc x y)).toReal

theorem q17_W_props {E : Type*} [NormedAddCommGroup E] (T : ℝ) (F : ℝ → E)
    (hF : BoundedVariationOn F (Set.Icc 0 T)) :
    (∀ x y, 0 ≤ x → x ≤ y → y ≤ T → ‖F y - F x‖ ≤ q17_Wf F x y) ∧
    (∀ x u y, 0 ≤ x → x ≤ u → u ≤ y → y ≤ T →
      q17_Wf F x u + q17_Wf F u y ≤ q17_Wf F x y) := by
  constructor
  · intro x y hx hxy hy
    have hfin : eVariationOn F (Set.Icc x y) ≠ ⊤ :=
      ne_top_of_le_ne_top hF (eVariationOn.mono F (Set.Icc_subset_Icc hx hy))
    have h1 : edist (F y) (F x) ≤ eVariationOn F (Set.Icc x y) := by
      rw [edist_comm]
      exact eVariationOn.edist_le F ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩
    rw [← dist_eq_norm, dist_edist]
    exact ENNReal.toReal_mono hfin h1
  · intro x u y hx hxu huy hy
    have hu0 : 0 ≤ u := le_trans hx hxu
    have huT : u ≤ T := le_trans huy hy
    have hadd := eVariationOn.Icc_add_Icc F (s := Set.Icc 0 T) hxu huy ⟨hu0, huT⟩
    have e1 : Set.Icc (0 : ℝ) T ∩ Set.Icc x u = Set.Icc x u :=
      Set.inter_eq_right.2 (Set.Icc_subset_Icc hx huT)
    have e2 : Set.Icc (0 : ℝ) T ∩ Set.Icc u y = Set.Icc u y :=
      Set.inter_eq_right.2 (Set.Icc_subset_Icc hu0 hy)
    have e3 : Set.Icc (0 : ℝ) T ∩ Set.Icc x y = Set.Icc x y :=
      Set.inter_eq_right.2 (Set.Icc_subset_Icc hx hy)
    rw [e1, e2, e3] at hadd
    have hfin1 : eVariationOn F (Set.Icc x u) ≠ ⊤ :=
      ne_top_of_le_ne_top hF (eVariationOn.mono F (Set.Icc_subset_Icc hx huT))
    have hfin2 : eVariationOn F (Set.Icc u y) ≠ ⊤ :=
      ne_top_of_le_ne_top hF (eVariationOn.mono F (Set.Icc_subset_Icc hu0 hy))
    unfold q17_Wf
    rw [← ENNReal.toReal_add hfin1 hfin2, hadd]

theorem q17_uf_strict (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N) :
    StrictMono (q17_uf T N) := by
  intro i j hij
  unfold q17_uf
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : (i.val : ℝ) < j.val := Nat.cast_lt.2 hij
  exact mul_lt_mul_of_pos_right h1 (div_pos hT hN')

/-- Convergence of the projected sums, one term at a time. -/
theorem q17_term_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Pj : ℕ → (E →L[ℝ] E)) (K : ℝ) (hK : ∀ L, ‖Pj L‖ ≤ K)
    (hconv : ∀ e, Tendsto (fun L => Pj L e) atTop (𝓝 e))
    (F : ℝ → E) (A : ℝ → (E →L[ℝ] ℝ)) (AL : ℕ → ℝ → (E →L[ℝ] ℝ)) (T : ℝ)
    (hAu : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ u ∈ Set.Icc (0 : ℝ) T, ‖AL L u - A u‖ ≤ ε)
    (τ a b : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun L => AL L τ (Pj L (F b - F a)) - A τ (F b - F a)) atTop (𝓝 0) := by
  have hn : Tendsto (fun L => ‖AL L τ - A τ‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨L0, hL0⟩ := hAu (ε / 2) (by positivity)
    refine ⟨L0, fun L hL => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_norm]
    linarith [hL0 L hL τ hτ]
  obtain ⟨v, hv⟩ : ∃ v : E, v = F b - F a := ⟨_, rfl⟩
  rw [← hv]
  have hX : Tendsto (fun L => Pj L v - v) atTop (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.2 (hconv v)
  have hnX : Tendsto (fun L => ‖Pj L v - v‖) atTop (𝓝 0) := by
    simpa using hX.norm
  have hg : Tendsto (fun L => ‖AL L τ - A τ‖ * (‖v‖ + ‖Pj L v - v‖) + ‖A τ‖ * ‖Pj L v - v‖)
      atTop (𝓝 0) := by
    have := (hn.mul ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖v‖) atTop (𝓝 ‖v‖)).add hnX)).add
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖A τ‖) atTop (𝓝 ‖A τ‖))).mul hnX)
    simpa using this
  have hid : ∀ L, AL L τ (Pj L v) - A τ v
      = (AL L τ - A τ) (v + (Pj L v - v)) + A τ (Pj L v - v) := by
    intro L
    simp only [ContinuousLinearMap.sub_apply, map_add, map_sub]
    abel
  refine squeeze_zero_norm (fun L => ?_) hg
  rw [hid L]
  calc ‖(AL L τ - A τ) (v + (Pj L v - v)) + A τ (Pj L v - v)‖
      ≤ ‖(AL L τ - A τ) (v + (Pj L v - v))‖ + ‖A τ (Pj L v - v)‖ := norm_add_le _ _
    _ ≤ ‖AL L τ - A τ‖ * ‖v + (Pj L v - v)‖ + ‖A τ‖ * ‖Pj L v - v‖ := by
        gcongr
        · exact ContinuousLinearMap.le_opNorm _ _
        · exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖AL L τ - A τ‖ * (‖v‖ + ‖Pj L v - v‖) + ‖A τ‖ * ‖Pj L v - v‖ := by
        gcongr
        exact norm_add_le _ _

theorem measure_projection_proof {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Pj : ℕ → (E →L[ℝ] E)) (K : ℝ) (hK : ∀ L, ‖Pj L‖ ≤ K)
    (hconv : ∀ e, Tendsto (fun L => Pj L e) atTop (𝓝 e))
    (T : ℝ) (hT : 0 < T) (F : ℝ → E) (hF : BoundedVariationOn F (Set.Icc 0 T)) (hF0 : F 0 = 0)
    (A : ℝ → (E →L[ℝ] ℝ)) (AL : ℕ → ℝ → (E →L[ℝ] ℝ))
    (hA : ContinuousOn A (Set.Icc 0 T)) (hAL : ∀ L, ContinuousOn (AL L) (Set.Icc 0 T))
    (hAu : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ u ∈ Set.Icc (0 : ℝ) T, ‖AL L u - A u‖ ≤ ε) :
    ∃ I : ℝ, IsRS T (fun τ a b => A τ (F b - F a)) I ∧
      ∃ IL : ℕ → ℝ, (∀ L, IsRS T (fun τ a b => AL L τ (Pj L (F b - F a))) (IL L)) ∧
        Tendsto IL atTop (𝓝 I) := by
  obtain ⟨hW0, hWadd⟩ := q17_W_props T F hF
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hW00 : 0 ≤ q17_Wf F 0 T := le_trans (norm_nonneg _) (hW0 0 T le_rfl hT.le le_rfl)
  have hWaddK : ∀ x u y, 0 ≤ x → x ≤ u → u ≤ y → y ≤ T →
      K * q17_Wf F x u + K * q17_Wf F u y ≤ K * q17_Wf F x y := fun x u y hx hxu huy hy => by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hWadd x u y hx hxu huy hy) hK0
  have hWG : ∀ L, ∀ x y, 0 ≤ x → x ≤ y → y ≤ T →
      ‖Pj L (F y) - Pj L (F x)‖ ≤ K * q17_Wf F x y := fun L x y hx hxy hy => by
    rw [← map_sub]
    calc ‖Pj L (F y - F x)‖ ≤ ‖Pj L‖ * ‖F y - F x‖ := (Pj L).le_opNorm _
      _ ≤ K * q17_Wf F x y := mul_le_mul (hK L) (hW0 x y hx hxy hy) (norm_nonneg _) hK0
  have hconvG : ∀ L (τ a b : ℝ), AL L τ (Pj L (F b) - Pj L (F a)) = AL L τ (Pj L (F b - F a)) :=
    fun L τ a b => by rw [map_sub (Pj L) (F b) (F a)]
  obtain ⟨I, hI⟩ := q17_exists T hT A F (q17_Wf F) hW0 hWadd hA
  have hILex : ∀ L, ∃ x : ℝ, IsRS T (fun τ a b => AL L τ (Pj L (F b - F a))) x := by
    intro L
    obtain ⟨x, hx⟩ := q17_exists T hT (AL L) (fun t => Pj L (F t)) (fun x y => K * q17_Wf F x y)
      (hWG L) hWaddK (hAL L)
    refine ⟨x, ?_⟩
    have hfun : (fun τ a b => AL L τ (Pj L (F b - F a))) =
        (fun τ a b => AL L τ ((fun t => Pj L (F t)) b - (fun t => Pj L (F t)) a)) := by
      funext τ a b
      exact (hconvG L τ a b).symm
    rw [hfun]
    exact hx
  choose IL hIL using hILex
  refine ⟨I, hI, IL, hIL, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hKW : 0 ≤ K * q17_Wf F 0 T := mul_nonneg hK0 hW00
  set η₁ : ℝ := ε / (6 * (K * q17_Wf F 0 T + 1)) with hη₁def
  have hη₁ : 0 < η₁ := div_pos hε (by linarith)
  have hη₁eq : η₁ * (K * q17_Wf F 0 T + 1) = ε / 6 := by
    rw [hη₁def]
    field_simp
  obtain ⟨δA, hδA, hmodA⟩ := q17_modulus T A hA η₁ hη₁
  obtain ⟨L₀, hL₀⟩ := hAu η₁ hη₁
  obtain ⟨δI, hδI, hI'⟩ := hI (ε / 6) (by positivity)
  set δR : ℝ := δA / 4 with hδRdef
  have hδR : 0 < δR := by positivity
  have hmin0 : 0 < min δI δR / 2 := half_pos (lt_min hδI hδR)
  have hmin1 : min δI δR / 2 < δI := by linarith [min_le_left δI δR]
  have hmin2 : min δI δR / 2 ≤ δR := by linarith [min_le_right δI δR]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, T / (min δI δR / 2) < M := exists_nat_gt _
  have hPmesh : T / ((M + 1 : ℕ) : ℝ) ≤ min δI δR / 2 :=
    q17_small T _ hT hmin0 M hM (M + 1) (by omega)
  obtain ⟨hPv1, hPv2, hPv3, hPv4, hPv5⟩ := q17_uf_valid T hT.le M
  have h0P : ∀ j : Fin (M + 1 + 1), 0 ≤ q17_uf T (M + 1) j := fun j => by
    have := hPv1 (Fin.zero_le j)
    rw [hPv4] at this
    exact this
  have hTP : ∀ j : Fin (M + 1 + 1), q17_uf T (M + 1) j ≤ T := fun j => by
    have := hPv1 (Fin.le_last j)
    rw [hPv5] at this
    exact this
  have hτI : ∀ i : Fin (M + 1), q17_ut T (M + 1) i ∈ Set.Icc (0 : ℝ) T := fun i =>
    ⟨le_trans (h0P _) (hPv3 i).1, le_trans (hPv3 i).2 (hTP _)⟩
  have hPI : |∑ i : Fin (M + 1), A (q17_ut T (M + 1) i)
      (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc)) - I| < ε / 6 :=
    hI' (M + 1) (q17_uf T (M + 1)) (q17_ut T (M + 1)) (q17_uf_strict T hT (M + 1) (by omega))
      hPv4 hPv5 hPv3 (fun i => by rw [hPv2 i]; exact lt_of_le_of_lt hPmesh hmin1)
  have hlim : Tendsto (fun L => ∑ i : Fin (M + 1), AL L (q17_ut T (M + 1) i)
      (Pj L (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc)))
      - ∑ i : Fin (M + 1), A (q17_ut T (M + 1) i)
      (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc))) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin (M + 1))) (fun i _ =>
      q17_term_tendsto Pj K hK hconv F A AL T hAu (q17_ut T (M + 1) i)
        (q17_uf T (M + 1) i.castSucc) (q17_uf T (M + 1) i.succ) (hτI i))
    simpa only [Finset.sum_sub_distrib, Finset.sum_const_zero] using h
  obtain ⟨L₁, hL₁⟩ := Metric.tendsto_atTop.1 hlim (ε / 6) (by positivity)
  -- per-`L` comparison of the integrals with the projected sums
  have hILbound : ∀ L, L₀ ≤ L → |IL L - ∑ i : Fin (M + 1), AL L (q17_ut T (M + 1) i)
      (Pj L (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc)))|
      < ε / 12 + 3 * η₁ * (K * q17_Wf F 0 T) := by
    intro L hL
    have hBL : ∀ s t, 0 ≤ s → s ≤ T → 0 ≤ t → t ≤ T → |s - t| ≤ 2 * δR →
        ‖AL L s - AL L t‖ ≤ 3 * η₁ := by
      intro s t hs hsT ht htT hst
      have e1 := hL₀ L hL s ⟨hs, hsT⟩
      have e3 := hL₀ L hL t ⟨ht, htT⟩
      have e2 := hmodA s t hs hsT ht htT (by rw [hδRdef] at hst; linarith)
      calc ‖AL L s - AL L t‖
          = ‖((AL L s - A s) + (A s - A t)) - (AL L t - A t)‖ := by congr 1; abel
        _ ≤ ‖(AL L s - A s) + (A s - A t)‖ + ‖AL L t - A t‖ := norm_sub_le _ _
        _ ≤ ‖AL L s - A s‖ + ‖A s - A t‖ + ‖AL L t - A t‖ := by
            linarith [norm_add_le (AL L s - A s) (A s - A t)]
        _ ≤ 3 * η₁ := by linarith
    obtain ⟨δL, hδL, hILd⟩ := hIL L (ε / 12) (by positivity)
    have hminL0 : 0 < min δL δR / 2 := half_pos (lt_min hδL hδR)
    have hminL1 : min δL δR / 2 < δL := by linarith [min_le_left δL δR]
    have hminL2 : min δL δR / 2 ≤ δR := by linarith [min_le_right δL δR]
    obtain ⟨M', hM'⟩ : ∃ M' : ℕ, T / (min δL δR / 2) < M' := exists_nat_gt _
    have hQmesh : T / ((M' + 1 : ℕ) : ℝ) ≤ min δL δR / 2 :=
      q17_small T _ hT hminL0 M' hM' (M' + 1) (by omega)
    obtain ⟨hQ1, hQ2, hQ3, hQ4, hQ5⟩ := q17_uf_valid T hT.le M'
    have hQI := hILd (M' + 1) (q17_uf T (M' + 1)) (q17_ut T (M' + 1))
      (q17_uf_strict T hT (M' + 1) (by omega)) hQ4 hQ5 hQ3
      (fun i => by rw [hQ2 i]; exact lt_of_le_of_lt hQmesh hminL1)
    have hR' : ‖∑ i : Fin (M' + 1), AL L (q17_ut T (M' + 1) i)
        (Pj L (F (q17_uf T (M' + 1) i.succ)) - Pj L (F (q17_uf T (M' + 1) i.castSucc)))
        - ∑ j : Fin (M + 1), AL L (q17_ut T (M + 1) j)
        (Pj L (F (q17_uf T (M + 1) j.succ)) - Pj L (F (q17_uf T (M + 1) j.castSucc)))‖
        ≤ 3 * η₁ * (K * q17_Wf F 0 T) :=
      q17_fin_rl (AL L) (fun t => Pj L (F t)) (fun x y => K * q17_Wf F x y) T δR (3 * η₁)
        (hWG L) hWaddK (by positivity) (hBL) (M' + 1) (M + 1)
        (q17_uf T (M' + 1)) (q17_ut T (M' + 1)) (q17_uf T (M + 1)) (q17_ut T (M + 1))
        hQ1 hPv1 (fun i => by rw [hQ2 i]; exact hQmesh.trans hminL2)
        (fun i => by rw [hPv2 i]; exact hPmesh.trans hmin2)
        hQ3 hPv3 hQ4 hQ5 hPv4 hPv5
    simp only [hconvG] at hR'
    rw [Real.norm_eq_abs] at hR'
    have h2 := abs_sub_le (IL L) (∑ i : Fin (M' + 1), AL L (q17_ut T (M' + 1) i)
        (Pj L (F (q17_uf T (M' + 1) i.succ) - F (q17_uf T (M' + 1) i.castSucc))))
        (∑ i : Fin (M + 1), AL L (q17_ut T (M + 1) i)
        (Pj L (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc))))
    rw [abs_sub_comm] at hQI
    linarith
  have hcap : 3 * η₁ * (K * q17_Wf F 0 T) < ε / 2 := by
    nlinarith [hη₁eq, hη₁]
  refine ⟨max L₀ L₁, fun L hL => ?_⟩
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : L₁ ≤ L := le_trans (le_max_right _ _) hL
  have hb1 := hILbound L hL0
  have hb2 := hL₁ L hL1
  rw [Real.dist_eq, sub_zero] at hb2
  rw [Real.dist_eq]
  have h4 := abs_sub_le (IL L) (∑ i : Fin (M + 1), AL L (q17_ut T (M + 1) i)
        (Pj L (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc))))
        (∑ i : Fin (M + 1), A (q17_ut T (M + 1) i)
        (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc)))
  have h5 := abs_sub_le (IL L) (∑ i : Fin (M + 1), A (q17_ut T (M + 1) i)
        (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc))) I
  have h6 := abs_sub_le (∑ i : Fin (M + 1), AL L (q17_ut T (M + 1) i)
        (Pj L (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc))))
        (∑ i : Fin (M + 1), A (q17_ut T (M + 1) i)
        (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc)))
        (∑ i : Fin (M + 1), A (q17_ut T (M + 1) i)
        (F (q17_uf T (M + 1) i.succ) - F (q17_uf T (M + 1) i.castSucc)))
  linarith

end Q17Measure

end HRS.Sec7

example := (@HRS.Sec7.measure_projection_proof : type_of% @HRS.Sec7.measure_projection)
