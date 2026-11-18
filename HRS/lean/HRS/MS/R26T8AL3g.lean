import HRS.MS.R26T8AL3f

/-!
# S8.2 observed-time layer, generic lemma L3 (statement): Sobolev multiplier by a smooth bounded-derivative coefficient

`r26t8a_l3`: for `c` smooth with every iterated derivative bounded and `v` `SobSmooth`:
`c · v` is `SobSmooth`, and for every natural `m`, `sobolevNormE m (c·v) ≤ C_m · sobolevNormE m v`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.Whole.Q09A LineDeriv

variable {d : ℕ}

theorem r26t8a_l3_memSobolev_zero (g : Euc d → ℝ) (hg : MemLp g 2 volume) :
    HRS.PDE.ToolboxRd.MemSobolev 0 g :=
  ⟨hg, by simpa [Real.rpow_zero] using integrable_norm_sq_fourierL2 hg⟩

theorem r26t8a_l3 (c v : Euc d → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcb : ∀ n : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ n c x‖ ≤ B) (hv : r26t8a_SobSmooth v) :
    r26t8a_SobSmooth (fun x => c x * v x) ∧ ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      sobolevNormE (m : ℝ) (fun x => c x * v x) ≤ ENNReal.ofReal C * sobolevNormE (m : ℝ) v := by
  classical
  have hcb0 := hcb
  choose Bc hBc using hcb
  have hcB : ∀ x, |c x| ≤ Bc 0 := fun x => by
    have := hBc 0 x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this
  have hc_inf : MemLp c ⊤ volume :=
    memLp_top_of_bound hc.continuous.aestronglyMeasurable (Bc 0)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hcB x)
  have hw2 : MemLp (fun x => c x * v x) 2 volume := hc_inf.mul (hv.2 0).1
  have hsq0 : ∫ x, (c x * v x) ^ 2 ≤ Bc 0 ^ 2 * ∫ x, v x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono (hw2.integrable_sq) ((hv.2 0).1.integrable_sq.const_mul _) fun x => ?_
    have h1 : (c x) ^ 2 ≤ Bc 0 ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcB x) 2
    calc (c x * v x) ^ 2 = (c x) ^ 2 * v x ^ 2 := by ring
      _ ≤ Bc 0 ^ 2 * v x ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hkey : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun x => c x * v x) ∧
      sobolevNormSq (m : ℝ) (fun x => c x * v x) ≤ K * sobolevNormSq (m : ℝ) v := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨Bc 0 ^ 2, sq_nonneg _, ?_, ?_⟩
      · rw [Nat.cast_zero]
        exact r26t8a_l3_memSobolev_zero _ hw2
      · simp only [Nat.cast_zero]
        rw [r26t8a_l3d_sob0 _ hw2, r26t8a_l3d_sob0 _ (hv.2 0).1]
        exact hsq0
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hG : ∀ i : Fin d, Chain i (n + 1) (fun x => (((fun y => c y * v y) x : ℝ) : ℂ))
          ((fun i j x => (((r26t8a_l3_D i)^[j] (fun y => c y * v y) x : ℝ) : ℂ)) i) :=
        fun i => ⟨by funext x; simp, fun j _ => r26t8a_l3e_wd i c v hc hcb0 hv j⟩
      obtain ⟨hmem, hb⟩ := memSobolev_of_chains (d := d) (m := n + 1) (by omega) hw2
        (fun i j x => (((r26t8a_l3_D i)^[j] (fun y => c y * v y) x : ℝ) : ℂ)) hG
      set S := sobolevNormSq ((n + 1 : ℕ) : ℝ) v with hS
      set K' : ℝ := (((n + 1 : ℕ) : ℝ) + 1) *
        (∑ k ∈ Finset.range (n + 1 + 1), (((n + 1).choose k : ℝ) * |Bc k|) ^ 2) with hK'
      have hterm : ∀ i : Fin d, ∫ x, ‖(((r26t8a_l3_D i)^[n + 1] (fun y => c y * v y) x : ℝ) : ℂ)‖ ^ 2
          ≤ K' * S := by
        intro i
        have e : ∀ x, ‖(((r26t8a_l3_D i)^[n + 1] (fun y => c y * v y) x : ℝ) : ℂ)‖ ^ 2 =
            ((r26t8a_l3_D i)^[n + 1] (fun y => c y * v y) x) ^ 2 := fun x => by
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
        simp only [e]
        exact (r26t8a_l3f_top i c v hc Bc (fun k x => hBc k x) hv (n + 1)).trans_eq (by rfl)
      have hsum : ∑ i : Fin d, ∫ x, ‖(((r26t8a_l3_D i)^[n + 1] (fun y => c y * v y) x : ℝ) : ℂ)‖ ^ 2
          ≤ (d : ℝ) * (K' * S) := by
        calc ∑ i : Fin d, ∫ x, ‖(((r26t8a_l3_D i)^[n + 1] (fun y => c y * v y) x : ℝ) : ℂ)‖ ^ 2
            ≤ ∑ _i : Fin d, K' * S := Finset.sum_le_sum fun i _ => hterm i
          _ = (d : ℝ) * (K' * S) := by simp
      have hv2 : ∫ x, v x ^ 2 ≤ S := by
        rw [← r26t8a_l3d_sob0 v (hv.2 0).1]
        exact r26t8a_l3d_sq_mono (by positivity) v (hv.2 (n + 1))
      have hcsq : ∫ x, (c x * v x) ^ 2 ≤ Bc 0 ^ 2 * S :=
        hsq0.trans (mul_le_mul_of_nonneg_left hv2 (sq_nonneg _))
      have hbd' : sobolevNormSq ((n + 1 : ℕ) : ℝ) (fun x => c x * v x) ≤
          ((d : ℝ) + 1) ^ n * (Bc 0 ^ 2 + (d : ℝ) * K') * S := by
        refine hb.trans ?_
        have hn : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by push_cast; ring
        have hexp : ((n + 1) - 1 : ℕ) = n := by omega
        rw [hexp]
        have hpos : (0 : ℝ) ≤ ((d : ℝ) + 1) ^ n := by positivity
        calc ((d : ℝ) + 1) ^ n * ((∫ x, (c x * v x) ^ 2) + ∑ i : Fin d,
              ∫ x, ‖(((r26t8a_l3_D i)^[n + 1] (fun y => c y * v y) x : ℝ) : ℂ)‖ ^ 2)
            ≤ ((d : ℝ) + 1) ^ n * ((Bc 0 ^ 2 * S) + (d : ℝ) * (K' * S)) :=
              mul_le_mul_of_nonneg_left (add_le_add hcsq hsum) hpos
          _ = ((d : ℝ) + 1) ^ n * (Bc 0 ^ 2 + (d : ℝ) * K') * S := by ring
      have hKnn : 0 ≤ ((d : ℝ) + 1) ^ n * (Bc 0 ^ 2 + (d : ℝ) * K') := by
        refine mul_nonneg (by positivity) (add_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_))
        rw [hK']
        refine mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => sq_nonneg _)
      exact ⟨_, hKnn, hmem, hbd'⟩
  choose K hK0 hmem hbd using hkey
  refine ⟨⟨hc.mul hv.1, fun m => hmem m⟩, fun m => ⟨Real.sqrt (K m), Real.sqrt_nonneg _, ?_⟩⟩
  have hv' : sobolevNormE (m : ℝ) v = ENNReal.ofReal (Real.sqrt (sobolevNormSq (m : ℝ) v)) := by
    unfold sobolevNormE
    rw [if_pos (hv.2 m)]
  have hc' : sobolevNormE (m : ℝ) (fun x => c x * v x) =
      ENNReal.ofReal (Real.sqrt (sobolevNormSq (m : ℝ) (fun x => c x * v x))) := by
    unfold sobolevNormE
    rw [if_pos (hmem m)]
  rw [hc', hv', ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.sqrt_mul (hK0 m)]
  exact Real.sqrt_le_sqrt (hbd m)

end HRS.MS.R26T8A

end
