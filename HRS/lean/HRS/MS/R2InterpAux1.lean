import HRS.Sections.Q17Aux7
import HRS.Whole.Oscillator

/-!
# S10.2 (worker S102), part 1: polygonal interpolation of paths with a family of contractions (generic)

Generic version of the torus projection `projPoly` (`HRS/Sections/Q17Aux5`, `Q17Aux6`): for a normed space `E` and contractions
`Pr L : E →L E` converging strongly to the identity, `(poly L w)(t) = ∑_i hat_i(t) Pr L (w(t_i))` (dyadic grid `t_i = iT/2^L`) is a linear
contraction of `C([0,T];E)` converging strongly to the identity.  Prefix `s102_`, namespace `HRS.MS.R2Interp`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.R2Interp

open HRS HRS.Sec7

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The interpolated function at the time `t`. -/
def s102_polyFun (T : ℝ) (hT : 0 ≤ T) (Pr : ℕ → E →L[ℝ] E) (L : ℕ) (w : C(Set.Icc (0 : ℝ) T, E))
    (t : Set.Icc (0 : ℝ) T) : E :=
  ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
    Pr L (w (Set.projIcc 0 T hT (i * T / 2 ^ L)))

theorem s102_polyFun_cont (T : ℝ) (hT : 0 ≤ T) (Pr : ℕ → E →L[ℝ] E) (L : ℕ)
    (w : C(Set.Icc (0 : ℝ) T, E)) : Continuous (s102_polyFun T hT Pr L w) := by
  unfold s102_polyFun
  refine continuous_finset_sum _ (fun i _ => ?_)
  refine Continuous.smul ?_ continuous_const
  unfold q17_hat
  fun_prop

theorem s102_polyFun_norm_le {T : ℝ} (hT : 0 < T) (Pr : ℕ → E →L[ℝ] E) (hPr : ∀ L, ‖Pr L‖ ≤ 1) (L : ℕ)
    (w : C(Set.Icc (0 : ℝ) T, E)) (t : Set.Icc (0 : ℝ) T) :
    ‖s102_polyFun T hT.le Pr L w t‖ ≤ ‖w‖ := by
  unfold s102_polyFun
  have hs0 : 0 ≤ (t : ℝ) * 2 ^ L / T := by
    have := t.2.1
    positivity
  have hsN : (t : ℝ) * 2 ^ L / T ≤ ((2 ^ L : ℕ) : ℝ) := by
    have := t.2.2
    rw [div_le_iff₀ hT]
    push_cast
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) L]
  calc ‖∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
        Pr L (w (Set.projIcc 0 T hT.le (i * T / 2 ^ L)))‖
      ≤ ∑ i ∈ Finset.range (2 ^ L + 1), ‖q17_hat ((t : ℝ) * 2 ^ L / T) i •
        Pr L (w (Set.projIcc 0 T hT.le (i * T / 2 ^ L)))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i * ‖w‖ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (q17_hat_nonneg _ _)]
        refine mul_le_mul_of_nonneg_left ?_ (q17_hat_nonneg _ _)
        refine ((Pr L).le_opNorm _).trans ?_
        calc ‖Pr L‖ * ‖w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))‖
            ≤ 1 * ‖w‖ := mul_le_mul (hPr L) (ContinuousMap.norm_coe_le_norm w _) (norm_nonneg _)
              zero_le_one
          _ = ‖w‖ := one_mul _
    _ = (∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i) * ‖w‖ :=
        (Finset.sum_mul _ _ _).symm
    _ = ‖w‖ := by rw [q17_hat_sum (2 ^ L) _ hs0 hsN, one_mul]

/-- The interpolation as a continuous linear map of norm `≤ 1`. -/
def s102_poly {T : ℝ} (hT : 0 < T) (Pr : ℕ → E →L[ℝ] E) (hPr : ∀ L, ‖Pr L‖ ≤ 1) (L : ℕ) :
    C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E) :=
  LinearMap.mkContinuous
    { toFun := fun w => ⟨s102_polyFun T hT.le Pr L w, s102_polyFun_cont T hT.le Pr L w⟩
      map_add' := fun w1 w2 => by
        ext t
        simp only [s102_polyFun, ContinuousMap.coe_mk, ContinuousMap.add_apply, map_add, smul_add,
          Finset.sum_add_distrib]
      map_smul' := fun c w => by
        ext t
        simp only [s102_polyFun, ContinuousMap.coe_mk, ContinuousMap.smul_apply, map_smul,
          RingHom.id_apply, Finset.smul_sum, smul_comm c] }
    1 (fun w => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 (fun t => s102_polyFun_norm_le hT Pr hPr L w t))

theorem s102_poly_apply {T : ℝ} (hT : 0 < T) (Pr : ℕ → E →L[ℝ] E) (hPr : ∀ L, ‖Pr L‖ ≤ 1) (L : ℕ)
    (w : C(Set.Icc (0 : ℝ) T, E)) (t : Set.Icc (0 : ℝ) T) :
    s102_poly hT Pr hPr L w t = s102_polyFun T hT.le Pr L w t := rfl

theorem s102_poly_norm_le {T : ℝ} (hT : 0 < T) (Pr : ℕ → E →L[ℝ] E) (hPr : ∀ L, ‖Pr L‖ ≤ 1) (L : ℕ) :
    ‖s102_poly hT Pr hPr L‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Uniform strong convergence of contractions on compact sets. -/
theorem s102_unif_proj (Pr : ℕ → E →L[ℝ] E) (hPr : ∀ L, ‖Pr L‖ ≤ 1)
    (hconv : ∀ x, Tendsto (fun L => Pr L x) atTop (𝓝 x)) {K : Set E} (hK : IsCompact K) (ε : ℝ)
    (hε : 0 < ε) : ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ x ∈ K, ‖Pr L x - x‖ < ε := by
  obtain ⟨S, hSK, hSfin, hcover⟩ := finite_cover_balls_of_compact hK (e := ε / 3) (by positivity)
  have hev : ∀ᶠ L : ℕ in atTop, ∀ y ∈ S, ‖Pr L y - y‖ < ε / 3 := by
    rw [Filter.eventually_all_finite hSfin]
    intro y _
    have := (tendsto_iff_norm_sub_tendsto_zero.1 (hconv y))
    exact (tendsto_order.1 this).2 (ε / 3) (by positivity)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 hev
  refine ⟨L₀, fun L hL x hx => ?_⟩
  obtain ⟨y, hyS, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  have hxy' : ‖x - y‖ < ε / 3 := mem_ball_iff_norm.1 hxy
  have hy := hL₀ L hL y hyS
  have hid : Pr L x - x = Pr L (x - y) + (Pr L y - y) - (x - y) := by
    rw [map_sub]
    abel
  rw [hid]
  have h1 : ‖Pr L (x - y)‖ ≤ ‖x - y‖ :=
    ((Pr L).le_opNorm _).trans (by nlinarith [hPr L, norm_nonneg (x - y)])
  calc ‖Pr L (x - y) + (Pr L y - y) - (x - y)‖
      ≤ ‖Pr L (x - y) + (Pr L y - y)‖ + ‖x - y‖ := norm_sub_le _ _
    _ ≤ ‖Pr L (x - y)‖ + ‖Pr L y - y‖ + ‖x - y‖ := by
        linarith [norm_add_le (Pr L (x - y)) (Pr L y - y)]
    _ < ε := by linarith

/-- Pointwise estimate of the interpolated projection. -/
theorem s102_poly_pointwise {T : ℝ} (hT : 0 < T) (Pr : ℕ → E →L[ℝ] E) (L : ℕ)
    (w : C(Set.Icc (0 : ℝ) T, E)) (ε₁ ε₂ δ : ℝ)
    (hL : T / (2 : ℝ) ^ L < δ)
    (hK1 : ∀ x ∈ Set.range w, ‖Pr L x - x‖ < ε₁)
    (hK2 : ∀ p q : Set.Icc (0 : ℝ) T, dist p q < δ → ‖w p - w q‖ < ε₂)
    (t : Set.Icc (0 : ℝ) T) :
    ‖s102_polyFun T hT.le Pr L w t - w t‖ ≤ ε₁ + ε₂ := by
  unfold s102_polyFun
  have hs0 : 0 ≤ (t : ℝ) * 2 ^ L / T := by
    have := t.2.1
    positivity
  have hsN : (t : ℝ) * 2 ^ L / T ≤ ((2 ^ L : ℕ) : ℝ) := by
    have := t.2.2
    rw [div_le_iff₀ hT]
    push_cast
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) L]
  have hsum := q17_hat_sum (2 ^ L) _ hs0 hsN
  have hsplit : ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
      Pr L (w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))) - w t =
      ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
        (Pr L (w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))) - w t) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hsum, one_smul]
  rw [hsplit]
  calc ‖∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
        (Pr L (w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))) - w t)‖
      ≤ ∑ i ∈ Finset.range (2 ^ L + 1), ‖q17_hat ((t : ℝ) * 2 ^ L / T) i •
        (Pr L (w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))) - w t)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i * (ε₁ + ε₂) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (q17_hat_nonneg _ _)]
        rcases eq_or_lt_of_le (q17_hat_nonneg ((t : ℝ) * 2 ^ L / T) i) with h0 | hpos
        · rw [← h0, zero_mul, zero_mul]
        · have hsi : |(t : ℝ) * 2 ^ L / T - i| < 1 := by
            by_contra hc
            push_neg at hc
            exact hpos.ne' (q17_hat_eq_zero hc)
          have hi' : i ≤ 2 ^ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          refine mul_le_mul_of_nonneg_left ?_ hpos.le
          have hi'' : (i : ℝ) ≤ 2 ^ L := by exact_mod_cast hi'
          have hp_mem : (i : ℝ) * T / 2 ^ L ∈ Set.Icc (0 : ℝ) T :=
            ⟨by positivity, by rw [div_le_iff₀ (by positivity)]; nlinarith⟩
          have hproj : Set.projIcc 0 T hT.le ((i : ℝ) * T / 2 ^ L) =
              ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩ := Set.projIcc_of_mem _ hp_mem
          rw [hproj]
          have hdist : dist (⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩ : Set.Icc (0 : ℝ) T) t < δ := by
            rw [Subtype.dist_eq, Real.dist_eq]
            have key : (i : ℝ) * T / 2 ^ L - (t : ℝ) =
                -((T / 2 ^ L) * ((t : ℝ) * 2 ^ L / T - i)) := by
              field_simp
              ring
            rw [key, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < T / 2 ^ L)]
            calc T / 2 ^ L * |(t : ℝ) * 2 ^ L / T - i| ≤ T / 2 ^ L * 1 :=
                  mul_le_mul_of_nonneg_left hsi.le (by positivity)
              _ = T / 2 ^ L := mul_one _
              _ < δ := hL
          have h1 := hK2 _ t hdist
          have h2 := hK1 (w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩) ⟨_, rfl⟩
          have hsp : Pr L (w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩) - w t =
              (Pr L (w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩) - w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩) +
              (w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩ - w t) := by abel
          rw [hsp]
          exact (norm_add_le _ _).trans (by linarith)
    _ = (∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i) * (ε₁ + ε₂) :=
        (Finset.sum_mul _ _ _).symm
    _ = ε₁ + ε₂ := by rw [hsum, one_mul]

/-- Strong convergence of the interpolated projections. -/
theorem s102_poly_tendsto {T : ℝ} (hT : 0 < T) (Pr : ℕ → E →L[ℝ] E) (hPr : ∀ L, ‖Pr L‖ ≤ 1)
    (hconv : ∀ x, Tendsto (fun L => Pr L x) atTop (𝓝 x)) (w : C(Set.Icc (0 : ℝ) T, E)) :
    Tendsto (fun L : ℕ => s102_poly hT Pr hPr L w) atTop (𝓝 w) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK : IsCompact (Set.range w) := isCompact_range w.continuous
  obtain ⟨L₀, hL₀⟩ := s102_unif_proj Pr hPr hconv hK (ε / 4) (by positivity)
  have hu := Metric.uniformContinuous_iff.1 (CompactSpace.uniformContinuous_of_continuous w.continuous)
    (ε / 4) (by positivity)
  obtain ⟨δ, hδ, hδu⟩ := hu
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℕ, T / δ < K1 := exists_nat_gt _
  filter_upwards [eventually_ge_atTop (max L₀ K1)] with L hL
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hLK : K1 ≤ L := le_trans (le_max_right _ _) hL
  have hpow : T / (2 : ℝ) ^ L < δ := by
    have hL2 : (L : ℝ) < (2 : ℝ) ^ L := by exact_mod_cast Nat.lt_two_pow_self
    have hK1' : (K1 : ℝ) ≤ L := by exact_mod_cast hLK
    have hTK : T < K1 * δ := (div_lt_iff₀ hδ).1 hK1
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
    rw [div_lt_iff₀ h2pos]
    nlinarith
  have hK2 : ∀ p q : Set.Icc (0 : ℝ) T, dist p q < δ → ‖w p - w q‖ < ε / 4 :=
    fun p q hpq => by
      rw [← dist_eq_norm]
      exact hδu hpq
  have hnorm : ‖s102_poly hT Pr hPr L w - w‖ ≤ ε / 4 + ε / 4 := by
    refine (ContinuousMap.norm_le _ (by positivity)).2 ?_
    intro t
    have e : (s102_poly hT Pr hPr L w - w) t = s102_polyFun T hT.le Pr L w t - w t := rfl
    rw [e]
    exact s102_poly_pointwise hT Pr L w (ε / 4) (ε / 4) δ hpow (fun x hx => hL₀ L hL0 x hx) hK2 t
  rw [dist_eq_norm]
  linarith

end HRS.MS.R2Interp

end
