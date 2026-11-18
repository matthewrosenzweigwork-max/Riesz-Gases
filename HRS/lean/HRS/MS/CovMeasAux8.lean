import HRS.MS.CovMeasAux7

/-!
# S10.1 (worker S101B), part 8: pairings of the feature with basic vectors of `𝒦`

`g^τ_u(x) = ⟨Γ_τ(x), u⟩` for `u = (a₀, a', b)`: `⟨B_τ(x),a₀⟩ + ⟨A'_τ(x),a'⟩ + ⟨B_τ(x),b⟩`.  For the vectors
`(e_α,0,0)`, `(0,0,e_α)`, `(0,1_{[0,t]}e_α,0)`:  `B^τ_α(x)`, `B^τ_α(x)`, `1_{τ<t}(U^{τ,t}φ_α - U^{τ,τ}φ_α)(x)`
(fundamental theorem of calculus in `t`).  `s101_Fm_Rk_eq_inner`: if `g_u = f`, `g_v = f'` then `F_{u⊗v} = ∇f·∇f'`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ} {m T : ℝ}

/-- The coordinate vector `e_α ∈ ℓ²`. -/
def s101e (m : ℝ) (α : MultiIndex d) : OscDual d m := lp.single 2 α (1 : ℝ)

/-- `1_{[0,t]} e ∈ L²([0,T];ℓ²)`. -/
def s101Ind (m T t : ℝ) (e : OscDual d m) : L2Path d m T :=
  indicatorConstLp 2 (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) t))
    (measure_ne_top (volume.restrict (Set.Icc (0 : ℝ) T)) _) e

lemma s101_inner_mk (a₀ b₀ : OscDual d m) (a' b' : L2Path d m T) (c₀ c₁ : OscDual d m) :
    inner ℝ (KSpace.mk a₀ a' b₀) (KSpace.mk c₀ b' c₁) =
      inner ℝ a₀ c₀ + inner ℝ a' b' + inner ℝ b₀ c₁ := by
  unfold KSpace.mk
  have h1 := WithLp.prod_inner_apply (𝕜 := ℝ)
    (WithLp.toLp 2 (a₀, WithLp.toLp 2 (a', b₀)) : WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)))
    (WithLp.toLp 2 (c₀, WithLp.toLp 2 (b', c₁)))
  have h2 := WithLp.prod_inner_apply (𝕜 := ℝ)
    (WithLp.toLp 2 (a', b₀) : WithLp 2 (L2Path d m T × OscDual d m)) (WithLp.toLp 2 (b', c₁))
  have h3 : inner ℝ (WithLp.toLp 2 (a₀, WithLp.toLp 2 (a', b₀)) :
      WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)))
      (WithLp.toLp 2 (c₀, WithLp.toLp 2 (b', c₁))) =
      inner ℝ a₀ c₀ + inner ℝ a' b' + inner ℝ b₀ c₁ := by
    rw [h1]
    simp only [WithLp.ofLp_toLp] at h2 ⊢
    rw [h2]
    ring
  exact h3

lemma s101_inner_ellVec_e {m : ℝ} {c : MultiIndex d → ℝ} (h : Memℓp c 2) (α : MultiIndex d) :
    inner ℝ (ellVec (d := d) m c) (s101e m α) = c α := by
  have hc := s101_ellVec_coord (m := m) h α
  rw [real_inner_comm]
  have h1 := lp.inner_single_left (𝕜 := ℝ) (G := fun _ : MultiIndex d => ℝ) α (1 : ℝ)
    (show lp (fun _ : MultiIndex d => ℝ) 2 from ellVec (d := d) m c)
  unfold OscDual.coord at hc
  have h2 : inner ℝ (s101e m α) (ellVec (d := d) m c) = inner ℝ (1 : ℝ)
      ((show lp (fun _ : MultiIndex d => ℝ) 2 from ellVec (d := d) m c) α) := h1
  rw [h2, hc]
  simp

lemma s101_Fl_memLp {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (x : Euc d) :
    MemLp (fun s => s101Fl C m T τ s x) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  have hthmem : ∀ s, Memℓp (fun α => s101Th C m T τ s α x) 2 := fun s =>
    s101_memℓp_of_bound hD.summable fun α => s101_th_bound hD hτ s α x
  have hm : AEStronglyMeasurable (fun s => s101Fl C m T τ s x) (volume.restrict (Icc (0 : ℝ) T)) :=
    s101_aesm_ellVec (m := m) (fun α s => s101Th C m T τ s α x)
      (fun α => (s101_th_aesm hD hτ α x).mono_measure Measure.restrict_le_self) hthmem
  refine MemLp.of_bound hm (Real.sqrt (∑' α, c α ^ 2)) (Eventually.of_forall fun s => ?_)
  exact s101_norm_ellVec_le hD.summable fun α => s101_th_bound hD hτ s α x

lemma s101_Av_eq {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (x : Euc d) :
    s101Av C m T τ x = (s101_Fl_memLp hD hτ x).toLp _ := by
  unfold s101Av
  rw [dif_pos (s101_Fl_memLp hD hτ x)]

/-- The pairing of the `A'`-component with `1_{[0,t]} e_α`. -/
theorem s101_inner_Av_Ind {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (α : MultiIndex d) (x : Euc d) :
    inner ℝ (s101Av C m T τ x) (s101Ind m T t (s101e m α)) =
      ∫ s in Icc (0 : ℝ) t, s101Th C m T τ s α x := by
  have hmem := s101_Fl_memLp hD hτ x
  rw [s101_Av_eq hD hτ x, real_inner_comm]
  unfold s101Ind
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral (𝕜 := ℝ)]
  have hae : (fun s => ((hmem.toLp _ : L2Path d m T) : ℝ → OscDual d m) s) =ᵐ[volume.restrict (Icc (0 : ℝ) T)]
      fun s => s101Fl C m T τ s x := MemLp.coeFn_toLp hmem
  have hsub : volume.restrict (Icc (0 : ℝ) t) ≤ volume.restrict (Icc (0 : ℝ) T) :=
    Measure.restrict_mono (Icc_subset_Icc_right ht.2) le_rfl
  have hint : ∫ s in Icc (0 : ℝ) t, ((hmem.toLp _ : L2Path d m T) : ℝ → OscDual d m) s
      ∂(volume.restrict (Icc (0 : ℝ) T)) = ∫ s in Icc (0 : ℝ) t, s101Fl C m T τ s x := by
    rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.2 (Icc_subset_Icc_right ht.2)]
    exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right ht.2) hae)
  rw [hint]
  have hint2 : Integrable (fun s => s101Fl C m T τ s x) (volume.restrict (Icc (0 : ℝ) t)) :=
    (hmem.integrable one_le_two).mono_measure hsub |>.congr (by
      exact Eventually.of_forall fun _ => rfl)
  rw [← integral_inner hint2]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  have hth : Memℓp (fun α => s101Th C m T τ s α x) 2 :=
    s101_memℓp_of_bound hD.summable fun α => s101_th_bound hD hτ s α x
  show inner ℝ (s101e m α) (ellVec (d := d) m (fun α => s101Th C m T τ s α x)) = _
  rw [real_inner_comm, s101_inner_ellVec_e hth]

lemma s101_th_intervalIntegrable {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (α : MultiIndex d) (x : Euc d) (a b : ℝ) :
    IntervalIntegrable (fun s => s101Th C m T τ s α x) volume a b := by
  have hm := s101_th_aesm hD hτ α x
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := c α) measure_Ioc_lt_top.ne hm ?_
  exact Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]; exact s101_th_bound hD hτ s α x

/-- `∫_{[0,t]} 1_{τ<s≤T} ∂_sU^{τ,s}φ_α(x) ds = 1_{τ<t}(U^{τ,t}φ_α - U^{τ,τ}φ_α)(x)`. -/
theorem s101_int_th {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (α : MultiIndex d) (x : Euc d) :
    ∫ s in Icc (0 : ℝ) t, s101Th C m T τ s α x =
      if τ < t then propagatorW C τ t (oscTestFun m α) x - propagatorW C τ τ (oscTestFun m α) x else 0 := by
  by_cases hlt : τ < t
  · rw [if_pos hlt, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1,
      ← intervalIntegral.integral_add_adjacent_intervals (b := τ)
        (s101_th_intervalIntegrable hD hτ α x 0 τ) (s101_th_intervalIntegrable hD hτ α x τ t)]
    have h0 : ∫ s in (0 : ℝ)..τ, s101Th C m T τ s α x = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro s hs
        rw [Set.uIcc_of_le hτ.1] at hs
        have : ¬ (τ < s ∧ s ≤ T) := fun h => absurd h.1 (not_lt.2 hs.2)
        simp [s101Th, this]
    rw [h0, zero_add]
    exact (s101_ftc hD hτ ⟨hlt.le, ht.2⟩ α x).symm
  · rw [if_neg hlt]
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    have : ¬ (τ < s ∧ s ≤ T) := fun h => hlt (h.1.trans_le hs.2)
    simp [s101Th, this]

/-- `g^τ_u(x) = ⟨Γ_τ(x), u⟩`. -/
def s101g (C : WholeCoeff d) (m T τ : ℝ) (u : KSpace d m T) (x : Euc d) : ℝ :=
  inner ℝ (s101Gamma C m T τ x) u

lemma s101_Bv_inner {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (α : MultiIndex d) (x : Euc d) :
    inner ℝ (s101Bv C m τ x) (s101e m α) = propagatorW C τ τ (oscTestFun m α) x := by
  have hmem : Memℓp (fun α => propagatorW C τ τ (oscTestFun m α) x) 2 :=
    s101_memℓp_of_bound hD.summable fun α => by
      have := hD.bddU α τ hτ τ ⟨le_rfl, hτ.2⟩ 0 (Nat.zero_le _) x
      simpa using this
  exact s101_inner_ellVec_e hmem α

lemma s101g_mk {C : WholeCoeff d} {m T τ : ℝ} (a₀ b₀ : OscDual d m) (a' : L2Path d m T) (x : Euc d) :
    s101g C m T τ (KSpace.mk a₀ a' b₀) x =
      inner ℝ (s101Bv C m τ x) a₀ + inner ℝ (s101Av C m T τ x) a' + inner ℝ (s101Bv C m τ x) b₀ :=
  s101_inner_mk _ _ _ _ _ _

/-- The three basic pairings. -/
theorem s101g_W {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (α : MultiIndex d) (x : Euc d) :
    s101g C m T τ (KSpace.mk 0 (s101Ind m T t (s101e m α)) (s101e m α)) x =
      if τ < t then propagatorW C τ t (oscTestFun m α) x else propagatorW C τ τ (oscTestFun m α) x := by
  rw [s101g_mk, inner_zero_right, zero_add, s101_inner_Av_Ind hD hτ ht, s101_int_th hD hτ ht,
    s101_Bv_inner hD hτ]
  split_ifs <;> ring

theorem s101g_P {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (α : MultiIndex d) (x : Euc d) :
    s101g C m T τ (KSpace.mk (s101e m α) (s101Ind m T t (s101e m α)) (-(s101e m α))) x =
      if τ < t then propagatorW C τ t (oscTestFun m α) x - propagatorW C τ τ (oscTestFun m α) x else 0 := by
  rw [s101g_mk, inner_neg_right, s101_inner_Av_Ind hD hτ ht, s101_int_th hD hτ ht, s101_Bv_inner hD hτ]
  ring

theorem s101g_Q {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (α : MultiIndex d) (x : Euc d) :
    s101g C m T τ (KSpace.mk 0 0 (s101e m α)) x = propagatorW C τ τ (oscTestFun m α) x := by
  rw [s101g_mk, inner_zero_right, inner_zero_right, s101_Bv_inner hD hτ]
  ring

theorem s101g_A {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (α : MultiIndex d) (x : Euc d) :
    s101g C m T τ (KSpace.mk (s101e m α) 0 0) x = propagatorW C τ τ (oscTestFun m α) x := by
  rw [s101g_mk, inner_zero_right, inner_zero_right, s101_Bv_inner hD hτ]
  ring

end HRS.MS.CovMeas
