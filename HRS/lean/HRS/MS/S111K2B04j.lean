import HRS.MS.S111K2B04i

/-!
# S11.1 continuation, B04 (part 10): continuity of `τ ↦ ∫_{(a,b]} W(v,τ) dv` on `[0,T]`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.R2WinErr HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {S T u Pw : ℝ}
  {z : ℝ → (Euc d → ℝ) → ℝ}

/-- Pointwise (in `v`) continuity of `τ ↦ W(v,τ)` along a sequence, off the exceptional time `v = u + τ₀`. -/
lemma s111k2_W_tendsto (h : S111k2Drift C m c0 r b S T u Pw z) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) (u + T))
    {τn : ℕ → ℝ} {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) T) (hτn : Tendsto τn atTop (𝓝 τ₀))
    (hne : v ≠ u + τ₀) :
    Tendsto (fun n => s111k2_W C m z u v (τn n)) atTop (𝓝 (s111k2_W C m z u v τ₀)) := by
  have hs : Tendsto (fun n => u + τn n) atTop (𝓝 (u + τ₀)) := tendsto_const_nhds.add hτn
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `v < u + τ₀`
    have hev : ∀ᶠ n in atTop, v < u + τn n := hs.eventually_const_lt hlt
    have hY := s111k2_Y_cont_orbit h.hW h.hc0 h.hbs h.hP h.hz hv (h.hone v hv) (h.dual_lt hv)
    have hs0 : u + τ₀ ∈ Set.Ici v := hlt.le
    have h1 : Tendsto (fun n => s111k2_Y C m z v (u + τn n)) atTop (𝓝 (s111k2_Y C m z v (u + τ₀))) :=
      (hY (u + τ₀) hs0).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hs, hev.mono fun n hn => hn.le⟩)
    have e0 : s111k2_W C m z u v τ₀ = s111k2_Y C m z v (u + τ₀) := by
      unfold s111k2_W; rw [if_pos hlt.le]
    rw [e0]
    refine h1.congr' (hev.mono fun n hn => ?_)
    beta_reduce
    unfold s111k2_W; rw [if_pos hn.le]
  · -- `u + τ₀ < v`
    have hev : ∀ᶠ n in atTop, u + τn n < v := hs.eventually_lt_const hgt
    have e0 : s111k2_W C m z u v τ₀ = 0 := by
      unfold s111k2_W; rw [if_neg (not_le.2 hgt)]
    rw [e0]
    refine tendsto_const_nhds.congr' (hev.mono fun n hn => ?_)
    beta_reduce
    unfold s111k2_W; rw [if_neg (not_le.2 hn)]

lemma s111k2_Dfun_cont (h : S111k2Drift C m c0 r b S T u Pw z) {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b')
    (hb : b' ≤ u + T) :
    Continuous (fun τ : Set.Icc (0 : ℝ) T => s111k2_Dfun C m z u a b' τ) := by
  have hsub : Set.Ioc a b' ⊆ Set.Icc (0 : ℝ) (u + T) := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  refine continuous_iff_seqContinuous.2 fun τn τ₀ hτn => ?_
  have hτ0 : (τ₀ : ℝ) ∈ Set.Icc (0 : ℝ) T := τ₀.2
  have hτnv : Tendsto (fun n => (τn n : ℝ)) atTop (𝓝 (τ₀ : ℝ)) := (continuous_subtype_val.tendsto τ₀).comp hτn
  rw [tendsto_iff_edist_tendsto_0]
  have hK := s111k2_Kdrift_pos d r Pw S
  -- the dominated convergence step
  have hlim : Tendsto (fun n => ∫⁻ v in Set.Ioc a b', ‖s111k2_W C m z u v (τn n) - s111k2_W C m z u v τ₀‖ₑ)
      atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := volume.restrict (Set.Ioc a b'))
      (F := fun n v => ‖s111k2_W C m z u v (τn n) - s111k2_W C m z u v τ₀‖ₑ) (f := fun _ => 0)
      (fun v => 2 * ENNReal.ofReal (s111k2_Kdrift d r Pw S) * s111k2_Phi c0 u r Pw z v)
      (fun n => (((s111k2_W_aesm h (τn n).2).mono_measure (Measure.restrict_mono hsub le_rfl)).sub
        ((s111k2_W_aesm h hτ0).mono_measure (Measure.restrict_mono hsub le_rfl))).enorm)
      (fun n => ae_restrict_of_forall_mem measurableSet_Ioc fun v hv => by
        calc ‖s111k2_W C m z u v (τn n) - s111k2_W C m z u v τ₀‖ₑ
            ≤ ‖s111k2_W C m z u v (τn n)‖ₑ + ‖s111k2_W C m z u v τ₀‖ₑ := enorm_sub_le
          _ ≤ ENNReal.ofReal (s111k2_Kdrift d r Pw S) * s111k2_Phi c0 u r Pw z v +
              ENNReal.ofReal (s111k2_Kdrift d r Pw S) * s111k2_Phi c0 u r Pw z v :=
            add_le_add (s111k2_W_bound h (hsub hv) (τn n).2) (s111k2_W_bound h (hsub hv) hτ0)
          _ = 2 * ENNReal.ofReal (s111k2_Kdrift d r Pw S) * s111k2_Phi c0 u r Pw z v := by ring)
      (by
        have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (s111k2_Kdrift d r Pw S) ≠ ⊤ :=
          ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
        rw [lintegral_const_mul' _ _ h2]
        exact ENNReal.mul_ne_top h2 (ne_top_of_le_ne_top (s111k2_Phi_fin h) (lintegral_mono_set hsub)))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc,
          ae_restrict_of_ae ((Set.countable_singleton (u + (τ₀ : ℝ))).ae_notMem (volume : Measure ℝ))]
          with v hv hne
        have hne' : v ≠ u + (τ₀ : ℝ) := fun hh => hne (by simpa using hh)
        have := s111k2_W_tendsto h (hsub hv) hτ0 hτnv hne'
        rw [tendsto_iff_edist_tendsto_0] at this
        simpa [edist_eq_enorm_sub] using this)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) (fun n => ?_)
  rw [edist_eq_enorm_sub]
  unfold s111k2_Dfun
  change ‖(∫ v in Set.Ioc a b', s111k2_W C m z u v (τn n)) - ∫ v in Set.Ioc a b', s111k2_W C m z u v τ₀‖ₑ ≤ _
  rw [← integral_sub (s111k2_W_integrable h (τn n).2 ha hab hb) (s111k2_W_integrable h hτ0 ha hab hb)]
  exact enorm_integral_le_lintegral_enorm _

end HRS.MS.S111K2
