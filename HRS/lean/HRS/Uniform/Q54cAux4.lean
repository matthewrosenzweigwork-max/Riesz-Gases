import HRS.Uniform.Q07cAux8
import HRS.Prob.MartingaleLindeberg

/-!
# Q54c, part 4: covariances of a Hilbert martingale with deterministic covariation

For `G` a continuous `H`-valued martingale with deterministic covariation density `C`
(`IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r)`) and `u v ∈ H`:

* `cov_fn`: `E[⟨G_p,u⟩⟨G_q,v⟩] = ∫_0^{p∧q} C_σ(u,v) dσ`;
* `inc_cov`: for increments over cells `(s,s']`, `(r,r']`:
  `E[⟨G_{s'}-G_s,u⟩⟨G_{r'}-G_r,v⟩] = ∫_{(s,s']∩(r,r']} C_σ(u,v) dσ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS HRS.Uniform.Q07c

section Mart

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {G : ℝ → Ω → H} {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ}

theorem second_moment (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    {p : ℝ} (hp : 0 ≤ p) (hpT : p ≤ T) (u v : H) :
    ∫ ω, inner ℝ (G p ω) u * inner ℝ (G p ω) v ∂P = ∫ σ in Set.Icc 0 p, C σ u v := by
  have hT : 0 ≤ T := hp.trans hpT
  have hmart := hG.covariation u v
  have h := hmart.setIntegral_eq hp MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  have h0 : ∫ ω, (inner ℝ (G 0 ω) u * inner ℝ (G 0 ω) v -
      ∫ σ in Set.Icc 0 0, (fun r (_ : Ω) => C r) σ ω u v) ∂P = 0 := by
    have : (fun ω => inner ℝ (G 0 ω) u * inner ℝ (G 0 ω) v -
        ∫ σ in Set.Icc 0 0, (fun r (_ : Ω) => C r) σ ω u v) =ᵐ[P] fun _ => (0 : ℝ) := by
      filter_upwards [hG.zero] with ω hω
      simp [hω]
    rw [integral_congr_ae this]; simp
  rw [h0] at h
  have hint : Integrable (fun ω => inner ℝ (G p ω) u * inner ℝ (G p ω) v) P :=
    (memLp_inner_aux hG hT u hpT).integrable_mul (memLp_inner_aux hG hT v hpT)
  have h2 := h.symm
  rw [integral_sub hint (integrable_const _), integral_const] at h2
  simp only [probReal_univ, smul_eq_mul, one_mul] at h2
  linarith

theorem cov_fn_le (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hqT : q ≤ T) (u v : H) :
    ∫ ω, inner ℝ (G p ω) u * inner ℝ (G q ω) v ∂P = ∫ σ in Set.Icc 0 p, C σ u v := by
  have hT : 0 ≤ T := hp.trans (hpq.trans hqT)
  have h := LindebergAux.integral_mul_martingale (P := P) ℱ (hG.martingale v) hpq
    (Z := fun ω => inner ℝ (G p ω) u) ((hG.martingale u).1 p)
    (memLp_inner_aux hG hT u (hpq.trans hqT)) (memLp_inner_aux hG hT v hqT)
  rw [h]
  exact second_moment hG hp (hpq.trans hqT) u v

theorem C_symm (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 T) (u v : H) : C σ u v = C σ v u := by
  obtain ⟨ω, hω⟩ := hG.sigma_traceClass.exists
  exact (hω σ hσ).symm u v

theorem cov_fn (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpT : p ≤ T) (hqT : q ≤ T) (u v : H) :
    ∫ ω, inner ℝ (G p ω) u * inner ℝ (G q ω) v ∂P = ∫ σ in Set.Icc 0 (min p q), C σ u v := by
  rcases le_total p q with h | h
  · rw [min_eq_left h]; exact cov_fn_le hG hp h hqT u v
  · rw [min_eq_right h]
    have := cov_fn_le hG hq h hpT v u
    calc ∫ ω, inner ℝ (G p ω) u * inner ℝ (G q ω) v ∂P =
        ∫ ω, inner ℝ (G q ω) v * inner ℝ (G p ω) u ∂P := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
      _ = ∫ σ in Set.Icc 0 q, C σ v u := this
      _ = ∫ σ in Set.Icc 0 q, C σ u v := by
          refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
          exact (C_symm hG ⟨hσ.1, hσ.2.trans (h.trans hpT)⟩ u v).symm

/-- indicator identity behind the increment covariance. -/
theorem ind_comb (F : ℝ → ℝ) {s s' r r' : ℝ} (hs : s ≤ s') (hr : r ≤ r') (σ : ℝ) :
    (Set.Iic (min s' r')).indicator F σ - (Set.Iic (min s' r)).indicator F σ -
      (Set.Iic (min s r')).indicator F σ + (Set.Iic (min s r)).indicator F σ =
    (Set.Ioc s s' ∩ Set.Ioc r r').indicator F σ := by
  simp only [Set.indicator, Set.mem_Iic, Set.mem_inter_iff, Set.mem_Ioc, le_min_iff]
  by_cases h1 : σ ≤ s' <;> by_cases h2 : σ ≤ s <;> by_cases h3 : σ ≤ r' <;> by_cases h4 : σ ≤ r <;>
    simp [h1, h2, h3, h4, not_le] <;> first | linarith | skip

theorem inc_cov (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    {s s' r r' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s') (hs'T : s' ≤ T) (hr : 0 ≤ r) (hrr' : r ≤ r')
    (hr'T : r' ≤ T) (u v : H) :
    ∫ ω, inner ℝ (G s' ω - G s ω) u * inner ℝ (G r' ω - G r ω) v ∂P =
      ∫ σ in Set.Ioc s s' ∩ Set.Ioc r r', C σ u v := by
  have hT : 0 ≤ T := hs.trans (hss'.trans hs'T)
  have hL : ∀ {x : ℝ}, 0 ≤ x → x ≤ T → ∀ w : H, MemLp (fun ω => inner ℝ (G x ω) w) 2 P :=
    fun hx hxT w => memLp_inner_aux hG hT w hxT
  have hI : ∀ {x y : ℝ}, 0 ≤ x → x ≤ T → 0 ≤ y → y ≤ T →
      Integrable (fun ω => inner ℝ (G x ω) u * inner ℝ (G y ω) v) P :=
    fun hx hxT hy hyT => (hL hx hxT u).integrable_mul (hL hy hyT v)
  have hs' : 0 ≤ s' := hs.trans hss'
  have hr' : 0 ≤ r' := hr.trans hrr'
  have e : ∀ ω, inner ℝ (G s' ω - G s ω) u * inner ℝ (G r' ω - G r ω) v =
      inner ℝ (G s' ω) u * inner ℝ (G r' ω) v - inner ℝ (G s' ω) u * inner ℝ (G r ω) v
      - inner ℝ (G s ω) u * inner ℝ (G r' ω) v + inner ℝ (G s ω) u * inner ℝ (G r ω) v := by
    intro ω; rw [inner_sub_left, inner_sub_left]; ring
  simp_rw [e]
  have i1 := hI hs' hs'T hr' hr'T
  have i2 := hI hs' hs'T hr (hrr'.trans hr'T)
  have i3 := hI hs (hss'.trans hs'T) hr' hr'T
  have i4 := hI hs (hss'.trans hs'T) hr (hrr'.trans hr'T)
  have i12 : Integrable (fun ω => inner ℝ (G s' ω) u * inner ℝ (G r' ω) v -
      inner ℝ (G s' ω) u * inner ℝ (G r ω) v) P := i1.sub i2
  have i123 : Integrable (fun ω => inner ℝ (G s' ω) u * inner ℝ (G r' ω) v -
      inner ℝ (G s' ω) u * inner ℝ (G r ω) v - inner ℝ (G s ω) u * inner ℝ (G r' ω) v) P := i12.sub i3
  rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]
  rw [cov_fn hG hs' hr' hs'T hr'T, cov_fn hG hs' hr hs'T (hrr'.trans hr'T),
    cov_fn hG hs hr' (hss'.trans hs'T) hr'T, cov_fn hG hs hr (hss'.trans hs'T) (hrr'.trans hr'T)]
  -- the deterministic identity
  have hCi : IntegrableOn (fun σ => C σ u v) (Set.Icc 0 T) := by
    obtain ⟨ω, hω⟩ := hG.sigma_entry_int.exists
    exact hω u v
  have hind : ∀ m : ℝ, m ≤ T → (∫ σ in Set.Icc 0 m, C σ u v) =
      ∫ σ in Set.Icc 0 T, (Set.Iic m).indicator (fun σ => C σ u v) σ := by
    intro m hm
    have hset : Set.Icc (0 : ℝ) T ∩ Set.Iic m = Set.Icc 0 m := by
      ext σ
      simp only [Set.mem_Icc, Set.mem_inter_iff, Set.mem_Iic]
      constructor
      · intro h; exact ⟨h.1.1, h.2⟩
      · intro h; exact ⟨⟨h.1, h.2.trans hm⟩, h.2⟩
    rw [setIntegral_indicator measurableSet_Iic, hset]
  have hiI : ∀ m : ℝ, Integrable ((Set.Iic m).indicator (fun σ => C σ u v))
      (volume.restrict (Set.Icc 0 T)) := fun m => hCi.indicator measurableSet_Iic
  have hmT : ∀ x y : ℝ, x ≤ T → min x y ≤ T := fun x y hx => (min_le_left _ _).trans hx
  have j1 := hiI (min s' r')
  have j2 := hiI (min s' r)
  have j3 := hiI (min s r')
  have j4 := hiI (min s r)
  have j12 : Integrable (fun σ => (Set.Iic (min s' r')).indicator (fun σ => C σ u v) σ -
      (Set.Iic (min s' r)).indicator (fun σ => C σ u v) σ) (volume.restrict (Set.Icc 0 T)) := j1.sub j2
  have j123 : Integrable (fun σ => (Set.Iic (min s' r')).indicator (fun σ => C σ u v) σ -
      (Set.Iic (min s' r)).indicator (fun σ => C σ u v) σ -
      (Set.Iic (min s r')).indicator (fun σ => C σ u v) σ) (volume.restrict (Set.Icc 0 T)) := j12.sub j3
  have e2 : (∫ σ in Set.Icc 0 T, ((Set.Iic (min s' r')).indicator (fun σ => C σ u v) σ -
      (Set.Iic (min s' r)).indicator (fun σ => C σ u v) σ -
      (Set.Iic (min s r')).indicator (fun σ => C σ u v) σ +
      (Set.Iic (min s r)).indicator (fun σ => C σ u v) σ)) =
      (∫ σ in Set.Icc 0 T, (Set.Iic (min s' r')).indicator (fun σ => C σ u v) σ) -
      (∫ σ in Set.Icc 0 T, (Set.Iic (min s' r)).indicator (fun σ => C σ u v) σ) -
      (∫ σ in Set.Icc 0 T, (Set.Iic (min s r')).indicator (fun σ => C σ u v) σ) +
      (∫ σ in Set.Icc 0 T, (Set.Iic (min s r)).indicator (fun σ => C σ u v) σ) := by
    rw [integral_add j123 j4, integral_sub j12 j3, integral_sub j1 j2]
  have e3 : (∫ σ in Set.Icc 0 T, ((Set.Iic (min s' r')).indicator (fun σ => C σ u v) σ -
      (Set.Iic (min s' r)).indicator (fun σ => C σ u v) σ -
      (Set.Iic (min s r')).indicator (fun σ => C σ u v) σ +
      (Set.Iic (min s r)).indicator (fun σ => C σ u v) σ)) =
      ∫ σ in Set.Icc 0 T, (Set.Ioc s s' ∩ Set.Ioc r r').indicator (fun σ => C σ u v) σ :=
    integral_congr_ae (Filter.Eventually.of_forall fun σ => ind_comb (fun σ => C σ u v) hss' hrr' σ)
  have hsub : Set.Ioc s s' ∩ Set.Ioc r r' ⊆ Set.Icc 0 T := by
    intro σ hσ
    exact ⟨hs.trans hσ.1.1.le, hσ.1.2.trans hs'T⟩
  have e4 : (∫ σ in Set.Icc 0 T, (Set.Ioc s s' ∩ Set.Ioc r r').indicator (fun σ => C σ u v) σ) =
      ∫ σ in Set.Ioc s s' ∩ Set.Ioc r r', C σ u v := by
    rw [setIntegral_indicator (measurableSet_Ioc.inter measurableSet_Ioc), Set.inter_eq_right.2 hsub]
  rw [hind _ (hmT _ _ hs'T), hind _ (hmT _ _ hs'T), hind _ (hmT _ _ (hss'.trans hs'T)),
    hind _ (hmT _ _ (hss'.trans hs'T)), ← e4, ← e3, e2]

end Mart

end HRS.Uniform.Q54c
