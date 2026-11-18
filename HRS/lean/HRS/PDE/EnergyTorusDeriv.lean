import HRS.PDE.EnergyTorus

/-!
# Differentiating `½‖F(τ)‖²_{H^m}` along a regular solution (Prop 3.13 (a))
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.ET

variable {d : ℕ}

/-! ### Truncation -/

theorem tendsto_hsNormSq_trunc (r : ℝ) (c : Coeff d) (hc : MemHs r c) :
    Tendsto (fun n : ℕ => hsNormSq r (truncCoeff n c)) atTop (𝓝 (hsNormSq r c)) := by
  unfold hsNormSq
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => sobWeight r k * ‖c k‖ ^ 2)
    hc (fun k => ?_) (Filter.Eventually.of_forall fun n k => ?_)
  · obtain ⟨N, hN⟩ := exists_inBox k
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [truncCoeff, hN n hn]
  · rw [Real.norm_of_nonneg (mul_nonneg (sobWeight_nonnegE r k) (sq_nonneg _))]
    by_cases hk : InBox n k
    · simp [truncCoeff, hk]
    · simp [truncCoeff, hk]
      exact mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _)

theorem sobWeight_two_ge_of_not_inBox {n : ℕ} {k : Lattice d} (hk : ¬ InBox n k) :
    (1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) ^ 2 ≤ sobWeight (2 : ℝ) k := by
  unfold InBox at hk
  push Not at hk
  obtain ⟨i, hi⟩ := hk
  have h1 : (n : ℤ) + 1 ≤ |k i| := by omega
  have h2 : ((n : ℝ) + 1) ≤ |((k i : ℤ) : ℝ)| := by
    have : (((n : ℤ) + 1 : ℤ) : ℝ) ≤ ((|k i| : ℤ) : ℝ) := by exact_mod_cast h1
    rw [Int.cast_abs] at this
    simpa using this
  have h3 : ((n : ℝ) + 1) ≤ Lattice.enorm k := h2.trans (abs_coord_le_enorm k i)
  have h4 : ((n : ℝ) + 1) ^ 2 ≤ Lattice.enorm k ^ 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    exact pow_le_pow_left₀ this h3 2
  have h5 : sobWeight (2 : ℝ) k = (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 := by
    unfold sobWeight; rw [Real.rpow_two]
  rw [h5]
  have : 1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
    nlinarith [Real.pi_pos, sq_nonneg Real.pi]
  exact pow_le_pow_left₀ (by positivity) this 2

/-- The tail of an `H^{r+2}` sequence is small in `H^r`. -/
def tailConst (n : ℕ) : ℝ := ((1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) ^ 2)⁻¹

theorem tailConst_nonneg (n : ℕ) : 0 ≤ tailConst n := by unfold tailConst; positivity

theorem tendsto_tailConst : Tendsto tailConst atTop (𝓝 0) := by
  unfold tailConst
  refine tendsto_inv_atTop_zero.comp ?_
  refine tendsto_atTop_mono (fun n : ℕ => ?_) tendsto_natCast_atTop_atTop
  have h1 : (1 : ℝ) ≤ 1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 := by
    have : 0 ≤ 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
    linarith
  have h2 : (n : ℝ) ≤ 1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 := by
    have hpi : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((n : ℝ) + 1)]
  nlinarith

theorem hsNormSq_tail_le (r : ℝ) (n : ℕ) {c : Coeff d} (hc : MemHs (r + 2) c) :
    MemHs r (c - truncCoeff n c) ∧
      hsNormSq r (c - truncCoeff n c) ≤ tailConst n * hsNormSq (r + 2) c := by
  have hle : ∀ k, sobWeight r k * ‖(c - truncCoeff n c) k‖ ^ 2 ≤
      tailConst n * (sobWeight (r + 2) k * ‖c k‖ ^ 2) := by
    intro k
    by_cases hk : InBox n k
    · simp only [Pi.sub_apply, truncCoeff, hk, ite_true, sub_self, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact mul_nonneg (tailConst_nonneg n) (mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _))
    · simp only [Pi.sub_apply, truncCoeff, hk, ite_false, sub_zero]
      have h2 := sobWeight_two_ge_of_not_inBox hk
      have hΘ : 0 < (1 + 4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) ^ 2 := by positivity
      have h3 : tailConst n * sobWeight (2 : ℝ) k ≥ 1 := by
        unfold tailConst
        rw [inv_mul_eq_div, ge_iff_le, le_div_iff₀ hΘ]
        linarith
      rw [sobWeight_add]
      have hw := sobWeight_nonnegE r k
      calc sobWeight r k * ‖c k‖ ^ 2 ≤ sobWeight r k * (tailConst n * sobWeight (2 : ℝ) k) * ‖c k‖ ^ 2 := by
            have : sobWeight r k * 1 ≤ sobWeight r k * (tailConst n * sobWeight (2 : ℝ) k) :=
              mul_le_mul_of_nonneg_left h3 hw
            nlinarith [sq_nonneg ‖c k‖]
        _ = _ := by ring
  have hs : Summable fun k => tailConst n * (sobWeight (r + 2) k * ‖c k‖ ^ 2) := hc.mul_left _
  have hm : MemHs r (c - truncCoeff n c) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonnegE r k) (sq_nonneg _)) hle hs
  refine ⟨hm, ?_⟩
  calc hsNormSq r (c - truncCoeff n c) ≤ ∑' k, tailConst n * (sobWeight (r + 2) k * ‖c k‖ ^ 2) :=
        hm.tsum_le_tsum hle hs
    _ = _ := by rw [tsum_mul_left]; rfl


/-! ### Strongly continuous paths: weak continuity, coordinates, boundedness -/

theorem weakContinuous_of_continuousInHs {r t : ℝ} {F : ℝ → Coeff d}
    (hF : ContinuousInHs r F t) : WeakContinuousInHs r F t := by
  refine ⟨hF.1, fun G hG => ?_⟩
  intro τ₀ hτ₀
  have hτ₀' : τ₀ ∈ Set.Icc 0 t := hτ₀
  have hnorm := hF.2 τ₀ hτ₀'
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ τ in 𝓝[Set.Icc 0 t] τ₀,
      ‖hsInner r (F τ) G - hsInner r (F τ₀) G‖ ≤ hsNorm r (F τ - F τ₀) * Real.sqrt (hsNormSq r G) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    obtain ⟨hm, -⟩ := memHs_sub_sq (hF.1 τ hτ) (hF.1 τ₀ hτ₀')
    rw [← hsInner_sub_left (hF.1 τ hτ) (hF.1 τ₀ hτ₀') hG]
    exact norm_hsInner_le hm hG
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  simpa using hnorm.mul_const (Real.sqrt (hsNormSq r G))

theorem bounded_of_continuousInHs {r t : ℝ} {F : ℝ → Coeff d} (hF : ContinuousInHs r F t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ ∈ Set.Icc (0 : ℝ) t, hsNormSq r (F τ) ≤ B :=
  by
  obtain ⟨B, hB0, hB⟩ := bounded_of_weakContinuous (weakContinuous_of_continuousInHs hF)
  exact ⟨B ^ 2, sq_nonneg _, hB⟩

theorem continuousOn_coord_of_continuousInHs {r t : ℝ} {F : ℝ → Coeff d}
    (hF : ContinuousInHs r F t) (k : Lattice d) :
    ContinuousOn (fun τ => F τ k) (Set.Icc 0 t) :=
  continuousOn_coord_of_weak (weakContinuous_of_continuousInHs hF) k

theorem tendsto_hsNormSq_sub {r t : ℝ} {F : ℝ → Coeff d} (hF : ContinuousInHs r F t)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Set.Icc 0 t) :
    Tendsto (fun τ => hsNormSq r (F τ - F τ₀)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0) := by
  have h := (hF.2 τ₀ hτ₀).pow 2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  refine h.congr fun τ => ?_
  unfold hsNorm
  rw [Real.sq_sqrt (hsNormSq_nonnegE _ _)]


/-! ### Continuity of the generator coordinates -/

theorem hsNormSq_one_sub_deriv {c c' : Coeff d} (hc : MemHs 1 c) (hc' : MemHs 1 c') (j : Fin d) :
    ∀ T : Finset (Lattice d), ∑ k ∈ T, ‖(derivCoeff j c - derivCoeff j c') k‖ ^ 2 ≤
      hsNormSq 1 (c - c') := by
  intro T
  obtain ⟨hm, -⟩ := memHs_sub_sq hc hc'
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (sum_le_hsNormSq hm T)
  have : (derivCoeff j c - derivCoeff j c') k = derivCoeff j (c - c') k := by
    simp [derivCoeff]; ring
  rw [this]
  exact norm_derivCoeff_sq_le j (c - c') k

theorem tendsto_mulCoeff_deriv_strong {α : Type*} {l : Filter α} [l.NeBot] (a : α → Coeff d)
    (a0 : Coeff d) (K : ℝ) (hK0 : 0 ≤ K) (ha : ∀ x, MemHs 0 (a x))
    (haK : ∀ x, hsNormSq 0 (a x) ≤ K)
    (hac : ∀ q, Tendsto (fun x => a x q) l (𝓝 (a0 q)))
    (Fa : α → Coeff d) (G : Coeff d) (hFa : ∀ x, MemHs 1 (Fa x)) (hG : MemHs 1 G)
    (hF : Tendsto (fun x => hsNormSq 1 (Fa x - G)) l (𝓝 0)) (j : Fin d) (k : Lattice d) :
    Tendsto (fun x => mulCoeff (a x) (derivCoeff j (Fa x)) k) l
      (𝓝 (mulCoeff a0 (derivCoeff j G) k)) := by
  set v : Lattice d → ℂ := derivCoeff j G with hv
  set f : α → Lattice d → ℂ := fun x q => a x (k - q) with hf
  set w : α → Lattice d → ℂ := fun x q => derivCoeff j (Fa x) q - v q with hw
  have hfK : ∀ x (T : Finset (Lattice d)), ∑ q ∈ T, ‖f x q‖ ^ 2 ≤ (Real.sqrt K) ^ 2 := by
    intro x T
    rw [Real.sq_sqrt hK0]
    obtain ⟨hs, htsum⟩ := summable_sq_subLeft (ha x) k
    exact (hs.sum_le_tsum T fun l _ => sq_nonneg _).trans (htsum.le.trans (haK x))
  have hvY : ∀ T : Finset (Lattice d), ∑ q ∈ T, ‖v q‖ ^ 2 ≤ (Real.sqrt (hsNormSq 1 G)) ^ 2 := by
    intro T
    rw [Real.sq_sqrt (hsNormSq_nonnegE _ _)]
    exact le_trans (Finset.sum_le_sum fun q _ => norm_derivCoeff_sq_le j G q) (sum_le_hsNormSq hG T)
  have hwY : ∀ x (T : Finset (Lattice d)),
      ∑ q ∈ T, ‖w x q‖ ^ 2 ≤ (Real.sqrt (hsNormSq 1 (Fa x - G))) ^ 2 := by
    intro x T
    rw [Real.sq_sqrt (hsNormSq_nonnegE _ _)]
    exact hsNormSq_one_sub_deriv (hFa x) hG j T
  have hsum1 : ∀ x, Summable fun q => f x q * v q := fun x =>
    Summable.of_norm (norm_tsum_mul_le_split (f x) v ∅ (Real.sqrt K) (Real.sqrt (hsNormSq 1 G))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (hfK x) (fun T _ => hvY T)).1
  have hsum2 : ∀ x, Summable fun q => f x q * w x q := fun x =>
    Summable.of_norm (norm_tsum_mul_le_split (f x) (w x) ∅ (Real.sqrt K)
      (Real.sqrt (hsNormSq 1 (Fa x - G))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (hfK x)
      (fun T _ => hwY x T)).1
  have e : ∀ x, mulCoeff (a x) (derivCoeff j (Fa x)) k =
      ∑' q, f x q * v q + ∑' q, f x q * w x q := by
    intro x
    rw [← (hsum1 x).tsum_add (hsum2 x)]
    unfold mulCoeff
    refine tsum_congr fun q => ?_
    simp only [hf, hw]
    ring
  have hA : Tendsto (fun x => ∑' q, f x q * v q) l (𝓝 (mulCoeff a0 (derivCoeff j G) k)) := by
    refine tendsto_tsum_mul f (fun q => a0 (k - q)) v (Real.sqrt K) (Real.sqrt_nonneg _)
      (Filter.Eventually.of_forall hfK) ?_ (fun q => hac (k - q))
    exact (memHs_zero_iffC _).1 ((memHs_zero_iffC _).2 (summable_of_sum_le (fun q => sq_nonneg _)
      hvY)) |> fun h => h
  have hB : Tendsto (fun x => ∑' q, f x q * w x q) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd : ∀ x, ‖∑' q, f x q * w x q‖ ≤
        Real.sqrt K * Real.sqrt (hsNormSq 1 (Fa x - G)) := by
      intro x
      have := (norm_tsum_mul_le_split (f x) (w x) ∅ (Real.sqrt K)
        (Real.sqrt (hsNormSq 1 (Fa x - G))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (hfK x)
        (fun T _ => hwY x T)).2
      simpa using this
    refine squeeze_zero (fun x => norm_nonneg _) hbd ?_
    have := ((Real.continuous_sqrt.tendsto 0).comp hF).const_mul (Real.sqrt K)
    simpa using this
  simp_rw [e]
  simpa using hA.add hB


theorem tendsto_coord_of_hs1 {α : Type*} {l : Filter α} {Fa : α → Coeff d} {G : Coeff d}
    (hFa : ∀ x, MemHs 1 (Fa x)) (hG : MemHs 1 G)
    (hF : Tendsto (fun x => hsNormSq 1 (Fa x - G)) l (𝓝 0)) (k : Lattice d) :
    Tendsto (fun x => Fa x k) l (𝓝 (G k)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ x, ‖Fa x k - G k‖ ^ 2 ≤ hsNormSq 1 (Fa x - G) := by
    intro x
    obtain ⟨hm, -⟩ := memHs_sub_sq (hFa x) hG
    have h1 := sobWeight_mul_sq_le_hsNormSq hm k
    have h2 : 1 ≤ sobWeight (d := d) 1 k := by rw [sobWeight_one]; exact one_le_sobBase k
    have : ‖(Fa x - G) k‖ ^ 2 ≤ sobWeight 1 k * ‖(Fa x - G) k‖ ^ 2 := by
      nlinarith [sq_nonneg ‖(Fa x - G) k‖]
    simpa using this.trans h1
  have hsq : Tendsto (fun x => ‖Fa x k - G k‖ ^ 2) l (𝓝 0) :=
    squeeze_zero (fun x => sq_nonneg _) hb hF
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
  exact this

theorem tendsto_forwardGen_both {α : Type*} {l : Filter α} [l.NeBot] (D : DynData d)
    (ρ : α → Torus d → ℝ) (ρ0 : Torus d → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hρ : ∀ x, MemHs 0 (coeffOf (ρ x))) (hρK : ∀ x, hsNormSq 0 (coeffOf (ρ x)) ≤ K)
    (hρc : ∀ q, Tendsto (fun x => coeffOf (ρ x) q) l (𝓝 (coeffOf ρ0 q)))
    (hb : ∀ x j, MemHs 0 (driftCoeff D (ρ x) j))
    (hbK : ∀ x j, hsNormSq 0 (driftCoeff D (ρ x) j) ≤ K)
    (hbc : ∀ j q, Tendsto (fun x => driftCoeff D (ρ x) j q) l (𝓝 (driftCoeff D ρ0 j q)))
    (Fa : α → Coeff d) (G : Coeff d) (hFa : ∀ x, MemHs 1 (Fa x)) (hG : MemHs 1 G)
    (hF : Tendsto (fun x => hsNormSq 1 (Fa x - G)) l (𝓝 0)) (k : Lattice d) :
    Tendsto (fun x => forwardGen D (ρ x) (Fa x) k) l (𝓝 (forwardGen D ρ0 G k)) := by
  unfold forwardGen
  refine Tendsto.sub (Tendsto.add ?_ ?_) ?_
  · simp only [laplaceCoeff]
    exact ((tendsto_coord_of_hs1 hFa hG hF k).const_mul _).const_mul _
  · unfold transportCoeff
    exact tendsto_finsetSum _ fun j _ => tendsto_mulCoeff_deriv_strong _ _ K hK0 (fun x => hb x j)
      (fun x => hbK x j) (hbc j) Fa G hFa hG hF j k
  · unfold nonlocalCoeff
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    have := tendsto_mulCoeff_deriv_strong (fun x => coeffOf (ρ x)) (coeffOf ρ0) K hK0 hρ hρK hρc
      Fa G hFa hG hF j k
    simp only [gradRieszCoeff, derivCoeff, rieszMult]
    exact (this.const_mul _).const_mul _ |>.const_mul _


theorem tsub_mem_Icc {t T σ : ℝ} (ht : t ∈ Set.Ioc 0 T) (hσ : σ ∈ Set.Icc 0 t) :
    t - σ ∈ Set.Icc 0 T :=
  ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩

/-- The coordinates of `σ ↦ 𝓛^{t-σ} F(σ)` are continuous on `[0,t]`. -/
theorem gen_coord_continuousOn {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d}
    {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ} (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) {F : ℝ → Coeff d} (hcont : ContinuousInHs ((m : ℝ) + 2) F t)
    (k : Lattice d) :
    ContinuousOn (fun σ => forwardGen D (μ (t - σ)) (F σ) k) (Set.Icc 0 t) := by
  obtain ⟨K, hK⟩ := exists_coeff_bound D μ m Λ VB T hA.hμ hA.hV
  have hK0 : 0 ≤ K := (hsNormSq_nonnegE 0 _).trans (hK t ⟨ht.1.le, ht.2⟩).2.1
  have hcoef : ∀ q, ContinuousOn (fun σ => coeffOf (μ (t - σ)) q) (Set.Icc 0 t) := by
    intro q
    refine (coeffOf_continuousOn hA.hμ q).comp (continuousOn_const.sub continuousOn_id) ?_
    intro σ hσ
    exact tsub_mem_Icc ht hσ
  have hdrift : ∀ j q, ContinuousOn (fun σ => driftCoeff D (μ (t - σ)) j q) (Set.Icc 0 t) :=
    fun j q => continuousOn_drift D (fun σ => μ (t - σ)) hcoef j q
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  rw [continuousOn_iff_continuous_restrict, continuous_iff_continuousAt]
  intro p
  have hp : p.1 ∈ Set.Icc (0 : ℝ) t := p.2
  have hF : Tendsto (fun x : Set.Icc (0 : ℝ) t => hsNormSq 1 (F x.1 - F p.1)) (𝓝 p) (𝓝 0) := by
    have h := tendsto_hsNormSq_sub hcont hp
    rw [tendsto_nhdsWithin_iff_subtype hp] at h
    refine squeeze_zero (fun x => hsNormSq_nonnegE _ _) (fun x => ?_) h
    obtain ⟨hmem, -⟩ := memHs_sub_sq (hcont.1 x.1 x.2) (hcont.1 p.1 hp)
    exact hsNormSq_mono hm1 hmem
  have key := tendsto_forwardGen_both (l := 𝓝 p) D (fun x : Set.Icc (0 : ℝ) t => μ (t - x.1))
    (μ (t - p.1)) K hK0 (fun x => (hK _ (tsub_mem_Icc ht x.2)).1)
    (fun x => (hK _ (tsub_mem_Icc ht x.2)).2.1)
    (fun q => ((hcoef q).restrict).continuousAt.tendsto)
    (fun x j => ((hK _ (tsub_mem_Icc ht x.2)).2.2 j).1)
    (fun x j => ((hK _ (tsub_mem_Icc ht x.2)).2.2 j).2)
    (fun j q => ((hdrift j q).restrict).continuousAt.tendsto)
    (fun x : Set.Icc (0 : ℝ) t => F x.1) (F p.1)
    (fun x => (hcont.1 x.1 x.2).mono hm1) ((hcont.1 p.1 hp).mono hm1) hF k
  exact key


/-! ### Calculus -/

theorem hasDerivWithinAt_of_primitive_real {t : ℝ} {g f : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc 0 t)) (c : ℝ)
    (hf : ∀ τ ∈ Set.Icc 0 t, f τ = c + ∫ σ in (0 : ℝ)..τ, g σ) :
    ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt f (g τ) (Set.Icc 0 t) τ := by
  intro τ hτ
  have ht0 : 0 ≤ t := hτ.1.trans hτ.2
  set B : ℝ → ℝ := Set.IccExtend ht0 (fun s : Set.Icc (0 : ℝ) t => g s) with hBdef
  have hB : Continuous B := hg.domRestrict.Icc_extend'
  have hBg : ∀ s ∈ Set.Icc (0 : ℝ) t, B s = g s := fun s hs => Set.IccExtend_of_mem ht0 _ hs
  have h1 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, B s) (B τ) τ :=
    (hB.integral_hasStrictDerivAt 0 τ).hasDerivAt
  have h2 := (h1.const_add c).hasDerivWithinAt (s := Set.Icc 0 t)
  rw [hBg τ hτ] at h2
  have hint : ∀ u ∈ Set.Icc (0 : ℝ) t, ∫ s in (0 : ℝ)..u, g s = ∫ s in (0 : ℝ)..u, B s := by
    intro u hu
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [hBg s (Set.uIcc_subset_Icc ⟨le_rfl, ht0⟩ hu hs)]
  exact h2.congr (fun u hu => by rw [hf u hu, hint u hu]) (by rw [hf τ hτ, hint τ hτ])

/-- Derivative of the box-truncated energy. -/
theorem hasDeriv_trunc_energy {t : ℝ} {n : ℕ} (m : ℝ) (F g : ℝ → Coeff d)
    (hd : ∀ k, ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt (fun τ => F τ k) (g τ k) (Set.Icc 0 t) τ) :
    ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt (fun τ => hsNormSq m (truncCoeff n (F τ)))
      (2 * (hsInner m (g τ) (truncCoeff n (F τ))).re) (Set.Icc 0 t) τ := by
  intro τ hτ
  have e : (fun τ => hsNormSq m (truncCoeff n (F τ))) =
      fun τ => ∑ k ∈ boxFinset d n, sobWeight m k * ‖F τ k‖ ^ 2 := by
    funext τ'
    rw [hsNormSq_trig (isTrigPoly_truncCoeff n (F τ'))]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [truncCoeff, mem_boxFinset.1 hk]
  rw [e]
  have hs := HasDerivWithinAt.fun_sum (u := boxFinset d n)
    (fun k _ => ((hd k τ hτ).norm_sq).const_mul (sobWeight m k))
  convert hs using 1
  rw [hsInner_trig (isTrigPoly_truncCoeff n (F τ)), Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : truncCoeff n (F τ) k = F τ k := by simp [truncCoeff, mem_boxFinset.1 hk]
  rw [hk', Complex.re_ofReal_mul, Complex.inner]
  ring


/-- **Differentiation of `½‖F‖²_{H^m}`** along a path whose coordinates solve the integrated
equation, abstractly: `F` bounded in `H^{m+2}`, `g` bounded in `H^m`, coordinatewise `C¹`. -/
theorem hasDeriv_energy_abstract {t : ℝ} (m : ℝ) (F g : ℝ → Coeff d) (Kg B : ℝ)
    (hKg0 : 0 ≤ Kg) (hB0 : 0 ≤ B)
    (hmemF : ∀ σ ∈ Set.Icc 0 t, MemHs (m + 2) (F σ))
    (hB : ∀ σ ∈ Set.Icc 0 t, hsNormSq (m + 2) (F σ) ≤ B)
    (hmemg : ∀ σ ∈ Set.Icc 0 t, MemHs m (g σ))
    (hKg : ∀ σ ∈ Set.Icc 0 t, hsNormSq m (g σ) ≤ Kg)
    (hcF : ∀ k, ContinuousOn (fun σ => F σ k) (Set.Icc 0 t))
    (hcg : ∀ k, ContinuousOn (fun σ => g σ k) (Set.Icc 0 t))
    (hd : ∀ k, ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt (fun τ => F τ k) (g τ k) (Set.Icc 0 t) τ) :
    ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt (fun τ' => (1 / 2 : ℝ) * hsNormSq m (F τ'))
      (hsInner m (g τ) (F τ)).re (Set.Icc 0 t) τ := by
  have hm2 : m ≤ m + 2 := by linarith
  have hmemF' : ∀ σ ∈ Set.Icc 0 t, MemHs m (F σ) := fun σ hσ => (hmemF σ hσ).mono hm2
  set Sn : ℕ → ℝ → ℝ := fun n σ => (hsInner m (g σ) (truncCoeff n (F σ))).re with hSn
  set S : ℝ → ℝ := fun σ => (hsInner m (g σ) (F σ)).re with hS
  -- continuity of Sn
  have hSn_cont : ∀ n, ContinuousOn (Sn n) (Set.Icc 0 t) := by
    intro n
    have e : ∀ σ, Sn n σ = ∑ k ∈ boxFinset d n, sobWeight m k * (g σ k * conj (F σ k)).re := by
      intro σ
      simp only [hSn]
      rw [hsInner_trig (isTrigPoly_truncCoeff n (F σ)), Complex.re_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : truncCoeff n (F σ) k = F σ k := by simp [truncCoeff, mem_boxFinset.1 hk]
      rw [hk', Complex.re_ofReal_mul]
    rw [show Sn n = fun σ => ∑ k ∈ boxFinset d n, sobWeight m k * (g σ k * conj (F σ k)).re from
      funext e]
    refine continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ?_
    exact Complex.continuous_re.comp_continuousOn
      ((hcg k).mul (Complex.continuous_conj.comp_continuousOn (hcF k)))
  -- uniform estimate
  set ε : ℕ → ℝ := fun n => Real.sqrt Kg * Real.sqrt (tailConst n * B) with hε
  have hbd : ∀ n, ∀ σ ∈ Set.Icc (0 : ℝ) t, |S σ - Sn n σ| ≤ ε n := by
    intro n σ hσ
    obtain ⟨htm, htb⟩ := hsNormSq_tail_le m n (hmemF σ hσ)
    have hmt : MemHs m (truncCoeff n (F σ)) := memHs_of_isTrigPolyE (isTrigPoly_truncCoeff n _) _
    have e : S σ - Sn n σ = (hsInner m (g σ) (F σ - truncCoeff n (F σ))).re := by
      simp only [hS, hSn]
      rw [hsInner_sub_right (hmemg σ hσ) (hmemF' σ hσ) hmt, Complex.sub_re]
    rw [e]
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_hsInner_le (hmemg σ hσ) htm).trans ?_
    refine mul_le_mul (Real.sqrt_le_sqrt (hKg σ hσ)) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    exact htb.trans (mul_le_mul_of_nonneg_left (hB σ hσ) (tailConst_nonneg n))
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => tailConst n * B) atTop (𝓝 0) := by
      simpa using tendsto_tailConst.mul_const B
    have h2 := ((Real.continuous_sqrt.tendsto 0).comp h1).const_mul (Real.sqrt Kg)
    simpa [hε] using h2
  have hε0 : ∀ n, 0 ≤ ε n := fun n => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hunif : TendstoUniformlyOn Sn S atTop (Set.Icc 0 t) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro e he
    filter_upwards [hεt.eventually_lt_const he] with n hn σ hσ
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hbd n σ hσ) hn
  have hS_cont : ContinuousOn S (Set.Icc 0 t) :=
    hunif.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall hSn_cont))
  -- the energy identity for the truncations
  intro τ hτ
  set y : ℝ → ℝ := fun τ' => (1 / 2 : ℝ) * hsNormSq m (F τ') with hy
  set yn : ℕ → ℝ → ℝ := fun n τ' => (1 / 2 : ℝ) * hsNormSq m (truncCoeff n (F τ')) with hyn
  have hyn_deriv : ∀ n, ∀ x ∈ Set.Icc (0 : ℝ) t, HasDerivWithinAt (yn n) (Sn n x) (Set.Icc 0 t) x := by
    intro n x hx
    have := (hasDeriv_trunc_energy (n := n) m F g hd x hx).const_mul (1 / 2 : ℝ)
    convert this using 1
    show (hsInner m (g x) (truncCoeff n (F x))).re = (1 / 2 : ℝ) * (2 * (hsInner m (g x) (truncCoeff n (F x))).re)
    ring
  have hFTC : ∀ n, ∀ x ∈ Set.Icc (0 : ℝ) t, ∫ u in (0 : ℝ)..x, Sn n u = yn n x - yn n 0 := by
    intro n x hx
    have ht0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, hx.1.trans hx.2⟩
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx.1 ?_ ?_ ?_
    · intro u hu
      exact (hyn_deriv n u ⟨hu.1, hu.2.trans hx.2⟩).continuousWithinAt.mono
        (Set.Icc_subset_Icc le_rfl hx.2)
    · intro u hu
      have hu' : u ∈ Set.Icc (0 : ℝ) t := ⟨hu.1.le, hu.2.le.trans hx.2⟩
      have hnhds : Set.Icc (0 : ℝ) t ∈ 𝓝 u := Icc_mem_nhds hu.1 (lt_of_lt_of_le hu.2 hx.2)
      exact ((hyn_deriv n u hu').hasDerivAt hnhds).hasDerivWithinAt
    · refine ContinuousOn.intervalIntegrable ?_
      refine (hSn_cont n).mono ?_
      rw [Set.uIcc_of_le hx.1]
      exact Set.Icc_subset_Icc le_rfl hx.2
  have hint_conv : ∀ x ∈ Set.Icc (0 : ℝ) t,
      Tendsto (fun n => ∫ u in (0 : ℝ)..x, Sn n u) atTop (𝓝 (∫ u in (0 : ℝ)..x, S u)) := by
    intro x hx
    have hsub : Set.uIcc (0 : ℝ) x ⊆ Set.Icc 0 t := by
      rw [Set.uIcc_of_le hx.1]; exact Set.Icc_subset_Icc le_rfl hx.2
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ n, ‖(∫ u in (0 : ℝ)..x, Sn n u) - ∫ u in (0 : ℝ)..x, S u‖ ≤ ε n * |x - 0| := by
      intro n
      rw [← intervalIntegral.integral_sub
        ((hSn_cont n).mono hsub |>.intervalIntegrable)
        ((hS_cont.mono hsub).intervalIntegrable), ]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
      have hu' : u ∈ Set.Icc (0 : ℝ) t := by
        rw [Set.uIoc_of_le hx.1] at hu
        exact ⟨hu.1.le, hu.2.trans hx.2⟩
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hbd n u hu'
    refine squeeze_zero (fun n => norm_nonneg _) hb ?_
    simpa using hεt.mul_const |x - 0|
  have hylim : ∀ x ∈ Set.Icc (0 : ℝ) t, Tendsto (fun n => yn n x) atTop (𝓝 (y x)) := by
    intro x hx
    simpa [hyn, hy] using (tendsto_hsNormSq_trunc m (F x) (hmemF' x hx)).const_mul (1 / 2 : ℝ)
  have hrep : ∀ x ∈ Set.Icc (0 : ℝ) t, y x = y 0 + ∫ u in (0 : ℝ)..x, S u := by
    intro x hx
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, hx.1.trans hx.2⟩
    have h1 : Tendsto (fun n => yn n x - yn n 0) atTop (𝓝 (y x - y 0)) :=
      (hylim x hx).sub (hylim 0 h0)
    have h2 : Tendsto (fun n => yn n x - yn n 0) atTop (𝓝 (∫ u in (0 : ℝ)..x, S u)) :=
      (hint_conv x hx).congr fun n => hFTC n x hx
    have := tendsto_nhds_unique h1 h2
    linarith
  exact hasDerivWithinAt_of_primitive_real hS_cont (y 0) hrep τ hτ


/-- **Prop 3.13 (a)**: differentiation of `½‖F(τ)‖²_{H^m}` along a regular solution. -/
theorem energy_deriv (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    {φc : Coeff d} {F : ℝ → Coeff d} (hF : IsForwardSolution D μ t φc F)
    (hcont : ContinuousInHs ((m : ℝ) + 2) F t) :
    ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt (fun τ' => (1 / 2 : ℝ) * hsNormSq (m : ℝ) (F τ'))
      (hsInner (m : ℝ) (forwardGen D (μ (t - τ)) (F τ)) (F τ)).re (Set.Icc 0 t) τ := by
  obtain ⟨K, hK0, hK⟩ := forwardGen_hs_bound hd s hs0 hsd m MB Λ VB
  obtain ⟨B, hB0, hB⟩ := bounded_of_continuousInHs hcont
  have hgen : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      MemHs (m : ℝ) (forwardGen D (μ (t - σ)) (F σ)) ∧
      hsNormSq (m : ℝ) (forwardGen D (μ (t - σ)) (F σ)) ≤ (3 * D.invβ ^ 2 + K) * hsNormSq ((m : ℝ) + 2) (F σ) := by
    intro σ hσ
    have hr := tsub_mem_Icc ht hσ
    exact hK D hA.hs hA.hM hA.hV (μ (t - σ)) (hA.hμ.prob _ hr) (hA.hμ.smooth _ hr)
      (hA.hμ.bound _ hr) (F σ) (hcont.1 σ hσ)
  have hc3 : 0 ≤ 3 * D.invβ ^ 2 + K := by positivity
  refine hasDeriv_energy_abstract (m : ℝ) F (fun σ => forwardGen D (μ (t - σ)) (F σ))
    ((3 * D.invβ ^ 2 + K) * B) B (by positivity) hB0 hcont.1 hB
    (fun σ hσ => (hgen σ hσ).1)
    (fun σ hσ => (hgen σ hσ).2.trans (mul_le_mul_of_nonneg_left (hB σ hσ) hc3))
    (fun k => continuousOn_coord_of_continuousInHs hcont k)
    (fun k => gen_coord_continuousOn hA ht hcont k) ?_
  intro k
  exact hasDerivWithinAt_of_primitive (gen_coord_continuousOn hA ht hcont k) (φc k) (hF.eq k) 

end HRS.PDE.ET
