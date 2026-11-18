import HRS.MC.S7FCW9Mom
import HRS.MC.S7FCW2
import HRS.MC.S7FCW5

/-!
# S7FCW9: relocated proof of `s7_FC_C4_field_all_t` (FC-C4, the `t`-free limit field)

The statement is copied verbatim from `HRS/MC/S7FCPlan.lean` (namespace `HRS.MC.Sec7.FCPlan`); it is proved here
in namespace `HRS.MC.Sec7.S7FCW9` and tied to the frozen statement in `HRS/MC/S7FCW9Tie.lean`.

Route.  (1) `η'` from C3, `K` from C1; the Wick coefficients do not see the density (`WCI.wci_proof`), so the
measurability in `t` is trivial; the uniform tails come from `qrs_hd_commutator_tail` on the cubes.
(2) `Q κ` from C2 for every nonzero frequency `κ`.  (3) `B t ω := ofSeq r (Q · t ω)`: joint measurability by
`S7FCW9_measurable_ofSeq`; honesty a.s. and the eval identity from the monotone bound of the weighted partial
sums (`lintegral_iSup`), with the `L^{2m}` bounds of `qrs_chaos_lp_lim` (`F = ∅`) and the finite Jensen
inequality of `S7FCW9Mom`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW9

open HRS HRS.Sec7 HRS.MC.QRSpec

variable {d : ℕ}

/-- Jensen weight `a_κ = ĵ_κ^{-(2r-(d+3))}`. -/
noncomputable def S7FCW9_wt (d : ℕ) (r : ℝ) (κ : NonzeroLattice d) : ℝ :=
  Lattice.jp κ.1 ^ (-(2 * r - ((d : ℝ) + 3)))

/-- Jensen scale `σ_κ = ĵ_κ^{d+3}`. -/
noncomputable def S7FCW9_sg (d : ℕ) (κ : NonzeroLattice d) : ℝ :=
  Lattice.jp κ.1 ^ ((d : ℝ) + 3)

theorem S7FCW9_wt_pos (r : ℝ) (κ : NonzeroLattice d) : 0 < S7FCW9_wt d r κ :=
  Real.rpow_pos_of_pos (Torus.jp_pos κ.1) _

theorem S7FCW9_sg_pos (κ : NonzeroLattice d) : 0 < S7FCW9_sg d κ :=
  Real.rpow_pos_of_pos (Torus.jp_pos κ.1) _

theorem S7FCW9_weight_eq (r j : ℝ) (hj : 0 < j) (x : ℝ) (d : ℕ) :
    j ^ (-(2 * r - ((d : ℝ) + 3))) * (x ^ 2 / j ^ ((d : ℝ) + 3)) = (j ^ (-r) * x) ^ 2 := by
  have hp : (j ^ (-r)) ^ 2 = j ^ (-(2 * r)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hj.le]
    congr 1
    push_cast
    ring
  have hs : j ^ (-(2 * r - ((d : ℝ) + 3))) = j ^ (-(2 * r)) * j ^ ((d : ℝ) + 3) := by
    rw [← Real.rpow_add hj]
    congr 1
    ring
  have hne : j ^ ((d : ℝ) + 3) ≠ 0 := (Real.rpow_pos_of_pos hj _).ne'
  rw [mul_pow, hp, hs]
  field_simp

theorem S7FCW9_rpow_le_one_add_sq (x q : ℝ) (hx : 0 ≤ x) (h1 : 1 ≤ q) (h2 : q ≤ 2) :
    x ^ q ≤ 1 + x ^ (2 * (1 : ℝ)) := by
  rw [show (2 : ℝ) * 1 = 2 by norm_num, Real.rpow_two]
  rcases le_total x 1 with hx1 | hx1
  · have h := Real.rpow_le_one hx hx1 (by linarith : (0 : ℝ) ≤ q)
    nlinarith [sq_nonneg x]
  · have h := Real.rpow_le_rpow_of_exponent_le hx1 h2
    rw [Real.rpow_two] at h
    nlinarith [sq_nonneg x]

set_option maxHeartbeats 4000000 in
theorem s7_FC_C4_field_all_t_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) {Ω' : Type}
    [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    ∃ B : ℝ → Ω' → NegSobolev d r, Measurable (Function.uncurry B) ∧
      (∀ t : ℝ, 0 ≤ t →
        IsWickQuadraticField R.D.s P' (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t)) ∧
      ∀ q : ℝ, 1 ≤ q → ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
        Integrable (fun ω => ‖B t ω‖ ^ q) P' ∧ ∫ ω, ‖B t ω‖ ^ q ∂P' ≤ C := by
  -- Step 0: constants, the good version `η'` of the field, and the regime bounds
  obtain ⟨K, hK0, hKb⟩ := HRS.MC.Sec7.S7FCW2.s7_FC_C1_coeffs_proof R r hr
  obtain ⟨η', hXm, hae, -⟩ := HRS.MC.Sec7.S7FCW2.s7_FC_C3_version_proof R r P' η hη
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast R.hd
  have hsd : R.D.s < (d : ℝ) := by linarith [R.hs]
  have hs' : R.D.s < (d : ℝ) / 2 := R.hs
  obtain ⟨M₀, hM₀, hbd⟩ : ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ t : ℝ, 0 ≤ t → ∀ x, R.ρ t x ≤ M₀ := by
    obtain ⟨m₀, M₀, hm₀, hb⟩ := R.bounds
    exact ⟨max M₀ 1, lt_max_of_lt_right one_pos, fun t ht x => (hb t ht x).2.trans (le_max_left _ _)⟩
  have hdens : ∀ t : ℝ, 0 ≤ t → IsProbDensity (R.ρ t) := fun t ht =>
    (R.mf (t + 1) (by linarith)).density t ⟨ht, by linarith⟩
  obtain ⟨Cq, hCq0, hq⟩ := HRS.MC.QRSpec.Hd.qrs_hd_commutator_tail_proof R.D.s R.D.hs0 R.hs R.hd
  have hMb : ∀ t : ℝ, 0 ≤ t → ∀ x, R.ρ t x ≤ M₀ := hbd
  -- the fixed exponent of the tails
  obtain ⟨e, he, hedef⟩ : ∃ e : ℝ, 0 < e ∧ e = (d : ℝ) - 2 * R.D.s :=
    ⟨_, by linarith, rfl⟩
  -- Step 1: the Wick coefficients do not depend on the time (the density is absorbed by `WCI.wci_proof`)
  obtain ⟨μ', hμ'⟩ : ∃ μ' : ℝ → Measure (Torus d), ∀ t, μ' t = withDensityReal (R.ρ (max t 0)) :=
    ⟨_, fun _ => rfl⟩
  have hconst : ∀ (κ : NonzeroLattice d) (t : ℝ) (l l' : NonzeroLattice d),
      wickCoeff (μ' t) (hTransport d R.D.s (Torus.realMode κ)) l l' =
        wickCoeff (μ' 0) (hTransport d R.D.s (Torus.realMode κ)) l l' := by
    intro κ t l l'
    rw [hμ', hμ']
    exact HRS.MC.WCI.wci_proof R.D.s R.D.hs0 hsd (R.ρ (max t 0)) (R.ρ (max 0 0))
      (hdens _ (le_max_right _ _)) (hdens _ (le_max_right _ _)) M₀
      (fun x => hMb _ (le_max_right _ _) x) (fun x => hMb _ (le_max_right _ _) x)
      (Torus.realMode κ) (HRS.FieldSingAux.isSmooth_realMode κ) l l'
  have hcm : ∀ κ : NonzeroLattice d, ∀ l l' : NonzeroLattice d,
      Measurable fun t => wickCoeff (μ' t) (hTransport d R.D.s (Torus.realMode κ)) l l' := by
    intro κ l l'
    have e1 : (fun t => wickCoeff (μ' t) (hTransport d R.D.s (Torus.realMode κ)) l l') =
        fun _ => wickCoeff (μ' 0) (hTransport d R.D.s (Torus.realMode κ)) l l' :=
      funext fun t => hconst κ t l l'
    rw [e1]
    exact measurable_const
  -- Step 2: the summability and the uniform tails, for `t ≥ 0`
  have hAt : ∀ κ : NonzeroLattice d, ∀ t : ℝ, 0 ≤ t →
      Summable fun p : NonzeroLattice d × NonzeroLattice d =>
        wickCoeff (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode κ)) p.1 p.2 ^ 2 :=
    fun κ t ht => (hq (R.ρ t) (hdens t ht) M₀ (hMb t ht) κ 1 le_rfl).1
  have hTt : ∀ κ : NonzeroLattice d, ∀ t : ℝ, 0 ≤ t →
      tailHS (wickCoeff (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode κ))) ∅ ≤
        Cq * Lattice.jp κ.1 ^ ((d : ℝ) + 3) :=
    fun κ t ht => (hq (R.ρ t) (hdens t ht) M₀ (hMb t ht) κ 1 le_rfl).2.1
  have hAt' : ∀ κ : NonzeroLattice d, ∀ t : ℝ, 0 ≤ t →
      Summable fun p : NonzeroLattice d × NonzeroLattice d =>
        wickCoeff (μ' t) (hTransport d R.D.s (Torus.realMode κ)) p.1 p.2 ^ 2 := by
    intro κ t ht
    rw [hμ', max_eq_left ht]
    exact hAt κ t ht
  obtain ⟨ε, hεdef⟩ : ∃ ε : NonzeroLattice d → ℕ → ℝ, ∀ κ n, ε κ n =
      Cq * Lattice.jp κ.1 ^ ((d : ℝ) + 3) * (((n + 1 : ℕ) : ℝ)) ^ (-e) := ⟨_, fun _ _ => rfl⟩
  have htail : ∀ κ : NonzeroLattice d, ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ,
      tailHS (wickCoeff (μ' t) (hTransport d R.D.s (Torus.realMode κ)))
        (S7FCW9_cube d (n + 1)) ≤ ε κ n := by
    intro κ t ht n
    rw [hμ', max_eq_left ht, hεdef, hedef]
    have h3 := (hq (R.ρ t) (hdens t ht) M₀ (hMb t ht) κ (n + 1) (by omega)).2.2
    exact h3 (S7FCW9_cube d (n + 1)) fun a ha => (S7FCW9_mem_cube_iff (n + 1) a).2 ha
  have hε : ∀ κ : NonzeroLattice d, Tendsto (ε κ) atTop (𝓝 0) := by
    intro κ
    have h1 := ((tendsto_rpow_neg_atTop he).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).const_mul
      (Cq * Lattice.jp κ.1 ^ ((d : ℝ) + 3))
    rw [mul_zero] at h1
    refine h1.congr fun n => ?_
    rw [hεdef]
    rfl
  -- Step 3: the Wick limits `Q κ` of the good version, for each frequency `κ`
  have hC2 : ∀ κ : NonzeroLattice d, ∃ Q : ℝ → Ω' → ℝ, Measurable (Function.uncurry Q) ∧
      ∀ t : ℝ, 0 ≤ t → IsHalfWick P' (η' t) (μ' t) (hTransport d R.D.s (Torus.realMode κ)) (Q t) := by
    intro κ
    refine HRS.MC.Sec7.S7FCW5.s7_FC_C2_wick_param_proof P' r η' hXm K ?_ μ'
      (hTransport d R.D.s (Torus.realMode κ)) (fun k l => hcm κ k l)
      (fun t ht => hAt' κ t ht) (fun n => S7FCW9_cube d (n + 1))
      (fun n => S7FCW9_cube_mono (show n + 1 ≤ n + 1 + 1 by omega)) (ε κ) (hε κ)
      (fun t ht n => htail κ t ht n)
    intro t ht
    obtain ⟨h1, h2⟩ := hKb P' η hη t ht
    exact ⟨S7FCW9_hfgc_congr (hae t ht).symm h1, S7FCW9_mcb_congr (hae t ht).symm h2⟩
  choose Q hQm hQ using hC2
  have hQt : ∀ κ : NonzeroLattice d, ∀ t : ℝ, 0 ≤ t →
      IsHalfWick P' (η' t) (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode κ)) (Q κ t) := by
    intro κ t ht
    have h := hQ κ t ht
    rw [hμ', max_eq_left ht] at h
    exact h
  have hpt : ∀ t : ℝ, Measurable fun ω : Ω' => ((t, ω) : ℝ × Ω') :=
    fun t => measurable_const.prodMk measurable_id
  have hQt_m : ∀ κ : NonzeroLattice d, ∀ t : ℝ, Measurable fun ω => Q κ t ω :=
    fun κ t => (hQm κ).comp (hpt t)
  -- the finite-Gaussian and covariance properties of the good version, for `t ≥ 0`
  have hG : ∀ t : ℝ, 0 ≤ t → HasFiniteGaussianCoeffs P' (η' t) ∧ ModeCovBound P' (η' t) K :=
    fun t ht => ⟨S7FCW9_hfgc_congr (hae t ht).symm (hKb P' η hη t ht).1,
      S7FCW9_mcb_congr (hae t ht).symm (hKb P' η hη t ht).2⟩
  -- Step 4: the Jensen weights and the monotone partial sums
  have hwsum : Summable fun κ : NonzeroLattice d => S7FCW9_wt d r κ :=
    S7FCW9_summable_jp (2 * r - ((d : ℝ) + 3)) (by linarith [hr, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (∑' κ : NonzeroLattice d, S7FCW9_wt d r κ) + 1 := ⟨_, rfl⟩
  have hA0 : 0 < A := by
    rw [hAdef]
    have hts : (0 : ℝ) ≤ ∑' κ : NonzeroLattice d, S7FCW9_wt d r κ :=
      tsum_nonneg fun κ => (S7FCW9_wt_pos r κ).le
    linarith
  have hAS : ∀ S : Finset (NonzeroLattice d), ∑ κ ∈ S, S7FCW9_wt d r κ ≤ A := by
    intro S
    rw [hAdef]
    have := Summable.sum_le_tsum S (fun κ _ => (S7FCW9_wt_pos r κ).le) hwsum
    linarith
  obtain ⟨Yf, hYf⟩ : ∃ Yf : ℝ → ℕ → Ω' → ℝ, ∀ t n ω, Yf t n ω =
      ∑ κ ∈ S7FCW9_cube d n, S7FCW9_wt d r κ * (Q κ t ω ^ 2 / S7FCW9_sg d κ) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hYfnn : ∀ t n ω, 0 ≤ Yf t n ω := fun t n ω => by
    rw [hYf]
    exact Finset.sum_nonneg fun κ _ => mul_nonneg (S7FCW9_wt_pos r κ).le
      (div_nonneg (sq_nonneg _) (S7FCW9_sg_pos κ).le)
  have hYfle : ∀ t ω, Monotone fun n => Yf t n ω := fun t ω =>
    monotone_nat_of_le_succ fun n => by
      show Yf t n ω ≤ Yf t (n + 1) ω
      rw [hYf, hYf]
      exact Finset.sum_le_sum_of_subset_of_nonneg (S7FCW9_cube_mono (Nat.le_succ n))
        fun κ _ _ => mul_nonneg (S7FCW9_wt_pos r κ).le
          (div_nonneg (sq_nonneg _) (S7FCW9_sg_pos κ).le)
  have hYfm : ∀ t n, Measurable fun ω => Yf t n ω := fun t n => by
    have e' : (fun ω => Yf t n ω) = fun ω => ∑ κ ∈ S7FCW9_cube d n,
        S7FCW9_wt d r κ * (Q κ t ω ^ 2 / S7FCW9_sg d κ) := funext fun ω => hYf t n ω
    rw [e']
    exact Finset.measurable_sum _ fun κ _ =>
      measurable_const.mul (((hQt_m κ t).pow_const 2).div_const _)
  -- Step 5: the `L^{2m}` bounds of the Wick limits and the Jensen bound of the partial sums
  have hmomD : ∀ m : ℝ, 1 ≤ m → ∃ D : ℝ, 0 ≤ D ∧ ∀ κ : NonzeroLattice d, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (|Q κ t ω| ^ (2 * m)) ∂P' ≤
        ENNReal.ofReal (S7FCW9_sg d κ ^ m * D) := by
    intro m hm
    obtain ⟨Cp, hCp0, hCp⟩ := HRS.MC.QRSpec.Chaos.qrs_chaos_lp_lim_proof (2 * m) (by linarith)
    refine ⟨(Cp * K) ^ (2 * m) * Cq ^ m,
      mul_nonneg (Real.rpow_nonneg (mul_nonneg hCp0.le hK0) _) (Real.rpow_nonneg hCq0.le _), ?_⟩
    intro κ t ht
    have hres := hCp d r P' (η' t) (hG t ht).1 K hK0 (hG t ht).2
      (withDensityReal (R.ρ t)) (hTransport d R.D.s (Torus.realMode κ)) (Q κ t) (hQt κ t ht)
      (hQt_m κ t).aestronglyMeasurable (hAt κ t ht) ∅
    have hz : (fun ω => Q κ t ω - wickSection P' (η' t) (withDensityReal (R.ρ t))
        (hTransport d R.D.s (Torus.realMode κ)) ∅ ω) = Q κ t := by
      funext ω
      simp [wickSection]
    rw [hz] at hres
    have hsq : Real.sqrt (tailHS (wickCoeff (withDensityReal (R.ρ t))
        (hTransport d R.D.s (Torus.realMode κ))) ∅) ≤ Real.sqrt (Cq * S7FCW9_sg d κ) :=
      Real.sqrt_le_sqrt (hTt κ t ht)
    have hres' := hres.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hsq (mul_nonneg hCp0.le hK0)))
    have hL := S7FCW9_lint_of_chaos P' (Q κ t) (2 * m) Cp K (Cq * S7FCW9_sg d κ) (by linarith)
      hK0 hCp0.le (mul_nonneg hCq0.le (S7FCW9_sg_pos κ).le) hres'
    have e' : (Cp * K) ^ (2 * m) * (Cq * S7FCW9_sg d κ) ^ (2 * m / 2)
        = S7FCW9_sg d κ ^ m * ((Cp * K) ^ (2 * m) * Cq ^ m) := by
      rw [show 2 * m / 2 = m by ring, Real.mul_rpow hCq0.le (S7FCW9_sg_pos κ).le]
      ring
    exact hL.trans (ENNReal.ofReal_le_ofReal e'.le)
  have hsupG : ∀ m : ℝ, 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ⨆ n, ENNReal.ofReal ((Yf t n ω) ^ m) ∂P' ≤ ENNReal.ofReal C := by
    intro m hm
    obtain ⟨D, hD0, hD⟩ := hmomD m hm
    refine ⟨A ^ m * D, mul_nonneg (Real.rpow_nonneg hA0.le _) hD0, fun t ht => ?_⟩
    have hm0 : 0 ≤ m := by linarith
    have hmeas : ∀ n, Measurable fun ω => ENNReal.ofReal ((Yf t n ω) ^ m) := fun n =>
      ENNReal.measurable_ofReal.comp ((hYfm t n).pow_const m)
    have hmono : Monotone fun n ω => ENNReal.ofReal ((Yf t n ω) ^ m) := fun n n' hnn' ω =>
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hYfnn t n ω) (hYfle t ω hnn') hm0)
    refine (le_of_eq (lintegral_iSup hmeas hmono)).trans (iSup_le fun n => ?_)
    have hJ := S7FCW9_lint_jensen P' (S7FCW9_cube d n) (S7FCW9_wt d r) (S7FCW9_sg d)
      (fun κ ω => Q κ t ω) A D m (fun κ => hQt_m κ t) (fun κ => (S7FCW9_wt_pos r κ).le)
      (fun κ => S7FCW9_sg_pos κ) (hAS _) hA0 hm hD0 (fun κ _ => hD κ t ht)
    simp only [hYf]
    exact hJ
  -- Step 6: a.e. honesty of the weighted coefficients (the `m = 1` bound)
  have hgood : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P',
      Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) * Q k t ω) 2 := by
    intro t ht
    obtain ⟨C1, hC1, hC1b⟩ := hsupG 1 le_rfl
    have hmeas1 : Measurable fun ω => ⨆ n, ENNReal.ofReal ((Yf t n ω) ^ (1 : ℝ)) :=
      Measurable.iSup fun n => ENNReal.measurable_ofReal.comp ((hYfm t n).pow_const (1 : ℝ))
    have hfin : ∀ᵐ ω ∂P', (⨆ n, ENNReal.ofReal ((Yf t n ω) ^ (1 : ℝ))) < ⊤ :=
      ae_lt_top' hmeas1.aemeasurable (lt_of_le_of_lt (hC1b t ht) ENNReal.ofReal_lt_top).ne
    filter_upwards [hfin] with ω hω
    refine (S7FCW9_memℓp_two_iff_bdd _).2
      ⟨⌈(⨆ n, ENNReal.ofReal ((Yf t n ω) ^ (1 : ℝ))).toReal⌉₊, fun n => ?_⟩
    have hsumg : ∑ k ∈ S7FCW9_cube d n, (Lattice.jp k.1 ^ (-r) * Q k t ω) ^ 2 = Yf t n ω := by
      rw [hYf]
      exact Finset.sum_congr rfl fun κ _ =>
        (S7FCW9_weight_eq r (Lattice.jp κ.1) (Torus.jp_pos κ.1) (Q κ t ω) d).symm
    show ∑ k ∈ S7FCW9_cube d n, (Lattice.jp k.1 ^ (-r) * Q k t ω) ^ 2 ≤ _
    rw [hsumg]
    have h1 : ENNReal.ofReal ((Yf t n ω) ^ (1 : ℝ)) ≤
        ⨆ k, ENNReal.ofReal ((Yf t k ω) ^ (1 : ℝ)) :=
      le_iSup (fun k => ENNReal.ofReal ((Yf t k ω) ^ (1 : ℝ))) n
    rw [Real.rpow_one] at h1
    exact ((ENNReal.ofReal_le_iff_le_toReal hω.ne).1 h1).trans (Nat.le_ceil _)
  -- Step 7: the field `B`
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → Ω' → NegSobolev d r,
      ∀ t ω, B t ω = NegSobolev.ofSeq r (fun κ => Q κ t ω) :=
    ⟨fun t ω => NegSobolev.ofSeq r (fun κ => Q κ t ω), fun _ _ => rfl⟩
  have hBm : Measurable (Function.uncurry B) := by
    have hfun : Function.uncurry B =
        fun p : ℝ × Ω' => NegSobolev.ofSeq r (fun κ => Q κ p.1 p.2) :=
      funext fun p => hBdef p.1 p.2
    rw [hfun]
    have hc : ∀ κ : NonzeroLattice d, Measurable (fun p : ℝ × Ω' => Q κ p.1 p.2) :=
      fun κ => hQm κ
    exact S7FCW9_measurable_ofSeq (α := ℝ × Ω') r (fun κ p => Q κ p.1 p.2) hc
  have hBt : ∀ t : ℝ, Measurable fun ω => B t ω := fun t => hBm.comp (hpt t)
  -- the eval identity and the moment identity on the honest set
  have hid : ∀ t : ℝ, ∀ ω : Ω', Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) * Q k t ω) 2 →
      ∀ m : ℝ, 0 ≤ m → ENNReal.ofReal (‖B t ω‖ ^ (2 * m)) =
        ⨆ n, ENNReal.ofReal ((Yf t n ω) ^ m) := by
    intro t ω hω m hm0
    have hcf : ∀ κ : NonzeroLattice d,
        NegSobolev.coord (B t ω) κ = Lattice.jp κ.1 ^ (-r) * Q κ t ω := fun κ => by
      rw [hBdef]
      exact NegSobolev.coord_ofSeq_of_mem (fun κ => Q κ t ω) hω κ
    have hYeq : ∀ n, ∑ k ∈ S7FCW9_cube d n, NegSobolev.coord (B t ω) k ^ 2 = Yf t n ω := by
      intro n
      rw [hYf]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [hcf κ]
      exact (S7FCW9_weight_eq r (Lattice.jp κ.1) (Torus.jp_pos κ.1) (Q κ t ω) d).symm
    have hs : HasSum (fun k => NegSobolev.coord (B t ω) k ^ 2) (‖B t ω‖ ^ 2) := by
      rw [(NegSobolev.coord_sq (B t ω)).2]
      exact (NegSobolev.coord_sq (B t ω)).1.hasSum
    have hT1 : Tendsto (fun n => Yf t n ω) atTop (𝓝 (‖B t ω‖ ^ 2)) := by
      have h := S7FCW9_tendsto_of_hasSum hs
      simpa only [hYeq] using h
    have hT3 : Tendsto (fun n => ENNReal.ofReal ((Yf t n ω) ^ m)) atTop
        (𝓝 (ENNReal.ofReal ((‖B t ω‖ ^ 2) ^ m))) :=
      ENNReal.tendsto_ofReal (hT1.rpow_const (Or.inr hm0))
    have hmono : Monotone fun n => ENNReal.ofReal ((Yf t n ω) ^ m) := fun n n' hnn' =>
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hYfnn t n ω) (hYfle t ω hnn') hm0)
    have hpow : ‖B t ω‖ ^ (2 * m) = (‖B t ω‖ ^ 2) ^ m := by
      rw [S7FCW9_sq_rpow, abs_norm]
    rw [hpow]
    exact (tendsto_nhds_unique (tendsto_atTop_iSup hmono) hT3).symm
  have hae2 : ∀ t : ℝ, 0 ≤ t → ∀ m : ℝ, 0 ≤ m → ∀ᵐ ω ∂P',
      ENNReal.ofReal (‖B t ω‖ ^ (2 * m)) = ⨆ n, ENNReal.ofReal ((Yf t n ω) ^ m) :=
    fun t ht m hm0 => (hgood t ht).mono fun ω hω => hid t ω hω m hm0
  have hL : ∀ m : ℝ, 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (‖B t ω‖ ^ (2 * m)) ∂P' ≤ ENNReal.ofReal C := by
    intro m hm
    obtain ⟨C, hC0, hC⟩ := hsupG m hm
    exact ⟨C, hC0, fun t ht =>
      (lintegral_congr_ae (hae2 t ht m (by linarith))).trans_le (hC t ht)⟩
  have hint : ∀ (q C : ℝ), 0 ≤ C →
      (∀ t : ℝ, 0 ≤ t → ∫⁻ ω, ENNReal.ofReal (‖B t ω‖ ^ q) ∂P' ≤ ENNReal.ofReal C) →
      ∀ t : ℝ, 0 ≤ t → Integrable (fun ω => ‖B t ω‖ ^ q) P' ∧ ∫ ω, ‖B t ω‖ ^ q ∂P' ≤ C := by
    intro q C hC hbd t ht
    have hmeas : Measurable fun ω => ‖B t ω‖ ^ q := ((hBt t).norm).pow_const q
    have h0 : 0 ≤ᵐ[P'] fun ω => ‖B t ω‖ ^ q :=
      Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _
    have hfin : ∫⁻ ω, ENNReal.ofReal (‖B t ω‖ ^ q) ∂P' < ⊤ :=
      lt_of_le_of_lt (hbd t ht) ENNReal.ofReal_lt_top
    refine ⟨⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h0).2 hfin⟩, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae h0 hmeas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hC (hbd t ht)
  -- Step 8: assembly
  refine ⟨B, hBm, ?_, ?_⟩
  · intro t ht κ
    have hH := hQt κ t ht
    refine S7FCW9_isHalfWick_congr (withDensityReal (R.ρ t)) _ (hae t ht) ?_ hH
    filter_upwards [hgood t ht] with ω hω
    show Q κ t ω = NegSobolev.eval (B t ω) (Torus.realMode κ)
    rw [S7FCW9_eval_realMode, hBdef]
    exact (S7FCW9_fourierCoeff_ofSeq (fun k => Q k t ω) hω κ).symm
  · intro q hq
    by_cases h2 : 2 ≤ q
    · obtain ⟨C, hC0, hC⟩ := hL (q / 2) (by linarith)
      have e2 : (2 : ℝ) * (q / 2) = q := by ring
      have hC' : ∀ t : ℝ, 0 ≤ t → ∫⁻ ω, ENNReal.ofReal (‖B t ω‖ ^ q) ∂P' ≤ ENNReal.ofReal C := by
        intro t ht
        have := hC t ht
        rwa [e2] at this
      exact ⟨C, fun t ht => hint q C hC0 hC' t ht⟩
    · push_neg at h2
      obtain ⟨C1, hC1, hC1b⟩ := hL 1 le_rfl
      have hC' : ∀ t : ℝ, 0 ≤ t →
          ∫⁻ ω, ENNReal.ofReal (‖B t ω‖ ^ q) ∂P' ≤ ENNReal.ofReal (1 + C1) := by
        intro t ht
        calc ∫⁻ ω, ENNReal.ofReal (‖B t ω‖ ^ q) ∂P'
            ≤ ∫⁻ ω, (1 + ENNReal.ofReal (‖B t ω‖ ^ (2 * (1 : ℝ)))) ∂P' := by
              refine lintegral_mono fun ω => ?_
              refine (ENNReal.ofReal_le_ofReal
                (S7FCW9_rpow_le_one_add_sq ‖B t ω‖ q (norm_nonneg _) hq h2.le)).trans_eq ?_
              rw [ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg (norm_nonneg _) _),
                ENNReal.ofReal_one]
          _ = 1 + ∫⁻ ω, ENNReal.ofReal (‖B t ω‖ ^ (2 * (1 : ℝ))) ∂P' := by
              rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
          _ ≤ 1 + ENNReal.ofReal C1 := add_le_add le_rfl (hC1b t ht)
          _ = ENNReal.ofReal (1 + C1) := by
              rw [ENNReal.ofReal_add zero_le_one hC1, ENNReal.ofReal_one]
      exact ⟨1 + C1, fun t ht => hint q (1 + C1) (by linarith) hC' t ht⟩

end HRS.MC.Sec7.S7FCW9

end
