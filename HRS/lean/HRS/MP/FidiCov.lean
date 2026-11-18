import HRS.MP.FidiDefs

/-!
# Packet MPFIDI-F3a/b: propagator convergence in `H^γ`, covariance of the surrogate
-/

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Main HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.MP.FidiCov

open HRS.MP.FidiDefs

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem fi_eval_meas {γ : ℝ} {ψ : Torus d → ℝ} (h : MemSobolev γ ψ) :
    Measurable fun F : NegSobolev d γ => NegSobolev.eval F ψ := by
  have : (fun F : NegSobolev d γ => NegSobolev.eval F ψ) =
      fun F => inner ℝ F (HRS.Uniform.Q54.lpOf γ h) := by
    funext F; exact HRS.Uniform.Q54.eval_eq_inner γ F h
  rw [this]
  exact (continuous_id.inner continuous_const).measurable

theorem fi3_statVec_meas (D : DynData d) (ρ : ℝ → Torus d → ℝ) (A : ℝ) {p : ℕ} (ts : Fin p → ℝ)
    (φ : Fin p → Torus d → ℝ) (γ : ℝ)
    (hmem : ∀ a, MemSobolev γ (propagator D ρ 0 (ts a) (φ a))) :
    Measurable (statVec D ρ A ts φ γ) := by
  unfold statVec
  refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp ?_
  exact Measurable.of_eval fun a => (fi_eval_meas (hmem a)).const_mul A


/-! ### F3a: propagators of a smooth test -/

open HRS.PDE HRS.A34 in
/-- membership in `H^γ` and continuity of the propagator `U^{0,t}φ` of a smooth test. -/
theorem fi3a_one {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {Rg : PDE.Regime}
    {MB Λ VB ν₀ T : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : AdjointData s (gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    MemSobolev (gammaIdx d : ℝ) (propagator D ρ 0 t φ) ∧ Continuous (propagator D ρ 0 t φ) := by
  have hJ : mStar d ≤ gammaIdx d + 2 := by unfold gammaIdx; omega
  have hφc : Continuous φ := HRS.A33.a33_cont hφ
  have hφm : MemSobolev ((gammaIdx d + 2 : ℕ) : ℝ) φ := HRS.A33.a33_memSob _ hφ
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [a34_prop_zero hd (gammaIdx d + 2) hJ Rg s MB Λ VB ν₀ T D ρ hA hφc hφm]
    exact ⟨HRS.A33.a33_memSob _ hφ, hφc⟩
  · obtain ⟨K, K₂, -, -, hu⟩ := a34_unif hd s hs0 hsd (gammaIdx d + 2) hJ Rg MB Λ VB ν₀ T
    obtain ⟨-, hr⟩ := hu D ρ hA ⟨hpos, ht.2⟩ hφc hφm
    obtain ⟨h1, h2, -⟩ := hr 0 ⟨le_rfl, hpos.le⟩
    refine ⟨(h1 (gammaIdx d) (by unfold gammaIdx; omega) (by omega)).1, ?_⟩
    exact HRS.PDE.ClassicalAux.continuous_of_isCk (h2.of_le (by norm_num))


open HRS.PDE HRS.A34 in
theorem fi3a_prop {Rg : PDE.Regime} {ν₀ MB Λ VB : ℝ} (S : MainData d) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    (∀ N : ℕ, 1 ≤ N → MemSobolev (gammaIdx d : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t φ) ∧
        Continuous (propagator (S.dyn N) (S.ρ N) 0 t φ)) ∧
    (MemSobolev (gammaIdx d : ℝ) (propagator (L.dyn S) L.ρ 0 t φ) ∧
        Continuous (propagator (L.dyn S) L.ρ 0 t φ)) ∧
    Tendsto (fun N => sobolevNorm (gammaIdx d : ℝ)
      (fun x => propagator (S.dyn N) (S.ρ N) 0 t φ x - propagator (L.dyn S) L.ρ 0 t φ x))
      atTop (𝓝 0) := by
  have hd := S.hd
  have hs0 := S.hs0
  have hsd := S.hsd
  refine ⟨fun N hN => fi3a_one hd hs0 hsd (S.dyn N) (S.ρ N) (hcoef.seq_adjoint N hN) ht hφ,
    fi3a_one hd hs0 hsd (L.dyn S) L.ρ hcoef.limit_adjoint ht hφ, ?_⟩
  have hφc : Continuous φ := HRS.A33.a33_cont hφ
  have hφm : MemSobolev ((gammaIdx d + 2 : ℕ) : ℝ) φ := HRS.A33.a33_memSob _ hφ
  have hJ : mStar d ≤ gammaIdx d + 2 := by unfold gammaIdx; omega
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have : ∀ᶠ N in atTop, sobolevNorm (gammaIdx d : ℝ)
        (fun x => propagator (S.dyn N) (S.ρ N) 0 0 φ x - propagator (L.dyn S) L.ρ 0 0 φ x) = 0 := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [a34_prop_zero hd (gammaIdx d + 2) hJ Rg S.s MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N)
          (hcoef.seq_adjoint N hN) hφc hφm,
        a34_prop_zero hd (gammaIdx d + 2) hJ Rg S.s MB Λ VB ν₀ S.T (L.dyn S) L.ρ
          hcoef.limit_adjoint hφc hφm]
      exact a34_sobolevNorm_zero_sub _ _
    exact tendsto_const_nhds.congr' (this.mono fun N h => h.symm)
  · obtain ⟨C, hC, hst⟩ := a34_stab hd S.s hs0 hsd (gammaIdx d) (by unfold gammaIdx; omega) hJ Rg
      MB Λ VB ν₀ S.T
    have hΔ := hcoef.tendsto
    have hup : Tendsto (fun N => C * (S.coeffDiscrepancy L (gammaIdx d) N +
        S.coeffDiscrepancy L (gammaIdx d) N) * sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ) φ) atTop
        (𝓝 0) := by
      have := ((hΔ.add hΔ).const_mul C).mul_const (sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ) φ)
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun N => a34_sobolevNorm_nonneg _ _) ?_ hup
    filter_upwards [eventually_ge_atTop 1] with N hN
    obtain ⟨hΔ0, hρΔ, hβΔ, -, -⟩ := a34_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB
      (hcoef.seq_adjoint N hN) hcoef.limit_adjoint
    obtain ⟨-, h2⟩ := hst (S.dyn N) (L.dyn S) (S.ρ N) L.ρ (hcoef.seq_adjoint N hN)
      hcoef.limit_adjoint rfl rfl (S.coeffDiscrepancy L (gammaIdx d) N) hρΔ ⟨hpos, ht.2⟩ hφc hφm
      ⟨le_rfl, hpos.le⟩
    refine h2.trans ?_
    have hn0 : 0 ≤ sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ) φ := a34_sobolevNorm_nonneg _ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hβΔ le_rfl) hC.le) hn0


/-! ### F3b: Gram representation of the covariance -/

section Gram

open HRS.PDE HRS.A34 HRS.A33

theorem fi3b_inner_ae {T : ℝ} {ρ : ℝ → Torus d → ℝ} (hρ : A33Rho T ρ) (D : DynData d) (q : ℝ)
    {ta tb : ℝ} {φa φb : Torus d → ℝ} :
    ∀ᵐ p ∂(a33_mu0 d T), inner ℝ (a34_h D ρ q ta φa p) (a34_h D ρ q tb φb p) =
      ρ p.1 p.2 * inner ℝ (a33_g D ρ q ta φa p) (a33_g D ρ q tb φb p) := by
  filter_upwards [a33_ae_mu0 (d := d) T] with p hp
  simp only [a34_h, real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, Real.mul_self_sqrt (hρ.nonneg p.1 hp p.2)]

theorem fi3b_inner_int {T : ℝ} {ρ : ℝ → Torus d → ℝ} (hρ : A33Rho T ρ) (D : DynData d) {q ta tb : ℝ}
    {φa φb : Torus d → ℝ} (hma : Measurable (a33_g D ρ q ta φa))
    (hmb : Measurable (a33_g D ρ q tb φb)) {Ba Bb : ℝ}
    (hba : ∀ p, ‖a33_g D ρ q ta φa p‖ ≤ Ba) (hbb : ∀ p, ‖a33_g D ρ q tb φb p‖ ≤ Bb) :
    Integrable (fun p => inner ℝ (a34_h D ρ q ta φa p) (a34_h D ρ q tb φb p)) (a33_mu0 d T) := by
  obtain ⟨Bρ, hBρ⟩ := hρ.bound
  have h1 : AEMeasurable (a34_h D ρ q ta φa) (a33_mu0 d T) :=
    (hρ.aemeasurable.sqrt).smul hma.aemeasurable
  have h2 : AEMeasurable (a34_h D ρ q tb φb) (a33_mu0 d T) :=
    (hρ.aemeasurable.sqrt).smul hmb.aemeasurable
  refine Integrable.of_bound (h1.inner h2).aestronglyMeasurable (Bρ * (Ba * Bb)) ?_
  filter_upwards [fi3b_inner_ae hρ D q (ta := ta) (tb := tb) (φa := φa) (φb := φb),
    a33_ae_mu0 (d := d) T] with p h1 hp
  rw [h1, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hBρ p.1 hp p.2) ((abs_real_inner_le_norm _ _).trans
    (mul_le_mul (hba p) (hbb p) (norm_nonneg _) ((norm_nonneg _).trans (hba p)))) (abs_nonneg _)
    ((abs_nonneg _).trans (hBρ p.1 hp p.2))


theorem fi3b_cov_eq {T : ℝ} {ρ : ℝ → Torus d → ℝ} (hρ : A33Rho T ρ) (D : DynData d) {q ta tb : ℝ}
    (hq : 0 ≤ q) (hta : ta ∈ Set.Icc (0 : ℝ) T) (htb : tb ∈ Set.Icc (0 : ℝ) T)
    {φa φb : Torus d → ℝ} (hma : Measurable (a33_g D ρ q ta φa))
    (hmb : Measurable (a33_g D ρ q tb φb)) {Ba Bb : ℝ}
    (hba : ∀ p, ‖a33_g D ρ q ta φa p‖ ≤ Ba) (hbb : ∀ p, ‖a33_g D ρ q tb φb p‖ ≤ Bb) :
    2 * q * ∫ r in Set.Icc 0 (min ta tb), ∫ x : Torus d,
        inner ℝ (Torus.grad (propagator D ρ r ta φa) x) (Torus.grad (propagator D ρ r tb φb) x) *
          ρ r x =
      ∫ p, inner ℝ (a34_h D ρ q ta φa p) (a34_h D ρ q tb φb p) ∂(a33_mu0 d T) := by
  classical
  by_cases hpos : 0 < ta ∧ 0 < tb
  swap
  · have hz : ∀ p, inner ℝ (a34_h D ρ q ta φa p) (a34_h D ρ q tb φb p) = 0 := by
      intro p
      rcases not_and_or.1 hpos with h | h
      · simp [a34_h, a34_g_zero D ρ q ta φa h]
      · simp [a34_h, a34_g_zero D ρ q tb φb h]
    have hmin : min ta tb = 0 := by
      apply le_antisymm _ (le_min hta.1 htb.1)
      rcases not_and_or.1 hpos with h | h
      · exact (min_le_left _ _).trans (not_lt.1 h)
      · exact (min_le_right _ _).trans (not_lt.1 h)
    simp only [hz, integral_zero]
    rw [hmin, Set.Icc_self, setIntegral_measure_zero _ (by simp), mul_zero]
  · obtain ⟨hapos, hbpos⟩ := hpos
    have hmT : min ta tb ≤ T := (min_le_left _ _).trans hta.2
    set F : ℝ × Torus d → ℝ := fun p =>
      inner ℝ (a34_h D ρ q ta φa p) (a34_h D ρ q tb φb p) with hF
    have hFint : Integrable F (a33_mu0 d T) := fi3b_inner_int hρ D hma hmb hba hbb
    have hfub := integral_prod F hFint
    have hprod : a33_mu0 d T = (volume.restrict (Set.Icc 0 T)).prod volume := rfl
    rw [hprod, hfub]
    set Φ : ℝ → ℝ := fun r => ∫ x : Torus d,
      inner ℝ (Torus.grad (propagator D ρ r ta φa) x) (Torus.grad (propagator D ρ r tb φb) x) *
        ρ r x with hΦ
    have key : ∀ a b i : ℝ, 0 ≤ a → 0 ≤ b →
        Real.sqrt a * (Real.sqrt a * (Real.sqrt b * (Real.sqrt b * i))) = a * b * i := by
      intro a b i ha hb
      have e1 := Real.mul_self_sqrt ha
      have e2 := Real.mul_self_sqrt hb
      calc _ = (Real.sqrt a * Real.sqrt a) * (Real.sqrt b * Real.sqrt b) * i := by ring
        _ = _ := by rw [e1, e2]
    have hinner : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫ x : Torus d, F (r, x) =
        (Set.Icc 0 (min ta tb)).indicator (fun r => 2 * q * Φ r) r := by
      intro r hr
      by_cases hr' : r ∈ Set.Icc 0 (min ta tb)
      · rw [Set.indicator_of_mem hr']
        have hra : r ∈ Set.Icc 0 ta := ⟨hr'.1, hr'.2.trans (min_le_left _ _)⟩
        have hrb : r ∈ Set.Icc 0 tb := ⟨hr'.1, hr'.2.trans (min_le_right _ _)⟩
        have : ∀ x : Torus d, F (r, x) = 2 * q * (inner ℝ
            (Torus.grad (propagator D ρ r ta φa) x) (Torus.grad (propagator D ρ r tb φb) x) *
              ρ r x) := by
          intro x
          simp only [hF, a34_h, a33_g, hra, hrb, hapos, hbpos, and_self, ite_true,
            real_inner_smul_left, real_inner_smul_right]
          rw [key _ _ _ (hρ.nonneg r hr x) (by linarith)]
          ring
        simp_rw [this]
        rw [integral_const_mul]
      · rw [Set.indicator_of_notMem hr']
        have : ∀ x : Torus d, F (r, x) = 0 := by
          intro x
          have h0 : a33_g D ρ q ta φa (r, x) = 0 ∨ a33_g D ρ q tb φb (r, x) = 0 := by
            by_contra hcon
            push_neg at hcon
            apply hr'
            have h1 : r ∈ Set.Icc 0 ta := by
              by_contra h
              exact hcon.1 (by unfold a33_g; exact if_neg (fun h' => h h'.1))
            have h2 : r ∈ Set.Icc 0 tb := by
              by_contra h
              exact hcon.2 (by unfold a33_g; exact if_neg (fun h' => h h'.1))
            exact ⟨h1.1, le_min h1.2 h2.2⟩
          rcases h0 with h | h <;> simp [hF, a34_h, h]
        simp_rw [this]
        simp
    have hcongr : ∫ r, ∫ x : Torus d, F (r, x) ∂volume ∂(volume.restrict (Set.Icc 0 T)) =
        ∫ r, (Set.Icc 0 (min ta tb)).indicator (fun r => 2 * q * Φ r) r
          ∂(volume.restrict (Set.Icc 0 T)) := by
      refine integral_congr_ae ?_
      exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hinner)
    rw [hcongr, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.2 (Set.Icc_subset_Icc le_rfl hmT), integral_const_mul]


/-- measurability, boundedness of the noise integrand and regularity of the density path. -/
theorem fi3b_facts {Rg : PDE.Regime} {MB Λ VB ν₀ T : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : AdjointData D.s (gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ) (q : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Measurable (a33_g D ρ q t φ) ∧ ∃ B : ℝ, ∀ p, ‖a33_g D ρ q t φ p‖ ≤ B := by
  have hs0 := D.hs0
  have hsd := D.hsd
  have hd : 1 ≤ d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    exact_mod_cast this
  have hJ : mStar d ≤ gammaIdx d + 2 := by unfold gammaIdx; omega
  rcases ht.1.eq_or_lt with h0 | hpos
  · have hz : a33_g D ρ q t φ = 0 := a34_g_zero D ρ q t φ (by rw [← h0]; exact lt_irrefl _)
    exact ⟨by rw [hz]; exact measurable_const, 0, fun p => by simp [hz]⟩
  · have hφc : Continuous φ := HRS.A33.a33_cont hφ
    have hφm : MemSobolev ((gammaIdx d + 2 : ℕ) : ℝ) φ := HRS.A33.a33_memSob _ hφ
    obtain ⟨K, K₂, -, -, hu⟩ := a34_unif hd D.s hs0 hsd (gammaIdx d + 2) hJ Rg MB Λ VB ν₀ T
    obtain ⟨⟨f, hcl, hpe⟩, hr⟩ := hu D ρ hA ⟨hpos, ht.2⟩ hφc hφm
    obtain ⟨hm, hb⟩ := a34_g_meas_bd D ρ q t φ hpos f hcl hpe
      (K := K₂ * sobolevNorm (mStar d : ℝ) φ) (fun r hr' x => (hr r hr').2.2 x)
    exact ⟨hm, _, hb⟩

theorem fi3b_rho {Rg : PDE.Regime} {MB Λ VB ν₀ T : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : AdjointData D.s (gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ) : A33Rho T ρ := by
  have hJd : (d : ℝ) / 2 < ((gammaIdx d + 2 : ℕ) : ℝ) := by
    have h1 := a33_mStar_gt d
    have h2 : (mStar d : ℝ) ≤ ((gammaIdx d + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by unfold gammaIdx; omega : mStar d ≤ gammaIdx d + 2)
    linarith
  exact (a34_rho (gammaIdx d + 2) hJd Rg D.s MB Λ VB ν₀ T D ρ hA).1

/-- the Gram representation of the covariance entries. -/
theorem fi3b_rep {Rg : PDE.Regime} {MB Λ VB ν₀ T : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : AdjointData D.s (gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ) {q : ℝ} (hq : 0 ≤ q)
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) (a b : Fin p) :
    surrogateCov D ρ q ts φ a b =
      ∫ x, inner ℝ (a34_h D ρ q (ts a) (φ a) x) (a34_h D ρ q (ts b) (φ b) x) ∂(a33_mu0 d T) := by
  obtain ⟨hma, Ba, hba⟩ := fi3b_facts D ρ hA q (hts a) (hφ a)
  obtain ⟨hmb, Bb, hbb⟩ := fi3b_facts D ρ hA q (hts b) (hφ b)
  exact fi3b_cov_eq (fi3b_rho D ρ hA) D hq (hts a) (hts b) hma hmb hba hbb

theorem fi3b_psd {Rg : PDE.Regime} {ν₀ MB Λ VB T : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : PDE.AdjointData D.s (gammaIdx d + 2) Rg MB Λ VB D ν₀ T ρ) {q : ℝ} (hq : 0 ≤ q)
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    (surrogateCov D ρ q ts φ).PosSemidef := by
  have hrep := fi3b_rep D ρ hA hq ts hts φ hφ
  set H : Fin p → ℝ × Torus d → Euc d := fun a => a34_h D ρ q (ts a) (φ a) with hH
  have hint : ∀ a b, Integrable (fun x => inner ℝ (H a x) (H b x)) (a33_mu0 d T) := by
    intro a b
    obtain ⟨hma, Ba, hba⟩ := fi3b_facts D ρ hA q (hts a) (hφ a)
    obtain ⟨hmb, Bb, hbb⟩ := fi3b_facts D ρ hA q (hts b) (hφ b)
    exact fi3b_inner_int (fi3b_rho D ρ hA) D hma hmb hba hbb
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext a b
    rw [Matrix.transpose_apply, hrep, hrep]
    exact integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)
  · have h1 : dotProduct (star x) (Matrix.mulVec (surrogateCov D ρ q ts φ) x) =
        ∫ y, ∑ a, ∑ b, x a * x b * inner ℝ (H a y) (H b y) ∂(a33_mu0 d T) := by
      rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _
        (fun b _ => (hint a b).const_mul (x a * x b)))]
      simp only [dotProduct, Matrix.mulVec, star_trivial]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finset_sum _ (fun b _ => (hint a b).const_mul (x a * x b)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul, hrep a b]
      ring
    rw [h1]
    refine integral_nonneg fun y => ?_
    have h2 : ∑ a, ∑ b, x a * x b * inner ℝ (H a y) (H b y) =
        inner ℝ (∑ a, x a • H a y) (∑ b, x b • H b y) := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_smul_left, real_inner_smul_right]
      ring
    rw [h2]
    exact real_inner_self_nonneg


theorem fi3b_memLp {T : ℝ} {ρ : ℝ → Torus d → ℝ} (hρ : A33Rho T ρ) (D : DynData d) {q t : ℝ}
    {φ : Torus d → ℝ} (hm : Measurable (a33_g D ρ q t φ)) {B : ℝ}
    (hb : ∀ p, ‖a33_g D ρ q t φ p‖ ≤ B) : MemLp (a34_h D ρ q t φ) 2 (a33_mu0 d T) := by
  obtain ⟨Bρ, hBρ⟩ := hρ.bound
  refine MemLp.of_bound ((hρ.aemeasurable.sqrt).smul hm.aemeasurable).aestronglyMeasurable
    (Real.sqrt Bρ * B) ?_
  filter_upwards [a33_ae_mu0 (d := d) T] with p hp
  simp only [a34_h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul (Real.sqrt_le_sqrt ((le_abs_self _).trans (hBρ p.1 hp p.2))) (hb p)
    (norm_nonneg _) (Real.sqrt_nonneg _)

/-- `L²` convergence of two sequences gives convergence of the inner products. -/
theorem fi3b_inner_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : ℕ → α → Euc d} {u₀ v₀ : α → Euc d}
    (hu : ∀ N, MemLp (u N) 2 μ) (hv : ∀ N, MemLp (v N) 2 μ) (hu₀ : MemLp u₀ 2 μ)
    (hv₀ : MemLp v₀ 2 μ)
    (hcu : Tendsto (fun N => ∫ x, ‖u N x - u₀ x‖ ^ 2 ∂μ) atTop (𝓝 0))
    (hcv : Tendsto (fun N => ∫ x, ‖v N x - v₀ x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ x, inner ℝ (u N x) (v N x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (u₀ x) (v₀ x) ∂μ)) := by
  have key : ∀ {w : ℕ → α → Euc d} {w₀ : α → Euc d} (hw : ∀ N, MemLp (w N) 2 μ)
      (hw₀ : MemLp w₀ 2 μ),
      Tendsto (fun N => ∫ x, ‖w N x - w₀ x‖ ^ 2 ∂μ) atTop (𝓝 0) →
      Tendsto (fun N => (hw N).toLp (w N)) atTop (𝓝 (hw₀.toLp w₀)) := by
    intro w w₀ hw hw₀ hc
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have e : ∀ N, ‖(hw N).toLp (w N) - hw₀.toLp w₀‖ = Real.sqrt (∫ x, ‖w N x - w₀ x‖ ^ 2 ∂μ) := by
      intro N
      rw [← MemLp.toLp_sub (hw N) hw₀]
      have := a34_norm_toLp_sq ((hw N).sub hw₀)
      rw [← Real.sqrt_sq (norm_nonneg ((((hw N).sub hw₀)).toLp (w N - w₀))), this]
      rfl
    simp_rw [e]
    have h := (Real.continuous_sqrt.tendsto 0).comp hc
    rw [Real.sqrt_zero] at h
    exact h
  have hlim := Filter.Tendsto.inner (𝕜 := ℝ) (key hu hu₀ hcu) (key hv hv₀ hcv)
  have hin : ∀ {f g : α → Euc d} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
    intro f g hf hg
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  simp_rw [hin] at hlim
  exact hlim


theorem fi3b_cov {Rg : PDE.Regime} {ν₀ MB Λ VB : ℝ} (S : MainData d) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) (a b : Fin p) :
    Tendsto (fun N => surrogateCov (S.dyn N) (S.ρ N) (S.qN N) ts φ a b) atTop
      (𝓝 (surrogateCov (L.dyn S) L.ρ L.invβstar ts φ a b)) := by
  have hd := S.hd
  have hs0 := S.hs0
  have hsd := S.hsd
  obtain ⟨C, hC, hdiff⟩ := a34_h_diff_field hd S.s hs0 hsd Rg ν₀ MB Λ VB S.T
  have hqN : ∀ N : ℕ, 1 ≤ N → 0 ≤ S.qN N ∧ S.qN N ≤ 1 := fun N hN =>
    a34_qScale_bounds (N := N) (by omega) (S.hκ N) (S.hinvβ N)
  -- the shifted coefficient discrepancy
  have hΔ : Tendsto (fun N : ℕ => S.coeffDiscrepancy L (gammaIdx d) (N + 1)) atTop (𝓝 0) :=
    hcoef.tendsto.comp (tendsto_add_atTop_nat 1)
  -- `L²` convergence of the noise integrands
  have hL2 : ∀ a, Tendsto (fun N : ℕ => ∫ x, ‖a34_h (S.dyn (N + 1)) (S.ρ (N + 1)) (S.qN (N + 1))
      (ts a) (φ a) x - a34_h (L.dyn S) L.ρ L.invβstar (ts a) (φ a) x‖ ^ 2 ∂(a33_mu0 d S.T))
      atTop (𝓝 0) := by
    intro a
    have hφc : Continuous (φ a) := HRS.A33.a33_cont (hφ a)
    have hφm : MemSobolev ((mStar d + 2 : ℕ) : ℝ) (φ a) := HRS.A33.a33_memSob _ (hφ a)
    set Nφ := sobolevNorm ((mStar d + 2 : ℕ) : ℝ) (φ a) with hNφ
    have hup : Tendsto (fun N : ℕ => (C + 1) * (S.coeffDiscrepancy L (gammaIdx d) (N + 1) +
        S.coeffDiscrepancy L (gammaIdx d) (N + 1) ^ 2) * Nφ ^ 2) atTop (𝓝 0) := by
      have := (((hΔ.add (hΔ.pow 2)).const_mul (C + 1)).mul_const (Nφ ^ 2))
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun N => integral_nonneg fun x => by positivity)
      ?_ hup
    refine Eventually.of_forall fun N => ?_
    have hN : 1 ≤ N + 1 := by omega
    obtain ⟨hΔ0, hρΔ, hβΔ, hqΔ, -⟩ := a34_delta_facts S L (gammaIdx d) (N + 1) Rg ν₀ MB Λ VB
      (hcoef.seq_adjoint (N + 1) hN) hcoef.limit_adjoint
    have hmono : mStar d + 2 ≤ gammaIdx d + 2 := by unfold gammaIdx; omega
    have h := hdiff (S.dyn (N + 1)) (L.dyn S) (S.ρ (N + 1)) L.ρ (S.qN (N + 1)) L.invβstar
      (S.coeffDiscrepancy L (gammaIdx d) (N + 1))
      (HRS.PDE.StabAux.adjointData_mono hmono (hcoef.seq_adjoint (N + 1) hN))
      (HRS.PDE.StabAux.adjointData_mono hmono hcoef.limit_adjoint) rfl rfl hΔ0
      (fun r hr => (HRS.PDE.cbNorm_mono' hmono _).trans (hρΔ r hr)) hβΔ (hqN (N + 1) hN).1
      (hqN (N + 1) hN).2 L.hinvβstar hqΔ (ts a) (hts a) (φ a) hφc hφm
    refine h.trans ?_
    have h0 : 0 ≤ (S.coeffDiscrepancy L (gammaIdx d) (N + 1) +
        S.coeffDiscrepancy L (gammaIdx d) (N + 1) ^ 2) * Nφ ^ 2 := by positivity
    nlinarith
  -- membership in `L²`
  have hmemN : ∀ N : ℕ, ∀ a, MemLp (a34_h (S.dyn (N + 1)) (S.ρ (N + 1)) (S.qN (N + 1)) (ts a) (φ a))
      2 (a33_mu0 d S.T) := by
    intro N a
    obtain ⟨hm, B, hB⟩ := fi3b_facts (S.dyn (N + 1)) (S.ρ (N + 1))
      (hcoef.seq_adjoint (N + 1) (by omega)) (S.qN (N + 1)) (hts a) (hφ a)
    exact fi3b_memLp (fi3b_rho (S.dyn (N + 1)) (S.ρ (N + 1)) (hcoef.seq_adjoint (N + 1) (by omega))) _ hm hB
  have hmemL : ∀ a, MemLp (a34_h (L.dyn S) L.ρ L.invβstar (ts a) (φ a)) 2 (a33_mu0 d S.T) := by
    intro a
    obtain ⟨hm, B, hB⟩ := fi3b_facts (L.dyn S) L.ρ hcoef.limit_adjoint L.invβstar (hts a) (hφ a)
    exact fi3b_memLp (fi3b_rho (L.dyn S) L.ρ hcoef.limit_adjoint) _ hm hB
  rw [fi3b_rep (L.dyn S) L.ρ hcoef.limit_adjoint L.hinvβstar ts hts φ hφ a b]
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  refine Tendsto.congr (fun N => (fi3b_rep (S.dyn (N + 1)) (S.ρ (N + 1))
    (hcoef.seq_adjoint (N + 1) (by omega)) (hqN (N + 1) (by omega)).1 ts hts φ hφ a b).symm) ?_
  exact fi3b_inner_tendsto (fun N => hmemN N a) (fun N => hmemN N b) (hmemL a) (hmemL b)
    (hL2 a) (hL2 b)

end Gram

end HRS.MP.FidiCov
