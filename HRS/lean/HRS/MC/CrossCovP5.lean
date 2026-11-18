import HRS.Main.HeadlineEdgeworth
import HRS.MC.CrossCovP2
import HRS.MC.CrossCovP4

/-!
# Packet CC5: `ccd_noise_bound` (statement of `HRS/MC/CrossCovSpec.lean`, proved)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CrossCov

open HRS HRS.Main

variable {d : ℕ}

theorem p_cc5_cont {u : Torus d → ℝ} (hu : Torus.IsSmooth u) : Continuous u := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift u) := hu
  exact Torus.continuous_of_continuous_lift h.continuous

theorem p_cc5_ck1 {u : Torus d → ℝ} (hu : Torus.IsSmooth u) : Torus.IsCk 1 u := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift u) := hu
  exact ContDiff.of_le h (by norm_cast)

theorem p_cc5_isSmooth_mul {a b : Torus d → ℝ} (ha : Torus.IsSmooth a) (hb : Torus.IsSmooth b) :
    Torus.IsSmooth (fun x => a x * b x) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift a) := ha
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift b) := hb
  exact h1.mul h2

theorem p_cc5_grad_apply (u : Torus d → ℝ) (x : Torus d) (i : Fin d) :
    Torus.grad u x i = Torus.partialDeriv i u x := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
    (x := EuclideanSpace.single i (1 : ℝ)) (y := fderiv ℝ (Torus.lift u) (Torus.rep x))
  unfold Torus.grad Torus.partialDeriv gradient
  rw [← h, EuclideanSpace.inner_single_right]
  simp

theorem p_cc5_inner_grad (g f : Torus d → ℝ) (x : Torus d) :
    inner ℝ (Torus.grad g x) (Torus.grad f x) =
      ∑ i, Torus.partialDeriv i g x * Torus.partialDeriv i f x := by
  simp only [PiLp.inner_apply, p_cc5_grad_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem p_cc5_mean_partialDeriv (i : Fin d) {h : Torus d → ℝ} (hh : Torus.IsSmooth h) :
    Torus.mean (Torus.partialDeriv i h) = 0 := by
  unfold Torus.mean
  have hc : Torus.IsCk 1 (fun _ : Torus d => (1 : ℝ)) := contDiff_const
  have := HRS.PDE.integral_partialDeriv_mul i h (fun _ => 1) (p_cc5_ck1 hh) hc
  have h0 : ∀ x, Torus.partialDeriv i (fun _ : Torus d => (1 : ℝ)) x = 0 := by
    intro x
    have e : Torus.lift (fun _ : Torus d => (1 : ℝ)) = fun _ => 1 := rfl
    simp [Torus.partialDeriv, e]
  simpa [h0] using this

theorem p_cc5_ibp (g f ρ : Torus d → ℝ) (hg : Torus.IsSmooth g) (hf : Torus.IsSmooth f)
    (hρ : Torus.IsSmooth ρ) :
    ∫ x, inner ℝ (Torus.grad g x) (Torus.grad f x) * ρ x =
      -∑ i, ∫ x, g x * Torus.partialDeriv i (fun y => ρ y * Torus.partialDeriv i f y) x := by
  have hg1 : Torus.IsCk 1 g := p_cc5_ck1 hg
  have hh : ∀ i, Torus.IsSmooth (fun y => ρ y * Torus.partialDeriv i f y) := fun i =>
    p_cc5_isSmooth_mul hρ (HRS.LocalDivAux.isSmooth_partialDeriv hf i)
  have h1 : ∀ x, inner ℝ (Torus.grad g x) (Torus.grad f x) * ρ x =
      ∑ i, Torus.partialDeriv i g x * (ρ x * Torus.partialDeriv i f x) := by
    intro x
    rw [p_cc5_inner_grad, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [h1]
  rw [integral_finsetSum]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact HRS.PDE.integral_partialDeriv_mul i g _ hg1 (p_cc5_ck1 (hh i))
  · intro i _
    have hc : Continuous fun x => Torus.partialDeriv i g x * (ρ x * Torus.partialDeriv i f x) :=
      (HRS.PDE.continuous_partialDeriv i g hg1).mul
        ((p_cc5_cont hρ).mul (HRS.PDE.continuous_partialDeriv i f (p_cc5_ck1 hf)))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem p_cc5_sobolev_partialDeriv (σ : ℝ) (i : Fin d) {u : Torus d → ℝ} (hu : Torus.IsCk 1 u)
    (hm : MemSobolev (σ + 1) u) :
    MemSobolev σ (Torus.partialDeriv i u) ∧
      sobolevNorm σ (Torus.partialDeriv i u) ≤ sobolevNorm (σ + 1) u := by
  obtain ⟨hmem, heq⟩ := HRS.PDE.hsNormSq_coeffOf (σ + 1) u hm
  obtain ⟨hd1, hd2⟩ := HRS.PDE.MFApriori.hsNormSq_derivCoeff_le (σ + 1) i hmem
  rw [add_sub_cancel_right] at hd1 hd2
  have hc := HRS.PDE.coeffOf_partialDeriv i u hu
  have hL2 : MemLp (Torus.partialDeriv i u) 2 volume :=
    HRS.PDE.ClassicalAux.memLp_two_of_continuous (HRS.PDE.continuous_partialDeriv i u hu)
  rw [← hc] at hd1 hd2
  obtain ⟨hS, hsq⟩ := HRS.PDE.ProdAux.memSobolev_of_memHs' σ hL2 hd1
  refine ⟨hS, ?_⟩
  have : sobolevNorm σ (Torus.partialDeriv i u) ^ 2 ≤ sobolevNorm (σ + 1) u ^ 2 := by
    rw [hsq, ← heq]; exact hd2
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).1 this

theorem p_cc5_cbNorm_nonneg (k : ℕ) (a : Torus d → ℝ) : 0 ≤ Torus.cbNorm k a :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- The vector field `w_i^s = ∂_i (ρ^s ∂_i U^{s,t}φ)` has uniformly bounded `H^N` norm for `s ∈ [0,t]`. -/
theorem p_cc5_uniform (S : PreparedData d) (N : ℕ) {t : ℝ} (ht : 0 < t)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ i : Fin d,
      MemSobolev (N : ℝ) (Torus.partialDeriv i (fun y => S.ρ s y *
        Torus.partialDeriv i (propagator S.dyn S.ρ s t φ) y)) ∧
      sobolevNorm (N : ℝ) (Torus.partialDeriv i (fun y => S.ρ s y *
        Torus.partialDeriv i (propagator S.dyn S.ρ s t φ) y)) ≤ B := by
  have hd1 : 1 ≤ d := by have := S.hd; omega
  obtain ⟨ρβ, hth, -⟩ :=
    PDE.thermal_exists_unique_smooth S.hd S.s S.hs0 S.hsd S.β S.hβ S.V S.hV
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = N + 2 + PDE.mStar d + d + 6 := ⟨_, rfl⟩
  have hj : (d : ℝ) / 2 + 4 < (j : ℝ) := by
    have : d + 6 ≤ j := by omega
    have h2 : ((d + 6 : ℕ) : ℝ) ≤ j := by exact_mod_cast this
    push_cast at h2
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hjms : PDE.mStar d ≤ j := by omega
  have hjN : N + 2 ≤ j := by omega
  obtain ⟨R, Λ, hAtAll⟩ := HRS.ThermLin.Plan2.tl2dy_moving S hth j hj
  obtain ⟨C, Cs, -, -, hmain⟩ :=
    PDE.adjoint_torus_classical hd1 S.s S.hs0 S.hsd j hjms R 1 Λ (Torus.cbNorm (j + 3) S.V)
  have hφc : Continuous φ := p_cc5_cont hφ
  have hφS : MemSobolev (j : ℝ) φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ _
  obtain ⟨-, -, hsob, -⟩ := hmain S.dyn S.β⁻¹ t S.ρ (hAtAll t ht) t ⟨ht, le_rfl⟩ φ hφc hφS
  obtain ⟨c₀, hc₀, Λρ, hρb⟩ := HRS.Q40b.q40b_rho_bounds hd1 (HRS.T25.t25_traj S)
  obtain ⟨Cp, hCp⟩ := PDE.product_toolbox_frac_high hd1 ((N + 1 : ℕ) : ℝ) (Nat.cast_nonneg _)
  obtain ⟨Lam, hLam⟩ : ∃ Lam : ℝ, Lam = R.lambdaM (Cs (N + 2)) S.β⁻¹ (PDE.thetaOrder d S.s) :=
    ⟨_, rfl⟩
  have hceil : ⌈((N + 1 : ℕ) : ℝ)⌉₊ = N + 1 := Nat.ceil_natCast _
  rw [hceil] at hCp
  have hΛ0 : 0 ≤ Λρ (N + 1) :=
    le_trans (p_cc5_cbNorm_nonneg _ _) ((hρb 0 le_rfl).2.2.2 (N + 1))
  have hφn0 : 0 ≤ sobolevNorm ((N + 2 : ℕ) : ℝ) φ := Real.sqrt_nonneg _
  refine ⟨|Cp| * Λρ (N + 1) * (Real.exp (|Lam| * t) * sobolevNorm ((N + 2 : ℕ) : ℝ) φ), by positivity, ?_⟩
  intro s hs i
  have hf : Torus.IsSmooth (propagator S.dyn S.ρ s t φ) := ccd_propagator_smooth S hs.1 hs.2 hφ
  obtain ⟨hfm, hfn⟩ := hsob (N + 2) (by omega) hjN s hs
  rw [← hLam] at hfn
  obtain ⟨-, hρsm, -, hρcb⟩ := hρb s hs.1
  have e1 : (((N + 2 : ℕ) : ℝ)) = ((N + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  have e2 : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
  have hfm' : MemSobolev (((N + 1 : ℕ) : ℝ) + 1) (propagator S.dyn S.ρ s t φ) := by
    rw [← e1]; exact hfm
  have hfn' : sobolevNorm (((N + 1 : ℕ) : ℝ) + 1) (propagator S.dyn S.ρ s t φ) ≤
      Real.exp (Lam * (t - s)) * sobolevNorm ((N + 2 : ℕ) : ℝ) φ := by
    rw [← e1]; exact hfn
  obtain ⟨hdm, hdn⟩ := p_cc5_sobolev_partialDeriv ((N + 1 : ℕ) : ℝ) i (p_cc5_ck1 hf) hfm'
  obtain ⟨hpm, hpn⟩ := hCp (S.ρ s) (PDE.MFSemigroup.isCk_nat_of_isSmooth hρsm (N + 1)) _ hdm
  have hh : Torus.IsSmooth (fun y => S.ρ s y * Torus.partialDeriv i (propagator S.dyn S.ρ s t φ) y) :=
    p_cc5_isSmooth_mul hρsm (HRS.LocalDivAux.isSmooth_partialDeriv hf i)
  rw [e2] at hpm hpn
  obtain ⟨hwm, hwn⟩ := p_cc5_sobolev_partialDeriv (N : ℝ) i (p_cc5_ck1 hh) hpm
  refine ⟨hwm, hwn.trans (hpn.trans ?_)⟩
  have hcb0 := p_cc5_cbNorm_nonneg (N + 1) (S.ρ s)
  have hcb := hρcb (N + 1)
  have hn0 : 0 ≤ sobolevNorm ((N : ℝ) + 1) (Torus.partialDeriv i (propagator S.dyn S.ρ s t φ)) :=
    Real.sqrt_nonneg _
  have hexp : Real.exp (Lam * (t - s)) ≤ Real.exp (|Lam| * t) := by
    refine Real.exp_le_exp.2 ?_
    calc Lam * (t - s) ≤ |Lam| * (t - s) := mul_le_mul_of_nonneg_right (le_abs_self Lam) (sub_nonneg.2 hs.2)
      _ ≤ |Lam| * t := mul_le_mul_of_nonneg_left (by linarith [hs.1]) (abs_nonneg Lam)
  rw [e2] at hdn hfn'
  calc Cp * Torus.cbNorm (N + 1) (S.ρ s) *
        sobolevNorm ((N : ℝ) + 1) (Torus.partialDeriv i (propagator S.dyn S.ρ s t φ))
      ≤ |Cp| * Λρ (N + 1) * sobolevNorm ((N : ℝ) + 1 + 1) (propagator S.dyn S.ρ s t φ) := by
        have h1 : Cp * Torus.cbNorm (N + 1) (S.ρ s) ≤ |Cp| * Λρ (N + 1) :=
          mul_le_mul (le_abs_self Cp) hcb hcb0 (abs_nonneg Cp)
        calc _ ≤ (|Cp| * Λρ (N + 1)) * sobolevNorm ((N : ℝ) + 1)
              (Torus.partialDeriv i (propagator S.dyn S.ρ s t φ)) := mul_le_mul_of_nonneg_right h1 hn0
          _ ≤ _ := mul_le_mul_of_nonneg_left hdn (mul_nonneg (abs_nonneg Cp) hΛ0)
    _ ≤ |Cp| * Λρ (N + 1) * (Real.exp (Lam * (t - s)) * sobolevNorm ((N + 2 : ℕ) : ℝ) φ) :=
        mul_le_mul_of_nonneg_left hfn' (mul_nonneg (abs_nonneg Cp) hΛ0)
    _ ≤ _ := by gcongr

theorem ccd_noise_bound (S : PreparedData d) (T' : ℝ) (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T')
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc (0 : ℝ) T', ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      |∫ s in Set.Icc (0 : ℝ) (min r t), ∫ x,
          inner ℝ (Torus.grad (propagator S.dyn S.ρ s r ψ) x)
            (Torus.grad (propagator S.dyn S.ρ s t φ) x) * S.ρ s x| ≤
        C * HRS.sobolevNorm (-(N : ℝ)) ψ := by
  obtain ⟨C4, hC4, h4⟩ := ccd_dual_pairing_bound S N
  rcases ht.1.eq_or_lt with h0 | hpos
  · refine ⟨0, le_rfl, fun r hr ψ hψ => ?_⟩
    have hmin : min r t = 0 := by rw [← h0]; exact min_eq_right hr.1
    rw [hmin, Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
      integral_zero_measure]
    simp
  · obtain ⟨B, hB0, hB⟩ := p_cc5_uniform S N hpos hφ
    have hT' : 0 ≤ T' := ht.1.trans ht.2
    refine ⟨d * C4 * B * T', by positivity, fun r hr ψ hψ => ?_⟩
    have hψn0 : 0 ≤ HRS.sobolevNorm (-(N : ℝ)) ψ := Real.sqrt_nonneg _
    have hpt : ∀ s ∈ Set.Icc (0 : ℝ) (min r t), ‖∫ x,
          inner ℝ (Torus.grad (propagator S.dyn S.ρ s r ψ) x)
            (Torus.grad (propagator S.dyn S.ρ s t φ) x) * S.ρ s x‖ ≤
        (d * C4 * B) * HRS.sobolevNorm (-(N : ℝ)) ψ := by
      intro s hs
      have hsr : s ≤ r := hs.2.trans (min_le_left _ _)
      have hst : s ≤ t := hs.2.trans (min_le_right _ _)
      have hg : Torus.IsSmooth (propagator S.dyn S.ρ s r ψ) := ccd_propagator_smooth S hs.1 hsr hψ
      have hf : Torus.IsSmooth (propagator S.dyn S.ρ s t φ) := ccd_propagator_smooth S hs.1 hst hφ
      have hρsm : Torus.IsSmooth (S.ρ s) := by
        obtain ⟨c₀, hc₀, Λρ, hρb⟩ := HRS.Q40b.q40b_rho_bounds (by have := S.hd; omega)
          (HRS.T25.t25_traj S)
        exact (hρb s hs.1).2.1
      rw [Real.norm_eq_abs, p_cc5_ibp _ _ _ hg hf hρsm, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hi : ∀ i : Fin d, |∫ x, propagator S.dyn S.ρ s r ψ x * Torus.partialDeriv i
          (fun y => S.ρ s y * Torus.partialDeriv i (propagator S.dyn S.ρ s t φ) y) x| ≤
          C4 * B * HRS.sobolevNorm (-(N : ℝ)) ψ := by
        intro i
        have hh : Torus.IsSmooth (fun y => S.ρ s y *
            Torus.partialDeriv i (propagator S.dyn S.ρ s t φ) y) :=
          p_cc5_isSmooth_mul hρsm (HRS.LocalDivAux.isSmooth_partialDeriv hf i)
        have hw := HRS.LocalDivAux.isSmooth_partialDeriv hh i
        refine (h4 s r hs.1 hsr _ ψ hw (p_cc5_mean_partialDeriv i hh) hψ).trans ?_
        have := (hB s ⟨hs.1, hst⟩ i).2
        gcongr
      calc _ ≤ ∑ _i : Fin d, C4 * B * HRS.sobolevNorm (-(N : ℝ)) ψ :=
            Finset.sum_le_sum fun i _ => hi i
        _ = _ := by simp [Finset.sum_const]; ring
    have hμ : (volume : Measure ℝ).real (Set.Icc (0 : ℝ) (min r t)) = min r t := by
      rw [Real.volume_real_Icc_of_le (le_min hr.1 ht.1)]; simp
    have hmin : min r t ≤ T' := (min_le_left _ _).trans hr.2
    have hmin0 : 0 ≤ min r t := le_min hr.1 ht.1
    calc _ = ‖∫ s in Set.Icc (0 : ℝ) (min r t), ∫ x,
          inner ℝ (Torus.grad (propagator S.dyn S.ρ s r ψ) x)
            (Torus.grad (propagator S.dyn S.ρ s t φ) x) * S.ρ s x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ((d * C4 * B) * HRS.sobolevNorm (-(N : ℝ)) ψ) * (volume : Measure ℝ).real (Set.Icc (0 : ℝ) (min r t)) :=
        norm_setIntegral_le_of_norm_le_const (by simp) hpt
      _ ≤ ((d * C4 * B) * HRS.sobolevNorm (-(N : ℝ)) ψ) * T' := by
        rw [hμ]; exact mul_le_mul_of_nonneg_left hmin (by positivity)
      _ = _ := by ring

end HRS.MC.CrossCov

end
