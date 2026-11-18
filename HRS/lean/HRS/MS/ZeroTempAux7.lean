import HRS.MS.ZeroTempAux6

/-!
# SA11, packet C1a: weak jets are classical derivatives; integration by parts for `C^j` functions

* `sa11_ibp_jet_gen`: `∫ ∂^τ φ · ψ = ∫ φ · ψ'` for `φ ∈ C^j` (not compactly supported) and `ψ ∈ C_c^∞`.
* `sa11_weak_ibp`: for `F ∈ W^{m,p}`, `∫ F_τ ψ = ∫ F_0 ψ'` whenever `ψ'` is the transposed test of `ψ`.
* `sa11_weak_eq_classical`: if `F_0 = f` a.e. and `f ∈ C^j`, then `F_τ = ∂^τ f` a.e. (`|τ| = j ≤ m`).
* `sa11_iter_le_weak`, `sa11_eLp_iter_le_weak`: classical iterated derivatives of `f` are controlled by `‖F‖`.
-/

noncomputable section

open MeasureTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ}

/-! ### Integration by parts for `C^j` functions against `C_c^∞` tests -/

theorem sa11_ibp_one_gen {f ψ : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hψ : IsCcInfty ψ) (u : Euc d) :
    ∫ x, fderiv ℝ f x u * ψ x = -∫ x, f x * fderiv ℝ ψ x u := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hdψ : IsCcInfty (fun x => fderiv ℝ ψ x u) := by
    refine ⟨?_, hψ.2.fderiv_apply (𝕜 := ℝ) u⟩
    have h1 : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.1.fderiv_right (by simp)
    exact (ContinuousLinearMap.apply ℝ ℝ u).contDiff.comp h1
  have hcf : Continuous fun x => fderiv ℝ f x u :=
    (ContinuousLinearMap.apply ℝ ℝ u).continuous.comp (hf.continuous_fderiv one_ne_zero)
  have h1 : Integrable (fun x => fderiv ℝ f x u * ψ x) :=
    (hcf.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.mul_left
  have h2 : Integrable (fun x => f x * fderiv ℝ ψ x u) :=
    (hf.continuous.mul hdψ.1.continuous).integrable_of_hasCompactSupport hdψ.2.mul_left
  have h3 : Integrable (fun x => f x * ψ x) :=
    (hf.continuous.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.mul_left
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := u) h1 h2 h3
    (fun x _ => hfd x) (fun x _ => hψd x)
  linarith

theorem sa11_partialDeriv_succ_gen {j : ℕ} (τ : Fin (j + 1) → Fin d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ) (x : Euc d) :
    partialDeriv τ φ x =
      fderiv ℝ (partialDeriv (Fin.tail τ) φ) x (EuclideanSpace.single (τ 0) 1) := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ j φ) x :=
    (hφ.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)) x
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
      (fun l => EuclideanSpace.single (Fin.tail τ l) 1)).hasFDerivAt.comp x hdiff.hasFDerivAt
  have e : (fun y => iteratedFDeriv ℝ j φ y (fun l => EuclideanSpace.single (Fin.tail τ l) 1)) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
        (fun l => EuclideanSpace.single (Fin.tail τ l) 1)) ∘ iteratedFDeriv ℝ j φ := rfl
  rw [e, hL.fderiv]
  rfl

theorem sa11_contDiff_partialDeriv {j k : ℕ} (τ : Fin j → Fin d) {φ : Euc d → ℝ}
    (hφ : ContDiff ℝ ((j + k : ℕ) : WithTop ℕ∞) φ) : ContDiff ℝ (k : WithTop ℕ∞) (partialDeriv τ φ) := by
  show ContDiff ℝ (k : WithTop ℕ∞) fun x => iteratedFDeriv ℝ j φ x (fun l => EuclideanSpace.single (τ l) 1)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
      (fun l => EuclideanSpace.single (τ l) 1)).contDiff.comp
    (hφ.iteratedFDeriv_right (i := j) (by exact_mod_cast (le_of_eq (Nat.add_comm k j))) :
      ContDiff ℝ (k : WithTop ℕ∞) (iteratedFDeriv ℝ j φ))

theorem sa11_ibp_jet_gen : ∀ (j : ℕ) (τ : Fin j → Fin d) (ψ : Euc d → ℝ), IsCcInfty ψ →
    ∃ ψ' : Euc d → ℝ, IsCcInfty ψ' ∧ ∀ φ : Euc d → ℝ, ContDiff ℝ (j : WithTop ℕ∞) φ →
      ∫ x, partialDeriv τ φ x * ψ x = ∫ x, φ x * ψ' x := by
  intro j
  induction j with
  | zero =>
    intro τ ψ hψ
    refine ⟨ψ, hψ, fun φ hφ => ?_⟩
    rw [sa11_partialDeriv_zero]
  | succ j ih =>
    intro τ ψ hψ
    have hψ1 : IsCcInfty (fun x => fderiv ℝ ψ x (EuclideanSpace.single (τ 0) 1)) := by
      refine ⟨?_, hψ.2.fderiv_apply (𝕜 := ℝ) _⟩
      have h1 : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.1.fderiv_right (by simp)
      exact (ContinuousLinearMap.apply ℝ ℝ _).contDiff.comp h1
    obtain ⟨ψ', hψ', hψ'eq⟩ := ih (Fin.tail τ) _ hψ1
    refine ⟨fun x => -ψ' x, ⟨hψ'.1.neg, hψ'.2.neg⟩, fun φ hφ => ?_⟩
    have hg : ContDiff ℝ 1 (partialDeriv (Fin.tail τ) φ) :=
      sa11_contDiff_partialDeriv (j := j) (k := 1) (Fin.tail τ) (by simpa [add_comm] using hφ)
    have e1 : ∫ x, partialDeriv τ φ x * ψ x =
        ∫ x, fderiv ℝ (partialDeriv (Fin.tail τ) φ) x (EuclideanSpace.single (τ 0) 1) * ψ x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [sa11_partialDeriv_succ_gen τ hφ x])
    rw [e1, sa11_ibp_one_gen hg hψ, hψ'eq φ (hφ.of_le (by exact_mod_cast Nat.le_succ j)), ← integral_neg]
    congr 1
    funext x
    ring

/-! ### Weak jets -/

section Weak

variable {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the weak integration by parts for an element of `W^{m,p}` -/
theorem sa11_weak_ibp (F : WmpSpace d m p) (j : Fin (m + 1)) (i : Fin (j : ℕ) → Fin d) {ψ ψ' : Euc d → ℝ}
    (hψ : IsCcInfty ψ) (hψ' : IsCcInfty ψ')
    (hibp : ∀ φ : Euc d → ℝ, IsCcInfty φ → ∫ x, partialDeriv i φ x * ψ x = ∫ x, φ x * ψ' x) :
    ∫ y, ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) y ⟨j, i⟩ * ψ y =
      ∫ y, ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) y (wZero d m) * ψ' y := by
  have hF := sa11_denseRange_J (d := d) (m := m) (p := p) F
  rw [mem_closure_iff_seq_limit] at hF
  obtain ⟨x, hxr, hxt⟩ := hF
  choose φ hφ using hxr
  have hval : ∀ n, sa11_pairL (m := m) (p := p) ⟨j, i⟩ hψ.1.continuous hψ.2 ((x n : WmpSpace d m p) : WLp d m p) =
      sa11_pairL (m := m) (p := p) (wZero d m) hψ'.1.continuous hψ'.2 ((x n : WmpSpace d m p) : WLp d m p) := by
    intro n
    rw [sa11_pairL_apply, sa11_pairL_apply]
    have hn : (x n : WmpSpace d m p) = sa11_J (φ n) := (hφ n).symm
    rw [hn]
    have e1 : ∫ y, (((sa11_J (m := m) (p := p) (φ n) : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) y ⟨j, i⟩ * ψ y
        = ∫ y, partialDeriv i (φ n).1 y * ψ y := by
      refine integral_congr_ae ?_
      filter_upwards [sa11_J_coe (m := m) (p := p) (φ n)] with y hy
      rw [hy]; rfl
    have e2 : ∫ y, (((sa11_J (m := m) (p := p) (φ n) : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) y (wZero d m) * ψ' y
        = ∫ y, (φ n).1 y * ψ' y := by
      refine integral_congr_ae ?_
      filter_upwards [sa11_J_coe (m := m) (p := p) (φ n)] with y hy
      rw [hy]
      show partialDeriv (wZero d m).2 (φ n).1 y * ψ' y = _
      rw [show partialDeriv (wZero d m).2 (φ n).1 = (φ n).1 from sa11_partialDeriv_zero (wZero d m).2 (φ n).1]
    rw [e1, e2]
    exact hibp (φ n).1 (φ n).2
  have hlim1 : Filter.Tendsto (fun n => sa11_pairL (m := m) (p := p) ⟨j, i⟩ hψ.1.continuous hψ.2
      ((x n : WmpSpace d m p) : WLp d m p)) Filter.atTop
      (nhds (sa11_pairL (m := m) (p := p) ⟨j, i⟩ hψ.1.continuous hψ.2 (F : WLp d m p))) :=
    ((sa11_pairL (m := m) (p := p) ⟨j, i⟩ hψ.1.continuous hψ.2).continuous.tendsto _).comp
      ((continuous_subtype_val.tendsto F).comp hxt)
  have hlim2 : Filter.Tendsto (fun n => sa11_pairL (m := m) (p := p) (wZero d m) hψ'.1.continuous hψ'.2
      ((x n : WmpSpace d m p) : WLp d m p)) Filter.atTop
      (nhds (sa11_pairL (m := m) (p := p) (wZero d m) hψ'.1.continuous hψ'.2 (F : WLp d m p))) :=
    ((sa11_pairL (m := m) (p := p) (wZero d m) hψ'.1.continuous hψ'.2).continuous.tendsto _).comp
      ((continuous_subtype_val.tendsto F).comp hxt)
  have heq := tendsto_nhds_unique hlim1 (hlim2.congr fun n => (hval n).symm)
  rw [sa11_pairL_apply, sa11_pairL_apply] at heq
  exact heq

/-- Weak derivatives of a `C^j` function are its classical derivatives. -/
theorem sa11_weak_eq_classical (F : WmpSpace d m p) (j : Fin (m + 1)) (i : Fin (j : ℕ) → Fin d) {f : Euc d → ℝ}
    (hf : ContDiff ℝ ((j : ℕ) : WithTop ℕ∞) f)
    (hF : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = f x) :
    ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) x ⟨j, i⟩ = partialDeriv i f x := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := Fact.out
  have hcd : Continuous (partialDeriv i f) := (sa11_contDiff_partialDeriv (j := (j : ℕ)) (k := 0) i
    (by simpa using hf)).continuous
  have hlocG := (sa11_comp_memLp (m := m) (p := p) ⟨j, i⟩ (F : WLp d m p)).locallyIntegrable hp1
  have hdiff : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) x ⟨j, i⟩ - partialDeriv i f x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (hlocG.sub hcd.locallyIntegrable) fun g hg hgc => ?_
    obtain ⟨ψ', hψ', hibpf⟩ := sa11_ibp_jet_gen (j : ℕ) i g ⟨hg, hgc⟩
    have hweak := sa11_weak_ibp F j i ⟨hg, hgc⟩ hψ' (fun φ hφ => by
      have := hibpf φ (hφ.1.of_le (by exact_mod_cast le_top))
      exact this)
    have h1 : ∫ y, ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) y (wZero d m) * ψ' y = ∫ y, f y * ψ' y :=
      integral_congr_ae (hF.mono fun y hy => by simp only [hy])
    have h2 := hibpf f hf
    have hI1 := sa11_pair_integrable (m := m) (p := p) ⟨j, i⟩ hg.continuous hgc (F : WLp d m p)
    have hI2 : Integrable (fun y => partialDeriv i f y * g y) :=
      (hcd.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
    simp only [smul_eq_mul, Pi.sub_apply]
    have : ∫ x, g x * (((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) x ⟨j, i⟩ - partialDeriv i f x) =
        (∫ x, ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) x ⟨j, i⟩ * g x) - ∫ x, partialDeriv i f x * g x := by
      rw [← integral_sub hI1 hI2]
      congr 1; funext x; ring
    rw [this, hweak, h1, h2]; ring
  filter_upwards [hdiff] with x hx
  linarith

omit [Fact (2 ≤ p)] in
/-- If `F`'s components of order `j` are the classical derivatives of `f`, then `‖D^j f‖ ≤ d^j ‖F‖` a.e. -/
theorem sa11_iter_le_weak {f : Euc d → ℝ} {j : ℕ} (hj : j < m + 1) (F : WLp d m p)
    (hF : ∀ i : Fin j → Fin d, ∀ᵐ x ∂(volume : Measure (Euc d)),
      (F : Euc d → (WIndex d m → ℝ)) x ⟨⟨j, hj⟩, i⟩ = partialDeriv i f x) :
    ∀ᵐ x ∂(volume : Measure (Euc d)), ‖iteratedFDeriv ℝ j f x‖ ≤ (d : ℝ) ^ j * ‖(F : Euc d → (WIndex d m → ℝ)) x‖ := by
  have hall : ∀ᵐ x ∂(volume : Measure (Euc d)), ∀ i : Fin j → Fin d,
      (F : Euc d → (WIndex d m → ℝ)) x ⟨⟨j, hj⟩, i⟩ = partialDeriv i f x := ae_all_iff.2 hF
  filter_upwards [hall] with x hx
  refine (sa11_opNorm_le_sum _).trans ?_
  have hterm : ∀ i : Fin j → Fin d,
      |iteratedFDeriv ℝ j f x (fun l => EuclideanSpace.single (i l) 1)| ≤ ‖(F : Euc d → (WIndex d m → ℝ)) x‖ := by
    intro i
    have := norm_le_pi_norm ((F : Euc d → (WIndex d m → ℝ)) x) (⟨⟨j, hj⟩, i⟩ : WIndex d m)
    rw [hx i, Real.norm_eq_abs] at this
    exact this
  calc ∑ i : Fin j → Fin d, |iteratedFDeriv ℝ j f x (fun l => EuclideanSpace.single (i l) 1)|
      ≤ ∑ _i : Fin j → Fin d, ‖(F : Euc d → (WIndex d m → ℝ)) x‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) ^ j * ‖(F : Euc d → (WIndex d m → ℝ)) x‖ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [Fintype.card_fun]

end Weak

end HRS.MS.ZeroTemp
