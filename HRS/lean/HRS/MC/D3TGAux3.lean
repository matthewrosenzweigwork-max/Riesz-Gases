import HRS.MC.D3TGAux2

/-!
# Packet D3TG, helper 3: the kernel `K t y = b t^{d-s} (P φ_t (y) - ∫ φ) / t`, smoothness and derivative bounds
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3TG

open HRS HRS.MC.D3EW HRS.MC.Per HRS.MC.D3T1 HRS.MC.FDLE

variable {d : ℕ}

/-- The integrand of the torus representation, as a function of the scale `t` and a point `y ∈ ℝ^d`. -/
def d3tgK (ψ : Euc d → ℝ) (s b t : ℝ) (y : Euc d) : ℝ :=
  b * (t ^ ((d : ℝ) - s) * (fdlPer (fdlPhiScale ψ t) (Torus.mk y) - ∫ x, fdlPhi ψ x) / t)

lemma d3tgK_eq' (ψ : Euc d → ℝ) (s b : ℝ) {t : ℝ} (ht : 0 < t) (y : Euc d) :
    d3tgK ψ s b t y
      = (b * t ^ ((d : ℝ) - s - 1)) * (fdlPer (fdlPhiScale ψ t) (Torus.mk y) - ∫ x, fdlPhi ψ x) := by
  unfold d3tgK
  rw [Real.rpow_sub_one ht.ne']
  field_simp

lemma d3tgK_eq (ψ : Euc d → ℝ) (s b : ℝ) {t : ℝ} (ht : 0 < t) :
    d3tgK ψ s b t = fun w : Euc d =>
      (b * t ^ ((d : ℝ) - s - 1)) * (∑' n : Lattice d, fdlPhiScale ψ t (w + Lattice.toEuc n))
        + (-(b * t ^ ((d : ℝ) - s - 1)) * ∫ x, fdlPhi ψ x) := by
  funext w
  rw [d3tgK_eq' ψ s b ht, per_fdlPer_mk]
  ring

lemma d3tgK_contDiffOn {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s b : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (d3tgK ψ s b)) (Ioi (0 : ℝ) ×ˢ (univ : Set (Euc d))) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨t0, y0⟩ := p
  have ht0 : 0 < t0 := hp.1
  set I : ℝ := ∫ x, fdlPhi ψ x with hI
  set S : Finset (Lattice d) :=
    (per_finite_lattice (d := d) (t0 + 1 + (‖y0‖ + 1))).toFinset with hS
  have o1 : IsOpen {q : ℝ × Euc d | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  have o2 : IsOpen {q : ℝ × Euc d | q.1 < t0 + 1} := isOpen_lt continuous_fst continuous_const
  have o3 : IsOpen {q : ℝ × Euc d | ‖q.2‖ < ‖y0‖ + 1} :=
    isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
  have e1 : ∀ᶠ q in 𝓝 (t0, y0), 0 < q.1 := o1.mem_nhds ht0
  have e2 : ∀ᶠ q in 𝓝 (t0, y0), q.1 < t0 + 1 := o2.mem_nhds (by show t0 < t0 + 1; linarith)
  have e3 : ∀ᶠ q in 𝓝 (t0, y0), ‖q.2‖ < ‖y0‖ + 1 := o3.mem_nhds (by show ‖y0‖ < ‖y0‖ + 1; linarith)
  have hev : Function.uncurry (d3tgK ψ s b) =ᶠ[𝓝 (t0, y0)] fun q : ℝ × Euc d =>
      b * (q.1 ^ ((d : ℝ) - s) *
        ((∑ n ∈ S, (q.1 ^ d)⁻¹ * fdlPhi ψ (q.1⁻¹ • (q.2 + Lattice.toEuc n))) - I) / q.1) := by
    filter_upwards [e1, e2, e3] with q hq1 hq2 hq3
    change d3tgK ψ s b q.1 q.2 = _
    unfold d3tgK
    rw [per_fdlPer_mk]
    have : ∑' n : Lattice d, fdlPhiScale ψ q.1 (q.2 + Lattice.toEuc n)
        = ∑ n ∈ S, fdlPhiScale ψ q.1 (q.2 + Lattice.toEuc n) := by
      refine tsum_eq_sum fun n hn => ?_
      apply per_phiScale_zero hψ hq1
      by_contra hlt
      apply hn
      rw [hS, Set.Finite.mem_toFinset]
      show ‖Lattice.toEuc n‖ ≤ t0 + 1 + (‖y0‖ + 1)
      have h2 : ‖Lattice.toEuc n‖ ≤ ‖q.2 + Lattice.toEuc n‖ + ‖q.2‖ := by
        have := norm_sub_le (q.2 + Lattice.toEuc n) q.2
        simpa using this
      linarith [not_le.mp hlt]
    rw [this]
    rfl
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hq0 : (t0, y0).1 ≠ 0 := ht0.ne'
  have h1 : ContDiffAt ℝ ∞ (fun q : ℝ × Euc d => q.1 ^ ((d : ℝ) - s)) (t0, y0) :=
    (Real.contDiffAt_rpow_const_of_ne hq0).comp (t0, y0) contDiff_fst.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun q : ℝ × Euc d => q.1⁻¹) (t0, y0) :=
    (contDiffAt_inv ℝ hq0).comp (t0, y0) contDiff_fst.contDiffAt
  have h3 : ContDiffAt ℝ ∞ (fun q : ℝ × Euc d => (q.1 ^ d)⁻¹) (t0, y0) :=
    (contDiff_fst.contDiffAt.pow d).inv (pow_ne_zero d hq0)
  have h4 : ContDiffAt ℝ ∞ (fun q : ℝ × Euc d =>
      ∑ n ∈ S, (q.1 ^ d)⁻¹ * fdlPhi ψ (q.1⁻¹ • (q.2 + Lattice.toEuc n))) (t0, y0) := by
    refine ContDiffAt.sum fun n _ => h3.mul ?_
    exact ((d3ew_phi_smooth hψ).contDiffAt).comp (t0, y0)
      (h2.smul (contDiff_snd.contDiffAt.add contDiffAt_const))
  exact contDiffAt_const.mul ((h1.mul (h4.sub contDiffAt_const)).div contDiff_fst.contDiffAt hq0)

lemma d3tg_diter_affine_pos {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (c e : ℝ) {k : ℕ} (hk : 1 ≤ k)
    (y : Euc d) :
    ‖iteratedFDeriv ℝ k (fun w => c * g w + e) y‖ = |c| * ‖iteratedFDeriv ℝ k g y‖ := by
  have hgk : ContDiffAt ℝ k g y :=
    (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  have : (fun w => c * g w + e) = (fun w => c • g w) + (fun _ => e) := by
    funext w; simp [smul_eq_mul]
  rw [this, iteratedFDeriv_add_apply (hgk.const_smul c) contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, add_zero, iteratedFDeriv_const_smul_apply' hgk,
    norm_smul, Real.norm_eq_abs]

lemma d3tg_pow_alg {t : ℝ} (ht : 0 < t) (k : ℕ) (s : ℝ) :
    t ^ ((d : ℝ) - s - 1) * ((t ^ d)⁻¹ * (t⁻¹) ^ k) = t ^ (-((k : ℝ) + s) - 1) := by
  rw [← Real.rpow_natCast t d, ← Real.rpow_neg ht.le, ← Real.rpow_natCast t⁻¹ k,
    Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, ← Real.rpow_add ht, ← Real.rpow_add ht]
  congr 1
  ring

lemma d3tgK_smooth {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s b : ℝ) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (fun w : Euc d => ∑' n : Lattice d, fdlPhiScale ψ t (w + Lattice.toEuc n)) :=
  per_G_contDiff (per_phiScale_contDiff hψ t) (fun x hx => per_phiScale_zero hψ ht hx.le)

/-- Small scales `0 < t ≤ 1`. -/
lemma d3tgK_small {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s b : ℝ) (k : ℕ) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ k (fdlPhi ψ) x‖ ≤ M) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (y : Euc d) {a : ℝ} (ha : ∀ n : Lattice d, a ≤ ‖y + Lattice.toEuc n‖) :
    ‖iteratedFDeriv ℝ k (d3tgK ψ s b t) y‖ ≤
      (if a ≤ t then |b| * 3 ^ d * M * t ^ (-((k : ℝ) + s) - 1) else 0)
        + |b| * |∫ x, fdlPhi ψ x| * t ^ ((d : ℝ) - s - 1) := by
  have hQ := d3tg_dper_bound hψ ht ht1 k hM y ha
  have hc : 0 < t ^ ((d : ℝ) - s - 1) := Real.rpow_pos_of_pos ht _
  have hcabs : |b * t ^ ((d : ℝ) - s - 1)| = |b| * t ^ ((d : ℝ) - s - 1) := by
    rw [abs_mul, abs_of_pos hc]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hmain : |b * t ^ ((d : ℝ) - s - 1)| * ((if a ≤ t then 3 ^ d * ((t ^ d)⁻¹ * (t⁻¹) ^ k * M) else 0))
      = (if a ≤ t then |b| * 3 ^ d * M * t ^ (-((k : ℝ) + s) - 1) else 0) := by
    split_ifs
    · rw [hcabs, ← d3tg_pow_alg ht k s]; ring
    · simp
  rw [d3tgK_eq ψ s b ht]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [norm_iteratedFDeriv_zero] at hQ ⊢
    set Q : ℝ := ∑' n : Lattice d, fdlPhiScale ψ t (y + Lattice.toEuc n) with hQdef
    have hQ' : |Q| ≤ if a ≤ t then 3 ^ d * ((t ^ d)⁻¹ * (t⁻¹) ^ 0 * M) else 0 := by
      simpa [hQdef] using hQ
    calc |b * t ^ ((d : ℝ) - s - 1) * Q + -(b * t ^ ((d : ℝ) - s - 1)) * ∫ x, fdlPhi ψ x|
        ≤ |b * t ^ ((d : ℝ) - s - 1) * Q| + |-(b * t ^ ((d : ℝ) - s - 1)) * ∫ x, fdlPhi ψ x| :=
          abs_add_le _ _
      _ ≤ |b * t ^ ((d : ℝ) - s - 1)| * (if a ≤ t then 3 ^ d * ((t ^ d)⁻¹ * (t⁻¹) ^ 0 * M) else 0)
            + |b| * |∫ x, fdlPhi ψ x| * t ^ ((d : ℝ) - s - 1) := by
          have e1 : |b * t ^ ((d : ℝ) - s - 1) * Q| = |b * t ^ ((d : ℝ) - s - 1)| * |Q| := abs_mul _ _
          have e2 : |-(b * t ^ ((d : ℝ) - s - 1)) * ∫ x, fdlPhi ψ x|
              = |b| * |∫ x, fdlPhi ψ x| * t ^ ((d : ℝ) - s - 1) := by
            rw [abs_mul, abs_neg, hcabs]; ring
          rw [e1, e2]
          gcongr
      _ = _ := by rw [hmain]
  · rw [d3tg_diter_affine_pos (d3tgK_smooth hψ s b ht) _ _ hk y]
    calc |b * t ^ ((d : ℝ) - s - 1)| * ‖iteratedFDeriv ℝ k (fun w => ∑' n : Lattice d,
            fdlPhiScale ψ t (w + Lattice.toEuc n)) y‖
        ≤ |b * t ^ ((d : ℝ) - s - 1)| * (if a ≤ t then 3 ^ d * ((t ^ d)⁻¹ * (t⁻¹) ^ k * M) else 0) := by
          gcongr
      _ = _ := hmain
      _ ≤ _ := by
          have : 0 ≤ |b| * |∫ x, fdlPhi ψ x| * t ^ ((d : ℝ) - s - 1) := by positivity
          linarith

end HRS.MC.D3TG
