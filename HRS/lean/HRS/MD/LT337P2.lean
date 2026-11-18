import HRS.Kernel.Riesz
import HRS.PDE.MeanFieldOneLe
import HRS.PDE.MeanFieldAux
import HRS.PDE.Classical
import HRS.PDE.Fourier
import HRS.PDE.Hadamard
import HRS.PDE.TorusCalculus
import HRS.Kernel.GradBasic
import HRS.Appendix.B15CAux1

/-!
# Packet LT2 (chunk D): the Coulomb kernel on the torus (Green identity, `Δ g = c_d` off the origin)

`lt2_green_proof` is the statement `HRS.MD.LT337.lt2_green` (M L3137-3139, 3147).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate
open HRS

namespace HRS.MD.LT337P2

variable {d N : ℕ}

/-- The Coulomb constant `c_d` (same definition as `HRS.MD.LT337.cd`). -/
def cd (d : ℕ) : ℝ := rieszConst d ((d : ℝ) - 2)

theorem lt2_cd_pos (hd : 2 ≤ d) : 0 < cd d := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact rieszConst_pos hd (by linarith) (by linarith)

/-- Part (i): the weak form of `-Δ g = c_d (δ_0 - 1)`. -/
theorem lt2_weak (hd : 2 ≤ d) (ψ : Torus d → ℝ) (hψ : Torus.IsCk 2 ψ) (x : Torus d) :
    ∫ y, periodicRiesz d ((d : ℝ) - 2) (x - y) * Torus.laplacian ψ y =
        cd d * ((∫ y, ψ y) - ψ x) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  have hgi : Integrable (periodicRiesz d ((d : ℝ) - 2)) :=
    PDE.MFOneLe.integrable_periodicRiesz (by omega) _ hs0 hsd
  have hψ1 : Torus.IsCk 1 ψ := hψ.of_le (by norm_num)
  have hψc : Continuous ψ := PDE.MFAux.continuous_of_isCk hψ1
  have hlc : Continuous (Torus.laplacian ψ) := PDE.ClassicalAux.continuous_laplacian hψ
  have hF : Continuous (convFun (periodicRiesz d ((d : ℝ) - 2)) (Torus.laplacian ψ)) :=
    PDE.MFAux.continuous_convFun hgi hlc
  have hR : Continuous (fun x => cd d * ((∫ y, ψ y) - ψ x)) :=
    continuous_const.mul (continuous_const.sub hψc)
  have key : convFun (periodicRiesz d ((d : ℝ) - 2)) (Torus.laplacian ψ) =
      fun x => cd d * ((∫ y, ψ y) - ψ x) := by
    refine PDE.ClassicalAux.eq_of_coeffOf_eq hF hR ?_
    funext k
    have e1 := PDE.MFOneLe.coeffOf_convFun (by omega) ((d : ℝ) - 2) hs0 hsd hlc k
    have e2 := congrFun (PDE.coeffOf_laplacian ψ hψ) k
    have e3 : PDE.coeffOf (fun x => cd d * ((∫ y, ψ y) - ψ x)) k =
        (cd d : ℂ) * (PDE.coeffOf (fun _ => ∫ y, ψ y) k - PDE.coeffOf ψ k) := by
      have := congrFun (PDE.ClassicalAux.coeffOf_const_mul (cd d) (fun x => (∫ y, ψ y) - ψ x)) k
      rw [this]
      congr 1
      exact congrFun (PDE.ClassicalAux.coeffOf_sub (g := fun _ => ∫ y, ψ y) (h := ψ)
        (integrable_const _) (PDE.ClassicalAux.integrable_of_continuous hψc)) k
    rw [e1, e2, e3, PDE.coeffOf_const]
    by_cases hk : k = 0
    · subst hk
      have h0 : PDE.coeffOf ψ 0 = ((∫ y, ψ y : ℝ) : ℂ) := by
        rw [PDE.coeffOf_eq_fcoef]
        simp [Torus.fcoef, Torus.mode_zero, integral_complex_ofReal]
      simp [rieszCoeff, PDE.deltaCoeff, h0]
    · simp only [PDE.deltaCoeff, hk, if_false]
      simp [PDE.laplaceCoeff, rieszCoeff, hk]
      have hk' : 0 < Lattice.enorm k := by
        unfold Lattice.enorm
        rw [norm_pos_iff]
        intro h
        apply hk
        funext i
        have := congrArg (fun v => v i) h
        simpa [Lattice.toEuc] using this
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hen : ((Lattice.enorm k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk'.ne'
      unfold cd
      field_simp
      ring
  exact congrFun key x


/-! ### Part (ii): `Δ g = c_d` off the origin -/

open KernelAux in
/-- Periodic functions on the covering space descend (copy of `HRS.periodic_rep_mk`). -/
theorem lt2_exists_lattice {x y : Euc d} (h : Torus.mk x = Torus.mk y) :
    ∃ n : Lattice d, x = y + Lattice.toEuc n := by
  have h0 : Torus.mk (x - y) = 0 := by rw [KernelGrad.mk_sub, h, sub_self]
  have hi : ∀ i : Fin d, ∃ n : ℤ, n • (1 : ℝ) = (x - y) i := fun i => by
    have := congrFun h0 i
    exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 this
  choose n hn using hi
  refine ⟨n, ?_⟩
  ext i
  have := hn i
  simp only [zsmul_eq_mul, mul_one] at this
  simp only [Lattice.toEuc, PiLp.add_apply]
  have h2 : (x - y) i = x i - y i := rfl
  linarith

theorem lt2_periodic_rep_mk {E : Type*} (G : Euc d → E)
    (hG : ∀ (x : Euc d) (n : Lattice d), G (x + Lattice.toEuc n) = G x) (y : Euc d) :
    G (Torus.rep (Torus.mk y)) = G y := by
  obtain ⟨n, hn⟩ := lt2_exists_lattice (x := Torus.rep (Torus.mk y)) (y := y) (Torus.mk_rep _)
  rw [hn, hG]

theorem lt2_laplacian_mk (φ : Torus d → ℝ) (y : Euc d) :
    Torus.laplacian φ (Torus.mk y) = Laplacian.laplacian (Torus.lift φ) y :=
  lt2_periodic_rep_mk (Laplacian.laplacian (Torus.lift φ)) (fun x n => by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift φ)
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    simp only [Torus.iteratedFDeriv_lift_periodic]) y

/-! #### Periodised bumps -/

/-- The torus function `t ↦ ∑_n f(rep t + n)`. -/
def perT (f : Euc d → ℝ) (t : Torus d) : ℝ := KernelAux.perz f (Torus.rep t)

theorem lt2_perz_add (f : Euc d → ℝ) (y : Euc d) (m : Lattice d) :
    KernelAux.perz f (y + Lattice.toEuc m) = KernelAux.perz f y := by
  unfold KernelAux.perz
  rw [← (Equiv.addLeft m).tsum_eq (fun n => f (y + Lattice.toEuc n))]
  refine tsum_congr fun n => ?_
  simp only [Equiv.coe_addLeft, KernelAux.toEuc_add, add_assoc]

theorem lt2_perT_mk (f : Euc d → ℝ) (v : Euc d) : perT f (Torus.mk v) = KernelAux.perz f v := by
  unfold perT
  obtain ⟨m0, hm0⟩ := KernelAux.rep_mk_eq v
  rw [hm0, lt2_perz_add]

theorem lt2_lift_perT (f : Euc d → ℝ) : Torus.lift (perT f) = KernelAux.perz f := by
  funext v
  exact lt2_perT_mk f v

theorem lt2_perT_isSmooth {f : Euc d → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hsupp : ∀ y, 1/8 ≤ ‖y‖ → f y = 0) :
    Torus.IsSmooth (perT f) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [lt2_lift_perT]
  exact KernelAux.contDiff_perz hf hsupp

theorem lt2_perz_nonneg {f : Euc d → ℝ} (hf : ∀ y, 0 ≤ f y) (v : Euc d) : 0 ≤ KernelAux.perz f v :=
  tsum_nonneg fun n => hf _

theorem lt2_perz_eq_zero {f : Euc d → ℝ} {r : ℝ} (hr : ∀ y, r ≤ ‖y‖ → f y = 0) {w : Euc d}
    (hw : ∀ n : Lattice d, r ≤ ‖w + Lattice.toEuc n‖) : KernelAux.perz f w = 0 := by
  unfold KernelAux.perz
  exact (tsum_congr fun n => hr _ (hw n)).trans tsum_zero

theorem lt2_perz_ne_zero {f : Euc d → ℝ} {w : Euc d} (h : KernelAux.perz f w ≠ 0) :
    ∃ n : Lattice d, f (w + Lattice.toEuc n) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  unfold KernelAux.perz
  exact (tsum_congr hcon).trans tsum_zero

theorem lt2_mk_toEuc (n : Lattice d) : Torus.mk (Lattice.toEuc n) = 0 := by
  funext i
  exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2 ⟨n i, by simp [Lattice.toEuc]⟩

theorem lt2_toEuc_neg (n : Lattice d) : Lattice.toEuc (-n) = -Lattice.toEuc n := by
  ext i; simp [Lattice.toEuc]

/-- A point of the torus other than `0` has positive distance to the lattice. -/
theorem lt2_lattice_dist {w : Euc d} (hw : Torus.mk w ≠ 0) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 16 ∧ ∀ n : Lattice d, 4 * b ≤ ‖w + Lattice.toEuc n‖ := by
  have hfin := KernelAux.finite_near w
  have hpos : ∀ n ∈ {n : Lattice d | ‖w + Lattice.toEuc n‖ < 1 / 4}, 0 < ‖w + Lattice.toEuc n‖ := by
    intro n _
    rw [norm_pos_iff]
    intro h0
    apply hw
    have : w = Lattice.toEuc (-n) := by rw [lt2_toEuc_neg]; exact eq_neg_of_add_eq_zero_left h0
    rw [this]
    exact lt2_mk_toEuc _
  have hev : ∀ᶠ b in 𝓝[>] (0 : ℝ), (∀ n ∈ {n : Lattice d | ‖w + Lattice.toEuc n‖ < 1 / 4},
      4 * b ≤ ‖w + Lattice.toEuc n‖) ∧ b ≤ 1 / 16 ∧ 0 < b := by
    refine ((Filter.eventually_all_finite hfin).2 fun n hn => ?_).and (Filter.Eventually.and ?_ ?_)
    · have h := hpos n hn
      have : ∀ᶠ b in 𝓝 (0 : ℝ), 4 * b ≤ ‖w + Lattice.toEuc n‖ := by
        have hc : Continuous fun b : ℝ => 4 * b := by fun_prop
        exact (hc.tendsto 0).eventually (Iic_mem_nhds (by simpa using h))
      exact nhdsWithin_le_nhds this
    · exact nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num))
    · exact self_mem_nhdsWithin
  obtain ⟨b, hb1, hb2, hb3⟩ := hev.exists
  refine ⟨b, hb3, hb2, fun n => ?_⟩
  by_cases hn : ‖w + Lattice.toEuc n‖ < 1 / 4
  · exact hb1 n hn
  · push Not at hn
    linarith

/-- The smooth bump with inner radius `a` and outer radius `r`. -/
def bf (a r : ℝ) (ha : 0 < a) (har : a < r) : Euc d → ℝ :=
  fun y => (⟨a, r, ha, har⟩ : ContDiffBump (0 : Euc d)) y

theorem bf_smooth (a r : ℝ) (ha : 0 < a) (har : a < r) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bf (d := d) a r ha har) :=
  (⟨a, r, ha, har⟩ : ContDiffBump (0 : Euc d)).contDiff

theorem bf_nonneg (a r : ℝ) (ha : 0 < a) (har : a < r) (y : Euc d) : 0 ≤ bf a r ha har y :=
  (⟨a, r, ha, har⟩ : ContDiffBump (0 : Euc d)).nonneg

theorem bf_one (a r : ℝ) (ha : 0 < a) (har : a < r) {y : Euc d} (hy : ‖y‖ ≤ a) :
    bf a r ha har y = 1 :=
  (⟨a, r, ha, har⟩ : ContDiffBump (0 : Euc d)).one_of_mem_closedBall (by simpa using hy)

theorem bf_zero (a r : ℝ) (ha : 0 < a) (har : a < r) {y : Euc d} (hy : r ≤ ‖y‖) :
    bf a r ha har y = 0 :=
  (⟨a, r, ha, har⟩ : ContDiffBump (0 : Euc d)).zero_of_le_dist (by simpa using hy)

theorem bf_zero8 (a r : ℝ) (ha : 0 < a) (har : a < r) (hr : r ≤ 1 / 8) :
    ∀ y : Euc d, 1 / 8 ≤ ‖y‖ → bf a r ha har y = 0 := fun y hy => bf_zero a r ha har (hr.trans hy)

theorem perT_support (a r : ℝ) (ha : 0 < a) (har : a < r) {t : Torus d}
    (ht : perT (bf a r ha har) t ≠ 0) : ∃ v : Euc d, ‖v‖ < r ∧ t = Torus.mk v := by
  obtain ⟨n, hn⟩ := lt2_perz_ne_zero ht
  refine ⟨Torus.rep t + Lattice.toEuc n, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    exact hn (bf_zero a r ha har hcon)
  · rw [KernelGrad.mk_add, Torus.mk_rep, lt2_mk_toEuc, add_zero]

theorem perT_zero (a r : ℝ) (ha : 0 < a) (har : a < r) (hr : r ≤ 1 / 8) :
    perT (bf (d := d) a r ha har) (Torus.mk 0) = 1 := by
  rw [lt2_perT_mk, KernelAux.perz_eq (bf_zero8 a r ha har hr) (by simp)]
  exact bf_one a r ha har (by simp; exact ha.le)

theorem perT_lap_support (a r : ℝ) (ha : 0 < a) (har : a < r) {t : Torus d}
    (ht : Torus.laplacian (perT (bf a r ha har)) t ≠ 0) : ∃ v : Euc d, ‖v‖ < 2 * r ∧ t = Torus.mk v := by
  by_contra hcon
  push Not at hcon
  apply ht
  have hu : ∀ n : Lattice d, 2 * r ≤ ‖Torus.rep t + Lattice.toEuc n‖ := by
    intro n
    by_contra h
    push Not at h
    apply hcon (Torus.rep t + Lattice.toEuc n) h
    rw [KernelGrad.mk_add, Torus.mk_rep, lt2_mk_toEuc, add_zero]
  have hr : 0 < r := ha.trans har
  have e : Torus.laplacian (perT (bf a r ha har)) t =
      Laplacian.laplacian (KernelAux.perz (bf a r ha har)) (Torus.rep t) := by
    conv_lhs => rw [← Torus.mk_rep t]
    rw [lt2_laplacian_mk, lt2_lift_perT]
  rw [e]
  have hev : KernelAux.perz (bf a r ha har) =ᶠ[𝓝 (Torus.rep t)] fun _ => (0 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds (Torus.rep t) hr] with u' hu'
    refine lt2_perz_eq_zero (r := r) (fun y hy => bf_zero a r ha har hy) fun n => ?_
    have h1 : dist u' (Torus.rep t) < r := hu'
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (Torus.rep t + Lattice.toEuc n) (u' + Lattice.toEuc n)
    have h3 : Torus.rep t + Lattice.toEuc n - (u' + Lattice.toEuc n) = Torus.rep t - u' := by abel
    rw [h3, norm_sub_rev] at h2
    have := hu n
    linarith
  rw [(InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds]
  simp

theorem lt2_mk_zero : Torus.mk (0 : Euc d) = 0 := by
  funext i; simp [Torus.mk]

/-- The cut-off kernel `(1 - χ_b) g`, smooth on the whole torus. -/
def f0 (d : ℕ) (b : ℝ) (hb : 0 < b) : Torus d → ℝ :=
  fun t => (1 - perT (bf (d := d) b (2 * b) hb (by linarith)) t) * periodicRiesz d ((d : ℝ) - 2) t

theorem lt2_f0_lift (b : ℝ) (hb : 0 < b) (w : Euc d) :
    Torus.lift (f0 d b hb) w =
      (1 - KernelAux.perz (bf (d := d) b (2 * b) hb (by linarith)) w) *
        Torus.lift (periodicRiesz d ((d : ℝ) - 2)) w := by
  simp only [Torus.lift, Function.comp, f0, lt2_perT_mk]

theorem lt2_f0_smooth (hd : 2 ≤ d) (b : ℝ) (hb : 0 < b) (hb16 : b ≤ 1 / 16) :
    Torus.IsSmooth (f0 d b hb) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (KernelAux.perz (bf (d := d) b (2 * b) hb (by linarith))) :=
    KernelAux.contDiff_perz (bf_smooth _ _ _ _) (bf_zero8 _ _ _ _ (by linarith))
  unfold Torus.IsSmooth Torus.IsCk
  have hl : Torus.lift (f0 d b hb) = fun w =>
      (1 - KernelAux.perz (bf (d := d) b (2 * b) hb (by linarith)) w) *
        Torus.lift (periodicRiesz d ((d : ℝ) - 2)) w := funext (lt2_f0_lift b hb)
  rw [hl, contDiff_iff_contDiffAt]
  intro w
  by_cases hw : Torus.mk w = 0
  · obtain ⟨n, hn⟩ := lt2_exists_lattice (x := w) (y := 0) (by rw [hw, lt2_mk_zero])
    have hev : (fun w => (1 - KernelAux.perz (bf (d := d) b (2 * b) hb (by linarith)) w) *
        Torus.lift (periodicRiesz d ((d : ℝ) - 2)) w) =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds w hb] with w' hw'
      have h1 : ‖w' + Lattice.toEuc (-n)‖ < b := by
        have : w' + Lattice.toEuc (-n) = w' - w := by
          rw [lt2_toEuc_neg, hn]; simp [sub_eq_add_neg]
        rw [this]
        have := hw'
        rwa [Metric.mem_ball, dist_eq_norm] at this
      have h2 : KernelAux.perz (bf (d := d) b (2 * b) hb (by linarith)) w' = 1 := by
        rw [← lt2_perz_add _ w' (-n), KernelAux.perz_eq (bf_zero8 _ _ _ _ (by linarith))
          (by linarith)]
        exact bf_one _ _ _ _ h1.le
      simp [h2]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  · exact ((contDiff_const.sub hsm).contDiffAt).mul
      (b15c_contDiffAt_lift_periodicRiesz (by omega) hs0 hsd hw)

/-- Green's second identity on the torus. -/
theorem lt2_ibp {f ψ : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hψ : Torus.IsCk 2 ψ) :
    ∫ y, f y * Torus.laplacian ψ y = ∫ y, Torus.laplacian f y * ψ y := by
  have hf1 : Torus.IsCk 1 f := hf.of_le (by norm_num)
  have hψ1 : Torus.IsCk 1 ψ := hψ.of_le (by norm_num)
  have hfc : Continuous f := PDE.MFAux.continuous_of_isCk hf1
  have hψc : Continuous ψ := PDE.MFAux.continuous_of_isCk hψ1
  have h1 : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j ψ) := fun j => PDE.isCk_one_partialDeriv j ψ hψ
  have h2 : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j f) := fun j => PDE.isCk_one_partialDeriv j f hf
  have c1 : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j ψ)) := fun j =>
    PDE.continuous_partialDeriv j _ (h1 j)
  have c2 : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j f)) := fun j =>
    PDE.continuous_partialDeriv j _ (h2 j)
  have hint : ∀ {u : Torus d → ℝ}, Continuous u → Integrable u := fun hu =>
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have eL : (fun y => f y * Torus.laplacian ψ y) =
      fun y => ∑ j, f y * Torus.partialDeriv j (Torus.partialDeriv j ψ) y := by
    funext y
    rw [PDE.laplacian_eq_sum ψ hψ, Finset.mul_sum]
  have eR : (fun y => Torus.laplacian f y * ψ y) =
      fun y => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j f) y * ψ y := by
    funext y
    rw [PDE.laplacian_eq_sum f hf, Finset.sum_mul]
  rw [eL, eR, integral_finsetSum Finset.univ (f :=
      fun (j : Fin d) (y : Torus d) => f y * Torus.partialDeriv j (Torus.partialDeriv j ψ) y)
      (fun j _ => hint (hfc.mul (c1 j))),
    integral_finsetSum Finset.univ (f :=
      fun (j : Fin d) (y : Torus d) => Torus.partialDeriv j (Torus.partialDeriv j f) y * ψ y)
      (fun j _ => hint ((c2 j).mul hψc))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have a1 := PDE.integral_partialDeriv_mul j f (Torus.partialDeriv j ψ) hf1 (h1 j)
  have a2 := PDE.integral_partialDeriv_mul j (Torus.partialDeriv j f) ψ (h2 j) hψ1
  linarith

/-! #### Test functions and translations -/

variable {ε : ℝ}

/-- The test bump of radius `ε` on the torus. -/
def psiE (d : ℕ) (ε : ℝ) (hε : 0 < ε) : Torus d → ℝ :=
  perT (bf (d := d) (ε / 2) ε (by positivity) (by linarith))

theorem psiE_smooth (hε : 0 < ε) (h8 : ε ≤ 1 / 8) : Torus.IsSmooth (psiE d ε hε) :=
  lt2_perT_isSmooth (bf_smooth _ _ _ _) (bf_zero8 _ _ _ _ h8)

theorem psiE_nonneg (hε : 0 < ε) (t : Torus d) : 0 ≤ psiE d ε hε t :=
  lt2_perz_nonneg (fun y => bf_nonneg _ _ _ _ y) _

theorem psiE_support (hε : 0 < ε) {t : Torus d} (ht : psiE d ε hε t ≠ 0) :
    ∃ v : Euc d, ‖v‖ < ε ∧ t = Torus.mk v :=
  perT_support _ _ _ _ ht

theorem psiE_lap_support (hε : 0 < ε) {t : Torus d} (ht : Torus.laplacian (psiE d ε hε) t ≠ 0) :
    ∃ v : Euc d, ‖v‖ < 2 * ε ∧ t = Torus.mk v :=
  perT_lap_support _ _ _ _ ht

theorem psiE_zero (hε : 0 < ε) (h8 : ε ≤ 1 / 8) : psiE d ε hε (Torus.mk 0) = 1 :=
  perT_zero _ _ _ _ h8

/-- The translate `y ↦ h (y - x)`. -/
def shiftT (h : Torus d → ℝ) (x : Torus d) : Torus d → ℝ := fun y => h (y - x)

theorem lt2_shift_lift (h : Torus d → ℝ) (x : Torus d) :
    Torus.lift (shiftT h x) = fun w => Torus.lift h (w + (-Torus.rep x)) := by
  funext w
  simp only [Torus.lift, Function.comp, shiftT]
  congr 1
  rw [KernelGrad.mk_add, KernelGrad.mk_neg, Torus.mk_rep]
  abel

theorem lt2_isCk_shift {h : Torus d → ℝ} {k : WithTop ℕ∞} (hh : Torus.IsCk k h) (x : Torus d) :
    Torus.IsCk k (shiftT h x) := by
  unfold Torus.IsCk
  rw [lt2_shift_lift]
  exact (show ContDiff ℝ k (Torus.lift h) from hh).comp (contDiff_id.add contDiff_const)

theorem lt2_laplacian_comp_add_right (G : Euc d → ℝ) (a v : Euc d) :
    Laplacian.laplacian (fun w => G (w + a)) v = Laplacian.laplacian G (v + a) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_add_right]

theorem lt2_laplacian_shift (h : Torus d → ℝ) (x y : Torus d) :
    Torus.laplacian (shiftT h x) y = Torus.laplacian h (y - x) := by
  have e : y - x = Torus.mk (Torus.rep y + (-Torus.rep x)) := by
    rw [KernelGrad.mk_add, KernelGrad.mk_neg, Torus.mk_rep, Torus.mk_rep]; abel
  conv_lhs => rw [← Torus.mk_rep y]
  rw [e, lt2_laplacian_mk, lt2_laplacian_mk, lt2_shift_lift, lt2_laplacian_comp_add_right]

theorem lt2_continuousAt_laplacian {f : Euc d → ℝ} {x : Euc d}
    (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f x) : ContinuousAt (Laplacian.laplacian f) x := by
  have hc : ContinuousAt (iteratedFDeriv ℝ 2 f) x :=
    hf.continuousAt_iteratedFDeriv (WithTop.coe_le_coe.2 le_top)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine tendsto_finsetSum _ fun i _ => ?_
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]).continuous.continuousAt).comp hc

theorem lt2_perz_local {b : ℝ} {w : Euc d} (hbd : ∀ n : Lattice d, 4 * b ≤ ‖w + Lattice.toEuc n‖)
    {v u' : Euc d} (hv : ‖v‖ ≤ b) (hu' : ‖u' - (v + w)‖ < b) (n : Lattice d) :
    2 * b ≤ ‖u' + Lattice.toEuc n‖ := by
  have e : w + Lattice.toEuc n = (u' + Lattice.toEuc n) - (v + (u' - (v + w))) := by abel
  have h1 := hbd n
  rw [e] at h1
  have h2 := norm_sub_le (u' + Lattice.toEuc n) (v + (u' - (v + w)))
  have h3 := norm_add_le v (u' - (v + w))
  linarith

theorem lt2_laplacian_eq (hd : 2 ≤ d) {z : Torus d} (hz : z ≠ 0) :
    Torus.laplacian (periodicRiesz d ((d : ℝ) - 2)) z = cd d := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  set g := periodicRiesz d ((d : ℝ) - 2) with hg
  set w := Torus.rep z with hw
  have hwz : Torus.mk w = z := Torus.mk_rep z
  have hmk : Torus.mk w ≠ 0 := by rw [hwz]; exact hz
  obtain ⟨b, hb0, hb16, hbd⟩ := lt2_lattice_dist hmk
  have hf₀s : Torus.IsSmooth (f0 d b hb0) := lt2_f0_smooth hd b hb0 hb16
  have hf₀2 : Torus.IsCk 2 (f0 d b hb0) := by
    have : Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) (f0 d b hb0) := hf₀s
    exact this.of_le (WithTop.coe_le_coe.2 le_top)
  set x : Torus d := -z with hx
  set F1 := shiftT (f0 d b hb0) x with hF1
  have hF12 : Torus.IsCk 2 F1 := lt2_isCk_shift hf₀2 x
  have hF1c : Continuous (Torus.laplacian F1) := PDE.ClassicalAux.continuous_laplacian hF12
  have hlgs : ∀ u : Euc d, Torus.mk u ≠ 0 →
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift g) u := fun u hu =>
    b15c_contDiffAt_lift_periodicRiesz (by omega) hs0 hsd hu
  have hperz : ∀ u' v : Euc d, ‖v‖ ≤ b → ‖u' - (v + w)‖ < b →
      KernelAux.perz (bf (d := d) b (2 * b) hb0 (by linarith)) u' = 0 := fun u' v hv hu' =>
    lt2_perz_eq_zero (r := 2 * b) (fun y hy => bf_zero _ _ _ _ hy) (lt2_perz_local hbd hv hu')
  have hmkx : ∀ v : Euc d, Torus.mk v - x = Torus.mk (v + w) := by
    intro v
    rw [KernelGrad.mk_add, hwz, hx]; abel
  have hK_A : ∀ v : Euc d, ‖v‖ ≤ b → g (x - Torus.mk v) = F1 (Torus.mk v) := by
    intro v hv
    have e1 : x - Torus.mk v = -(Torus.mk v - x) := by abel
    rw [e1, hg, periodicRiesz_neg, hmkx]
    simp only [hF1, shiftT, hmkx, f0, lt2_perT_mk]
    rw [hperz (v + w) v hv (by simpa using hb0)]
    simp
  have hK_B : ∀ v : Euc d, ‖v‖ ≤ b →
      Torus.laplacian F1 (Torus.mk v) = Laplacian.laplacian (Torus.lift g) (v + w) := by
    intro v hv
    rw [hF1, lt2_laplacian_shift, hmkx, lt2_laplacian_mk]
    have hev : Torus.lift (f0 d b hb0) =ᶠ[𝓝 (v + w)] Torus.lift g := by
      filter_upwards [Metric.ball_mem_nhds (v + w) hb0] with u' hu'
      have hu'' : ‖u' - (v + w)‖ < b := by
        rwa [Metric.mem_ball, dist_eq_norm] at hu'
      rw [lt2_f0_lift, hperz u' v hv hu'']
      simp only [sub_zero, one_mul]
      rfl
    exact (InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds
  have hint : ∀ {u : Torus d → ℝ}, Continuous u → Integrable u := fun hu =>
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hΔc : ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ b / 2 →
      ∫ y, (Torus.laplacian F1 y - cd d) * psiE d ε hε y = 0 := by
    intro ε hε hεb
    have h8 : ε ≤ 1 / 8 := by linarith
    set ψ := psiE d ε hε with hψ
    have hψs : Torus.IsSmooth ψ := psiE_smooth hε h8
    have hψ2 : Torus.IsCk 2 ψ := by
      have : Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := hψs
      exact this.of_le (WithTop.coe_le_coe.2 le_top)
    have hψc : Continuous ψ := PDE.MFAux.continuous_of_isCk (hψ2.of_le (by norm_num))
    have hψx : ψ x = 0 := by
      by_contra hne
      obtain ⟨v, hv, hxv⟩ := psiE_support hε hne
      have hmv : Torus.mk v = Torus.mk (-w) := by
        rw [← hxv, hx, ← hwz, KernelGrad.mk_neg]
      obtain ⟨n, hn⟩ := lt2_exists_lattice hmv
      have h4 := hbd (-n)
      have e : w + Lattice.toEuc (-n) = -v := by
        rw [lt2_toEuc_neg, hn]; abel
      rw [e, norm_neg] at h4
      linarith
    have E3 : ∫ y, g (x - y) * Torus.laplacian ψ y = cd d * ((∫ y, ψ y) - ψ x) :=
      lt2_weak hd ψ hψ2 x
    have E1 : ∫ y, g (x - y) * Torus.laplacian ψ y = ∫ y, F1 y * Torus.laplacian ψ y := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      by_cases hΔ : Torus.laplacian ψ y = 0
      · simp [hΔ]
      · obtain ⟨v, hv, hy⟩ := psiE_lap_support hε hΔ
        have hvb : ‖v‖ ≤ b := by linarith
        show g (x - y) * _ = _
        rw [hy, hK_A v hvb]
    have E2 := lt2_ibp hF12 hψ2
    have E4 : ∫ y, Torus.laplacian F1 y * ψ y = cd d * ∫ y, ψ y := by
      rw [← E2, ← E1, E3, hψx]; ring
    have hi1 : Integrable (fun y => Torus.laplacian F1 y * ψ y) := hint (hF1c.mul hψc)
    have hi2 : Integrable ψ := hint hψc
    have : (fun y => (Torus.laplacian F1 y - cd d) * ψ y) =
        fun y => Torus.laplacian F1 y * ψ y - cd d * ψ y := by funext y; ring
    rw [this, integral_sub hi1 (hi2.const_mul _), integral_const_mul, E4]
    ring
  by_contra hne
  have hκ0 : Torus.laplacian g z - cd d ≠ 0 := sub_ne_zero.2 hne
  set κ := Torus.laplacian g z - cd d with hκ
  have hcont : ContinuousAt
      (fun v : Euc d => Laplacian.laplacian (Torus.lift g) (v + w) - cd d) 0 := by
    have h1 := lt2_continuousAt_laplacian (hlgs w hmk)
    have h' : ContinuousAt (fun v : Euc d => v + w) 0 :=
      (continuous_id.add continuous_const).continuousAt
    exact (h1.comp_of_eq h' (by simp)).sub continuousAt_const
  have hW0 : Laplacian.laplacian (Torus.lift g) (0 + w) - cd d = κ := by
    rw [zero_add, ← lt2_laplacian_mk, hwz]
  have hκpos : 0 < |κ| / 2 := by positivity
  obtain ⟨δ, hδ, hδW⟩ := Metric.continuousAt_iff.1 hcont (|κ| / 2) hκpos
  set ε₁ := min δ (b / 2) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hδ (by linarith)
  set ψ := psiE d ε₁ hε₁0 with hψ
  have hψs : Torus.IsSmooth ψ := psiE_smooth hε₁0 (by
    have : ε₁ ≤ b / 2 := min_le_right _ _
    linarith)
  have hψc : Continuous ψ := PDE.MFAux.continuous_of_isCk (by
    have : Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := hψs
    exact (this.of_le (WithTop.coe_le_coe.2 le_top) : Torus.IsCk 2 ψ).of_le (by norm_num))
  have hpt : ∀ y, κ ^ 2 / 2 * ψ y ≤ κ * ((Torus.laplacian F1 y - cd d) * ψ y) := by
    intro y
    by_cases hy0 : ψ y = 0
    · simp [hy0]
    · obtain ⟨v, hv, hy⟩ := psiE_support hε₁0 hy0
      have hvb : ‖v‖ ≤ b := by
        have : ε₁ ≤ b / 2 := min_le_right _ _
        linarith
      have hvδ : ‖v‖ < δ := lt_of_lt_of_le hv (min_le_left _ _)
      have hW := hδW (x := v) (by simpa using hvδ)
      rw [hW0, Real.dist_eq] at hW
      rw [hy, hK_B v hvb]
      set Wv := Laplacian.laplacian (Torus.lift g) (v + w) - cd d with hWv
      have hkey : κ ^ 2 / 2 ≤ κ * Wv := by
        have h1 : |κ * (Wv - κ)| ≤ κ ^ 2 / 2 := by
          rw [abs_mul]
          have : |κ| * |Wv - κ| ≤ |κ| * (|κ| / 2) :=
            mul_le_mul_of_nonneg_left hW.le (abs_nonneg _)
          have h2 : |κ| * (|κ| / 2) = κ ^ 2 / 2 := by
            rw [← sq_abs κ]; ring
          linarith
        have h3 := (abs_le.1 h1).1
        nlinarith
      have hψn : 0 ≤ ψ (Torus.mk v) := psiE_nonneg hε₁0 _
      calc κ ^ 2 / 2 * ψ (Torus.mk v) ≤ κ * Wv * ψ (Torus.mk v) :=
            mul_le_mul_of_nonneg_right hkey hψn
        _ = κ * (Wv * ψ (Torus.mk v)) := by ring
  have h81 : ε₁ ≤ 1 / 8 := by
    have : ε₁ ≤ b / 2 := min_le_right _ _
    linarith
  have hψpos : 0 < ∫ y, ψ y :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := Torus.mk 0) hψc
      (HasCompactSupport.of_compactSpace _) (fun y => psiE_nonneg hε₁0 y)
      (by rw [hψ, psiE_zero hε₁0 h81]; norm_num)
  have hI : ∫ y, κ ^ 2 / 2 * ψ y ≤ ∫ y, κ * ((Torus.laplacian F1 y - cd d) * ψ y) :=
    integral_mono (hint (continuous_const.mul hψc))
      (hint (continuous_const.mul ((hF1c.sub continuous_const).mul hψc))) hpt
  rw [integral_const_mul, integral_const_mul, hΔc ε₁ hε₁0 (min_le_right _ _)] at hI
  have : 0 < κ ^ 2 / 2 * ∫ y, ψ y := mul_pos (by positivity) hψpos
  simp at hI
  linarith

theorem lt2_green_proof (hd : 2 ≤ d) :
    0 < cd d ∧
    (∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ∀ x : Torus d,
      ∫ y, periodicRiesz d ((d : ℝ) - 2) (x - y) * Torus.laplacian ψ y =
        cd d * ((∫ y, ψ y) - ψ x)) ∧
    (∀ z : Torus d, z ≠ 0 → Torus.laplacian (periodicRiesz d ((d : ℝ) - 2)) z = cd d) :=
  ⟨lt2_cd_pos hd, fun ψ hψ x => lt2_weak hd ψ hψ x, fun _ hz => lt2_laplacian_eq hd hz⟩

end HRS.MD.LT337P2
