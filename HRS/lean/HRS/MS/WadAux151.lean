import HRS.MS.WadAux150

/-!
# S8.3, packet S8G-2: the one-body family of functionals `ℓ(x) q = T(⟨·⟩^M q)(x)` on `C_0`

`S8gV d = C_0(ℝ^d)` (Mathlib), `s8g_ι M q = ⟨·⟩^M q ∈ C_M`.  For a linear operator `T` on `C_M` with `T f ∈ C_M^{n+1}` and
`|∂^α (T f)| ≤ A C ⟨x⟩^M` whenever `Wt M C f` (`S8gOp`), `ℓ x := (q ↦ T (ι q) x)` is a `C^n` map `ℝ^d → (C_0)^*`
(`s8g_ell_contDiff`) with `‖D^kℓ(x)‖ ≤ (d+1)^{n+1} A ⟨x⟩^M` (`s8g_ell_iter_bound`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- The Banach space `C_0(ℝ^d)` (a `def` with explicit instances, so that nested operator spaces synthesize). -/
def S8gV (d : ℕ) : Type := ZeroAtInftyContinuousMap (Euc d) ℝ

instance : NormedAddCommGroup (S8gV d) :=
  inferInstanceAs (NormedAddCommGroup (ZeroAtInftyContinuousMap (Euc d) ℝ))

instance : NormedSpace ℝ (S8gV d) := inferInstanceAs (NormedSpace ℝ (ZeroAtInftyContinuousMap (Euc d) ℝ))

instance : FunLike (S8gV d) (Euc d) ℝ := inferInstanceAs (FunLike (ZeroAtInftyContinuousMap (Euc d) ℝ) (Euc d) ℝ)

theorem s8g_ext {q1 q2 : S8gV d} (h : ∀ x, q1 x = q2 x) : q1 = q2 :=
  ZeroAtInftyContinuousMap.ext h

theorem s8g_cont (q : S8gV d) : Continuous q :=
  ContinuousMapClass.map_continuous (F := ZeroAtInftyContinuousMap (Euc d) ℝ) q

theorem s8g_zero_at_infty (q : S8gV d) : Tendsto q (cocompact (Euc d)) (𝓝 0) :=
  zero_at_infty (F := ZeroAtInftyContinuousMap (Euc d) ℝ) q

theorem s8g_add_apply (q1 q2 : S8gV d) (x : Euc d) : (q1 + q2) x = q1 x + q2 x := rfl

theorem s8g_smul_apply (c : ℝ) (q : S8gV d) (x : Euc d) : (c • q) x = c * q x := rfl

theorem s8g_norm_apply_le (q : S8gV d) (x : Euc d) : |q x| ≤ ‖q‖ := by
  let q' : ZeroAtInftyContinuousMap (Euc d) ℝ := q
  have h := BoundedContinuousFunction.norm_coe_le_norm q'.toBCF x
  rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at h
  exact h

theorem s8g_norm_le {q : S8gV d} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |q x| ≤ C) : ‖q‖ ≤ C := by
  let q' : ZeroAtInftyContinuousMap (Euc d) ℝ := q
  have e : ‖q‖ = ‖q'.toBCF‖ := (ZeroAtInftyContinuousMap.norm_toBCF_eq_norm).symm
  rw [e]
  exact (BoundedContinuousFunction.norm_le hC).2 fun x => h x

/-- Build an element of `C_0` from a continuous function tending to `0` at infinity. -/
def s8g_mk (f : Euc d → ℝ) (hc : Continuous f) (ht : Tendsto f (cocompact (Euc d)) (𝓝 0)) : S8gV d :=
  (⟨⟨f, hc⟩, ht⟩ : ZeroAtInftyContinuousMap (Euc d) ℝ)

@[simp] theorem s8g_mk_apply (f : Euc d → ℝ) (hc : Continuous f) (ht : Tendsto f (cocompact (Euc d)) (𝓝 0))
    (x : Euc d) : s8g_mk f hc ht x = f x := rfl

/-- `ι q = ⟨·⟩^M q`. -/
def s8g_ι (M : ℝ) (q : S8gV d) : Euc d → ℝ := fun x => jbracket x ^ M * q x

theorem s8g_ι_memCM (M : ℝ) (q : S8gV d) : MemCM M (s8g_ι M q) := by
  refine ⟨(s85_jb_rpow_continuous M).mul (s8g_cont q), ?_⟩
  refine (s8g_zero_at_infty q).congr fun x => ?_
  have hp := Real.rpow_pos_of_pos (s83_jb_pos x) M
  simp only [s8g_ι]
  field_simp

theorem s8g_ι_add (M : ℝ) (q1 q2 : S8gV d) : s8g_ι M (q1 + q2) = s8g_ι M q1 + s8g_ι M q2 := by
  funext x; simp [s8g_ι, s8g_add_apply, mul_add]

theorem s8g_ι_smul (M c : ℝ) (q : S8gV d) : s8g_ι M (c • q) = c • s8g_ι M q := by
  funext x; simp [s8g_ι, s8g_smul_apply]; ring

theorem s8g_ι_wt (M : ℝ) (q : S8gV d) : Wt M ‖q‖ (s8g_ι M q) := fun x => by
  rw [Real.norm_eq_abs]
  simp only [s8g_ι, abs_mul, abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos x).le M)]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (s8g_norm_apply_le q x) (Real.rpow_nonneg (s83_jb_pos x).le M)

/-- The abstract hypotheses on a one-body operator `T` (which will be `f ↦ U_t(P_μ f)`). -/
structure S8gOp (M : ℝ) (T : (Euc d → ℝ) → Euc d → ℝ) (J : ℕ) (A : ℝ) : Prop where
  nonneg : 0 ≤ A
  add : ∀ f g, MemCM M f → MemCM M g → T (f + g) = T f + T g
  smul : ∀ (c : ℝ) f, MemCM M f → T (c • f) = c • T f
  mem : ∀ f, MemCM M f → MemCMj M J (T f)
  bnd : ∀ f (C : ℝ), MemCM M f → Wt M C f → ∀ i ≤ J, ∀ idx : Fin i → Fin d, ∀ x,
    |partialDeriv idx (T f) x| ≤ A * C * jbracket x ^ M

theorem s8g_op_zero {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {J : ℕ} {A : ℝ} (hT : S8gOp M T J A) (q : S8gV d)
    (x : Euc d) : |T (s8g_ι M q) x| ≤ A * ‖q‖ * jbracket x ^ M := by
  have := hT.bnd (s8g_ι M q) ‖q‖ (s8g_ι_memCM M q) (s8g_ι_wt M q) 0 (Nat.zero_le _) (fun l => l.elim0) x
  simpa [partialDeriv] using this

/-- The functional `ℓ(x) q = T(ι q)(x)`. -/
def s8g_ell {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {J : ℕ} {A : ℝ} (hT : S8gOp M T J A) (x : Euc d) :
    S8gV d →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun q => T (s8g_ι M q) x
      map_add' := fun q1 q2 => by
        rw [s8g_ι_add, hT.add _ _ (s8g_ι_memCM M q1) (s8g_ι_memCM M q2)]; rfl
      map_smul' := fun c q => by
        rw [s8g_ι_smul, hT.smul c _ (s8g_ι_memCM M q)]; rfl }
    (A * jbracket x ^ M) (fun q => by
      have := s8g_op_zero hT q x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
      calc _ ≤ A * ‖q‖ * jbracket x ^ M := this
        _ = _ := by ring)

theorem s8g_ell_apply {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {J : ℕ} {A : ℝ} (hT : S8gOp M T J A) (x : Euc d)
    (q : S8gV d) : s8g_ell hT x q = T (s8g_ι M q) x := rfl

/-- The weight `(d+1)^N A ⟨x⟩^M`. -/
def s8g_w (d : ℕ) (M A : ℝ) (N : ℕ) : Euc d → ℝ := fun x => ((d : ℝ) + 1) ^ N * (A * jbracket x ^ M)

theorem s8g_w_cont (M A : ℝ) (N : ℕ) : Continuous (s8g_w d M A N) :=
  continuous_const.mul (continuous_const.mul (s85_jb_rpow_continuous M))

theorem s8g_w_nonneg {A : ℝ} (hA : 0 ≤ A) (M : ℝ) (N : ℕ) (x : Euc d) : 0 ≤ s8g_w d M A N x :=
  mul_nonneg (by positivity) (mul_nonneg hA (Real.rpow_nonneg (s83_jb_pos x).le _))

theorem s8g_iter_bound {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {n : ℕ} {A : ℝ} (hT : S8gOp M T (n + 1) A)
    (q : S8gV d) {k : ℕ} (hk : k ≤ n + 1) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun x => s8g_ell hT x q) x‖ ≤ s8g_w d M A (n + 1) x * ‖q‖ := by
  have hK : 0 ≤ A * ‖q‖ * jbracket x ^ M :=
    mul_nonneg (mul_nonneg hT.nonneg (norm_nonneg _)) (Real.rpow_nonneg (s83_jb_pos x).le _)
  have h1 := s83_norm_iter_le_card hK k (T (s8g_ι M q)) x (fun idx =>
    hT.bnd _ ‖q‖ (s8g_ι_memCM M q) (s8g_ι_wt M q) k hk idx x)
  have h2 : (d : ℝ) ^ k ≤ ((d : ℝ) + 1) ^ (n + 1) :=
    calc (d : ℝ) ^ k ≤ ((d : ℝ) + 1) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ ((d : ℝ) + 1) ^ (n + 1) := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) hk
  refine h1.trans ?_
  show _ ≤ ((d : ℝ) + 1) ^ (n + 1) * (A * jbracket x ^ M) * ‖q‖
  calc (d : ℝ) ^ k * (A * ‖q‖ * jbracket x ^ M) ≤ ((d : ℝ) + 1) ^ (n + 1) * (A * ‖q‖ * jbracket x ^ M) :=
        mul_le_mul_of_nonneg_right h2 hK
    _ = _ := by ring

theorem s8g_ell_contDiff {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {n : ℕ} {A : ℝ} (hT : S8gOp M T (n + 1) A) :
    ContDiff ℝ (n : WithTop ℕ∞) (s8g_ell hT) := by
  refine s8g_smooth (s8g_w_cont M A (n + 1)) (s8g_w_nonneg hT.nonneg M (n + 1)) n (s8g_ell hT) (fun q => ?_)
    (fun q k hk x => s8g_iter_bound hT q hk x)
  exact (hT.mem _ (s8g_ι_memCM M q)).1

theorem s8g_ell_iter_bound {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {n : ℕ} {A : ℝ} (hT : S8gOp M T (n + 1) A)
    {k : ℕ} (hk : k ≤ n) (x : Euc d) : ‖iteratedFDeriv ℝ k (s8g_ell hT) x‖ ≤ s8g_w d M A (n + 1) x := by
  have hw0 := s8g_w_nonneg hT.nonneg M (n + 1) x
  refine ContinuousMultilinearMap.opNorm_le_bound hw0 fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hw0 (Finset.prod_nonneg fun i _ => norm_nonneg _))
    fun q => ?_
  have hc : ContDiffAt ℝ k (s8g_ell hT) x :=
    ((s8g_ell_contDiff hT).of_le (by exact_mod_cast hk)).contDiffAt
  have e := ContinuousLinearMap.iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ ℝ q) hc
    (i := k) (by exact_mod_cast le_rfl)
  have e2 : iteratedFDeriv ℝ k (fun x => s8g_ell hT x q) x =
      (ContinuousLinearMap.apply ℝ ℝ q).compContinuousMultilinearMap (iteratedFDeriv ℝ k (s8g_ell hT) x) := e
  have h3 := (iteratedFDeriv ℝ k (fun x => s8g_ell hT x q) x).le_opNorm v
  rw [e2] at h3
  have h4 : ‖iteratedFDeriv ℝ k (s8g_ell hT) x v q‖ ≤
      ‖iteratedFDeriv ℝ k (fun x => s8g_ell hT x q) x‖ * ∏ i, ‖v i‖ := by
    rw [e2]
    simpa using h3
  refine h4.trans ?_
  calc _ ≤ s8g_w d M A (n + 1) x * ‖q‖ * ∏ i, ‖v i‖ :=
        mul_le_mul_of_nonneg_right (s8g_iter_bound hT q (by omega) x) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = _ := by ring

end HRS.MS.Wad
