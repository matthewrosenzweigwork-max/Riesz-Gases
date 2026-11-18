import HRS.MS.MfeConfAux84

/-!
# S.B.1, packet F8 (part 17): the clamped trajectory and joint continuity of the level-`k` fields

`ρb s = ρ (clamp s)` (clamp to `[0,T]`); every pointwise fact at `s ∈ ℝ` is a fact at the clamped time.  Joint continuity of
`ρb`, its first and second `x`-derivatives, of `A(ρb)`, of `G = k * ρb`, `∂_jG`, `∂_j∂_jG`, `Ġ`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1w_anti {p q : ℝ} (hpq : p ≤ q) (hp : 0 ≤ p) (y : Euc d) : sb1w q y ≤ sb1w p y := by
  unfold sb1w
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y]) (by linarith)

/-- the clamped trajectory -/
def sb1_lv_rb {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) : Euc d → ℝ := ρ (Set.projIcc (0 : ℝ) T hT s)

theorem sb1_lv_cl {T : ℝ} (hT : 0 ≤ T) (s : ℝ) : ((Set.projIcc (0 : ℝ) T hT s : Set.Icc (0 : ℝ) T) : ℝ) ∈ Set.Icc (0 : ℝ) T :=
  (Set.projIcc (0 : ℝ) T hT s).2

section Traj

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)

include H hT

theorem sb1_lv_rb_cont : Continuous (fun p : ℝ × Euc d => sb1_lv_rb hT ρ p.1 p.2) :=
  (sb1_rho_cont H.tr).comp (((continuous_projIcc (h := hT)).comp continuous_fst).prodMk continuous_snd)

theorem sb1_lv_drb_cont (j : Fin d) :
    Continuous (fun p : ℝ × Euc d => fderiv ℝ (sb1_lv_rb hT ρ p.1) p.2 (sb1e j)) :=
  (sb1_d_cont H.tr j).comp (((continuous_projIcc (h := hT)).comp continuous_fst).prodMk continuous_snd)

theorem sb1_lv_ddrb_cont (j : Fin d) :
    Continuous (fun p : ℝ × Euc d => fderiv ℝ (fun y => fderiv ℝ (sb1_lv_rb hT ρ p.1) y (sb1e j)) p.2 (sb1e j)) :=
  (sb1_dd_cont H.tr j).comp (((continuous_projIcc (h := hT)).comp continuous_fst).prodMk continuous_snd)

theorem sb1_lv_fderiv_rb_cont :
    Continuous (fun p : ℝ × Euc d => fderiv ℝ (sb1_lv_rb hT ρ p.1) p.2) :=
  (sb1_fderiv_cont H.tr).comp (((continuous_projIcc (h := hT)).comp continuous_fst).prodMk continuous_snd)

theorem sb1_lv_rb_le (s : ℝ) (y : Euc d) : |sb1_lv_rb hT ρ s y| ≤ C3 * sb1w ((d : ℝ) + 2) y := by
  have h0 := (H.tr.slice _ (sb1_lv_cl hT s)).dens.nonneg y
  unfold sb1_lv_rb
  rw [abs_of_nonneg h0]
  refine (H.rho_le (sb1_lv_cl hT s) y).trans ?_
  exact mul_le_mul_of_nonneg_left (sb1w_anti (by linarith) (by positivity) y) H.C3nn

theorem sb1_lv_drb_le (s : ℝ) (j : Fin d) (y : Euc d) :
    |fderiv ℝ (sb1_lv_rb hT ρ s) y (sb1e j)| ≤ C3 * sb1w ((d : ℝ) + 2) y := by
  unfold sb1_lv_rb
  refine ((sb1_apply_single_le _ j).trans (H.drho_le (sb1_lv_cl hT s) y)).trans ?_
  exact mul_le_mul_of_nonneg_left (sb1w_anti (by linarith) (by positivity) y) H.C3nn

theorem sb1_lv_At_le (s : ℝ) (y : Euc d) : |sb1At D hT ρ s y| ≤ sb1CA D B C C3 * sb1w ((d : ℝ) + 2) y := by
  unfold sb1At
  exact H.A_le (sb1_lv_cl hT s) y

/-- joint continuity of `G = k * ρb` -/
theorem sb1_lv_G_cont {k : Euc d → ℝ} {A : ℝ} (hk : Sb1Gr k A) (hkc : Continuous k) :
    Continuous (Function.uncurry fun s x => sb1G k (sb1_lv_rb hT ρ s) x) :=
  sb1_lv_cv_cont hk hkc (φ := fun s => sb1_lv_rb hT ρ s) (a := C3) (sb1_lv_rb_cont H hT) H.tr.hd
    (sb1_lv_rb_le H hT)

/-- joint continuity of `∂_jG = cv (∂_jk) ρb` (and of the Hessian entries, by the same lemma with another kernel) -/
theorem sb1_lv_cv_rb_cont {f : Euc d → ℝ} {A : ℝ} (hf : Sb1Gr f A) (hfc : Continuous f) :
    Continuous (Function.uncurry fun s x => sb1_lv_cv f (sb1_lv_rb hT ρ s) x) :=
  sb1_lv_cv_cont hf hfc (φ := fun s => sb1_lv_rb hT ρ s) (a := C3) (sb1_lv_rb_cont H hT) H.tr.hd (sb1_lv_rb_le H hT)

/-- joint continuity of `Ġ(s,x) = ∫ A(ρ_s)(y) k(x-y) dy` -/
theorem sb1_lv_Gd_cont {k : Euc d → ℝ} {A : ℝ} (hk : Sb1Gr k A) (hkc : Continuous k) :
    Continuous (Function.uncurry fun s x => sb1_lv_cv k (sb1At D hT ρ s) x) :=
  sb1_lv_cv_cont hk hkc (φ := fun s => sb1At D hT ρ s) (a := sb1CA D B C C3)
    (by exact sb1At_cont H.tr hT) H.tr.hd (sb1_lv_At_le H hT)

end Traj

end HRS.MS.MfeConf
