import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsUniqueFixedPoint

section

namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

section Subst

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem le_order_subst_sub_subst {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f g : MvPowerSeries σ R} {n : ℕ∞}
    (h : n ≤ order (f - g)) : n ≤ order (subst a f - subst a g) := by
  rw [← subst_sub ha]
  refine le_trans ?_ (le_order_subst ha (f - g))
  have h1 : 1 ≤ ⨅ i, (a i).order :=
    le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha0 i)
  calc n ≤ 1 * order (f - g) := by simpa using h
    _ ≤ _ := by gcongr

private def Close (n k : ℕ∞) (u v : MvPowerSeries τ S) : Prop :=
  k ≤ order u ∧ k ≤ order v ∧ n + k ≤ order (u - v) + 1

private lemma close_one (n : ℕ∞) : Close n 0 (1 : MvPowerSeries τ S) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  simp

private lemma close_mul {n k l : ℕ∞} {u v u' v' : MvPowerSeries τ S} (h : Close n k u v)
    (h' : Close n l u' v') : Close n (k + l) (u * u') (v * v') := by
  obtain ⟨hu, hv, huv⟩ := h
  obtain ⟨hu', hv', huv'⟩ := h'
  refine ⟨(add_le_add hu hu').trans (le_order_mul), (add_le_add hv hv').trans (le_order_mul), ?_⟩
  have e : u * u' - v * v' = (u - v) * u' + v * (u' - v') := by ring
  rw [e]
  refine le_trans ?_ (add_le_add min_order_le_add le_rfl)
  rw [← min_add_add_right]
  refine le_min ?_ ?_
  · calc n + (k + l) = (n + k) + l := by rw [add_assoc]
      _ ≤ (order (u - v) + 1) + order u' := add_le_add huv hu'
      _ = (order (u - v) + order u') + 1 := by rw [add_right_comm]
      _ ≤ order ((u - v) * u') + 1 := add_le_add le_order_mul le_rfl
  · calc n + (k + l) = k + (n + l) := by rw [add_left_comm]
      _ ≤ order v + (order (u' - v') + 1) := add_le_add hv huv'
      _ = (order v + order (u' - v')) + 1 := by rw [add_assoc]
      _ ≤ order (v * (u' - v')) + 1 := add_le_add le_order_mul le_rfl

private lemma close_pow {n k : ℕ∞} {u v : MvPowerSeries τ S} (h : Close n k u v) (m : ℕ) :
    Close n (m * k) (u ^ m) (v ^ m) := by
  induction m with
  | zero => simpa using close_one (τ := τ) (S := S) n
  | succ m ih =>
    have := close_mul ih h
    rw [pow_succ, pow_succ]
    convert this using 1
    push_cast
    ring

private lemma close_prod {ι : Type*} (s : Finset ι) {n : ℕ∞} {k : ι → ℕ∞}
    {u v : ι → MvPowerSeries τ S} (h : ∀ i ∈ s, Close n (k i) (u i) (v i)) :
    Close n (∑ i ∈ s, k i) (∏ i ∈ s, u i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using close_one (τ := τ) (S := S) n
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact close_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma close_monomial {n : ℕ∞} {a b : σ → MvPowerSeries τ S}
    (h : ∀ i, Close n 1 (a i) (b i)) (d : σ →₀ ℕ) :
    Close n (d.degree : ℕ∞) (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  have := close_prod d.support (k := fun i => (d i : ℕ∞) * 1) (u := fun i => a i ^ d i)
    (v := fun i => b i ^ d i) (fun i _ => close_pow (h i) (d i))
  simpa [Finsupp.prod, Finsupp.degree_apply] using this

theorem add_le_order_subst_sub_subst {a b : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (hb : HasSubst b) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hb0 : ∀ i, constantCoeff (b i) = 0) {n : ℕ∞} (hab : ∀ i, n ≤ order (a i - b i))
    {f : MvPowerSeries σ R} {m : ℕ∞} (hf : m ≤ order f) :
    n + m ≤ order (subst a f - subst b f) + 1 := by
  have hclose : ∀ i, Close n 1 (a i) (b i) := fun i =>
    ⟨one_le_order_iff_constCoeff_eq_zero.2 (ha0 i),
      one_le_order_iff_constCoeff_eq_zero.2 (hb0 i), add_le_add (hab i) le_rfl⟩

  have hcoeff : ∀ e : τ →₀ ℕ, (e.degree : ℕ∞) + 1 < n + m →
      coeff e (subst a f - subst b f) = 0 := by
    intro e he
    rw [map_sub, coeff_subst ha, coeff_subst hb,
      ← finsum_sub_distrib (coeff_subst_finite ha f e) (coeff_subst_finite hb f e)]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : coeff d f = 0
    · simp [hd]
    rw [← smul_sub, ← map_sub]
    obtain ⟨-, -, hdc⟩ := close_monomial hclose d
    have hmd : m ≤ (d.degree : ℕ∞) := hf.trans (order_le hd)
    have : (e.degree : ℕ∞) + 1 < order ((d.prod fun s e => a s ^ e) -
        (d.prod fun s e => b s ^ e)) + 1 :=
      he.trans_le ((add_le_add le_rfl hmd).trans hdc)
    rw [coeff_of_lt_order ((ENat.add_lt_add_iff_right ENat.one_ne_top).1 this), smul_zero]
  by_contra hlt
  rw [not_le] at hlt
  have hfin : (order (subst a f - subst b f)).toNat = order (subst a f - subst b f) := by
    refine ENat.natCast_toNat fun htop => ?_
    rw [htop] at hlt
    simp at hlt
  obtain ⟨e, he, hdeg⟩ := exists_coeff_ne_zero_and_order hfin
  exact he (hcoeff e (by rw [hdeg]; exact hlt))

end Subst

section FixedPoint

variable {σ R : Type*} [CommRing R]

theorem existsUnique_fixedPoint (Φ : MvPowerSeries σ R → MvPowerSeries σ R)
    (hΦ : ∀ f g : MvPowerSeries σ R, ∀ n : ℕ, (n : ℕ∞) ≤ order (f - g) →
      ((n + 1 : ℕ) : ℕ∞) ≤ order (Φ f - Φ g)) :
    ∃! f, Φ f = f :=
  _root_.UpperTheory.Reformulated.B.Ydb5.existsUnique_fixedPoint Φ hΦ

end FixedPoint

end GroundTheory.LocalField.FormalGroup

end

section

namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries

variable {R : Type*} [CommRing R] (F : FormalGroup R)

noncomputable def higher : MvPowerSeries (Fin 2) R :=
  F.toPowerSeries - X 0 - X 1

theorem toPowerSeries_eq_X_add_X_add_higher : F.toPowerSeries = X 0 + X 1 + higher F := by
  simp [higher]

theorem two_le_order_higher : (2 : ℕ∞) ≤ order (higher F) := by
  refine nat_le_order fun d hd => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = Finsupp.single 0 a + Finsupp.single 1 b :=
    ⟨d 0, d 1, by ext i; fin_cases i <;> simp⟩
  have hab : a + b < 2 := by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have := congrArg (fun d => d 0) h
    simp at this
  have ha : a < 2 := by omega
  have hb : b < 2 := by omega
  interval_cases a <;> interval_cases b <;> simp_all [higher, coeff_X, F.lin_coeff_X,
    F.lin_coeff_Y, F.zero_constantCoeff, Ne.symm h01]

theorem constantCoeff_higher : constantCoeff (higher F) = 0 :=
  one_le_order_iff_constCoeff_eq_zero.1 (le_trans (by norm_num) (two_le_order_higher F))

theorem subst_eq_add_add_subst_higher {τ : Type*} {a b : MvPowerSeries τ R}
    (hab : HasSubst ![a, b]) :
    subst ![a, b] F.toPowerSeries = a + b + subst ![a, b] (higher F) := by
  conv_lhs => rw [toPowerSeries_eq_X_add_X_add_higher F]
  rw [subst_add hab, subst_add hab, subst_X hab, subst_X hab]
  simp

lemma hasSubst_pair {τ : Type*} {a b : MvPowerSeries τ R} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : HasSubst ![a, b] :=
  hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simpa

private noncomputable def invStep (g : MvPowerSeries Unit R) : MvPowerSeries Unit R :=
  -X () - subst ![X (), g - C (constantCoeff g)] (higher F)

private lemma constantCoeff_sub_C (g : MvPowerSeries Unit R) :
    constantCoeff (g - C (constantCoeff g)) = 0 := by simp

private lemma invStep_contract (f g : MvPowerSeries Unit R) (n : ℕ)
    (h : (n : ℕ∞) ≤ order (f - g)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (invStep F f - invStep F g) := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have key := add_le_order_subst_sub_subst (R := R) (m := 2) (n := (n : ℕ∞))
    (hasSubst_pair hX (constantCoeff_sub_C f)) (hasSubst_pair hX (constantCoeff_sub_C g))
    (fun i => by fin_cases i <;> simp) (fun i => by fin_cases i <;> simp) ?_
    (two_le_order_higher F)
  · have e : invStep F f - invStep F g = -(subst ![X (), f - C (constantCoeff f)] (higher F) -
        subst ![X (), g - C (constantCoeff g)] (higher F)) := by
      simp only [invStep]; ring
    rw [e, order_neg]
    have : ((n + 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) + 2 := by push_cast; ring
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 (this ▸ key)
  · intro i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · simp [hn]
      · have h0 : constantCoeff (f - g) = 0 := by
          rw [← coeff_zero_eq_constantCoeff_apply]
          exact coeff_of_lt_order (lt_of_lt_of_le (by simpa using hn) h)
        rw [map_sub, sub_eq_zero] at h0
        rw [h0]
        simpa using h

private lemma existsUnique_invStep : ∃! g, invStep F g = g :=
  existsUnique_fixedPoint _ (invStep_contract F)

noncomputable def inv : PowerSeries R :=
  (existsUnique_invStep F).exists.choose

private lemma invStep_inv : invStep F (inv F) = inv F :=
  (existsUnique_invStep F).exists.choose_spec

private lemma constantCoeff_invStep (g : MvPowerSeries Unit R) :
    constantCoeff (invStep F g) = 0 := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  rw [invStep, map_sub, map_neg, hX,
    constantCoeff_subst_eq_zero (hasSubst_pair hX (constantCoeff_sub_C g))
      (fun i => by fin_cases i <;> simp) (constantCoeff_higher F)]
  simp

theorem constantCoeff_inv : PowerSeries.constantCoeff (inv F) = 0 := by
  rw [← invStep_inv F]
  exact constantCoeff_invStep F _

theorem hasSubst_inv : PowerSeries.HasSubst (inv F) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_inv F)

private lemma invStep_of_constantCoeff_eq_zero {g : MvPowerSeries Unit R}
    (hg : constantCoeff g = 0) : invStep F g = -X () - subst ![X (), g] (higher F) := by
  simp [invStep, hg]

theorem subst_X_inv :
    subst ![PowerSeries.X, inv F] F.toPowerSeries = (0 : PowerSeries R) := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have hi : constantCoeff (inv F : MvPowerSeries Unit R) = 0 := constantCoeff_inv F
  have := invStep_inv F
  rw [invStep_of_constantCoeff_eq_zero F hi] at this
  change subst ![X (), (inv F : MvPowerSeries Unit R)] F.toPowerSeries = 0
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hX hi)]
  linear_combination (-1 : MvPowerSeries Unit R) * this

theorem eq_inv_of_subst_eq_zero {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0)
    (h : subst ![PowerSeries.X, g] F.toPowerSeries = (0 : PowerSeries R)) : g = inv F := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have hg' : constantCoeff (g : MvPowerSeries Unit R) = 0 := hg
  change subst ![X (), (g : MvPowerSeries Unit R)] F.toPowerSeries = 0 at h
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hX hg')] at h
  have hfix : invStep F g = g := by
    rw [invStep_of_constantCoeff_eq_zero F hg']
    linear_combination (-1 : MvPowerSeries Unit R) * h
  exact (existsUnique_invStep F).unique hfix (invStep_inv F)

theorem subst_subst_pair {σ : Type*} {g h : PowerSeries R} (hgh : HasSubst ![g, h])
    {x : MvPowerSeries σ R} (hx : PowerSeries.HasSubst x) (G : MvPowerSeries (Fin 2) R) :
    PowerSeries.subst x (subst ![g, h] G : PowerSeries R) =
      subst ![PowerSeries.subst x g, PowerSeries.subst x h] G := by
  have hx' : HasSubst (fun _ : Unit => x) := PowerSeries.hasSubst_iff.mp hx
  rw [PowerSeries.subst_def, subst_comp_subst_apply hgh hx']
  congr 1
  funext s
  fin_cases s <;> rfl

variable {σ : Type*}

noncomputable instance : Neg (F.Point σ) where
  neg x := ⟨PowerSeries.subst x.val (inv F), by
    simpa [PowerSeries.coe_substAlgHom] using (hasSubst_inv F).comp x.prop⟩

theorem neg_point_val (x : F.Point σ) : (-x).val = PowerSeries.subst x.val (inv F) := rfl

private lemma add_neg_point (x : F.Point σ) : x + -x = 0 := by
  apply Subtype.ext
  have hX : constantCoeff (PowerSeries.X : PowerSeries R) = 0 := PowerSeries.constantCoeff_X
  have h := congrArg (PowerSeries.subst x.val) (subst_X_inv F)
  rw [subst_subst_pair (hasSubst_pair hX (constantCoeff_inv F)) x.prop,
    PowerSeries.subst_X x.prop] at h
  rw [FormalGroup.add_apply, neg_point_val, h]
  rw [← PowerSeries.coe_substAlgHom x.prop, map_zero]
  rfl

noncomputable instance instAddGroupPoint : AddGroup (F.Point σ) :=
  { (inferInstance : AddMonoid (F.Point σ)) with
    neg := Neg.neg
    zsmul := zsmulRec
    neg_add_cancel := fun x => by
      have h1 := add_neg_point F x
      have h2 := add_neg_point F (-x)
      have hx : x = -(-x) :=
        calc x = x + 0 := (add_zero x).symm
          _ = x + (-x + -(-x)) := by rw [h2]
          _ = (x + -x) + -(-x) := (add_assoc _ _ _).symm
          _ = -(-x) := by rw [h1, zero_add]
      calc -x + x = -x + -(-x) := congrArg (-x + ·) hx
        _ = 0 := h2 }

noncomputable instance instAddCommGroupPoint [F.IsComm] : AddCommGroup (F.Point σ) :=
  { instAddGroupPoint F with
    add_comm := fun x y => Subtype.ext (F.comm' x.prop y.prop) }

private noncomputable def pointX : F.Point Unit := ⟨PowerSeries.X, PowerSeries.HasSubst.X'⟩

end GroundTheory.LocalField.FormalGroup

end
