module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.LatSheaf

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]

def secGrp (M : X → AddSubgroup V) (U : X.Opens) : AddSubgroup V where
  carrier := {v | (∀ y ∈ U, v ∈ M y) ∧ (genericPoint X ∉ U → v = 0)}
  add_mem' := fun {a b} ha hb =>
    ⟨fun y hy => add_mem (ha.1 y hy) (hb.1 y hy), fun h => by rw [ha.2 h, hb.2 h, add_zero]⟩
  zero_mem' := ⟨fun y _ => zero_mem _, fun _ => rfl⟩
  neg_mem' := fun {a} ha => ⟨fun y hy => neg_mem (ha.1 y hy), fun h => by rw [ha.2 h, neg_zero]⟩

variable (M : X → AddSubgroup V)

theorem val_eq_zero {U : X.Opens} (h : genericPoint X ∉ U) (s : secGrp M U) : (s : V) = 0 := s.2.2 h


open Classical in
def resHom {U W : X.Opens} (e : W ≤ U) : secGrp M U →+ secGrp M W where
  toFun s := if h : genericPoint X ∈ W then ⟨(s : V), fun y hy => s.2.1 y (e hy), fun h' => (h' h).elim⟩
    else 0
  map_zero' := by split_ifs <;> rfl
  map_add' s t := by split_ifs <;> first | rfl | simp

open Classical in
theorem val_resHom {U W : X.Opens} (e : W ≤ U) (s : secGrp M U) :
    ((resHom M e s : secGrp M W) : V) = if genericPoint X ∈ W then (s : V) else 0 := by
  unfold resHom; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]; split_ifs <;> rfl

theorem val_resHom_of_mem {U W : X.Opens} (e : W ≤ U) (h : genericPoint X ∈ W) (s : secGrp M U) :
    ((resHom M e s : secGrp M W) : V) = s := by rw [val_resHom, if_pos h]

def pre : TopCat.Presheaf Ab.{0} X where
  obj U := AddCommGrpCat.of (secGrp M U.unop)
  map f := AddCommGrpCat.ofHom (resHom M (leOfHom f.unop))
  map_id U := by
    ext s
    change ((resHom M le_rfl s : secGrp M U.unop) : V) = s
    rw [val_resHom]; split_ifs with h
    · rfl
    · exact (val_eq_zero M h s).symm
  map_comp f g := by
    ext s
    change ((resHom M (leOfHom (f ≫ g).unop) s : secGrp M _) : V) =
      ((resHom M (leOfHom g.unop) (resHom M (leOfHom f.unop) s) : secGrp M _) : V)
    rw [val_resHom, val_resHom, val_resHom]
    split_ifs with h1 h2 <;> first | rfl | exact (h2 (leOfHom g.unop h1)).elim

theorem sec_ext {U : X.Opens} {s t : secGrp M U} (h : genericPoint X ∈ U → (s : V) = t) : s = t := by
  by_cases hU : genericPoint X ∈ U
  · exact Subtype.ext (h hU)
  · exact Subtype.ext ((val_eq_zero M hU s).trans (val_eq_zero M hU t).symm)

def sv (U : (X.Opens)ᵒᵖ) (s : (pre M).obj U) : V := @Subtype.val V (· ∈ secGrp M U.unop) s

theorem sv_mem (U : (X.Opens)ᵒᵖ) (s : (pre M).obj U) : sv M U s ∈ secGrp M U.unop :=
  @Subtype.property V (· ∈ secGrp M U.unop) s

theorem sv_ext {U : (X.Opens)ᵒᵖ} {s t : (pre M).obj U} (h : genericPoint X ∈ U.unop → sv M U s = sv M U t) :
    s = t :=
  sec_ext M (U := U.unop) (s := s) (t := t) h

def mk (U : (X.Opens)ᵒᵖ) (v : V) (h : v ∈ secGrp M U.unop) : (pre M).obj U :=
  (⟨v, h⟩ : secGrp M U.unop)

@[simp] theorem sv_mk (U : (X.Opens)ᵒᵖ) (v : V) (h : v ∈ secGrp M U.unop) : sv M U (mk M U v h) = v := rfl

open Classical in
theorem sv_map {U W : (X.Opens)ᵒᵖ} (f : U ⟶ W) (s : (pre M).obj U) :
    sv M W ((pre M).map f s) = if genericPoint X ∈ W.unop then sv M U s else 0 :=
  val_resHom M (leOfHom f.unop) s

theorem isSheaf_pre : (pre M).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have key : ∀ k l, genericPoint X ∈ W k → genericPoint X ∈ W l →
      sv M _ (sf k) = sv M _ (sf l) := fun k l hk hl => by
    have := congrArg (sv M _) (hsf k l)
    rw [sv_map, sv_map, if_pos (show genericPoint X ∈ W k ⊓ W l from ⟨hk, hl⟩),
      if_pos (show genericPoint X ∈ W k ⊓ W l from ⟨hk, hl⟩)] at this
    exact this
  by_cases hg : genericPoint X ∈ iSup W
  · obtain ⟨k₀, hk₀⟩ := Opens.mem_iSup.1 hg
    have mem : sv M _ (sf k₀) ∈ secGrp M (iSup W) := by
      refine ⟨fun y hy => ?_, fun h => (h hg).elim⟩
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hy
      rw [key k₀ k hk₀ (gen_mem hk)]
      exact (sv_mem M _ (sf k)).1 y hk
    refine ⟨mk M (Opposite.op (iSup W)) _ mem, fun k => ?_, fun t ht => ?_⟩
    · refine sv_ext M fun hk => ?_
      rw [sv_map, if_pos hk, sv_mk]
      exact key k₀ k hk₀ hk
    · refine sv_ext M fun _ => ?_
      have := congrArg (sv M _) (ht k₀)
      rw [sv_map, if_pos hk₀] at this
      rw [sv_mk]
      exact this
  · refine ⟨mk M (Opposite.op (iSup W)) 0 (zero_mem _), fun k => ?_, fun t _ => ?_⟩
    · exact sv_ext M fun hk => (hg (Opens.mem_iSup.2 ⟨k, hk⟩)).elim
    · exact sv_ext M fun h => (hg h).elim

variable {M}
variable (hM : ∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y)


open Classical in
def smulSec (U : X.Opens) (r : Γ(X, U)) (s : secGrp M U) : secGrp M U :=
  if h : genericPoint X ∈ U then
    ⟨fnOf U h r • (s : V), fun y hy => hM y _ _ (regAt_fnOf hy h r) (s.2.1 y hy), fun h' => (h' h).elim⟩
  else 0

theorem val_smulSec {U : X.Opens} (h : genericPoint X ∈ U) (r : Γ(X, U)) (s : secGrp M U) :
    (smulSec hM U r s : V) = fnOf U h r • (s : V) := by
  rw [smulSec, dite_eq_left h]

def secModule (U : X.Opens) : Module Γ(X, U) (secGrp M U) where
  smul := smulSec hM U
  one_smul s := sec_ext M fun h => by
    change (smulSec hM U 1 s : V) = s
    rw [val_smulSec hM h, map_one, one_smul]
  mul_smul a b s := sec_ext M fun h => by
    change (smulSec hM U (a * b) s : V) = smulSec hM U a (smulSec hM U b s)
    rw [val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, map_mul, mul_smul]
  smul_zero a := sec_ext M fun h => by
    change (smulSec hM U a 0 : V) = ((0 : secGrp M U) : V)
    rw [val_smulSec hM h, ZeroMemClass.coe_zero, smul_zero]
  smul_add a s t := sec_ext M fun h => by
    change (smulSec hM U a (s + t) : V) = ((smulSec hM U a s + smulSec hM U a t : secGrp M U) : V)
    rw [AddSubgroup.coe_add, val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, AddSubgroup.coe_add,
      smul_add]
  add_smul a b s := sec_ext M fun h => by
    change (smulSec hM U (a + b) s : V) = ((smulSec hM U a s + smulSec hM U b s : secGrp M U) : V)
    rw [AddSubgroup.coe_add, val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, map_add (f := _), add_smul]
  zero_smul s := sec_ext M fun h => by
    change (smulSec hM U 0 s : V) = ((0 : secGrp M U) : V)
    rw [val_smulSec hM h, map_zero, zero_smul, ZeroMemClass.coe_zero]

theorem resHom_smulSec {U W : X.Opens} (e : W ≤ U) (r : Γ(X, U)) (s : secGrp M U) :
    resHom M e (smulSec hM U r s) = smulSec hM W (resG X e r) (resHom M e s) :=
  sec_ext M fun h => by
    rw [val_resHom_of_mem M e h, val_smulSec hM h, val_smulSec hM (e h), fnOf_resG,
      val_resHom_of_mem M e h]

def toMod : X.Modules :=
  letI : ∀ U, Module (X.ringCatSheaf.obj.obj U) ((pre M).obj U) := fun U => secModule hM U.unop
  { val := PresheafOfModules.ofPresheaf (pre M) fun _ _ f r m => resHom_smulSec hM (leOfHom f.unop) r m
    isSheaf := isSheaf_pre M }

def latModel : LatModel M (toMod hM) where
  val U _ := { toFun := fun s => sv M (Opposite.op U) s, map_zero' := rfl, map_add' := fun _ _ => rfl }
  inj U _ s t e := sv_ext M fun _ => e
  range U h := by
    ext v
    simp only [AddMonoidHom.mem_range, AddMonoidHom.coe_mk, ZeroHom.coe_mk, latSec,
      AddSubgroup.mem_iInf]
    constructor
    · rintro ⟨s, rfl⟩ y hy
      exact (sv_mem M _ s).1 y hy
    · intro hv
      exact ⟨mk M (Opposite.op U) v ⟨hv, fun h' => (h' h).elim⟩, rfl⟩
  res U W e h s := by
    exact (sv_map M (homOfLE e).op s).trans (if_pos h)
  smul U h r s := val_smulSec hM h r s

end GlobalTheory.LogDR.LatSheaf

theorem GlobalTheory.LogDR.exists_latModel : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M : X → AddSubgroup V),
    (∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y) →
      ∃ F : X.Modules, Nonempty (LatModel M F) :=
  fun _ _ _ _ _ _ hM => ⟨LatSheaf.toMod hM, ⟨LatSheaf.latModel hM⟩⟩
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RoundEqn

open GlobalTheory.Cartier.CartierDiv

variable {X : Scheme.{0}} [IsIntegral X]

theorem eff_of_atlas {C : Type} {E : C → CartierDiv X} {n : ℕ} {ι : Type}
    (𝒜 : SncAtlas E n ι) (c : C) : (E c).Eff := by
  intro y
  have hy : y ∈ ⨆ i, 𝒜.U i := by rw [𝒜.cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
  obtain ⟨e, -, -, heq⟩ := 𝒜.snc i
  refine ⟨_, heq c y hi, ?_⟩
  rw [one_mul]
  cases h : e c with
  | none => exact (unitAt_one y).regAt
  | some j => exact ((𝒜.chart i).chart y hi).mem j

theorem Eff.nsmul' {D : CartierDiv X} (h : D.Eff) (m : ℕ) : (m • D).Eff := by
  induction m with
  | zero => rw [zero_nsmul]; exact eff_zero
  | succ m ih => rw [succ_nsmul]; exact ih.add h

theorem isEqn_sum {C : Type} (s : Finset C) (D : C → CartierDiv X) (g : C → X.functionFieldˣ)
    (y : X) (h : ∀ c ∈ s, (D c).IsEqn y (g c)) : (∑ c ∈ s, D c).IsEqn y (∏ c ∈ s, g c) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun c hc => h c (Finset.mem_insert_of_mem hc))

theorem prod_elim_pow {C : Type} [Fintype C] {n : ℕ} {M : Type} [CommMonoid M] (x : Fin n → M)
    (J : Finset (Fin n)) (e : C → Option (Fin n)) (hJ : ∀ j, j ∈ J ↔ ∃ c, e c = some j)
    (r : C → ℕ) :
    ∏ c, ((e c).elim 1 x) ^ r c =
      ∏ j ∈ J, x j ^ (∑ c, if e c = some j then r c else 0) := by
  have step : ∀ c, ((e c).elim 1 x) ^ r c =
      ∏ j ∈ J, x j ^ (if e c = some j then r c else 0) := by
    intro c
    cases h : e c with
    | none => simp
    | some j₀ =>
      have hj₀ : j₀ ∈ J := (hJ j₀).2 ⟨c, h⟩
      rw [Finset.prod_eq_single j₀]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro hn; exact (hn hj₀).elim
  simp_rw [step]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Finset.prod_pow_eq_pow_sum _ _ _

end GlobalTheory.RoundEqn


open GlobalTheory.RoundEqn GlobalTheory.Cartier.CartierDiv in
theorem GlobalTheory.roundedTwist_isEqn :
  ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ((p • G + ∑ c, r c • E c) - p • G).Eff ∧ ∀ (i : ι), ∃ ρ : Fin n → ℕ, (∀ j, ρ j < p) ∧ ∀ y ∈ 𝒜.U i, ∀ t, G.IsEqn y t → (p • G + ∑ c, r c • E c).IsEqn y (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j) := by
  intro p hp X _ _ C _ E n ι _ 𝒜 G r hr
  classical
  refine ⟨?_, fun i => ?_⟩
  · rw [add_sub_cancel_left]
    refine Finset.sum_induction _ (fun D : CartierDiv X => D.Eff) (fun _ _ h h' => h.add h') eff_zero ?_
    intro c _
    exact Eff.nsmul' (eff_of_atlas 𝒜 c) (r c)
  · obtain ⟨e, huniq, hJ, heq⟩ := 𝒜.snc i
    refine ⟨fun j => ∑ c, if e c = some j then r c else 0, fun j => ?_, fun y hy t ht => ?_⟩
    · show (∑ c, if e c = some j then r c else 0) < p
      by_cases h : ∃ c, e c = some j
      · obtain ⟨c₀, hc₀⟩ := h
        rw [Finset.sum_eq_single c₀]
        · rw [if_pos hc₀]; exact hr c₀
        · intro c _ hc; rw [if_neg]; exact fun h' => hc (huniq c c₀ j h' hc₀)
        · intro hn; exact (hn (Finset.mem_univ _)).elim
      · push_neg at h
        rw [Finset.sum_eq_zero fun c _ => if_neg (h c)]
        exact hp.out.pos
    · rw [← prod_elim_pow (𝒜.x i) (𝒜.J i) e hJ r]
      refine (ht.nsmul p).add (isEqn_sum _ _ _ y fun c _ => ?_)
      exact (heq c y hy).nsmul (r c)
end
end

section

open GlobalTheory GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.StabD

variable {K : Type} [Field K]

theorem dK_unit (u : Kˣ) : dK (u : K) = (u : K) • dlog u := by
  rw [dlog, smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ u.ne_zero, one_smul]

theorem dlog_mul (u w : Kˣ) : dlog (u * w) = dlog u + dlog w := by
  simp only [dlog, Units.val_inv_eq_inv_val, Units.val_mul, dK, Derivation.leibniz, smul_add, smul_smul]
  rw [add_comm]
  congr 1
  · congr 1; field_simp
  · congr 1; field_simp

theorem dlog_one : dlog (1 : Kˣ) = 0 := by simp [dlog]

theorem dlog_inv (u : Kˣ) : dlog u⁻¹ = -dlog u := by
  have h := dlog_mul u⁻¹ u
  rw [inv_mul_cancel, dlog_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem dlog_pow (u : Kˣ) (m : ℕ) : dlog (u ^ m) = (m : K) • dlog u := by
  induction m with
  | zero => simp [dlog_one]
  | succ m ih => rw [pow_succ, dlog_mul, ih, Nat.cast_succ, add_smul, one_smul]

theorem dlog_prod {ι : Type} (s : Finset ι) (f : ι → Kˣ) : dlog (∏ i ∈ s, f i) = ∑ i ∈ s, dlog (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dlog_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, dlog_mul, ih]

theorem dDR_dlog (u : Kˣ) : CechDR.dDR ℤ K (CechDR.ι1 (dlog u)) = 0 := by
  have hD : dK ((u⁻¹ : Kˣ) : K) = -(((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K)) • dK (u : K) := by
    rw [dK_unit, dlog_inv, dlog, smul_neg, smul_smul, neg_smul]
  rw [dlog, map_smul, CechDR.dDR_smul, CechDR.dDR_D, smul_zero, add_zero]
  change CechDR.ι1 (dK ((u⁻¹ : Kˣ) : K)) * CechDR.ι1 (dK (u : K)) = 0
  rw [hD, map_smul, smul_mul_assoc, ExteriorAlgebra.ι_sq_zero, smul_zero]

theorem dDR_frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) :
    CechDR.dDR ℤ K (CechDR.ι1 (frame x J i)) = 0 := by
  unfold frame
  split_ifs
  · exact dDR_dlog _
  · exact CechDR.dDR_D _

theorem dDR_ιMulti (q : ℕ) (v : Fin q → Ω[K⁄ℤ]) (hv : ∀ i, CechDR.dDR ℤ K (CechDR.ι1 (v i)) = 0) :
    CechDR.dDR ℤ K (ExteriorAlgebra.ιMulti K q v) = 0 := by
  induction q with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (abelian₂ K)), CechDR.dDR_algebraMap]
    simp
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, CechDR.dDR_mul]
    change _ * CechDR.dDR ℤ K _ + CechDR.dDR ℤ K (CechDR.ι1 (v 0)) * _ = 0
    rw [ih (Matrix.vecTail v) (fun i => hv _), hv 0, mul_zero, zero_mul, add_zero]

theorem dK_mem_frame (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (T : Kˣ) (r : Fin n → ℕ)
    (hx : AlgChart A x) (hT : dlog T = ∑ j ∈ J, (r j : K) • dlog (x j)) (c : K) (hc : c * (T : K) ∈ A) :
    ∃ d : Fin n → K, (∀ i, d i * (T : K) ∈ A) ∧ dK c = ∑ i, d i • frame x J i := by
  classical
  set a := c * (T : K) with ha
  obtain ⟨cc, hcc, hDa⟩ := hx.deriv a hc
  let e : Fin n → K := fun i => if i ∈ J then cc i * (x i : K) - a * (r i : K) else cc i
  have he : ∀ i, e i ∈ A := by
    intro i
    simp only [e]
    split_ifs
    · exact sub_mem (mul_mem (hcc i) (hx.mem i)) (mul_mem hc (natCast_mem A _))
    · exact hcc i
  have hT0 : (T : K) ≠ 0 := T.ne_zero
  refine ⟨fun i => (T : K)⁻¹ * e i, fun i => ?_, ?_⟩
  · rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hT0, one_mul]; exact he i
  have hsum : ∑ i, e i • frame x J i = dK a - a • ∑ j ∈ J, (r j : K) • dlog (x j) := by
    have hpt : ∀ i, e i • frame x J i =
        cc i • dK (x i : K) - (if i ∈ J then (a * (r i : K)) • dlog (x i) else 0) := by
      intro i
      simp only [e, frame]
      split_ifs
      · rw [sub_smul, mul_smul, ← dK_unit]
      · rw [sub_zero]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib, ← hDa, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.smul_sum]
    simp only [smul_smul]
  have hlead : dK a = c • dK (T : K) + (T : K) • dK c := Derivation.leibniz _ _ _
  have hTc : (T : K) • dK c = dK a - a • dlog T := by
    rw [hlead, dK_unit, smul_smul, ← ha]; abel
  calc dK c = (T : K)⁻¹ • ((T : K) • dK c) := by rw [smul_smul, inv_mul_cancel₀ hT0, one_smul]
    _ = _ := by
      rw [hTc, hT, ← hsum, Finset.smul_sum]
      simp only [smul_smul]

theorem dlog_twist (p : ℕ) [CharP K p] {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ)
    (r : Fin n → ℕ) : dlog (t ^ p * ∏ j ∈ J, x j ^ r j) = ∑ j ∈ J, (r j : K) • dlog (x j) := by
  rw [dlog_mul, dlog_pow, CharP.cast_eq_zero, zero_smul, zero_add, dlog_prod]
  simp only [dlog_pow]

end GlobalTheory.LogDR.StabD


open GlobalTheory.LogDR.StabD in
theorem GlobalTheory.LogDR.extD_mem_chartForms_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ), AlgChart A x → ∀ q, ∀ η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) q, extD K η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) (q + 1) := by
  intro K _ p _ _ A n x J t r hx q η hη
  unfold chartForms spanForms at hη ⊢
  induction hη using AddSubgroup.closure_induction with
  | mem η hη =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hη
    obtain ⟨d, hd, hDc⟩ := dK_mem_frame A x J _ r hx (dlog_twist p x J t r) c hc
    rw [extD_apply, CechDR.dDR_smul, dDR_ιMulti q v (fun i => by
      obtain ⟨k, hk⟩ := hv i; rw [← hk]; exact dDR_frame x J k), smul_zero, add_zero]
    change CechDR.ι1 (dK c) * _ ∈ _

    rw [hDc, map_sum, Finset.sum_mul]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨d i, hd i, Fin.cons (frame x J i) v, fun k => ?_, ?_⟩
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact ⟨i, rfl⟩
      · rw [Fin.cons_succ]; exact hv k
    · rw [ExteriorAlgebra.ιMulti_succ_apply, map_smul, smul_mul_assoc]
      rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [(extD K).map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
end
end

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem ofCard_symm_apply_eq_sort {n : ℕ} (s : Finset (Fin n)) (k : ℕ) (hk : k < s.card) :
    Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (rfl : s.card = s.card)) ⟨k, hk⟩ =
      (s.sort (· ≤ ·))[k]'(by rw [Finset.length_sort]; exact hk) := by
  show s.orderEmbOfFin rfl ⟨k, hk⟩ = _
  rw [Finset.orderEmbOfFin_apply]
  rfl

noncomputable def dlogBasis {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    Module.Basis (Fin n) K Ω[K⁄ℤ] :=
  (Module.Basis.mk hx.1 (by rw [hx.2])).unitsSMul fun i => (x i)⁻¹

theorem dlogBasis_apply {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) (i : Fin n) :
    dlogBasis x hx i = dlog (x i) := by
  rw [dlogBasis, Module.Basis.unitsSMul_apply, Module.Basis.mk_apply, Units.smul_def]
  rfl

theorem logWedge_eq_basis {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    logWedge x = ⇑(dlogBasis x hx).ExteriorAlgebra := by
  funext s
  rw [ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    logWedge]
  congr 1
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_ofFn, Function.comp_apply, dlogBasis_apply]
    rw [ofCard_symm_apply_eq_sort]

theorem logWedge_basis : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ), IsCoord x →
    LinearIndependent K (logWedge x) ∧ Submodule.span K (Set.range (logWedge x)) = ⊤ := by
  intro K _ n x hx
  rw [logWedge_eq_basis x hx]
  exact ⟨(dlogBasis x hx).ExteriorAlgebra.linearIndependent, (dlogBasis x hx).ExteriorAlgebra.span_eq⟩

end GlobalTheory.LogDR
end
