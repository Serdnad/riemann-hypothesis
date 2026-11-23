module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle920
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle919
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift.DPStep

variable {R : Type} [CommRing R] {I : Ideal R}

def prods (κ : DividedPowers I) (m : ℕ) : Set R :=
  {x | ∃ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) ∧ m ≤ (l.map Prod.fst).sum ∧
    x = (l.map fun p ↦ κ.dpow p.1 p.2).prod}

theorem prod_mem (κ : DividedPowers I) : ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) →
    1 ≤ (l.map Prod.fst).sum → (l.map fun p ↦ κ.dpow p.1 p.2).prod ∈ I := by
  intro l
  induction l with
  | nil => simp
  | cons p l ih =>
    intro hl hs
    have hp : p.2 ∈ I := hl p (by simp)
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h] at hs
      exact I.mul_mem_left _ (ih (fun q hq ↦ hl q (by simp [hq])) (by omega))
    · exact I.mul_mem_right _ (κ.dpow_mem (by omega) hp)

theorem dpow_prod_eq_zero (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    ∀ l : List (ℕ × R), (∀ p ∈ l, p.2 ∈ I) → N + 1 ≤ (l.map Prod.fst).sum →
      ∀ n, 2 ≤ n → κ.dpow n (l.map fun p ↦ κ.dpow p.1 p.2).prod = 0 := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons p l ih =>
    intro hl hs n hn
    have hp : p.2 ∈ I := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ I := fun q hq ↦ hl q (by simp [hq])
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · rw [h, κ.dpow_zero hp, _root_.one_mul]
      exact ih hl' (by omega) n hn
    · set P := (l.map fun p ↦ κ.dpow p.1 p.2).prod
      have hm : κ.dpow p.1 p.2 ∈ I := κ.dpow_mem (by omega) hp
      have hz : P * κ.dpow (n * p.1) p.2 = 0 := by
        have := hN ((n * p.1, p.2) :: l) (by
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hp
          · exact hl' q hq) (by
          have : 2 * p.1 ≤ n * p.1 := Nat.mul_le_mul_right _ hn
          simp only [List.map_cons, List.sum_cons]
          omega)
        simpa [List.map_cons, List.prod_cons, mul_comm] using this
      rw [mul_comm, κ.dpow_mul hm, κ.dpow_comp (by omega) hp]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_left_comm, _root_.mul_assoc, hz, mul_zero, mul_zero]

end GlobalTheory.SqLift.DPStep

namespace GlobalTheory.SqLift.DPStep

variable {R : Type} [CommRing R] {I : Ideal R}

def idl (κ : DividedPowers I) (m : ℕ) : Ideal R := Ideal.span (prods κ m)

theorem idl_le (κ : DividedPowers I) (N : ℕ) : idl κ (N + 1) ≤ I := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨l, hl, hs, rfl⟩
  exact prod_mem κ l hl (by omega)

theorem mul_idl_eq_zero (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) {a : R} (ha : a ∈ I) :
    ∀ b ∈ idl κ (N + 1), a * b = 0 := by
  intro b hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    have := hN ((1, a) :: l) (by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ha
      · exact hl q hq) (by simp only [List.map_cons, List.sum_cons]; omega)
    simpa [κ.dpow_one ha] using this
  | zero => exact mul_zero a
  | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

theorem idl_sq (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) : idl κ (N + 1) ^ 2 = 0 := by
  rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two]
  refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
  rw [Ideal.mem_bot]
  exact mul_idl_eq_zero κ hN (idl_le κ N ha) b hb

theorem dpow_idl (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    ∀ x ∈ idl κ (N + 1), ∀ n, 2 ≤ n → κ.dpow n x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hs, rfl⟩ := hx
    exact dpow_prod_eq_zero κ hN l hl hs
  | zero => intro n hn; exact κ.dpow_eval_zero (by omega)
  | add x y hxm hym hx hy =>
    intro n hn
    have hxI := idl_le κ N hxm
    have hyI := idl_le κ N hym
    rw [κ.dpow_add hxI hyI]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
    by_cases h1 : 2 ≤ k.1
    · rw [hx _ h1, MulZeroClass.zero_mul]
    by_cases h2 : 2 ≤ k.2
    · rw [hy _ h2, mul_zero]
    obtain ⟨a, b⟩ := k
    simp only at h1 h2 hk
    obtain rfl : a = 1 := by omega
    obtain rfl : b = 1 := by omega
    rw [κ.dpow_one hxI, κ.dpow_one hyI]
    exact mul_idl_eq_zero κ hN hxI y hym
  | smul r x hxm hx =>
    intro n hn
    rw [smul_eq_mul, κ.dpow_mul (idl_le κ N hxm), hx n hn, mul_zero]

theorem isSubDPIdeal (κ : DividedPowers I) {N : ℕ} (hN : NilExp κ (N + 2)) :
    IsSubDPIdeal κ (idl κ (N + 1) ⊓ I) := by
  refine DividedPowers.IsSubDPIdeal.mk inf_le_right ?_
  intro n hn j hj
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [κ.dpow_one hj.2]
    exact hj
  · rw [dpow_idl κ hN j hj.1 n h]
    exact Ideal.zero_mem _

end GlobalTheory.SqLift.DPStep


open GlobalTheory.SqLift.DPStep in
theorem GlobalTheory.SqLift.exists_isStep_nilExp :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → ∀ N : ℕ, NilExp κ (N + 2) →
    ∃ (R₁ : Type) (_ : CommRing R₁) (J : Ideal R) (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (I₁ : Ideal R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀),
      IsStep κ π hJ ρ κ₁ π₁ ∧ NilExp κ₁ (N + 1) := by
  intro R R₀ _ _ I κ π hπ hker N hN
  set J := idl κ (N + 1)
  have hJI : J ≤ I := idl_le κ N
  have hsub := isSubDPIdeal κ hN
  have hz : ∀ a ∈ J, π a = 0 := fun a ha ↦ by rw [← RingHom.mem_ker, hker]; exact hJI ha
  let π₁ : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π hz
  have hnil1 : NilExp (DividedPowers.Quotient.dividedPowers κ hsub) (N + 1) := by
    intro l hl hs
    have key : ∀ l : List (ℕ × (R ⧸ J)), (∀ p ∈ l, p.2 ∈ I.map (Ideal.Quotient.mk J)) →
        ∃ l' : List (ℕ × R), (∀ p ∈ l', p.2 ∈ I) ∧ l'.map Prod.fst = l.map Prod.fst ∧
          (l.map fun p ↦ (DividedPowers.Quotient.dividedPowers κ hsub).dpow p.1 p.2).prod =
            Ideal.Quotient.mk J (l'.map fun p ↦ κ.dpow p.1 p.2).prod := by
      intro l
      induction l with
      | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
      | cons p l ih =>
        intro hl
        obtain ⟨l', hl', he, hp⟩ := ih fun q hq ↦ hl q (by simp [hq])
        obtain ⟨a, ha, hae⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
          (hl p (by simp))
        refine ⟨(p.1, a) :: l', ?_, by simp [he], ?_⟩
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact ha
          · exact hl' q hq
        · simp only [List.map_cons, List.prod_cons, map_mul, hp, ← hae]
          rw [DividedPowers.Quotient.dpow_apply κ hsub ha]
    obtain ⟨l', hl', he, hp⟩ := key l hl
    rw [hp, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨l', hl', by rw [he]; exact hs, rfl⟩
  refine ⟨R ⧸ J, inferInstance, J, idl_sq κ hN, Ideal.Quotient.mk J, I.map (Ideal.Quotient.mk J),
    DividedPowers.Quotient.dividedPowers κ hsub, π₁, ?_, hnil1⟩
  refine
    { nil := ⟨N + 2, hN⟩
      nil₁ := ⟨N + 1, hnil1⟩
      surj := Ideal.Quotient.mk_surjective
      surj₁ := ?_
      comp := Ideal.Quotient.lift_comp_mk J π hz
      ker := hker
      kerJ := Ideal.mk_ker
      ker₁ := ?_
      dp := DividedPowers.Quotient.isDPMorphism κ hsub
      dpJ := ?_ }
  · intro y
    obtain ⟨a, rfl⟩ := hπ y
    exact ⟨Ideal.Quotient.mk J a, Ideal.Quotient.lift_mk J π hz⟩
  · ext y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hker, Ideal.mem_quotient_iff_mem hJI]
  · refine (isDPMorphism_iff _ _ _).2 ⟨by rw [Ideal.map_id]; exact hJI, fun n hn a ha ↦ ?_⟩
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [RingHom.id_apply, RingHom.id_apply, κ.dpow_one (hJI ha), (divided₂ _).dpow_one ha]
    · rw [RingHom.id_apply, RingHom.id_apply, squareZeroDividedPowers_dpow _ h, dpow_idl κ hN a ha n h]
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op)) := by
  first | exact @GlobalTheory.CoverHyp.restrict_bijective | exact GlobalTheory.CoverHyp.restrict_bijective | (intros; apply GlobalTheory.CoverHyp.restrict_bijective <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.LBLift

section Alg

variable {R : Type} [CommRing R] (I : Ideal R) {D T : Type} [Category.{0} D] [Category.{0} T]

def In1 (F : D ⥤ CommAlgCat.{0} R) (f : C1 F) : Prop :=
  ∀ (t t' : D) (a : t ⟶ t'), f t t' a ∈ I.map (algebraMap R (F.obj t'))

def In2 (F : D ⥤ CommAlgCat.{0} R) (z : C2 F) : Prop :=
  ∀ (t t' t'' : D) (a : t ⟶ t') (b : t' ⟶ t''), z t t' t'' a b ∈ I.map (algebraMap R (F.obj t''))

variable {F : D ⥤ CommAlgCat.{0} R} {F' : T ⥤ CommAlgCat.{0} R}

def PrimI (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F') : Prop :=
  ∀ (z : Z2 F) (f : C1 F'), In2 I F z.1 → In1 I F' f →
    d1 F' f = (n₀.pullbackTwoCocycle z).1 - (n₁.pullbackTwoCocycle z).1 - (n₂.pullbackTwoCocycle z).1 → ∃ f₀ : C1 F, In1 I F f₀ ∧ d1 F f₀ = z.1

def mdef (F : D ⥤ CommAlgCat.{0} R) (u : C1 F) : C2 F :=
  fun t t' t'' a b ↦ mp F b (u t t' a) * u t' t'' b - u t t'' (a ≫ b)

def MulRel (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F') (u : C1 F) (v : C0 F') : Prop :=
  In1 I F' fun t t' a ↦ n₀.α t' (u _ _ (n₀.G.map a)) * v t' -
    n₁.α t' (u _ _ (n₁.G.map a)) * n₂.α t' (u _ _ (n₂.G.map a)) * mp F' a (v t)

end Alg

section Geo

variable {R : Type} [CommRing R] {X X₀ Y : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

structure IsBasis (G : D ⥤ AffOp X) : Prop where
  cover : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : D, x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U
  dir : ∀ (t₁ t₂ : D) (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 →
    ∃ t₃ : D, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U

def pullMap {s : X ⟶ Sp R} {s' : Y ⟶ Sp R} {φ : Y ⟶ X} (w : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (G : D ⥤ AffOp X) (H : T ⥤ AffOp Y) (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) :
    CoefMap (RingHom.id R) (G ⋙ OAff s) (H ⋙ OAff s') where
  G := K
  α t := CechDR.secPull s s' ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩
  naturality {p q} a b :=
    (congrArg (fun t ↦ t.hom b) (φ.map_appLE (le q) (homOfLE (leOfHom (G.map (K.map a)).unop)).op)).trans
      (congrArg (fun t ↦ t.hom b) (φ.appLE_map (le p) (homOfLE (leOfHom (H.map a).unop)).op)).symm
  smul t := semiHom_secPull w ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩

structure IsThick (I : Ideal R) (s : X ⟶ Sp R) (i : X₀ ⟶ X) : Prop where
  closed : IsClosedImmersion i
  surj : Surjective i
  app_surj : ∀ U : X.affineOpens, Function.Surjective (i.app U.1).hom
  ker : ∀ (U : X.affineOpens) (b : Sec s U.1), (i.app U.1).hom b = 0 ↔ b ∈ I.map (algebraMap R (Sec s U.1))

def Small (i : X₀ ⟶ X) (L : LB X₀) : Type := {p : X.affineOpens × L.ι // i ⁻¹ᵁ p.1.1 ≤ L.U p.2}

instance (i : X₀ ⟶ X) (L : LB X₀) : Preorder (Small i L) := Preorder.lift fun p ↦ p.1.1

def smallG (i : X₀ ⟶ X) (L : LB X₀) : (Small i L)ᵒᵖ ⥤ AffOp X :=
  (Monotone.functor (f := fun p : Small i L ↦ p.1.1) fun _ _ h ↦ h).op

theorem Small.le_inf {i : X₀ ⟶ X} {L : LB X₀} {p q : (Small i L)ᵒᵖ} (a : p ⟶ q) :
    i ⁻¹ᵁ q.unop.1.1.1 ≤ L.U p.unop.1.2 ⊓ L.U q.unop.1.2 :=
  _root_.le_inf (fun _ hx ↦ p.unop.2 ((show q.unop.1.1 ≤ p.unop.1.1 from leOfHom a.unop) hx)) q.unop.2

def IsLift (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀) (u : C1 (smallG i L ⋙ OAff s)) : Prop :=
  ∀ (p q : (Small i L)ᵒᵖ) (a : p ⟶ q),
    (i.app q.unop.1.1.1).hom (u p q a) = (res (Small.le_inf a) (L.g p.unop.1.2 q.unop.1.2)).val

end Geo


open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic in
attribute [local instance] Over.cartesianMonoidalCategory in
def AbLift : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (X₀ Y₀ : Scheme.{0}) (i : X₀ ⟶ A.left) (i' : Y₀ ⟶ (A ⊗ A).left) (ψ₀ ψ₁ ψ₂ : Y₀ ⟶ X₀),
      IsThick I A.hom i → IsThick I (A ⊗ A).hom i' → ψ₀ ≫ i = i' ≫ (μ[A]).left → ψ₁ ≫ i = i' ≫ (fst A A).left →
      ψ₂ ≫ i = i' ≫ (snd A A).left →
      ∀ c : Pic X₀, CechPic.pull ψ₀ c = CechPic.pull ψ₁ c + CechPic.pull ψ₂ c → ∃ c' : Pic A.left, CechPic.pull i c' = c

end GlobalTheory.LBLift
end
end

section

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystalline_H2_small_cover_bijective : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull2 := by
  first | exact @GlobalTheory.Cris.small_descent_H2_bijective | exact GlobalTheory.Cris.small_descent_H2_bijective | (intros; apply GlobalTheory.Cris.small_descent_H2_bijective <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.Wts

variable {ι : Type} {N : ℕ} (W : Wts ι N)

theorem div_gap_step (h : W.Hyp) (hd : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) :
    0 ≤ W.u1 τ a - W.u1 τ b ∧
      ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) ≤ W.u τ a - W.u τ b + 2 := by
  have hM : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
  have hc := h.weightConst_nonneg
  obtain ⟨h41, -, h43⟩ := h.h4 τ a b hab
  have h2 := h.h2.1
  rw [(hd τ).2 a b hab]
  have hN : (0 : ℤ) ≤ N := by positivity
  split_ifs with hb
  · have := h43 hb
    refine ⟨Int.ediv_nonneg (by linarith) hM.le, ?_⟩
    refine (Int.mul_ediv_self_le hM.ne').trans ?_
    linarith
  · have h5 := h41 hb
    have h6 : (0 : ℤ) ≤ ((W.T : ℤ) + W.Dd + 2) * ((W.T : ℤ) + W.Dd + 2 + 2 * N) := by positivity
    exact ⟨Int.ediv_nonneg (by linarith) hM.le, Int.mul_ediv_self_le hM.ne'⟩

theorem div_gap_sum (h : W.Hyp) (hd : W.IsDiv) (τ : ι) (n : ℕ) : ∀ a b : Fin N, (b : ℕ) = a + n →
    0 ≤ W.u1 τ a - W.u1 τ b ∧
      ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) ≤ W.u τ a - W.u τ b + 2 * n := by
  induction n with
  | zero =>
    intro a b hab
    have : b = a := Fin.ext (by simpa using hab)
    subst this
    simp
  | succ n ih =>
    intro a b hab
    have hlt : (a : ℕ) + n < N := by have := b.2; omega
    obtain ⟨h1, h2⟩ := ih a ⟨a + n, hlt⟩ rfl
    obtain ⟨h3, h4⟩ := W.div_gap_step h hd τ ⟨a + n, hlt⟩ b (by simp; omega)
    refine ⟨by linarith, ?_⟩
    push_cast
    nlinarith

end GlobalTheory.MeanTop.Wts

namespace GlobalTheory.MeanTop

theorem divided_entries : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ i,
    ((W.T : ℤ) + W.Dd + 1) * |W.u1 τ i| ≤ |W.u τ i| + W.c0 + 4 * N ∧
      (W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0) ∧ ((i : ℕ) < W.kc → 0 ≤ W.u1 τ i) := by
  intro ι _ N W h hd τ i
  have hk := h.kc_pos
  have hk2 := h.kc_lt
  have hp := h.p_lt
  have hc := h.weightConst_nonneg
  have hi := i.2
  have hN : (0 : ℤ) ≤ N := by positivity
  let a : Fin N := ⟨W.kc - 1, by omega⟩
  have ha : (a : ℕ) + 1 = W.kc := by simp only [a]; omega
  have hu : W.u τ a = 0 := h.anchor τ a ha
  have hu1 : W.u1 τ a = 0 := (hd τ).1 a ha
  have up : (i : ℕ) < W.kc → 0 ≤ W.u1 τ i ∧
      ((W.T : ℤ) + W.Dd + 1) * W.u1 τ i ≤ W.u τ i + 2 * N := by
    intro hi'
    obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (a - i) i a (by omega)
    have h3 : (((a : ℕ) - i : ℕ) : ℤ) ≤ N := by omega
    rw [hu1, sub_zero] at h1 h2
    rw [hu] at h2
    exact ⟨h1, by linarith⟩
  have down : W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0 ∧
      ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) ≤ -W.u τ i + 2 * N := by
    intro hi'
    obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (i - a) a i (by omega)
    have h3 : (((i : ℕ) - a : ℕ) : ℤ) ≤ N := by omega
    rw [hu1, zero_sub] at h1 h2
    rw [hu] at h2
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, fun hi' => (down hi').1, fun hi' => (up hi').1⟩
  by_cases hi' : (i : ℕ) < W.kc
  · obtain ⟨h1, h2⟩ := up hi'
    rw [abs_of_nonneg h1]
    have := le_abs_self (W.u τ i)
    linarith
  · obtain ⟨h1, h2⟩ := down (by omega)
    rw [abs_of_nonpos h1]
    have := neg_le_abs (W.u τ i)
    linarith

end GlobalTheory.MeanTop
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_tangent_of_uniformisation_jet : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g), A.left.IsSeparated → ∀ (W : Opens (Tot Empty g)) (x : Sp (Hol W) ⟶ A.left), (∀ (p : Tot Empty g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = (u.ex p.2).left) → x ≫ A.hom = spMap (algebraMap ℂ (Hol W)) → (0 : Tot Empty g) ∈ W → ∀ (w : Fin g → ℂ) (ρ : Hol W →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn 0 ∧ (ρ h).snd = fderiv ℂ h.fn 0 (0, w)) → ∃ v : epsR ℂ ⟶ A, v.left = spMap ρ.toRingHom ≫ x ∧ IsTangent v ∧ u.IsDiff w v := by
  first | exact @GlobalTheory.AnPer.exists_tangent_of_jet | exact GlobalTheory.AnPer.exists_tangent_of_jet | (intros; apply GlobalTheory.AnPer.exists_tangent_of_jet <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.period_formalLog_lift_characterSeries : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) [Algebra ℚ F.Q] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), constantCoeff g = 1 → (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ t, c.HasPeriod F.θ t (formalLog (map (algebraMap F.B F.Q) g)) (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  first | exact @GlobalTheory.CharPeriod.hasPeriod_formalLog_char | exact GlobalTheory.CharPeriod.hasPeriod_formalLog_char | (intros; apply GlobalTheory.CharPeriod.hasPeriod_formalLog_char <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.coeff_mem_of_coeff_cob1_mem : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ I : Ideal O, (p : O) ∈ I → ∀ s : MvPowerSeries (Fin d) O, (∀ α, coeff α (cob1 c.μ s) ∈ I) → ∀ α, coeff α s ∈ I := by
  first | exact @GlobalTheory.QLog.coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem | exact GlobalTheory.QLog.coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem | (intros; apply GlobalTheory.QLog.coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem <;> assumption)
end
