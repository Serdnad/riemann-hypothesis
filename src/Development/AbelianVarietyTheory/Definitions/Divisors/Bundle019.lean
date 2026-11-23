module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

section act
variable {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
  {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}

theorem IsEtLev.congr (h : IsEtLev o w0 r lv) {x y : D.La} (hxy : x - y ∈ wSub D w0 r) : lv x = lv y := by
  have : x = y + (x - y) := by abel
  rw [this, h.1, h.2.2.1 _ hxy, _root_.mul_one]

theorem IsEtLev.congr_mk (h : IsEtLev o w0 r lv) {x y : D.La}
    (hxy : Submodule.Quotient.mk (p := wSub D w0 r) x = Submodule.Quotient.mk y) : lv x = lv y :=
  h.congr ((Submodule.Quotient.eq _).1 hxy)

def liftAct (g : LevGrp D w0 r) (x : D.La) : D.La :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose

theorem mk_liftAct (g : LevGrp D w0 r) (x : D.La) :
    Submodule.Quotient.mk (p := wSub D w0 r) (liftAct g x) = g (Submodule.Quotient.mk x) :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose_spec

end act

end GlobalTheory.UPel.HT.EtLev
end
end

section

noncomputable section
namespace GlobalTheory.KS
namespace Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.EtC GlobalTheory.UPel.HT
open scoped TensorProduct

variable {S : Scheme.{0}} {O : Type} [Ring O]

theorem act_zero {A : Over S} [GrpObj A] (act : OActN O A) : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  have : act.act 0 * act.act 0 = act.act 0 * 1 := h.symm.trans (_root_.mul_one _).symm
  exact mul_left_cancel this

variable (l : ℕ) [Fact l.Prime] {E : Type} [CommRing E] [Algebra ℚ_[l] E]

section Gal
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

end Gal

theorem powMap_pr {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) : powMap f φ h m ≫ (pr A i).left = (pr A' i).left ≫ φ := by
  unfold powMap
  rw [← Over.comp_left, Pi.lift_comp_π]
  rfl

theorem powMap_over {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) : powMap f φ h m ≫ (pow A m).hom = (pow A' m).hom ≫ f := by
  unfold powMap
  exact Over.w _

end Model
end GlobalTheory.KS
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

def uIdeal (D : Datum p) (r : ℤ) : Ideal (𝓞 D.F) := Ideal.span {(p : 𝓞 D.F), D.ω - (r : 𝓞 D.F)}

theorem p_mem_uIdeal (D : Datum p) (r : ℤ) : (p : 𝓞 D.F) ∈ uIdeal D r :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem sub_mem_uIdeal (D : Datum p) (r : ℤ) : D.ω - (r : 𝓞 D.F) ∈ uIdeal D r :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

def IsPIsog {N : ℕ} {s : S ⟶ Sp R} (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) : Prop :=
  (∃ k : ℕ, c = p ^ k) ∧
  IsMonHom ψ ∧ (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta x ≫ ψ) ∧
    Nonempty (LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ))) ∧
    ∃ ψ' : o'.A ⟶ o.A, IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 o.A) ^ c ∧ ψ' ≫ ψ = (𝟙 o'.A) ^ c

theorem IsPIsog.exists_eq_pow {N : ℕ} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) : ∃ k : ℕ, c = p ^ k := h.1

theorem IsPIsog.pos {N : ℕ} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) : 0 < c := by
  obtain ⟨k, rfl⟩ := h.1
  exact pow_pos (Fact.out : p.Prime).pos k

def KilledBy {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (v : Ideal (𝓞 D.F)) {T : Over S} (g : T ⟶ o.A) : Prop :=
  ∀ a ∈ v, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1

def IsTj {N : ℕ} {s : S ⟶ Sp R} (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S),
    (∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)

structure TjCorr {N : ℕ} (F : RepFam b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) where

  Y : Scheme.{0}

  s : Y ⟶ F.X

  t : Y ⟶ F.X
  st : s ≫ F.s = t ≫ F.s

  o : Obj b N (s ≫ F.s)

  o' : Obj b N (s ≫ F.s)
  ms : ObjMap o F.univ s
  mt : ObjMap o' F.univ t

  ψ : o.A ⟶ o'.A
  isog : IsPIsog c o o' ψ
  tj : IsTj r w j o o' ψ

  wPrime : w.IsPrime

  uLe : uIdeal D r ≤ w

  pReg : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0

  sFin : IsFinite s

  tFin : IsFinite t

  sSurj : Surjective s

theorem KilledBy.one {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (v : Ideal (𝓞 D.F)) (T : Over S) :
    KilledBy o v (1 : T ⟶ o.A) := fun a _ => by
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
  exact one_comp _

theorem pReg_of_flat {Y : Scheme.{0}} (s : Y ⟶ Sp R) [Flat s] (hR : ∀ a : R, (p : R) * a = 0 → a = 0)
    (U : Y.Opens) (f : Γ(Y, U)) (hf : (p : Γ(Y, U)) * f = 0) : f = 0 := by
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · have hfl : (s.appLE ⊤ V.1.1 le_top).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) s inferInstance ⟨⊤, isAffineOpen_top _⟩ V.1 le_top
    have hp : (p : Γ(Sp R, ⊤)) ∈ nonZeroDivisors Γ(Sp R, ⊤) := by
      rw [mem_nonZeroDivisors_iff_left]
      intro a ha
      let e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
      refine e.injective ((hR _ ?_).trans (map_zero e).symm)
      rw [← map_natCast e, ← map_mul, ha, map_zero]
    letI := (s.appLE ⊤ V.1.1 le_top).hom.toAlgebra
    haveI : Module.Flat Γ(Sp R, ⊤) Γ(Y, V.1.1) := hfl
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(Y, V.1.1)) hp
    let ρ : Γ(Y, U) →+* Γ(Y, V.1.1) := (Y.presheaf.map (homOfLE V.2).op).hom
    show ρ f = ρ 0
    refine hreg ?_
    simp only [Algebra.smul_def, map_natCast, map_zero, mul_zero]
    rw [← map_natCast ρ, ← map_mul, hf, map_zero]

theorem pReg_of_isUnit {Y : Scheme.{0}} (s : Y ⟶ Sp R) (hR : IsUnit (p : R))
    (U : Y.Opens) (f : Γ(Y, U)) (hf : (p : Γ(Y, U)) * f = 0) : f = 0 := by
  have := hR.map (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appLE ⊤ U le_top).hom)
  rw [map_natCast] at this
  exact this.mul_right_eq_zero.1 hf

def IsWOrd {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) {k : Type} [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) : Prop :=
  CharP k p ∧ w.IsPrime ∧ (p : 𝓞 D.F) ∈ w ∧
    Nat.card {g : Over.mk x ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * (D.n - 1))

end GlobalTheory.UPel.HT.ES
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

structure Near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (G : Over S) where

  U : Over (Sp R)

  smooth : Smooth U.hom

  separated : IsSeparated U.hom

  quasiCompact : QuasiCompact U.hom

  u : pullback U.hom π ⟶ G.left

  isOpen : IsOpenImmersion u

  u_over : u ≫ G.hom = pullback.snd U.hom π

  all : ∀ g : G.left, π (G.hom g) = closedPoint R → g ∈ Set.range u

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

def Near.Pt (N : Near π G) {T : Scheme.{0}} (s : T ⟶ S) (a : T ⟶ N.U.left) (x : T ⟶ G.left) : Prop :=
  ∃ x₀ : T ⟶ pullback N.U.hom π, x₀ ≫ pullback.fst _ _ = a ∧ x₀ ≫ pullback.snd _ _ = s ∧ x₀ ≫ N.u = x

def Near.Law [GrpObj G] (N : Near π G) : Prop :=
  ∃ (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left),
    (∀ z : (N.U ⊗ N.U).left, (N.U ⊗ N.U).hom z = closedPoint R → z ∈ V) ∧ m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom ∧
    ∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G),
      N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left →
      N.Pt s (v ≫ m) (x * y).left

def Near.Datum [GrpObj G] (N : Near π G)
    (φ : (Over.pullback (pullback.fst π π)).obj G ≅ (Over.pullback (pullback.snd π π)).obj G) : Prop :=
  IsMonHom φ.hom ∧ ∀ (T : Scheme.{0}) (a : T ⟶ N.U.left) (x : T ⟶ ((Over.pullback (pullback.fst π π)).obj G).left),
    N.Pt (x ≫ pullback.snd G.hom (pullback.fst π π) ≫ pullback.fst π π) a (x ≫ pullback.fst G.hom (pullback.fst π π)) →
    N.Pt (x ≫ pullback.snd G.hom (pullback.fst π π) ≫ pullback.snd π π) a
      (x ≫ φ.hom.left ≫ pullback.fst G.hom (pullback.snd π π))

end

def Gal {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') : Subgroup (R' ≃+* R') where
  carrier := {σ | ∀ r, σ (ρ r) = ρ r}
  mul_mem' := fun {a b} ha hb r => by rw [RingAut.mul_apply, hb r, ha r]
  one_mem' := fun _ => rfl
  inv_mem' := fun {a} ha r => by
    have := congrArg a.symm (ha r)
    rw [RingEquiv.symm_apply_apply] at this
    exact this.symm

def Gal.hom {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'} (σ : Gal ρ) : R' →+* R' := σ.1.toRingHom

def PullOver {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {s : R' →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg ρ D D') (h : IsPullDeg s D' D') : Prop :=
  (∀ x, h.xe x = x) ∧ ∀ (b : D'.P.A.left ⟶ D.P.A.left) (c : D'.P.A.left ⟶ D'.P.A.left),
    b = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) → c = h.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) → c ≫ b = b

def IsGal {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') : Prop :=
  Finite (Gal ρ) ∧ ∀ x : R', (∀ σ ∈ Gal ρ, σ x = x) → x ∈ ρ.range

structure GalAct {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R'} (ρ : R →+* R')
    {D : DegPre R} {D' : DegData R' I} (hD : IsPullDeg ρ D D'.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')}
    [GrpObj G'] [IsCommMonObj G'] (U' : Unif I D' A' G') where

  act : Gal ρ → (G'.left ⟶ G'.left)

  cart : ∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)

  act_one : act 1 = 𝟙 _

  act_mul : ∀ σ τ, act (σ * τ) = act σ ≫ act τ

  unif : ∀ σ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre)
    (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
    bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = act σ ∧ IsPullUnif (Gal.hom σ) h bc U' U' ∧ PullOver hD h

end GlobalTheory.Mum
end
end
