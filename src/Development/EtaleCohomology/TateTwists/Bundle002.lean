module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts : Prop :=
  ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ),
    (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V),
    ∃ e : ((Arrow.mk g).cechConerve ⋙ Ψ).leftOp ≅ (Arrow.mk (Ψ.map g).unop).cechNerve,
      lev Ψ (coAug g) = e.hom ≫ (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKummerClassExplicitCocycle : Prop :=
  ∀ (q : ℕ) [NeZero q],
    (∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
      ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
        CohomologyClass.mk γ = kum q u ∧
        (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
        ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ),
          v ^ q = Units.map x.appTop.hom.toMonoidHom u →
          ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
      pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)) ∧
    ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
      kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleRootsOfUnityReductionMapGenerator : Prop :=
  ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsEtaleFirstChernKummerCocycleRep (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def first_chern_class_exists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ, IsEtaleFirstChernKummerCocycleRep q L γ

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupLeibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)), μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ → δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleCochainCupAssociativeOfPairing : Prop :=
  ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M') (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) → ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w) a b c, ν.cup E h2 (μ.cup E h1 a b) c = ν'.cup E h4 a (μ'.cup E h3 b c)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleCochainEvaluationNaturalInRestriction : Prop :=
  ∀ {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U),
    ev (R := R) α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) =
      Sec.res g (ev (R := R) α p s h U x)

theorem freeGen_nat {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  have hm : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)) =
      ModuleCat.freeMk (R := ULift.{1} R) (ULift.up (P.map g.op x)) := by
    simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.comp_map]; erw [ModuleCat.free_map_apply]; rfl
  exact h.symm.trans (congrArg (toSheafify Scheme.etaleTopology ((freeP R).obj P) |>.app (op V)).hom hm)

theorem ev_nat_pf : EtaleCochainEvaluationNaturalInRestriction := by
  intro R _ E I n α p s h V U g x
  unfold ev
  rw [← freeGen_nat]
  have key := congrArg (fun f => f.hom (freeGen R _ U x))
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at key
  exact key

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty : Prop :=
  ∀ (R : Type) [CommRing R] (P : PSh) (F : Shv R), (∀ a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) → ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x) ∧ (∀ φ ψ : (free R).obj P ⟶ F, (∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) → φ = ψ) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x)) ∧ ∀ (Q : PSh) (f : P ⟶ Q) U x, Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKummerTriangleExists : Prop :=
  ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleRestrictScalarsResolutionCompatible : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S)
    (U : Scheme.{0}) (a : Sec F U),
    (GlobalTheory.EtC.restrMap φ F).app U 0 (Sec.map (resι S F) a) =
      Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSchemeGlobalSectionCohomologyClass : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k →
    (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev (R := R) α.1 0 n (by simp) U x = Sec.res x z) ∧
      ∀ (p : ℕ) s h U x, ev (R := R) α.1 (p + 1) s h U x = 0) ∧
    ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n,
      Sec.map (I.d n k) (ev (R := R) α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
      (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X,
        Sec.map (I.d m n) y = ev (R := R) α.1 0 n (by simp) X (𝟙 X))
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTwistResolutionPairingCupUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k → ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν → ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h
end
