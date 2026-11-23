module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.OneMul
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeKill
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

noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G

def LineEx : Prop := ∀ {Y T : Scheme.{0}} (j : T ⟶ Y) [IsClosedImmersion j],
  (∀ y : Y, ∃ (V : Y.Opens) (s : Γ(Y, V)), y ∈ V ∧ IsAffineOpen V ∧ s ∈ nonZeroDivisors Γ(Y, V) ∧ RingHom.ker (j.app V).hom = Ideal.span {s}) →
  ∃ (D : E.LineData Y) (f : ∀ {V : Scheme.{0}} (_ : V ⟶ D.Y), Γ(V, ⊤)),
    (∀ {V' V : Scheme.{0}} (g : V' ⟶ V) (a : V ⟶ D.Y), f (g ≫ a) = g.appTop.hom (f a)) ∧
    (∀ {V : Scheme.{0}} (a b : V ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f), f a = (D.u a b h : Γ(V, ⊤)) * f b) ∧
    (∀ {V : Scheme.{0}} (a : V ⟶ D.Y), (∀ v : V, (a ≫ D.f) v ∉ Set.range j) → IsUnit (f a)) ∧ sSup (Pb.𝒱D D) = ⊤ ∧ Etale D.f ∧
    ∀ (V : Y.Opens) (s : Γ(Y, V)), IsAffineOpen V → s ∈ nonZeroDivisors Γ(Y, V) → RingHom.ker (j.app V).hom = Ideal.span {s} →
      ∃ σ : (V : Scheme.{0}) ⟶ D.Y, σ ≫ D.f = V.ι ∧ f σ = V.topIso.inv.hom s

def BlowOfBl : Prop := ∀ (R : Type) [CommRing R] [IsNoetherianRing R] {Z W : Sch R} (d : ℕ) [IsProper Z.hom]
  [SmoothOfRelativeDimension d Z.hom] (π : W ⟶ XX Z), IsBl π →
    ∃ D : E.LineData W.left, Etale D.f ∧ Nonempty (Blow (XX Z).hom (dg Z).left π.left D d)

def BlowBC : Prop := ∀ (K K' : Type) [CommRing K] [CommRing K'] (φ : K →+* K') {W Z Y W' Z' Y' : Scheme.{0}}
  (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z) (D : E.LineData Y) (d : ℕ) (q' : Z' ⟶ Spec (CommRingCat.of K'))
  (i' : W' ⟶ Z') (π' : Y' ⟶ Z') (a : Z' ⟶ Z) (b : W' ⟶ W) (c : Y' ⟶ Y),
  IsPullback a q' q (Spec.map (CommRingCat.ofHom φ)) → IsPullback b i' i a → IsPullback c π' π a →
    Nonempty (Blow q i π D d) → Nonempty (Blow q' i' π' (D.pb c) d)

def PresBC : Prop := ∀ {Y Z Y' Z' : Scheme.{0}} (π : Y ⟶ Z) (π' : Y' ⟶ Z') (a : Z' ⟶ Z) (c : Y' ⟶ Y), IsPullback c π' π a →
  ∀ (V : Z.Opens) (C : Y.Opens) (h : C ≤ π ⁻¹ᵁ V), IsAffineOpen V → IsAffineOpen C → IsAffineOpen (a ⁻¹ᵁ V) →
  ∀ (h' : c ⁻¹ᵁ C ≤ π' ⁻¹ᵁ (a ⁻¹ᵁ V)) (σ : Type) (u : σ → Γ(Y, C)) (S : Set (MvPolynomial σ Γ(Z, V))),
    Function.Surjective (MvPolynomial.eval₂Hom (π.appLE V C h).hom u) → RingHom.ker (MvPolynomial.eval₂Hom (π.appLE V C h).hom u) = Ideal.span S →
    IsAffineOpen (c ⁻¹ᵁ C) ∧ Function.Surjective (MvPolynomial.eval₂Hom (π'.appLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) h').hom fun s => (c.app C).hom (u s)) ∧
      RingHom.ker (MvPolynomial.eval₂Hom (π'.appLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) h').hom fun s => (c.app C).hom (u s)) =
        Ideal.span (MvPolynomial.map (a.app V).hom '' S)

def CoordBC : Prop := ∀ (K K' : Type) [CommRing K] [CommRing K'] (φ : K →+* K') {Z Z' : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K))
  (q' : Z' ⟶ Spec (CommRingCat.of K')) (a : Z' ⟶ Z), IsPullback a q' q (Spec.map (CommRingCat.ofHom φ)) → ∀ (V : Z.Opens), IsAffineOpen V →
  ∀ (σ : Type) (x : σ → Γ(Z, V)), (MvPolynomial.eval₂Hom (Pb.strV q V) x).Etale →
    IsAffineOpen (a ⁻¹ᵁ V) ∧ (MvPolynomial.eval₂Hom (Pb.strV q' (a ⁻¹ᵁ V)) fun s => (a.app V).hom (x s)).Etale

def OKDvr : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  IsNoetherianRing (OK l K)

def SmSst : Prop := ∀ (O : Type) [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) [Smooth p],
  GlobalTheory.Et.IsStrictlySemistable ϖ p

end UpperTheory.Gal.KunnethLefschetz.G
end
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G

structure PBData {T W : Scheme.{0}} (r : T ⟶ W) (d : ℕ) where
  W' : Scheme.{0}
  c : W' ⟶ W
  [smc : Smooth c]
  [suc : Surjective c]
  g : ∀ {V : Scheme.{0}} (a b : V ⟶ W'), a ≫ c = b ≫ c → GL (Fin d) Γ(V, ⊤)
  g_nat : ∀ {V' V : Scheme.{0}} (s : V' ⟶ V) (a b : V ⟶ W') (h : a ≫ c = b ≫ c),
    g (s ≫ a) (s ≫ b) (by rw [Category.assoc, h, Category.assoc]) = Matrix.GeneralLinearGroup.map s.appTop.hom (g a b h)
  g_coc : ∀ {V : Scheme.{0}} (a b k : V ⟶ W') (h : a ≫ c = b ≫ c) (h' : b ≫ c = k ≫ c), g b k h' * g a b h = g a k (h.trans h')
  T' : Scheme.{0}
  e : T' ⟶ T
  [sme : Smooth e]
  [sue : Surjective e]
  ρ : T' ⟶ W'
  comm : ρ ≫ c = e ≫ r
  v : ∀ {V : Scheme.{0}} (_ : V ⟶ T'), Um d Γ(V, ⊤)
  v_nat : ∀ {V' V : Scheme.{0}} (s : V' ⟶ V) (a : V ⟶ T'), (v (s ≫ a)).1 = s.appTop.hom ∘ (v a).1
  w : ∀ {V : Scheme.{0}} (a b : V ⟶ T'), a ≫ e = b ≫ e → (Γ(V, ⊤))ˣ
  gv : ∀ {V : Scheme.{0}} (a b : V ⟶ T') (h : a ≫ e = b ≫ e) (h' : (a ≫ ρ) ≫ c = (b ≫ ρ) ≫ c),
    (g _ _ h' : Matrix _ _ _).mulVec (v a).1 = (w a b h : Γ(V, ⊤)) • (v b).1
  inj : ∀ {V : Scheme.{0}} (a b : V ⟶ T') (h' : (a ≫ ρ) ≫ c = (b ≫ ρ) ≫ c) (u : (Γ(V, ⊤))ˣ),
    (g _ _ h' : Matrix _ _ _).mulVec (v a).1 = (u : Γ(V, ⊤)) • (v b).1 → a ≫ e = b ≫ e
  onto : ∀ {V : Scheme.{0}} (a₀ : V ⟶ W') (v₀ : Um d Γ(V, ⊤)) (x : V), ∃ (U : V.Opens) (a : (U : Scheme.{0}) ⟶ T')
    (h : (a ≫ ρ) ≫ c = (U.ι ≫ a₀) ≫ c) (u : (Γ((U : Scheme.{0}), ⊤))ˣ), x ∈ U ∧
      (g _ _ h : Matrix _ _ _).mulVec (v a).1 = (u : Γ((U : Scheme.{0}), ⊤)) • (U.ι.appTop.hom ∘ v₀.1)

def PBEx : Prop := ∀ (K : Type) [CommRing K] {W Z Y T : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z)
  (D : E.LineData Y) (d : ℕ), Nonempty (Blow q i π D d) → ∀ (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i →
  ∃ (P : PBData r d) (τ : P.T' ⟶ D.Y) (hτ : τ ≫ D.f = P.e ≫ j), ∀ {V : Scheme.{0}} (a b : V ⟶ P.T') (h : a ≫ P.e = b ≫ P.e)
    (h' : (a ≫ τ) ≫ D.f = (b ≫ τ) ≫ D.f), P.w a b h = (D.u _ _ h')⁻¹

def PBOf : Prop := In → ∀ (q : ℕ) [NeZero q] {T W : Scheme.{0}} (r : T ⟶ W) (d : ℕ) (P : PBData r d), IsUnit (q : Γ(W, ⊤)) →
  ∀ (L : cech P.e ⟶ ofCat (glCat 1)) (ε : ℤˣ), (∀ (V : Scheme.{0}) (x : V ⟶ T) (a : Fin 2 → (V ⟶ P.T')) (h : ∀ s, a s ≫ P.e = x),
    lineUnit L (cechPt P.e 1 x a h) = P.w (a 0) (a 1) ((h 0).trans (h 1).symm) ^ (ε : ℤ)) →
  ∀ x : Ht q (sch.obj T) 2 1, pull _ (cechAug P.e) _ 2 x = c1 q L → PBT q d r x

def PBE : Prop := In → ∀ (q : ℕ) [NeZero q] (K : Type) [CommRing K], IsUnit (q : K) → ∀ {W Z Y T : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z) (D : E.LineData Y) (d : ℕ), Nonempty (Blow p i π D d) →
  ∀ (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → ∀ L : cech D.f ⟶ ofCat (glCat 1), D.IsMap L →
  ∀ x : Ht q (sch.obj Y) 2 1, pull _ (cechAug D.f) _ 2 x = c1 q L →
    PBT q d r (pull _ (sch.map j) _ 2 x) ∧ ∀ U : Y.Opens, Off j U → pull _ (sch.map U.ι) _ 2 x = 0

def BlowE : Prop := ∀ (K : Type) [Field K] {W Z Y T : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z)
  (D : E.LineData Y) (d e : ℕ), Nonempty (Blow p i π D (d + 1)) → SmoothOfRelativeDimension (e + (d + 1)) p → IsProper π →
  ∀ (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → IsPair 1 (e + d) (π ≫ p) j ∧ IsProper r

def RegSeq : Prop := ∀ (A C : Type) [CommRing A] [CommRing C] (d : ℕ) (φ : MvPolynomial (Fin d) A →+* C), φ.Flat →
  ∀ a : Fin d → C, ∑ l, a l * φ (MvPolynomial.X l) ∈ Ideal.span (Set.range fun l => φ (MvPolynomial.X l)) ^ 2 →
    ∀ l, a l ∈ Ideal.span (Set.range fun l => φ (MvPolynomial.X l))

end UpperTheory.Gal.KunnethLefschetz.G
end
end
