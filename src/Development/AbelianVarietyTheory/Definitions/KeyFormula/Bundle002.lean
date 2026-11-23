module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import Mathlib.Analysis.Complex.Polynomial.Basic
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.KeyKa
open GlobalTheory.KeyPow

def KaRule (g c M : ℕ) : Prop :=
  ∃ ka : ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K], KeyIn K → Kˣ,
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (Mx : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (Mx i) v (v' i)) →
      a ^ (8 * c) * (ka K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = Mx.det ^ (4 * c) * ka K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧
    (∀ (K K' : Type) [Field K] [CharZero K] [IsAlgClosed K] [Field K'] [CharZero K'] [IsAlgClosed K'] (f : K →+* K')
      (x : KeyIn K) (x' : KeyIn K'), x.P.g = g → KeyPB x' x f → (ka K' x' : K') = f (ka K x)) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (x : KeyIn R), x.P.g = g → IsUnit (M : R) →
      ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (j : R →+* R') (u : R'ˣ),
        Function.Injective j ∧ IsLocalHom j ∧
        ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (f : R' →+* K) (xK : KeyIn K),
          KeyPB xK x (f.comp j) → (ka K xK : K) = f u) ∧
    ∀ a b : Fin g → ℂ, charHalf g a b → ∃ U : Matrix (Fin g) (Fin g) ℂ → ℂ, Key.IsHoloSiegel g U ∧
      ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm))

def KaSt : Prop := ∀ g p : ℕ, 1 ≤ g → p.Prime → ∃ c M : ℕ, 1 ≤ c ∧ 1 ≤ M ∧ ¬ p ∣ M ∧ KaRule g c M

def KeyDesc : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), ∃ (K₀ : Subfield K) (x₀ : KeyIn K₀), Countable K₀ ∧ KeyPB x x₀ K₀.subtype

def KaRuleK (g c M : ℕ) (ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ) : Prop :=
    (∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (Mx : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (Mx i) v (v' i)) →
      a ^ (8 * c) * (ka K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = Mx.det ^ (4 * c) * ka K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧
    (∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K')
      (x : KeyIn K) (x' : KeyIn K'), x.P.g = g → KeyPB x' x f → (ka K' x' : K') = f (ka K x)) ∧
    (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), x.P.g = g → IsUnit (M : R) → KeyPB xK x (algebraMap R K) →
      ∃ u : Rˣ, (ka K xK : K) = algebraMap R K u ∧
        ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
          (ka k xk : k) = r u) ∧
    ∀ a b : Fin g → ℂ, charHalf g a b → ∃ U : Matrix (Fin g) (Fin g) ℂ → ℂ, Key.IsHoloSiegel g U ∧
      ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm))

end GlobalTheory.KeyKa
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyEq

def Val (x : KeyIn ℂ) (t : ℂ) : Prop :=
  ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
    charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8

def Nrm (x : KeyIn ℂ) {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) : Prop :=
  ∃ (h : x.P.g = g) (M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ), c ≠ 0 ∧
    NormalAt x (τ.submatrix (Fin.cast h) (Fin.cast h)) M (fun i => a (i.cast h)) (fun i => b (i.cast h)) c

def frac {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (m n : Fin g → ℤ) : Fin g → ℂ :=
  (k : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))

def trl {S : Scheme.{0}} (A : Over S) [GrpObj A] (p : 𝟙_ (Over S) ⟶ A) : A ⟶ A := (toUnit A ≫ p) * 𝟙 A

def IsTrl (x' x : KeyIn ℂ) (p : 𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) (ν : ℂˣ) : Prop :=
  ∃ (φ : x'.P.A ≅ x.P.A) (hg : x'.P.g = x.P.g) (w : LB.Iso x'.P.L (x.P.L.pull (φ.hom ≫ trl x.P.A p).left))
    (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ 2).left, 𝟙 x.P.A.left] ![1, -4]))
    (rp : LB.Gen (x.P.L.pull p.left)),
    p ^ 2 = 1 ∧ IsMonHom φ.hom ∧ w.IsGen ∧ mu.IsGen ∧ rp.IsGen ∧
    (∀ i, x'.v i ≫ φ.hom = x.v (i.cast hg)) ∧
    (∀ (z : x'.P.A.left) (j : x.P.L.ι) (k : x'.P.L.ι), (φ.hom ≫ trl x.P.A p).left z ∈ x.P.L.U j → z ∈ x'.P.L.U k →
      gs (φ.hom ≫ trl x.P.A p).left z (x.P.L.U j) (x.th.f j) =
        (gw w (𝟙 _) z j k).val * gs (𝟙 _) z (x'.P.L.U k) (x'.th.f k)) ∧
    (∀ (q : (𝟙_ (Over (Sp ℂ))).left) J J', Good x.P.L q J → Good x'.P.L q J' →
      val rp (𝟙 _) q J = gw w (eSec x'.P.A) q (J (𝟙 _ ≫ p.left)) (J' (𝟙 _ ≫ eSec x'.P.A)) * val x'.rig (𝟙 _) q J') ∧
    (∀ (q : (𝟙_ (Over (Sp ℂ))).left) J, Good x.P.L q J → val mu (eSec x.P.A) q J = val x.rig (𝟙 _) q J ^ (-3 : ℤ)) ∧
    ∀ (q : (𝟙_ (Over (Sp ℂ))).left) J, Good x.P.L q J →
      val mu p.left q J = gm (𝟙 _) q ⊤ (show Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ from unitOn ν) * val x.rig (𝟙 _) q J * val rp (𝟙 _) q J ^ (-4 : ℤ)

variable {S : Type} [CommRing S]

end GlobalTheory.KeyEq
end
end
