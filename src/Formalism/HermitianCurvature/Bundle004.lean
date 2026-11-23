module

public import Formalism.HermitianCurvature.StatementLE
public import Formalism.HermitianCurvature.StatementQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.FourierDecayAlt.C7

open Finset Matrix

open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

def LamInterlaces (k r : ℕ) (u : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ i : Fin (k + 2 * r + 1),
    (i.val + 1 ≤ k → lam i < u (i.val + 1)) ∧ (i.val + 2 ≤ k → u (i.val + 2) < lam i)

def Between (u u' : ℕ → ℝ) (l : ℕ) (Y : ℝ) : Prop :=
  min (u l) (u' l) < -Y ∧ -Y < max (u l) (u' l)

def LamSide : Prop :=
  ∀ (k r : ℕ) (u u' : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k →
    LamInterlaces k r u lam → LamInterlaces k r u' lam → Between u u' l Y →
    ∀ i : Fin (k + 2 * r + 1), (l ≤ i.val + 1 → lam i < min (u l) (u' l)) ∧
      (i.val + 1 < l → max (u l) (u' l) < lam i)

def RhoSide : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k → I.Interlaces k u u' ρ → Between u u' l Y →
    ∀ i ∈ Icc 1 (k - 1), (l ≤ i → ρ i < -Y) ∧ (i < l → -Y < ρ i)

def PSign : Prop :=
  ∀ (k r : ℕ) (u u' ρ : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k →
    LamInterlaces k r u lam → LamInterlaces k r u' lam → I.Interlaces k u u' ρ → Between u u' l Y →
    0 < (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s) ∧ 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ Y ∧
      |∏ s, (Y + lam s)| = (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s)

def principalHermitianLattice {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  B.beta D (w.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F) F

def RootsOutJoint : Prop :=
  ∀ (S : LE.Sys) (u u' : ℕ → ℝ) (l : ℕ), 1 ≤ l → l ≤ S.k →
    LamInterlaces S.k S.r u S.lam → LamInterlaces S.k S.r u' S.lam →
    (∀ Y ∈ Set.Icc S.α S.β, Between u u' l Y) → S.RootsOut

end

end Formalism.FourierDecayAlt.C7
end

section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.JF

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Om (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) := B.GV k r ∩ Q.OmPlus k r z z'

def QDom (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set ((Fin r → ℂ) × ℂ) :=
  {q | (∀ a, q.1 a ≠ 0) ∧ Tz k r z * Tz k r z' < Complex.normSq q.2}

def xiP {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) : ℂ :=
  psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2))

def integrand {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) (p : B.SS k r) : Wq →L[ℂ] Wp :=
  xiP D p • B.rho D p F g

def sL {k r : ℕ} (p : B.SS k r) : B.Mat k r := Matrix.of p.1.2 * Matrix.of p.1.1

def sR {k r : ℕ} (p : B.SS k r) : B.Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1

def AdL {k r : ℕ} (p : B.SS k r) (X : B.Mat k r) : B.Mat k r := (sL p)⁻¹ * X * sL p

def AdR {k r : ℕ} (p : B.SS k r) (X : B.Mat k r) : B.Mat k r := (sR p)⁻¹ * X * sR p

def castW {k : ℕ} (μ : B.Mat k 0) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.reindex (finCongr (by omega)) (finCongr (by omega)) μ

def sliceR {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) (μ : B.Mat k 0) : Wq →L[ℂ] Wp :=
  ∫ nn : Mt k r × Mt k r, (psi k r D.z cStd (Matrix.of nn.1) * star (psi k r D.z' cStd (Matrix.of nn.2))) •
    F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ∂(D.μN.prod D.μN)

def TransportedAlt (k r : ℕ) (A : ℝ) (m : ℕ) : Prop :=
  ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < (A - 6 * (r : ℝ) * (m : ℝ)) / (9 * ((r : ℝ) + 1))

def JConv : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A 0 → B.InCC A 0 F →
    (∀ g ∈ Om k r D.z D.z', Integrable (integrand D F g) D.μSS) ∧
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧ ∀ g ∈ K, ∀ᵐ p ∂D.μSS, ‖B.rho D p F g‖ ≤ b p

def JDom : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    (∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS) ∧
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p

def JWords : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    Q.CkLev k r 0 m (Q.OmPlus k r D.z D.z') (B.JF D F) ∧
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        Integrable (fun p => xiP D p • B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS ∧
        B.dLR u v (B.JF D F) g =
          ∫ p, xiP D p • B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g ∂D.μSS

def JWordsOfDom : Prop := JDom → JWords

def RwRho : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (m : ℕ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (p : B.SS k r),
    D.inSS p → B.CkOn (m : ℕ∞) (B.GV k r) f →
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.inLie k r X) → (∀ X ∈ v, B.inLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ B.GV k r, B.dLR u v (B.rho D p f) g = B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) f) g

def CVLeft : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) (f : B.Mat k r → E),
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) f →
    ∀ y ∈ B.GV k r, ∀ g ∈ B.GV k r, Q.CV k r Y (fun x => f (y * x)) g = Q.CV k r Y f (y * g)

def CVRight : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) (f : B.Mat k r → E),
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) f →
    ∀ y ∈ B.GV k r, ∀ g ∈ B.GV k r, Q.CV k r Y (fun x => f (x * y)) g = Q.CV k r Y f (g * y)

def CVPost : Prop :=
  ∀ (k r : ℕ) (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (Y : ℂ) (Φ : E →L[ℂ] E') (f : B.Mat k r → E),
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) f →
    ∀ g ∈ B.GV k r, Q.CV k r Y (fun x => Φ (f x)) g = Φ (Q.CV k r Y f g)

def CVRho : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (p : B.SS k r),
    D.inSS p → B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) f →
    ∀ g ∈ B.GV k r, Q.CV k r Y (B.rho D p f) g = B.rho D p (Q.CV k r Y f) g

def CVRhoOfParts : Prop := CVLeft → CVRight → CVPost → CVRho

def CVWordSum : Prop :=
  ∀ (k r : ℕ) (Y : ℂ), ∃ L : List (ℂ × List (B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ 2 * r + k + 1) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
      B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
        Q.CV k r Y f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum

def CVUnderInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (Y : ℂ),
    2 * r + k + 1 ≤ m → TransportedAlt k r A m → B.InCC A m F →
    ∀ g ∈ Om k r D.z D.z', Q.CV k r Y (B.JF D F) g = ∫ p, xiP D p • Q.CV k r Y (B.rho D p F) g ∂D.μSS

def CVUnderIntOfParts : Prop := JWords → CVWordSum → RwRho → CVUnderInt

def GqDom : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∀ q ∈ QDom k r D.z D.z', B.gq D q ∈ Om k r D.z D.z'

def GqOm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∀ᵐ q ∂(volume.restrict (B.Qset D)), B.gq D q ∈ Om k r D.z D.z'

def PsiOnto : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∀ g ∈ Om k r D.z D.z',
      ∃ p, D.inSS p ∧ ∃ q ∈ QDom k r D.z D.z', g = B.sgs p (B.gq D q)

def JqSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ContDiffOn ℝ (m : WithTop ℕ∞) (fun q => B.JF D F (B.gq D q)) (QDom k r D.z D.z')

def JqSmoothOfParts : Prop := JWords → GqDom → JqSmooth

end Formalism.FourierDecayAlt.JF
end
end
