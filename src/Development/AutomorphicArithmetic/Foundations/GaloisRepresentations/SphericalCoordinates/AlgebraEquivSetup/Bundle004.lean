module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.DatumToG
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

@[expose] public section

section

noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

def BarEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  ∃ bar : 𝓞 E ≃+* 𝓞 E, ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)

def QuadEx : Prop := ∀ d : ℕ, 0 < d → ∃ (tr nm : ℤ) (f : ℚ), tr ^ 2 - 4 * nm < 0 ∧ ((tr ^ 2 - 4 * nm : ℤ) : ℚ) = f ^ 2 * (-(d : ℚ)) ∧
  ∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm

def CEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (τ₀ : E →+* ℂ) (M : ℕ), 0 < M →
  ∃ c : 𝓞 E, IsCMField.complexConj E (c : E) = c ∧ (τ₀ (c : E)).re < 0 ∧
    (∀ τ : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ₀ → 0 < (τ (c : E)).re) ∧ ∃ b : 𝓞 E, c = 1 + (M : 𝓞 E) * b

def UnitMod : Prop := ∀ (E : Type) [Field E] [NumberField E] (M : ℕ) (c b : 𝓞 E), c ≠ 0 → c = 1 + (M : 𝓞 E) * b →
  ∃ e : ℕ, e.Coprime M ∧ ∃ c' : 𝓞 E, c * c' = (e : 𝓞 E)

def InCodiff {E : Type} [Field E] [NumberField E] (y : E) : Prop := ∀ x : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (y * x) = m

def GenCodiff {E : Type} [Field E] [NumberField E] (M : ℕ) (y : E) : Prop :=
  InCodiff y ∧ ∃ e : ℕ, e.Coprime M ∧ ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (e : E) * z = y * x

def CodiffGen : Prop := ∀ (E : Type) [Field E] [NumberField E] (M : ℕ), 0 < M → ∃ y : E, GenCodiff M y

def CodiffUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] (M : ℕ), 0 < M → ∀ (y t : E), GenCodiff M y → InCodiff t →
  (∀ P : Ideal (𝓞 E), P.IsMaximal → (M : 𝓞 E) ∈ P → ∃ s u : 𝓞 E, s ∉ P ∧ u ∉ P ∧ (s : E) * t = (u : E) * y) → GenCodiff M t

def IdemEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (bar : 𝓞 E ≃+* 𝓞 E) (ω : 𝓞 E) (tr nm : ℤ), (∀ x, bar (bar x) = x) →
  ω + bar ω = (tr : 𝓞 E) → ω * bar ω = (nm : 𝓞 E) → ∀ M : ℕ, 0 < M →
  (∀ q : ℕ, q.Prime → q ∣ M → ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm) →
  ∃ ε : 𝓞 E, ∀ P : Ideal (𝓞 E), P.IsMaximal → (M : 𝓞 E) ∈ P → ε + bar ε - 1 ∈ P ∧ ε * bar ε ∈ P

def RealGen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E),
  (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → ∀ M : ℕ, 0 < M → ∀ ε : 𝓞 E,
  (∀ P : Ideal (𝓞 E), P.IsMaximal → (M : 𝓞 E) ∈ P → ε + bar ε - 1 ∈ P ∧ ε * bar ε ∈ P) →
  ∃ t : E, IsCMField.complexConj E t = t ∧ GenCodiff M t

def PosGen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ), 0 < M → ∀ t : E,
  IsCMField.complexConj E t = t → GenCodiff M t →
  ∃ t' : E, IsCMField.complexConj E t' = t' ∧ GenCodiff M t' ∧ ∀ τ : E →+* ℂ, 0 < (τ t').re

def DeltaEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E),
  (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → ∀ (ω : 𝓞 E) (tr nm : ℤ),
  ω + bar ω = (tr : 𝓞 E) → ω * bar ω = (nm : 𝓞 E) → tr ^ 2 - 4 * nm < 0 → ∀ M : ℕ, IsCoprime (tr ^ 2 - 4 * nm) (M : ℤ) →
  ∀ t : E, IsCMField.complexConj E t = t → GenCodiff M t → (∀ τ : E →+* ℂ, 0 < (τ t).re) → ∀ τ₀ : E →+* ℂ,
  ∃ δ : E, IsCMField.complexConj E δ = -δ ∧ GenCodiff M δ ∧ ∀ τ : E →+* ℂ, τ (ω : E) = τ₀ (ω : E) → (τ δ).im < 0

def PerfOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (M : ℕ), GenCodiff M A.δ →
  (∃ e : ℕ, e.Coprime M ∧ ∃ c' : 𝓞 E, A.c * c' = (e : 𝓞 E)) → ∀ q : ℕ, q ∣ M → A.PerfAt q

def PerfCof : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E),
  ∃ e : ℕ, 0 < e ∧ ∀ q : ℕ, e.Coprime q → A.PerfAt q

def FormOKSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), A.FormOK n

def FormPerfSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n q : ℕ), A.PerfAt q → A.FormPerf n q

def SigSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), 1 ≤ n → A.SigOK n

abbrev Phi {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) : Type := {τ : E →+* ℂ // τ (A.ω : E) = A.τ₀ (A.ω : E)}

def RealIso : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ),
  ∃ Θ : ℝ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℝ] (Phi A × Fin n → ℂ), ∀ (x : Fin n → 𝓞 E) τ i, Θ (1 ⊗ₜ x) (τ, i) = τ.1 (x i : E)


open Classical in
def TraceType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E),
  (∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ : Phi A, 2 * (τ.1 x).re) ∧
  (∀ f : (E →+* ℂ) → ℂ, ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))), f τ =
    ∑ τ : Phi A, f (ComplexEmbedding.conjugate τ.1)) ∧
  (∀ v : InfinitePlace E, ∃! τ : Phi A, InfinitePlace.mk τ.1 = v) ∧ (A.τ₀ (A.ω : E)).im ≠ 0


open Classical in
def FormCoord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (Θ : ℝ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℝ] (Phi A × Fin n → ℂ)), (∀ (x : Fin n → 𝓞 E) τ i, Θ (1 ⊗ₜ x) (τ, i) = τ.1 (x i : E)) →
  ∀ x y, (A.EF n).baseChange ℝ x y =
    ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Θ x k * (starRingEnd ℂ) (Θ y k)).re

def HdSign : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (τ : E →+* ℂ) (i : Fin n),
  (τ (A.hd n i : E)).im = 0 ∧ (τ A.δ).re = 0 ∧
  (InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ ∧ (i : ℕ) = 0 → 0 < (τ (A.hd n i : E)).re) ∧
  (¬ (InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ ∧ (i : ℕ) = 0) → (τ (A.hd n i : E)).re < 0)

def DiagTrace : Prop := ∀ (I : Type) [Fintype I] (a : I → ℂ) (M : (I → ℂ) →ₗ[ℝ] (I → ℂ)), (∀ z k, M z k = a k * z k) →
  LinearMap.trace ℝ _ M = 2 * (∑ k, a k).re

def DomSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), 1 ≤ n → A.Dom n

def KqEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E),
  ∃ Kq : Subfield E, (A.ω : E) ∈ Kq ∧ (Module.finrank ℚ Kq = 2 ∧ ∀ τ : E →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0) ∧
    ∀ x ∈ Kq, ∃ a b : ℚ, x = a + b * (A.ω : E)

def UEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (p : ℕ) [Fact p.Prime], A.SplitK p →
  ∀ Kq : Subfield E, ∀ hω : (A.ω : E) ∈ Kq, (∀ x ∈ Kq, ∃ a b : ℚ, x = a + b * (A.ω : E)) → ∀ τ : E →+* PadicAlgCl p,
  ∃ (u : Kq →+* ℚ_[p]) (ρ : ℤ_[p]), LiesOver Kq u τ ∧ u ⟨A.ω, hω⟩ = (ρ : ℚ_[p])

def OrbEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (Kq : Subfield E) (u : Kq →+* ℚ_[p])
  (τ₁ : E →+* PadicAlgCl p), LiesOver Kq u τ₁ →
  ∃ (m : ℕ) (emb : Fin m → (E →+* PadicAlgCl p)) (w : Fin m), emb w = τ₁ ∧ (∀ i, LiesOver Kq u (emb i)) ∧
    (∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i) = emb j → i = j) ∧
    ∀ τ : E →+* PadicAlgCl p, LiesOver Kq u τ → ∃ i, ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      τ = ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i)

def LiftEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (τ₀ : E →+* ℂ),
  ∃ (s : E →+* AlgebraicClosure ℚ) (iotaC : AlgebraicClosure ℚ →+* ℂ), ∀ x, iotaC (s x) = τ₀ x

def AtPEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (p : ℕ) [Fact p.Prime], A.SplitK p →
  Nonempty (A.AtP p)

def RepEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ),
  ∃ (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E)), ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)

def RepOK {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) : Prop :=
  ∃ β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E), (∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)) ∧
    ∀ x z, β (rep x z) = x *ᵥ β z

def RepLaws : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))), RepOK A n rep →
  Function.Injective rep ∧
  (∀ M : Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)), (∃ x, rep x = M) ↔ ∀ b : 𝓞 E,
    M * (DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ =
      (DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ * M) ∧
  (∀ c : 𝓞 E, rep (algebraMap E _ (c : E)) = (DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) c).baseChange ℚ) ∧
  ∀ (x : Matrix (Fin n) (Fin n) (𝓞 E)) (v : Fin n → 𝓞 E),
    rep (x.map (algebraMap (𝓞 E) E)) ((1 : ℚ) ⊗ₜ[ℤ] v) = (1 : ℚ) ⊗ₜ[ℤ] (x *ᵥ v)

def RepAdj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))), RepOK A n rep →
  ∀ x v w, (A.EF n).baseChange ℚ (rep x v) w = (A.EF n).baseChange ℚ v (rep (hermStar (A.H n) (A.det_ne n) x).unop w)

def Orient : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (hn : 1 ≤ n) (hs : A.SigOK n)
  (p : ℕ) [Fact p.Prime] (P : A.AtP p)
  (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))), RepOK A n rep →
  ∃ J : ℝ ⊗[ℚ] (A.grp hn hs P).C, J * J = -1 ∧ (starT (A.grp hn hs P).star ℝ J).unop = -J ∧
    (∀ x, x ≠ 0 → 0 < ((A.EF n).baseChange ℚ).baseChange ℝ (actOn (C := (A.grp hn hs P).C) rep ℝ J x) x) ∧
    ∀ v : InfinitePlace E, (open scoped Classical ComplexOrder in
      ((if v.embedding (A.ω : E) = A.τ₀ (A.ω : E) then -Complex.I else Complex.I) •
        ((A.grp hn hs P).gram v * (A.grp hn hs P).psiR v J)).PosDef)

def SetupEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime], 1 ≤ n →
  A.Good p → Nonempty (Setup A n p)

def SetupBasic : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime]
  (S : Setup A n p), S.G.a = 1 ∧ sigPosH (S.G.gram_herm (InfinitePlace.mk A.τ₀)) = 1 ∧
    (2 < Module.finrank ℚ E → S.D.Compact ∧ S.D.CompactB)

end UpperTheory.Gal.W2.Seed
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

def OHat (p : ℕ) (E : Type) [Field E] [NumberField E] : AddSubgroup (AfP p ⊗[ℚ] E) :=
  AddSubgroup.closure {z | ∃ (a : AfP p) (x : 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ (x : E)}

structure AdQ (p : ℕ) where
  ρ : AfQ →+* AfP p
  surj : Function.Surjective ρ
  ker : ∀ a, ρ a = 0 ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → a v = 0
  int : ∀ a, IsIntAf (ρ a) ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (a v) ≤ 1

structure AdT (p : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] extends AdQ p where
  Φ : Af E →+* AfP p ⊗[ℚ] E
  Φ_E : ∀ x : E, Φ (algebraMap E (Af E) x) = 1 ⊗ₜ x
  Φ_Q : ∀ a : AfQ, Φ (finiteAdeleMap ℚ E a) = ρ a ⊗ₜ 1
  Φ_surj : Function.Surjective Φ
  Φ_ker : ∀ x, Φ x = 0 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0
  Φ_int : ∀ x, Φ x ∈ OHat p E ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → Valued.v (pLoc E w x) ≤ 1
  Φ_conj : ∀ x, Φ (conjFin (conjE E) x) = conjT E (AfP p) (Φ x)

def AdQEx : Prop := ∀ (p : ℕ) [Fact p.Prime], Nonempty (AdQ p)

def AdTensor : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ ι : AfQ ⊗[ℚ] E ≃+* Af E,
  (∀ (a : AfQ) (x : E), ι (a ⊗ₜ x) = finiteAdeleMap ℚ E a * algebraMap E (Af E) x) ∧
  (∀ y, y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E), (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)} ↔
    ∀ w : Plc E, Valued.v (pLoc E w (ι y)) ≤ 1) ∧
  ∀ a : AfQ, conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a

def IdemP : Prop := ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E], ∃ e : AfQ,
  (∀ v : Plc ℚ, ((p : 𝓞 ℚ) ∈ v.asIdeal → e v = 1) ∧ ((p : 𝓞 ℚ) ∉ v.asIdeal → e v = 0)) ∧
  ∀ w : Plc E, ((p : 𝓞 E) ∈ w.asIdeal → pLoc E w (finiteAdeleMap ℚ E e) = 1) ∧
    ((p : 𝓞 E) ∉ w.asIdeal → pLoc E w (finiteAdeleMap ℚ E e) = 0)

def AdTEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [IsCMField E], Nonempty (AdT p E)

def IsMu {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) : Prop :=
  ∀ (r : R) (x : Matrix (Fin n) (Fin n) E) i k, μ (r ⊗ₜ x) i k = r ⊗ₜ x i k

def MuEx : Prop := ∀ (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] (n : ℕ),
  ∃ μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E), IsMu μ

def MuStar : Prop := ∀ (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)), IsMu μ → ∀ x,
  Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * μ (starT (hermStar (A.H n) (A.det_ne n)) R x).unop =
    ((μ x).map (conjT E R))ᵀ * Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E))

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsIso (A : Arith E) (n : ℕ) (a : GL (Fin n) (Af E)) : Prop :=
  (a.val.map (conjFin (conjE E)))ᵀ * Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E)) * a.val = 1 ∧
    ∀ (w : Plc E) (q : ℕ), q.Prime → A.Good q → (q : 𝓞 E) ∈ w.asIdeal → GeneralLinearGroup.map (pLoc E w) a ∈ KGL w (n := n)

def Arith.β₀ (A : Arith E) (n : ℕ) : (Matrix (Fin n) (Fin n) E)ˣ :=
  GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i => (A.dg n i : E)) (by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    have := A.c_ne
    unfold Arith.dg; split_ifs <;> simp [this])

variable {A : Arith E} {n p : ℕ} [Fact p.Prime]

def Setup.mx (S : Setup A n p) (h : S.G.GAf) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E :=
  ((h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] S.G.C)

structure Tr (S : Setup A n p) extends AdT p E where
  μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)
  mu : IsMu μ
  a : GL (Fin n) (Af E)
  iso : IsIso A n a
  j : GUf E n →* S.G.GAf
  j_mx : ∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map Φ
  j_sim : ∀ g, ((uSimR (AfP p) (j g) : (AfP p)ˣ) : AfP p) = ρ (sim g : AfQˣ)
  sec : S.G.GAf →* GUf E n
  j_sec : ∀ h, j (sec h) = h
  sec_p : ∀ h (w : Plc E), (p : 𝓞 E) ∈ w.asIdeal → comp w (sec h) = 1
  j_eq : ∀ g g', j g = j g' ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g'

def JEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ a : GL (Fin n) (Af E), IsIso A n a → ∃ j : GUf E n →* S.G.GAf,
    (∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map T.Φ) ∧
    ∀ g, ((uSimR (AfP p) (j g) : (AfP p)ˣ) : AfP p) = T.ρ (sim g : AfQˣ)

def JEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ (a : GL (Fin n) (Af E)) (j : GUf E n →* S.G.GAf), (∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map T.Φ) →
  (∀ g g' : GUf E n, (∀ w, comp w g = comp w g') → g = g') ∧
  ∀ g g', j g = j g' ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g'

def JSurj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ a : GL (Fin n) (Af E), IsIso A n a → ∀ h : S.G.GAf, ∃ g : GUf E n,
    μ (S.mx h) = (a * mat g * a⁻¹).val.map T.Φ ∧ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g = 1

def IsoEx' : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), Odd n → ∃ a, IsIso A n a

def TrEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p),
  Odd n → Nonempty (Tr S)

def LocComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Plc E) (hw : IsSplitAt w)
  (x : GL (Fin n) (w.adicCompletion E)) (g : GUf E n), comp w g = 1 → CertificateRingHomMap.loc hw x * g = g * CertificateRingHomMap.loc hw x

theorem apart_of_not_mem {w u : Plc E} (hw : (p : 𝓞 E) ∉ w.asIdeal) (hu : (p : 𝓞 E) ∈ u.asIdeal) : GlobalTheory.Cong.Apart u w := by
  intro h
  apply hw
  have h1 : (p : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
    simpa using hu
  rw [h] at h1
  have h2 : algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal := h1
  simpa using h2

def Tr.at {S : Setup A n p} (T : Tr S) (hc : LocComm) (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal) :
    Loc S.G.GAf (GL (Fin n) (w.adicCompletion E)) where
  pr := (comp w).comp T.sec
  loc := T.j.comp (CertificateRingHomMap.loc hw)
  pr_loc x := by
    have := (T.j_eq (T.sec (T.j (CertificateRingHomMap.loc hw x))) (CertificateRingHomMap.loc hw x)).1 (T.j_sec _) w hp
    simpa using this
  comm x g h := by
    have := congrArg T.j (hc E n w hw x (T.sec g) h)
    simpa [T.j_sec] using this

def LatCoord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∃ ν : AfP p ⊗[ℚ] VQ S.D ≃+ (Fin n → AfP p ⊗[ℚ] E),
    (∀ (r : AfP p) (v : Fin n → 𝓞 E) i, ν (r ⊗ₜ ((1 : ℚ) ⊗ₜ[ℤ] v)) i = r ⊗ₜ (v i : E)) ∧
    (∀ h v, ν (S.L.actG h v) = μ (S.mx h) *ᵥ ν v) ∧ ∀ v, v ∈ LaHat S.D ↔ ∀ i, ν v i ∈ OHat p E

def Cong1 (N : ℕ) (w : Plc E) (x : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∀ i k, Valued.v ((x.val - 1) i k) ≤ Valued.v (N : w.adicCompletion E)

def KNIff : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (g : GUf E n),
  ((∀ v ∈ LaHat S.D, S.L.actG (T.j g) v ∈ LaHat S.D) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k,
    Valued.v ((GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val i k) ≤ 1) ∧
  ∀ N : ℕ, 0 < N → (S.L.CongOne N (T.j g) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
    Cong1 N w (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)))

def StdForm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ (B : DForm S.G) (x : (AfP p ⊗[ℚ] S.G.C)ˣ) (hx : Triv S.G (AfP p) B.β x 1) (e : GlobalTheory.LKCx.grp S.G B.β →* Gam0 E n),
    (∀ y, ((e y : Gam0 E n) : GL (Fin n) E × ℚˣ) = (y : S.G.Cˣ × ℚˣ)) ∧ ∀ y, GlobalTheory.LKCx.toAfF S.G B.β x 1 hx y = T.j (rat (e y))

def PInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (y : Gam0 E n), inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G →
  (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ KGL w (n := n)) ∧
    ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∈ v.asIdeal → Valued.v (((sim (rat y) : AfQˣ) : AfQ) v) = 1

end UpperTheory.Gal.W2.Seed
end
end
