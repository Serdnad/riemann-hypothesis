module

public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.ComplSmulMapE
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def OneAt (P : HeightOneSpectrum (𝓞 E)) (a : E) : Prop := P.valuation E (a - 1) < 1

structure LocSys {A : Type} [CommGroup A] (lam : HeightOneSpectrum (𝓞 F) → Eˣ →* A) (Rm : Set (HeightOneSpectrum (𝓞 F))) : Prop where

  wild : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ),
    (∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → OneAt P (a : E)) → lam v a = 1

  trivF : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ), lam v (Units.map (algebraMap F E).toMonoidHom k) = 1

  unr : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Rm → ∀ a : Eˣ,
    (∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → P.valuation E (a : E) = 1) → lam v a = 1

def lamH (χ : Formalism.L2.Host.HChar E) (v : HeightOneSpectrum (𝓞 F)) : Eˣ →* ℂˣ :=
  ∏ P ∈ Formalism.L2.Host.aboveF (L := E) F v, χ.locK P

theorem local_idempotent_mul (v : HeightOneSpectrum (𝓞 F)) (a b : E) :
    (a ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)) * (b ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)) =
      ((a * b) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1) : AfE F E) := by
  have h1 : Formalism.L2.G.sgl F v 1 * Formalism.L2.G.sgl F v 1 = Formalism.L2.G.sgl F v 1 := by rw [← Formalism.L2.G.sgl_mul, one_mul]
  have h2 : Formalism.L2.G.sgl F v 1 * (1 - Formalism.L2.G.sgl F v 1) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
  have h3 : (1 - Formalism.L2.G.sgl F v 1) * Formalism.L2.G.sgl F v 1 = 0 := by rw [_root_.sub_mul, one_mul, h1, sub_self]
  have h4 : (1 - Formalism.L2.G.sgl F v 1) * (1 - Formalism.L2.G.sgl F v 1) = 1 - Formalism.L2.G.sgl F v 1 := by rw [mul_sub, mul_one, h3, sub_zero]
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, h1, h2, h3, h4, TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero, zero_add, one_mul]

theorem locId_one (v : HeightOneSpectrum (𝓞 F)) :
    ((1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1) : AfE F E) = 1 := by
  rw [← TensorProduct.tmul_add, add_sub_cancel]
  rfl


variable (E) in
def locId (v : HeightOneSpectrum (𝓞 F)) : Eˣ →* (AfE F E)ˣ where
  toFun a :=
    { val := (a : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)
      inv := ((a⁻¹ : Eˣ) : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)
      val_inv := by rw [local_idempotent_mul, Units.mul_inv, locId_one]
      inv_val := by rw [local_idempotent_mul, Units.inv_mul, locId_one] }
  map_one' := Units.ext (by show ((1 : Eˣ) : E) ⊗ₜ[F] _ + _ = 1; rw [Units.val_one, locId_one])
  map_mul' a b := Units.ext (by
    show ((a * b : Eˣ) : E) ⊗ₜ[F] _ + _ = (_ + _) * (_ + _)
    rw [local_idempotent_mul, Units.val_mul])

def lamX {L : Type} [Field L] (ξ : Chr F E L) (v : HeightOneSpectrum (𝓞 F)) : Eˣ →* Lˣ := ξ.comp (locId E v)

end Loc

section G

variable {X : Fields} (Pr : Primes X)

def XiOffG (ξ : Chr X.F X.E X.K) : Prop :=
  ∀ P ∈ Pr.vGs, ∀ v : HeightOneSpectrum (𝓞 X.F), P.asIdeal.under (𝓞 X.F) = v.asIdeal → v ∉ Qprime ξ

end G

section Stmts

def OverTwo : Prop :=
  ∀ X : Fields, X.Ok → ∀ P P' : HeightOneSpectrum (𝓞 X.E), P'.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F) → P' = P ∨ P' = conjPrime₂ P

def ApproxP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P Q : HeightOneSpectrum (𝓞 E)), P ≠ Q → ∀ t : 𝓞 E,
    ∃ b : 𝓞 E, b ≠ 0 ∧ b - t ∈ P.asIdeal ^ 2 ∧ b - 1 ∈ Q.asIdeal

def AbsSplit : Prop :=
  ∀ X : Fields, X.Ok → ∀ (A : Type) [CommGroup A] (lam : HeightOneSpectrum (𝓞 X.F) → X.Eˣ →* A) (Rm : Set (HeightOneSpectrum (𝓞 X.F))), LocSys lam Rm →
    ∀ (v : HeightOneSpectrum (𝓞 X.F)) (P : HeightOneSpectrum (𝓞 X.E)), P.asIdeal.under (𝓞 X.F) = v.asIdeal → conjPrime₂ P ≠ P →
    ∀ x b : X.Eˣ, OneAt (conjPrime₂ P) (b : X.E) → OneAt P ((b : X.E) / ((x : X.E) / star (x : X.E))) → lam v x = lam v b

def AbsInert : Prop :=
  ∀ X : Fields, X.Ok → ∀ (A : Type) [CommGroup A] (lam : HeightOneSpectrum (𝓞 X.F) → X.Eˣ →* A) (Rm : Set (HeightOneSpectrum (𝓞 X.F))), LocSys lam Rm →
    ∀ (v : HeightOneSpectrum (𝓞 X.F)) (P : HeightOneSpectrum (𝓞 X.E)), P.asIdeal.under (𝓞 X.F) = v.asIdeal → conjPrime₂ P = P → v ∉ Rm →
    ¬ (P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))).map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ P.asIdeal ^ 2 →
    ∀ x : X.Eˣ, lam v x = 1

def XiSys : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (S : Set ℕ) (ξ : Tup F E L S),
    LocSys (lamX (ξ : Chr F E L)) (Qprime (ξ : Chr F E L))

def XiProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (S : Set ℕ) (ξ : Tup F E L S) (x : Eˣ),
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => lamX (ξ : Chr F E L) v x).Finite ∧ ∏ᶠ v : HeightOneSpectrum (𝓞 F), lamX (ξ : Chr F E L) v x = 1

def XiUnif : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (S : Set ℕ) (ξ : Tup F E L S)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) = v.asIdeal → v ∉ Qprime (ξ : Chr F E L) →
    ∀ (w : Eˣ) (b : 𝓞 E), (w : E) = (b : E) → b ∈ P.asIdeal → b ∉ P.asIdeal ^ 2 →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal → b - 1 ∈ P'.asIdeal) →
      lamX (ξ : Chr F E L) v w = unifVal (ξ : Chr F E L) P

def XiQ : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (S : Set ℕ) (ξ : Tup F E L S)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) = v.asIdeal →
    ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (w : Eˣ) (b : 𝓞 E), (w : E) = (b : E) → b - ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal ^ 2 →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal → b - 1 ∈ P'.asIdeal) →
      lamX (ξ : Chr F E L) v w = qVal (ξ : Chr F E L) P

def XiRes : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L] (S : Set ℕ) (ξ : Tup F E L S)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) = v.asIdeal →
    ∀ (w : Eˣ) (b : 𝓞 E) (r : (𝓞 E ⧸ P.asIdeal)ˣ), (w : E) = (b : E) → Ideal.Quotient.mk P.asIdeal b = (r : 𝓞 E ⧸ P.asIdeal) →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal → b - 1 ∈ P'.asIdeal) →
      lamX (ξ : Chr F E L) v w = resChar (ξ : Chr F E L) P r

def HSys : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (Rm : Set (HeightOneSpectrum (𝓞 F))),
    (∀ P, χ.TameAt P) → χ.TrivOn F →
    (∀ v : HeightOneSpectrum (𝓞 F), v ∉ Rm → ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → χ.UnrAt P) →
    LocSys (lamH (F := F) χ) Rm

def HProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ P, P ∉ S → χ.UnrAt P) → ∀ x : Eˣ,
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => lamH (F := F) χ v x).Finite ∧ ∏ᶠ v : HeightOneSpectrum (𝓞 F), lamH (F := F) χ v x = (χ.inf x)⁻¹

def HEval : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Formalism.L2.Host.HChar E), (∀ P, χ.TameAt P) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) = v.asIdeal → ∀ b : Eˣ,
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal → OneAt P' (b : E)) → lamH (F := F) χ v b = χ.locK P b

def HLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (P : HeightOneSpectrum (𝓞 E)),
    (χ.TameAt P → ∀ a : Eˣ, OneAt P (a : E) → χ.locK P a = 1) ∧
    (χ.UnrAt P → ∀ a : Eˣ, P.valuation E (a : E) = 1 → χ.locK P a = 1) ∧
    (χ.UnrAt P → ∀ a : Eˣ, P.valuation E (a : E) = WithZero.exp (-1 : ℤ) → χ.locK P a = χ.val P)

def HInf : Prop :=
  ∀ X : Fields, X.Ok → ∀ (σ₀ : X.K →+* ℂ) (χ : Formalism.L2.Host.HChar X.E) (n e : X.Tau → ℤ), χ.HasInf (X.embC σ₀) n → (∀ τ, n τ = 2 * -(e τ)) →
    ∀ x : X.Eˣ, ((χ.inf x : ℂˣ) : ℂ) = ∏ τ, σ₀ (X.emb τ ((x : X.E) / star (x : X.E))) ^ (-(e τ))

end Stmts

end Formalism.L2.Ker
end
end

section

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

def Amb.AnaStep {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) : Prop :=
  A.LaHyp a b Sall ∧ A.ESmooth a b ∧ A.JetsRat a b Sall D

section Inst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

def ThHyp : Prop :=
  (∀ i, i ≤ m2 → A.AnaStep (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)) ∧
  A.AnaStep (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) ∧
  (∀ i, i ≤ m2 → ThEquivP ((chThT W Ch sel mu cst A u m2).th i) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho) ∧
  ThEquivP (chThT W Ch sel mu cst A u m2).top (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u (m2 + 1)).rho (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho

end Inst

section Nat

open Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

def NatOk (σ₀ : X.K →+* ℂ) : Prop :=
  TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ δ ≠ 0 ∧ TaylorLogMetric.IsChi D χ ∧ IsDgen D cD ∧ s.Ok ∧ s.σ₀ = σ₀

end Nat

section InstN

open Formalism.MainNotions

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (G : ChGlob X R.m)

def LawTies : Prop :=
  MuqTie Ch sel mu cst ∧ MuqTieG sel mu cst G.σ₀ G.mu0 ∧ (∃ eta : Formalism.L2.Host.HChar X.E, Ch.Tied G.σ₀ (fun j τ => (W.row τ).e j) G.mu0 eta) ∧
    ∀ u τ, RowPar.of (W.hc u τ) = W.row τ

variable {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (u : Pr.Word) (m2 : ℕ)

def ThHypN : Prop :=
  NatOk s cc δ χ cD G.σ₀ ∧ LawTies W Ch sel mu cst G ∧ ThHyp W Ch sel mu cst (ambOf s B χ cD) u m2

end InstN

section Tab

variable {X : Fields} (A : Amb X) {a b : ℕ}

def Amb.tabK (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Ξ : HomE X.E a b → X.K) (m : DVar X.Tau a b →₀ ℕ) : X.K :=
  latSum (divLat cA (homAt Sall N N')) (mulLat cB (homAt Sall N N')) fun x => Ξ x * A.jetK Sall N N' cB x m

def Amb.thDat (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (Ξ : HomE X.E a b → X.K) : VCx X.Tau a b → ℂ := fun z =>
  latSum (divLat cA (homAt Sall N N')) (mulLat cB (homAt Sall N N')) fun x => A.σ₀ (Ξ x) * A.thInd Sall N N' cB x z

end Tab

section Ne

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

def scalK (i : ℕ) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a (rowSG Pr sel mu)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (fr' : Frs X.E b (rowSG Pr sel mu)) : X.K :=
  muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) N fr *
    (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) N' fr')⁻¹

end Ne

end Formalism.L2.Ker
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Abs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable {S : GSD K}

end Abs

section Pts

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

end Pts

section PtsFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}


omit [NumberField E] in
theorem decoF_ext {p p' : DecoF E n ST SG Q} (h1 : p.deco = p'.deco) (h2 : ∀ R : Q, p.fr R = p'.fr R) : p = p' :=
  Subtype.ext (Prod.ext h1 (funext h2))

end PtsFin

section PtsG

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

end PtsG

section ChN

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

end ChN

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

variable {K : Type} [Field K] {SB : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end Local

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

section Ops

variable (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

end Ops

variable {u : Pr.Word}


variable (R u) in
abbrev TopPt : Type := RowPt Pr R sel mu × DecoSet (E := X.E) (n := R.N R.m) (ST := Pr.vT u) (SG := rowSG Pr sel mu)

def tilTop (d : RowPt Pr R sel mu) : TopPt R sel mu u := (d, tilQ sel mu u d)



end Chain

section Stmts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (hM : MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2)) (h1 : Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY)
  (hF : ∀ j, (chF W sel mu L u j).Ok)


end Stmts

section Move

variable {X : Fields} (A : Amb X) {a b : ℕ}

end Move

section MoveCh

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end MoveCh

section MoveC

variable {X : Fields} (A : Amb X) {a b : ℕ}

end MoveC

section MoveCCh

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end MoveCCh

section OrdDet

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def OrdDetFin : Prop :=
  ∀ N : Submodule (𝓞 E) (Sp E n), IsSdLat N → {Q : HeightOneSpectrum (𝓞 E) | ordDet Q N ≠ 0}.Finite

end OrdDet

section OrdDetCh

variable {X : Fields} {Pr : Primes X} (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end OrdDetCh

section Dia

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

end Dia

section DiaCh

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (hM : MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2)) (h1 : Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY)
  (hF : ∀ j, (chF W sel mu L u j).Ok)

end DiaCh

end Formalism.L2.Ker
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

def Amb.EOmega {X : Fields} (A : Amb X) (a b : ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' → ContDiff ℂ ⊤ (A.e a b N N')

def Amb.IndOmega {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    ContDiff ℂ ⊤ (A.thInd Sall N N' c x)

def WtLaw {ι : Type} {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (e : ι → ℤ) : Prop :=
  (∀ τ, (n τ : ℤ) + ((b / 2 : ℕ) : ℤ) - e τ = (lam τ).detShift) ∧ ∀ τ, e τ - ((a / 2 : ℕ) : ℤ) = -(lam' τ).detShift

def Amb.EqLaw {X : Fields} (A : Amb X) (a b : ℕ) : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ z, A.e a b (gmap γ.1 N) (gmap γ'.1 N') z = A.e a b N N' (A.pullV a b γ.1 γ'.1 z)

def ThIndOfEq : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ),
    (∀ τ x, X.embC A.σ₀ τ (star x) = star (X.embC A.σ₀ τ x)) → 0 < D → A.LaHyp a b Sall → A.EqLaw a b → A.ThIndEq a b Sall D

end Formalism.L2.Ker
end
end
