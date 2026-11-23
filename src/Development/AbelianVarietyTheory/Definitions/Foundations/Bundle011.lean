module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.GroupTheory.Nilpotent
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
public import Formalism.LocalRingCardinality.Bundle003
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

section

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.LambdaValuationPowers

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def AdmissibleHodgeTateZetaClassParams {l : ℕ} [Fact l.Prime] (e : ℕ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
    (α : Qbar l) : Prop :=
  5 ≤ N ∧ Nat.Coprime l N ∧
    (∀ r₀ : (ZMod l)ˣ, gm r₀ ∈ CongruenceSubgroup.Gamma1 N ∧
      (((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod l) = -(r₀ : ZMod l) * (((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod l)) ∧
    ‖α‖ = 1 ∧ ∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = α • pr b

end GlobalTheory.LambdaValuationPowers
end
end

section

noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ ReciprocityTheory.Gal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def liftK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (a : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))) : X.Khat l :=
  Classical.epsilon fun b : X.Khat l => AdicCompletion.eval (idl l) (X.Kl l) n b = a


open Classical in
def clsK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (w : X.K) : X.Khat l :=
  if h : w ≠ 0 then liftK X l n (X.cls l n (Units.mk0 w h)) else 0

def liftSL (M : ℕ) (g : SL(2, ZMod M)) : SL(2, ℤ) :=
  Classical.epsilon fun γ : SL(2, ℤ) => Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = g


def repC (l : ℕ) [Fact l.Prime] (r : ℕ) (x : (ZMod (l ^ r))ˣ) : Ω ≃ₐ[ℚ] Ω :=
  Classical.epsilon fun s : Ω ≃ₐ[ℚ] Ω => cycMod (F := ℚ) (Ω := Ω) l r s = x

def chik4 (l : ℕ) [Fact l.Prime] (e : ℕ) (ψ : ZMod l → Qbar l) (r : ℕ) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  ((((y : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * ψ (((y : ZMod (l ^ r)).val : ℕ) : ZMod l)

end GlobalTheory.K4
end
end

section

noncomputable section
section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)

def eExp (D : D7) (j : Fin D.R.m) (g : D.R.Psi) : ℚ := (D.hc (D.eTau.symm g)).e j

structure CharFrame (D : D7) where

  P : PiBar D.host

  W : Omg D.host

  mu0 : Fin D.R.m → HChar D.host.E
  eta : HChar D.host.E
  chiPsi : HChar D.host.E
  del : HChar D.host.E
  del' : HChar D.host.E
  isMu0 : ∀ j, IsMu0 P W (eExp D j) j.1 (mu0 j)
  isEta : IsEtaT D.host eta
  isChi : IsChiPsi D.host chiPsi
  isDel : IsDelta D.host.pde del
  isDel' : IsDelta D.host.pde' del'

def CharFrame.delAt {D : D7} (C : CharFrame D) (l : ℕ) : HChar D.host.E := if l = D.host.pde then C.del' else C.del

structure TupTied (D : D7) (C : CharFrame D) (nch : NChoice D) where

  xi : D.what₂.Tup → HChar D.host.E
  xi_inj : Function.Injective xi
  xi_fin : ∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n
  xi_triv : ∀ μ, (xi μ).TrivOn D.host.F
  xi_tame : ∀ μ v, (xi μ).TameAt v

  psi : D.what₂.places.Pl → HChar D.host.E

  trueColumnChoices_heckeChar_reference_eq_one : xi D.what₂.mu0 = 1

  xi_star : xi D.what₂.muStar = C.del
  xi_star' : xi D.what₂.muStar' = C.del'

  xi_tw : ∀ w, xi (D.what₂.muTw w) = C.delAt (D.what₂.places.resChar w) * psi w

  psi_is : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → IsPsi (D.what₂.places.resChar w) (nch.Q w) (psi w)

  psi_un : ∀ w, D.what₂.muAt w = D.what₂.mu0 → psi w = 1

def IsFinIdele {L : Type} [Field L] [NumberField L] (a : Ideles L) : Prop :=
  ∀ w : InfinitePlace L, (a : AdeleRing (𝓞 L) L).1 w = 1

structure DtTied (D : D7) (C : CharFrame D) where
  eDt : Ideles D.host.E →* D.Dt
  surj : Function.Surjective eDt

  ker_open : IsOpen ((eDt.ker : Subgroup (Ideles D.host.E)) : Set (Ideles D.host.E))
  inf : ∀ w y, eDt (infIdele D.host.E w y) = 1

  onF : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (k : D.host.Fˣ),
    eDt (∏ Q ∈ aboveF (L := D.host.E) D.host.F v, localIdele D.host.E Q (atFin Q (upF D.host.F k))) = 1

  ker_le : ∀ a, eDt a = 1 → ∀ w w', IsConjPl D.host w w' →
    Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 w) = Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 w')

  rat : letI := D.host.cmStar; ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
    eDt (diagUnits D.host.E k) = D.e1Dt z

  UO_eq : ∀ x, x ∈ D.UO ↔ ∃ a : Ideles D.host.E,
    (∀ v, Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 v) = 1) ∧ eDt a = x

  muTil_eq : ∀ (j : Fin D.R.m) (a : Ideles D.host.E), IsFinIdele a → D.muTil (j.1 + 1) (eDt a) = (C.mu0 j).1 a

  chiD_eq : ∀ a : Ideles D.host.E, IsFinIdele a → D.chiD (eDt a) = C.chiPsi.1 a

def IsCSD {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) : Prop :=
  (∀ w w', IsConjPl H w w' → ∀ k : H.Eˣ, χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹) ∧
    ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹

end GlobalTheory.Mem.Chr

end
end
end

section

noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def chiK (l : ℕ) [Fact l.Prime] (ψ : ZMod l → Qbar l) (r : ℕ) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  ψ (((y : ZMod (l ^ r)).val : ℕ) : ZMod l)

end GlobalTheory.K4
end
end

section

noncomputable section
namespace GlobalTheory.FockAlg
open Formalism.BasicNotions.TH

def IsFockIP {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) : Prop :=
  ∀ α β : σ →₀ ℕ, inner ℂ (ι (MvPolynomial.monomial α 1)) (ι (MvPolynomial.monomial β 1)) =
    if α = β then α.prod (fun _ k => (k.factorial : ℂ)) else 0

def harm1 (p q r s : ℕ) : Set (Pol p q r s) :=
  {P | ∀ Z : Mat r s, IsPC Z → minusPart (fockAct2 p q r s Z) P = 0}

def harm2 (p q r s : ℕ) : Set (Pol p q r s) :=
  {P | ∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) P = 0}

def jointHarm (p q r s : ℕ) : Set (Pol p q r s) := harm2 p q r s ∩ harm1 p q r s

def Intw {p q r s : ℕ} (M1 : GKMod p q) (M2 : GKMod r s)
    (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V) : Prop :=
  (∀ X, f ∘ₗ fockAct1 p q r s X = TensorProduct.map (M1.act X) LinearMap.id ∘ₗ f) ∧
  (∀ Y, f ∘ₗ fockAct2 p q r s Y = TensorProduct.map LinearMap.id (M2.act Y) ∘ₗ f)

def genSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (S : Set V) : Submodule ℂ V :=
  sInf {N | S ⊆ N ∧ ∀ Z, ∀ y ∈ N, act Z y ∈ N}

def ConeTypes {p q : ℕ} (M : GKMod p q) (lam : Ix p q → ℚ) : Prop :=
  ∀ (μ : Ix p q → ℚ) v, IsHW M.act μ v →
    ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → lam b < lam a) ∧
      μ = fun c => blattner lam c +
        ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))

theorem J_eq {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) : F.J = jointHarm p q r s := rfl

theorem isIntw_iff {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) (M1 : GKMod p q) (M2 : GKMod r s)
    (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V) : IsIntw F M1 M2 f ↔ Intw M1 M2 f :=
  Iff.rfl

theorem isFockIsometry_of_fockData {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2) : IsFockIP F.ι := by
  intro α β
  exact F.fockIP α β

end GlobalTheory.FockAlg
end
end

section

noncomputable section
namespace GlobalTheory.Glob.IntegralWittCoefficients.Model
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

def stdLat (E : Type) [Field E] [NumberField E] (N : ℕ) : Submodule (𝓞 E) (Fin N → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

theorem mem_range_iff {E : Type} [Field E] [NumberField E] (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_stdLat {E : Type} [Field E] [NumberField E] {N : ℕ} (x : Fin N → E) :
    x ∈ stdLat E N ↔ ∀ k, IsIntegral ℤ (x k) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
  exact forall_congr' fun k => mem_range_iff (x k)

theorem isSDLat_std (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) : IsSDLat E N (stdLat E N) := by
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈ stdLat E N := fun k => by
    rw [mem_stdLat]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [mem_range_iff]
    rw [mem_stdLat] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)
  · rw [mem_stdLat]
    intro k
    have := h _ (hs k)
    rw [mem_range_iff] at this
    simpa [stdH, Pi.single_apply, apply_ite] using this

end GlobalTheory.Glob.IntegralWittCoefficients.Model
end
end
