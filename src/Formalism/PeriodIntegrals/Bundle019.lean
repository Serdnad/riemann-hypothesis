module

import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.WittVector.Basic
public import Formalism.GradedWeylDivisibility.Bundle001
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.RealPlaceAnalysis.Bundle004
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.PeriodIntegrals.Bundle009
public import Formalism.HermitianLattices.Bundle003
public import Formalism.PeriodIntegrals.Bundle013
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.PeriodIntegrals.Bundle018
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace PI.ArtSch

open scoped NNReal

noncomputable section

section
variable (l : ℕ) [Fact l.Prime]

theorem OC_l_not_unit : ¬ IsUnit ((l : ℕ) : PadicComplexInt l) := by
  apply Formalism.BasicNotions.Loc.OC_l_not_unit <;> assumption

instance factOC : Fact (¬ IsUnit ((l : ℕ) : PadicComplexInt l)) := ⟨OC_l_not_unit l⟩

abbrev OC : Type := ↥(PadicComplexInt l)

abbrev OCb : Type := PreTilt (OC l) l

instance domOCb : IsDomain (OCb l) :=
  PreTilt.isDomain (PadicComplex l) (PadicComplex.valued l).v (OC l) (PadicComplexInt.integers l) l

abbrev Cb : Type := FractionRing (OCb l)

instance charCb : CharP (Cb l) l := charP_of_injective_algebraMap' (OCb l) l

abbrev WCb : Type := WittVector l (Cb l)

abbrev valb : Valuation (OCb l) ℝ≥0 :=
  PreTilt.val (PadicComplex l) (PadicComplex.valued l).v (OC l) (PadicComplexInt.integers l) l

end

def Main : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (x : WCb l), ∃ y : WCb l, WittVector.map (frobenius (Cb l) l) y - y = x

def WittLift : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p], (∀ a : k, ∃ y : k, y ^ p - y = a) →
    ∀ x : WittVector p k, ∃ y : WittVector p k, WittVector.map (frobenius k p) y - y = x

def TiltAS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (a : Cb l), ∃ y : Cb l, y ^ l - y = a

def RootModP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c b : ModP (OC l) l), ∃ z : ModP (OC l) l, z ^ l - c * z - b = 0

def TiltDiv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (x y : OCb l), valb l x ≤ valb l y → y ∣ x

def TiltSmall : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : OCb l), valb l e < 1 → ∃ w : OCb l, w ^ l - w = e

def TiltGlue : Prop := RootModP → TiltDiv → TiltSmall → TiltAS

theorem main_of (hW : WittLift) (hT : TiltAS) : Main := by
  intro l _ x
  exact hW l (Cb l) (hT l) x

end

end PI.ArtSch
end

section

noncomputable section

namespace PI

def stdGram {N : ℕ} (ν : Fin N → ℕ) {r : ℕ} (e : Module.Basis (Fin r) ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)) :
    Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j =>
    Formalism.GradedWeylDivisibility.fockQ (MvPolynomial.map (Int.castRingHom ℚ) (e i : MvPolynomial (Fin N × Fin N) ℤ))
              (MvPolynomial.map (Int.castRingHom ℚ) (e j : MvPolynomial (Fin N × Fin N) ℤ)) /
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν)

def MuStd {N : ℕ} (ν : Fin N → ℕ) (μ : ℝ) : Prop :=
  ∃ (r : ℕ) (e : Module.Basis (Fin r) ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)), 0 < r ∧
    μ = -Real.log ((stdGram ν e).det : ℝ) / r

def cNu {N : ℕ} (ν : Fin N → ℕ) : ℝ :=
  (Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) : ℝ) / ∏ l, ((ν l).factorial : ℝ)

def HookBound : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ), Antitone ν →
    1 ≤ cNu ν ∧ cNu ν ≤ ((ν ⟨0, hN⟩ : ℝ) + N) ^ (N * (N - 1) / 2)

def StdSlopeLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (μ : ℝ), Antitone ν → MuStd ν μ →
    -((∑ l, (ν l : ℝ)) * Real.log N + Real.log (cNu ν)) ≤ μ

end PI
end
end

section

noncomputable section

open MeasureTheory

namespace PI.CdHaarScale

abbrev umat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

def CdTieAt (cd : Formalism.BasicNotions.CDHaar) (n : ℕ) (ε : Fin n → Bool) (c : NNReal) : Prop :=
  ∀ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((c : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

end PI.CdHaarScale

namespace PI

def CdHaarScale : Prop :=
  ∀ (cd : Formalism.BasicNotions.CDHaar) (n : ℕ) (ε : Fin n → Bool), ∃ c : NNReal, 0 < c ∧ PI.CdHaarScale.CdTieAt cd n ε c

end PI
end
end

section

namespace PI.AlgWtHwUnq

open NumberField IsDedekindDomain Formalism.L2.NG ReciprocityTheory.Aut

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

def Stmt : Prop :=
  ∀ (a : AlgWt L n) (τ : L →+* ℂ) (lam lam' : Fin n → ℤ), a.HWAt τ lam → a.HWAt τ lam' → lam = lam'

end PI.AlgWtHwUnq
end

section

noncomputable section

open Matrix NumberField
open scoped TensorProduct
open PI.UJClassFin

namespace PI.UJClassMass2

def gramOf {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) {M : ℕ} (b : Module.Basis (Fin M) E V) : Matrix (Fin M) (Fin M) E :=
  fun i j => h (b i) (b j)

def crdOf {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) : Set (Fin M → E) :=
  {x | ∑ i, x i • b i ∈ L0}

def stab {G : Type*} [Group G] (Γ K : Subgroup G) (g : G) : Set Γ := {γ | g⁻¹ * ((γ : G) * g) ∈ K}

def UJClassMass : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (n : ℕ) (g : Fin n → HA (AF F) σ (gramOf h b)),
      (∀ x, ∃ i, ∃ γ : GamG σ (gramOf h b), ∃ k : SFin σ (gramOf h b) (crdOf b L0),
        x = (γ : HA (AF F) σ (gramOf h b)) * g i * k) →
      (∀ i j (γ γ' : GamG σ (gramOf h b)) (k k' : SFin σ (gramOf h b) (crdOf b L0)),
        (γ : HA (AF F) σ (gramOf h b)) * g i * k = (γ' : HA (AF F) σ (gramOf h b)) * g j * k' → i = j) →
      ∑ i, ((Nat.card (stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) (g i)) : ℝ))⁻¹ =
        Formalism.HermitianLatticesTheory.mass h L0

end PI.UJClassMass2
end
end

section

noncomputable section

namespace PI.BesselMapUniq

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open PI.UpqRep

section Bessel

def ellA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
  else (g *ᵥ z) (Formalism.QuantumDeterminants.eI k r a)

def psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Complex.exp (Complex.I * ((∑ a, c a * ellA k r z g a).re : ℂ))

end Bessel

section Smooth

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

def IsBesselMapSm {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (B : H → Wp) : Prop :=
  (∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ w ∈ smoothVecs (k := k) (r := r) σ, B (v + w) = B v + B w) ∧
    (∀ (c : ℂ), ∀ v ∈ smoothVecs (k := k) (r := r) σ, B (c • v) = c • B v) ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
      B (σ (h * m) v) = ψ m • π h (B v)) ∧
    IsCWCont (k := k) (r := r) σ B

end Smooth

def BesselMapUniq : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    (∀ a, c a ≠ 0) → IsHCTypeW k r z u π →
    ∀ B₁ B₂ : H → Wp, IsBesselMapSm (k := k) (r := r) z (psiGen k r z c) σ π B₁ →
      IsBesselMapSm (k := k) (r := r) z (psiGen k r z c) σ π B₂ →
      ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ smoothVecs (k := k) (r := r) σ, a • B₁ v + b • B₂ v = 0

end PI.BesselMapUniq
end
end

section

namespace PI

def QmBorderES : Prop := BorderE ∧ BorderS

end PI
end

section

namespace PI

def QmBorderFull : Prop := BorderFull

end PI
end

section

namespace PI

def QmColExp : Prop := ExpFirstCol ∧ ExpLastCol

end PI
end

section

namespace PI

def QmMove : Prop := MoveVec ∧ MoveCov

end PI
end

section

namespace PI

def QmRowExp : Prop := ExpFirstRow ∧ ExpLastRow

end PI
end

section

namespace PI

def QmRowForm : Prop := RowForm

end PI
end
