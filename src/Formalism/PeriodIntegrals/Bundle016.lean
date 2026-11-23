module

public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Formalism.PeriodIntegrals.Bundle013
public import Formalism.PeriodIntegrals.JointBlockShapes.JointShape
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UpqRep
public import Mathlib.Analysis.InnerProductSpace.Defs

@[expose] public section

section

noncomputable section

open Matrix Formalism.QuantumDeterminants

namespace PI.BesselLevi

def BesselLevi : Prop :=
  ∀ (k r : ℕ) (T : ℝ), 0 < T → ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
    s ∈ UH (Hpk k r) →
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0) →
    (∀ i : Fin (2 * r + k + 1), r ≤ i.val →
      (s *ᵥ (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))) i =
        (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) i) →
    s ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))

end PI.BesselLevi
end
end

section

noncomputable section

namespace PI.BesselL2FixAtZero

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff ENNReal
open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Defs

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def ellA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
  else (g *ᵥ z) (Formalism.QuantumDeterminants.eI k r a)

def psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Complex.exp (Complex.I * ((∑ a, c a * ellA k r z g a).re : ℂ))

end Defs

end PI.BesselL2FixAtZero
end
end

section

noncomputable section
open NumberField Matrix

namespace PI.SqPair

open Formalism.L2.PairingIndexBounds.Eq.SqG

def PLocal (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L' L'' : Submodule (𝓞 E) (Fin N → E)) (n : 𝓞 E) (p : ℕ) : Prop :=
  ∃ e : Matrix (Fin N) (Fin N) E,
    (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') ∧
    ∀ M ∈ ({e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)} : Set (Matrix (Fin N) (Fin N) E)),
      ∀ y, (y ∈ L' ∨ y ∈ L'') →
        ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ ∃ m, m ∈ L' ∧ m ∈ L'' ∧ (s : E) • (M *ᵥ y) = (n : E) • m

def PLocalAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ n : 𝓞 E, n ≠ 0 → ∀ p : ℕ, p.Prime → PLocal E N L' L'' n p

def LocCartanPair : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R ≃+* R), (∀ x, σ (σ x) = x) →
    ∀ (R₀ : Subring R), (∀ x, x ∈ R₀ ↔ σ x = x) →
    ∀ [IsDomain R₀] [IsDiscreteValuationRing R₀] [HenselianLocalRing R₀]
      [Finite (IsLocalRing.ResidueField R₀)],
    (∃ θ : R, IsUnit (θ - σ θ)) →
    ∀ ϖ : R₀, Irreducible ϖ →
    ∀ (N : ℕ), Even N → ∀ (k : ℕ) (h : Matrix (Fin N) (Fin N) R),
      (h.map σ)ᵀ * h = ((ϖ : R) ^ (2 * k)) • (1 : Matrix (Fin N) (Fin N) R) →
      ∃ e f : Matrix (Fin N) (Fin N) R, e * e = e ∧ (e.map σ)ᵀ = 1 - e ∧ e * h = h * f

end PI.SqPair
end
end

section

open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldDCUnfold

def FoldDCUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S S' : Subgroup G) [Countable Γ], S ≤ Γ → S' ≤ Γ →
  ∀ (D D' : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
    Formalism.L2.SG.FoldBound.IsRightTransversal Γ S' D' →
  ∀ (R : Set G), Formalism.L2.SG.PoincareSeriesSquareIntegrable.IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (Formalism.L2.SG.PoincareSeriesSquareIntegrable.stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (g h : G → ℝ≥0∞), Measurable g → Measurable h →
    (∀ s ∈ S, ∀ y : G, g (s * y) = g y) → (∀ s ∈ S', ∀ y : G, h (s * y) = h y) →
    (∫⁻ x in FΓ, (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) ∂μ)
      = ∑' r : R, ∫⁻ x in Fs r, g x * h ((r : G)⁻¹ * x) ∂μ

end PI.FoldDCUnfold
end

section

noncomputable section
open scoped ComplexConjugate

namespace PI.GoodTwo

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

def IntCurve {K : Type} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1 ∧ ‖W.Δ‖ = 1

def Half : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ (c : ℂ) (hc : c ≠ 0) (W : WeierstrassCurve ℂ_[2]),
      (W.c₄ / 12 = ι (scalePair L c hc).g₂ ∧ W.c₆ / 216 = ι (scalePair L c hc).g₃) ∧ IntCurve W

def Full : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ (c : ℂ) (hc : c ≠ 0) (W : WeierstrassCurve ℂ_[2]),
      (W.c₄ / 12 = ι (scalePair L c hc).g₂ ∧ W.c₆ / 216 = ι (scalePair L c hc).g₃) ∧ IntCurve W ∧ ‖W.a₁‖ = 1

def Twist : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (W : WeierstrassCurve K) (g2 g3 : K),
    W.Δ ≠ 0 → g2 ^ 3 - 27 * g3 ^ 2 ≠ 0 → W.c₄ ^ 3 * (g2 ^ 3 - 27 * g3 ^ 2) = 1728 * g2 ^ 3 * W.Δ →
    ∃ u : K, u ≠ 0 ∧ W.c₄ / 12 = u ^ 4 * g2 ∧ W.c₆ / 216 = u ^ 6 * g3

def JUnit : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), Squarefree d → d % 8 = 7 → HasCMBy d L → ∀ ι : ℂ ≃+* ℂ_[2], ‖ι (jInv L)‖ = 1

def disc (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

def IsIdxTwo (L L' : PeriodPair) : Prop :=
  ∃ t : ℂ, t ∉ L.lattice ∧ 2 * t ∈ L.lattice ∧ ∀ z, z ∈ L'.lattice ↔ (z ∈ L.lattice ∨ z - t ∈ L.lattice)

def TwoIsog : Prop :=
  ∀ L L' : PeriodPair, IsIdxTwo L L' → (disc L' + 16 * disc L) ^ 3 = jInv L * disc L' * disc L ^ 2

def NormPow : Prop :=
  ∀ d : ℕ, Squarefree d → d % 8 = 7 →
    ∃ (h : ℕ) (x y : ℤ), 0 < h ∧ Odd y ∧ x ^ 2 + x * y + (((d + 1) / 4 : ℕ) : ℤ) * y ^ 2 = 2 ^ h

def Chain : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → HasCMBy d L → ∀ (h : ℕ) (x y : ℤ), Odd y →
    x ^ 2 + x * y + (((d + 1) / 4 : ℕ) : ℤ) * y ^ 2 = 2 ^ h → ∀ π : ℂ, (π = x + y * omegaK d ∨ π = x + y * conj (omegaK d)) →
    ∃ M : ℕ → PeriodPair, M 0 = L ∧ (∀ i, HasCMBy d (M i)) ∧ (∀ i, i < h → IsIdxTwo (M i) (M (i + 1))) ∧
      ∀ z, z ∈ (M h).lattice ↔ π * z ∈ L.lattice

end PI.GoodTwo
end
end

section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace PI

open PI.UpqRep

section

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

def thetaH (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  -(Hpk k r * Xᴴ * Hpk k r)

def dsigC (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  dsig (k := k) (r := r) σ ((1 / 2 : ℂ) • (X + thetaH k r X)) v +
    Complex.I • dsig (k := k) (r := r) σ ((-(Complex.I / 2)) • (X - thetaH k r X)) v

end

end PI
end
end

section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace PI

open PI.UpqRep

def LowSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H), IsHCParam lam →
    IsDSHpk k r ε lam σ → IsLowUnitH k r ε lam σ w → w ∈ smoothVecs (k := k) (r := r) σ

def SmoothCyc : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H), IsHCParam lam →
    IsDSHpk k r ε lam σ → IsLowUnitH k r ε lam σ w →
    ∀ x ∈ smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)),
    (∀ w' ∈ Ws, ∀ Y ∈ w', InLieHpk k r Y) → ∀ δ : ℝ, 0 < δ →
    ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ i, g i ∈ UH (Hpk k r)) ∧
      (Ws.map fun w' => ‖dsigW (k := k) (r := r) σ w' (x - ∑ i, c i • σ (g i) w)‖).sum < δ

end PI
end
end

section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.ZuckTensor

open PI.UpqRep

def GapAtLeast {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) : Prop :=
  ∀ a b : Fin n, ε a ≠ ε b → h ≤ |lam a - lam b|

structure TensorDS (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) where
  Sm : Finset (Fin n)
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)
  ds : ∀ s ∈ Sm, IsHCParam (μ + Pi.single s 1) ∧ IsDS ε (μ + Pi.single s 1) (σs s)
  inequiv : ∀ s ∈ Sm, ∀ s' ∈ Sm, s ≠ s' → ¬ ∃ U : Hs s ≃ₗᵢ[ℂ] Hs s',
    ∀ g ∈ UJset ε, ∀ x, U (σs s g x) = σs s' g (U x)
  toSum : ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, Hs (sI i)),
      (∀ i, sI i ∈ Sm ∧ IsKFin ε (σs (sI i)) (vI i) ∧ IsKFin ε (σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g *ᵥ x)) = ∑ i, ⟪wI i, σs (sI i) g (vI i)⟫_ℂ
  ofSum : ∀ s ∈ Sm, ∀ v w : Hs s, IsKFin ε (σs s) v → IsKFin ε (σs s) w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σs s g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g *ᵥ xI i))

attribute [instance] TensorDS.nH TensorDS.iH TensorDS.cH

structure TensorDSd (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) where
  Sm : Finset (Fin n)
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)
  ds : ∀ s ∈ Sm, IsHCParam (μ - Pi.single s 1) ∧ IsDS ε (μ - Pi.single s 1) (σs s)
  inequiv : ∀ s ∈ Sm, ∀ s' ∈ Sm, s ≠ s' → ¬ ∃ U : Hs s ≃ₗᵢ[ℂ] Hs s',
    ∀ g ∈ UJset ε, ∀ x, U (σs s g x) = σs s' g (U x)
  toSum : ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, Hs (sI i)),
      (∀ i, sI i ∈ Sm ∧ IsKFin ε (σs (sI i)) (vI i) ∧ IsKFin ε (σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g⁻¹ *ᵥ x)) = ∑ i, ⟪wI i, σs (sI i) g (vI i)⟫_ℂ
  ofSum : ∀ s ∈ Sm, ∀ v w : Hs s, IsKFin ε (σs s) v → IsKFin ε (σs s) w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σs s g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g⁻¹ *ᵥ xI i))

attribute [instance] TensorDSd.nH TensorDSd.iH TensorDSd.cH

def Zuck : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
      ∃ X : TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ IsHCParam (μ + Pi.single s 1)

def ZuckDual : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∃ g : ℝ, 1 < g ∧ GapAtLeast ε μ g) →
      ∃ X : TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ IsHCParam (μ - Pi.single s 1)

end PI.ZuckTensor

end
end

section

noncomputable section

open Matrix FockH1Action

namespace PI.FockDegreeTwoParts

def WtDeg : Prop := ∀ p q r s : ℕ,
  (∀ d (μ : Ix p q → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (fockAct1 p q r s) μ P →
    degW (cPair r s) μ ≤ d) ∧
  (∀ d (μ : Ix r s → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (fockAct2 p q r s) μ P →
    degW (cPair p q) μ ≤ d)

def OneDeg : Prop := ∀ p q r s : ℕ,
  (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
    (∀ Z : Mat r s, IsPC Z → minusPart ((fockAct2 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
  (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
    (∀ Z : Mat p q, IsPC Z → minusPart ((fockAct1 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d)

def JointMult : Prop := ∀ p q r s : ℕ,
  (∀ (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    (JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (Jset p q r s)) = 1) ∧
    (¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (Jset p q r s) = ⊥))

def HarmSplit : Prop := ∀ p q r s : ℕ,
  (∀ (u1 u2 : Bool), (u1 || u2) = true → ∀ d : ℕ,
    homog (Ix p q × Ix r s) (d + 2) =
      (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (lowKer p q r s u1 u2)) ⊔
      Submodule.span ℂ (raised p q r s u1 u2 d))

end PI.FockDegreeTwoParts
end
end

section

noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm

def AllLoc (P : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E],
    Model F E → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → P M

def LocGlue : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M =>
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (abelian₂ : Submodule M.L.O V),
    H.IsSelfDual abelian₂ → ∀ (U : Submodule E V) (hU : IsCompl U (H.perp U)),
    (∀ u : V, u ∈ U → ((∃ x ∈ abelian₂, (Submodule.linearProjOfIsCompl U (H.perp U) hU x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ U → H.h u y ∈ M.L.O)) ∧
    (∀ u : V, u ∈ H.perp U → ((∃ x ∈ abelian₂,
        (Submodule.linearProjOfIsCompl (H.perp U) U hU.symm x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ H.perp U → H.h u y ∈ M.L.O))

def LocOProj : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M =>
  ∀ (W : Type) [AddCommGroup W] [Module E W] (P : Submodule M.L.O W), P.FG → Module.Projective M.L.O P

end PI.LocHerm
end
end

section

noncomputable section

namespace PI.OmFibreUniq

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

abbrev TupV (n a : ℕ) : Type := Fin a → Fin n → Fv F v ⊗[F] E

def dX (a : ℕ) : Measure (TupV (E := E) v n a) :=
  if h : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ then h.choose else 0

def dT (a : ℕ) : Measure (HermR (Fv F v) σ a) :=
  if h : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν then h.choose else 0

def IndepV (a : ℕ) : Set (TupV (E := E) v n a) := {X | LinearIndependent (Fv F v ⊗[F] E) X}

def IsOm (a : ℕ) (fib : HermR (Fv F v) σ a → Measure (TupV (E := E) v n a)) : Prop :=
  IsFibreFamily (dX σ J ψ v a) (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a)
    (dT σ ψ v a) Set.univ fib

def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x =
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : NumberField.InfinitePlace F, (NumberField.InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

def StdHyp : Prop := IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ IsStdChar ψ

def OmUnique (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ fib, IsOm σ J ψ v a fib) ∧ ∀ fib fib', IsOm σ J ψ v a fib → IsOm σ J ψ v a fib' → fib = fib'

end Meas

end PI.OmFibreUniq
end
end
