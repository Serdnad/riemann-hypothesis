module

public import Formalism.PeriodIntegrals.Bundle010
public import Formalism.PeriodIntegrals.Bundle002
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Formalism.PeriodIntegrals.UpqRep
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Formalism.RealPlaceAnalysis.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

section

namespace PI

def WfRing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf g →
    CoefWf (f + g) ∧ CoefWf (f - g) ∧ CoefWf (f * g) ∧ ∀ c : ℂ_[p], InWf c → CoefWf (MvPowerSeries.C c * f)

end PI
end

section

noncomputable section

namespace PI

def WfEndDefs.W2pair (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} :
    Set (ℂ_[p] × ℂ_[p]))

def mulBy {p : ℕ} [Fact p.Prime] {σ : Type*} (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex

def PairW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ α ∈ WfEndDefs.W2pair p, α.1 ∈ Wp p

def WfEnd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p → AddIntG.IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (AddIntG.flog W wq) = PowerSeries.X →
    ∀ c : ℂ_[p], InWf c →
      IntegralMv (mulBy (AddIntG.flog W wq) ex c (MvPowerSeries.X ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralW (mulBy (AddIntG.flog W wq) ex c (MvPowerSeries.X ()) : MvPowerSeries Unit ℂ_[p])

end PI

end
end

section

namespace PI

def InvSerSub : Prop :=
  ∀ (K : Type) [Field K] (S : Subring K) (l ex : PowerSeries K),
    (∀ n, PowerSeries.coeff n l ∈ S) → PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X → ∀ n, PowerSeries.coeff n ex ∈ S

def WfLogL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p → AddIntG.IsWq W wq →
    CoefWf (AddIntG.flog W wq)

def WfLog : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p → AddIntG.IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (AddIntG.flog W wq) = PowerSeries.X →
    CoefWf (AddIntG.flog W wq) ∧ CoefWf ex

end PI
end

section

namespace PI

def SubstSub : Prop :=
  ∀ (A : Type) [CommRing A] (S : Subring A) (σ : Type) (f : PowerSeries A) (a : MvPowerSeries σ A),
    (∀ n, PowerSeries.coeff n f ∈ S) → (∀ n, MvPowerSeries.coeff n a ∈ S) →
    MvPowerSeries.constantCoeff a = 0 → ∀ n, MvPowerSeries.coeff n (PowerSeries.subst a f) ∈ S

def WfSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    CoefWf f → CoefWf a → MvPowerSeries.constantCoeff a = 0 → CoefWf (PowerSeries.subst a f)

end PI
end

section

noncomputable section

namespace PI

open PI.UpqRep

def HCMult : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S →
      FiniteDimensional ℂ (eqImg (fun k : KG ε => σ (toMK k)) S)

end PI
end
end

section

noncomputable section

namespace PI

open PI.UpqRep

def KFinSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDSHpk k r ε lam σ →
    ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → v ∈ smoothVecs (k := k) (r := r) σ

end PI
end
end

section

noncomputable section

namespace PI

open PI.UpqRep

def nPl {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = true)).card

def nMi {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = false)).card

def WeylForK : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset ε) σ → IsKTypeOf ε σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Λ + rhoC ε) a - (Λ + rhoC ε) b)) /
      ((∏ i ∈ Finset.range (nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (nMi ε), (i.factorial : ℝ))

end PI
end
end

section

open MeasureTheory Matrix Finset Topology
open scoped InnerProductSpace ContDiff ComplexOrder

noncomputable section

namespace PI.UpqRep

def rdM {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (X : Matrix (Fin m) (Fin m) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ → V) : Matrix (Fin m) (Fin m) ℂ → V :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

section KF

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsKFin {n : ℕ} (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ IsKStableOn ε σ S

end KF

def thetaJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Jm ε * Xᴴ * Jm ε)

def reJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (X + thetaJ ε X)

def imJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I / 2)) • (X - thetaJ ε X)

def rdC {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => rdM (reJ ε X) f g + Complex.I * rdM (imJ ε X) f g

def rdCWord {n : ℕ} (ε : Fin n → Bool) :
    List (Matrix (Fin n) (Fin n) ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ
  | [], f => f
  | X :: w, f => rdC ε X (rdCWord ε w f)

def gelfandOp {n : ℕ} (ε : Fin n → Bool) (k : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a : Fin (k + 1) → Fin n,
    rdCWord ε (List.ofFn fun i : Fin (k + 1) => Matrix.single (a i) (a (finRotate (k + 1) i)) (1 : ℂ)) f g

def IsEquiv {n : ℕ} {H' H : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ε : Fin n → Bool) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ v : H', U (σ' g v) = σ g (U v)

section Eig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def Eig (ε : Fin n → Bool) (c : ℕ → ℂ) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
    (∀ g ∈ UJset ε, F g = ⟪x, Ψ g y⟫_ℂ) ∧ ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = c k * F g

end Eig

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def wI (k r : ℕ) (j : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + j.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0

def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re

def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}

def blockW (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j =>
    if hi : r ≤ i.val ∧ i.val < r + k then
      (if hj : r ≤ j.val ∧ j.val < r + k then h ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0)
    else (if i = j then 1 else 0)

def IsFrameW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) = z

section Second

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ g, IsFrameW k r z g ∧ IsHCTypeU k u (fun h => π (g * blockW k r h * g⁻¹))

def InLieHpk (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  Xᴴ * Hpk k r + Hpk k r * X = 0

def dsig (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def dsigW (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)

def IsLowUnitH (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ∃ P, IsCayleyU k r ε P ∧ IsLowUnit ε lam (fun g => σ (P⁻¹ * g * P)) w

end Second

end PI.UpqRep

end
end

section

open Matrix

noncomputable section

namespace PI

def symD {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : ℝ :=
  sInf {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
    ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
    t = Real.sqrt (Formalism.REAL.hs X)}

def SymDist : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g k : Formalism.REAL.UJ ε), symD ε (g * k) ≤ symD ε g + symD ε k

end PI

end
end

section

noncomputable section

open scoped Classical

open IsDedekindDomain NumberField ValuativeRel MeasureTheory

namespace PI.PinHostLoc

def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (g : Fin 2 → ℕ), (∀ i, (g i).Prime) → g 0 ≠ g 1 →
    ∀ i : Fin 2, ((g i : ℕ) : 𝓞 F) ∈ p.asIdeal → ((g i : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 →
      Irreducible ((Formalism.MainNotions.S.Loc.resChar p : ℕ) : 𝒪[A.Fp]) ∧
        ∃ u : 𝒪[A.Fp], IsUnit u ∧
          (u : A.Fp) = A.ιF (((g 0 : ℕ) : F) * ((g 1 : ℕ) : F) / ((g i : ℕ) : F))

end PI.PinHostLoc
end
end

section

noncomputable section

open ValuativeRel IsDedekindDomain NumberField

namespace PI.TrDualLoc

def Stmt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) [Fact (Formalism.MainNotions.S.Loc.resChar p).Prime]
    (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp]
    [Algebra ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp], Continuous (algebraMap ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp) →
    FiniteDimensional ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
    (∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) →
    ∀ t : K, (∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) →
    ∀ c ∈ 𝒪[Fp], ‖Algebra.trace ℚ_[Formalism.MainNotions.S.Loc.resChar p] Fp (c * ι t)‖ ≤ 1

end PI.TrDualLoc
end
end

section

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocDualGen

def DualAtL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) (δ : A.Fp) : Prop :=
  ∀ x : A.Ep, (∀ y ∈ A.O, A.psiE (-(x * y * algebraMap A.Fp A.Ep δ⁻¹)) = 1) ↔ x ∈ A.O

def UnramL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) : Prop :=
  ∀ ϖ : 𝒪[A.Fp], Irreducible ϖ → ∀ x ∈ A.O,
    x * x ∈ Submodule.span A.O {algebraMap A.Fp A.Ep (ϖ : A.Fp)} →
      x ∈ Submodule.span A.O {algebraMap A.Fp A.Ep (ϖ : A.Fp)}

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p),
    (IsReduced A.Ep → UnramL A → ∃ δ : A.Fp, δ ≠ 0 ∧ DualAtL A δ) ∧
    (∀ (δ : A.Fp) (u : 𝒪[A.Fp]), IsUnit u → DualAtL A δ → DualAtL A (δ * (u : A.Fp))) ∧
    (IsReduced A.Ep → UnramL A → Irreducible ((resChar p : ℕ) : 𝒪[A.Fp]) → DualAtL A 1)

end PI.LocDualGen
end
end
