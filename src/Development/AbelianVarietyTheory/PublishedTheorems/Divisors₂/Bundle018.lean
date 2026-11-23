module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published

def LeviCentreFiniteUnitary : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
    (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ →
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y.J.det ≠ 0 →
    Y₁.J.det ≠ 0 → ∀ ψ : UA σ Y.J → ℂ, (∀ u ∈ unip σ Y H, ∀ x, ψ (u * x) = ψ x) →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    (∀ φ : GAd σ (c • Y.J.map σ) → ℂ, (∀ (g : UA σ Y.J) (g' : GAd σ (c • Y.J.map σ)), g.1 = g'.1 → φ g' = ψ g) →
      GlobalTheory.UAut.IsSm σ (c • Y.J.map σ) φ ∧
        FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ})) →
    ∀ (h : UA σ Y.J) (g : UA σ Y₁.J → ℂ), (∀ h₁ m, IsLevi (W₁ := Y₁) H 1 h₁ m → g h₁ = ψ (m * h)) →
    ∀ φ₁ : GAd σ (c • Y₁.J.map σ) → ℂ, (∀ (g₁ : UA σ Y₁.J) (g' : GAd σ (c • Y₁.J.map σ)), g₁.1 = g'.1 → φ₁ g' = g g₁) →
      FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y₁.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ₁})

end GlobalTheory.Published

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published

def LeviCentreInducedUnitary : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
    (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ →
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J →
    ∀ ψ : UA σ Y.J → ℂ, (∀ u ∈ unip σ Y H, ∀ x, ψ (u * x) = ψ x) →
    ∀ χ : Chr F E, Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
    (∀ t m, IsLevi (W₁ := Y₁) H t 1 m → ∀ x, ψ (m * x) = (χ t : ℂ) * ψ x) →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    ∀ φ : GAd σ (c • Y.J.map σ) → ℂ, (∀ (g : UA σ Y.J) (g' : GAd σ (c • Y.J.map σ)), g.1 = g'.1 → φ g' = ψ g) →
      GlobalTheory.UAut.IsSm σ (c • Y.J.map σ) φ →
    ∀ V : Submodule ℂ (GAd σ (c • Y₁.J.map σ) → ℂ), FiniteDimensional ℂ V → (∀ v ∈ V, GlobalTheory.UAut.IsSm σ (c • Y₁.J.map σ) v) →
      (∀ v ∈ V, ∀ z, GlobalTheory.UAut.IsCentral σ (c • Y₁.J.map σ) z → GlobalTheory.UAut.dop z v ∈ V) →
    ∀ Kc : Set (UA σ Y.J), (∀ x : UA σ Y.J, ∃ u ∈ unip σ Y H, ∃ t h₁ m, IsLevi (W₁ := Y₁) H t h₁ m ∧ ∃ k ∈ Kc, x = u * m * k) →
      (∀ k ∈ Kc, ∃ v ∈ V, ∀ (h₁ : UA σ Y₁.J) (m : UA σ Y.J) (g' : GAd σ (c • Y₁.J.map σ)),
        IsLevi (W₁ := Y₁) H 1 h₁ m → h₁.1 = g'.1 → v g' = ψ (m * k)) →
      FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ})

end GlobalTheory.Published

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.Published

def RallisTowerUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin m) (Fin m) E),
    (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 →
  ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW m →
  ∀ f : UA σ JW → ℂ,
    (∃ (c₀ : E) (K : Subgroup (GAd σ (c₀ • JW.map σ))) (φ : GAd σ (c₀ • JW.map σ) → ℂ), IsHermND σ (c₀ • JW.map σ) ∧
      GlobalTheory.UAut.IsMaxCpt σ (c₀ • JW.map σ) K ∧ GlobalTheory.UAut.IsAut σ (c₀ • JW.map σ) K φ ∧
      GlobalTheory.SiegelSet.IsCuspidal σ (c₀ • JW.map σ) φ ∧
      ∀ (h : UA σ JW) (h' : GAd σ (c₀ • JW.map σ)), h.1 = h'.1 → φ h' = f h) →
    (∀ (n₁ k : ℕ) (J₁ : Matrix (Fin n₁) (Fin n₁) E), 1 ≤ k → n₁ + 2 * k = n → (∀ i j, σ (J₁ j i) = J₁ i j) → J₁.det ≠ 0 →
      ∀ co₁ : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n₁ × Fin m),
        (∀ x : Matrix (Fin n₁) (Fin m) E, ∃ y z : Fin n₁ × Fin m → F,
          co₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om₁ : UA σ J₁ × UA σ JW →* Module.End ℂ ((Fin n₁ × Fin m → AF F) → ℂ),
        IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co₁ χX χW om₁ →
      ∀ Φ₁ ∈ schA F (Fin n₁ × Fin m), ∀ (g : UA σ J₁) (μ : Measure (UA σ JW)) (𝓕 : Set (UA σ JW)), μ.IsHaarMeasure →
        IsFundamentalDomain (ratU σ JW) 𝓕 μ → ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (om₁ (g, h) Φ₁)) ∂μ = 0) →
  ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin m),
    (∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F,
      co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
  ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ),
    IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co χX χW om →
  ∀ Φ ∈ schA F (Fin n × Fin m), ∀ (μ : Measure (UA σ JW)) (𝓕 : Set (UA σ JW)), μ.IsHaarMeasure →
    IsFundamentalDomain (ratU σ JW) 𝓕 μ →
  ∀ c : E, IsHermND σ (c • JX.map σ) → ∀ th : GAd σ (c • JX.map σ) → ℂ,
    (∀ (g : UA σ JX) (g' : GAd σ (c • JX.map σ)), g.1 = g'.1 →
      th g' = ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) ∂μ) →
    GlobalTheory.SiegelSet.IsCuspidal σ (c • JX.map σ) th

end GlobalTheory.Published

end
end

section

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.Published


open GlobalTheory.EisLine in
def EisensteinResidueLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
      ∀ (x : Matrix (Fin n) (Fin 1) E), x = X.submatrix id (fun _ => 0) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ,
        (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
          ∃ k ∈ levelAll σ J L a, g = p * k) →
        (∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) →
      ∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
            (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) →
      ∃ R : ℂ, R ≠ 0 ∧ ∀ g : GAd σ J,
        Tendsto (fun s : ℂ => (s - ((n : ℂ) - 1) / 2) * ∑' t : T, (h (t.1.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2))
          (𝓝[{s : ℂ | ((n : ℝ) - 1) / 2 < s.re}] (((n : ℂ) - 1) / 2)) (𝓝 R)

end GlobalTheory.Published

end
end
