module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published.LeviCentreModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F) in
def big (δ : E) : Spc F E 3 := ⟨!![0, 0, 1; 0, δ, 0; -1, 0, 0], ⊥, fun _ => 1, fun _ => 1⟩


variable (F) in
def small (δ : E) : Spc F E 1 := ⟨!![δ], ⊥, fun _ => 1, fun _ => 1⟩



end GlobalTheory.Published.LeviCentreModel

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula GlobalTheory.SiegelFormula.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published.ThetaConvModel

variable {D : D7}

theorem exists_schwartz (θ : InfFam D) (m n : ℕ) : ∃ Φ : schwartzA θ m n, Φ.1 0 ≠ 0 := by
  classical
  let b : ContDiffBump (0 : D.what₂.Tau → Fin m → Fin n → ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hb2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ := hb1.toSchwartzMap hb2
  have hf : f 0 = 1 := by
    show ((b 0 : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]; simp
  let W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ Formalism.L2.Theta.intAE D}
      add_mem' := fun ha hb i j => (Formalism.L2.Theta.intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (Formalism.L2.Theta.intAE D).zero_mem
      neg_mem' := fun ha i j => (Formalism.L2.Theta.intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (Formalism.L2.Theta.intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  let φ : Mx D m n → ℂ := fun x =>
    f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))
  have hφ : φ ∈ schwartzA θ m n := Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨⟨φ, hφ⟩, ?_⟩
  show f _ * g _ ≠ 0
  have e : (fun τ i j => compAt θ τ (0 : Mx D m n) i j : D.what₂.Tau → Fin m → Fin n → ℂ) = 0 := by
    ext τ i j; simp [compAt]
  rw [e, hf]
  simp [g]
  exact (QuotientAddGroup.eq_zero_iff (N := W) (0 : Matrix (Fin m) (Fin n) _)).2 W.zero_mem

end GlobalTheory.Published.ThetaConvModel

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWAniso

section Coord

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Invertible (2 : R)] {n m : ℕ}


end Coord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}


end GlobalTheory.SWAniso

namespace GlobalTheory.Published

def SiegelWeilAnisotropicCM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ B : Base F E, IsCharAF F B.ψ →
  ∀ (n m : ℕ), 1 ≤ n → n < m →
  ∀ X : Spc F E n, IsHermND σ X.J → X.L.IsLattice E →
    (∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)) → (∀ w, IsCartan (X.J.map (B.emb w).1) (X.θ w)) →
  ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J → X₂.L = sumLat finSumFinEquiv X.L X.L →
    (∀ w, X₂.θ w = blkMat finSumFinEquiv (X.θ w) (-X.θ w)) →
  ∀ W : Spc F E m, (∀ i j, σ (W.J j i) = -W.J i j) → (∀ x, form σ W.J x x = 0 → x = 0) →
  ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X₂.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin (n + n) × Fin m),
    (∀ x : Matrix (Fin (n + n)) (Fin m) E, ∃ y z : Fin (n + n) × Fin m → F,
      co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ u, (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
    (∀ u, (∀ j, uᵀ j ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : Rep σ X₂ W, IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X₂.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) co 1 χ om →
  ∀ K : Subgroup (UA σ X₂.J), IsStab B K →
    IwasawaOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X₂.J)).subtype (absE F E) K →
  ∀ Φ ∈ schA F (Fin (n + n) × Fin m), FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (k, 1) Φ}) →
  ∀ (ν : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 ν →
    let P : Subgroup (UA σ X₂.J) := siegelOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X₂.J)).subtype
    let s₀ : ℂ := ((m : ℂ) - (n : ℂ)) / 2
    let f : ℂ → UA σ X₂.J → ℂ :=
      flatOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X₂.J)).subtype (absE F E) K (fun g => om (g, 1) Φ 0) s₀
    (∀ g, IntegrableOn (fun h => theta om Φ g h) 𝓕 ν) ∧
    (∀ s : ℂ, (n : ℝ) / 2 < s.re →
      AutomorphicL2Unitary.LeftInv (P ⊓ ratU σ X₂.J) (f s) ∧ ∀ g, Eis.CosetConv P (ratU σ X₂.J) (f s) g) ∧
    ∀ g, Cont.HolValueAt (fun s => Eis.cosetSum P (ratU σ X₂.J) (f s) g) s₀ (⨍ h in 𝓕, theta om Φ g h ∂ν)

end GlobalTheory.Published

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.Published

def SiegelEisensteinDoubled : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ (B : Base F E) (n : ℕ), 1 ≤ n →
  ∀ W : Spc F E n, (∀ i j, σ (W.J j i) = -W.J i j) → W.L.IsLattice E →
    (∀ y, y ∈ W.L ↔ ∀ x ∈ W.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W.J y x))) →
    (∀ w, IsCartan (Complex.I • W.J.map (B.emb w).1) (W.θ w)) →
  ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
  ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
  ∀ χ : Chr F E, IsHecke F E χ →
  ∀ (s₁ : ℂ) (φ : UA σ W₂.J → ℂ), φ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χ s₁ →
    let P : Subgroup (UA σ W₂.J) := siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype
    let f : ℂ → UA σ W₂.J → ℂ := flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ s₁
    ∃ Ei : ℂ → UA σ W₂.J → ℂ,
      (∀ s : ℂ, (n : ℝ) / 2 < s.re → ∀ g,
        Eis.CosetConv P (ratU σ W₂.J) (f s) g ∧ Ei s g = Eis.cosetSum P (ratU σ W₂.J) (f s) g) ∧
      ∀ s₀ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → UA σ W₂.J → ℂ), 0 < r ∧
        (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Ei s g) ∧
        (∀ g, DifferentiableOn ℂ (fun s => H s g) (Metric.ball s₀ r)) ∧
        ContinuousOn (fun x : ℂ × UA σ W₂.J => H x.1 x.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
        ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ g, ‖H s g‖ ≤ C * (ht g : ℝ) ^ N

end GlobalTheory.Published

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.Published

def SiegelWeilAnisotropicHermitian : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ B : Base F E, IsCharAF F B.ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ W : Spc F E n, (∀ i j, σ (W.J j i) = -W.J i j) → W.L.IsLattice E →
    (∀ y, y ∈ W.L ↔ ∀ x ∈ W.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W.J y x))) →
    (∀ w, IsCartan (Complex.I • W.J.map (B.emb w).1) (W.θ w)) →
  ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
  ∀ X : Spc F E m, (∀ i j, σ (X.J j i) = X.J i j) → (∀ x, form σ X.J x x = 0 → x = 0) →
  ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)) (Fin m × Fin (n + n)),
    (∀ x : Matrix (Fin m) (Fin (n + n)) E, ∃ y z : Fin m × Fin (n + n) → F,
      co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
    (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : Rep σ X W₂, IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J) co χ 1 om →
  ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)).subtype (absE F E) K →
  ∀ Φ ∈ schA F (Fin m × Fin (n + n)), FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ X.J)) (𝓕 : Set (UA σ X.J)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) 𝓕 ν →
    let P : Subgroup (UA σ W₂.J) := siegelOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)).subtype
    let s₀ : ℂ := ((m : ℂ) - (n : ℂ)) / 2
    let f : ℂ → UA σ W₂.J → ℂ :=
      flatOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)).subtype (absE F E) K (fun g => om (1, g) Φ 0) s₀
    (∀ g, IntegrableOn (fun h => theta om Φ h g) 𝓕 ν) ∧
    (∀ s : ℂ, (n : ℝ) / 2 < s.re →
      AutomorphicL2Unitary.LeftInv (P ⊓ ratU σ W₂.J) (f s) ∧ ∀ g, Eis.CosetConv P (ratU σ W₂.J) (f s) g) ∧
    ∀ g, Cont.HolValueAt (fun s => Eis.cosetSum P (ratU σ W₂.J) (f s) g) s₀
      ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, theta om Φ h g ∂ν)

end GlobalTheory.Published

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.CechPic

namespace GlobalTheory.Published

def ArithHilbertSamuel : Prop :=
  ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a →
      (∀ᶠ m : ℕ in atTop, ((L.pow m).tens N).smallSec.Finite) ∧
      (fun m : ℕ => Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) -
          a / ((D + 1).factorial : ℝ) * (m : ℝ) ^ (D + 1)) =o[atTop] fun m : ℕ => (m : ℝ) ^ (D + 1)

namespace ArithHilbertSamuel

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

theorem resG_resG {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

def secTensTriv (A : LB X) : A.Sec ≃ (tens A (LB.triv X)).Sec where
  toFun s := ⟨fun c => resG X inf_le_left (s.f c.1), fun c d => by
    have e := congrArg (resG X (U := A.U c.1 ⊓ A.U d.1)
      (V := (A.U c.1 ⊓ ⊤) ⊓ (A.U d.1 ⊓ ⊤)) (inf_le_inf inf_le_left inf_le_left)) (s.compat c.1 d.1)
    rw [map_mul, resG_resG, resG_resG] at e
    refine (resG_resG _ _ _).trans (e.trans ?_)
    refine congrArg₂ (· * ·) ?_ (resG_resG _ _ _).symm
    simp only [tens, map_one, mul_one]
    rfl⟩
  invFun t := ⟨fun i => resG X (le_inf le_rfl le_top) (t.f (i, PUnit.unit)), fun i j => by
    have e := congrArg (resG X (U := (A.U i ⊓ ⊤) ⊓ (A.U j ⊓ ⊤)) (V := A.U i ⊓ A.U j)
      (inf_le_inf (le_inf le_rfl le_top) (le_inf le_rfl le_top))) (t.compat (i, PUnit.unit) (j, PUnit.unit))
    erw [map_mul, resG_resG, resG_resG] at e
    refine (resG_resG _ _ _).trans (e.trans ?_)
    refine congrArg₂ (· * ·) ?_ (resG_resG _ _ _).symm
    simp only [tens, map_one, mul_one]
    exact (resG_resG _ _ _).trans (by simp [resG])⟩
  left_inv s := DVR.SecOps.sec_ext fun i => (resG_resG _ _ _).trans (by simp [resG])
  right_inv t := DVR.SecOps.sec_ext fun c => (resG_resG _ _ _).trans (by simp [resG]; rfl)

theorem nsq_secTensTriv (M : HermLB p) (s : M.B.Sec) (σ : k →+* ℂ) (y : CxPts p σ) :
    ((M.tens (HermLB.triv p)).φ σ).nsq (secVal p σ (secTensTriv M.B s)) y = (M.φ σ).nsq (secVal p σ s) y := by
  have hy := mem_pick ((M.tens (HermLB.triv p)).φ σ).isLB y
  rw [(M.φ σ).nsq_eq (secVal_mem s) (mem_ptsIn_inf.1 hy).1]
  exact congrArg₂ (fun a b => ‖a‖ ^ 2 * Real.exp (-b)) (ev_res _ hy _) (add_zero _)

theorem smallSec_tens_triv (M : HermLB p) :
    (M.tens (HermLB.triv p)).smallSec = secTensTriv M.B '' M.smallSec := by
  ext t
  obtain ⟨s, rfl⟩ := (secTensTriv M.B).surjective t
  refine Iff.trans ?_ (secTensTriv M.B).injective.mem_set_image.symm
  exact forall₂_congr fun σ y => by rw [nsq_secTensTriv]

variable [IsIntegral X] {L : HermLB p} {a : ℝ}

theorem of_triv (h : ArithHilbertSamuel) (hX : IsArithVar p D) (hL : L.IsNef D) (ha : L.IsSelfInter a) :
    (∀ᶠ m : ℕ in atTop, (L.pow m).smallSec.Finite) ∧
      (fun m : ℕ => Real.log ((L.pow m).smallSec.ncard : ℝ) -
          a / ((D + 1).factorial : ℝ) * (m : ℝ) ^ (D + 1)) =o[atTop] fun m : ℕ => (m : ℝ) ^ (D + 1) := by
  obtain ⟨h₁, h₂⟩ := h k X p D hX L (HermLB.triv p) a hL ha
  have e (m : ℕ) : ((L.pow m).tens (HermLB.triv p)).smallSec.ncard = (L.pow m).smallSec.ncard := by
    rw [smallSec_tens_triv]
    exact Set.ncard_image_of_injective _ (secTensTriv _).injective
  refine ⟨h₁.mono fun m hm => ?_, by simpa only [e] using h₂⟩
  rw [smallSec_tens_triv] at hm
  exact Set.Finite.of_finite_image hm (secTensTriv _).injective.injOn

theorem tendsto_of_triv (h : ArithHilbertSamuel) (hX : IsArithVar p D) (hL : L.IsNef D) (ha : L.IsSelfInter a) :
    Tendsto (fun m : ℕ => Real.log ((L.pow m).smallSec.ncard : ℝ) *
      (((D + 1).factorial : ℝ) / (m : ℝ) ^ (D + 1))) atTop (𝓝 a) := by
  have hf : ((D + 1).factorial : ℝ) ≠ 0 := by positivity
  have h₁ := ((h.of_triv hX hL ha).2.tendsto_div_nhds_zero.mul_const ((D + 1).factorial : ℝ)).add_const a
  rw [zero_mul, zero_add] at h₁
  refine h₁.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem volNef (h : ArithHilbertSamuel) : VolNef := fun k _ X _ p D hX L a hL ha => by
  refine Tendsto.limsup_eq (((continuous_coe_real_ereal.tendsto a).comp
    (h.tendsto_of_triv hX hL ha)).congr' ?_)
  filter_upwards [(h.of_triv hX hL ha).1] with m hm
  have h0 : 0 < (L.pow m).smallSec.ncard := (Set.ncard_pos hm).2 ⟨_, (L.pow m).zero_mem_smallSec⟩
  rw [← hm.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
    ENNReal.log_ofReal_of_pos (by exact_mod_cast h0), ← EReal.coe_mul]
  rfl

end ArithHilbertSamuel

end GlobalTheory.Published
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.StdUnn

def WeilEisensteinSiegelConvergence : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → 2 * n < V.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω →
  ∀ Φ : schwartzA θ V.rank n, Eis.CosetConv (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) 1

end GlobalTheory.Published

end
end
