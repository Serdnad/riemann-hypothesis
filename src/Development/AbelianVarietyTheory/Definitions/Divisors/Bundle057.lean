module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047

@[expose] public section

section

namespace GlobalTheory.ThK

structure KP : Prop where

  base : GlobalTheory.FunPr.Hypotheses₂

  howeDualityUnitary : GlobalTheory.Published.HoweDualityUnitary

  howeDualityReal : GlobalTheory.Published.HoweDualityReal

  automorphicFormsUnitary : GlobalTheory.Published.AutomorphicFormsUnitary

  eisensteinIsotropicLine : GlobalTheory.Published.EisensteinIsotropicLine

  genericityGL : GlobalTheory.Published.GenericityGL

  complementaryThetaInert : GlobalTheory.Published.ComplementaryThetaInert

  siegelSetUnitary : GlobalTheory.Published.SiegelSetUnitary

  minguezThetaGL : GlobalTheory.Published.MinguezThetaGL

  jacquetShalika : GlobalTheory.Published.JacquetShalika

  discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL

  heckeTateFunctionalEquation : GlobalTheory.Published.HeckeTateFunctionalEquation

  automorphicFormsFiniteUnitary : GlobalTheory.Published.AutomorphicFormsFiniteUnitary

  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration

  cuspidalSpectrumGL : GlobalTheory.Published.CuspidalSpectrumGL

  siegelWeilAnisotropicCM : GlobalTheory.Published.SiegelWeilAnisotropicCM

  siegelWeilAnisotropicHermitian : GlobalTheory.Published.SiegelWeilAnisotropicHermitian

  siegelEisensteinDoubled : GlobalTheory.Published.SiegelEisensteinDoubled

  leviCentreFiniteUnitary : GlobalTheory.Published.LeviCentreFiniteUnitary

  leviBlockCentreFinite : GlobalTheory.Published.LeviBlockCentreFinite

  leviCentreInducedUnitary : GlobalTheory.Published.LeviCentreInducedUnitary

  eisensteinResidueLine : GlobalTheory.Published.EisensteinResidueLine

  rallisTowerUnitary : GlobalTheory.Published.RallisTowerUnitary

end GlobalTheory.ThK
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp
open scoped NNReal

section Generic

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def ratioField (ev : V →ₗ[K] Ω) : IntermediateField K Ω :=
  IntermediateField.adjoin K {a | ∃ v w, a = ev v / ev w}

def GenRatios (ev : V →ₗ[K] Ω) : Prop := ev ≠ 0 ∧ ratioField ev = ⊤

def ValBound (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  ∀ ν : Valuation Ω ℝ≥0, (∀ a : K, a ≠ 0 → ν (algebraMap K Ω a) = 1) → ∃ v, ν t ≤ ν (ev v) ^ τ

end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

set_option synthInstance.maxHeartbeats 100000 in
def BirOn (Z : Comp Xo c) (G : WTZ E) : Prop := GenRatios (genPoint Z (cuspOn U Z G))

set_option synthInstance.maxHeartbeats 100000 in
def ValMult (Z : Comp Xo c) (G G' : WTZ E) : Prop :=
  ∃ (a : ℕ) (θ : Rul Xo c), 1 ≤ a ∧ genVal Z θ ≠ 0 ∧ ∀ (k : ℕ), 1 ≤ k → ∀ f ∈ cuspOn U Z ((a * k) • G'),
    θ ^ k * f ∈ cuspOn U Z ((a * k) • G) ∧ ValBound (genPoint Z (cuspOn U Z G)) (a * k) (genVal Z (θ ^ k * f))

end GlobalTheory.DegVal
end
end

section



noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}


theorem mem_holSub_model {Cp : Type} (X : Cp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) :
    P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem mul_mem_cuspOn_of_isSec {Z : Comp Xo c} {G₀ : WTZ E} (h0 : Even G₀.2) {s : Rul Xo c}
    (hs : s ∈ secZ Xo c (exZ Dw G₀)) (hZ : s ∈ suppOn Z)
    (hh : ∀ σ, GoodEmb c σ → ∀ k, ((U σ).X k).IsSec (modelWt (U σ) G₀ k) (rdU (U σ) s k))
    (hb : ∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C)
    {G : WTZ E} (hG : Even G.2) {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : f * s ∈ cuspOn U Z (G + G₀) := by
  refine ⟨?_, mul_mem_suppOn _ hZ⟩
  have hf' := mem_cuspW.1 hf.1
  refine mem_cuspW.2 ⟨exZ_add_eq (Dw := Dw) G G₀ ▸ mul_mem_secZ hf'.1 hs, fun σ hσ => ?_⟩
  rw [AllWt.rdU_mul, mem_holSub_model]
  intro k
  rw [modelWt_add (U σ) hG h0 k]
  refine (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_model _ _ _).1 (hf'.2 σ hσ) k) _ ⟨hh σ hσ k, ?_⟩
  obtain ⟨C, hC⟩ := hb σ hσ
  refine ⟨max 0 (C / lieFacZ Dw x G₀), fun y _ => ?_⟩
  by_cases hy : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
  · refine le_max_of_le_right ((le_div_iff₀' (lieFacZ_pos x G₀)).2 ?_)
    have := hC _ hy
    unfold homN ptN at this
    exact this
  · have := rdU_eq_zero (U σ) hZ hy
    simp only at this
    simp [Data.pnorm, this]


end GlobalTheory.FlatTw
end
end

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.ResLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def col {n r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin 1) E := X.submatrix id fun _ => 0

def Scales (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (p : GAd σ J)
    (l : (AF F ⊗[F] E)ˣ) : Prop := (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x

def lineGrp (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) : Subgroup (GAd σ J) where
  carrier := {p | ∃ l, Scales σ J x p l}
  one_mem' := ⟨1, by simp [Scales]⟩
  mul_mem' := fun {a b} ⟨l, e⟩ ⟨l', e'⟩ => ⟨l * l', by
    unfold Scales at *
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', Matrix.mul_smul, e, smul_smul, Units.val_mul, mul_comm]⟩
  inv_mem' := fun {a} ⟨l, e⟩ => ⟨l⁻¹, by
    unfold Scales at *
    have := congrArg (fun Z => (l⁻¹).1 • ((matHom _ σ J a⁻¹).1 * Z)) e
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul] at this
    exact this.symm⟩

structure Data (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) : Prop where
  cm : IsCMExt F E σ
  unr : Algebra.Unramified (𝓞 F) (𝓞 E)
  herm : IsHermND σ J
  witt : IsWittFrame σ J X Y
  adapted : GlobalTheory.EisLine.IsAdapted σ J X Y L a
  iwa : ∀ g, ∃ p l, Scales σ J (col X) p l ∧ ∃ k ∈ levelAll σ J L a, g = p * k
  ht : ∀ p l, Scales σ J (col X) p l → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l

def IsReps (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l, Scales σ J x (γ * t⁻¹ : ratPts σ J).1 l

structure IsHt {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (h : G → ℝ) : Prop where
  pos : ∀ g, 0 < h g
  cont : Continuous h
  one : ∀ k ∈ K, h k = 1
  iw : ∀ g, ∃ k ∈ K, ∀ x, h (g * x) = h g * h (k * x)

instance countable_inf {G : Type} [Group G] (Γ H : Subgroup G) [Countable Γ] : Countable (Γ ⊓ H : Subgroup G) :=
  (Subgroup.inclusion_injective inf_le_left).countable

structure SemiLat {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (N M Λ : Subgroup G) (ν : Measure N)
    (π : Measure M) (𝓝 : Set N) (𝓜 : Set M) : Prop where
  closedN : IsClosed (N : Set G)
  closedM : IsClosed (M : Set G)
  norm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N
  disj : ∀ g ∈ N, g ∈ M → g = 1
  dec : ∀ γ ∈ Λ, ∃ u ∈ N, ∃ m ∈ M, u ∈ Λ ∧ m ∈ Λ ∧ γ = u * m
  haarN : ν.IsHaarMeasure
  haarM : π.IsHaarMeasure
  domN : IsFundamentalDomain (Λ.subgroupOf N) 𝓝 ν
  domM : IsFundamentalDomain (Λ.subgroupOf M) 𝓜 π
  finN : ν 𝓝 ≠ ⊤
  finM : π 𝓜 ≠ ⊤
  count : Countable Λ := by infer_instance
  topGrp : IsTopologicalGroup G := by infer_instance
  borel : BorelSpace G := by infer_instance

namespace Inhab

open GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E}


theorem semiLat_ne_zero {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    {N M Λ : Subgroup G} {ν : Measure N} {π : Measure M} {𝓝 : Set N} {𝓜 : Set M}
    (H : SemiLat N M Λ ν π 𝓝 𝓜) : ν 𝓝 ≠ 0 := by
  haveI := H.haarN
  haveI := H.count
  haveI := H.topGrp
  haveI := H.borel
  haveI : Countable (Λ.subgroupOf N) := Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, x.2⟩ : Λ)) fun a b h => Subtype.ext (Subtype.ext (congrArg (·.1) h))
  exact H.domN.measure_ne_zero (NeZero.ne ν)

theorem fd_one {H : Type} [Group H] [MeasurableSpace H] [MeasurableSingletonClass H] (Λ : Subgroup H) (hΛ : ∀ g, g ∈ Λ)
    (μ : Measure H) : IsFundamentalDomain Λ ({1} : Set H) μ :=
  IsFundamentalDomain.mk' (measurableSet_singleton _).nullMeasurableSet fun x =>
    ⟨⟨x⁻¹, hΛ _⟩, inv_mul_cancel x, fun _ hy => Subtype.ext (eq_inv_of_mul_eq_one_left hy)⟩

theorem haar_count {H : Type} [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
    [BorelSpace H] : (Measure.count : Measure H).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
    open_pos := fun U _ hU h => hU.ne_empty (Measure.count_eq_zero_iff.1 h) }

theorem semiLat_finite {G : Type} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace G]
    [BorelSpace G] (N M : Subgroup G) [hN : N.Normal] (hd : ∀ g ∈ N, g ∈ M → g = 1) (hs : ∀ g, ∃ u ∈ N, ∃ m ∈ M, g = u * m) :
    SemiLat N M ⊤ Measure.count Measure.count {1} {1} :=
  ⟨isClosed_discrete _, isClosed_discrete _, fun m _ u hu => hN.conj_mem u hu m, hd,
    fun γ _ => let ⟨u, hu, m, hm, e⟩ := hs γ; ⟨u, hu, m, hm, trivial, trivial, e⟩, haar_count, haar_count,
    fd_one _ (fun _ => Subgroup.mem_subgroupOf.2 (Subgroup.mem_top _)) _,
    fd_one _ (fun _ => Subgroup.mem_subgroupOf.2 (Subgroup.mem_top _)) _, by simp, by simp,
    inferInstance, inferInstance, inferInstance⟩

end Inhab

end GlobalTheory.ResLine

end
end
