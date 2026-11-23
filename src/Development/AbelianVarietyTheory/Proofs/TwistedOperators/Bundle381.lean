module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle048
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle094
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobolevCauchyTendstoSmoothLimit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.hilbertTensor_traceClass_hasTrace_prod : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ Φ' : ContinuousMultilinearMap ℂ Hs H) (κ κ' : ℂ), (∀ y y', inner ℂ (Φ y') (Φ y) = ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ y') (Φ' y) = κ * ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ' y') (Φ' y) = κ' * ∏ i, inner ℂ (y' i) (y i)) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ y, X (Φ y) = Φ' fun i => B i (y i)) → (∀ v, (∀ y, inner ℂ (Φ y) v = 0) → X v = 0) → HasTrace X (κ * ∏ i, b i) := by
  first | exact @GlobalTheory.tensorTrace_hasTrace | exact GlobalTheory.tensorTrace_hasTrace | (intros; apply GlobalTheory.tensorTrace_hasTrace <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepLatIdeal

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem smul_mem_of_mem_smul (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (a : E)
    (ha : ∀ m ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E m * a) (x : Fin n → E) (hx : x ∈ 𝔪 • Λ) :
    a • x ∈ Λ := by
  refine Submodule.smul_induction_on (p := fun w => a • w ∈ Λ) hx (fun m hm y hy => ?_) (fun u v hu hv => ?_)
  · obtain ⟨c, hc⟩ := ha m hm
    have e : a • (m • y) = c • y := by
      rw [← algebraMap_smul E m y, ← algebraMap_smul E c y, smul_smul, hc, mul_comm]
    simp only [e]
    exact Λ.smul_mem c hy
  · simp only [smul_add]
    exact Λ.add_mem hu hv

theorem smul_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (a : E)
    (ha : ∀ m ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E m * a)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) • z ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    have hax := smul_mem_of_mem_smul Λ 𝔪 a ha x hx
    change _ ∈ Submodule.span _ _
    refine Submodule.subset_span ⟨a • x, hax, ?_⟩
    funext i
    show (a • x) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (x i ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [smul_add]; exact Submodule.add_mem _ hu hv
  | smul s u _ hu =>
    rw [Subring.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ s hu

theorem eq_zero_of_mem_hatL_bot (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (⊥ : Submodule (𝓞 E) (Fin n → E))) : z = 0 := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    have hx0 : x = 0 := (Submodule.mem_bot _).1 hx
    subst hx0
    funext i
    show (0 : E) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = 0
    exact TensorProduct.zero_tmul _ _
  | zero => rfl
  | add u v _ _ hu hv => rw [hu, hv, add_zero]
  | smul s u _ hu => rw [hu, smul_zero]

theorem nontrivial_af : Nontrivial (Formalism.L2.Herm.Af F) := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' := congrArg (fun b : Formalism.L2.Herm.Af F => b v) h
  change (0 : _) = 1 at h'
  exact zero_ne_one h'

theorem mem_smul_span (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (y : Fin n → E)
    (hy : g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    y ∈ 𝔪 • Submodule.span (𝓞 E) {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ} := by
  by_cases h𝔪 : 𝔪 = ⊥
  · subst h𝔪
    have h0 : g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = 0 :=
      eq_zero_of_mem_hatL_bot _ (by simpa [Submodule.bot_smul] using hy)
    have hv : (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = 0 := by
      have := congrArg (fun w => (g⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 *ᵥ w) h0
      simpa [Matrix.mulVec_mulVec] using this
    haveI := nontrivial_af (F := F)
    have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] Formalism.L2.Herm.Af F) :=
      Algebra.TensorProduct.includeLeft_injective (algebraMap F (Formalism.L2.Herm.Af F)).injective
    have hy0 : y = 0 := by
      funext i
      apply hinj
      simpa using congrFun hv i
    subst hy0
    exact Submodule.zero_mem _
  · have hP : (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have h1 : (1 : E) ∈ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
        (((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hP]
      exact FractionalIdeal.one_mem_one _
    have key : ∀ c ∈ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
        (((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E),
        c • y ∈ 𝔪 • Submodule.span (𝓞 E) {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
          Formalism.L2.Herm.hatL (F := F) Λ} := by
      intro c hc
      refine Submodule.mul_induction_on (C := fun c => c • y ∈ 𝔪 • Submodule.span (𝓞 E)
        {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) Λ})
        hc (fun m hm a ha => ?_) (fun u v hu hv => ?_)
      · obtain ⟨m', hm', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
        have hint : ∀ t ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E t * a := by
          intro t ht
          obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
            ((FractionalIdeal.mem_inv_iff hP).1 ha _ (FractionalIdeal.mem_coeIdeal_of_mem _ ht))
          exact ⟨c, by rw [hc, mul_comm]⟩
        have hcol : (fun i => (a • y) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) =
            (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) • (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) := by
          funext i
          show (a * y i) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (y i ⊗ₜ[F] 1)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        have haS : g.1 *ᵥ (fun i => (a • y) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
          rw [hcol, Matrix.mulVec_smul]
          exact smul_mem_hatL Λ 𝔪 a hint _ hy
        rw [mul_smul, algebraMap_smul]
        exact Submodule.smul_mem_smul hm' (Submodule.subset_span haS)
      · rw [add_smul]
        exact Submodule.add_mem _ hu hv
    simpa using key 1 h1

end General

theorem mem_smul_latAt : ∀ (D : D7) (V : HSp D) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (x : GA D V) (y : Fin V.rank → D.host.E), (Lev.finE V x⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) → y ∈ 𝔪 • latAt Λ x := by
  intro D V Λ 𝔪 _ x y hy
  unfold GlobalTheory.SepPer.latAt
  exact mem_smul_span Λ 𝔪 (Lev.finE V x⁻¹) y hy

end GlobalTheory.SepLatIdeal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLoc

variable {D : D7}

def embAt (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau) (k : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  cmp θ τ (stabilizerEmbedding d (atTau θ Y τ k))

def mco {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (v₀ : M.H τ) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : ℂ :=
  ⟪M.rep τ g₀ v₀, M.rep τ g (M.rep τ g₀ v₀)⟫_ℂ

def ptY {Y : HSp D} {S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S') (τ : D.what₂.Tau) (u : Formalism.REAL.UJ (M₀.ε τ)) :
    Matrix (Fin Y.rank) (Fin Y.rank) ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M₀ τ (Formalism.MainNotions.S.umat u)

structure LocOK (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S')
    (M : DSModel V S) (τ : D.what₂.Tau) (q : ℝ) (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ)
    (εB : Fin V.rank → Bool) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ) (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : M₀.H τ) (c : ℂ) : Prop where

  unitA : IsUnit A

  gramA : Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ

  unitB : IsUnit B

  gramB : Bᴴ * Formalism.REAL.Jm εB * B = gramAt D V τ

  adapted : ∀ (y : Fin Y.rank → ℂ) (a : ℂ),
    eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2

  real : g₀ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)

  kfin : v₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ

  dec : DecayAt M τ v₀ v₀ (2 * V.rank ^ 2 + 1)

  sm : w ∈ M₀.sm τ

  ne : w ≠ 0

  cne : c ≠ 0

  act : ∀ b : M₀.H τ, ∫ u, mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u)) * ⟪b, M₀.rep τ (ptY M₀ τ u) w⟫_ℂ ∂(Formalism.REAL.muG (M₀.ε τ)) =
    c * ⟪b, w⟫_ℂ

  far : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => mco M τ g₀ v₀ (g * embAt θ d τ (ptY M₀ τ u))) (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖mco M τ g₀ v₀ (g * embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖c‖

  lip : ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖mco M τ g₀ v₀ (embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * ptY M₀ τ u)) -
      mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖mco M τ g₀ v₀ (embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * ptY M₀ τ u)) -
      mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤ Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹)

end GlobalTheory.PackLoc

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameDecay

section Frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing

theorem hs_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (Real.rpow_natCast _ 2).symm

theorem hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepPer.hsn (A * B) ≤ GlobalTheory.SepPer.hsn A * GlobalTheory.SepPer.hsn B := by
  unfold GlobalTheory.SepPer.hsn
  rw [hs_eq_norm, hs_eq_norm, hs_eq_norm]
  exact Matrix.frobenius_norm_mul A B

end Frob

theorem hsn_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ GlobalTheory.SepPer.hsn A := Real.sqrt_nonneg _

theorem one_le_hsn_of_mem {n : ℕ} (ε : Fin n → Bool) (i : Fin n) (y : Matrix (Fin n) (Fin n) ℂ)
    (hy : y ∈ Formalism.MainNotions.S.UJset ε) : 1 ≤ GlobalTheory.SepPer.hsn y := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  have h := congrFun (congrFun hy' i) i
  have e1 : (yᴴ * Formalism.REAL.Jm ε * y) i i = ∑ k, star (y k i) * ((if ε k then 1 else -1) * y k i) := by
    simp only [Formalism.REAL.Jm]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    ring
  have e2 : ‖Formalism.REAL.Jm ε i i‖ = 1 := by
    by_cases hi : ε i = true <;> simp [Formalism.REAL.Jm, hi]
  have hcol : 1 ≤ ∑ k, ‖y k i‖ ^ 2 := by
    rw [← e2, ← h, e1]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    by_cases hk : ε k = true <;> simp [hk, norm_mul, sq]
  have hall : ∑ k, ‖y k i‖ ^ 2 ≤ ∑ a, ∑ b, ‖y a b‖ ^ 2 :=
    Finset.sum_le_sum fun a _ =>
      Finset.single_le_sum (f := fun b => ‖y a b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ i)
  unfold GlobalTheory.SepPer.hsn
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (hcol.trans hall)

end GlobalTheory.FrameDecay

namespace GlobalTheory.FrameDecay

theorem coef_frame_decay : ∀ (m N : ℕ), N = m + 1 → ∀ (ε : Fin N → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v₀ : H) (g₀ F G : Matrix (Fin N) (Fin N) ℂ) (A₀ : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → g₀ ∈ Formalism.MainNotions.S.UJset ε → IsUnit F → Fᴴ * Formalism.REAL.Jm ε * F = G →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε, ‖⟪π g₀ v₀, π g (π g₀ v₀)⟫_ℂ‖ ≤ A₀ * GlobalTheory.SepReal.hsn g ^ (-(20 * ((m : ℝ) + 1) ^ 2))) →
  ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH G, ‖⟪v₀, π (F * g * F⁻¹) v₀⟫_ℂ‖ * (1 + GlobalTheory.SepPer.hsn g) ^ (2 * N ^ 2 + 1) ≤ C := by
  intro m N hN ε H instH instI π v₀ g₀ F G A₀ hπ hg₀ hF hG hdec
  obtain ⟨⟨_, hmul⟩, hiso, -⟩ := hπ
  have hg₀' : g₀ᴴ * Formalism.REAL.Jm ε * g₀ = Formalism.REAL.Jm ε := hg₀
  have hJJ := Formalism.REAL.Jm_mul_self ε

  have hleft : (Formalism.REAL.Jm ε * g₀ᴴ * Formalism.REAL.Jm ε) * g₀ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g₀ᴴ, hg₀', hJJ]
  have hinv : g₀⁻¹ = Formalism.REAL.Jm ε * g₀ᴴ * Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv hleft
  have hl : g₀⁻¹ * g₀ = 1 := by rw [hinv, hleft]
  have hr : g₀ * g₀⁻¹ = 1 := Matrix.mul_nonsing_inv g₀ (Matrix.isUnit_det_of_left_inverse hleft)
  have hmemMul : ∀ a ∈ Formalism.MainNotions.S.UJset ε, ∀ b ∈ Formalism.MainNotions.S.UJset ε, a * b ∈ Formalism.MainNotions.S.UJset ε := by
    intro a ha b hb
    have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
    show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
    calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [ha', hb']
  have hinvMem : g₀⁻¹ ∈ Formalism.MainNotions.S.UJset ε := by
    show (g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * g₀⁻¹ = Formalism.REAL.Jm ε
    conv_lhs => rw [← hg₀']
    rw [show (g₀⁻¹)ᴴ * (g₀ᴴ * Formalism.REAL.Jm ε * g₀) * g₀⁻¹ = (g₀ * g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (g₀ * g₀⁻¹) by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc], hr]
    simp

  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  have hFl : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul F hFd
  have hFr : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hFd

  have hkeep : ∀ u w : H, ⟪π g₀ u, π g₀ w⟫_ℂ = ⟪u, w⟫_ℂ := by
    intro u w
    let T : H →ₗᵢ[ℂ] H := ⟨(π g₀ : H →ₗ[ℂ] H), fun v => hiso g₀ hg₀ v⟩
    exact T.inner_map_map u w
  set k : ℝ := 20 * ((m : ℝ) + 1) ^ 2 with hk
  set e : ℕ := 2 * N ^ 2 + 1 with he
  have hek : (e : ℝ) ≤ k := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [he, hk, hN]; push_cast; nlinarith
  set c₁ : ℝ := GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * GlobalTheory.SepPer.hsn (g₀ * F) with hc₁
  have hc₁0 : 0 ≤ c₁ := mul_nonneg (hsn_nonneg _) (hsn_nonneg _)
  refine ⟨|A₀| * (1 + c₁) ^ e, fun g hg => ?_⟩
  have hg' : gᴴ * G * g = G := hg
  set x := F * g * F⁻¹ with hx
  have hxMem : x ∈ Formalism.MainNotions.S.UJset ε := by
    show xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε
    have : xᴴ * Formalism.REAL.Jm ε * x = (F⁻¹)ᴴ * (gᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * g) * F⁻¹ := by
      rw [hx, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, hG, hg', ← hG]
    have hFH : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hFr, Matrix.conjTranspose_one]
    calc (F⁻¹)ᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * F⁻¹ = ((F⁻¹)ᴴ * Fᴴ) * Formalism.REAL.Jm ε * (F * F⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hFH, hFr, Matrix.one_mul, Matrix.mul_one]
  set y := g₀ * x * g₀⁻¹ with hy
  have hyMem : y ∈ Formalism.MainNotions.S.UJset ε := hmemMul _ (hmemMul _ hg₀ _ hxMem) _ hinvMem

  have hco : ⟪v₀, π x v₀⟫_ℂ = ⟪π g₀ v₀, π y (π g₀ v₀)⟫_ℂ := by
    have h1 : π y (π g₀ v₀) = π g₀ (π x v₀) := by
      have h2 : y * g₀ = g₀ * x := by rw [hy, Matrix.mul_assoc, hl, Matrix.mul_one]
      rw [← ContinuousLinearMap.comp_apply, ← hmul _ hyMem _ hg₀, h2, hmul _ hg₀ _ hxMem,
        ContinuousLinearMap.comp_apply]
    rw [h1, hkeep]

  set s := GlobalTheory.SepPer.hsn y with hs
  set t := GlobalTheory.SepPer.hsn g with ht
  have hs1 : 1 ≤ s := one_le_hsn_of_mem ε ⟨0, by omega⟩ y hyMem
  have hs0 : 0 < s := by linarith
  have hts : t ≤ c₁ * s := by
    have hgeq : g = (F⁻¹ * g₀⁻¹) * y * (g₀ * F) := by
      have : (F⁻¹ * g₀⁻¹) * y * (g₀ * F) = (F⁻¹ * F) * g * (F⁻¹ * F) := by
        rw [hy, hx]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc g₀⁻¹ g₀, hl, Matrix.one_mul,
          ← Matrix.mul_assoc g₀⁻¹ g₀, hl, Matrix.one_mul]
      rw [this, hFl, Matrix.one_mul, Matrix.mul_one]
    rw [ht, hgeq, hc₁]
    calc GlobalTheory.SepPer.hsn ((F⁻¹ * g₀⁻¹) * y * (g₀ * F))
        ≤ GlobalTheory.SepPer.hsn ((F⁻¹ * g₀⁻¹) * y) * GlobalTheory.SepPer.hsn (g₀ * F) := hsn_mul_le _ _
      _ ≤ (GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * s) * GlobalTheory.SepPer.hsn (g₀ * F) :=
          mul_le_mul_of_nonneg_right (hsn_mul_le _ _) (hsn_nonneg _)
      _ = GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * GlobalTheory.SepPer.hsn (g₀ * F) * s := by ring
  have hbd := hdec y hyMem
  have hsame : GlobalTheory.SepReal.hsn y = s := rfl
  rw [hsame, ← hco] at hbd
  have hpow : s ^ (-k) ≤ (s ^ e)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hs0.le]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hz : ‖⟪v₀, π x v₀⟫_ℂ‖ ≤ |A₀| * (s ^ e)⁻¹ :=
    hbd.trans ((mul_le_mul_of_nonneg_right (le_abs_self A₀) (Real.rpow_nonneg hs0.le _)).trans
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)))
  have hT : (1 + t) ^ e ≤ (1 + c₁) ^ e * s ^ e := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith [hsn_nonneg g]) ?_ e
    nlinarith
  have hse : 0 < s ^ e := pow_pos hs0 e
  calc ‖⟪v₀, π x v₀⟫_ℂ‖ * (1 + t) ^ e ≤ (|A₀| * (s ^ e)⁻¹) * ((1 + c₁) ^ e * s ^ e) :=
        mul_le_mul hz hT (pow_nonneg (by linarith [hsn_nonneg g]) _)
          (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr hse.le))
    _ = |A₀| * (1 + c₁) ^ e := by field_simp

end GlobalTheory.FrameDecay
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem norm_dict : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (w : Fin V.rank → D.host.E), ∏ v, Real.sqrt (∑ i, ‖(Formalism.MainNotions.S.uMat (x.1 v)⁻¹ *ᵥ (((Formalism.IndefR.Eqv.UI.instV fr).P v)⁻¹ *ᵥ fun j => (Formalism.IndefR.Eqv.UI.instV fr).φ v (w j))) i‖ ^ 2) = ∏ τ, nrm θ A (Formalism.IndefR.Eqv.UI.brg fr x) τ w := by
  intro D θ hθ V A fr hP x w
  symm
  refine Fintype.prod_equiv (Formalism.L2.Host.tauPl D) _ _ fun τ => ?_
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  unfold nrm eu GlobalTheory.SepPer.cmp
  rw [← map_inv (Formalism.IndefR.Eqv.UI.brg fr) x, (GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr).2.1 x⁻¹ τ _ rfl, hP τ]
  have key : ∀ (U Q : Matrix (Fin V.rank) (Fin V.rank) ℂ) (y : Fin V.rank → ℂ),
      A.fr τ *ᵥ (((A.fr τ)⁻¹ * U * Q) *ᵥ y) = U *ᵥ (Q *ᵥ y) := fun U Q y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  erw [key]
  have hP' : (Formalism.IndefR.Eqv.UI.instV fr).P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := hP τ
  have hφ : (Formalism.IndefR.Eqv.UI.instV fr).φ (Formalism.L2.Host.tauPl D τ) = tauE D τ := by
    show Formalism.IndefR.Eqv.UI.phiV D _ = _
    simp only [Formalism.IndefR.Eqv.UI.phiV, Equiv.symm_apply_apply]
  erw [hP', hφ]
  rfl

end GlobalTheory.NormDict
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.growthSobolev_cauchy_tendsto_smooth_limit : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ ψ n ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (ψ n) ≠ ⊤) → (∀ d, Filter.Tendsto (fun p : ℕ × ℕ => GlobalTheory.Size.growthSob θ V d N (ψ p.1 - ψ p.2)) Filter.atTop (nhds 0)) → ∃ f : GA D V → ℂ, Continuous f ∧ f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, Filter.Tendsto (fun n => GlobalTheory.Size.growthSob θ V d N (ψ n - f)) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.GrowthComplete.complete | exact GlobalTheory.GrowthComplete.complete | (intros; apply GlobalTheory.GrowthComplete.complete <;> assumption)
end
