module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle029
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import Mathlib.RingTheory.Nullstellensatz
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.EqZeroOfIsIsoSub
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCuspDataForTorusInvariant
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.Prime
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle030
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.RingTheory.Localization.FractionRing
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollA
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.mixed_discriminant_two_row_expansion : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (u : Fin (d + 2) → Fin 2 → ℝ) (v : Fin (d + 2) → ℝ) (n₀ n₁ : Fin 3 → ℝ) (e₀ e₁ : ℂ),
      ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁)
        ((∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))) =
      e₀ * e₁ * L (evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.mixed_discriminant_one_row_expansion : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (c : Fin (d + 1) → ℝ) (v : Fin (d + 1) → ℝ) (n : Fin 3 → ℝ) (e : ℂ),
      ((d + 1).factorial : ℂ) * mdisc (fun r => blk ((c r : ℂ) * e)
        ((∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H)) =
      e * L (evalW n n (pderiv (some 0) (∏ r, rowW ![c r, 0] (v r)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.extract_one | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.extract_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.extract_one <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt Filter Topology

def cxSimple {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ) : Prop :=
  ∃ (y : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ), IsSetSheet S Ψ y w γ ∧
    ∀ᶠ q in 𝓝 (y, w), q.2 ∈ setFibre S Ψ q.1 → q.2 = segre (γ q.1)

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartSet (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def chartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (chartSet S σ i)

def chartComponents (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Finset (Ideal (MvPolynomial (Fin m) ℂ)) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) ℂ)
    (chartIdeal S σ i)).toFinset

omit [∀ k, Fintype (ι k)] in
theorem mem_chartComponents {S : Set ((Σ k, ι k) → ℂ)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} :
    J ∈ chartComponents S σ i ↔ J ∈ (chartIdeal S σ i).minimalPrimes :=
  Set.Finite.mem_toFinset _

def chartSection [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) : MvPolynomial (Fin m) ℂ :=
  aeval (fun q : Σ k, ι k => (X (σ.symm (Function.update i q.1 q.2)) : MvPolynomial (Fin m) ℂ)) s

def domCell (i : (k : K) → ι k) : Set ((Σ k, ι k) → ℂ) :=
  {z | ∀ i', ‖segre z i'‖ ≤ ‖segre z i‖}


open Classical in
def absLogNorm (A : HermLine ι) (s : MRingOver ℂ ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 then |logNormC A s z| else 0

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.exists_cusp_data_for_torus_invariant : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) [Nonempty Ψ] (U : ((Σ k, J k) → ℂ) → ℝ), (∀ z, 0 ≤ U z) → (∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) → ∃ Cd : CuspData D ℤ (Fin 2 → ℤ), Cd.cuspWeight = U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Fake.every_weight_is_cusp_weight | exact GlobalTheory.CompanionTheory.Ar.Cusp.Fake.every_weight_is_cusp_weight | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Fake.every_weight_is_cusp_weight <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead

theorem aeval_eq_image {σ E : Type} [CommRing E] [Algebra ℚ E] (π : MvPolynomial σ ℂ →+* E)
    (G : MvPolynomial σ ℚ) :
    aeval (fun q => π (X q)) G = π (map (algebraMap ℚ ℂ) G) := by
  have h : (aeval (fun q => π (X q)) : MvPolynomial σ ℚ →ₐ[ℚ] E).toRingHom =
      π.comp (map (algebraMap ℚ ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact DFunLike.congr_fun (RingHom.ext_rat
        ((aeval (fun q => π (X q)) : MvPolynomial σ ℚ →ₐ[ℚ] E).toRingHom.comp C)
        ((π.comp (map (algebraMap ℚ ℂ))).comp C)) r
    · intro i
      simp
  exact DFunLike.congr_fun h G

theorem aeval_int_eq {σ Ω : Type} [CommRing Ω] [Algebra ℚ Ω] (τ : σ → Ω)
    (g : MvPolynomial σ ℤ) : aeval τ g = aeval τ (map (Int.castRingHom ℚ) g) := by
  have h : (aeval τ : MvPolynomial σ ℤ →ₐ[ℤ] Ω).toRingHom =
      (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom.comp (map (Int.castRingHom ℚ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact DFunLike.congr_fun (RingHom.ext_int
        ((aeval τ : MvPolynomial σ ℤ →ₐ[ℤ] Ω).toRingHom.comp C)
        (((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom.comp
          (map (Int.castRingHom ℚ))).comp C)) r
    · intro i
      simp
  exact DFunLike.congr_fun h g

theorem map_map_int {σ : Type} (g : MvPolynomial σ ℤ) :
    map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) g) = map (Int.castRingHom ℂ) g := by
  rw [MvPolynomial.map_map,
    RingHom.ext_int ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ)]

theorem read_in_field {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (τ : σ → Ω)
    (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (Js : Set (MvPolynomial σ ℤ)) (e n : ℕ)
    (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ)
    (hF : aeval τ F ≠ 0) (hS : S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)))
    (hz : ∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i))
    (hprime : ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q))
    (𝔮 : Ideal (MvPolynomial σ ℂ))
    (hker : ∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ 𝔮)
    (hFq : map (algebraMap ℚ ℂ) F ∉ 𝔮)
    (E : Type) [Field E] [Algebra ℚ E] (π : MvPolynomial σ ℂ →+* E)
    (hπ : ∀ p, π p = 0 ↔ p ∈ 𝔮) :
    (∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮 := by
  have hau : ∀ G : MvPolynomial σ ℚ,
      aeval (fun q => π (X q)) G = π (map (algebraMap ℚ ℂ) G) := aeval_eq_image π
  have hunit : IsUnit (aeval (fun q => π (X q)) F) := by
    rw [hau]
    exact IsUnit.mk0 _ (fun h => hFq ((hπ _).1 h))
  obtain ⟨φ, hφ⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.Kext.exists_algHom_adjoin_inv Ω σ τ F S E (fun q => π (X q)) hF hS
    (fun G hG => by rw [hau]; exact (hπ _).2 (hker G hG)) hunit
  have hτS : ∀ q, τ q ∈ S := fun q => by
    rw [hS]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨q, rfl⟩)
  let τS : σ → S := fun q => ⟨τ q, hτS q⟩
  have hcoe : ∀ G : MvPolynomial σ ℚ, ((aeval τS G : S) : Ω) = aeval τ G := by
    intro G
    have h : S.val.comp (aeval τS) = aeval τ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [τS]
    exact DFunLike.congr_fun h G
  have hq : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmem : ∀ s, s ∈ RingHom.ker φ ↔ φ s = 0 := fun s => RingHom.mem_ker
  have hleft : (∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔
      (∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ RingHom.ker φ) := by
    constructor
    · intro h g hg s hs
      rw [hmem, hφ (map (Int.castRingHom ℚ) g) s (by rw [hs, aeval_int_eq]), hau, map_map_int]
      exact (hπ _).2 (h g hg)
    · intro h g hg
      have hs := hcoe (map (Int.castRingHom ℚ) g)
      have h0 := h g hg (aeval τS (map (Int.castRingHom ℚ) g)) (by rw [hs, aeval_int_eq])
      rw [hmem, hφ _ _ hs, hau, map_map_int] at h0
      exact (hπ _).1 h0
  have hright : ∀ i, z i ∈ RingHom.ker φ ↔ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮 := by
    intro i
    have hzi : φ (z i * (aeval τS F) ^ N i) = aeval (fun q => π (X q)) (Z i) :=
      hφ _ _ (by push_cast; rw [hcoe, hz])
    have hfS : φ (aeval τS F) = aeval (fun q => π (X q)) F := hφ _ _ (hcoe F)
    rw [map_mul, map_pow, hfS] at hzi
    have hf0 : aeval (fun q => π (X q)) F ≠ 0 := hunit.ne_zero
    rw [hmem, ← hπ, ← hau, ← hzi]
    simp [hf0]
  rw [hleft, hprime _ hq]
  exact exists_congr fun i => and_congr_right fun _ => hright i

theorem boundary_on_primes : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (Js : Set (MvPolynomial σ ℤ)) (e n : ℕ) (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ), aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) → (∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i)) → (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ Js, ∀ s : S, (s : Ω) = aeval τ g → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) → ∀ 𝔮 : Ideal (MvPolynomial σ ℂ), 𝔮.IsPrime → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ 𝔮) → map (algebraMap ℚ ℂ) F ∉ 𝔮 → ((∀ g ∈ Js, map (Int.castRingHom ℂ) g ∈ 𝔮) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ map (algebraMap ℚ ℂ) (Z i) ∈ 𝔮) := by
  intro Ω _ _ σ τ F S Js e n z Z N hF hS hz hprime 𝔮 h𝔮 hker hFq
  have : IsDomain (MvPolynomial σ ℂ ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let π : MvPolynomial σ ℂ →+* FractionRing (MvPolynomial σ ℂ ⧸ 𝔮) :=
    (algebraMap (MvPolynomial σ ℂ ⧸ 𝔮) (FractionRing (MvPolynomial σ ℂ ⧸ 𝔮))).comp
      (Ideal.Quotient.mk 𝔮)
  have hπ : ∀ p, π p = 0 ↔ p ∈ 𝔮 := by
    intro p
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let _ : Algebra ℚ (FractionRing (MvPolynomial σ ℂ ⧸ 𝔮)) :=
    (π.comp ((C : ℂ →+* MvPolynomial σ ℂ).comp (algebraMap ℚ ℂ))).toAlgebra
  exact read_in_field τ F S Js e n z Z N hF hS hz hprime 𝔮 hker hFq _ π hπ

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem exists_independent_le_of_dual_min :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (μ : ℝ), 0 < μ →
      (∀ y : V, y ≠ 0 → (∀ x ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) → μ ≤ ‖y‖) →
      ∃ b : Fin (Module.finrank ℝ V) → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
        ∀ i, ‖b i‖ ≤ (Module.finrank ℝ V : ℝ) ^ (3 / 2 : ℝ) / μ := by
  intro V _ _ _ L _ _ μ hμ hdual
  set n := Module.finrank ℝ V with hn
  set c : ℝ := (n : ℝ) / μ with hc
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hμ.le
  have hspan : Submodule.span ℝ (L : Set V) = ⊤ := IsZLattice.span_top
  have main : ∀ k, k ≤ n → ∃ b : Fin k → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
      (∀ i, ‖b i‖ ^ 2 ≤ n * c ^ 2) ∧
      (∀ w ∈ Submodule.span ℝ (Set.range b), ∃ z ∈ Submodule.span ℤ (Set.range b),
        ‖w - z‖ ^ 2 ≤ k * c ^ 2 / 4) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, ?_⟩
      intro w hw
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hw0 : w = 0 := by
        rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hw
        exact hw
      simp [hw0]
    | succ k ih =>
      intro hk
      obtain ⟨b, hbL, hbli, hbn, hcov⟩ := ih (by omega)
      set W := Submodule.span ℝ (Set.range b) with hW
      set N := Submodule.span ℤ (Set.range b) with hN
      have hNL : N ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
      have hNW : Submodule.span ℝ (N : Set V) = W := Submodule.span_span_of_tower ℤ ℝ (Set.range b)
      have hWtop : W ≠ ⊤ := by
        intro h
        have h1 : Module.finrank ℝ W = k := by rw [hW, finrank_span_eq_card hbli, Fintype.card_fin]
        rw [h, finrank_top] at h1
        omega
      have hNsubW : ∀ y ∈ N, y ∈ W := fun y hy => by rw [← hNW]; exact Submodule.subset_span hy
      obtain ⟨m, hmL, hp0, hpn⟩ := Formalism.NormUnitaryCountingLemmas.exists_starProjection_ne_zero_norm_le_of_dualMinimum L hspan hμ hdual W N hNL hNW hWtop
      set p := Wᗮ.starProjection m with hp
      have hpW : p ∈ Wᗮ := Wᗮ.starProjection_apply_mem m
      have hwW : m - p ∈ W := by
        have := Wᗮ.sub_starProjection_mem_orthogonal m
        rwa [Submodule.orthogonal_orthogonal] at this
      obtain ⟨z, hzN, hz⟩ := hcov (m - p) hwW
      have hzW : z ∈ W := hNsubW z hzN
      set v := m - z with hv
      have hvdec : v = (m - p - z) + p := by rw [hv]; abel
      have hvL : v ∈ L := L.sub_mem hmL (hNL hzN)
      have hp2 : ‖p‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpn 2
      have pyth : ∀ a ∈ W, ∀ q ∈ Wᗮ, ‖a + q‖ ^ 2 = ‖a‖ ^ 2 + ‖q‖ ^ 2 := by
        intro a ha q hq
        have h0 : ⟪a, q⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal ha hq
        rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_real h0]
      have hvW : v ∉ W := by
        intro h
        apply hp0
        have hmW : m ∈ W := by
          have e : m = v + z := by rw [hv]; abel
          rw [e]
          exact W.add_mem h hzW
        have hm' : m ∈ Wᗮᗮ := by rwa [Submodule.orthogonal_orthogonal]
        exact Wᗮ.starProjection_apply_eq_zero_iff.mpr hm'
      have hsub : m - p - z ∈ W := W.sub_mem hwW hzW
      refine ⟨Fin.cons v b, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hvL
        · simpa using hbL j
      · exact linearIndependent_finCons.mpr ⟨hbli, hvW⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          rw [hvdec, pyth _ hsub _ hpW]
          have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
          nlinarith [sq_nonneg c, mul_le_mul_of_nonneg_right hkn (sq_nonneg c)]
        · simpa using hbn j
      · intro w' hw'
        rw [Fin.range_cons, Submodule.mem_span_insert] at hw'
        obtain ⟨t, u, hu, rfl⟩ := hw'
        set s := t - round t with hs
        have hs2 : s ^ 2 ≤ 1 / 4 := by
          have h := abs_sub_round t
          rw [← hs] at h
          nlinarith [abs_nonneg s, sq_abs s]
        have hq : s • (m - p - z) + u ∈ W := W.add_mem (W.smul_mem _ hsub) hu
        obtain ⟨z', hz'N, hz'⟩ := hcov (s • (m - p - z) + u) hq
        refine ⟨(round t : ℤ) • v + z', ?_, ?_⟩
        · rw [Fin.range_cons, Submodule.mem_span_insert]
          exact ⟨round t, z', hz'N, rfl⟩
        · have e : t • v + u - ((round t : ℤ) • v + z') = (s • (m - p - z) + u - z') + s • p := by
            rw [← Int.cast_smul_eq_zsmul ℝ, hs, hvdec]
            module
          rw [e, pyth _ (W.sub_mem hq (hNsubW z' hz'N)) _ (Wᗮ.smul_mem _ hpW), norm_smul,
            mul_pow, Real.norm_eq_abs, sq_abs]
          have h4 := mul_le_mul hs2 hp2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
          push_cast
          nlinarith [h4, hz']
  obtain ⟨b, hbL, hbli, hbn, -⟩ := main n le_rfl
  refine ⟨b, hbL, hbli, fun i => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast i.pos
  have key : (n : ℝ) ^ (3 / 2 : ℝ) / μ = Real.sqrt (n * c ^ 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc0, hc, Real.sqrt_eq_rpow, ← mul_div_assoc,
      ← Real.rpow_add_one hnR.ne']
    norm_num
  rw [key]
  calc ‖b i‖ = Real.sqrt (‖b i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (hbn i)

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem mollify_converges_C2_rate :
    ∀ (D : ℕ) (ρ : ReciprocityTheory.AnForm.A.Mollifier D) (V K : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ) (w : ℝ → (Fin D → ℂ) → ℝ), IsOpen V → IsCompact K → K ⊆ V → ContDiffOn ℝ ∞ u V → (∀ᶠ t in 𝓝[>] (0 : ℝ), Set.EqOn (w t) u V) → TendstoUniformlyOn (fun t => ReciprocityTheory.AnForm.A.molli ρ t (w t)) (u) (𝓝[>] 0) K ∧ TendstoUniformlyOn (fun t => fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t))) (fderiv ℝ (u)) (𝓝[>] 0) K ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)))) (fderiv ℝ (fderiv ℝ (u))) (𝓝[>] 0) K ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K, ‖fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) z - fderiv ℝ (u) z‖ ≤ M * t := by
  intro D ρ V K u w hV hK hKV hu hw
  obtain ⟨C, ε₀, hε₀, hC⟩ := ReciprocityTheory.AnForm.A.mollification_second_order D ρ V K u hV
    (by exact_mod_cast contDiffOn_infty.1 hu 3) hK hKV
  have hsmallt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε₀ / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  have key : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K,
      |ReciprocityTheory.AnForm.A.molli ρ t (w t) z - u z| ≤ C * t ∧
      ‖fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) z - fderiv ℝ u z‖ ≤ C * t ∧
      ‖fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t))) z - fderiv ℝ (fderiv ℝ u) z‖
        ≤ C * t := by
    filter_upwards [self_mem_nhdsWithin, hsmallt, hw] with t ht htε hwt z hz
    have ht0 : 0 < t := ht
    have hz2 : z ∈ ReciprocityTheory.AnForm.A.shrink V (2 * t) :=
      (hC (2 * t) (by linarith) (by linarith) z hz).1
    obtain ⟨-, h0, h1, h2⟩ := hC t ht0 (by linarith) z hz
    have hev : ReciprocityTheory.AnForm.A.molli ρ t (w t) =ᶠ[𝓝 z] ReciprocityTheory.AnForm.A.molli ρ t u := by
      filter_upwards [ball_mem_nhds z ht0] with y hy
      refine ReciprocityTheory.AnForm.A.molli_congr ρ ht0 (U := V) ?_ hwt
      intro x hx
      apply hz2
      rw [mem_closedBall] at hx ⊢
      rw [mem_ball] at hy
      linarith [dist_triangle x y z]
    rw [hev.eq_of_nhds, hev.fderiv_eq, hev.fderiv.fderiv_eq]
    exact ⟨h0, h1, h2⟩
  have hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ t in 𝓝[>] (0 : ℝ), C * t < δ := by
    intro δ hδ
    have h : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
      have h' : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    exact h.eventually (Iio_mem_nhds hδ)
  refine ⟨?_, ?_, ?_, C, key.mono fun t ht z hz => (ht z hz).2.1⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, Real.dist_eq]
    exact lt_of_le_of_lt (ht z hz).1 htδ
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (ht z hz).2.1 htδ
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (ht z hz).2.2 htδ

end GlobalTheory.CompanionTheory.Ar.Giv
end
