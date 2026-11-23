module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle845
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle835
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FirstBetti

theorem finrank_homology_succ_add (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K]
    (C : CochainComplex (ModuleCat.{0} O) ℕ) [∀ i, Module.Finite O (C.X i)] (n : ℕ) :
    Module.finrank K ((((ModuleCat.extendScalars (algebraMap O K)).mapHomologicalComplex _).obj
        C).homology (n + 1))
      + Module.finrank K (LinearMap.range ((C.d n (n + 1)).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d (n + 1) (n + 2)).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X (n + 1)) := by
  let D := ((ModuleCat.extendScalars (algebraMap O K)).mapHomologicalComplex _).obj C
  have e1 := (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).toLinearEquiv
  obtain ⟨e2⟩ := GlobalTheory.Semicont.nonempty_homology_map_extendScalars_equiv K (C.sc' n (n + 1) (n + 2))
  have h := GlobalTheory.Semicont.finrank_homology_add_finrank_range
    ((C.d n (n + 1)).hom.baseChange K) ((C.d (n + 1) (n + 2)).hom.baseChange K)
    (by rw [← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero,
      LinearMap.baseChange_zero])
  rw [(e1.trans e2).finrank_eq]
  exact h

theorem smul_eq_zero_of_algebraMap_eq_zero {O : Type} [CommRing O] {K : Type} [Field K]
    [Algebra O K] {M : Type} [AddCommGroup M] [Module O M] {r : O} (hr : algebraMap O K r = 0)
    (z : K ⊗[O] M) : r • z = 0 := by
  rw [← algebraMap_smul K r z, hr, zero_smul]

theorem baseChange_eq_zero_of_ring {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {M : Type} [AddCommGroup M] [Module O M] (e : M →ₗ[O] O)
    (he : ∀ x, algebraMap O K (e x) = 0) : e.baseChange K = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply, ← mul_one (e x), ← smul_eq_mul,
      TensorProduct.tmul_smul, smul_eq_zero_of_algebraMap_eq_zero (he x)]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, LinearMap.zero_apply, add_zero]

theorem baseChange_eq_zero_of_pi {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {M : Type} [AddCommGroup M] [Module O M] {n : ℕ} (e : M →ₗ[O] (Fin n → O))
    (he : ∀ x i, algebraMap O K (e x i) = 0) : e.baseChange K = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply, pi_eq_sum_univ (e x),
      TensorProduct.tmul_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [TensorProduct.tmul_smul, smul_eq_zero_of_algebraMap_eq_zero (he x i)]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, LinearMap.zero_apply, add_zero]

end GlobalTheory.FirstBetti

namespace GlobalTheory


open FirstBetti in
theorem finrank_homology_one_two_of_dual_resolution : ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g → ∀ (f : Fin g → O), Ideal.span (Set.range f) ≠ ⊤ → IsArtinianRing (O ⧸ Ideal.span (Set.range f)) → ∀ (C : CochainComplex (ModuleCat.{0} O) ℕ), (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap) → Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O] (O ⧸ Ideal.span (Set.range f))) → ∀ (K : Type) [Field K] (φ : O →+* K), RingHom.ker φ = IsLocalRing.maximalIdeal O → Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1) = g ∧ Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2) ≤ g.choose 2 := by
  intro O _ _ g hdim f hne hart C hC hex hN K _ φ hker
  obtain ⟨eN⟩ := hN
  letI := φ.toAlgebra
  haveI : ∀ i, Module.Free O (C.X i) := fun i => (hC i).1
  haveI : ∀ i, Module.Finite O (C.X i) := fun i => (hC i).2
  have hIm : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal O := IsLocalRing.le_maximalIdeal hne
  have hIφ : ∀ x ∈ Ideal.span (Set.range f), algebraMap O K x = 0 := fun x hx => by
    have : x ∈ RingHom.ker φ := hker ▸ hIm hx
    exact this

  have hreg : RingTheory.Sequence.IsRegular O (List.ofFn f) := by
    refine GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le O g g f hdim
      (fun i => hIm (Ideal.subset_span ⟨i, rfl⟩)) ?_
    have h0 : ringKrullDim (O ⧸ Ideal.span (Set.range f)) ≤ 0 := Ring.krullDimLE_iff.1 inferInstance
    calc ringKrullDim (O ⧸ Ideal.span (Set.range f)) + (g : WithBot ℕ∞) ≤ 0 + (g : WithBot ℕ∞) :=
          add_le_add_left h0 _
      _ = g := zero_add _
  obtain ⟨e₁, e₂, hx1, hx2, he1, he2⟩ := GlobalTheory.T.koszul_resolution_three_terms_exact O g f hreg.toIsWeaklyRegular

  let ε : Module.Dual O (C.X 0) →ₗ[O] O ⧸ Ideal.span (Set.range f) :=
    eN.toLinearMap ∘ₗ (LinearMap.range (C.d 0 1).hom.dualMap).mkQ
  have hεs : Function.Surjective ε := eN.surjective.comp (Submodule.mkQ_surjective _)
  have hεx : Function.Exact (C.d 0 1).hom.dualMap ε := by
    rw [LinearMap.exact_iff, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  obtain ⟨hA, hB⟩ := GlobalTheory.T.finrank_homology_resolutions_residueField O K (O ⧸ Ideal.span (Set.range f))
    (Module.Dual O (C.X 0)) (Module.Dual O (C.X 1)) (Module.Dual O (C.X 2)) (Module.Dual O (C.X 3))
    O (Fin g → O) (Fin (g.choose 2) → O) ε (C.d 0 1).hom.dualMap (C.d 1 2).hom.dualMap
    (C.d 2 3).hom.dualMap (Ideal.span (Set.range f)).mkQ e₁ e₂ hεs hεx (hex 0) (hex 1)
    (Submodule.mkQ_surjective _) hx1 hx2

  have hz1 : e₁.baseChange K = 0 := baseChange_eq_zero_of_ring e₁ fun x => hIφ _ (he1 x)
  have hz2 : e₂.baseChange K = 0 := baseChange_eq_zero_of_pi e₂ fun x i => hIφ _ (he2 x i)
  have hk1 : Module.finrank K (LinearMap.ker (e₁.baseChange K)) = g := by
    rw [hz1, LinearMap.ker_zero, finrank_top, GlobalTheory.Semicont.finrank_baseChange_fin]
  have hr2 : Module.finrank K (LinearMap.range (e₂.baseChange K)) = 0 := by
    rw [hz2, LinearMap.range_zero, finrank_bot]
  have hc2 : Module.finrank K (K ⊗[O] (Fin (g.choose 2) → O)) = g.choose 2 :=
    GlobalTheory.Semicont.finrank_baseChange_fin _ _

  obtain ⟨r0, n0⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 0) (C.X 1) (C.d 0 1).hom
  obtain ⟨r1, n1⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 1) (C.X 2) (C.d 1 2).hom
  obtain ⟨r2, n2⟩ := GlobalTheory.T.finrank_range_baseChange_eq_finrank_range_dualMap O K (C.X 2) (C.X 3) (C.d 2 3).hom
  have k1 := LinearMap.finrank_range_add_finrank_ker ((C.d 0 1).hom.dualMap.baseChange K)
  have k2 := LinearMap.finrank_range_add_finrank_ker ((C.d 1 2).hom.dualMap.baseChange K)

  have h1 : Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1)
      + Module.finrank K (LinearMap.range ((C.d 0 1).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d 1 2).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X 1) := finrank_homology_succ_add O K C 0
  have h2 : Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2)
      + Module.finrank K (LinearMap.range ((C.d 1 2).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d 2 3).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X 2) := finrank_homology_succ_add O K C 1
  constructor <;> omega

end GlobalTheory
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory

theorem eq_chart_mul_of_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), IsOrth X x → 0 < ρ → σ 0 = 1 → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∃ w : ChartSp X, ‖w‖ < δ ∧ σ w.1 * t w.2 = g := by
  intro E _ _ _ r X x σ t ρ hx hρ hσ0 hσc hσB ht _ _ hstab δ hδ
  obtain ⟨η, hη, hB⟩ := GlobalTheory.T.diagonalPhaseFrame_small_angles E X.Ψ r δ hδ
  have hσa : ContinuousAt σ 0 := hσc.continuousAt (Metric.ball_mem_nhds 0 hρ)
  obtain ⟨ε1, hε1, κ, hκ, hC⟩ := GlobalTheory.T.exists_conj_inv_section_mul_entries_near_one E r X x σ hx hσ0 hσa η hη
  obtain ⟨ε2, hε2, hA⟩ := GlobalTheory.T.leftMul_near_one_lu_split_small_chart E r X x hx (min (min δ ρ) κ) (lt_min (lt_min hδ hρ) hκ)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun g hg => ?_⟩
  have hg1 : g ∈ grpBall (realSU X.Ψ X.Gm) ε1 := fun τ a b => lt_of_lt_of_le (hg τ a b) (min_le_left _ _)
  obtain ⟨z, hz, b, hb, hgx⟩ := hA (fun τ => (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
    (fun τ a c => lt_of_lt_of_le (hg τ a c) (min_le_right _ _))
  have hz1 : ‖z‖ < δ := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))
  have hz2 : z ∈ Metric.ball (0 : V (nd X)) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _))
  have hz3 : ‖z‖ < κ := lt_of_lt_of_le hz (min_le_right _ _)
  obtain ⟨b', hb', hσx⟩ := hσB z hz2
  have hxu : ∀ τ, IsUnit (mat x τ) := fun τ =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ))

  have hstep : ∃ b'' ∈ Bor X.Ψ r, X.lmulC (fun τ => (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b'' := by
    refine ⟨fun τ => ((mat b' τ)⁻¹ * mat b τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ?_, ?_⟩
    · have hb'u : IsUnit (mat b' τ).det := isUnit_iff_ne_zero.2 (hb' τ).1
      refine ⟨?_, fun a c hca => ?_⟩
      · show ((mat b' τ)⁻¹ * mat b τ).det ≠ 0
        rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
        exact mul_ne_zero (inv_ne_zero (hb' τ).1) (hb τ).1
      · show ((mat b' τ)⁻¹ * mat b τ) a c = 0
        letI := Matrix.invertibleOfIsUnitDet _ hb'u
        have h1 : (mat b' τ)⁻¹.BlockTriangular id :=
          Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => (hb' τ).2 a c h)
        have h2 : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
        exact (h1.mul h2) hca
    · funext τ
      have hb'u : IsUnit (mat b' τ).det := isUnit_iff_ne_zero.2 (hb' τ).1
      set S : GL (Fin r) ℂ := ((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hS
      set G : GL (Fin r) ℂ := ((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hG
      have eM : ((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ) = S⁻¹ * G := rfl
      have e1 : (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b' τ := congrFun hσx τ
      have e2 : (G : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b τ := congrFun hgx τ
      have e3 : mat x τ * mat (nmat X z) τ = (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ * (mat b' τ)⁻¹ := by
        rw [e1, Matrix.mul_assoc (mat x τ * mat (nmat X z) τ), Matrix.mul_nonsing_inv _ hb'u, Matrix.mul_one]
      show (((S⁻¹ * G : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ : Matrix (Fin r) (Fin r) ℂ) =
        mat x τ * ((mat b' τ)⁻¹ * mat b τ)
      rw [Units.val_mul, Matrix.mul_assoc, e2, e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc]
  obtain ⟨θ, hθ⟩ := hstab _ hstep
  have hP : ∀ θ₀, ∀ τ, (mat x τ)⁻¹ * ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat (phaseFrame θ₀) τ := by
    intro θ₀ τ
    have h1 : ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (phaseFrame θ₀) τ := congrFun (ht θ₀) τ
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hxu τ)), Matrix.one_mul]
  have hph : ∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η := by
    intro τ a
    have h := hC z hz3 g hg1 τ a a
    rw [hθ, hP θ τ] at h
    simpa [mat] using h
  obtain ⟨θ', hθ', hPP⟩ := hB θ hph
  have htt : t θ' = t θ := by
    apply Subtype.ext; funext τ; apply Units.ext
    have h1 := congrFun ((ht θ').trans ((congrArg (rmul x) hPP).trans (ht θ).symm)) τ
    exact (hxu τ).mul_left_injective h1
  refine ⟨(z, θ'), ?_, ?_⟩
  · rw [Prod.norm_def]; exact max_lt hz1 hθ'
  · show σ z * t θ' = g
    rw [htt, ← hθ, mul_inv_cancel_left]

end GlobalTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFg
variable (R : Type) [CommRing R]
open GlobalTheory.EtC.DiscChains

def colCx (X : SimplicialObject Spc) (a : ℕ) :
    (biChains R X).X (-(a : ℤ)) ≅ (chains R).obj (X.obj (op (SimplexCategory.mk a))) :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapIso (Iso.refl _)

theorem colCx_f (X : SimplicialObject Spc) (a b : ℕ) :
    (biChainsXIso R X a b).inv ≫ (colCx R X a).hom.f (-(b : ℤ)) =
      (chainsXIso R (X.obj (op (SimplexCategory.mk a))) b).inv := by
  have h1 := (HomologicalComplex.extendXIso (((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj ((dblF R).obj ((freeBi R).obj X))) ComplexShape.embeddingDownNat (i := a) (i' := -(a:ℤ)) rfl).inv_hom_id
  have h2 := congrArg (fun f => HomologicalComplex.Hom.f f (-(b:ℤ))) h1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h2
  erw [Iso.trans_hom, HomologicalComplex.comp_f, Iso.trans_inv]
  erw [Category.assoc, reassoc_of% h2]
  erw [Functor.mapIso_refl, Iso.refl_hom, HomologicalComplex.id_f, Category.comp_id]
  rfl

def prE (E : Spc) (a : ℕ) : (chains R).obj (disc.obj (E.obj (op (SimplexCategory.mk a)))) ⟶
    sgl (((chains R).obj E).X (-(a : ℤ))) :=
  (he R _).inv ≫ (CochainComplex.singleFunctor (Shv R) 0).map (chainsXIso R E a).inv

def prEquiv (E : Spc) (a : ℕ) : HomotopyEquiv ((chains R).obj (disc.obj (E.obj (op (SimplexCategory.mk a)))))
    (sgl (((chains R).obj E).X (-(a : ℤ)))) :=
  (he R _).symm.trans (HomotopyEquiv.ofIso ((CochainComplex.singleFunctor (Shv R) 0).mapIso (chainsXIso R E a).symm))

theorem prE_zero (E : Spc) (a : ℕ) :
    (chainsXIso R (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0).inv ≫ (prE R E a).f 0 =
      (chainsXIso R E a).inv ≫ sglι _ := by
  set P := E.obj (op (SimplexCategory.mk a))
  have hφψ : (he R P).hom.f 0 ≫ (he R P).inv.f 0 = 𝟙 _ := by
    have hc := (he R P).homotopyHomInvId.comm 0
    have hz1 : IsZero ((sgl ((free R).obj P)).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)
    have hzm : IsZero ((sgl ((free R).obj P)).X (-1)) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp), prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
      hz1.eq_of_tgt ((sgl ((free R).obj P)).d 0 1) 0, hzm.eq_of_tgt ((he R P).homotopyHomInvId.hom 0 (-1)) 0] at hc
    simp at hc
    exact hc
  have hinv0 : (chainsXIso R (disc.obj P) 0).inv ≫ (he R P).inv.f 0 = sglι ((free R).obj P) := by
    rw [← he_hom_f_zero R P, Category.assoc, hφψ, Category.comp_id]
  have h1 : sglι ((free R).obj P) ≫ ((CochainComplex.singleFunctor (Shv R) 0).map (chainsXIso R E a).inv).f 0 =
      (chainsXIso R E a).inv ≫ sglι _ := by
    change _ ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map (chainsXIso R E a).inv).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    erw [Iso.inv_hom_id_assoc]
  rw [prE, HomologicalComplex.comp_f, ← Category.assoc, hinv0, h1]

theorem mk_sum_cocycle {K L : Cx R} {n : ℤ} {ι : Type} [DecidableEq ι] (s : Finset ι) (γ : ι → Cocycle K L n) :
    ∑ j ∈ s, CohomologyClass.mk (γ j) = CohomologyClass.mk (∑ j ∈ s, γ j) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact (CohomologyClass.mk_zero (K := K) (L := L) (n := n)).symm
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ih, CohomologyClass.mk_add]

theorem pull_colIso_pbfMap (q : ℕ) [NeZero q] (P : PSh) {N : ℕ} (V₀ : disc.obj P ⟶ ofCat (glCat N))
    (hP : Inv q (disc.obj P)) (m i : ℤ) (x : ∀ j : Fin N, Ht q (disc.obj P) (m - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ (colIso P V₀).hom _ m (pbfMap q V₀ m i x) =
      ∑ j : Fin N, ((cup q (pull _ (ptimes.fst P (Fib N)) _ _ (x j))
        (cpow q (c1 q (ptimes.snd P (Fib N) ≫ Fib.line N)) j)).cast (by ring) (by ring) : Ht q (ptimes P (Fib N)) m i) := by
  unfold pbfMap

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_htCast, (a6nat_holds q).1, ← pull_comp, colIso_hom_fst, pull_cpow q a6nat_holds _ (inv_pullback_pgl q V₀ hP),
    (a6nat_holds q).2.2.1 _ _ (inv_pullback_pgl q V₀ hP), colIso_line]

theorem ev_prE_pos (E : Spc) (a : ℕ) {I : Cx R} {d : ℤ} (c : Cochain (sgl (((chains R).obj E).X (-(a : ℤ)))) I d)
    (s : ℕ) (t : ℤ) (h : -(s : ℤ) + d = t) (U : Scheme.{0})
    (x : Sx (disc.obj (E.obj (op (SimplexCategory.mk a)))) s U) (hs : 0 < s) :
    _root_.GlobalTheory.EtC.ev (R := R) ((Cochain.ofHom (prE R E a)).comp c (zero_add d)) s t h U x = 0 := by
  have hz : IsZero ((sgl (((chains R).obj E).X (-(a : ℤ)))).X (-(s : ℤ))) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ (-(s : ℤ)) (by omega)
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, hz.eq_of_src (c.v (-(s : ℤ)) t h) 0, comp_zero, comp_zero]
  exact map_zero (mapHom _ _ (freeGen R _ U x))

theorem ev_prE_zero (E : Spc) (a : ℕ) {I : Cx R} {d : ℤ} (c : Cochain (sgl (((chains R).obj E).X (-(a : ℤ)))) I d)
    (t : ℤ) (h : -((0 : ℕ) : ℤ) + d = t) (U : Scheme.{0}) (x : Sx (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0 U) :
    _root_.GlobalTheory.EtC.ev (R := R) ((Cochain.ofHom (prE R E a)).comp c (zero_add d)) 0 t h U x =
      Sec.map ((chainsXIso R E a).inv ≫ sglι _ ≫ c.v 0 t (by simpa using h)) (freeGen R _ U x) := by
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  change Sec.map ((chainsXIso R (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0).inv ≫ (prE R E a).f 0 ≫ c.v 0 t _) _ = _
  rw [reassoc_of% prE_zero R E a]
  rfl

end GlobalTheory.PBFg
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem appLE_resG_tr {A B : Scheme.{0}} (f : A ⟶ B) {O O' : B.Opens} {V V' : A.Opens} (h : O' ≤ O)
    (h' : V' ≤ V) (e : V ≤ f ⁻¹ᵁ O) (e' : V' ≤ f ⁻¹ᵁ O') (x : Γ(B, O)) :
    (f.appLE O' V' e').hom (resG B h x) = resG A h' ((f.appLE O V e).hom x) := by
  simp only [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem ι_appLE_bijective_of_image {T : Scheme.{0}} (Vo O : T.Opens) (W : Vo.toScheme.Opens)
    (e : W ≤ Vo.ι ⁻¹ᵁ O) (hW : Vo.ι ''ᵁ W = O) : Function.Bijective (Vo.ι.appLE O W e).hom := by
  rw [Scheme.Opens.ι_appLE]
  have k : (homOfLE (Set.image_subset_iff.mpr e) : Vo.ι ''ᵁ W ⟶ O) = eqToHom hW := Subsingleton.elim _ _
  rw [k]
  exact (T.presheaf.mapIso (eqToIso hW).op).commRingCatIsoToRingEquiv.bijective

theorem exists_cech_ho1_cmp : ∀ (X T : Scheme.{0}) (p : T ⟶ X), IsSeparated p → ∀ (U : X.affineOpens) (J : Type) (W : J → T.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = p ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), ∃ Φ : (∀ i i' : J, Γ(T, W i ⊓ W i')) → GlobalTheory.CechDR.HO1 ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)), (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∀ (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ k, (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ((e k) i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ((e k) i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') ((e k) i i''))) → Φ (fun i i' => c i i' - ∑ k, (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i') = Φ c - ∑ k, r k • Φ (e k)) ∧ (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → Φ c = 0 → ∃ h : ∀ i : J, Γ(T, W i), ∀ i i', c i i' = resG T inf_le_left (h i) - resG T inf_le_right (h i')) ∧ (∀ x, ∃ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) ∧ Φ c = x) ∧ ∀ (R' : Type) [CommRing R'] (σ : Γ(X, U.1) →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ T) (ι' : Y ⟶ (p ⁻¹ᵁ U.1).toScheme), ι' ≫ (p ⁻¹ᵁ U.1).ι = ι → ∀ (w : ι' ≫ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (Φ c) = 0 := by
  intro X T p hp U J W hWa hWcov hWU
  have hsepV : (p ⁻¹ᵁ U.1).toScheme.IsSeparated := by
    haveI : IsAffine U.1 := U.2
    constructor
    rw [← Limits.terminal.comp_from (p ∣_ U.1)]
    infer_instance
  have himg : ∀ O : T.Opens, O ≤ p ⁻¹ᵁ U.1 → (p ⁻¹ᵁ U.1).ι ''ᵁ ((p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) = O := by
    intro O hO
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hO
  let W' : J → (p ⁻¹ᵁ U.1).toScheme.Opens := fun i => (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ W i
  have hW' : ⨆ i, W' i = ⊤ := by
    simp only [W', ← Scheme.Hom.preimage_iSup, hWcov, Scheme.Opens.ι_preimage_self]
  have hWa' : ∀ i, IsAffineOpen (W' i) := fun i => by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (p ⁻¹ᵁ U.1).ι, himg _ (hWU i)]
    exact hWa i
  let τ : ∀ i i', Γ(T, W i ⊓ W i') →+* Γ((p ⁻¹ᵁ U.1).toScheme, W' i ⊓ W' i') := fun i i' =>
    ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom
  have hcoc : ∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) →
      IsCocycle W' (fun i i' => τ i i' (c i i')) := by
    intro c hc i i' i''
    have e := congrArg ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i' ⊓ W i'') (W' i ⊓ W' i' ⊓ W' i'') (fun _ hx => hx)).hom (hc i i' i'')
    rw [map_add (f := _), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i') (V' := W' i ⊓ W' i' ⊓ W' i'') inf_le_left inf_le_left (fun _ hx => hx) (fun _ hx => hx),
      appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i' ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i' ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fun _ hx => hx) (fun _ hx => hx),
      appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ hx => hx) (fun _ hx => hx)] at e
    exact e
  have hb2 : ∀ i i', Function.Bijective (τ i i') := fun i i' =>
    ι_appLE_bijective_of_image _ _ _ _ (himg _ (inf_le_left.trans (hWU i)))
  refine ⟨fun c => cmp ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) W' hW'
    (fun i i' => τ i i' (c i i')), ?_, ?_, ?_, ?_⟩
  · intro c hc N r e he
    have h1 := GlobalTheory.T.cechClassMap_sub_sum_const_linear Γ(X, U.1) _ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) _ W' hW'
      (fun i i' => τ i i' (c i i')) (hcoc c hc) N r (fun k i i' => τ i i' (e k i i')) (fun k => hcoc _ (he k))
    refine Eq.trans ?_ h1
    dsimp only
    congr 1
    funext i i'

    simp only [map_sub, map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact GlobalTheory.T.appLE_opensInclusion_appLE_eq_secMap_isoSpec X T p U (W i ⊓ W i') _ (W' i ⊓ W' i') (fun _ hx => hx) (r k)
  · intro c hc h0
    haveI := hsepV
    obtain ⟨h'', hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_class_eq_zero _ _ _ _ W' hW' hWa' (fun i i' => (hWa' i).inf (hWa' i')) _ (hcoc c hc) h0
    choose h hh1 using fun i => (ι_appLE_bijective_of_image (p ⁻¹ᵁ U.1) (W i) (W' i) le_rfl (himg _ (hWU i))).2 (h'' i)
    refine ⟨h, fun i i' => (hb2 i i').1 ?_⟩
    change ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom (c i i') = ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom (resG T inf_le_left (h i) - resG T inf_le_right (h i'))
    rw [map_sub, appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i) (O' := W i ⊓ W i') (V := W' i) (V' := W' i ⊓ W' i') inf_le_left inf_le_left le_rfl (fun _ hx => hx), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i') (O' := W i ⊓ W i') (V := W' i') (V' := W' i ⊓ W' i') inf_le_right inf_le_right le_rfl (fun _ hx => hx), hh1, hh1]
    exact hh i i'
  · intro x
    haveI := hsepV
    obtain ⟨c', hc', hx⟩ := GlobalTheory.T.cech_h1_class_eq_of_cocycle_affine_cover _ _ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) _ W' hW' hWa'
      (fun i i' => (hWa' i).inf (hWa' i')) (fun i i' i'' => ((hWa' i).inf (hWa' i')).inf (hWa' i'')) x
    choose c hc using fun i i' => (hb2 i i').2 (c' i i')
    refine ⟨c, ?_, ?_⟩
    · intro i i' i''
      apply (ι_appLE_bijective_of_image (p ⁻¹ᵁ U.1) (W i ⊓ W i' ⊓ W i'') (W' i ⊓ W' i' ⊓ W' i'') (fun _ hx => hx)
        (himg _ (inf_le_left.trans (inf_le_left.trans (hWU i))))).1
      rw [map_add (f := _), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i') (V' := W' i ⊓ W' i' ⊓ W' i'') inf_le_left inf_le_left (fun _ hx => hx) (fun _ hx => hx),
        appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i' ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i' ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fun _ hx => hx) (fun _ hx => hx),
        appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ hx => hx) (fun _ hx => hx)]
      have e1 := hc i i'
      have e2 := hc i' i''
      have e3 := hc i i''
      simp only [τ] at e1 e2 e3
      rw [e1, e2, e3]
      exact hc' i i' i''
    · have e : (fun i i' => τ i i' (c i i')) = c' := funext fun i => funext fun i' => hc i i'
      change cmp _ W' hW' (fun i i' => τ i i' (c i i')) = x
      rw [e]
      exact hx
  · intro R' _ σ Y s' ι ι' hι w c hc hcob
    obtain ⟨h', hh'⟩ := hcob
    subst hι
    haveI := hsepV
    refine GlobalTheory.T.cechClass_pullHO1_eq_zero_of_pullback_coboundary _ _ _ _ W' hW' hWa' R' σ Y s' ι' w _ (hcoc c hc) ⟨h', fun i i' => ?_⟩
    refine Eq.trans ?_ (hh' i i')
    rw [← Scheme.Hom.appLE_comp_appLE ι' (p ⁻¹ᵁ U.1).ι _ (W' i ⊓ W' i')]
    all_goals rfl
end GlobalTheory.CechCmp
end
end
