module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle018
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle097
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle053
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle098
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentResidueIntegrality
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

theorem _root_.GlobalTheory.T.dimension_plus_flag_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (c : Coeff l) [Fintype (CMType H)] [Fintype (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1})],
    D.dim + Fintype.card (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1}) =
      Top.dimFl (CMType H) (D.p + D.q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.dim_add_card_strictLower | exact GlobalTheory.CompanionTheory.Ar.FlagStep.dim_add_card_strictLower | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.dim_add_card_strictLower <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem _root_.GlobalTheory.T.line_bundle_from_unit_ratios : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X] (I : Type) (V : Option I → X.Opens) (T : I → Ω), IsCptGen ξ → (∀ i, ∀ q ∈ V (some i), genPt ξ ⤳ q) → (∀ q ∈ V none, ¬ genPt ξ ⤳ q) → (∀ (i j : I) (q : X) (hq : genPt ξ ⤳ q), q ∈ V (some i) → q ∈ V (some j) → unitAt ξ ⟨q, hq⟩ (T j / T i)) → (⨆ i, V i = ⊤) → ∃ g : ∀ i j, Γ(X, V i ⊓ V j)ˣ, (LB.mk (Option I) V g).IsLB ∧ ∀ (i j : I) (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ V (some i) ⊓ V (some j)), genMap ξ ⟨q, hq⟩ (X.presheaf.germ _ q h (g (some i) (some j)).val) = T j / T i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition.exists_transition | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition.exists_transition | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.Transition.exists_transition <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem closure_finiteType_over_int : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) :=
  @PositivityTheory.Xgn.coordinate_map_finite_type

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

namespace GlobalTheory.CompanionTheory.Ar.FrameUnit

theorem sum_smul_comb {R U : Type} [CommRing R] [AddCommGroup U] [Module R U] {n : ℕ}
    (C : Matrix (Fin n) (Fin n) R) (b : Fin n → U) (a : Fin n → R) :
    ∑ i, a i • ∑ k, C i k • b k = ∑ k, (Matrix.vecMul a C) k • b k := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.vecMul, dotProduct, Finset.sum_smul]

theorem comb_basis {R U : Type} [CommRing R] [AddCommGroup U] [Module R U] {n : ℕ}
    (C : Matrix (Fin n) (Fin n) R) (hC : IsUnit C.det) (b : Fin n → U) (hb : LinearIndependent R b) :
    LinearIndependent R (fun i => ∑ k, C i k • b k) ∧
      Submodule.span R (Set.range fun i => ∑ k, C i k • b k) = Submodule.span R (Set.range b) := by
  have hDC : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hC
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [sum_smul_comb] at hg
    have h0 : Matrix.vecMul g C = 0 := by
      funext k
      exact (Fintype.linearIndependent_iff.1 hb) _ hg k
    have h1 : g = Matrix.vecMul (Matrix.vecMul g C) C⁻¹ := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv C hC, Matrix.vecMul_one]
    rw [h1, h0, Matrix.zero_vecMul]
    rfl
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h : b j = ∑ i, (C⁻¹ j i) • ∑ k, C i k • b k := by
      rw [sum_smul_comb]
      have : Matrix.vecMul (C⁻¹ j) C = Pi.single j 1 := by
        have := congrFun (congrArg (fun A : Matrix (Fin n) (Fin n) R => A) hDC) j
        funext k
        have h2 := congrFun this k
        simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using h2
      rw [this]
      simp [Pi.single_apply]
    rw [SetLike.mem_coe, h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isEigFrame_of_isUnit_det : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (σ : O →+* R) (n : ℕ) (u v : Fin n → (epsAt x ⟶ G)) (C : Matrix (Fin n) (Fin n) R), IsEigFrame act x σ u → (∀ i, IsComb (C i) u (v i)) → IsUnit C.det → IsEigFrame act x σ v := by
  intro S R _ G _ _ x O _ act σ n u v C hu hv hC
  obtain ⟨L, _, _, ⟨M⟩⟩ := lieModel_exists S G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G R x L M O act.act act.hom act.one act.mul act.add
  obtain ⟨hc, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S R G x L M
  have hf' := (hf O act ρ σ hρ).2 n
  have hex : ∀ k, ∃ e, M.pt e = u k := fun k => M.onto _ (hu.1 k).1
  choose b hb using hex
  obtain rfl : u = fun k => M.pt (b k) := funext fun k => (hb k).symm
  have hvv : v = fun i => M.pt (∑ k, C i k • b k) :=
    funext fun i => (hc n (C i) b (v i)).1 (hv i)
  subst hvv
  obtain ⟨hli, hsp⟩ := (hf' b).1 hu
  obtain ⟨h1, h2⟩ := comb_basis C hC b hli
  exact (hf' _).2 ⟨h1, h2.trans hsp⟩

end GlobalTheory.CompanionTheory.Ar.FrameUnit
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange

theorem eigFrame_change : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] [Nontrivial R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (σ : O →+* R) (n r : ℕ) (u : Fin n → (epsAt x ⟶ G)) (V : Fin r → (epsAt x ⟶ G)), IsEigFrame act x σ u → IsEigFrame act x σ V → r = n ∧ ∃ C : Matrix (Fin r) (Fin n) R, (∀ i, IsComb (C i) u (V i)) ∧ ∃ C' : Matrix (Fin n) (Fin r) R, C * C' = 1 ∧ C' * C = 1 := by
  intro S R _ _ G _ _ x O _ act σ n r u V hu hV
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G R x E M O act.act act.hom act.one act.mul act.add
  obtain ⟨hc, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S R G x E M
  have hfr := (hf O act ρ σ hρ).2
  choose u' hu' using fun i => M.onto (u i) (hu.1 i).1
  choose V' hV' using fun i => M.onto (V i) (hV.1 i).1
  obtain rfl : (fun k => M.pt (u' k)) = u := funext hu'
  obtain rfl : (fun k => M.pt (V' k)) = V := funext hV'
  obtain ⟨lu, su⟩ := (hfr n u').1 hu
  obtain ⟨lV, sV⟩ := (hfr r V').1 hV
  let bu : Module.Basis (Fin n) R (eigSp ρ σ) := (Module.Basis.span lu).map (LinearEquiv.ofEq _ _ su)
  let bV : Module.Basis (Fin r) R (eigSp ρ σ) := (Module.Basis.span lV).map (LinearEquiv.ofEq _ _ sV)
  have bu_eq : ∀ i, (bu i : E) = u' i := fun i => by
    simp [bu, Module.Basis.span_apply]
  have bV_eq : ∀ i, (bV i : E) = V' i := fun i => by
    simp [bV, Module.Basis.span_apply]
  have hrn : r = n := by simpa using Fintype.card_congr (bV.indexEquiv bu)
  refine ⟨hrn, (bu.toMatrix bV).transpose, fun i => ?_, (bV.toMatrix bu).transpose, ?_, ?_⟩
  · refine (hc n _ u' _).2 ?_
    have h : V' i = ∑ k, (bu.toMatrix bV).transpose i k • u' k := by
      have h := congrArg Subtype.val (bu.sum_repr (bV i))
      rw [bV_eq] at h
      rw [← h]
      clear h hc hf hfr hu hV hu' hV' hρ
      simp only [Submodule.coe_sum, Submodule.coe_smul, bu_eq, Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    exact congrArg M.pt h
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]

end GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HolFac

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

private theorem spMap_appLE_comp_fromSpec {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W)
    (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    spMap ((x.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom) ≫ hW.fromSpec = x := by
  have key := IsAffineOpen.SpecMap_appLE_fromSpec x hW
    (isAffineOpen_top (Spec (CommRingCat.of ℂ))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at key
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, key]
  rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem exists_ringMaps_of_hol : ∀ (X : Scheme.{0}) (W : X.Opens) (hW : IsAffineOpen W) (n : ℕ)
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsHolTo (Metric.ball 0 1) p → ⊤ ≤ p 0 ⁻¹ᵁ W →
    ∃ (ρ : ℝ) (ψ : (Fin n → ℂ) → (Γ(X, W) →+* ℂ)), 0 < ρ ∧ ρ ≤ 1 ∧ Flat.IsHolPts (Metric.ball 0 1) ψ ∧
      ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (ψ z) ≫ hW.fromSpec = p ((ρ : ℂ) • z) := by
  intro X W hW n p hp h0
  classical
  obtain ⟨hSo, -⟩ := hp W 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hSo 0 ⟨Metric.mem_ball_self one_pos, h0⟩
  obtain ⟨ρ, hρpos, hρ1, hρε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ρ ≤ ε :=
    ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, min_le_left _ _⟩
  have hmaps : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (ρ : ℂ) • z ∈
      {b | b ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ⊤ ≤ (TopologicalSpace.Opens.map (p b).base).obj W} := by
    intro z hz
    apply hball
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρpos.le]
    calc ρ * ‖z‖ < ρ * 1 := mul_lt_mul_of_pos_left hz hρpos
      _ = ρ := mul_one ρ
      _ ≤ ε := hρε
  let φ : ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ W → (Γ(X, W) →+* ℂ) := fun x hx =>
    (x.appLE W ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom
  refine ⟨ρ, fun z => if hz : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W then φ _ hz else φ _ h0,
    hρpos, hρ1, ⟨Metric.isOpen_ball, ?_⟩, ?_⟩
  · intro r
    have hlin : DifferentiableOn ℂ (fun b : Fin n → ℂ => (ρ : ℂ) • b) (Metric.ball 0 1) :=
      differentiableOn_id.const_smul (ρ : ℂ)
    have hd := (hp W r).2.comp hlin hmaps
    refine hd.congr ?_
    intro z hz
    have hzS : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W := (hmaps z hz).2
    show (if hz : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W then φ _ hz else φ _ h0) r = valR (p ((ρ : ℂ) • z)) W r
    rw [dite_eq_left hzS]
    unfold valR
    rw [dite_eq_left hzS]
    rfl
  · intro z hz
    have hzS : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W := (hmaps z hz).2
    show spMap (if hz : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W then φ _ hz else φ _ h0) ≫ hW.fromSpec = _
    rw [dite_eq_left hzS]
    exact spMap_appLE_comp_fromSpec hW _ hzS

end GlobalTheory.CompanionTheory.Ar.HolFac
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.hodge_cpt_flag_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H), Fl.RootLines xdeg e → (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsDegOn Set.univ y (∑ i, xdeg (τ, i)) (∏ i, e (τ, i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isDegOn | exact GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isDegOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isDegOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.gramAt_conj_point_map_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L (spMap (starRingEnd ℂ) ≫ z) b (Γ.map (starRingEnd ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.hodge_component_reduction_at_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inr τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ (σ.comp (cmConj E).toRingHom)) 1 (regAt 𝔐.ξ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.mem_V_inr_iff_latOn | exact GlobalTheory.CompanionTheory.Ar.Flat.mem_V_inr_iff_latOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.mem_V_inr_iff_latOn <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.hodge_component_integral_over_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (s : ∀ k, J k) (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) s q → OverZp 𝔐 p q → HTL.IsLocIn (chartRing o (mseg y) s) (regAt 𝔐.ξ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.HTL.isLocIn_regAt_chartRing | exact GlobalTheory.CompanionTheory.Ar.Flat.HTL.isLocIn_regAt_chartRing | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.HTL.isLocIn_regAt_chartRing <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.hodge_component_residue_integrality : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → p ∈ S → ∀ (τ : CMType H) (σ : E →+* Ω), (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a) → ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (ds : chartRing o (mseg y) s.1), GeneratesDiff σ ds → ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) s.1 q → InFibre 𝔐.ξ p q → ∀ e : 𝔐.Li, e ∈ 𝔐.V (Sum.inl τ) q ↔ e ∈ HTL.latOn (Dc s) (GlobalTheory.CompanionTheory.Ar.HT.eigSp 𝔐.ρ σ) (ds : Ω) (regAt 𝔐.ξ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.HTStalk.mem_V_inl_iff | exact GlobalTheory.CompanionTheory.Ar.Flat.HTStalk.mem_V_inl_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.HTStalk.mem_V_inl_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.semiabelian_pullback_tangent_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)),
    ∃ φ₁ : tK.G.left ⟶ Y.t.G.left, IsGrpPullback tK.G Y.t.G (y ≫ Y.j) φ₁ ∧
      ∀ (u : epsAt (𝟙 (Sp K)) ⟶ tK.G) (v : epsAt (under y) ⟶ Xo.univ.t.G) (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G),
        SameVec Y y v v' → u.left ≫ m.φ = v.left → u.left ≫ φ₁ = v'.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_cart_to_model | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_cart_to_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_cart_to_model <;> assumption)
end
