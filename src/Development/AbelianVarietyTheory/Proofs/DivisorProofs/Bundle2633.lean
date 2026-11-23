module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle084
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle108
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UnifField

open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds

variable {p : ℕ} [Fact p.Prime]

theorem exists_field (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Algebra (FractionRing V) (PadicAlgCl p)] (hc : IsAdicComplete (maximalIdeal V) V)
    (hn : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
      (K : Set (PadicAlgCl p)) = Set.range (algebraMap (FractionRing V) (PadicAlgCl p)) := by
  haveI := hc
  obtain ⟨K, hK, e⟩ := GlobalTheory.ZH.FieldOfTest.exists_finiteDimensional_of_isComplete p
    (algebraMap (FractionRing V) (PadicAlgCl p)).fieldRange
    (by rw [RingHom.coe_fieldRange]; exact GlobalTheory.ZH.FieldOfTest.isComplete_range_fractionRing V (PadicAlgCl p) hn)
  exact ⟨K, hK, by rw [e, RingHom.coe_fieldRange]⟩

def secK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : K →+* FractionRing (intRing K) :=
  (IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).symm.toRingHom

theorem comp_secK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).comp (secK K) = algebraMap K (PadicAlgCl p) := by
  have h : algebraMap (FractionRing (intRing K)) (PadicAlgCl p) = (algebraMap K (PadicAlgCl p)).comp
      (IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (intRing K)) (RingHom.ext fun w => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
    refine (IsFractionRing.lift_algebraMap (intRing_injective K) w).trans ?_
    have := (IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).commutes w
    simp only [AlgEquiv.coe_toRingEquiv, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      RingHom.coe_coe, this]
    rfl
  rw [h, RingHom.comp_assoc]
  ext x
  show algebraMap K (PadicAlgCl p) ((IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K)
    ((IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).symm x)) = _
  rw [AlgEquiv.apply_symm_apply]

theorem exists_map (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] [Algebra (FractionRing V) (PadicAlgCl p)]
    (hn : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V)))
    (hK : Set.range (algebraMap (FractionRing V) (PadicAlgCl p)) ⊆ K) :
    ∃ (φ : V →+* intRing K) (φK : FractionRing V →+* FractionRing (intRing K)),
      φK.comp (algebraMap V _) = (algebraMap (intRing K) _).comp φ ∧
      (maximalIdeal V).map φ ≤ maximalIdeal (intRing K) ∧
      (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).comp φK =
        algebraMap (FractionRing V) (PadicAlgCl p) := by
  let jF := algebraMap (FractionRing V) (PadicAlgCl p)
  let ρK : FractionRing V →+* K := jF.codRestrict K (fun x => hK ⟨x, rfl⟩)
  have hle : ∀ v : V, ‖jF (algebraMap V _ v)‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  let φ : V →+* intRing K := (ρK.comp (algebraMap V (FractionRing V))).codRestrict (intRing K) (fun v => by
    rw [ValuationSubring.mem_comap, mem_OO_iff]
    exact hle v)
  have h3 : (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).comp ((secK K).comp ρK) = jF := by
    rw [← RingHom.comp_assoc, comp_secK]
    rfl
  refine ⟨φ, (secK K).comp ρK, ?_, ?_, h3⟩
  · refine RingHom.ext fun v => (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).injective ?_
    have e1 := RingHom.congr_fun h3 (algebraMap V _ v)
    simp only [RingHom.comp_apply] at e1 ⊢
    rw [e1]
    exact ((IsFractionRing.lift_algebraMap (intRing_injective K) (φ v)).trans rfl).symm
  · refine Ideal.map_le_iff_le_comap.2 fun m hm => ?_
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine (IsLocalRing.mem_maximalIdeal _).1 hm ?_
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h1 : jF (algebraMap V _ m) * ((y : K) : PadicAlgCl p) = 1 := by
      have := congrArg (fun w : intRing K => ((w : K) : PadicAlgCl p)) hy
      simpa [φ, ρK] using this
    have h2 : ((y : K) : PadicAlgCl p) = jF (algebraMap V _ m)⁻¹ := by
      rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right h1
    have hy1 : ‖((y : K) : PadicAlgCl p)‖ ≤ 1 := by
      have := y.2
      rw [ValuationSubring.mem_comap, mem_OO_iff] at this
      exact this
    obtain ⟨z, hz⟩ := (hn (algebraMap V _ m)⁻¹).1 (h2 ▸ hy1)
    have h0 : algebraMap V (FractionRing V) m ≠ 0 := fun h => by simp [h] at h1
    refine IsUnit.of_mul_eq_one z (IsFractionRing.injective V (FractionRing V) ?_)
    rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]

end GlobalTheory.UnifField
end

noncomputable section
namespace GlobalTheory.UnifField
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds

theorem exists_common_ring : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ x : FractionRing V', ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V' (FractionRing V'))) → ∀ s : Finset (PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra (FractionRing W) (PadicAlgCl p)), IsAdicComplete (maximalIdeal W) W ∧ (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ (↑s ⊆ Set.range (algebraMap (FractionRing W) (PadicAlgCl p))) ∧ (∀ z : PadicAlgCl p, ∃ f : Polynomial (FractionRing W), f ≠ 0 ∧ Polynomial.eval₂ (algebraMap (FractionRing W) (PadicAlgCl p)) z f = 0) ∧ (∃ (φ : V →+* W) (φK : FractionRing V →+* FractionRing W), φK.comp (algebraMap V _) = (algebraMap W _).comp φ ∧ (maximalIdeal V).map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V) (PadicAlgCl p)) ∧ (∃ (φ : V' →+* W) (φK : FractionRing V' →+* FractionRing W), φK.comp (algebraMap V' _) = (algebraMap W _).comp φ ∧ (maximalIdeal V').map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V') (PadicAlgCl p)) := by
  intro p _ V V' _ _ _ _ _ _ _ _ hc hc' hn hn' s
  obtain ⟨K₁, h₁, e₁⟩ := exists_field V hc hn
  obtain ⟨K₂, h₂, e₂⟩ := exists_field V' hc' hn'
  let K₃ := IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p))
  have h₃ : FiniteDimensional ℚ_[p] K₃ :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let K := K₁ ⊔ K₂ ⊔ K₃
  have hK : FiniteDimensional ℚ_[p] K := inferInstance
  obtain ⟨hdvr, hcW, hnW⟩ := GlobalTheory.T.padicIntermediateFieldIntRing_complete_dvr p K hK
  have l₁ : K₁ ≤ K := le_sup_left.trans le_sup_left
  have l₂ : K₂ ≤ K := le_sup_right.trans le_sup_left
  have l₃ : K₃ ≤ K := le_sup_right
  refine ⟨intRing K, inferInstance, inferInstance, hdvr, fracAlgebra K, hcW, hnW, ?_, ?_,
    exists_map K V (fun x => hn x) (fun x hx => l₁ (show x ∈ (K₁ : Set (PadicAlgCl p)) by rw [e₁]; exact hx)),
    exists_map K V' (fun x => hn' x) (fun x hx => l₂ (show x ∈ (K₂ : Set (PadicAlgCl p)) by rw [e₂]; exact hx))⟩
  · intro x hx
    have hxK : x ∈ K := l₃ (IntermediateField.subset_adjoin ℚ_[p] _ hx)
    exact ⟨secK K ⟨x, hxK⟩, (RingHom.congr_fun (comp_secK K) ⟨x, hxK⟩).trans rfl⟩
  · intro z
    have hz : IsIntegral ℚ_[p] z := Algebra.IsIntegral.isIntegral z
    refine ⟨(minpoly ℚ_[p] z).map ((secK K).comp (algebraMap ℚ_[p] K)),
      Polynomial.map_ne_zero (minpoly.ne_zero hz), ?_⟩
    rw [Polynomial.eval₂_map, ← RingHom.comp_assoc, comp_secK, ← IsScalarTower.algebraMap_eq,
      ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ_[p] z

end GlobalTheory.UnifField
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RayEv

theorem Ray.isAffineHom_q {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O D.X] {oa : D.OAct O} (Y : Ray oa) : IsAffineHom Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.RayEv

theorem GlobalTheory.RayEv.Ray.isAffineOpen_preimage_q : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type)
    [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens),
    IsAffineOpen (Y.q.left ⁻¹ᵁ V.1) := by
  intro R _ _ Q O _ _ _ oa Y V
  haveI := Y.isAffineHom_q
  exact V.2.preimage Y.q.left
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem weight_scalar_zero_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ), x' ≫ Y.q = x ≫ Y.q → (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) → c 0 = 1 := by
  intro R _ _ Q O _ _ _ oa Y S _ φ x x' c _ h
  have e : unitOn (c 0) = unitOn (1 : Sˣ) := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext (X := (Over.mk (spMap φ)).left) (V := ⊤) fun y _ => ?_
    choose J hJ using fun ψ : (Over.mk (spMap φ)).left ⟶ Q.P.A.left =>
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart Q.P.isLB (ψ y)
    have hG : Good Q.P.L y J := hJ
    have h0 := h 0 y J hG
    rw [val_corr hG (Y.Φ _ x').s_zero, val_corr hG (Y.Φ _ x).s_zero, val_one, _root_.mul_one] at h0
    have h1 : unitOn (1 : Sˣ) = 1 := map_one _
    exact h0.symm.trans ((congrArg (gm _ y ⊤) h1).trans (map_one _)).symm
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
    (congrArg Units.val e))

end GlobalTheory.Heat
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LiftDer

theorem exists_lift_of_smooth (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f]
    (U : X.Opens) (hU : IsAffineOpen U) (D : Derivation ℤ R R) :
    ∃ δ : Γ(X, U) → Γ(X, U), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ r, δ (constFn f U r) = constFn f U (D r) := by
  let g : R →+* Γ(X, U) :=
    (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hg : g.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm).bijective
    · exact HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  letI : Algebra R Γ(X, U) := g.toAlgebra
  haveI : Algebra.FormallySmooth R Γ(X, U) := hg.formallySmooth
  obtain ⟨d, hadd, hmul, hc⟩ := GlobalTheory.KS.exists_derivation_extend_of_formallySmooth R Γ(X, U) Γ(X, U)
    (RingHom.id _) (fun r => g (D r)) (fun a b => by simp) (fun a b => by
      simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, RingHom.id_apply]
      rw [RingHom.algebraMap_toAlgebra])
  exact ⟨d, hadd, hmul, fun r => hc r⟩

theorem isAffineHom_q {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : IsAffineHom Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have hc : IsAffineHom c.q.left := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst Q.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

theorem smooth_H {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : Smooth Y.H.hom := by
  have h1 : Smooth Y.q.left := Y.smooth_q
  have := Q.P.smoothDim
  have h2 : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
  rw [← Over.w Y.q]
  infer_instance

theorem exists_lift_preimage : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ ∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r) := by
  intro R _ _ Q O _ _ _ oa Y V D
  have := isAffineHom_q Y
  have := smooth_H Y
  exact exists_lift_of_smooth R Y.H.left Y.H.hom _ (V.2.preimage Y.q.left) D

end GlobalTheory.LiftDer
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

set_option autoImplicit false

namespace GlobalTheory.ShiftUnit

theorem cv_nsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    (g : GtPt D T) {y : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J) (a mu : D.X) (k : ℕ) :
    GlobalTheory.TorusModel.cv g (a + k • mu) y J * cubN (th D y J) k (cP D T a) (cP D T mu) g.b =
      GlobalTheory.TorusModel.cv g a y J * GlobalTheory.TorusModel.cv g mu y J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero, pow_zero]; rfl
  | succ k ih =>
    have e := GlobalTheory.TorusModel.cv_add g hJ (a + k • mu) mu
    rw [cPoint_add, cPoint_nsmul] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, e, pow_succ,
      ← _root_.mul_assoc, ← ih, cubN, mul_right_comm]

theorem cst_mul {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (a b : V) :
    cst q z (a * b) = cst q z a * cst q z b := by
  unfold cst; rw [map_mul]; exact gs_mul q z ⊤ trivial _ _

theorem cst_pow {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (a : V) (n : ℕ) :
    cst q z (a ^ n) = cst q z a ^ n := by
  induction n with
  | zero => unfold cst; rw [pow_zero, pow_zero, map_one, gs_eq q z ⊤ trivial, map_one, map_one]
  | succ n ih => rw [pow_succ, cst_mul, ih, pow_succ]

end GlobalTheory.ShiftUnit


open GlobalTheory.ShiftUnit in
theorem GlobalTheory.ShiftUnit.shift_unit_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Q.TauBimult → ∀ (k : ℕ) (mu α : Q.X) (xp : 𝟙_ (Over (Sp R)) ⟶ Y.H) (A₀ B₀ P₀ : R) (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1)) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left ≫ Y.q.left] ![1, -1])), xp ≫ Y.q = Q.c mu → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z A₀ * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 Z) z J).val = cst (g ≫ jK R) z B₀ * (val (Q.tau mu α) g z J).val) → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi mu) g z J).val = cst (g ≫ jK R) z P₀ * (val ψ₀ (g ≫ jK R) z J).val) → (∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ xp⁻¹))).s mu) (𝟙 _) z J = 1) → ∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) k mu α) → ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (pp : Over.mk (g ≫ jK R) ⟶ DegPre.BF Q (FractionRing R)) (yp : Over.mk (g ≫ jK R) ⟶ Y.H), (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g → pp ≫ DegPre.prB Q (FractionRing R) = yp ≫ Y.q → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z B₀ * (val u (show Z ⟶ _ from pp.left) z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 Z) z J).val * ((val e (show Z ⟶ Y.H.left from (yp * (toUnit _ ≫ xp)).left) z J) ^ k).val = cst (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 Z) z J).val := by
  intro R _ _ Q O _ _ _ oa Y hB k mu α xp A₀ B₀ P₀ ψ₀ e hxp hA hP he u hu hcorr Z g pp yp hg hpp z J hJ
  have e1 := (gen_fe (D := Q) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α).2 u hu hcorr _ pp z J hJ
  rw [uVal, val_famMult _ hJ, hg, TWM.val_powGen, TWM.val_powGen] at e1
  have c1 : pp ≫ fst (TF (FractionRing R)) Q.P.A ≫ cP Q (TF (FractionRing R)) mu = cP Q (Over.mk (g ≫ jK R)) mu := by
    rw [← Category.assoc, comp_cP]
  have jr : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
  have hr : val (Z := (Over.mk (g ≫ jK R)).left) Q.rigK g z J = val (Z := (Over.mk (g ≫ jK R)).left) Q.rig (g ≫ jK R) z J := by
    rw [DegPre.rigK, val_pull hJ, jr]
  rw [c1, hpp, hr] at e1
  have b1 : (Y.Φ (Over.mk (g ≫ jK R)) yp).b = yp ≫ Y.q := Ray.Φ_b Y yp
  have b2 : (Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).b = cP Q (Over.mk (g ≫ jK R)) mu := by
    rw [Ray.Φ_b, Category.assoc, hxp]; rfl
  have e2 : val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J *
      cubN (th Q z J) k (cP Q (Over.mk (g ≫ jK R)) α) (cP Q (Over.mk (g ≫ jK R)) mu) (yp ≫ Y.q) =
      val ((Y.Φ _ yp).s α) (𝟙 _) z J * val ((Y.Φ _ yp).s mu) (𝟙 _) z J ^ k := by
    have := cv_nsmul (Y.Φ _ yp) hJ α mu k
    rw [b1] at this
    exact this
  have e3 : val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J *
      th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu) =
      val ((Y.Φ _ yp).s α) (𝟙 _) z J * val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 _) z J := by
    have := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ yp (toUnit _ ≫ xp))).2 α z J hJ
    rw [b1, b2] at this
    exact this
  have m1 : (yp * (toUnit (Over.mk (g ≫ jK R)) ≫ xp)) * (toUnit (Over.mk (g ≫ jK R)) ≫ xp⁻¹) = yp := by
    rw [GrpObj.comp_inv, mul_inv_cancel_right]
  have e4 : val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J * val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J * val (Z := (Over.mk (g ≫ jK R)).left) Q.rig (g ≫ jK R) z J *
      val ((Y.Φ _ yp).s mu) (𝟙 _) z J = 1 := by
    have := he (Over.mk (g ≫ jK R)) (yp * (toUnit _ ≫ xp)) z J hJ
    rw [m1] at this
    exact this
  have e5 : (val (Z := (Over.mk (g ≫ jK R)).left) (Q.psi mu) g z J).val = cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val :=
    hP Z g z J hJ
  have e6 : cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (val ((Y.Φ _ (toUnit _ ≫ xp)).s α) (𝟙 _) z J).val =
      cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * (val (Z := (Over.mk (g ≫ jK R)).left) (Q.tau mu α) g z J).val :=
    hA Z g z J hJ
  have V : val (Z := (Over.mk (g ≫ jK R)).left) u pp.left z J * val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J * val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J ^ k *
      val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J ^ k =
      (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹ *
        val (Z := (Over.mk (g ≫ jK R)).left) (Q.tau mu α) g z J * val (Z := (Over.mk (g ≫ jK R)).left) (Q.psi mu) g z J ^ k * val ((Y.Φ _ yp).s α) (𝟙 _) z J := by
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul e1
    have a2 := congrArg Additive.ofMul e2
    have a4 := congrArg Additive.ofMul e4
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a1 a2 a4 ⊢
    have a4k := congrArg (k • ·) a4
    simp only [smul_add, smul_zero] at a4k
    linear_combination (norm := abel) a1 + a2 + a4k
  have Vv := congrArg Units.val V
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at Vv
  rw [e5, mul_pow] at Vv
  have e3v := congrArg Units.val e3
  simp only [Units.val_mul] at e3v
  have hθ : Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu)) * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) = 1 := Units.mul_inv _
  suffices FINAL : cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * (val (Z := (Over.mk (g ≫ jK R)).left) u pp.left z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J).val *
      ((val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J) ^ k).val =
    cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J).val by exact FINAL
  rw [cst_mul, cst_pow, Units.val_pow_eq_pow_val]
  have hu0 : IsUnit ((val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k) := (Units.isUnit _).pow k
  apply hu0.mul_right_cancel
  linear_combination cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * Vv + cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J).val * hθ - cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) * e3v - cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * (val ((Y.Φ _ yp).s α) (𝟙 _) z J).val * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) * e6
end
