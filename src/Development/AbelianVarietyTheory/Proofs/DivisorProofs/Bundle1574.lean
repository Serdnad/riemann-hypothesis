module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle974
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle670
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false
noncomputable section
open scoped Classical
open GlobalTheory.ChartGlue

namespace GlobalTheory.CoverDegField

theorem exists_open_covering_charts : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  intro k _ X Y _ _ p q σ D hpP hqP hsm π hπ hη hδ
  haveI : SmoothOfRelativeDimension D p := hsm
  haveI : CharZero k := RingHom.charZero σ
  obtain ⟨U₁, t₁, hU₁, hx₁, ht⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := p) (D := D) (genericPoint X)
  obtain ⟨U₂, hU₂, hx₂, hV₂, he₂, hf₂, hr₂⟩ := GlobalTheory.T.exists_affine_etale_finite_free_nbhd k X Y p q hpP hqP π hπ hη hδ
  obtain ⟨U, hxU, hG⟩ := GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover p π D _ _ U₁ U₂ hU₁ hx₁ ⟨t₁, ht⟩ hU₂ hx₂ hV₂ he₂ hf₂ hr₂
  refine ⟨U, hxU, fun y hy => ?_, fun y hy => ?_, fun z hz c hc => ?_⟩
  · rw [GlobalTheory.encard_fibre_eq_encard_ringHom π hπ U hG.1 hG.2.1 σ y hy]
    exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank (π.app U).hom _ hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2 _
  · obtain ⟨t, ht⟩ := hG.2.2.1
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hG.1 t ht hy
    exact ⟨c, hc⟩
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hV, hzV, h, hVe⟩ := GlobalTheory.CoverDeg.etale_pullback_coords π hπ D _ U hG c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hV _ hVe (mem_ptsIn.2 hzV)
    have key : ∀ w ∈ c''.e.source, w ∈ ptsIn q σ V ∧
        ∀ a, c''.e w a = ev q σ V ((π.appLE c.U V h).hom (c.x a)) w := by
      rcases c'' with ⟨e, U', aff, x', et, ss, ae, ho⟩
      dsimp only at hU'' hx'' ⊢
      subst hU''
      have hx : x' = fun a => (π.appLE c.U U' h).hom (c.x a) := hx''
      subst hx
      exact fun w hw => ⟨ss hw, ae w hw⟩
    have hS : IsOpen (c''.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
      (PtsOver.continuous_map π hπ (spMap σ)).continuousOn.isOpen_inter_preimage c''.e.open_source
        c.e.open_source
    refine ⟨c''.restr _ hS, ⟨hc'', hc'', hc⟩, fun w hw => ⟨hw.2.2, ?_⟩⟩
    have hw' : w ∈ c''.e.source := hw.1
    obtain ⟨hwV, hwe⟩ := key w hw'
    ext a
    change c''.e w a = c.e (PtsOver.map π hπ (spMap σ) w) a
    rw [hwe a, c.apply_eq _ hw.2.2 a]
    exact valR_appLE w.1 π h hwV _

end GlobalTheory.CoverDegField
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.GenericCharts

theorem exists_etale_coords (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp F) (D : ℕ) (hp : IsProjOver p) (hd : topologicalKrullDim X = (D : ℕ)) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  obtain ⟨N, i, hi, hcomp⟩ := hp
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : LocallyOfFiniteType p := by rw [← hcomp]; infer_instance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let ψ := Spec.preimage (hU.fromSpec ≫ p)
  have hψ : Spec.map ψ = hU.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(X, U) := ψ.hom.toAlgebra
  haveI hft : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hA : Algebra.trdeg F Γ(X, U) = D :=
    GlobalTheory.GenFinite.trdeg_affineOpen_eq F p hU ⟨_, hxU⟩ D hd
  haveI : FaithfulSMul F Γ(X, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(X, U)).injective
  obtain ⟨f, hf, hs⟩ := GlobalTheory.GenericEtale.exists_away F Γ(X, U) hA
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap Γ(X, U) B)) := IsOpenImmersion.of_isLocalization f
  let i' : Sp Γ(X, U) ⟶ X := hU.fromSpec
  haveI : IsOpenImmersion i' := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hi' : i' ≫ p = spMap (algebraMap F Γ(X, U)) := hψ.symm
  let j : Sp B ⟶ X := spMap (algebraMap Γ(X, U) B) ≫ i'
  have hj : j ≫ p = spMap (algebraMap F B) := by
    rw [Category.assoc, hi', IsScalarTower.algebraMap_eq F Γ(X, U) B, ← Spec.map_comp]
    rfl
  have h₁ : SmoothOfRelativeDimension D (j ≫ p) := by
    rw [hj]
    refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension D)).mpr ?_
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).mpr hs)
  have h₂ : SmoothOfRelativeDimension D (j.opensRange.ι ≫ p) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    have : SmoothOfRelativeDimension (0 + D) (j.isoOpensRange.inv ≫ j ≫ p) := inferInstance
    rwa [zero_add] at this
  refine ModelCharts.exists_etale_coords_of_opens p D j.opensRange ?_
  exact ⟨genericPoint _, genericPoint_eq_of_isOpenImmersion j⟩

theorem exists_generic_charts : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source := by
  intro F _ X _ _ p σ D hp hd
  haveI : CharZero F := σ.charZero
  obtain ⟨U, x, hU, hη, hx⟩ := exists_etale_coords F X p D hp hd
  exact ⟨U, hη, fun y hy => (AlgChart.exists_of_etale hU x hx hy).imp fun c h => h.1⟩

end GlobalTheory.GenericCharts
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pointwise_cocycle_on_cover_extends_up_to_coboundary : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u → ∃ u' : Fn1 X, IsCoc (whole X) u' ∧ Cohom W u u' := by
  first | exact @GlobalTheory.PtExt.CocExt.cocycle_extends | exact GlobalTheory.PtExt.CocExt.cocycle_extends | (intros; apply GlobalTheory.PtExt.CocExt.cocycle_extends <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), IsAbelianScheme A → ∃ L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), ∀ c x, IsCan t c x ↔ L c = x := by
  first | exact @GlobalTheory.PtExt.exists_canMap | exact GlobalTheory.PtExt.exists_canMap | (intros; apply GlobalTheory.PtExt.exists_canMap <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.PtExt.exists_hodge_to_omega : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (G : PDivGroup p R) (t : GlobalTheory.PDivGroup.TorsionTower G A),
    ∃ ψ : PrimitiveSubmodule A →ₗ[R] G.omega,
      ∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c)) := by
  intro p _ R _ N hN A _ hA G t
  obtain ⟨L, hL⟩ := GlobalTheory.PtExt.exists_canMap R A p G t hA
  have hinj := GlobalTheory.PDivGroup.rigOfOmega_injective_of_pow p R N hN G
  have hmem : ∀ c : PrimitiveSubmodule A, (L ∘ₗ (PrimitiveSubmodule A).subtype) c ∈ LinearMap.range G.rigOfOmega := by
    intro c
    have hc : c.1.1 ∈ F1 (A.hom ≫ 𝟙 _) := c.2
    rw [hodgeFiltration_eq_range] at hc
    obtain ⟨β, hβ⟩ := hc
    have hβp : Form.cl _ β ∈ primDR A := hβ ▸ c.1.2
    obtain ⟨w, -, hw⟩ := GlobalTheory.PtExt.isCan_form R A p G t β hβp
    have hcc : (⟨_, hβp⟩ : primDR A) = c.1 := Subtype.ext hβ
    rw [hcc] at hw
    exact ⟨w, ((hL _ _).1 hw).symm⟩
  refine ⟨(LinearEquiv.ofInjective G.rigOfOmega hinj).symm ∘ₗ
    (L ∘ₗ (PrimitiveSubmodule A).subtype).codRestrict (LinearMap.range G.rigOfOmega) hmem, fun c ↦ ?_⟩
  rw [hL]
  exact (LinearEquiv.ofInjective_symm_apply G.rigOfOmega (h := hinj)
    ((L ∘ₗ (PrimitiveSubmodule A).subtype).codRestrict (LinearMap.range G.rigOfOmega) hmem c)).symm
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ArithTrdeg

theorem trdeg_functionField_eq {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ} (h : IsArithVar p D) :
    Algebra.trdeg ℤ X.functionField = D := by
  have hft := DimCoheight.finiteType_of_isAmb (MixHt.isAmb_of_isArithVar h)
  have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat

  have key : ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
      ringKrullDim Γ(X, U) =
        ((Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) : WithBot ℕ∞) := by
    intro U hU hne
    have := hft U hU
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    have : CharZero Γ(X, U) :=
      ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hc0
    have hinj : Function.Injective (algebraMap ℤ Γ(X, U)) := RingHom.injective_int _
    have : FaithfulSMul ℤ Γ(X, U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one _ hinj,
      ← DimCoheight.trdeg_eq_of_isFractionRing ℤ Γ(X, U) X.functionField]
  have hdim : ((Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) : WithBot ℕ∞) =
      ((D + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← h.dim_eq]
    apply le_antisymm
    · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
      have hU : IsAffineOpen U := hU
      rw [← key U hU ⟨⟨_, hxU⟩⟩, ← Published.dim_affineOpen hU]
      exact topologicalKrullDim_subspace_le X (U : Set X)
    · refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      have hU : IsAffineOpen U := hU
      refine ⟨(U : Set X), U.isOpen, hyU, ?_⟩
      rw [Published.dim_affineOpen hU, key U hU ⟨⟨y, hyU⟩⟩]
  have h2 : Cardinal.toENat (Algebra.trdeg ℤ X.functionField) = D := by
    have h3 : (Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) = ((D : ℕ∞) + 1) := by
      exact_mod_cast hdim
    exact (WithTop.add_right_cancel (ENat.one_ne_top) h3)
  exact Cardinal.toENat_eq_natCast.1 h2

theorem isTranscendenceBasis_functionField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    (∃ x : Fin D → X.functionField, IsTranscendenceBasis ℤ x) ∧
      ∀ x : Fin D → X.functionField, AlgebraicIndependent ℤ x → IsTranscendenceBasis ℤ x := by
  intro k _ X _ p D h
  have htr := trdeg_functionField_eq h
  refine ⟨?_, fun x hx => hx.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr]; simp)⟩
  have : FaithfulSMul ℤ X.functionField := by
    have : CharZero X.functionField := by
      have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat
      exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 hc0
    exact (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective_int _)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ X.functionField
  have hcard := hs.cardinalMk_eq_trdeg
  rw [htr] at hcard
  have : Finite s := Cardinal.lt_aleph0_iff_finite.1 (by rw [hcard]; exact Cardinal.natCast_lt_aleph0)
  have : Fintype s := Fintype.ofFinite s
  have e : s ≃ Fin D := Fintype.equivFinOfCardEq (by
    rw [Cardinal.mk_fintype] at hcard; exact_mod_cast hcard)
  exact ⟨_, hs.comp_equiv e.symm⟩

end GlobalTheory.ArithTrdeg
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LiftAmple

def chartPullPullPow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull i) (lbPow (L.pull i) n) (𝟙 T) where
  idx J := J
  le J y hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    let K : PUnit → (L.pull i).ι := J
    let K' : PUnit → (L.pull i).ι := J'
    have h₁ : i y ∈ L.U (J PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ)
    have h₂ : i y ∈ L.U (J' PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ')
    have k₁ : (𝟙 T) y ∈ powChart (L.pull i) K := mem_powChart.2 (mem_pull.2 h₁)
    have k₂ : (𝟙 T) y ∈ powChart (L.pull i) K' := mem_powChart.2 (mem_pull.2 h₂)
    refine (gm_pull_g (lbPow L n) i (𝟙 T) y J J' hJ hJ').trans ?_
    refine (gm_lbPow_g n (𝟙 T ≫ i) y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.2 h₁)
      (mem_powChart.2 h₂)).trans ?_
    refine Eq.trans ?_ (gm_lbPow_g (L := L.pull i) n (𝟙 T) y K K' k₁ k₂).symm
    rw [gm_pull_g L i (𝟙 T) y (K PUnit.unit) (K' PUnit.unit) (mem_powChart.1 k₁) (mem_powChart.1 k₂)]

theorem exists_sec_pull_pow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) (σ : (lbPow (L.pull i) n).Sec) :
    ∃ σ' : ((lbPow L n).pull i).Sec, nonzeroLocus σ' = nonzeroLocus σ :=
  ⟨chartSec (chartPullPullPow L i n) σ, nonzeroLocus_chartSec_id _ σ fun _ J hJ =>
    ⟨J, mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hJ)))⟩⟩

end GlobalTheory.LiftAmple

namespace GlobalTheory.LiftAmple

theorem exists_sec_nonzero_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ →
    ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p D hX L hL T i _ n s hn hs
  haveI : Module.Finite ℤ k := hX.finite
  haveI : IsNoetherian ℤ k := inferInstance
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (GlobalTheory.T.eventually_surjective_toPushforward_ampleLineBundle_pow k X p hX.isProjOver L hL T i)
  have hN : N₀ ≤ n * (N₀ + 1) := by nlinarith
  obtain ⟨σ', hσ'⟩ := exists_sec_pull_pow L i (n * (N₀ + 1)) (secPow s (N₀ + 1))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionPullback_of_surjective_toPushforward X T i (lbPow L (n * (N₀ + 1))) (isLB_lbPow hL.isLB _) (hN₀ _ hN) σ'
  refine ⟨n * (N₀ + 1), u, by nlinarith, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ nonzeroLocus (GlobalTheory.secPull u i) := by
    rw [hu, hσ', nonzeroLocus_secPow s (Nat.le_add_left 1 N₀), hs]; trivial
  rw [nonzeroLocus_secPull] at hz
  exact hz

end GlobalTheory.LiftAmple
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

theorem _root_.GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∃ Ω : X.Opens, (Ω : Set X).Nonempty ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Ω.toScheme := by
  first | exact @GlobalTheory.NormalOpen.exists_normal_opens | exact GlobalTheory.NormalOpen.exists_normal_opens | (intros; apply GlobalTheory.NormalOpen.exists_normal_opens <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory.GenericCoords

theorem exists_affine_etale_coords : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧
      ∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale := by
  intro k _ X _ p D h
  obtain ⟨U, t, hU, hη, he⟩ := GlobalTheory.GenericEtale.exists_etale_coords h
  exact ⟨U, hU, hη, t, he⟩

end GlobalTheory.GenericCoords
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_irreducible_zeroSet_section_closedIrreducible : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : LB X) (s : M.Sec) (C : Set X), M.IsLB → IsIrreducible C → IsClosed C → (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X)).Nonempty → ¬ C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) → ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) ∧ topologicalKrullDim C ≤ topologicalKrullDim C' + 1 := by
  first | exact @GlobalTheory.KrullZero.exists_irreducible_zero | exact GlobalTheory.KrullZero.exists_irreducible_zero | (intros; apply GlobalTheory.KrullZero.exists_irreducible_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_projectiveVariety_of_isLocalRingOfVarietyPoint : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L) (n : ℕ) (x : Fin n → L), IsLocModel c R → TrBasis c x →
  ∃ (Y : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral Y) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (e : Y.functionField ≃+* L) (y : Y),
    IsProjOver p ∧ topologicalKrullDim Y = n ∧ (∀ a, e (GlobalTheory.Cartier.constFn p a) = c a) ∧ (locRing y).map e.toRingHom = R := by
  first | exact @GlobalTheory.LocModelProj.exists_projective_of_isLocModel | exact GlobalTheory.LocModelProj.exists_projective_of_isLocModel | (intros; apply GlobalTheory.LocModelProj.exists_projective_of_isLocModel <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isTranscendenceBasis_residueField_uniformiser_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∀ (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K), (∃ x : Fin (m + 2) → L, TrBasis cL x) →
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) := by
  first | exact @GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons | exact GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons | (intros; apply GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons <;> assumption)
end
