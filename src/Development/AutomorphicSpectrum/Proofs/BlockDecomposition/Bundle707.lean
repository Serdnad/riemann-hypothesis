module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle252
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasChartsOfForallIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle021
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle703
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle700
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle702
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle704
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.IkLintProof

theorem integral_nonneg_real {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hn : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) : 0 ≤ (∫ x, f x ∂μ).re ∧ (∫ x, f x ∂μ).im = 0 := by
  have e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) integral_complex_ofReal
    exact Complex.ext (by simp) (by simp [(hn x).2])
  rw [e2]
  exact ⟨by simpa using integral_nonneg fun x => (hn x).1, by simp⟩

theorem lintegral_enorm_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ)
    (hn : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) : ∫⁻ x, ‖f x‖ₑ ∂μ = ‖∫ x, f x ∂μ‖ₑ := by
  have e : ∀ x, f x = ((f x).re : ℂ) := fun x => Complex.ext (by simp) (by simp [(hn x).2])
  have hr : Integrable (fun x => (f x).re) μ := hf.re
  have h0 : 0 ≤ ∫ x, (f x).re ∂μ := integral_nonneg fun x => (hn x).1
  have e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
    exact Eq.trans (integral_congr_ae (ae_of_all _ e)) integral_complex_ofReal
  have e3 : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x).re := fun x => by
    conv_lhs => rw [e x]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hn x).1]
  rw [lintegral_congr e3, ← ofReal_integral_eq_lintegral_ofReal hr (ae_of_all _ fun x => (hn x).1), e2,
    ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0]

variable {D : D7}

theorem integrable_ik {θ : InfFam D} (hθ : IsInfFam θ) {T T' : HSp D} {t n : ℕ} (d : HypDec T T' t)
    (μ : Measure (Mx D t n)) [μ.IsAddHaarMeasure] {Φ : Mx D T.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ T.rank n)
    (a : Mx D T'.rank n) : Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, h⟩ := h
    exact (GlobalTheory.RegSch.IkSchwartz.pure d hθ μ f g hg Φ h).1 a
  | zero => exact integrable_zero _ _ _
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.smul c

theorem integrable_K {T : HSp D} {n : ℕ} {K : Subgroup (GA D T)} (hK : IsCompact (K : Set (GA D T))) (ν : Measure K)
    [IsProbabilityMeasure ν] {Φ : Mx D T.rank n → ℂ} (hΦ : Continuous Φ) (x : Mx D T.rank n) :
    Integrable (fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x)) ν := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have hB : BorelSpace (GA D T) := ⟨rfl⟩
  have hKB : BorelSpace K := Subtype.borelSpace _
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hc : Continuous fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x) :=
    hΦ.comp (((continuous_mt T).comp continuous_subtype_val.inv).matrix_mul continuous_const)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end GlobalTheory.CompanionTheory.ColumnSplitting.IkLintProof

namespace GlobalTheory.CompanionTheory.ColumnSplitting


open IkLintProof in
theorem ikLint : IkLint := by
  intro D n t B W d I θ hθ M hM hn a
  haveI := I.probK
  obtain ⟨𝓕, hμ⟩ := I.cov₁
  haveI := hμ.1
  have hK := (GlobalTheory.RegSch.FirstTermCompare.hasIw_of_good d I.good).2
  have hP : projS I.νK M ∈ schwartzA θ B.rank n := GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz D θ hθ B n I.l.K hK I.νK I.probK _ hM
  have hc : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hi := fun x => integrable_K hK I.νK hc x
  have inner : ∀ x, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) x)‖ₑ ∂I.νK = ‖projS I.νK M x‖ₑ :=
    fun x => lintegral_enorm_eq (hi x) fun k => hn _
  have pos : ∀ x, 0 ≤ (projS I.νK M x).re ∧ (projS I.νK M x).im = 0 :=
    fun x => integral_nonneg_real fun k => hn _
  rw [lintegral_congr fun U => inner _]
  exact lintegral_enorm_eq (integrable_ik hθ d I.μ₁ hP a) fun U => pos _

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AbFibre

theorem isPullback_baseChange {S T : Scheme.{0}} (s : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((Over.pullback s).map f).left (pullback.fst X.hom s) (pullback.fst Y.hom s) f.left := by
  have h1 : ((Over.pullback s).map f).left ≫ pullback.snd Y.hom s = pullback.snd X.hom s := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  have h2 : ((Over.pullback s).map f).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ f.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hX : f.left ≫ Y.hom = X.hom := Over.w f
  refine IsPullback.of_right ?_ h2 (IsPullback.of_hasPullback Y.hom s).flip
  rw [h1, hX]
  exact (IsPullback.of_hasPullback X.hom s).flip

theorem exists_geometric_point {S : Scheme.{0}} (Y : Over S) (y : Y.left) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (s : Spec (.of Ω) ⟶ S) (w : ↥(pullback Y.hom s)),
      pullback.fst Y.hom s w = y := by
  let Ω := AlgebraicClosure (Y.left.residueField y)
  let g : Spec (.of Ω) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) Ω)) ≫ Y.left.fromSpecResidueField y
  let L : Spec (.of Ω) ⟶ pullback Y.hom (g ≫ Y.hom) := pullback.lift g (𝟙 _) (by simp)
  let pt : ↥(Spec (.of Ω)) := IsLocalRing.closedPoint Ω
  refine ⟨Ω, inferInstance, inferInstance, g ≫ Y.hom, L pt, ?_⟩
  change (L ≫ pullback.fst Y.hom (g ≫ Y.hom)) pt = y
  rw [pullback.lift_fst]
  exact Scheme.fromSpecResidueField_apply y _

theorem finiteOfFibres : PositivityTheory.Tls2.Zar3.Ch1.FiniteOfFibres := by
  intro R _ A B _ _ l hA hB _ hfib
  haveI := hA
  haveI := hB
  have hcomp : l.left ≫ B.hom = A.hom := Over.w l
  haveI : IsProper A.hom := IsAbelianScheme.proper (A := A)
  haveI : IsProper B.hom := IsAbelianScheme.proper (A := B)
  haveI : IsProper (l.left ≫ B.hom) := by rw [hcomp]; infer_instance
  haveI : IsProper l.left := IsProper.of_comp l.left B.hom
  have lift : ∀ {T : Scheme.{0}} (s : T ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (x : ↥A.left)
      (w : ↥(pullback B.hom s)), pullback.fst B.hom s w = l.left x →
      ∃ v, ((Over.pullback s).map l).left v = w ∧ pullback.fst A.hom s v = x := by
    intro T s x w hxw
    have h := isPullback_baseChange s l
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := pullback.fst B.hom s) (g := l.left) w x hxw
    refine ⟨h.isoPullback.inv z, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
    · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]
  have hfin : ∀ y : ↥B.left, (l.left ⁻¹' {y}).Finite := by
    intro y
    obtain ⟨Ω, _, _, s, w, hw⟩ := exists_geometric_point B y
    have hF : IsFinite ((Over.pullback s).map l).left := (hfib Ω s).1
    refine ((Scheme.Hom.finite_preimage_singleton ((Over.pullback s).map l).left w).image
      (pullback.fst A.hom s)).subset ?_
    intro x hx
    have hx' : l.left x = y := hx
    obtain ⟨v, hv1, hv2⟩ := lift s x w (by rw [hw, hx'])
    exact ⟨v, hv1, hv2⟩
  have hsurj : Surjective l.left := by
    refine ⟨fun y => ?_⟩
    obtain ⟨Ω, _, _, s, w, hw⟩ := exists_geometric_point B y
    have hS : Surjective ((Over.pullback s).map l).left := (hfib Ω s).2
    obtain ⟨v, hv⟩ := hS.surj w
    refine ⟨pullback.fst A.hom s v, ?_⟩
    have hsq := (isPullback_baseChange s l).w
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply, hv, hw]
  haveI : LocallyQuasiFinite l.left := LocallyQuasiFinite.of_finite_preimage_singleton l.left hfin
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite l.left, hsurj⟩

end GlobalTheory.CompanionTheory.AbFibre
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp)

namespace GlobalTheory.CompanionTheory.FlatFactor

theorem ext_of_affine_points {R : Type} [CommRing R] {W X : Over (Sp R)} (u v : W ⟶ X)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (t : sp (R₀ := R) S ⟶ W), t ≫ u = t ≫ v) : u = v := by
  have key : ∀ (B : CommRingCat.{0}) (j₀ : Spec B ⟶ W.left), j₀ ≫ u.left = j₀ ≫ v.left := by
    intro B j₀
    letI : Algebra R B := (Spec.preimage (j₀ ≫ W.hom)).hom.toAlgebra
    let j : sp (R₀ := R) B ⟶ W := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ W.hom)).symm
    exact congrArg CommaMorphism.left (h B j)
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext W.left.affineCover _ _ fun i => key _ _

theorem comp_eq_of_comp_eq {R : Type} [CommRing R] {A B A' : Over (Sp R)} [GrpObj A] [GrpObj B] [GrpObj A']
    (l : A ⟶ B) (f : A ⟶ A') [IsMonHom l] [IsMonHom f]
    (hk : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A), z ≫ l = 1 → z ≫ f = 1)
    {W : Over (Sp R)} (a b : W ⟶ A) (h : a ≫ l = b ≫ l) : a ≫ f = b ≫ f := by
  refine ext_of_affine_points _ _ fun S _ _ t => ?_
  have h1 : ((t ≫ a) / (t ≫ b)) ≫ l = 1 := by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, h, div_self']
  have h2 := hk S _ h1
  rw [GrpObj.div_comp, div_eq_one] at h2
  simpa using h2

theorem factorThroughFF : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  intro R _ A B A' _ _ _ l f hl hf hfl hsl hql hk
  have hc : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ A.left), g ≫ l.left = g' ≫ l.left →
      g ≫ f.left = g' ≫ f.left := by
    intro Z g g' h
    have hw : g' ≫ A.hom = g ≫ A.hom := by
      rw [← Over.w l, ← Category.assoc, ← h, Category.assoc]
    have := comp_eq_of_comp_eq l f hk (W := Over.mk (g ≫ A.hom))
      (Over.homMk g rfl) (Over.homMk g' hw) (Over.OverMorphism.ext h)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac l.left f.left hc
  let g : B ⟶ A' := Over.homMk (EffectiveEpi.desc l.left f.left hc) (by
    rw [← cancel_epi l.left, ← Category.assoc, hfac, Over.w, Over.w])
  have hg : l ≫ g = f := Over.OverMorphism.ext hfac
  refine ⟨g, ⟨?_, ?_⟩, hg⟩
  · rw [← IsMonHom.one_hom l, Category.assoc, hg, IsMonHom.one_hom]
  · have := GlobalTheory.FlatQuotient.epi_tensorHom l l
    rw [← cancel_epi (l ⊗ₘ l), ← IsMonHom.mul_hom_assoc, hg, tensorHom_comp_tensorHom_assoc, hg,
      IsMonHom.mul_hom]

end GlobalTheory.CompanionTheory.FlatFactor
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open GlobalTheory.CompanionTheory.Ar.GR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.KerFF

variable {R : Type} [CommRing R]

theorem exists_sp_iso (X : Over (Sp R)) [IsFinite X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom] :
    ∃ (F : Type) (_ : CommRing F) (_ : Algebra R F) (_ : Nonempty (sp (R₀ := R) F ≅ X)),
      Module.Finite R F ∧ Module.Projective R F := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  have f₁ : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have f₂ : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have f₃ : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at f₁
  rw [Flat.SpecMap_iff] at f₂
  rw [LocallyOfFinitePresentation.SpecMap_iff] at f₃
  letI : Algebra R Γ(X.left, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite R Γ(X.left, ⊤) := RingHom.finite_algebraMap.1 f₁
  haveI : Module.Flat R Γ(X.left, ⊤) := RingHom.flat_algebraMap_iff.1 f₂
  haveI : Algebra.FinitePresentation R Γ(X.left, ⊤) := RingHom.finitePresentation_algebraMap.1 f₃
  haveI : Module.FinitePresentation R Γ(X.left, ⊤) := Module.FinitePresentation.of_finite_of_finitePresentation _ _
  refine ⟨Γ(X.left, ⊤), inferInstance, inferInstance,
    ⟨Over.isoMk X.left.isoSpec.symm ?_⟩, inferInstance, Module.Flat.projective_of_finitePresentation⟩
  exact hφ.symm

theorem mul_comp_hom {A B T : Over (Sp R)} [GrpObj A] [GrpObj B] (u v : T ⟶ A) (l : A ⟶ B) [IsMonHom l] :
    (u * v) ≫ l = (u ≫ l) * (v ≫ l) := by
  rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem one_comp_hom {A B T : Over (Sp R)} [GrpObj A] [GrpObj B] (l : A ⟶ B) [IsMonHom l] :
    (1 : T ⟶ A) ≫ l = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem kernelFinFlat : PositivityTheory.Tls2.Zar3.Ch1.KernelFinFlat := by
  intro R _ A B _ _ l hA hB hl hfin hflat
  haveI := hA.smooth
  haveI := hB.smooth
  haveI : IsFinite l.left := hfin
  haveI : Flat l.left := hflat
  haveI : IsMonHom l := hl
  have hw : l.left ≫ B.hom = A.hom := Over.w l
  haveI : LocallyOfFinitePresentation (l.left ≫ B.hom) := by rw [hw]; infer_instance
  haveI : LocallyOfFinitePresentation l.left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp l.left B.hom
  let e : Sp R ⟶ B.left := (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left
  have he : e ≫ B.hom = 𝟙 _ := Over.w (η[B] : 𝟙_ (Over (Sp R)) ⟶ B)
  haveI : Mono e := mono_of_mono_fac he
  let X : Over (Sp R) := Over.mk (pullback.snd l.left e)
  haveI : IsFinite X.hom := inferInstanceAs (IsFinite (pullback.snd l.left e))
  haveI : Flat X.hom := inferInstanceAs (Flat (pullback.snd l.left e))
  haveI : LocallyOfFinitePresentation X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd l.left e))
  have hf : pullback.fst l.left e ≫ A.hom = X.hom := by
    rw [← hw, pullback.condition_assoc, he, Category.comp_id]
    rfl
  let f : X ⟶ A := Over.homMk (pullback.fst l.left e) hf
  have key : ∀ (T : Over (Sp R)) (z : T ⟶ A), z ≫ l = 1 ↔ ∃ t : T ⟶ X, t ≫ f = z := by
    intro T z
    have one_left : (1 : T ⟶ B).left = T.hom ≫ e := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    constructor
    · intro h
      have h' : z.left ≫ l.left = T.hom ≫ e := by
        rw [← one_left, ← h, Over.comp_left]
      refine ⟨Over.homMk (pullback.lift z.left T.hom h') (pullback.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    · rintro ⟨t, rfl⟩
      apply Over.OverMorphism.ext
      rw [one_left, ← Over.w t]
      change (t.left ≫ pullback.fst l.left e) ≫ l.left = (t.left ≫ pullback.snd l.left e) ≫ e
      rw [Category.assoc, Category.assoc, pullback.condition]
  have fmono : ∀ {T : Over (Sp R)} (t t' : T ⟶ X), t ≫ f = t' ≫ f → t = t' := by
    intro T t t' h
    apply Over.OverMorphism.ext
    rw [← cancel_mono (pullback.fst l.left e)]
    exact congrArg (fun u => u.left) h
  obtain ⟨F, iF, aF, ⟨ee⟩, hfinF, hproj⟩ := exists_sp_iso X
  have ker : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
      z ≫ l = 1 ↔ ∃ φ : F →ₐ[R] S, spMap φ ≫ (ee.hom ≫ f) = z := by
    intro S _ _ z
    rw [key]
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨φ, hφ⟩ := GlobalTheory.NatFun.spMap_surjective (k := R) (A := F) (B := S) (t ≫ ee.inv)
      exact ⟨φ, by rw [hφ]; simp⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨spMap φ ≫ ee.hom, by simp⟩
  refine ⟨F, iF, aF, ee.hom ≫ f, ⟨hproj, hfinF, ?_, ?_, ?_, ?_⟩, ker⟩
  · intro S _ _ φ φ' h
    apply GlobalTheory.NatFun.spMap_injective (k := R) (A := F) (B := S)
    have h₁ : (spMap φ ≫ ee.hom) ≫ f = (spMap φ' ≫ ee.hom) ≫ f := by simpa using h
    exact (cancel_mono ee.hom).1 (fmono _ _ h₁)
  · intro S _ _
    exact (ker S 1).1 (one_comp_hom l)
  · intro S _ _ φ φ'
    exact (ker S _).1 (by
      rw [mul_comp_hom, (ker S _).2 ⟨φ, rfl⟩, (ker S _).2 ⟨φ', rfl⟩, _root_.mul_one])
  · intro S _ _ φ
    have hz := (ker S _).2 ⟨φ, rfl⟩
    have h₂ : (spMap φ ≫ ee.hom ≫ f)⁻¹ ≫ l = 1 := by
      have h₃ := mul_comp_hom (spMap φ ≫ ee.hom ≫ f)⁻¹ (spMap φ ≫ ee.hom ≫ f) l
      rw [inv_mul_cancel, one_comp_hom, hz, _root_.mul_one] at h₃
      exact h₃.symm
    obtain ⟨χ, hχ⟩ := (ker S _).1 h₂
    exact ⟨χ, by rw [hχ, inv_mul_cancel]⟩

end GlobalTheory.CompanionTheory.Ar.KerFF
end
end

section

namespace GlobalTheory.CompanionTheory.FlatFib

theorem flatOfFibresFinite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  intro R _ X Y f h1 h0 h2 h3 H
  exact GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ X Y f h1 h0 h2 h3 H

end GlobalTheory.CompanionTheory.FlatFib
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.segment_product_jacquet_shuffle_count : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Γ i) (x i).rep) → ∀ W : List (IrrGL (k := k)), (∀ w ∈ W, w.IsCusp) → jmL W (prodIrr x hd) = (shuffleCount W (fun i => decWord (Γ i)) : ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr | exact GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr | (intros; apply GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr <;> assumption)
end

section

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

theorem _root_.GlobalTheory.T.orthogonal_of_non_isomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ¬ IsoV V V' →
    ∀ φ ∈ V, ∀ ψ ∈ V', ∫ x in F, φ.1 x * (starRingEnd ℂ) (ψ.1 x) ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV | exact GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV | (intros; apply GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_first_block_group_embedding : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n), ∃ ι : G D ρ →* G D n, Continuous ι ∧
  ∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  first | exact @GlobalTheory.CompanionTheory.FirstBlockEmb.exists_first_emb | exact GlobalTheory.CompanionTheory.FirstBlockEmb.exists_first_emb | (intros; apply GlobalTheory.CompanionTheory.FirstBlockEmb.exists_first_emb <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.partial_coefficient_sub : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F F' : G D n → ℂ), Continuous F → LeftInv (GF D n) F → Continuous F' → LeftInv (GF D n) F' → ∀ (y : Mx D ρ p) (g : G D n), pc M m ψ b₀ (F - F') (M.sh y * g) = pc M m ψ b₀ F (M.sh y * g) - pc M m ψ b₀ F' (M.sh y * g) := by
  first | exact @GlobalTheory.CompanionTheory.PcAdd.pc_sub | exact GlobalTheory.CompanionTheory.PcAdd.pc_sub | (intros; apply GlobalTheory.CompanionTheory.PcAdd.pc_sub <;> assumption)
end

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.partial_constant_term_bound : PcBound := by
  first | exact @GlobalTheory.CompanionTheory.PcB.pcBound | exact GlobalTheory.CompanionTheory.PcB.pcBound | (intros; apply GlobalTheory.CompanionTheory.PcB.pcBound <;> assumption)
end
