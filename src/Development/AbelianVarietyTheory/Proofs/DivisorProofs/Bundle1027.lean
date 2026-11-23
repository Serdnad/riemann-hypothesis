module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.WordDerivativeBlocks
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle997
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.DerivReindex

open GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials

theorem wordDeriv_eq {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (dir : Λ → W) (l : List Λ)
    (F : W → ℂ) (p : W) {n : ℕ} (h : l.length = n) :
    iteratedFDeriv ℂ n F p (fun i => dir (l.get ⟨i, by rw [h]; exact i.2⟩)) = wordDeriv dir l F p := by
  subst h; rfl

theorem wordDeriv_comp {Λ Λ' W W' : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup W'] [NormedSpace ℂ W'] (dir : Λ → W) (dir' : Λ' → W') (g : Λ → Λ')
    (T : W →L[ℂ] W') (hT : ∀ x, T (dir x) = dir' (g x)) (l : List Λ) (F : W' → ℂ)
    (hF : ContDiff ℂ l.length F) :
    wordDeriv dir l (F ∘ T) 0 = wordDeriv dir' (l.map g) F 0 := by
  rw [← wordDeriv_eq dir' (l.map g) F 0 (n := l.length) (by simp), wordDeriv,
    T.iteratedFDeriv_comp_right hF 0 le_rfl, map_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  simp [hT]

theorem derivAt0_reindex : ∀ (D : D7) (ι : Type) [Fintype ι] (e : ι ≃ D.what₂.Tau) (a b : ℕ) (F : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ F → ∀ m : DVar ι a b →₀ ℕ, derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D F (Finsupp.equivMapDomain (e.prodCongr (Equiv.refl (Fin b × Fin a))) m) := by
  intro D ι _ e a b F hF m
  have han : AnalyticOnNhd ℂ F Set.univ := GlobalTheory.SCV.analyticOnNhd_of_differentiable hF _
  set g := e.prodCongr (Equiv.refl (Fin b × Fin a)) with hg
  let T : VCx ι a b →L[ℂ] TaylorLogMetric.VC D a b :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (e.symm τ)
  have hT : ∀ x, T (coordX x) = TaylorLogMetric.coordV D (g x) := by
    intro x
    funext τ i j
    change coordX x (e.symm τ) i j = _
    unfold coordX TaylorLogMetric.coordV
    exact @if_congr _ _ _ (_) (_) _ _ _ _ (and_congr_left' e.symm_apply_eq) rfl rfl
  have hne : (m.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h1 : derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m
      = wordDeriv coordX m.toMultiset.toList (F ∘ T) 0 :=
    wordDeriv_eq coordX m.toMultiset.toList (F ∘ T) 0 (Multiset.length_toList _)
  have h2 : TaylorLogMetric.taylor D F (Finsupp.equivMapDomain g m)
      = wordDeriv (TaylorLogMetric.coordV D) (Finsupp.equivMapDomain g m).toMultiset.toList F 0 /
        (m.prod fun _ n => (n.factorial : ℂ)) := by
    rw [TaylorLogMetric.taylor, Finsupp.prod_equivMapDomain]
    congr 1
    exact wordDeriv_eq _ _ F 0 (Multiset.length_toList _)
  rw [h1, h2, mul_div_cancel₀ _ hne, wordDeriv_comp coordX (TaylorLogMetric.coordV D) g T hT _ F han.contDiff]
  refine wordDeriv_perm _ (han 0 trivial) ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_map, Finsupp.equivMapDomain_eq_mapDomain]

end GlobalTheory.DerivReindex
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_nowhereZero_section_near_of_flat_trivial : ∀ (B C : Type) [CommRing B] [IsNoetherianRing B] [CommRing C] (g : B →+* C), g.Flat → ∀ (W : (Sp B).Opens), Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : spMap g ⁻¹ᵁ W ≤ ⊤)).op).hom → ∀ (M : LB W.toScheme), M.IsLB → Triv (M.pull (spMap g ∣_ W)) → ∀ y : Sp C, ∃ (s : M.Sec) (D : (Sp C).Opens), y ∈ D ∧ ∀ z : (spMap g ⁻¹ᵁ W).toScheme, (spMap g ⁻¹ᵁ W).ι z ∈ D → (spMap g ∣_ W) z ∈ Out.nonzeroLocus s := by
  first | exact @GlobalTheory.FlatTrivSec.exists_sec_near | exact GlobalTheory.FlatTrivSec.exists_sec_near | (intros; apply GlobalTheory.FlatTrivSec.exists_sec_near <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.rough_hormander_estimate_compact_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K t0 : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), t0 ≤ t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧ n0 A la (F0 - F) ≤ ENNReal.ofReal K * n1 C la F0 := by
  first | exact @GlobalTheory.rough_hormander_compact | exact GlobalTheory.rough_hormander_compact | (intros; apply GlobalTheory.rough_hormander_compact <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

abbrev isoSpecSp (X : Scheme.{0}) [IsAffine X] : sch.obj X ⟶ sp Γ(X, ⊤) := sch.map X.isoSpec.hom

theorem pull_isoSpecSp_inv (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (X : Scheme.{0}) [IsAffine X]
    (x : H R (sch.obj X) F n) : pull R (isoSpecSp X) F n (pull R (sch.map X.isoSpec.inv) F n x) = x := by
  rw [← pull_comp, ← sch.map_comp, Iso.hom_inv_id, sch.map_id, pull_id]

theorem pull_isoSpecSp_inv' (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (X : Scheme.{0}) [IsAffine X]
    (x : H R (sp Γ(X, ⊤)) F n) : pull R (sch.map X.isoSpec.inv) F n (pull R (isoSpecSp X) F n x) = x := by
  rw [← pull_comp, ← sch.map_comp, Iso.inv_hom_id, sch.map_id, pull_id]

theorem isoSpecSp_naturality {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    isoSpecSp X ≫ spMap f.appTop.hom = sch.map f ≫ isoSpecSp Y := by
  simp only [isoSpecSp, spMap, CommRingCat.ofHom_hom, ← sch.map_comp, Scheme.isoSpec_hom_naturality]

theorem pull_isoSpecSp_naturality (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (z : H R (sp Γ(Y, ⊤)) F n) :
    pull R (sch.map f) F n (pull R (isoSpecSp Y) F n z) = pull R (isoSpecSp X) F n (pull R (spMap f.appTop.hom) F n z) := by
  rw [← pull_comp, ← pull_comp, isoSpecSp_naturality]

theorem contCone_of_affine_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i)) → ContCone R F (sch.mapCone c) := by
  intro R _ F hF I _ _ G c hc hG
  haveI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let c' : Cocone (G ⋙ Scheme.Γ.rightOp).leftOp := coconeLeftOpOfCone (Scheme.Γ.rightOp.mapCone c)
  have hc' : IsColimit c' := isColimitCoconeLeftOpOfCone _ (isLimitOfPreserves Scheme.Γ.rightOp hc)
  have hb := GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary R F hF Iᵒᵖ _ c' hc'
  intro n
  obtain ⟨h1, h2⟩ := hb n
  refine ⟨fun x => ?_, fun i y hy => ?_⟩
  · obtain ⟨j, y', hy'⟩ := h1 (pull R (sch.map c.pt.isoSpec.inv) F n x)
    refine ⟨j.unop, pull R (isoSpecSp (G.obj j.unop)) F n y', ?_⟩
    change pull R (sch.map (c.π.app j.unop)) F n _ = x
    refine (pull_isoSpecSp_naturality R F n (X := c.pt) (Y := G.obj j.unop) (c.π.app j.unop) y').trans ?_
    change pull R (isoSpecSp c.pt) F n (pull R (spMap (c'.ι.app j).hom) F n y') = x
    rw [hy', pull_isoSpecSp_inv]
  · change pull R (sch.map (c.π.app i)) F n y = 0 at hy
    let y' : H R (sp Γ(G.obj i, ⊤)) F n := pull R (sch.map (G.obj i).isoSpec.inv) F n y
    have hyy : y = pull R (isoSpecSp (G.obj i)) F n y' := (pull_isoSpecSp_inv R F n _ y).symm
    have hz : pull R (spMap (c'.ι.app (op i)).hom) F n y' = 0 := by
      have e : pull R (isoSpecSp c.pt) F n (pull R (spMap (c.π.app i).appTop.hom) F n y') = 0 := by
        rw [← pull_isoSpecSp_naturality R F n (X := c.pt) (Y := G.obj i) (c.π.app i) y', ← hyy]
        exact hy
      have e2 := congrArg (pull R (sch.map c.pt.isoSpec.inv) F n) e
      rw [pull_isoSpecSp_inv', map_zero] at e2
      exact e2
    obtain ⟨k, f, hk⟩ := h2 (op i) y' hz
    refine ⟨k.unop, f.unop, ?_⟩
    change pull R (sch.map (G.map f.unop)) F n y = 0
    rw [hyy]
    refine (pull_isoSpecSp_naturality R F n (X := G.obj k.unop) (Y := G.obj i) (G.map f.unop) y').trans ?_
    change pull R (isoSpecSp (G.obj k.unop)) F n (pull R (spMap ((G ⋙ Scheme.Γ.rightOp).leftOp.map f).hom) F n y') = 0
    rw [hk]
    exact AddMonoidHom.map_zero _

end GlobalTheory.EtC
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem sncChart_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C : SncChart f d L σ), IsPullback π f' f (spMap φ) → ∃ C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π), C'.U = π ⁻¹ᵁ C.U := by
  intro R R' _ _ φ X X' f f' π d s L σ C hP
  obtain ⟨hA, hE⟩ := GlobalTheory.T.isEtaleCoordinatesOnOpen_baseChange_preimage R R' φ X X' f f' π C.U d C.t hP C.affine C.etale
  refine ⟨{
    U := π ⁻¹ᵁ C.U
    affine := hA
    t := fun a => (π.app C.U).hom (C.t a)
    etale := hE
    c := fun i => fun _ => C.c i
    le := fun i => (π.preimage_mono (C.le i)).trans (Cartier.pull_U (L i) π fun _ => C.c i).ge
    e := C.e
    inj := C.inj
    u := fun i => Units.map (π.app C.U).hom (C.u i)
    eq := fun i => ?_ }, rfl⟩
  show resG X' _ (resG X' _ ((π.app _).hom ((σ i).f (C.c i)))) = _
  rw [Cartier.resG_resG, ← Cartier.app_resG π (C.le i), C.eq i, map_mul]
  rcases h : C.e i with _ | a
  · simp
  · simp
end LogPair
end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LogPair

theorem smooth_of_relSnc :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X)
      (σ : ∀ i, (L i).Sec), RelSnc f d L σ → SmoothOfRelativeDimension d f := by
  intro R _ X f d s L σ h
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  choose C hC using h.chart
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) (fun x => (C x).U) ?_
    fun x => ?_
  · rw [← top_le_iff]
    rintro x -
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hC x⟩
  · exact GlobalTheory.ChartSmooth.smooth_of_etale f (C x).affine (C x).t (C x).etale

end GlobalTheory.LogPair
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPer_of_isPull1_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (hM : ∀ l : u'.Λ, M l ∈ u.Λ) x x' q, IsPull1 h x x' → IsPer u.ex u.Λ x q → IsPer u'.ex u'.Λ x' fun l => q ⟨M l, hM l⟩ := by
  first | exact @GlobalTheory.CechPer.Nat.isPer_pull | exact GlobalTheory.CechPer.Nat.isPer_pull | (intros; apply GlobalTheory.CechPer.Nat.isPer_pull <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPer_unique' : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ x q' → q = q' := by
  first | exact @GlobalTheory.CechPer.isPer_unique | exact GlobalTheory.CechPer.isPer_unique | (intros; apply GlobalTheory.CechPer.isPer_unique <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unitCocycleLiftObstruction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), L.IsFun → UCoc F u → ∃ c, IsObU L α u c := by
  first | exact @GlobalTheory.LBObs.exists_isObU | exact GlobalTheory.LBObs.exists_isObU | (intros; apply GlobalTheory.LBObs.exists_isObU <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitCocycleLiftObstruction_unique : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u c' → c = c' := by
  first | exact @GlobalTheory.LBObs.isObU_unique | exact GlobalTheory.LBObs.isObU_unique | (intros; apply GlobalTheory.LBObs.isObU_unique <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitCocycle_lift_of_obstruction_eq_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), IsObU L α u 0 → ∃ v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ, (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), (v T T'' (a ≫ b) : L.B T'') = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') := by
  first | exact @GlobalTheory.LBLift.lift_of_isObU_zero | exact GlobalTheory.LBLift.lift_of_isObU_zero | (intros; apply GlobalTheory.LBLift.lift_of_isObU_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitCocycleLiftObstruction_pullback_naturality : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (u' : ∀ (T T' : C') (_ : T ⟶ T'), (F'.obj T')ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsLift L' n l → L.IsNat L' n l → (∀ T T' a, (u' T T' a : F'.obj T') = n.α T' (u _ _ (n.G.map a) : F.obj (n.G.obj T'))) → IsObU L α u c → IsObU L' α u' ((extMap R₁ n).pull2 c) := by
  first | exact @GlobalTheory.LBObs.isObU_pull | exact GlobalTheory.LBObs.isObU_pull | (intros; apply GlobalTheory.LBObs.isObU_pull <;> assumption)
end
