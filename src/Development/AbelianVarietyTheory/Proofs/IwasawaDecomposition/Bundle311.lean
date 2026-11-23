module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Analysis.Calculus.Deriv.Star
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

theorem _root_.GlobalTheory.T.holomorphicDiscreteSeries_lowestKType_smooth_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), HolShape M → LowSm M ∧ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M := by
  first | exact @GlobalTheory.HolLowOnce.lowSm_and_lowIrr | exact GlobalTheory.HolLowOnce.lowSm_and_lowIrr | (intros; apply GlobalTheory.HolLowOnce.lowSm_and_lowIrr <;> assumption)
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw TopologicalSpace

namespace GlobalTheory.ProperFinite

theorem finite_coh_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (f : X ⟶ Sp R)
    [IsProper f] (F : X.Modules) [QCoh.IsFiniteQC F] (p : ℕ) :
    letI := algebraΓOfHom f; Module.Finite R (coh F p) :=
  finite_coh_of_forall_modification f (fun Z _ ι _ => GlobalTheory.ChowLemma.exists_isProjOver_isIso_morphismRestrict R Z (ι ≫ f)) F p

theorem nonempty_perf_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R)
    [IsProper f] [Flat f] {M : LB Y} (hM : M.IsLB) : Nonempty (Perf f M) := by
  let := algebraΓOfHom f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := Y) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have := Twist.isFiniteQC_twist (F := structureModule Y) hM
  obtain ⟨K, φ, -, h2, -, h4, -, -, h7⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} (cechLB f M D) m
      (fun p hp => isZero_cechLB_X f M _ (by rw [Fintype.card_fin]; exact hp.le))
      (flat_cechLB_X f hM hD') (fun n => by
        obtain ⟨e⟩ := FieldChangeInter.nonempty_coh_equiv f hM hc hD' n
        have := finite_coh_of_isProper f (twist (structureModule Y) M) n
        exact Module.Finite.equiv e.symm)
  exact perf_of_projective_model R Y f M (Fin m) _ K φ hM hc hD' ⟨fun p => ⟨h2 p, h4 p⟩, h7⟩


open FibreLift in
theorem exists_pull_eq_smul {R : Type} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R)
    [IsProper f] [Flat f] {M : LB Y} (hM : M.IsLB) {K : Type} [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) {Y₀ : Scheme.{0}} {π : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ Sp K}
    (h : IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g))) (hH : FirstCohomologyVanishes (M.pull π))
    (x₀ : SecOnR f₀ (M.pull π) ⊤) :
    ∃ (c : R) (x : SecOnR f M ⊤), g c ≠ 0 ∧ SecOnR.pull M h.w ⊤ ⊤ le_top x = g c • x₀ := by
  obtain ⟨P⟩ := nonempty_perf_of_isProper f hM
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point R K g _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g Y₀ π f₀ h hH)
  obtain ⟨E, hE⟩ := P.sec K g Y₀ π f₀ h
  obtain ⟨v₀, hv₀⟩ := E.surjective (SecOnR.topEquiv f₀ _ x₀)
  obtain ⟨z, hz, -⟩ := hu K g hr.isUnit v₀.1 v₀.2
  obtain ⟨c, w, hc, hw⟩ := _root_.GlobalTheory.AbLaw.FibreLift.exists_common_denominator g hg z
  have hv : g ∘ B.mulVec w = g c • v₀.1 := by
    rw [← hz, ← Matrix.mulVec_smul, ← hw]
    exact funext fun j => RingHom.map_mulVec g _ _ j
  obtain ⟨s, hs⟩ := exists_sec_of_ker P (B.mulVec w)
    (by rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec])
  refine ⟨c, (SecOnR.topEquiv f M).symm s, hc, (SecOnR.topEquiv f₀ _).injective ?_⟩
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i)
    (fun i => le_pull M π (P.le i)) (fun y => Seesaw.exists_mem P (π y)) fun i => ?_
  have e₁ := Seesaw.loc_comp P h (B.mulVec w) i
  rw [hv, Seesaw.loc_smul, ← hs] at e₁
  have e₂ : Seesaw.loc P π f₀ v₀.1 i = _ := (hE v₀ i).symm
  rw [e₂, hv₀] at e₁
  refine Eq.trans ?_ ((rs_topEquiv_smul f₀ _ (g c) x₀ _ _).trans e₁).symm
  refine (rs_rs _ _ _).trans ?_
  refine (congrArg (rs Y₀ _) (SecOn.coord_pullLE π le_top _ _)).trans ?_
  refine (GlobalTheory.LB.resG_appLE π _ _ _).trans ?_
  refine (GlobalTheory.LB.appLE_resG π inf_le_right _ (s.f (P.ch i))).trans ?_
  rw [← Scheme.Hom.appLE_eq_app]
  exact (GlobalTheory.LB.appLE_resG π (P.le i) le_rfl _).symm


open AmpleNear in
theorem relAmple_near_fibre {R : Type} [CommRing R] [IsNoetherianRing R] (B : Over (Sp R)) [IsProper B.hom]
    [Flat B.hom] {L : LB B.left} (hL : L.IsLB) {K : Type} [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a)
    (hA : RelAmple ((Over.pullback (spMap g)).obj B) (L.pull (pullback.fst B.hom (spMap g)))) :
    ∃ r : R, g r ≠ 0 ∧
      RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r))).obj B)
        (L.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)))) := by
  have h := IsPullback.of_hasPullback B.hom (spMap g)
  obtain ⟨d, hd, h0, hv⟩ := exists_pw_h1Zero K _ _ (LB.isLB_pull hL _) hA
  have hv' : FirstCohomologyVanishes ((pw L d).pull (pullback.fst B.hom (spMap g))) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec ((pw L d).pull (pullback.fst B.hom (spMap g)))),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [pw_pull]
    obtain ⟨n, s, hs⟩ := hv
    exact ⟨h0, n, s, hs.1, fun i => (hs.2 i).1⟩
  obtain ⟨h1, n, s₀, hs₀, hs₀'⟩ := hv'
  choose c x hc hx using fun i => exists_pull_eq_smul B.hom (isLB_pw hL d) g hg h h1
    ((SecOnR.topEquiv _ _).symm (s₀ i))
  have e := fun i => preimage_nonzeroLocus_of_pull_eq h.w (pw L d) (x i) _ (hc i) (hx i)
  simp only [LinearEquiv.apply_symm_apply] at e
  obtain ⟨r, hr, hr'⟩ := exists_affine_loci_near B.hom (pw L d) (isLB_pw hL d)
    (fun i => SecOnR.topEquiv B.hom _ (x i)) g _ _ h (by simpa only [e] using hs₀)
    (by simpa only [e] using hs₀')
  refine ⟨r, hr, ?_⟩
  let j := Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)
  have : IsAffine (Scheme.Opens.toScheme (X := Sp R) (PrimeSpectrum.basicOpen r)) :=
    IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r
  have hv : ∃ s : Fin (n + 1) → LB.Sec (pw (L.pull (pullback.fst B.hom j)) d),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [← pw_pull]
    refine ⟨fun i => secPull (SecOnR.topEquiv B.hom _ (x i)) _, ?_⟩
    simp only [nonzeroLocus_secPull]
    exact hr' _ _ _ (IsPullback.of_hasPullback B.hom j)
  obtain ⟨s, hs, hs'⟩ := hv
  have : IsProper ((Over.pullback j).obj B).hom := inferInstanceAs (IsProper (pullback.snd B.hom j))
  exact relAmple_of_affine_loci ((Over.pullback j).obj B) _ (LB.isLB_pull hL _) hd s hs hs'


open FibreAmple in
theorem relAmple_of_geometricFibres {S : Scheme.{0}} [IsLocallyNoetherian S] (A : Over S) [IsProper A.hom]
    [Flat A.hom] {M : LB A.left} (hM : M.IsLB)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), IsAmpleLB (M.pull (pullback.fst A.hom y))) :
    RelAmple A M := by
  refine AmpleLocal.relAmple_of_locally S A M hM inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let t : Sp Γ(S, V) ⟶ S := hV.fromSpec
  obtain ⟨p, hp⟩ : s ∈ Set.range t := by rw [hV.range_fromSpec]; exact hs
  have hB := IsPullback.of_hasPullback A.hom t
  have hL := pull_isLB hM (pullback.fst A.hom t)
  have := p.isPrime
  let g := algebraMap Γ(S, V) p.asIdeal.ResidueField
  let i := algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
  have : IsProper (Over.mk (pullback.snd A.hom t)).hom := inferInstanceAs (IsProper (pullback.snd A.hom t))
  have : Flat (Over.mk (pullback.snd A.hom t)).hom := inferInstanceAs (Flat (pullback.snd A.hom t))
  have : IsProper (Over.mk (pullback.snd A.hom (spMap i ≫ spMap g ≫ t))).hom :=
    inferInstanceAs (IsProper (pullback.snd A.hom _))
  obtain ⟨r, hr, hA⟩ := relAmple_near_fibre (Over.mk (pullback.snd A.hom t)) hL g (residueField_fraction p.asIdeal)
    (relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback (pullback.snd A.hom t) (spMap g)).paste_horiz hB)
      (IsPullback.of_hasPullback A.hom _) (pull_isLB hL _) (lbIso_pull_pull hM _ _)
      ((relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hM _)).2 (hfib _ _)))
  let D : (Sp Γ(S, V)).Opens := PrimeSpectrum.basicOpen r
  have hD : p ∈ D := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  have hrange : Set.range (t ''ᵁ D).ι ⊆ Set.range (D.ι ≫ t) := by
    rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨t ''ᵁ D, ⟨p, hD, hp⟩, ?_⟩
  exact relAmple_of_factor hM ((IsPullback.of_hasPullback (pullback.snd A.hom t) D.ι).paste_horiz hB)
    (isPullback_morphismRestrict A.hom (t ''ᵁ D)).flip (IsOpenImmersion.lift (D.ι ≫ t) _ hrange)
    (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) hA

end GlobalTheory.ProperFinite
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.InfFamUnique

theorem existsUnique_infFam : ∀ D : D7, ∃! θ : InfF D, IsInfFam θ := by
  intro D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  exact ⟨θ, hθ, fun θ' h' => funext fun ρ =>
    GlobalTheory.Mem.VolEmb.infEmb_unique (tauE D ρ) (θ' ρ) (θ ρ) (h' ρ) (hθ ρ)⟩

end GlobalTheory.Mem.InfFamUnique
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.HeckeExp

variable {D : D7}


open Classical in
theorem exists_idele_at {θ : InfF D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1,
      by rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := by
    rw [← sub_eq_zero]
    refine hσ.ext _ (by rw [RingHom.map_sub, RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul, sub_self]) fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one,
      sub_eq_zero]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem arg_ne_zero (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : (AE D)ˣ) :
    θ (infPart D (x : AE D)) / (‖θ (infPart D (x : AE D))‖ : ℂ) ≠ 0 := by
  have h : θ (infPart D (x : AE D)) ≠ 0 := ((x.isUnit.map (infPart D)).map θ).ne_zero
  exact div_ne_zero h (by exact_mod_cast norm_ne_zero_iff.2 h)

theorem eq_of_zpow_eq {n m : ℤ} (h : ∀ w : ℂ, ‖w‖ = 1 → w ^ n = w ^ m) : n = m := by
  by_contra hne
  have hd : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have h1 := h (Complex.exp ((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I _)
  have h2 : Complex.exp ((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) * Complex.I) ^ (n - m) = 1 := by
    rw [zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  have hd' : ((n - m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have e : ((n - m : ℤ) : ℂ) * (((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
    rw [Complex.ofReal_div, Complex.ofReal_intCast]; field_simp
  rw [← Complex.exp_int_mul, e, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem hasInfExp_unique {χ : IdC D} {τ : D.what₂.Tau} {a a' : ℚ} (h : HasInfExp D χ τ a) (h' : HasInfExp D χ τ a') :
    a = a' := by
  obtain ⟨n, hn, ⟨θ, hθ⟩, h1⟩ := h
  obtain ⟨m, hm, -, h2⟩ := h'
  have e : n = m := eq_of_zpow_eq fun w hw => by
    obtain ⟨x, hx1, hx2⟩ := exists_idele_at hθ τ w (by rintro rfl; simp at hw)
    have ho : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' hτ => by rw [hx2, if_neg hτ]
    have e1 := h1 θ hθ x hx1 ho
    have e2 := h2 θ hθ x hx1 ho
    rw [hx2, if_pos rfl, hw, Complex.ofReal_one, div_one] at e1 e2
    exact e1.symm.trans e2
  subst e
  linarith

theorem hasInfExp_mul {χ χ' : IdC D} {τ : D.what₂.Tau} {a a' : ℚ} (h : HasInfExp D χ τ a) (h' : HasInfExp D χ' τ a') :
    HasInfExp D (χ * χ') τ (a + a') := by
  obtain ⟨n, hn, h0, h1⟩ := h
  obtain ⟨m, hm, -, h2⟩ := h'
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, h0, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h1 θ hθ x hx hτ, h2 θ hθ x hx hτ, zpow_add₀ (arg_ne_zero _ x)]

theorem hasInfExp_inv {χ : IdC D} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ τ a) : HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, h0, h1⟩ := h
  refine ⟨-n, by push_cast; rw [hn]; ring, h0, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, h1 θ hθ x hx hτ, _root_.zpow_neg]

def hcSubgroup (D : D7) : Subgroup (IdC D) where
  carrier := {χ | IsHC D χ}
  one_mem' := isHC_one D
  mul_mem' := fun {χ χ'} h h' =>
    ⟨⟨h.1.1.mul h'.1.1, fun x => by rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]⟩, fun τ =>
      (h.2 τ).elim fun _ ha => (h'.2 τ).elim fun _ ha' => ⟨_, hasInfExp_mul ha ha'⟩⟩
  inv_mem' := fun {χ} h =>
    ⟨⟨h.1.1.inv, fun x => by rw [MonoidHom.inv_apply, h.1.2, inv_one]⟩, fun τ =>
      (h.2 τ).elim fun _ ha => ⟨_, hasInfExp_inv ha⟩⟩

theorem hecke_exp_laws : ∀ D : D7, (∃ C : Subgroup (IdC D), ∀ χ, χ ∈ C ↔ IsHC D χ) ∧
    (∀ (χ : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ τ a' → a = a') ∧
    ∀ (χ χ' : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ' τ a' → HasInfExp D (χ * χ') τ (a + a') :=
  fun D => ⟨⟨hcSubgroup D, fun _ => Iff.rfl⟩, fun _ _ _ _ => hasInfExp_unique, fun _ _ _ _ _ => hasInfExp_mul⟩

end GlobalTheory.Mem.HeckeExp

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.Mem.AutConj

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.SmoothForms

def ConjAlg (A : Type) : Type := A

instance (A : Type) [Ring A] : Ring (ConjAlg A) := inferInstanceAs (Ring A)

instance (A : Type) [Ring A] [Algebra ℂ A] : Algebra ℂ (ConjAlg A) :=
  RingHom.toAlgebra' (S := ConjAlg A) ((algebraMap ℂ A).comp (starRingEnd ℂ))
    fun c x => Algebra.commutes (A := A) (star c) x

theorem exists_conj (L : Type) [LieRing L] [LieAlgebra ℝ L] :
    ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →+* UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L),
      (∀ (c : ℂ) u, π (c • u) = star c • π u) ∧
      ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
  have hs : ∀ (c : ℂ) (u : ConjAlg (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L))),
      c • u = (star c • (show UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) from u) :
        UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) := fun c u =>
    (Algebra.smul_def (A := UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) (star c) u).symm
  obtain ⟨π, hπ⟩ := GlobalTheory.EnvelopingExtension.exists_algHom_of_real L
    (ConjAlg (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)))
    (fun X => (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)))
    (fun X Y => by rw [TensorProduct.tmul_add, map_add (f := _)]; rfl)
    (fun c X => by
      refine Eq.trans ?_ (hs _ _).symm
      change UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] (c • X)) =
        star (c : ℂ) • UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)
      rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp)
    (fun X Y => by
      have : UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] ⁅X, Y⁆) =
          UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Y) -
          UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] Y) * UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [← Ring.lie_def, ← LieHom.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
      exact this)
  exact ⟨π.toRingHom, fun c u => (map_smul π c u).trans (hs c _), hπ⟩

variable {D : D7} {θ : InfF D} {V : HSp D}

def conjWord {α : Type} (w : α →₀ ℂ) : α →₀ ℂ := w.mapRange star (star_zero ℂ)

theorem conjWord_conjWord {α : Type} (w : α →₀ ℂ) : conjWord (conjWord w) = w := by
  ext a; simp [conjWord]

theorem conjWord_center (τ : D.what₂.Tau) {w : List (LieAt V τ) →₀ ℂ}
    (hw : envOf V τ w ∈ Subalgebra.center ℂ (EnvAt V τ)) :
    envOf V τ (conjWord w) ∈ Subalgebra.center ℂ (EnvAt V τ) := by
  obtain ⟨π, h1, h2⟩ := exists_conj (LieAt V τ)
  have key : ∀ w : List (LieAt V τ) →₀ ℂ, envOf V τ (conjWord w) = π (envOf V τ w) := fun w => by
    rw [envOf, envOf, conjWord, Finsupp.sum_mapRange_index (fun _ => by rw [zero_smul]), map_finsuppSum]
    refine Finsupp.sum_congr fun l _ => ?_
    rw [h1, map_list_prod, List.map_map]
    congr 2
    exact List.map_congr_left fun X _ => (h2 X).symm
  rw [Subalgebra.mem_center_iff] at hw ⊢
  intro u
  obtain ⟨w', rfl⟩ := GlobalTheory.T.enveloping_map_surjective D V τ u
  rw [← conjWord_conjWord w', key (conjWord w'), key w, ← map_mul, ← map_mul, hw]

theorem wordDer_star (e : LieInf V → GA D V) (l : List (LieInf V)) (φ : GA D V → ℂ) :
    wordDer V e l (star φ) = star (wordDer V e l φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    change lieDer V e X (wordDer V e l (star φ)) = star (lieDer V e X (wordDer V e l φ))
    rw [ih]
    funext g
    exact deriv.star

theorem envDer_star (e : LieInf V → GA D V) (τ : D.what₂.Tau) (w : List (LieAt V τ) →₀ ℂ) (φ : GA D V → ℂ) :
    envDer V e τ w (star φ) = star (envDer V e τ (conjWord w) φ) := by
  rw [envDer, envDer, conjWord, Finsupp.sum_mapRange_index (fun _ => by rw [zero_smul]), Finsupp.sum, Finsupp.sum, star_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [wordDer_star, star_smul, star_star]

theorem finiteDimensional_span_star {G : Type} {S S' : Set (G → ℂ)} (h : FiniteDimensional ℂ (Submodule.span ℂ S))
    (hs : ∀ f ∈ S', star f ∈ S) : FiniteDimensional ℂ (Submodule.span ℂ S') := by
  obtain ⟨t, ht, e⟩ := Submodule.fg_def.1 (Module.Finite.iff_fg.1 h)
  have := FiniteDimensional.span_of_finite ℂ (ht.image star)
  have key : ∀ f ∈ Submodule.span ℂ t, star f ∈ Submodule.span ℂ (star '' t) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [star_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (star '' t)) (Submodule.span_le.2 fun f hf => ?_)
  have := key (star f) (e ▸ Submodule.subset_span (hs f hf))
  rwa [star_star] at this

theorem isZFiniteAt_star {e : LieInf V → GA D V} {τ : D.what₂.Tau} {φ : GA D V → ℂ} (h : IsZFiniteAt V e τ φ) :
    IsZFiniteAt V e τ (star φ) := by
  refine finiteDimensional_span_star h ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨conjWord w, conjWord_center τ hw, by rw [envDer_star, star_star]⟩

theorem foldr_Rder_star (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (star φ) = star (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    funext g
    exact deriv.star

theorem isAutFunSm_star : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ),
    IsAutFunSm θ V φ → IsAutFunSm θ V (fun g => star (φ g)) := by
  intro D θ hθ V φ h
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hsm : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        (star φ) (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) :=
    fun k τs Xs hX g => Complex.conjCLE.contDiff.comp (h.smooth k τs Xs hX g)
  change IsAutFunSm θ V (star φ)
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.star⟩, hsm, ?_, ?_⟩
  · simp only [Pi.star_apply, h.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k h1 h2 g => by simp only [Pi.star_apply, hk k h1 h2 g]⟩
  · exact (zfin_iff R ((smooth_iff R _).1 hsm)).2 fun τ =>
      isZFiniteAt_star ((zfin_iff R ((smooth_iff R φ).1 h.smooth)).1 h.zfin τ)
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_Rder_star, Pi.star_apply, norm_star]
    exact hC g hg

end GlobalTheory.Mem.AutConj

end
end
