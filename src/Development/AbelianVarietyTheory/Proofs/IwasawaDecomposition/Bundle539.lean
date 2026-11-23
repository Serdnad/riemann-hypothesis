module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle533
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle113
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle524
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle245
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle002
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle006
public import Formalism.LocalToGlobal.HermitianColumns.FullSym
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroOfSetting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocIdOfCompletions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef


open IsLocalRing in
theorem isEtaleCompletion_comp_bij {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : Toroidal.IsEtaleCompletion φ) : Toroidal.IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

end GlobalTheory.TorRef
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.TorRef TensorProduct

namespace GlobalTheory.NormalBaseChange

theorem exists_etale_of_isEtaleCompletion (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [IsNoetherianRing A] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (het : IsEtaleCompletion (algebraMap A R)) (hfu : ((residue R).comp (algebraMap A R)).FormallyUnramified) :
    ∃ g : AdicCompletion (maximalIdeal A) A →+* R, g.comp (algebraMap A _) = algebraMap A R ∧
      @Algebra.Etale _ R _ _ g.toAlgebra := by
  obtain ⟨hflat, hmap, hfin⟩ := het
  set h := algebraMap A R with hh
  let D := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing D := AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : IsAdicComplete ((maximalIdeal A).map h) R := by rw [hmap]; infer_instance
  obtain ⟨g, hg⟩ := exists_adicCompletion_ringHom_extend (maximalIdeal A) h
  letI : Algebra D R := g.toAlgebra
  have hgA : ∀ a, g (algebraMap A D a) = h a := fun a => RingHom.congr_fun hg a
  have hmA : (maximalIdeal D).map (algebraMap D R) = maximalIdeal R := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    change (maximalIdeal A).map (g.comp _) = _
    rw [hg, hmap]
  haveI : IsLocalHom (algebraMap D R) := ((local_hom_tfae _).out 1 3).mpr hmA.le
  have hres : ((residue R).comp g).Finite :=
    RingHom.Finite.of_comp_finite (f := algebraMap A D) (by rw [RingHom.comp_assoc, hg]; exact hfin)
  haveI : Module.Finite D (R ⧸ (maximalIdeal D).map (algebraMap D R)) := by
    rw [← RingHom.finite_algebraMap]
    show ((Ideal.Quotient.mk _).comp (algebraMap D R)).Finite
    rw [hmA]
    exact hres
  haveI : IsHausdorff ((maximalIdeal D).map (algebraMap D R)) R := by rw [hmA]; infer_instance
  haveI : Module.Finite D R := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal D)
  haveI : Module.Flat D R := by
    refine LocalFlat.flat_of_relationsLift R (I := maximalIdeal D)
      (hmA.le.trans (maximalIdeal_le_jacobson _)) fun n => ?_
    haveI : Module.Flat A R := RingHom.flat_algebraMap_iff.mp hflat
    have fg := (maximalIdeal A).fg_of_isNoetherianRing
    have hkerA : ∀ x : D, AdicCompletion.evalₐ (maximalIdeal A) n x = 0 ↔ x ∈ maximalIdeal D ^ n := by
      intro x
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A,
        ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
      constructor
      · intro h0
        rw [← AdicCompletion.factor_evalₐ_eq_eval _ x (by simp), h0, map_zero]
      · intro h0
        rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (by simp), h0, map_zero]
    have hmapn : (maximalIdeal D ^ n).map (algebraMap D R) = (maximalIdeal A ^ n).map (algebraMap A R) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_map]
      change (maximalIdeal A ^ n).map (g.comp _) = _
      rw [hg]
    refine LocalFlat.relationsLift_of_square
      (AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom
      (Ideal.Quotient.mk ((maximalIdeal A ^ n).map (algebraMap A R)))
      (algebraMap _ _) (AdicCompletion.surjective_evalₐ _ n) Ideal.Quotient.mk_surjective ?_ ?_ ?_ ?_
    · ext x
      exact (hkerA x)
    · rw [Ideal.mk_ker, hmapn]
    · ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal A) n x)
      have hx : x - algebraMap A D a ∈ maximalIdeal D ^ n := by
        rw [← hkerA, map_sub, ← ha, AlgHom.commutes, sub_eq_zero]
        rfl
      have hx' : algebraMap D R x - h a ∈ (maximalIdeal A ^ n).map (algebraMap A R) := by
        rw [← hmapn, ← hgA]
        rw [show algebraMap D R x - g (algebraMap A D a) = algebraMap D R (x - algebraMap A D a) from
          (map_sub g _ _).symm]
        exact Ideal.mem_map_of_mem _ hx
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← ha]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, eq_comm, Ideal.Quotient.eq]
      exact hx'
    · rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R (maximalIdeal A ^ n)).toLinearEquiv
  haveI : Algebra.FormallyUnramified D (ResidueField R) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    have e : (algebraMap D (ResidueField R)).comp (algebraMap A D) = (residue R).comp h := by
      rw [← hg]; rfl
    exact RingHom.FormallyUnramified.of_comp (f := algebraMap A D) (by rw [e]; exact hfu)
  haveI : Algebra.FormallyUnramified D R :=
    GlobalTheory.EtaleCompletionNormal.formallyUnramified_of_map_maximalIdeal hmA
  haveI : Algebra.FinitePresentation D R :=
    (Algebra.FinitePresentation.of_finiteType (R := D) (A := R)).1 inferInstance
  exact ⟨g, hg, Algebra.Etale.of_formallyUnramified_of_flat⟩

end GlobalTheory.NormalBaseChange
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.AnForm.R

namespace GlobalTheory.ProjBlowup

theorem exists_blowup_graph {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (hσ : Generates J σ) :
    ∃ (G : Scheme.{0}) (b : G ⟶ X) (c : G ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      FinalTheorems.Blowup b J ∧ Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  have : IsProper (PSpace.str R m) := isProper_str R m
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let U : X.Opens := J.support.compl
  have hU : ∀ x : U.toScheme, U.ι x ∉ J.support := fun x => x.2
  have htop : ∀ {W : Scheme.{0}} (g : W ⟶ X), (∀ w, g w ∉ J.support) → J.comap g = ⊤ := fun g hg =>
    eq_top_of_forall_notMem _ fun w hw => hg w ((mem_support_comap J g w).1 hw)
  obtain ⟨φ, hφ, hφσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X U _ L m σ U.ι (U.ι ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ U.ι hσ)
    (by rw [htop _ hU]; exact effCartier_top _)
  let b := graphClosure.fst s (PSpace.str R m) U.ι φ hφ.symm
  let c := graphClosure.snd s (PSpace.str R m) U.ι φ hφ.symm
  let j := graphClosure.incl s (PSpace.str R m) U.ι φ hφ.symm
  have hjb : j ≫ b = U.ι := graphClosure.incl_fst ..
  have hjc : j ≫ c = φ := graphClosure.incl_snd ..
  have hbc : Proportional σ b c := .of_comp j (by rwa [hjb, hjc])
  have hc : b ≫ s = c ≫ PSpace.str R m := graphClosure.condition ..
  have hι : pullback.lift b c hc = graphClosure.ι s (PSpace.str R m) U.ι φ hφ.symm := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]; rfl
    · rw [pullback.lift_snd]; rfl
  refine ⟨_, b, c, hc, ⟨GlobalTheory.T.effCartier_of_proportional_sections R X _ U _ L m σ b c j (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ b hσ) hbc inferInstance
    inferInstance fun t => ?_, fun W g hg => ?_⟩, hbc, ?_⟩
  · rw [mem_support_comap, ← Scheme.Hom.comp_apply, hjb]; exact hU t
  · obtain ⟨ψ, hψ, hψσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X W _ L m σ g (g ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ g hσ) hg
    have hd := GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier W _ hg
    let d := Scheme.Opens.ι (X := W) (J.comap g).support.compl
    have hdU : ∀ t, (d ≫ g) t ∉ J.support := fun t ht => t.2 ((mem_support_comap J g _).2 ht)
    let w := IsOpenImmersion.lift U.ι (d ≫ g) (by
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨_, hdU t⟩, rfl⟩)
    have hw : w ≫ U.ι = d ≫ g := IsOpenImmersion.lift_fac ..
    have hw' : d ≫ ψ = w ≫ φ := GlobalTheory.T.eq_of_proportional_to_generating_sections R X _ L m σ (d ≫ g) _ _ (htop _ hdU ▸ GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ (d ≫ g) hσ)
      (by rw [Category.assoc, hψ, Category.assoc, hφ, reassoc_of% hw]) (hψσ.comp d) (hw ▸ hφσ.comp w)
    have key : ∀ h : W ⟶ _, h ≫ b = g → d ≫ h = w ≫ j := fun h hh => by
      have H := graphClosure.isPullback_incl s (PSpace.str R m) U.ι φ hφ.symm
      have e : w ≫ U.ι = (d ≫ h) ≫ b := by rw [hw, Category.assoc, hh]
      have h1 := H.lift_fst w (d ≫ h) e
      rw [Category.comp_id] at h1
      rw [← H.lift_snd w (d ≫ h) e, h1]
    have hl := graphClosure.lift_fst s (PSpace.str R m) U.ι φ hφ.symm g ψ hψ.symm d w hw.symm hw'
    exact ⟨_, hl, fun h hh => hom_ext_of_isSchemeTheoreticallyDominant d b ((key h hh).trans (key _ hl).symm)
      (hh.trans hl.symm)⟩
  · rw [hι]; infer_instance

theorem exists_iso_of_blowup {X X' G : Scheme.{0}} (J : X.IdealSheafData) (b : X' ⟶ X) (b₀ : G ⟶ X)
    (hb : FinalTheorems.Blowup b J) (hb₀ : FinalTheorems.Blowup b₀ J) : ∃ e : X' ⟶ G, IsIso e ∧ e ≫ b₀ = b := by
  obtain ⟨e, he, -⟩ := hb₀.2 X' b hb.1
  obtain ⟨e', he', -⟩ := hb.2 G b₀ hb₀.1
  have h1 : e ≫ e' = 𝟙 X' := by
    obtain ⟨_, -, hu⟩ := hb.2 X' b hb.1
    rw [hu (e ≫ e') (by show (e ≫ e') ≫ b = b; rw [Category.assoc, he', he]), hu (𝟙 X') (Category.id_comp _)]
  have h2 : e' ≫ e = 𝟙 G := by
    obtain ⟨_, -, hu⟩ := hb₀.2 G b₀ hb₀.1
    rw [hu (e' ≫ e) (by show (e' ≫ e) ≫ b₀ = b₀; rw [Category.assoc, he, he']), hu (𝟙 G) (Category.id_comp _)]
  exact ⟨e, ⟨e', h1, h2⟩, he⟩

theorem exists_closedImmersion_of_generates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X X' : Scheme.{0})
    (s : X ⟶ Sp R) (J : X.IdealSheafData)
    (b : X' ⟶ X) (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), IsProjOver s → FinalTheorems.Blowup b J →
    GlobalTheory.ProjBlowup.Generates J σ → ∃ (c : X' ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      GlobalTheory.ProjBlowup.Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  intro R _ _ X X' s J b L₀ m σ hs hb hσ
  obtain ⟨G, b₀, c₀, hc₀, hb₀, hp₀, hi₀⟩ := exists_blowup_graph s hs J L₀ m σ hσ
  obtain ⟨e, he, heb⟩ := exists_iso_of_blowup J b b₀ hb hb₀
  have hc : b ≫ s = (e ≫ c₀) ≫ PSpace.str R m := by rw [← heb, Category.assoc, Category.assoc, hc₀]
  have hp : Proportional σ b (e ≫ c₀) := heb ▸ hp₀.comp e
  have hl : pullback.lift b (e ≫ c₀) hc = e ≫ pullback.lift b₀ c₀ hc₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, heb]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  refine ⟨e ≫ c₀, hc, hp, ?_⟩
  rw [hl]
  infer_instance

end GlobalTheory.ProjBlowup
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLiftSmooth

theorem lift_growth (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeilDatumO ψ S T χS χT om)
    (θ : InfFam D) (hθ : IsInfFam θ) (hS : ∀ τ, (gramAt D S τ).PosDef)
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (F : GA D S → X) (hF : Continuous F) (hFi : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h)
    (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) :
    ∃ N : ℕ, ∀ L : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ x : GA D T,
      ∃ c : ℝ, ∀ g ∈ GinfC T, ‖lift om ν 𝓕 (fun h => L (F h)) (x * g)‖ ≤ c * normInf θ T g ^ N := by
  obtain ⟨N, hN⟩ := GlobalTheory.ThetaGrowth.thetaKO_growth ψ S T χS χT om hW θ hθ
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hS
  have hfin : ν 𝓕 < ⊤ := lt_top_iff_ne_top.2 (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D S ν 𝓕 ⟨hν, h𝓕⟩).2
  refine ⟨N, fun L hL x => ?_⟩
  let b := Module.finBasis ℂ X
  choose c hc using fun j => hN (L (b j)) (hL _) x C hC
  have hco : ∀ j, ∃ M : ℝ, ∀ h ∈ C, ‖b.repr (F h) j‖ ≤ M := fun j =>
    hC.exists_bound_of_continuousOn
      (((b.coord j).continuous_of_finiteDimensional.comp hF).continuousOn)
  choose M hM using hco
  refine ⟨(∑ j, M j * c j) * ν.real 𝓕, fun g hg => ?_⟩
  have key : ∀ h, ‖thetaKO om h (x * g) (L (F h))‖ ≤ (∑ j, M j * c j) * normInf θ T g ^ N := by
    intro h
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
    have hinv := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hW (L (F k)) (hL _)).2 γ hγ 1
      (one_mem _) k (x * g)
    rw [one_mul] at hinv
    rw [hFi γ hγ, hinv]
    have e : thetaKO om k (x * g) (L (F k)) = ∑ j, b.repr (F k) j * thetaKO om k (x * g) (L (b j)) := by
      conv_lhs => rw [← b.sum_repr (F k)]

      simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hM j k hk) (hc j k hk g hg) (norm_nonneg _) ((norm_nonneg _).trans (hM j k hk))
  calc _ ≤ (∑ j, M j * c j) * normInf θ T g ^ N * ν.real 𝓕 :=
        norm_setIntegral_le_of_norm_le_const hfin fun h _ => key h
    _ = _ := by ring

theorem lift_smooth_growth_killed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn T θ (lift om ν 𝓕 fun h => L (F h)) ∧ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsUnifModGrowth T θ (lift om ν 𝓕 fun h => L (F h)) ∧ ∀ τ (Z : Mt T.rank), (∀ x h, RderC θ T τ Z (fun g => thetaKO om h g (L x)) = 0) → RderC θ T τ Z (lift om ν 𝓕 fun h => L (F h)) = 0 := by
  intro D ψ S T χS χT om hW θ hθ hS X _ _ _ L hL F hF hFi ν 𝓕 hν h𝓕
  have hder := fun (L : X →ₗ[ℂ] (WO S T → ℂ)) (hL : ∀ x, IsThetaFunO ψ S T (L x)) =>
    GlobalTheory.T.definiteThetaLift_continuous_invariant_hasDerivAt D ψ S T χS χT om hW θ hθ hS X L hL F hF hFi ν 𝓕 hν h𝓕
  refine ⟨?_, ?_, ?_⟩
  · refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ T
      {φ | ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧ φ = lift om ν 𝓕 fun h => L' (F h)}
      ?_ ?_ _ ⟨L, hL, rfl⟩
    · rintro φ ⟨L', hL', rfl⟩
      exact (hder L' hL').1.1
    · rintro φ ⟨L', hL', rfl⟩ τ Y hY
      obtain ⟨L'', h1, -, h3⟩ := (hder L' hL').2 τ Y hY
      exact ⟨_, ⟨L'', h1, rfl⟩, h3⟩
  · obtain ⟨N, hN⟩ := lift_growth D ψ S T χS χT om hW θ hθ hS X F hF hFi ν 𝓕 hν h𝓕
    refine ⟨N, fun l hl x => ?_⟩
    have hw : ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧
        List.foldr (fun p f => Rder θ T p.1 p.2 f) (lift om ν 𝓕 fun h => L (F h)) l
          = lift om ν 𝓕 fun h => L' (F h) := by
      induction l with
      | nil => exact ⟨L, hL, rfl⟩
      | cons p l ih =>
        obtain ⟨L', hL', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
        obtain ⟨L'', h1, -, h3⟩ := (hder L' hL').2 p.1 p.2 (hl p List.mem_cons_self)
        refine ⟨L'', h1, ?_⟩
        rw [List.foldr_cons, e]
        exact funext fun g => (h3 g).deriv
    obtain ⟨L', hL', e⟩ := hw
    rw [e]
    exact hN L' hL' x
  · intro τ Z hZ
    obtain ⟨hY₁, hY₂⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
    obtain ⟨L₁, -, a₁, b₁⟩ := (hder L hL).2 τ _ hY₁
    obtain ⟨L₂, -, a₂, b₂⟩ := (hder L hL).2 τ _ hY₂
    funext g
    have hp : ∀ h, thetaKO om h g (L₁ (F h)) = -Complex.I * thetaKO om h g (L₂ (F h)) := by
      intro h
      have := congrFun (hZ (F h) h) g
      simp only [RderC, Rder, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [(a₁ (F h) h g).deriv, (a₂ (F h) h g).deriv] at this
      linear_combination this
    simp only [RderC, Rder, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [(b₁ g).deriv, (b₂ g).deriv]
    simp only [lift, hp, integral_const_mul]
    ring

end GlobalTheory.DefLiftSmooth
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.LocalPack

namespace GlobalTheory.Mem.ConcreteRecord

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

variable (D : D7) (L0 : LevelData D)

def Companion : Prop :=
  ∀ u, ∃ 𝔞 : Ideal (𝓞 D.host.E), (L0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
    (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (L0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0

def stdBasis (hS : Formalism.L2.Herm.StdTied D) : GL (Fin D.R.k) D.host.E := Classical.choose (exists_stdB_of_tied D hS)

theorem stdBasis_std (hS : Formalism.L2.Herm.StdTied D) : Cmp.StdB D (stdBasis D hS) := Classical.choose_spec (exists_stdB_of_tied D hS)

def placeId (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))) :=
  locIdStd D u w hg (Classical.choose (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)) (stdBasis D hS) (stdBasis_std D hS)
    (Classical.choose (hC u)) (Classical.choose_spec (hC u))

def embK (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w] :=
  Classical.choose (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg))

def embAlg (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w] :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))

theorem embK_embAlg (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (z : D.what₂.LL) : embK D L0 u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) = lamV (embAlg D L0 u w hg) (D.what₂.embLL z) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))).1 z

def awayChar (T : ∀ u : D.what₂.Word, Forms0 D u) (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ :=
  Classical.choose (GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ hψ u w hg)

def gatOf (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (sc : Scale) (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    GAtP (D.what₂.places.resChar w) :=
  (packC D (fun u => L0 u) I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc 1 (D.what₂.places.resChar w))


theorem gatOf_d (T : ∀ u : D.what₂.Word, Forms0 D u) (hJ : ∀ u, Joint0 L0 u (T u)) (I) (ψ) (sc : Scale) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (gatOf D L0 I ψ sc u w h).d = Module.finrank ℂ (D.mem u).A.Mu0 := by
  have e := GlobalTheory.ClassRank.pack_d_eq D L0 T hJ u w h (I u w h) (ψ u w h) (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc 1 (D.what₂.places.resChar w))
  rw [pack_eq] at e
  exact e

section Main

variable {D L0}


theorem posOK_placeId (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0)
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (packC D (fun u => L0 u) (placeId D L0 hS hC) ψ u w hg).posOK (embK D L0 u w hg) (embAlg D L0 u w hg) := by
  have e := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg)))).2 (ψ u w hg)
  unfold LocPack.posOK at e ⊢
  exact e

end Main

section Main2

variable {D L0}

end Main2

theorem gPlTiedS_of {X : D7} {Gt : GatTies X} (H0 : Formalism.L2.Herm.Herm0 X)
    (hpl : ∀ u w hg (v : Fin (X.gat u w hg).P.nV) (s : Fin ((X.gat u w hg).P.n' v)) (x : 𝓞 X.host.F),
      x ∈ ((H0.g u w hg).pl v).1.asIdeal ↔
        (0 : WithTop ℤ) < X.what₂.places.val w (tauLL X (Gt.gat_pos u w hg ⟨v, s⟩) (algebraMap X.host.F X.host.E (x : X.host.F))))
    (B : Formalism.L2.Herm.HermColsCh X) (gS : Formalism.L2.Herm.SymmetricGroupCompatibility X B) (hB : B.lev0 = H0.lev0) (hg : HEq gS H0.g) :
    Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces X B gS Gt := by
  obtain ⟨l, g⟩ := H0
  dsimp only at hB hg hpl
  subst hB
  obtain rfl := eq_of_heq hg
  exact hpl

end GlobalTheory.Mem.ConcreteRecord
end
end
