module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle114
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle057
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle117
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.mem_weilGroupAtPlace_of_fixes_extension : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v') (σ : Weil h) (g : _root_.Formalism.ConjugateSelfDual.G L Ω), (∀ z : Ω, (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) z = g z) → g ∈ Weil h' := by
  first | exact @GlobalTheory.AboveL.mem_weil_of_fix | exact GlobalTheory.AboveL.mem_weil_of_fix | (intros; apply GlobalTheory.AboveL.mem_weil_of_fix <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.KS

theorem isProjOver_pow : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsProjOver s → ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB →
    Out.RelAmple A L → ∀ k : ℕ, IsProjOver ((GlobalTheory.KS.pow A k).hom ≫ s) := by
  intro R _ _ X s hs A _ _ hA L hL hamp k
  obtain ⟨hsp, H, hH⟩ := (GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs
  have p := Out.powIsPowGrp A k
  have hrel : Out.RelAmple (Out.powObj A k) (Out.boxLB L p.pr) :=
    GlobalTheory.relAmple_boxLB X (Out.powObj A k) A k p L hL hamp
  obtain ⟨-, N, hN⟩ := GlobalTheory.RelAmpleQProj.isProper_and_exists_isAmpleLB (Out.powObj A k)
    (LB.isLB_linComb hL _ _) hrel hH
  let e : GlobalTheory.KS.pow A k ≅ Out.powObj A k :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Out.powIsLimit A k)
  have hpA : IsProper A.hom := hA.proper
  have : IsProper (GlobalTheory.KS.pow A k).hom := GlobalTheory.KS.Leray.isProper_pow_hom A hpA k
  have : IsIso e.hom.left := ((Over.forget X).mapIso e).isIso_hom
  have := hsp
  exact (hN.pull_of_isAffineHom e.hom.left).isProjOver _

end GlobalTheory.KS
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CotDim

open TensorProduct KaehlerDifferential

theorem exists_basis_mod_sq {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (d : ℕ)
    (hb : letI := e.toAlgebra; Nonempty (Module.Basis (Fin d) ℂ (ℂ ⊗[A] Ω[A⁄ℂ]))) :
    ∃ g : Fin d → A, (∀ j, e (g j) = 0) ∧
      (∀ a : A, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2) ∧
      (∀ c : Fin d → ℂ, ∑ j, c j • g j ∈ RingHom.ker e ^ 2 → c = 0) := by
  letI : Algebra A ℂ := e.toAlgebra
  haveI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun c => (he c).symm
  obtain ⟨b⟩ := hb
  have hs : Function.Surjective (algebraMap A ℂ) := fun c => ⟨algebraMap ℂ A c, he c⟩
  have key : ∀ (c : ℂ) (w : Ω[A⁄ℂ]), (1 : ℂ) ⊗ₜ[A] (c • w) = c • ((1 : ℂ) ⊗ₜ[A] w) := by
    intro c w
    rw [← algebraMap_smul A c w, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
    exact he c
  let φ : A →ₗ[ℂ] ℂ ⊗[A] Ω[A⁄ℂ] :=
    { toFun := fun a => (1 : ℂ) ⊗ₜ[A] D ℂ A a
      map_add' := fun a b => by rw [map_add (f := _), TensorProduct.tmul_add]
      map_smul' := fun c a => by rw [(D ℂ A).map_smul c a, key]; rfl }
  have hφ : ∀ x : RingHom.ker (algebraMap A ℂ), φ x =
      kerCotangentToTensor ℂ A ℂ ((RingHom.ker (algebraMap A ℂ)).toCotangent x) :=
    fun x => (kerCotangentToTensor_toCotangent ℂ A ℂ x).symm
  have hinj := GlobalTheory.SmoothTangent.kerCotangentToTensor_injective ℂ A ℂ hs
  have hsurj : ∀ v, ∃ x : RingHom.ker (algebraMap A ℂ), φ x = v := by
    intro v
    obtain ⟨y, hy⟩ := (exact_kerCotangentToTensor_mapBaseChange ℂ A ℂ hs v).mp (Subsingleton.elim _ _)
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
    exact ⟨x, (hφ x).trans hy⟩
  have hker : ∀ x : RingHom.ker (algebraMap A ℂ), φ x = 0 → (x : A) ∈ RingHom.ker e ^ 2 := by
    intro x hx
    rw [hφ, ← map_zero (kerCotangentToTensor ℂ A ℂ), hinj.eq_iff, Ideal.toCotangent_eq_zero] at hx
    exact hx
  choose g hg using fun j => hsurj (b j)
  have hmemg : ∀ c : Fin d → ℂ, ∑ j, c j • (g j : A) ∈ RingHom.ker (algebraMap A ℂ) := fun c =>
    Ideal.sum_mem _ fun j _ => by rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (g j).2
  have hφg : ∀ c : Fin d → ℂ, φ (∑ j, c j • (g j : A)) = ∑ j, c j • b j := fun c => by

    rw [map_sum]; simp only [map_smul, hg]
  refine ⟨fun j => g j, fun j => (g j).2, ?_, ?_⟩
  · intro a ha
    refine ⟨fun j => b.repr (φ a) j, ?_⟩
    have hmem : a - ∑ j, b.repr (φ a) j • (g j : A) ∈ RingHom.ker (algebraMap A ℂ) :=
      Ideal.sub_mem _ ha (hmemg _)
    refine hker ⟨_, hmem⟩ ?_
    change φ (a - _) = 0
    rw [map_sub, hφg, b.sum_repr, sub_self]
  · intro c hc
    have h0 : φ (∑ j, c j • (g j : A)) = 0 := by
      have h1 := hφ ⟨_, hmemg c⟩
      rw [(Ideal.toCotangent_eq_zero _ _).2 hc, map_zero] at h1
      exact h1
    rw [hφg] at h0
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c h0 i

end GlobalTheory.CotDim

namespace GlobalTheory.CotDim

open TensorProduct KaehlerDifferential

theorem nonempty_basis_fibre {A : Type} [CommRing A] [Algebra ℂ A] (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (d : ℕ) (t : A) (ht : e t ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension d ℂ (Localization.Away t)] :
    letI := e.toAlgebra; Nonempty (Module.Basis (Fin d) ℂ (ℂ ⊗[A] Ω[A⁄ℂ])) := by
  letI : Algebra A ℂ := e.toAlgebra
  haveI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun c => (he c).symm
  let et : Localization.Away t →+* ℂ := IsLocalization.Away.lift t (isUnit_iff_ne_zero.2 ht)
  letI : Algebra (Localization.Away t) ℂ := et.toAlgebra
  haveI : IsScalarTower A (Localization.Away t) ℂ := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.Away.lift_eq t (isUnit_iff_ne_zero.2 ht) a).symm
  haveI : Nontrivial (Localization.Away t) := et.domain_nontrivial
  haveI : Algebra.FormallyEtale A (Localization.Away t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.IsStandardSmooth ℂ (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := ℂ) (S := Localization.Away t) d
  haveI : Module.Finite (Localization.Away t) Ω[Localization.Away t⁄ℂ] := Module.finite_of_rank_eq_nat hr
  let b0 := Module.finBasisOfFinrankEq (Localization.Away t) Ω[Localization.Away t⁄ℂ]
    (Module.finrank_eq_of_rank_eq hr)
  let b1 : Module.Basis (Fin d) ℂ (ℂ ⊗[Localization.Away t] Ω[Localization.Away t⁄ℂ]) := b0.baseChange ℂ
  let E1 : ℂ ⊗[Localization.Away t] (Localization.Away t ⊗[A] Ω[A⁄ℂ]) ≃ₗ[ℂ]
      ℂ ⊗[Localization.Away t] Ω[Localization.Away t⁄ℂ] :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
      (tensorKaehlerEquivOfFormallyEtale ℂ A (Localization.Away t))
  let E2 := TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away t) ℂ ℂ Ω[A⁄ℂ]
  exact ⟨(b1.map E1.symm).map E2⟩

end GlobalTheory.CotDim

theorem GlobalTheory.CotDim.exists_cotangent_basis : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    (U : X.Opens), IsAffineOpen U → ∀ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
    let e : Sec p U →+* ℂ := CxPts.evHom hy; ∃ g : Fin d → Sec p U, (∀ j, e (g j) = 0) ∧
      (∀ a : Sec p U, e a = 0 → ∃ c : Fin d → ℂ, a - ∑ j, c j • g j ∈ RingHom.ker e ^ 2) ∧
      (∀ c : Fin d → ℂ, ∑ j, c j • g j ∈ RingHom.ker e ^ 2 → c = 0) := by
  intro X p d _ U hU y hy e
  have he : ∀ c : ℂ, e (algebraMap ℂ (Sec p U) c) = c := fun c => by
    exact (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension d) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hts, ht⟩ : ∃ t : Sec p U, t ∈ s ∧ e t ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hle : Ideal.span (↑s : Set Γ(X, U)) ≤ RingHom.ker (e : Γ(X, U) →+* ℂ) :=
      Ideal.span_le.2 fun t ht => hcon t ht
    have h1 : (1 : Γ(X, U)) ∈ RingHom.ker (e : Γ(X, U) →+* ℂ) := hle (by rw [hs]; exact Submodule.mem_top)
    have h2 : e 1 = 0 := h1
    rw [map_one] at h2
    exact one_ne_zero h2
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv
    (@h t hts (Localization.Away t) _ (inferInstance : Algebra (Sec p U) (Localization.Away t))
      (by exact (inferInstance : IsLocalization (Submonoid.powers t) (Localization.Away t))))
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d ℂ (Localization.Away (t : Sec p U)) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap,
      IsScalarTower.algebraMap_eq ℂ (Sec p U) (Localization.Away (t : Sec p U))]
    first
      | exact h₁
      | (convert h₁ using 1 <;> rfl)
  exact GlobalTheory.CotDim.exists_basis_mod_sq e he d (GlobalTheory.CotDim.nonempty_basis_fibre e he d t ht)
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TransvZeros

theorem mem_minimalPrimes_of_le_sup_sq {A : Type} [CommRing A] {I m : Ideal A} [hm : m.IsMaximal]
    (hfg : m.FG) (hI : I ≤ m) (hsq : m ≤ I ⊔ m ^ 2) : m ∈ I.minimalPrimes := by
  refine ⟨⟨hm.isPrime, hI⟩, fun P hP hPm => ?_⟩
  obtain ⟨hPp, hIP⟩ := hP
  let π := Ideal.Quotient.mk I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hcm : (m.map π).comap π = m := by
    rw [Ideal.comap_map_of_surjective' π hπ, Ideal.mk_ker, sup_eq_left.2 hI]
  have hcP : (P.map π).comap π = P := by
    rw [Ideal.comap_map_of_surjective' π hπ, Ideal.mk_ker, sup_eq_left.2 hIP]
  have hidem : IsIdempotentElem (m.map π) := by
    refine le_antisymm Ideal.mul_le_left ?_
    have h1 : m.map π ≤ (I ⊔ m ^ 2).map π := Ideal.map_mono hsq
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow, pow_two] at h1
    exact h1
  obtain ⟨e, he, hme⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (hfg.map π)).1 hidem
  have hPq : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ
    (by rw [Ideal.mk_ker]; exact hIP)
  have hem : e ∈ m.map π := hme ▸ Ideal.mem_span_singleton_self e
  have hne : 1 - e ∉ P.map π := by
    intro h
    have h' : 1 - e ∈ m.map π := Ideal.map_mono hPm h
    have h1 : (1 : A ⧸ I) ∈ m.map π := by simpa using Ideal.add_mem _ h' hem
    have h2 : (1 : A) ∈ m := by
      rw [← hcm, Ideal.mem_comap, map_one]; exact h1
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have heP : e ∈ P.map π := by
    have h0 : e * (1 - e) ∈ P.map π := by
      rw [mul_sub, mul_one, he.eq, sub_self]; exact Ideal.zero_mem _
    exact (hPq.mem_or_mem h0).resolve_right hne
  have hle : m.map π ≤ P.map π := by
    rw [hme, Ideal.span_le, Set.singleton_subset_iff]; exact heP
  rw [← hcm, ← hcP]
  exact Ideal.comap_mono hle

theorem eq_of_evHom_eq {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {y z : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U)
    (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U) (e : CxPts.evHom hy = CxPts.evHom hz) : y = z := by
  have e₁ : y.1.appLE U ⊤ hy = z.1.appLE U ⊤ hz := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec y.1 hU (isAffineOpen_top (Sp ℂ)) hy
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec z.1 hU (isAffineOpen_top (Sp ℂ)) hz
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact Subtype.ext ((cancel_epi _).1 a).symm

theorem evHom_algX {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} {y : CxPts p (RingHom.id ℂ)}
    (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U) (c : ℂ) : CxPts.evHom hy (algX p U c) = c :=
  (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)

theorem eq_of_ker_eq {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {y z : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U)
    (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U)
    (e : RingHom.ker (CxPts.evHom hy) = RingHom.ker (CxPts.evHom hz)) : y = z := by
  refine eq_of_evHom_eq hU hy hz (RingHom.ext fun f => ?_)
  have h1 : f - algX p U (CxPts.evHom hy f) ∈ RingHom.ker (CxPts.evHom hy) := by
    rw [RingHom.mem_ker, map_sub, evHom_algX, sub_self]
  rw [e, RingHom.mem_ker, map_sub, evHom_algX, sub_eq_zero] at h1
  exact h1.symm

theorem finite_transv_zeros : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ (k : ℕ) (φ : Fin k → Γ(X, U)), {z : CxPts p (RingHom.id ℂ) | ∃ hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U,
      (∀ j, CxPts.evHom hz (φ j) = 0) ∧
        RingHom.ker (CxPts.evHom hz) ≤ Ideal.span (Set.range φ) ⊔ RingHom.ker (CxPts.evHom hz) ^ 2}.Finite := by
  intro X p _ U hU k φ
  have h1 := LocallyOfFiniteType.finiteType_appLE p (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, U) := hft
  haveI : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing ℂ _
  classical
  let F : CxPts p (RingHom.id ℂ) → Ideal Γ(X, U) := fun z =>
    if hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U then RingHom.ker (CxPts.evHom hz) else ⊥
  refine Set.Finite.of_finite_image (f := F)
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ (Ideal.span (Set.range φ))).subset ?_) ?_
  · rintro _ ⟨z, ⟨hz, hv, hsq⟩, rfl⟩
    simp only [F, dif_pos hz]
    haveI : (RingHom.ker (CxPts.evHom hz)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ fun c => ⟨algX p U c, evHom_algX hz c⟩
    refine mem_minimalPrimes_of_le_sup_sq (IsNoetherian.noetherian _) ?_ hsq
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hv j
  · rintro y ⟨hy, -⟩ z ⟨hz, -⟩ e
    simp only [F, dif_pos hy, dif_pos hz] at e
    exact eq_of_ker_eq hU hy hz e

end GlobalTheory.TransvZeros
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open MeasureTheory Topology

namespace GlobalTheory.ChartSard

theorem null_negEv_of_det_eq_zero : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) (U : X.Opens) (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d)
    (φ : Fin d → Γ(X, U)), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ z ∈ ch.e.source, ∀ hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U,
        (ch.jacMat φ z).det = 0 → (fun j => -GlobalTheory.CxPts.evHom hz (φ j)) ∈ E := by
  intro X p d U ch φ
  set T : (Fin d → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
    (EuclideanSpace.equiv (Fin d) ℂ).symm.toContinuousLinearMap with hT
  have hTw : ∀ w, T w = WithLp.toLp 2 w := fun w => rfl
  set g : Fin d → EuclideanSpace ℂ (Fin d) → ℂ :=
    fun j => GlobalTheory.CxPts.ev p (RingHom.id ℂ) U (φ j) ∘ ch.e.symm with hg
  set H : (Fin d → ℂ) → (Fin d → ℂ) := fun w j => -g j (T w) with hH
  refine ⟨H '' {w | DifferentiableAt ℝ H w ∧ (fderiv ℝ H w).det = 0},
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := fun w => fderiv ℝ H w)
      (fun w hw => hw.1.hasFDerivAt.hasFDerivWithinAt) (fun w hw => hw.2), ?_⟩
  intro z hzs hz hdet
  set w : Fin d → ℂ := (ch.e z).ofLp with hw
  have hTz : T w = ch.e z := rfl
  have hL : ∀ j, HasFDerivAt (g j) (fderiv ℂ (g j) (ch.e z)) (T w) := fun j => by
    rw [hTz]; exact (ch.differentiableAt_ev (φ j) hzs hz).hasFDerivAt
  set M : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun j => -((fderiv ℂ (g j) (ch.e z)).comp T) with hM
  have hHM : HasFDerivAt H M w := by
    refine hasFDerivAt_pi'.2 fun j => ?_
    exact ((hL j).comp w T.hasFDerivAt).neg
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hTv : T v = ∑ b, v b • EuclideanSpace.single b (1 : ℂ) := by
    ext i
    simp [hTw, Pi.single_apply]
  have hMv : M v = 0 := by
    funext j
    have hj := congrFun hv j
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hj

    simp only [hM, ContinuousLinearMap.pi_apply, neg_apply,
    ContinuousLinearMap.comp_apply, hTv, map_sum, map_smul, smul_eq_mul, Pi.zero_apply, neg_eq_zero]
    rw [← hj]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨w, ⟨(hHM.restrictScalars ℝ).differentiableAt, ?_⟩, ?_⟩
  · rw [(hHM.restrictScalars ℝ).fderiv]
    refine LinearMap.det_eq_zero_iff_ker_ne_bot.2 ((Submodule.ne_bot_iff _).2 ⟨v, ?_, hv0⟩)
    show M v = 0
    exact hMv
  · funext j
    simp only [hH, hg, Function.comp_apply, hTz, ch.e.left_inv hzs, GlobalTheory.CxPts.ev_eq hz]

end GlobalTheory.ChartSard
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MaxPt

theorem eq_top_of_forall_cxPts_mem : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens),
    (∀ z : CxPts p (RingHom.id ℂ), z ∈ CxPts.ptsIn p (RingHom.id ℂ) U) → U = ⊤ := by
  intro X p _ U hall
  by_contra hU
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ U := by
    by_contra h
    push_neg at h
    exact hU (eq_top_iff.2 fun y _ => h y)
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hV : IsAffineOpen V := hV
  let S : Set (PrimeSpectrum Γ(X, V)) := {η | hV.fromSpec η ∉ U}
  have hS : IsClosed S := by
    have : IsOpen {η : PrimeSpectrum Γ(X, V) | hV.fromSpec η ∈ U} :=
      U.isOpen.preimage hV.fromSpec.continuous
    exact this.isClosed_compl
  have hSne : S.Nonempty := by
    have : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hxV
    obtain ⟨ξ, hξ⟩ := this
    exact ⟨ξ, by show hV.fromSpec ξ ∉ U; rw [hξ]; exact hx⟩
  obtain ⟨η, hηS, hηc⟩ := hS.exists_closed_singleton hSne
  have hm : η.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal η).1 hηc
  set m := η.asIdeal
  have h1 := LocallyOfFiniteType.finiteType_appLE p (isAffineOpen_top (Sp ℂ)) hV (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p V).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, V) := (algX p V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, V) := hft
  letI : Field (Γ(X, V) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(X, V) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(X, V) ⧸ m)
  have hbij : Function.Bijective (algebraMap ℂ (Γ(X, V) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃+* (Γ(X, V) ⧸ m) := RingEquiv.ofBijective _ hbij
  let φ : Γ(X, V) →+* ℂ := (e.symm : (Γ(X, V) ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m)
  have hφ : ∀ a, φ (algX p V a) = (RingHom.id ℂ) a := by
    intro a
    show e.symm (Ideal.Quotient.mk m (algebraMap ℂ Γ(X, V) a)) = a
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.symm_apply_apply a
  have hker : RingHom.ker φ = m := by
    ext f
    rw [RingHom.mem_ker]
    show e.symm (Ideal.Quotient.mk m f) = 0 ↔ f ∈ m
    rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  have hz := CxPts.mem_ptsIn.1 (hall (CxPts.ofHom hV φ hφ))
  have hpt : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ) = η := by
    apply PrimeSpectrum.ext
    show Ideal.comap φ (IsLocalRing.maximalIdeal ℂ) = m
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]
  have : (CxPts.ofHom hV φ hφ).1 (IsLocalRing.closedPoint ℂ) = hV.fromSpec η := by
    show (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) (IsLocalRing.closedPoint ℂ) = _
    show hV.fromSpec (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint ℂ)) = _
    rw [hpt]
  exact hηS (this ▸ hz)

end GlobalTheory.MaxPt
end
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualPageWord_inert_prime_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → φ.1.2 = -1 → (pageWord L j ε τ φ).Box ∧ ((pageWord L j ε τ φ).HypNT ∨ (φ = D.R.cc ∧ (pageWord L j ε τ φ).HypAT l ∧ ∀ i, (pageWord L j ε τ φ).thick i)) := by
  first | exact @GlobalTheory.HTW.pageWord_inert_dichotomy | exact GlobalTheory.HTW.pageWord_inert_dichotomy | (intros; apply GlobalTheory.HTW.pageWord_inert_dichotomy <;> assumption)
end
