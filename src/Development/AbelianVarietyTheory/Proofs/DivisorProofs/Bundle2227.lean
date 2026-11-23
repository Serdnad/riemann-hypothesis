module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle162
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle074
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle281
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle602
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueNormalOfProfiniteInvariantsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.PolRigid

open GlobalTheory.CechPic

theorem cls_lam_pull {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : LB B.left} (hL : L.IsLB)
    (x y : B ⟶ B) (h : ((abelian₂ B L).pull (lift x y).left).IsLB) :
    cls _ h = lam (cls L hL) x y := by
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have h₁ : cls _ hlam = lam (cls L hL) (fst B B) (snd B B) := cls_cube_two hL _ _ hlam
  rw [cls_pull hlam, h₁, pull_lam, lift_fst, lift_snd]

theorem lbIso_lam_of_quotient : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [CommRing R₀] [Nontrivial R₀] (π : R →+* R₀), Function.Surjective π → ∀ (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left), P.IsLB → (∃ t : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → ∀ (L : LB B.left) (L₀ : LB B₀.left), L.IsLB → L₀.IsLB → LBIso (L.pull i) L₀ → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → LBIso (abelian₂ B L) P := by
  intro R R₀ _ _ _ _ π hπ B _ _ B₀ _ _ i i₂ hA hpb hsq P hP hP₁ hP₂ L L₀ hL hL₀ e₀ e
  haveI : IsLocalRing R₀ := IsLocalRing.of_surjective' π hπ
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hlam₀ : (abelian₂ B₀ L₀).IsLB := LB.isLB_linComb hL₀ _ _
  have hD : (LB.div (abelian₂ B L) P).IsLB := LB.isLB_div hlam hP
  have hcD : cls _ hD = cls _ hlam - cls P hP := cls_div hlam hP hD

  have triv_of : ∀ {Y : Scheme.{0}} (f : Y ⟶ (G2 B).left), pull f (cls _ hlam) = pull f (cls P hP) →
      GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull f) := fun f hf =>
    (cls_eq_zero_iff (pull_isLB hD f)).1 (by rw [cls_pull hD, hcD, map_sub, hf, sub_self])

  have ax : ∀ (x y : B ⟶ B), (∃ t : (P.pull (lift x y).left).Gen, t.IsGen) → lam (cls L hL) x y = 0 →
      GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift x y).left) := fun x y hPxy hl => by
    refine triv_of _ ?_
    rw [← cls_pull hlam _ (pull_isLB hlam _), cls_lam_pull hL x y, hl, ← cls_pull hP _ (pull_isLB hP _)]
    exact ((cls_eq_zero_iff (pull_isLB hP _)).2 hPxy).symm
  have h₁ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift (𝟙 B) 1).left) := ax _ _ hP₂ (lam_one_right _ _)
  have h₂ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift 1 (𝟙 B)).left) := ax _ _ hP₁ (lam_one_left _ _)

  have hsq₀ : pull i₂ (cls _ hlam) = pull i₂ (cls P hP) := by
    have a : LBIso (abelian₂ B₀ L₀) ((abelian₂ B L).pull i₂) := GlobalTheory.ZM.SiegPull.lbIso_lam_pull hpb e₀.symm hsq
    rw [← cls_pull hlam _ (pull_isLB hlam _), ← cls_pull hP _ (pull_isLB hP _),
      ← (cls_eq_iff hlam₀ (pull_isLB hlam _)).2 a, (cls_eq_iff hlam₀ (pull_isLB hP _)).2 e]

  let k := ResidueField R₀
  let g₀ : R →+* k := (residue R₀).comp π
  have hpb₂ : IsPullback i₂ (G2 B₀).hom (G2 B).hom (spMap π) :=
    GlobalTheory.SiegelDescent.isPullback_square hpb.1 i₂ hsq
  have h₀ := (IsPullback.of_hasPullback (G2 B₀).hom (spMap (residue R₀))).paste_horiz hpb₂
  have e₁ : spMap (residue R₀) ≫ spMap π = Spec.map (CommRingCat.ofHom g₀) := by
    simp only [spMap, g₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [e₁] at h₀
  have ht₀ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (pullback.fst (G2 B₀).hom (spMap (residue R₀)) ≫ i₂)) :=
    triv_of _ (by rw [pull_comp, pull_comp, hsq₀])
  have hPf : GlobalTheory.SpreadingModels.PerfAll :=
    GlobalTheory.T.perfect_of_models (GlobalTheory.T.has_model_of_spreading GlobalTheory.T.scheme_models_spread GlobalTheory.T.smooth_spreads_out GlobalTheory.T.isProper_spreads_out GlobalTheory.T.line_bundle_spreads_out')
  haveI := hA.smooth
  haveI := hA.proper
  have sm : Smooth (B ⊗ B).hom := by
    change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  have pr : IsProper (B ⊗ B).hom := by
    change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  obtain ⟨r, hr, hU⟩ := GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre GlobalTheory.globalFns_holds GlobalTheory.AbLaw.Seesaw.seesaw
    (GlobalTheory.SmallExtLift.exists_gen_of_small_extension GlobalTheory.globalFns_holds GlobalTheory.KuennethOne.kuenneth_injective)
    R B hA _ hD (hPf R _ (B ⊗ B).hom sm pr _ hD) h₁ h₂ k g₀ _ _ _ h₀ ht₀

  have hru : IsUnit r := by
    by_contra hnu
    refine hr ?_
    show residue R₀ (π r) = 0
    rw [residue_eq_zero_iff]
    intro hu
    obtain ⟨s, hs⟩ := hu.exists_right_inv
    obtain ⟨t, rfl⟩ := hπ s
    have hk : r * t - 1 ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hs, map_one, sub_self]
    have hm : RingHom.ker π ≤ maximalIdeal R := le_maximalIdeal (RingHom.ker_ne_top π)
    have hunit : IsUnit (r * t) := by
      by_contra h'
      have h1 : r * t ∈ maximalIdeal R := (mem_maximalIdeal _).2 h'
      have h2 : (1 : R) ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem h1 (hm hk)
        simpa using this
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
    exact hnu (isUnit_of_mul_isUnit_left hunit)
  let U := (B ⊗ B).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)
  have hsub : Set.range (𝟙 (B ⊗ B).left) ⊆ Set.range U.ι := by
    rintro x -
    rw [Scheme.Opens.range_ι]
    change r ∉ ((B ⊗ B).hom x).asIdeal
    exact fun hx => ((B ⊗ B).hom x).2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hru)
  have hT := GlobalTheory.AbLaw.CubeOpen.triv_comp (IsOpenImmersion.lift U.ι (𝟙 _) hsub) (IsOpenImmersion.lift_fac _ _ _) hU
  have hz : cls _ hD = 0 := by
    rw [← pull_id (cls _ hD), ← cls_pull hD _ (pull_isLB hD _)]
    exact (cls_eq_zero_iff _).2 hT
  exact (cls_eq_iff hlam hP).1 (sub_eq_zero.1 (hcD ▸ hz))

end GlobalTheory.PolRigid
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ResidueFixed

theorem residue_fixed_mem : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ x ∈ V, (∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → V.valuation (σ x - x) < 1) → ∃ r : R, V.valuation (x - algebraMap K Ω (algebraMap R K r)) < 1 := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV x hx hfix
  classical
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have h : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact h
  let φ : R →+* V := (algebraMap R Ω).codRestrict V.toSubring hRV

  have hmR : ∀ r ∈ maximalIdeal R, V.valuation (algebraMap R Ω r) < 1 := by
    intro r hr
    by_contra hlt
    have h1 : V.valuation (algebraMap R Ω r) = 1 :=
      le_antisymm (V.valuation_le_one (φ r)) (not_lt.1 hlt)
    have hu : IsUnit (φ r) := (V.valuation_eq_one_iff (φ r)).2 h1
    have hne : algebraMap R K r ≠ 0 := by
      intro h0
      rw [show algebraMap R Ω r = algebraMap K Ω (algebraMap R K r) from rfl, h0, map_zero, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω (algebraMap R K r)⁻¹ ∈ V
      obtain ⟨u, hu'⟩ := hu
      have : ((u⁻¹ : Vˣ) : V) * φ r = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Vˣ) : V)) : Ω) = algebraMap K Ω (algebraMap R K r)⁻¹ := by
        rw [map_inv₀]
        refine (eq_inv_of_mul_eq_one_left ?_)
        exact congrArg Subtype.val this
      rw [← h2]; exact SetLike.coe_mem _
    rw [hV] at hinv
    obtain ⟨r', hr'⟩ := hinv
    apply (mem_maximalIdeal r).1 hr
    refine isUnit_iff_exists_inv.2 ⟨r', IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr', map_one, mul_inv_cancel₀ hne]

  let B := integralClosure R Ω
  have hBV : ∀ b : B, (b : Ω) ∈ V := by
    intro b
    obtain ⟨p, hpm, hp⟩ := b.2
    have hint : IsIntegral V (b : Ω) := by
      refine ⟨p.map φ, hpm.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hp
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    rw [← hy]; exact y.2
  let ψ : B →+* V := (B.val : B →+* Ω).codRestrict V.toSubring hBV
  let Q : Ideal B := (maximalIdeal V).comap ψ
  have hQ : ∀ b : B, b ∈ Q ↔ V.valuation (b : Ω) < 1 := fun b => V.valuation_lt_one_iff (ψ b)
  let G := Ω ≃ₐ[K] Ω
  have hc : SMulCommClass G R Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have : ContinuousSMul G B := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant R B G := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral R k := by
      have h2 : IsIntegral R (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff ).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hQP : Q.LiesOver (maximalIdeal R) := by
    constructor
    refine le_antisymm (fun r hr => ?_) (IsLocalRing.le_maximalIdeal ?_)
    · change algebraMap R B r ∈ Q
      rw [hQ]; exact hmR r hr
    · intro h1
      have h : (1 : R) ∈ Q.comap (algebraMap R B) := by
        change (1 : R) ∈ Q.under R
        rw [h1]; exact Submodule.mem_top
      rw [Ideal.mem_comap, map_one, hQ] at h
      simp at h
  have hQmax : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (maximalIdeal R)
  letI := Ideal.Quotient.field (maximalIdeal R)
  letI := Ideal.Quotient.field Q
  haveI hN : Normal (R ⧸ maximalIdeal R) (B ⧸ Q) := GlobalTheory.T.residue_normal_of_profinite_invariants G (maximalIdeal R) Q
  haveI : PerfectField (R ⧸ maximalIdeal R) := ‹PerfectField (ResidueField R)›
  haveI : IsGalois (R ⧸ maximalIdeal R) (B ⧸ Q) := {}

  have hBle : ∀ b : B, V.valuation (b : Ω) ≤ 1 := fun b => V.valuation_le_one (ψ b)

  have hsub : ∀ g ∈ MulAction.stabilizer G Q, ∀ y ∈ V, g y ∈ V := by
    intro g hg y hy
    obtain ⟨a, s, ha, hs, hsv, hys⟩ := GlobalTheory.T.exists_integral_quotient_of_valuationSubring_above_dvr R K Ω V hV y hy
    let a' : B := ⟨a, ha⟩
    let s' : B := ⟨s, hs⟩
    have hs'Q : s' ∉ Q := by rw [hQ]; exact fun h => (ne_of_lt h) hsv
    have hgs : g • s' ∉ Q := by
      intro h
      apply hs'Q
      have h' : g • s' ∈ g • Q := by rw [MulAction.mem_stabilizer_iff.1 hg]; exact h
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul] at h'
      exact h'
    have hgsv : V.valuation (g s) = 1 := by
      rw [hQ] at hgs
      exact le_antisymm (hBle (g • s')) (not_lt.1 hgs)
    have hga : V.valuation (g a) ≤ 1 := hBle (g • a')
    apply V.mem_of_valuation_le_one
    have : g y * g s = g a := by rw [← map_mul, hys]
    rw [← this, map_mul, hgsv, _root_.mul_one] at hga
    exact hga
  have hstabV : ∀ g ∈ MulAction.stabilizer G Q, g • V = V := by
    intro g hg
    ext z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hz
      have := hsub g hg _ hz
      have e : g (g⁻¹ • z) = z := smul_inv_smul g z
      rwa [e] at this
    · intro hz
      exact hsub g⁻¹ (inv_mem hg) z hz

  obtain ⟨a, s, ha, hs, hsv, hxs⟩ := GlobalTheory.T.exists_integral_quotient_of_valuationSubring_above_dvr R K Ω V hV x hx
  let a' : B := ⟨a, ha⟩
  let s' : B := ⟨s, hs⟩
  have hs'Q : s' ∉ Q := by rw [hQ]; exact fun h => (ne_of_lt h) hsv
  have hsne : Ideal.Quotient.mk Q s' ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  let ξ : B ⧸ Q := Ideal.Quotient.mk Q a' / Ideal.Quotient.mk Q s'
  have hξ : ∀ τ : (B ⧸ Q) ≃ₐ[R ⧸ maximalIdeal R] (B ⧸ Q), τ ξ = ξ := by
    intro τ
    obtain ⟨⟨σ, hσQ⟩, hστ⟩ :=
      Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) (maximalIdeal R) Q τ
    have hlt := hfix σ (hstabV σ hσQ)
    have hσs : σ • s' ∉ Q := by
      intro h
      apply hs'Q
      have h' : σ • s' ∈ σ • Q := by rw [MulAction.mem_stabilizer_iff.1 hσQ]; exact h
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul] at h'
      exact h'
    have hσsv : V.valuation (σ s) = 1 := by
      have h := hσs
      rw [hQ] at h
      exact le_antisymm (hBle (σ • s')) (not_lt.1 h)
    have hσs0 : Ideal.Quotient.mk Q (σ • s') ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hστ]
    simp only [ξ, map_div₀, Ideal.Quotient.stabilizerHom_apply]
    change Ideal.Quotient.mk Q (σ • a') / Ideal.Quotient.mk Q (σ • s') = _
    rw [div_eq_div_iff hσs0 hsne, ← map_mul, ← map_mul, Ideal.Quotient.eq, hQ]
    have e : ((σ • a' * s' - a' * σ • s' : B) : Ω) = (σ x - x) * s * σ s := by
      change σ a * s - a * σ s = _
      rw [← hxs, map_mul]; ring
    rw [e, map_mul, map_mul, hsv, hσsv, _root_.mul_one, _root_.mul_one]
    exact hlt
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := R ⧸ maximalIdeal R) ξ).2 hξ
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨r, ?_⟩
  have h1 : Ideal.Quotient.mk Q (algebraMap R B r) = ξ := hc
  have h2 : Ideal.Quotient.mk Q (algebraMap R B r * s') = Ideal.Quotient.mk Q a' := by
    rw [map_mul, h1, div_mul_cancel₀ _ hsne]
  rw [Ideal.Quotient.eq, hQ] at h2
  have e : ((algebraMap R B r * s' - a' : B) : Ω) = (algebraMap K Ω (algebraMap R K r) - x) * s := by
    change algebraMap K Ω (algebraMap R K r) * s - a = _
    rw [← hxs]; ring
  rw [e, map_mul, hsv, _root_.mul_one, Valuation.map_sub_swap] at h2
  exact h2

end GlobalTheory.ResidueFixed
end

section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRed

theorem natCast_ne_zero_of_residue {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {m : ℕ} (h : (m : ResidueField R) ≠ 0) : (m : K) ≠ 0 := by
  intro h0
  apply h
  have h1 : (m : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, map_zero, h0])
  rw [← map_natCast (residue R), h1, map_zero]

theorem torsionUnramified_pow_of_tateUnramified {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    {V : ValuationSubring Ω} {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {l : ℕ} [Fact l.Prime] (hl : (l : K) ≠ 0) (h : TateUnramified A V l) (n : ℕ) :
    TorsionUnramified A V (l ^ n) := by
  intro σ hσ x hx
  obtain ⟨t, rfl⟩ := GlobalTheory.T.tateModule_level_surjective_of_divisible l (ptOver K Ω ⟶ A) (GlobalTheory.T.abelianVariety_sepClosed_point_divisible K Ω A hA l hl) n x hx
  rw [← lev_galTate, h σ hσ]
  rfl

theorem infinite_torsionUnramified_of_tateUnramified :
    ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
      [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
      (V : ValuationSubring Ω), IsAbove R K V.toSubring →
      ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
      ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → TateUnramified A V l →
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V _ A _ _ hA l hp hl h
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n)
    (Nat.pow_right_injective hp.out.two_le) fun n => ⟨?_, ?_⟩
  · rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  · exact torsionUnramified_pow_of_tateUnramified hA (natCast_ne_zero_of_residue hl) h n

end GlobalTheory.AbVarRed
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.OrthoFrame

theorem isSelfDualC_colLat_of_orthonormal : ∀ {D : D7} (S : HSp D) (B : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → IsSelfDualC S (colLat B) := by
  intro D S B hB
  exact GlobalTheory.FunObj.VecEx.isSelfDualC_colLat S B hB

end GlobalTheory.FunObj.OrthoFrame
end
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idempotentSum_conjSum_orthogonal_dvd : ∀ (D : D7) (e e' : AE D) (P P' : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ), IsIdemSum e P → IsIdemSum e' P' → (∀ PP ∈ P, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ P', ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (e + cA D e) * (e' + cA D e') = 0 := by
  first | exact @GlobalTheory.IdemOrth.idemSum_orth | exact GlobalTheory.IdemOrth.idemSum_orth | (intros; apply GlobalTheory.IdemOrth.idemSum_orth <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelAction_framedPoints_isAction : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) , R.toLevCh.Is A.μ0 → LawsJ T → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) := by
  first | exact @GlobalTheory.LevelActFromLevel.actLev_of_levIs | exact GlobalTheory.LevelActFromLevel.actLev_of_levIs | (intros; apply GlobalTheory.LevelActFromLevel.actLev_of_levIs <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF


theorem _root_.GlobalTheory.T.weil_datum_twist_by_hecke_characters_trivial_base : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT νS νT : (AF F ⊗[F] E)ˣ →* Circle) ω,
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        IsHeckeCharF νS → IsHeckeCharF νT → ResEtaF νS 0 → ResEtaF νT 0 →
        ∃ ω', IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (χS * νS) (χT * νT) ω' := by
  first | exact @GlobalTheory.WeilTwistF.exists_weilDatumOF_twist | exact GlobalTheory.WeilTwistF.exists_weilDatumOF_twist | (intros; apply GlobalTheory.WeilTwistF.exists_weilDatumOF_twist <;> assumption)
end

section

open FourierTransform MeasureTheory Filter Topology

theorem GlobalTheory.GaussWidths.all_widths : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M :=
  GlobalTheory.GaussWidths.all_widths_of_conv GlobalTheory.T.mem_of_closedSubmodule_gaussian_convolution
end
