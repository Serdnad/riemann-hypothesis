module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle566
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle174
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Mathlib.RingTheory.LaurentSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncIso

theorem mem_vanishingIdeal_ideal_iff {X : Scheme.{0}} (Z : Closeds X) (U : X.affineOpens) (s : Γ(X, U.1)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U ↔
      ∀ x ∈ (U.1 : Set X), x ∈ (Z : Set X) → x ∉ X.basicOpen s := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · rintro h x hxU hxZ hxs
    rw [← U.2.range_fromSpec] at hxU
    obtain ⟨p, rfl⟩ := hxU
    have hp : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := hxs
    rw [U.2.fromSpec_preimage_basicOpen] at hp
    exact hp (h p hxZ)
  · intro h p hpZ
    by_contra hs
    have hp : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
      rw [U.2.fromSpec_preimage_basicOpen]; exact hs
    have hpU : U.2.fromSpec p ∈ (U.1 : Set X) := by
      rw [← U.2.range_fromSpec]; exact ⟨p, rfl⟩
    exact h _ hpU hpZ hp

theorem rsp_ringEquiv {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] (e : R ≃+* S)
    {n : ℕ} {x : Fin n → R} (h : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R n x) : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp S n (fun i => e (x i)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have hr : Set.range (fun i => e (x i)) = e '' Set.range x := by
    rw [← Set.range_comp]; rfl
  rw [hr, ← Ideal.map_span, h1]
  ext y
  rw [Ideal.mem_map_of_equiv, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩ hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hz ((isUnit_map_iff e z).1 hu)
  · intro hy
    refine ⟨e.symm y, (IsLocalRing.mem_maximalIdeal _).2 fun hu => hy ?_, e.apply_symm_apply y⟩
    simpa using (isUnit_map_iff e (e.symm y)).2 hu

theorem snc_vanishingIdeal_of_isIso {A B : Scheme.{0}} (f : A ⟶ B) [IsIso f] (Z : Closeds B) (Z' : Closeds A)
    (hZ : ∀ a : A, a ∈ Z' ↔ f a ∈ Z) (h : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal Z)) :
    ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal Z') := by
  intro a
  obtain ⟨hreg, U, hU, n, g, J, hrsp, hid⟩ := h (f a)
  let e : B.presheaf.stalk (f a) ≃+* A.presheaf.stalk a := (asIso (f.stalkMap a)).commRingCatIsoToRingEquiv
  have he : ∀ t, e t = f.stalkMap a t := fun _ => rfl
  let U' : A.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have hU' : a ∈ U'.1 := hU
  refine ⟨IsRegularLocalRing.of_ringEquiv e, U', hU', n, fun i => f.app U.1 (g i), J, ?_, ?_⟩
  · have hg : ∀ i, A.presheaf.germ U'.1 a hU' (f.app U.1 (g i)) = e (B.presheaf.germ U.1 (f a) hU (g i)) := by
      intro i
      rw [he, Scheme.Hom.germ_stalkMap_apply]
    simp only [hg]
    exact rsp_ringEquiv e hrsp
  · let φ : Γ(B, U.1) ≃+* Γ(A, U'.1) := (asIso (f.app U.1)).commRingCatIsoToRingEquiv
    have hφ : ∀ t, φ t = f.app U.1 t := fun _ => rfl
    ext t
    obtain ⟨s, rfl⟩ : ∃ s, φ s = t := φ.surjective t
    have key : φ s ∈ (Scheme.IdealSheafData.vanishingIdeal Z').ideal U' ↔
        s ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U := by
      rw [mem_vanishingIdeal_ideal_iff, mem_vanishingIdeal_ideal_iff, hφ, ← Scheme.preimage_basicOpen]
      constructor
      · intro H b hbU hbZ hbs
        obtain ⟨a', rfl⟩ : ∃ a', f a' = b := ⟨(inv f) b, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
        exact H a' hbU ((hZ a').2 hbZ) hbs
      · intro H a' ha'U ha'Z ha's
        exact H (f a') ha'U ((hZ a').1 ha'Z) ha's
    rw [key, hid, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    have hp : (∏ i ∈ J, f.app U.1 (g i)) = φ (∏ i ∈ J, g i) := by
      rw [map_prod]; rfl
    rw [hp, map_dvd_iff]

end GlobalTheory.SncIso

namespace GlobalTheory.VarFlag

open GlobalTheory.Toroidal (gen genι genBd genBdIdeal mem_genBd)

theorem snc_genBdIdeal_of_snc_boundary {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} :
    ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.LogKS.boundary Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (GlobalTheory.Toroidal.genBdIdeal Y) := by
  intro h
  refine GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso (genι Y) (GlobalTheory.LogKS.interior Y).compl (genBd Y) ?_ h
  intro a
  have hinj : Function.Injective (genι Y) := (genι Y).isOpenEmbedding.injective
  rw [mem_genBd]
  show a ∉ Set.range Y.jQ ↔ genι Y a ∉ Set.range Y.j
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [Model.j, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, hinj ?_⟩
    rw [← hx, Model.j, Scheme.Hom.comp_apply]

end GlobalTheory.VarFlag
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem eq_zero_of_ger_dense {Y : Scheme.{0}} [IsReduced Y] {O V : Y.Opens} (hd : Dense (O : Set Y))
    (a : Γ(Y, V)) (h : ∀ z (hz : z ∈ V), z ∈ O → ger z hz a = 0) : a = 0 := by
  refine eq_zero_of_basicOpen_eq_bot a ?_
  by_contra hne
  obtain ⟨y, hy', hy⟩ := hd.inter_open_nonempty _ (Y.basicOpen a).isOpen
    (Set.nonempty_iff_ne_empty.2 fun e => hne (Opens.ext e))
  have hm := Y.basicOpen_le _ hy'
  have hu : IsUnit (ger y hm a) := (Y.mem_basicOpen _ y hm).1 hy'
  rw [h y hm hy] at hu
  exact not_isUnit_zero hu

theorem exists_ext_of_dense_local : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} [IsReduced Y] (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (O : Y.Opens), Dense (O : Set Y) → ∀ (m : H0 p B O), (∀ y : Y, y ∉ O → ∃ (W : Y.Opens) (i : B.ι) (hi : W ≤ B.U i) (b : Γ(Y, W)), y ∈ W ∧ (∀ y' (h : y' ∈ W) (h' : y' ∈ O), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∉ O → ger y' h b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y')) → ∃ s : H0 p B ⊤, H0.restr le_top s = m ∧ ∀ y : Y, y ∉ O → ∀ (i : B.ι) (hi : y ∈ B.U i), H0.germ i y (memTop y) hi s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  intro k _ Y _ p B hB O hd m hloc
  choose W i hi b hyW hagree hmax using hloc
  let τ := B.ι ⊕ {y : Y // y ∉ O}
  let V : τ → Y.Opens := fun t => Sum.elim (fun j => O ⊓ B.U j) (fun y => W y.1 y.2) t
  let c : τ → B.ι := fun t => Sum.elim (fun j => j) (fun y => i y.1 y.2) t
  have hc : ∀ t, V t ≤ B.U (c t) := fun t => by
    rcases t with j | ⟨y, hy⟩
    · exact inf_le_right
    · exact hi y hy
  let u : ∀ t, Γ(Y, V t) := fun t => match t with
    | Sum.inl j => m.loc j
    | Sum.inr y => b y.1 y.2
  have key : ∀ t z (h : z ∈ V t) (hz : z ∈ O), ger z h (u t) = H0.germ (c t) z hz (hc t h) m := by
    intro t z h hz
    rcases t with j | ⟨y, hy⟩
    · rfl
    · exact hagree y hy z h hz
  have cover : ∀ y ∈ (⊤ : Y.Opens), ∃ t, y ∈ V t := fun y _ => by
    by_cases hy : y ∈ O
    · obtain ⟨j, hj⟩ := exists_chart hB y
      exact ⟨Sum.inl j, hy, hj⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, hyW y hy⟩
  have rule : ∀ y t t' (h : y ∈ V t) (h' : y ∈ V t'),
      ger y h (u t) = tr B y (c t) (c t') * ger y h' (u t') := by
    intro y t t' h h'
    have l₁ : V t ⊓ V t' ≤ V t := inf_le_left
    have l₂ : V t ⊓ V t' ≤ V t' := inf_le_right
    have l₃ : V t ⊓ V t' ≤ B.U (c t) ⊓ B.U (c t') := inf_le_inf (hc t) (hc t')
    have hz : ∀ z (hz : z ∈ V t ⊓ V t'), ger z hz (resG Y l₁ (u t) -
        resG Y l₃ (B.g (c t) (c t')).val * resG Y l₂ (u t')) =
        ger z (l₁ hz) (u t) - (tr B z (c t) (c t')).val * ger z (l₂ hz) (u t') := by
      intro z hz
      rw [map_sub, map_mul, ger_resG, ger_resG, ger_resG, val_tr B z (l₃ hz)]
    have e := eq_zero_of_ger_dense hd _ fun z hzV hzO => by
      rw [hz z hzV, key t z (l₁ hzV) hzO, key t' z (l₂ hzV) hzO, sub_eq_zero]
      exact H0.germ_change _ _ z hzO _ _ m
    have e' := congrArg (ger y (memInf h h')) e
    rw [hz y (memInf h h'), map_zero, sub_eq_zero] at e'
    exact e'
  obtain ⟨f, hf⟩ := H0.exists_of_germs (p := p) (O := ⊤) hB V c (fun _ => le_top) hc cover u rule
  refine ⟨f, ?_, ?_⟩
  · refine H0.ext_germ fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart hB y
    refine ⟨j, hj, ?_⟩
    rw [H0.germ_restr]
    exact (hf (Sum.inl j) y ⟨hy, hj⟩).trans rfl
  · intro y hy j hj
    rw [H0.germ_change j (i y hy) y _ hj (hi y hy (hyW y hy))]
    have e := hf (Sum.inr ⟨y, hy⟩) y (hyW y hy)
    refine (congrArg (fun x => (tr B y j (i y hy)).val * x) e).symm ▸ ?_
    exact Ideal.mul_mem_left _ _ (hmax y hy y (hyW y hy) hy)

end GlobalTheory.CompHS
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.valuation_subring_dedekind_open_immersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (W : ValuationSubring c.F), GlobalTheory.Models.IsDedFrac W.subtype ∧ IsOpenImmersion (spMap W.subtype) := by
  first | exact @GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion | exact GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion | (intros; apply GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LineNorm

namespace GlobalTheory.FlatModel

theorem exists_affine_normal_domain {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (V : X.Opens) {z : X}
    (hz : z ∈ V) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : IsDomain Γ(X, U)),
      z ∈ U ∧ U ≤ V ∧ IsIntegrallyClosed Γ(X, U) := by
  have hC : IsOpen (irreducibleComponent z) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)
  obtain ⟨U, hU, hzU, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := z)
    (U := V ⊓ ⟨irreducibleComponent z, hC⟩) ⟨hz, mem_irreducibleComponent⟩
  have hpre : IsPreirreducible (U : Set X) := (isIrreducible_irreducibleComponent (x := z)).2.open_subset U.2
    fun q hq => (hle hq).2
  have hirr : IsIrreducible (U : Set X) := ⟨⟨z, hzU⟩, hpre⟩
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hirr
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : Nonempty (Spec Γ(X, U)) := ⟨hU.isoSpec.hom ⟨z, hzU⟩⟩
  have : IsIntegral (Spec Γ(X, U)) := isIntegral_of_isOpenImmersion hU.isoSpec.inv
  have hd : IsDomain Γ(X, U) := (affine_isIntegral_iff _).1 this
  exact ⟨U, hU, hd, hzU, fun q hq => (hle hq).1,
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain _).1 (GlobalTheory.IsNormalScheme.spec_of_isAffineOpen hU)⟩

end GlobalTheory.FlatModel

end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
noncomputable section

namespace GlobalTheory.PtDeg

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem fibre_iso_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ) (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (Q : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A)), GlobalTheory.IsPolFibre σ F.P₀ Q ψ → (∀ i, GlobalTheory.IsVecOver σ ψ (F.v i) (v' i)) → ∀ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x), ∃ f : Q.A ⟶ T.pol.A, IsMonHom f ∧ LBIso (lbPow (T.pol.L.pull f.left) 1) (lbPow Q.L 1) ∧ ∀ i (q : epsR ℂ ⟶ Q.A), IsLieComb (fun k => σ (v i k)) v' q → ∀ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i → q ≫ f = w' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ v hFC σ φ hφ z hz Q ψ v' hQ hv' T m

  have hφσ : (φ.toRingHom : K →+* ℂ) = σ := RingHom.ext hφ
  have hbase : z.x = spMap σ ≫ y.x := by rw [hz.1, hφσ]; rfl

  have hcomp := hQ.2.1.comp F.fib.2.1
  have w0 : (ψ ≫ F.φ) ≫ B.t.G.hom = (Q.A.hom ≫ spMap σ) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [hcomp.1.w, Category.assoc]
  let χ₀ : Q.A.left ⟶ t₀.G.left := m2.cart.1.lift (ψ ≫ F.φ) (Q.A.hom ≫ spMap σ) w0
  have hχ₀2 : χ₀ ≫ m2.φ = ψ ≫ F.φ := m2.cart.1.lift_fst _ _ w0
  have hχ₀b : χ₀ ≫ t₀.G.hom = Q.A.hom ≫ spMap σ := m2.cart.1.lift_snd _ _ w0
  have hχ₀ : IsGrpPullback Q.A t₀.G (spMap σ) χ₀ := m2.cart.cancel (by rw [hχ₀2]; exact hcomp) hχ₀b
  have hχ := hχ₀.comp m1.cart
  have w1 : (χ₀ ≫ m1.φ) ≫ Xo.univ.t.G.hom = Q.A.hom ≫ z.x := by rw [hχ.1.w, hbase]
  let fl : Q.A.left ⟶ T.t.G.left := m.cart.1.lift (χ₀ ≫ m1.φ) Q.A.hom w1
  have hfl : fl ≫ m.φ = χ₀ ≫ m1.φ := m.cart.1.lift_fst _ _ w1
  have hflb : fl ≫ T.t.G.hom = Q.A.hom := m.cart.1.lift_snd _ _ w1
  let f : Q.A ⟶ T.pol.A := Over.homMk fl hflb
  refine ⟨f, ?_, ?_, ?_⟩
  ·
    refine GlobalTheory.DivisibleHom.isMonHom_of_mul_points f fun S x y => ?_
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · have e1 := hχ.2 S x y (pushPt hχ.1.w x) (pushPt hχ.1.w y) rfl rfl
      have e2 := m.cart.2 S (x ≫ f) (y ≫ f) (pushPt m.cart.1.w (x ≫ f)) (pushPt m.cart.1.w (y ≫ f)) rfl rfl
      rw [Over.comp_left, Category.assoc]
      change _ ≫ fl ≫ m.φ = _
      rw [hfl, ← e1, ← e2]
      refine mul_left_congr (by rw [hbase]) _ _ _ _ ?_ ?_
      · show x.left ≫ χ₀ ≫ m1.φ = (x.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
      · show y.left ≫ χ₀ ≫ m1.φ = (y.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
    · exact (Over.w ((x * y) ≫ f)).trans (Over.w ((x ≫ f) * (y ≫ f))).symm
  ·
    obtain ⟨wT, hwT, -⟩ := m.lin
    obtain ⟨w1', hw1', -⟩ := m1.lin
    obtain ⟨w2', hw2', -⟩ := m2.lin
    have hT : LBIso T.t.PP.L (Xo.univ.t.PP.L.pull m.φ) := ⟨wT, hwT⟩
    have h1 : LBIso t₀.PP.L (Xo.univ.t.PP.L.pull m1.φ) := ⟨w1', hw1'⟩
    have h2 : LBIso t₀.PP.L (B.t.PP.L.pull m2.φ) := ⟨w2', hw2'⟩
    have hT2 := GlobalTheory.CM.EllComp.lbIso_pull_comp hT.symm fl
    rw [hfl] at hT2
    have h3 := GlobalTheory.CM.EllComp.lbIso_pull_comp h1.symm χ₀
    have h4 := GlobalTheory.CM.EllComp.lbIso_pull_comp h2.symm χ₀
    rw [hχ₀2] at h4
    have h5 : LBIso (B.t.PP.L.pull (ψ ≫ F.φ)) (F.P₀.L.pull ψ) := GlobalTheory.CM.EllComp.lbIso_pull_comp F.fib.2.2 ψ
    have e45 := LBIso.trans (pull_isLB B.t.PP.isLB _) (pull_isLB F.P₀.isLB ψ) Q.isLB h5 hQ.2.2
    have e345 := LBIso.trans (pull_isLB t₀.PP.isLB χ₀) (pull_isLB B.t.PP.isLB _) Q.isLB h4.symm e45
    have e2345 := LBIso.trans (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB t₀.PP.isLB χ₀) Q.isLB h3 e345
    have main : LBIso (T.t.PP.L.pull fl) Q.L :=
      LBIso.trans (pull_isLB T.t.PP.isLB fl) (pull_isLB Xo.univ.t.PP.isLB _) Q.isLB hT2.symm e2345
    exact GlobalTheory.lbIso_lbPow main 1
  ·
    intro i q hq w' hw'
    obtain ⟨u, w, hu1, hu2, hw⟩ := hFC i
    haveI := GlobalTheory.ShFam.OpenReg.mono_spMap_algebraMap (𝓞 K) K
    have hFw : F.φ ≫ B.t.G.hom = F.P₀.A.hom ≫ spMap (algebraMap (𝓞 K) K) := F.fib.2.1.1.w
    have hu3 : u ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
      rw [← cancel_mono (spMap (algebraMap (𝓞 K) K))]
      calc (u ≫ t₀.G.hom) ≫ spMap (algebraMap (𝓞 K) K) = (u ≫ m2.φ) ≫ B.t.G.hom := by
            rw [Category.assoc, Category.assoc, m2.cart.1.w]
        _ = (w.left ≫ F.P₀.A.hom) ≫ spMap (algebraMap (𝓞 K) K) := by
            rw [hu2, Category.assoc, hFw, Category.assoc]
        _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap (𝓞 K) K) := by rw [Over.w w]; rfl
    obtain ⟨q', hq', -⟩ := GlobalTheory.existsUnique_isVecOver hQ.2.1.1 w
    have hq'c : IsLieComb (fun k => σ (v i k)) v' q' := by
      let d := ReciprocityTheory.ChartRestriction.G.Chart.dualMapR σ
      have dover : spMap d ≫ spMap (algebraMap K (DualNumber K)) =
          spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := by
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext r <;> simp [d, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
      have dscale (a : K) : spMap d ≫ spMap (epsScaleR a) =
          spMap (epsScaleR (σ a)) ≫ spMap d := by
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext r <;> simp [d, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
      rw [GlobalTheory.ArcQ.NormalForm.isLieComb_iff] at hw ⊢
      let U : Over.mk ((epsR ℂ).hom ≫ spMap σ) ⟶ epsR K := Over.homMk (spMap d) dover
      have e₁ := map_list_prod (pushHom hQ.2.1 (epsR ℂ)) (List.ofFn fun k => GlobalTheory.ArcQ.NormalForm.sc (σ (v i k)) ≫ v' k)
      have e₂ := map_list_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := F.P₀.A) U) (List.ofFn fun k => GlobalTheory.ArcQ.NormalForm.sc (v i k) ≫ F.v k)
      rw [List.map_ofFn] at e₁ e₂
      have e₃ : (pushHom hQ.2.1 (epsR ℂ)) ∘ (fun k => GlobalTheory.ArcQ.NormalForm.sc (σ (v i k)) ≫ v' k) =
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := F.P₀.A) U) ∘ fun k => GlobalTheory.ArcQ.NormalForm.sc (v i k) ≫ F.v k :=
        funext fun k => Over.OverMorphism.ext (by
          show (spMap (epsScaleR (σ (v i k))) ≫ (v' k).left) ≫ ψ =
            spMap d ≫ spMap (epsScaleR (v i k)) ≫ (F.v k).left
          rw [Category.assoc, hv', ← Category.assoc, ← Category.assoc, dscale])
      rw [e₃, ← e₂, ← hw] at e₁
      apply Over.OverMorphism.ext
      apply hQ.2.1.1.hom_ext
      · exact hq'.trans (congrArg (·.left) e₁).symm
      · rw [Over.w, Over.w]
    have hqq : q = q' := by
      obtain ⟨a, ha, rfl⟩ := hq
      obtain ⟨b, hb, rfl⟩ := hq'c
      have hab : a = b := funext fun k => Over.OverMorphism.ext ((ha k).trans (hb k).symm)
      rw [hab]
    subst hqq
    have key : q.left ≫ χ₀ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR σ) ≫ u := by
      apply m2.cart.1.hom_ext
      · rw [Category.assoc, hχ₀2, Category.assoc, hu2, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ F.φ) hq'
      · rw [Category.assoc, hχ₀b, Category.assoc, hu3, ← Category.assoc, Over.w q]
        show spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ = _
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext a <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hw', hz.2.1, ← hu1, hφσ]
      change (q.left ≫ fl) ≫ m.φ = _
      rw [Category.assoc, hfl, ← Category.assoc, key, Category.assoc]
      rfl
    · exact (Over.w (q ≫ f)).trans (Over.w w').symm

end GlobalTheory.PtDeg
end
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lact_one_self {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((↑(1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) = y τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

theorem isTransp_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp), IsTransp p r i v ψ 1 k k 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hm r h ho i v ψ k
  have hl := h.laws v
  obtain ⟨-, hA, -, -, -, -, hj⟩ := GlobalTheory.PinNum.numerics_of_pins D (r.used v).full.Q hl.p.pins
  obtain ⟨hpq, hr, -⟩ := hj ((i : ℕ) + 1) ⟨by omega, by omega⟩
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1) (by rw [hpq]; exact hr) hA
  refine ⟨GlobalTheory.LevelCusp.isMatch_of_isUStab _ ⟨fun x y => by simp, fun x => by simp⟩, fun x hx => ?_, fun w => ?_⟩
  · have e : castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x) = x := by
      rw [lact_one_self]; rfl
    refine ⟨by rw [e]; exact hx, 1, ?_⟩
    have ey : (uAt r v i).un k ⟨castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x), by rw [e]; exact hx⟩ =
        (uAt r v i).un k ⟨x, hx⟩ := congrArg _ (Subtype.ext e)
    have hf := hL.func 1 _ ((uAt r v i).un k ⟨x, hx⟩) ((uAt r v i).un k ⟨x, hx⟩)
      (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩))
      (hL.one _ _) (Formalism.L2.Pj.mvPt_spec hL.total 1 _)
    have hy : (uAt r v i).un k ⟨x, hx⟩ =
        mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩) :=
      (GlobalTheory.LevelLawsCompare.frMap_id_iff _ _).1 hf
    rw [ey]
    exact (congrArg (FrBor 1 ((uAt r v i).un k ⟨x, hx⟩)) hy).mp (GlobalTheory.ShFam.Descent.frBor_one _)
  · have hw : Matrix.mulVec ((1 : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)
        (w : Fin D.R.r → D.host.E) ∈ ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.lattice₂ D ((uAt r v i).X k).Λ := by
      rw [Units.val_one, Matrix.one_mulVec]; exact w.2
    refine ⟨hw, ?_⟩
    calc Submodule.Quotient.mk ⟨_, hw⟩ = Submodule.Quotient.mk w :=
          congrArg _ (Subtype.ext (Matrix.one_mulVec _))
      _ = ψ k ((ψ k).symm (Submodule.Quotient.mk w)) := ((ψ k).apply_symm_apply _).symm
      _ = _ := rfl
end GlobalTheory.ShareOn

end
end
