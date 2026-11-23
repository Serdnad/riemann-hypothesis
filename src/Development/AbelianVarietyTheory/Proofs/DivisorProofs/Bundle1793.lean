module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047

@[expose] public section

section

namespace ConjugatePlaceIntegrality
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.ConjPlaceInt

variable {D : D7}

theorem sg_mem_OA {x : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D} (hx : x ∈ OA D) : sg D x ∈ OA D :=
  Formalism.UG.P.csDual_sig_mem D.sp.cm.sig hx

theorem cpt_sg_mem_integers : ∀ {D : D7} (Q : Pl D.host.E) (z : Lev.EAf D),
    cpt Q z ∈ Q.adicCompletionIntegers D.host.E →
      cpt (GlobalTheory.IdemSupport.cP Q) (sg D z) ∈ (GlobalTheory.IdemSupport.cP Q).adicCompletionIntegers D.host.E := by
  intro D Q z hz
  obtain ⟨e, -, -, h1, h0⟩ := GlobalTheory.StdFrames.exists_idem (D := D) ({Q} : Set (Pl D.host.E))
  have he1 : cpt Q e = 1 := h1 Q rfl
  have hez : e * z ∈ OA D := (mem_OA_iff _).2 fun P => by
    by_cases hP : P = Q
    · subst hP
      rw [map_mul, he1, one_mul]
      exact hz
    · rw [map_mul, h0 P hP, zero_mul]
      exact zero_mem _
  have hs : cpt (GlobalTheory.IdemSupport.cP Q) (sg D e) = 1 := by
    have h2 : cpt (GlobalTheory.IdemSupport.cP Q) (sg D (1 - e)) = 0 :=
      cpt_sg_eq_zero (by rw [cP_cP, map_sub, map_one, he1, sub_self])
    rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h2
    exact h2.symm
  have h3 := (mem_OA_iff _).1 (sg_mem_OA hez) (GlobalTheory.IdemSupport.cP Q)
  rwa [map_mul, map_mul, hs, one_mul] at h3

end GlobalTheory.CompanionTheory.ConjPlaceInt

end
end

end ConjugatePlaceIntegrality
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

end
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LieBasisRing

open GlobalTheory.KSExist.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isSplitting_embS {l : Level H} (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => (algebraMap c.F S).comp (embK c σ) := by
  refine EigenSplit.isSplitting_of_isDomain (S := c.F) (σ := fun σ : E →+* ℂ => embK c σ) (fun σ σ' e => ?_)
    (NumberField.Embeddings.card E ℂ) _ ?_
  · have e' : embF c σ = embF c σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e
    ext x
    have := congrArg (fun f : E →+* c.F => ((f x : c.F) : ℂ)) e'
    exact this
  · have : IsUnit ((NumberField.discr E : ℤ) : c.F) :=
      isUnit_iff_ne_zero.2 (by exact_mod_cast NumberField.discr_ne_zero E)
    simpa using this.map (algebraMap c.F S)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
  {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}

theorem isCombAt_of_isLieComb (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR S ⟶ A))
    (cf : Fin n → S) (w : epsR S ⟶ A) (h : IsLieComb cf v w) :
    IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => pushHom hπ (epsR S) (u i), fun i => ?_, (push_prod hπ u).symm⟩
  show (u i).left ≫ π = _
  rw [hu i, Category.assoc]
  rfl

end GlobalTheory.LieBasisRing

namespace GlobalTheory.LieBasisRing

theorem span_eq_top {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O]
    (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* S} (hχ : EigenSplit.IsSplitting χ)
    {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR S ⟶ A)) (hub : ∀ σ k, IsTangent (ub σ k))
    (hbasis : ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w) :
    Submodule.span S (Set.range fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)) = ⊤ := by
  let ρ : O →+* Module.End S (Serre.Lie a) := Module.toModuleEnd S (S := O) (Serre.Lie a)
  rw [eq_top_iff]
  intro x _
  rw [← EigenSplit.sum_proj hχ ρ x]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hx := EigenSplit.proj_mem hχ ρ σ x
  obtain ⟨cf, hcf⟩ := hbasis σ (EigenSplit.proj hχ ρ σ x).hom (EigenSplit.proj hχ ρ σ x).isTangent fun z =>
    congrArg Serre.Lie.hom (EigenSplit.mem_eigenSub.1 hx z)
  have e : EigenSplit.proj hχ ρ σ x = ∑ i, cf i • Serre.Lie.mk a (ub σ i) (hub σ i) :=
    Serre.Lie.ext ((Serre.Lie.isLieComb_iff cf (fun i => Serre.Lie.mk a (ub σ i) (hub σ i)) _).1 hcf)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, i⟩, rfl⟩)

theorem linearIndependent {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] [IsCommMonObj A] {O : Type}
    [CommRing O] (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* S}
    (hχ : EigenSplit.IsSplitting χ) {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR S ⟶ A))
    (hub : ∀ σ k, IsTangent (ub σ k))
    (heig : ∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ ub σ k)
    (huniq : ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∀ cf cf', IsLieComb cf (ub σ) w → IsLieComb cf' (ub σ) w → cf = cf') :
    LinearIndependent S fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _) := by
  let ρ : O →+* Module.End S (Serre.Lie a) := Module.toModuleEnd S (S := O) (Serre.Lie a)
  let v : (Σ σ, Fin (m σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)
  have hmem : ∀ k, v k ∈ EigenSplit.eigenSub ρ (χ k.1) := fun k =>
    EigenSplit.mem_eigenSub.2 fun z => Serre.Lie.ext (heig k.1 k.2 z)
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  obtain ⟨σ, i⟩ := k
  have h1 := congrArg (EigenSplit.proj hχ ρ σ) hg

  rw [map_sum, map_zero, Fintype.sum_sigma] at h1
  have h2 : ∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩ = 0 := by
    rw [← h1, Finset.sum_eq_single σ]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, EigenSplit.proj_of_mem hχ (hmem ⟨σ, j⟩)]
    · intro σ' _ hσ'
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, EigenSplit.proj_of_mem_ne hχ hσ' (hmem ⟨σ', j⟩), smul_zero]
    · intro h; exact absurd (Finset.mem_univ σ) h
  have hw : ∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩ ∈ EigenSplit.eigenSub ρ (χ σ) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem ⟨σ, j⟩)
  have c1 : IsLieComb (fun j => g ⟨σ, j⟩) (ub σ) (∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩).hom :=
    (Serre.Lie.isLieComb_iff _ (fun j => v ⟨σ, j⟩) _).2 rfl
  have c0 : IsLieComb (0 : Fin (m σ) → S) (ub σ) (∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩).hom :=
    (Serre.Lie.isLieComb_iff _ (fun j => v ⟨σ, j⟩) _).2 (by rw [h2]; simp)
  have := huniq σ _ (Serre.Lie.isTangent _) (fun z => congrArg Serre.Lie.hom (EigenSplit.mem_eigenSub.1 hw z))
    _ _ c1 c0
  exact congrFun this i

end GlobalTheory.LieBasisRing

namespace GlobalTheory.LieBasisRing

open GlobalTheory.KSExist.FrameLift

theorem lifts_basis_mod_fil : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left},
    IsGrpPullback A Xo.univ.t.G y.x π →
    ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) →
    ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) →
    Submodule.span S (Set.range hb) ⊔ Fil A = ⊤ ∧
      LinearIndependent S (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  intro P E _ _ _ H Dw l Xo c S _ _ y A _ π hπ ub hub hb hhb
  classical
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have : IsCommMonObj A := hA.comm
  obtain ⟨a, ha⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback Xo.univ.t.act hπ
  have htan : ∀ σ k, IsTangent (ub σ k) := fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k)
  have heig : ∀ σ k z, ub σ k ≫ a.act z =
      GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ ub σ k := fun σ k z =>
    (eig_iff hπ (ha z) _ _).1 (by rw [hub]; exact y.eig σ k z)
  have eu : ∀ σ, y.u σ = fun i => (ub σ i).left ≫ π := fun σ => funext fun i => (hub σ i).symm
  have hbasis : ∀ σ (w : epsR S ⟶ A), IsTangent w →
      (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w := by
    intro σ w ht he
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [eu σ] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩
  have huniq : ∀ σ (w : epsR S ⟶ A), IsTangent w →
      (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ w) →
      ∀ cf cf', IsLieComb cf (ub σ) w → IsLieComb cf' (ub σ) w → cf = cf' := by
    intro σ w ht he cf cf' h h'
    obtain ⟨cf₀, -, hu⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    have k := isCombAt_of_isLieComb hπ _ cf w h
    have k' := isCombAt_of_isLieComb hπ _ cf' w h'
    rw [← eu σ] at k k'
    exact (hu cf k).trans (hu cf' k').symm
  have L := (P.2.1 S A _ hA gA).1
  let v : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub k.1 k.2) (htan _ _)
  have hχ := isSplitting_embS (E := E) c S
  have hspan : Submodule.span S (Set.range v) = ⊤ := span_eq_top a hχ ub htan hbasis
  have hind : LinearIndependent S v := linearIndependent a hχ ub htan heig huniq
  have hv : (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = (L.quotEquiv a).symm ∘ v := by
    funext k
    rw [Function.comp_apply, LinearEquiv.eq_symm_apply, LieExact.quotEquiv_mk, L.toLie_eq_iff]
    exact hhb k
  refine ⟨?_, hv ▸ hind.map' _ (L.quotEquiv a).symm.ker⟩
  have h1 : Submodule.map (Fil A).mkQ (Submodule.span S (Set.range hb)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span S (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = ⊤
    rw [hv, Set.range_comp, eq_top_iff]
    intro q _
    have hq : (L.quotEquiv a) q ∈ Submodule.span S (Set.range v) := hspan ▸ Submodule.mem_top
    simpa using hq
  have h2 := congrArg (Submodule.comap (Fil A).mkQ) h1
  rwa [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] at h2

end GlobalTheory.LieBasisRing
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps
open Formalism.L2.Host (atFin IsUnitAt)

noncomputable section

namespace GlobalTheory.GaussMod

variable {E : Type} [Field E] [NumberField E]

theorem locK_congr {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (hχ : χ.LevelLe w a) {x y : 𝓞 E}
    (hx : x ∉ w.asIdeal) (hy : y ∉ w.asIdeal) (hx0 : (x : E) ≠ 0) (hy0 : (y : E) ≠ 0) (h : x - y ∈ w.asIdeal ^ a) :
    χ.locK w (Units.mk0 (x : E) hx0) = χ.locK w (Units.mk0 (y : E) hy0) := by
  have hval : ∀ z : E, Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z := fun z =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w z
  have hx1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hx
  have hy1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hy
  have h1 : χ.loc w (atFin w (Units.mk0 _ hx0 * (Units.mk0 _ hy0)⁻¹)) = 1 := by
    have e : ((atFin w (Units.mk0 _ hx0 * (Units.mk0 _ hy0)⁻¹) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        algebraMap E (w.adicCompletion E) ((x : E) / y) := by
      simp [atFin, div_eq_mul_inv]
    refine hχ _ ?_ ?_
    · rw [IsUnitAt, e, hval, map_div₀, hx1, hy1, div_one]
    · rw [e, ← map_one (algebraMap E (w.adicCompletion E)), ← map_sub, hval, div_sub_one hy0, map_div₀, hy1, div_one]
      exact valuation_sub_le h
  rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem gaussSumAt_normSq (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ) (ha : a ≠ 0) (hE : ExpAt χ w a)
    (hu : IsUnitary χ) (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) :
    ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := by
  classical
  have hχ : χ.LevelLe w a := (hE a).2 le_rfl
  have := w.isMaximal
  set P := w.asIdeal with hP
  have hfin : Finite (𝓞 E ⧸ P ^ a) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.ne_bot)
  haveI : Fintype (𝓞 E ⧸ P ^ a) := Fintype.ofFinite _
  have hval : ∀ z : E, Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z := fun z =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w z
  have hne0 : ∀ x : 𝓞 E, x ∉ P → (x : E) ≠ 0 := fun x hx h0 => hx (by
    have : x = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    rw [this]; exact P.zero_mem)
  let f : 𝓞 E → ℂ := fun x => psiAt w (algebraMap E (w.adicCompletion E) ((x : E) / c))
  have f_add : ∀ x y, f (x + y) = f x * f y := fun x y => by
    have e : ((x + y : 𝓞 E) : E) / c = (x : E) / c + (y : E) / c := by push_cast; ring
    show psiAt w _ = psiAt w _ * psiAt w _
    rw [e, map_add (f := _), psiAt_add]
  have f_zero : ∀ x ∈ P ^ a, f x = 1 := fun x hx => by
    apply psiAt_eq_one
    have h1 := valuation_sub_le (w := w) (y := x) (y' := 0) (by simpa using hx)
    rw [hval, map_div₀, hc, div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
    convert h1 using 2 <;> (push_cast; ring)
  have f_congr : ∀ x y, x - y ∈ P ^ a → f x = f y := fun x y h => by
    rw [show x = y + (x - y) by ring, f_add, f_zero _ h, mul_one]
  let ψb : AddChar (𝓞 E ⧸ P ^ a) ℂ :=
    { toFun := fun q => f (Quotient.out q)
      map_zero_eq_one' := f_zero _ (by rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out])
      map_add_eq_mul' := fun q r => by
        rw [← f_add]
        apply f_congr
        rw [← Ideal.Quotient.eq, map_add (f := _), Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] }
  have ψb_mk : ∀ x, ψb (Ideal.Quotient.mk _ x) = f x := fun x =>
    f_congr _ _ (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out])
  have hout : ∀ u : (𝓞 E ⧸ P ^ a)ˣ, (Quotient.out (u : 𝓞 E ⧸ P ^ a) : 𝓞 E) ∉ P := out_notMem w ha
  have h1P : (1 : 𝓞 E) ∉ P := (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  let χb : (𝓞 E ⧸ P ^ a)ˣ →* ℂˣ :=
    { toFun := fun u => χ.locK w (Units.mk0 _ (hne0 _ (hout u)))
      map_one' := by
        rw [locK_congr hχ (hout 1) h1P _ (hne0 _ h1P)
          (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out, map_one, Units.val_one])]
        rw [show (Units.mk0 (((1 : 𝓞 E)) : E) (hne0 _ h1P)) = 1 by ext; simp, map_one]
      map_mul' := fun u v => by
        have hm : (Quotient.out ((u * v : (𝓞 E ⧸ P ^ a)ˣ) : 𝓞 E ⧸ P ^ a) : 𝓞 E) -
            Quotient.out (u : 𝓞 E ⧸ P ^ a) * Quotient.out (v : 𝓞 E ⧸ P ^ a) ∈ P ^ a := by
          rw [← Ideal.Quotient.eq, map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out,
            Units.val_mul]
        have hp : Quotient.out (u : 𝓞 E ⧸ P ^ a) * Quotient.out (v : 𝓞 E ⧸ P ^ a) ∉ P := fun h =>
          (w.isPrime.mem_or_mem h).elim (hout u) (hout v)
        rw [locK_congr hχ (hout _) hp _ (hne0 _ hp) hm, ← map_mul]
        congr 1
        ext
        simp }
  have hG : gaussSumAt χ w a c = ∑ u : (𝓞 E ⧸ P ^ a)ˣ, (((χb u)⁻¹ : ℂˣ) : ℂ) * ψb (u : 𝓞 E ⧸ P ^ a) := by
    rw [gaussSumAt, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [gaussTerm, dite_eq_right (hne0 _ (hout u))]
    rfl
  have hM : ∀ q : 𝓞 E ⧸ P ^ a, IsUnit q ↔ q ∉ P.map (Ideal.Quotient.mk (P ^ a)) := fun q => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.mem_quotient_iff_mem (Ideal.pow_le_self ha)]
    constructor
    · intro hu hx
      have h1 := hu.map (Ideal.Quotient.factor (Ideal.pow_le_self ha : P ^ a ≤ P))
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx] at h1
      have := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
      exact not_isUnit_zero h1
    · exact Ideal.Quotient.isUnit_mk_pow_of_notMem P
  have hψ : ∀ d : 𝓞 E ⧸ P ^ a, (∀ x, ψb (d * x) = 1) → d = 0 := fun d hd => by
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine GlobalTheory.GaussModulus.mem_pow_of_psiAt_trivial w a c hc d fun x => ?_
    have := hd (Ideal.Quotient.mk _ x)
    rw [← map_mul, ψb_mk] at this
    simpa [f] using this
  obtain ⟨r, ur, hur, hrP, hr1, hrχ⟩ := GlobalTheory.GaussModulus.exists_int_witness χ w a ha hE
  have hr0 : (r : E) ≠ 0 := hne0 r hrP
  have hur' : ur = Units.mk0 (r : E) hr0 := Units.ext hur
  rw [hur'] at hrχ
  obtain ⟨t, ht⟩ := Ideal.Quotient.isUnit_mk_pow_of_notMem P (n := a) hrP
  have hχt : ∃ t : (𝓞 E ⧸ P ^ a)ˣ, (∀ m ∈ P.map (Ideal.Quotient.mk (P ^ a)), ((t : 𝓞 E ⧸ P ^ a) - 1) * m = 0) ∧
      χb t ≠ 1 := by
    refine ⟨t, fun m hm => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [Ideal.mem_quotient_iff_mem (Ideal.pow_le_self ha)] at hm
      rw [ht, ← map_one (Ideal.Quotient.mk (P ^ a)), ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have e : P ^ (a - 1) * P = P ^ a := by rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 ha)]
      rw [← e]
      exact Ideal.mul_mem_mul hr1 hm
    · show χ.locK w _ ≠ 1
      rwa [locK_congr hχ (hout t) hrP _ hr0 (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out, ht])]
  obtain ⟨t0, ht0, hχ0⟩ := hχt
  have hnorm : ∀ u : (𝓞 E ⧸ P ^ a)ˣ, ‖((χb u : ℂˣ) : ℂ)‖ = 1 := fun u => hu _
  have hG' : gaussSumAt χ w a c = ∑ u : (𝓞 E ⧸ P ^ a)ˣ, (((χb u : ℂˣ) : ℂ))⁻¹ * ψb (u : 𝓞 E ⧸ P ^ a) := by
    rw [hG]
    simp only [Units.val_inv_eq_inv_val]
  rw [hG', GlobalTheory.gauss_units_norm_sq _ hM ψb hψ (fun u => ((χb u : ℂˣ) : ℂ)) (fun u v => by rw [map_mul, Units.val_mul])
    hnorm t0 ht0 (fun h => hχ0 (Units.ext h)), Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    map_pow]
  push_cast
  rfl

end GlobalTheory.GaussMod
end
end

section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.holAtlas_isForm_del : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → A.IsForm (A.del α) := by
  first | exact @GlobalTheory.CxForm.DelForm.isForm_del | exact GlobalTheory.CxForm.DelForm.isForm_del | (intros; apply GlobalTheory.CxForm.DelForm.isForm_del <;> assumption)
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.holAtlas_isForm_pullback_holomorphic : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A'.IsForm (A.pullback A' f α) := by
  first | exact @GlobalTheory.PullbackForm.isForm_pullback | exact GlobalTheory.PullbackForm.isForm_pullback | (intros; apply GlobalTheory.PullbackForm.isForm_pullback <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ j, chernAt T v j = aeval (fun i => ofValues (ddc (fun x => -Real.log (d i x)) v)) (esymm (Fin s) ℂ j) := by
  first | exact @GlobalTheory.ChernTri.chernAt_tri | exact GlobalTheory.ChernTri.chernAt_tri | (intros; apply GlobalTheory.ChernTri.chernAt_tri <;> assumption)
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.del_dbar_chainRule_holomorphicPullback : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (β : V n → Alt n) (v : V m), IsOpen U → v ∈ U → DifferentiableOn ℂ τ U →
    (∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (β y) S) (τ v)) →
    delAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (delAt β (τ v)) ∧
    dbarAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (dbarAt β (τ v)) := by
  first | exact @GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp | exact GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp | (intros; apply GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_isotropic_places_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) := by
  first | exact @GlobalTheory.PlaceIso.exists_isotropic_places | exact GlobalTheory.PlaceIso.exists_isotropic_places | (intros; apply GlobalTheory.PlaceIso.exists_isotropic_places <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (q : ℕ), q ≠ 0 → ∃ U : Subgroup (AF F ⊗[F] E)ˣ, IsOpen (U : Set (AF F ⊗[F] E)ˣ) ∧ (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → z ∈ U) ∧ ∀ k : Eˣ, Units.map (incAF F E).toMonoidHom k ∈ U → ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k ∧ (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
  first | exact @GlobalTheory.OpenCongrIdele.exists_open_congr | exact GlobalTheory.OpenCongrIdele.exists_open_congr | (intros; apply GlobalTheory.OpenCongrIdele.exists_open_congr <;> assumption)
end
