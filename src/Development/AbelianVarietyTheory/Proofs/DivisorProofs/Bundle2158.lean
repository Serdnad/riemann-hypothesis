module

public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle908
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LieBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem card_frameIdx (Dw : Datum H) :
    Fintype.card (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have h := FlagTan.isHalf_psiSet H
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [h.sum_univ (fun σ => Dw.mult σ), ← h.card, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rcases FlagTan.mult_conj (Dw := Dw) τ with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
  exact add_comm _ _

theorem isSplitting_embK {l : Level H} (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => (algebraMap c.F K).comp (embK c σ) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  refine EigenSplit.isSplitting_of_isDomain (S := c.F) (σ := fun σ : E →+* ℂ => embK c σ) (fun σ σ' e => ?_)
    (NumberField.Embeddings.card E ℂ) _ (isUnit_iff_ne_zero.2 (by exact_mod_cast NumberField.discr_ne_zero E))
  have e' : embF c σ = embF c σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e
  ext x
  have := congrArg (fun f : E →+* c.F => ((f x : c.F) : ℂ)) e'
  exact this

theorem finrank_quot_fil (P : GlobalTheory.Published.AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {g : ℕ}
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Module.Finite K (HdR A ⧸ Fil A) ∧ Module.finrank K (HdR A ⧸ Fil A) = g := by
  obtain ⟨-, -, hfin, -, hrk⟩ := P.2.1 K A g hA hg
  have hF : Module.finrank K (PrimitiveSubmodule A) = g := by
    have := hrk ⟨⊥, Ideal.isPrime_bot⟩
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  let e : (HdR A ⧸ Fil A) ≃ₗ[K] Module.Dual K (PrimitiveSubmodule A) := Subspace.quotAnnihilatorEquiv (PrimitiveSubmodule A)
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Subspace.dual_finrank_eq, hF]

theorem span_eq_top {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O]
    (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* K} (hχ : EigenSplit.IsSplitting χ)
    {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hub : ∀ σ k, IsTangent (ub σ k))
    (hbasis : ∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w) :
    Submodule.span K (Set.range fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)) = ⊤ := by
  let ρ : O →+* Module.End K (Serre.Lie a) := Module.toModuleEnd K (S := O) (Serre.Lie a)
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

end GlobalTheory.LieBasis

namespace GlobalTheory.LieBasis

theorem lifts_basis_mod_fil : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
    (y : FrPt Xo c K) {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π →
    ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) →
    ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) →
    Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ ∧
      LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  intro P E _ _ _ H Dw l Xo c K _ _ y A _ π hπ ub hub hb hhb
  classical
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have : IsCommMonObj A := hA.comm
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  obtain ⟨ub', hub', htan, -, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  have e : ub' = ub := funext fun σ => funext fun k => Over.OverMorphism.ext
    (hπ.1.hom_ext ((hub' σ k).trans (hub σ k).symm) ((Over.w (ub' σ k)).trans (Over.w (ub σ k)).symm))
  subst e
  have L := (P.2.1 K A _ hA gA).1
  let v : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub' k.1 k.2) (htan _ _)
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    span_eq_top a (isSplitting_embK c K) ub' htan hbasis
  obtain ⟨hfin, hdim⟩ := finrank_quot_fil P hA gA
  have hcard : Fintype.card (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) = Module.finrank K (Serre.Lie a) := by
    rw [← (L.quotEquiv a).finrank_eq, hdim, card_frameIdx]
  have hind : LinearIndependent K v := linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hcard
  have hv : (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = (L.quotEquiv a).symm ∘ v := by
    funext k
    rw [Function.comp_apply, LinearEquiv.eq_symm_apply, LieExact.quotEquiv_mk, L.toLie_eq_iff]
    exact hhb k
  refine ⟨?_, hv ▸ hind.map' _ (L.quotEquiv a).symm.ker⟩
  have h1 : Submodule.map (Fil A).mkQ (Submodule.span K (Set.range hb)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span K (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = ⊤
    rw [hv, Set.range_comp, eq_top_iff]
    intro q _
    have hq : (L.quotEquiv a) q ∈ Submodule.span K (Set.range v) := hspan ▸ Submodule.mem_top
    simpa using hq
  have h2 := congrArg (Submodule.comap (Fil A).mkQ) h1
  rwa [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] at h2

end GlobalTheory.LieBasis
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusModel GlobalTheory.AdicColimit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

def pushEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y =>
    ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem actPull_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] [IsCommMonObj G] {Λ : Type} [Ring Λ]
    (ρ : RingAct G Λ) (a : Λ) :
    ((actPull f ρ).act a).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ (ρ.act a).left :=
  pullback.lift_fst _ _ _

variable {p : ℕ} {R : Type} [CommRing R] {I : Ideal R} {O : Type} [CommRing O]

theorem isAdicColimit_of_isNilpotent {f : R →+* O} (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    (S : Type) [CommRing S] [Algebra O S] (hS : IsNilpotent (p : S)) :
    IsAdicColimit I (Over.mk ((specO O S).hom ≫ spMap f)) := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨m, hm⟩ := hS
  have e : (specO O S).hom ≫ spMap f = Spec.map (CommRingCat.ofHom ((algebraMap O S).comp f)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  rw [e]
  refine isAdicColimit_of_pow I _ (n * m) fun a ha => ?_
  have h₁ : (I ^ n).map f ≤ Ideal.span {(p : O)} := Ideal.map_le_iff_le_comap.2 hn
  have h₂ : f a ∈ Ideal.span {(p : O) ^ m} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono h₁ m ?_
    rw [← Ideal.map_pow, ← pow_mul]
    exact Ideal.mem_map_of_mem f ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h₂
  rw [RingHom.comp_apply, ← hc, map_mul, map_pow, map_natCast, hm, mul_zero]

variable [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} [Algebra O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ]

theorem spMap_comp_algebraMap (f : R →+* O) :
    spMap ((algebraMap O C).comp f) = spMap (algebraMap O C) ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

def ofCompletion (hv : v.Integers O) (ε : Eps p C) (f : R →+* O)
    (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (ιG : RingAct G Λ)
    {E : SplitExt (Sp R)} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] (d : E.GtDatum H) (ρ : RingAct H Λ)
    (J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G)))
    (hnat : ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ H), J T' hT' (k ≫ x) = k ≫ J T hT x)
    (hlin : ∀ T hT (x : T ⟶ H) (a : Λ), J T hT (x ≫ ρ.act a) = J T hT x ≫ ιG.act a)
    (A' : PolAV (Sp C)) (oA' : A'.OAct Λ) (j : A'.A.left ⟶ G.left)
    (hj : IsGrpPullback A'.A G (spMap ((algebraMap O C).comp f)) j)
    (hact : ∀ a, (oA'.act a).left ≫ j = j ≫ (ιG.act a).left) : Point p v O Λ where
  integers := hv
  eps := ε
  A := A'
  oA := oA'
  G := (Over.pullback (spMap f)).obj G
  semi := IsSemiAbelian.pullback _ G hG
  gen := pullback.lift j (A'.A.hom ≫ spMap (algebraMap O C))
    (by rw [hj.1.w, spMap_comp_algebraMap, Category.assoc])
  gen_pull := (isGrpPullback_pullback G (spMap f)).cancel
    (hj.congr (spMap_comp_algebraMap f) (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  oG := actPull (spMap f) ιG
  gen_act a := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hact, Category.assoc, actPull_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, pullback.lift_snd, Over.w_assoc, Category.assoc]
      exact ((congrArg (_ ≫ ·) (Over.w ((actPull (spMap f) ιG).act a))).trans (pullback.lift_snd _ _ _)).symm
  Ext := GtBaseChange.extBC (spMap f) E
  Gt := (Over.pullback (spMap f)).obj H
  D := (GtBaseChange.isGt_extBC (spMap f) E H d).some
  oGt := actPull (spMap f) ρ
  cmp S _ _ hS := (pushEquiv (isGrpPullback_pullback H (spMap f)) _).trans
    ((J _ (isAdicColimit_of_isNilpotent hf S hS)).trans (pushEquiv (isGrpPullback_pullback G (spMap f)) _).symm)
  cmp_nat S S' _ _ _ _ hS hS' φ x := by
    let k : Over.mk ((specO O S').hom ≫ spMap f) ⟶ Over.mk ((specO O S).hom ≫ spMap f) :=
      Over.homMk (ptMap φ).left (Over.w_assoc (ptMap φ) _)
    have e : ∀ {X : Over (Sp R)} [GrpObj X] (y : specO O S ⟶ (Over.pullback (spMap f)).obj X),
        pushEquiv (isGrpPullback_pullback X (spMap f)) _ (ptMap φ ≫ y) =
          k ≫ pushEquiv (isGrpPullback_pullback X (spMap f)) _ y := fun y =>
      Over.OverMorphism.ext (Category.assoc _ _ _)
    simp only [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_eq, e, e, MulEquiv.apply_symm_apply, hnat]
  cmp_act S _ _ hS a x := by
    have e : ∀ {X : Over (Sp R)} [GrpObj X] [IsCommMonObj X] (α : RingAct X Λ)
        (y : specO O S ⟶ (Over.pullback (spMap f)).obj X),
        pushEquiv (isGrpPullback_pullback X (spMap f)) _ (y ≫ (actPull (spMap f) α).act a) =
          pushEquiv (isGrpPullback_pullback X (spMap f)) _ y ≫ α.act a := fun α y =>
      Over.OverMorphism.ext ((Category.assoc _ _ _).trans
        ((congrArg (y.left ≫ ·) (actPull_fst _ α a)).trans (Category.assoc _ _ _).symm))
    simp only [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_eq, e, e, MulEquiv.apply_symm_apply, hlin]

section Unif

variable [IsDomain R] {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G)

theorem exists_comparison : ∃ (H : Over (Sp R)) (_ : GrpObj H) (_ : IsCommMonObj H)
    (Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T) (J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G))),
    (splitExt D.toPre).IsGt H ∧ Represents Φ ∧
      (∀ T hT w x, J T hT w = x ↔ FormalPoint.IsPointOf U (Φ T w) x) ∧
      ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ H), J T' hT' (k ≫ x) = k ≫ J T hT x := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL hH
  obtain ⟨J, hJ⟩ := exists_mulEquiv U hL (Φ := Φ) hΦ
  exact ⟨H, inferInstance, inferInstance, Φ, J, hH, hΦ, hJ, fun T T' hT hT' k x =>
    (hJ _ hT' _ _).2 (((hJ _ hT x _).1 rfl).pull k (hΦ.1 _ _ k _))⟩

theorem exists_point_of_unif (hG : IsSemiAbelian G) [Module Λ D.toPre.X] {ιD : D.OAct Λ} {ιA : A.OAct Λ}
    {ιG : RingAct G Λ} (hO : U.OLinear Λ ιD ιA ιG) (hv : v.Integers O) (ε : Eps p C) (f : R →+* O)
    (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    (A' : PolAV (Sp C)) (oA' : A'.OAct Λ) (j : A'.A.left ⟶ G.left)
    (hj : IsGrpPullback A'.A G (spMap ((algebraMap O C).comp f)) j)
    (hact : ∀ a, (oA'.act a).left ≫ j = j ≫ (ιG.act a).left) :
    ∃ (H : Over (Sp R)) (_ : GrpObj H) (_ : IsCommMonObj H) (Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T)
      (ρ : RingAct H Λ) (P : Point p v O Λ),
      (splitExt D.toPre).IsGt H ∧ Represents Φ ∧
      (∀ (a : Λ) T (x : T ⟶ H), FormalPoint.IsSmulPt ιD a (Φ T x) (Φ T (x ≫ ρ.act a))) ∧
      P.eps = ε ∧ P.A = A' ∧ HEq P.oA oA' ∧ P.G = (Over.pullback (spMap f)).obj G ∧
      P.Ext = GtBaseChange.extBC (spMap f) (splitExt D.toPre) ∧ P.Gt = (Over.pullback (spMap f)).obj H ∧
      ∃ (πG : P.G.left ⟶ G.left) (πH : P.Gt.left ⟶ H.left) (hπG : IsGrpPullback P.G G (spMap f) πG)
        (hπH : IsGrpPullback P.Gt H (spMap f) πH),
        HEq πG (pullback.fst G.hom (spMap f)) ∧ HEq πH (pullback.fst H.hom (spMap f)) ∧
        HEq (P.gen ≫ πG) j ∧
        (∀ a, (P.oG.act a).left ≫ πG = πG ≫ (ιG.act a).left) ∧
        (∀ a, (P.oGt.act a).left ≫ πH = πH ≫ (ρ.act a).left) ∧
        ∀ (S : Type) [CommRing S] [Algebra O S] (hS : IsNilpotent (p : S)) (x : specO O S ⟶ P.Gt),
          FormalPoint.IsPointOf U (Φ _ (pushPt hπH.1.w x)) (pushPt hπG.1.w (P.cmp S hS x)) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, Φ, J, ⟨d⟩, hΦ, hJ, hnat⟩ := exists_comparison U
  obtain ⟨ρ, hρ⟩ := exists_ringAct hL ιD (Φ := Φ) hΦ
  refine ⟨H, inferInstance, inferInstance, Φ, ρ, ofCompletion hv ε f hf hG ιG d ρ J hnat
      (fun T hT x a => (hJ _ hT _ _).2 (((hJ _ hT x _).1 rfl).smul hL hO a (hρ a _ _))) A' oA' j hj hact,
    ⟨d⟩, hΦ, hρ, rfl, rfl, HEq.rfl, rfl, rfl, rfl, _, _, isGrpPullback_pullback G _, isGrpPullback_pullback H _,
    HEq.rfl, HEq.rfl, heq_of_eq (pullback.lift_fst _ _ _), actPull_fst _ ιG, actPull_fst _ ρ, fun S _ _ hS x => ?_⟩
  exact (hJ _ (isAdicColimit_of_isNilpotent hf S hS) _ _).1
    ((pushEquiv (isGrpPullback_pullback G (spMap f)) _).apply_symm_apply _).symm

end Unif

end GlobalTheory.HTLat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SymPrincipalTranslate
open GlobalTheory.CechPic

theorem pull_local_eq_zero {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (c : Pic X) :
    pull f c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hc : f.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  exact GlobalTheory.KTrivOfLam.pull_eq_zero_of_chart hL f i fun y =>
    ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open (L.U i).isOpen hi

theorem cls_lam_div {S : Scheme.{0}} {G : Over S} [GrpObj G] {L M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : (abelian₂ G (LB.div L M)).IsLB) (h₁ : (abelian₂ G L).IsLB) (h₂ : (abelian₂ G M).IsLB) :
    cls _ h = cls _ h₁ - cls _ h₂ := by
  rw [show cls (abelian₂ G (LB.div L M)) h = _ from cls_linComb (LB.isLB_div hL hM) _ _ h,
    show cls (abelian₂ G L) h₁ = _ from cls_linComb hL _ _ h₁, show cls (abelian₂ G M) h₂ = _ from cls_linComb hM _ _ h₂,
    cls_div hL hM, ← Finset.sum_sub_distrib]
  simp only [map_sub, smul_sub]

theorem exists_two_torsion_rigTransl : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (L' : LB P.A.left), L'.IsLB → Rigidified P.A L' → Sym P.A L' → LBIso (abelian₂ P.A L') (abelian₂ P.A P.L) → ∃ x : 𝟙_ (Over (Sp R)) ⟶ P.A, x * x = 1 ∧ LBIso L' (GlobalTheory.RigidTranslate.rigTransl P.L x) := by
  intro R _ _ _ P L' hL' _ hsym hlam
  have := P.isAb.comm
  have hO : (LB.div L' P.L).IsLB := LB.isLB_div hL' P.isLB
  have hΛ' : (abelian₂ P.A L').IsLB := LB.isLB_linComb hL' _ _
  have hΛ : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have hΛO : (abelian₂ P.A (LB.div L' P.L)).IsLB := LB.isLB_linComb hO _ _
  have hu : ∃ u : LB.Gen (abelian₂ P.A (LB.div L' P.L)), u.IsGen := by
    refine (cls_eq_zero_iff hΛO).1 ?_
    rw [cls_lam_div hL' P.isLB hΛO hΛ' hΛ, sub_eq_zero]
    exact (cls_eq_iff hΛ' hΛ).2 hlam
  obtain ⟨x, hx⟩ := GlobalTheory.LN.ega_holds.2.2.2 R P _ hO hu
  let τ : P.A ⟶ P.A := (toUnit P.A ≫ x) * 𝟙 P.A

  have hτ : cls L' hL' = pull τ.left (cls P.L P.isLB) := by
    have h1 := (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).2 hx
    rw [cls_div hL' P.isLB hO, cls_linComb P.isLB] at h1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul, pull_id] at h1
    exact sub_left_injective (h1.trans (sub_eq_add_neg _ _).symm)

  have hR : (GlobalTheory.RigidTranslate.rigTransl P.L x).IsLB := LB.isLB_linComb P.isLB _ _
  have hcR : cls _ hR = pull τ.left (cls P.L P.isLB) := by
    have e : GlobalTheory.PolTranslate.transl x = τ := by rw [GlobalTheory.PolTranslate.transl, _root_.mul_comm]
    refine (cls_linComb P.isLB _ _ hR).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul]
    rw [Over.comp_left, pull_comp, pull_local_eq_zero (R := R) x.left, map_zero, neg_zero, add_zero, e]
  refine ⟨x, ?_, (cls_eq_iff hL' hR).1 (hτ.trans hcR.symm)⟩

  have hs : pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB :=
    GlobalTheory.RigSymSubring.cls_of_sym P.isLB P.sym
  have hs' : pull (GrpObj.inv : P.A ⟶ P.A).left (cls L' hL') = cls L' hL' :=
    GlobalTheory.RigSymSubring.cls_of_sym hL' hsym
  let τ' : P.A ⟶ P.A := (toUnit P.A ≫ x⁻¹) * 𝟙 P.A
  have e1 : (GrpObj.inv : P.A ⟶ P.A) ≫ τ = τ' ≫ GrpObj.inv := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv,
      ← GrpObj.comp_inv, inv_inv, Hom.inv_def, Category.id_comp]
  have e2 : τ ≫ τ' = 𝟙 P.A := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, ← _root_.mul_assoc,
      ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.one_mul]
  have e3 : τ ≫ τ = (toUnit P.A ≫ (x * x)) * 𝟙 P.A := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, ← _root_.mul_assoc,
      ← MonObj.comp_mul]
  have h2 : pull ((toUnit P.A ≫ (x * x)) * 𝟙 P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
    have k : pull τ'.left (cls P.L P.isLB) = pull τ.left (cls P.L P.isLB) := by
      have := hs'
      rw [hτ, ← pull_comp, ← Over.comp_left, e1, Over.comp_left, pull_comp, hs] at this
      exact this
    have k2 := congrArg (pull τ.left) k
    rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, e2, e3, Over.id_left, pull_id] at k2
    exact k2.symm

  refine (P.ktriv R (𝟙 (Sp R)) (x * x) fun p => ⟨⊤, trivial, ?_⟩).trans Hom.one_def.symm
  let T : Over (Sp R) := Over.mk (𝟙 (Sp R))
  have hTD : (translDiff P.A P.L (x * x)).IsLB := LB.isLB_linComb P.isLB _ _
  refine (cls_eq_zero_iff (pull_isLB hTD _)).1 ?_
  rw [cls_pull hTD]
  suffices h0 : cls _ hTD = 0 by rw [h0, map_zero]
  have e₁ : cls _ hTD = pull (lift (fst T P.A ≫ (x * x)) (snd T P.A) ≫ μ[P.A]).left (cls P.L P.isLB) -
      pull (snd T P.A).left (cls P.L P.isLB) := by
    refine (cls_linComb P.isLB _ _ hTD).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul]
    exact (sub_eq_add_neg _ _).symm
  have e₂ : lift (fst T P.A ≫ (x * x)) (snd T P.A) ≫ μ[P.A] = snd T P.A ≫ ((toUnit P.A ≫ (x * x)) * 𝟙 P.A) := by
    show (fst T P.A ≫ (x * x)) * snd T P.A = _
    rw [MonObj.comp_mul (snd T P.A), ← Category.assoc (snd T P.A), comp_toUnit, Category.comp_id]
    congr 1
  rw [e₁, e₂, Over.comp_left, pull_comp, h2, sub_self]
end GlobalTheory.SymPrincipalTranslate
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj


theorem _root_.GlobalTheory.T.addHaarChar_leftRight_matrixMul_adeleTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j m : ℕ) [LocallyCompactSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] (g : GL (Fin j) (AF F ⊗[F] E)) (a : GL (Fin m) (AF F ⊗[F] E)), addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE g a) = absE F E (Matrix.GeneralLinearGroup.det g) ^ m * absE F E (Matrix.GeneralLinearGroup.det a) ^ j := by
  first | exact @GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE | exact GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE | (intros; apply GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem range_evAt_eq_adel_image : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, Set.range (evAt R i σ (v₀ i σ)) = adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ))) '' (Formalism.L2.Pj.holSub0 (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) : Set _) := by
  intro hc hf D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hp i σ hσ hV
  obtain ⟨hs, -, w, hw⟩ := GlobalTheory.T.holomorphicShape_integralWeight_goodEmbedding D G Pl0 T0 A T R κ v₀ hT i σ hσ
  have hg := GlobalTheory.T.coreDictionary_good_at_good_embedding D G Pl0 T0 A T R κ v₀ hL hM hT hp i σ hσ hV w hw
  have hχ := (GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM hT hp i σ hσ hV).2.1
  obtain ⟨h1, h2⟩ := GlobalTheory.T.extremalVector_eval_multiplicitySpace_onto_holomorphic hc hf D R.θ _ _ (R.MW i σ) w _ _ _ _ _ _ _ _ _ hs hg hw (v₀ i σ)
    (hT.hv₀ i σ).1 _ hχ
  have hW := hM.HW i σ
  have hr : LinearMap.range (R.HW i σ).e = R.Wall i σ := hW.2.1
  ext f
  constructor
  · rintro ⟨h, rfl⟩
    have hm : (R.HW i σ).e h ∈ R.Wall i σ := hr ▸ LinearMap.mem_range_self _ h
    obtain ⟨P, hP, e⟩ := h2 _ hm
    exact ⟨P, hP, e⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨S, hS, e⟩ := h1 P hP
    have hm : S ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hS
    obtain ⟨h, rfl⟩ := hm
    exact ⟨h, e⟩

end GlobalTheory.HolDict
end
