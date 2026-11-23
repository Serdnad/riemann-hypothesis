module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle325
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle323
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle294
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleModuleIffLatticeQuotients
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle263
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUnitTeichmullerPrincipalUnitSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfTensorLatticeSpecialisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle291
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle326
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle327
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.admT3_of_hecke_semisimple : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → D.nexp.sig_all → HkSS D → IntegralHeckeForms.GoodLatticePoints D.nexp := by
  first | exact @GlobalTheory.EigRed.admT3_of_semisimple_good | exact GlobalTheory.EigRed.admT3_of_semisimple_good | (intros; apply GlobalTheory.EigRed.admT3_of_semisimple_good <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.Models
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open scoped LaurentSeries PowerSeries

theorem exists_simple_quotient {k G : Type} [Field k] [Group G] (B : Ob k G) (hB : B.m ≠ 0) :
    ∃ (A C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom A B f ∧ IsHom B C p ∧ Function.Injective f ∧ Function.Surjective p ∧ Function.Exact f p ∧
      IsSimpleModule (MonoidAlgebra k G) C.ρ.asModule ∧ A.m < B.m := by
  haveI : Nonempty (Fin B.m) := ⟨⟨0, Nat.pos_of_ne_zero hB⟩⟩
  haveI : Nontrivial B.ρ.asModule := B.ρ.asModuleEquiv.toEquiv.nontrivial
  have hfl := finiteLength_asModule B.ρ
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  obtain ⟨S, hS, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule (MonoidAlgebra k G) B.ρ.asModule)).resolve_left
    bot_ne_top
  let S' : Submodule k (Fin B.m → k) := (S.restrictScalars k).comap B.ρ.asModuleEquiv.symm.toLinearMap
  have hinv : ∀ g, S' ≤ S'.comap (B.ρ g) := by
    intro g x hx
    have hx' : B.ρ.asModuleEquiv.symm x ∈ S := hx
    change B.ρ.asModuleEquiv.symm (B.ρ g x) ∈ S
    rw [Representation.asModuleEquiv_symm_map_rho]
    exact S.smul_mem _ hx'
  obtain ⟨A, eA, hA⟩ := exists_ob (B.ρ.subrepresentation S' hinv)
  obtain ⟨C, eC, hC⟩ := exists_ob (B.ρ.quotient S' hinv)
  have hp : IsHom B C (eC.toLinearMap ∘ₗ S'.mkQ) := fun g x => hC g (S'.mkQ x)
  have hps : Function.Surjective (eC.toLinearMap ∘ₗ S'.mkQ) := eC.surjective.comp S'.mkQ_surjective
  refine ⟨A, C, S'.subtype ∘ₗ eA.symm.toLinearMap, eC.toLinearMap ∘ₗ S'.mkQ, ?_, hp,
    S'.subtype_injective.comp eA.symm.injective, hps, ?_, ?_, ?_⟩
  · intro g x
    obtain ⟨y, rfl⟩ := eA.surjective x
    rw [← hA]
    simp
  · intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Set.mem_range, Submodule.subtype_apply]
    exact ⟨fun h => ⟨eA ⟨x, h⟩, by simp⟩, fun ⟨y, hy⟩ => hy ▸ (eA.symm y).2⟩
  · let q := asModuleMap (π := B.ρ) (π' := C.ρ) _ hp
    have hq : Function.Surjective q := hps
    have hk : S = LinearMap.ker q := by
      ext x
      change _ ↔ eC (S'.mkQ (B.ρ.asModuleEquiv x)) = 0
      rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Iff.rfl
    haveI := isSimpleModule_iff_isCoatom.mpr hS
    exact IsSimpleModule.congr ((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq)).symm
  · have h1 : S' ≠ ⊤ := by
      intro h
      refine hS.1 (eq_top_iff.mpr fun x _ => ?_)
      have : B.ρ.asModuleEquiv x ∈ S' := h ▸ Submodule.mem_top
      exact this
    have h2 := Submodule.finrank_lt h1
    rw [eA.finrank_eq] at h2
    simpa using h2

theorem sameSS_piRep_succ {k G : Type} [Field k] [Group G] {s : ℕ} (C : Fin (s + 1) → Ob k G) (A B : Ob k G)
    (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin (C 0).m → k))
    (ef : IsHom A B f) (ep : IsHom B (C 0) p) (hf : Function.Injective f) (hp : Function.Surjective p)
    (H : Function.Exact f p) (h : SameSS A.ρ (piRep fun a : Fin s => (C a.succ).ρ)) :
    SameSS B.ρ (piRep fun a => (C a).ρ) := by
  have h1 : SameSS B.ρ ((C 0).ρ.prod (piRep fun a : Fin s => (C a.succ).ρ)) :=
    SameSS.of_exact_of_exact ef ep hf hp H (f' := LinearMap.inr k _ _) (p' := LinearMap.fst k _ _)
      (fun g x => by simp) (fun g x => by simp) LinearMap.inr_injective LinearMap.fst_surjective .inr_fst h
      (SameSS.refl _ (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩))
  refine h1.congr_right (Fin.consLinearEquiv k fun a => Fin (C a).m → k) fun g x => ?_
  funext a
  refine Fin.cases ?_ (fun j => ?_) a <;> rfl

theorem ModTh.exists_simple_pieces : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m), M.Model B N → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ ∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x := by
  intro k G _ _ l n _ _ _ R F r Dt M B
  induction B using (measure fun A : Ob k G => A.m).wf.induction with
  | _ B ih =>
  intro N hN
  by_cases hB : B.m = 0
  · haveI : IsEmpty (Fin B.m) := ⟨fun a => by have := a.2; omega⟩
    refine ⟨0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, ?_, fun i x => ?_⟩
    · exact SameSS.of_equiv (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
        (LinearEquiv.ofSubsingleton _ _) fun _ _ => Subsingleton.elim _ _
    · rw [Finset.univ_eq_empty, Finset.sum_empty]
      unfold sen qmult gmult
      exact Module.finrank_zero_of_subsingleton
  · obtain ⟨A, C₀, f, p, ef, ep, hf, hp, H, hs, hlt⟩ := exists_simple_quotient B hB
    obtain ⟨s, C, L, hL, hC, hss, hsen⟩ := ih A hlt _ (GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A B f N ef hf hN)
    obtain ⟨hobj, hlat, -, hc⟩ := GlobalTheory.T.obj_and_abc_of_model F M B N hN
    let C' : Fin (s + 1) → Ob k G := Fin.cons C₀ C
    refine ⟨s + 1, C', Fin.cons (α := fun a => Lats k n (C' a).m) (F.push B C₀ p N) L, fun a => ?_, fun a => ?_,
      sameSS_piRep_succ C' A B f p ef ep hf hp H hss, fun i x => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) a
      · exact ModTh.model_push_of_surjective F M B C₀ p N ep hp hN
      · exact hL j
    · refine Fin.cases ?_ (fun j => ?_) a
      · exact hs
      · exact hC j
    · rw [Fin.sum_univ_succ, GlobalTheory.T.senMultiplicity_additive_exact_sequence F A B C₀ f p N hobj ef ep hf hp H i (hlat i) (hc i) x, hsen, add_comm]
      rfl

end GlobalTheory.Models
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.splitsInCMField_placeBelow_of_completelySplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → (∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) → ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Splits (below P) := by
  first | exact @GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm | exact GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm | (intros; apply GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm <;> assumption)
end

section

noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Polynomial
open Formalism.MainNotions.N (GRep)

namespace GlobalTheory.FullCharpoly

section Lat
variable {G LL O V W : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
  {ρ : Representation LL G V} {σ : Representation LL G W}

def mapLat (e : V ≃ₗ[LL] W) (he : ∀ g x, e (ρ g x) = σ g (e x)) (L : Lattice (O := O) ρ) :
    Lattice (O := O) σ where
  T := L.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W)
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, L.stable g x hx, he g x⟩
  fg := L.fg.map _
  free := by
    have := L.free
    exact Module.Free.of_equiv ((e.restrictScalars O).submoduleMap L.T)
  span := by
    have h : ((L.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W) : Submodule O W) : Set W) =
        (e : V →ₗ[LL] W) '' (L.T : Set V) := rfl
    rw [h, Submodule.span_image, L.span, Submodule.map_top, LinearEquiv.range]

variable {E M : Type} [AddCommGroup E] [Module O E] [AddCommGroup M] [Module O M]

theorem quot_equiv_iff (L₁ L₂ : Lattice (O := O) ρ) (act : G → E → E) (π : Representation O G M)
    (p : E →ₗ[O] M) (hp : Function.Surjective p) (hact : ∀ g x, p (act g x) = π g (p x)) :
    (∃ e : (E ⧸ LinearMap.ker p) ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype),
      ∀ (g : G) (x : E) (y : ↥L₁.T), e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
        e (Submodule.Quotient.mk (act g x)) = Submodule.Quotient.mk ⟨ρ g y, L₁.stable g y y.2⟩) ↔
    ∃ q : ↥L₁.T →ₗ[O] M, Function.Surjective q ∧ (∀ g x, q (latRep L₁ g x) = π g (q x)) ∧
      ∀ x, q x = 0 ↔ (x : V) ∈ L₂.T := by
  constructor
  · rintro ⟨e, he⟩
    let Φ := p.quotKerEquivOfSurjective hp
    refine ⟨(Φ.toLinearMap.comp e.symm.toLinearMap).comp (L₂.T.comap L₁.T.subtype).mkQ, ?_, ?_, ?_⟩
    · exact Φ.surjective.comp (e.symm.surjective.comp (Submodule.mkQ_surjective _))
    · intro g y
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk y))
      have h1 : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
        rw [hx, LinearEquiv.apply_symm_apply]
      have h3 : latRep L₁ g y = ⟨ρ g y, L₁.stable g y y.2⟩ := Subtype.ext (latRep_apply L₁ g y)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply]
      rw [h3, ← he g x y h1, LinearEquiv.symm_apply_apply, ← hx]
      simp only [Φ, LinearMap.quotKerEquivOfSurjective_apply_mk]
      exact hact g x
    · intro y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
        LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.coe_subtype]
  · rintro ⟨q, hq, hqe, hqk⟩
    have hker : LinearMap.ker q = L₂.T.comap L₁.T.subtype := by
      ext y
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype, hqk]
    let ψ : M ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype) :=
      (q.quotKerEquivOfSurjective hq).symm.trans (Submodule.quotEquivOfEq _ _ hker)
    have hψ : ∀ y, ψ (q y) = Submodule.Quotient.mk y := by
      intro y
      simp only [ψ, LinearEquiv.trans_apply]
      rw [(LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk q hq y).symm]
      rfl
    have hΦ : ∀ x, p.quotKerEquivOfSurjective hp (Submodule.Quotient.mk x) = p x :=
      LinearMap.quotKerEquivOfSurjective_apply_mk p hp
    refine ⟨(p.quotKerEquivOfSurjective hp).trans ψ, fun g x y h => ?_⟩
    simp only [LinearEquiv.trans_apply, hΦ] at h ⊢
    have hxy : p x = q y := ψ.injective (h.trans (hψ y).symm)
    have h3 : latRep L₁ g y = ⟨ρ g y, L₁.stable g y y.2⟩ := Subtype.ext (latRep_apply L₁ g y)
    rw [hact, hxy, ← hqe, h3, hψ]

end Lat

section Sum
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] {n : ℕ}
    {emb : ZMod n → (K₀ →ₐ[Qp] LL)} {lam : O} {jT : ZMod n → ℤ → ℤ} {cT : G → Polynomial LL}

def ofFull (F : tableLineDegreeTwo.FullRep PD emb lam jT cT) : GRep G Qp LL O where
  V := F.V
  cadd := IsModuleTopology.toContinuousAdd LL F.V
  csmul := by have := IsModuleTopology.toContinuousSMul LL F.V; infer_instance
  ρ := F.ρ
  cont := F.full.1

def sumFull {m : ℕ} (F : Fin m → tableLineDegreeTwo.FullRep PD emb lam jT cT) : GRep G Qp LL O where
  V := ∀ j, (F j).V
  cadd := IsModuleTopology.toContinuousAdd LL _
  csmul := by have := IsModuleTopology.toContinuousSMul LL (∀ j, (F j).V); infer_instance
  ρ := tableLineDegreeTwo.piRep F
  cont := fun x => continuous_pi fun j => (F j).full.1 (x j)

def toFull (A : GRep G Qp LL O) (h : tableLineDegreeTwo.IsFull PD emb lam jT cT A.ρ) : tableLineDegreeTwo.FullRep PD emb lam jT cT where
  V := A.V
  ρ := A.ρ
  full := h

private theorem mapLattice_quotient_of_equivariant_equiv {G LL O V W M : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
    {ρ : Representation LL G V} {σ : Representation LL G W} [AddCommGroup M] [Module O M]
    (π : Representation O G M) (e : V ≃ₗ[LL] W) (he : ∀ g x, e (ρ g x) = σ g (e x))
    (L₁ L₂ : Lattice (O := O) ρ) (q : ↥L₁.T →ₗ[O] M) (hq : Function.Surjective q)
    (hqe : ∀ g x, q (latRep L₁ g x) = π g (q x)) (hqk : ∀ x, q x = 0 ↔ (x : V) ∈ L₂.T) :
    ∃ q' : ↥(mapLat e he L₁).T →ₗ[O] M, Function.Surjective q' ∧
      (∀ g x, q' (latRep (mapLat e he L₁) g x) = π g (q' x)) ∧
      ∀ x, q' x = 0 ↔ (x : W) ∈ (mapLat e he L₂).T := by
  let s : ↥L₁.T ≃ₗ[O] ↥(mapLat e he L₁).T := (e.restrictScalars O).submoduleMap L₁.T
  have hsx : ∀ x, (s x : W) = e x := fun x => rfl
  refine ⟨q.comp s.symm.toLinearMap, hq.comp s.symm.surjective, ?_, ?_⟩
  · intro g y
    obtain ⟨x, rfl⟩ := s.surjective y
    have hs : latRep (mapLat e he L₁) g (s x) = s (latRep L₁ g x) := by
      apply Subtype.ext
      rw [latRep_apply, hsx, hsx, latRep_apply, he]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact hqe g x
  · intro y
    obtain ⟨x, rfl⟩ := s.surjective y
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hqk, hsx]
    change (x : V) ∈ L₂.T ↔ e x ∈ L₂.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W)
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨z, hz, hze⟩
      have hzx : z = (x : V) := e.injective hze
      rwa [← hzx]


omit [IsTopologicalRing LL] in
theorem admissible_quotient_ker_iff_full_lattices {E M : Type} [AddCommGroup E] [Module O E] [AddCommGroup M] [Module O M]
    (act : G → E → E) (π : Representation O G M)
    (p : E →ₗ[O] M) (hp : Function.Surjective p) (hact : ∀ g x, p (act g x) = π g (p x)) :
    tableLineDegreeTwo.AdmQ PD emb lam jT cT act (LinearMap.ker p) ↔
      ∃ (μ : ℕ) (F : Fin μ → GRep G Qp LL O) (A : GRep G Qp LL O)
      (e : A.V ≃ₗ[LL] (∀ j, (F j).V)) (L₁ L₂ : Lattice (O := O) A.ρ) (q : ↥L₁.T →ₗ[O] M),
      (∀ j, tableLineDegreeTwo.IsFull PD emb lam jT cT (F j).ρ) ∧ (∀ g x j, e (A.ρ g x) j = (F j).ρ g (e x j)) ∧ L₂.T ≤ L₁.T ∧
      Function.Surjective q ∧ (∀ g x, q (latRep L₁ g x) = π g (q x)) ∧ ∀ x, q x = 0 ↔ (x : A.V) ∈ L₂.T := by
  constructor
  · rintro ⟨m, F, L₁, L₂, hle, e, he⟩
    obtain ⟨q, hq, hqe, hqk⟩ := (quot_equiv_iff L₁ L₂ act π p hp hact).1 ⟨e, he⟩
    exact ⟨m, fun j => ofFull (F j), sumFull F, LinearEquiv.refl LL _, L₁, L₂, q,
      fun j => (F j).full, fun g x j => rfl, hle, hq, hqe, hqk⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, he, hle, hq, hqe, hqk⟩
    let F' : Fin μ → tableLineDegreeTwo.FullRep PD emb lam jT cT := fun j => toFull (F j) (hF j)
    let e' : A.V ≃ₗ[LL] (∀ j, (F' j).V) := e
    have he' : ∀ g x, e' (A.ρ g x) = tableLineDegreeTwo.piRep F' g (e' x) := fun g x => funext fun j => he g x j
    obtain ⟨q', hq', hqe', hqk'⟩ := mapLattice_quotient_of_equivariant_equiv π e' he' L₁ L₂ q hq hqe hqk
    exact ⟨μ, F', mapLat e' he' L₁, mapLat e' he' L₂, Submodule.map_mono hle,
      (quot_equiv_iff _ _ act π p hp hact).2 ⟨q', hq', hqe', hqk'⟩⟩


omit [TopologicalSpace G] [TopologicalSpace LL] [IsTopologicalRing LL] in
theorem resPoly_eq {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (χ : ℕ → G →* Oˣ) (t : ℕ) :
    tableLineDegreeTwo.resPoly ρ χ t = fun g => LinearMap.charpoly (ρ g) *
      ∏ c : Fin t, (X - C (algebraMap O LL (χ (c.val + 1) g))) := by
  funext g
  simp only [tableLineDegreeTwo.resPoly]
  congr 1
  symm
  refine Finset.prod_bij (fun (c : Fin t) _ => c.val + 1) ?_ ?_ ?_ ?_
  · intro c _
    simp only [Finset.mem_Icc]
    omega
  · intro a _ b _ hab
    exact Fin.ext (by simpa using hab)
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    exact ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, by simp only; omega⟩
  · intro c _
    simp [tableLineDegreeTwo.charL]

end Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem isFull_iff_polyFull (jT : ZMod S.n → ℤ → ℤ) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) :
    tableLineDegreeTwo.IsFull (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) A.ρ ↔ PolyFull S jT A := by
  unfold tableLineDegreeTwo.IsFull PolyFull
  rw [resPoly_eq]
  simp only [tableLineDegreeTwo.Over, AlgHom.ext_iff, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  exact ⟨fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨A.cont, h.1, h.2.1, h.2.2⟩⟩

theorem admissibleQuotient_iff_admissible_module : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ), (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) → ∀ (E M : Type) [AddCommGroup E] [Module S.O E] [AddCommGroup M] [Module S.O M] (act : S.G → E → E) (π : Representation S.O S.G M) (p : E →ₗ[S.O] M), Function.Surjective p → (∀ g x, p (act g x) = π g (p x)) → (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) act (LinearMap.ker p) ↔ S.admitted π) := by
  intro l _ P S jT hj E M _ _ _ _ act π p hp hact
  refine (admissible_quotient_ker_iff_full_lattices act π p hp hact).trans (Iff.trans ?_ (admissibleModule_iff_lattice_quotients S hj π).symm)
  constructor
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, h⟩
    exact ⟨μ, F, A, e, L₁, L₂, q, fun j => (isFull_iff_polyFull S jT (F j)).1 (hF j), h⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, h⟩
    exact ⟨μ, F, A, e, L₁, L₂, q, fun j => (isFull_iff_polyFull S jT (F j)).2 (hF j), h⟩

end GlobalTheory.FullCharpoly
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tilt_unit_teichmuller_principal_unit_split : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Fl l), IsUnit x → ∃ (ω x₁ : Per.Fl l) (N : ℕ), x = ω * x₁ ∧ GlobalTheory.LogU.InJ (Per.tm (x₁ ^ (l ^ N)) - 1) ∧ ∀ (g : Per.Gq l) (e : Per.Fl l), e.untilt = 1 → Per.σF g x = x * e → Per.σF g ω = ω := by
  first | (exact @GlobalTheory.LogU.teich_split) | (exact GlobalTheory.LogU.teich_split) | (intros; apply GlobalTheory.LogU.teich_split  <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_tensor_lattice_specialisation : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f n : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (θ : Ainf l →ₐ[ℤ_[l]] OC l), IsMat K LL T M A → IsThetaShift AI n θ → ∃ Φ : TW (RA LL) T →+ (Fin d → PadicComplex l), (∀ (r : RA LL) (z : TW (RA LL) T), Φ (r • z) = (lam o A (thR LL θ r)).mulVec (Φ z)) ∧ (∀ z i, ‖Φ z i‖ ≤ 1) ∧ (∀ (g : ↥(GK K)) (z : TW (RA LL) T), Φ (TWact (gRA AI LL (g : GQ l)) T g z) = (M (g : GQ l)).mulVec (fun i => AI.actC (g : GQ l) (Φ z i))) ∧ ∀ j, ∃ t : ↥T.L.T, Φ ((1 : RA LL) ⊗ₜ[↥(OL LL)] t) = Pi.single j 1 := by
  exact @GlobalTheory.Cyc.Decomp.exists_specPhi
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

noncomputable section

namespace GlobalTheory.Pass.LocDual

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def locU {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  GlobalTheory.JumpDual.matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw M)
    (GlobalTheory.JumpDual.loc_cont D i w hw M hM)

def IsSummandTw (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)) : Prop :=
  ∃ (a : ℕ) (x : Fin a → ↥Xs) (j : X.V →ₗ[Br.LL D.nbr i w hw] (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)),
    Function.Injective j ∧
    (∀ g v, j (X.ρ g v) = fun b => (Br.loc D.nbr i w hw (rTwO D.nd i r (x b)) g).mulVec (j v b)) ∧
    ∃ C : Submodule (Br.LL D.nbr i w hw) (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw),
      (∀ g, ∀ u ∈ C, (fun b => (Br.loc D.nbr i w hw (rTwO D.nd i r (x b)) g).mulVec (u b)) ∈ C) ∧
      IsCompl (LinearMap.range j) C

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]

def DualLatLe (U U' : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (b : ℕ) : Prop :=
  ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ finrank O ↥(latticeFiniteCohomology PD LT') + finrank O ↥LT.T ≤ b

end Gen

end GlobalTheory.Pass.LocDual

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobFixedLatticeCondition_smul_of_frobenius_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) (e : ↥(MaximalUnramifiedExtension l)), fr l r e = e → LatC P U x y a → LatC P U x y (e • a) := by
  first | exact @GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed | exact GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed | (intros; apply GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isBdRPlusUnitMatrix_restrictionLatticeMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR), (∀ m, UnitM P (U m)) → UnitM P (U0 P ω hdet U) := by
  first | exact @GlobalTheory.PMon.ResR.unitM_U0_of_unitM | exact GlobalTheory.PMon.ResR.unitM_U0_of_unitM | (intros; apply GlobalTheory.PMon.ResR.unitM_U0_of_unitM <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.linearIndependent_restrictionLattice_column : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x : Fin r × n), (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) → ∀ c : n × Fin r → ↥(MaximalUnramifiedExtension l), (∀ i, fr l 1 (c i) = c i) → ∑ i, kd P (c i) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i (x.2, x.1) ∈ Fil P 1 → c = 0 := by
  first | exact @GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil | exact GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil | (intros; apply GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.restrictionLattice_columns_condition_linearIndependent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → (∀ c, LatC P U x y (colv P ω A₀ c)) ∧ LinearIndependent ℚ_[l] (colv P ω A₀) := by
  first | exact @GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent | exact GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent | (intros; apply GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent <;> assumption)
end
