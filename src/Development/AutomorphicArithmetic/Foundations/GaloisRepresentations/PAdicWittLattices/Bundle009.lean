module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle144
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem affine_point_comp {X Y : Scheme.{0}} (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (i : V ≤ f ⁻¹ᵁ U) {Ω : Type} [Field Ω] (x : Γ(X, V) →+* Ω) :
    (Spec.map (CommRingCat.ofHom x) ≫ hV.fromSpec) ≫ f =
      Spec.map (CommRingCat.ofHom (x.comp (f.appLE U V i).hom)) ≫ hU.fromSpec := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV i, ← Category.assoc, ← Spec.map_comp]
  rfl

private theorem affine_point_injective {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Ω : Type} [Field Ω]
    {a b : Γ(X, V) →+* Ω}
    (h : Spec.map (CommRingCat.ofHom a) ≫ hV.fromSpec = Spec.map (CommRingCat.ofHom b) ≫ hV.fromSpec) : a = b := by
  have h' := Spec.map_injective ((cancel_mono _).1 h)
  exact congrArg CommRingCat.Hom.hom h'

private theorem cech_section_local_split (hP : PtsOfSplits) (hS : AlgSplit) (hT : AlgTr) {k : Type} [Field k] {Z Y W : Scheme.{0}}
    (p : Z ⟶ sp k) (q : Y ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J]
    (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c) (hsp : Splits s c σ) (U : Z.Opens) (hU : IsAffineOpen U)
    (V : W.Opens) (hV : IsAffineOpen V) (hVU : V ≤ c ⁻¹ᵁ U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) :
    (c.appLE U V hVU).hom (secTrace p q hU b) =
      ∑ j, ((σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U))).hom b := by
  letI : Algebra (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := secAlg p q s U
  haveI : Module.Finite (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := sec_finite hU
  haveI : Algebra.Etale (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := sec_etale hU
  letI : Algebra (GlobalTheory.CechDR.Sec p U) Γ(W, V) := (c.appLE U V hVU).hom.toAlgebra
  have hcomp : ∀ j, s.app U ≫ (σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U)) =
      c.appLE U V hVU := by
    intro j
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [hσ j]
  let τ : J → GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U) →ₐ[GlobalTheory.CechDR.Sec p U] Γ(W, V) := fun j =>
    { toRingHom := ((σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U))).hom
      commutes' := fun a => congrArg (fun f => CommRingCat.Hom.hom f a) (hcomp j) }
  have hA' : IsAffineOpen (s ⁻¹ᵁ U) := hU.preimage s
  obtain ⟨e, he⟩ := hS _ _ _ J τ (by
    intro Ω _ _ x y hxy
    have hring : y.comp (s.appLE U (s ⁻¹ᵁ U) le_rfl).hom = x.comp (c.appLE U V hVU).hom := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact hxy
    have hpt : (Spec.map (CommRingCat.ofHom y) ≫ hA'.fromSpec) ≫ s =
        (Spec.map (CommRingCat.ofHom x) ≫ hV.fromSpec) ≫ c :=
      (affine_point_comp s hU hA' le_rfl y).trans
        ((congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ hU.fromSpec) hring).trans
          (affine_point_comp c hU hV hVU x).symm)
    obtain ⟨j, hj, huniq⟩ := hP s c J σ hsp Ω _ _ hpt
    refine ⟨j, ?_, fun j' hj' => huniq j' ?_⟩
    · exact affine_point_injective hA'
        ((affine_point_comp (σ j) hA' hV (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U)) x).symm.trans hj)
    · exact (affine_point_comp (σ j') hA' hV (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j') U)) x).trans
        (congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ hA'.fromSpec) hj'))
  exact hT _ _ _ J τ e he b

theorem UpperTheory.Gal.G3.pHodgeFun :
    PtsOfSplits → AlgSplit → AlgTr → ∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b) := by
  intro hP hS hT k _ Z Y W p q r s _ _ c J _ σ hσ hsp U hU b
  refine TopCat.Sheaf.eq_of_locally_eq' W.sheaf (fun i : {V : W.Opens // IsAffineOpen V ∧ V ≤ c ⁻¹ᵁ U} => i.1) (c ⁻¹ᵁ U) (fun i => homOfLE i.2.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hxV⟩
  · rintro ⟨V, hV, hVU⟩
    have key := cech_section_local_split hP hS hT p q s c J σ hσ hsp U hU V hV hVU b
    refine key.trans ((Finset.sum_congr rfl fun j _ => ?_).trans (map_sum (W.presheaf.map (homOfLE hVU).op).hom _ _).symm)
    change _ = ((σ j).app (s ⁻¹ᵁ U) ≫ W.presheaf.map (homOfLE (GlobalTheory.GalTrace.preimage_le (hσ j) U)).op ≫ W.presheaf.map (homOfLE hVU).op).hom b
    rw [← Functor.map_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pHodgeTr :
    (∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b)) → HodgeTr := by
  intro h k _ a b Z Y p q s _ _ hs W r c hc J _ σ hσq hsp x
  obtain ⟨hσ, _⟩ := hsp
  have hom := GlobalTheory.GalTrace.omegaTrace_omegaPull (k := k) hs hc Finset.univ hσ hσq
    (fun U hU b => by simpa using h k p q r s c J σ hσ ⟨hσ, ‹_›⟩ U hU b) a
  exact GlobalTheory.GalTrace.hodgePull_hodgeTrace hs hc Finset.univ hσ hσq a hom b x
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem trace_pi_eq_sum {C J : Type} [CommRing C] [Fintype J] (a : J → C) :
    Algebra.trace C (J → C) a = ∑ j, a j := by
  classical
  rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace C (Pi.basisFun C J), Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  simp [LinearMap.toMatrix_apply, Pi.single_apply]

theorem UpperTheory.Gal.G3.pAlgTr :
    AlgTr := by
  intro A A' C _ _ _ _ _ _ _ J _ τ e he b
  letI : Algebra A' (C ⊗[A] A') := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Projective A A' := projective_of_etale A A'
  haveI : Module.Free C (C ⊗[A] A') := Module.Free.of_equiv e.symm.toLinearEquiv
  haveI : Module.Finite C (C ⊗[A] A') := Module.Finite.equiv e.symm.toLinearEquiv
  have h1 := algTrace_of_isPushout (B := A) (B' := A') (C := C) (C' := C ⊗[A] A') b
  have h2 : (etTrace A A') b = (algTrace A A') b := rfl
  rw [h2, ← h1, algTrace_eq_trace]
  have h3 : algebraMap A' (C ⊗[A] A') b = e.symm (e (1 ⊗ₜ[A] b)) := by
    rw [AlgEquiv.symm_apply_apply]
    rfl
  rw [h3, Algebra.trace_eq_of_algEquiv e.symm, trace_pi_eq_sum]
  exact Finset.sum_congr rfl fun j _ => he b j
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.G3

private theorem ordExStep (hS : OrdStep) {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (d : ℕ)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hcf : IsFinite c) (hce : Etale c) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (huniv : ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin d → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
      ∃! w : U ⟶ W, w ≫ c = z ∧ ∀ j, w ≫ σ j = y j) :
    ∃ (W' : Scheme.{0}) (c' : W' ⟶ Z) (σ' : Fin (d + 1) → (W' ⟶ Y)), IsFinite c' ∧ Etale c' ∧
      (∀ j, σ' j ≫ s = c') ∧
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W'), Function.Injective fun j => x ≫ σ' j) ∧
      ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin (d + 1) → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
        (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
        ∃! w : U ⟶ W', w ≫ c' = z ∧ ∀ j, w ≫ σ' j = y j := by
  haveI := hcf
  haveI := hce
  let P := pullback s c
  have hsq : ∀ j, σ j ≫ s = 𝟙 W ≫ c := fun j => by rw [hσ j, Category.id_comp]
  let sec : Fin d → (W ⟶ P) := fun j => pullback.lift (σ j) (𝟙 W) (hsq j)
  have hsec1 : ∀ j, sec j ≫ pullback.fst s c = σ j := fun j => pullback.lift_fst _ _ _
  have hsec2 : ∀ j, sec j ≫ pullback.snd s c = 𝟙 W := fun j => pullback.lift_snd _ _ _
  haveI hOP : MorphismProperty.HasOfPostcompProperty (@IsOpenImmersion : MorphismProperty Scheme)
      (@Etale : MorphismProperty Scheme) := by
    apply MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2
    intro X Y f hf
    haveI : Etale f := hf
    exact inferInstanceAs <| IsOpenImmersion (pullback.diagonal f)
  have hopen : ∀ j, IsOpenImmersion (sec j) := fun j =>
    MorphismProperty.of_postcomp (W := (@IsOpenImmersion : MorphismProperty Scheme))
      (W' := (@Etale : MorphismProperty Scheme)) (sec j) (pullback.snd s c)
      (inferInstanceAs (Etale (pullback.snd s c)))
      (by rw [hsec2]; exact inferInstanceAs (IsOpenImmersion (𝟙 W)))
  have hclosed : ∀ j, IsClosedImmersion (sec j) := fun j => by
    haveI : IsClosedImmersion (sec j ≫ pullback.snd s c) := by
      rw [hsec2]; infer_instance
    exact IsClosedImmersion.of_comp (sec j) (pullback.snd s c)
  let S : Set P := ⋃ j, Set.range (sec j).base
  have hSc : IsClosed S := isClosed_iUnion_of_finite fun j => (hclosed j).isClosedEmbedding.isClosed_range
  have hSo : IsOpen S := isOpen_iUnion fun j => (hopen j).base_open.isOpen_range
  let O : P.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hOr : Set.range O.ι.base = Sᶜ := O.range_ι
  haveI : IsClosedImmersion O.ι := .of_isPreimmersion _ (by rw [hOr]; exact hSo.isClosed_compl)
  have hpt : ∀ (j : Fin d) (Ω : Type) [Field Ω] (x : sp Ω ⟶ P),
      x.base (IsLocalRing.closedPoint Ω) ∈ Set.range (sec j).base →
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j := by
    intro j Ω _ x hx
    have hr : Set.range x.base ⊆ Set.range (sec j).base := by
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint Ω)]
    haveI := hopen j
    have hf := IsOpenImmersion.lift_fac (sec j) x hr
    rw [← hf, Category.assoc, Category.assoc, hsec1, reassoc_of% hsec2]
  have hback : ∀ (j : Fin d) {T : Scheme.{0}} (x : T ⟶ P),
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j → x = (x ≫ pullback.snd s c) ≫ sec j := by
    intro j T x hx
    apply pullback.hom_ext
    · rw [Category.assoc, hsec1, hx, Category.assoc]
    · rw [Category.assoc, hsec2, Category.comp_id]
  refine ⟨O, O.ι ≫ pullback.snd s c ≫ c,
    Fin.snoc (α := fun _ => ((O : Scheme) ⟶ Y)) (fun j => O.ι ≫ pullback.snd s c ≫ σ j)
      (O.ι ≫ pullback.fst s c), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.snoc_last, Category.assoc, pullback.condition]
    · simp only [Fin.snoc_castSucc, Category.assoc, hσ j]
  · intro Ω _ x
    have key : ∀ j : Fin d, x ≫ O.ι ≫ pullback.fst s c ≠ x ≫ O.ι ≫ pullback.snd s c ≫ σ j := by
      intro j h
      have h2 := hback j (x ≫ O.ι) (by simpa only [Category.assoc] using h)
      have hin : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ S := by
        rw [h2]
        exact Set.mem_iUnion.2 ⟨j, _, rfl⟩
      have hO : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ Set.range O.ι.base :=
        ⟨x.base (IsLocalRing.closedPoint Ω), rfl⟩
      rw [hOr] at hO
      exact hO hin
    intro a b hab
    simp only at hab
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab (key j)
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab.symm (key i)
      | cast j =>
        simp only [Fin.snoc_castSucc] at hab
        exact congrArg Fin.castSucc (hinj Ω (x ≫ O.ι ≫ pullback.snd s c) (by simpa only [Category.assoc] using hab))
  · intro U z y hy hinjU
    obtain ⟨w0, ⟨hw0c, hw0σ⟩, hw0u⟩ := huniv U z (fun j => y j.castSucc) (fun j => hy _)
      (fun Ω _ x a b h => Fin.castSucc_injective _ (hinjU Ω x h))
    let φ : U ⟶ P := pullback.lift (y (Fin.last d)) w0 (by rw [hy, hw0c])
    have hφ1 : φ ≫ pullback.fst s c = y (Fin.last d) := pullback.lift_fst _ _ _
    have hφ2 : φ ≫ pullback.snd s c = w0 := pullback.lift_snd _ _ _
    have hrange : Set.range φ.base ⊆ Set.range O.ι.base := by
      rintro _ ⟨u, rfl⟩
      rw [hOr]
      intro hu
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hu
      let x := U.fromSpecResidueField u
      have hxu : x.base (IsLocalRing.closedPoint (U.residueField u)) = u :=
        U.fromSpecResidueField_apply u _
      have := hpt j (U.residueField u) (x ≫ φ) (by
        show φ.base (x.base _) ∈ _
        rw [hxu]
        exact hj)
      rw [Category.assoc, Category.assoc, hφ1, reassoc_of% hφ2, hw0σ] at this
      exact (Fin.castSucc_lt_last j).ne (hinjU _ x this).symm
    refine ⟨IsOpenImmersion.lift O.ι φ hrange, ⟨?_, fun k => ?_⟩, ?_⟩
    · rw [IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0c]
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [Fin.snoc_last, IsOpenImmersion.lift_fac_assoc, hφ1]
      · rw [Fin.snoc_castSucc, IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0σ]
    · rintro w' ⟨hw'c, hw'σ⟩
      rw [← cancel_mono O.ι, IsOpenImmersion.lift_fac]
      have e2 : w' ≫ O.ι ≫ pullback.snd s c = w0 := by
        refine hw0u _ ⟨by simpa only [Category.assoc] using hw'c, fun j => ?_⟩
        have := hw'σ j.castSucc
        rw [Fin.snoc_castSucc] at this
        simpa only [Category.assoc] using this
      apply pullback.hom_ext
      · have := hw'σ (Fin.last d)
        rw [Fin.snoc_last] at this
        rw [Category.assoc, this, hφ1]
      · rw [Category.assoc, e2, hφ2]

theorem pOrdEx : OrdStep → OrdEx := by
  intro hS Z Y s _ _ d
  induction d with
  | zero =>
    refine ⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0, ?_, ?_⟩
    · intro Ω _ x a
      exact a.elim0
    · intro U z y _ _
      exact ⟨z, ⟨Category.comp_id _, fun j => j.elim0⟩, fun w hw => by simpa using hw.1⟩
  | succ d ih =>
    obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := ih
    exact ordExStep hS s d c σ hcf hce hσ hinj huniv

end UpperTheory.Gal.G3

end
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem mem_range_diagonal_iff {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsOpenImmersion (pullback.diagonal s)]
    (Ω : Type) [Field Ω] (y : UpperTheory.Gal.G3.sp Ω ⟶ pullback s s) :
    y (IsLocalRing.closedPoint Ω) ∈ Set.range (pullback.diagonal s) ↔
      y ≫ pullback.fst s s = y ≫ pullback.snd s s := by
  constructor
  · rintro ⟨z, hz⟩
    have hsub : Set.range y ⊆ Set.range (pullback.diagonal s) := by
      rintro _ ⟨q, rfl⟩
      have hq : q = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
      rw [hq]
      exact ⟨z, hz⟩
    have hfac := IsOpenImmersion.lift_fac (pullback.diagonal s) y hsub
    rw [← hfac, Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  · intro h
    refine ⟨(y ≫ pullback.fst s s) (IsLocalRing.closedPoint Ω), ?_⟩
    have hy : (y ≫ pullback.fst s s) ≫ pullback.diagonal s = y := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
    conv_rhs => rw [← hy]
    rfl

theorem UpperTheory.Gal.G3.pOrdStep :
    OrdStep := by
  intro Z Y W s _ _ c d σ hσ
  have hc : ∀ j, pullback.fst s c ≫ s = (pullback.snd s c ≫ σ j) ≫ s := fun j => by
    rw [Category.assoc, hσ j, pullback.condition]
  let φ : Fin d → (pullback s c ⟶ pullback s s) := fun j =>
    pullback.lift (pullback.fst s c) (pullback.snd s c ≫ σ j) (hc j)
  have hopen : ∀ j, IsOpen ((φ j) ⁻¹' Set.range (pullback.diagonal s)) := fun j =>
    (pullback.diagonal s).isOpenEmbedding.isOpen_range.preimage (φ j).continuous
  have hclosed : ∀ j, IsClosed ((φ j) ⁻¹' Set.range (pullback.diagonal s)) := fun j =>
    (pullback.diagonal s).isClosedEmbedding.isClosed_range.preimage (φ j).continuous
  refine ⟨⟨(⋃ j, (φ j) ⁻¹' Set.range (pullback.diagonal s))ᶜ,
    (isClosed_iUnion_of_finite hclosed).isOpen_compl⟩, (isOpen_iUnion hopen).isClosed_compl, ?_⟩
  intro Ω _ x
  have key : ∀ j, (x ≫ φ j) (IsLocalRing.closedPoint Ω) ∈ Set.range (pullback.diagonal s) ↔
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j := by
    intro j
    rw [mem_range_diagonal_iff s Ω (x ≫ φ j)]
    simp only [Category.assoc, φ, pullback.lift_fst, pullback.lift_snd]
  show x (IsLocalRing.closedPoint Ω) ∈ (⋃ j, (φ j) ⁻¹' Set.range (pullback.diagonal s))ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists]
  refine forall_congr' (fun j => ?_)
  exact (not_congr (key j)).trans ⟨fun h e => h e.symm, fun h e => h e.symm⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pLiesAbs :
    FEtBasic → TrBase.{u} → TrPushM.{u} → LiesAbs.{u} := by
  intro hF hB hP B R _ T hT Z Y C D pZ pY pC pD π hπ sg tg htg s t ht κ h d m hsg hs hκt hsd hℓ tr trg htr htrg x
  have hpb : IsPullback (pullback.snd π s) (pullback.fst π s) s π := (IsPullback.of_hasPullback π s).flip
  have hfst : FEt (pullback.fst π s) d := hF.1 _ _ s π d hpb hsd
  haveI : IsFinite (pullback.fst π s) := hfst.1
  haveI : Etale (pullback.fst π s) := hfst.2.1
  obtain ⟨tr1, htr1⟩ := hT.tr pZ (pullback.fst π s ≫ pZ) (pullback.fst π s) rfl
  have hsndp : pullback.snd π s ≫ pD = pullback.fst π s ≫ pZ := by
    rw [← hs, ← Category.assoc, ← pullback.condition, Category.assoc, hπ]
  have base := hB T hT pY pD pZ (pullback.fst π s ≫ pZ) (pullback.snd π s) (pullback.fst π s) s π d
    hsndp hπ rfl hpb hsd tr tr1 htr htr1 ((T.pull t ht) x)
  have htrg' : T.IsTr pZ pC (pullback.lift sg κ h ≫ pullback.fst π s) trg := by
    rw [pullback.lift_fst]; exact htrg
  have hℓq : pullback.lift sg κ h ≫ (pullback.fst π s ≫ pZ) = pC := by
    rw [← Category.assoc, pullback.lift_fst, hsg]
  have push := hP T hT pZ (pullback.fst π s ≫ pZ) pC (pullback.lift sg κ h) (pullback.fst π s) d m hℓq rfl
    hfst hℓ tr1 trg htr1 htrg' ((T.pull (pullback.snd π s) hsndp) ((T.pull t ht) x))
  have hcongr : ∀ {W : Scheme} {r : W ⟶ B} (f f' : W ⟶ Y) (e : f = f') (hf : f ≫ pY = r) (hf' : f' ≫ pY = r),
      T.pull f hf x = T.pull f' hf' x := by
    intro W r f f' e hf hf'
    subst e
    rfl
  have h1 : (tg ≫ π) ≫ pY = pC := by rw [Category.assoc, hπ, htg]
  have h2 : (pullback.snd π s ≫ t) ≫ pY = pullback.fst π s ≫ pZ := by rw [Category.assoc, ht, hsndp]
  have h3 : (pullback.lift sg κ h ≫ pullback.snd π s ≫ t) ≫ pY = pC := by
    rw [Category.assoc, h2, hℓq]
  have hmor : tg ≫ π = pullback.lift sg κ h ≫ pullback.snd π s ≫ t := by
    rw [← Category.assoc, pullback.lift_snd, hκt]
  rw [← T.pull_comp tg π htg hπ h1, hcongr _ _ hmor h1 h3,
    T.pull_comp (pullback.lift sg κ h) (pullback.snd π s ≫ t) hℓq h2 h3,
    T.pull_comp (pullback.snd π s) t hsndp ht h2, push, base]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pMultiSplit :
    FEtBasic → SplitsBasic → GalClosD → MultiSplit := by
  intro hF hS hG Z n
  induction n with
  | zero =>
    intro Y s d _
    exact ⟨Z, 𝟙 Z, 1, one_pos, UpperTheory.Gal.Int.Geo.fEt_id Z, fun i => i.elim0⟩
  | succ n ih =>
    intro Y s d hs
    obtain ⟨W, c, e, he, hc, hspl⟩ := ih (fun i => Y i.castSucc) (fun i => s i.castSucc)
      (fun i => d i.castSucc) (fun i => hs i.castSucc)
    have hP : FEt (pullback.snd (s (Fin.last n)) c) (d (Fin.last n)) :=
      hF.1 (pullback.fst _ _) (pullback.snd _ _) (s (Fin.last n)) c _
        (IsPullback.of_hasPullback _ _) (hs _)
    obtain ⟨W2, c2, G, _, _, a, σ, hgal, hσ⟩ := hG (pullback.snd (s (Fin.last n)) c) _ hP
    have hc2 : FEt c2 (Nat.card G) := hF.2.2 c2 G a hgal
    refine ⟨W2, c2 ≫ c, e * Nat.card G, Nat.mul_pos he Nat.card_pos,
      hF.2.1 c2 c e (Nat.card G) hc2 hc, ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_)
    · haveI := (hs (Fin.last n)).1
      haveI := (hs (Fin.last n)).2.1
      exact ⟨fun j => σ j ≫ pullback.fst _ _,
        (hS.2 (pullback.fst _ _) (pullback.snd _ _) (s (Fin.last n)) c
          (IsPullback.of_hasPullback _ _) c2 (Fin (d (Fin.last n))) σ hσ.1).mp hσ⟩
    · obtain ⟨τ, hτ⟩ := hspl i
      haveI := (hs i.castSucc).1
      haveI := (hs i.castSucc).2.1
      exact ⟨fun j => c2 ≫ τ j, hS.1 (s i.castSucc) c _ τ c2 hτ⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTrBase :
    FEtBasic → SplitsBasic → GalClosD → TrBase.{u} := by
  intro hF hS hC B R _ T hT P Y Z' Z p q p' q' v s' s g d hv hg hq' hpb hs tr tr' htr htr' x
  haveI : IsFinite s := hs.1
  haveI : Etale s := hs.2.1
  obtain ⟨W, c, G, _, _, a, σ, hgal, hspl⟩ := hC s' d (hF.1 v s' s g d hpb hs)
  have hσs : ∀ j, σ j ≫ s' = c := hspl.1
  have hσ' : ∀ j, σ j ≫ q' = c ≫ p' := fun j => by
    rw [← hq', ← Category.assoc, hσs j]
  have hσv : ∀ j, (σ j ≫ v) ≫ q = c ≫ p' := fun j => by
    rw [Category.assoc, hv, hσ' j]
  have hcg : (c ≫ g) ≫ p = c ≫ p' := by rw [Category.assoc, hg]
  have hspl2 : Splits s (c ≫ g) (fun j => σ j ≫ v) :=
    (hS.2 v s' s g hpb c (Fin d) σ hσs).1 hspl
  apply hT.inj p' (c ≫ p') c rfl G a hgal
  rw [← T.pull_comp c g rfl hg hcg, htr W (c ≫ p') (c ≫ g) hcg (Fin d) (fun j => σ j ≫ v) hσv hspl2 x,
    htr' W (c ≫ p') c rfl (Fin d) σ hσ' hspl]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact T.pull_comp (σ j) v (hσ' j) hv (hσv j) x
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pFEtInj :
    GalClosD → FEtInj.{u} := by
  intro hGC B R _ T hT Z W p r c hc d hd hfet
  obtain ⟨V, e, G, _, _, a, σ, hgal, hspl⟩ := hGC c d hfet
  have h0 : σ ⟨0, hd⟩ ≫ c = e := hspl.1 _
  subst h0
  have hinj := hT.inj p ((σ ⟨0, hd⟩ ≫ c) ≫ p) (σ ⟨0, hd⟩ ≫ c) rfl G a hgal
  have hσr : σ ⟨0, hd⟩ ≫ r = (σ ⟨0, hd⟩ ≫ c) ≫ p := by
    rw [← hc, Category.assoc]
  have hcomp := T.pull_comp (σ ⟨0, hd⟩) c hσr hc rfl
  intro x y hxy
  apply hinj
  rw [hcomp x, hcomp y, hxy]
end
