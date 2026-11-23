module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle185
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle468
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.FerrandPush

set_option backward.isDefEq.respectTransparency false in
theorem isClosedImmersion_toSpecΓ_comp {X : Scheme.{0}} (O : X.Opens) (hO : IsAffineOpen O)
    {A : CommRingCat.{0}} (q : A ⟶ Γ(X, O)) (h : Function.Surjective q.hom) :
    IsClosedImmersion (O.toSpecΓ ≫ Spec.map q) := by
  have := IsClosedImmersion.spec_of_surjective _ h
  rw [← hO.isoSpec_hom]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem surjective_toSpecΓ_comp {X : Scheme.{0}} (O : X.Opens) (hO : IsAffineOpen O)
    {A : CommRingCat.{0}} (q : A ⟶ Γ(X, O)) (h : Function.Surjective q.hom)
    (h' : IsNilpotent (RingHom.ker q.hom)) : Surjective (O.toSpecΓ ≫ Spec.map q) := by
  have : Surjective (Spec.map q) := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap q.hom)
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ h,
      PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    obtain ⟨n, hn⟩ := h'
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn] at this
  rw [← hO.isoSpec_hom]
  infer_instance

theorem mem_upOpen_iff {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (x : Y₀) : i x ∈ upOpen i U ↔ x ∈ U :=
  SetLike.ext_iff.mp (preimage_upOpen i U) x


set_option backward.isDefEq.respectTransparency false in
theorem exists_pushout_data : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₁.app U).hom)) → (∀ U : Y₂.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₂.app U).hom)) → ∃ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ ∧ IsClosedImmersion j₂ ∧ Surjective j₁ ∧ Surjective j₂ ∧ ∃ 𝒱 : Set Y.Opens, TopologicalSpace.Opens.IsBasis 𝒱 ∧ ∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  intro Y₀ Y₁ Y₂ i₁ i₂ hc₁ hc₂ hs₁ hs₂ hn₁ hn₂
  haveI := hc₁; haveI := hc₂; haveI := hs₁; haveI := hs₂
  have hR : ∀ U ∈ good i₁ i₂, _ := fun U (hU : U ∈ good i₁ i₂) ↦
    GlobalTheory.T.pullbackCone_surjective_nilpotent_ker (res i₁ U) (res i₂ U) (GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker i₁ hn₁ U hU.2.1).1 (GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker i₁ hn₁ U hU.2.1).2
      (GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker i₂ hn₂ U hU.2.2).1 (GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker i₂ hn₂ U hU.2.2).2
  have hπ : ∀ U ∈ good i₁ i₂, Function.Surjective ((fibπ i₁ i₂).app (op U)).hom ∧
      IsNilpotent (RingHom.ker ((fibπ i₁ i₂).app (op U)).hom) := fun U hU ↦ (hR U hU).2.2
  have hbas₀ : ∀ U ∈ good i₁ i₂, ∀ (W : Y₀.Opens) (x : Y₀), x ∈ U → x ∈ W →
      ∃ V ∈ good i₁ i₂, x ∈ V ∧ V ≤ U ∧ V ≤ W := by
    intro U hU W x hxU hxW
    obtain ⟨f, hf, hxf⟩ := hU.1.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
    obtain ⟨a, rfl⟩ := (hπ U hU).1 f
    exact ⟨_, GlobalTheory.T.ferrand_pushout_good_basic_open i₁ i₂ U hU a, hxf, Y₀.basicOpen_le _, hf⟩
  have hopen := GlobalTheory.T.isOpenImmersion_of_nilpotent_thickening_cover Y₀ (good i₁ i₂) (fun U hU ↦ hU.1) (fib i₁ i₂) (fibπ i₁ i₂) hπ (GlobalTheory.T.isLocalization_away_ferrandPush_fib i₁ i₂)
  let F := ThickGlue.specDiagram (good i₁ i₂) (fib i₁ i₂)
  haveI hF : ∀ {U V : good i₁ i₂} (f : U ⟶ V), IsOpenImmersion (F.map f) :=
    fun {U V} f ↦ hopen _ U.2 _ V.2 f.le
  haveI : (F ⋙ Scheme.forget).IsLocallyDirected :=
    GlobalTheory.T.isLocallyDirected_of_bijective_basis_compatible (good i₁ i₂) (fun U hU V _ x hx hy ↦ hbas₀ U hU V x hx hy) F hF
      (fun U ↦ ThickGlue.toSpec (fibπ i₁ i₂) U.1)
      (fun U ↦ by
        haveI := ThickGlue.isClosedImmersion_toSpec (fibπ i₁ i₂) U.2.1 (hπ U.1 U.2).1
        exact (ThickGlue.toSpec _ U.1).isClosedEmbedding.injective)
      (fun U ↦ by
        haveI := ThickGlue.surjective_toSpec (fibπ i₁ i₂) U.2.1 (hπ U.1 U.2).1 (hπ U.1 U.2).2
        exact (ThickGlue.toSpec _ U.1).surjective)
      (fun h ↦ ThickGlue.toSpec_naturality _ h)
  let e₁ : ∀ U : good i₁ i₂, (upOpen i₁ U.1).toScheme ⟶ F.obj U := fun U ↦
    (upOpen i₁ U.1).toSpecΓ ≫ Spec.map (cone i₁ i₂ U.1).fst
  let e₂ : ∀ U : good i₁ i₂, (upOpen i₂ U.1).toScheme ⟶ F.obj U := fun U ↦
    (upOpen i₂ U.1).toSpecΓ ≫ Spec.map (cone i₁ i₂ U.1).snd
  have hn1 : ∀ {U V : good i₁ i₂} (h : U.1 ≤ V.1), Y₁.homOfLE (upOpen_mono i₁ h) ≫ e₁ V =
      e₁ U ≫ F.map (homOfLE (show U ≤ V from h)) := by
    intro U V h
    change _ = _ ≫ Spec.map (fibMap i₁ i₂ h)
    simp only [e₁]
    rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, fibMap_fst]
  have hn2 : ∀ {U V : good i₁ i₂} (h : U.1 ≤ V.1), Y₂.homOfLE (upOpen_mono i₂ h) ≫ e₂ V =
      e₂ U ≫ F.map (homOfLE (show U ≤ V from h)) := by
    intro U V h
    change _ = _ ≫ Spec.map (fibMap i₁ i₂ h)
    simp only [e₂]
    rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, fibMap_snd]
  have hbasK : ∀ {Yk : Scheme.{0}} (ik : Y₀ ⟶ Yk) [IsClosedImmersion ik] [Surjective ik],
      ∀ U ∈ good i₁ i₂, ∀ V ∈ good i₁ i₂, ∀ y : Yk, y ∈ upOpen ik U → y ∈ upOpen ik V →
        ∃ W ∈ good i₁ i₂, y ∈ upOpen ik W ∧ W ≤ U ∧ W ≤ V := by
    intro Yk ik _ _ U hU V _ y hyU hyV
    obtain ⟨x, rfl⟩ := ik.surjective y
    rw [mem_upOpen_iff] at hyU hyV
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas₀ U hU V x hyU hyV
    exact ⟨W, hW, (mem_upOpen_iff ik W x).2 hxW, h1, h2⟩
  have hcovK : ∀ {Yk : Scheme.{0}} (ik : Y₀ ⟶ Yk) [IsClosedImmersion ik] [Surjective ik],
      ∀ y : Yk, ∃ U ∈ good i₁ i₂, y ∈ upOpen ik U := by
    intro Yk ik _ _ y
    obtain ⟨x, rfl⟩ := ik.surjective y
    obtain ⟨U, hU, hx⟩ := GlobalTheory.T.exists_mem_good_of_closedImmersions i₁ i₂ x
    exact ⟨U, hU, (mem_upOpen_iff ik U x).2 hx⟩
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_glue_to_locallyDirected_colimit_of_basis (good i₁ i₂) F Y₁ (upOpen i₁) (upOpen_mono i₁) (hbasK i₁)
    (hcovK i₁) e₁ hn1
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.exists_glue_to_locallyDirected_colimit_of_basis (good i₁ i₂) F Y₂ (upOpen i₂) (upOpen_mono i₂) (hbasK i₂)
    (hcovK i₂) e₂ hn2
  obtain ⟨ci₁, su₁, pre₁⟩ := GlobalTheory.T.isClosedImmersion_surjective_to_colimit (good i₁ i₂) F Y₁ (upOpen i₁) (upOpen_mono i₁) (hcovK i₁) e₁
    (fun U ↦ isClosedImmersion_toSpecΓ_comp _ U.2.2.1 _ (hR U.1 U.2).1.1)
    (fun U ↦ surjective_toSpecΓ_comp _ U.2.2.1 _ (hR U.1 U.2).1.1 (hR U.1 U.2).1.2) hn1 j₁ hj₁
  obtain ⟨ci₂, su₂, pre₂⟩ := GlobalTheory.T.isClosedImmersion_surjective_to_colimit (good i₁ i₂) F Y₂ (upOpen i₂) (upOpen_mono i₂) (hcovK i₂) e₂
    (fun U ↦ isClosedImmersion_toSpecΓ_comp _ U.2.2.2 _ (hR U.1 U.2).2.1.1)
    (fun U ↦ surjective_toSpecΓ_comp _ U.2.2.2 _ (hR U.1 U.2).2.1.1 (hR U.1 U.2).2.1.2) hn2 j₂ hj₂
  have key1 : ∀ U : good i₁ i₂, U.1.ι ≫ i₁ ≫ j₁ =
      U.1.toSpecΓ ≫ Spec.map ((cone i₁ i₂ U.1).fst ≫ res i₁ U.1) ≫ colimit.ι F U := by
    intro U
    rw [← Scheme.Hom.resLE_comp_ι_assoc i₁ (preimage_upOpen i₁ U.1).ge, hj₁ U]
    simp only [e₁, res, Spec.map_comp, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  have key2 : ∀ U : good i₁ i₂, U.1.ι ≫ i₂ ≫ j₂ =
      U.1.toSpecΓ ≫ Spec.map ((cone i₁ i₂ U.1).snd ≫ res i₂ U.1) ≫ colimit.ι F U := by
    intro U
    rw [← Scheme.Hom.resLE_comp_ι_assoc i₂ (preimage_upOpen i₂ U.1).ge, hj₂ U]
    simp only [e₂, res, Spec.map_comp, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  have hw : i₁ ≫ j₁ = i₂ ≫ j₂ := by
    refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
    obtain ⟨U, hU, hx⟩ := GlobalTheory.T.exists_mem_good_of_closedImmersions i₁ i₂ x
    refine ⟨U, hx, ?_⟩
    rw [key1 ⟨U, hU⟩, key2 ⟨U, hU⟩, (cone i₁ i₂ U).condition]
  have h0 : ∀ U : good i₁ i₂, (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    intro U
    change i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ (colimit.ι F U).opensRange) = U.1
    rw [pre₁ U, preimage_upOpen]
  refine ⟨colimit F, j₁, j₂, hw, ci₁, ci₂, su₁, su₂,
    Set.range (fun U : good i₁ i₂ ↦ (colimit.ι F U).opensRange), ?_, ?_⟩
  · rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro O y hy
    obtain ⟨x, rfl⟩ := (i₁ ≫ j₁).surjective y
    obtain ⟨U₀, hU₀, hx₀⟩ := GlobalTheory.T.exists_mem_good_of_closedImmersions i₁ i₂ x
    obtain ⟨U, hU, hxU, -, hUO⟩ := hbas₀ U₀ hU₀ ((i₁ ≫ j₁) ⁻¹ᵁ O) x hx₀ hy
    refine ⟨_, ⟨⟨U, hU⟩, rfl⟩, ?_, ?_⟩
    · show x ∈ (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F ⟨U, hU⟩).opensRange
      rw [h0 ⟨U, hU⟩]
      exact hxU
    · intro z hz
      obtain ⟨x', rfl⟩ := (i₁ ≫ j₁).surjective z
      have hx' : x' ∈ (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F ⟨U, hU⟩).opensRange := hz
      rw [h0 ⟨U, hU⟩] at hx'
      exact hUO hx'
  · rintro _ ⟨U, rfl⟩
    have hle : ⊤ ≤ (colimit.ι F U) ⁻¹ᵁ (colimit.ι F U).opensRange := fun x _ ↦ ⟨x, rfl⟩
    haveI hiso : IsIso ((colimit.ι F U).appLE (colimit.ι F U).opensRange ⊤ hle) := by
      have := (colimit.ι F U).isIso_app (colimit.ι F U).opensRange le_rfl
      have : IsIso (homOfLE hle) := homOfLE_isIso_of_eq _ (top_le_iff.mp hle).symm
      rw [Scheme.Hom.appLE]
      infer_instance
    let ψ : Γ(colimit F, (colimit.ι F U).opensRange) ≅ (fib i₁ i₂).obj (op U.1) :=
      asIso ((colimit.ι F U).appLE (colimit.ι F U).opensRange ⊤ hle) ≪≫ Scheme.ΓSpecIso _
    have a1 := GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor (A := (fib i₁ i₂).obj (op U.1)) (colimit.ι F U) j₁ (upOpen i₁ U.1)
      (cone i₁ i₂ U.1).fst (pre₁ U) (hj₁ U)
    have a2 := GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor (A := (fib i₁ i₂).obj (op U.1)) (colimit.ι F U) j₂ (upOpen i₂ U.1)
      (cone i₁ i₂ U.1).snd (pre₂ U) (hj₂ U)
    have P := IsPullback.of_isLimit (coneIsLimit i₁ i₂ U.1)
    refine P.of_iso ψ.symm (Y₁.presheaf.mapIso (eqToIso (pre₁ U)).op)
      (Y₂.presheaf.mapIso (eqToIso (pre₂ U)).op) (Y₀.presheaf.mapIso (eqToIso (h0 U)).op)
      ?_ ?_ ?_ ?_
    · rw [Iso.symm_hom, Iso.eq_inv_comp]
      simp only [ψ, Iso.trans_hom, asIso_hom, Category.assoc, Functor.mapIso_hom, Iso.op_hom,
        eqToIso.hom]
      rw [← reassoc_of% a1]
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map_assoc]
    · rw [Iso.symm_hom, Iso.eq_inv_comp]
      simp only [ψ, Iso.trans_hom, asIso_hom, Category.assoc, Functor.mapIso_hom, Iso.op_hom,
        eqToIso.hom]
      rw [← reassoc_of% a2]
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map_assoc]
    · simp only [res, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]
    · simp only [res, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]

end GlobalTheory.FerrandPush
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem ker_kappa_xI_comap :
    ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
      (J : Ideal (C ⊗[A] B)) (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C))
      (U : Z.affineOpens),
      (letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
       ∃ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = secAlg C h U ∧
         RingHom.ker (kappa A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))
           ((xI A B C J).comap (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) U) =
         J.map (Algebra.TensorProduct.map φ (AlgHom.id A B))) := by
  intro A B C _ _ _ _ _ J Z h U
  let f := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let g := h ≫ f
  let W := pullback.snd (str A B) g ⁻¹ᵁ (U : Z.Opens)
  let := (secAlg A g U).toAlgebra
  let φ : C →ₐ[A] Γ(Z, U) :=
    { toRingHom := secAlg C h U
      commutes' := fun a => by
        have hs : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appLE ⊤ U (by simp) =
            CommRingCat.ofHom (algebraMap A C) ≫
              (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) := by
          calc
            _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
                h.appLE ⊤ U (by simp) :=
              congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h f ⊤ U (by simp))
            _ = _ := (Scheme.ΓSpecIso_inv_naturality_assoc
              (CommRingCat.ofHom (algebraMap A C)) (h.appLE ⊤ U (by simp))).symm
        exact (congrArg (fun F => F.hom a) hs).symm }
  refine ⟨φ, rfl, ?_⟩
  have : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  have hW : IsAffineOpen W := U.2.preimage _
  have hTensor : ((bc A B f h).appLE ⊤ W (by simp)).hom.comp (psi A B C) =
      (theta A B g U).comp (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom := by
    have eL : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (pullback.fst (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := C)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_fst, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have eR : (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (pullback.snd (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have hpsi (c : C) (b : B) : psi A B C (c ⊗ₜ[A] b) =
        (pullback.fst (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
        (pullback.snd (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
      have h1 := congrArg (fun F => F.hom b) eL
      have h2 := congrArg (fun F => F.hom c) eR
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
      rw [h1, h2, ← map_mul, ← map_mul]
      simp [psi]
    have eF : (pullback.fst (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        (pullback.fst (str A B) g).appLE ⊤ W (by simp) := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      exact appLE_eq_of_eq ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) _ _ _ _
    have eS : (pullback.snd (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        h.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      refine (appLE_eq_of_eq (f₂ := pullback.snd (str A B) g ≫ h)
        (pullback.lift_snd _ _ _) _ _ _ (by simp)).trans ?_
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul c b =>
      have hF := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) eF
      have hS := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)) eS
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hF hS
      rw [RingHom.comp_apply, hpsi, map_mul, hF, hS, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, mul_comm]
      let : Algebra A Γ(pullback (str A B) g, W) :=
        (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
      symm
      change theta A B g U (secAlg C h U c ⊗ₜ[A] b) =
        ((pullback.snd (str A B) g).app U).hom (secAlg C h U c) *
          ((pullback.fst (str A B) g).appLE ⊤ W (by simp)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hk := Scheme.IdealSheafData.ker_subschemeι_app
    ((xI A B C J).comap (bc A B f h)) ⟨W, hW⟩
  rw [ker_kappa_eq]
  erw [hk]
  rw [GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine,
    GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top, Ideal.map_map, hTensor,
    ← Ideal.map_map, Ideal.comap_map_of_bijective _
      (GlobalTheory.T.sectionTensorPullbackRingHom_bijective A B _ U)]
  rfl

end GlobalTheory.HilbAff
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open GlobalTheory.HilbAff in

theorem _root_.GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map :
    ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
      (J : Ideal (C ⊗[A] B)) (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C))
      (U : Z.affineOpens),
      (letI := (GlobalTheory.HilbAff.secAlg A
        (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
       ∃ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = GlobalTheory.HilbAff.secAlg C h U ∧
         RingHom.ker (GlobalTheory.HilbAff.kappa A B
           (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))
           ((GlobalTheory.HilbAff.xI A B C J).comap
             (GlobalTheory.HilbAff.bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) U) =
         J.map (Algebra.TensorProduct.map φ (AlgHom.id A B))) := by
  intro A B C _ _ _ _ _ J Z h U
  let f := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let g := h ≫ f
  let W := pullback.snd (str A B) g ⁻¹ᵁ (U : Z.Opens)
  let := (secAlg A g U).toAlgebra
  let φ : C →ₐ[A] Γ(Z, U) :=
    { toRingHom := secAlg C h U
      commutes' := fun a => by
        have hs : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appLE ⊤ U (by simp) =
            CommRingCat.ofHom (algebraMap A C) ≫
              (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) := by
          calc
            _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
                h.appLE ⊤ U (by simp) :=
              congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h f ⊤ U (by simp))
            _ = _ := (Scheme.ΓSpecIso_inv_naturality_assoc
              (CommRingCat.ofHom (algebraMap A C)) (h.appLE ⊤ U (by simp))).symm
        exact (congrArg (fun F => F.hom a) hs).symm }
  refine ⟨φ, rfl, ?_⟩
  have : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  have hW : IsAffineOpen W := U.2.preimage _
  have hTensor : ((bc A B f h).appLE ⊤ W (by simp)).hom.comp (psi A B C) =
      (theta A B g U).comp (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom := by
    have eL : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (pullback.fst (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := C)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_fst, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have eR : (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (pullback.snd (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have hpsi (c : C) (b : B) : psi A B C (c ⊗ₜ[A] b) =
        (pullback.fst (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
        (pullback.snd (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
      have h1 := congrArg (fun F => F.hom b) eL
      have h2 := congrArg (fun F => F.hom c) eR
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
      rw [h1, h2, ← map_mul, ← map_mul]
      simp [psi]
    have eF : (pullback.fst (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        (pullback.fst (str A B) g).appLE ⊤ W (by simp) := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      exact appLE_eq_of_eq ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) _ _ _ _
    have eS : (pullback.snd (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        h.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      refine (appLE_eq_of_eq (f₂ := pullback.snd (str A B) g ≫ h)
        (pullback.lift_snd _ _ _) _ _ _ (by simp)).trans ?_
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul c b =>
      have hF := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) eF
      have hS := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)) eS
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hF hS
      rw [RingHom.comp_apply, hpsi, map_mul, hF, hS, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, mul_comm]
      let : Algebra A Γ(pullback (str A B) g, W) :=
        (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
      symm
      change theta A B g U (secAlg C h U c ⊗ₜ[A] b) =
        ((pullback.snd (str A B) g).app U).hom (secAlg C h U c) *
          ((pullback.fst (str A B) g).appLE ⊤ W (by simp)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hk := Scheme.IdealSheafData.ker_subschemeι_app
    ((xI A B C J).comap (bc A B f h)) ⟨W, hW⟩
  rw [ker_kappa_eq]
  erw [hk]
  rw [GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine,
    GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top, Ideal.map_map, hTensor,
    ← Ideal.map_map, Ideal.comap_map_of_bijective _
      (GlobalTheory.T.sectionTensorPullbackRingHom_bijective A B _ U)]
  rfl
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.finrank_frobeniusKernelQuotient_le_pow_cotangent : ∀ (q : ℕ) (K H : Type) [Field K] [CommRing H] [Bialgebra K H] [Module.Finite K H], 0 < q → Module.finrank K (H ⧸ frobKerIdeal q K H) ≤ q ^ Module.finrank K (Cot K H) := by
  first | exact @GlobalTheory.FrobKerDim.finrank_quot_frobKerIdeal_le | exact GlobalTheory.FrobKerDim.finrank_quot_frobKerIdeal_le | (intros; apply GlobalTheory.FrobKerDim.finrank_quot_frobKerIdeal_le <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_orthogonal_rational_frame_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → Fin r → E), GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom → ∃ v : Fin r → Fin r → E, (∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v k) = 0) ∧ GlobalTheory.OrthoFrame.frm X.Ψ v ∈ X.dom := by
  first | exact @GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm | exact GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm | (intros; apply GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem homSh_injective (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M] :
    Injective ((homSh J).obj (op M)) := by
  obtain ⟨e, -, hX⟩ := GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv R J
  haveI : Module.Projective (ULift.{1} R) M := (IsProjective.iff_projective (P := M)).2 ‹_›
  constructor
  intro X Y g i _
  have surj : Function.Surjective (Linear.leftComp (ULift.{1} R) J i) :=
    fun k => ⟨Injective.factorThru k i, Injective.comp_factorThru k i⟩
  obtain ⟨h', hh'⟩ := Module.projective_lifting_property _ (e X M g) surj
  refine ⟨(e Y M).symm h', ?_⟩
  apply (e X M).injective
  rw [hX, Equiv.apply_symm_apply, hh']

end GlobalTheory.EtC
end
