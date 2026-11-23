module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineLeOrDisjoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle244
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroAgree

open GlobalTheory.MulUnramified

variable {C C₀ : Type} [CommRing C] [CommRing C₀] (π : C →+* C₀)

lemma spMap_surjective (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) :
    Function.Surjective (spMap π) := by
  intro (p : PrimeSpectrum C)
  change p ∈ Set.range (PrimeSpectrum.comap π)
  rw [range_comap_of_surjective _ _ hπ, PrimeSpectrum.mem_zeroLocus]
  intro a ha
  refine p.isPrime.mem_of_pow_mem 2 ?_
  have : a ^ 2 ∈ RingHom.ker π ^ 2 := Ideal.pow_mem_pow ha 2
  rw [hsq, Submodule.zero_eq_bot, Ideal.mem_bot] at this
  rw [this]
  exact zero_mem _

lemma preimage_eq_of_agree (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0)
    {X Y : Over (Sp C)} {f f' : X ⟶ Y}
    (h : ∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ X), y ≫ f = y ≫ f')
    (V : Y.left.Opens) : f.left ⁻¹ᵁ V = f'.left ⁻¹ᵁ V := by
  have hs : Surjective (spMap π) := ⟨spMap_surjective π hπ hsq⟩
  have hf : Surjective (pullback.fst X.hom (spMap π)) := inferInstance
  have e := congrArg (·.left) (h (Over.mk (pullback.snd X.hom (spMap π)))
    (Over.homMk (pullback.fst X.hom (spMap π)) pullback.condition))
  simp only [Over.comp_left, Over.homMk_left] at e
  exact preimage_eq _ hf.surj e V

noncomputable def alg (X : Over (Sp C)) (V : X.left.Opens) : C →+* Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ X.hom.appLE ⊤ V le_top).hom

lemma fromSpec_over (X : Over (Sp C)) {V : X.left.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = spMap (alg X V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top (Spec (CommRingCat.of C))) hV
    (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, alg, spMap, CommRingCat.ofHom_hom, Spec.map_comp]

lemma appLE_alg {X Y : Over (Sp C)} (f : X ⟶ Y) (V : Y.left.Opens) (V' : X.left.Opens)
    (hf : V' ≤ f.left ⁻¹ᵁ V) (c : C) : f.left.appLE V V' hf (alg Y V c) = alg X V' c := by
  simp only [alg, CommRingCat.hom_comp, RingHom.comp_apply]
  exact comp_appLE_apply f.left Y.hom (Over.w f) _ _ _ _ _ _ _

lemma sub_mem (hπ : Function.Surjective π) {X Y : Over (Sp C)} {f f' : X ⟶ Y}
    (h : ∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ X), y ≫ f = y ≫ f')
    {V : Y.left.Opens} (hV : IsAffineOpen V) {V' : X.left.Opens} (hV' : IsAffineOpen V')
    (hf : V' ≤ f.left ⁻¹ᵁ V) (hf' : V' ≤ f'.left ⁻¹ᵁ V) (s : Γ(Y.left, V)) :
    f.left.appLE V V' hf s - f'.left.appLE V V' hf' s ∈ (RingHom.ker π).map (alg X V') := by
  set J := (RingHom.ker π).map (alg X V')
  let q : Γ(X.left, V') →+* Γ(X.left, V') ⧸ J := Ideal.Quotient.mk J
  let ψ : C₀ →+* Γ(X.left, V') ⧸ J :=
    (Ideal.quotientMap J (alg X V') Ideal.le_comap_map).comp
      (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ψ.comp π = q.comp (alg X V') := by
    ext c
    have e : (RingHom.quotientKerEquivOfSurjective hπ).symm (π c) = Ideal.Quotient.mk _ c :=
      (RingEquiv.symm_apply_eq _).mpr rfl
    simp only [ψ, q, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
      Ideal.quotientMap_mk]
  let y : Over.mk ((Over.mk (spMap ψ)).hom ≫ spMap π) ⟶ X :=
    Over.homMk (spMap q ≫ hV'.fromSpec) (by
      rw [Category.assoc, fromSpec_over]
      simp only [Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ])
  have e := congrArg (·.left) (h (Over.mk (spMap ψ)) y)
  simp only [y, Over.comp_left, Over.homMk_left, Category.assoc] at e
  rw [← hV.SpecMap_appLE_fromSpec f.left hV' hf, ← hV.SpecMap_appLE_fromSpec f'.left hV' hf',
    ← Category.assoc, ← Category.assoc, cancel_mono, spMap, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj] at e
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact congr($e s)

lemma eq_on_map {B R : Type} [CommRing B] [CommRing R] (I : Ideal C) (hI : I ^ 2 = 0)
    (φB : C →+* B) (φR : C →+* R) (β β' : B →+* R) (hβ : β.comp φB = φR) (hβ' : β'.comp φB = φR)
    (hd : ∀ b, β b - β' b ∈ I.map φR) {x : B} (hx : x ∈ I.map φB) : β x = β' x := by
  have hJ : I.map φR * I.map φR = ⊥ := by
    rw [← Ideal.map_mul, ← pow_two, hI, Submodule.zero_eq_bot, Ideal.map_bot]
  suffices β x = β' x ∧ β x ∈ I.map φR from this.1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [← RingHom.comp_apply β, hβ, ← RingHom.comp_apply β', hβ']
    exact ⟨rfl, Ideal.mem_map_of_mem _ hc⟩
  | zero => simp
  | add x y _ _ hx hy =>
    exact ⟨by simp only [map_add, hx.1, hy.1], by simpa only [map_add] using add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [smul_eq_mul, map_mul, map_mul, ← hx.1, ← sub_eq_zero, ← sub_mul, ← Ideal.mem_bot, ← hJ]
      exact Ideal.mul_mem_mul (hd a) hx.2
    · rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hx.2

end GlobalTheory.SqZeroAgree

namespace GlobalTheory


open MulUnramified SqZeroAgree in
theorem comp_eq_of_sqZero_agree : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀),
    Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (K G : Over (Sp C)) (g g' : K ⟶ G),
    (∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ K), y ≫ g = y ≫ g') →
    ∀ (T : Over (Sp C)) (w w' : T ⟶ K),
    (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ w = j ≫ w') →
    w' ≫ g = w' ≫ g' → w ≫ g = w ≫ g' := by
  intro C C₀ _ _ π hπ hsq K G g g' hg T w w' hw h'
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  refine Scheme.hom_ext_of_forall _ _ fun t ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.left (w.left t))) isOpen_univ
  obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'V : V' ≤ g.left ⁻¹ᵁ V⟩ :=
    K.left.isBasis_affineOpens.exists_subset_of_mem_open (a := w.left t) (u := g.left ⁻¹ᵁ V) htV
      (TopologicalSpace.Opens.isOpen _)
  obtain ⟨_, ⟨W, hW, rfl⟩, htW, hWV' : W ≤ w.left ⁻¹ᵁ V'⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (a := t) (u := w.left ⁻¹ᵁ V') htV'
      (TopologicalSpace.Opens.isOpen _)
  have hV'V₂ : V' ≤ g'.left ⁻¹ᵁ V := preimage_eq_of_agree π hπ hsq hg V ▸ hV'V
  have hWV'₂ : W ≤ w'.left ⁻¹ᵁ V' := preimage_eq_of_agree π hπ hsq hw V' ▸ hWV'
  refine ⟨W, htW, ?_⟩
  have key : ∀ s, w.left.appLE V' W hWV' (g.left.appLE V V' hV'V s) =
      w.left.appLE V' W hWV' (g'.left.appLE V V' hV'V₂ s) := by
    intro s
    have hx := sub_mem π hπ hg hV hV' hV'V hV'V₂ s
    have e := eq_on_map (RingHom.ker π) hsq (alg K V') (alg T W) (w.left.appLE V' W hWV').hom
      (w'.left.appLE V' W hWV'₂).hom (RingHom.ext (appLE_alg w V' W hWV'))
      (RingHom.ext (appLE_alg w' V' W hWV'₂)) (sub_mem π hπ hw hV' hW hWV' hWV'₂) hx
    have e' : w'.left.appLE V' W hWV'₂ (g.left.appLE V V' hV'V s) =
        w'.left.appLE V' W hWV'₂ (g'.left.appLE V V' hV'V₂ s) := by
      rw [comp_appLE_apply _ _ rfl _ _ _ _ _ (le_preimage_of_comp _ _ hV'V hWV'₂),
        comp_appLE_apply _ _ rfl _ _ _ _ _ (le_preimage_of_comp _ _ hV'V₂ hWV'₂)]
      have hh : w'.left ≫ g.left = w'.left ≫ g'.left := by rw [← Over.comp_left, h', Over.comp_left]
      rw [appLE_congr hh V W _ (le_preimage_of_comp _ _ hV'V₂ hWV'₂)]
    simp only [map_sub] at e
    rw [← sub_eq_zero, ← sub_eq_zero.mpr e, e', sub_self, sub_zero]
  have fin : (w.left ≫ g.left).appLE V W (le_preimage_of_comp _ _ hV'V hWV') =
      (w.left ≫ g'.left).appLE V W (le_preimage_of_comp _ _ hV'V₂ hWV') := by
    ext s
    rw [← comp_appLE_apply _ _ rfl _ _ _ hV'V hWV', ← comp_appLE_apply _ _ rfl _ _ _ hV'V₂ hWV']
    exact key s
  rw [← hW.isoSpec_hom_fromSpec, Category.assoc, Category.assoc,
    ← hV.SpecMap_appLE_fromSpec _ hW (le_preimage_of_comp _ _ hV'V hWV'), fin,
    hV.SpecMap_appLE_fromSpec _ hW]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FiniteBirationalNear

theorem isIso_morphismRestrict_of_isNormal : ∀ {S T : Scheme.{0}} [IsLocallyNoetherian T] (ν : S ⟶ T) [IsFinite ν] (U V : T.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (V : Scheme.{0}) → Dense (U : Set T) → Dense (ν ⁻¹' (U : Set T)) → IsIso (ν ∣_ U) → IsIso (ν ∣_ V) := by
  intro S T _ ν _ U V hS hV hU hνU hiso
  have : IsReduced S := by
    haveI : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
      have := (hS x).1
      infer_instance
    exact isReduced_of_isReduced_stalk S
  have hloc : ∀ x : V, ∃ W : T.Opens, (x : T) ∈ W ∧ IsIso (ν ∣_ W) := by
    intro x
    have e := (V.stalkIso x).symm.commRingCatIsoToRingEquiv
    have h1 : IsDomain (T.presheaf.stalk (x : T)) := by
      have := (hV x).1
      exact e.toMulEquiv.isDomain _
    have h2 : IsIntegrallyClosed (T.presheaf.stalk (x : T)) := by
      have := (hV x).2
      exact IsIntegrallyClosed.of_equiv e.symm
    exact main S T ν U ‹_› ‹_› hiso hU hνU (x : T) h1 h2
  choose W hxW hW using hloc
  let W' : V → V.toScheme.Opens := fun x => V.ι ⁻¹ᵁ W x
  have hcov : iSup W' = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxW y⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) W' hcov
    fun x => ?_
  have h1 : IsIso (ν ∣_ W x ∣_ ((W x).ι ⁻¹ᵁ V)) := inferInstance
  have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict ν (W x) ((W x).ι ⁻¹ᵁ V))).1 h1
  have e : (W x).ι ''ᵁ ((W x).ι ⁻¹ᵁ V) = V.ι ''ᵁ W' x := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, inf_comm]
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict ν V (W' x))).2
    (((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictEq ν e)).1 h2)

end GlobalTheory.FiniteBirationalNear
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FormalAlg

theorem exists_isProper_isImmersion_isProjOver : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Nonempty W → ∃ (W' P : Scheme.{0}) (π : W' ⟶ W) (q : W' ⟶ P) (s : P ⟶ Spec (CommRingCat.of R)) (U : W.Opens), IsProper π ∧ (U : Set W).Nonempty ∧ IsIso (π ∣_ U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s ∧ IsImmersion q ∧ q ≫ s = π ≫ f := by
  first
  | exact @_root_.GlobalTheory.DenseClosedAffineSubsets.chow
  | exact _root_.GlobalTheory.DenseClosedAffineSubsets.chow
  | (apply _root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenseClosedAffineSubsets.chow ..)

end GlobalTheory.FormalAlg
end

section

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

namespace GlobalTheory.OrthoFrame

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (u : Fin r → Fin r → E) : Frame Ψ r :=
  fun τ k a => τ.1 (u a k)

theorem col_frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (u : Fin r → Fin r → E) (τ : Ψ) (a : Fin r) :
    col (mat (frm Ψ u) τ) a = Data.emb τ.1 (u a) := rfl

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem hermC_emb {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]

theorem im_emb_herm_self {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (x : Fin r → E) : (τ (herm G x x)).im = 0 := by
  have h2 : conj (τ (herm G x x)) = τ (herm G x x) := by
    rw [← emb_cc, HermitianTraceFormVanishing.herm_conj G hG x x]
  exact Complex.conj_eq_iff_im.1 h2

theorem dmin_frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (u : Fin r → Fin r → E) (ho : ∀ j k, j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (frm Ψ u) τ i = ∏ k : Fin i, τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
      (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))) := by
  unfold dmin lminor
  have : (gram τ.1 G (mat (frm Ψ u) τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = Matrix.diagonal (fun k => τ.1 (herm G
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))) := by
    ext a b
    simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, col_frm, hermC_emb, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · rw [ho _ _ (fun e => h (Fin.castLE_injective _ e)), map_zero]
  rw [this, Matrix.det_diagonal]

theorem psgn_mul_dmin {r : ℕ} (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (p0 : ℕ)
    (u : Fin r → Fin r → E) (ho : ∀ j k, j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) (i : Fin (r + 1)) :
    psgn p0 i * (dmin G (frm Ψ u) τ i).re = ∏ k : Fin i, (sgn p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) k : Fin r) *
      (τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))).re) := by
  have hr : ∀ w : Fin r → E, τ.1 (herm G w w) = ((τ.1 (herm G w w)).re : ℂ) := fun w =>
    Complex.ext (by simp) (by simp [im_emb_herm_self τ.1 G hG w])
  rw [dmin_frm Ψ G u ho τ i, Finset.prod_mul_distrib, psgn, ← Fin.prod_univ_eq_prod_range]
  congr 1
  rw [Finset.prod_congr rfl (fun k _ => hr _), ← Complex.ofReal_prod, Complex.ofReal_re]

theorem prod_succ {r : ℕ} (f : Fin r → ℝ) (j : Fin r) :
    ∏ k : Fin (j.succ : ℕ), f (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) k) =
      (∏ k : Fin (j.castSucc : ℕ), f (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) k)) * f j := by
  change ∏ k : Fin ((j : ℕ) + 1), f (Fin.castLE _ k) = (∏ k : Fin (j : ℕ), f (Fin.castLE _ k)) * f j
  rw [Fin.prod_univ_castSucc]
  rfl

theorem sign_of_mem {r : ℕ} (X : Data E r) (u : Fin r → Fin r → E)
    (ho : ∀ j k, j ≠ k → herm X.Gm (u j) (u k) = 0) (hu : frm X.Ψ u ∈ X.dom) (τ : X.Ψ) (j : Fin r) :
    0 < sgn X.p0 j * (τ.1 (herm X.Gm (u j) (u j))).re := by
  have h1 := (hu τ).2 j.succ
  have h0 := (hu τ).2 j.castSucc
  rw [psgn_mul_dmin X.Ψ X.Gm X.Gm_herm X.p0 u ho τ] at h1 h0
  rw [prod_succ (fun k => sgn X.p0 k * (τ.1 (herm X.Gm (u k) (u k))).re)] at h1
  exact (pos_iff_pos_of_mul_pos h1).1 h0

theorem mem_of_sign {r : ℕ} (X : Data E r) (u : Fin r → Fin r → E)
    (ho : ∀ j k, j ≠ k → herm X.Gm (u j) (u k) = 0) (hd : (Matrix.of u).det ≠ 0)
    (hs : ∀ τ : X.Ψ, ∀ j : Fin r, 0 < sgn X.p0 j * (τ.1 (herm X.Gm (u j) (u j))).re) : frm X.Ψ u ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have : mat (frm X.Ψ u) τ = τ.1.mapMatrix (Matrix.of u).transpose := by
      ext k a; rfl
    rw [this, ← RingHom.map_det, Matrix.det_transpose]
    exact (map_ne_zero τ.1).2 hd
  · rw [psgn_mul_dmin X.Ψ X.Gm X.Gm_herm X.p0 u ho τ]
    exact Finset.prod_pos fun k _ => hs τ _

end

end GlobalTheory.OrthoFrame
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Matrix Polynomial

namespace GlobalTheory.UnitaryCongruenceDetAny

theorem det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), 3 ≤ M → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → IsUStab G Λ γ → (∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M G Λ γ hM hG hfg hspan hst hcong
  classical
  obtain ⟨hherm, -⟩ := hst
  set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hM0 : (M : AlgebraicClosure E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hME : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA
  have hAΛ : ∀ x ∈ Λ, A *ᵥ x ∈ Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    have : A *ᵥ x = y := by
      rw [hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hME, one_smul]
    rw [this]; exact hy
  have hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]
  have hroot : ∀ l ∈ (g.map φ).charpoly.roots,
      IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E)) := by
    intro l hl
    have hdet : (scalar (Fin r) l - g.map φ).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact (mem_roots'.1 hl).2
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply GlobalTheory.UnitaryCongruenceDet.isIntegral_of_left_eigen A Λ hfg hspan hAΛ _ u hu
    have hgu : u ᵥ* g.map φ = l • u := by
      rw [vecMul_sub, sub_eq_zero] at hu0
      rw [← hu0]
      funext j
      simp [scalar_apply, vecMul_diagonal, mul_comm]
    rw [hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]
    funext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  obtain ⟨z, hz, hprod⟩ := GlobalTheory.UnitaryCongruenceDet.prod_eq_one_add M hM0 _ hroot
  have hφdet : φ g.det = 1 + M * z := by
    rw [RingHom.map_det, ← hprod]
    exact Matrix.det_eq_prod_roots_charpoly _

  set z₀ : E := (g.det - 1) / (M : E) with hz₀
  have hφz : φ z₀ = z := by
    rw [hz₀, map_div₀, map_sub, map_one, map_natCast, hφdet]
    field_simp
    ring
  have hz₀int : IsIntegral ℤ z₀ := by
    have h1 : IsIntegral ℤ (φ z₀) := by rw [hφz]; exact hz
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).1 h1

  have hcc := GlobalTheory.UnitaryCongruenceDet.det_mul_cc_det G g hG hherm
  have hnorm : ∀ ψ : E →+* ℂ, ‖ψ g.det‖ = 1 := by
    intro ψ
    have h1 := congrArg ψ hcc
    rw [map_mul, map_one, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj] at h1
    have h2 : Complex.normSq (ψ g.det) = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (h2.trans (one_pow 2).symm)

  have hsmall : ∀ ψ : E →+* ℂ, ‖ψ z₀‖ < 1 := by
    intro ψ
    have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
    rw [hz₀, map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    calc ‖ψ g.det - 1‖ ≤ ‖ψ g.det‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm, norm_one]; norm_num
      _ < M := by linarith
  have hz0 : z₀ = 0 := by
    by_contra hne
    let α : 𝓞 E := ⟨z₀, hz₀int⟩
    have hα : α ≠ 0 := by
      intro h; apply hne
      have := congrArg (fun a : 𝓞 E => (a : E)) h
      exact this
    obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hα
    exact absurd hσ (not_le.2 (hsmall σ))
  have : g.det - 1 = 0 := by
    have h := hz0
    rw [hz₀, div_eq_zero_iff] at h
    exact h.resolve_right hME
  exact sub_eq_zero.1 this

end GlobalTheory.UnitaryCongruenceDetAny
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (X : Data E r), 3 ≤ M → (∀ γ, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  first | exact @GlobalTheory.UnitaryCongruenceDet.det_eq_one | exact GlobalTheory.UnitaryCongruenceDet.det_eq_one | (intros; apply GlobalTheory.UnitaryCongruenceDet.det_eq_one <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.exists_candidate_borel_move_open_frames_baire : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (S : Set (GL (Fin r) E)) (a c : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ z ∈ W, ∃ γ ∈ S, ∃ b ∈ Bor X.Ψ r, lact c z = rmul (lact γ (lact a z)) b) → ∃ γ ∈ S, ∃ V : Set (Frame X.Ψ r), IsOpen V ∧ V.Nonempty ∧ V ⊆ X.dom ∧ ∀ x ∈ V, ∃ b ∈ Bor X.Ψ r, lact ((γ * a)⁻¹ * c) x = rmul x b := by
  first | exact @GlobalTheory.baire_one_candidate | exact GlobalTheory.baire_one_candidate | (intros; apply GlobalTheory.baire_one_candidate <;> assumption)
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.real_independent_skew_matrices : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (G : Matrix (Fin r) (Fin r) E), G.det ≠ 0 → ∀ e : Fin n → Matrix (Fin r) (Fin r) E, (∀ i, (e i)ᵀ * G + G * (e i).map cc = 0) → LinearIndependent (maximalRealSubfield E) e → LinearIndependent E e := by
  first | exact @GlobalTheory.linearIndependent_of_skew_of_real | exact GlobalTheory.linearIndependent_of_skew_of_real | (intros; apply GlobalTheory.linearIndependent_of_skew_of_real <;> assumption)
end
