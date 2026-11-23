module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle036
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle058
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle067
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle061
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle055
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle060
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle072
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle026
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle063
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Recog

theorem ontoAt_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {I : Type} {B A : Over S} {B' A' : Over S'}
    [GrpObj A] [GrpObj A'] {φ : B'.left ⟶ B.left} {χ : A'.left ⟶ A.left} (hφ : φ ≫ B.hom = B'.hom ≫ f)
    (hχ : IsGrpPullback A' A f χ) {ψ : I → (B ⟶ A)} {ψ' : I → (B' ⟶ A')}
    (hψ : ∀ i, (ψ' i).left ≫ χ = φ ≫ (ψ i).left) {k : Type} [Field k] {t' : Sp k ⟶ S'} {t : Sp k ⟶ S}
    (ht : t = t' ≫ f) (h : OntoAt (B := fun _ => B') ψ' t') : OntoAt (B := fun _ => B) ψ t := by
  intro y
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hχ t' t ht
  obtain ⟨n, i, x, hx⟩ := h (e.symm y)
  refine ⟨n, i, fun m => Over.homMk ((x m).left ≫ φ) ?_, ?_⟩
  · have hw := Over.w (x m)
    simp only [Over.mk_hom] at hw ⊢
    rw [Category.assoc, hφ, ← Category.assoc, hw, ht]
  · calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = (List.ofFn fun m => e (x m ≫ ψ' (i m))).prod := by
        rw [hx, map_list_prod, List.map_ofFn]; rfl
      _ = _ := by
        congr 1
        refine List.ofFn_inj.mpr (funext fun m => ?_)
        apply Over.OverMorphism.ext
        rw [he, Over.comp_left, Over.comp_left, Category.assoc, hψ]
        rfl

private lemma spMap_comp_moduli_spaces {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem exists_isTen_of_hasType : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [NumberField k] (ω : 𝓞 k) (C : Ell H (𝓞 k) ω) (T : PAT H (Sp (𝓞 k))) (r : ℕ), C.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) → HasType H T.t.act (2 * ω - 1) r 0 →
  ∃ (k₁ : IntermediateField ℚ ℂ) (_ : NumberField k₁) (hk : k ≤ k₁) (ω₁ : 𝓞 k₁) (C₁ : Ell H (𝓞 k₁) ω₁) (φ : C₁.P.A.left ⟶ C.P.A.left) (T₁ : PAT H (Sp (𝓞 k₁))) (_ : SABMap T₁.t T.t (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom))) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), EllMap C₁ C (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) φ ∧ D.p + D.q = r ∧ IsKForm D ε h ∧ (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) ∧ Nonempty (IsTen C₁ D h T₁) := by
  intro hU hL hD E _ _ _ H k _ ω C T r hP hT
  have hB : Out.PolBaseChangeSt := hL.polBaseChange

  obtain ⟨Ck, φk, hCk⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k) ω C k (algebraMap (𝓞 k) k)
  obtain ⟨Tk, mk, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ (spMap (algebraMap (𝓞 k) k)) T
  obtain ⟨Cc, φc, hCc⟩ := GlobalTheory.CM.exists_ellMap hB E H k _ Ck ℂ (algebraMap k ℂ)
  obtain ⟨Tc, mc, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ (spMap (algebraMap k ℂ)) Tk
  have hPk : Ck.IsPrincipalAt (algebraMap k ℂ) :=
    (GlobalTheory.CM.EllComp.ellMap_comp E H (𝓞 k) ω C k _ Ck (algebraMap (𝓞 k) k) φk hCk).2.1 _ hP
  have hPc : Cc.IsPrincipalAt (RingHom.id ℂ) :=
    (GlobalTheory.CM.EllComp.ellMap_comp E H k _ Ck ℂ _ Cc (algebraMap k ℂ) φc hCc).2.1 _ (by rwa [RingHom.id_comp])
  obtain ⟨nc, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mk mc
  rw [spMap_comp_moduli_spaces] at nc
  have hinj : Function.Injective ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) := by
    rw [RingHom.coe_comp]
    exact (algebraMap k ℂ).injective.comp (IsFractionRing.injective (𝓞 k) k)
  have hTc := (GlobalTheory.CM.hasType_baseChange E H (𝓞 k) ℂ _ T.t Tc.t nc (2 * ω - 1) r 0).1 hinj hT
  have hωc : ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) (2 * ω - 1) =
      2 * algebraMap k ℂ (algebraMap (𝓞 k) k ω) - 1 := by
    simp only [map_sub, map_mul, map_ofNat, map_one, RingHom.comp_apply]
  rw [hωc] at hTc

  obtain ⟨D, ε, h, ψc, hpq, hK, hpos, hFc, hOc⟩ := GlobalTheory.T.exists_homFamily_of_pureType_complex_triple hU hL E H _ Cc Tc r hPc hTc

  obtain ⟨k₁, hfin, hk, huniv⟩ := GlobalTheory.T.cmFamily_descends_to_numberField hU hL E H k _ Ck D h Tk ⊤ _ Cc φc Tc mc ψc hCc hFc
  have : FiniteDimensional ℚ k₁ := hfin
  have : NumberField k₁ := ⟨⟩
  obtain ⟨C₁, φ₁, hC₁⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k) ω C (𝓞 k₁)
    (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom)
  obtain ⟨T₁, m₁, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _
    (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom)) T
  obtain ⟨C₂, φa, hC₂⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k₁) _ C₁ k₁ (algebraMap (𝓞 k₁) k₁)
  obtain ⟨T₂, ma, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ (spMap (algebraMap (𝓞 k₁) k₁)) T₁
  have hring : (algebraMap (𝓞 k₁) k₁).comp
      (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) =
      (IntermediateField.inclusion hk).toRingHom.comp (algebraMap (𝓞 k) k) := by
    ext x; rfl
  have hring' : (algebraMap k₁ ℂ).comp (IntermediateField.inclusion hk).toRingHom = algebraMap k ℂ := by
    ext x; rfl
  have h21 := (GlobalTheory.CM.EllComp.ellMap_comp E H (𝓞 k) ω C (𝓞 k₁) _ C₁ _ φ₁ hC₁).1 k₁ _ C₂ _ φa hC₂
  rw [hring] at h21
  obtain ⟨φ₂, hφ₂, -⟩ := GlobalTheory.CM.Factor.ellMap_cancel hCk h21
  have hCc' : EllMap Cc Ck ((algebraMap k₁ ℂ).comp (IntermediateField.inclusion hk).toRingHom) φc := by
    rw [hring']; exact hCc
  obtain ⟨φ₃, hφ₃, hφ₃c⟩ := GlobalTheory.CM.Factor.ellMap_cancel hφ₂ hCc'
  obtain ⟨n21, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ ma
  obtain ⟨m₂, -⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H k k k₁ (RingHom.id k)
    (IntermediateField.inclusion hk).toRingHom).2 _ _ _ T.t Tk.t T₂.t mk n21
    (by rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, hring])
  obtain ⟨m₃, hm₃⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H k₁ k₁ ℂ (RingHom.id k₁)
    (algebraMap k₁ ℂ)).2 _ _ _ Tk.t T₂.t Tc.t m₂ mc (by rw [spMap_comp_moduli_spaces, hring'])
  obtain ⟨ψ₂, hF₂, hψ₂⟩ := huniv k₁ hk le_rfl _ C₂ φ₂ φ₃ T₂ m₂ m₃ hφ₂ hφ₃ hφ₃c hm₃

  obtain ⟨ψ₁, hF₁, hψ₁⟩ := GlobalTheory.T.cmFamily_extends_over_dedekindDomain hL hD E H (𝓞 k₁) k₁ _ C₁ D h T₁ ⊤ _ C₂ φa T₂ ma ψ₂ hC₂ hF₂

  obtain ⟨n1, hn1⟩ := GlobalTheory.ObjMaps.exists_sab_comp ma m₃
  obtain ⟨-, ⟨-, ⟨hsq3, -⟩, -⟩, -⟩ := hφ₃
  obtain ⟨-, ⟨-, ⟨hsqa, -⟩, -⟩, -⟩ := hC₂
  have hOnto : OntoAt ψ₁ (spMap ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁))) := by
    refine ontoAt_of_isGrpPullback (φ := φ₃ ≫ φa) (χ := n1.φ) ?_ n1.cart (fun a => ?_) ?_ hOc
    · rw [Category.assoc, hsqa.w, ← Category.assoc, hsq3.w, Category.assoc]
    · rw [hn1, ← Category.assoc, hψ₂ a, Category.assoc, hψ₁ a, Category.assoc]
    · rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, RingHom.id_comp]
  have hinj₁ : Function.Injective ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁)) := by
    rw [RingHom.coe_comp]
    exact (algebraMap k₁ ℂ).injective.comp (IsFractionRing.injective (𝓞 k₁) k₁)
  exact ⟨k₁, inferInstance, hk, _, C₁, φ₁, T₁, m₁, D, ε, h, hC₁, hpq, hK, hpos,
    GlobalTheory.T.nonempty_tensor_of_onto_full_family hL E H (𝓞 k₁) _ _ C₁ D ε h T₁ ψ₁ hinj₁ hK hpos hF₁ hOnto⟩

end GlobalTheory.CM.Recog
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF

theorem prod_ofFn_sum {M : Type} [Monoid M] {p q : ℕ} (f : Fin p ⊕ Fin q → M) :
    (List.ofFn fun i : Fin (p + q) => f (finSumFinEquiv.symm i)).prod =
      (List.ofFn fun i => f (Sum.inl i)).prod * (List.ofFn fun i => f (Sum.inr i)).prod := by
  rw [List.ofFn_add, List.prod_append]
  congr 2
  · congr 1
    funext i
    exact congrArg f (finSumFinEquiv_symm_apply_castAdd i)
  · congr 1
    funext i
    exact congrArg f (finSumFinEquiv_symm_apply_natAdd i)

theorem lamEq_adj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (a : 𝓞 E) : LamEq t.PP.L (t.act.act a) (𝟙 t.G) t.PP.L (𝟙 t.G) (t.act.act (H.bar a)) := by
  have := t.adj a
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  exact this

theorem exists_lamObjGood_of_cmObj : Out.SecTwistSt → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l), (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (La : ℝ), (∀ τ, τ ∈ psiSet H ↔ labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → ∀ (xB : KeyIn K) (φB : xB.P.A.left ⟶ X.B.pol.A.left), IsFibreOf X.B.pol xB (gmap K) φB → ∃ (oa : X.B.pol.OAct (𝓞 E)) (oaΨ : (X.A true).pol.OAct (𝓞 E)) (oa' : (X.A false).pol.OAct (𝓞 E)) (xΨ x' : KeyIn K) (φΨ : xΨ.P.A.left ⟶ (X.A true).pol.A.left) (φ' : x'.P.A.left ⟶ (X.A false).pol.A.left) (τΨ : Fin xΨ.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) (τ' : Fin x'.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) ≠ H.rt0}) (ℓΨ : Fin xΨ.P.g → MLine K) (ℓ' : Fin x'.P.g → MLine K) (Tl LamL : MLine K), oa.act = X.B.t.act.act ∧ oaΨ.act = (X.A true).t.act.act ∧ oa'.act = (X.A false).t.act.act ∧ LamObjGood (LamObj.mk (c := c) (nΨ := p) (n' := q) K X.B.pol oa (X.A true).pol oaΨ (X.A false).pol oa' (fun i => X.φ (Sum.inl i)) (fun i => X.φ (Sum.inr i)) (fun i => X.hh (Sum.inl i)) (fun i => X.hh (Sum.inr i)) xB xΨ x' φB φΨ φ' τΨ τ' ℓΨ ℓ' Tl LamL) (Module.finrank ℚ E / 2) La := by
  intro hS hU hL hX E _ _ _ _ H l c hstar K _ _ _ ρ σ₁ p q X La hρ hLa xB φB hB
  obtain ⟨hbij, -, -, ρ', -, h₁, h₂, hc, -⟩ := labK_spec E H l c K
  have hfpos : 0 < Module.finrank ℚ E / 2 := by
    have e := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at e
    have : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have hρρ : ρ' = ρ := by
    have : Nonempty (psiSet H) := (Nat.card_pos_iff.1 (hc ▸ hfpos)).1
    obtain ⟨τ, hτ⟩ := this
    exact Subtype.ext (((h₁ τ).1 hτ).symm.trans ((hρ τ).1 hτ))
  subst hρρ
  obtain ⟨oa, hoa, hR⟩ := GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple hL E H hstar K X.B
  obtain ⟨oaΨ, hoaΨ, hRΨ⟩ := GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple hL E H hstar K (X.A true)
  obtain ⟨oa', hoa', hR'⟩ := GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple hL E H hstar K (X.A false)
  obtain ⟨xΨ, φΨ, τΨ, hFΨ, hgΨ, hTΨ⟩ := GlobalTheory.T.exists_lie_eigenbasis_genericFibre_cmTriple hS hL E H K (X.A true) oaΨ (psiSet H) (labK c K) ρ' hoaΨ hbij
    X.ρ_sq hρ X.typeP
  obtain ⟨x', φ', τ', hF', hg', hT'⟩ := GlobalTheory.T.exists_lie_eigenbasis_genericFibre_cmTriple hS hL E H K (X.A false) oa' (psiSet H)ᶜ (labK c K) (-ρ') hoa' hbij
    (by rw [neg_sq, X.ρ_sq]) h₂ ((hasType_neg_iff E H _ _ _ ρ' 0 1 X.ρ_sq).1 X.typeM)
  choose ℓΨ hℓΨ using GlobalTheory.T.exists_metrised_line_of_lieVector hS hU hL K _ xΨ φΨ hFΨ
  choose ℓ' hℓ' using GlobalTheory.T.exists_metrised_line_of_lieVector hS hU hL K _ x' φ' hF'
  obtain ⟨Tl, LamL, k₁, k₂, k₃, k₄, k₅⟩ := GlobalTheory.LamF.exists_keyLines hS hU hL hX K _ xB φB hB
  have pB := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ xB φB).1 hB
  have pΨ := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ xΨ φΨ).1 hFΨ
  have p' := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ x' φ').1 hF'
  have gB : X.B.g = Module.finrank ℚ E / 2 * (p + q) :=
    (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ' X.B ⟨xB.P, φB, pB, xB.v, xB.basis⟩ p q X.split X.typeB X.ρ_sq).2.2.2.1
  have gA : ∀ b, (X.A b).g = Module.finrank ℚ E / 2 := fun b => by
    cases b
    · exact p'.1.symm.trans hg'
    · exact pΨ.1.symm.trans hgΨ
  have hlam : ∀ j, LamEq X.B.pol.L (X.φ j) (X.φ j) (X.A j.isLeft).pol.L ((X.A j.isLeft).t.act.act (X.hh j))
      (𝟙 (X.A j.isLeft).pol.A) := fun j =>
    (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring hL (𝓞 K) (X.A j.isLeft).pol (X.A j.isLeft).pol X.B.pol (X.A j.isLeft).pol _ _ _ _
      (X.lin j).isMonHom (X.lin j).isMonHom ((X.A j.isLeft).t.act.hom _) inferInstance ℂ
      (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance
      (σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)) (X.weil j)
  have hsym : ∀ j, star (X.hh j) = X.hh j := fun j => (hstar _).trans
    (GlobalTheory.LamF.bar_eq_of_lamEq_multiplier hL E H K (X.A j.isLeft).pol X.B.pol (X.A j.isLeft).t.act (X.φ j) (X.hh j)
      (by change 1 ≤ (X.A j.isLeft).g; rw [gA]; exact hfpos) (lamEq_adj _) (hlam j))
  have hpol := fun j : Fin p ⊕ Fin q => GlobalTheory.T.weilPairing_iff_of_cubeLBPairingIso hL K (X.A j.isLeft).pol X.B.pol (X.φ j) ((X.A j.isLeft).t.act.act (X.hh j))
    (X.lin j).isMonHom ((X.A j.isLeft).t.act.hom (X.hh j)) (hlam j)
  refine ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, hoaΨ, hoa', ?_⟩
  refine ⟨hR, hRΨ, hR', hB, hFΨ, hF', hgΨ, hg', pB.1.trans gB, hTΨ, hT', fun i a => ?_, fun i a => ?_,
    ⟨fun i => (X.lin (Sum.inl i)).isMonHom, fun i => (X.lin (Sum.inr i)).isMonHom, ?_⟩,
    ⟨fun i => hsym (Sum.inl i), fun i => hsym (Sum.inr i), fun i => ?_, fun i => ?_⟩,
    ⟨fun i => hLa (Sum.inl i), fun i => hLa (Sum.inr i)⟩, hℓΨ, hℓ', k₁, k₂, k₃, k₄, k₅⟩
  · dsimp only
    rw [hoa, hoaΨ]
    exact (X.lin (Sum.inl i)).comm a
  · dsimp only
    rw [hoa, hoa']
    exact (X.lin (Sum.inr i)).comm a
  · refine GlobalTheory.T.exists_inverse_isogeny_sum_of_cm_homs hU hL hX K σ₁ (X.A true).pol (X.A false).pol X.B.pol p q _ _
      (fun i => (X.lin (Sum.inl i)).isMonHom) (fun i => (X.lin (Sum.inr i)).isMonHom) ?_ fun y => ?_
    · change X.B.g = p * (X.A true).g + q * (X.A false).g
      rw [gB, gA, gA]
      ring
    · obtain ⟨x, hx⟩ := X.onto y
      exact ⟨fun i => x (Sum.inl i), fun i => x (Sum.inr i), hx.trans (prod_ofFn_sum fun j => x j ≫ X.φ j)⟩
  · dsimp only
    rw [hoaΨ]
    exact hpol (Sum.inl i)
  · dsimp only
    rw [hoa']
    exact hpol (Sum.inr i)

end GlobalTheory.LamF
end
end
