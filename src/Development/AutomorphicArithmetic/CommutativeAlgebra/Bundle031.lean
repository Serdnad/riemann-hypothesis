module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
public import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

namespace UpperTheory.AdditiveHomTwist

universe v₁ v₂ u₁ u₂

private theorem biprod_iso {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (S₁ S₂ : C) [HasBinaryBiproduct S₁ S₂] (T : D)
    (s₁ : F.obj S₁ ⟶ T) (p₁ : T ⟶ F.obj S₁) (s₂ : F.obj S₂ ⟶ T) (p₂ : T ⟶ F.obj S₂)
    (h₁ : s₁ ≫ p₁ = 𝟙 _) (h₂ : s₂ ≫ p₂ = 𝟙 _) (h₁₂ : s₁ ≫ p₂ = 0) (h₂₁ : s₂ ≫ p₁ = 0)
    (ht : p₁ ≫ s₁ + p₂ ≫ s₂ = 𝟙 _) : Nonempty (F.obj (S₁ ⊞ S₂) ≅ T) := by
  refine ⟨{ hom := F.map biprod.fst ≫ s₁ + F.map biprod.snd ≫ s₂
            inv := p₁ ≫ F.map biprod.inl + p₂ ≫ F.map biprod.inr
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₁₂, reassoc_of% h₂₁,
      zero_comp, comp_zero, add_zero, zero_add]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add (f := _), biprod.total, F.map_id]
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← F.map_comp_assoc, ← F.map_comp_assoc]
    simp only [biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
      F.map_id, F.map_zero, Category.id_comp, zero_comp, comp_zero, add_zero, zero_add]
    exact ht

variable {B : Scheme.{0}} {q : ℕ}

private noncomputable def hm {P P' : B.Etale ⥤ Shv (ZMod q)} (φ : P ⟶ P') (J : Shv (ZMod q)) : HP P' J ⟶ HP P J :=
  Functor.whiskerRight (NatTrans.op φ) _

private theorem hm_id (P : B.Etale ⥤ Shv (ZMod q)) (J : Shv (ZMod q)) : hm (𝟙 P) J = 𝟙 _ := by
  unfold hm
  rw [NatTrans.op_id]
  exact Functor.whiskerRight_id' _

private theorem hm_comp {P P' P'' : B.Etale ⥤ Shv (ZMod q)} (φ : P ⟶ P') (ψ : P' ⟶ P'') (J : Shv (ZMod q)) :
    hm ψ J ≫ hm φ J = hm (φ ≫ ψ) J := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change φ.app U.unop ≫ ψ.app U.unop ≫ (x : P''.obj U.unop ⟶ J) = (φ.app U.unop ≫ ψ.app U.unop) ≫ x
  exact (Category.assoc _ _ _).symm

private theorem hm_zero (P P' : B.Etale ⥤ Shv (ZMod q)) (J : Shv (ZMod q)) : hm (0 : P ⟶ P') J = 0 := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change (0 : P.obj U.unop ⟶ P'.obj U.unop) ≫ (x : P'.obj U.unop ⟶ J) = 0
  exact zero_comp

private theorem hm_add {P P' : B.Etale ⥤ Shv (ZMod q)} (φ ψ : P ⟶ P') (J : Shv (ZMod q)) :
    hm (φ + ψ) J = hm φ J + hm ψ J := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change (φ.app U.unop + ψ.app U.unop) ≫ (x : P'.obj U.unop ⟶ J) = φ.app U.unop ≫ x + ψ.app U.unop ≫ x
  exact Preadditive.add_comp _ _ _ _ _ _

private theorem transfer (S : SShv B q) [Injective S] {G : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} (e : S.obj ≅ G) :
    ∃ h : Presheaf.IsSheaf (EtTop B) G, Injective (⟨G, h⟩ : SShv B q) := by
  have h : Presheaf.IsSheaf (EtTop B) G := (Presheaf.isSheaf_of_iso_iff e).1 S.property
  refine ⟨h, ?_⟩
  have i : S ≅ (⟨G, h⟩ : SShv B q) :=
    (fullyFaithfulSheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).preimageIso e
  exact Injective.of_iso i inferInstance

end UpperTheory.AdditiveHomTwist

open UpperTheory.AdditiveHomTwist ZeroObject in
theorem UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct :
    ∀ (q : ℕ) (B : Scheme.{0}), (∀ P P' : B.Etale ⥤ Shv (ZMod q), Nonempty (P ≅ P') → Good P → Good P') ∧ (∀ P : B.Etale ⥤ Shv (ZMod q), (∀ U, IsZero (P.obj U)) → Good P) ∧ ∀ (P P₁ P₂ : B.Etale ⥤ Shv (ZMod q)) (i₁ : P₁ ⟶ P) (r₁ : P ⟶ P₁) (i₂ : P₂ ⟶ P) (r₂ : P ⟶ P₂), i₁ ≫ r₁ = 𝟙 _ → i₂ ≫ r₂ = 𝟙 _ → i₁ ≫ r₂ = 0 → i₂ ≫ r₁ = 0 → r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 _ → Good P₁ → Good P₂ → Good P := by
  intro q B
  refine ⟨?_, ?_, ?_⟩
  · intro P P' hPP hP
    obtain ⟨e⟩ := hPP
    unfold Good at hP ⊢
    intro J hJ
    obtain ⟨h, hi⟩ := hP J hJ
    have e' : HP P J ≅ HP P' J :=
      { hom := hm e.inv J
        inv := hm e.hom J
        hom_inv_id := by rw [hm_comp, e.hom_inv_id, hm_id]
        inv_hom_id := by rw [hm_comp, e.inv_hom_id, hm_id] }
    exact transfer (⟨HP P J, h⟩ : SShv B q) e'
  · intro P hP
    unfold Good
    intro J hJ
    have hz : IsZero (HP P J) := by
      rw [IsZero.iff_id_eq_zero]
      have h0 : (𝟙 P : P ⟶ P) = 0 :=
        NatTrans.ext (funext fun U => (hP U).eq_of_src _ _)
      rw [← hm_id, h0, hm_zero]
    have hz0 : IsZero ((sheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
        (0 : SShv B q)) :=
      Functor.map_isZero _ (isZero_zero _)
    exact transfer (0 : SShv B q) (hz0.iso hz)
  · intro P P₁ P₂ i₁ r₁ i₂ r₂ h1 h2 h12 h21 ht hP₁ hP₂
    unfold Good at hP₁ hP₂ ⊢
    intro J hJ
    obtain ⟨g₁, hi₁⟩ := hP₁ J hJ
    obtain ⟨g₂, hi₂⟩ := hP₂ J hJ
    let S₁ : SShv B q := ⟨HP P₁ J, g₁⟩
    let S₂ : SShv B q := ⟨HP P₂ J, g₂⟩
    haveI : Injective S₁ := hi₁
    haveI : Injective S₂ := hi₂
    obtain ⟨e⟩ := biprod_iso (sheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q))))
      S₁ S₂ (HP P J) (hm r₁ J) (hm i₁ J) (hm r₂ J) (hm i₂ J)
      (by rw [hm_comp, h1, hm_id]; rfl) (by rw [hm_comp, h2, hm_id]; rfl)
      (by rw [hm_comp, h21, hm_zero]) (by rw [hm_comp, h12, hm_zero])
      (by rw [hm_comp, hm_comp, ← hm_add, ht, hm_id])
    exact transfer (S₁ ⊞ S₂) e
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

namespace UpperTheory.BaseNoeth

private theorem exists_ratHom {A : Type} [CommRing A] (h : ∀ k : ℕ, k ≠ 0 → IsUnit (k : A)) :
    Nonempty (ℚ →+* A) := by
  have hu : ∀ y : nonZeroDivisors ℤ, IsUnit (Int.castRingHom A y) := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hn := h y.natAbs (Int.natAbs_ne_zero.mpr hy0)
    rcases Int.natAbs_eq y with e | e
    · have : Int.castRingHom A y = (y.natAbs : A) := by
        conv_lhs => rw [e]
        simp
      simpa [this] using hn
    · have : Int.castRingHom A y = -(y.natAbs : A) := by
        conv_lhs => rw [e]
        simp
      simpa [this] using hn.neg
  exact ⟨IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) hu⟩

variable {p : ℕ} [Fact p.Prime]

private theorem units_of {A : Type} [CommRing A] (hp : IsUnit ((p : ℕ) : A))
    (hu : ∀ k : ℕ, k.Coprime p → IsUnit (k : A)) (k : ℕ) (hk : k ≠ 0) : IsUnit (k : A) := by
  have pp : p.Prime := Fact.out
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p pp.ne_one
  have hcop : m.Coprime p := ((Nat.Prime.coprime_iff_not_dvd pp).mpr hm).symm
  rw [Nat.cast_mul, Nat.cast_pow]
  exact (hp.pow e).mul (hu m hcop)

private theorem core (D : Datum p) {A : Type} [CommRing A] (hp : IsUnit ((p : ℕ) : A))
    (hu : ∀ k : ℕ, k.Coprime p → IsUnit (k : A)) (ρ : A) (hρ : ρ ^ 2 - D.tr * ρ + D.nm = 0)
    (t : Fin D.a → (𝓞 D.F →+* A)) (hω : ∀ i, t i D.ω = ρ)
    (hc : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) :
    ∃ (R₁ : Subring A) (_ : IsNoetherianRing R₁) (b₁ : Base D R₁), IsUnit ((p : ℕ) : R₁) ∧
      ((b₁.ρ : R₁) : A) = ρ ∧ ∀ i c, ((b₁.t i c : R₁) : A) = t i c := by
  classical
  obtain ⟨f⟩ := exists_ratHom (units_of hp hu)
  letI : Algebra ℚ A := f.toAlgebra

  obtain ⟨G, hG⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 D.F)).FG)

  have hw : ∀ ij : Fin D.a × Fin D.a, ∃ c : 𝓞 D.F →₀ A, ij.1 ≠ ij.2 →
      (c.sum fun x a => a * (t ij.1 x - t ij.2 x)) = 1 := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨0, fun h => absurd hij h⟩
    · have h1 : (1 : A) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [hc i j hij]; trivial
      obtain ⟨c, hc'⟩ := (Finsupp.mem_ideal_span_range_iff_exists_finsupp).mp h1
      exact ⟨c, fun _ => hc'⟩
  choose w hw using hw

  let T : Finset A := insert ρ ((Finset.univ.biUnion fun i : Fin D.a => G.image (t i)) ∪
    (Finset.univ.biUnion fun ij : Fin D.a × Fin D.a => (w ij).support.image (w ij)))
  let B : Subalgebra ℚ A := Algebra.adjoin ℚ (T : Set A)
  have hfg : B.FG := Subalgebra.fg_adjoin_finset T
  haveI : Algebra.FiniteType ℚ B := (Subalgebra.fg_iff_finiteType B).mp hfg
  haveI hN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℚ B
  have hTB : ∀ a ∈ T, a ∈ B := fun a ha => Algebra.subset_adjoin (by exact_mod_cast ha)
  have hρB : ρ ∈ B := hTB _ (Finset.mem_insert_self _ _)
  have htB : ∀ i c, t i c ∈ B := by
    intro i c
    have hcG : c ∈ Submodule.span ℤ (G : Set (𝓞 D.F)) := by rw [hG]; trivial
    induction hcG using Submodule.span_induction with
    | mem x hx =>
      refine hTB _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_))
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (by exact_mod_cast hx)⟩
    | zero => simpa using B.zero_mem
    | add x y _ _ hx hy => simpa using B.add_mem hx hy
    | smul a x _ hx =>
      have : t i (a • x) = (a : A) * t i x := by simp
      rw [this]
      exact B.mul_mem (by simpa using B.toSubring.intCast_mem a) hx
  have hwB : ∀ ij x, w ij x ∈ B := by
    intro ij x
    by_cases hx : x ∈ (w ij).support
    · refine hTB _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
      exact Finset.mem_biUnion.mpr ⟨ij, Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩
    · rw [Finsupp.notMem_support_iff.mp hx]; exact B.zero_mem
  have hun : ∀ k : ℕ, k ≠ 0 → IsUnit ((k : ℕ) : B.toSubring) := by
    intro k hk
    have h := (IsUnit.mk0 (k : ℚ) (by exact_mod_cast hk)).map (algebraMap ℚ B)
    simpa using h
  let t₁ : Fin D.a → (𝓞 D.F →+* B.toSubring) := fun i => (t i).codRestrict B.toSubring (htB i)
  let ρ₁ : B.toSubring := ⟨ρ, hρB⟩
  have pp : p.Prime := Fact.out
  have hpu : IsUnit ((p : ℕ) : B.toSubring) := hun p pp.ne_zero
  refine ⟨B.toSubring, hN, ?_⟩
  refine ⟨⟨fun k hk => hun k ?_, ρ₁, ?_, t₁, ?_, ?_, ?_⟩, hpu, rfl, fun i c => rfl⟩
  · rintro rfl
    have := (Nat.coprime_zero_left p).mp hk
    exact pp.ne_one this
  · apply Subtype.ext
    simpa [ρ₁] using hρ
  · intro i
    exact Subtype.ext (hω i)
  · intro i j hij
    rw [Ideal.eq_top_iff_one]
    have key : ((((w (i, j)).support.sum fun x =>
        (⟨w (i, j) x, hwB _ x⟩ : B.toSubring) * (t₁ i x - t₁ j x)) : B.toSubring)) = 1 := by
      apply Subtype.ext
      have := hw (i, j) hij
      rw [Finsupp.sum] at this
      simpa [t₁] using this
    rw [← key]
    exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)
  · intro i j _ k _ _ β
    exfalso
    have h1 := hpu.map β
    simp at h1

private theorem gam_toSpecΓ {S : Scheme.{0}} {R₁ : Type} [CommRing R₁] (f : R₁ →+* Γ(S, ⊤)) (a : R₁) :
    gam (S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) : S ⟶ Sp R₁) a = f a := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv ≫
      (S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)).appTop = CommRingCat.ofHom f := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Scheme.toSpecΓ_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun g => CommRingCat.Hom.hom g a) h

end UpperTheory.BaseNoeth

open UpperTheory.BaseNoeth in
theorem UpperTheory.exists_noetherian_base_link :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0}) (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsNoetherianRing R₁) (b₁ : Base D R₁) (s₁ : S ⟶ Sp R₁), IsUnit ((p : ℕ) : R₁) ∧ Link b b₁ s s₁ := by
  intro p _ D R _ b S s hp
  let g : R →+* Γ(S, ⊤) := gam s
  obtain ⟨R₁, hN, b₁, hpu, h1, h2⟩ := core D (A := Γ(S, ⊤)) hp
    (fun k hk => by simpa using (b.unit k hk).map g) (g b.ρ)
    (by simpa using congrArg g b.ρ_root)
    (fun i => g.comp (b.t i)) (fun i => by simp [b.t_ω])
    (fun i j hij => by
      have h := congrArg (Ideal.map g) (b.comax i j hij)
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
      simpa [Function.comp_def] using h)
  refine ⟨R₁, inferInstance, hN, b₁, S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom R₁.subtype), hpu, ?_, ?_⟩
  · rw [gam_toSpecΓ]
    exact h1.symm
  · intro i c
    rw [gam_toSpecΓ]
    exact (h2 i c).symm
end
