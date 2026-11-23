module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem affSmooth_mvPolynomial (R : Type) [CommRing R] [Nontrivial R] (r : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension r R (MvPolynomial (Fin r) R) := by
  have : Algebra.IsStandardSmooth R (MvPolynomial (Fin r) R) :=
    Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.2
      ⟨inferInstance, _, KaehlerDifferential.mvPolynomialBasis R _, by
        rintro _ ⟨i, rfl⟩
        exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply R _ i).symm⟩⟩
  exact (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).2 (by
    rw [rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis R _), Fintype.card_fin])

theorem affSmooth_of_range_eq {R S K : Type} [CommRing R] [Nontrivial R] [CommRing S] [CommRing K] {r : ℕ}
    (ψ : R →+* S) (j : S →+* K) (hj : Function.Injective j) (t : Fin r → K)
    (hg : Function.Injective (MvPolynomial.eval₂Hom (j.comp ψ) t))
    (h : (MvPolynomial.eval₂Hom (j.comp ψ) t).range = j.range) :
    ψ.IsStandardSmoothOfRelativeDimension r := by
  let g := MvPolynomial.eval₂Hom (j.comp ψ) t
  let e : MvPolynomial (Fin r) R ≃+* S :=
    (RingEquiv.ofBijective g.rangeRestrict
      ⟨fun _ _ h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩).trans
      ((RingEquiv.subringCongr h).trans (RingEquiv.ofBijective j.rangeRestrict
        ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩).symm)
  have he : ∀ P, j (e P) = g P := fun P =>
    congrArg Subtype.val ((RingEquiv.ofBijective j.rangeRestrict
        ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩).apply_symm_apply _)
  have : ψ = e.toRingHom.comp (algebraMap R (MvPolynomial (Fin r) R)) :=
    RingHom.ext fun a => hj (by
      show _ = j (e (MvPolynomial.C a))
      rw [he]
      exact (MvPolynomial.eval₂Hom_C (j.comp ψ) t a).symm)
  rw [this]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ e
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (affSmooth_mvPolynomial R r))

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem AffCover.smoothOfRelativeDimension {M : RatModel F Ω} {M' : RatModel F Ω'} {φ : Ω →ₐ[F] Ω'}
    {f : M'.Z ⟶ M.Z} {r : ℕ} (h : AffCover M M' φ f r) : SmoothOfRelativeDimension r f := by
  refine ⟨fun z => ?_⟩
  obtain ⟨U, W, t, hU, hW, hz, hUW, hind, hR⟩ := h.2 z
  have e : U ≤ f ⁻¹ᵁ W := hUW
  have nU : (U : Set M'.Z).Nonempty := ⟨z, hz⟩
  have nW : (W : Set M.Z).Nonempty := ⟨f z, hUW z hz⟩
  have : Nontrivial Γ(M.Z, W) := (M.res W nW).domain_nontrivial
  have hc : (M'.res U nU).comp (f.appLE W U e).hom = (φ : Ω →+* Ω').comp (M.res W nW) := RingHom.ext fun a => by
    show M'.res U nU _ = φ (M.res W nW a)
    rw [M.res_apply, M'.res_apply, ← h.1.valF_app nW a]
    exact M'.valF_resG e nU (f.app W a)
  refine ⟨W, hW, U, hU, hz, e, affSmooth_of_range_eq _ (M'.res U nU) (M'.res_injective U nU) t ?_ ?_⟩
  · rw [hc, injective_iff_map_eq_zero]
    intro P hP
    apply MvPolynomial.map_injective _ (M.res_injective W nW)
    rw [map_zero]
    apply hind
    rw [MvPolynomial.eval₂_map]
    exact hP
  · rw [hc, M'.range_res, hR]
    have hm : ∀ a, (φ : Ω →+* Ω').comp (M.res W nW) a ∈ φ '' (M.ringOn W : Set Ω) := fun a =>
      ⟨_, (RatModel.mem_ringOn_iff_exists nW).2 ⟨a, (M.res_apply W nW a).symm⟩, rfl⟩
    have hm' : ∀ x ∈ M.ringOn W,
        φ x ∈ (MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp (M.res W nW)) t).range := fun x hx => by
      obtain ⟨a, rfl⟩ := (RatModel.mem_ringOn_iff_exists nW).1 hx
      exact ⟨MvPolynomial.C a, by rw [MvPolynomial.eval₂Hom_C, ← M.res_apply W nW]; rfl⟩
    apply le_antisymm
    · rintro _ ⟨P, rfl⟩
      rw [Subalgebra.mem_toSubring]
      induction P using MvPolynomial.induction_on with
      | C a => rw [MvPolynomial.eval₂Hom_C]; exact Algebra.subset_adjoin (Or.inl (hm a))
      | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
      | mul_X P i hP =>
        rw [map_mul, MvPolynomial.eval₂Hom_X']
        exact mul_mem hP (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
    · intro x hx
      rw [Subalgebra.mem_toSubring] at hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        rcases hx with ⟨y, hy, rfl⟩ | ⟨i, rfl⟩
        · exact hm' y hy
        · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ i⟩
      | algebraMap c => rw [← φ.commutes]; exact hm' _ (Subalgebra.algebraMap_mem _ c)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy

theorem affCover_smooth (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r d : ℕ)
    (h : AffCover M M' φ f r) (hd : SmoothOfRelativeDimension d M.s) :
    SmoothOfRelativeDimension (d + r) M'.s := by
  have := h.smoothOfRelativeDimension
  rw [← h.1.inducedModelMorphism_comp_structureMap, Nat.add_comm]
  infer_instance

end GlobalTheory.FlagBundle
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

private theorem eq_spMap_of_specializes {X : Scheme.{0}} {K : Type} [Field K] (g : Sp K ⟶ X) {z : X}
    (h : g (IsLocalRing.closedPoint K) ⤳ z) :
    g = spMap (X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) g).hom ≫
      X.fromSpecStalk z := by
  conv_lhs => rw [← spMap_stalkClosedPointTo g]
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
  show Spec.map _ ≫ _ = Spec.map _ ≫ _
  simp only [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]

private theorem spMap_comp_spMap_divisor {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_isHom_of_generic (M : RatModel F Ω) (M' : RatModel F Ω') (f : M'.Z ⟶ M.Z) (hs : f ≫ M.s = M'.s)
    (hg : f (genericPoint M'.Z) = genericPoint M.Z) : ∃ φ : Ω →ₐ[F] Ω', M.IsHom M' φ f := by
  classical
  have hp0 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = genericPoint M.Z := by
    have h1 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = f (M'.pt (IsLocalRing.closedPoint Ω')) := rfl
    rw [h1]
    exact (congrArg f (M'.pt_apply (IsLocalRing.closedPoint Ω'))).trans hg
  have hp : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') ⤳ genericPoint M.Z := by rw [hp0]
  have hq : M.pt = spMap (M.stalkHom (genericPoint M.Z)) ≫ M.Z.fromSpecStalk (genericPoint M.Z) :=
    eq_spMap_of_specializes M.pt (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z))
  have hsurj : Function.Surjective (M.stalkHom (genericPoint M.Z)) := by
    intro x
    have hx : x ∈ M.O (genericPoint M.Z) := by rw [M.O_genericPoint]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := (M.stalkEquiv (genericPoint M.Z)).surjective ⟨x, hx⟩
    refine ⟨a, ?_⟩
    rw [← RatModel.coe_stalkEquiv, ha]
  let E := RingEquiv.ofBijective (M.stalkHom (genericPoint M.Z)) ⟨M.stalkHom_injective _, hsurj⟩
  let α := (M.Z.presheaf.stalkSpecializes hp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω') (M'.pt ≫ f)).hom
  let φ₀ : Ω →+* Ω' := α.comp E.symm.toRingHom
  have key : φ₀.comp (M.stalkHom (genericPoint M.Z)) = α := by
    ext a
    show α (E.symm (E a)) = α a
    rw [E.symm_apply_apply]
  have hpt : M'.pt ≫ f = spMap φ₀ ≫ M.pt := by
    rw [eq_spMap_of_specializes (M'.pt ≫ f) hp, hq, ← Category.assoc, ← spMap_comp_spMap_divisor, key]
  have hc : spMap (φ₀.comp (algebraMap F Ω)) = spMap (algebraMap F Ω') := by
    rw [spMap_comp_spMap_divisor, ← M.pt_s, ← Category.assoc, ← hpt, Category.assoc, hs, M'.pt_s]
  have hinj : φ₀.comp (algebraMap F Ω) = algebraMap F Ω' := by
    have h2 : CommRingCat.ofHom (φ₀.comp (algebraMap F Ω)) = CommRingCat.ofHom (algebraMap F Ω') :=
      Spec.map_injective hc
    ext a
    exact congrArg (fun g => g.hom a) h2
  exact ⟨⟨φ₀, fun a => RingHom.congr_fun hinj a⟩, hpt⟩

theorem apply_eq_of_isHom_id {M : RatModel F Ω} {χ : Ω →ₐ[F] Ω} (h : M.IsHom M χ (𝟙 M.Z)) (x : Ω) : χ x = x := by
  have hpt : (𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω)) = genericPoint M.Z := by
    exact M.pt_apply _
  have hx : x ∈ M.O ((𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω))) := by
    rw [hpt, M.O_genericPoint]; exact Algebra.mem_top
  have h2 := h.val_comp M.pt (IsLocalRing.closedPoint Ω) hx
  rw [Category.comp_id, RatModel.val_pt, RatModel.val_pt] at h2
  exact h2.symm

theorem iso_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y) :
    e.hom (genericPoint X) = genericPoint Y := by
  exact genericPoint_eq_of_isOpenImmersion e.hom

private theorem mat_map_mul_inv {ι : Type} {m : ι → ℕ} {K K' : Type} [Field K] [Field K'] (σ : K →+* K')
    (X Y : Mat m K) : (X * Y⁻¹).map σ = X.map σ * (Y.map σ)⁻¹ := by
  rw [Mat.map_mul, Mat.map_inv]

theorem exists_refines_of_iso {ι : Type} {m k : ι → ℕ} (M : RatModel F Ω) (M' : RatModel F Ω') (e : M'.Z ≅ M.Z)
    (hs : e.hom ≫ M.s = M'.s) (S : Fr M m k) :
    ∃ (φ : Ω →ₐ[F] Ω') (S' : Fr M' m k), Refines S S' φ e.hom := by
  classical
  obtain ⟨φ, hφ⟩ := exists_isHom_of_generic M M' e.hom hs (iso_genericPoint e)
  have hs' : e.inv ≫ M'.s = M.s := by rw [← hs, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨ψ, hψ⟩ := exists_isHom_of_generic M' M e.inv hs' (iso_genericPoint e.symm)
  have hid : M.IsHom M (ψ.comp φ) (𝟙 M.Z) := by
    have h1 := hφ.comp hψ
    rwa [e.inv_hom_id] at h1
  have hid' : M'.IsHom M' (φ.comp ψ) (𝟙 M'.Z) := by
    have h1 := hψ.comp hφ
    rwa [e.hom_inv_id] at h1
  have hψφ : ∀ x, ψ (φ x) = x := fun x => apply_eq_of_isHom_id hid x
  have hφψ : ∀ x, φ (ψ x) = x := fun x => apply_eq_of_isHom_id hid' x
  have pt2 : ∀ z' : M'.Z, e.inv (e.hom z') = z' := fun z' => by simp
  have memφ : ∀ {z' : M'.Z} {x : Ω}, x ∈ M.O (e.hom z') → φ x ∈ M'.O z' := fun hx => hφ.map_mem_O hx
  have memψ : ∀ {z' : M'.Z} {x : Ω'}, x ∈ M'.O z' → ψ x ∈ M.O (e.hom z') := by
    intro z' x hx
    apply hψ.map_mem_O
    rwa [pt2]
  have mm1 : ∀ g : Mat m Ω, (g.map φ).map ψ = g := by
    intro g; funext τ; ext i j; simp [Mat.map, hψφ]
  have mm2 : ∀ g : Mat m Ω', (g.map ψ).map φ = g := by
    intro g; funext τ; ext i j; simp [Mat.map, hφψ]
  have I1 : ∀ (B : Mat m Ω') (A : Mat m Ω), B.map ψ * A⁻¹ = (B * (A.map φ)⁻¹).map ψ := by
    intro B A
    have h1 := mat_map_mul_inv ψ.toRingHom B (A.map φ)
    have h2 : (B * (A.map φ)⁻¹).map ψ = B.map ψ * ((A.map φ).map ψ)⁻¹ := h1
    rw [h2, mm1]
  have I2 : ∀ (B : Mat m Ω') (A : Mat m Ω), (B.map ψ * A⁻¹).map φ = B * (A.map φ)⁻¹ := by
    intro B A
    have h1 := mat_map_mul_inv φ.toRingHom (B.map ψ) A
    have h2 : (B.map ψ * A⁻¹).map φ = (B.map ψ).map φ * (A.map φ)⁻¹ := h1
    rw [h2, mm2]
  have hdet : ∀ {A : Mat m Ω}, (∀ τ, (A τ).det ≠ 0) → ∀ τ, ((A.map φ) τ).det ≠ 0 := by
    intro A hA τ
    have h1 : ((A.map φ) τ).det = φ (A τ).det := Mat.det_map A φ.toRingHom τ
    rw [h1]
    exact (map_ne_zero φ).2 (hA τ)
  let S' : Fr M' m k :=
    { S := fun z' => {A' | A'.map ψ ∈ S.S (e.hom z')}
      loc := by
        intro z'
        obtain ⟨U, A, hzU, hA, hU⟩ := S.loc (e.hom z')
        refine ⟨e.hom ⁻¹ᵁ U, A.map φ, hzU, hdet hA, fun z'' hz'' A'' => ?_⟩
        show A''.map ψ ∈ S.S (e.hom z'') ↔ _
        rw [hU (e.hom z'') hz'' (A''.map ψ), I1]
        constructor
        · intro h
          have h1 : Par k (M'.O z'').toSubring (((A'' * (A.map φ)⁻¹).map ψ).map φ) :=
            h.map φ.toRingHom (fun x hx => memφ hx)
          rwa [mm2] at h1
        · intro h
          exact h.map ψ.toRingHom (fun x hx => memψ hx) }
  refine ⟨φ, S', ⟨le_rfl, hφ, ?_, ?_, ?_⟩⟩
  · intro z' A' hA' A hA
    have h1 : Par k (M.O (e.hom z')).toSubring (A'.map ψ * A⁻¹) :=
      (Fr.mem_iff hA).1 (show A'.map ψ ∈ S.S (e.hom z') from hA')
    have h2 : Par k (M'.O z').toSubring ((A'.map ψ * A⁻¹).map φ) :=
      h1.map φ.toRingHom (fun x hx => memφ hx)
    rwa [I2] at h2
  · unfold KeepsRad Rad
    intro z' g hg
    obtain ⟨hg0, hgO, hgr⟩ := hg
    refine ⟨(map_ne_zero φ).2 hg0, memφ hgO, fun x n hx hxn => ?_⟩
    have hx' : ψ x ∈ M.O (e.hom z') := memψ hx
    have hxn' : ψ x ^ n / g ∈ M.O (e.hom z') := by
      have h1 := memψ hxn
      rw [map_div₀, map_pow, hψφ] at h1
      exact h1
    have h2 := memφ (hgr (ψ x) n hx' hxn')
    rw [map_div₀, hφψ] at h2
    exact h2
  · intro K _ x A hA h hh
    refine ⟨x ≫ e.inv, ⟨by simp, ?_⟩, fun p hp => ?_⟩
    · have hx1 : e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
        have h1 : (x ≫ e.inv) (IsLocalRing.closedPoint K) = e.inv (x (IsLocalRing.closedPoint K)) := rfl
        rw [h1]
        simp
      have hd : ∀ τ, ((A.map φ) τ).det ≠ 0 := hdet (Fr.det_ne hA)
      have hone : (1 : Mat m Ω').map (M'.val (x ≫ e.inv)) = 1 := by
        funext τ; ext i j
        simp only [Mat.map, Matrix.map_apply, Pi.one_apply, Matrix.one_apply]
        split_ifs
        · exact RatModel.val_one _
        · exact RatModel.val_zero _
      have hinv : (1 : Mat m K)⁻¹ = 1 := by
        have h1 := Mat.mul_inv (g := (1 : Mat m K)) (fun τ => by simp)
        rwa [one_mul] at h1
      unfold Bears
      refine ⟨A.map φ, ?_, ?_⟩
      · show (A.map φ).map ψ ∈ S.S (e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)))
        rw [mm1, hx1]
        exact hA
      · rw [Mat.mul_inv hd, hone, hinv, mul_one]
        exact hh
    · rw [← hp.1, Category.assoc, e.hom_inv_id, Category.comp_id]

theorem exists_var_refines (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) (ι : Type)
    (m k : ι → ℕ) (S : Fr M m k) (h : Good M d) :
    ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m k),
      Y.dim = d ∧ Refines S S' φ f := by
  obtain ⟨hP, hSm, hGI⟩ := h
  haveI : SmoothOfRelativeDimension d M.s := hSm
  haveI : GeometricallyIntegral M.s := hGI
  haveI : GeometricallyConnected M.s := by
    constructor
    intro a b y c fst snd hpb
    have := GeometricallyIntegral.geometrically_isIntegral (f := M.s) y fst snd hpb
    infer_instance
  obtain ⟨Y, e, hd, he⟩ := GlobalTheory.ProjVar.Var.exists_iso M.s d hP
  have hs : e.inv ≫ M.s = (ratOf Y).s := by
    show e.inv ≫ M.s = Y.str
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨φ, S', hS'⟩ := exists_refines_of_iso M (ratOf Y) e.symm hs S
  exact ⟨Y, φ, e.inv, S', hd, hS'⟩

end GlobalTheory.FlagBundle
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

noncomputable section

namespace GlobalTheory.FlagBundle.QuotDual

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K]

abbrev restBlock (k : ι → ℕ) (τ : ι) (g : Mat m K) : Matrix (Rest m k τ) (Rest m k τ) K :=
  (g τ).submatrix Subtype.val Subtype.val

theorem restBlock_mul {O : Subring K} (τ : ι) (g : Mat m K) {h : Mat m K} (hh : Par k O h) :
    restBlock k τ (g * h) = restBlock k τ g * restBlock k τ h := by
  ext i j
  simp only [Matrix.submatrix_apply, Pi.mul_apply, Matrix.mul_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin (m τ) => k τ ≤ (l : ℕ)) (by simp)
    (fun l => g τ i.1 l * h τ l j.1)]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_).symm
  have hl' : (l : ℕ) < k τ := by simpa using hl
  have hj := j.2
  rw [(hh τ).2.2.2 l j.1 hl' (by show (l : ℕ) < j.1; omega), mul_zero]

theorem restBlock_one (τ : ι) : restBlock k τ (1 : Mat m K) = 1 :=
  Matrix.submatrix_one _ Subtype.val_injective

theorem restBlock_inv_mul {O : Subring K} (τ : ι) {g : Mat m K} (hg : Par k O g) :
    restBlock k τ g⁻¹ * restBlock k τ g = 1 := by
  rw [← restBlock_mul τ _ hg, Mat.inv_mul hg.det_ne, restBlock_one]

theorem restBlock_inv {O : Subring K} (τ : ι) {g : Mat m K} (hg : Par k O g) :
    (restBlock k τ g)⁻¹ = restBlock k τ g⁻¹ :=
  Matrix.inv_eq_left_inv (restBlock_inv_mul τ hg)

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

theorem span_mul_le {J : Type} [Fintype J] (O : Subalgebra F Ω) (P B : Matrix J J Ω) (hP : ∀ i j, P i j ∈ O) :
    Submodule.span O (Set.range (P * B)) ≤ Submodule.span O (Set.range B) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun l => ⟨P i l, hP i l⟩, ?_⟩
  ext j
  simp [Matrix.mul_apply, Finset.sum_apply, Subalgebra.smul_def]

variable {M : RatModel F Ω} {S : Fr M m k} {A₀ : Mat m Ω}

theorem par_generic (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A : Mat m Ω} (hA : A ∈ S.S z) :
    Par k (M.O (genericPoint M.Z)).toSubring (A * A₀⁻¹) :=
  (Fr.mem_iff h₀).1 (Fr.mem_genericPoint hA)

theorem det_dualBlock_ne (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A : Mat m Ω} (hA : A ∈ S.S z) :
    (dualBlock k τ A₀ A).det ≠ 0 := by
  have h := par_generic h₀ hA
  have e := congrArg Matrix.det (restBlock_inv_mul τ h)
  rw [Matrix.det_mul, Matrix.det_one] at e
  show ((restBlock k τ (A * A₀⁻¹))⁻¹).transpose.det ≠ 0
  rw [Matrix.det_transpose, restBlock_inv τ h]
  exact left_ne_zero_of_mul_eq_one e

theorem span_dualBlock_le (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A A' : Mat m Ω} (hA : A ∈ S.S z)
    (hA' : A' ∈ S.S z) : Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A')) ≤
      Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  have hg := (Fr.mem_iff hA).1 hA'
  have e : A' * A₀⁻¹ = (A' * A⁻¹) * (A * A₀⁻¹) := by
    rw [← mul_assoc, mul_assoc A', Mat.inv_mul (Fr.det_ne hA), mul_one]
  have e2 : dualBlock k τ A₀ A' = (restBlock k τ (A' * A⁻¹)⁻¹).transpose * dualBlock k τ A₀ A := by
    show ((restBlock k τ (A' * A₀⁻¹))⁻¹).transpose = _ * ((restBlock k τ (A * A₀⁻¹))⁻¹).transpose
    rw [e, restBlock_mul τ _ (par_generic h₀ hA), Matrix.mul_inv_rev, Matrix.transpose_mul, restBlock_inv τ hg]
  rw [e2]
  exact span_mul_le _ _ _ fun i j => (hg.inv τ).1 _ _

theorem span_dualBlock_eq (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A A' : Mat m Ω} (hA : A ∈ S.S z)
    (hA' : A' ∈ S.S z) : Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A')) =
      Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) :=
  le_antisymm (span_dualBlock_le τ h₀ hA hA') (span_dualBlock_le τ h₀ hA' hA)

theorem exists_lat_dualBlock (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (ι : Type)
    (m k : ι → ℕ) (S : Fr M m k) (τ : ι) (A₀ : Mat m Ω) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) :
    ∃ EE : M.Lat (Rest m k τ), ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  refine ⟨⟨fun z => Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ (S.nonempty z).some)), fun z => ?_⟩,
    fun z A hA => ⟨det_dualBlock_ne τ h₀ hA, span_dualBlock_eq τ h₀ hA (S.nonempty z).some_mem⟩⟩
  obtain ⟨U, A, hz, hA, hU⟩ := S.loc z
  have hm : ∀ z' ∈ U, A ∈ S.S z' := fun z' hz' => (hU z' hz' A).2 (by rw [Mat.mul_inv hA]; exact Par.one)
  exact ⟨U, dualBlock k τ A₀ A, hz, det_dualBlock_ne τ h₀ (hm z hz),
    fun z' hz' => span_dualBlock_eq τ h₀ (hm z' hz') (S.nonempty z').some_mem⟩

end GlobalTheory.FlagBundle.QuotDual
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

theorem ProjBundle.affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J]
    (EE : M.Lat J) (s : J → Ω') (h : ProjBundle M EE M' φ f s) : AffCover M M' φ f (Fintype.card J - 1) := by
  refine ⟨h.hom, fun z' => ?_⟩
  obtain ⟨U₀, b, hz, hb, hE⟩ := EE.loc (f z')
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U₀) hz
  obtain ⟨hc, hch⟩ := h.chart W b hW ⟨_, hzW⟩ fun z hzz => hE z (hle hzz)
  obtain ⟨i, hi⟩ := hc z' hzW
  obtain ⟨U, hU, hUe, hR⟩ := hch i hi.1
  have hcard : Fintype.card {j // j ≠ i} = Fintype.card J - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  let e : Fin (Fintype.card J - 1) ≃ {j // j ≠ i} := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ y, y ∈ U ↔ f y ∈ W ∧ M'.Div ((b.map φ).mulVec s) i y := fun y =>
    Set.ext_iff.1 hUe y
  refine ⟨U, W, fun k => (b.map φ).mulVec s (e k).1 / (b.map φ).mulVec s i, hU, hW, (hmem z').2 ⟨hzW, hi⟩,
    fun y hy => ((hmem y).1 hy).1, fun P hP => ?_, ?_⟩
  · apply MvPolynomial.rename_injective e e.injective
    rw [map_zero]
    refine (h.gen b hb i).2 _ ?_
    rw [MvPolynomial.eval₂_rename]
    exact hP
  · rw [hR]
    refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_mono (Set.union_subset_union_right _ ?_))
    · rintro x (hx | ⟨j, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inl hx)
      · by_cases hj : j = i
        · subst hj
          show _ / _ ∈ _
          rw [div_self hi.1]
          exact one_mem _
        · refine Algebra.subset_adjoin (Or.inr ⟨e.symm ⟨j, hj⟩, ?_⟩)
          simp only [Equiv.apply_symm_apply]
    · rintro _ ⟨k, rfl⟩
      exact ⟨(e k).1, rfl⟩

end GlobalTheory.FlagBundle
end
