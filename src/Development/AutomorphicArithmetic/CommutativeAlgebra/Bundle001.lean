module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.RingTheory.MvPolynomial.Tower
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

@[expose] public section

section

noncomputable section
open Polynomial

theorem UpperTheory.exists_eval_roots_symmetric_eq_algebraMap :
    ∀ (A : Type) [CommRing A] (N : ℕ) (g : A[X]) (F : MvPolynomial (Fin N) A), F.IsSymmetric → ∃ a : A, ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → MvPolynomial.aeval x F = algebraMap A S a := by
  intro A _ N g F hF
  obtain ⟨P, hP⟩ := MvPolynomial.esymmAlgHom_fin_surjective A (le_refl N) ⟨F, hF⟩
  have hPF : MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A (i + 1)) P = F := by
    rw [← MvPolynomial.esymmAlgHom_apply, hP]
  let c : Fin N → A := fun i => (-1) ^ ((i : ℕ) + 1) * g.coeff (N - ((i : ℕ) + 1))
  refine ⟨MvPolynomial.aeval c P, ?_⟩
  intro S _ _ x hg
  have key : ∀ i : Fin N, MvPolynomial.aeval x (MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1)) =
      algebraMap A S (c i) := by
    intro i
    have hi := i.2
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    set s := Finset.univ.val.map x with hs
    have hcs : Multiset.card s = N := by simp [s]
    have hprod : (s.map fun t => X - C t).prod = g.map (algebraMap A S) := by
      rw [hg, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]
      rfl
    have hk : N - ((i : ℕ) + 1) ≤ Multiset.card s := by omega
    have hco := Multiset.prod_X_sub_C_coeff s hk
    rw [hprod, Polynomial.coeff_map, hcs, show N - (N - ((i : ℕ) + 1)) = (i : ℕ) + 1 by omega]
      at hco
    simp only [c, map_mul, map_pow, map_neg, map_one, hco]
    rw [← mul_assoc, ← mul_pow]
    simp
  have hcomp : (MvPolynomial.aeval x).comp
      (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1))) =
      MvPolynomial.aeval (fun i => algebraMap A S (c i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.aeval_X, key]
  calc MvPolynomial.aeval x F
      = ((MvPolynomial.aeval x).comp
          (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1)))) P := by
        rw [← hPF]
        rfl
    _ = MvPolynomial.aeval (fun i => algebraMap A S (c i)) P := by rw [hcomp]
    _ = algebraMap A S (MvPolynomial.aeval c P) := MvPolynomial.aeval_algebraMap_apply S c P

end
end

section

theorem UpperTheory.dvd_exponent_of_pow_eq_laurent_monomial :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O] [IsLocalRing O] (c : ℕ) (v : (LaurentPolynomial O)ˣ), (v : LaurentPolynomial O) ^ q = LaurentPolynomial.T (c : ℤ) → q ∣ c := by
  intro q _ O _ _ c v hv
  classical
  let φ : LaurentPolynomial O →+* LaurentPolynomial (IsLocalRing.ResidueField O) :=
    AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O)
  have hT : ∀ n : ℤ, φ (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
    intro n
    show AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O) (AddMonoidAlgebra.single n 1) =
      AddMonoidAlgebra.single n 1
    rw [AddMonoidAlgebra.mapRingHom_single, map_one]
  have hw : (φ v) ^ q = LaurentPolynomial.T (c : ℤ) := by
    rw [← map_pow, hv, hT]
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow (φ v)
  have hpq : p ^ q = Polynomial.X ^ (c + q * n) := by
    apply Polynomial.toLaurent_injective
    rw [map_pow, hp, mul_pow, hw, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add,
      Polynomial.toLaurent_X_pow]
    congr 1
  have hdeg := congrArg Polynomial.natDegree hpq
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_pow] at hdeg
  have h1 : q ∣ q * n + c := ⟨p.natDegree, by rw [add_comm]; exact hdeg.symm⟩
  exact (Nat.dvd_add_right (dvd_mul_right q n)).mp h1
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.isAffine_isLocalizationAway_of_range_eq_basicOpen :
    ∀ {U W : Scheme.{0}} [IsAffine U] (a : W ⟶ U) [IsOpenImmersion a] (t : Γ(U, ⊤)),
        Set.range a = (U.basicOpen t : Set U) →
        IsAffine W ∧ (∀ x : Γ(W, ⊤), ∃ (k : ℕ) (y : Γ(U, ⊤)), a.appTop.hom t ^ k * x = a.appTop.hom y) ∧
          ∀ y : Γ(U, ⊤), a.appTop.hom y = 0 → ∃ k : ℕ, t ^ k * y = 0 := by
  intro U W _ a _ t h
  have hr : Set.range a = Set.range (U.basicOpen t).ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  let χ := IsOpenImmersion.isoOfRangeEq a (U.basicOpen t).ι hr
  have hfac : χ.hom ≫ (U.basicOpen t).ι = a := IsOpenImmersion.isoOfRangeEq_hom_fac a _ hr
  haveI : IsAffine (U.basicOpen t) := (isAffineOpen_top U).basicOpen t
  have hW : IsAffine W := IsAffine.of_isIso χ.hom
  have happ : ∀ r, a.appTop.hom r =
      χ.hom.appTop.hom (algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) r) := by
    intro r
    rw [← hfac, Scheme.Hom.comp_appTop]
    rfl
  have hl : ∀ x, χ.inv.appTop.hom (χ.hom.appTop.hom x) = x := by
    intro x
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, χ.inv_hom_id]
    simp
  have hr' : ∀ x, χ.hom.appTop.hom (χ.inv.appTop.hom x) = x := by
    intro x
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, χ.hom_inv_id]
    simp
  refine ⟨hW, ?_, ?_⟩
  · intro x
    obtain ⟨⟨ℓ, m⟩, hℓ⟩ := IsLocalization.surj (Submonoid.powers t) (χ.inv.appTop.hom x)
    obtain ⟨k, hk⟩ := m.2
    have hk' : t ^ k = (m : Γ(U, ⊤)) := hk
    have hℓ' : χ.inv.appTop.hom x * algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) (t ^ k) =
        algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) ℓ := by
      rw [hk']
      exact hℓ
    refine ⟨k, ℓ, ?_⟩
    rw [happ, happ, ← hℓ']
    simp only [map_pow, map_mul, hr']
    ring
  · intro y hy
    have h0 : algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) y = 0 := by
      have h2 := congrArg χ.inv.appTop.hom ((happ y).symm.trans hy)
      rwa [hl, map_zero] at h2
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers t) _ y).mp h0
    exact ⟨k, hk⟩
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem UpperTheory.bijective_sigma_spec_points_coproduct :
    ∀ {I : Type} (Z : I → Scheme.{0}) (K : Type) [Field K], Function.Bijective (fun p : (Σ c, (Spec (CommRingCat.of K) ⟶ Z c)) => p.2 ≫ Sigma.ι Z p.1) := by
  intro I Z K _
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  constructor
  · rintro ⟨c, f⟩ ⟨c', f'⟩ h
    simp only at h
    have hz : (Sigma.ι Z c) (f z) = (Sigma.ι Z c') (f' z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
    have hs := (sigmaι_eq_iff Z c c' (f z) (f' z)).mp hz
    obtain ⟨rfl, -⟩ := Sigma.mk.inj hs
    have hff : f = f' := (cancel_mono (Sigma.ι Z c)).mp h
    rw [hff]
  · intro f
    obtain ⟨⟨c, y⟩, hy⟩ := (sigmaMk Z).surjective (f z)
    rw [sigmaMk_mk] at hy
    have H : Set.range f ⊆ Set.range (Sigma.ι Z c) := by
      rintro _ ⟨w, rfl⟩
      exact ⟨y, by rw [hy, Subsingleton.elim w z]⟩
    exact ⟨⟨c, IsOpenImmersion.lift (Sigma.ι Z c) f H⟩, IsOpenImmersion.lift_fac _ _ _⟩
end

section

open CategoryTheory Limits AlgebraicGeometry

private theorem core {J : Type} [SmallCategory J] [IsCofiltered J]
    (B DZ DY O : J ⥤ Scheme.{0}) (S0 Z0 Y0 : Scheme.{0})
    (pZ : DZ ⟶ B) (pY : DY ⟶ B) (α : DZ ⟶ DY) (ι : O ⟶ DY) (g : DZ ⟶ O)
    (hg : g ≫ ι = α) (hα : α ≫ pY = pZ) [∀ k, Mono (ι.app k)]
    (qB : B ⟶ (Functor.const J).obj S0) (qZ : DZ ⟶ (Functor.const J).obj Z0)
    (qY : DY ⟶ (Functor.const J).obj Y0)
    (pZ0 : Z0 ⟶ S0) (pY0 : Y0 ⟶ S0) (α0 : Z0 ⟶ Y0) (hα0 : α0 ≫ pY0 = pZ0)
    (hq : ∀ k, qZ.app k ≫ α0 = α.app k ≫ qY.app k)
    (hZ : ∀ k, IsPullback (qZ.app k) (pZ.app k) pZ0 (qB.app k))
    (hY : ∀ k, IsPullback (qY.app k) (pY.app k) pY0 (qB.app k))
    [LocallyOfFinitePresentation pZ0] [LocallyOfFiniteType pY0]
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (DZ.map f)]
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (O.map f)]
    [∀ k, CompactSpace (DZ.obj k)] [∀ k, CompactSpace (O.obj k)]
    [∀ k, QuasiSeparatedSpace (O.obj k)]
    (cO : Cone O) (hO : IsLimit cO) (cZ : Cone DZ) (hcZ : IsLimit cZ)
    (E : cO.pt ≅ cZ.pt) (hE : ∀ k, E.hom ≫ cZ.π.app k ≫ g.app k = cO.π.app k)
    (a : cZ.pt ⟶ Z0) (ha : ∀ k, cZ.π.app k ≫ qZ.app k = a) :
    ∃ k, IsIso (g.app k) := by
  let tO : O ⟶ (Functor.const J).obj S0 := ι ≫ qY ≫ (Functor.const J).map pY0
  let tZ : DZ ⟶ (Functor.const J).obj S0 := qZ ≫ (Functor.const J).map pZ0
  have htO : ∀ k, tO.app k = ι.app k ≫ qY.app k ≫ pY0 := fun k => rfl
  have htZ : ∀ k, tZ.app k = qZ.app k ≫ pZ0 := fun k => rfl
  have hgk : ∀ k, g.app k ≫ ι.app k = α.app k := fun k => by
    simpa using congr_app hg k
  have hαk : ∀ k, α.app k ≫ pY.app k = pZ.app k := fun k => by
    simpa using congr_app hα k
  have hcZg : ∀ k, cZ.π.app k ≫ g.app k = E.inv ≫ cO.π.app k := by
    intro k
    rw [← hE k]
    simp
  have hOq : ∀ k, cO.π.app k ≫ ι.app k ≫ qY.app k = E.hom ≫ a ≫ α0 := by
    intro k
    calc cO.π.app k ≫ ι.app k ≫ qY.app k
        = E.hom ≫ cZ.π.app k ≫ (g.app k ≫ ι.app k) ≫ qY.app k := by
          rw [← hE k]
          simp
      _ = E.hom ≫ (cZ.π.app k ≫ qZ.app k) ≫ α0 := by
          rw [hgk, ← hq]
          simp
      _ = E.hom ≫ a ≫ α0 := by rw [ha]
  obtain ⟨i, h, hh1, hh2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    O tO pZ0 cO hO (E.hom ≫ a) (by
      refine NatTrans.ext (funext fun k => ?_)
      rw [NatTrans.comp_app, htO, Functor.const_map_app, reassoc_of% (hOq k), hα0]
      simp)
  obtain ⟨k, u, hu⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    DZ tZ pZ0 cZ hcZ (g.app i ≫ h) (qZ.app i)
    (by
      simp only [htZ, Category.assoc, hh2, htO]
      rw [reassoc_of% (hgk i), reassoc_of% (hq i).symm, hα0])
    (htZ i)
    (by
      rw [reassoc_of% (hcZg i), hh1]
      simp [ha])
  obtain ⟨k', v, hv⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    O tO pY0 cO hO (h ≫ α0) (ι.app i ≫ qY.app i)
    (by rw [Category.assoc, hα0, hh2])
    (by rw [htO]; simp only [Category.assoc])
    (by rw [reassoc_of% hh1, hOq])
  obtain ⟨m, w1, w2, hw⟩ := IsCofiltered.cospan u v
  have hZm : (O.map (w1 ≫ u) ≫ h) ≫ pZ0 = (ι.app m ≫ pY.app m) ≫ qB.app m := by
    rw [Category.assoc, hh2, NatTrans.naturality]
    simp [htO, (hY m).w]
  let s := (hZ m).lift (O.map (w1 ≫ u) ≫ h) (ι.app m ≫ pY.app m) hZm
  refine ⟨m, ⟨⟨s, ?_, ?_⟩⟩⟩
  · apply (hZ m).hom_ext
    · rw [Category.assoc, (hZ m).lift_fst, Category.id_comp, ← g.naturality_assoc,
        Functor.map_comp, Category.assoc, hu, ← Category.assoc, ← Functor.map_comp,
        qZ.naturality]
      simp
    · rw [Category.assoc, (hZ m).lift_snd, Category.id_comp, reassoc_of% (hgk m), hαk m]
  · rw [← cancel_mono (ι.app m), Category.assoc, hgk m, Category.id_comp]
    apply (hY m).hom_ext
    · rw [Category.assoc, ← hq m, ← Category.assoc, (hZ m).lift_fst, hw, Functor.map_comp]
      simp only [Category.assoc]
      rw [hv, ← Functor.map_comp_assoc, ι.naturality_assoc, qY.naturality]
      simp
    · rw [Category.assoc, hαk m, (hZ m).lift_snd]

private noncomputable def toConst {I : Type} [SmallCategory I] (D : I ⥤ Scheme.{0}) {j i0 : I}
    (e0 : j ⟶ i0) : Over.forget j ⋙ D ⟶ (Functor.const (Over j)).obj (D.obj i0) where
  app k := D.map (k.hom ≫ e0)
  naturality k k' f := by
    have := Over.w f
    simp only [Functor.comp_map, Over.forget_map, Functor.const_obj_map, Category.comp_id,
      Functor.comp_obj, Over.forget_obj, Functor.const_obj_obj]
    rw [← D.map_comp, reassoc_of% this]

theorem UpperTheory.limit_compact_of_cofiltered_cartesian_affine_transition :
    ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (B DZ DY : I ⥤ Scheme.{0})
        [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
        (α : DZ ⟶ DY) (pZ : DZ ⟶ B) (pY : DY ⟶ B), α ≫ pY = pZ →
        (∀ {i j : I} (f : i ⟶ j), IsPullback (DZ.map f) (pZ.app i) (pZ.app j) (B.map f)) →
        (∀ {i j : I} (f : i ⟶ j), IsPullback (DY.map f) (pY.app i) (pY.app j) (B.map f)) →
        ∀ (cZ : Cone DZ) (_ : IsLimit cZ) (cY : Cone DY) (_ : IsLimit cY),
        (∀ i, CompactSpace (DZ.obj i)) → (∀ i, QuasiSeparatedSpace (DZ.obj i)) →
        (∀ i, CompactSpace (DY.obj i)) → (∀ i, QuasiSeparatedSpace (DY.obj i)) →
        ∀ (i0 : I), LocallyOfFinitePresentation (pZ.app i0) → LocallyOfFiniteType (pY.app i0) →
        ∀ (m : cZ.pt ⟶ cY.pt) [IsOpenImmersion m], (∀ i, cZ.π.app i ≫ α.app i = m ≫ cY.π.app i) →
        ∀ (j : I) (_ : j ⟶ i0) (V : (DY.obj j).Opens), IsCompact (V : Set (DY.obj j)) →
          α.app j ⁻¹ᵁ V = ⊤ → cY.π.app j ⁻¹ᵁ V = m.opensRange →
          ∃ (l : I) (_ : l ⟶ j), IsOpenImmersion (α.app l) := by
  intro I _ _ B DZ DY _ α pZ pY hα hZpb hYpb cZ hcZ cY hcY hcZ1 hqZ1 hcY1 hqY1 i0 _ _ m _ hm j e0 V
    hV hαV hmV
  have hDZaff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (DZ.map f) := fun f =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (hZpb f).flip
      inferInstance
  have hDYaff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (DY.map f) := fun f =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (hYpb f).flip
      inferInstance
  have hDZaff' : ∀ {a b : Over j} (f : a ⟶ b), IsAffineHom ((Over.forget j ⋙ DZ).map f) :=
    fun f => hDZaff f.left
  have hDZc' : ∀ k : Over j, CompactSpace ((Over.forget j ⋙ DZ).obj k) := fun k => hcZ1 k.left
  let O := opensDiagram DY j V
  let ι : O ⟶ Over.forget j ⋙ DY := opensDiagramι DY j V
  let α' : Over.forget j ⋙ DZ ⟶ Over.forget j ⋙ DY := Functor.whiskerLeft (Over.forget j) α
  have hOc : ∀ k : Over j, CompactSpace (O.obj k) := fun k =>
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := DY.map k.hom) _ V.2 hV)
  have hOq : ∀ k : Over j, QuasiSeparatedSpace (O.obj k) := fun k => by
    haveI : QuasiSeparatedSpace ((Over.forget j ⋙ DY).obj k) := hqY1 k.left
    exact quasiSeparatedSpace_of_quasiSeparated (ι.app k)
  have hrange : ∀ k : Over j, Set.range (α'.app k) ⊆ Set.range (ι.app k) := by
    intro k y hy
    obtain ⟨x, rfl⟩ := hy
    have hpre : α.app k.left ⁻¹ᵁ (DY.map k.hom ⁻¹ᵁ V) = ⊤ := by
      rw [← Scheme.Hom.comp_preimage, ← α.naturality, Scheme.Hom.comp_preimage, hαV]
      simp
    have hx : x ∈ α.app k.left ⁻¹ᵁ (DY.map k.hom ⁻¹ᵁ V) := by
      rw [hpre]
      trivial
    exact ⟨⟨_, hx⟩, rfl⟩
  let g : Over.forget j ⋙ DZ ⟶ O :=
    { app := fun k => IsOpenImmersion.lift (ι.app k) (α'.app k) (hrange k)
      naturality := by
        intro k k' f
        rw [← cancel_mono (ι.app k'), Category.assoc, Category.assoc, ι.naturality]
        simp only [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac_assoc]
        exact α'.naturality f }
  have hgk : ∀ k, g.app k ≫ ι.app k = α'.app k := fun k => IsOpenImmersion.lift_fac _ _ _
  let E : (cY.π.app j ⁻¹ᵁ V).toScheme ≅ cZ.pt :=
    IsOpenImmersion.isoOfRangeEq (cY.π.app j ⁻¹ᵁ V).ι m (by simp [hmV])
  have hE : ∀ k : Over j, E.hom ≫ (cZ.whisker (Over.forget j)).π.app k ≫ g.app k =
      (opensCone DY cY j V).π.app k := by
    intro k
    apply (cancel_mono (ι.app k)).mp
    simp only [Category.assoc, hgk]
    have h1 : (cZ.whisker (Over.forget j)).π.app k ≫ α'.app k = m ≫ cY.π.app k.left := hm k.left
    have h2 : E.hom ≫ m = (cY.π.app j ⁻¹ᵁ V).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have h3 : E.hom ≫ m ≫ cY.π.app k.left = (cY.π.app j ⁻¹ᵁ V).ι ≫ cY.π.app k.left := by
      rw [reassoc_of% h2]
    have h4 : (opensCone DY cY j V).π.app k ≫ ι.app k =
        (cY.π.app j ⁻¹ᵁ V).ι ≫ cY.π.app k.left := Scheme.Hom.resLE_comp_ι _ _
    rw [h1]
    exact h3.trans h4.symm
  obtain ⟨k, hk⟩ := core (J := Over j) (Over.forget j ⋙ B) (Over.forget j ⋙ DZ)
    (Over.forget j ⋙ DY) O (B.obj i0) (DZ.obj i0) (DY.obj i0)
    (Functor.whiskerLeft (Over.forget j) pZ) (Functor.whiskerLeft (Over.forget j) pY)
    α' ι g
    (NatTrans.ext (funext fun k => hgk k))
    (NatTrans.ext (funext fun k => by simpa [α'] using congr_app hα k.left))
    (toConst B e0) (toConst DZ e0) (toConst DY e0) (pZ.app i0) (pY.app i0) (α.app i0)
    (by simpa using congr_app hα i0)
    (fun k => by simp [toConst, α', α.naturality])
    (fun k => hZpb _) (fun k => hYpb _)
    (opensCone DY cY j V) (isLimitOpensCone DY cY hcY j V)
    (cZ.whisker (Over.forget j)) ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) cZ).symm hcZ)
    E hE (cZ.π.app i0) (fun k => by simp [toConst])
  refine ⟨k.left, k.hom, ?_⟩
  show IsOpenImmersion (α'.app k)
  rw [← hgk k]
  infer_instance
end

section

open CategoryTheory Limits AlgebraicGeometry

private theorem exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom {I : Type} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{0})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c) (i0 : I)
    (W : c.pt.Opens) (hW : IsCompact (W : Set c.pt)) :
    ∃ (j : I) (_ : j ⟶ i0) (V : (D.obj j).Opens), IsCompact (V : Set (D.obj j)) ∧
      c.π.app j ⁻¹ᵁ V = W := by
  obtain ⟨Us, hsub, hfin, rfl⟩ :=
    (isBasis_preimage_isAffineOpen D c hc).exists_finite_of_isCompact hW
  clear hW
  induction Us, hfin using Set.Finite.induction_on with
  | empty => exact ⟨i0, 𝟙 i0, ⊥, by simp, by simp⟩
  | @insert U s hUs hs ih =>
    obtain ⟨i, V, hV, rfl⟩ := hsub (Set.mem_insert _ _)
    obtain ⟨j, fj, V', hV', e⟩ := ih (fun x hx => hsub (Set.mem_insert_of_mem _ hx))
    refine ⟨IsCofiltered.min i j, IsCofiltered.minToRight i j ≫ fj,
      D.map (IsCofiltered.minToLeft i j) ⁻¹ᵁ V ⊔ D.map (IsCofiltered.minToRight i j) ⁻¹ᵁ V', ?_, ?_⟩
    · rw [TopologicalSpace.Opens.coe_sup]
      exact (QuasiCompact.isCompact_preimage _ V.2 hV.isCompact).union
        (QuasiCompact.isCompact_preimage _ V'.2 hV')
    · rw [sSup_insert, ← e, Scheme.Hom.preimage_sup, ← Scheme.Hom.comp_preimage,
        ← Scheme.Hom.comp_preimage, c.w, c.w]

theorem UpperTheory.limit_of_cofiltered_affine_base_change_squares :
    ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (B DZ DY : I ⥤ Scheme.{0})
        [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
        (α : DZ ⟶ DY) (pZ : DZ ⟶ B) (pY : DY ⟶ B), α ≫ pY = pZ →
        (∀ {i j : I} (f : i ⟶ j), IsPullback (DZ.map f) (pZ.app i) (pZ.app j) (B.map f)) →
        (∀ {i j : I} (f : i ⟶ j), IsPullback (DY.map f) (pY.app i) (pY.app j) (B.map f)) →
        ∀ (cZ : Cone DZ) (_ : IsLimit cZ) (cY : Cone DY) (_ : IsLimit cY),
        (∀ i, CompactSpace (DZ.obj i)) → (∀ i, QuasiSeparatedSpace (DZ.obj i)) →
        (∀ i, CompactSpace (DY.obj i)) → (∀ i, QuasiSeparatedSpace (DY.obj i)) →
        ∀ (i0 : I) (m : cZ.pt ⟶ cY.pt) [IsOpenImmersion m], (∀ i, cZ.π.app i ≫ α.app i = m ≫ cY.π.app i) →
        ∃ (j : I) (_ : j ⟶ i0) (V : (DY.obj j).Opens), IsCompact (V : Set (DY.obj j)) ∧
          α.app j ⁻¹ᵁ V = ⊤ ∧ cY.π.app j ⁻¹ᵁ V = m.opensRange := by
  intro I _ _ B DZ DY _ α pZ pY hα hZ hY cZ hcZ cY hcY hZc _ hYc _ i0 m _ hm
  have hZa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (DZ.map f) := fun f =>
    MorphismProperty.of_isPullback (P := @IsAffineHom) (hZ f).flip inferInstance
  have hYa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (DY.map f) := fun f =>
    MorphismProperty.of_isPullback (P := @IsAffineHom) (hY f).flip inferInstance
  haveI := Scheme.compactSpace_of_isLimit DZ cZ hcZ
  have hW : IsCompact (m.opensRange : Set cY.pt) := by
    rw [Scheme.Hom.coe_opensRange]
    exact isCompact_range m.continuous
  obtain ⟨j, fj, V, hV, e⟩ := exists_isCompact_preimage_eq_of_isLimit_of_isAffineHom DY cY hcY i0 m.opensRange hW
  have htop : cZ.π.app j ⁻¹ᵁ (α.app j ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hm, Scheme.Hom.comp_preimage, e]
    exact Scheme.Hom.preimage_opensRange m
  obtain ⟨k, fkj, hk⟩ := exists_map_eq_top DZ cZ hcZ (α.app j ⁻¹ᵁ V) htop
  refine ⟨k, fkj ≫ fj, DY.map fkj ⁻¹ᵁ V, QuasiCompact.isCompact_preimage _ V.2 hV, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_preimage, ← α.naturality, Scheme.Hom.comp_preimage, hk]
  · rw [← Scheme.Hom.comp_preimage, cY.w, e]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.isOpenImmersion_of_closedImmersion_flat_etale :
    ∀ {V X T : Scheme.{0}} (v : V ⟶ X) (p : X ⟶ T), Etale p → IsClosedImmersion v → Flat (v ≫ p) → LocallyOfFinitePresentation (v ≫ p) → IsOpenImmersion v := by
  intro V X T v p hp hv hf hl
  have hv' : FormallyUnramified v := inferInstance
  have hu : FormallyUnramified (v ≫ p) :=
    MorphismProperty.comp_mem @FormallyUnramified v p hv' inferInstance
  have he : Etale (v ≫ p) := Etale.of_formallyUnramified_of_flat (v ≫ p)
  have hev : Etale v := Etale.of_comp v p
  exact IsOpenImmersion.of_flat_of_mono v
end
