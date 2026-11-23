module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.SpreadingOut
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.TwoTorsionPointsSpreading

set_option backward.isDefEq.respectTransparency false

theorem exists_open_injective {S : Scheme.{0}} {X G : Over S} [IsIntegral X.left] [IsSeparated G.hom] {m : ℕ}
    (s : Fin m → (X ⟶ G)) (hs : Function.Injective s) :
    ∃ W : X.left.Opens, (W : Set X.left).Nonempty ∧ ∀ (T : Over S) [Nonempty T.left] (y : T ⟶ X),
      ⊤ ≤ y.left ⁻¹ᵁ W → Function.Injective fun i => y ≫ s i := by
  classical
  let C : Fin m → Fin m → Set X.left := fun i j =>
    closure (Set.range (equalizer.ι (s i) (s j)).left)
  have hopen : IsOpen (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ) :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isClosed_closure.isOpen_compl
  refine ⟨⟨_, hopen⟩, ?_, ?_⟩
  · refine ⟨genericPoint X.left, ?_⟩
    show genericPoint X.left ∈ (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ : Set X.left)
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    intro i j hij hmem
    apply hij
    apply hs
    have hg : closure ({genericPoint X.left} : Set X.left) = Set.univ := genericPoint_spec X.left
    have huniv : C i j = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← hg]
      exact closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
    have : IsDominant (equalizer.ι (s i) (s j)).left := ⟨by
      rw [DenseRange, dense_iff_closure_eq]; exact huniv⟩
    ext1
    exact ext_of_isDominant_of_isSeparated G.hom (by simp) (equalizer.ι (s i) (s j)).left
      (by rw [← Over.comp_left, equalizer.condition, Over.comp_left])
  · intro T _ y hy i j hij
    by_contra hne
    obtain ⟨t⟩ := ‹Nonempty T.left›
    have ht : y.left t ∈ (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (C i j)ᶜ : Set X.left) := hy (Set.mem_univ t)
    simp only [Set.mem_iInter, Set.mem_compl_iff] at ht
    apply ht i j hne
    apply subset_closure
    refine ⟨(equalizer.lift y hij).left t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]

theorem exists_spread {Z S Y : Scheme.{0}} [IsIntegral Z] (c : Z ⟶ S) (G : Over S) [LocallyOfFiniteType G.hom]
    (j : Y ⟶ Z) (hj : GlobalTheory.IsGenericPointHom j) {m : ℕ} (P : Fin m → (Over.mk (j ≫ c) ⟶ G)) :
    ∃ (U : Z.Opens) (_ : genericPoint Z ∈ U) (k : Over.mk (j ≫ c) ⟶ Over.mk (U.ι ≫ c)) (_ : IsDominant k.left)
      (s : Fin m → (Over.mk (U.ι ≫ c) ⟶ G)), ∀ i, k ≫ s i = P i := by
  classical
  have hr := GlobalTheory.IsGenericPointHom.range_eq hj
  obtain ⟨e, he⟩ := hj
  have hφ : ∀ i, (e.inv ≫ (P i).left) ≫ G.hom = Z.fromSpecStalk (genericPoint Z) ≫ c := by
    intro i
    rw [Category.assoc, Over.w (P i)]
    simp [← he]
  choose U hU f hf₁ hf₂ using fun i =>
    spread_out_of_isGermInjective' c G.hom (e.inv ≫ (P i).left) (hφ i)
  have hopen : IsOpen (⋂ i, (U i : Set Z)) := isOpen_iInter_of_finite fun i => (U i).isOpen
  let V : Z.Opens := ⟨_, hopen⟩
  have hηV : genericPoint Z ∈ V := Set.mem_iInter.mpr hU
  have hle : ∀ i, V ≤ U i := fun i => Set.iInter_subset _ i
  have hres : ∀ i, V.fromSpecStalkOfMem _ hηV ≫ Z.homOfLE (hle i) =
      (U i).fromSpecStalkOfMem _ (hU i) := by
    intro i
    rw [← cancel_mono (U i).ι]
    simp [Scheme.Opens.fromSpecStalkOfMem_ι]
  refine ⟨V, hηV, Over.homMk (e.hom ≫ V.fromSpecStalkOfMem _ hηV) ?_, ?_,
    fun i => Over.homMk (Z.homOfLE (hle i) ≫ f i) ?_, ?_⟩
  · simp [Scheme.Opens.fromSpecStalkOfMem_ι_assoc, ← he]
  · show IsDominant (e.hom ≫ V.fromSpecStalkOfMem _ hηV)
    rw [isDominant_iff, DenseRange, dense_iff_inter_open]
    rintro W hW ⟨w, hw⟩
    have h1 : IsOpen (V.ι '' W) := V.ι.isOpenEmbedding.isOpenMap _ hW
    obtain ⟨v, hvW, hv⟩ :=
      ((genericPoint_spec Z).mem_open_set_iff h1).mpr ⟨_, trivial, w, hw, rfl⟩
    have hη : genericPoint Z ∈ Set.range j := by rw [hr]; rfl
    obtain ⟨y, hy⟩ := hη
    refine ⟨v, hvW, y, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, he, hy, hv]
  · rw [Category.assoc, hf₂, Scheme.homOfLE_ι_assoc]
    rfl
  · intro i
    ext1
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]
    rw [reassoc_of% (hres i), ← hf₁, Iso.hom_inv_id_assoc]

end PositivityTheory.Xgn.TwoTorsionPointsSpreading

set_option backward.isDefEq.respectTransparency false in
theorem PositivityTheory.Xgn.two_torsion_points_spread_open : ∀ (Z' S : Scheme.{0}) [IsIntegral Z'] (c : Z' ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ (m : ℕ) (P : Fin m → (Over.mk (j ≫ c) ⟶ G)), Function.Injective P → (∀ i, P i ^ 2 = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ x ⁻¹ᵁ V → ∃ Q : Fin m → (Over.mk (x ≫ c) ⟶ G), Function.Injective Q ∧ ∀ i, Q i ^ 2 = 1 := by
  intro Z' S _ c G _ _ _ L' _ j hj m P hP hP2
  obtain ⟨U, hηU, k, hk, s, hs⟩ :=
    PositivityTheory.Xgn.TwoTorsionPointsSpreading.exists_spread c G j hj P
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI : IsIntegral (Over.mk (U.ι ≫ c)).left := inferInstanceAs (IsIntegral U.toScheme)
  haveI : IsReduced (Over.mk (U.ι ≫ c)).left := inferInstanceAs (IsReduced U.toScheme)
  have hsinj : Function.Injective s := fun a b hab => hP (by rw [← hs a, ← hs b, hab])
  have hs2 : ∀ i, s i ^ 2 = 1 := by
    intro i
    have h1 : k ≫ s i ^ 2 = k ≫ 1 := by
      rw [pow_two, MonObj.comp_mul, ← pow_two, hs i, hP2 i]
      simp
    ext1
    exact ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w, Over.w]) k.left
      (by rw [← Over.comp_left, h1, Over.comp_left])
  obtain ⟨W, hWne, hW⟩ :=
    PositivityTheory.Xgn.TwoTorsionPointsSpreading.exists_open_injective (X := Over.mk (U.ι ≫ c)) s hsinj
  obtain ⟨w, hw⟩ := hWne
  refine ⟨U.ι ''ᵁ W, ⟨U.ι w, w, hw, rfl⟩, ?_⟩
  intro K _ x hx
  have hxW : ∀ t, ∃ w ∈ W, U.ι w = x t := by
    intro t
    obtain ⟨w, hw, hwt⟩ := hx (Set.mem_univ t)
    exact ⟨w, hw, hwt⟩
  let x' := IsOpenImmersion.lift U.ι x (by
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, -, h⟩ := hxW t
    exact ⟨w, h⟩)
  let y : Over.mk (x ≫ c) ⟶ Over.mk (U.ι ≫ c) := Over.homMk x' (by
    simp only [Over.mk_hom]
    rw [IsOpenImmersion.lift_fac_assoc])
  haveI : Nonempty (Over.mk (x ≫ c)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  refine ⟨fun i => y ≫ s i, hW (Over.mk (x ≫ c)) y ?_, fun i => ?_⟩
  · intro t _
    show x' t ∈ W
    obtain ⟨w, hw, hwt⟩ := hxW t
    have : x' t = w := U.ι.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac, hwt])
    rw [this]
    exact hw
  · show (y ≫ s i) ^ 2 = 1
    rw [pow_two, ← MonObj.comp_mul, ← pow_two, hs2 i]
    simp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.SplitTorusExtension

theorem one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    change ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have h₁ : (e * e).left = e.left := by
    rw [h.2 T 1 1 e e rfl rfl, _root_.mul_one]
    rfl
  have h₂ : e * e = e := Over.OverMorphism.ext h₁
  have h₃ : e = 1 := by simpa using h₂
  rw [← h₃]
  rfl

theorem eq_one {S S' : Scheme.{0}} {G' H' : Over S'} [GrpObj G'] [GrpObj H'] {G H : Over S} [GrpObj G] [GrpObj H]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ)
    (hψ : IsGrpPullback H' H f ψ) (i : G' ⟶ H') [IsMonHom i] [Mono i] (u : G ⟶ H)
    (hu : i.left ≫ ψ = φ ≫ u.left) (T : Over S') (t : Over.mk (T.hom ≫ f) ⟶ G) (ht : t ≫ u = 1) : t = 1 := by
  have hw : t.left ≫ G.hom = T.hom ≫ f := Over.w t
  let s : T.left ⟶ G'.left := hφ.1.lift t.left T.hom hw
  have hs : s ≫ φ = t.left := hφ.1.lift_fst _ _ _
  let s' : T ⟶ G' := Over.homMk s (hφ.1.lift_snd _ _ _)
  have h1 : s' ≫ i = 1 := by
    apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · rw [← one_left hψ T, Over.comp_left, Category.assoc, hu, ← Category.assoc]
      change (s ≫ φ) ≫ u.left = _
      rw [hs, ← Over.comp_left, ht]
    · rw [Over.w, Over.w]
  have h2 : s' = 1 := by
    have h3 : (1 : T ⟶ G') ≫ i = 1 := by simp [Hom.one_def]
    rw [← h3] at h1
    exact (cancel_mono i).mp h1
  apply Over.OverMorphism.ext
  rw [one_left hφ T, ← h2]
  exact hs.symm

end PositivityTheory.Xgn.SplitTorusExtension

theorem PositivityTheory.Xgn.exists_split_torus_extension : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 := by
  intro hext Z' _ _ hnorm G _ hG L' _ j hj τ
  letI := τ.addCommGroup
  haveI := τ.free
  haveI := τ.finite
  haveI := τ.i_hom
  haveI : Mono τ.i := τ.isKernel.mono_fst_of_mono
  have hT : IsSemiAbelian (splitTorus Z' τ.X) :=
    ((GlobalTheory.splitTorus_properties Z').1 τ.X).2.2.2.2.2.2.2.2.1
  obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange Z' (Sp L') j τ.X
  haveI := he
  have hφ : IsGrpPullback (splitTorus (Sp L') τ.X) (splitTorus Z' τ.X) j
      (e.hom.left ≫ pullback.fst (splitTorus Z' τ.X).hom j) := by
    have h0 := (isGrpPullback_of_iso e).comp (isGrpPullback_pullback (splitTorus Z' τ.X) j)
    rwa [Category.id_comp] at h0
  have hψ := isGrpPullback_pullback G j
  obtain ⟨F, ⟨hF, hu⟩, -⟩ :=
    GlobalTheory.Published.SemiAbelianHomExtension.generic_of_isGrpPullback hext hnorm hj hT hG hφ hψ τ.i
  refine ⟨F, hF, fun A _ g t ht => ?_⟩
  haveI := hF
  exact SplitTorusExtension.eq_one hφ hψ τ.i F hu (Over.mk (spMap g)) t ht
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Xgn.HodgeCharacterGeneric

open Polynomial GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.HT.LatBasic TensorProduct

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]

theorem sum_emb [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E) (x : E) :
    ∑ s : E →+* K, s x = algebraMap ℚ K (Algebra.trace ℚ E x) := by
  classical
  letI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  let f : (E →+* K) → (E →ₐ[ℚ] AlgebraicClosure K) := fun s =>
    ((algebraMap K (AlgebraicClosure K)).comp s).toRatAlgHom
  have hf : Function.Injective f := by
    intro s t hst
    ext y
    have := congrArg (fun g : E →ₐ[ℚ] AlgebraicClosure K => g y) hst
    exact (algebraMap K (AlgebraicClosure K)).injective this
  have hcard : Fintype.card (E →+* K) = Fintype.card (E →ₐ[ℚ] AlgebraicClosure K) := by
    rw [AlgHom.card, ← h, Nat.card_eq_fintype_card]
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
  apply (algebraMap K (AlgebraicClosure K)).injective

  rw [map_sum]
  calc ∑ s : E →+* K, algebraMap K (AlgebraicClosure K) (s x) = ∑ s, f s x := rfl
    _ = ∑ σ : E →ₐ[ℚ] AlgebraicClosure K, σ x := hb.sum_comp (fun σ => σ x)
    _ = algebraMap ℚ (AlgebraicClosure K) (Algebra.trace ℚ E x) :=
        (trace_eq_sum_embeddings (AlgebraicClosure K) (x := x)).symm
    _ = _ := by simp [eq_ratCast]

variable {V : Type} [AddCommGroup V] [Module K V]

theorem sum_eigProj [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End K V) : ∑ s, eigProj ρ s = 1 := by
  classical
  set b := RingOfIntegers.basis E with hb
  have h1 : (1 : E) = ∑ j, ((b.repr 1 j : ℤ) : E) * integralBasis E j := by
    have := congrArg (algebraMap (𝓞 E) E) (b.sum_repr 1)

    simpa [integralBasis_apply, map_sum, zsmul_eq_mul] using this.symm
  have hrep : ∀ k, Algebra.trace ℚ E (dualInt E k) = ((b.repr 1 k : ℤ) : ℚ) := by
    intro k

    conv_lhs => rw [← mul_one (dualInt E k), h1, Finset.mul_sum, map_sum]
    simp_rw [mul_left_comm (dualInt E _), ← zsmul_eq_mul, map_zsmul, trace_dualInt]
    simp
  simp only [eigProj]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_emb h, hrep]
  calc ∑ k, algebraMap ℚ K ((b.repr 1 k : ℤ) : ℚ) • ρ (b k) = ρ (∑ k, b.repr 1 k • b k) := by

        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, map_intCast, Int.cast_smul_eq_zsmul]
    _ = 1 := by rw [b.sum_repr, map_one]

theorem isInternal [Fintype (E →+* K)] [DecidableEq (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End K V) : DirectSum.IsInternal (HT.eigSp ρ) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro s
    rw [Submodule.disjoint_def]
    intro x hx hy
    have hk : (⨆ j, ⨆ (_ : j ≠ s), HT.eigSp ρ j) ≤ LinearMap.ker (eigProj ρ s) :=
      iSup₂_le fun j hj y hy => eigProj_of_ne hj.symm hy
    rw [← eigProj_of_mem hx]
    exact hk hy
  · rw [eq_top_iff]
    intro x _
    have : x = ∑ s, eigProj ρ s x := by
      rw [← LinearMap.sum_apply, sum_eigProj h]; rfl
    rw [this]
    exact Submodule.sum_mem _ fun s _ => Submodule.mem_iSup_of_mem s (eigProj_mem ρ s x)

theorem charpoly_eq [Fintype (E →+* K)] [FiniteDimensional K V]
    (h : Nat.card (E →+* K) = Module.finrank ℚ E) (ρ : 𝓞 E →+* Module.End K V) :
    (∀ a : 𝓞 E, (ρ a).charpoly =
      ∏ s : E →+* K, (X - Polynomial.C (s (a : E))) ^ Module.finrank K (HT.eigSp ρ s)) ∧
    ∑ s : E →+* K, Module.finrank K (HT.eigSp ρ s) = Module.finrank K V := by
  classical
  let b := (isInternal h ρ).collectedBasis fun s => Module.finBasis K (HT.eigSp ρ s)
  have hb : ∀ i, b i ∈ HT.eigSp ρ i.1 := fun i => (isInternal h ρ).collectedBasis_mem _ i
  refine ⟨fun a => ?_, ?_⟩
  · have hm : LinearMap.toMatrix b b (ρ a) = Matrix.diagonal fun i => i.1 (a : E) := by
      ext i j
      rw [LinearMap.toMatrix_apply, mem_eigSp.1 (hb j) a, map_smul, b.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Finsupp.single_apply, Ne.symm hij]
    rw [← LinearMap.charpoly_toMatrix _ b, hm, Matrix.charpoly_diagonal, Fintype.prod_sigma]
    simp
  · rw [Module.finrank_eq_card_basis b]
    simp

theorem reg_ne (σ : E →+* K) : eigProj (regAct K E) σ 1 ≠ 0 := by
  classical
  intro h0
  have hne : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have := sum_dualInt_mul (E := E)
    simp [Finset.univ_eq_empty] at this
  obtain ⟨k⟩ := hne
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, regAct_basis] at h0
  have hk := Fintype.linearIndependent_iff.mp
    (Algebra.TensorProduct.basis K (RingOfIntegers.basis E)).linearIndependent _ h0 k
  have hd : dualInt E k = 0 := by
    rw [← map_zero σ] at hk
    exact σ.injective hk
  have ht := trace_dualInt (E := E) k k
  simp [hd] at ht

theorem charpoly_lmul [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E) (a : 𝓞 E) :
    (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K) =
      ∏ s : E →+* K, (X - Polynomial.C (s (a : E))) := by
  classical
  have hfr : Module.finrank K (K ⊗[ℤ] 𝓞 E) = Module.finrank ℚ E := by
    rw [Module.finrank_baseChange, RingOfIntegers.rank]
  obtain ⟨hc, hs⟩ := charpoly_eq h (regAct K E)
  have hpos : ∀ s : E →+* K, 1 ≤ Module.finrank K (HT.eigSp (regAct K E) s) := fun s =>
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨_, eigProj_mem _ s 1⟩, fun h0 => reg_ne s (congrArg Subtype.val h0)⟩
  have hone : ∀ s, Module.finrank K (HT.eigSp (regAct K E) s) = 1 := by
    by_contra hn
    push_neg at hn
    obtain ⟨t, ht⟩ := hn
    have hlt : ∑ _s : E →+* K, 1 < ∑ s, Module.finrank K (HT.eigSp (regAct K E) s) :=
      Finset.sum_lt_sum (fun s _ => hpos s)
        ⟨t, Finset.mem_univ _, lt_of_le_of_ne (hpos t) (Ne.symm ht)⟩
    rw [hs, hfr, ← h, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
    simp [Nat.card_eq_fintype_card] at hlt
  have hbc : regAct K E a = (Algebra.lmul ℤ (𝓞 E) a).baseChange K := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext c y
    simp [regAct]
  rw [← algebraMap_int_eq, ← LinearMap.charpoly_baseChange, ← hbc, hc a]
  simp [hone]

theorem charpoly_rhoH {O : Type} [CommRing O] [StarRing O] {d : ℕ} (B : Germ.FB K d O) (a : O) :
    (rhoH B a).charpoly = (rho B a).charpoly * (rho B (star a)).charpoly := by
  classical
  let b := (Pi.basisFun K (Fin d)).prod (Pi.basisFun K (Fin d))
  have hM : LinearMap.toMatrix b b (rhoH B a) =
      Matrix.fromBlocks (rho B a) 0 (-Matrix.transpose (bil (B.ad a) 1 1))
        (Matrix.transpose (rho B (star a))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [b, LinearMap.toMatrix_apply, rhoH, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rw [← LinearMap.charpoly_toMatrix (rhoH B a) b, hM, Matrix.charpoly_fromBlocks_zero₁₂,
    Matrix.charpoly_transpose]

end PositivityTheory.Xgn.HodgeCharacterGeneric

theorem PositivityTheory.Xgn.hodge_character_generic : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [CharZero K] (d r : ℕ) (B : Germ.FB K d (𝓞 E)) (ρ : 𝓞 E →+* Module.End K (Fin d → K)), (∀ a v, ρ a v = (rho B a).mulVec v) → Nat.card (E →+* K) = Module.finrank ℚ E → (∀ s s' : E →+* K, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) → Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ s') = r) → HChar B r := by
  classical
  intro E _ _ _ K _ _ d r B ρ hρ h hdim
  have hinj : ∀ s : E →+* K,
      Function.Injective (s.comp ((algebraMap (𝓞 E) E).comp (starRingEnd (𝓞 E)))) :=
    fun s x y hxy => star_injective (IsFractionRing.injective (𝓞 E) E (s.injective hxy))
  let φ : (E →+* K) → (E →+* K) := fun s => IsFractionRing.lift (hinj s)
  have hφ : ∀ s (x : 𝓞 E), φ s (algebraMap (𝓞 E) E x) = s (algebraMap (𝓞 E) E (star x)) :=
    fun s x => IsFractionRing.lift_algebraMap (hinj s) x
  have hφφ : ∀ s, φ (φ s) = s := fun s =>
    IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => by rw [hφ, hφ, star_star]
  have hbij : Function.Bijective φ := Function.Involutive.bijective hφφ
  have hsum : ∀ s, Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ (φ s)) = r :=
    fun s => hdim s (φ s) fun a => hφ s a
  have hrho : ∀ a, (rho B a).charpoly = (ρ a).charpoly := by
    intro a
    rw [← Matrix.charpoly_toLin']
    congr 1
    exact LinearMap.ext fun v => by rw [Matrix.toLin'_apply, hρ]
  obtain ⟨hc, -⟩ := PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_eq h ρ
  intro a
  rw [PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_rhoH, hrho, hrho, hc, hc,
    PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_lmul h, ← Finset.prod_pow]
  have h2 : ∏ s : E →+* K, (Polynomial.X - Polynomial.C (s ((star a : 𝓞 E) : E))) ^
        Module.finrank K (HT.eigSp ρ s) =
      ∏ s : E →+* K, (Polynomial.X - Polynomial.C (s (a : E))) ^
        Module.finrank K (HT.eigSp ρ (φ s)) := by
    symm
    refine Fintype.prod_bijective φ hbij _ _ fun s => ?_
    have := hφ s (star a)
    rw [star_star] at this
    simp only [this]
  rw [h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← pow_add, hsum s]
end
