module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.NearFibreIso

open GlobalTheory.DenseFibreIso

variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)

def Near (Q : MorphismProperty Scheme.{0}) (x : X) : Prop :=
  ∃ (T T' : Scheme.{0}) (g : T ⟶ X) (g' : T' ⟶ Y) (f' : T' ⟶ T),
    IsPullback f' g' g f ∧ IsOpenImmersion g ∧ x ∈ Set.range g ∧ Q f'

theorem Near.of_pullback {Q : MorphismProperty Scheme.{0}} {T T' : Scheme.{0}} {g : T ⟶ X}
    {g' : T' ⟶ Y} {f' : T' ⟶ T} (H : IsPullback f' g' g f) [IsOpenImmersion g] {y : T}
    (h : Near f' Q y) : Near f Q (g y) := by
  obtain ⟨T₀, T₀', g₀, g₀', f₀, H₀, hg₀, ⟨z, rfl⟩, hQ⟩ := h
  have := hg₀
  refine ⟨T₀, T₀', g₀ ≫ g, g₀' ≫ g', f₀, H₀.paste_vert H, inferInstance, ⟨z, ?_⟩, hQ⟩
  simp

theorem isIso_fibre_of_pullback {S : Scheme.{0}} (t : S ⟶ Sp R)
    [IsIso (pullback.snd f (pullback.fst s t))] {T T' : Scheme.{0}} {g : T ⟶ X} {g' : T' ⟶ Y}
    {f' : T' ⟶ T} (H : IsPullback f' g' g f) :
    IsIso (pullback.snd f' (pullback.fst (g ≫ s) t)) := by
  have H' : IsPullback (pullback.snd f' (pullback.fst (g ≫ s) t))
      (pullback.fst f' (pullback.fst (g ≫ s) t) ≫ g') (pullback.fst (g ≫ s) t ≫ g) f :=
    (IsPullback.of_hasPullback _ _).flip.paste_vert H
  refine DenseFibreIso.isIso_of_fibre s f t H' (pullback.snd _ _) ?_
  rw [Category.assoc, pullback.condition]

variable (K : Type) [Field K] [Algebra R K]

theorem near_isFinite [IsProper f]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) : Near f @IsFinite x := by
  have hsub : (f ⁻¹' {x}).Subsingleton := by
    let k : Sp K := IsLocalRing.closedPoint K
    have hk : s x = spMap (algebraMap R K) k := by
      apply PrimeSpectrum.ext
      rw [← hx, RingHom.ker_eq_comap_bot, ← Ideal.eq_bot_of_prime k.asIdeal]
      rfl
    obtain ⟨x', hx', -⟩ := Scheme.Pullback.exists_preimage_pullback x k hk
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨z₁, hz₁, hz₁'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := pullback.fst s (spMap (algebraMap R K))) y₁ x' (hy₁.trans hx'.symm)
    obtain ⟨z₂, hz₂, hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := pullback.fst s (spMap (algebraMap R K))) y₂ x' (hy₂.trans hx'.symm)
    have hz : z₁ = z₂ :=
      (pullback.snd f (pullback.fst s (spMap (algebraMap R K)))).isOpenEmbedding.injective
        (hz₁'.trans hz₂'.symm)
    rw [← hz₁, ← hz₂, hz]
  obtain ⟨V, hxV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hsub.finite
  refine ⟨V, f ⁻¹ᵁ V, V.ι, (f ⁻¹ᵁ V).ι, f ∣_ V, isPullback_morphismRestrict f V, inferInstance, ?_, hV⟩
  simpa using hxV

theorem near_isClosedImmersion [hfin : IsFinite f]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f @IsClosedImmersion x := by
  refine DenseFibreIso.local_of_ring s f @IsClosedImmersion K ?_ x hx
  intro A B _ _ _ _ _ _ j j' _ H _ hbij m
  have hf : IsFinite (spMap (algebraMap A B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) H.flip hfin
  have : Module.Finite A B := RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hf)
  obtain ⟨a, ha, hsurj⟩ := DenseFibreIso.exists_away_surjective (A ⊗[R] K) hbij.2 m
  exact ⟨a, ha, IsClosedImmersion.spec_of_surjective _ hsurj⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem near_isIso [hcl : IsClosedImmersion f] [IsLocallyNoetherian X] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  refine DenseFibreIso.local_of_ring s f (MorphismProperty.isomorphisms _) K ?_ x hx
  intro A B _ _ _ _ _ _ j j' hj H hjs hbij m
  have : IsOpenImmersion j' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hj
  have hci : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h1 := (spMap (algebraMap A B)).app_surjective ⊤ (isAffineOpen_top _)
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    intro b
    obtain ⟨c, hc⟩ := h1 ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom c, ?_⟩
    have h3 := congr_arg (fun k => (ConcreteCategory.hom k) c) h2
    simp only [CategoryTheory.comp_apply, CommRingCat.hom_ofHom] at h3
    rw [← h3]
    change (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((spMap (algebraMap A B)).app ⊤ c) = b
    rw [hc]
    simp
  have : IsLocallyNoetherian (Sp A) := isLocallyNoetherian_of_isOpenImmersion j
  have : IsNoetherian (Sp A) := {}
  have : IsNoetherianRing A := isNoetherian_Spec.mp this
  have hflat : Flat (spMap (algebraMap R B)) := by
    have e : spMap (algebraMap R B) = spMap (algebraMap A B) ≫ spMap (algebraMap R A) := by
      change Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rw [e, ← hjs, reassoc_of% H.w]
    infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflat)
  obtain ⟨a, ha, hb⟩ := DenseFibreIso.exists_away_bijective R K hs hbij.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.mpr hb⟩

theorem near_isIso_of_isProper [IsProper f] [IsLocallyNoetherian X] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  obtain ⟨T, T', g, g', f', H, hg, ⟨y, rfl⟩, hQ⟩ := near_isFinite s f K x hx
  have := hg
  have : IsFinite f' := hQ
  have : IsIso (pullback.snd f' (pullback.fst (g ≫ s) (spMap (algebraMap R K)))) :=
    isIso_fibre_of_pullback s f _ H
  have hy : RingHom.ker (algebraMap R K) = ((g ≫ s) y).asIdeal := by simpa using hx
  obtain ⟨T₂, T₂', g₂, g₂', f₂, H₂, hg₂, ⟨y₂, rfl⟩, hQ₂⟩ := near_isClosedImmersion (g ≫ s) f' K y hy
  have := hg₂
  have : IsClosedImmersion f₂ := hQ₂
  have : IsIso (pullback.snd f₂ (pullback.fst (g₂ ≫ g ≫ s) (spMap (algebraMap R K)))) :=
    isIso_fibre_of_pullback (g ≫ s) f' _ H₂
  have : IsLocallyNoetherian T₂ := isLocallyNoetherian_of_isOpenImmersion (g₂ ≫ g)
  have : IsOpenImmersion g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hg
  have : IsOpenImmersion g₂' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H₂ hg₂
  have : Flat (f₂ ≫ g₂ ≫ g ≫ s) := by
    rw [reassoc_of% H₂.w, reassoc_of% H.w]
    infer_instance
  have hy₂ : RingHom.ker (algebraMap R K) = ((g₂ ≫ g ≫ s) y₂).asIdeal := by simpa using hy
  exact Near.of_pullback f H (Near.of_pullback f' H₂ (near_isIso (g₂ ≫ g ≫ s) f₂ K y₂ hy₂))

theorem isOpen_near (Q : MorphismProperty Scheme.{0}) : IsOpen {x : X | Near f Q x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨T, T', g, g', f', H, hg, hx, hQ⟩
  have := hg
  exact ⟨Set.range g, fun z hz => ⟨T, T', g, g', f', H, hg, hz, hQ⟩, g.isOpenEmbedding.isOpen_range, hx⟩

theorem isIso_of_near {S : Scheme.{0}} (t : S ⟶ X)
    (h : ∀ y : S, Near f (MorphismProperty.isomorphisms _) (t y)) : IsIso (pullback.snd f t) := by
  choose T T' g g' f' H hg hx hQ using h
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun y => t ⁻¹ᵁ (g y).opensRange) ?_ fun y => ?_
  · refine eq_top_iff.mpr fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, ?_⟩
    simpa using hx z
  · have := hg y
    have : IsIso (f' y) := hQ y
    have hle : Set.range (Scheme.Opens.ι (t ⁻¹ᵁ (g y).opensRange) ≫ t) ⊆ Set.range (g y) := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    have hu := IsOpenImmersion.lift_fac (g y) _ hle
    have big := (isPullback_morphismRestrict (pullback.snd f t) (t ⁻¹ᵁ (g y).opensRange)).paste_vert
      (IsPullback.of_hasPullback f t).flip
    rw [← hu] at big
    rw [MorphismProperty.isomorphisms.iff]
    exact (big.of_bot' (H y)).isIso_fst_of_isIso

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y X : Scheme.{0}) (s : X ⟶ Sp R) (φ : Y ⟶ X) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → IsProper φ → Flat (φ ≫ s) → IsIso (pullback.snd φ (pullback.fst s (spMap x))) → ∃ f : R, x f ≠ 0 ∧ IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R (Localization.Away f))))) := by
  intro R _ _ Y X s φ K _ x hs _ hφ hflat hiso
  let : Algebra R K := x.toAlgebra
  have : IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R K)))) := hiso
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hU : IsOpen {z : X | Near φ (MorphismProperty.isomorphisms _) z} := isOpen_near φ _
  have hZ : IsClosed (s '' {z : X | Near φ (MorphismProperty.isomorphisms _) z}ᶜ) :=
    s.isClosedMap _ hU.isClosed_compl
  let p : PrimeSpectrum R := ⟨RingHom.ker x, RingHom.ker_isPrime x⟩
  have hp : p ∉ s '' {z : X | Near φ (MorphismProperty.isomorphisms _) z}ᶜ := by
    rintro ⟨z, hz, hsz⟩
    refine hz (near_isIso_of_isProper s φ K z ?_)
    rw [hsz]
    rfl
  obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hZ.isOpen_compl
  refine ⟨f, fun h0 => (PrimeSpectrum.mem_basicOpen _ _).mp hpf (RingHom.mem_ker.mpr h0), ?_⟩
  refine isIso_of_near φ _ fun y => ?_
  by_contra hy
  have hmem : s (pullback.fst s (spMap (algebraMap R (Localization.Away f))) y) ∈
      PrimeSpectrum.basicOpen f := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    refine (PrimeSpectrum.mem_basicOpen _ _).mpr fun hf => ?_
    have hf' : algebraMap R (Localization.Away f) f ∈
        (pullback.snd s (spMap (algebraMap R (Localization.Away f))) y).asIdeal := hf
    exact (pullback.snd s (spMap (algebraMap R (Localization.Away f))) y).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hf' (IsLocalization.Away.algebraMap_isUnit f))
  exact hsub hmem ⟨_, hy, rfl⟩

end GlobalTheory.NearFibreIso
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.FinAffineCharts

variable {X : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)ˣ) :
    res h₂ (res h₁ s) = res (h₂.trans h₁) s := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem cocycle_on {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have := congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k))
    (hL.cocycle i j k)
  rwa [map_mul, res_res, res_res, res_res] at this

noncomputable def refineLB (L : LB X) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LB X :=
  ⟨κ, W, fun a b => res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))⟩

theorem refineLB_isLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) (hc : ⨆ a, W a = ⊤) : (refineLB L W c h).IsLB := {
  cover := hc
  g_self a := by
    have := congrArg (res (h a)) (hL.g_self (c a))
    rw [res_res, map_one] at this
    exact (res_res _ _ _).trans this
  cocycle a b d :=
    (congrArg₂ (· * ·) (res_res _ _ _) (res_res _ _ _)).trans
      ((cocycle_on hL _ _ _ _ _ _).trans (res_res _ _ _).symm) }

theorem iso_refineLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LBIso L (refineLB L W c h) := by
  refine ⟨⟨fun p => res (inf_le_inf_right _ (h p.1) : W p.1 ⊓ L.U p.2 ≤ L.U (c p.1) ⊓ L.U p.2)
    (L.g (c p.1) p.2)⟩, ?_⟩
  have key : ∀ (a b : κ) (i j : L.ι),
      res (inf_le_left : W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W a ⊓ L.U i)
        (res (inf_le_inf_right _ (h a) : W a ⊓ L.U i ≤ L.U (c a) ⊓ L.U i) (L.g (c a) i)) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W a ⊓ W b)
        (res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ L.U i ⊓ L.U j) (L.g i j))⁻¹ *
      res (inf_le_right : W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W b ⊓ L.U j)
        (res (inf_le_inf_right _ (h b) : W b ⊓ L.U j ≤ L.U (c b) ⊓ L.U j) (L.g (c b) j)) := by
    intro a b i j
    rw [res_res, res_res, res_res, mul_right_comm, cocycle_on hL (c a) (c b) j _ _
      (le_inf (inf_le_left.trans (inf_le_left.trans (h a))) (inf_le_right.trans inf_le_right)),
      eq_mul_inv_iff_mul_eq]
    exact cocycle_on hL _ _ _ _ _ _
  exact fun p q => key p.1 q.1 p.2 q.2

theorem exists_finite_affine_cover [CompactSpace X] (M : LB X) (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → X.Opens) (c : κ → M.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (c a)) ∧ ⨆ a, W a = ⊤ := by
  have h : ∀ x : X, ∃ (W : X.Opens) (c : M.ι), IsAffineOpen W ∧ x ∈ W ∧ W ≤ M.U c := by
    intro x
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hM.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hc (M.U c).isOpen
    exact ⟨W, c, hW, hx, hle⟩
  choose W c hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun a => W a, fun a => c a, fun a => hW a, fun a => hle a,
    top_le_iff.1 ?_⟩
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem exists_finite_affine_charts : ∀ (X : Scheme.{0}) (L : LB X), CompactSpace X → L.IsLB → ∃ L' : LB X, Finite L'.ι ∧ L'.IsLB ∧ (∀ i, IsAffineOpen (L'.U i)) ∧ LBIso L L' := by
  intro X L _ hL
  obtain ⟨κ, hκ, W, c, hW, h, hc⟩ := exists_finite_affine_cover L hL
  exact ⟨refineLB L W c h, hκ, refineLB_isLB hL W c h hc, hW, iso_refineLB hL W c h⟩

end GlobalTheory.FinAffineCharts
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverOpCompat

section
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

private lemma isGrpPullback_one_left (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (ρ : T ⟶ S') :
    (1 : Over.mk (ρ ≫ f) ⟶ G).left = (1 : Over.mk ρ ⟶ G').left ≫ φ := by

  have hw : ((1 : Over.mk ρ ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (ρ ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let u : Over.mk (ρ ≫ f) ⟶ G := Over.homMk _ hw
  have huu : (u * u).left = ((1 : Over.mk ρ ⟶ G') * 1).left ≫ φ := h.2 (Over.mk ρ) 1 1 u u rfl rfl
  rw [_root_.mul_one] at huu
  have hsq : u * u = u := Over.OverMorphism.ext huu
  have hu : u = 1 := by
    calc u = u * u * u⁻¹ := (_root_.mul_inv_cancel_right u u).symm
      _ = 1 := by rw [hsq, _root_.mul_inv_cancel]
  rw [← hu]
  rfl

theorem push_mul (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p q : Over.mk ρ ⟶ G') (x y : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) (hy : y.left = q.left ≫ φ) :
    (x * y).left = (p * q).left ≫ φ := by
  subst e
  exact h.2 (Over.mk ρ) p q x y hx hy

theorem push_inv (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p : Over.mk ρ ⟶ G') (x : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) :
    (x⁻¹).left = (p⁻¹).left ≫ φ := by
  subst e

  have hw : ((p⁻¹).left ≫ φ) ≫ G.hom = (Over.mk (ρ ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let z : Over.mk (ρ ≫ f) ⟶ G := Over.homMk _ hw
  have hxz : (x * z).left = (p * p⁻¹).left ≫ φ := push_mul h rfl p p⁻¹ x z hx rfl
  rw [_root_.mul_inv_cancel, ← isGrpPullback_one_left h ρ] at hxz
  have hxz' : x * z = 1 := Over.OverMorphism.ext hxz
  have hz : x⁻¹ = z := (_root_.eq_inv_of_mul_eq_one_right hxz').symm
  rw [hz]
  rfl

theorem push_one (h : IsGrpPullback G' G f φ) :
    f ≫ (1 : Out.baseOver S ⟶ G).left = (1 : Out.baseOver S' ⟶ G').left ≫ φ := by

  let c : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
    Over.homMk f (by simp [Out.baseOver])
  have hc : c ≫ (1 : Out.baseOver S ⟶ G) = 1 := MonObj.comp_one c
  have hl : f ≫ (1 : Out.baseOver S ⟶ G).left = (1 : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ G).left := by
    rw [← hc]
    rfl
  rw [hl]
  exact isGrpPullback_one_left h (Out.baseOver S').hom

end

theorem opCompat : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (B : ∀ i j, Over (U i ⊓ U j).toScheme) [∀ i j, GrpObj (B i j)] (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j, IsGrpPullback (B i j) (G i) (S.homOfLE inf_le_left) (a i j)) → (∀ i j, IsGrpPullback (B i j) (G j) (S.homOfLE inf_le_right) (b i j)) → (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (x * y).left ≫ ψ i = (x' * y').left ≫ ψ j ∧ (x⁻¹).left ≫ ψ i = (x'⁻¹).left ≫ ψ j) ∧ ∀ i j, S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (1 : Out.baseOver (U j).toScheme ⟶ G j).left ≫ ψ j := by
  intro S I U A G _ ψ B _ a b _ ha hb hsq
  refine ⟨fun i j T r r' x y x' y' hx hy => ?_, fun i j => ?_⟩
  ·
    let p : T ⟶ (B i j).left := (hsq i j).lift x.left x'.left hx
    let q : T ⟶ (B i j).left := (hsq i j).lift y.left y'.left hy
    have hpa : p ≫ a i j = x.left := (hsq i j).lift_fst _ _ _
    have hpb : p ≫ b i j = x'.left := (hsq i j).lift_snd _ _ _
    have hqa : q ≫ a i j = y.left := (hsq i j).lift_fst _ _ _
    have hqb : q ≫ b i j = y'.left := (hsq i j).lift_snd _ _ _
    let ρ : T ⟶ (U i ⊓ U j).toScheme := p ≫ (B i j).hom
    have er : r = ρ ≫ S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) := by
      show r = (p ≫ (B i j).hom) ≫ _
      rw [Category.assoc, ← (ha i j).1.w, ← Category.assoc, hpa]
      exact (Over.w x).symm
    have er' : r' = ρ ≫ S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) := by
      show r' = (p ≫ (B i j).hom) ≫ _
      rw [Category.assoc, ← (hb i j).1.w, ← Category.assoc, hpb]
      exact (Over.w x').symm
    have eq : q ≫ (B i j).hom = ρ := by
      apply (cancel_mono (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).1
      rw [Category.assoc, ← (ha i j).1.w, ← Category.assoc, hqa]
      exact (Over.w y).trans er
    let P : Over.mk ρ ⟶ B i j := Over.homMk p rfl
    let Q : Over.mk ρ ⟶ B i j := Over.homMk q eq
    have m1 := push_mul (ha i j) er P Q x y hpa.symm hqa.symm
    have m2 := push_mul (hb i j) er' P Q x' y' hpb.symm hqb.symm
    have i1 := push_inv (ha i j) er P x hpa.symm
    have i2 := push_inv (hb i j) er' P x' hpb.symm
    refine ⟨?_, ?_⟩
    · rw [m1, m2]
      simp only [Category.assoc]
      rw [(hsq i j).w]
    · rw [i1, i2]
      simp only [Category.assoc]
      rw [(hsq i j).w]
  ·
    have e1 := congrArg (· ≫ ψ i) (push_one (ha i j))
    have e2 := congrArg (· ≫ ψ j) (push_one (hb i j))
    simp only [Category.assoc] at e1 e2
    rw [e1, e2, (hsq i j).w]

end GlobalTheory.CoverOpCompat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_square_of_isGrpPullback {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S)
    [GrpObj G] (f : S' ⟶ S) (m : G'.left ⟶ G.left) (h : IsGrpPullback G' G f m) :
    ∃ m₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare m m₂ ∧
      m₂ ≫ (fst G G * snd G G).left = (fst G' G' * snd G' G').left ≫ m ∧
      m₂ ≫ (G ⊗ G).hom = (G' ⊗ G').hom ≫ f := by
  have hw : m ≫ G.hom = G'.hom ≫ f := h.1.w
  let a : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((fst G' G').left ≫ m) (by
    simp only [Category.assoc, hw, Over.mk_hom]
    rw [← Category.assoc, Over.w])
  let b : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((snd G' G').left ≫ m) (by
    simp only [Category.assoc, hw, Over.mk_hom]
    rw [← Category.assoc, Over.w])
  refine ⟨(lift a b).left, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact congrArg Over.Hom.left (lift_fst a b)
  · exact congrArg Over.Hom.left (lift_snd a b)
  · rw [← h.2 (G' ⊗ G') (fst G' G') (snd G' G') a b rfl rfl]
    have : lift a b ≫ (fst G G * snd G G) = a * b := by
      rw [MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left this
  · exact Over.w (lift a b)

theorem square_fibre_affine_opens : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap x₀) m → (∃ m₂ : (P₀.A ⊗ P₀.A).left ⟶ (P.A ⊗ P.A).left, IsSquare m m₂ ∧ m₂ ≫ (fst P.A P.A * snd P.A P.A).left = (fst P₀.A P₀.A * snd P₀.A P₀.A).left ≫ m ∧ m₂ ≫ (P.A ⊗ P.A).hom = (P₀.A ⊗ P₀.A).hom ≫ spMap x₀) ∧ IsSeparated P₀.A.hom ∧ IsPullback (fst P₀.A P₀.A).left (snd P₀.A P₀.A).left P₀.A.hom P₀.A.hom ∧ (∀ W : P.A.left.Opens, IsAffineOpen W → IsAffineOpen (m ⁻¹ᵁ W)) ∧ ∀ W W' : P.A.left.Opens, IsAffineOpen W → IsAffineOpen W' → IsAffineOpen (W ⊓ W') := by
  intro K _ P₀ R _ x₀ P m h
  have hp₀ : IsProper P₀.A.hom := P₀.isAb.proper
  have hp : IsProper P.A.hom := P.isAb.proper
  refine ⟨exists_square_of_isGrpPullback _ _ _ _ h, inferInstance,
    IsPullback.of_hasPullback _ _, fun W hW => ?_, fun W W' hW hW' => ?_⟩
  · have : IsAffineHom m :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) h.1.flip inferInstance
    exact hW.preimage m
  · have : IsSeparated (terminal.from P.A.left) := by
      rw [← terminal.comp_from P.A.hom]; infer_instance
    exact hW.inf hW'

end GlobalTheory.KS
end
