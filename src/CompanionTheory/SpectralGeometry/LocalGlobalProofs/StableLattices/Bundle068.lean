module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle050
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle067
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.PointSurjTotal

theorem acyclic_over_affineOpen {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}}
    (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X) (q : Z ⟶ T) (H : IsPullback p q a b)
    (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y →
      FibAc a (G.pull σ))
    {κ : Type} [LinearOrder κ] [Fintype κ] (B : κ → X.Opens) (hB : ∀ i, IsAffineOpen (B i))
    (hc : ⨆ i, B i = ⊤) {V : T.Opens} (hV : IsAffineOpen V) :
    (cechLB (p ≫ a) G fun i => p ⁻¹ᵁ B i ⊓ q ⁻¹ᵁ V).Acyclic := by
  obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := over_affineOpen_of_isPullback a b p q H hV B hB hc G hG
  have h := fibAc_of_closed_fibres a b p q H ha G hG Γ(T, V) hV.fromSpec Y π f Hy
    (fun s σ h₁ h₂ h₃ => hfib (s ≫ hV.fromSpec) σ (by simpa using h₁) h₂ (by simpa using h₃))
    κ E hE hEc
  exact fun m => (GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic f _ _ E h m).of_iso i₁

theorem fibAc_comp_of_fibres : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → FibAc a (G.pull σ)), FibAc (p ≫ a) G := by
  intro k _ _ X T Z a b p q H ha _ _ _ G hG hfib κ _ _ D hD hc n
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have : T.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace b
  obtain ⟨m, B, hB, hBc⟩ := GlobalTheory.PicZeroVan.exists_fin_affine_cover X
  obtain ⟨r, E, hE, hEc⟩ := GlobalTheory.PicZeroVan.exists_fin_affine_cover T
  let V : Fin (r + 1) → T.Opens := Fin.cons ⊥ E
  have hV : ∀ j, IsAffineOpen (V j) := fun j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact isAffineOpen_bot T
    · exact hE j
  have hVc : ⨆ j, V j = ⊤ := by
    rw [← top_le_iff, ← hEc]
    exact iSup_le fun j => le_iSup V j.succ
  have hsep : IsSeparated (p ≫ a) := by
    have : IsSeparated p := MorphismProperty.of_isPullback (P := @IsSeparated) H.flip inferInstance
    infer_instance
  obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ k Z (p ≫ a) G κ D (Fin m) (fun i => p ⁻¹ᵁ B i)
    (Fin (r + 1)) (fun j => q ⁻¹ᵁ V j) hG hsep hD hc
    (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
    (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
    (fun i _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hB i) h)
    (fun j _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hV j) h)
    (fun i j => (over_affineOpen_of_isPullback a b p q H (hV j) B hB hBc G hG).1 i) n
  have e₂ := trunc₂HomologyIsoFstSingleton (0 : Fin (r + 1)) (secCube (p ≫ a) G
    fun u : Fin m ⊕ₗ Fin (r + 1) =>
      Sum.elim (fun i => p ⁻¹ᵁ B i) (fun j => q ⁻¹ᵁ V j) (ofLex u))
    (fun t ht _ => by
      have hVt : IsAffineOpen (⨅ j ∈ t, V j) :=
        IsAffineOpen.biInf _ t.finite_toSet ht fun j _ => hV j
      obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G
        (fun i => p ⁻¹ᵁ B i) (fun j => q ⁻¹ᵁ V j) t _ (preimage_biInf V q t)
      exact fun l => (acyclic_over_affineOpen a b p q H ha G hG hfib B hB hBc hVt l).of_iso i₂) n
  obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G
    (fun i => p ⁻¹ᵁ B i) (fun j => q ⁻¹ᵁ V j) {0} (q ⁻¹ᵁ V 0) (by simp)
  have h₀ := (acyclic_over_affineOpen a b p q H ha G hG hfib B hB hBc (hV 0) n).of_iso i₂
  have z := h₀.isZero_homology.of_iso e₂
  have : Subsingleton _ := ModuleCat.subsingleton_of_isZero z
  have := e₁.toEquiv.subsingleton
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (ModuleCat.isZero_of_subsingleton _)

end GlobalTheory.CompanionTheory.PointSurjTotal
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.fibrewise_acyclicity_base_change : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) [LocallyOfFiniteType (t ≫ b)] (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    (hfib : ∀ (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z), s ≫ t ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X →
      σ ≫ q = a ≫ s ≫ t → FibAc a (G.pull σ)), FibAc f (G.pull π) := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres | exact GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PolSpread

def good {S : Type} [CommRing S] (B : Over (Sp S)) (M : LB B.left) : Set S :=
  {r | Out.RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp S) (PrimeSpectrum.basicOpen r))).obj B)
    (M.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Sp S) (PrimeSpectrum.basicOpen r))))}

theorem exists_good_notMem {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing S] (σ : S →+* R)
    (A : Over (Sp R)) (B : Over (Sp S)) [IsProper B.hom] [Flat B.hom] {M : LB B.left} (hM : M.IsLB)
    {L : LB A.left} (hL : L.IsLB) {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom (spMap σ))
    (e : LBIso L (M.pull φ)) (hA : Out.RelAmple A L) (p : Ideal R) [p.IsPrime] :
    ∃ r ∈ good B M, σ r ∉ p := by
  let p₀ : Ideal S := p.comap σ
  have : p₀.IsPrime := Ideal.IsPrime.comap σ
  let a := algebraMap S p₀.ResidueField
  let b := algebraMap R p.ResidueField
  let i : p₀.ResidueField →+* p.ResidueField := Ideal.ResidueField.map p₀ p σ rfl
  have hw : spMap b ≫ spMap σ = spMap i ≫ spMap a := by
    have : i.comp a = b.comp σ := RingHom.ext fun r => Ideal.ResidueField.map_algebraMap p₀ p σ rfl r
    unfold spMap
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  have hX := (IsPullback.of_hasPullback A.hom (spMap b)).paste_horiz h
  have h₂ : Out.RelAmple (Over.mk (pullback.snd A.hom (spMap b))) (M.pull (pullback.fst A.hom (spMap b) ≫ φ)) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM h hX (spMap b) rfl hL e hA
  rw [hw] at hX
  have h₀ : Out.RelAmple ((Over.pullback (spMap a)).obj B) (M.pull (pullback.fst B.hom (spMap a))) :=
    GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i (IsPullback.of_hasPullback B.hom (spMap a)) hX
      (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) h₂
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hM a
    (GlobalTheory.FibreAmple.residueField_fraction p₀) h₀
  exact ⟨r, hr', fun hp => hr (Ideal.algebraMap_residueField_eq_zero.2 hp)⟩

theorem span_good {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing S] (σ : S →+* R)
    (A : Over (Sp R)) (B : Over (Sp S)) [IsProper B.hom] [Flat B.hom] {M : LB B.left} (hM : M.IsLB)
    {L : LB A.left} (hL : L.IsLB) {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom (spMap σ))
    (e : LBIso L (M.pull φ)) (hA : Out.RelAmple A L) : Ideal.span (σ '' good B M) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have := hm.isPrime
  obtain ⟨r, hr, hr'⟩ := exists_good_notMem σ A B hM hL h e hA m
  exact hr' (hle (Ideal.subset_span ⟨r, hr, rfl⟩))

theorem relAmple_of_span {S S' : Type} [CommRing S] [CommRing S'] (τ : S →+* S') (B : Over (Sp S)) [IsProper B.hom]
    {M : LB B.left} (hM : M.IsLB) (T : Set S) (hT : T ⊆ good B M) (h : Ideal.span (τ '' T) = ⊤) :
    Out.RelAmple (Over.mk (pullback.snd B.hom (spMap τ))) (M.pull (pullback.fst B.hom (spMap τ))) := by
  let f := pullback.snd B.hom (spMap τ)
  have : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  have : IsProper f := inferInstance
  have hB := IsPullback.of_hasPullback B.hom (spMap τ)
  refine GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S') (Over.mk f) _ (pull_isLB hM _) inferInstance inferInstance
    fun s => ?_
  let s' : PrimeSpectrum S' := s
  obtain ⟨r, hr, hs⟩ : ∃ r ∈ T, τ r ∉ s'.asIdeal := by
    by_contra hc
    push_neg at hc
    refine s'.isPrime.ne_top (top_le_iff.1 (h ▸ Ideal.span_le.2 ?_))
    rintro _ ⟨r, hr, rfl⟩
    exact hc r hr
  let U : (Sp S').Opens := PrimeSpectrum.basicOpen (τ r)
  let D : (Sp S).Opens := PrimeSpectrum.basicOpen r
  have hrange : Set.range (U.ι ≫ spMap τ) ⊆ Set.range D.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact x.2
  let u := IsOpenImmersion.lift D.ι (U.ι ≫ spMap τ) hrange
  have hu : u ≫ D.ι = U.ι ≫ spMap τ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, hs, ?_⟩
  have hU := (isPullback_morphismRestrict f U).flip
  have a₁ : Out.RelAmple (Over.mk (f ∣_ U)) (M.pull ((f ⁻¹ᵁ U).ι ≫ pullback.fst B.hom (spMap τ))) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback B.hom D.ι) (hU.paste_horiz hB) u hu
      (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) (hT hr)
  exact GlobalTheory.FibreAmple.relAmple_of_factor (pull_isLB hM _) hU hU (𝟙 _) (Category.id_comp _) (pull_isLB hM _)
    (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _).symm a₁

end GlobalTheory.CompanionTheory.PolSpread
end
end
