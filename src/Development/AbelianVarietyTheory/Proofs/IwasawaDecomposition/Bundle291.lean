module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle279
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle264
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle281
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

namespace GlobalTheory.RayTopGalois

theorem count_comap {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [DecidableEq (Associates (Ideal R))] [∀ p : Associates (Ideal R), Decidable (Irreducible p)]
    [DecidableEq (Associates (Ideal S))] [∀ p : Associates (Ideal S), Decidable (Irreducible p)]
    (e : R ≃+* S) (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal).count (Associates.mk (I.comap e.symm)).factors =
      (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  have hI' : I.comap e.symm ≠ ⊥ := by
    rw [← Ideal.map_comap_of_equiv]
    exact fun h => hI ((Ideal.map_eq_bot_iff_of_injective e.injective).1 h)
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI') (HeightOneSpectrum.associates_irreducible _),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) (HeightOneSpectrum.associates_irreducible _),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  have : (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = p.asIdeal.map (e : R →+* S) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  rw [this, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  exact Ideal.comap_le_comap_iff_of_surjective e.symm e.symm.surjective _ _

section Transport

variable {K K' N : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field N] [NumberField N]
  [Algebra K N] [Algebra K' N] (s : K ≃+* K') (hs : ∀ x, algebraMap K' N (s x) = algebraMap K N x)

def autEquiv : (N ≃ₐ[K] N) ≃* (N ≃ₐ[K'] N) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    obtain ⟨y, rfl⟩ := s.surjective x
    rw [hs]; exact σ.commutes y
  invFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    rw [← hs]; exact σ.commutes _
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

abbrev primeEquiv : HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K') :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s)

include hs in
omit [NumberField K] [NumberField K'] [NumberField N] in
theorem liesOver_iff (𝔭 : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 N)) :
    P.LiesOver (primeEquiv s 𝔭).asIdeal ↔ P.LiesOver 𝔭.asIdeal := by
  have h : ∀ x : 𝓞 K, algebraMap (𝓞 K') (𝓞 N) (RingOfIntegers.mapRingEquiv s x) = algebraMap (𝓞 K) (𝓞 N) x :=
    fun x => RingOfIntegers.ext (hs x)
  have h2 : ∀ x : 𝓞 K, RingOfIntegers.mapRingEquiv s x ∈ (primeEquiv s 𝔭).asIdeal ↔ x ∈ 𝔭.asIdeal := fun x => by
    change (RingOfIntegers.mapRingEquiv s).symm (RingOfIntegers.mapRingEquiv s x) ∈ 𝔭.asIdeal ↔ _
    rw [RingEquiv.symm_apply_apply]
  refine ⟨fun ⟨H⟩ => ⟨Ideal.ext fun x => ?_⟩, fun ⟨H⟩ => ⟨Ideal.ext fun x => ?_⟩⟩
  · rw [← h2, H, Ideal.mem_under, Ideal.mem_under, h]
  · obtain ⟨y, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective x
    rw [h2, H, Ideal.mem_under, Ideal.mem_under, h]

theorem absNorm_primeEquiv (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm (primeEquiv s 𝔭).asIdeal = Ideal.absNorm 𝔭.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s) ?_).toEquiv).symm
  exact (Ideal.map_comap_of_equiv _).symm

omit [NumberField N] in
theorem isFrob_iff' (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : N ≃ₐ[K] N) :
    IsFrob N (primeEquiv s 𝔭) (autEquiv s hs σ) ↔ IsFrob N 𝔭 σ := by
  unfold IsFrob
  rw [absNorm_primeEquiv]
  exact exists_congr fun P => and_congr_right' (and_congr (liesOver_iff s hs 𝔭 P) Iff.rfl)

omit [NumberField K] [NumberField K'] [NumberField N] in
theorem inInertia_iff' (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : N ≃ₐ[K] N) :
    InInertia N (primeEquiv s 𝔭) (autEquiv s hs σ) ↔ InInertia N 𝔭 σ :=
  exists_congr fun P => and_congr_right' (and_congr (liesOver_iff s hs 𝔭 P) Iff.rfl)

theorem heckeVal_transport [IsGalois K N] [IsGalois K' N] (χ : (N ≃ₐ[K'] N) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    heckeVal N χ (primeEquiv s 𝔭) = heckeVal N (χ.comp (autEquiv s hs).toMonoidHom) 𝔭 := by
  by_cases h : ∀ τ, InInertia N (primeEquiv s 𝔭) τ → χ τ = 1
  · obtain ⟨σ, hσ⟩ := exists_isFrob N 𝔭
    rw [heckeVal_eq N _ 𝔭 (fun τ hτ => h _ ((inInertia_iff' s hs 𝔭 τ).2 hτ)) hσ,
      heckeVal_eq N χ _ h ((isFrob_iff' s hs 𝔭 σ).2 hσ)]
    rfl
  · rw [heckeVal_eq_zero N χ _ h, heckeVal_eq_zero N _ 𝔭 fun h' => h fun τ hτ => ?_]
    obtain ⟨σ, rfl⟩ := (autEquiv s hs).surjective τ
    exact h' σ ((inInertia_iff' s hs 𝔭 σ).1 hτ)

theorem heckeIdeal_transport [IsGalois K N] [IsGalois K' N] (χ : (N ≃ₐ[K'] N) →* ℂˣ) {a : 𝓞 K} (ha : a ≠ 0) :
    heckeIdeal N χ (Ideal.span {RingOfIntegers.mapRingEquiv s a}) =
      heckeIdeal N (χ.comp (autEquiv s hs).toMonoidHom) (Ideal.span {a}) := by
  have e : Ideal.span {RingOfIntegers.mapRingEquiv s a} =
      (Ideal.span {a}).comap (RingOfIntegers.mapRingEquiv s).symm := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_span, Set.image_singleton]
    rfl
  unfold heckeIdeal
  rw [← finprod_comp_equiv (primeEquiv s)]
  refine finprod_congr fun 𝔭 => ?_
  rw [heckeVal_transport s hs, e, count_comap _ _ (by simpa using ha)]


include hs in
theorem isModulus_top_transport [IsGalois K N] [IsGalois K' N] (h : ∀ χ : (N ≃ₐ[K] N) →* ℂˣ, IsModulus N χ ⊤)
    (χ : (N ≃ₐ[K'] N) →* ℂˣ) : IsModulus N χ ⊤ := by
  have hc : ∀ J : Ideal (𝓞 K), IsCoprime J ⊤ := fun J => by
    rw [← Ideal.one_eq_top]; exact isCoprime_one_right
  refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr => ?_⟩
  · obtain ⟨𝔮, rfl⟩ := (primeEquiv s).surjective 𝔭
    rw [heckeVal_transport s hs]
    exact (h _).2.1 𝔮 fun h => 𝔮.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))
  · obtain ⟨a, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective α
    obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective β
    have ha : a ≠ 0 := fun h => hr.1 (by rw [h, map_zero])
    have hb : b ≠ 0 := fun h => hr.2.1 (by rw [h, map_zero])
    rw [heckeIdeal_transport s hs χ ha, heckeIdeal_transport s hs χ hb]
    refine (h _).2.2 a b ⟨ha, hb, hc _, hc _, trivial, fun φ => ?_⟩
    have := hr.2.2.2.2.2 (φ.comp s.symm.toRingHom)
    change 0 < φ (s.symm (s a)) * φ (s.symm (s b)) at this
    rwa [s.symm_apply_apply, s.symm_apply_apply] at this

include hs in
omit [NumberField K] [NumberField K'] in
theorem isAbelianGalois_transport [CharZero K] [IsAbelianGalois K N] : IsAbelianGalois K' N := by
  have : IsGalois K' N := IsGalois.of_equiv_equiv (f := s) (g := RingEquiv.refl N) (RingHom.ext hs)
  have : IsMulCommutative (N ≃ₐ[K'] N) := ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := (autEquiv s hs).surjective a
    obtain ⟨b, rfl⟩ := (autEquiv s hs).surjective b
    rw [← map_mul, ← map_mul, mul_comm' a b]⟩⟩
  exact {}

end Transport

theorem exists_extension {L N : Type} [Field L] [NumberField L] [Field N] [NumberField N] [i : Algebra L N]
    (h : IsRayField L N ⊤) (s : L ≃+* L) :
    ∃ f : N →+* N, ∀ x, f (algebraMap L N x) = algebraMap L N (s x) := by
  have hab := h.1
  let j : Algebra L N := ((@algebraMap L N _ _ i).comp s.symm.toRingHom).toAlgebra
  have hs : ∀ x, @algebraMap L N _ _ j (s x) = @algebraMap L N _ _ i x := fun x =>
    congrArg (@algebraMap L N _ _ i) (s.symm_apply_apply x)
  have hab' := @isAbelianGalois_transport L L N _ _ _ _ i j s hs _ hab
  have hm := @GlobalTheory.RayMaximal.isModulus_of_isRay L _ _ N _ _ i hab ⊤ ⊤ h.2 dvd_rfl top_ne_bot
  obtain ⟨f⟩ := @rayClassFieldMaximalSt_holds L N N _ _ _ _ i hab _ _ j hab' ⊤ top_ne_bot h.2
    (@isModulus_top_transport L L N _ _ _ _ _ _ i j s hs (@IsAbelianGalois.toIsGalois _ _ _ _ i hab)
      (@IsAbelianGalois.toIsGalois _ _ _ _ j hab') hm)
  refine ⟨@AlgHom.toRingHom L N N _ _ _ j i f, fun x => ?_⟩
  rw [← hs]
  exact @AlgHom.commutes L N N _ _ _ j i f (s x)

theorem isGalois_of_isRayField_top : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
    [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L],
    GlobalTheory.Mem.Fld.IsRayField L N ⊤ → IsGalois K N := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ h
  have hab := h.1
  refine IsGalois.of_fixedField_eq_bot K N (eq_bot_iff.2 fun x hx => ?_)
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x).2 fun σ =>
    hx (σ.restrictScalars K) trivial
  obtain ⟨z, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) y).2 fun s => by
    obtain ⟨f, hf⟩ := exists_extension h s.toRingEquiv
    let g : N →ₐ[K] N := { f with
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_apply K L N]
        exact (hf _).trans (congrArg _ (s.commutes k)) }
    exact (algebraMap L N).injective ((hf y).symm.trans
      (hx (AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)) trivial))
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

end GlobalTheory.RayTopGalois

end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp
  tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag


attribute [local instance] Over.cartesianMonoidalCategory in
open MonObj in
instance tanAddCommGroup {X : Scheme.{0}} {S : Type} [CommRing S] (x : Sp S ⟶ X) (G : Over X) [GrpObj G]
    [IsCommMonObj G] : AddCommGroup (TanM x G) := inferInstance

section Bundles

structure Charts (X : Scheme.{0}) : Type 1 where
  ι : Type
  [fin : Finite ι]
  R : ι → Type
  [ring : ∀ a, CommRing (R a)]
  χ : ∀ a, Sp (R a) ⟶ X
  opn : ∀ a, IsOpenImmersion (χ a)

attribute [instance] Charts.fin Charts.ring Charts.opn

def Charts.carrier {X : Scheme.{0}} (ch : Charts X) : Set X := ⋃ a, Set.range (ch.χ a)

structure Coc (Z : Scheme.{0}) : Type 1 where
  A : Type
  B : A → Z.Opens
  aff : ∀ α, IsAffineOpen (B α)
  cover : ∀ x : Z, ∃ α, x ∈ B α
  n : A → ℕ
  T : ∀ α β, Matrix (Fin (n α)) (Fin (n β)) Γ(Z, B α ⊓ B β)
  refl : ∀ (α : A) (S : Type) [CommRing S] (z : Sp S ⟶ Z) (h : ⊤ ≤ z ⁻¹ᵁ B α),
    (T α α).map (ev z _ (le_preimage_inf h h)) = 1
  coc : ∀ (α β γ : A) (S : Type) [CommRing S] (z : Sp S ⟶ Z) (hα : ⊤ ≤ z ⁻¹ᵁ B α) (hβ : ⊤ ≤ z ⁻¹ᵁ B β)
    (hγ : ⊤ ≤ z ⁻¹ᵁ B γ), (T α β).map (ev z _ (le_preimage_inf hα hβ)) * (T β γ).map (ev z _ (le_preimage_inf hβ hγ)) =
      (T α γ).map (ev z _ (le_preimage_inf hα hγ))

namespace Coc

variable {Z Z' : Scheme.{0}} (C : Coc Z) {S S' : Type} [CommRing S] [CommRing S']



end Coc

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Tan

variable {X : Scheme.{0}} {t : SAB H X} {S S' : Type} [CommRing S] [CommRing S']



variable {Z : Scheme.{0}} {π : Z ⟶ X} {U : Z.Opens} {hU : IsAffineOpen U} {κ : Type} [Finite κ]

end Tan

section Atlas

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}

structure PreAtlas (M : Model Xo c V.subtype) (X : Scheme.{0}) : Type 1 where
  ch : Charts X
  alg : ∀ a, c.F →+* ch.R a
  fr : ∀ a, Vecs Dw M.t (ch.R a)

def PreAtlas.FlagAt {M : Model Xo c V.subtype} {X : Scheme.{0}} (A : PreAtlas M X) (π : X ⟶ M.X)
    (ty : (E →+* ℂ) → Finset ℕ) {k : Type} [Field k] (w : Sp k ⟶ X) (u : Vecs Dw M.t k) : Prop :=
  ∃ (a : A.ch.ι) (φ : A.ch.R a →+* k), spMap φ ≫ A.ch.χ a = w ∧
    LocM.IsFrame M.t (φ.comp (A.alg a)) (w ≫ π) u ∧ SameFlag ty M.t (w ≫ π) ((A.fr a).bc φ) u

structure Atlas (M : Model Xo c V.subtype) {X : Scheme.{0}} (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) : Type 1
    extends PreAtlas M X where
  cover : ch.carrier = π ⁻¹' Set.range M.j
  alg_s : ∀ a, ch.χ a ≫ π ≫ M.s = spMap ((alg a).comp V.subtype)
  smooth : ∀ a, Smooth (ch.χ a ≫ π)
  frame : ∀ a, LocM.IsFrame M.t (alg a) (ch.χ a ≫ π) (fr a)
  glue : ∀ (k : Type) [Field k] (a a' : ch.ι) (φ : ch.R a →+* k) (φ' : ch.R a' →+* k),
    spMap φ ≫ ch.χ a = spMap φ' ≫ ch.χ a' → SameFlag ty M.t (spMap φ ≫ ch.χ a ≫ π) ((fr a).bc φ) ((fr a').bc φ')
  bij : ∀ (k : Type) [Field k] (f : c.F →+* k) (y : Sp k ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f →
    ∀ u, LocM.IsFrame M.t f (y ≫ M.j) u → ∃! w : Sp k ⟶ X, w ≫ π = y ≫ M.j ∧ toPreAtlas.FlagAt π ty w u

variable {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

namespace Atlas

variable (A : Atlas M π ty) {S : Type} [CommRing S] {K : Type} [Field K]

end Atlas

namespace Atlas

variable (A : Atlas M π ty) {S : Type} [CommRing S] {K : Type} [Field K]

end Atlas

variable {A : Atlas M π ty} {σ : E →+* ℂ} {k r : ℕ}

end Atlas

section Maps

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

variable {i : Idx H p} {X : Scheme.{0}} {π : X ⟶ (Y i).X} {ty : (E →+* ℂ) → Finset ℕ}

end Maps

end GlobalTheory.DRFlag
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.BSpan

theorem exists_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem ..)

theorem smul_mem_of_dvd {A V : Type} [CommRing A] [AddCommGroup V] [Module A V] {M : Submodule A V} {a b : A} {x : V}
    (hab : a ∣ b) (hx : a • x ∈ M) : b • x ∈ M := by
  obtain ⟨c, rfl⟩ := hab
  rw [mul_comm, mul_smul]
  exact M.smul_mem _ hx

theorem dualFr_isFullLattice {K : Type} [Field K] [NumberField K] {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K))
    (hM : Submodule.IsFullLattice K M) : Submodule.IsFullLattice K (dualFr M) :=
  GlobalTheory.DualLat.isLattice_dualFr M hM


theorem isLattice_delAtr {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice K (delAtr emb lam L) :=
  (GlobalTheory.TransLattice.nabDelLattice K ι n lam _ fun τ =>
    dualFr_isFullLattice _ (GlobalTheory.TauLat.tauLat_lattice_dual_round.1 E K ι n emb τ L hL)).2

theorem span_locW_eq_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (Pl : Rows.Places K) (w : Pl.Pl) (M : Submodule (𝓞 K) V)
    (h : ∀ x : V, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M) : Submodule.span K (locW Pl w M : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨d, hd, hx⟩ := h x
  have hd' : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd
  have : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
    rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span hx))

theorem exists_smul_mem_latOf {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok)
    [Finite S.Cl] (M : S.Cl → Submodule (𝓞 K) (VV K lam)) (hM : ∀ c, Submodule.span K (M c : Set (VV K lam)) = ⊤)
    (x : S.FormsK emb lam h) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ S.latOf emb lam h M := by
  classical
  haveI := Fintype.ofFinite S.Cl
  have h1 : ∀ c, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x.1 c ∈ M c := fun c => exists_smul_mem (by rw [hM c]; trivial)
  choose d hd hdM using h1
  refine ⟨∏ c, d c, Finset.prod_ne_zero_iff.2 fun c _ => hd c, fun c => ?_⟩
  exact smul_mem_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ c)) (hdM c)



theorem span_locW_BLat : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Pl : Rows.Places K) i (hF : ((I.S i).fam emb (lamT hc i)).Ok) (w : Pl.Pl) P, Submodule.span K (locW Pl w (BLat J emb hc i hF P) : Set ((I.S i).hlat emb (lamT hc i) hF).V) = ⊤ := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ hI hJ Pl i hF w P
  haveI := (hI.step i).fin_orb
  refine span_locW_eq_top Pl w _ fun x => ?_
  exact exists_smul_mem_latOf (I.S i) emb (lamT hc i) hF _
    (fun c => by
      let b := c.1
      let d := (I.S i).rep c
      have hd := (hJ.tied i).ok b d
      have hker : Submodule.IsFullLattice E ((J.A i).ker b d P) := by
        letI := (hJ.lev i).ker_lat b d P
        letI := (hJ.lev i).N_lat b d
        refine { span_eq_top := top_unique ?_ }
        rw [← (Submodule.IsFullLattice.span_eq_top (A := E) (M := (J.A i).N b d)), Submodule.span_le]
        intro x hx
        obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.1.ne_bot
        have hrx : r • x ∈ (J.A i).ker b d P := by
          rw [(hJ.tied i).ker_eq]
          exact Submodule.subset_span ⟨hd.N_le_Lsh (Submodule.smul_mem _ r hx),
            ((hd.mem_kerAt P _).1 (hd.smul_mem_kerAt P hr hx)).2⟩
        have hrE : algebraMap (𝓞 E) E r ≠ 0 := by simpa using hr0
        have hspan : r • x ∈ Submodule.span E (((J.A i).ker b d P) : Set _) :=
          Submodule.subset_span hrx
        have hh : (algebraMap (𝓞 E) E r)⁻¹ • (r • x) ∈
            Submodule.span E (((J.A i).ker b d P) : Set _) := Submodule.smul_mem _ _ hspan
        rw [← algebraMap_smul E r x, smul_smul, inv_mul_cancel₀ hrE, one_smul] at hh
        exact hh
      letI := isLattice_delAtr emb (lamT hc i) ((J.A i).ker b d P) hker
      exact Submodule.IsFullLattice.span_eq_top) x

end GlobalTheory.Mem.BSpan
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.principalLevelForm_mem_span_adelicRationalForms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → Fn ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  first | exact @GlobalTheory.TopSpan.proj_span | exact GlobalTheory.TopSpan.proj_span | (intros; apply GlobalTheory.TopSpan.proj_span <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

theorem _root_.GlobalTheory.T.vacuum_entire_and_normalizedJets_algebraic : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → Even a → Even b → (ambOf s B χ cD).ESmooth a b ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ), JetAlg (ambOf s B χ cD) a b S M := by
  first | exact @GlobalTheory.Mem.Col2.JetAlgebraic.esmooth_jetAlg | exact GlobalTheory.Mem.Col2.JetAlgebraic.esmooth_jetAlg | (intros; apply GlobalTheory.Mem.Col2.JetAlgebraic.esmooth_jetAlg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.exists_functionField_map_fullFlag_generic_point : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∃ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ ∧ CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) := by
  first | exact @GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | exact GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | (intros; apply GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.normalised_subgroup_column_matrices_entry_zero : ∀ (k : Type) [CommRing k], IsField k → ∀ n r : ℕ, 2 ≤ r → r < n → ∀ (H : Subgroup (GL (Fin n) k)) (b : GL (Fin n) k), (∀ u ∈ unip k n, ∀ h ∈ H, u * h * u⁻¹ ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → h.val = colMat v m → h ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → (b * h * b⁻¹).val = colMat v m → h ∈ H) → (∀ i j : Fin n, (i : ℕ) + 1 = j → (j : ℕ) < r → ∃ (c : k) (h : GL (Fin n) k), h.val = Matrix.transvection i j c ∧ h ∉ H) → ∀ a c : Fin n, r ≤ (a : ℕ) → (c : ℕ) < r → b.val a c = 0 := by
  first | exact @GlobalTheory.PosAgree.entry_zero | exact GlobalTheory.PosAgree.entry_zero | (intros; apply GlobalTheory.PosAgree.entry_zero <;> assumption)
end
