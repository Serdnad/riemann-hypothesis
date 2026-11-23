module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.G3

private noncomputable def geomPt (X : Scheme.{0}) (x : X) : sp (AlgebraicClosure (X.residueField x)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
    X.fromSpecResidueField x

private theorem geomPt_apply (X : Scheme.{0}) (x : X)
    (s : sp (AlgebraicClosure (X.residueField x))) : geomPt X x s = x := by
  exact Scheme.fromSpecResidueField_apply x _

private theorem surj_of_pts {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z), ∃! y : sp Ω ⟶ Y, y ≫ f = z) : Surjective f := by
  constructor
  intro z
  obtain ⟨y, hy, -⟩ := h (AlgebraicClosure (Z.residueField z)) (geomPt Z z)
  obtain ⟨s⟩ : Nonempty (sp (AlgebraicClosure (Z.residueField z))) := ⟨IsLocalRing.closedPoint _⟩
  have key : (y ≫ f) s = geomPt Z z s := by rw [hy]
  rw [Scheme.Hom.comp_apply, geomPt_apply] at key
  exact ⟨y s, key⟩

private theorem diag_surj {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z), ∃! y : sp Ω ⟶ Y, y ≫ f = z) :
    Surjective (pullback.diagonal f) := by
  constructor
  intro p
  obtain ⟨y, hy, huniq⟩ := h _ (geomPt (pullback f f) p ≫ pullback.fst f f ≫ f)
  have e1 : geomPt (pullback f f) p ≫ pullback.fst f f = geomPt (pullback f f) p ≫ pullback.snd f f := by
    rw [huniq (geomPt (pullback f f) p ≫ pullback.fst f f) (by dsimp only; rw [Category.assoc]),
      huniq (geomPt (pullback f f) p ≫ pullback.snd f f)
        (by dsimp only; rw [Category.assoc, pullback.condition])]
  have e2 : (geomPt (pullback f f) p ≫ pullback.fst f f) ≫ pullback.diagonal f = geomPt (pullback f f) p := by
    apply pullback.hom_ext
    · simp
    · simp [e1]
  obtain ⟨s⟩ : Nonempty (sp (AlgebraicClosure ((pullback f f).residueField p))) :=
    ⟨IsLocalRing.closedPoint _⟩
  have key : ((geomPt (pullback f f) p ≫ pullback.fst f f) ≫ pullback.diagonal f) s =
      geomPt (pullback f f) p s := by rw [e2]
  rw [Scheme.Hom.comp_apply, geomPt_apply] at key
  exact ⟨_, key⟩

theorem UpperTheory.Gal.G3.pIsoPts :
    IsoPts := by
  intro Y Z f _ h
  have hd : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, diag_surj f h⟩
  have : Mono f := (pullback.isIso_diagonal_iff f).1 hd
  have : IsOpenImmersion f := IsOpenImmersion.of_flat_of_mono f
  exact (isIso_iff_isOpenImmersion_and_surjective f).2 ⟨this, surj_of_pts f h⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
open Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR KaehlerDifferential
universe u v

set_option autoImplicit false

private theorem natCast_isUnit (k : Type) [Field k] [CharZero k] {A : Type} [CommRing A] [Algebra k A]
    {n : ℕ} (hn : n ≠ 0) : IsUnit (n : A) := by
  have h : IsUnit (n : k) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn)
  simpa using h.map (algebraMap k A)

private theorem unit_of_trace_one (k : Type) [Field k] [CharZero k] {A A' : Type} [CommRing A]
    [CommRing A'] [Algebra k A] [Algebra A A'] [Module.Finite A A'] [Module.Projective A A']
    (onto : Function.Surjective (PrimeSpectrum.comap (algebraMap A A'))) :
    IsUnit (algTrace A A' 1) := by
  by_contra hnot
  obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits hnot
  obtain ⟨Q, hQ⟩ := onto ⟨M, hM.isPrime⟩
  have hcomap : Q.asIdeal.comap (algebraMap A A') = M := congrArg PrimeSpectrum.asIdeal hQ
  let Am := Localization.AtPrime M
  let L := LocalizedModule M.primeCompl A'
  have base := IsLocalizedModule.isBaseChange M.primeCompl Am
    (LocalizedModule.mkLinearMap M.primeCompl A')
  haveI : Module.Free Am L := Module.free_of_flat_of_isLocalRing
  haveI : Nontrivial L := by
    refine ⟨⟨LocalizedModule.mkLinearMap M.primeCompl _ 1, 0, fun h ↦ ?_⟩⟩
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff M.primeCompl
      (LocalizedModule.mkLinearMap M.primeCompl A')).1 h
    have ht0 : algebraMap A A' t = 0 := by
      rw [Algebra.algebraMap_eq_smul_one]; exact ht
    have hin : (t : A) ∈ Q.asIdeal.comap (algebraMap A A') := by
      rw [Ideal.mem_comap, ht0]; exact Q.asIdeal.zero_mem
    exact t.2 (hcomap.le hin)
  have hrank : algebraMap A Am (algTrace A A' 1) = (Module.finrank Am L : Am) := by
    rw [algTrace_apply, ← projTrace_of_isBaseChange base (LinearMap.mul _ _ 1) LinearMap.id
      (fun x ↦ by simp), projTrace_eq_trace, LinearMap.trace_id]
  have hne : Module.finrank Am L ≠ 0 := fun h ↦
    not_subsingleton L ((Module.finrank_eq_zero_iff_of_free Am L).1 h)
  have hunit : IsUnit (algebraMap A Am (algTrace A A' 1)) := by
    rw [hrank, ← map_natCast (algebraMap A Am)]
    exact (natCast_isUnit k hne).map _
  exact (IsLocalization.AtPrime.isUnit_to_map_iff Am M _).1 hunit hmem

section
variable {k : Type} [Field k] [CharZero k] {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {f : X' ⟶ X} [IsFinite f] [Etale f]

private theorem unit_secTrace [Surjective f] {U : X.Opens} (hU : IsAffineOpen U) :
    IsUnit (secTrace (f := f) s s' hU 1) := by
  letI := secAlg s s' f U
  haveI := sec_finite (s := s) (s' := s') (f := f) hU
  haveI := sec_etale (s := s) (s' := s') (f := f) hU
  haveI := projective_of_etale (Sec s U) (Sec s' (f ⁻¹ᵁ U))
  have hsq : Surjective (Spec.map (f.app U)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_fromSpec_app_preimage f hU (hU.preimage f)) inferInstance
  exact unit_of_trace_one k (A := Sec s U) (A' := Sec s' (f ⁻¹ᵁ U)) hsq.surj

omit [CharZero k] in
private theorem pull_trace_app (hf : f ≫ s = s') (j : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (w : Γ(Omega s j, U)) :
    (omegaPull hf j ≫ omegaTrace hf j).app U w = secTrace (f := f) s s' hU 1 • w := by
  obtain ⟨x, rfl⟩ := toOm_surjective (s := s) (j := j) hU w
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaTrace hf j).app U ((omegaPull hf j).val.app (op U) ((toOmega s j).app (op U) x)) = _
  rw [omegaPull_toOmega hf j U x, ← one_smul (Sec s' (f ⁻¹ᵁ U)) (formPull hf U j x)]
  erw [omegaTrace_toOm_smul_formPull hf j hU]
  exact (toOm s j U).map_smul _ x

private theorem pull_trace_leftInv [Surjective f] (hf : f ≫ s = s') (j : ℕ) :
    ∃ ψ : Omega s j ⟶ Omega s j, (omegaPull hf j ≫ omegaTrace hf j) ≫ ψ = 𝟙 _ := by
  let t : ∀ U : X.affineOpens, (Sec s U.1)ˣ := fun U ↦
    (unit_secTrace (s := s) (s' := s') (f := f) U.2).unit
  have ht : ∀ U : X.affineOpens, (t U : Sec s U.1) = secTrace (f := f) s s' U.2 1 := fun _ ↦ rfl
  have hinv : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1),
      Sec.res s h ((t U)⁻¹ : (Sec s U.1)ˣ) = ((t V)⁻¹ : (Sec s V.1)ˣ) := fun U V h ↦ by
    have e : Sec.res s h (t U) = t V := by
      rw [ht, ht, secTrace_res U.2 V.2 h, map_one]
    refine Units.eq_inv_of_mul_eq_one_right ?_
    rw [← e, ← map_mul, Units.inv_mul, map_one]
  let mulInv : ∀ U : X.affineOpens, Γ(Omega s j, U.1) →ₗ[Γ(X, U.1)] Γ(Omega s j, U.1) := fun U ↦
    LinearMap.lsmul Γ(X, U.1) Γ(Omega s j, U.1) (show Sec s U.1 from ((t U)⁻¹ : (Sec s U.1)ˣ))
  have hmul : ∀ (U : X.affineOpens) (w : Γ(Omega s j, U.1)),
      mulInv U w = (((t U)⁻¹ : (Sec s U.1)ˣ) : Sec s U.1) • w := fun _ _ ↦ rfl
  have hres : ∀ (U V : X.Opens) (h : V ≤ U) (g : Sec s U) (n : Γ(Omega s j, U)),
      (Omega s j).presheaf.map (homOfLE h).op (g • n) =
        Sec.res s h g • (Omega s j).presheaf.map (homOfLE h).op n :=
    fun _ _ _ _ _ ↦ Scheme.Modules.map_smul _ _ _ _
  refine ⟨homOfAffine mulInv fun U V h w ↦ by rw [hmul, hmul, hres, hinv],
    hom_ext_affine fun U hU w ↦ ?_⟩
  refine (homOfAffine_app mulInv _ ⟨U, hU⟩ ((omegaPull hf j ≫ omegaTrace hf j).app U w)).trans ?_
  rw [hmul, pull_trace_app hf j hU, ← ht ⟨U, hU⟩, smul_smul, Units.inv_mul, one_smul]
  rfl
end

theorem UpperTheory.Gal.G3.pHodgeInj :
    HodgeInj := by
  intro k _ _ a b Z W p r c _ _ _ hc x y hxy
  letI := algΓ p
  obtain ⟨ψ, hψ⟩ := pull_trace_leftInv hc a
  have back : ∀ z : hodgeH p a b,
      cohOn.map k ψ ⊤ b (hodgeTrace hc a b (hodgePull hc a b z)) = z := fun z ↦ by
    refine (congrArg (cohOn.map k ψ ⊤ b) (hodgeTrace_hodgePull hc a b z)).trans ?_
    refine (cohOn.map_map k _ ψ z).trans ?_
    rw [hψ]
    exact LinearMap.congr_fun (cohOn.map_id k _ ⊤ b) z
  rw [← back x, ← back y, hxy]
end
