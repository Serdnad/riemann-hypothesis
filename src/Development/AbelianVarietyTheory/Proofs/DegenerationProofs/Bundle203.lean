module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle168
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle176
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle198
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle118
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem iter_lift {R K Ω : Type} [CommRing R] [Field K] [Field Ω] [Algebra K Ω] [Algebra R Ω]
    (I : Ideal R) (φ : Ω ≃ₐ[K] Ω) (q : ℕ)
    (h : ∀ x : R, ∃ y : R, algebraMap R Ω y = φ (algebraMap R Ω x) ∧ y - x ^ q ∈ I) (n : ℕ) (x : R) :
    ∃ y : R, algebraMap R Ω y = (φ ^ n) (algebraMap R Ω x) ∧ y - x ^ (q ^ n) ∈ I := by
  induction n with
  | zero => exact ⟨x, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, hI⟩ := ih
    obtain ⟨z, hz, hJ⟩ := h y
    refine ⟨z, by rw [hz, hy, pow_succ', AlgEquiv.mul_apply], ?_⟩
    rw [← Ideal.Quotient.eq] at hI hJ ⊢
    rw [hJ, map_pow, hI, ← map_pow, ← pow_mul, pow_succ]

theorem pow_pow_fixed {k : Type} [Monoid k] (c : k) (a : ℕ) (h : c ^ a = c) (n : ℕ) : c ^ (a ^ n) = c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, h]

theorem exists_lift_frac {A K L : Type} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    (g : A →+* L) (hg : Function.Injective g) : ∃ j : K →+* L, j.comp (algebraMap A K) = g :=
  ⟨IsFractionRing.lift hg, RingHom.ext fun a => IsFractionRing.lift_algebraMap hg a⟩

theorem isSemiAbelian_of_rational_torsion (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (l : ℕ) (hl : l.Prime) (h3 : 3 ≤ l)
    (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (htors : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 →
      spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left)
    (W L R K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V W] [Algebra K L] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K'] [Algebra R K'] [IsFractionRing R K']
    [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω] [IsLocalHom (algebraMap W R)]
    (hWR : Function.Injective (algebraMap W R)) (hRΩ : Function.Injective (algebraMap R Ω))
    (hcW : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K))
    (hVΩ : (algebraMap W Ω).comp (algebraMap V W) = (algebraMap K Ω).comp (algebraMap V K))
    (hk : IsAlgClosed (IsLocalRing.ResidueField R)) (hlR : IsUnit (l : R))
    (p r₀ f : ℕ) (hp : p.Prime) (hpR : CharP (IsLocalRing.ResidueField R) p) (hr₀ : 1 ≤ r₀) (hf : 1 ≤ f)
    (hres : ∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r₀) ^ m) = c)
    (σ φ : Ω ≃ₐ[K] Ω) (hfix : ∀ w : W, (φ ^ f) (algebraMap W Ω w) = algebraMap W Ω w)
    (hφ : ∀ x : R, ∃ y : R, algebraMap R Ω y = φ (algebraMap R Ω x) ∧ y - x ^ (p ^ r₀) ∈ IsLocalRing.maximalIdeal R)
    (hζ : ∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ (p ^ r₀))
    (hL : ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L,
      φ (σ x) = (σ ^ (p ^ r₀)) (φ x) ∧ (σ x = x → ∃ a b : R, algebraMap R Ω b ≠ 0 ∧ x * algebraMap R Ω b = algebraMap R Ω a))
    (G : Over (Sp W)) [GrpObj G] (hG : SmConn G) (hmod : IsModel (L := L) P.A G)
    (hdim : SmoothOfRelativeDimension P.g G.hom)
    (N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left)
    (hN : AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N)
    (c : ℕ) (hc : 1 ≤ c)
    (hext : ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left,
      s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left) :
    IsSemiAbelian G := by
  classical
  obtain ⟨j', hj0⟩ := exists_lift_frac (K := K') (algebraMap R Ω) hRΩ
  have hj' : ∀ x : R, j' (algebraMap R K' x) = algebraMap R Ω x := fun x => RingHom.congr_fun hj0 x
  obtain ⟨i, hi⟩ := exists_lift_frac (K := L) ((algebraMap R K').comp (algebraMap W R))
    ((IsFractionRing.injective R K').comp hWR)
  replace hi := hi.symm
  have hjW : (j'.comp i).comp (algebraMap W L) = algebraMap W Ω := by
    rw [RingHom.comp_assoc, ← hi]
    exact RingHom.ext fun w => (hj' _).trans (IsScalarTower.algebraMap_apply W R Ω w).symm
  have hjK : (j'.comp i).comp (algebraMap K L) = algebraMap K Ω := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) ?_
    rw [RingHom.comp_assoc, ← hcW, ← RingHom.comp_assoc, hjW, hVΩ]
  obtain ⟨θ, hθ, hθK⟩ := GlobalTheory.T.grpScheme_points_model_over_field K W L P.A G hmod Ω (j'.comp i) hjK hjW
  obtain ⟨e, act, hact, he, hpair, hrel, hdef⟩ := GlobalTheory.T.galois_action_torsion_pairing_tame_fixedPoints K P Ω l (p ^ r₀) hl htors σ φ K' j' hζ
    (fun L h₁ h₂ h₃ x hx => ⟨(hL L h₁ h₂ h₃ x hx).1, fun h => by
      obtain ⟨a, b, hb0, hab⟩ := (hL L h₁ h₂ h₃ x hx).2 h
      refine ⟨algebraMap R _ a / algebraMap R _ b, ?_⟩
      rw [map_div₀, hj', hj', div_eq_iff hb0]
      exact hab.symm⟩)
  have hcard := (GlobalTheory.T.torsion_points_polarised_abelianVariety_galois K P Ω l hl).1
  haveI := P.isAb.comm
  have hψ : (φ ^ f).toRingEquiv.toRingHom.comp (j'.comp i) = j'.comp i := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors W) ?_
    rw [RingHom.comp_assoc, hjW]
    exact RingHom.ext fun w => hfix w
  obtain ⟨t, a, m, C, Q, H, U, hm, hH, hcnt, hQ, hU, hHU, hT⟩ :=
    GlobalTheory.T.frobenius_counts_integral_torsion_specialFibre W R Ω hRΩ hk p (r₀ * f) l hp hpR (Nat.mul_pos hr₀ hf) hl hlR
      (fun c => by
        obtain ⟨m, hm, h⟩ := hres c
        refine ⟨m, hm, ?_⟩
        rw [pow_mul, ← pow_mul _ f m, mul_comm f m, pow_mul _ m f]
        exact pow_pow_fixed c _ h f)
      (φ ^ f).toRingEquiv.toRingHom (fun w => hfix w)
      (fun x => by rw [pow_mul]; exact iter_lift _ φ _ hφ f x)
      G hG P.g hdim N hN (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) θ (act (φ ^ f))
      (fun x => hθ _ hψ _ _ (hact _ x))
  rw [← map_pow, ← pow_mul] at hU hHU
  have hqq : (p ^ (r₀ * f)) ^ m = (p ^ r₀) ^ (f * m) := by rw [pow_mul, ← pow_mul _ f m]
  rw [hqq] at hU hQ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hg : P.g ≤ t + a := by
    refine GlobalTheory.T.weight_le_add_of_torsion_pairing (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) Ω l ((p ^ r₀) ^ (f * m)) P.g t a c C hl h3
      (Nat.cast_ne_zero.2 hl.ne_zero) ?_ hc hcard e he (act σ) (act (φ ^ (f * m))) (hpair _) (hrel _)
      (fun x hx => Over.OverMorphism.ext ((hact σ x).trans (htors σ x hx))) H U Q ?_ hcnt hQ hU hHU
    · rw [← pow_mul]
      exact Nat.one_lt_pow (Nat.mul_pos hr₀ (Nat.mul_pos hf hm)).ne' hp.one_lt
    · intro n x hx hS
      obtain ⟨y, hy⟩ := hdef n x hx hS
      obtain ⟨y', hy'⟩ := hθK K' i j' rfl x y hy _ hi
      obtain ⟨s, hs₁, hs₂⟩ := hext y'
      refine (hH _).2 ⟨s, hs₁, ?_⟩
      rw [← hy', ← hs₂, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hj0]
  have hproper : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    obtain ⟨ε, -⟩ := hmod
    haveI := P.isAb.proper
    rw [← Over.w ε.hom]
    have : IsProper ((Over.pullback (spMap (algebraMap K L))).obj P.A).hom :=
      inferInstanceAs (IsProper (pullback.snd _ _))
    have : IsIso ε.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ε.hom))
    infer_instance
  · clear hcard
    refine GlobalTheory.T.isSemiAbelian_of_proper_generic_torusExtension_special W L G hG hproper _ _ ?_ ?_ (hT hg)
    · ext w
      rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]
    · intro z
      obtain ⟨m, hm, h⟩ := hres z
      have h1 : 1 < (p ^ r₀) ^ m := by
        rw [← pow_mul]
        exact Nat.one_lt_pow (Nat.mul_pos hr₀ hm).ne' hp.one_lt
      refine ⟨Polynomial.X ^ ((p ^ r₀) ^ m) - Polynomial.X, ?_, by simp [h]⟩
      refine Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow _) ?_
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]
      exact_mod_cast h1

theorem potentialSemistable_rational_lTorsion_any_closure (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (IsLocalRing.ResidueField V)) (l : ℕ) (hl : l.Prime) (h3 : 3 ≤ l) (hlu : IsUnit (l : V))
    (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω]
    (htors : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 →
      spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) :
    PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  classical
  obtain ⟨R, _, σ, φ, hSH, hloc, hres, hW, hσ, hφ, hζ, hL⟩ := GlobalTheory.T.exists_maxUnramified_frobenius_tame_alt V K hfin l hl hlu Ω _ rfl
  letI := Fintype.ofFinite (IsLocalRing.ResidueField V)
  obtain ⟨p, hpV⟩ := CharP.exists (IsLocalRing.ResidueField V)
  obtain ⟨r₀, hp, hq⟩ := FiniteField.card (IsLocalRing.ResidueField V) p
  rw [← Nat.card_eq_fintype_card] at hq
  rw [hq] at hres hφ hζ hL
  have hpR : CharP (IsLocalRing.ResidueField R) p :=
    charP_of_injective_ringHom (IsLocalRing.ResidueField.map (algebraMap V R)).injective p
  have hVΩ : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have hRΩ : Function.Injective (algebraMap R Ω) := Subtype.val_injective
  have hVR : Function.Injective (algebraMap V R) := fun a b h => hVΩ (congrArg Subtype.val h)
  obtain ⟨K', _, _, hSH⟩ : ∃ (K' : Type) (_ : Field K') (_ : Algebra R K'), SH R K' := ⟨_, _, _, hSH⟩
  haveI : IsFractionRing R K' := hSH.2.2.2
  obtain ⟨jK, hjK'⟩ := exists_lift_frac (K := K) ((algebraMap R K').comp (algebraMap V R))
    ((IsFractionRing.injective R K').comp hVR)
  letI : Algebra K K' := jK.toAlgebra
  have hcomp : (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) := hjK'.symm
  obtain ⟨s, c, hc, hgeo⟩ := GlobalTheory.T.exists_neronNeutralComponent_finite_level V K R K' hSH hcomp P
  obtain ⟨W, hWd, hs, hWc, hWf, hWl, f, hf, hfix⟩ := hW s
  obtain ⟨G, _, L, _, _, _, _, hG, hcW, hmod, hdim, ⟨N, hN⟩, hext⟩ := hgeo W hWd hs hWl
  have hlR : IsUnit (l : R) := by simpa using hlu.map (algebraMap V R)
  haveI : IsLocalHom (algebraMap W R) := hWl
  have hsemi : IsSemiAbelian G :=
    isSemiAbelian_of_rational_torsion V K l hl h3 P Ω htors W L R K' Subtype.val_injective hRΩ hcW
      (IsScalarTower.algebraMap_eq V K Ω) hSH.2.2.1 hlR p r₀ f hp hpR r₀.2 hf hres σ φ (fun w => hfix w.1 w.2) hφ hζ
      (fun L h₁ h₂ h₃ x hx => ⟨(hL L h₁ h₂ h₃ x hx).1, fun h => by
        obtain ⟨a, ha, b, hb, hb0, hab⟩ := (hL L h₁ h₂ h₃ x hx).2 h
        exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, hab⟩⟩)
      G hG hmod hdim N hN c hc hext
  have hVW : IsLocalHom (algebraMap V W) := ⟨fun v hv => by
    have : IsUnit (algebraMap V R v) := hv.map W.val
    exact (isUnit_map_iff (algebraMap V R) v).1 this⟩
  exact ⟨W, L, inferInstance, inferInstance, hWd, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcW, hWf, hVW, hWc, G, inferInstance, hmod, hsemi⟩

theorem potModel_of_rational_torsion : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → 3 ≤ l → IsUnit (l : V) → ∀ (P : Out.PolAV (Sp K)), (∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ P.A), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ hfin l hl h3 hlu P htors
  exact potentialSemistable_rational_lTorsion_any_closure V K hfin l hl h3 hlu P (AlgebraicClosure K) htors

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OnModel

theorem mem_nonzeroLocus_pullTo {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) {y : Y'}
    (hy : h y ∈ nonzeroLocus s) : y ∈ nonzeroLocus (VVRank.pullTo s h e) := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
  have hle := VVRank.wchart_le_of_eq (L := L) h e j
  have q := Y'.basicOpen_res ((h.app _).hom (s.f j)) (homOfLE hle).op
  refine q.ge ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Y.basicOpen_le _ hj) k, ?_⟩
  exact (Scheme.preimage_basicOpen h (s.f j)).le hj

section Base
variable {S : Scheme.{0}} (G : Over S)

def toBase : G.left ⟶ (Over.mk (𝟙 S) ⊗ G).left :=
  (lift (Over.homMk G.hom (Category.comp_id _) : G ⟶ Over.mk (𝟙 S)) (𝟙 G)).left

theorem toBase_snd : toBase G ≫ (snd (Over.mk (𝟙 S)) G).left = 𝟙 _ := by
  rw [toBase, ← Over.comp_left, lift_snd, Over.id_left]

theorem snd_hom : (snd (Over.mk (𝟙 S)) G).left ≫ G.hom = (fst (Over.mk (𝟙 S)) G).left :=
  (pullback.condition (f := 𝟙 S) (g := G.hom)).symm.trans (Category.comp_id _)

theorem comp_toBase {Z : Scheme.{0}} (r : Z ⟶ (Over.mk (𝟙 S) ⊗ G).left) :
    (r ≫ (snd (Over.mk (𝟙 S)) G).left) ≫ toBase G = r := by
  have a : toBase G ≫ (fst (Over.mk (𝟙 S)) G).left = G.hom := by
    rw [toBase, ← Over.comp_left, lift_fst]; rfl
  refine psi_ext ?_ ?_
  · rw [Category.assoc, a, Category.assoc]
    exact congrArg (r ≫ ·) (snd_hom G)
  · rw [Category.assoc, toBase_snd, Category.comp_id]

variable [GrpObj G] {L : LB G.left} {k : ℕ}

def down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) : H0 L k :=
  VVRank.pullTo (φ := fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) G).left) (ε := fun _ => (k : ℤ)) σ (toBase G)
    fun _ => toBase_snd G

theorem sval_down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) {Z : Scheme.{0}} (r : Z ⟶ (Over.mk (𝟙 S) ⊗ G).left)
    (z : Z) {J} (hJ : Good L z J) :
    sval (down G σ) (r ≫ (snd (Over.mk (𝟙 S)) G).left) z J = VVRank.sv G σ r z J := by
  refine (VVRank.sval_pullTo _ _ _ _ z hJ).trans ?_
  rw [comp_toBase]

theorem mem_nonzeroLocus_down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) {g : (Over.mk (𝟙 S) ⊗ G).left}
    (hg : g ∈ nonzeroLocus σ) : (snd (Over.mk (𝟙 S)) G).left g ∈ nonzeroLocus (down G σ) := by
  refine mem_nonzeroLocus_pullTo _ _ _ ?_
  have e := comp_toBase G (𝟙 _)
  rw [Category.id_comp] at e
  rw [← Scheme.Hom.comp_apply, e]
  exact hg

end Base

theorem isGenSec_of_down {V : Type} [CommRing V] (G : Over (Sp V)) [GrpObj G] {L : LB G.left} (hL : L.IsLB) {k : ℕ}
    (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 (Sp V))))) (h : ∀ s : H0 L k, ∃ b : V, SecIsMul G.hom b s (down G σ)) :
    IsGenSec G L (k : ℤ) σ := by
  intro s
  obtain ⟨b, hb⟩ := h (down G s)
  let c : Γ((Over.mk (𝟙 (Sp V))).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b
  have key : SecM.ofSec G s = c • SecM.ofSec G σ := ThetaAct.sv_ext hL fun y J hJ => by
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm
    refine (sval_down G s (𝟙 _) y hJ).symm.trans (Eq.trans ?_ (congrArg (_ * ·) (sval_down G σ (𝟙 _) y hJ)))
    have hz := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (𝟙 _ ≫ (snd (Over.mk (𝟙 (Sp V))) G).left)
    refine (congrArg (gs _ y _) (hb _)).trans ((gs_mul _ y _ hz _ _).trans (congrArg (· * _) ?_))
    refine (gs_res _ y le_top hz _).trans ((gs_pull _ G.hom y ⊤ trivial _).trans ?_)
    rw [Category.assoc, snd_hom]
  exact ⟨c, fun j => congrArg (fun q => q.1 j) key⟩

theorem theta_on_model : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : LB.Sec (LPow G U.LG.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp V)))), NZ G U.LG.L (𝟙 (Sp V)) σ → IsGenSec G U.LG.L ((1 : ℕ) : ℤ) σ ∧ ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))), (∀ x (c : F), ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  intro hHV V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U σ hσ
  have hL := U.LG.isLB
  have := A.isAb.comm
  obtain ⟨g, hg, hg'⟩ := hσ
  obtain ⟨hgen, hexp⟩ := GlobalTheory.T.section_nonzero_closedFibre_generates_expansion_zero hHV.1 V hc ϖ hϖ D Q hQ F v hv A G hG U (down G σ)
    ⟨_, by rw [← Scheme.Hom.comp_apply, snd_hom]; exact hg, mem_nonzeroLocus_down G σ hg'⟩
  refine ⟨isGenSec_of_down G hL σ hgen, fun m h₁ h₂ h₃ ξ => ?_⟩
  obtain ⟨w₀, ρ, w, hp, hN, hw, hr, H⟩ := GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso V _ D A G U.toUnifPre
  have hτ : 𝟙 (Sp F) ≫ (Over.mk (jFK (R := V) F ≫ jK V)).hom = (TFK (R := V) F).hom ≫ jK V := Category.id_comp _
  obtain ⟨th, hth⟩ := exists_secRel hp (T := TFK (R := V) F) (T₀ := Over.mk (jFK (R := V) F ≫ jK V)) (𝟙 (Sp F)) hτ hw hL
    A.isLB (VVRank.pullS G _ ξ σ)
  obtain ⟨σ', hσ', hE⟩ := H F 1 (down G σ) th fun Z r z J J' hJ hJ' => by
    refine Eq.trans ?_ (hth Z r z J J' hJ hJ')
    refine Eq.trans ?_ ((sval_down G σ _ z hJ).trans (VVRank.sv_pullS G _ ξ σ _ z hJ).symm)
    rw [Category.assoc, VVRank.whisker_snd_left, Category.assoc, psi_snd']
  obtain ⟨ϑ, hϑ, hP⟩ := hexp σ' hσ'
  obtain ⟨k₁, x, c, k₂, k₃⟩ := GlobalTheory.T.normalisedThetaConstants_primitive_integral_one_unit hHV V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ (hE ϑ hϑ) hP m h₁ h₂ h₃
  have hx : ∀ x : TFK (R := V) F ⟶ A.A, 𝟙 (Sp F) ≫ (pushHom hp (TFK (R := V) F) x).left = x.left ≫ _ :=
    fun x => Category.id_comp _
  refine ⟨fun x₀ c hc => ?_, pushHom hp (TFK (R := V) F) x, c, ?_, k₃⟩
  · let y : TFK (R := V) F ⟶ A.A := Over.homMk (hp.1.lift x₀.left (jFK (R := V) F) (Over.w x₀)) (hp.1.lift_snd _ _ _)
    have hy : 𝟙 (Sp F) ≫ x₀.left = y.left ≫ _ := (Category.id_comp _).trans (hp.1.lift_fst _ _ _).symm
    have hn : y ^ (m ^ 2) = 1 := by
      refine Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))
      refine (over_pow hp (T₀ := Over.mk (jFK (R := V) F ≫ jK V)) _ hτ hy _).symm.trans ?_
      rw [hc.1]
      exact over_one hp _ hτ
    exact k₁ y c (ThG.move hp _ hτ hw hL A.isLB hr hy hn hth hc)
  · have : IsIso (X := (TFK (R := V) F).left) (Y := (Over.mk (jFK (R := V) F ≫ jK V)).left) (𝟙 (Sp F)) := IsIso.id _
    have q := ThG.up hp _ hτ hw hL A.isLB hr (hx x) (by rw [← map_pow, k₂.1, map_one]) hth k₂
    have e : inv (X := (TFK (R := V) F).left) (Y := (Over.mk (jFK (R := V) F ≫ jK V)).left) (𝟙 (Sp F)) = 𝟙 (Sp F) :=
      IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
    rw [e] at q
    exact q

end GlobalTheory.Ex.OnModel
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.hasGeometricTest_of_hasUniformisedTest : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ρ.HasU → ρ.HasGeo := by
  first | exact @GlobalTheory.ZH.GeoExist.hasGeo_of_hasU | exact GlobalTheory.ZH.GeoExist.hasGeo_of_hasU | (intros; apply GlobalTheory.ZH.GeoExist.hasGeo_of_hasU <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem eigen_of_expansion_in_class : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (w₀ : W0 u.U.toUnifPre), w₀.IsGen → ∀ (α : u.D.toPre.X) (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N) (Φ : Fam u.D.toPre (PadicAlgCl p) S.N), IsComb u.A s b σ → u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ → (∀ β, (∀ z : u.D.toPre.X, β ≠ α + S.N • z) → ∀ j, (Φ.s β).f j = 0) → ∀ (t : S.perp l.yy.ker) (h : S.Gam), ∑ j, (∑ i, y₀ (algebraMap o S.R (S.ρ t j i)) * b i) * y₀ ⟨S.ev h j, S.ev_mem h j⟩ = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val * ∑ j, b j * y₀ ⟨S.ev h j, S.ev_mem h j⟩ := by
  intro h1 h2 hT o Ω _ _ _ _ S ρ p _ y₀ u l hy x rig e th s hx hs w₀ hw₀ α b σ Φ hσ hΦ hsupp t h
  obtain ⟨hLL, -⟩ := laws_all h1 h2
  obtain ⟨hc, -, hadm, -⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hy
  have hodd : Odd S.N := by
    rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hN1 : 1 ≤ S.N := le_trans (by norm_num) S.N_ge
  obtain ⟨-, -, -, hval, -, hθ⟩ := hs
  obtain ⟨θ, hθs, hθa⟩ := hθ (t : S.Gam)
  obtain ⟨τ, q, hqy, hqt, hqx, hτ⟩ := GlobalTheory.T.torusPoints_level_weights_from_orthogonal_labels h1 h2 hT o Ω S ρ p y₀ u l hy x hx t
  obtain ⟨⟨w, hw⟩, -⟩ := GlobalTheory.UT.SymFrame.main hLL u.V _ hadm u.D (PadicAlgCl p) S.N hodd q
  obtain ⟨-, -, c3, c4, c5⟩ := GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s b
  choose s' hs' using fun i => (c4 θ (s i)).exists
  obtain ⟨σ', hσ'⟩ := (c4 θ σ).exists
  have hσ'c : IsComb u.A s' b σ' := (c3 θ s' σ σ' hs' hσ).1 hσ'
  have hσ'c2 := c5 S.J (fun i j => y₀ (algebraMap o S.R (S.ρ t j i))) s' b σ' (fun i => hθa i _ (hs' i)) hσ'c
  obtain ⟨hbij, hlin⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hLL u.V _ hadm u.D u.A u.G u.semi u.U
  obtain ⟨hb1, hb2⟩ := hbij (PadicAlgCl p) S.N hN1 w₀ hw₀
  obtain ⟨Φ', hΦ'⟩ := (hb1 σ').exists
  have hrel := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hodd q _ hqx θ hθs w₀ hw₀ w hw
    σ σ' Φ Φ' hΦ hΦ' hσ'
  have hwt := ((GlobalTheory.UT.TorusWeight.torus_weight hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hodd q τ hqy
    hqt w hw).2 Φ Φ').1 hrel
  set κ : PadicAlgCl p := y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val with hκ
  have hΦeq : Φ' = (κ - 1) • Φ + Φ := by
    rw [sub_smul, one_smul, sub_add_cancel]
    refine fam_ext fun β j => ?_
    rw [hwt β j, smul_f, ← constBF_eq]
    by_cases hβ : ∀ z : u.D.toPre.X, β ≠ α + S.N • z
    · rw [hsupp β hβ j, mul_zero, mul_zero]
    · push Not at hβ
      obtain ⟨z, rfl⟩ := hβ
      rw [hτ, hκ]
      simp
  obtain ⟨⟨σ'', hσ''⟩, -⟩ := GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N (Fin 2) (fun _ => σ) ![κ - 1, 1]
  have hσ''e : u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ'' ((κ - 1) • Φ + Φ) := by
    refine hlin (PadicAlgCl p) S.N w₀ σ σ σ'' Φ Φ (κ - 1) hΦ hΦ fun j => ?_
    rw [hσ'' j, Fin.sum_univ_two]
    simp [liftFun, cF]
  have heq : σ'' = σ' := (hb2 Φ').unique (hΦeq ▸ hσ''e) hΦ'
  subst heq
  obtain ⟨v1, -, v3, -⟩ := GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists h1 u.V u.A (PadicAlgCl p) S.N (x h) (e h)
  have a1 := v1 S.J s b _ σ hσ (fun i => hval i h)
  have a2 := v1 S.J s _ _ σ'' hσ'c2 (fun i => hval i h)
  have a3 := v1 (Fin 2) (fun _ => σ) _ _ σ'' hσ'' (fun _ => a1)
  rw [v3 _ _ _ a2 a3, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end GlobalTheory.TestFibre
end
