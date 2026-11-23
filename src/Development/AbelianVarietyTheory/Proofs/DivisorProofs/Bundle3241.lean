module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3207
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle724
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.MapAff

theorem theta_map_aff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o R : Type) [CommRing o] [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (β : o →+* R) (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → 3 ≤ m → IsUnit (m : R) → n + 1 = m ^ (4 * g) → PolFib G L g x → (∀ (K : Type) [Field K] (i : R →+* K), IsGenSec G L _ (SecAt.pull G L θ i)) → ∃ f : Sp R ⟶ PSpace o n, f ≫ PSpace.str o n = spMap β ∧ ThMap G L ρ m x f := by
  intro S G _ _ L ρ hL hρ g m n o R _ _ _ _ _ _ β x θ hm hm3 hmu hn hpol hgen
  obtain ⟨e, he⟩ := GlobalTheory.T.thetaSymmetricFunctions_mem_normalDomain S G L ρ hL hρ g m (n + 1) R x θ hm hmu hn hpol
  have hpolK : ∀ (K : Type) [Field K] (i : R →+* K), PolFib G L g (spMap i ≫ x) := fun K _ i =>
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S G L G L (𝟙 S) (𝟙 G.left) hL hL (GlobalTheory.SiegLower.isGrpPullback_id G)
      (GlobalTheory.SiegLower.lbIso_pull_id hL) g R x).2 K i hpol
  have hspan : Ideal.span (Set.range e) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    letI := Ideal.Quotient.field M
    let i : R →+* AlgebraicClosure (R ⧸ M) := (algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).comp (Ideal.Quotient.mk M)
    have hmK : ((m : ℕ) : AlgebraicClosure (R ⧸ M)) ≠ 0 := by
      have := hmu.map i
      rw [map_natCast] at this
      exact this.ne_zero
    have hpK := hpolK _ i
    obtain ⟨pt, c, hl⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m (n + 1) _ (spMap i ≫ x) (SecAt.pull G L θ i) hm hmK hn hpK
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_thetaConstant_levelSquare_ne_zero S G L ρ hL hρ g m (n + 1) _ (spMap i ≫ x) c hm hm3 hmK hpK ⟨_, pt, hgen _ i, hl⟩
    obtain ⟨j, hj⟩ := GlobalTheory.UMin.symTup_basic.2.2.2 _ (n + 1) c ⟨a, ha⟩
    apply hj
    rw [← he _ i pt c hl j]
    have hM' : e j ∈ M := hle (Ideal.subset_span ⟨j, rfl⟩)
    simp [i, Ideal.Quotient.eq_zero_iff_mem.2 hM']
  have hstr : GlobalTheory.ProjSpace.pt β e hspan ≫ PSpace.str o n = spMap β := by
    rw [GlobalTheory.ProjSpace.pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C β e r
  have hf : PCrd (GlobalTheory.ProjSpace.pt β e hspan) e := (GlobalTheory.UMin.CrdUniq.pCrd_iff _ β hstr e).2 ⟨hspan, rfl⟩
  refine ⟨GlobalTheory.ProjSpace.pt β e hspan, hstr, ?_⟩
  intro K _ x' c ⟨θ', pt, hθ', hl⟩
  obtain ⟨i, rfl⟩ := GlobalTheory.UMin.CrdUniq.exists_spMap' x'
  obtain ⟨r, hr⟩ := hθ' (SecAt.pull G L θ i)
  have hsm : SecM.ofSec G (SecAt.pull G L θ i) = r • SecM.ofSec G θ' := Subtype.ext (funext hr)
  set a : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r with ha
  have hra : GlobalTheory.ZH.fn a = r := by
    simp [GlobalTheory.ZH.fn, a]
  have hl0 : ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun b => a * c b) := by
    refine ⟨hl.1, fun b => ?_, hl.2.2⟩
    have h1 := GlobalTheory.Ex.OneGen.ThG.smul hL hsm (hl.2.1 b)
    convert h1 using 1
    rw [← hra]
    exact map_mul _ _ _
  have h2 : PCrd (spMap i ≫ GlobalTheory.ProjSpace.pt β e hspan) (fun j => a ^ (n + 1).factorial * symTup c j) := by
    have := GlobalTheory.T.projectiveHomogeneousCoords_basic_properties.1 o R K n _ e i hf
    convert this using 2 with j
    rw [he K i pt _ hl0 j, GlobalTheory.UMin.symTup_basic.1]
  have ha0 : a ≠ 0 := by
    rintro h0
    obtain ⟨j, hj⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties.2.2 o K n _).2 _ h2
    apply hj
    simp [h0, Nat.factorial_ne_zero]
  have h3 := GlobalTheory.T.projectiveHomogeneousCoords_basic_properties.2.1 o K n _ _ ((a ^ (n + 1).factorial)⁻¹) (isUnit_iff_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ha0))) h2
  convert h3 using 1
  funext j
  rw [inv_mul_cancel_left₀ (pow_ne_zero _ ha0)]

end GlobalTheory.UMin.MapAff
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.IntTheta

section Pull
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ}

theorem sec_ext' {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f₁, p₁⟩ := s
  obtain ⟨f₂, p₂⟩ := s'
  obtain rfl : f₁ = f₂ := funext h
  rfl

theorem gs_pullS' {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 1 → L.ι) (hz : r z ∈ (LPow A L a T').U j) :
    gs r z ((LPow A L a T').U j) ((VVRank.pullS A a h s).f j) =
      gs (r ≫ (h ▷ A).left) z ((LPow A L a T).U j) (s.f j) :=
  (gs_res r z (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j) hz _).trans
    (gs_pull r (h ▷ A).left z _ (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j hz) _)

theorem pullS_comp' {T T' T'' : Over S} (h' : T'' ⟶ T') (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) :
    VVRank.pullS A a h' (VVRank.pullS A a h s) = VVRank.pullS A a (h' ≫ h) s :=
  sec_ext' fun j => fn_ext fun y hy => by
    refine (gs_pullS' h' _ _ y j hy).trans ((gs_pullS' h _ _ y j
      (chart_le_res A L (h' ▷ A) (whiskerRight_snd _ _) a j hy)).trans (Eq.trans ?_ (gs_pullS' _ _ _ y j hy).symm))
    rw [comp_whiskerRight, Over.comp_left]
    rfl

theorem pullS_heq {T : Over S} {Y : Scheme.{0}} {y₁ y₂ : Y ⟶ S} (e : y₁ = y₂) (h₁ : Over.mk y₁ ⟶ T)
    (h₂ : Over.mk y₂ ⟶ T) (he : h₁.left = h₂.left) (s : LB.Sec (LPow A L a T)) :
    HEq (VVRank.pullS A a h₁ s) (VVRank.pullS A a h₂ s) := by
  subst e
  obtain rfl : h₁ = h₂ := Over.OverMorphism.ext he
  rfl

end Pull

section Sec
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left)

theorem pull_pull {R K K' : Type} [CommRing R] [CommRing K] [CommRing K'] {x : Sp R ⟶ S} (θ : SecAt G L x)
    (i : R →+* K) (i' : K →+* K') :
    HEq (SecAt.pull G L (SecAt.pull G L θ i) i') (SecAt.pull G L θ (i'.comp i)) := by
  unfold SecAt.pull
  rw [pullS_comp']
  refine pullS_heq ?_ _ _ ?_ θ
  · rw [spMap_comp, Category.assoc]
  · simp only [Over.comp_left, Over.homMk_left]
    exact (spMap_comp i i').symm

theorem pull_heq_of_eq {R K : Type} [CommRing R] [CommRing K] {x : Sp R ⟶ S} (θ : SecAt G L x)
    {i₁ i₂ : R →+* K} (h : i₁ = i₂) : HEq (SecAt.pull G L θ i₁) (SecAt.pull G L θ i₂) := by
  subst h; rfl

variable {G L} in
theorem thList_of_heq (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ) {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S} (e : x₁ = x₂)
    {θ₁ : SecAt G L x₁} {θ₂ : SecAt G L x₂} (h : HEq θ₁ θ₂) {N : ℕ} {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K}
    (H : ThList G L ρ m x₁ θ₁ pt c) : ∃ pt' : Fin N → (Over.mk x₂ ⟶ G), ThList G L ρ m x₂ θ₂ pt' c := by
  subst e
  obtain rfl := eq_of_heq h
  exact ⟨pt, H⟩

end Sec

end GlobalTheory.UMin.IntTheta

namespace GlobalTheory.UMin.IntTheta

theorem at_cdvr (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (χ : Sp R ⟶ S) (σ : SecAt t.G t.PP.L χ)
    (e : Fin N → FractionRing R) (hm : Odd m) (hm3 : 3 ≤ m) (hmu : IsUnit (m : R)) (hN : N = m ^ (4 * g))
    (hP : PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ)) (hNZ : NZ t.G t.PP.L χ σ)
    (hS : SymAt t.G t.PP.L t.PP.rig m (spMap (algebraMap R (FractionRing R)) ≫ χ)
      (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) e)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) (φ : R →+* V)
    (F : FractionRing R →+* FractionRing V)
    (hring₀ : F.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ) :
    ∃ eV : Fin N → V, (∀ j, algebraMap V (FractionRing V) (eV j) = F (e j)) ∧ ∃ j, IsUnit (eV j) := by
  obtain ⟨hdvr, -, -⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨i, hi⟩ : ∃ i : V →+* AlgebraicClosure (FractionRing V),
      i = (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V)) :=
    ⟨_, rfl⟩
  obtain ⟨i', hi'⟩ : ∃ i' : FractionRing R →+* AlgebraicClosure (FractionRing V),
      i' = (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp F := ⟨_, rfl⟩
  have hring : i'.comp (algebraMap R (FractionRing R)) = i.comp φ := by
    rw [hi, hi', RingHom.comp_assoc, hring₀, RingHom.comp_assoc]

  have : IsMonHom (Iso.refl t.G).hom := inferInstanceAs (IsMonHom (𝟙 t.G))
  have hid : IsGrpPullback t.G t.G (𝟙 _) (𝟙 t.G.left) := isGrpPullback_of_iso (Iso.refl t.G)
  have hmove : ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), ∀ (R'' : Type) [CommRing R''] (j : R' →+* R''),
      PolFib t.G t.PP.L g x → PolFib t.G t.PP.L g (spMap j ≫ x) := fun R' _ x =>
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S t.G t.PP.L t.G t.PP.L (𝟙 S) (𝟙 t.G.left) t.PP.isLB t.PP.isLB hid
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id t.PP.isLB) g R' x).2
  have hPK : PolFib t.G t.PP.L g (spMap i' ≫ spMap (algebraMap R (FractionRing R)) ≫ χ) :=
    hmove _ _ _ i' hP
  have hmK : ((m : ℕ) : AlgebraicClosure (FractionRing V)) ≠ 0 := by
    have := (hmu.map (i'.comp (algebraMap R (FractionRing R)))).ne_zero
    simpa using this
  obtain ⟨pt, c, hT⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m N
    (AlgebraicClosure (FractionRing V)) _
    (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) i') hm hmK hN hPK
  have hsym := hS _ i' pt c hT

  have ex : spMap i' ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap i ≫ spMap φ ≫ χ := by
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hring]
  have hθ : HEq (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) i')
      (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ φ) i) :=
    ((pull_pull t.G t.PP.L σ _ i').trans (pull_heq_of_eq t.G t.PP.L σ hring)).trans
      (pull_pull t.G t.PP.L σ φ i).symm
  obtain ⟨pt', hT'⟩ := thList_of_heq t.PP.rig m ex hθ hT
  have hPV : PolFib t.G t.PP.L g (jK V ≫ spMap φ ≫ χ) := by
    have e₁ : jK V ≫ spMap φ ≫ χ = spMap F ≫ spMap (algebraMap R (FractionRing R)) ≫ χ := by
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hring₀]
    rw [e₁]; exact hmove _ _ _ F hP
  have hNZV := GlobalTheory.UMin.nz_pull S t.G t.PP.L t.PP.isLB t.semi R V χ σ φ hNZ
  have hmV : IsUnit ((m : ℕ) : V) := by simpa using hmu.map φ
  have hinj : Function.Injective i := by
    rw [hi, RingHom.coe_comp]
    exact (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective.comp
      (IsFractionRing.injective V (FractionRing V))
  have hprim := GlobalTheory.T.thetaConstants_primitive_principallyPolarised_trait E H S t g V hV (spMap φ ≫ χ) hPV (SecAt.pull t.G t.PP.L σ φ) hNZV m N hm hm3 hmV
    (AlgebraicClosure (FractionRing V)) i pt' c hinj hT'
  rw [hi] at hprim
  refine GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_primitive_unit V (AlgebraicClosure (FractionRing V)) (algebraMap (FractionRing V) _) N c (fun j => F (e j))
    hprim (fun j => ?_)
  rw [← hsym j, hi']; rfl

end GlobalTheory.UMin.IntTheta

namespace GlobalTheory.UMin.IntTheta

theorem comp_inj {R V : Type} [CommRing R] [CommRing V] [IsDomain V] (φ : R →+* V) (hφ : Function.Injective φ) :
    Function.Injective ((algebraMap V (FractionRing V)).comp φ) := by
  rw [RingHom.coe_comp]; exact (IsFractionRing.injective V (FractionRing V)).comp hφ

theorem integral_with_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (σ : SecAt t.G t.PP.L χ) (e : Fin N → FractionRing R), Odd m → 3 ≤ m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ) → NZ t.G t.PP.L χ σ → SymAt t.G t.PP.L t.PP.rig m (spMap (algebraMap R (FractionRing R)) ≫ χ) (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) e → ∃ e' : Fin N → R, (∀ j, algebraMap R (FractionRing R) (e' j) = e j) ∧ ∃ j, IsUnit (e' j) := by
  intro E _ _ _ H S t g m N R _ _ _ _ _ _ χ σ e hm hm3 hmu hN hP hNZ hS
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V)
      (hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ)), ∃ eV : Fin N → V,
        (∀ j, algebraMap V (FractionRing V) (eV j) = IsFractionRing.lift hg (e j)) ∧ ∃ j, IsUnit (eV j) := by
    intro V _ _ _ hV φ hg
    have h₀ : (IsFractionRing.lift (K := FractionRing R) hg).comp (algebraMap R (FractionRing R)) =
        (algebraMap V (FractionRing V)).comp φ := by
      ext r
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    exact at_cdvr E H S t g m N R χ σ e hm hm3 hmu hN hP hNZ hS V hV φ _ h₀
  have hint : ∀ j, ∃ r : R, algebraMap R (FractionRing R) r = e j := by
    intro j
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) (e j)
    change IsLocalization.mk' (FractionRing R) a b = e j at hab
    have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have hdvd : (b : R) ∣ a := GlobalTheory.T.dvd_of_dvd_in_all_completeDVR_normal_noetherian R a b hb0 fun V _ _ _ hV φ hφ => by
      obtain ⟨eV, he, -⟩ := key V hV φ (comp_inj φ hφ)
      refine ⟨eV j, ?_⟩
      apply IsFractionRing.injective V (FractionRing V)
      have h1 := he j
      rw [← hab, IsFractionRing.lift_mk'] at h1
      have hb' : ((algebraMap V (FractionRing V)).comp φ) (b : R) ≠ 0 :=
        fun h => hb0 ((comp_inj φ hφ) (h.trans (map_zero _).symm))
      rw [eq_div_iff hb'] at h1
      simp only [RingHom.comp_apply] at h1
      rw [map_mul, ← h1, mul_comm]
    obtain ⟨r, hr⟩ := hdvd
    refine ⟨r, ?_⟩
    rw [← hab, hr, IsLocalization.mk'_mul_cancel_left]
  choose e' he' using hint
  refine ⟨e', he', ?_⟩
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨eV, he, j, hu⟩ := key V hV φ (comp_inj φ hφ)
  have hj : φ (e' j) = eV j := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [he j, ← he' j, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  refine ⟨j, (isUnit_map_iff φ _).1 ?_⟩
  rw [hj]; exact hu

end GlobalTheory.UMin.IntTheta
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fs_box_rank_le : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J]
    (e : J → X.functionField) (x : Fin D → X.functionField) (w : J × Finset (Fin D) → ℝ),
    LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, 0 ≤ w c) →
    IsFS M (boxFam e x) w → (D.factorial : ℝ) * Fintype.card J ≤ gdeg M D := by
  intro hAr hHS k _ X _ p D hD M J _ e x w he hx hw hFS
  have hNef : M.IsNef D := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hAr k X p D hD M _ (boxFam e x) w hFS hw
  obtain ⟨P, hPL, hmem⟩ := GlobalTheory.T.isFubiniStudy_ratFns_mem_pairSections k X p M _ (boxFam e x) w hFS
  subst hPL
  exact GlobalTheory.T.rank_le_geometricDegree_of_isNef hAr hHS k X p D hD P hNef J e x he hx hmem

end GlobalTheory.HSNef
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem isTopForm_mul_topDens : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {ρ : CxPts X.str σ → ℝ}, Continuous ρ → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) := by
  intro F _ σ X m E O H hM ρ hρ
  refine ⟨?_, ?_⟩
  · intro c c' y hy hc hc'
    have hA := (E.nonempty (under y)).choose_spec
    simp only [topDens]
    rw [chernTop_frame_chart_trans E O H hM _ hy c c' hc hc' hA hA]
    ring
  · intro c
    refine GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density c.e (d := fun z => ρ z * topDens E H c z) (isOpen_ptsIn O) ?_
    intro y hy hc
    have hA := (E.nonempty (under y)).choose_spec
    refine ⟨fun v => ρ (c.e.symm v) * chernTop (MvPolynomial.X ((), X.dim))
      (fun w => H (E.nonempty (under y)).choose (c.e.symm w)) v, ?_, ?_⟩
    · have h1 : ContinuousAt (fun v => ρ (c.e.symm v)) (c.e y) :=
        hρ.continuousAt.comp (c.e.continuousAt_symm (c.e.map_source hc))
      have hsm := hM.mContDiffAt_chart hy c hc hA ()
      have hu := hM.isUnit_det_chart hy c hc hA ()
      have h2 : ContinuousAt (fun v => chernTop (MvPolynomial.X ((), X.dim))
          (fun w => H (E.nonempty (under y)).choose (c.e.symm w)) v) (c.e y) := by
        simp only [GlobalTheory.T.chernTopDensity_eq_polarisedTopChern]
        refine continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_)
        refine GlobalTheory.T.continuousAt_polarisedTopChernCoeff (fun i a b p q => ?_)
        exact ((MContDiffAt.curv (j := 0) hsm hu (by norm_num) (coordVec a) (coordVec b)) p q).continuousAt
      exact h1.mul h2
    · filter_upwards [(isOpen_ptsIn O).mem_nhds hy, c.e.open_source.mem_nhds hc,
        GlobalTheory.FrameLift.eventually_mem hA] with z hz hzc hzA
      simp only [topDens, c.e.left_inv hzc]
      rw [hM.chernTop_frame _ hz c hzc (E.nonempty (under z)).choose_spec hzA]

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.transgression_correction_isTopDegreeForm : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) := by
  first | exact @GlobalTheory.GoodTop.isTopForm_corrDens | exact GlobalTheory.GoodTop.isTopForm_corrDens | (intros; apply GlobalTheory.GoodTop.isTopForm_corrDens <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem topDens_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ (c : AlgChart X.str σ X.dim) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → y ∈ c.e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → (Real.pi ^ X.dim)⁻¹ * (mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) (e y)).re = ‖transDet e c.e y‖ ^ 2 * topDens E H c y := by
  intro F _ σ X m E O H hM e he c y hy hye hyc A hA
  set G : V X.dim → Matrix (Fin m) (Fin m) ℂ := fun u => H A (c.e.symm u) () with hG
  set φ : V X.dim → V X.dim := c.e ∘ e.symm with hφ
  have ho := isOpen_over e c.e.open_source
  have hm := mem_over e hye hyc
  have hdiff : DifferentiableOn ℂ φ (e.target ∩ e.symm ⁻¹' c.e.source) := holoChart_trans_algChart he c
  have han : AnalyticAt ℂ φ (e y) := GlobalTheory.InjHol.analyticAt_of_differentiableOn_euclidean ho hm hdiff
  have hφy : φ (e y) = c.e y := by simp only [hφ, Function.comp_apply, e.left_inv hye]
  have hG2 : MContDiffAt 2 G (φ (e y)) := hφy ▸ hM.mContDiffAt_chart hy c hyc hA ()
  have hGu : IsUnit (G (φ (e y))).det := hφy ▸ hM.isUnit_det_chart hy c hyc hA ()
  have hger : (fun v => H A (e.symm v) ()) =ᶠ[𝓝 (e y)] fun v => G (φ v) := by
    filter_upwards [ho.mem_nhds hm] with w hw
    simp only [hG, hφ, Function.comp_apply, c.e.left_inv hw.2]
  have hcurv : curvAt (fun v => H A (e.symm v) ()) (e y) = curvAt (fun v => G (φ v)) (e y) := by
    funext a b
    exact curv_congr hger _ _
  have key := GlobalTheory.T.polarisedTopChernCoeff_curvature_comp_holomorphic (G := G) (φ := φ) (w := e y) (han.contDiffAt) hG2 hGu
  rw [hcurv, key, hφy]
  have hfr : topDens E H c y = chernTop (MvPolynomial.X ((), X.dim)) (fun v => H A (c.e.symm v)) (c.e y) :=
    hM.chernTop_frame _ hy c hyc (E.nonempty (under y)).choose_spec hA
  rw [hfr, GlobalTheory.T.chernTopDensity_eq_polarisedTopChern, transDet, Complex.re_ofReal_mul]
  ring

end GlobalTheory.GoodTop
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem finrank_ratF_eq_gdeg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (Module.finrank (ratF x) X.functionField : ℝ) = (e : ℝ) ^ D * gdeg P.L D := by
  intro hA k _ X _ p D hX P hamp e x hg
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  obtain ⟨hI, π, hπ, hgen, hr0, hr, hiso⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hamp e x hg
  obtain ⟨B, -, hB⟩ := GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference k X p D hX P e x hg
  obtain ⟨u, hu, -⟩ := hB 1 le_rfl
  have h1 := (hiso u hu).gdeg_eq D
  obtain ⟨hPV, hdeg, hcard⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D
  have h2 := (GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow hA k (PSpace k D) (PSpace.str k D) D hPV).1 X p hX π hπ hgen hr0 (ProjSpace.hermitianTwistingSheaf k D)
  have h3 : gdeg ((up P.L u).pow e) D = (e : ℝ) ^ D * gdeg (up P.L u) D :=
    GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow k X p D hX (up P.L u) e fun _ _ => 1
  have h4 := GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hA k X p D hX P.L u
  rw [← hr]
  push_cast
  rw [← hcard, ← hdeg, ← h2, ← h1, h3, h4]

end GlobalTheory.HSAmp
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv G), (∀ x, Δ'.mult x = Δ.mult (j x)) → ∀ (N : MLine p (τ.comp (algebraMap k K))) (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f g : CxPts p (τ.comp (algebraMap k K)) → ℝ), side (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) (fun y => g (bcPt hp.w τ y)) Δ' = side N L f g Δ := by
  first | exact @GlobalTheory.Mix.side_bc_eq | exact GlobalTheory.Mix.side_bc_eq | (intros; apply GlobalTheory.Mix.side_bc_eq <;> assumption)
end
