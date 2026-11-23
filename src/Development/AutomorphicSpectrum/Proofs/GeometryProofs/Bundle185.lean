module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle050
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderBaseChangeGeneric
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Mathlib.FieldTheory.Relrank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle178
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JNormal

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.KForm

section Embeddings

variable {E : Type} [Field E] [NumberField E]


open Classical in
theorem sum_dual_mul (σ τ : E →+* ℂ) :
    ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = if τ = σ then 1 else 0 := by
  let ρ : 𝓞 E →+* Module.End ℂ ℂ :=
    (Algebra.lmul ℂ ℂ).toRingHom.comp (τ.comp (algebraMap (𝓞 E) E))
  have hρ : ∀ (a : 𝓞 E) (z : ℂ), ρ a z = τ (a : E) * z := fun a z => rfl
  have hmem : (1 : ℂ) ∈ HT.eigSp ρ τ := HT.LatBasic.mem_eigSp.2 fun a => by
    rw [hρ, smul_eq_mul]
  have hP : HT.eigProj ρ σ 1 =
      ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) := by
    simp [HT.eigProj, LinearMap.sum_apply, hρ]
  rw [← hP]
  split_ifs with h
  · subst h
    exact HT.LatBasic.eigProj_of_mem hmem
  · exact HT.LatBasic.eigProj_of_ne (Ne.symm h) hmem

theorem trace_cast (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ z := by
  have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
  simpa using this

end Embeddings

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem kappa_form {ε : ℤˣ} {h : D.La → D.La → OK H} {σ : E →+* ℂ} {κ : OK H →+* ℂ}
    (hh : IsKForm D ε h) (hκ : κ (wK H) = σ (H.w0 : E)) (X Y : D.La) :
    κ (h X Y) = ((ε : ℤ) : ℂ) *
      ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) := by
  obtain ⟨hT, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D
  have e1 : h X Y = (((ε : ℤ) * (D.EF (H.w0 • X) Y - D.EF X Y) : ℤ) : OK H) +
      (((ε : ℤ) * D.EF X Y : ℤ) : OK H) * wK H := by
    apply Subtype.ext
    simpa [wK] using hh X Y
  have t1 : ((D.EF (H.w0 • X) Y : ℤ) : ℂ) =
      ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) := by
    have := congrArg (fun q : ℚ => (q : ℂ)) (hT H.w0 X Y)
    simp only [trace_cast, map_mul] at this
    rw [this]
    simp
  have t0 : ((D.EF X Y : ℤ) : ℂ) = ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) := by
    have h1 : Algebra.trace ℚ E (sesq D X Y) = (D.EF X Y : ℚ) := by simpa using hT 1 X Y
    rw [← trace_cast, h1]
    simp
  have hs : ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) =
      ∑ τ : E →ₐ[ℚ] ℂ, τ (H.w0 : E) * τ (sesq D X Y) - ∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y) +
        (∑ τ : E →ₐ[ℚ] ℂ, τ (sesq D X Y)) * σ (H.w0 : E) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_add κ, map_mul, map_intCast, map_intCast, hκ, hs]
  push_cast
  rw [t1, t0]
  ring

theorem sigma_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (σ : E →+* ℂ) (κ : OK H →+* ℂ) (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x y : D.La), IsKForm D ε h → κ (wK H) = σ (H.w0 : E) → ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * σ ((H.rt : E) * sesq D x y) := by
  classical
  intro E _ _ _ H D ε h σ κ n e x y hh hκ
  obtain ⟨-, -, -, hL, hR, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D

  have hform : ∀ a c : 𝓞 E, κ (h (a • x) (c • y)) = ((ε : ℤ) : ℂ) *
      ∑ τ : E →ₐ[ℚ] ℂ, τ (a : E) * starRingEnd ℂ (τ (c : E)) *
        (τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E))) := by
    intro a c
    rw [kappa_form hh hκ]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hc : τ (IsCMField.complexConj E (c : E)) = starRingEnd ℂ (τ (c : E)) :=
      IsCMField.complexEmbedding_complexConj E (τ : E →+* ℂ) (c : E)
    rw [hL, hR, map_mul, map_mul, hc]
    ring

  set S : (E →ₐ[ℚ] ℂ) → ℂ := fun τ =>
    ∑ k : Fin n, σ (HT.dualInt E (e k)) * τ ((RingOfIntegers.basis E (e k) : 𝓞 E) : E) with hSdef
  have hS : ∀ τ : E →ₐ[ℚ] ℂ, S τ = if (τ : E →+* ℂ) = σ then 1 else 0 := by
    intro τ
    have := sum_dual_mul σ (τ : E →+* ℂ)
    rw [← Equiv.sum_comp e] at this
    exact this
  set c : (E →ₐ[ℚ] ℂ) → ℂ := fun τ =>
    τ (sesq D x y) * (τ (H.w0 : E) - 1 + σ (H.w0 : E)) with hcdef
  have hexp : ∑ k, ∑ k', σ (HT.dualInt E (e k)) *
        κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) *
        starRingEnd ℂ (σ (HT.dualInt E (e k'))) =
      ((ε : ℤ) : ℂ) * ∑ τ : E →ₐ[ℚ] ℂ, S τ * starRingEnd ℂ (S τ) * c τ := by

    simp only [hform, hSdef, hcdef, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, Finset.sum_eq_single σ.toRatAlgHom]
  · have h1 : S σ.toRatAlgHom = 1 := by
      rw [hS]
      exact if_pos (RingHom.ext fun _ => rfl)
    have h2 : σ (H.rt : E) = 2 * σ (H.w0 : E) - 1 := by
      have h3 := congrArg (fun a : 𝓞 E => σ (algebraMap (𝓞 E) E a)) H.two_weight_eq_one_add_root
      simp only [map_mul, map_add (f := _), map_one, map_ofNat] at h3
      rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap]
      linear_combination -h3
    rw [h1, map_one, map_mul, h2]
    simp only [hcdef]
    change _ * (1 * 1 * (σ (sesq D x y) * (σ (H.w0 : E) - 1 + σ (H.w0 : E)))) = _
    ring
  · intro τ _ hτ
    have h0 : S τ = 0 := by
      rw [hS]
      refine if_neg fun hc => hτ (AlgHom.ext fun z => ?_)
      exact congrArg (fun f : E →+* ℂ => f z) hc
    rw [h0]
    simp
  · intro hn
    exact absurd (Finset.mem_univ _) hn

end GlobalTheory.CompanionTheory.Ar.Fl.KForm
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_base_change_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤) ∧ Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.btOrder_baseChange
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.LieRank

variable {S : Scheme.{0}}

theorem dualMap_apply {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (a : DualNumber R) :
    dualMap c a = TrivSqZeroExt.inl (c a.fst) + TrivSqZeroExt.inr (c a.snd) := rfl

theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    (dualMap c).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp c := by
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, map_zero, TrivSqZeroExt.inr_zero, add_zero]

theorem fst_comp_dualMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  change (dualMap c a).fst = c a.fst
  simp [dualMap_apply]

theorem dualMap_comp_epsMul {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (r : R) :
    (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
  refine RingHom.ext fun a => ?_
  change dualMap c (TrivSqZeroExt.map (r • (LinearMap.id : R →ₗ[R] R)) a) =
    TrivSqZeroExt.map (c r • (LinearMap.id : R' →ₗ[R'] R')) (dualMap c a)
  ext <;> simp [dualMap_apply, mul_comm]

def epsPull {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (x : Sp R ⟶ S) :
    epsAt (spMap c ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap c)) (by
    change spMap (dualMap c) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap c ≫ x
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (dualMap_comp_algebraMap c))

theorem one_left_pull (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) :
    (1 : Over.mk (spMap c ≫ x) ⟶ G).left = spMap c ≫ (1 : Over.mk x ⟶ G).left := by
  have h := MonObj.comp_one (Over.homMk (spMap c) rfl : Over.mk (spMap c ≫ x) ⟶ Over.mk x) (M := G)
  exact (congrArg (fun k => k.left) h).symm

theorem isTanAt_pull (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    IsTanAt G (spMap c ≫ x) (epsPull c x ≫ v) := by
  unfold IsTanAt at hv ⊢
  rw [one_left_pull, ← hv]
  change _ ≫ spMap (dualMap c) ≫ v.left = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (by
    refine RingHom.ext fun a => ?_
    exact (RingHom.congr_fun (fst_comp_dualMap c) a))

theorem epsPull_comp_left (G : Over S) {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) (v : epsAt x ⟶ G) : (epsPull c x ≫ v).left = spMap (dualMap c) ≫ v.left := by
  simp [epsPull]

theorem exists_lift (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (x : Sp R ⟶ S) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] [Module R E']
    [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') :
    ∃ j : E →ₗ[R] E', ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := by
  have hex : ∀ e, ∃ e', M'.pt e' = epsPull (algebraMap R R') x ≫ M.pt e := fun e =>
    M'.onto _ (isTanAt_pull G _ x _ (M.tan e))
  choose f hf using hex
  have hadd : ∀ a b, f (a + b) = f a + f b := fun a b => by
    apply M'.inj
    rw [M'.add, hf, hf, hf, M.add, MonObj.comp_mul]
  have hsmul : ∀ (r : R) a, f (r • a) = r • f a := fun r a => by
    apply M'.inj
    apply Over.OverMorphism.ext
    rw [← algebraMap_smul R' r (f a), M'.smul, hf, hf, epsPull_comp_left, epsPull_comp_left, M.smul,
      ← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (dualMap_comp_epsMul (algebraMap R R') r)
  have hl : ∀ e, ((M'.pt (f e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := fun e => by
    rw [hf, Category.comp_id, epsPull_comp_left]
  exact ⟨⟨⟨f, hadd⟩, hsmul⟩, hl⟩

theorem finrank_of_isBaseChange {A F : Type} [CommRing A] [Field F] [Algebra A F] {E E' : Type} [AddCommGroup E]
    [Module A E] [AddCommGroup E'] [Module F E'] [Module A E'] [IsScalarTower A F E'] [Module.Finite A E]
    [Module.Projective A E] (j : E →ₗ[A] E') (hj : IsBaseChange F j) (p : PrimeSpectrum F) :
    Module.finrank F E' = Module.rankAtStalk E (PrimeSpectrum.comap (algebraMap A F) p) := by
  rw [← Module.rankAtStalk_baseChange (S := F) (M := E) p]
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact (LinearEquiv.finrank_eq hj.equiv).symm

theorem finrank_eq_of_isBaseChange_fractionRing {D L : Type} [CommRing D] [IsDomain D] [Field L] [Algebra D L]
    [IsFractionRing D L] {E E' : Type} [AddCommGroup E] [Module D E] [AddCommGroup E'] [Module L E'] [Module D E']
    [IsScalarTower D L E'] (j : E →ₗ[D] E') (hj : IsBaseChange L j) :
    Module.finrank D E = Module.finrank L E' := by
  have : IsLocalizedModule (nonZeroDivisors D) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors D) L j).2 hj
  have h1 := IsLocalizedModule.rank_eq (nonZeroDivisors D) le_rfl j
  have h2 := IsLocalization.rank_eq L (N := E') (nonZeroDivisors D) le_rfl
  simp only [Module.finrank, h1, h2]

end GlobalTheory.CompanionTheory.Ar.LieRank

namespace GlobalTheory.CompanionTheory.Ar.LieRank

theorem exists_factor {X : Scheme.{0}} {A F : Type} [CommRing A] [Field F] (i₀ : Sp A ⟶ X) [IsOpenImmersion i₀]
    (y : Sp F ⟶ X) (h : genPt y ∈ Set.range i₀) : ∃ φ : A →+* F, spMap φ ≫ i₀ = y := by
  have hr : Set.range y ⊆ Set.range i₀ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    rw [hp]
    exact h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom, ?_⟩
  have e : spMap (Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom = IsOpenImmersion.lift i₀ y hr :=
    Spec.map_preimage _
  rw [e]
  exact IsOpenImmersion.lift_fac i₀ y hr

theorem genPt_comp {X : Scheme.{0}} {A F : Type} [CommRing A] [Field F] (i₀ : Sp A ⟶ X) (φ : A →+* F) :
    genPt (spMap φ ≫ i₀) = i₀ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint F)) := rfl

theorem finrank_fieldPt {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] {A F : Type} [CommRing A] [Field F]
    (i₀ : Sp A ⟶ S) {E Li : Type} [AddCommGroup E] [Module A E] [AddCommGroup Li] [Module F Li]
    (MA : LieModel G i₀ E) (φ : A →+* F) (M : LieModel G (spMap φ ≫ i₀) Li) :
    Module.finrank F Li = Module.rankAtStalk E (PrimeSpectrum.comap φ (IsLocalRing.closedPoint F)) := by
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective S G A i₀ E MA
  letI : Algebra A F := φ.toAlgebra
  letI : Module A Li := Module.compHom Li φ
  haveI : IsScalarTower A F Li := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := exists_lift G i₀ MA M
  exact finrank_of_isBaseChange j (GlobalTheory.T.lie_model_isBaseChange S G A F i₀ E Li MA M j hj) _

theorem finrank_eq_of_specializes {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (y₁ : Sp F₁ ⟶ X) (y₂ : Sp F₂ ⟶ X) (h : genPt y₁ ⤳ genPt y₂)
    {E₁ E₂ : Type} [AddCommGroup E₁] [Module F₁ E₁] [AddCommGroup E₂] [Module F₂ E₂]
    (M₁ : LieModel G y₁ E₁) (M₂ : LieModel G y₂ E₂) :
    Module.finrank F₁ E₁ = Module.finrank F₂ E₂ := by
  obtain ⟨U, hU, hqU, -⟩ := exists_isAffineOpen_mem_and_subset (x := genPt y₂) (U := ⊤) trivial
  have h₁U : genPt y₁ ∈ U := h.mem_open U.isOpen hqU
  have hr : Set.range hU.fromSpec = (U : Set X) := hU.range_fromSpec
  obtain ⟨φ₁, rfl⟩ := exists_factor (A := Γ(X, U)) hU.fromSpec y₁ (by rw [hr]; exact h₁U)
  obtain ⟨φ₂, rfl⟩ := exists_factor (A := Γ(X, U)) hU.fromSpec y₂ (by rw [hr]; exact hqU)
  obtain ⟨E, _, _, ⟨MA⟩⟩ := lieModel_exists X G Γ(X, U) hU.fromSpec
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective X G Γ(X, U) hU.fromSpec E MA
  haveI := Module.finitePresentation_of_projective Γ(X, U) E
  rw [finrank_fieldPt G _ MA φ₁ M₁, finrank_fieldPt G _ MA φ₂ M₂]
  rw [genPt_comp, genPt_comp] at h
  have hs := (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).1 h
  exact (hs.map (Module.isLocallyConstant_rankAtStalk (R := Γ(X, U)) (M := E)).continuous).eq

end GlobalTheory.CompanionTheory.Ar.LieRank

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_finrank_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V), Module.finrank (𝓞 L) V = Module.finrank Ω Li := by
  intro X Ω _ ξ hsp G _ _ _ Li _ _ M L _ _ z V _ _ MB
  obtain ⟨V', _, _, ⟨M'⟩⟩ := lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)
  letI : Module (𝓞 L) V' := Module.compHom V' (algebraMap (𝓞 L) L)
  haveI : IsScalarTower (𝓞 L) L V' := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := LieRank.exists_lift G z MB M'
  rw [LieRank.finrank_eq_of_isBaseChange_fractionRing j (GlobalTheory.T.lie_model_isBaseChange X G (𝓞 L) L z V V' MB M' j hj)]
  exact (LieRank.finrank_eq_of_specializes G ξ _ (hsp _) M M').symm

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

theorem _root_.GlobalTheory.T.tangent_vectors_spread_from_stalk : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (P : X) (ι : Type) [Finite ι] (e : ι → (epsAt (X.fromSpecStalk P) ⟶ G)) (f : X.presheaf.stalk P), (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G (X.fromSpecStalk P) (e i)) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (θ : R →+* X.presheaf.stalk P) (e' : ι → (epsAt x ⟶ G)) (f' : R), P ∈ x.opensRange ∧ spMap θ ≫ x = X.fromSpecStalk P ∧ θ f' = f ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (e' i)) ∧ ∀ i, (e i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e' i).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_chart_spread | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_chart_spread | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_chart_spread <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem dualMap_comp_algebraMap (c : R →+* R') :
    (dualMap c).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp c := by
  refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (c : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

theorem dualMap_comp_epsMul (c : R →+* R') (r : R) :
    (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul]
  · simp [dualMap, epsMul, mul_comm]

def epsBase (c : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap c ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap c)) (by
    change spMap (dualMap c) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap c ≫ x
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, dualMap_comp_algebraMap])

def ptBase (c : R →+* R') (x : Sp R ⟶ S) : Over.mk (spMap c ≫ x) ⟶ Over.mk x :=
  Over.homMk (spMap c) rfl

theorem isTanAt_base (G : Over S) [GrpObj G] (c : R →+* R') (x : Sp R ⟶ S) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G (spMap c ≫ x) (epsBase c x ≫ v) := by
  have h1 : (ptBase c x ≫ (1 : Over.mk x ⟶ G)) = 1 := MonObj.comp_one _
  have h2 : spMap c ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (spMap c ≫ x) ⟶ G).left := by
    rw [← h1]; rfl
  unfold IsTanAt at hv ⊢
  rw [← h2, ← hv]
  change Spec.map _ ≫ spMap (dualMap c) ≫ v.left = spMap c ≫ Spec.map _ ≫ v.left
  simp only [spMap]
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, fst_comp_dualMap]

theorem exists_isBaseChange (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type)
    [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E' : Type) [AddCommGroup E'] [Module R' E']
    [Module R E'] [IsScalarTower R R' E'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E) (M : LieModel G x E) (j : E →ₗ[R] E'),
      IsBaseChange R' j ∧ ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := by
  obtain ⟨E, iA, iM, ⟨M⟩⟩ := lieModel_exists S G R x
  have hex : ∀ e, ∃ e', M'.pt e' = epsBase (algebraMap R R') x ≫ M.pt e :=
    fun e => M'.onto _ (isTanAt_base G _ x _ (M.tan e))
  choose f hf using hex
  have hleft : ∀ e, (M'.pt (f e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := fun e => by
    rw [hf e]; rfl
  let j : E →ₗ[R] E' :=
    { toFun := f
      map_add' := fun a b => M'.inj (by
        rw [M'.add, hf, hf, hf, M.add, MonObj.comp_mul])
      map_smul' := fun r a => M'.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, ← algebraMap_smul R' r (f a), M'.smul, hleft, hleft, M.smul]
        simp only [spMap]
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← CommRingCat.ofHom_comp, dualMap_comp_epsMul])) }
  refine ⟨E, iA, iM, M, j, GlobalTheory.T.lie_model_isBaseChange S G R R' x E E' M M' j fun e => ?_, hleft⟩
  simpa only [Category.comp_id, j, LinearMap.coe_mk, AddHom.coe_mk] using hleft e

end GlobalTheory.CompanionTheory.Ar.LieBaseChange
end
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.arith_var_common_cover : ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (y₁ : (Σ k, ι₁ k) → Ω₁) (y₂ : (Σ k, ι₂ k) → Ω₂) (d : ℕ) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), IsArithVar (mCoordIdeal y₁) d → IsArithVar (mCoordIdeal y₂) d → Birational y₁ → Birational y₂ → FiniteDimensional i₁.fieldRange Ω → FiniteDimensional i₂.fieldRange Ω → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → ι₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → ι₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (y : (Σ k, ι k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), IsBlockMap κ₁ v₁ ∧ IsBlockMap κ₂ v₂ ∧ y ∘ v₁ = (fun p => i₁ (y₁ p)) ∧ y ∘ v₂ = (fun p => i₂ (y₂ p)) ∧ IsArithVar (mCoordIdeal y) d ∧ Birational y ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂ ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = Module.finrank i₁.fieldRange Ω ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) = Module.finrank i₂.fieldRange Ω :=
  @_root_.PositivityTheory.UnitarySelfGeneration.j_normal
end
