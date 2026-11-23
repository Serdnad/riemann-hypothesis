module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle056
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle002
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle022
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle010
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.EigenspaceComposition

theorem epi_spMap {K L : Type} [Field K] [Field L] (a : K →+* L) : Epi (spMap a) := by
  apply GlobalTheory.CompanionTheory.Ar.HtEnd.epiSp <;> assumption

theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (Y : Over S) :
    (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

end PositivityTheory.Xgf.EigenspaceComposition

namespace PositivityTheory.Xgf

private theorem isTanAt_base_change_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] {F F' : Type} [Field F] [Field F']
    (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (hx : x' = spMap f ≫ x)
    (w : epsAt x ⟶ G) (w' : epsAt x' ⟶ G) (hw : w'.left = spMap (dualMap f) ≫ w.left) :
    IsTanAt G x' w' ↔ IsTanAt G x w := by
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F' F' F').toRingHom) ≫ spMap (dualMap f) =
      spMap f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F F F).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    simp [dualMap]
  haveI := EigenspaceComposition.epi_spMap f
  show _ = (1 : Over.mk x' ⟶ G).left ↔ _ = (1 : Over.mk x ⟶ G).left
  rw [EigenspaceComposition.one_left', EigenspaceComposition.one_left', hw, ← Category.assoc, key, Category.assoc]
  simp only [Over.mk_hom, hx, Category.assoc]
  constructor
  · intro h
    exact (cancel_epi (spMap f)).mp h
  · intro h
    rw [h]

open PositivityTheory.Xgf.EigenspaceComposition in
theorem tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  intro E _ _ _ H S t F F' _ _ f x x' τ n v hx'
  have hcomp : ∀ w : epsAt x ⟶ t.G, ∃ w' : epsAt x' ⟶ t.G, w'.left = spMap (dualMap f) ≫ w.left := by
    intro w
    refine ⟨Over.homMk (spMap (dualMap f) ≫ w.left) ?_, rfl⟩
    rw [Category.assoc, Over.w w]
    simp only [epsAt, Over.mk_hom, hx', spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    apply RingHom.ext
    intro a
    simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨⟨fun k => Classical.choose (hcomp (v k)), fun k => Classical.choose_spec (hcomp (v k))⟩, ?_⟩
  intro v' hv'
  have htan : ∀ k, IsTanAt t.G x' (v' k) ↔ IsTanAt t.G x (v k) :=
    fun k => isTanAt_base_change_iff t.G f x x' hx' (v k) (v' k) (hv' k)
  by_cases hT : ∀ k, IsTanAt t.G x (v k)
  · obtain ⟨N, M, ρ, hρ, hbc⟩ := lie_model_action_base_change E H S t F x
    obtain ⟨M', ρ', hρ', hpt, hc⟩ := hbc F' f x' hx'
    choose u hu using fun k => M.onto (v k) (hT k)
    have hv'eq : v' = fun k => M'.pt (f ∘ u k) := by
      funext k
      apply Over.OverMorphism.ext
      rw [hv' k, hpt, hu k]
    have hveq : v = fun k => M.pt (u k) := funext fun k => (hu k).symm
    rw [hv'eq, hveq, ((lie_model_eigenvectors_action S F t.G x _ M).2 _ t.act ρ τ hρ).2 n u,
      ((lie_model_eigenvectors_action S F' t.G x' _ M').2 _ t.act ρ' (f.comp τ) hρ').2 n (fun k => f ∘ u k)]
    exact EigenspaceComposition.core (τ := τ) hc u
  · push_neg at hT
    obtain ⟨k, hk⟩ := hT
    constructor
    · intro h
      exact absurd (h.1 k).1 hk
    · intro h
      exact absurd ((htan k).1 (h.1 k).1) hk

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.exists_local_basis_cm_order

section Gen

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ℓ : ℕ) (hℓ : ℓ.Prime)

def primeTo : Submonoid R where
  carrier := {r | ∃ n : ℕ, ¬ ℓ ∣ n ∧ r = (n : R)}
  one_mem' := ⟨1, hℓ.not_dvd_one, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, fun h => (hℓ.dvd_mul.1 h).elim ha hb, by push_cast; ring⟩

theorem primeTo_le : primeTo R ℓ hℓ ≤ nonZeroDivisors R := by
  rintro _ ⟨n, hn, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  have : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  exact_mod_cast this

theorem finite_primes [IsDedekindDomain R] [Module.Finite ℤ R] :
    {I : Ideal (Localization (primeTo R ℓ hℓ)) | I.IsPrime}.Finite := by
  have hint : ∀ P : Ideal R, P.IsPrime → Disjoint (primeTo R ℓ hℓ : Set R) P → P ≠ ⊥ → Ideal.span {(ℓ : R)} ≤ P := by
    intro P hP hdis hne
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hc := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) hx0 hxP (Algebra.IsIntegral.isIntegral x)
    obtain ⟨m, hmP, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
    have hN : ((m.natAbs : ℕ) : R) ∈ P := by
      rw [Ideal.mem_comap] at hmP
      rcases Int.natAbs_eq m with h | h
      · rw [h] at hmP
        simpa using hmP
      · rw [h] at hmP
        have := P.neg_mem_iff.mpr hmP
        simpa using this
    obtain ⟨e, n, hn, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hm0) ℓ hℓ.one_lt.ne'
    rw [hmn, Nat.cast_mul, Nat.cast_pow] at hN
    rcases hP.mem_or_mem hN with h | h
    · rw [Ideal.span_singleton_le_iff_mem]
      exact hP.mem_of_pow_mem _ h
    · exact absurd h (Set.disjoint_left.mp hdis ⟨n, hn, rfl⟩)
  have hfree : Module.Free ℤ R := Module.free_of_finite_type_torsion_free'
  have hℓ0 : Ideal.span {(ℓ : R)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ.ne_zero
  haveI := Ideal.finiteQuotientOfFreeOfNeBot _ hℓ0
  have hfinI : Finite (Ideal (R ⧸ Ideal.span {(ℓ : R)})) :=
    Finite.of_injective (fun I : Ideal (R ⧸ Ideal.span {(ℓ : R)}) => (I : Set (R ⧸ Ideal.span {(ℓ : R)}))) SetLike.coe_injective
  have hfinU : {P : Ideal R | Ideal.span {(ℓ : R)} ≤ P}.Finite := by
    refine (Set.finite_range (fun K : Ideal (R ⧸ Ideal.span {(ℓ : R)}) => K.comap (Ideal.Quotient.mk _))).subset ?_
    intro P hP
    refine ⟨P.map (Ideal.Quotient.mk _), ?_⟩
    simp only
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hP
  refine ((hfinU.insert ⊥).image (fun P => P.map (algebraMap R (Localization (primeTo R ℓ hℓ))))).subset ?_
  intro Q hQ
  have hQ' := (IsLocalization.isPrime_iff_isPrime_disjoint (primeTo R ℓ hℓ) _ Q).mp hQ
  refine ⟨Ideal.under R Q, ?_, IsLocalization.map_under (primeTo R ℓ hℓ) _ Q⟩
  by_cases h0 : Ideal.under R Q = ⊥
  · exact Or.inl h0
  · exact Or.inr (hint _ hQ'.1 hQ'.2 h0)


include hℓ in
theorem locBasis [IsDedekindDomain R] [Module.Finite ℤ R] {M : Type} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : ∃ (g : ℕ) (b : Fin g → M), IsLocBasis R ℓ b := by
  classical
  haveI : IsDomain (Localization (primeTo R ℓ hℓ)) := IsLocalization.isDomain_localization (primeTo_le R ℓ hℓ)
  haveI : IsDedekindDomain (Localization (primeTo R ℓ hℓ)) := IsLocalization.isDedekindDomain R (primeTo_le R ℓ hℓ) _
  haveI : IsPrincipalIdealRing (Localization (primeTo R ℓ hℓ)) := IsPrincipalIdealRing.of_finite_primes (finite_primes R ℓ hℓ)
  haveI : Module.Finite (Localization (primeTo R ℓ hℓ)) (LocalizedModule (primeTo R ℓ hℓ) M) :=
    Module.Finite.of_isLocalizedModule (primeTo R ℓ hℓ) (LocalizedModule.mkLinearMap (primeTo R ℓ hℓ) M)
  haveI : Module.Free (Localization (primeTo R ℓ hℓ)) (LocalizedModule (primeTo R ℓ hℓ) M) := Module.free_of_finite_type_torsion_free'
  have hinj : Function.Injective (algebraMap R (Localization (primeTo R ℓ hℓ))) :=
    IsLocalization.injective _ (primeTo_le R ℓ hℓ)
  haveI : FaithfulSMul R (Localization (primeTo R ℓ hℓ)) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  set f := LocalizedModule.mkLinearMap (primeTo R ℓ hℓ) M with hf
  set v := Module.finBasis (Localization (primeTo R ℓ hℓ)) (LocalizedModule (primeTo R ℓ hℓ) M) with hv
  choose q hq using fun i => IsLocalizedModule.mk'_surjective (primeTo R ℓ hℓ) f (v i)
  have hu : ∀ i, IsUnit (algebraMap R (Localization (primeTo R ℓ hℓ)) ((q i).2 : R)) :=
    fun i => IsLocalization.map_units _ (q i).2
  have hfb : ∀ i, f (q i).1 = (hu i).unit • v i := by
    intro i
    rw [Units.smul_def, IsUnit.unit_spec, algebraMap_smul, ← hq i]
    exact (IsLocalizedModule.mk'_cancel' f _ _).symm
  have hfb' : ⇑f ∘ (fun i => (q i).1) = (fun i => (hu i).unit) • ⇑v := by
    funext i
    exact hfb i
  have hliL : LinearIndependent (Localization (primeTo R ℓ hℓ)) (⇑f ∘ fun i => (q i).1) := by
    rw [hfb']
    exact v.linearIndependent.units_smul _
  have hliR : LinearIndependent R (fun i => (q i).1) :=
    LinearIndependent.of_comp f (hliL.restrict_scalars' R)
  have hspan : Submodule.span (Localization (primeTo R ℓ hℓ)) (Set.range (⇑f ∘ fun i => (q i).1)) = ⊤ := by
    rw [eq_top_iff, ← v.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : v i = (hu i).unit⁻¹ • f (q i).1 := by
      rw [hfb i, inv_smul_smul]
    rw [h1]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hpt : ∀ y : M, ∃ t : primeTo R ℓ hℓ, (t : R) • y ∈ Submodule.span R (Set.range fun i => (q i).1) := by
    intro y
    have hy : f y ∈ Submodule.localized' (Localization (primeTo R ℓ hℓ)) (primeTo R ℓ hℓ) f
        (Submodule.span R (Set.range fun i => (q i).1)) := by
      rw [Submodule.localized'_span, ← Set.range_comp, hspan]
      trivial
    obtain ⟨m0, hm0, s0, hs0⟩ := (Submodule.mem_localized' _ _ f _ _).mp hy
    rw [IsLocalizedModule.mk'_eq_iff] at hs0
    have h2 : f m0 = f (s0 • y) := by
      rw [hs0, Submonoid.smul_def, Submonoid.smul_def, map_smul]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := primeTo R ℓ hℓ) h2
    refine ⟨c * s0, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← Submonoid.smul_def, ← hc, Submonoid.smul_def]
    exact Submodule.smul_mem _ _ hm0
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  choose t ht using fun j => hpt (g j)
  choose nn hnn hnn' using fun j => (t j).2
  refine ⟨_, fun i => (q i).1, hliR, ∏ j, nn j, ?_, ?_⟩
  · intro h
    obtain ⟨j, -, hj⟩ := (hℓ.prime.dvd_finsetProd_iff _).mp h
    exact hnn j hj
  · intro y
    have hy : y ∈ Submodule.span R (Set.range g) := by
      rw [hg]
      trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_comm, mul_smul, ← Nat.cast_smul_eq_nsmul R (nn j), ← hnn' j]
      exact Submodule.smul_of_tower_mem _ _ (ht j)
    | zero => simp
    | add x z _ _ hx hz =>
      rw [smul_add]
      exact add_mem hx hz
    | smul r x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ _ hx


include hℓ in
theorem locBasis' [IsDedekindDomain R] [Module.Finite ℤ R] {M : Type} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : ∃ b : Fin (Module.finrank R M) → M, IsLocBasis R ℓ b := by
  obtain ⟨g, b, hli, n, hn, hsp⟩ := locBasis R ℓ hℓ (M := M)
  have hn0 : (n : R) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact hn (dvd_zero ℓ)
    exact_mod_cast this
  have hmem : ∀ y : M, (n : R) • y ∈ Submodule.span R (Set.range b) := by
    intro y
    rw [Nat.cast_smul_eq_nsmul]
    exact hsp y
  have h1 : Module.finrank R (Submodule.span R (Set.range b)) = g := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have h2 := Submodule.finrank_le (Submodule.span R (Set.range b))
  have hinj : Function.Injective ((n : R) • LinearMap.id : M →ₗ[R] M) := by
    intro x y hxy
    exact smul_right_injective M hn0 hxy
  have h3 := LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.codRestrict (Submodule.span R (Set.range b)) ((n : R) • LinearMap.id) hmem)
    (by
      intro x y hxy
      apply hinj
      simpa using congrArg Subtype.val hxy)
  have hg : g = Module.finrank R M := by omega
  subst hg
  exact ⟨b, hli, n, hn, hsp⟩

end Gen

end GlobalTheory.CompanionTheory.Ar.Fl.exists_local_basis_cm_order

namespace PositivityTheory.Xgf

theorem exists_local_basis_cm_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : ℕ), ℓ.Prime → ∃ (f : ℕ) (b : Fin f → 𝓞 E), 2 * f = Module.finrank ℚ E ∧ IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b := by
  classical
  intro E _ _ _ H ℓ hℓ
  obtain ⟨hD, hrep, -, -, hrank, hproj⟩ := CM.OK_isDedekindDomain_and_projective E H
  haveI := hD
  haveI := (hproj (𝓞 E) (Module.Finite.self (𝓞 E)) inferInstance).1
  haveI : Module.Finite ℤ (CM.OK H) := by
    refine ⟨⟨({1, CM.wK H} : Finset (CM.OK H)), ?_⟩⟩
    rw [eq_top_iff]
    intro a _
    obtain ⟨⟨m1, m2⟩, hm, -⟩ := hrep a
    rw [hm]
    refine add_mem ?_ ?_
    · rw [← zsmul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [← zsmul_eq_mul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.Ar.Fl.exists_local_basis_cm_order.locBasis' (CM.OK H) ℓ hℓ (M := 𝓞 E)
  exact ⟨_, b, hrank, hb⟩

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem curve_z_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (Z : Curve0 H ρ), Z.z ≠ 0 := by
  intro E _ _ _ H ρ Z hz
  obtain ⟨Hm, χ, Ef, -, -, hT2, -⟩ := Z.theta
  have hd : Z.u.IsDiff 0 Z.C'.v := by
    have h := Z.diff
    rw [hz, mul_zero] at h
    exact h
  have ht : IsTangent Z.C'.v := Z.C'.basis.1 0
  have h1 : IsTangent (1 : epsR ℂ ⟶ Z.C'.P.A) := (ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).1 ReciprocityTheory.ChartRestriction.G.Chart.isTan_one
  have hd1 : Z.u.IsDiff 0 (1 : epsR ℂ ⟶ Z.C'.P.A) := GlobalTheory.UnifDifferential.isDiff_one Z.u
  have e : Z.C'.v = 1 := (hT2 0).unique ⟨ht, hd⟩ ⟨h1, hd1⟩
  have hb := Z.C'.basis.2 Z.C'.v ht
  have c0 : IsLieComb ![(0 : ℂ)] ![Z.C'.v] Z.C'.v := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff, ReciprocityTheory.ChartRestriction.G.Chart.prodPts, e]
    simp
  have c1 : IsLieComb ![(1 : ℂ)] ![Z.C'.v] Z.C'.v := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff, ReciprocityTheory.ChartRestriction.G.Chart.prodPts]
    simp only [Matrix.cons_val_fin_one, ReciprocityTheory.ChartRestriction.G.Chart.scaleD_one, ReciprocityTheory.ChartRestriction.G.Chart.spMap_id,
      Category.id_comp, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
    exact (_root_.mul_one _).symm
  have h01 := congrFun (hb.unique c0 c1) 0
  simp at h01

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rt_cases (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
  simp at this
  rw [H.sqrt_neg_disc_sq, ← this]

theorem exists_emb (b : Bool) : ∃ τ : E →+* ℂ, τ (H.rt : E) = (if b then H.rt0 else -H.rt0) := by
  cases b
  · exact GlobalTheory.CM.LatData.exists_embedding H (by simp [H.sqrt_neg_disc_sq])
  · exact GlobalTheory.CM.LatData.exists_embedding H H.sqrt_neg_disc_sq

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)

def eP (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) : {k // ty k = τ} ≃ Fin p :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_eq_nat_card]; exact (hty τ).1 h)

def eQ (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) : {k // ty k = τ} ≃ Fin q :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_eq_nat_card]; exact (hty τ).2 h)

def blk (k : Fin g) : Fin p ⊕ Fin q :=
  if h : ty k (H.rt : E) = H.rt0 then .inl (eP hty (ty k) h ⟨k, rfl⟩) else .inr (eQ hty (ty k) h ⟨k, rfl⟩)

theorem blk_inl (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) (k : Fin g) (hk : ty k = τ) :
    blk hty k = .inl (eP hty τ h ⟨k, hk⟩) := by
  subst hk
  simp [blk, h]

theorem blk_inr (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) (k : Fin g) (hk : ty k = τ) :
    blk hty k = .inr (eQ hty τ h ⟨k, hk⟩) := by
  subst hk
  simp [blk, h]

variable {D : Datum H} (c : D.La →ₗ[𝓞 E] (Fin p ⊕ Fin q →₀ 𝓞 E)) (n : ℕ)

def per : D.La →+ (Fin g → ℂ) where
  toFun y k := ty k ((c y (blk hty k) : 𝓞 E) : E) / n
  map_zero' := by funext k; simp
  map_add' y y' := by funext k; simp [add_div]

theorem per_apply (y : D.La) (k : Fin g) : per hty c n y k = ty k ((c y (blk hty k) : 𝓞 E) : E) / n := rfl

theorem per_smul (a : 𝓞 E) (y : D.La) (k : Fin g) : per hty c n (a • y) k = ty k (a : E) * per hty c n y k := by
  simp [per_apply, mul_div_assoc]

theorem per_inl (y : D.La) (a : Fin p) (hc : c y = Finsupp.single (.inl a) (n : 𝓞 E)) (k : Fin g)
    (hk : ty k (H.rt : E) ≠ H.rt0) : per hty c n y k = 0 := by
  rw [per_apply, hc, blk_inr hty (ty k) hk k rfl]
  simp

theorem per_inr (y : D.La) (b : Fin q) (hc : c y = Finsupp.single (.inr b) (n : 𝓞 E)) (k : Fin g)
    (hk : ty k (H.rt : E) ≠ -H.rt0) : per hty c n y k = 0 := by
  have h : ty k (H.rt : E) = H.rt0 := (rt_cases (ty k)).resolve_right hk
  rw [per_apply, hc, blk_inl hty (ty k) h k rfl]
  simp

theorem coef_zero_of_per (hn : 0 < n) (y : D.La) (h : per hty c n y = 0) : c y = 0 := by
  ext m
  cases m with
  | inl a =>
    obtain ⟨τ, hτ⟩ := exists_emb (H := H) true
    simp only [if_true] at hτ
    let k := ((eP hty τ hτ).symm a).1
    have hk : ty k = τ := ((eP hty τ hτ).symm a).2
    have hb : blk hty k = .inl a := by
      rw [blk_inl hty τ hτ k hk]
      simp [k]
    have h1 := congrFun h k
    rw [per_apply, hb] at h1
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Pi.zero_apply, div_eq_zero_iff, or_iff_left hn', map_eq_zero] at h1
    simpa using h1
  | inr b =>
    obtain ⟨τ, hτ⟩ := exists_emb (H := H) false
    simp only [Bool.false_eq_true, if_false] at hτ
    have hτ' : τ (H.rt : E) ≠ H.rt0 := by rw [hτ]; exact fun h => Host_rt0_ne_neg (H := H) h.symm
    let k := ((eQ hty τ hτ').symm b).1
    have hk : ty k = τ := ((eQ hty τ hτ').symm b).2
    have hb : blk hty k = .inr b := by
      rw [blk_inr hty τ hτ' k hk]
      simp [k]
    have h1 := congrFun h k
    rw [per_apply, hb] at h1
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Pi.zero_apply, div_eq_zero_iff, or_iff_left hn', map_eq_zero] at h1
    simpa using h1

end PositivityTheory.Xgf.DPer

end
end
