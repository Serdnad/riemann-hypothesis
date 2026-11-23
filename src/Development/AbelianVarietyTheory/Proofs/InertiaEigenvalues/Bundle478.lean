module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerGeneratorMatrixPerturbation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle145
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle178
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Formalism.SharpRestriction.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle470
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle471
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle264
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle287
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle390
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle475
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Functoriality
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle152

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

theorem _root_.GlobalTheory.T.splitPrime_place_cmType_conjugate : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hw' : w' ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host w w' → (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨ (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  first | exact @GlobalTheory.SplitType.place_type_conj | exact GlobalTheory.SplitType.place_type_conj | (intros; apply GlobalTheory.SplitType.place_type_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (r : ℕ) (a : PadicComplex l), a ∈ inC (Kinf K) → ‖a‖ < 1 → ∀ c : GQ l → Fin r → PadicComplex l, CocOn (Hinf K) (fun g y k => act g (y k)) (ball l r) c → CobOn (Hinf K) (fun g y k => act g (y k)) (ball l r) (fun g => a • c g) := by
  first | exact @GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary | exact GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary | (intros; apply GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (y : PadicComplex l), ‖y‖ ≤ 1 → ((∀ h ∈ Hinf K, act h y = y) ↔ y ∈ Ohat K) := by
  first | exact @GlobalTheory.CycInvariants.fixed_iff_mem_Ohat | exact GlobalTheory.CycInvariants.fixed_iff_mem_Ohat | (intros; apply GlobalTheory.CycInvariants.fixed_iff_mem_Ohat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cyclotomic_tower_generator_matrix_perturbation : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ (r : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)), (∀ a b, U g a b ∈ intC (Ks K j)) → (∀ a b, ‖(U g - 1) a b‖ < rho1 l) → ∀ i : ℤ, (∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) → twAct act χ i U g y = y → y = 0) ∧ ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Xj K j) → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) ∧ twAct act χ i U g y - y = (ζ - 1) • w := by
  first | exact @GlobalTheory.CycPerturb.perturbation | exact GlobalTheory.CycPerturb.perturbation | (intros; apply GlobalTheory.CycPerturb.perturbation <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.OneSubPhi

theorem one_sub_mul_onto (p : ℕ) {A : Type} [CommRing A] (φ : A →+* A)
    (hA : IsAdicComplete (Ideal.span {(p : A)}) A) (x : A) : ∃ y : A, y - (p : A) * φ y = x := by
  have hc : IsAdicComplete (Ideal.span {(p : ℤ)}) A := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := A), Ideal.map_span, Set.image_singleton, map_natCast]
    exact hA
  let f : A →ₗ[ℤ] A :=
    LinearMap.id - ((AddMonoidHom.mulLeft (p : A)).comp φ.toAddMonoidHom).toIntLinearMap
  have hf : ∀ y, f y = y - (p : A) * φ y := fun _ => rfl
  have hs : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : ℤ)}) fun G => ?_
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ G
    refine ⟨g, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hf]
    have : g - (p : A) * φ g - g = (p : ℤ) • (-φ g) := by simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨y, hy⟩ := hs x
  exact ⟨y, (hf y).symm.trans hy⟩

theorem onto_of_denom (p : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (φ : A →+* A)
    (ψ : B →+* B) (hψ : ∀ x, ψ (f x) = f (φ x)) (t : A) (ht : φ t = (p : A) * t)
    (hT : IsUnit (f t)) (hp : IsUnit (p : B))
    (h0 : ∀ x : A, ∃ y : A, y - (p : A) * φ y = x)
    (h1 : ∀ (r : ℕ) (x : A), ∃ β z : A, (p : A) * φ x = (p : A) * (φ β - (p : A) ^ r * β) + t * z)
    (r : ℕ) : ∀ (x : A) (b : B), b * f t ^ r = f x * f t → ∃ y : B, y - ψ y = b := by
  have hψT : ψ (f t) = (p : B) * f t := by rw [hψ, ht, map_mul, map_natCast]
  induction r with
  | zero =>
    intro x b hb
    obtain ⟨y, hy⟩ := h0 x
    refine ⟨f y * f t, ?_⟩
    have e := congrArg f hy
    rw [map_sub, map_mul, map_natCast] at e
    rw [map_mul, hψT, hψ]
    linear_combination f t * e - hb
  | succ r ih =>
    intro x b hb
    have hb' : b * f t ^ r = f x := hT.mul_right_cancel (by rw [← hb]; ring)
    obtain ⟨β, z, hz⟩ := h1 r x
    obtain ⟨s, hs⟩ := (hT.pow r).exists_left_inv
    obtain ⟨q, hq⟩ := (hp.pow (r + 1)).exists_left_inv
    have hψq : ψ q * (p : B) ^ (r + 1) = 1 := by
      have := congrArg ψ hq
      rwa [map_mul, map_pow, map_natCast, map_one] at this
    have eq : ψ q = q := by linear_combination q * hψq - ψ q * hq
    have hψs : ψ s * ((p : B) ^ r * f t ^ r) = 1 := by
      have := congrArg ψ hs
      rwa [map_mul, map_pow, hψT, map_one, mul_pow] at this
    obtain ⟨y, hy⟩ := ih z (f z * f t * s) (by rw [mul_assoc, hs, mul_one])
    have e1 := congrArg ψ hb'
    rw [map_mul, map_pow, hψT, hψ, mul_pow] at e1
    have e2 := congrArg f hz
    simp only [map_mul, map_add (f := _), map_sub, map_pow, map_natCast] at e2
    refine ⟨b - f β * s + q * y, ?_⟩
    rw [map_add (f := _), map_sub, map_mul, map_mul, eq, hψ]
    apply ((hp.pow (r + 1)).mul (hT.pow r)).mul_left_cancel
    linear_combination -(p : B) * e1 - e2 - (p : B) ^ (r + 1) * f β * hs + (p : B) * f (φ β) * hψs
      + f t ^ r * (y - ψ y) * hq + f t ^ r * hy + f z * f t * hs

variable {l : ℕ} [Fact l.Prime]

theorem ainf_onto (r : ℕ) (a : Per.Ainf l) : ∃ β : Per.Ainf l, Per.φA l β - (l : Per.Ainf l) ^ r * β = a := by
  obtain ⟨β, hβ⟩ := (ArtinSchreierWitt.main l).2.2 ((l : Per.Ainf l) ^ r) a
  exact ⟨β, by rw [GlobalTheory.RingBasics.φA_apply]; exact hβ⟩

theorem phiA_alg (a : Per.Ainf l) : phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem exists_w (e : Per.Fl l) (he : e.untilt = 1) : ∃ w : Per.Acris l,
    (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) := by
  obtain ⟨w, hw, -⟩ := exists_mu_pow_div l e he
  have hw0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hw1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw0
  rw [map_mul, map_natCast, map_pow, ← TFil.alg_factor] at hw1
  exact ⟨_, hw1⟩

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem mul_phi_mem (C : Core l) (x : Per.Acris l) : ∃ (a : Per.Ainf l) (z : Per.Acris l),
    (l : Per.Acris l) * phiA l x = (l : Per.Acris l) * algebraMap (Per.Ainf l) (Per.Acris l) a + C.t * z := by
  have he := core_isEps l C
  obtain ⟨t, u, ht, hu, htu⟩ := exists_isLogA l C.ε he.1
  have e1 : t = C.t := (LogFun.log_fun l C.ε C.t he.1 C.t_log).1 t ht
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨w, hw⟩ := exists_w C.ε he.1
  obtain ⟨a, z, hz⟩ := phiA_mem_ainf_add l C.ε he w hw x
  have h2 : l - 1 = l - 2 + 1 := by
    have := (Fact.out : l.Prime).two_le
    omega
  rw [h2, pow_succ] at hw
  generalize algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) = m at hw htu
  refine ⟨a, v * m ^ (l - 2) * z, ?_⟩
  rw [hz, ← e1, htu]
  linear_combination z * hw - m * m ^ (l - 2) * z * hv

end GlobalTheory.MemLoc.OneSubPhi

namespace GlobalTheory.MemLoc

theorem one_sub_phi_onto (l : ℕ) [Fact l.Prime] (C : Core l) : C.OneSubPhiOnto := by
  intro b
  obtain ⟨r, x, hx⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
  obtain ⟨hT, -, -, hl⟩ := core_t_unit_fil l C
  refine OneSubPhi.onto_of_denom l (algebraMap (Per.Acris l) (Per.Bcris l)) (phiA l) (Per.φB l)
    (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 C.t (TPhi.t_phi l C) hT hl
    (OneSubPhi.one_sub_mul_onto l (phiA l) (acris_basic l).1) (fun s y => ?_) (r + 1) x b
    (by rw [pow_succ, ← mul_assoc, hx])
  obtain ⟨a, z, hz⟩ := OneSubPhi.mul_phi_mem C y
  obtain ⟨β, hβ⟩ := OneSubPhi.ainf_onto s a
  refine ⟨algebraMap (Per.Ainf l) (Per.Acris l) β, z, ?_⟩
  rw [hz, ← hβ, OneSubPhi.phiA_alg, map_sub, map_mul, map_pow, map_natCast]

end GlobalTheory.MemLoc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per

theorem _root_.GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective : ∀ (l : ℕ) [Fact l.Prime] (c : Core l), c.TensorInj := by
  first | exact @GlobalTheory.MemLoc.TensorInj.tensorInj | exact GlobalTheory.MemLoc.TensorInj.tensorInj | (intros; apply GlobalTheory.MemLoc.TensorInj.tensorInj <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.AwayT

theorem away_of_injective {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R)
    (hu : IsUnit (algebraMap R S t))
    (hs : ∀ b : S, ∃ (r : ℕ) (x : R), b * algebraMap R S t ^ r = algebraMap R S x)
    (hi : Function.Injective (algebraMap R S)) : IsLocalization.Away t S :=
  IsLocalization.Away.mk t hu hs fun _ _ h => ⟨0, by rw [hi h]⟩

theorem lift_injective {R P S : Type} [CommRing R] [CommRing P] [CommRing S] [Algebra R P] (x : R)
    [IsLocalization.Away x P] (f : R →+* S) (g : P →+* S) (hg : ∀ a, g (algebraMap R P a) = f a)
    (hf : Function.Injective f) : Function.Injective g := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj x z
  have h1 : f a = 0 := by rw [← hg, ← ha, map_mul, hz, zero_mul]
  have h2 : a = 0 := hf (h1.trans (map_zero f).symm)
  rw [h2, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S := P) x).pow n).mul_left_eq_zero.1 ha

variable {l : ℕ} [Fact l.Prime]

theorem plusInj (C : Core l) : C.PlusInj :=
  lift_injective ((l : ℕ) : Per.Acris l) C.j C.jP C.jP_alg (crisP_injective l C.j C.j_cris)

theorem plusToB_injective (C : Core l) : Function.Injective (plusToB l) := fun x y h =>
  plusInj C ((BdRField.bdR_isField l).2.1 (by rw [← C.ι_plusToB, ← C.ι_plusToB, h]))

theorem acris_injective (C : Core l) : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) :=
  fun x y h => crisP_injective l C.j C.j_cris
    ((BdRField.bdR_isField l).2.1 (by rw [← C.ι_j, ← C.ι_j, h]))

theorem awayT (C : Core l) : C.AwayT :=
  away_of_injective C.t (core_t_unit_fil l C).1 (GlobalTheory.T.bcris_eq_acris_localization_periodT l C) (acris_injective C)

theorem plusAwayT (C : Core l) : C.PlusAwayT := by
  letI := (plusToB l).toAlgebra
  have e : ∀ x : Per.Acris l, algebraMap (BcrisP l) (Per.Bcris l) (algebraMap _ _ x) =
      algebraMap (Per.Acris l) (Per.Bcris l) x := plusToB_alg
  refine away_of_injective _ ?_ (fun b => ?_) (plusToB_injective C)
  · rw [e]
    exact (core_t_unit_fil l C).1
  · obtain ⟨r, x, h⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
    exact ⟨r, algebraMap _ _ x, by rw [e, e]; exact h⟩

theorem away_and_inj (l : ℕ) [Fact l.Prime] (C : Core l) : C.AwayT ∧ C.PlusAwayT ∧ C.PlusInj :=
  ⟨awayT C, plusAwayT C, plusInj C⟩

end GlobalTheory.MemLoc.AwayT
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.linkN_along_family_of_localBounds : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  first | exact @GlobalTheory.LinkFam.main | exact GlobalTheory.LinkFam.main | (intros; apply GlobalTheory.LinkFam.main <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_all_ranks : ∀ r, UnitMatch r := by
  first | exact @GlobalTheory.JR.unitMatch_all | exact GlobalTheory.JR.unitMatch_all | (intros; apply GlobalTheory.JR.unitMatch_all <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.CokerFin



theorem coker_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∃ c : ℕ, ∀ z ∈ W.N T₂, (∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : AA K LL) ^ c • z) ∧ ∃ y ∈ W.N T₁, W.map π y = (letπ : AA K LL) ^ c • z := by
  intro D HW F Cm l _ K s LL h W E C T₀ T₁ T₂ ι π h0 h1 h2 hs
  have hP : WachCharacterisationLattice W := GlobalTheory.T.wachModule_uniqueness_characterisation D HW F l K s LL h
  have hp10 : p10 W T₂ := hP T₂ h2
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hfl : Module.Flat (AA K LL) W.EE :=
    GlobalTheory.T.flat_wachLetterRing_completion_of_dense_saturated ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)) ((D.loc l).PD K).p W.EE W.EE_π
      W.EE_complete W.EE_dense W.EE_sat
  obtain ⟨hfree, hbc⟩ := GlobalTheory.T.wachSaturation_image_free_and_spans D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hs hfl
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.saturation_gamma_stable_of_good D HW F l K s LL h T₁ T₂ π h1 h2
  have hS := hp10 _ hfree hbc hg1 hg2 (GlobalTheory.T.wachSaturation_frobenius_mem_up_to_Q_power D HW F l K s LL h T₁ T₂ π h1 h2)
    (GlobalTheory.T.wachSaturation_Q_power_mem_frobenius_span D HW F l K s LL h T₁ T₂ π h1 h2 hfree hbc)
  obtain ⟨c, hc⟩ := GlobalTheory.NL.Coker.uniform (W.N_fg T₂) hS.ge
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨⟨y, hy, e1⟩, ⟨y', hy', e2⟩⟩ := hc z hz
  exact ⟨⟨y, hy, e1⟩, ⟨y', hy', e2⟩⟩

end GlobalTheory.NL.CokerFin
end

section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology

namespace GlobalTheory.WeakClosedX

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem jD_aN_eq_range_gen {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}
    {s : ℕ} {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (T : Lt K LL) (a : AA K LL) :
    ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T a : Set (W.DD T)) =
      Set.range fun c : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (c i)) • y i := by
  obtain ⟨S, hS⟩ := W.N_fg T
  let n : Fin S.card → W.DD T := fun i => (S.equivFin.symm i : W.DD T)
  have hrange : Set.range n = (S : Set (W.DD T)) := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact (S.equivFin.symm i).2
    · intro hz; exact ⟨S.equivFin ⟨z, hz⟩, by simp [n]⟩
  have hspan : W.N T = Submodule.span (AA K LL) (Set.range n) := by rw [hrange, hS]
  refine ⟨S.card, fun i => E.tie.jD T (a • n i), ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hx
    rw [hspan] at hm
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (AA K LL)).1 hm
    refine ⟨c, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [GlobalTheory.NL.WkRange.jD_smul_letter]
    exact smul_comm _ _ _
  · rintro ⟨c, rfl⟩
    refine ⟨∑ i, c i • (a • n i), ?_, ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, c i • n i, ?_, ?_⟩
      · rw [hspan]
        exact (Submodule.mem_span_range_iff_exists_fun (AA K LL)).2 ⟨c, rfl⟩
      · simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum]
        exact Finset.sum_congr rfl fun i _ => GlobalTheory.NL.WkRange.jD_smul_letter E T _ _

theorem jD_XN_closed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T))) := by
  intro D HW F l _ K s LL h T _
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (LatB T d) := GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T
  let bO := Module.finBasis ℤ_[l] ↥(OL LL)
  letI τ := twTop T b
  letI tW : TopologicalSpace (WCb l) := wTop l
  letI := cbTop l
  haveI := hausdorff_tilt_witt (l := l)
  haveI := ring_cb (l := l)
  haveI : T2Space (WCb l) := GlobalTheory.WeakTop.t2Space_wittVector_product
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  letI := zlMod T
  haveI := zlTower T
  have hc : Continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) := continuous_induced_dom
  haveI hT2 : T2Space (TW (RW LL) T) :=
    T2Space.of_injective_continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b).injective hc
  haveI hAG : IsTopologicalAddGroup (TW (RW LL) T) :=
    Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩
  refine ⟨τ, hT2, hAG, GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology (D.locA l) T b, GlobalTheory.T.continuous_one_tmul_latB T b, ?_⟩
  obtain ⟨r, y, hy⟩ := jD_aN_eq_range_gen ((F l).E K s LL h) T ((HW l).W K s LL h).X
  rw [hy]
  letI := aTop (K := K) bO
  haveI := GlobalTheory.T.compactSpace_aTop' (K := K) bO
  refine (isCompact_range ?_).isClosed
  refine continuous_finsetSum _ fun i _ => ?_
  exact (GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology ((F l).E K s LL h) T b bO (y i)).comp (continuous_apply i)

end GlobalTheory.WeakClosedX
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.etaleComparison_pi_wachLattice_closed_weak : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T letπ : Set (((HW l).W K s LL h).DD T))) := by
  first | exact @GlobalTheory.WeakClosed.jD_piN_closed | exact GlobalTheory.WeakClosed.jD_piN_closed | (intros; apply GlobalTheory.WeakClosed.jD_piN_closed <;> assumption)
end
