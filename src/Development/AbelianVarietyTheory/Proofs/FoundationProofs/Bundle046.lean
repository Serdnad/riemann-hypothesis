module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Algebraic.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Pi
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory

open IsLocalRing Polynomial TensorProduct

theorem ker_includeRight_residueField_le_jacobson (R B : Type*) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] :
    RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) ≤
      (⊥ : Ideal B).jacobson := by
  intro x hx
  apply mem_jacobson_bot_of_forall_isMaximal
  intro n hn
  haveI := hn
  have hc := comap_eq_maximalIdeal_of_finite (R := R) n
  let φ : ResidueField R →ₐ[R] B ⧸ n :=
    Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R (B ⧸ n)) fun a ha => by
      rw [Algebra.ofId_apply, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem,
        ← Ideal.mem_comap, hc]
      exact ha
  let ψ := Algebra.TensorProduct.lift φ (Ideal.Quotient.mkₐ R n) fun _ _ => Commute.all _ _
  have h1 : ψ ((1 : ResidueField R) ⊗ₜ[R] x) = Ideal.Quotient.mk n x := by
    simp [ψ]
  have h0 : (1 : ResidueField R) ⊗ₜ[R] x = 0 := by
    simpa using RingHom.mem_ker.mp hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← h1, h0, map_zero]

theorem includeRight_residueField_surjective (R B : Type*) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] :
    Function.Surjective (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) := by
  have hs : Function.Surjective (algebraMap R (ResidueField R)) := IsLocalRing.residue_surjective
  exact Algebra.TensorProduct.includeRight_surjective B hs

theorem isUnit_of_isUnit_one_tmul_residueField (R : Type*) {B : Type*} [CommRing R]
    [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B] {x : B}
    (hx : IsUnit ((1 : ResidueField R) ⊗ₜ[R] x)) : IsUnit x := by
  apply isUnit_of_isUnit_mk_of_le_jacobson (ker_includeRight_residueField_le_jacobson R B)
  let e := Ideal.quotientKerAlgEquivOfSurjective (includeRight_residueField_surjective R B)
  have he : e (Ideal.Quotient.mk _ x) = (1 : ResidueField R) ⊗ₜ[R] x := rfl
  have h := hx.map e.symm
  rwa [← he, AlgEquiv.symm_apply_apply] at h

theorem isLocalRing_of_isLocalRing_residueField_tensor (R B : Type*) [CommRing R]
    [IsLocalRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    [IsLocalRing (ResidueField R ⊗[R] B)] : IsLocalRing B := by
  haveI : Nontrivial B := (includeRight_residueField_surjective R B).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((1 : ResidueField R) ⊗ₜ[R] x) with h | h
  · exact Or.inl (isUnit_of_isUnit_one_tmul_residueField R h)
  · right
    apply isUnit_of_isUnit_one_tmul_residueField R
    rwa [TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def]

theorem existsUnique_idempotent_lift_quotient (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    {c : S ⧸ (maximalIdeal R).map (algebraMap R S)} (hc : IsIdempotentElem c) :
    ∃! e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c := by
  refine existsUnique_idempotent_lift_of_henselian R (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective ?_ hc
  rw [Ideal.mk_ker]
  exact map_maximalIdeal_le_jacobson_of_finite R S

theorem bijective_baseChange_residueField_of_etale (R A B : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Module.Finite R B] :
    Function.Bijective fun f : A →ₐ[R] B ↦
      Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f := by
  have hG := bijective_algHom_comp_of_etale_of_henselian R (A := A)
    (Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B)
    (includeRight_residueField_surjective R B) (ker_includeRight_residueField_le_jacobson R B)
  have key : ∀ f : A →ₐ[R] B,
      ((Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f).restrictScalars
        R).comp Algebra.TensorProduct.includeRight = Algebra.TensorProduct.includeRight.comp f := by
    intro f
    ext a
    simp
  refine ⟨fun f g hfg => ?_, fun h => ?_⟩
  · apply hG.1
    dsimp only at hfg ⊢
    rw [← key f, ← key g, hfg]
  · obtain ⟨f, hf⟩ := hG.2 ((h.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    refine ⟨f, ?_⟩
    dsimp only at hf ⊢
    apply Algebra.TensorProduct.ext'
    intro a b
    have hb : Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) f
        ((1 : ResidueField R) ⊗ₜ[R] b) = h ((1 : ResidueField R) ⊗ₜ[R] b) := by
      have := congrArg (fun φ : A →ₐ[R] ResidueField R ⊗[R] B => φ b) hf
      simpa using this
    have hab : a ⊗ₜ[R] b = a • ((1 : ResidueField R) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hab, map_smul, map_smul, hb]

theorem etale_adjoinRoot_of_isUnit_derivative {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic)
    (h : IsUnit (AdjoinRoot.mk f f.derivative)) : Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (↑u⁻¹ : AdjoinRoot f)
  have h1 : AdjoinRoot.mk f (derivative f * p - 1) = 0 := by
    rw [map_sub, map_mul, hp, ← hu, Units.mul_inv, map_one, sub_self]
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_zero.mp h1
  let P : StandardEtalePair R :=
    ⟨f, hf, 1, p, -q, 0, by rw [pow_zero]; linear_combination hq⟩
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by
    simp [P]
  let e2 : AdjoinRoot f ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit (AdjoinRoot f) (Localization.Away (AdjoinRoot.mk P.f P.g)) _
      hunit).restrictScalars R
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans e2.symm)

theorem exists_etale_lift_of_isSeparable.{u} (R : Type u) (L : Type*) [CommRing R] [IsLocalRing R]
    [Field L] [Algebra (ResidueField R) L] [Module.Finite (ResidueField R) L]
    [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
      IsLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField R) L
  have hsep : (minpoly (ResidueField R) pb.gen).Separable :=
    Algebra.IsSeparable.isSeparable _ pb.gen
  have hmon : (minpoly (ResidueField R) pb.gen).Monic := minpoly.monic pb.isIntegral_gen
  have hs : Function.Surjective (algebraMap R (ResidueField R)) := IsLocalRing.residue_surjective
  obtain ⟨f, hfmap, hfdeg, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective _ hs _)) hmon
  haveI hfin : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  letI : Algebra R L :=
    ((algebraMap (ResidueField R) L).comp (algebraMap R (ResidueField R))).toAlgebra
  haveI : IsScalarTower R (ResidueField R) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hroot : Polynomial.aeval pb.gen f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap (ResidueField R), hfmap, minpoly.aeval]
  let g : AdjoinRoot f →ₐ[R] L := AdjoinRoot.liftAlgHom f (Algebra.ofId R L) pb.gen hroot
  let ψ : ResidueField R ⊗[R] AdjoinRoot f →ₐ[ResidueField R] L :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) g fun _ _ => Commute.all _ _
  have hψroot : ψ ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.root f) = pb.gen := by
    simp only [ψ, g, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hsurjψ : Function.Surjective ψ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← pb.adjoin_gen_eq_top, Algebra.adjoin_le_iff,
      Set.singleton_subset_iff]
    exact (AlgHom.mem_range ψ).mpr ⟨_, hψroot⟩
  let bT := Algebra.TensorProduct.basis (ResidueField R) (AdjoinRoot.powerBasis' hf).basis
  haveI : Module.Finite (ResidueField R) (ResidueField R ⊗[R] AdjoinRoot f) :=
    Module.Finite.of_basis bT
  have hdim : Module.finrank (ResidueField R) (ResidueField R ⊗[R] AdjoinRoot f) =
      Module.finrank (ResidueField R) L := by
    rw [Module.finrank_eq_card_basis bT, Fintype.card_fin, AdjoinRoot.powerBasis'_dim, pb.finrank,
      ← pb.natDegree_minpoly, Polynomial.natDegree_eq_of_degree_eq hfdeg]
  have hinjψ : Function.Injective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := ψ.toLinearMap)).mpr
      hsurjψ
  let e := AlgEquiv.ofBijective ψ ⟨hinjψ, hsurjψ⟩
  haveI : Nontrivial (ResidueField R ⊗[R] AdjoinRoot f) := hsurjψ.nontrivial
  haveI : IsLocalRing (ResidueField R ⊗[R] AdjoinRoot f) :=
    IsLocalRing.of_surjective' e.symm.toRingEquiv.toRingHom e.symm.surjective
  have hloc : IsLocalRing (AdjoinRoot f) := isLocalRing_of_isLocalRing_residueField_tensor R _
  have hder : IsUnit (AdjoinRoot.mk f (derivative f)) := by
    apply isUnit_of_isUnit_one_tmul_residueField R
    have h1 : ψ ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.mk f (derivative f)) =
        Polynomial.aeval pb.gen (derivative (minpoly (ResidueField R) pb.gen)) := by
      rw [← hfmap, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
      simp only [ψ, g, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    have h2 : IsUnit (e ((1 : ResidueField R) ⊗ₜ[R] AdjoinRoot.mk f (derivative f))) := by
      rw [show e _ = ψ _ from rfl, h1, isUnit_iff_ne_zero]
      exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
    simpa using h2.map e.symm
  haveI := etale_adjoinRoot_of_isUnit_derivative hf hder
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, hfin, inferInstance, hloc, ⟨e⟩⟩

theorem exists_etale_lift_of_etale.{u, v} (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R]
    [CommRing E] [Algebra (ResidueField R) E] [Algebra.Etale (ResidueField R) E] :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧
      Algebra.Etale R A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] E) := by
  obtain ⟨I, hI, Ai, _, _, e, hAi⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (ResidueField R) E).mp inferInstance
  have H : ∀ i, ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧
      Algebra.Etale R A ∧ IsLocalRing A ∧
        Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] Ai i) := fun i => by
    haveI := (hAi i).1
    haveI := (hAi i).2
    exact exists_etale_lift_of_isSeparable R (Ai i)
  choose A hA1 hA2 hfin het _ hiso using H
  have := Fintype.ofFinite I
  classical
  refine ⟨Π i, A i, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.piRight R (ResidueField R) (ResidueField R) A).trans
    ((AlgEquiv.piCongrRight fun i => (hiso i).some).trans e.symm)

end GlobalTheory
end
end

section

open Finset GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.EisCong

variable {K : Type} [Field K] [CharZero K]

def pInt (p : ℕ) [Fact p.Prime] (K : Type) [Field K] : Subring K where
  carrier := {x | ∃ D : ℕ, ¬ p ∣ D ∧ IsIntegral ℤ ((D : K) * x)}
  mul_mem' := by
    rintro x y ⟨D, hD, hx⟩ ⟨E, hE, hy⟩
    refine ⟨D * E, fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hD hE, ?_⟩
    have : ((D * E : ℕ) : K) * (x * y) = ((D : K) * x) * ((E : K) * y) := by push_cast; ring
    rw [this]; exact hx.mul hy
  one_mem' := ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using isIntegral_one⟩
  add_mem' := by
    rintro x y ⟨D, hD, hx⟩ ⟨E, hE, hy⟩
    refine ⟨D * E, fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hD hE, ?_⟩
    have : ((D * E : ℕ) : K) * (x + y) = (E : K) * ((D : K) * x) + (D : K) * ((E : K) * y) := by
      push_cast; ring
    rw [this]
    exact ((isIntegral_natCast E).mul hx).add ((isIntegral_natCast D).mul hy)
  zero_mem' := ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using isIntegral_zero⟩
  neg_mem' := by
    rintro x ⟨D, hD, hx⟩
    exact ⟨D, hD, by rw [mul_neg]; exact hx.neg⟩

variable {p : ℕ} [Fact p.Prime]

omit [CharZero K] in
lemma mem_of_isIntegral {x : K} (h : IsIntegral ℤ x) : x ∈ pInt p K :=
  ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using h⟩

lemma inv_nat_mem {m : ℕ} (h : ¬ p ∣ m) : (m : K)⁻¹ ∈ pInt p K := by
  have hm : (m : K) ≠ 0 := by
    have : m ≠ 0 := by rintro rfl; exact h (dvd_zero _)
    exact_mod_cast this
  exact ⟨m, h, by rw [mul_inv_cancel₀ hm]; exact isIntegral_one⟩

lemma inv_int_mem {c : ℤ} (h : ¬ (p : ℤ) ∣ c) : (c : K)⁻¹ ∈ pInt p K := by
  have h1 : ((c.natAbs : ℕ) : K)⁻¹ ∈ pInt p K := inv_nat_mem (fun h' => h (Int.natCast_dvd.2 h'))
  rcases Int.natAbs_eq c with h2 | h2
  · rw [h2]; simpa using h1
  · rw [h2]; simpa using neg_mem h1

omit [CharZero K] in
lemma root_zpow_mem {ζ : K} {M : ℕ} (hM : 0 < M) (h : IsPrimitiveRoot ζ M) (e : ℤ) : ζ ^ e ∈ pInt p K := by
  rcases e with e | e
  · simpa using pow_mem (mem_of_isIntegral (h.isIntegral hM)) e
  · rw [zpow_negSucc, ← inv_pow]; exact pow_mem (mem_of_isIntegral (h.inv.isIntegral hM)) _

lemma pow_div_mem {k e : ℕ} (hk : k ≠ 0) (h : k < p ^ (e + 1)) : (p : K) ^ e / k ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p hp.ne_one
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  have hv : v ≤ e := by
    have : p ^ v < p ^ (e + 1) := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)) h
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 this
    omega
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hv
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : (p : K) ^ (v + w) / ((p ^ v * u : ℕ) : K) = (p : K) ^ w * (u : K)⁻¹ := by
    push_cast; field_simp; ring
  rw [this]
  exact mul_mem (pow_mem (natCast_mem _ p) w) (inv_nat_mem hu)

lemma pow_div_add_two_mem (hp2 : p ≠ 2) (n i : ℕ) : ((p : K) ^ (n + 1)) ^ i / ((i : K) + 2) ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have h1 : ∀ i : ℕ, i + 2 < 3 ^ (i + 1) := by
    intro i
    induction i with
    | zero => norm_num
    | succ i ih => rw [pow_succ]; omega
  have h2 : i + 2 < p ^ ((n + 1) * i + 1) :=
    (h1 i).trans_le ((Nat.pow_le_pow_left h3 _).trans (Nat.pow_le_pow_right hp.pos (by nlinarith)))
  have := pow_div_mem (K := K) (k := i + 2) (by omega) h2
  rw [← pow_mul]
  simpa using this

lemma prime_mul_bernoulli_mem (k : ℕ) : (p : K) * ((bernoulli (k + 2) : ℚ) : K) ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  rcases Nat.even_or_odd (k + 2) with ⟨m, hm⟩ | hodd
  · have hk2 : k + 2 = 2 * m := by omega
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
    have hB : bernoulli (k + 2) = (z : ℚ) -
        ∑ q ∈ Finset.range (2 * m + 2) with q.Prime ∧ (q - 1) ∣ 2 * m, (1 : ℚ) / q := by
      rw [hk2, hz]; ring
    rw [hB]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    refine sub_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) (sum_mem fun q hq => ?_)
    have hq' := (Finset.mem_filter.mp hq).2.1
    by_cases hql : q = p
    · subst hql
      have : (q : K) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [mul_one_div_cancel this]; exact one_mem _
    · rw [one_div]
      exact mul_mem (natCast_mem _ _)
        (inv_nat_mem fun h => hql ((Nat.prime_dvd_prime_iff_eq hp hq').mp h).symm)
  · rw [bernoulli_eq_zero_of_odd hodd (by omega)]
    simp

lemma choose_cast (m i : ℕ) :
    (((m + 2).choose (i + 2) : ℕ) : K) = ((m : K) + 2) * ((m + 1).choose (i + 1) : ℕ) / ((i : K) + 2) := by
  have h := Nat.add_one_mul_choose_eq (m + 1) (i + 1)
  have hi : (i : K) + 2 ≠ 0 := by exact_mod_cast (show i + 2 ≠ 0 by omega)
  rw [eq_div_iff hi]
  have h' := congrArg (Nat.cast : ℕ → K) h
  push_cast at h'
  simp only [add_assoc, one_add_one_eq_two] at h'
  rw [← h']

lemma binom_second (hp2 : p ≠ 2) (n m : ℕ) (x t : ℤ) :
    ∃ y ∈ pInt p K, ((x : K) + t * (p : K) ^ (n + 1)) ^ (m + 2) =
      (x : K) ^ (m + 2) + ((m : K) + 2) * t * (p : K) ^ (n + 1) * (x : K) ^ (m + 1) +
        ((m : K) + 2) * ((p : K) ^ (n + 1)) ^ 2 * y := by
  set Q : K := (p : K) ^ (n + 1) with hQ
  refine ⟨∑ i ∈ range (m + 1), (t : K) ^ (i + 2) * (x : K) ^ (m - i) * ((m + 1).choose (i + 1) : ℕ) *
    (Q ^ i / ((i : K) + 2)), sum_mem fun i _ => mul_mem (mul_mem (mul_mem (pow_mem (intCast_mem _ _) _)
      (pow_mem (intCast_mem _ _) _)) (natCast_mem _ _)) (pow_div_add_two_mem hp2 n i), ?_⟩
  rw [add_comm (x : K), add_pow, sum_range_succ', sum_range_succ', mul_sum]
  have : ∀ i ∈ range (m + 1), ((t : K) * Q) ^ (i + 1 + 1) * (x : K) ^ (m + 2 - (i + 1 + 1)) *
      ((m + 2).choose (i + 1 + 1) : ℕ) = ((m : K) + 2) * Q ^ 2 * ((t : K) ^ (i + 2) * (x : K) ^ (m - i) *
        ((m + 1).choose (i + 1) : ℕ) * (Q ^ i / ((i : K) + 2))) := by
    intro i _
    rw [show m + 2 - (i + 1 + 1) = m - i by omega, show i + 1 + 1 = i + 2 by omega, choose_cast]
    ring
  rw [sum_congr rfl this]
  simp
  ring

lemma binom_first (Q : ℤ) (k : ℕ) (x t : ℤ) :
    ∃ y : ℤ, ((x : K) + t * (Q : K)) ^ k = (x : K) ^ k + Q * y := by
  obtain ⟨y, hy⟩ := sub_dvd_pow_sub_pow (x + t * Q) x k
  refine ⟨t * y, ?_⟩
  have := congrArg (Int.cast : ℤ → K) hy
  push_cast at this ⊢
  linear_combination this



end GlobalTheory.EisCong
end

section

namespace GlobalTheory

theorem exists_finite_pid_subalgebra_div_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgebraic ℤ_[p] s) →
  ∃ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R ∧ IsPrincipalIdealRing R ∧ ∀ s ∈ S, ∃ a ∈ R, ∃ b ∈ R, s = a / b := by
  intro p _ Ω _ _ hinj S hS
  haveI : FaithfulSMul ℤ_[p] Ω := (faithfulSMul_iff_algebraMap_injective ℤ_[p] Ω).mpr hinj
  letI : Algebra (FractionRing ℤ_[p]) Ω := FractionRing.liftAlgebra ℤ_[p] Ω
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) Ω := FractionRing.isScalarTower_liftAlgebra ℤ_[p] Ω
  set L := IntermediateField.adjoin (FractionRing ℤ_[p]) (S : Set Ω) with hL
  haveI : FiniteDimensional (FractionRing ℤ_[p]) L := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    exact ((hS x hx).extendScalars (IsFractionRing.injective ℤ_[p] (FractionRing ℤ_[p]))).isIntegral
  haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) L := inferInstance
  haveI : IsDedekindDomain (integralClosure ℤ_[p] L) :=
    integralClosure.isDedekindDomain ℤ_[p] (FractionRing ℤ_[p]) L
  haveI : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.finite ℤ_[p] (FractionRing ℤ_[p]) L (integralClosure ℤ_[p] L)
  have hPID : IsPrincipalIdealRing (integralClosure ℤ_[p] L) := by
    apply IsPrincipalIdealRing.of_finite_primes
    haveI := GlobalTheory.finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[p] (integralClosure ℤ_[p] L)
    apply ((Set.finite_range (fun M : MaximalSpectrum (integralClosure ℤ_[p] L) => M.asIdeal)).insert ⊥).subset
    intro I hI
    by_cases h : I = ⊥
    · exact Or.inl h
    · exact Or.inr ⟨⟨I, (show I.IsPrime from hI).isMaximal h⟩, rfl⟩
  let f : L →ₐ[ℤ_[p]] Ω :=
    { algebraMap L Ω with
      commutes' := fun r => by
        change ((algebraMap ℤ_[p] L r : L) : Ω) = _
        rw [IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) L r]
        exact (IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) Ω r).symm }
  have hf : Function.Injective f := Subtype.val_injective
  let e := Subalgebra.equivMapOfInjective (integralClosure ℤ_[p] L) f hf
  refine ⟨(integralClosure ℤ_[p] L).map f, Module.Finite.equiv e.toLinearEquiv,
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective, ?_⟩
  intro s hs
  obtain ⟨c, hc0, hci⟩ := (hS s hs).exists_integral_multiple
  have hsL : s ∈ L := IntermediateField.subset_adjoin _ _ hs
  refine ⟨c • s, ?_, algebraMap ℤ_[p] Ω c, Subalgebra.algebraMap_mem _ c, ?_⟩
  · rw [Subalgebra.mem_map]
    refine ⟨c • ⟨s, hsL⟩, ?_, rfl⟩
    show IsIntegral ℤ_[p] (c • (⟨s, hsL⟩ : L))
    rw [← isIntegral_algHom_iff f hf]
    exact hci
  · rw [Algebra.smul_def, mul_div_cancel_left₀ _ ((map_ne_zero_iff _ hinj).mpr hc0)]

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem isIntegral_of_forall_mem_discreteValuationSubring : ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K] [Algebra S K] [IsFractionRing S K] (t : K), (∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ s : S, algebraMap S K s ∈ V) → t ∈ V) → IsIntegral S t := by
  intro S K _ _ _ _ _ _ t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType S K := .of_isLocalization K (nonZeroDivisors S)
  have hic : IsIntegrallyClosedIn (integralClosure S K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure S K) K)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure S K).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := exists_discreteValuationSubring_of_valuationSubring (R := S) W
    (fun r => hW ((integralClosure S K).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  exact (V.inv_mem_nonunits_iff.mp (h3 _ rfl)).resolve_left ht0 (ht V h1 h2)

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_ratAlg : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (n : ℕ) (ζ : Ω), 1 ≤ n → IsPrimitiveRoot ζ (l ^ n) → A.valuation (ζ - 1) ^ (l ^ n).totient = A.valuation (l : Ω) := by
  first | exact @GlobalTheory.valuation_zeta_sub_one_pow_totient | exact GlobalTheory.valuation_zeta_sub_one_pow_totient | (intros; apply GlobalTheory.valuation_zeta_sub_one_pow_totient <;> assumption)
end
