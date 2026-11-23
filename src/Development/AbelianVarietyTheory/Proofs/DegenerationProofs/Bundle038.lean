module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle010
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCompatibleNormTowerProfinite
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory

theorem isAlgebraic_int_eval₂Hom_of_isAlgebraic {σ : Type} (y : σ → ℂ)
    (hy : ∀ i, IsAlgebraic ℚ (y i)) (c : MvPolynomial σ ℤ) :
    IsAlgebraic ℤ (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c) := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ]
  induction c using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (a : ℚ)
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => rw [map_mul, MvPolynomial.eval₂Hom_X']; exact hp.mul (hy i)

theorem exists_ringHom_complex_of_countable_of_relations :
    ∀ (F : Type) [Field F] [CharZero F] [Countable F] (x : Fin 2 → F) (y : Fin 2 → ℂ), (∀ i, IsAlgebraic ℚ (y i)) → (∀ c : MvPolynomial (Fin 2) ℤ, MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c = 0 → MvPolynomial.eval₂Hom (Int.castRingHom F) x c = 0) → ∃ f : F →+* ℂ, ∀ i, f (x i) = y i := by
  intro F _ _ _ x y hy hrel
  set ey := MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y with hey
  set ex := MvPolynomial.eval₂Hom (Int.castRingHom F) x with hex
  let R := MvPolynomial (Fin 2) ℤ ⧸ RingHom.ker ey
  have hprime : (RingHom.ker ey).IsPrime := RingHom.ker_isPrime ey
  have : IsDomain R := Ideal.Quotient.isDomain _
  let em : R →+* ℂ := RingHom.kerLift ey
  have hem : Function.Injective em := RingHom.kerLift_injective ey
  let β : R →+* F := Ideal.Quotient.lift _ ex fun c hc => hrel c hc
  have halg : ∀ r : R, IsAlgebraic ℤ r := by
    intro r
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine (isAlgebraic_algHom_iff em.toIntAlgHom hem).1 ?_
    exact isAlgebraic_int_eval₂Hom_of_isAlgebraic y hy c
  have hβ : Function.Injective β := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker β) h0 hr (halg r) ?_
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker] at hn
    simpa using hn
  have hc : Countable R := hβ.countable
  let : Algebra R F := β.toAlgebra
  let : Algebra R ℂ := em.toAlgebra
  have : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).2 hβ
  have : FaithfulSMul R ℂ := (faithfulSMul_iff_algebraMap_injective R ℂ).2 hem
  obtain ⟨j⟩ := nonempty_algHom_complex_of_countable R F
  refine ⟨j.toRingHom, fun i => ?_⟩
  have h := j.commutes (Ideal.Quotient.mk _ (MvPolynomial.X i))
  have h1 : algebraMap R F (Ideal.Quotient.mk _ (MvPolynomial.X i)) = x i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom F) x i
  have h2 : algebraMap R ℂ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = y i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom ℂ) y i
  rw [h1, h2] at h
  exact h

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

section

variable {p : ℕ} [Fact p.Prime]

theorem mem_padicAlgCl_valuationSubring_iff_norm_le_one (x : PadicAlgCl p) :
    x ∈ OO p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe]
  rfl

noncomputable def integralClosureToPadicAlgClIntegers
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : integralClosure ℤ_[p] K →+* OO p :=
  (K.val.toRingHom.comp (integralClosure ℤ_[p] K).val.toRingHom).codRestrict (OO p) fun x =>
    (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).mpr
      ((mem_integralClosure_padicInt_iff K _).mp x.2)

theorem isLocalHom_integralClosureToPadicAlgClIntegers
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IsLocalHom (integralClosureToPadicAlgClIntegers K) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have hy' : ((x : K) : PadicAlgCl p) * (y : PadicAlgCl p) = 1 :=
    congrArg (fun z : OO p => (z : PadicAlgCl p)) hy
  have h0 : (x : K) ≠ 0 := by
    intro h0
    rw [h0] at hy'
    simp at hy'
  have hinv : (x : K)⁻¹ ∈ integralClosure ℤ_[p] K := by
    rw [mem_integralClosure_padicInt_iff, IntermediateField.coe_inv,
      ← eq_inv_of_mul_eq_one_right hy']
    exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).mp y.2
  exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ h0))

theorem exists_factor_integralClosure_of_finiteType {A : Type*} [CommRing A]
    [Algebra.FiniteType ℤ A] (φ : A →+* OO p) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K →
        ∃ ψ : A →+* integralClosure ℤ_[p] K,
          (integralClosureToPadicAlgClIntegers K).comp ψ = φ := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := A)
  let φ' : A →+* PadicAlgCl p := (OO p).subtype.comp φ
  refine ⟨IntermediateField.adjoin ℚ_[p] ((s.image φ' : Finset _) : Set (PadicAlgCl p)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x,
    fun K hK => ?_⟩
  have hmem : ∀ a, φ' a ∈ K := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (s : Set A) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      exact hK (IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩))
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact K.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact K.mul_mem hx hy
  let ψ₁ : A →+* K := φ'.codRestrict K hmem
  refine ⟨ψ₁.codRestrict (integralClosure ℤ_[p] K) fun a =>
    (mem_integralClosure_padicInt_iff K _).mpr
      ((mem_padicAlgCl_valuationSubring_iff_norm_le_one _).mp (φ a).2), ?_⟩
  ext a
  rfl

theorem exists_affineOpen_factor_of_isLocalRing {R : CommRingCat.{0}} [IsLocalRing R]
    {X : Scheme.{0}} (y : Spec R ⟶ X) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (φ : Γ(X, V) ⟶ R), Spec.map φ ≫ hV.fromSpec = y := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : y ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hz
    exact (this.ge (Set.mem_univ x) : x ∈ y ⁻¹ᵁ V)
  refine ⟨V, hV, Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

end

theorem padicAlgCl_integral_points :
    (∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (z : X),
      IsClosed ({z} : Set X) → ∀ U : X.Opens, (U : Set X).Nonempty →
        ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ X),
          y (cPt p) = z ∧ Set.range (gPt p ≫ y) ⊆ U) ∧
    (∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (p : ℕ) [Fact p.Prime]
      (y : Sp (OO p) ⟶ X), ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p),
        FiniteDimensional ℚ_[p] K₀ ∧ ∀ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K →
          ∃ (j : integralClosure ℤ_[p] K →+* OO p) (y₀ : Sp (integralClosure ℤ_[p] K) ⟶ X),
            (∀ x, ((j x : OO p) : PadicAlgCl p) = ((x : K) : PadicAlgCl p)) ∧ IsLocalHom j ∧
              spMap j ≫ y₀ = y) := by
  refine ⟨fun X _ π _ _ z hz U hU => ?_, fun X π _ p _ y => ?_⟩
  · obtain ⟨p, hp, hpz⟩ := exists_prime_residueField_eq_zero π hz
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨K, hK, y, hy, hyU, -⟩ := exists_padic_point_scheme π hz hpz U hU
    haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
    haveI : IsLocalRing (integralClosure ℤ_[p] K) :=
      (integralClosureToPadicAlgClIntegers K).domain_isLocalRing
    refine ⟨p, inferInstance, spMap (integralClosureToPadicAlgClIntegers K) ≫ y, ?_, ?_⟩
    · refine (Scheme.Hom.comp_apply _ _ _).trans ((congrArg y ?_).trans hy)
      exact IsLocalRing.comap_closedPoint (integralClosureToPadicAlgClIntegers K)
    · rintro _ ⟨x, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply]
      have key : spMap (integralClosureToPadicAlgClIntegers K) ((gPt p) x) =
          genericPoint (Sp (integralClosure ℤ_[p] K)) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        apply le_antisymm _ bot_le
        intro a ha
        have ha' : ((a : K) : PadicAlgCl p) ∈ (x : PrimeSpectrum (PadicAlgCl p)).asIdeal := ha
        haveI := (x : PrimeSpectrum (PadicAlgCl p)).isPrime
        rw [Ideal.eq_bot_of_prime (x : PrimeSpectrum (PadicAlgCl p)).asIdeal,
          Ideal.mem_bot] at ha'
        exact Subtype.ext (Subtype.ext ha')
      rw [Scheme.Hom.comp_apply, key]
      exact hyU
  · obtain ⟨V, hV, φ, rfl⟩ := exists_affineOpen_factor_of_isLocalRing y
    haveI := finiteType_int_sections π hV
    obtain ⟨K₀, hK₀, H⟩ := exists_factor_integralClosure_of_finiteType φ.hom
    refine ⟨K₀, hK₀, fun K hK => ?_⟩
    obtain ⟨ψ, hψ⟩ := H K hK
    refine ⟨integralClosureToPadicAlgClIntegers K,
      Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, fun _ => rfl,
      isLocalHom_integralClosureToPadicAlgClIntegers K, ?_⟩
    rw [← Category.assoc]
    congr 1
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact congrArg (fun f => ((f a : OO p) : PadicAlgCl p)) hψ

end GlobalTheory
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.CubeBalance

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem cubN_succ (θ : A → A → A → U) (k : ℕ) (x y : A) :
    cubN θ (k + 1) 1 x y = cubN θ k 1 x y * θ (x ^ k) x y := by
  simp only [cubN, Finset.prod_range_succ, _root_.one_mul]

theorem cubN_add (h : IsCub θ) (a b : ℕ) (x y : A) :
    cubN θ (a + b) 1 x y = θ (x ^ a) (x ^ b) y * cubN θ a 1 x y * cubN θ b 1 x y := by
  have s := h.N_split b (x ^ a) x y
  have e : cubN θ (a + b) 1 x y = cubN θ a 1 x y * cubN θ b (x ^ a) x y := by
    simp only [cubN, Finset.prod_range_add, _root_.one_mul, pow_add]
  rw [e, s, ← _root_.mul_assoc, mul_comm (cubN θ a 1 x y)]

theorem cubN_mul (h : IsCub θ) (a b : ℕ) (x y : A) :
    cubN θ (a * b) 1 x y = cubN θ a 1 (x ^ b) y * cubN θ b 1 x y ^ a := by
  induction a with
  | zero => simp [cubN]
  | succ a ih =>
    rw [Nat.succ_mul, cubN_add h, ih, cubN_succ, ← pow_mul, mul_comm b a, pow_succ]
    ac_rfl

theorem cubN_swap (h : IsCub θ) (a b : ℕ) (x y : A) :
    cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a = cubN θ b 1 y (x ^ a) * cubN θ a 1 x y ^ b := by
  induction b with
  | zero =>
    rw [pow_zero, h.N_one]
    simp [cubN]
  | succ b ih =>
    have n := h.N_add a 1 x (y ^ b) y
    rw [h.face, _root_.mul_one, _root_.one_mul] at n
    have r : ∀ z : A, θ (y ^ b) y z = θ z (y ^ b) y := fun z => by rw [h.s12, h.s01]
    rw [cubN_succ, cubN_succ, r, r, pow_succ y, mul_pow, pow_succ, mul_comm (cubN θ b 1 y x ^ a),
      ← _root_.mul_assoc, n]
    calc θ (x ^ a) (y ^ b) y * cubN θ a 1 x (y ^ b) * cubN θ a 1 x y * cubN θ b 1 y x ^ a
        = θ (x ^ a) (y ^ b) y * cubN θ a 1 x y * (cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a) := by ac_rfl
      _ = _ := by rw [ih]; ac_rfl

end GlobalTheory.CubeBalance
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ReZeta

theorem exists_exponent {K : Type} [Field K] (ξ ζ : ℕ → Kˣ) (hξ : ∀ n, 0 < n → IsPrimitiveRoot (ξ n) n)
    (hξ' : ∀ n m, 0 < n → 0 < m → ξ (n * m) ^ m = ξ n) (hζ : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n)
    (hζ' : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) :
    ∃ ν : ℕ → ℤ, (∀ n, 0 < n → ξ n ^ ν n = ζ n) ∧ (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n := by
  have h : ∀ n : ℕ, ∃ i : ℕ, 0 < n → ξ n ^ i = ζ n := fun n => by
    by_cases hn : 0 < n
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (hξ n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity n (ζ n)).2 (hζ n hn).pow_eq_one)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose i hi using h
  refine ⟨fun n => i n, fun n hn => by rw [zpow_natCast, hi n hn], fun n hn => ?_, fun n m hn hm => ?_⟩
  · exact Nat.isCoprime_iff_coprime.2 (((hξ n hn).pow_iff_coprime hn _).1 (hi n hn ▸ hζ n hn))
  · rw [← (hξ n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, hi n hn, mul_inv_eq_one,
      ← hξ' n m hn hm, ← pow_mul, mul_comm m, pow_mul, hi _ (Nat.mul_pos hn hm), hζ' n m hn hm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem modN_smul (D : Datum H) {n : ℕ} {c : 𝓞 E} (h : (n : 𝓞 E) ∣ c) (a : D.La) : D.ModN n (c • a) := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨b • a, by rw [mul_smul, Nat.cast_smul_eq_nsmul]⟩

theorem exists_sim (D : Datum H) (ν : ℕ → ℤ) (h₁ : ∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ))
    (h₂ : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) : ∃ g : Sim D, g.ν = ν := by
  obtain ⟨t, ht₁, ht₂, -⟩ := GlobalTheory.NormTower.exists_norm_tower E H (GlobalTheory.HostModel.level H 1 one_pos) ν h₁ h₂
  refine ⟨⟨fun n => t n • LinearMap.id, ν, fun n m hn hm a => ?_, fun n hn => ?_, fun n hn a b => ?_⟩, rfl⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [← sub_smul]
    exact modN_smul D (ht₂ n m hn hm) a
  · obtain ⟨u, v, huv⟩ := h₁ n hn
    obtain ⟨c, hc⟩ := ht₁ n hn
    have huv' : (u : 𝓞 E) * (ν n : 𝓞 E) + (v : 𝓞 E) * (n : 𝓞 E) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huv
    have hd : (n : 𝓞 E) ∣ (u : 𝓞 E) * H.bar (t n) * t n - 1 :=
      ⟨u * c - v, by linear_combination (u : 𝓞 E) * hc + huv'⟩
    refine ⟨((u : 𝓞 E) * H.bar (t n)) • LinearMap.id, fun a => ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    have := modN_smul D hd a
    rw [sub_smul, one_smul] at this
    exact ⟨by rwa [← mul_smul], by rwa [← mul_smul, mul_comm]⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    obtain ⟨c, hc⟩ := ht₁ n hn
    have e : H.bar (t n) * t n = (ν n : 𝓞 E) + (n : 𝓞 E) * c := by linear_combination hc
    refine ⟨D.EF a (c • b), ?_⟩
    rw [D.adj, ← mul_smul, e, add_smul, mul_smul, Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul, map_add (f := _),
      map_zsmul, map_nsmul, smul_eq_mul, nsmul_eq_mul, add_sub_cancel_left]

end GlobalTheory.ReZeta
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory

theorem jacobson_closedPoints_tools_int : ∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π], JacobsonSpace X ∧ (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧ (∀ U V : X.Opens, (∀ x : X, IsClosed ({x} : Set X) → (x ∈ U ↔ x ∈ V)) → U = V) ∧ (∀ (ξ : X) (κ : Type) [Finite κ] (U : κ → X.Opens) (W : X.Opens), ξ ∈ W → ∃ x : X, IsClosed ({x} : Set X) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i) ∧ (∀ (κ : Type) [Finite κ] (Sg : κ → Set X), IrreducibleSpace X → (∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Sg i) → ∃ i, Dense (Sg i)) :=
  jacobson_tools_of_locallyOfFiniteType_int
end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem etale_mulN_and_isOpen_om (C : Core) (L : C.Law) (T : C.Theta) :
    letI := L.grp; Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left ∧ IsOpen (T.Om L) := by
  letI := L.grp
  letI := L.comm
  have := L.smooth
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have h : Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left := GlobalTheory.GrpTangent.etale_mulN C.GG T.m_unit
  exact ⟨h, (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left.isOpenMap _ (Out.nonzeroLocus T.s).isOpen⟩

theorem etale_mulN_and_isOpen_om_of_isSemiAbelian : ∀ (C : Core) (L : C.Law) (T : C.Theta), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → Out.MulNSt → Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left ∧ IsOpen (T.Om L) :=
  fun C L T _ _ => etale_mulN_and_isOpen_om C L T

end GlobalTheory.ZJ
end
