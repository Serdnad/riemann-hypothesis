module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSMulRegularCokerDualMapOfExactFibres
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
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
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function

namespace GlobalTheory
namespace DualCokernel

theorem extZero_of_isRegularLocalRing (R : Type) [CommRing R] [IsRegularLocalRing R] (g : ℕ)
    (hg : ringKrullDim R = g) (j : ℕ) (hj : j < g) : ExtZero (R := R) R j := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : xs.length = g := by
    rw [hg] at hd
    exact_mod_cast hd
  refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ _ ?_ hreg j
    (by simpa [hlen] using hj)
  · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  · rw [smul_eq_mul, Ideal.mul_top]
    exact (maximalIdeal.isMaximal R).ne_top.lt_top
  · intro r hr
    exact h ▸ Ideal.subset_span hr

end DualCokernel


open DualCokernel in
theorem exact_dualMap_of_exact_fibres_of_isRegularLocalRing :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (g : ℕ), ringKrullDim A = g →
      ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ∃ (K : Type) (_ : Field K) (φ : A →+* K),
        RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      ∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap := by
  intro A _ _ g hg C hF ⟨n, hn⟩ hex
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  have hDext : ∀ i, ∀ j < g, ExtZero (R := A) (Module.Dual A (C.X i)) j := fun i j hj =>
    FiniteLengthComplex.subsingleton_ext_free _ j (extZero_of_isRegularLocalRing A g hg j hj) _
  have hdd : ∀ i j k f, (C.d i j).hom.dualMap ((C.d j k).hom.dualMap f) = 0 := fun i j k f => by
    ext x
    simp [d_d_apply]

  have hloc : ∀ i, ∀ p : Ideal A, p.IsPrime → p ≠ maximalIdeal A → ∃ s, s ∉ p ∧
      ∀ f, (C.d (i - 1) i).hom.dualMap f = 0 →
        s • f ∈ LinearMap.range (C.d i (i + 1)).hom.dualMap := by
    intro i p hp hpm
    obtain ⟨K, _, φ, hφ, hK⟩ := hex ⟨p, hp⟩
    obtain ⟨t, ht, k₀, k₁, hk⟩ := exists_homotopy C hF n hn p
      (fun j => exact_fibre C p φ hφ j (hK j (Or.inl hpm))) i
    refine ⟨t, ht, fun f hf => ⟨k₁.dualMap f, LinearMap.ext fun x => ?_⟩⟩
    have h1 : f ((C.d (i - 1) i).hom (k₀ x)) = 0 := LinearMap.congr_fun hf (k₀ x)
    have h2 := congrArg f (hk x)
    rw [map_add (f := _), h1, zero_add, map_smul] at h2
    exact h2

  have hhom : ∀ i, g ≤ i → ∃ (s : C.X (i + 1) →ₗ[A] C.X i) (t : C.X (i + 1 + 1) →ₗ[A] C.X (i + 1)),
      ∀ x, (C.d i (i + 1)).hom (s x) + t ((C.d (i + 1) (i + 1 + 1)).hom x) = x := by
    intro i hi
    obtain ⟨K, _, φ, hφ, hK⟩ := hex ⟨maximalIdeal A, inferInstance⟩
    obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField
      (f := (C.d i (i + 1)).hom) (g := (C.d (i + 1) (i + 1 + 1)).hom)
      (LinearMap.ext (d_d_apply C _ _ _)) fun m hm' => by
        exact exact_fibre C m φ (hφ.trans (eq_maximalIdeal hm').symm) (i + 1)
          (hK _ (Or.inr (by omega)))
    exact ⟨s, t, fun x => by simpa using LinearMap.congr_fun hst x⟩

  have hstep : ∀ i, ExtZero (R := A)
      (Module.Dual A (C.X (i + 1)) ⧸ LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap) 0 →
      LinearMap.ker (C.d i (i + 1)).hom.dualMap ≤
        LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap := by
    intro i h0 f hf
    refine (Submodule.Quotient.mk_eq_zero _).1 (eq_zero_of_extZero h0 _ fun p hp hpm => ?_)
    obtain ⟨s, hs, hs'⟩ := hloc (i + 1) p hp hpm
    exact ⟨s, hs, (Submodule.Quotient.mk_eq_zero _).2 (hs' f hf)⟩
  have hle : ∀ i, LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap ≤
      LinearMap.ker (C.d i (i + 1)).hom.dualMap := by
    rintro i _ ⟨y, rfl⟩
    exact hdd _ _ _ y
  have key : ∀ k i, i + k = g → ∀ j < i, ExtZero (R := A)
      (Module.Dual A (C.X i) ⧸ LinearMap.range (C.d i (i + 1)).hom.dualMap) j := by
    intro k
    induction k with
    | zero =>
      rintro i rfl
      obtain ⟨s, t, hst⟩ := hhom i le_rfl
      have hds : ∀ x, (C.d i (i + 1)).hom (s ((C.d i (i + 1)).hom x)) = (C.d i (i + 1)).hom x :=
        fun x => by simpa [d_d_apply] using hst ((C.d i (i + 1)).hom x)
      let ι := (LinearMap.range (C.d i (i + 1)).hom.dualMap).liftQ
        (LinearMap.id - (C.d i (i + 1)).hom.dualMap ∘ₗ s.dualMap) (by
          rintro _ ⟨f, rfl⟩
          ext x
          simp [hds])
      have hι : (LinearMap.range (C.d i (i + 1)).hom.dualMap).mkQ ∘ₗ ι = LinearMap.id := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
        refine (Submodule.Quotient.eq _).2 ⟨-s.dualMap f, ?_⟩
        simp [ι]
      exact fun j hj => extZero_retract ι _ hι j (hDext i j hj)
    | succ k ih =>
      intro i hi j hj
      have h := ih (i + 1) (by omega)
      exact extZero_coker ((LinearMap.range _).liftQ _ (hle i))
        (LinearMap.range (C.d i (i + 1)).hom.dualMap).mkQ
        (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (hstep i (h 0 (by omega)))))
        (Submodule.mkQ_surjective _)
        (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_liftQ]) j
        (h _ (by omega)) (hDext i j (by omega))
  intro i
  refine LinearMap.exact_iff.2 (le_antisymm ?_ (hle i))
  rcases lt_or_ge i g with hi | hi
  · exact hstep i (key (g - (i + 1)) (i + 1) (by omega) 0 (by omega))
  · intro f hf
    obtain ⟨s, t, hst⟩ := hhom i hi
    refine ⟨t.dualMap f, LinearMap.ext fun x => ?_⟩
    have h1 : f ((C.d i (i + 1)).hom (s x)) = 0 := LinearMap.congr_fun hf (s x)
    have h2 := congrArg f (hst x)
    rw [map_add (f := _), h1, zero_add] at h2
    exact h2

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MatrixAction

variable {S : Scheme.{0}}


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.MatrixAction.comp_finsetProd {G : Over S} [GrpObj G] [IsCommMonObj G] {T T' : Over S}
    (a : T' ⟶ T) {κ : Type} (s : Finset κ) (x : κ → (T ⟶ G)) :
    a ≫ (∏ l ∈ s, x l) = ∏ l ∈ s, a ≫ x l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, comp_mul, ih]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.MatrixAction.isMonHom_of_points {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h1 : ∀ T : Over S, (1 : T ⟶ G) ≫ f = 1)
    (hm : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  constructor
  · have := h1 (𝟙_ (Over S))
    simpa [Hom.one_def] using this
  · have := hm (G ⊗ G) (fst G G) (snd G G)
    simpa [Hom.mul_def] using this

section
variable {G : Over S} [GrpObj G] {O : Type} [Ring O] (ρ : RingAct G O)

end

end GlobalTheory.MatrixAction
end

section

noncomputable section

namespace GlobalTheory.ClassWeight

abbrev TorChar (X : Type) [AddCommGroup X] (F : Type) [Field F] (N : ℕ) : Subgroup (Multiplicative X →* Fˣ) :=
  (powMonoidHom N : (Multiplicative X →* Fˣ) →* (Multiplicative X →* Fˣ)).ker

variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}

def evalChar (F : Type) [Field F] (N : ℕ) (α : X) : TorChar X F N →* Fˣ :=
  MonoidHom.mk' (fun τ => τ.1 (Multiplicative.ofAdd α)) fun _ _ => rfl

theorem evalChar_add (α β : X) (τ : TorChar X F N) :
    evalChar F N (α + β) τ = evalChar F N α τ * evalChar F N β τ := map_mul τ.1 _ _

theorem evalChar_add_nsmul (α mu : X) (τ : TorChar X F N) : evalChar F N (α + N • mu) τ = evalChar F N α τ := by
  have h : evalChar F N (N • mu) τ = 1 :=
    (map_pow τ.1 (Multiplicative.ofAdd mu) N).trans (DFunLike.congr_fun (show τ.1 ^ N = 1 from τ.2) _)
  rw [evalChar_add, h, mul_one]

theorem exists_evalChar_ne [Module.Finite ℤ X] [IsAlgClosed F] (hN : (N : F) ≠ 0) {α β : X}
    (h : ¬ ∃ mu, β = α + N • mu) : ∃ τ : TorChar X F N, evalChar F N β τ ≠ evalChar F N α τ := by
  have : NeZero (N : F) := ⟨hN⟩
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have : NeZero N := ⟨hN0⟩
  let K : AddSubgroup X := (nsmulAddMonoidHom N : X →+ X).range
  have hK : ∀ q : X ⧸ K, N • q = 0 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨x, rfl⟩
  have : Module.Finite ℤ (X ⧸ K) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' K).toIntLinearMap (QuotientAddGroup.mk'_surjective K)
  have : Finite (X ⧸ K) := Module.finite_of_fg_torsion _ fun q =>
    ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0)⟩, (natCast_zsmul q N).trans (hK q)⟩
  have h0 : HasEnoughRootsOfUnity F N := inferInstance
  have : HasEnoughRootsOfUnity F (Monoid.exponent (Multiplicative (X ⧸ K))) :=
    h0.of_dvd F (Monoid.exponent_dvd_of_forall_pow_eq_one fun q => hK q.toAdd)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative (X ⧸ K)) F
    (a := Multiplicative.ofAdd ((β - α : X) : X ⧸ K)) fun e => by
      obtain ⟨mu, hmu⟩ := (QuotientAddGroup.eq_zero_iff _).1 (show ((β - α : X) : X ⧸ K) = 0 from e)
      exact h ⟨mu, (sub_eq_iff_eq_add'.1 hmu.symm)⟩
  let τ : TorChar X F N := ⟨φ.comp (QuotientAddGroup.mk' K).toMultiplicative, MonoidHom.ext fun x =>
    (map_pow φ _ N).symm.trans ((congrArg φ (show (Multiplicative.ofAdd (x.toAdd : X ⧸ K)) ^ N = 1 from hK (x.toAdd : X ⧸ K))).trans (map_one φ))⟩
  refine ⟨τ, fun e => hφ ?_⟩
  have e₂ := evalChar_add (β - α) α τ
  rw [sub_add_cancel, e] at e₂
  exact right_eq_mul.1 e₂

variable {E : Type} [AddCommGroup E] [Module F E] {W : X → Type} [∀ α, AddCommGroup (W α)] [∀ α, Module F (W α)]

def classSub (S : ∀ α, E →ₗ[F] W α) (N : ℕ) (α : X) : Submodule F E where
  carrier := {v | ∀ β, (¬ ∃ mu, β = α + N • mu) → S β v = 0}
  add_mem' := fun {v v'} h h' β hβ => by rw [map_add (f := _), h β hβ, h' β hβ, add_zero]
  zero_mem' := fun β _ => map_zero _
  smul_mem' := fun c v h β hβ => by rw [map_smul, h β hβ, smul_zero]

theorem exists_proj [Module.Finite ℤ X] [IsAlgClosed F] (hN : (N : F) ≠ 0) (S : ∀ α, E →ₗ[F] W α)
    (hc : (Nat.card (TorChar X F N) : F) ≠ 0) (l : TorChar X F N → E → E)
    (hl : ∀ τ v β, S β (l τ v) = (evalChar F N β τ : F) • S β v) (α : X) (v : E) :
    ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v := by
  have : Finite (TorChar X F N) := Nat.finite_of_card_ne_zero fun e => hc (by rw [e, Nat.cast_zero])
  have := Fintype.ofFinite (TorChar X F N)
  have key : ∀ β, S β ((Nat.card (TorChar X F N) : F)⁻¹ • ∑ τ, (((evalChar F N α τ)⁻¹ : Fˣ) : F) • l τ v) =
      ((Nat.card (TorChar X F N) : F)⁻¹ * ∑ τ, ((Units.coeHom F).comp (evalChar F N β / evalChar F N α)) τ) • S β v :=
    fun β => by

      rw [map_smul, map_sum, mul_smul, Finset.sum_smul]
      refine congrArg _ (Finset.sum_congr rfl fun τ _ => ?_)
      rw [map_smul, hl, smul_smul, ← Units.val_mul, mul_comm, ← div_eq_mul_inv]
      rfl
  refine ⟨_, fun β hβ => (key β).trans ?_, fun mu => (key _).trans ?_⟩
  · obtain ⟨τ, hτ⟩ := exists_evalChar_ne hN hβ
    rw [sum_hom_units_eq_zero _ fun e => hτ (div_eq_one.1 (Units.ext (DFunLike.congr_fun e τ))), mul_zero, zero_smul]
  · have e : ∀ τ, ((Units.coeHom F).comp (evalChar F N (α + N • mu) / evalChar F N α)) τ = 1 := fun τ =>
      congrArg Units.val (div_eq_one.2 (evalChar_add_nsmul α mu τ))
    rw [Finset.sum_congr rfl fun τ _ => e τ, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_one, inv_mul_cancel₀ hc, one_smul]

theorem classSub_structure [Module.Finite ℤ X] [IsAlgClosed F] [FiniteDimensional F E] (hN : (N : F) ≠ 0)
    {A : Type} [CommGroup A] [Finite A] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)) (hA : (Nat.card A : F) ≠ 0)
    (hd : Module.finrank F E ^ 2 = Nat.card A) (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hn : ∀ a, (∀ b, e a b = 1) → a = 1)
    (S : ∀ α, E →ₗ[F] W α) (hS : ∀ v, (∀ α, S α v = 0) → v = 0)
    (a : TorChar X F N →* A) (ha : Function.Injective a)
    (hT : ∀ τ, ∃ c : Fˣ, ∀ v α, S α (Φ (a τ) v) = ((c * evalChar F N α τ : Fˣ) : F) • S α v)
    (H : Subgroup A) (hH : ∀ h ∈ H, ∀ α v v' (c : F), S α v = c • S α v' → S α (Φ h v) = c • S α (Φ h v'))
    (hcard : Nat.card (TorChar X F N) * Nat.card H = Nat.card A) (α : X) :
    (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
    Module.finrank F (classSub S N α) * Nat.card (TorChar X F N) = Module.finrank F E ∧
    ∀ U : Submodule F E, U ≤ classSub S N α → (∀ h ∈ H, ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = classSub S N α := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  have : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := F)
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hd
      omega
    · exact h
  have ext : ∀ v v', (∀ α, S α v = S α v') → v = v' := fun v v' h =>
    sub_eq_zero.1 (hS _ fun α => by rw [map_sub, h, sub_self])
  choose c hcT using hT
  let l₀ : TorChar X F N → (E ≃ₗ[F] E) := fun τ => (Φ (a τ)).trans (LinearEquiv.smulOfUnit (c τ)⁻¹)
  have l₀e : ∀ τ v, l₀ τ v = (((c τ)⁻¹ : Fˣ) : F) • Φ (a τ) v := fun _ _ => rfl
  have hl : ∀ τ v β, S β (l₀ τ v) = (evalChar F N β τ : F) • S β v := fun τ v β => by
    rw [l₀e, map_smul, hcT, smul_smul, ← Units.val_mul, inv_mul_cancel_left]
  let l : TorChar X F N →* (E ≃ₗ[F] E) := MonoidHom.mk' l₀ fun τ τ' => LinearEquiv.ext fun v => ext _ _ fun β => by
    rw [LinearEquiv.mul_apply, hl, hl, hl, smul_smul, map_mul, Units.val_mul]
  let i : TorChar X F N ≃* a.range := MonoidHom.ofInjective ha
  let lam : a.range →* (E ≃ₗ[F] E) := l.comp i.symm.toMonoidHom
  have hlam : ∀ t : a.range, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v := fun t => by
    obtain ⟨τ, rfl⟩ := i.surjective t
    refine ⟨(c τ)⁻¹, fun v => ?_⟩
    show l₀ (i.symm (i τ)) v = _
    rw [i.symm_apply_apply]; rfl
  let Wt : (a.range →* Fˣ) → Submodule F E := fun χ =>
    { carrier := {v | ∀ t, lam t v = (χ t : F) • v}
      add_mem' := fun {v v'} h h' t => by rw [map_add (f := _), h t, h' t, smul_add]
      zero_mem' := fun t => by rw [map_zero, smul_zero]
      smul_mem' := fun r v h t => by rw [map_smul, h t, smul_comm] }
  have hWt : ∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v := fun _ _ => Iff.rfl
  let χ : a.range →* Fˣ := (evalChar F N α).comp i.symm.toMonoidHom
  have hW : Wt χ = classSub S N α := Submodule.ext fun v => ⟨fun h β hβ => by
      obtain ⟨τ, hτ⟩ := exists_evalChar_ne (F := F) hN hβ
      have h₁ : l₀ (i.symm (i τ)) v = (evalChar F N α (i.symm (i τ)) : F) • v := h (i τ)
      have h₂ := congrArg (S β) h₁
      rw [i.symm_apply_apply, hl, map_smul] at h₂
      by_contra h₃
      exact hτ (Units.ext (smul_left_injective F h₃ h₂)), fun h t => ext _ _ fun β => by
      refine (hl (i.symm t) v β).trans ?_
      rw [map_smul]
      by_cases hβ : ∃ mu, β = α + N • mu
      · obtain ⟨mu, rfl⟩ := hβ
        rw [evalChar_add_nsmul]; rfl
      · rw [h β hβ, smul_zero, smul_zero]⟩
  have hci : Nat.card a.range = Nat.card (TorChar X F N) := (Nat.card_congr i.toEquiv).symm
  have hTH : ∀ t ∈ a.range, ∀ h ∈ H, e t h = 1 := by
    rintro _ ⟨τ, rfl⟩ h hh
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have h₁ : Φ (a τ) (Φ h v) = Φ h (Φ (a τ) v) := ext _ _ fun β =>
      (hcT τ _ β).trans (hH h hh β _ _ _ (hcT τ v β)).symm
    have h₂ : Φ h (Φ (a τ) v) ≠ 0 := by simpa using hv
    apply HeisenbergWeightDim.units_eq_of_smul_eq h₂
    rw [← hc, h₁, Units.val_one, one_smul]
  have hperp := (perfectPairing_orthogonal_of_card F A e (HeisenbergWeightDim.comm_mul_left hm hc)
    (HeisenbergWeightDim.comm_mul_right hm hc) hn a.range H hTH (by rw [hci, hcard])).2.1
  refine ⟨exists_proj hN S (fun h => hA (by rw [← hcard, Nat.cast_mul, h, zero_mul])) (fun τ v => l₀ τ v) hl α, ?_,
    fun U hU hst => ?_⟩
  · rw [← hW, ← hci]
    exact (heisenberg_weightSpace_finrank F A E e Φ hA hd hm hc hn a.range lam hlam Wt hWt).2 χ
  · rw [← hW] at hU ⊢
    exact heisenberg_weightSpace_irreducible F A E e Φ hA hd hm hc hn a.range lam hlam Wt hWt χ U hU
      fun h hh => hst h ((hperp h).1 fun t ht => hh ⟨t, ht⟩)

end GlobalTheory.ClassWeight
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem eq_top_of_special_part : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y : Over (Spec (CommRingCat.of R))) [UniversallyClosed Y.hom] (U : Y.left.Opens), (∀ z : (thickObj R I 0 Y).left, pullback.fst Y.hom (thick R I 0) z ∈ U) → U = ⊤ := by
  intro R _ I hI Y _ U hU
  by_contra hne
  have hcl : IsClosed (Y.hom '' ((U : Set Y.left)ᶜ)) :=
    Y.hom.isClosedMap _ U.isOpen.isClosed_compl
  have hne' : ((U : Set Y.left)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    exact hne (TopologicalSpace.Opens.ext h)
  obtain ⟨y, hy⟩ := hne'
  let p : PrimeSpectrum R := Y.hom y
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have hspec : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 hpm
  have hq : q ∈ Y.hom '' ((U : Set Y.left)ᶜ) :=
    hspec.mem_closed hcl ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hyq⟩ := hq
  have hr : q ∈ Set.range (thick R I 0) := by
    have h1 : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        PrimeSpectrum.mem_zeroLocus]
      intro x hx
      have hx' : x ∈ I := by simpa using hx
      exact (Ideal.mem_sInf.1 (hI hx')) ⟨bot_le, hm⟩
    exact h1
  have h2 : y' ∈ Set.range (pullback.fst Y.hom (thick R I 0)) := by
    rw [Scheme.Pullback.range_fst]
    show Y.hom y' ∈ Set.range (thick R I 0)
    rw [hyq]; exact hr
  obtain ⟨z, rfl⟩ := h2
  exact hy' (hU z)

end GlobalTheory.Unif
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk :
    ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
      [Algebra (FractionRing R) F], IsIntegral (DegPre.BF D F).left ∧
        ∀ y : (DegPre.BF D F).left, IsIntegrallyClosed ((DegPre.BF D F).left.presheaf.stalk y) := by
  intro R _ _ D F _ _
  have h₁ := D.P.isAb.smooth
  have h₂ := D.P.isAb.geomConnected
  let j : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) := DegPre.jFR (R := R) F
  let g : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := pullback.fst j D.P.A.hom
  have hs : Smooth g := inferInstanceAs (Smooth (pullback.fst j D.P.A.hom))
  have hc : ConnectedSpace (DegPre.BF D F).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.P.A.hom) j
      (pullback.snd j D.P.A.hom) (pullback.fst j D.P.A.hom) (IsPullback.of_hasPullback j D.P.A.hom).flip
  exact ⟨isIntegral_of_smooth_field_of_connectedSpace g, fun y ↦
    ((isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ g hs).2.1 y).2⟩

end GlobalTheory
end
