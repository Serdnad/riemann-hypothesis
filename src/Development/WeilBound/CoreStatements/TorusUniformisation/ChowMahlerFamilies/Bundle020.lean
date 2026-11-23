module

import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProduct
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle012
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle007
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DualIntegralLattice
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimGe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle058
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle063
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle024
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.Xgn.A_xgr_r_om

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
  {F : Type} [Field F]

theorem mem_x_ideal_iff (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C (r * χ a)) ∈ M := by
  rw [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  have he : (r • fun a : F => algebraMap R C (χ a)) = fun a => algebraMap R C (r * χ a) := by
    funext a
    simp [Algebra.smul_def, map_mul]
  rw [he]

theorem mem_aug (M : Submodule R (F → C)) (g : F → C) :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

theorem v_le_of_mem (hv : v.Integers R) {a b : R} (h : a ∈ Ideal.span {b}) :
    v (algebraMap R C a) ≤ v (algebraMap R C b) := by
  exact hv.le_of_dvd (Ideal.mem_span_singleton.mp h)

theorem v_eq_of_span (hv : v.Integers R) {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    v (algebraMap R C a) = v (algebraMap R C b) := by
  apply le_antisymm
  · apply v_le_of_mem hv
    rw [← h]
    exact Ideal.mem_span_singleton_self a
  · apply v_le_of_mem hv
    rw [h]
    exact Ideal.mem_span_singleton_self b

theorem sq_bound (hv : v.Integers R) {X : Type} (s : Set (X → C)) (l : (X → C) →ₗ[R] C)
    (b : NNReal) (h : ∀ g ∈ s, ∀ g' ∈ s, v (l (g * g')) ≤ b) :
    ∀ g ∈ sqIdeal (Submodule.span R s), v (l g) ≤ b := by
  apply GlobalTheory.CompanionTheory.Ar.GR.ROm.sq_bound <;> assumption

variable [Fintype F] [DecidableEq F]

theorem pow_mem_aug (AA : HopfOrder (C := C) R F) {g : F → C} (hg : g ∈ augIdeal AA.carrier)
    (k : ℕ) : g ^ (k + 1) ∈ augIdeal AA.carrier := by
  rw [mem_aug] at hg ⊢
  refine ⟨?_, by simp [Pi.pow_apply, hg.2]⟩
  induction k with
  | zero => simpa using hg.1
  | succ n ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg.1

theorem pow_mem_sq (AA : HopfOrder (C := C) R F) (χ : MulChar F R) {c : R}
    (hc : c ∈ xIdeal AA.carrier χ) {k : ℕ} (hk : 2 ≤ k) :
    (fun a => algebraMap R C (c ^ k * (χ ^ k) a)) ∈ sqIdeal (augIdeal AA.carrier) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hg : (fun a => algebraMap R C (c * χ a)) ∈ augIdeal AA.carrier := by
    rw [mem_aug]
    refine ⟨(mem_x_ideal_iff _ χ c).mp hc, ?_⟩
    simp [MulChar.map_nonunit χ not_isUnit_zero]
  have he : (fun a => algebraMap R C (c ^ (j + 2) * (χ ^ (j + 2)) a)) =
      (fun a => algebraMap R C (c * χ a)) * (fun a => algebraMap R C (c * χ a)) ^ (j + 1) := by
    funext a
    simp only [Pi.mul_apply, Pi.pow_apply, MulChar.pow_apply' χ (by omega : j + 2 ≠ 0), map_pow,
      map_mul]
    ring
  rw [he]
  unfold sqIdeal
  exact Submodule.subset_span ⟨_, hg, _, pow_mem_aug AA hg j, rfl⟩

theorem sq_le (AA : HopfOrder (C := C) R F) : sqIdeal (augIdeal AA.carrier) ≤ AA.carrier := by
  unfold sqIdeal
  rw [Submodule.span_le]
  rintro h ⟨f, hf, f', hf', rfl⟩
  exact AA.mul_mem f f' ((mem_aug _ f).mp hf).1 ((mem_aug _ f').mp hf').1

omit [Fintype F] [DecidableEq F] in
theorem eig_fun (χ : MulChar F R) (r : R) (a x : F) :
    algebraMap R C (r * χ (a • x)) = algebraMap R C (χ a) * algebraMap R C (r * χ x) := by
  simp only [smul_eq_mul, map_mul]; ring

end

theorem digits {p f m : ℕ} (h1 : 1 ≤ m) (h2 : m < p ^ f) :
    ∃ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) ∧ ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
  apply GlobalTheory.CompanionTheory.Ar.GR.ROm.digits <;> assumption

theorem hasLen_quot {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) {M : Type} [AddCommGroup M] [Module R M] (φ : R →ₗ[R] M)
    (hφ : Function.Surjective φ) (δ : R) (hk : LinearMap.ker φ = Ideal.span {δ}) :
    HasLen v R M (v (algebraMap R C δ)) := by
  refine ⟨1, fun _ => δ, ⟨?_⟩, by simp⟩
  exact ((φ.quotKerEquivOfSurjective hφ).symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    (LinearEquiv.funUnique (Fin 1) R (R ⧸ Ideal.span {δ})).symm

end PositivityTheory.Xgn.A_xgr_r_om
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.DualLatticeFamily

theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.dotDual
  simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

noncomputable def dotB (Ω : Type) [Field Ω] (r : ℕ) : (Fin r → Ω) →ₗ[Ω] (Fin r → Ω) →ₗ[Ω] Ω :=
  LinearMap.mk₂ Ω (fun a b => a ⬝ᵥ b) (fun a a' b => add_dotProduct a a' b)
    (fun c a b => smul_dotProduct c a b) (fun a b b' => dotProduct_add a b b')
    (fun c a b => dotProduct_smul c a b)

theorem dotB_apply {Ω : Type} [Field Ω] {r : ℕ} (a b : Fin r → Ω) : dotB Ω r a b = a ⬝ᵥ b := rfl

theorem dotB_bij (Ω : Type) [Field Ω] (r : ℕ) : Function.Bijective (dotB Ω r).flip := by
  classical
  refine ⟨fun a b h => funext fun i => ?_, fun ψ => ⟨fun i => ψ (Pi.single i 1), ?_⟩⟩
  · have := LinearMap.congr_fun h (Pi.single i 1)
    simpa [dotB_apply] using this
  · refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : Fin r → Ω) = x • (Pi.single i 1 : Fin r → Ω) := by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rw [LinearMap.flip_apply, dotB_apply, single_dotProduct, hx, map_smul, smul_eq_mul]

theorem overlap {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {T : Type} (x : T → Ω) {r : ℕ}
    (i j : T) (hi : x i ≠ 0) (hj : x j ≠ 0) (Li Lj : AddSubgroup (Fin r → Ω))
    (hov : ∀ e ∈ Lj, ∃ m : ℕ, (x j / x i) ^ m • e ∈ Li) (hL : LocFree (chartRing O x j) r Lj)
    (w : Fin r → Ω) (hw : w ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual (chartRing O x i) Li) :
    ∃ m : ℕ, (x i / x j) ^ m • w ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual (chartRing O x j) Lj := by
  rw [mem_dotDual] at hw
  have hdiv : x i / x j ∈ chartRing O x j := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j i
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.Ar.Num.Reflexive.exists_uniform_denominator (chartRing O x j) r Lj hL
    (x i / x j) hdiv ((dotB Ω r).flip w) fun e he => by
      obtain ⟨m, hm⟩ := hov e he
      have h1 := hw _ hm
      rw [smul_dotProduct, smul_eq_mul] at h1
      obtain ⟨m', hm'⟩ : ∃ m' : ℕ, (x i / x j) ^ m' * ((x j / x i) ^ m * (e ⬝ᵥ w)) ∈ chartRing O x j :=
        ReciprocityTheory.ChartRestriction.G.Geo.exists_pow_mul_mem_chartRing x i j hi h1
      have hone : (x i / x j) ^ m * (x j / x i) ^ m = 1 := by
        rw [← mul_pow, div_mul_div_comm, _root_.mul_comm (x i), div_self (mul_ne_zero hj hi), one_pow]
      have h2 := mul_mem (pow_mem hdiv m) hm'
      have h3 : (x i / x j) ^ m * ((x i / x j) ^ m' * ((x j / x i) ^ m * (e ⬝ᵥ w))) =
          (x i / x j) ^ m' * (e ⬝ᵥ w) := by
        calc _ = (x i / x j) ^ m' * (e ⬝ᵥ w) * ((x i / x j) ^ m * (x j / x i) ^ m) := by ring
          _ = _ := by rw [hone, _root_.mul_one]
      rw [h3] at h2
      exact ⟨m', h2⟩
  refine ⟨m, (mem_dotDual _ _ _).2 fun l hl => ?_⟩
  rw [dotProduct_smul, smul_eq_mul]
  exact hm l hl

end PositivityTheory.Xgn.DualLatticeFamily

open PositivityTheory.Xgn.DualLatticeFamily in
theorem PositivityTheory.Xgn.dual_lattice_family : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (r : ℕ) (Γ : (∀ k, J k) → AddSubgroup (Fin r → Ω)), IsLatFamily O y Γ → (∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (Γ c)) → IsLatFamily O y (fun c => dotDual (chartRing O (mseg y) c) (Γ c)) ∧ ∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (dotDual (chartRing O (mseg y) c) (Γ c)) := by
  intro O _ Ω _ _ K _ J _ y r Γ hΓ hL
  refine ⟨⟨fun s _ a ha w hw => ?_, fun s t hs ht w hw => ?_⟩, fun c hc => ?_⟩
  · refine (mem_dotDual _ _ _).2 fun l hl => ?_
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha ((mem_dotDual _ _ _).1 hw l hl)
  · exact overlap (mseg y) s t hs ht (Γ s) (Γ t) (hΓ.2 t s ht hs) (hL t ht) w hw
  · exact (GlobalTheory.CompanionTheory.Ar.Num.DualLattice.locFree_dual _ (dotB Ω r) (dotB_bij Ω r) r (Γ c) _ (hL c hc)
      fun w => mem_dotDual _ _ w).1
end

section

namespace PositivityTheory.Xgn.GramDeterminantUnit
open NumberField GlobalTheory.CompanionTheory.Ar

end PositivityTheory.Xgn.GramDeterminantUnit

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem PositivityTheory.Xgn.gram_determinant_unit_mod_p : ∀ (E : Type) [Field E] [NumberField E] (cc : E ≃+* E) (p R N : ℕ) [Fact p.Prime], 1 ≤ R → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)), (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv cc a • y)) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ¬ IsUnit (p : O) → ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) → ∃ C : Matrix (Fin N) (Fin N) Ω, (∀ i j, C i j ∈ (algebraMap O Ω).range) ∧ (Matrix.of fun i j => ∑ k, σ (HT.dualInt E k) * ((e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : Ω)) * C = 1 :=
  _root_.UpperTheory.Reformulated.B.DualIntegralLattice.main
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TorsionGroupBaseChange

theorem pow_congr {S Y : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : Y ⟶ S} (h : f = f') (N : ℕ)
    (g : Over.mk f ⟶ G) (g' : Over.mk f' ⟶ G) (hg : g.left = g'.left) : g ^ N = 1 ↔ g' ^ N = 1 := by
  subst h
  have : g = g' := Over.OverMorphism.ext hg
  rw [this]

theorem mul_congr {S Y : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : Y ⟶ S} (h : f = f')
    (u v : Over.mk f ⟶ G) (u' v' : Over.mk f' ⟶ G) (hu : u.left = u'.left) (hv : v.left = v'.left) :
    (u * v).left = (u' * v').left := by
  subst h
  have h1 : u = u' := Over.OverMorphism.ext hu
  have h2 : v = v' := Over.OverMorphism.ext hv
  rw [h1, h2]

def Kill {S Y : Scheme.{0}} (G : Over S) [GrpObj G] (N : ℕ) (g : Y ⟶ G.left) : Prop :=
  (Over.homMk g rfl : Over.mk (g ≫ G.hom) ⟶ G) ^ N = 1

theorem kernel' {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}}
    (b : Y ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ G.left) (hg : g ≫ G.hom = b ≫ x) :
    Kill G N g ↔ ∃ y : Y ⟶ Γ.G.left, y ≫ Γ.G.hom = b ∧ y ≫ i = g := by
  unfold Kill
  constructor
  · intro hk
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk b
    let g₀ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g hg
    have hk' : g₀ ^ N = 1 := (pow_congr hg.symm N g₀ (Over.homMk g rfl) rfl).2 hk
    obtain ⟨y, hy⟩ := (h.kernel Y' g₀).1 hk'
    exact ⟨y.left, Over.w y, by simpa [g₀] using hy⟩
  · rintro ⟨y, hy1, hy2⟩
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk b
    let g₀ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g hg
    have hk' : g₀ ^ N = 1 :=
      (h.kernel Y' g₀).2 ⟨Over.homMk y hy1, by simpa [g₀] using hy2⟩
    exact (pow_congr hg.symm N g₀ (Over.homMk g rfl) rfl).1 hk'

theorem inj' {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}}
    (y z : Y ⟶ Γ.G.left) (h1 : y ≫ Γ.G.hom = z ≫ Γ.G.hom) (h2 : y ≫ i = z ≫ i) : y = z := by
  let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (z ≫ Γ.G.hom)
  have := h.inj Y' (Over.homMk y h1) (Over.homMk z rfl) (by simpa using h2)
  simpa using congrArg Over.Hom.left this

end PositivityTheory.Xgn.TorsionGroupBaseChange

open PositivityTheory.Xgn.TorsionGroupBaseChange in
theorem PositivityTheory.Xgn.torsion_group_base_change : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R'] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S), Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = x' → ∀ (N : ℕ) (i : Γ.G.left ⟶ G.left) (i' : Γ'.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Γ'.IsTorsionAlong G x' N i' → ∀ (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp (algebraMap R R') → (∀ t, Spec.map (CommRingCat.ofHom a) ≫ (Γ.pt t).left ≫ i = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ (algebraMap R R') F := by
  intro R R' _ _ _ _ _ T _ Γ Γ' S G _ x x' hx N i i' h h' a ha hpt
  have hKi' : Kill G N i' := (kernel' h' Γ'.G.hom i' h'.isOver).2 ⟨𝟙 _, by simp, by simp⟩
  have hi'x : i' ≫ G.hom = (Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫ x := by
    rw [Category.assoc, hx]
    exact h'.isOver
  obtain ⟨F, hF1, hF2⟩ := (kernel' h _ i' hi'x).1 hKi'
  refine ⟨F, hF2, ?_⟩
  have lift : ∀ {Z : Scheme.{0}} (u : Z ⟶ Γ.G.left) (v : Z ⟶ Spec (CommRingCat.of R')),
      u ≫ Γ.G.hom = v ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) →
      ∃ l : Z ⟶ Γ'.G.left, l ≫ F = u ∧ l ≫ Γ'.G.hom = v := by
    intro Z u v huv
    have hk : Kill G N (u ≫ i) :=
      (kernel' h (u ≫ Γ.G.hom) (u ≫ i) (by simp only [Category.assoc, h.isOver])).2 ⟨u, rfl, rfl⟩
    have hg : (u ≫ i) ≫ G.hom = v ≫ x' := by
      rw [Category.assoc, h.isOver, ← Category.assoc, huv, Category.assoc, hx]
    obtain ⟨l, hl1, hl2⟩ := (kernel' h' v (u ≫ i) hg).1 hk
    refine ⟨l, inj' h _ _ ?_ ?_, hl1⟩
    · rw [Category.assoc, hF1, ← Category.assoc, hl1, huv]
    · rw [Category.assoc, hF2, hl2]
  have uniq : ∀ {Z : Scheme.{0}} (l₁ l₂ : Z ⟶ Γ'.G.left), l₁ ≫ F = l₂ ≫ F →
      l₁ ≫ Γ'.G.hom = l₂ ≫ Γ'.G.hom → l₁ = l₂ := by
    intro Z l₁ l₂ e1 e2
    refine inj' h' _ _ e2 ?_
    rw [← hF2, ← Category.assoc, e1, Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hF1
      (fun s => Classical.choose (lift s.fst s.snd s.condition))
      (fun s => (Classical.choose_spec (lift s.fst s.snd s.condition)).1)
      (fun s => (Classical.choose_spec (lift s.fst s.snd s.condition)).2)
      (fun s m h1 h2 => uniq _ _ ?_ ?_))
    · rw [h1, (Classical.choose_spec (lift s.fst s.snd s.condition)).1]
    · rw [h2, (Classical.choose_spec (lift s.fst s.snd s.condition)).2]
  · intro S' u v u₀ v₀ hu hv
    apply inj' h
    · simp only [Category.assoc, hF1, Over.w, Over.w_assoc, Over.mk_hom]
    · let U₀ : Over.mk ((Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))).hom ≫ x) ⟶ G :=
        Over.homMk (u₀.left ≫ i) (by simp [h.isOver])
      let V₀ : Over.mk ((Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))).hom ≫ x) ⟶ G :=
        Over.homMk (v₀.left ≫ i) (by simp [h.isOver])
      let U₁ : Over.mk (S'.hom ≫ x') ⟶ G := Over.homMk (u.left ≫ i') (by simp [h'.isOver])
      let V₁ : Over.mk (S'.hom ≫ x') ⟶ G := Over.homMk (v.left ≫ i') (by simp [h'.isOver])
      have e0 := h.mul (Over.mk (S'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))) u₀ v₀ U₀ V₀ rfl rfl
      have e1 := h'.mul S' u v U₁ V₁ rfl rfl
      have e2 : (U₀ * V₀).left = (U₁ * V₁).left :=
        mul_congr (by simp [hx]) U₀ V₀ U₁ V₁ (by simp [U₀, U₁, hu, hF2]) (by simp [V₀, V₁, hv, hF2])
      rw [← e0, e2, e1, Category.assoc, hF2]
  · refine ⟨FractionRing R, inferInstance, algebraMap R (FractionRing R), RingHom.id _, a,
      fun t => (Γ.pt t).left, fun _ _ e => e, RingHom.id_comp _, ha, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · exact Over.w (Γ.pt t)
    · simp
    · apply inj' h
      · simp only [Category.assoc, Over.w, hF1, Over.w_assoc, Over.mk_hom]
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ha]
      · simp only [Category.assoc, hF2]
        exact hpt t
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceDifferentials

theorem main (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] (p : ℕ) [hpp : Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ NumberField.discr E) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    (m : Ideal A) [m.IsPrime] (hm : (p : A) ∈ m) (O : Type) [CommRing O] [IsLocalRing O] [Algebra A O]
    [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (σ : E →+* Ω) :
    (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧
      ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 := by
  refine ⟨fun a => ?_, ?_⟩
  · have h1 : IsIntegral ℤ (σ (a : E)) :=
      (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := A)).1 h1
    exact ⟨algebraMap A O b, by rw [← IsScalarTower.algebraMap_apply, hb]⟩
  · set n : ℕ := (NumberField.discr E).natAbs with hn
    have hx : ((n : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := by
      rw [hn, ← NumberField.absNorm_differentIdeal E (𝓞 E)]
      exact Ideal.absNorm_mem _
    have hpn : ¬ p ∣ n := fun h => hp (Int.natCast_dvd.2 h)
    have hnm : ((n : ℕ) : A) ∉ m := by
      intro h
      have hc : IsCoprime (p : A) (n : A) := Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hpp.out).2 hpn)
      obtain ⟨u, v, huv⟩ := hc
      exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one m).2
        (huv ▸ m.add_mem (m.mul_mem_left u hm) (m.mul_mem_left v h)))
    have hu : IsUnit (algebraMap A O (n : A)) :=
      IsLocalization.map_units O (⟨(n : A), hnm⟩ : m.primeCompl)
    obtain ⟨o, ho⟩ := hu.exists_left_inv
    refine ⟨(n : 𝓞 E), hx, o, ?_⟩
    have h2 := congrArg (algebraMap O Ω) ho
    simp only [map_mul, map_natCast, map_one] at h2
    have h3 : σ (((n : ℕ) : 𝓞 E) : E) = (n : Ω) := by simp
    rw [h3, h2]

end PositivityTheory.Xgn.SequenceDifferentials

theorem PositivityTheory.Xgn.sequence_differentials_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧ ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ hp A _ _ _ m _ hm O _ _ _ _ _ _ _ σ
  exact PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hp A m hm O σ
end

section

namespace PositivityTheory.Xgn.A_s_joinright

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.full GenericDimBound.full GenericDimGe.proof SpecialIdealCorresp.full
    SpecialIdealMultiHomog.full SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialQuotDim.full
    ComponentDim.proof

theorem pairNumRelabel : PairNumberRelabelAlt.Statement :=
  PairNumberRelabelAlt.proof (VerticalComponentFibre.proof fibreVarieties)

theorem of_pullback (h : PairNumberPullback.Statement) : FlagModelJoinRightAlt.Statement :=
  FlagModelJoinRightAlt.proof JoinVerticalDivisor.proof (FlagPairJoinRight.proof JoinVerticalDivisorRight.proof)
    (PairNumberJoinRight.proof
      (PairNumberJoinLeft.proof h JoinVerticalDivisorLeft.proof BirationalJoin.proof)
      JoinVerticalDivisorRight.proof pairNumRelabel)

end PositivityTheory.Xgn.A_s_joinright
end
