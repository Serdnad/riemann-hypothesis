module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3PadicGlobal
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle007
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle031
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle012
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LowerBoundOfBaseSetting
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle015
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightGapDeltaEqAntisymmetric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle013
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc

@[expose] public section

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.finite_vertical_recursion : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (a : K → ℕ) (s : MRing ι ℤ), IsMultiHomog s a → s ∉ P → ∀ (L : Fin D → HermLine ι) (A : HermLine ι), (Function.support fun p : Nat.Primes => vertAt p P s (List.ofFn fun j => (L j).a)).Finite ∧ recR I P L A s = (∑ᶠ W, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) + (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn fun j => (L j).a) : ℝ)) - arInt P s A L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.RecSplit.recR_split | exact GlobalTheory.CompanionTheory.Ar.Num.RecSplit.recR_split | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.RecSplit.recR_split <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.flag_m3_padic_global : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (p : Nat.Primes) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (S : Finset Nat.Primes) (T : LocPair ι ℤ (Ψ × Fin N)), T.IsVertOff (mCoordIdeal y) S → (AtPlacesOver A Ω p fun O _ _ _ _ => FlagChernComparison (pointIdeal O y) D p j φ (T.map (Int.castRingHom O))) → FlagChernComparison (extTo (ZP p) (mCoordIdeal y)) D p j φ (T.map (Int.castRingHom (ZP p))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PlacesFlagM3.flag_m3_padic | exact GlobalTheory.CompanionTheory.Ar.Num.PlacesFlagM3.flag_m3_padic | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PlacesFlagM3.flag_m3_padic <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3

noncomputable section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_support_finite (P : Ideal (MRing ι O)) (f : MRing ι O) :
    (Function.support (divCycle P f)).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp [divCycle, h]

theorem C_not_mem {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {a : O} (ha : a ≠ 0) :
    (C a : MRing ι O) ∉ P := by
  intro h
  have h' : a ∈ P.comap (C : O →+* MRing ι O) := h
  rw [hP.noTorsion] at h'
  exact ha (by simpa using h')

theorem laNum_eq (P : Ideal (MRing ι O)) (a : O) {r : ℕ} (x : Fin r → K → ℤ) (k : ℕ)
    (Q : List (K → ℤ)) :
    ((laNum P a x k Q : ℤ) : ℝ) =
      (k : ℝ) * cycNum (divCycle P (C a)) x (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ (k - 1)) Q := by
  have h := (cycNum_int_and_comb O K ι (Fin r) x Q).1 (divCycle P (C a))
    (divCycle_support_finite P (C a)) (psum (Fin r) ℤ (k - 1))
  have e : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin r) ℤ (k - 1)) =
      ∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ (k - 1) := by

    simp [psum, map_sum]
  rw [e] at h
  rw [h, laNum]
  push_cast
  rfl

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]

theorem liePs_inl (j j' m : ℕ) (τ : Ψ) :
    (liePs (N := j + j') j m (Sum.inl τ) : MvPolynomial (Ψ × Fin (j + j')) ℝ) =
      rename (fun i : Fin j => (τ, Fin.castAdd j' i))
        (∑ i : Fin j, (X i : MvPolynomial (Fin j) ℝ) ^ m) := by

  simp only [liePs, map_sum, map_pow, rename_X, Finset.sum_filter, Fin.sum_univ_add]
  simp

theorem liePs_inr (j j' m : ℕ) (τ : Ψ) :
    (liePs (N := j + j') j m (Sum.inr τ) : MvPolynomial (Ψ × Fin (j + j')) ℝ) =
      rename (fun i : Fin j' => (τ, Fin.natAdd j i))
        (∑ i : Fin j', (-(X i : MvPolynomial (Fin j') ℝ)) ^ m) := by

  simp only [liePs, map_sum, map_pow, map_neg, rename_X, Finset.sum_filter, Fin.sum_univ_add]
  have h0 : ∀ x : Fin j, ¬ j ≤ (x : ℕ) := fun x => not_le.2 x.2
  simp [h0]

theorem cycNum_neg {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d)
    {a : O} (ha : a ≠ 0) {r : ℕ} (cls : Fin r → K → ℤ) (m : ℕ) (Q : List (K → ℤ))
    (hQ : m + Q.length = d) :
    cycNum (divCycle P (C a)) (fun i => -cls i) (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m) Q =
      cycNum (divCycle P (C a)) cls (∑ i : Fin r, (-(X i : MvPolynomial (Fin r) ℝ)) ^ m) Q := by
  have hC : IsMultiHomog (C a : MRing ι O) (0 : K → ℕ) := isWeightedHomogeneous_C _ a
  have hH : (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m).IsHomogeneous m :=
    IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_X ℝ i).pow m
  have h := (GlobalTheory.T.divisor_cycle_substitution O ϖ hϖ K ι P d hP 0 0 (C a) (C a) hC hC (C_not_mem hP ha) (C_not_mem hP ha)
    (Fin r) (Fin r) cls (fun t i => if t = i then -1 else 0) _ m hH Q hQ).2
  have e1 : (fun t : Fin r => ∑ i, (if t = i then (-1 : ℤ) else 0) • cls i) = fun i => -cls i := by
    funext t
    simp
  have e2 : aeval (fun t : Fin r => ∑ i, (C (((if t = i then (-1 : ℤ) else 0 : ℤ)) : ℝ) * X i :
      MvPolynomial (Fin r) ℝ)) (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m) =
      ∑ i : Fin r, (-(X i : MvPolynomial (Fin r) ℝ)) ^ m := by

    simp [map_sum, apply_ite]
  rw [e1, e2] at h
  exact h

end

end GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3

namespace GlobalTheory.CompanionTheory.Ar.Num


open GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3 in
theorem flag_m3_of_local_m3 : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ), (p : O) ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j j' : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair ι O (Ψ × Fin (j + j'))) (lie : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j) (fun _ : Ψ => j')) σ))) (om : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j') (fun _ : Ψ => j)) σ))), (∀ τ, lie (Sum.inl τ) = T.comp fun i : Fin j => (τ, Fin.castAdd j' i)) → (∀ τ, om (Sum.inl τ) = T.comp fun i : Fin j' => (τ, Fin.natAdd j i)) → (∀ τ k Q, Q.length + k = d + 1 → laNum P (p : O) (lie (Sum.inr τ)).x k Q = laNum P (p : O) (fun i : Fin j' => -T.x (τ, Fin.natAdd j i)) k Q) → LabelChernComparison P d p φ lie om → FlagChernComparison P d p j φ T := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP p hp Ψ _ _ j j' φ T lie om hl ho hr hM τ k hk Q hQ
  set Z := divCycle P (C (p : O)) with hZ
  have hm : k - 1 + Q.length = d := by omega

  have hlab : ∀ τ' : Ψ ⊕ Ψ, ((laNum P (p : O) (lie τ').x k Q : ℤ) : ℝ) =
      (k : ℝ) * cycNum Z T.x (liePs j (k - 1) τ') Q := by
    rintro (t | t)
    · have e : (lie (Sum.inl t)).x = fun i : Fin j => T.x (t, Fin.castAdd j' i) := by
        rw [hl t]; rfl
      have e' : ((laNum P (p : O) (lie (Sum.inl t)).x k Q : ℤ) : ℝ) =
          ((laNum P (p : O) (fun i : Fin j => T.x (t, Fin.castAdd j' i)) k Q : ℤ) : ℝ) :=
        congrArg (fun y : Fin j → K → ℤ => ((laNum P (p : O) y k Q : ℤ) : ℝ)) e
      rw [e', laNum_eq, liePs_inl, (GlobalTheory.T.cycle_number_rename).1 O K ι _ _ _ Z T.x]
      rfl
    · rw [hr t k Q hQ, laNum_eq, cycNum_neg hϖ hP hp _ _ Q hm, liePs_inr,
        (GlobalTheory.T.cycle_number_rename).1 O K ι _ _ _ Z T.x]
      rfl
  have hL := hM k hk Q hQ (Sum.inl τ)
  have e1 : (lie (Sum.inl τ)).ck P k Q = (T.comp fun i : Fin j => (τ, Fin.castAdd j' i)).ck P k Q :=
    congrArg (fun L : LocPair ι O (Fin j) => L.ck P k Q) (hl τ)
  have e2 : (om (Sum.inl τ)).ck P k Q = (T.comp fun i : Fin j' => (τ, Fin.natAdd j i)).ck P k Q :=
    congrArg (fun L : LocPair ι O (Fin j') => L.ck P k Q) (ho τ)
  have hadd := GlobalTheory.T.local_pair_split_sum O K ι j j' (T.comp fun i : Fin (j + j') => (τ, i)) P k Q
  have hlin := GlobalTheory.T.cycle_number_linear O K ι (Ψ × Fin (j + j')) Z T.x Q
  rw [e1, e2] at hL
  have hleft : (((T.comp fun i : Fin (j + j') => (τ, i)).ck P k Q : ℤ) : ℝ) =
      (((T.comp fun i : Fin j => (τ, Fin.castAdd j' i)).ck P k Q : ℤ) : ℝ) +
      (((T.comp fun i : Fin j' => (τ, Fin.natAdd j i)).ck P k Q : ℤ) : ℝ) := by
    rw [hadd]
    push_cast
    rfl
  rw [hleft, hL, bracket]
  rw [hlin.2.1, hlin.2.2.1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ' _ => ?_
  rw [hlin.2.1, hlab τ']
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.power_sums_vanish_of_trivial_flags : NumericalSegre.Statement → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (N : ℕ) (x : Fin N → K → ℤ), (∀ W, IsFibreComp P W → TrivFlagAt W x) → PowerSumsVanish P d x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt | exact GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

section

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem antisymDegree_eq_dimFl' : GroundTheory.Heights₂.Heights.antisymDegree Ψ N = dimFl Ψ N := by
  simp [GroundTheory.Heights₂.Heights.antisymDegree, dimFl, Nat.choose_two_right]

theorem flMonoLines_eq (m : Ψ × Fin N →₀ ℕ) (d : ℕ) (hm : m.degree = d) :
    GroundTheory.Heights₂.Heights.LowerBoundFree.monoLines Ψ N m d =
      monoLines (GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N) m d := by
  funext k
  have hl : (Finsupp.toMultiset m).toList.length = d := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hm]
    rfl
  have hk : (k : ℕ) < (Finsupp.toMultiset m).toList.length := by
    rw [hl]
    exact k.2
  simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.monoLines, monoLines, dif_pos hk]

theorem linRoot_pow_eq (lam : Wt Ψ N) (n : ℕ) :
    linRoot lam ^ n = ((-1 : ℝ) ^ n) •
      ∏ _k : Fin n, ∑ x : Ψ × Fin N, C (lam x.1 x.2) * X x := by
  rw [linRoot, neg_pow, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_C_mul, map_pow, map_neg, map_one]

end

theorem hhFl_linRoot_pow : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (lam : Wt Ψ N), 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) = eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := by
  intro II hII Ψ _ _ N _ lam _ hP
  have hword : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N,
      hhFl Ψ N II (monomial (∑ k, Finsupp.single (w k) 1) 1) = (-1 : ℝ) ^ (dimFl Ψ N + 1) *
        II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
          (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
          (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k)) := by
    intro w
    obtain ⟨hdeg, σ, -, hI⟩ := GlobalTheory.T.monomial_lines_permutation II hII.1 _ _ (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
      _ (GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N) w hP
      (fun j => GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)
    have hdeg' : (∑ k, Finsupp.single (w k) 1 : Ψ × Fin N →₀ ℕ).degree =
        GroundTheory.Heights₂.Heights.LowerBoundFree.dimFl Ψ N + 1 := hdeg
    have e1 : II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.monoLines Ψ N (∑ k, Finsupp.single (w k) 1) (dimFl Ψ N + 1)) =
      II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
        (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k)) := by
      rw [flMonoLines_eq _ _ hdeg]
      exact hI
    rw [HhModel.hhFl_monomial, GroundTheory.Heights₂.Heights.LowerBoundFree.hFlMono, if_pos hdeg', hdeg, one_mul]
    exact congrArg (fun t => (-1 : ℝ) ^ (dimFl Ψ N + 1) * t) e1
  have hpoly : PB.hFlPoly Ψ N II = PB.formPoly (dimFl Ψ N + 1) fun w =>
      II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
        (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k)) := by
    rw [PB.hFlPoly, antisymDegree_eq_dimFl']
  rw [linRoot_pow_eq, map_smul, GlobalTheory.T.functional_product_linear_forms _ _ (hhFl Ψ N II) (fun _ x => lam x.1 x.2), hpoly,
    (PB.formPoly_isHomogeneous_and_eval (Ψ × Fin N) (dimFl Ψ N + 1) _).2]
  simp only [hword, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : ((-1 : ℝ) ^ (dimFl Ψ N + 1)) * (-1 : ℝ) ^ (dimFl Ψ N + 1) = 1 := by
    rw [← mul_pow]
    simp
  linear_combination (∏ k, lam (w k).1 (w k).2) *
    II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
      (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
      (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k)) * h2

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem _root_.GlobalTheory.T.weight_gap_delta_eq_antisymmetric : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), PB.toWt (gapDelta Ψ N) = GroundTheory.Heights₂.Heights.antisymDelta Ψ N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_gapDelta_eq_antisymDelta | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_gapDelta_eq_antisymDelta | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_gapDelta_eq_antisymDelta <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem ht_combLine_integral_multiple : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ) (W : Ideal (MRing M.ι)), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.IsPt W → 0 < degC W ∧ II M.K M.ι W 1 ![combLine (M.line t) n] = q * M.ht II t lam s W * degC W := by
  intro II hII Ψ _ N M t lam s q n W hn hW
  have hpos : 0 < degC W := GroundTheory.Heights₂.Heights.LowerBoundFree.degC_pos_of_isArithVar_one hW.1
  refine ⟨hpos, ?_⟩
  have hl : ∀ j, IsSmoothHerm (M.line t j) := by
    intro j
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hupd : ∀ B : HermLine M.ι, Function.update (![M.A] : Fin 1 → HermLine M.ι) 0 B = ![B] := by
    intro B
    funext k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp
  have hL : ∀ i, IsSmoothHerm ((![M.A] : Fin 1 → HermLine M.ι) i) := by
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact M.A_smooth
  have h := GlobalTheory.T.arith_intersection_multilinear II hII M.K M.ι W 1 ![M.A] 0 (Option (Ψ × Fin N)) (M.line t) n hW.1 hL hl
  simp only [hupd] at h
  have hd : (degC W : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [h, RootModel.ht, mul_assoc, div_mul_cancel₀ _ hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hn j, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Top
end
