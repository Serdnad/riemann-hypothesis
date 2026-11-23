module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle681
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle301
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1079
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle683
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle682
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.PosWeight

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow_self (P : LocPrime l) (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem norm_nat_eq_one {a : ℕ} (ha : ¬ l ∣ a) : ‖(a : Om l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr ha)

theorem norm_frK_pow (P : LocPrime l) (K : FinExt l) (n : ℕ) (c : ↥(K0 K)) :
    ‖(((frK P K ^ n) c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1, ih]

def co {K : FinExt l} (e : ℕ) (lam : ℕ → ↥(K0 K)) (i : ℕ × Bool) : ↥(K0 K) :=
  if i.2 then lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹ else -(lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹)

def ex (l s : ℕ) (i : ℕ × Bool) : ℕ := if i.2 then (1 + l ^ s) * i.1 else i.1

theorem formula_pos : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  intro LT l _ AI hT K s hs e he g hg hχ lam d hlam hd hrec
  have hl : l.Prime := Fact.out
  have hu : ¬ l ∣ 1 + l ^ s := by
    intro h
    have h1 : l ∣ l ^ s := dvd_pow_self l (by have := hs.1; omega)
    exact hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left h1).mp h))
  have hmem : ∀ a ∈ primeTo l s, ¬ l ∣ a := fun a ha => (Finset.mem_filter.mp ha).2
  have hne : ∀ a ∈ primeTo l s, (a : Om l) ≠ 0 := fun a ha h => by
    have := norm_nat_eq_one (hmem a ha)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hne' : ∀ a ∈ primeTo l s, (a : ↥(K0 K)) ≠ 0 := fun a ha h =>
    hne a ha (by simpa using congrArg (fun x : ↥(K0 K) => (x : Om l)) h)
  set T : Finset (ℕ × Bool) := primeTo l s ×ˢ Finset.univ with hTdef
  have hc : ∀ i ∈ T, ‖(co e lam i : Om l)‖ ≤ 1 ∧ ¬ l ∣ ex l s i := by
    rintro ⟨a, b⟩ hi
    have ha : a ∈ primeTo l s := (Finset.mem_product.mp hi).1
    have h1 := norm_nat_eq_one (hmem a ha)
    have h2 : ‖(lam a : Om l) * ((a : Om l) ^ e)⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, norm_pow, h1]
      simpa using hlam a
    cases b
    · refine ⟨?_, hmem a ha⟩
      simpa [co, -norm_mul] using h2
    · refine ⟨by simpa [co, -norm_mul] using h2, ?_⟩
      intro h
      rcases (Nat.Prime.dvd_mul hl).mp h with h | h
      · exact hu h
      · exact hmem a ha h
  have hall : ∀ j : ℕ, ∃ dj : ↥(K0 K), j ≤ e → (‖(dj : Om l)‖ ≤ 1 ∧
      dj - (l : ↥(K0 K)) ^ j * frK (LT l) K dj =
        (frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) ∧
      (j = e → dj = (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d) := by
    intro j
    by_cases hje : j = e
    · subst hje
      refine ⟨(((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d, fun _ => ⟨⟨?_, ?_⟩, fun _ => rfl⟩⟩
      · have h1 : ‖((1 + l ^ s : ℕ) : Om l) ^ j - 1‖ ≤ 1 := by
          have := IsUltrametricDist.norm_intCast_le_one (Om l) (((1 + l ^ s : ℕ) : ℤ) ^ j - 1)
          simpa using this
        have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ j - 1) * (d : Om l) := by simp
        rw [h2, norm_mul]
        exact mul_le_one₀ h1 (norm_nonneg _) hd
      · have h3 : ∑ i ∈ T, co j lam i * (ex l s i : ↥(K0 K)) ^ j =
            (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * ∑ a ∈ primeTo l s, lam a := by
          rw [hTdef, Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          have := hne' a ha
          simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, Nat.cast_mul]
          field_simp
          ring
        rw [h3, map_mul, map_mul, ← hrec]
        simp only [map_sub, map_pow, map_natCast, map_one]
        ring
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · refine ⟨0, fun _ => ⟨⟨by simp, ?_⟩, fun h => absurd h hje⟩⟩
        rw [hTdef, Finset.sum_product]
        simp [co]
      · obtain ⟨dj, h1, h2⟩ := (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l (LT l) K).2 j hj
          ((frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) (by
            rw [norm_frK_pow, AddSubmonoidClass.coe_finsetSum]
            refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
            have h2 : ((co e lam i * (ex l s i : ↥(K0 K)) ^ j : ↥(K0 K)) : Om l) =
              (co e lam i : Om l) * (ex l s i : Om l) ^ j := by simp
            rw [h2, norm_mul, norm_pow, norm_nat_eq_one (hc i hi).2]
            simpa using (hc i hi).1)
        exact ⟨dj, fun _ => ⟨⟨h1, h2⟩, fun h => absurd h hje⟩⟩
  choose D hD using hall
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.dualExp_teichmuller_power_sum_formula LT l AI hT K s hs e g hg hχ (ℕ × Bool) T (co e lam) (ex l s) D hc
    (fun j hj => (hD j hj).1)
  refine ⟨z, hz, ?_⟩
  have hlev : levSum (LT l) K s e T (co e lam) (ex l s) (D e) =
      (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * cycVal (LT l) K s e lam d := by
    rw [(hD e le_rfl).2 rfl]
    unfold levSum cycVal
    rw [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm]
      congr 1
      rw [hTdef, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have h0 := hne a ha
      have hz : (LT l).ζQ s ^ ((1 + l ^ s) * a * l ^ i) = (LT l).ζQ s ^ (a * l ^ i) := by
        rw [mul_assoc, add_mul, one_mul, pow_add, pow_mul _ (l ^ s), zeta_pow_self, one_pow, mul_one]
      have hco : (((frK (LT l) K ^ i) (lam a * ((a : ↥(K0 K)) ^ e)⁻¹) : ↥(K0 K)) : Om l) =
          (((frK (LT l) K ^ i) (lam a) : ↥(K0 K)) : Om l) * ((a : Om l) ^ e)⁻¹ := by
        rw [map_mul, map_inv₀, map_pow, map_natCast]
        simp
      simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, map_neg,
        NegMemClass.coe_neg, hco, hz, Nat.cast_mul]
      field_simp
      ring
    · have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * (d : Om l) := by simp
      rw [h2]
      ring
  rw [hlev] at hE
  convert hE using 1
  rw [div_eq_mul_inv, map_mul, map_sub, map_pow, map_natCast, map_one]
  ring

end GlobalTheory.ExpImage.PosWeight
end
end

section

noncomputable section

namespace GlobalTheory.Triple

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction.Gen
open Formalism.L2.Host (HChar CharFrame)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE)
open GlobalTheory.TripleGal (UnrRho HkFrob)

theorem eq_one_of_isOfFinOrder_of_charpoly {K : Type} [Field K] [CharZero K] {n : ℕ} {A : GL (Fin n) K}
    (hA : IsOfFinOrder A) (hc : (A : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n) : A = 1 := by
  obtain ⟨m, hm, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hA
  have h1 : minpoly K (A : Matrix (Fin n) (Fin n) K) ∣ X ^ m - C 1 := minpoly.dvd _ _ (by
    rw [map_sub, map_pow, aeval_X, map_one, map_one, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self])
  have h2 := ((separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero).squarefree.squarefree_of_dvd
    h1).isRadical n _ (hc ▸ Matrix.minpoly_dvd_charpoly _)
  have h3 := aeval_eq_zero_of_dvd_aeval_eq_zero h2 (minpoly.aeval K _)
  rw [map_sub, aeval_X, map_one, sub_eq_zero] at h3
  exact Units.ext h3

theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem eval_charpolyRev {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (z : R) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm z]

theorem charpolyRev_of_inv {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) {m : Multiset ℂ}
    (hB : B.charpoly = (m.map fun a => X - C a).prod) : A.charpolyRev = (m.map fun a => 1 - C a⁻¹ * X).prod := by
  have e : ∀ z : ℂ, (Matrix.scalar (Fin n) z - B).det = (m.map fun a => z - a).prod := fun z => by
    rw [← Matrix.eval_charpoly, hB, eval_multiset_prod, Multiset.map_map]
    simp
  have h0 : (Matrix.scalar (Fin n) 0 - B).det ≠ 0 := by
    rw [map_zero, zero_sub, Matrix.det_neg]
    exact mul_ne_zero (by simp) (Matrix.isUnit_det_of_left_inverse h).ne_zero
  apply Polynomial.funext
  intro z
  refine mul_right_cancel₀ h0 ?_
  have e1 : (1 - z • A) * (Matrix.scalar (Fin n) 0 - B) = Matrix.scalar (Fin n) z - B := by
    rw [map_zero, zero_sub, mul_neg, sub_mul, one_mul, smul_mul_assoc, h, neg_sub, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  rw [eval_charpolyRev, ← Matrix.det_mul, e1, e, e, eval_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  refine congrArg _ (Multiset.map_congr rfl fun a ha => ?_)
  have ha0 : a ≠ 0 := fun h1 => h0 (by
    rw [e]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by rw [h1, sub_self]⟩))
  simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem sum_coeff_charpolyRev {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    ∑ k ∈ Finset.range (n + 1), M.charpolyRev.coeff k = (1 - M).det := by
  have h : M.charpolyRev.natDegree < n + 1 := by
    rw [← Matrix.reverse_charpoly, Nat.lt_succ_iff]
    exact (reverse_natDegree_le _).trans (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  have := eval_eq_sum_range' h 1
  simp only [one_pow, mul_one, eval_charpolyRev, one_smul] at this
  exact this.symm

variable {D : D7} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw}

theorem cyclotomicEps_eq_one_on_inertia {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i)) {A : ValuationSubring D.nd.Om}
    (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver (F := D.host.E) A v) {σ : GalE D} (hσ : σ ∈ Ine (F := D.host.E) A) : eps0 X i σ = 1 := by
  have h1 : cycZ D.host.E D.nd.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hv hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  rw [eps0, MonoidHom.comp_apply, h1, map_one]

theorem cyclotomicEps_frobenius_eq_norm {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i)) {A : ValuationSubring D.nd.Om}
    (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver (F := D.host.E) A v) {σ : GalE D} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 X i σ : (X.O0 i)ˣ) : X.O0 i) = (normV v : ℕ) := by
  show algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E D.nd.Om (X.l i) σ : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) = _
  rw [cycZ_of_isFrob hv hA hσ, map_natCast]

def twistW (s : X.Sig i) : GalE D →* (X.O0 i)ˣ := eps0 X i ^ D.R.t * (chiS i s)⁻¹

def matW (s : X.Sig i) (g : GalE D) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
  ((twistW s g : (X.O0 i)ˣ) : X.O0 i) • ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))

theorem matW_eq (s : X.Sig i) (g : GalE D) :
    matW s g = (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g := by
  rw [matW, Tmat, smul_smul, twistW, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_pow_eq_pow_val]

theorem matW_mul_inv (s : X.Sig i) (g : GalE D) : matW s g * matW s g⁻¹ = 1 := by
  rw [matW, matW, smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one,
    map_one, Units.val_one, Units.val_one, one_smul]

variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {s : X.Sig i}

section With

variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : Zbar (X.l i) →+* FbAt D w}

end With

theorem notMem_of_mem_pD {v : PlE D.host} (hv : v ∈ X.pD i) :
    v ∉ placesOver D.host.E (X.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have h : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) :=
    X.pD_eq i ▸ Finset.mem_coe.2 hv
  have hl : (X.l i).Prime := (X.lPrime i).out
  split_ifs at h with e
  · exact ⟨GlobalTheory.GalChar.notMem_of_ne D.host.pde'_prime hl (e ▸ D.host.pde_ne.symm) h,
      fun k => GlobalTheory.GalChar.notMem_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h⟩
  · exact ⟨GlobalTheory.GalChar.notMem_of_ne D.host.pde_prime hl (Ne.symm e) h,
      fun k => GlobalTheory.GalChar.notMem_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h⟩

theorem matW_of_mem_Ine (hu : UnrRho i s) {v : PlE D.host} (hl : v ∉ placesOver D.host.E (X.l i))
    (hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k)) {A : ValuationSubring D.nd.Om}
    (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver (F := D.host.E) A v) {g : GalE D} (hI : g ∈ Ine (F := D.host.E) A) :
    matW s g = (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
  rw [matW_eq, Tmat, cyclotomicEps_eq_one_on_inertia hl hA hI, hu v hl hg A hA g hI, Units.val_one, Units.val_one, one_pow, one_smul]

variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}

end GlobalTheory.Triple

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

theorem _root_.GlobalTheory.T.inner_product_integral_formula : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), ∃ c : ℝ, 0 < c ∧ ∀ u u' : (R.HV i t).H, ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h in R.fdV i t, ⟪R.extV i t u h, R.extV i t u' h⟫_ℂ ∂(R.νV i t) ∧ ∀ a a' : (R.cV i).W, IntegrableOn (fun h => star ⟪a, R.extV i t u h⟫_ℂ * ⟪a', R.extV i t u' h⟫_ℂ) (R.fdV i t) (R.νV i t) := by
  first | exact @GlobalTheory.AdelicL2Norm.norm_eq_integral | exact GlobalTheory.AdelicL2Norm.norm_eq_integral | (intros; apply GlobalTheory.AdelicL2Norm.norm_eq_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.LocalRepsFin

theorem exists_isCosetRep_finIdem : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ α : GA D V, SuppF V f α → ∃ C : Finset (GA D V), (∀ γ ∈ C, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ levG V β L ∧ SuppF V f k} α C := by
  intro D V β L v f hf α hα
  obtain ⟨ε, hε, rfl⟩ := hf
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hG : ∀ g, SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) g → g ∈ GfC V := fun g hg =>
    GlobalTheory.IdemSupport.mem_GfC_of_suppF V (GlobalTheory.IdemSupport.place_comp hΦ hε).1 hg
  let S : Subgroup (GA D V) := GlobalTheory.IdemSupport.suppGroup V (algebraMap _ (Formalism.L2.Theta.AE D) ε)
  have hS : ∀ g, g ∈ S ↔ SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) g := fun _ => Iff.rfl
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨R, r1, r2⟩ := GlobalTheory.HeckeLabels.exists_reps (GlobalTheory.HeckeLabels.relIndex_conj_ne_zero (L := S)
    (GlobalTheory.ParahoricCompact.isCompact_levG V β L) (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L)
    (fun k hk hk' => ⟨hG k ((hS k).1 hk), hk'⟩) ((hS α).2 hα))
  have hK : {k | k ∈ levG V β L ∧ SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) k} =
      (levG V β L ⊓ S : Subgroup (GA D V)) :=
    Set.ext fun k => and_congr_right fun _ => (hS k).symm
  have r0 : ∀ γ ∈ R, SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) γ := fun γ hγ => by
    obtain ⟨a, ha, b, hb, rfl⟩ := r1 γ hγ
    exact (hS _).1 (mul_mem (mul_mem ha.2 ((hS α).2 hα)) hb.2)
  rw [hK]
  exact ⟨R, r0, fun γ hγ => ⟨hG γ (r0 γ hγ), r1 γ hγ⟩, r2⟩

end GlobalTheory.LocalRepsFin
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Matrix
open scoped TensorProduct

namespace GlobalTheory.FinIsoProof

open GlobalTheory.DefU.ClassFin GlobalTheory.AdeleBaseChange

theorem nonempty_finIso (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Nonempty (FinIso L n) := by
  obtain ⟨ι, hι⟩ := exists_toAd (maximalRealSubfield L) L
  let κ : AL L ≃+* FiniteAdeleRing (𝓞 L) L := RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩
  have hκ : ∀ x a, κ (x ⊗ₜ a) = algebraMap L _ x * adMap (maximalRealSubfield L) L a := hι
  have hc : ∀ y, κ (conjAL L y) = conjFin (cc L) (κ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul x a =>
      change κ ((IsCMField.complexConj L x) ⊗ₜ a) = _
      rw [hκ, hκ, map_mul, conjFin_adMap (cc L) (fun k => IsCMField.complexConj_apply_eq_self L k), conjFin_algebraMap]
      rfl
  have hc' : ∀ y, κ.symm (conjFin (cc L) y) = conjAL L (κ.symm y) := fun y => by
    rw [RingEquiv.symm_apply_eq, hc, RingEquiv.apply_symm_apply]
  let p : GAf L n →* GL (Fin n) (FiniteAdeleRing (𝓞 L) L) :=
    (GeneralLinearGroup.map κ.toRingHom).comp (ReciprocityTheory.Aut.GA L n).subtype
  have hp : ∀ x, Formalism.UG.cT (conjFin (cc L)) (p x).val * (p x).val = 1 := fun x =>
    unitary_map κ.toRingHom (conjAL L) (conjFin (cc L)) hc x.1.val (mul_eq_one_comm.mp x.2)
  let j : GAf L n →* UA L n := ((finGL L n).comp p).codRestrict (UA L n) fun x => finGL_mem_UA _ (hp x)
  refine ⟨⟨κ, map_tmul_one hι, ?_, j, fun x => MonoidHom.mem_ker.2 (pInf_finGL (p x)), ?_, ?_⟩⟩
  · intro w v h
    have hv : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext h
    subst hv
    refine ⟨locMap _ w, GlobalTheory.LFun.InertChart.continuous_complMap (rfl : w.under (𝓞 (maximalRealSubfield L)) = _), fun a => ?_⟩
    rw [hκ, map_one, one_mul]
    rfl
  · intro x w s t
    have h1 : (finGL L n (p x)).val.map (pFin L) = (p x).val := congrArg Units.val (pFin_finGL (p x))
    exact congrArg (pLoc L w) (congrFun₂ h1 s t)
  · intro y hy
    let z := GeneralLinearGroup.map (pFin L) y.1
    have hz : Formalism.UG.cT (conjFin (cc L)) z.val * z.val = 1 := cT_pFin y
    have hm : GeneralLinearGroup.map κ.symm.toRingHom z ∈ ReciprocityTheory.Aut.GA L n :=
      mul_eq_one_comm.mp (unitary_map κ.symm.toRingHom _ _ hc' z.val hz)
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    have e : p ⟨_, hm⟩ = z := Units.ext (Matrix.ext fun i k => κ.apply_symm_apply _)
    change finGL L n (p ⟨_, hm⟩) = _
    rw [e]
    exact finGL_pFin ⟨y, hy⟩

theorem finIso_nonempty : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), Nonempty (FinIso L n) :=
  fun L _ _ _ n => nonempty_finIso L n

end GlobalTheory.FinIsoProof
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.downwardThetaLift_real_points_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (u, 1) f) l g = downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g := by
  first | exact @GlobalTheory.DownLift.downInt_realEquiv | exact GlobalTheory.DownLift.downInt_realEquiv | (intros; apply GlobalTheory.DownLift.downInt_realEquiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.galoisConj_classScalars_and_volume : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ta (M.vol a) = M.vol b ∧ ∀ k, ta (M.ep a k) = M.ep b (e k) := by
  first | exact @GlobalTheory.ConjScalar.conj_vol_ep | exact GlobalTheory.ConjScalar.conj_vol_ep | (intros; apply GlobalTheory.ConjScalar.conj_vol_ep <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isDeltaRingHom_powerSeries_of_rank_one_image : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C] (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ (σ : (Wq l a)⟦X⟧ →+* C) (e : ℕ), σ X ^ e ∈ J → DC.δ (σ X) = 0 → IsδMap (deltaS l a) DC σ := by
  first | exact @GlobalTheory.sdelta_of_rank_one | exact GlobalTheory.sdelta_of_rank_one | (intros; apply GlobalTheory.sdelta_of_rank_one <;> assumption)
end
