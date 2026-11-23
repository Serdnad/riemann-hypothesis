module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle213
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle293
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle126
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle243
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle202
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle159
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle162
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.ExpandKer

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem dxi_mul (i j : ℕ) :
    A.dxi 1 i * A.dxi 1 j = ((i + j).choose i : A.Acr 1) * A.dxi 1 (i + j) := by
  obtain ⟨-, hmul, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  change A.mkAcr 1 (A.dxi0 i) * A.mkAcr 1 (A.dxi0 j)
    = ((i + j).choose i : A.Acr 1) * A.mkAcr 1 (A.dxi0 (i + j))
  rw [← map_mul, hmul, map_mul, map_natCast]

theorem aTo1_pi : A.aTo1 A.pi = -A.dxi 1 1 := by
  obtain ⟨-, -, hfac, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  have h1 : A.dxi0 1 = algebraMap A.W A.Acr0 A.xi := by
    simpa using hfac 1
  have h2 : A.dxi 1 1 = A.toAcr 1 A.xi := by
    change A.mkAcr 1 (A.dxi0 1) = A.mkAcr 1 (algebraMap A.W A.Acr0 A.xi)
    rw [h1]
  rw [h2, ← A.aTo1_coeff, A.xi_coeff_zero, map_neg, neg_neg]

theorem toAcr_teichmuller (b : A.A) : A.toAcr 1 (WittVector.teichmuller l b) = A.aTo1 b := by
  rw [← A.aTo1_coeff, WittVector.teichmuller_coeff_zero]

theorem exists_coprime {m : ℕ} (hm : l ∣ m) {j : ℕ} (hj : j < l) :
    ∃ c : ℕ, c.Coprime l ∧ A.dxi 1 1 ^ j * A.dxi 1 m = (c : A.Acr 1) * A.dxi 1 (m + j) := by
  have hp : l.Prime := Fact.out
  induction j with
  | zero => exact ⟨1, Nat.coprime_one_left l, by simp⟩
  | succ j ih =>
    obtain ⟨c, hc, hcj⟩ := ih (Nat.lt_of_succ_lt hj)
    have hnd : ¬ l ∣ m + j + 1 := by
      intro h
      have h2 : l ∣ j + 1 := by
        rw [Nat.add_assoc] at h
        exact (Nat.dvd_add_right hm).mp h
      have := Nat.le_of_dvd (Nat.succ_pos j) h2
      omega
    refine ⟨c * (m + j + 1), Nat.Coprime.mul_left hc ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm, ?_⟩
    rw [pow_succ', mul_assoc, hcj, mul_left_comm, dxi_mul A 1 (m + j), Nat.choose_one_right]
    have e : 1 + (m + j) = m + (j + 1) := by omega
    rw [e]
    push_cast
    ring

theorem mem_of_coprime_mul {I : Ideal (A.Acr 1)} {c : ℕ} (hc : c.Coprime l) {x : A.Acr 1}
    (h : (c : A.Acr 1) * x ∈ I) : x ∈ I := by
  have hl : ((l : ℕ) : A.Acr 1) = 0 := by
    have e : ((l : ℕ) : A.Acr 1) = A.toAcr 1 (l : A.W) := by rw [map_natCast]
    rw [e]
    change Ideal.Quotient.mk _ (algebraMap A.W A.Acr0 (l : A.W)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.subset_span (by simp)
  have h1 : (1 : A.Acr 1) = (c : A.Acr 1) * (Nat.gcdA c l : A.Acr 1)
      + (l : A.Acr 1) * (Nat.gcdB c l : A.Acr 1) := by
    have h' := Nat.gcd_eq_gcd_ab c l
    rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at h'
    have h'' := congrArg (fun z : ℤ => (z : A.Acr 1)) h'
    push_cast at h''
    exact h''
  have hx : x = (Nat.gcdA c l : A.Acr 1) * ((c : A.Acr 1) * x) := by
    calc x = (1 : A.Acr 1) * x := (one_mul x).symm
      _ = _ := by rw [h1, hl]; ring
  rw [hx]
  exact I.mul_mem_left _ h

theorem inner_step (k : ℕ) {j : ℕ} (hj : j < l) (b : A.A)
    (h : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + j + 1)) :
    b ∈ Ideal.span {A.pi} := by
  obtain ⟨c, hc, hcj⟩ := exists_coprime A (dvd_mul_right l k) hj
  have hx : A.aTo1 b * A.dxi 1 (l * k + j) ∈ A.Fil 1 (l * k + j + 1) := by
    have e : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k)
        = (c : A.Acr 1) * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j))) := by
      rw [map_mul, map_pow, aTo1_pi A]
      calc (-A.dxi 1 1) ^ j * A.aTo1 b * A.dxi 1 (l * k)
          = (-1) ^ j * A.aTo1 b * (A.dxi 1 1 ^ j * A.dxi 1 (l * k)) := by ring
        _ = _ := by rw [hcj]; ring
    rw [e] at h
    have h2 := mem_of_coprime_mul A hc h
    have h3 : (-1 : A.Acr 1) ^ j * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j)))
        ∈ A.Fil 1 (l * k + j + 1) := Ideal.mul_mem_left _ _ h2
    have h4 : (-1 : A.Acr 1) ^ j * ((-1) ^ j * (A.aTo1 b * A.dxi 1 (l * k + j)))
        = A.aTo1 b * A.dxi 1 (l * k + j) := by
      rw [← mul_assoc, ← mul_pow]
      simp
    rwa [h4] at h3
  rw [← toAcr_teichmuller A b] at hx
  have hth := ((GlobalTheory.T.graded_filtration_generated_by_dividedXi A 1 (l * k + j)).2 (WittVector.teichmuller l b)).mp hx
  have hz : A.aToU1 b = 0 := by
    have e := A.sharpMap_coeff (WittVector.teichmuller l b)
    rw [WittVector.teichmuller_coeff_zero] at e
    rw [e, Ideal.Quotient.eq_zero_iff_mem]
    exact hth
  obtain ⟨-, hker⟩ := GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A
  rw [← hker]
  exact RingHom.mem_ker.mpr hz

theorem term_eq_zero {a : A.A} (h : a ∈ Ideal.span {A.pi ^ l}) (m : ℕ) :
    A.aTo1 a * A.dxi 1 m = 0 := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.expansion_surjective_additive_linear A
  rw [map_mul, mul_assoc, h4, mul_zero]

theorem term_mem (c : ℕ →₀ A.A) (h0 : A.expand c = 0) (k : ℕ)
    (hk : ∀ i < k, c i ∈ Ideal.span {A.pi ^ l}) :
    A.aTo1 (c k) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + l) := by
  obtain ⟨-, hadd, -, -⟩ := GlobalTheory.T.expansion_surjective_additive_linear A
  obtain ⟨-, -, -, -, hmap, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  have hdx : ∀ m, A.dxi 1 m ∈ A.Fil 1 m := fun m => by
    rw [hmap]
    change A.mkAcr 1 (A.dxi0 m) ∈ _
    apply Ideal.mem_map_of_mem
    unfold CrystallineSemistableComparison.PAlg.Fil0
    exact Ideal.subset_span ⟨m, le_rfl, rfl⟩
  have hanti : ∀ r s : ℕ, r ≤ s → A.Fil 1 s ≤ A.Fil 1 r := by
    intro r s hrs
    rw [hmap, hmap]
    apply Ideal.map_mono
    unfold CrystallineSemistableComparison.PAlg.Fil0
    apply Ideal.span_mono
    rintro z ⟨i, hi, rfl⟩
    exact ⟨i, le_trans hrs hi, rfl⟩
  have hsingle : A.expand (Finsupp.single k (c k)) = A.aTo1 (c k) * A.dxi 1 (l * k) := by
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum_single_index]
    simp
  have herase : A.expand (c.erase k) ∈ A.Fil 1 (l * k + l) := by
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum]
    apply Ideal.sum_mem
    intro i hi
    have hik : i ≠ k := by
      rintro rfl
      simp at hi
    rw [Finsupp.erase_ne hik]
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · rw [term_eq_zero A (hk i hlt)]
      exact Ideal.zero_mem _
    · apply Ideal.mul_mem_left
      refine hanti _ _ ?_ (hdx (l * i))
      calc l * k + l = l * (k + 1) := by ring
        _ ≤ l * i := Nat.mul_le_mul (le_refl l) hgt
  have hsplit := hadd (Finsupp.single k (c k)) (c.erase k)
  rw [Finsupp.single_add_erase, h0, hsingle] at hsplit
  have e : A.aTo1 (c k) * A.dxi 1 (l * k) = -A.expand (c.erase k) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hsplit.symm
  rw [e]
  exact (Ideal.neg_mem_iff _).mpr herase

theorem fil_anti {r s : ℕ} (h : r ≤ s) : A.Fil 1 s ≤ A.Fil 1 r := by
  obtain ⟨-, -, -, -, hmap, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  rw [hmap, hmap]
  apply Ideal.map_mono
  unfold CrystallineSemistableComparison.PAlg.Fil0
  apply Ideal.span_mono
  rintro z ⟨i, hi, rfl⟩
  exact ⟨i, le_trans h hi, rfl⟩

theorem coeff_mem (c : ℕ →₀ A.A) (h0 : A.expand c = 0) (k : ℕ)
    (hk : ∀ i < k, c i ∈ Ideal.span {A.pi ^ l}) : c k ∈ Ideal.span {A.pi ^ l} := by
  have hT := term_mem A c h0 k hk
  have key : ∀ j, j ≤ l → c k ∈ Ideal.span {A.pi ^ j} := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (ih (Nat.le_of_succ_le hj))
      have h1 : A.aTo1 (A.pi ^ j * b) * A.dxi 1 (l * k) ∈ A.Fil 1 (l * k + j + 1) := by
        rw [mul_comm (A.pi ^ j) b, hb]
        exact fil_anti A (by omega) hT
      obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp (inner_step A k (Nat.lt_of_succ_le hj) b h1)
      rw [← hb, ← hb', pow_succ]
      exact Ideal.mem_span_singleton'.mpr ⟨b', by ring⟩
  exact key l le_rfl

theorem expand_eq_zero_iff : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (c : ℕ →₀ A.A),
    A.expand c = 0 ↔ ∀ k, c k ∈ Ideal.span {A.pi ^ l} := by
  intro l _ A c
  constructor
  · intro h0 k
    refine Nat.strong_induction_on k ?_
    intro k ih
    exact coeff_mem A c h0 k ih
  · intro h
    unfold CrystallineSemistableComparison.PAlg.expand
    rw [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro i _
    exact term_eq_zero A (h i) _

end GlobalTheory.CompanionTheory.ExpandKer
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem dxi_zero {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) : A.dxi n 0 = 1 := by
  have h : A.dxi0 0 = 1 := Subtype.ext (by simp [PAlg.dxi0, dpw])
  rw [PAlg.dxi, h, map_one]

theorem exists_toAcr_sub_mem {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (z : A.Acr n) :
    ∃ w : A.W, z - A.toAcr n w ∈ A.Fil n 1 := by
  have h0 : z ∈ A.Fil n 0 := by
    rw [((GlobalTheory.T.crystalline_filtration_multiplicative A).2.2.2.2.2.2.1 n)]; trivial
  obtain ⟨w, hw⟩ := (GlobalTheory.T.graded_filtration_generated_by_dividedXi A n 0).1 z h0
  refine ⟨w, ?_⟩
  simpa [dxi_zero] using hw

theorem toAcr_mem_fil_iff {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (w : A.W) :
    A.toAcr n w ∈ A.Fil n 1 ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  have h := (GlobalTheory.T.graded_filtration_generated_by_dividedXi A n 0).2 w
  simpa [dxi_zero] using h

theorem uToQ_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.uToQ n) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨w, hw⟩ := exists_toAcr_sub_mem A n z
  exact ⟨A.th w, (Ideal.Quotient.eq.2 hw).symm⟩

theorem ker_uToQ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} := by
  ext x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change A.th w ∈ _ ↔ A.th w ∈ _
  rw [RingHom.mem_ker, uToQ_th, Ideal.Quotient.eq_zero_iff_mem, toAcr_mem_fil_iff]

theorem uToPQ_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.uToPQ n) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨w, hw⟩ := exists_toAcr_sub_mem A n z
  have h : z - A.toAcr n w ∈ A.PFil n := Ideal.mem_sup_right hw
  exact ⟨A.th w, (Ideal.Quotient.eq.2 h).symm⟩

theorem ker_uToPQ {l : ℕ} [Fact l.Prime] (A : PAlg l) {n : ℕ} (hn : n ≠ 0) :
    RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.th w ∈ _
    have h : A.toAcr n w ∈ A.PFil n := Ideal.Quotient.eq_zero_iff_mem.1 hx
    obtain ⟨u, hu, z, hz, e⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    obtain ⟨w', hw'⟩ := exists_toAcr_sub_mem A n a
    have h1 : A.toAcr n (w - (l : A.W) * w') ∈ A.Fil n 1 := by
      have e' : A.toAcr n (w - (l : A.W) * w') = (a - A.toAcr n w') * (l : A.Acr n) + z := by
        rw [map_sub, map_mul, map_natCast, ← e]; ring
      rw [e']
      exact add_mem (Ideal.mul_mem_right _ _ hw') hz
    have h2 := (toAcr_mem_fil_iff A n _).1 h1
    have h3 : A.th (w - (l : A.W) * w') ∈ Ideal.span {(l : A.U)} :=
      Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ hn) h2
    have h4 : A.th w = A.th (w - (l : A.W) * w') + (l : A.U) * A.th w' := by
      rw [map_sub, map_mul, map_natCast]; ring
    rw [h4]
    exact add_mem h3 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast,
      ← map_natCast (Ideal.Quotient.mk (A.PFil n))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))

theorem uToQ_main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (A.uToQ n) ∧
    RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} ∧ Function.Surjective (A.uToPQ n) ∧
    (n ≠ 0 → RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)}) :=
  fun A n => ⟨uToQ_surjective A n, ker_uToQ A n, uToPQ_surjective A n, fun hn => ker_uToPQ A hn⟩

end GlobalTheory.CompanionTheory.Untilt
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.OmGlob

theorem vk_cosieve {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ) (α : U.ι) :
    Cosieve (Vk q U a α) :=
  fun _ _ φ h => Site.inU_hom φ.hom h

end GlobalTheory.CompanionTheory.OmGlob
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
namespace GlobalTheory.CompanionTheory.GrCech

theorem capO_affine {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (U : Cov q) (n : ℕ)
    (i : Fin (n + 1) → U.ι) : IsAffineOpen (capO U.U i) := by
  classical
  have h := U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have e : (⨅ α ∈ Finset.univ.image i, U.U α) = capO U.U i := by
    refine le_antisymm (le_iInf fun a => ?_) (le_iInf₂ fun α hα => ?_)
    · exact iInf₂_le (i a) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
      exact capO_le U.U i a
  rwa [e] at h

theorem inU_capO {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (nlFun γ p X q κ)) :
    InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  have h := GlobalTheory.T.inOpen_finite_inf_iff (γ := γ) (p := p) (q := q) (κ := κ) (fun a => U (i a)) Finset.univ T
  simpa [capO] using h

theorem capT_eq {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {ι : Type} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => St Q {U α}) i = St Q {capO U i} := by
  funext T
  refine propext ⟨fun h => ⟨(h 0).1, capO U i, rfl, (inU_capO U i T).2 fun a => ?_⟩, ?_⟩
  · obtain ⟨-, V, hV, hT⟩ := h a
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact hT
  · rintro ⟨hq, V, hV, hT⟩ a
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact ⟨hq, _, rfl, (inU_capO U i T).1 hT a⟩

end GlobalTheory.CompanionTheory.GrCech

namespace GlobalTheory.CompanionTheory.GrCech

theorem inU_mono {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {V W : X.Opens} (h : V ≤ W) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) : InU W T :=
  fun x hx => h (hT hx)

theorem vb_cech (hLoc : KH.LocGr) (hPoly : KH.PolyTf) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (U : Cov q) (r : ℕ) (hr : r < s) :
    Nonempty (VB (fun W : X.Opens => strV q W) U.U (CrystallineSemistableComparison.Pb.cechH (grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r)
      (fun α => St (TF l s) {U.U α}) r)) := by
  classical
  have isF : ∀ Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))), IsFil (sP Q) (sFil Q) :=
    fun Q => GlobalTheory.T.sheaf_filtration_property Q
  choose ω hω using fun α => GlobalTheory.T.exists_graded_form_on_affine_chart hLoc hPoly l s hb q (U.c α) r hr
  have hT : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (T : Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))), capT (fun α => St (TF l s) {U.U α}) i T → InU (capO U.U i) T := by
    intro n i T h
    rw [capT_eq] at h
    obtain ⟨-, V, hV, hT⟩ := h
    rwa [Set.mem_singleton_iff.1 hV] at hT
  have hle : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (a : Fin (n + 1)),
      capT (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) i ≤ St (TF l s) {U.U (i a)} := fun i a T h => h a
  have hpair : ∀ α β, IsAffineOpen (U.U α ⊓ U.U β) := by
    intro α β
    have h := U.inter {α, β} ⟨α, by simp⟩
    have e : (⨅ γ ∈ ({α, β} : Finset U.ι), U.U γ) = U.U α ⊓ U.U β := by
      rw [Finset.iInf_insert, Finset.iInf_singleton]
    rwa [e] at h
  have hl2 : ∀ {V W : X.Opens} (h : V ≤ W), St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {V} ≤ St (TF l s) {W} := by
    rintro V W h T ⟨hq, V', hV, hT⟩
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact ⟨hq, W, rfl, inU_mono h hT⟩
  have hq2 : ∀ {V : X.Opens} (T), St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {V} T → InU V T := by
    rintro V T ⟨hq, V', hV, hT⟩
    rwa [Set.mem_singleton_iff.1 hV] at hT
  have hg0 := fun α β (k' : Idx r (U.d β)) => (hω α (U.U α ⊓ U.U β) (hpair α β) inf_le_left _ rfl (hl2 inf_le_left) (isF _) hq2
    ((resU _ (hl2 inf_le_right)).pull r (ω β k'))).exists
  choose g' hg' using hg0
  refine GlobalTheory.T.cover_cup_action_basis (fun W => strV q W) _ U.U _ r (fun α => Idx r (U.d α))
    (fun i => fHom (isF _) (hT i) r) (fun i a k => (resU _ (hle i a)).pull r (ω (i a) k)) (fun α β k k' => g' α β k' k)
    ?_ ?_ ?_ ?_ ?_
  · intro n i a h
    exact hω (i a) (capO U.U i) (capO_affine U n i) (capO_le U.U i a) _ (capT_eq _ _ i) (hle i a) (isF _) (hT i) h
  · intro n i c h
    exact fAct_str (isF _) (hT i) r c h
  · intro n i j f h
    exact res_fAct (isF _) (hT _) r (isF _) (hT i) (capO_comp U.U i j.succAbove) _ f h
  · intro n i j a k
    exact res_res _ _ _ r _
  · intro n i a a' k'
    have hle2 : capT (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) i ≤ St (TF l s) {U.U (i a) ⊓ U.U (i a')} := by
      intro T h
      exact ⟨(h a).1, _, rfl, le_preimage_inf (pt T) (hq2 T (hle i a T h)) (hq2 T (hle i a' T h))⟩
    have h1 := congrArg ((resU _ hle2).pull r) (hg' (i a) (i a') k')

    rw [res_res, map_sum] at h1
    refine h1.trans (Finset.sum_congr rfl fun k _ => ?_)
    refine (res_fAct (isF _) hq2 r (isF _) (hT i) (le_inf (capO_le U.U i a) (capO_le U.U i a')) hle2 _ _).trans ?_
    change fAct _ _ r _ _ = fAct _ _ r _ _
    rw [res_res]

theorem main_nl (hLoc : KH.LocGr) (hPoly : KH.PolyTf) {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ) :
    Module.Finite O ((CrystallineSemistableComparison.Pb.cechH (grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r)
      (fun α => St (TF l s) {U.U α}) r).cx.H p) := by
  obtain ⟨V⟩ := vb_cech hLoc hPoly l s hb q U r hr
  exact GlobalTheory.T.affine_cover_cohomology_finite q U.U U.cover (capO_affine U) _ V p



theorem main_thm : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ),
    Module.Finite O ((CrystallineSemistableComparison.Pb.cechH (Pb.sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) r).cx.H p) := by
  intro hLoc hPoly _ _ O _ _ l s hb X q _ U r hr p
  exact main_nl hLoc hPoly l s hb q U r hr p

end GlobalTheory.CompanionTheory.GrCech
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.PDSpanning

theorem exists_sum_dpow : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (z : (pq B).P), ∃ b : ℕ →₀ B, z = b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1) := by
  intro B _ J δ z
  refine ⟨(pq B).e.repr z, ?_⟩
  have h := (pq B).e.linearCombination_repr z
  rw [Finsupp.linearCombination_apply] at h
  refine h.symm.trans (Finsupp.sum_congr fun k _ => ?_)
  rw [(eta_std δ).var k, Algebra.smul_def]

end GlobalTheory.CompanionTheory.PDSpanning
end
