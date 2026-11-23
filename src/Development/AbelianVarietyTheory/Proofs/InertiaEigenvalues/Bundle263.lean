module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle238
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle239
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgIdentityProdOfUnitResultant
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle240
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle241
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle242
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.idempotentBlockCharPoly_eq_charpoly_image : ∀ {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K), e * e = e → e.rank = t → ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e ∧ ∀ M : Matrix (Fin n) (Fin n) K, blockPol e (e * M * e) = (b * M * a).charpoly := by
  first | exact @GlobalTheory.BlockCharpoly.blockPol_eq_charpoly | exact GlobalTheory.BlockCharpoly.blockPol_eq_charpoly | (intros; apply GlobalTheory.BlockCharpoly.blockPol_eq_charpoly <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, InRing T rep (a k)) → ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T := by
  first | exact @GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing | exact GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing | (intros; apply GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU
open GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

def InJ (w : Per.Ainf l) : Prop := ∃ c : Per.OC l, Per.θ l w = (l : Per.OC l) * c

def IsLogJ (w : Per.Ainf l) (y : Per.Acris l) : Prop :=
  ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ s : Per.Acris0 l,
    ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) w) ^ (k + 1) ∧
    ∃ z : Per.Acris l, y - algebraMap (Per.Acris0 l) (Per.Acris l) s = ((l : ℕ) : Per.Acris l) ^ r * z

theorem isLogJ_zero : IsLogJ (0 : Per.Ainf l) 0 := fun _ => ⟨0, fun _ _ => ⟨0, by simp, 0, by simp⟩⟩

private theorem acris_eq_zero_of_forall_dvd (x : Per.Acris l)
    (h : ∀ r : ℕ, ∃ z : Per.Acris l, x = ((l : ℕ) : Per.Acris l) ^ r * z) : x = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {((l : ℕ) : Per.Acris l)})
    (GlobalTheory.MemLoc.acris_basic l).1.toIsHausdorff x fun r => ?_
  obtain ⟨z, hz⟩ := h r
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  exact ⟨z, hz⟩

theorem isLogJ_unique {w : Per.Ainf l} {y y' : Per.Acris l} (h : IsLogJ w y) (h' : IsLogJ w y') :
    y = y' := by
  rw [← sub_eq_zero]
  refine acris_eq_zero_of_forall_dvd (y - y') fun r => ?_
  obtain ⟨N, hN⟩ := h r
  obtain ⟨N', hN'⟩ := h' r
  obtain ⟨s, hs, z, hz⟩ := hN (max N N') (le_max_left _ _)
  obtain ⟨s', hs', z', hz'⟩ := hN' (max N N') (le_max_right _ _)
  have : s = s' := Subtype.ext
    ((GlobalTheory.RingBasics.isUnit_nat l _ (Nat.factorial_ne_zero _)).mul_left_cancel (hs.trans hs'.symm))
  subst this
  have key : y - y' = ((l : ℕ) : Per.Acris l) ^ r * (z - z') := by linear_combination hz - hz'
  exact ⟨z - z', key⟩

theorem isLogJ_extends {f : Per.Ainf l →+* Per.Ainf l} {F : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) {w : Per.Ainf l} {y : Per.Acris l}
    (hy : IsLogJ w y) : IsLogJ (f w) (F y) := by
  intro r
  obtain ⟨N, hN⟩ := hy r
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s, hs, z, hz⟩ := hN n hn
  refine ⟨⟨Per.extP f s, hf.mem _ s.2⟩, ?_, F z, ?_⟩
  · have := congrArg (Per.extP f) hs

    simpa only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, GlobalTheory.RingBasics.awayMap_algebraMap₂] using this
  · have := congrArg F hz
    rw [map_sub, map_mul, map_pow, map_natCast, hf.env] at this
    exact this

theorem inJ_mu {e : Per.Fl l} (he : e.untilt = 1) : InJ (mu e) :=
  ⟨0, by rw [Model.theta_mu, he, sub_self, mul_zero]⟩

theorem inJ_pow {e : Per.Fl l} (h : InJ (Per.tm e - 1)) (m : ℕ) : InJ (Per.tm (e ^ m) - 1) := by
  obtain ⟨c, hc⟩ := h
  have hθ : Per.θ l (Per.tm e) - 1 = (l : Per.OC l) * c := by rw [← hc, map_sub, map_one]
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (Per.θ l (Per.tm e)) 1 m
  refine ⟨c * d, ?_⟩
  have e1 : Per.tm (e ^ m) = Per.tm e ^ m := map_pow (WittVector.teichmuller l) e m
  rw [e1, map_sub, map_one, map_pow, ← one_pow m, hd, hθ, mul_assoc]

end GlobalTheory.LogU
end
end

section

open Formalism
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PeriodSol
open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem dvd_of_constantCoeff (x : Per.Ainf l) (h : WittVector.constantCoeff x = 0) :
    (l : Per.Ainf l) ∣ x := by
  have h0 := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) x 0
  have hI : (Finset.Iic 0 : Finset ℕ) = {0} := by ext i; simp
  rw [hI, Finset.sum_singleton] at h0
  rw [WittVector.constantCoeff_apply] at h
  simpa [h] using h0

theorem constantCoeff_natCast_mul (x : Per.Ainf l) :
    WittVector.constantCoeff ((l : Per.Ainf l) * x) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem iterate_tm (n : ℕ) (y : Per.Fl l) :
    (⇑(Per.φA l))^[n] (Per.tm y) = Per.tm (y ^ (l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, ← pow_mul, ← pow_succ]

theorem smod_iff (m : ℕ) (x y : Per.Ainf l) :
    x ≡ y [SMOD ((Ideal.span {(l : Per.Ainf l)}) ^ m • ⊤ : Submodule (Per.Ainf l) (Per.Ainf l))] ↔
      (l : Per.Ainf l) ^ m ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem xi_bar_ne_zero (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) :
    WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) ≠ 0 := by
  set e' := (frobeniusEquiv (Per.Fl l) l).symm e with he'
  have hxi : WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) = ∑ i ∈ Finset.range l, e' ^ i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GlobalTheory.MemLoc.xi, map_sum, map_pow, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, he']
  have hpow : e' ^ l = e := by
    have := (frobeniusEquiv (Per.Fl l) l).apply_symm_apply e
    rwa [frobeniusEquiv_apply, ← he'] at this
  intro h0
  rw [hxi] at h0
  have h1 := geom_sum_mul e' l
  rw [h0, zero_mul, hpow] at h1
  have he1 : e = 1 := (sub_eq_zero.1 h1.symm)
  apply he.2
  rw [he1, map_one]
  simp

end GlobalTheory.PeriodSol

namespace GlobalTheory.PeriodSol
open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem exists_step (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) (n : ℕ) (hn : 0 < n) (c : Per.Ainf l) :
    ∃ y : Per.Fl l, (l : Per.Ainf l) ∣
      c + ((⇑(Per.φA l))^[n] (Per.tm y) - GlobalTheory.MemLoc.xi e * Per.tm y) := by
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
  set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)
  set b := WittVector.constantCoeff c
  have hdeg : (C b - C a * X : (Per.Fl l)[X]).degree < ((l ^ n : ℕ) : WithBot ℕ) := by
    have h1 : (C b - C a * X : (Per.Fl l)[X]).degree ≤ 1 := by compute_degree
    exact lt_of_le_of_lt h1 (by exact_mod_cast hq)
  have hmon : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).Monic := monic_X_pow_add hdeg
  have hnd : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).natDegree ≠ 0 := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
    omega
  obtain ⟨y, hy⟩ := GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd
  refine ⟨y, dvd_of_constantCoeff _ ?_⟩
  rw [iterate_tm]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hy
  rw [map_add (f := _), map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _),
    WittVector.constantCoeff_apply (x := Per.tm _), WittVector.teichmuller_coeff_zero,
    WittVector.teichmuller_coeff_zero]
  rw [← hy]
  ring

theorem exists_start (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) (n : ℕ) (hn : 0 < n) :
    ∃ w₀ : Per.Fl l, w₀ ≠ 0 ∧ w₀ ^ (l ^ n) = WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) * w₀ := by
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
  set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)
  have hq1 : l ^ n - 1 ≠ 0 := by omega
  have hmon : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).Monic := monic_X_pow_sub_C a hq1
  have hnd : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).natDegree ≠ 0 := by
    rw [natDegree_X_pow_sub_C _]; exact hq1
  obtain ⟨y, hy⟩ := GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd
  simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy
  refine ⟨y, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow hq1] at hy
    exact xi_bar_ne_zero e he hy.symm
  · rw [← hy, ← pow_succ, Nat.sub_add_cancel hq.le]

theorem period_solution : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), GlobalTheory.MemLoc.IsEps e →
    ∀ n : ℕ, 0 < n → ∃ w : Per.Ainf l, GlobalTheory.MemLoc.xi e * w ≠ 0 ∧
      (⇑(Per.φA l))^[n] w = GlobalTheory.MemLoc.xi e * w := by
  intro l _ e he n hn
  set ξ := GlobalTheory.MemLoc.xi e
  let Φ : Per.Ainf l →+* Per.Ainf l := Per.φA l ^ n
  have hΦ : ∀ x, (⇑(Per.φA l))^[n] x = Φ x := fun x => by simp [Φ, RingHom.coe_pow]
  let F : Per.Ainf l → Per.Ainf l := fun w => Φ w - ξ * w
  have F_sub : ∀ a b, F (a - b) = F a - F b := fun a b => by simp only [F, map_sub]; ring
  have F_lin : ∀ (m : ℕ) a b, F (a + (l : Per.Ainf l) ^ m * b) = F a + (l : Per.Ainf l) ^ m * F b :=
    fun m a b => by simp only [F, map_add (f := _), map_mul, map_pow, map_natCast]; ring
  have step : ∀ (k : ℕ) (w : Per.Ainf l), ∃ w' : Per.Ainf l,
      (l : Per.Ainf l) ^ (k + 1) ∣ F w →
        (l : Per.Ainf l) ^ (k + 2) ∣ F w' ∧ (l : Per.Ainf l) ^ (k + 1) ∣ w' - w := by
    intro k w
    by_cases hw : (l : Per.Ainf l) ^ (k + 1) ∣ F w
    · obtain ⟨c, hc⟩ := hw
      obtain ⟨y, d, hd⟩ := exists_step e he n hn c
      refine ⟨w + (l : Per.Ainf l) ^ (k + 1) * Per.tm y, fun _ => ⟨⟨d, ?_⟩, ⟨Per.tm y, by ring⟩⟩⟩
      rw [F_lin, hc, ← mul_add]
      have : F (Per.tm y) = (⇑(Per.φA l))^[n] (Per.tm y) - ξ * Per.tm y := by simp only [F, hΦ]
      rw [this, hd]; ring
    · exact ⟨w, fun h => absurd h hw⟩
  choose g hg using step
  obtain ⟨w₀, hw₀, hw₀q⟩ := exists_start e he n hn
  let seq : ℕ → Per.Ainf l := fun k => Nat.rec (Per.tm w₀) (fun k w => g k w) k
  have hseq0 : seq 0 = Per.tm w₀ := rfl
  have hseqS : ∀ k, seq (k + 1) = g k (seq k) := fun k => rfl
  have hF0 : (l : Per.Ainf l) ^ (0 + 1) ∣ F (seq 0) := by
    rw [zero_add, pow_one, hseq0]
    apply dvd_of_constantCoeff
    simp only [F, ← hΦ, iterate_tm, map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _),
      WittVector.teichmuller_coeff_zero, hw₀q]
    exact sub_self _
  have hF : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ F (seq k) := by
    intro k
    induction k with
    | zero => exact hF0
    | succ k ih => rw [hseqS]; exact (hg k (seq k) ih).1
  have hdiff : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ seq (k + 1) - seq k := fun k => by
    rw [hseqS]; exact (hg k (seq k) (hF k)).2
  have hcau : ∀ m d, (l : Per.Ainf l) ^ m ∣ seq m - seq (m + d) := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have h2 : (l : Per.Ainf l) ^ m ∣ seq (m + d + 1) - seq (m + d) :=
        (pow_dvd_pow _ (by omega)).trans (hdiff (m + d))
      have : seq m - seq (m + (d + 1)) = (seq m - seq (m + d)) - (seq (m + d + 1) - seq (m + d)) := by
        rw [← add_assoc]; ring
      rw [this]; exact dvd_sub ih h2
  have hcomp : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := seq) (fun {m n} hmn => by
    rw [smod_iff]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcau m d)
  have hL' : ∀ k, (l : Per.Ainf l) ^ k ∣ seq k - L := fun k => (smod_iff k _ _).1 (hL k)
  have hFL : F L = 0 := by
    refine hcomp.toIsHausdorff.haus (F L) fun k => ?_
    rw [smod_iff, sub_zero]
    obtain ⟨c, hc⟩ := hL' k
    have e1 : L = seq k + (l : Per.Ainf l) ^ k * (-c) := by rw [mul_neg, ← hc]; ring
    rw [e1, F_lin]
    exact dvd_add ((pow_dvd_pow _ (Nat.le_succ k)).trans (hF k)) (dvd_mul_right _ _)
  have hL0 : WittVector.constantCoeff L = w₀ := by
    obtain ⟨c, hc⟩ := hL' 1
    obtain ⟨c', hc'⟩ := hdiff 0
    have e1 : L = Per.tm w₀ + (l : Per.Ainf l) * (c' - c) := by
      rw [pow_one] at hc; rw [zero_add, pow_one] at hc'
      rw [mul_sub, ← hc, ← hc', ← hseq0]; ring
    rw [e1, map_add (f := _), constantCoeff_natCast_mul, add_zero, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
  refine ⟨L, fun h0 => ?_, ?_⟩
  · have := congrArg WittVector.constantCoeff h0
    rw [map_mul, map_zero, hL0] at this
    exact mul_ne_zero (xi_bar_ne_zero e he) hw₀ this
  · rw [hΦ]; exact sub_eq_zero.1 hFL

end GlobalTheory.PeriodSol
end
end

section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule : ∀ (E : Type) [Field E] [NumberField E] (d : (AdeleRing (𝓞 E) E)ˣ), GlobalTheory.Mem.Chr.CharModel.logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  first | (exact @GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (exact GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (intros; apply GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule  <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem _root_.GlobalTheory.T.serreTate_linearIndependent_of_weightwise : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (G : Subgroup (GQ l)) (E : IntermediateField ℚ_[l] (Om l)), (∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E)) → ∀ (r n : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (e : Fin n → Fin r → PadicComplex l) (u : Fin n → ℤ), (∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k) → (∀ (a : ℤ) (c : Fin n → ↥E), (∀ k, u k ≠ a → c k = 0) → ∑ k, (((c k : ↥E) : Om l) : PadicComplex l) • e k = 0 → ∀ k, c k = 0) → LinearIndependent (PadicComplex l) e := by
  first | exact @GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise | exact GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise | (intros; apply GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallis_matching_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f₁' f₂' : Gl r F → ℂ) (f₁ f₂ : Hn r F E → ℂ), IsTest f₁' → IsTest f₂' → IsTest f₁ → IsTest f₂ → Match M f₁' f₁ → Match M f₂' f₂ → Match M (f₁' + f₂') (f₁ + f₂) := by
  first | exact @GlobalTheory.JR.match_add | exact GlobalTheory.JR.match_add | (intros; apply GlobalTheory.JR.match_add <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallis_match_of_dense_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ), IsTest f' → IsTest f → ((∀ a : Inv r F, Delta a ≠ 0 → (companion a.1).charpoly.Separable → MatchAt M f' f a) → Match M f' f) ∧ (0 < r → (∀ a : Inv r F, Delta a ≠ 0 → mom (sec a) 0 ≠ 0 → MatchAt M f' f a) → Match M f' f) := by
  first | exact @GlobalTheory.JR.DenseMatch.match_of_dense | exact GlobalTheory.JR.DenseMatch.match_of_dense | (intros; apply GlobalTheory.JR.DenseMatch.match_of_dense <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.involutiveAlg_identity_prod_of_unit_resultant : ∀ (K : UQ) (B₁ B₂ C₁ C₂ : InvAlg K), ((B₁.P * B₂.P) * (C₁.P * C₂.P)).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsIntegral K.O C₁.g → IsIntegral K.O C₂.g → val K.O (resultant (B₁.P * B₂.P) (C₁.P * C₂.P)) = 0 → InvAlg.Identity B₁ B₂ → InvAlg.Identity C₁ C₂ → InvAlg.Identity (B₁.prod C₁) (B₂.prod C₂) := by
  first | exact @GlobalTheory.UnitLemma.ProdId.identity_prod | exact GlobalTheory.UnitLemma.ProdId.identity_prod | (intros; apply GlobalTheory.UnitLemma.ProdId.identity_prod <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitary_lattice_count_ratio_tendsto : UnitaryLimit := by
  first | exact @GlobalTheory.UnitLemma.unitaryLimit | exact GlobalTheory.UnitLemma.unitaryLimit | (intros; apply GlobalTheory.UnitLemma.unitaryLimit <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_weilRepSL2_hermitianBlock : WeilEt → GammaOne → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Hn r F E → ℂ) → Hn r F E → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t X, W (nS t) f X = ψ (t * Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2) * f X) ∧ W (wS F) f = fourU M ψ f := by
  first | exact @GlobalTheory.weilSL2_hermitian | exact GlobalTheory.weilSL2_hermitian | (intros; apply GlobalTheory.weilSL2_hermitian <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.truncatedWhittaker_jHyp_eq_orbitalIntegral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = A.orbK μK φ' a := by
  first | exact @GlobalTheory.whittaker_jHyp_eq_orbK | exact GlobalTheory.whittaker_jHyp_eq_orbK | (intros; apply GlobalTheory.whittaker_jHyp_eq_orbK <;> assumption)
end
