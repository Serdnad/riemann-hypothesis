module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle301
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle302
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle303
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle306
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplFrob

variable {l : ℕ} [Fact l.Prime]

theorem frobW_inclW (a : Ainf l) :
    frobW l (inclW l a) = inclW l (WittVector.map (frobenius (OCb l) l) a) := by
  ext n
  rw [coeff_frobW, coeff_inclW, coeff_inclW, WittVector.map_coeff, frobenius_def, map_pow]

theorem frob_inclR (LL : FinExt l) (a : RA LL) :
    ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a' := by
  refine ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]]
    WittVector.map (frobenius (OCb l) l) (crd (basisO LL) j a), ext_crd (basisO LL) fun i => ?_⟩
  rw [crd_φRW, crd_inclR, crd_inclR, crd_sum, frobW_inclW]

theorem nearPi_frob {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s m n : ℕ)
    (h : n ≤ m * l) (x : RW LL) (hx : NearPi AI LL s m x) : NearPi AI LL s n (φRW LL x) := by
  rw [nearPi_iff_crd] at hx ⊢
  intro i
  obtain ⟨c, hc⟩ := hx i
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  refine ⟨(AI.εroot s - 1) ^ k * c ^ l, ?_⟩
  rw [crd_φRW, coeff_frobW, hc, ← map_pow, mul_pow, ← pow_mul, hk, pow_add, mul_assoc]

theorem near_self {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (p : ℕ) (t : R) :
    Near ι p t 1 t := ⟨1, 0, by simp⟩

theorem not_isUnit_root_sub_one {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    ¬ IsUnit (AI.εroot s - 1) := fun h =>
  one_ne_zero ((GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).1 1
    fun m => (h.pow m).dvd)

theorem dvd_of_coeff {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) (z : ℤ_[l]) (c : OCb l)
    (h : (z • (1 : WCb l)).coeff 0 = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ 1 * c)) :
    (l : ℤ_[l]) ∣ z := by
  by_contra hz
  have hu : IsUnit z := by
    rw [PadicInt.isUnit_iff]
    rw [← PadicInt.norm_lt_one_iff_dvd] at hz
    exact le_antisymm z.2 (not_lt.1 hz)
  have h1 : z • (1 : WCb l) = inclW l (zlW l (OCb l) z) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (map_zlW l (algebraMap (OCb l) (Cb l)) z).symm
  rw [h1, coeff_inclW, pow_one] at h
  have h2 := IsFractionRing.injective (OCb l) (Cb l) h
  have h3 : IsUnit ((zlW l (OCb l) z).coeff 0) :=
    (hu.map (zlW l (OCb l))).map (WittVector.constantCoeff : Ainf l →+* OCb l)
  rw [h2] at h3
  exact not_isUnit_root_sub_one AI s (isUnit_of_mul_isUnit_left h3)

theorem const_dvd {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (o : ↥(OL LL))
    (h : NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o)) :
    ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  rw [nearPi_iff_crd] at h
  have h1 : ∀ i, (l : ℤ_[l]) ∣ (basisO LL).repr o i := fun i => by
    obtain ⟨c, hc⟩ := h i
    exact dvd_of_coeff AI s _ c hc
  choose d hd using h1
  refine ⟨∑ i, d i • basisO LL i, ?_⟩
  rw [Finset.mul_sum]
  refine ((basisO LL).sum_repr o).symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hd, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem frobenius_and_constants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ),
    (∀ a : RA LL, ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a') ∧
    NearPi AI LL s 2 (φRW LL (piR AI LL s)) ∧
    (∀ (m : ℕ) (x : RW LL), NearPi AI LL s m x → NearPi AI LL s m (φRW LL x)) ∧
    ∀ o : ↥(OL LL), NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o) →
      ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  intro l hl P AI LL s
  refine ⟨frob_inclR LL, ?_, fun m x hx => ?_, const_dvd AI LL s⟩
  · exact nearPi_frob AI LL s 1 2 (by rw [one_mul]; exact hl.out.two_le) _ (near_self _ _ _)
  · exact nearPi_frob AI LL s m m (Nat.le_mul_of_pos_right m hl.out.pos) x hx

end GlobalTheory.DecomplFrob
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.FixL

theorem fix_of_mul {R : Type} [CommRing R] (p : ℕ) (h : ∀ x : R, (p : R) * x = 0 → x = 0)
    (f : R →+* R) (x : R) (hx : f ((p : R) * x) = (p : R) * x) : f x = x := by
  have hf : f (p : R) = (p : R) := map_natCast f p
  have h2 : (p : R) * (f x - x) = 0 := by
    rw [mul_sub, ← hf, ← map_mul, hx, hf, sub_self]
  exact sub_eq_zero.mp (h _ h2)

theorem fix_of_sum {R : Type} [CommRing R] (p : ℕ)
    (h : ∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0)
    (f : R →+* R) (x : ℕ → R) (hx : ∀ i, f (x i) = x i) (y : R)
    (hy : ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) :
    f y = y := by
  apply sub_eq_zero.mp
  apply h
  intro k
  obtain ⟨r, hr⟩ := hy k
  have hsum : f (∑ i ∈ Finset.range k, (p : R) ^ i * x i) = ∑ i ∈ Finset.range k, (p : R) ^ i * x i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_mul, map_pow, map_natCast, hx]
  have hfy : f y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * f r := by
    rw [← hsum, ← map_sub, hr, map_mul, map_pow, map_natCast]
  refine ⟨f r - r, ?_⟩
  rw [mul_sub, ← hfy, ← hr]
  ring

theorem frob_comm {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l)
    (g : GQ l) (x : RW LL) : AI.gRW LL g (φRW LL x) = φRW LL (AI.gRW LL g x) := by
  have key : ∀ w : WCb l, AI.actWCbHom g (frobW l w) = frobW l (AI.actWCbHom g w) := by
    intro w
    unfold LocAinf.actWCbHom frobW
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    unfold mapAlgEquivW
    ext n
    dsimp only [AlgEquiv.ofRingEquiv]
    simp [mapEquivW, WittVector.map_coeff, frobenius_def]
  have hc : ((AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l).comp (frobW l)) =
      (frobW l).comp (AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l) := AlgHom.ext key
  unfold LocAinf.gRW φRW
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
    ← Algebra.TensorProduct.map_comp, hc]

private theorem mem_fixSub_lemma {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (LL : FinExt l) (H : Set (GQ l)) (x : RW LL) :
    x ∈ fixSub AI LL H ↔ ∀ g ∈ H, AI.gRW LL g x = x := by
  unfold fixSub
  simp [Subring.mem_iInf, RingHom.mem_eqLocus]

theorem fixSub_ladic (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l)
    (H : Set (GQ l)) :
    (∀ x, (l : RW LL) * x ∈ fixSub AI LL H → x ∈ fixSub AI LL H) ∧
    (∀ x ∈ fixSub AI LL H, φRW LL x ∈ fixSub AI LL H) ∧
    ∀ x : ℕ → RW LL, (∀ i, x i ∈ fixSub AI LL H) → ∃ y ∈ fixSub AI LL H, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.Decompl.LAdic.ladic_RW l LL
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_fixSub_lemma] at hx ⊢
    intro g hg
    exact fix_of_mul l h0 (AI.gRW LL g : RW LL →+* RW LL) x (hx g hg)
  · intro x hx
    rw [mem_fixSub_lemma] at hx ⊢
    intro g hg
    rw [frob_comm, hx g hg]
  · intro x hx
    obtain ⟨s, hs⟩ := h2 x
    refine ⟨s, ?_, hs⟩
    rw [mem_fixSub_lemma]
    intro g hg
    exact fix_of_sum l h1 (AI.gRW LL g : RW LL →+* RW LL) x
      (fun i => (mem_fixSub_lemma AI LL H (x i)).1 (hx i) g hg) s hs

end GlobalTheory.Decompl.FixL
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage.Values

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)

theorem zeta_pow (m i : ℕ) : P.ζQ (m + i) ^ (l ^ i) = P.ζQ m := by
  induction i with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, P.ζQ_succ, ih]

theorem cycVal_single {s e j : ℕ} (hj : 1 ≤ j) (hjs : j ≤ s) (μ : ℕ → ℤ) (V : Om l)
    (hμ : ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (μ a : Om l) * P.ζQ i ^ a = if i = j then V else 0)
    (x : ↥(K0 K)) :
    cycVal P K s e (fun a => (μ a : ↥(K0 K)) * x) 0 =
      (l : Om l) ^ (e * (s - j)) * (((frK P K ^ (s - j)) x : ↥(K0 K)) : Om l) * V := by
  have key : ∀ i ∈ Finset.range s,
      ∑ a ∈ primeTo l s, (((frK P K ^ i) ((μ a : ↥(K0 K)) * x) : ↥(K0 K)) : Om l) *
        P.ζQ s ^ (a * l ^ i) =
      (((frK P K ^ i) x : ↥(K0 K)) : Om l) * (if s - i = j then V else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [← hμ (s - i) (by omega) (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hz : P.ζQ s ^ (l ^ i) = P.ζQ (s - i) := by
      have := zeta_pow P (s - i) i
      rwa [Nat.sub_add_cancel hi'.le] at this
    rw [map_mul, map_intCast, mul_comm a, pow_mul, hz]
    push_cast
    ring
  unfold cycVal
  rw [Finset.sum_congr rfl fun i hi => by rw [key i hi], Finset.sum_eq_single (s - j)]
  · rw [if_pos (by omega)]
    simp [mul_assoc]
  · intro i hi hne
    have hi' := Finset.mem_range.mp hi
    rw [if_neg (by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem cycVal_add (s e : ℕ) (f g : ℕ → ↥(K0 K)) (d : ↥(K0 K)) :
    cycVal P K s e (fun a => f a + g a) d =
      cycVal P K s e f 0 + cycVal P K s e g 0 + (l : Om l) ^ (s * e) * (d : Om l) := by
  unfold cycVal
  simp only [map_add (f := _), IntermediateField.coe_add, add_mul, Finset.sum_add_distrib, mul_add,
    IntermediateField.coe_zero, mul_zero, add_zero]

theorem exists_pre (k : ℕ) (y : ↥(K0 K)) :
    ∃ x : ↥(K0 K), (frK P K ^ k) x = y ∧ ‖(x : Om l)‖ = ‖(y : Om l)‖ := by
  induction k generalizing y with
  | zero => exact ⟨y, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨z, rfl⟩ := (P.PD K).σ_bij.2 y
    obtain ⟨x, hx, hn⟩ := ih z
    refine ⟨x, ?_, ?_⟩
    · rw [pow_succ', AlgHom.mul_apply, hx]
    · rw [hn]
      exact ((GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1 z).symm

theorem norm_int_mul {z : ℤ} {x : ↥(K0 K)} (hx : ‖(x : Om l)‖ ≤ 1) :
    ‖(((z : ↥(K0 K)) * x : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  push_cast
  rw [norm_mul]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ z) (norm_nonneg _) hx

theorem norm_pow_mul (k : ℕ) {x : ↥(K0 K)} (hx : ‖(x : Om l)‖ ≤ 1) :
    ‖(((l : ↥(K0 K)) ^ k * x : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  have := norm_int_mul K (z := (l : ℤ) ^ k) hx
  simpa using this

theorem sum_zeta : ∑ r ∈ Finset.Ico 1 l, P.ζQ 1 ^ r = -1 := by
  have h1 : P.ζQ 1 ^ l = 1 := (P.ζQ_succ 0).trans P.ζQ_zero
  have h2 := mul_geom_sum (P.ζQ 1) l
  rw [h1, sub_self, mul_eq_zero] at h2
  have h3 := h2.resolve_left (sub_ne_zero.mpr P.ζQ_one)
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Fact.out : l.Prime).pos] at h3
  simp only [pow_zero, zero_add] at h3
  linear_combination h3

theorem exists_minus_one {s : ℕ} (hs : 1 ≤ s) : ∃ ν : ℕ → ℤ,
    ∑ a ∈ primeTo l s, ν a = ((l : ℤ) - 1) * (l : ℤ) ^ (s - 1) ∧ ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (ν a : Om l) * P.ζQ i ^ a =
        if i = 1 then -(l : Om l) ^ (s - 1) else 0 := by
  have h : ∀ r : ℕ, ∃ μ : ℕ → ℤ, r ∈ Finset.Ico 1 l →
      (∑ a ∈ primeTo l s, μ a = (l : ℤ) ^ (s - 1) ∧ ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (μ a : Om l) * P.ζQ i ^ a =
        if i = 1 then (l : Om l) ^ (s - 1) * P.ζQ 1 ^ r else 0) := by
    intro r
    by_cases hr : r ∈ Finset.Ico 1 l
    · have hr' := Finset.mem_Ico.mp hr
      obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_int_weights_compatibleRootsOfUnity_levels l P.ζQ P.ζQ_zero P.ζQ_one P.ζQ_succ s 1 r le_rfl hs
        (Nat.not_dvd_of_pos_of_lt hr'.1 hr'.2)
      exact ⟨μ, fun _ => ⟨by simpa using h1, by simpa using h2⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose μ hμ using h
  refine ⟨fun a => ∑ r ∈ Finset.Ico 1 l, μ r a, ?_, fun i hi his => ?_⟩
  · rw [Finset.sum_comm, Finset.sum_congr rfl fun r hr => (hμ r hr).1, Finset.sum_const,
      Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (Fact.out : l.Prime).one_lt.le, Nat.cast_one]
  · push_cast
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun r hr => (hμ r hr).2 i hi his]
    split_ifs
    · rw [← Finset.mul_sum, sum_zeta]
      ring
    · simp

theorem exists_cycVal_eq (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e j n : ℕ)
    (hj : 1 ≤ j) (hjs : j ≤ s) (hn : ¬ l ∣ n) (c : Om l) (hc : c ∈ K0 K) (hc1 : ‖c‖ ≤ 1) :
    ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧
      d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧
      cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * (c * P.ζQ j ^ n) := by
  obtain ⟨c, rfl⟩ : ∃ c' : ↥(K0 K), (c' : Om l) = c := ⟨⟨c, hc⟩, rfl⟩
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_int_weights_compatibleRootsOfUnity_levels l P.ζQ P.ζQ_zero P.ζQ_one P.ζQ_succ s j n hj hjs hn
  by_cases hj1 : j = 1
  · subst hj1
    simp only [if_true] at h1 h2
    obtain ⟨ν, g1, g2⟩ := exists_minus_one P hjs
    obtain ⟨d, hd, hdc⟩ := (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).2 (e + 1) (by omega) (frK P K c)
      (by rw [(GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1]; exact hc1)
    obtain ⟨x, hx, hxn⟩ := exists_pre P K (s - 1) c
    obtain ⟨y, hy, hyn⟩ := exists_pre P K (s - 1) ((l : ↥(K0 K)) ^ e * d)
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at *
    refine ⟨fun a => (μ a : ↥(K0 K)) * x + (ν a : ↥(K0 K)) * y, (l : ↥(K0 K)) ^ t * d,
      fun a => ?_, norm_pow_mul K t hd, ?_, ?_⟩
    · rw [IntermediateField.coe_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        (norm_int_mul K (hxn ▸ hc1)) (norm_int_mul K (hyn ▸ norm_pow_mul K e hd)))
    · rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Int.cast_sum,
        ← Int.cast_sum, h1, g1, pow_succ' (frK P K), AlgHom.mul_apply, map_add, map_mul, map_mul,
        map_mul, map_intCast, map_intCast, hx, hy]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_intCast]
      push_cast
      linear_combination (l : ↥(K0 K)) ^ t * hdc
    · rw [cycVal_add, cycVal_single P K le_rfl hjs μ _ h2, cycVal_single P K le_rfl hjs ν _ g2]
      simp only [Nat.add_sub_cancel]
      rw [hx, hy]
      push_cast
      ring
  · simp only [if_neg hj1] at h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, s = k + 2 + t := ⟨s - (k + 2), by omega⟩
    obtain ⟨x, hx, hxn⟩ := exists_pre P K t ((l : ↥(K0 K)) ^ ((e + 1) * k + e) * c)
    refine ⟨fun a => (μ a : ↥(K0 K)) * x, 0,
      fun a => norm_int_mul K (hxn ▸ norm_pow_mul K _ hc1), by simp, ?_, ?_⟩
    · rw [← Finset.sum_mul, ← Int.cast_sum, h1]
      simp
    · rw [cycVal_single P K hj hjs μ _ h2, Nat.add_sub_cancel_left, hx,
        show k + 2 + t - 1 = k + t + 1 by omega]
      push_cast
      ring

end GlobalTheory.ExpImage.Values
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpStep

theorem exists_fixed {A W : Type} [CommRing A] [CommRing W] (i : A →+* W) (φ : A →+* A)
    (Φ : W →+* W) (h : ∀ a, Φ (i a) = i (φ a)) {N D c : A} (hD : IsUnit (i D))
    (hN : φ N = c * N) (hD' : φ D = c * D) : ∃ w : W, Φ w = w ∧ i N = w * i D := by
  obtain ⟨v, hv⟩ := hD.exists_left_inv
  have e : i N = i N * v * i D := by rw [mul_assoc, hv, mul_one]
  refine ⟨i N * v, ?_, e⟩
  apply (hD.map Φ).mul_right_cancel
  rw [← map_mul, ← e, h, h, hN, hD', map_mul, map_mul]
  linear_combination (i c) * e

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem isUnit_inclW {a : Ainf l} (ha : a.coeff 0 ≠ 0) : IsUnit (inclW l a) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [inclW, WittVector.map_coeff]
  exact fun hz => ha (IsFractionRing.injective (OCb l) (Cb l) (by rw [hz, map_zero]))

theorem π₁_coeff : AI.π₁.coeff 0 ≠ 0 := by
  have h0 : AI.π₁.coeff 0 = AI.ε1 - 1 := by
    change WittVector.constantCoeff (WittVector.teichmuller l AI.ε1 - 1) = _
    rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  rw [h0]
  intro hz
  apply AI.ε_ne_one
  rw [← frobeniusEquiv_symm_pow_p (OCb l) l AI.ε]
  change AI.ε1 ^ l = 1
  rw [sub_eq_zero.mp hz, one_pow]

theorem act_π₁_coeff (g : GQ l) : (AI.actW g AI.π₁).coeff 0 ≠ 0 := by
  rw [LocAinf.actW, WittVector.map_coeff]
  intro hz
  exact π₁_coeff AI ((AI.actT g).injective (by rw [map_zero]; exact hz))

theorem frob_π₁ : WittVector.frobenius AI.π₁ = AI.μ := by
  rw [LocAinf.π₁, LocAinf.μ, map_sub, map_one, WittVector.frobenius_eq_map_frobenius,
    WittVector.map_teichmuller, LocAinf.ε1, frobenius_apply_frobeniusEquiv_symm]

theorem frob_act (g : GQ l) (a : Ainf l) :
    WittVector.frobenius (AI.actW g a) = AI.actW g (WittVector.frobenius a) := by
  ext n
  simp only [LocAinf.actW, WittVector.coeff_frobenius_charP, WittVector.map_coeff, map_pow]

theorem frob_zl (z : ℤ_[l]) :
    WittVector.frobenius (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := by
  rw [WittVector.frobenius_eq_map_frobenius]
  exact map_zlW l _ z

theorem frobW_inclW (a : Ainf l) : frobW l (inclW l a) = inclW l (WittVector.frobenius a) := by
  ext n
  change (WittVector.map (frobenius (Cb l) l) (inclW l a)).coeff n = _
  simp only [inclW, WittVector.coeff_frobenius_charP, WittVector.map_coeff, map_pow, frobenius_def]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (U : ℤ_[l]) (k : ℕ) (β η : Ainf l), Step AI g U AI.μ k (WittVector.frobenius β - AI.ξ ^ k * β) (WittVector.frobenius η - AI.ξ ^ k * η) → ∃ z : ℤ_[l], Step AI g U AI.π₁ k β (η + algebraMap ℤ_[l] (Ainf l) z * AI.π₁ ^ k) := by
  intro l _ P AI g U k β η h
  have hu : IsUnit (inclW l (AI.π₁ ^ k * AI.actW g AI.π₁ ^ k)) := by
    rw [map_mul, map_pow, map_pow]
    exact ((isUnit_inclW (π₁_coeff AI)).pow k).mul ((isUnit_inclW (act_π₁_coeff AI g)).pow k)
  obtain ⟨w, hw, e⟩ := exists_fixed (inclW l) WittVector.frobenius (frobW l : WCb l →+* WCb l)
    frobW_inclW (N := algebraMap ℤ_[l] (Ainf l) U * AI.actW g β * AI.π₁ ^ k
      - AI.actW g AI.π₁ ^ k * β - AI.actW g AI.π₁ ^ k * η)
    (c := AI.ξ ^ k * AI.actW g AI.ξ ^ k) hu (by
      unfold Step at h
      simp only [map_sub, map_mul, map_pow, frob_act, frob_zl, frob_π₁, AI.μ_eq, mul_pow] at h ⊢
      linear_combination h) (by
      simp only [map_mul, map_pow, frob_act, frob_π₁, AI.μ_eq, mul_pow]
      ring)
  obtain ⟨z, rfl⟩ := (GlobalTheory.ArtinSchreierWitt.main l).2.1 w hw
  refine ⟨z, ?_⟩
  rw [← (inclWA l).commutes z] at e
  change _ = inclW l _ * _ at e
  rw [← map_mul] at e
  have e' := WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l)) e
  unfold Step
  linear_combination e'

end GlobalTheory.ExpStep
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_abelianizedGalois_hom_of_closureIso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (φ : Ω ≃+* Ω') (j : E →+* E'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → ∃ ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω, Continuous ρ ∧ ∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  first | exact @GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv | exact GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv | (intros; apply GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv <;> assumption)
end

section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.monicIrreducible_inject_regularCharacterOrbits : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Module.finrank (ZMod g) K = d → ∃ c : (ZMod g)[X] → (Kˣ →* ℂˣ), (∀ P, IsPrimeLab d P → IsRegularChar g d (c P)) ∧ ∀ P P', IsPrimeLab d P → IsPrimeLab d P' → (∃ i < d, c P' = c P ^ g ^ i) → P = P' := by
  first | exact @GlobalTheory.PrimeLabOrbit.primeLab_to_regularChar | exact GlobalTheory.PrimeLabOrbit.primeLab_to_regularChar | (intros; apply GlobalTheory.PrimeLabOrbit.primeLab_to_regularChar <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.io_equivariant_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), inclR LL (E.tie.io (W.γA (W.resΓ g) a)) = AI.gRW LL (g : GQ l) (inclR LL (E.tie.io a)) := by
  first | exact @GlobalTheory.Cyc.Decomp.io_equivariant | exact GlobalTheory.Cyc.Decomp.io_equivariant | (intros; apply GlobalTheory.Cyc.Decomp.io_equivariant <;> assumption)
end
