module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle540
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSectionAcrisBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormAinfDisc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle067
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormConstantCoeffEqOneOfEisensteinFrobeniusCycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle608
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.Cpt

theorem of_add {R : Type} (Q : ℕ → R → Prop) (hmono : ∀ n x, Q (n + 1) x → Q n x) :
    ∀ n k x, Q (n + k) x → Q n x := by
  intro n k x
  induction k with
  | zero => exact id
  | succ k ih => exact fun h => ih (hmono _ _ (by rwa [← add_assoc] at h))

def Good {R : Type} [CommRing R] {ι : Type} (I : ℕ → Ideal R) (Q : ℕ → (ι → R) → Prop) (n : ℕ) (y : ι → R) :
    Prop :=
  ∀ k, n ≤ k → ∃ x, Q k x ∧ ∀ i, x i - y i ∈ I n

theorem exists_seq {R : Type} [CommRing R] (I : ℕ → Ideal R) (hI : ∀ n, I (n + 1) ≤ I n) (hI0 : I 0 = ⊤)
    (hfin : ∀ n, Finite (R ⧸ I n)) (ι : Type) [Finite ι] (Q : ℕ → (ι → R) → Prop)
    (hmono : ∀ n x, Q (n + 1) x → Q n x) (hcong : ∀ n x y, Q n x → (∀ i, x i - y i ∈ I n) → Q n y)
    (hex : ∀ n, ∃ x, Q n x) :
    ∃ y : ℕ → ι → R, (∀ n, Q n (y n)) ∧ ∀ n i, y (n + 1) i - y n i ∈ I n := by
  classical
  have step : ∀ n y, Good I Q n y → ∃ y', Good I Q (n + 1) y' ∧ ∀ i, y' i - y i ∈ I n := by
    intro n y hy
    by_contra hne
    haveI : Finite (ι → R ⧸ I (n + 1)) := by haveI := hfin (n + 1); infer_instance
    let rep : (ι → R ⧸ I (n + 1)) → ι → R := fun t i => Classical.choose (Ideal.Quotient.mk_surjective (t i))
    have hrep : ∀ t i, Ideal.Quotient.mk (I (n + 1)) (rep t i) = t i :=
      fun t i => Classical.choose_spec (Ideal.Quotient.mk_surjective (t i))
    let P : (ι → R ⧸ I (n + 1)) → Prop := fun t =>
      ∃ k, n + 1 ≤ k ∧ ¬ ∃ x, Q k x ∧ ∀ i, x i - rep t i ∈ I (n + 1)
    let kf : (ι → R ⧸ I (n + 1)) → ℕ := fun t => if h : P t then h.choose else 0
    have hkf : ∀ t (h : P t), kf t = h.choose := fun t h => dif_pos h
    obtain ⟨t0, ht0⟩ := Finite.exists_max kf
    obtain ⟨x, hx, hxy⟩ := hy (n + kf t0) (Nat.le_add_right _ _)
    let t : ι → R ⧸ I (n + 1) := fun i => Ideal.Quotient.mk _ (x i)
    have hxt : ∀ i, x i - rep t i ∈ I (n + 1) := fun i =>
      Ideal.Quotient.eq.1 (hrep t i).symm
    have hty : ∀ i, rep t i - y i ∈ I n := fun i => by
      have : rep t i - y i = (x i - y i) - (x i - rep t i) := by ring
      rw [this]
      exact sub_mem (hxy i) (hI n (hxt i))
    have hng : ¬ Good I Q (n + 1) (rep t) := fun hg => hne ⟨rep t, hg, hty⟩
    have hP : P t := by
      by_contra hc
      refine hng fun k hk => ?_
      by_contra hk'
      exact hc ⟨k, hk, hk'⟩
    have hs := hP.choose_spec
    rw [← hkf t hP] at hs
    refine hs.2 ⟨x, ?_, hxt⟩
    have hle : kf t ≤ n + kf t0 := (ht0 t).trans (Nat.le_add_left _ _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    exact of_add Q hmono (kf t) d x (hd ▸ hx)
  choose! f hf1 hf2 using step
  let seq : ℕ → ι → R := fun n => Nat.rec (motive := fun _ => ι → R) 0 (fun n y => f n y) n
  have hgood : ∀ n, Good I Q n (seq n) := by
    intro n
    induction n with
    | zero =>
      intro k _
      obtain ⟨x, hx⟩ := hex k
      exact ⟨x, hx, fun i => by rw [hI0]; exact Submodule.mem_top⟩
    | succ n ih => exact hf1 n (seq n) ih
  refine ⟨seq, fun n => ?_, fun n i => hf2 n (seq n) (hgood n) i⟩
  obtain ⟨x, hx, hxs⟩ := hgood n n le_rfl
  exact hcong n x (seq n) hx hxs

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem X_pow_mem (bk : BK K) (n m : ℕ) :
    (X : bk.S) ^ (bk.Ep.natDegree * (n + m)) ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} := by
  have h1 : (X : bk.S) ^ (bk.Ep.natDegree * (n + m)) ∈
      (Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E}) ^ (n + m) := by
    rw [pow_mul]; exact Ideal.pow_mem_pow (BK.X_pow_natDegree_mem bk) _
  have h2 := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {bk.E})
    (n := n) (m := m)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
  exact h2 h1

theorem finite_quot (bk : BK K) (n m : ℕ) :
    Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m})) := by
  haveI := GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow l K bk n (bk.Ep.natDegree * (n + m))
  have H : Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ (bk.Ep.natDegree * (n + m))} ≤
      Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} :=
    sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 (X_pow_mem bk n m))
  refine Finite.of_surjective (Ideal.Quotient.factor H) fun y => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

theorem exists_lim (bk : BK K) (m : ℕ) (s : ℕ → bk.S)
    (hs : ∀ n, s (n + 1) - s n ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) :
    ∃ L : bk.S, ∀ n, s (n + m) - L ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} := by
  have hd : ∀ n, ∃ a b : bk.S, s (n + 1) - s n = (l : bk.S) ^ n * a + bk.E ^ m * b := by
    intro n
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hs n)
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨a, b, by rw [← hyz]; ring⟩
  choose a b hab using hd
  let z : ℕ → bk.S := fun n => s n - bk.E ^ m * ∑ k ∈ Finset.range n, b k
  have hz1 : ∀ n, z (n + 1) - z n = (l : bk.S) ^ n * a n := by
    intro n
    simp only [z, Finset.sum_range_succ]
    linear_combination hab n
  have hcau : ∀ n N, n ≤ N → z N - z n ∈ Ideal.span {(l : bk.S) ^ n} := by
    intro n N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      have : z (N + 1) - z n = (z (N + 1) - z N) + (z N - z n) := by ring
      rw [this, hz1]
      exact add_mem (Ideal.mem_span_singleton.2 (dvd_mul_of_dvd_left (pow_dvd_pow _ hN) _)) ih
  have hJ : ∀ n, Ideal.span {(l : bk.S) ^ n} ≤ bk.J ^ n := fun n => by
    rw [← Ideal.span_singleton_pow]; exact Ideal.pow_right_mono le_sup_left n
  obtain ⟨L, hL⟩ := bk.complete.toIsPrecomplete.prec (f := z) (fun {p q} hpq => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (hJ p (hcau p q hpq)))
  refine ⟨L, fun n => ?_⟩
  have h1 := hL (n + m)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {bk.E})
    (n := n) (m := m)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
  have : s (n + m) - L = (z (n + m) - L) + bk.E ^ m * ∑ k ∈ Finset.range (n + m), b k := by
    simp only [z]; ring
  rw [this]
  exact add_mem (h2 h1) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem compact : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) [Finite ι] (m : ℕ)
    (Q : ℕ → (ι → bk.S) → Prop), (∀ n x, Q (n + 1) x → Q n x) →
    (∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) → Q n y) →
    (∀ n, ∃ x, Q n x) → ∃ x, ∀ n, Q n x := by
  intro l _ K bk ι _ m Q hmono hcong hex
  obtain ⟨y, hQ, hy⟩ := exists_seq (fun n => Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m})
    (fun n => sup_le_sup_right (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ n))) _)
    (by simp) (fun n => finite_quot bk n m) ι Q hmono hcong hex
  choose L hL using fun i => exists_lim bk m (fun n => y n i) (fun n => hy n i)
  exact ⟨L, fun n => hcong n _ _ (of_add Q hmono n m _ (hQ (n + m))) (fun i => hL i n)⟩

end GlobalTheory.BKLim.Cpt
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.CrZero

theorem pow_cancel {A : Type*} [CommRing A] (p : A) (hp : ∀ x : A, p * x = 0 → x = 0)
    (k : ℕ) (a b : A) (h : p ^ k * a = p ^ k * b) : a = b := by
  induction k generalizing a b with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have h' : p * (p ^ k * a - p ^ k * b) = 0 := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', h, sub_self]
    exact sub_eq_zero.mp (hp _ h')

theorem eq_zero_of_forall_dvd {A : Type*} [CommRing A] (p : A)
    (hH : IsHausdorff (Ideal.span {p}) A) (x : A) (h : ∀ M : ℕ, p ^ M ∣ x) : x = 0 := by
  refine hH.haus x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.mpr (h n)

end GlobalTheory.CrZero


open GlobalTheory.CrZero in
theorem GlobalTheory.BKLim.acris_frob_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d c : ℕ)
    (D₀ F F' : Matrix (Fin d) (Fin d) (Per.Acris l)),
    (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D₀ i j) →
    (l : Per.Acris l) ^ c • D₀ = F * D₀.map (phiA l) * F' → D₀ = 0 := by
  intro l _ K bk d c D₀ F F' hdiv hfr
  obtain ⟨htor, hcomp, -, hphi, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  set u := ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X with hu
  have hφu : phiA l u = u ^ l := by
    rw [hu, RingHom.comp_apply, hphi, ← bk.ev_frob]
    have : frobS l bk.a X = X ^ l := by simp [frobS]
    rw [this, map_pow, map_pow]
  have hφl : ∀ k : ℕ, phiA l ((l : Per.Acris l) ^ k) = (l : Per.Acris l) ^ k := by
    intro k; simp

  have key : ∀ n : ℕ, ∃ N : Matrix (Fin d) (Fin d) (Per.Acris l),
      (l : Per.Acris l) ^ (c * n) • D₀ = u ^ (l ^ n) • N := by
    intro n
    induction n with
    | zero =>
      refine ⟨Matrix.of fun i j => (hdiv i j).choose, ?_⟩
      ext i j
      simp only [mul_zero, pow_zero, pow_one, one_smul, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [one_mul]; exact (hdiv i j).choose_spec
    | succ n ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨F * N.map (phiA l) * F', ?_⟩
      have hmap : ((l : Per.Acris l) ^ (c * n) • D₀).map (phiA l)
          = (l : Per.Acris l) ^ (c * n) • D₀.map (phiA l) := by
        ext i j; simp [hφl]
      have hmap2 : (u ^ (l ^ n) • N).map (phiA l) = u ^ (l ^ (n + 1)) • N.map (phiA l) := by
        ext i j; simp [hφu, ← pow_mul]; ring
      calc (l : Per.Acris l) ^ (c * (n + 1)) • D₀
          = (l : Per.Acris l) ^ (c * n) • ((l : Per.Acris l) ^ c • D₀) := by
            rw [smul_smul, ← pow_add, mul_add, mul_one]
        _ = F * (((l : Per.Acris l) ^ (c * n) • D₀).map (phiA l)) * F' := by
            rw [hfr, hmap, Matrix.mul_smul, Matrix.smul_mul]
        _ = u ^ (l ^ (n + 1)) • (F * N.map (phiA l) * F') := by
            rw [hN, hmap2, Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  have hH : IsHausdorff (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) := hcomp.toIsHausdorff
  refine eq_zero_of_forall_dvd _ hH _ fun M => ?_
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually l K bk c M
  obtain ⟨N, hN⟩ := key n₀
  obtain ⟨y, hy⟩ := hn₀ n₀ le_rfl
  have hent : (l : Per.Acris l) ^ (c * n₀) * D₀ i j = u ^ (l ^ n₀) * N i j := by
    have := congrFun (congrFun hN i) j
    simpa using this
  have hpos : 1 ≤ l ^ n₀ := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hsplit : u ^ (l ^ n₀) = u * u ^ (l ^ n₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨u * y * N i j, ?_⟩
  apply pow_cancel _ htor (c * n₀)
  rw [hent, hsplit, hy]
  ring
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem norm_iA_mu_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (e : OCb l), IsEps e →
    ‖bk.iA (mu e)‖ ≤ (l : ℝ)⁻¹ ∧ (l = 2 → ‖bk.iA (mu e)‖ ≤ (4 : ℝ)⁻¹) := by
  intro l _ K bk e he
  have hker := (GlobalTheory.T.breuilKisin_seedDisc_norm_bounds l K bk).2.2
  have hθmu : Per.θ l (mu e) = 0 := by
    simp only [mu, map_sub, map_one]
    simp [he.1]
  refine ⟨hker _ hθmu, ?_⟩
  rintro rfl
  set δ := (frobeniusEquiv (Per.Fl 2) 2).symm e with hδ
  have hδ2 : δ ^ 2 = e := by
    rw [hδ]; exact frobenius_apply_frobeniusEquiv_symm (Per.Fl 2) 2 e
  have hu : δ.untilt ^ 2 = 1 := by
    rw [← map_pow, hδ2, he.1]
  have hu' : δ.untilt = -1 := by
    have h1 : (δ.untilt - 1) * (δ.untilt + 1) = 0 := by linear_combination hu
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) he.2
    · linear_combination h
  have hθa : Per.θ 2 (Per.tm δ + 1) = 0 := by
    simp [hu']
  have ha := hker _ hθa
  have hfac : mu e = (Per.tm δ + 1) * ((Per.tm δ + 1) - 2) := by
    simp only [mu]
    rw [← hδ2]
    show WittVector.teichmuller 2 (δ ^ 2) - 1 = _
    rw [map_pow]
    ring
  have h2 : ‖bk.iA ((Per.tm δ + 1) - 2)‖ ≤ (2 : ℝ)⁻¹ := by
    rw [map_sub]
    have hn2 : ‖bk.iA 2‖ ≤ (2 : ℝ)⁻¹ := by
      have := DiscBasic.norm_l_disc_le 2 (bk.ev X) bk.ρ₀
      rw [map_ofNat]; simpa using this
    rw [sub_eq_add_neg]
    refine (DiscBasic.norm_add_le_max_disc 2 (bk.ev X) bk.ρ₀ _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · rw [norm_neg]; exact hn2
  rw [hfac, map_mul]
  refine (norm_mul_le _ _).trans ?_
  have : ((2 : ℕ) : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (4 : ℝ)⁻¹ := by norm_num
  rw [← this]
  exact mul_le_mul ha h2 (norm_nonneg _) (by positivity)

end GlobalTheory.BSP.BK
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_breuilKisin_eisenstein_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d m n : ℕ) (Y : Matrix (Fin d) (Fin m) (bk.S)), ∃ (c : ℕ) (X X' R : Matrix (Fin d) (Fin d) (bk.S)) (Q : Matrix (Fin m) (Fin d) (bk.S)) (Q' : Matrix (Fin d) (Fin m) (bk.S)), X * X' = ((l : bk.S) ^ c * bk.E ^ n) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ X = Y * Q + bk.E ^ n • R ∧ (l : bk.S) ^ c • Y = X * Q' := by
  first | exact @GlobalTheory.BSP.LocalizedLatticeBasis.exists_lattice_basis | exact GlobalTheory.BSP.LocalizedLatticeBasis.exists_lattice_basis | (intros; apply GlobalTheory.BSP.LocalizedLatticeBasis.exists_lattice_basis <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_pow_mul_unramified_eq_witt_bcris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) ∈ K.1 → ∃ (n : ℕ) (w : Wq l bk.a), (l : Per.Bcris l) ^ n * C.u c = Per.aB l (wA l bk.a w) := by
  first | exact @GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB | exact GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB | (intros; apply GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsUnit (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) := by
  first | exact @GlobalTheory.BSP.isUnit_toDisc_frobS_E | exact GlobalTheory.BSP.isUnit_toDisc_frobS_E | (intros; apply GlobalTheory.BSP.isUnit_toDisc_frobS_E <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.digitMonomials_basis_envelope_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (J : Ideal A) (r : ℕ → MvPolynomial ℕ A), (∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ r i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) → ∀ n : ℕ, (∀ x : MvPolynomial ℕ A, ∃ c : Digits l →₀ A, x - c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) ∧ ∀ c : Digits l →₀ A, c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) → ∀ α, c α ∈ J ^ n := by
  first | exact @GlobalTheory.digitMonomials_basis_mod_pow | exact GlobalTheory.digitMonomials_basis_mod_pow | (intros; apply GlobalTheory.digitMonomials_basis_mod_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_frobenius_section_acris_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (A A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → ∃ (k : ℕ) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)), Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) ∧ (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ (Q' - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) ∧ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a bk.E) ^ N • (Q * (A.map fun s => ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff s))))) = ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) ^ N • ((A.map fun s => ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a s)) * Q.map (phiA l)) := by
  first | exact @GlobalTheory.CrisSec.phiSection | exact GlobalTheory.CrisSec.phiSection | (intros; apply GlobalTheory.CrisSec.phiSection <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_gaussNorm_ainf_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∃ N : Ainf l → ℝ, (∀ x y, N (x * y) = N x * N y) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ N (l : Ainf l) = (l : ℝ)⁻¹ ∧ (∀ x, N x ≤ ‖toDisc l (bk.ev X) ρ x‖) ∧ ∀ x, (ρ : ℝ) * ‖toDisc l (bk.ev X) ρ x‖ ≤ N x := by
  first | exact @GlobalTheory.DiscGauss.exists_gauss_disc | exact GlobalTheory.DiscGauss.exists_gauss_disc | (intros; apply GlobalTheory.DiscGauss.exists_gauss_disc <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_integral_powerSeries_division_approx : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧), g ∈ A O K → ∀ n₀ : ℕ, ‖coeff n₀ g‖ = 1 → (∀ i < n₀, ‖coeff i g‖ < 1) → ∀ δ : ℝ, 0 < δ → ∀ f ∈ A O K, ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := by
  first | exact @GlobalTheory.BK.DivApprox.exists_div_approx | exact GlobalTheory.BK.DivApprox.exists_div_approx | (intros; apply GlobalTheory.BK.DivApprox.exists_div_approx <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.norm_constantCoeff_eq_one_of_eisenstein_frobenius_cycle : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (l e a M N : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (Δ k k' : ZMod a → K⟦X⟧), (∀ τ n, ‖coeff n (Δ τ)‖ ≤ 1) → (∀ τ, ∃ n, ‖coeff n (Δ τ)‖ = 1) → (∀ τ n, ‖coeff n (k τ)‖ ≤ 1) → (∀ τ n, ‖coeff n (k' τ)‖ ≤ 1) → (∀ τ, k τ * k' τ = E K l e ^ N) → (∀ τ, Δ τ * k τ = E K l e ^ M * frob K l (Δ (τ - 1))) → ∀ τ, ‖constantCoeff (Δ τ)‖ = 1 := by
  first | exact @GlobalTheory.BK.Cycle.norm_constantCoeff_eq_one_of_cycle | exact GlobalTheory.BK.Cycle.norm_constantCoeff_eq_one_of_cycle | (intros; apply GlobalTheory.BK.Cycle.norm_constantCoeff_eq_one_of_cycle <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory


theorem _root_.GlobalTheory.T.heckeCharRestrictMaxReal_val_eq_prod_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ν : Formalism.L2.Host.HChar E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
    (∀ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v,
      ν.UnrAt w ∧ w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1) →
    (GlobalTheory.PolChar.resReal ν).val v = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v, ν.val w := by
  first | exact @GlobalTheory.PolChar.resReal_val_eq_prod | exact GlobalTheory.PolChar.resReal_val_eq_prod | (intros; apply GlobalTheory.PolChar.resReal_val_eq_prod <;> assumption)
end
end
