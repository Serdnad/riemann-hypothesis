module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle252
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSolFiltered
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle275
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle742
public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.DecomplMat

variable {R A : Type} [CommRing R] [CommRing A] {ι : A →+* R} {p : ℕ} {t : R}

theorem near_pow_two {x : R} (hx : Near ι p t 2 x) (n : ℕ) : Near ι p t (2 * n) (x ^ n) := by
  induction n with
  | zero => exact ⟨1, 0, by simp⟩
  | succ n ih =>
    have h := ih.mul hx
    rw [← pow_succ] at h
    exact h

theorem near_frob (φ : R →+* R) (hι : ∀ a, ∃ a', φ (ι a) = ι a') (ht : Near ι p t 2 (φ t))
    {n : ℕ} {v : R} (hv : Near ι p t n v) : Near ι p t (2 * n) (φ v) := by
  obtain ⟨a, r, rfl⟩ := hv
  obtain ⟨a', ha'⟩ := hι a
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_natCast, ha', mul_comm _ (ι a')]
  exact ((near_pow_two ht n).mul_ι a').add (Near.of_mul _ _)

theorem near_mul_of_bound {c m : ℕ} {q w : R} (hq : Near ι p t 0 (t ^ c * q))
    (hw : Near ι p t (m + c) w) : Near ι p t m (q * w) := by
  obtain ⟨a, r, rfl⟩ := hw
  obtain ⟨b, s, h⟩ := hq
  refine ⟨b * a, t ^ m * ι a * s + q * r, ?_⟩
  rw [map_mul, pow_add]
  linear_combination (t ^ m * ι a) * h

theorem near_bound_mono {τ : A} (hτ : ι τ = t) {c c' : ℕ} (h : c ≤ c') {q : R}
    (hq : Near ι p t 0 (t ^ c * q)) : Near ι p t 0 (t ^ c' * q) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 := hq.mul_ι (τ ^ k)
  rw [map_pow, hτ] at h1
  convert h1 using 1
  ring

def nearSub (ι : A →+* R) (p : ℕ) (t : R) (m : ℕ) : AddSubgroup R where
  carrier := {x | Near ι p t m x}
  add_mem' := Near.add
  zero_mem' := Near.zero m
  neg_mem' := Near.neg

def vecs (d : ℕ) (H : AddSubgroup R) : AddSubgroup (Fin d → R) where
  carrier := {v | ∀ i, v i ∈ H}
  add_mem' := fun ha hb i => H.add_mem (ha i) (hb i)
  zero_mem' := fun _ => H.zero_mem
  neg_mem' := fun ha i => H.neg_mem (ha i)

def semi {d : ℕ} (Q : Fin d → Fin d → R) (φ : R →+* R) : (Fin d → R) →+ (Fin d → R) where
  toFun v := fun i => ∑ k, Q i k * φ (v k)
  map_zero' := by ext i; simp
  map_add' v w := by ext i; simp [mul_add, Finset.sum_add_distrib]

theorem semi_apply {d : ℕ} (Q : Fin d → Fin d → R) (φ : R →+* R) (v : Fin d → R) (i : Fin d) :
    semi Q φ v i = ∑ k, Q i k * φ (v k) := rfl

theorem semi_iterate {EE : Type} [CommRing EE] (j : EE →+* R) (φ : R →+* R)
    (hφ : ∀ e, ∃ e', φ (j e) = j e') {d : ℕ} (Pm : Matrix (Fin d) (Fin d) EE) (n : ℕ) :
    ∃ q : Fin d → Fin d → EE, ∀ v i,
      (semi (fun i k => j (Pm i k)) φ)^[n] v i = ∑ k, j (q i k) * φ^[n] (v k) := by
  classical
  choose ψ hψ using hφ
  induction n with
  | zero =>
    refine ⟨fun i k => if i = k then 1 else 0, fun v i => ?_⟩
    simp [apply_ite j]
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨fun i l => ∑ k, Pm i k * ψ (q k l), fun v i => ?_⟩
    rw [Function.iterate_succ_apply', semi_apply]

    simp only [hq, map_sum, map_mul, hψ, Function.iterate_succ_apply', Finset.mul_sum,
    Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]

theorem iterate_persist {EE : Type} [CommRing EE] (j : EE →+* R) (φ : R →+* R)
    (hφ : ∀ e, ∃ e', φ (j e) = j e') {n n' : ℕ} (h : n ≤ n') {y : R}
    (hy : ∃ e r, φ^[n] y = j e + (p : R) * r) : ∃ e r, φ^[n'] y = j e + (p : R) * r := by
  induction h with
  | refl => exact hy
  | step _ ih =>
    obtain ⟨e, r, h⟩ := ih
    obtain ⟨e', he'⟩ := hφ e
    refine ⟨e', φ r, ?_⟩
    rw [Function.iterate_succ_apply', h, map_add (f := _), map_mul, map_natCast, he']

theorem matrix_frob_sub_one_bijective :
    ∀ (R EE A : Type) [CommRing R] [CommRing EE] [CommRing A] (j : EE →+* R) (ι : A →+* R) (φ : R →+* R) (S : Subring R) (p : ℕ) (t : R) (τ : A), ι τ = t → (∀ e, j e ∈ S) → (∀ x ∈ S, φ x ∈ S) → (∀ e, ∃ e', φ (j e) = j e') → (∀ a, ∃ a', φ (ι a) = ι a') → Near ι p t 2 (φ t) → (∀ e, ∃ c : ℕ, Near ι p t 0 (t ^ c * j e)) → (∀ x, (p : R) * x ∈ S → x ∈ S) → (∀ x e, (p : R) * x = j e → ∃ e', x = j e') → (∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) → (∀ i, Near ι p t (i + k) (f i)) → ∃ s ∈ S, ∀ m, Near ι p t (m + k) (s - ∑ i ∈ Finset.range m, f i)) → (∀ x, (∀ m, ∃ e, Near ι p t m (x - j e)) → ∃ e r, x - j e = (p : R) * r) → (∀ y ∈ S, ∀ m, ∃ (n : ℕ) (y0 : R) (e : EE) (r : R), φ^[n] y0 = j e + (p : R) * r ∧ Near ι p t m (y - y0)) → (∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ s ∈ S, ∀ k, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) → (∀ x, (∀ k : ℕ, ∃ e r, x - j e = (p : R) ^ k * r) → ∃ e, x = j e) → ∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) EE), (∀ y : Fin d → R, (∀ i, y i ∈ S) → ∃ z : Fin d → R, (∀ i, z i ∈ S) ∧ ∀ i, ∃ e, y i - (∑ k, j (Pm i k) * φ (z k) - z i) = j e) ∧ (∀ z : Fin d → R, (∀ i, z i ∈ S) → (∀ i, ∃ e, ∑ k, j (Pm i k) * φ (z k) - z i = j e) → ∀ i, ∃ e, z i = j e) := by
  intro R EE A _ _ _ j ι φ S p t τ hτ hjS hφS hφj hφι hφt hbd hSs hEs hc hcl hnil hpc hEc d Pm
  classical
  obtain ⟨c, hcP⟩ : ∃ c : ℕ, ∀ i k, Near ι p t 0 (t ^ c * j (Pm i k)) := by
    choose cf hcf using hbd
    exact ⟨Finset.univ.sup (fun x : Fin d × Fin d => cf (Pm x.1 x.2)), fun i k =>
      near_bound_mono hτ (Finset.le_sup (f := fun x : Fin d × Fin d => cf (Pm x.1 x.2))
        (Finset.mem_univ (i, k))) (hcf _)⟩
  set Φ := semi (fun i k => j (Pm i k)) φ with hΦ
  have hF : ∀ m, ∀ x ∈ vecs d (nearSub ι p t (m + (c + 1))),
      Φ x ∈ vecs d (nearSub ι p t (m + 1 + (c + 1))) := by
    intro m x hx i
    change Near ι p t _ (∑ k, j (Pm i k) * φ (x k))
    refine Near.sum _ fun k _ => near_mul_of_bound (hcP i k) ?_
    exact (near_frob φ hφι hφt (hx k)).mono hτ (by omega)
  have hFa : ∀ m, vecs d (nearSub ι p t (m + 1 + (c + 1))) ≤
      vecs d (nearSub ι p t (m + (c + 1))) :=
    fun m x hx i => Near.mono hτ (by omega) (hx i)
  have key := sub_one_bijective_quotient_of_topNilpotent (Fin d → R) p Φ
    (vecs d S.toAddSubgroup) (vecs d j.range.toAddSubgroup)
    (fun m => vecs d (nearSub ι p t (m + (c + 1))))
    (fun x hx i => by obtain ⟨e, he⟩ := hx i; exact he ▸ hjS e)
    (fun x hx i => show ∑ k, j (Pm i k) * φ (x k) ∈ S from S.sum_mem fun k _ => S.mul_mem (hjS _) (hφS _ (hx k)))
    (fun x hx i => show ∑ k, j (Pm i k) * φ (x k) ∈ j.range from
      j.range.sum_mem fun k _ => j.range.mul_mem ⟨_, rfl⟩ (by
      obtain ⟨e, he⟩ := hx k
      obtain ⟨e', he'⟩ := hφj e
      exact ⟨e', by rw [← he', he]⟩))
    hF hFa
    (fun x hx i => hSs _ (by simpa using hx i))
    (fun x hx i => by
      obtain ⟨e, he⟩ := hx i
      obtain ⟨e', he'⟩ := hEs (x i) e (by simpa using he.symm)
      exact ⟨e', he'.symm⟩)
    (fun f hf hf' => by
      choose s hs hs' using fun i => hc (c + 1) (fun n => f n i) (fun n => hf n i)
        (fun n => hf' n i)
      refine ⟨s, hs, fun m i => ?_⟩
      have := hs' i m
      rw [Pi.sub_apply, Finset.sum_apply]
      exact this)
    (fun x hx => by
      choose e r h using fun i => hcl (x i) (fun m => by
        obtain ⟨w, hw, hw'⟩ := hx m
        obtain ⟨e, he⟩ := hw i
        exact ⟨e, he ▸ Near.mono hτ (Nat.le_add_right _ _) (hw' i)⟩)
      refine ⟨fun i => j (e i), fun i => ⟨_, rfl⟩, r, ?_⟩
      ext i
      simpa using h i)
    (fun y hy => by
      choose n y0 e r h1 h2 using fun i => hnil (y i) (hy i) (c + 1)
      obtain ⟨q, hq⟩ := semi_iterate j φ hφj Pm (Finset.univ.sup n)
      choose e' r' h' using fun i => iterate_persist (p := p) j φ hφj
        (Finset.le_sup (f := n) (Finset.mem_univ i)) ⟨e i, r i, h1 i⟩
      have it : ∀ N : ℕ, Φ^[N] y - Φ^[N] y0 ∈ vecs d (nearSub ι p t (0 + (c + 1))) := by
        intro N
        induction N with
        | zero => intro i; rw [Nat.zero_add]; exact h2 i
        | succ N ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_sub]
          exact hFa 0 (hF 0 _ ih)
      refine ⟨Finset.univ.sup n, fun i => j (∑ k, q i k * e' k), fun i => ⟨_, rfl⟩, fun i => ?_⟩
      have h3 : Near ι p t (0 + (c + 1)) _ := it (Finset.univ.sup n) i
      have h4 := h3.add (Near.of_mul _ (∑ k, j (q i k) * r' k))
      change Near ι p t (0 + (c + 1)) _
      convert h4 using 1
      simp only [Pi.sub_apply]
      rw [hq y0 i]

      simp only [h', mul_add, Finset.sum_add_distrib, map_sum, map_mul, Finset.mul_sum,
      mul_left_comm (p : R)]
      ring)
    (fun x hx => by
      choose s hs hs' using fun i => hpc (fun n => x n i) (fun n => hx n i)
      refine ⟨s, hs, fun k => ?_⟩
      choose r hr using fun i => hs' i k
      refine ⟨r, ?_⟩
      ext i
      simpa [Finset.sum_apply] using hr i)
    (fun x hx i => by
      obtain ⟨e, he⟩ := hEc (x i) (fun k => by
        obtain ⟨w, hw, r, hr⟩ := hx k
        obtain ⟨e, he⟩ := hw i
        refine ⟨e, r i, ?_⟩
        rw [he]
        simpa using congrFun hr i)
      exact ⟨e, he.symm⟩)
  refine ⟨fun y hy => ?_, fun z hz h i => ?_⟩
  · obtain ⟨z, hz, h⟩ := key.1 y hy
    refine ⟨z, hz, fun i => ?_⟩
    obtain ⟨e, he⟩ := h i
    exact ⟨e, he.symm⟩
  · obtain ⟨e, he⟩ := key.2 z hz (fun i => by
      obtain ⟨e, he⟩ := h i
      exact ⟨e, he.symm⟩) i
    exact ⟨e, he.symm⟩

end GlobalTheory.DecomplMat
end

section

noncomputable section

namespace GlobalTheory.ExpImage.EpsSolve

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem εroot_pow_eq (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ m ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply',
      frobeniusEquiv_symm_pow_p]
    exact ih

theorem epsT_pow (s : ℕ) : epsT AI s ^ (l ^ s) = 1 + AI.μ := by
  rw [epsT, ← map_pow, εroot_pow_eq, LocAinf.μ]
  ring

theorem epsT_zero : epsT AI 0 = 1 + AI.μ := by simpa using epsT_pow AI 0

theorem μ_not_unit : ¬ IsUnit AI.μ := by
  obtain ⟨θ, -, -, -, h, -⟩ := GlobalTheory.Cyc.exists_isTheta l P AI
  intro hu
  have h0 : θ AI.μ = 0 := (h _).mpr ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩
  have := hu.map θ
  rw [h0] at this
  exact not_isUnit_zero this

theorem actW_epsT (g : GQ l) (u : ℕ) (hu : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) (j : ℕ) :
    AI.actW g (epsT AI j) = epsT AI j ^ u := by
  rw [epsT, LocAinf.actW, WittVector.map_teichmuller, ← map_pow,
    ← GlobalTheory.ExpImage.actT_εroot_eq_pow l P AI g u hu j]
  rfl

theorem actW_μ (g : GQ l) (u : ℕ) (hu : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) :
    AI.actW g AI.μ = (1 + AI.μ) ^ u - 1 := by
  have h := actW_epsT AI g u hu 0
  rw [epsT_zero, map_add (f := _), map_one] at h
  linear_combination h

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ),
    Lev l s → ∀ g : GQ l, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ U : ℤ_[l],
    (l : ℤ_[l]) ^ s ∣ U - 1 → ∀ m : ℕ, ¬ l ∣ m → Solv AI K s g U (epsT AI s ^ m) := by
  intro l _ P AI K s hs g hg U hU m hm
  have hc := (GlobalTheory.Per.AinfComplete.main l AI.μ (μ_not_unit AI)).2
  obtain ⟨⟨ev, hev⟩, huniq⟩ := GlobalTheory.PowerSeriesAdicEval.exists_eval_and_unique ℤ_[l] (Ainf l) AI.μ hc
  obtain ⟨v, hv⟩ : (PowerSeries.X : PowerSeries ℤ_[l]) ∣ (1 + PowerSeries.X) ^ (1 + l ^ s) - 1 := by
    have := sub_dvd_pow_sub_pow (1 + PowerSeries.X : PowerSeries ℤ_[l]) 1 (1 + l ^ s)
    simpa using this
  have hsub : PowerSeries.HasSubst (PowerSeries.X * v : PowerSeries ℤ_[l]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  let γ : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] PowerSeries ℤ_[l] := PowerSeries.substAlgHom hsub
  have hγ : γ PowerSeries.X = PowerSeries.X * v := PowerSeries.substAlgHom_X hsub
  have hgμ : AI.actW g AI.μ = AI.μ * ev v := by
    have := congrArg ev hv
    simp only [map_sub, map_pow, map_add (f := _), map_one, map_mul, hev] at this
    rw [actW_μ AI g _ hg, this]
  have hgev : ∀ f, AI.actW g (ev f) = ev (γ f) := by
    have := huniq (((AI.actWHom g : Ainf l ≃ₐ[ℤ_[l]] Ainf l) : Ainf l →ₐ[ℤ_[l]] Ainf l).comp ev)
      (ev.comp γ) (by
        change AI.actW g (ev PowerSeries.X) = ev (γ PowerSeries.X)
        rw [hγ, map_mul, hev, hgμ]) (by
        change AI.μ ∣ AI.actW g (ev PowerSeries.X)
        rw [hev, hgμ]
        exact dvd_mul_right _ _)
    intro f
    exact DFunLike.congr_fun this f
  have hχ : ∀ h ∈ Hinf K, (P.χQ h : ℚ_[l]) = ((1 : ℕ) : ℚ_[l]) := by
    intro h hh
    have := ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K h (Hinf_le_fix hh)).2.mp hh
    rw [this]
    simp
  have hhev : ∀ h ∈ Hinf K, ∀ f, AI.actW h (ev f) = ev f := by
    intro h hh
    have hμ : AI.actW h AI.μ = AI.μ := by
      rw [actW_μ AI h 1 (hχ h hh)]
      ring
    have := huniq (((AI.actWHom h : Ainf l ≃ₐ[ℤ_[l]] Ainf l) : Ainf l →ₐ[ℤ_[l]] Ainf l).comp ev)
      ev (by
        change AI.actW h (ev PowerSeries.X) = ev PowerSeries.X
        rw [hev, hμ]) (by
        change AI.μ ∣ AI.actW h (ev PowerSeries.X)
        rw [hev, hμ])
    intro f
    exact DFunLike.congr_fun this f
  have hgE : AI.actW g (epsT AI s) = epsT AI s * (1 + AI.μ) := by
    rw [actW_epsT AI g _ hg, pow_add, pow_one, epsT_pow]
  choose pp FF hpF using GlobalTheory.ExpImage.solve_mod_pow l s hs m hm U hU γ v hv.symm hγ
  let F : ℕ → PowerSeries ℤ_[l] := fun k => Nat.rec 1 (fun k f => FF (k + 1) f) k
  have hF : ∀ k, F (k + 1) = FF (k + 1) (F k) := fun _ => rfl
  refine ⟨fun k => epsT AI s ^ m * ev (pp (k + 1) (F k)), fun k => epsT AI s ^ m * ev (F k), ?_,
    fun k h hh => ?_, fun k => ?_⟩
  · change epsT AI s ^ m * ev 1 = _
    rw [map_one, mul_one]
  · rw [map_mul, map_pow, actW_epsT AI h 1 (hχ h hh), pow_one, hhev h hh]
  · have h1 := congrArg ev (hpF (k + 1) (F k))
    have hC : ev (PowerSeries.C U) = algebraMap ℤ_[l] (Ainf l) U := ev.commutes U
    simp only [map_sub, map_pow, map_add (f := _), map_one, map_mul, hev, hC, map_natCast] at h1
    unfold Step
    beta_reduce
    rw [hF, map_mul, map_pow, hgE, hgev, hgμ, mul_pow, mul_pow]
    linear_combination (epsT AI s ^ m * AI.μ ^ (k + 1)) * h1

end GlobalTheory.ExpImage.EpsSolve
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.quotientAverage_map_lattice_equiv : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (G' : Type) [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [SecondCountableTopology G'] [T2Space G'] (Γ : AddSubgroup G) (Γ' : AddSubgroup G'), IsCoLat Γ → IsCoLat Γ' → ∀ e : G ≃ₜ+ G', (∀ x, e x ∈ Γ' ↔ x ∈ Γ) → ∀ Φ : G' → ℂ, Per Γ' Φ → avg Γ (fun x => Φ (e x)) = avg Γ' Φ := by
  first | exact @GlobalTheory.CuspGeneric.avg_equiv | exact GlobalTheory.CuspGeneric.avg_equiv | (intros; apply GlobalTheory.CuspGeneric.avg_equiv <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeGal

def conjGal {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) :
    (Ω' ≃ₐ[E'] Ω') →* (Ω ≃ₐ[E] Ω) where
  toFun τ :=
    { toRingEquiv := (φ.trans τ.toRingEquiv).trans φ.symm
      commutes' := fun x => by
        show φ.symm (τ (φ (algebraMap E Ω x))) = algebraMap E Ω x
        rw [hφ, AlgEquiv.commutes, ← hφ, RingEquiv.symm_apply_apply] }
  map_one' := by
    ext z
    show φ.symm (φ z) = z
    exact φ.symm_apply_apply z
  map_mul' τ τ' := by
    ext z
    show φ.symm ((τ * τ') (φ z)) = φ.symm (τ (φ (φ.symm (τ' (φ z)))))
    rw [RingEquiv.apply_symm_apply]
    rfl

theorem conjGal_apply {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x))
    (τ : Ω' ≃ₐ[E'] Ω') (z : Ω) : conjGal φ j hφ τ z = φ.symm (τ (φ z)) := rfl

theorem exists_abHom_of_ringEquiv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) →
    ∃ ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω, Continuous ρ ∧
      ∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) →
        ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E Ω _ _ _ _ _ E' Ω' _ _ _ _ _ φ j hφ
  haveI : Algebra.IsIntegral E' Ω' := (IsAlgClosure.isAlgebraic (R := E') (K := Ω')).isIntegral
  haveI : IsClosed ((commutator (Formalism.ConjugateSelfDual.G E Ω)).topologicalClosure : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  let c := conjGal φ j hφ
  have hc : Continuous c :=
    continuous_galHom_of_fix c fun y => ⟨φ y, fun τ hτ => by
      rw [conjGal_apply, hτ, RingEquiv.symm_apply_apply]⟩
  let r : Formalism.ConjugateSelfDual.G E' Ω' →* Gab E Ω := (toAb E Ω).comp c
  have hr : Continuous r := QuotientGroup.continuous_mk.comp hc
  refine ⟨liftAb r hr, continuous_liftAb r hr, fun τ σ h => ?_⟩
  rw [liftAb_toAb]
  show toAb E Ω (c τ) = toAb E Ω σ
  congr 1
  ext z
  rw [conjGal_apply, ← h, RingEquiv.symm_apply_apply]

end GlobalTheory.HeckeGal
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PurityInvariants

theorem isRoot_of_eigen {R K : Type} [CommRing R] [Field K] (f : R →+* K) (ι : K →+* ℂ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (c : K) (x : Fin n → K) (hx : x ≠ 0)
    (h : (M.map f).mulVec x = c • x) : (M.charpoly.map (ι.comp f)).IsRoot (ι c) := by
  classical
  have hdet : (Matrix.scalar (Fin n) c - M.map f).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨x, hx, ?_⟩
    rw [Matrix.sub_mulVec, h]
    ext j
    simp [Matrix.scalar_apply]
  have hroot : ((M.map f).charpoly).eval c = 0 := by
    rw [Matrix.eval_charpoly]
    exact hdet
  unfold Polynomial.IsRoot
  rw [← Polynomial.map_map, ← Matrix.charpoly_map, Polynomial.eval_map, Polynomial.eval₂_hom,
    hroot, map_zero]

theorem eigen_of_dual {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (hM : IsUnit M.det) (c : R) (x : Fin n → K)
    (h : ((c • M⁻¹.transpose).map f).mulVec x = x) : (M.transpose.map f).mulVec x = f c • x := by
  have key : M.transpose * (c • M⁻¹.transpose) = c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hM, Matrix.transpose_one]
  calc (M.transpose.map f).mulVec x
      = (M.transpose.map f).mulVec (((c • M⁻¹.transpose).map f).mulVec x) := by rw [h]
    _ = ((M.transpose * (c • M⁻¹.transpose)).map f).mulVec x := by
        rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    _ = f c • x := by
        rw [key]
        ext j
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite f, ite_mul, Finset.sum_ite_eq]

theorem one_lt_norm {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    (1 : ℝ) < ((normV v : ℕ) : ℝ) := by
  have h1 : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have : 1 < normV v := by omega
  exact_mod_cast this

end GlobalTheory.PurityInvariants
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_gauss_norm_extension_acris : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), (l : ℝ)⁻¹ ≤ r → r < 1 → ∃ N : Per.Acris l → ℝ, (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ (∀ x y, N (x * y) = N x * N y) ∧ ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := by
  first | exact @GlobalTheory.GaussExt.exists_gauss_acris | exact GlobalTheory.GaussExt.exists_gauss_acris | (intros; apply GlobalTheory.GaussExt.exists_gauss_acris <;> assumption)
end
