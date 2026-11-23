module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle072
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle073
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle074
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle075
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle076
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MoveCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions
open GlobalTheory.IndefiniteRowSideFullHecke

section Clauses

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mulLat_le_divLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (cA cB : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat cB M ≤ divLat cA M := by
  rintro _ ⟨z, hz, rfl⟩
  exact M.smul_mem _ (M.smul_mem _ hz)


open Classical in
theorem inRange_indicator (K : Type) [Field K] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) :
    MovementLaw.InRangeOf S cA cB N N' (fun x => if x ∈ divLat cA (homAt S N N') then (1 : K) else 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_contra h
    exact hx (if_neg h)
  · have hy' := mulLat_le_divLat cA cB _ hy
    have : x + y ∈ divLat cA (homAt S N N') ↔ x ∈ divLat cA (homAt S N N') := Submodule.add_mem_iff_left _ hy'
    simp only [this]

end Clauses


open Classical in
theorem degAt_eq {X : Fields} {a b : ℕ} (m : DVar X.Tau a b →₀ ℕ) (τ : X.Tau) :
    IndexExponentDegree.degAt m τ = ∑ k ∈ m.support.filter (fun k => k.1 = τ), m k := by
  unfold IndexExponentDegree.degAt
  rw [Finset.sum_filter, Finset.sum_subset (Finset.subset_univ m.support) (by
    intro k _ hk
    simp [Finsupp.notMem_support_iff.1 hk]), Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rw [Fintype.sum_prod_type]
    simp
  · intro σ _ hσ
    simp [hσ]
  · simp

theorem nuW_detShift_nonneg {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    0 ≤ (W.nuW u (i + 1) τ).detShift := by
  have hpos : 0 < R.N i := R.N_pos i
  have hlt : R.N i < R.N R.m := by
    unfold Ranks.N
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hi (Nat.succ_pos R.t)) _
  have hb : Examples₂.blkN R (R.N i) = i := by
    unfold Examples₂.blkN Ranks.N
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (Nat.succ_pos _)]
  have h1 : Examples₂.wtN (W.hc u τ) (R.N i) = -wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := by
    unfold Examples₂.wtN
    rw [dite_eq_right (by unfold Ranks.N; omega), dif_pos (by rw [hb]; exact hi)]
    simp only [hb]
  have h2 := Examples₂.wtN_anti (W.hc u τ) (Nat.sub_le (R.N i) 1) hlt
  have h3 := Examples₂.lamOf_eq (W.hc u τ) i hi.le ⟨R.N i - 1, by omega⟩
  rw [Examples₂.wtQ_eq_wtN] at h3
  have h4 : (W.nuW u (i + 1) τ).detShift =
      (Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ + ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    unfold DomWeight.detShift
    rw [dif_pos (show 0 < R.N (i + 1 - 1) from hpos)]
    simp only [Wts.nuW, shiftW, Wts.lamN, RowPar.eAt, RowPar.of, Nat.add_sub_cancel, hi, dif_pos]
    rfl
  rw [h4]
  have h5 : -(Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ ≤ ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    rw [Int.le_floor]
    push_cast
    rw [h3]
    simp only at h2 ⊢
    linarith
  omega

theorem degNu_eq {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    IndexExponentDegree.degNu (W.lamTrue u i) (nuLast W u i) τ = ∑ k, (W.nuW u (i + 1) τ).w k := by
  have hpos : 0 < R.N i := R.N_pos i
  unfold IndexExponentDegree.degNu nuLast
  rw [Int.toNat_of_nonneg (nuW_detShift_nonneg W u hi τ)]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold DomWeight.detShift
  rw [dif_pos (show 0 < R.N (i + 1 - 1) from hpos), dif_pos hpos]
  show ((W.lamN u i τ).w s + _) - ((W.lamN u i τ).w ⟨R.N i - 1, _⟩ + _) + ((W.lamN u i τ).w ⟨R.N i - 1, _⟩ + _) =
    (W.lamN u i τ).w s + _
  ring

section Jets

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)

def JetsAll (deg : X.Tau → ℤ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  ∀ Ξ : HomE X.E a b → X.K, MovementLaw.InRangeOf S cA cB N N' Ξ → MovementLaw.JetsIn A S cB deg N N' Ξ

theorem jetsIn_iff (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ) (deg : X.Tau → ℤ) (h : ∀ τ, IndexExponentDegree.degNu lam n τ = deg τ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    IndexExponentDegree.JetsIn A S cA cB lam n N N' ↔ JetsAll A S cA cB deg N N' := by
  constructor
  · intro hJ Ξ hΞ x hx m hm
    refine hJ x (hΞ.1 x hx) m fun τ => ?_
    rw [degAt_eq, h τ, ← hm τ]
  · intro hJ x hx m hm
    refine hJ _ (inRange_indicator X.K S cA cB N N') x (by simp [hx]) m fun τ => ?_
    rw [← h τ, ← hm τ, degAt_eq]


open Classical in
def JetsDeg (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ) (deg : X.Tau → ℤ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange S M c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, ((∑ k ∈ m.support.filter (fun k => k.1 = τ), m k : ℕ) : ℤ) = deg τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m

theorem jetsAll_of_deg (deg : X.Tau → ℤ) (h : JetsDeg A a b S (cA * cB) deg) (hB : 0 < cB)
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') :
    JetsAll A S cA cB deg N N' := by
  intro Ξ hΞ x hx m hm
  refine h N N' cB x ⟨hN, hN', hB, Dvd.intro_left _ rfl, ?_⟩ m hm
  have h1 : ((cA : ℕ) : 𝓞 X.E) • x ∈ homAt S N N' := hΞ.1 x hx
  show ((cA * cB : ℕ) : 𝓞 X.E) • x ∈ homAt S N N'
  rw [Nat.cast_mul, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ h1

end Jets

theorem cBof_pos {X : Fields} {Pr : Primes X} (hP : Pr.Ok) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) : 0 < cBof sel mu cst u := by
  unfold cBof
  refine Nat.mul_pos (hP.T_prime u).pos (pow_pos (Finset.prod_pos fun P _ => ?_) _)
  exact Nat.pos_of_ne_zero (by unfold Formalism.L2.Col.qOf; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot)

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (A : Amb X) {i : ℕ} {b : ℕ} (lam' : X.Tau → DomWeight b)

end Step

end GlobalTheory.MoveCompare
end
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.JetDeg

theorem algHom_hom {K σ ρ M N : Type} [CommRing K] [AddCommMonoid M] [AddCommMonoid N] (w : σ → M) (w' : ρ → N)
    (g : M →+ N) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial ρ K)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (g (w v))) {f : MvPolynomial σ K} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) (g d) := by

  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hd : Finsupp.weight w m = d := hf (mem_support_iff.mp hm)

  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod, ← hd, Finsupp.weight_apply,
  Finsupp.sum, map_sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun v _ => ?_
  rw [map_pow, map_nsmul]
  exact (hφ v).pow _

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {a b : ℕ}

def posW (a : ℕ) (τ : ι) : ι × Fin a × Fin a → ℕ := fun v => if v.1 = τ then 1 else 0

def derW (a b : ℕ) (τ : ι) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℕ :=
  Sum.elim (fun _ => 0) fun k => if k.1 = τ then 1 else 0

theorem blockEmb_hom (τ τ' : ι) (ν : Fin a → ℕ) {f : MvPolynomial (Fin a × Fin a) K}
    (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f ν) :
    IsWeightedHomogeneous (posW a τ) (Formalism.GradedWeylDivisibility.blockEmb K τ' f) (if τ' = τ then ∑ i, ν i else 0) := by
  let g : (Fin a → ℕ) →+ ℕ :=
    { toFun := fun x => if τ' = τ then ∑ i, x i else 0
      map_zero' := by simp
      map_add' := by
        intro x y
        split_ifs <;> simp [Finset.sum_add_distrib] }
  refine algHom_hom (Formalism.GradedWeylDivisibility.colW a a) (posW a τ) g _ (fun v => ?_) hf
  have h := isWeightedHomogeneous_X K (posW a τ) (τ', v)
  have e : g (Formalism.GradedWeylDivisibility.colW a a v) = posW a τ (τ', v) := by
    simp [g, Formalism.GradedWeylDivisibility.colW, posW, Pi.single_apply]
  rw [e]
  simpa [Formalism.GradedWeylDivisibility.blockEmb] using h

theorem frDet_hom (τ τ' : ι) :
    IsWeightedHomogeneous (posW a τ) (frDet K a τ') (if τ' = τ then a else 0) := by
  rw [frDet, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have h : IsWeightedHomogeneous (posW a τ) (∏ i : Fin a, (X (τ', σ i, i) : Pol K ι a))
      (∑ _i : Fin a, if τ' = τ then 1 else 0) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X K (posW a τ) (τ', σ i, i)
  have e : (∑ _i : Fin a, if τ' = τ then 1 else 0) = if τ' = τ then a else 0 := by
    split_ifs <;> simp
  rw [e] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · simpa [h1] using h
  · simpa [h1] using h.neg

theorem subD_hom (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (derW a b τ) (subD K ι a b P) d := by
  refine algHom_hom (posW a τ) (derW a b τ) (AddMonoidHom.id ℕ) _ (fun v => ?_) hP
  rw [subD, aeval_X]
  split_ifs with h
  · refine IsWeightedHomogeneous.sum _ _ _ fun β _ => ?_
    have := (isWeightedHomogeneous_X K (derW a b τ) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul
      (isWeightedHomogeneous_X K (derW a b τ) (Sum.inr (v.1, β, v.2.1)))
    simpa [derW, posW] using this
  · exact isWeightedHomogeneous_zero _ _ _

variable [Fintype ι]

theorem VV_hom (lam : ι → DomWeight a) (τ : ι) {P : Pol K ι a} (hP : P ∈ Formalism.L2.DIV.VV K lam) :
    IsWeightedHomogeneous (posW a τ) P (∑ i, (lam τ).natW i) := by
  have : Formalism.L2.DIV.VV K lam ≤ weightedHomogeneousSubmodule K (posW a τ) (∑ i, (lam τ).natW i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => Formalism.GradedWeylDivisibility.blockEmb K τ' (F τ'))
      (fun τ' => if τ' = τ then ∑ i, (lam τ').natW i else 0) (w := posW a τ)
      fun τ' _ => blockEmb_hom τ τ' _ (hF τ').1
    simpa using h
  exact this hP

theorem sharp_hom (n : ι → ℕ) (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (posW a τ) (sharp n P) (d + n τ * a) := by
  refine hP.mul ?_
  have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => frDet K a τ' ^ n τ')
    (fun τ' => n τ' • if τ' = τ then a else 0) (w := posW a τ)
    fun τ' _ => (frDet_hom τ τ').pow _
  simpa using h

theorem weight_derW (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    Finsupp.weight (derW a b τ) μ = ∑ β : Fin b, ∑ α : Fin a, μ (Sum.inr (τ, β, α)) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type (α₁ := ι) (α₂ := Fin b × Fin a), Finset.sum_eq_single τ]
  · simp [derW, Fintype.sum_prod_type]
  · intro x _ hx
    simp [derW, hx]
  · simp

theorem natW_cast (lam : DomWeight a) (i : Fin a) : (lam.natW i : ℤ) = lam.w i - lam.detShift := by
  have hi := i.2
  have h : lam.detShift ≤ lam.w i := by
    rw [DomWeight.detShift, dite_eq_left (by omega)]
    exact lam.anti (by rw [Fin.le_def]; simp only; omega)
  rw [DomWeight.natW]
  omega

end GlobalTheory.JetDeg


open GlobalTheory.JetDeg in
theorem GlobalTheory.subD_sharp_inDeg : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b) (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n → ∀ P ∈ Formalism.L2.DIV.VV K lam, ∀ μ ∈ (subD K ι a b (sharp n P)).support, InDeg lam s' (Finsupp.comapDomain Sum.inr μ Sum.inr_injective.injOn) := by
  classical
  intro K _ ι _ a b hab lam lam' s s' n hw P hP μ hμ τ
  have h := GlobalTheory.JetDeg.subD_hom (b := b) τ (GlobalTheory.JetDeg.sharp_hom n τ (GlobalTheory.JetDeg.VV_hom lam τ hP)) (mem_support_iff.mp hμ)
  rw [GlobalTheory.JetDeg.weight_derW] at h
  simp only [Finsupp.comapDomain_apply]
  rw [h]
  push_cast
  have e : ∀ i, (lam τ).w i + s' τ = ((lam τ).natW i : ℤ) + n τ := fun i => by
    rw [GlobalTheory.JetDeg.natW_cast, hw.2.2 τ]; ring
  simp [e, Finset.sum_add_distrib, mul_comm]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem log_le_of_le_two_mul_pow_eight {x a y k g : ℝ} (hx : 1 < x) (ha : a ≤ 5) (hy : 0 ≤ y) (hk0 : 0 < k)
    (hk : k ≤ 2 * x ^ a) (hg0 : 0 < g) (hg : g ≤ 2 * (k * Real.exp y) ^ 8) :
    Real.log g ≤ 40 * Real.log x + 9 * y + 9 := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h1 : Real.log k ≤ Real.log 2 + a * Real.log x := by
    have := Real.log_le_log hk0 hk
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 a).ne', Real.log_rpow hx0] at this
  have h2 : Real.log g ≤ Real.log 2 + 8 * (Real.log k + y) := by
    have := Real.log_le_log hg0 hg
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_mul hk0.ne' (Real.exp_pos y).ne', Real.log_exp, Nat.cast_ofNat] at this
  have h3 : a * Real.log x ≤ 5 * Real.log x := mul_le_mul_of_nonneg_right ha hlx.le
  linarith

theorem szRow_sizeG : SzRow (fun _ _ L => SizeG L) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow eps (eps + eps / 100) 40 9 1 0 he.le
    (by linarith) one_pos
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨x0, ?_⟩⟩⟩
  intro D L hLe hx hV i j
  obtain ⟨-, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  obtain ⟨-, -, -, -, hg, -⟩ := hV.host
  have hx1 := L.sc.one_lt_alt
  have hxp : 0 < L.sc.x := by linarith
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk1
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  refine ⟨(hg i).1, (hg i).2.trans (by linarith [(hg j).1]), ?_⟩
  have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le (by positivity) (hg i).1
  have hL0 : 0 ≤ L.sc.L := (Real.rpow_pos_of_pos hxp _).le
  have h1 := log_le_of_le_two_mul_pow_eight hx1 (by rw [hLe]; linarith) hL0 hk0 hk2 hg0 (hg i).2
  have h2 := hx0 L.sc.x hx
  have h3 : L.sc.x ^ szTh L * L.sc.L = L.sc.x ^ (eps + eps / 100) := by
    simp only [szTh, Scale.L, hLe]
    rw [← Real.rpow_add hxp, add_comm]
  rw [h3]
  simp only [Scale.L, hLe] at h1
  rw [pow_zero, mul_one, one_mul] at h2
  exact h1.trans h2

theorem szRow_sizeG_sizeWords : SzRow (fun _ _ L => SizeG L ∧ SizeWords L) :=
  szRow_and_imp.1 _ _ szRow_sizeG szRow_card_words_le

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.explicitRanks_basic_bounds_large_scale : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.f : ℝ) ≤ s.x ^ (3 : ℝ) ∧ (R.m : ℝ) ≤ s.x ∧ (R.r : ℝ) ≤ s.x ^ (5 : ℝ) ∧ R.k ≤ R.r ∧ R.r ≤ 2 * R.k ∧ s.L ≤ s.x ∧ 1 ≤ s.L ∧ s.x ^ ((13 : ℝ) / 2) ≤ (R.f : ℝ) * R.r * s.L ∧ (R.f : ℝ) * R.r * s.L ≤ s.x ^ ((687 : ℝ) / 100) ∧ ((R.f * R.r.choose 2 : ℕ) : ℝ) ≤ s.x ^ (12 : ℝ) ∧ (R.k : ℝ) * R.f / R.m ≤ s.x ^ (7 : ℝ) ∧ ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) ∧ s.x ^ (377 : ℝ) ≤ (R.t : ℝ) ∧ (R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ (R.N R.m : ℝ) ≤ s.x ^ (402 : ℝ) ∧ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
  first | exact @GlobalTheory.EX.rank_basic_bounds | exact GlobalTheory.EX.rank_basic_bounds | (intros; apply GlobalTheory.EX.rank_basic_bounds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem four_polys_le_of_cube_le (d n r y T : ℝ) (hd0 : 0 ≤ d) (hn0 : 0 ≤ n) (_hr0 : 0 ≤ r)
    (hd : d ≤ y) (hn : n ≤ y) (hr : r ≤ y) (hy : 10000 ≤ y) (hT : y ^ 3 ≤ T) :
    (d + 2) * n + 2 * r ≤ T ∧ 40 * (d + 2) ≤ T ∧ 11 * d ^ 2 ≤ T ∧
      r + 2 * (2 * 5 ^ 4 * r) * (d + 1) ≤ T := by
  have hy0 : 0 ≤ y := by linarith
  have h1 : 10000 * y ≤ y * y := mul_le_mul_of_nonneg_right hy hy0
  have h2 : 10000 * (y * y) ≤ T := by
    have : 10000 * (y * y) ≤ y * (y * y) := mul_le_mul_of_nonneg_right hy (mul_nonneg hy0 hy0)
    have e : y * (y * y) = y ^ 3 := by ring
    linarith
  have hdn : d * n ≤ y * y := mul_le_mul hd hn hn0 hy0
  have hdd : d * d ≤ y * y := mul_le_mul hd hd hd0 hy0
  have hrd : r * d ≤ y * y := mul_le_mul hr hd hd0 hy0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem szRow_rank_polys_le_TO :
    SzRow (fun C D L => (((D.R.f * D.R.r.choose 2 : ℕ) + 2) * (nWv D.R L.sc : ℕ) + 2 * D.R.r ≤ (TOv L.sc : ℕ)) ∧ (40 * ((D.R.f * D.R.r.choose 2 : ℕ) + 2) ≤ (TOv L.sc : ℕ)) ∧ (11 * (D.R.f * D.R.r.choose 2 : ℕ) ^ 2 ≤ (TOv L.sc : ℕ)) ∧ (D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * ((D.R.f * D.R.r.choose 2 : ℕ) + 1) ≤ (TOv L.sc : ℕ))) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x0 10000, fun D L heps hx hV => ?_⟩⟩⟩
  obtain ⟨-, -, hr, -, -, -, -, -, -, hD, -, hnW, -⟩ :=
    hx0 L.sc D.R heps (le_trans (le_max_left _ _) hx) hV.ranks
  have hx1 : (10000 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx2 : (1 : ℝ) ≤ L.sc.x := by linarith
  have mono : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hx2 h
  have hy : (10000 : ℝ) ≤ L.sc.x ^ (23 : ℝ) := by
    have := mono 1 23 (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hT : (L.sc.x ^ (23 : ℝ)) ^ 3 ≤ (TOv L.sc : ℝ) := by
    have e : (L.sc.x ^ (23 : ℝ)) ^ 3 = L.sc.x ^ (69 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    rw [e]
    exact le_trans (mono 69 377 (by norm_num)) (Nat.le_ceil _)
  obtain ⟨h1, h2, h3, h4⟩ := four_polys_le_of_cube_le
    ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) (nWv D.R L.sc : ℝ) (D.R.r : ℝ) (L.sc.x ^ (23 : ℝ)) (TOv L.sc : ℝ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (hD.trans (mono _ _ (by norm_num))) (hnW.trans (mono _ _ (by norm_num)))
    (hr.trans (mono _ _ (by norm_num))) hy hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.explicitChoice_polynomial_le_baseSize : SzRow (fun C D L => (((TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ (C.T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * zBase L ^ C.T.eP) ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 ≤ L.sc.b)) := by
  first | exact @GlobalTheory.EX.szRow_poly_le_b | exact GlobalTheory.EX.szRow_poly_le_b | (intros; apply GlobalTheory.EX.szRow_poly_le_b <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_sizeN_sizeM_sizeK_sizeT_sizeTT_sizeDe2_sizeLw : SzRow (fun _ _ L => SizeN L ∧ SizeM L ∧ SizeK L ∧ SizeT L ∧ SizeTT L ∧ SizeDe2 L ∧ SizeLw L) := by
  first | exact @GlobalTheory.EX.szRow_rankSizes | exact GlobalTheory.EX.szRow_rankSizes | (intros; apply GlobalTheory.EX.szRow_rankSizes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_sizeLa_sizeRho_sizeBot : SzRow (fun _ _ L => SizeLa L ∧ SizeRho L ∧ SizeBot L) := by
  first | exact @GlobalTheory.EX.szRow_la_rho_bot | exact GlobalTheory.EX.szRow_la_rho_bot | (intros; apply GlobalTheory.EX.szRow_la_rho_bot <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_card_TT_le_Nstar_and_rhoP_le_and_bT_le : SzRow (fun C D L => ((D.host.TT.card : ℝ) ≤ Nstar L) ∧ (rhoP L C.P.Crho ≤ L.sc.x ^ (-2 : ℝ)) ∧ (∀ t, (L.bT t : ℝ) ≤ L.sc.b' + Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k)) := by
  first | exact @GlobalTheory.EX.szRow_tops_band_bottoms | exact GlobalTheory.EX.szRow_tops_band_bottoms | (intros; apply GlobalTheory.EX.szRow_tops_band_bottoms <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_TOv_mul_PP_le_b_and_sqrt_b : SzRow (fun C D L => (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ))) := by
  first | exact @GlobalTheory.EX.szRow_TO_PP_le_b | exact GlobalTheory.EX.szRow_TO_PP_le_b | (intros; apply GlobalTheory.EX.szRow_TO_PP_le_b <;> assumption)
end
