module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.ColonInt

theorem mem_int_of_pow {E : Type} [Field E] [NumberField E] (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (c y : Q.adicCompletion E) (hc : c ≠ 0) (h : ∀ n : ℕ, c * y ^ n ∈ Q.adicCompletionIntegers E) :
    y ∈ Q.adicCompletionIntegers E := by
  have h' : ∀ n : ℕ, Valued.v (c * y ^ n) ≤ 1 := fun n =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := Q)).1 (h n)
  refine (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := Q)).2 ?_
  by_contra hy
  push_neg at hy
  have hc' : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hy0 : Valued.v y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 hc'
  obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.1 hy0
  have hb1 : (1 : Multiplicative ℤ) < b := by
    rw [← hb] at hy
    exact WithZero.coe_lt_coe.1 hy
  have h2 := h' (Int.natAbs (Multiplicative.toAdd a) + 1)
  rw [Valuation.map_mul, Valuation.map_pow, ← ha, ← hb, ← WithZero.coe_pow, ← WithZero.coe_mul] at h2
  have h3 : a * b ^ (Int.natAbs (Multiplicative.toAdd a) + 1) ≤ 1 := WithZero.coe_le_coe.1 h2
  have h4 : Multiplicative.toAdd a + (Int.natAbs (Multiplicative.toAdd a) + 1 : ℕ) * Multiplicative.toAdd b ≤ 0 := by
    have := Multiplicative.toAdd_le.2 h3
    simpa [toAdd_mul, toAdd_pow] using this
  have h5' : 0 < Multiplicative.toAdd b := by
    have := Multiplicative.toAdd_lt.2 hb1
    simpa using this
  have h5 : 1 ≤ Multiplicative.toAdd b := by omega
  push_cast at h4
  have h6 : (0:ℤ) ≤ |Multiplicative.toAdd a| := abs_nonneg _
  have h7 : -Multiplicative.toAdd a ≤ |Multiplicative.toAdd a| := neg_le_abs _
  nlinarith

variable {D : D7}

def evQ {E : Type} [Field E] [NumberField E] (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E where
  toFun x := x Q
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem herm_cols {S : HSp D} {ρ : ℕ} (A B : Mx D S.rank ρ) (κ a : AE D) (l l' : Fin ρ) :
    GlobalTheory.IwaPlace.hermAt S (fun j => a * A j l) (fun i => κ * B i l') = cA D κ * a * (adj B * (gA S * A)) l' l := by
  simp only [GlobalTheory.IwaPlace.hermAt, Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mul_incA_mem {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) (o : 𝓞 D.host.E) :
    a * incA D (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
  rw [map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 (AddSubgroup.subset_closure ⟨1, fun w => ?_, o, ?_⟩)
  · rw [map_one]; exact one_mem _
  · rfl

theorem exists_den {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι κ D.host.E) :
    ∃ t : 𝓞 D.host.E, t ≠ 0 ∧ ∀ k l, ∃ o : 𝓞 D.host.E, (t : D.host.E) * M k l = o := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E))
    (Finset.univ : Finset (ι × κ)) (fun p => M p.1 p.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun k l => ?_⟩
  obtain ⟨o, ho⟩ := hb (k, l) (Finset.mem_univ _)
  refine ⟨o, ?_⟩
  rw [show ((o : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E o from rfl, ho, Algebra.smul_def]

theorem colon_int : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (x : AE D), x - 1 ∈ idAt D (· = v) → (∀ r ∈ idAt D (· = v), (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → ∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * x * a) ∈ latV S L (· = v)) → x - 1 ∈ intAt D (· = v) := by
  intro D S S₀ ρ d L L₀ v _ hL _ i j x hx hK
  obtain ⟨hsupp, ⟨m, hm, hmul⟩, hchar⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL
  obtain ⟨ε, hcε, hε, hεa⟩ := GlobalTheory.IwaPlace.LocSD.exists_idem (D := D) v
  have hεε : ε * ε = ε := hεa ε hε.1
  obtain ⟨t, ht0, ht⟩ := exists_den (Matrix.fromCols d.e d.e')
  set T : AE D := incA D (t : D.host.E) with hT
  have hX : ∀ κ : AE D, κ ∈ intAt D (· = v) → ∀ l k, κ * (T * d.jX k l) ∈ intAt D (· = v) := by
    intro κ hκ l k
    obtain ⟨o, ho⟩ := ht k (Sum.inl l)
    have e : T * d.jX k l = incA D (o : D.host.E) := by
      rw [← ho, Matrix.fromCols_apply_inl, map_mul]; rfl
    rw [e]; exact mul_incA_mem hκ o
  have hY : ∀ κ : AE D, κ ∈ intAt D (· = v) → ∀ l k, κ * (T * d.jY k l) ∈ intAt D (· = v) := by
    intro κ hκ l k
    obtain ⟨o, ho⟩ := ht k (Sum.inr l)
    have e : T * d.jY k l = incA D (o : D.host.E) := by
      rw [← ho, Matrix.fromCols_apply_inr, map_mul]; rfl
    rw [e]; exact mul_incA_mem hκ o
  have hU : ∀ l (a : AE D), colMul d.jX l a ∈ latV S L (· = v) →
      ((m : AE D) * ε * cA D T) * a ∈ intAt D (· = v) := by
    intro l a ha
    have hxΛ : (fun k => ((m : AE D) * (ε * T)) * d.jY k l) ∈ latV S L (· = v) := by
      have := hmul (fun k => ε * (T * d.jY k l)) (fun k => hY ε hε l k)
      convert this using 1
      funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
    have h1 := ((hchar _ (hsupp _ ha)).1 ha) _ hxΛ
    rw [show colMul d.jX l a = fun j => a * d.jX j l from rfl, herm_cols, d.gram_YX, Matrix.one_apply_eq,
      mul_one] at h1
    convert h1 using 1
    rw [map_mul, map_mul, map_natCast, hcε]; ring
  obtain ⟨β, hβ⟩ : ∃ β : AE D, β = (m : AE D) * ε * cA D T := ⟨_, rfl⟩
  rw [← hβ] at hU
  have hβI : β ∈ idAt D (· = v) := by
    rw [hβ]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hε.1)
  have hc0 : colMul d.jX j ((m : AE D) * (ε * T)) ∈ latV S L (· = v) := by
    have := hmul (fun k => ε * (T * d.jX k j)) (fun k => hX ε hε j k)
    convert this using 1
    funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul]; ring
  obtain ⟨c, hc⟩ : ∃ c : AE D, c = (m : AE D) * (T * β) := ⟨_, rfl⟩
  have hcK : ∀ a, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (c * a) ∈ latV S L (· = v) := by
    intro a ha
    have := hmul (fun k => (β * a) * (T * d.jX k i)) (fun k => hX _ (hU j a ha) i k)
    convert this using 1
    funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul, hc]; ring
  have hcI : c ∈ idAt D (· = v) := by
    rw [hc]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hβI)
  have hit : ∀ n : ℕ, c * x ^ n ∈ idAt D (· = v) ∧ ∀ a, colMul d.jX j a ∈ latV S L (· = v) →
      colMul d.jX i (c * x ^ n * a) ∈ latV S L (· = v) := by
    intro n
    refine ⟨Ideal.mul_mem_right _ _ hcI, ?_⟩
    induction n with
    | zero => rw [pow_zero, mul_one]; exact hcK
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact hK _ (Ideal.mul_mem_right _ _ hcI) ih
  have hbd : ∀ n : ℕ, β * (c * x ^ n * ((m : AE D) * (ε * T))) ∈ intAt D (· = v) := fun n =>
    hU i _ ((hit n).2 _ hc0)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  refine ⟨hx, (hΦ.int _).2 fun Q => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AE D →+* Q.adicCompletion D.host.E, ∀ z, ψ z = Φ z Q :=
    ⟨(evQ Q).comp Φ, fun _ => rfl⟩
  have hψinc : ∀ e : D.host.E, ψ (incA D e) = algebraMap D.host.E _ e := fun e => by
    rw [hψ, hΦ.inc]; rfl
  have hεQ : ψ ε = 0 ∨ ψ ε = 1 := by
    have h := congrArg ψ hεε
    rw [map_mul] at h
    rcases mul_eq_zero.1 (show ψ ε * (ψ ε - 1) = 0 by rw [mul_sub, h, mul_one, sub_self]) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.1 h1)
  rw [← hψ]
  rcases hεQ with h0 | h1
  · rw [← hεa _ hx, map_mul, h0, zero_mul]; exact zero_mem _
  · rw [map_sub, map_one]
    refine sub_mem ?_ (one_mem _)
    have ht' : (t : D.host.E) ≠ 0 := by exact_mod_cast ht0
    have hκ : (m : D.host.E) ^ 4 * star (t : D.host.E) ^ 2 * (t : D.host.E) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hm.ne')) (pow_ne_zero _ (star_ne_zero.2 ht')))
        (pow_ne_zero _ ht')
    refine mem_int_of_pow Q _ (ψ x) ((map_ne_zero (algebraMap D.host.E _)).2 hκ) fun n => ?_
    have h := (hΦ.int _).1 (hbd n).2 Q
    rw [← hψ] at h
    have e1 : ψ T = algebraMap D.host.E _ (t : D.host.E) := hψinc _
    have e2 : ψ (cA D T) = algebraMap D.host.E _ (star (t : D.host.E)) := hψinc _
    rw [hc, hβ] at h
    simp only [RingHom.map_mul, RingHom.map_pow, map_natCast, h1] at h ⊢
    rw [← e1, ← e2]
    convert h using 1
    ring

end GlobalTheory.ColonInt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RealData

theorem isKC_comm_Jpq {p q : ℕ} {b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hb : IsKC b) :
    b * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * b := by
  ext a c
  rcases a with i | i <;> rcases c with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
  · rw [hb (Sum.inl i) (Sum.inr j) (by simp [sameBlock]), neg_zero]
  · rw [hb (Sum.inr i) (Sum.inl j) (by simp [sameBlock]), neg_zero]

theorem conj_mem_Kset {n p q : ℕ} (ε : Fin n → Bool) (e : Fin n ≃ Fin p ⊕ Fin q)
    (hJ : (Formalism.UG.Jpq p q).submatrix e e = Formalism.REAL.Jm ε) (fr g : Matrix (Fin n) (Fin n) ℂ) (hfr : IsUnit fr)
    (hg : gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g = frᴴ * Formalism.REAL.Jm ε * fr)
    (b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hb : IsKC b)
    (hbA : b * fr.submatrix e.symm id = fr.submatrix e.symm id * g) :
    fr * g * fr⁻¹ ∈ Formalism.REAL.Kset ε := by
  have hdet : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have hinv : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet

  set X := b.submatrix e e with hX
  have hXfr : X * fr = fr * g := by
    have h1 := congrArg (fun N => N.submatrix e id) hbA
    rw [Matrix.submatrix_mul _ _ _ _ _ e.bijective, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id] at h1
    simpa [Matrix.submatrix_submatrix] using h1
  have hXe : fr * g * fr⁻¹ = X := by
    rw [← hXfr, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hXe]
  have hcomm : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := by
    rw [← hJ, hX, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective,
      isKC_comm_Jpq hb]

  have hiso : Xᴴ * Formalism.REAL.Jm ε * X = Formalism.REAL.Jm ε := by
    have hgX : g = fr⁻¹ * X * fr := by
      rw [Matrix.mul_assoc, hXfr, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have hinvH : (fr⁻¹)ᴴ * frᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
    have key : X = fr * g * fr⁻¹ := hXe.symm
    calc Xᴴ * Formalism.REAL.Jm ε * X
        = (fr⁻¹)ᴴ * (gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g) * fr⁻¹ := by
          rw [key]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (fr⁻¹)ᴴ * frᴴ * Formalism.REAL.Jm ε * (fr * fr⁻¹) := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hinvH, hinv, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, hcomm⟩
  rw [Matrix.mem_unitaryGroup_iff']
  change Xᴴ * X = 1
  calc Xᴴ * X = Xᴴ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * X := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    _ = Xᴴ * Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε := by
        rw [Matrix.mul_assoc (Xᴴ * Formalism.REAL.Jm ε) X, hcomm]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hiso, Formalism.REAL.Jm_mul_self]

theorem conj_mem_Kset_of_mem_Kinf : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (hV : V.SigOK) (k : GA D V), IsInfFam θ → k ∈ GlobalTheory.Cusp.Kinf θ V (GlobalTheory.ChainOnto.RealData.sortedFrame M hV) → ∀ τ, M.fr τ * infMat D.sp.cm.sig V.gram (θ τ) k * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := by
  intro D θ V S M hV k hθ hk τ
  obtain ⟨-, hkτ⟩ := GlobalTheory.Cusp.mem_Kinf.1 hk
  obtain ⟨b, hb, hbA⟩ := hkτ τ
  have hU := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ
  have hU' : (infMat D.sp.cm.sig V.gram (θ τ) k)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) *
      infMat D.sp.cm.sig V.gram (θ τ) k = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by
    rw [M.fr_gram τ]; exact hU
  exact conj_mem_Kset (M.ε τ) (signEquiv (M.ε τ) (card_true M hV τ) (card_false M hV τ))
    (Jpq_submatrix _ _) (M.fr τ) _ (M.fr_unit τ) hU' b hb hbA

end GlobalTheory.ChainOnto.RealData

end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

namespace GlobalTheory.Core.Rk.Dich

theorem exists_leftInv_of_linInd {K : Type} [Field K] {a b : ℕ} (C : Matrix (Fin a) (Fin b) K)
    (hC : LinearIndependent K C.transpose) : ∃ L : Matrix (Fin b) (Fin a) K, L * C = 1 := by
  have hinj : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hC
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot.2 fun x y h => hinj (by simpa [Matrix.toLin'_apply] using h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  calc LinearMap.toMatrix' g * C = LinearMap.toMatrix' g * LinearMap.toMatrix' (Matrix.toLin' C) := by
        rw [LinearMap.toMatrix'_toLin']
    _ = LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' C) := (LinearMap.toMatrix'_comp _ _).symm
    _ = 1 := by rw [hg, LinearMap.toMatrix'_id]

variable {D : D7}



theorem conj_io_gen_mem (V : HSp D) (γ : GA D (dblSp V)) (hγ : γ ∈ GQ (dblSp V))
    (γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E)
    (hγi : (Formalism.L2.Theta.matHom (dblSp V) γ⁻¹).1 = γi.map (incA D)) (r : ℕ)
    (K : Matrix (Fin V.rank) (Fin r) D.host.E) (hK : diagSnd γi * K = 0)
    (hC : IsIsoFrame V (leviMat finSumFinEquiv γi * K)) (g : GA D V)
    (h1 : HMul.hMul ((Formalism.L2.Theta.matHom V g).1 - 1) ((leviMat finSumFinEquiv γi * K).map (incA D)) = 0)
    (h3 : ∀ x : Fin V.rank → D.host.E,
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (leviMat finSumFinEquiv γi * K) * V.gram).mulVec x = 0 →
      ∃ a : Fin r → AE D, ((Formalism.L2.Theta.matHom V g).1 - 1).mulVec (fun i => incA D (x i)) =
        ((leviMat finSumFinEquiv γi * K).map (incA D)).mulVec a) :
    ∃ h : γ * io V (g, 1) * γ⁻¹ ∈ siegel V, aP V ⟨_, h⟩ = 1 := by
  classical
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set J := V.gram with hJ
  have hinjA : Function.Injective (incA D) := by
    haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
    exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective
  obtain ⟨g0, hg0, -, hinv⟩ := exists_rat (dblSp V) hγ
  have hγi' : γi = (g0⁻¹).1 := Matrix.map_injective hinjA (hγi.symm.trans hinv)
  have hu : Formalism.UG.cT σ γi * GlobalTheory.Doubling.dblGram finSumFinEquiv J * γi = GlobalTheory.Doubling.dblGram finSumFinEquiv J := by
    rw [hγi', hJ, ← gram_hdbl V]; exact (Formalism.UG.UJ _ _).inv_mem hg0
  have hiso := isotropic_diag hu
  set P := leviMat finSumFinEquiv γi with hP
  set Q' := diagSnd γi with hQ'
  set C := P * K with hCdef
  have hCJP : Formalism.UG.cT σ C * J * P = 0 := by
    calc Formalism.UG.cT σ C * J * P = Formalism.UG.cT σ K * (Formalism.UG.cT σ P * J * P) := by
          rw [hCdef, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ (Q' * K) * J * Q' := by rw [hiso, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hK]; simp [Formalism.UG.cT]
  have hcol : ∀ i, (Formalism.UG.cT σ C * J).mulVec (fun j => P j i) = 0 := fun i => by
    funext k
    have := congrFun (congrFun hCJP k) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  choose a ha using fun i => h3 _ (hcol i)
  set G := (Formalism.L2.Theta.matHom V g).1 with hG
  set m := G - 1 with hm
  let A : Matrix (Fin r) (Fin V.rank) (AE D) := Matrix.of fun k i => a i k
  have hmP : m * P.map (incA D) = HMul.hMul (C.map (incA D)) A := by
    ext j i
    have := congrFun (ha i) j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, A] using this
  have hCm : C.map (incA D) = HMul.hMul (P.map (incA D)) (K.map (incA D)) := Matrix.map_mul
  obtain ⟨L, hL⟩ := exists_leftInv_of_linInd C hC.2.1
  have hAK : A * K.map (incA D) = 0 := by
    have e1 : C.map (incA D) * (A * K.map (incA D)) = 0 := by
      rw [← Matrix.mul_assoc, ← hmP, Matrix.mul_assoc, ← hCm, h1]
    have e2 : L.map (incA D) * C.map (incA D) = 1 := by
      rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
    calc A * K.map (incA D) = L.map (incA D) * C.map (incA D) * (A * K.map (incA D)) := by
          rw [e2, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]
  set Γ := (Formalism.L2.Theta.matHom (dblSp V) γ).1 with hΓ
  set Γi := (Formalism.L2.Theta.matHom (dblSp V) γ⁻¹).1 with hΓi
  have hΓΓi : Γ * Γi = 1 := by
    rw [hΓ, hΓi, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hMg : (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1 = Γ * blkMat finSumFinEquiv G 1 * Γi := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, matHom_io, val_blkGL, map_one, Units.val_one]
  have hdiag : ∀ x : Fin V.rank → AE D, Γi *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (P.map (incA D) *ᵥ x) (Q'.map (incA D) *ᵥ x) := fun x => by
    rw [hγi, mulVec_pairVec_diag, leviMat_map, diagSnd_map]
  have hact : ∀ x : Fin V.rank → AE D, (Γ * blkMat finSumFinEquiv G 1 * Γi) *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (x + (K.map (incA D) * A) *ᵥ x) (x + (K.map (incA D) * A) *ᵥ x) := fun x => by
    have hy : Γi *ᵥ pairVec finSumFinEquiv (x + (K.map (incA D) * A) *ᵥ x) (x + (K.map (incA D) * A) *ᵥ x) =
        blkMat finSumFinEquiv G 1 *ᵥ (Γi *ᵥ pairVec finSumFinEquiv x x) := by
      rw [hdiag, hdiag, blkMat_mulVec, one_mulVec]
      congr 1
      · rw [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← hCm, ← hmP, ← mulVec_mulVec,
          show G = m + 1 from (sub_add_cancel G 1).symm, add_mulVec, one_mulVec, add_comm]
      · rw [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.map_mul, hK,
          Matrix.map_zero _ (map_zero _), Matrix.zero_mul, zero_mulVec, add_zero]
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hy, mulVec_mulVec, hΓΓi, one_mulVec]
  have hKD : KeepsDiag finSumFinEquiv (Γ * blkMat finSumFinEquiv G 1 * Γi) :=
    keepsDiag_of_mulVec fun w hw => by
      obtain ⟨x, rfl⟩ := (mem_diagSub finSumFinEquiv).1 hw
      rw [hact]; exact (pairVec_mem_diagSub finSumFinEquiv).2 rfl
  have hmem : γ * io V (g, 1) * γ⁻¹ ∈ siegel V := mem_siegelOf.2 (by
    change KeepsDiag finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1
    rw [hMg]; exact hKD)
  have hlevi : leviMat finSumFinEquiv (Γ * blkMat finSumFinEquiv G 1 * Γi) = 1 + K.map (incA D) * A := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have h := (hKD.mulVec_diag (Pi.single j 1)).symm.trans (hact _)
    funext i
    have := congrFun h (finSumFinEquiv (.inl i))
    rw [pairVec_inl, pairVec_inl] at this
    rw [this, add_mulVec, one_mulVec]
  refine ⟨hmem, Units.ext ?_⟩
  rw [Units.val_one]
  change (leviMat finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1).det = 1
  rw [hMg, hlevi, Matrix.det_one_add_mul_comm, hAK, add_zero, Matrix.det_one]

theorem conj_io_unip_siegel : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ n ∈ NI V (leviMat finSumFinEquiv γi * K), ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1 := by
  intro D V γ hγ γi hγi r K hK hC n hn
  let φ : GA D V →* GA D (dblSp V) := (MulAut.conj γ).toMonoidHom.comp ((io V).comp (MonoidHom.inl _ _))
  let H : Subgroup (GA D (dblSp V)) := (aP V).ker.map (siegel V).subtype
  have hle : NI V (leviMat finSumFinEquiv γi * K) ≤ H.comap φ := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    obtain ⟨h1, -, h3⟩ := hg
    obtain ⟨hmem, ha⟩ := conj_io_gen_mem V γ hγ γi hγi r K hK hC g h1 h3
    exact ⟨⟨_, hmem⟩, ha, rfl⟩
  obtain ⟨p, hp, hpe⟩ := hle hn
  refine ⟨p, ?_, hp⟩
  have : (p : GA D (dblSp V)) = γ * io V (n, 1) * γ⁻¹ := hpe
  rw [this, inv_mul_cancel_right]

end GlobalTheory.Core.Rk.Dich
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

namespace GlobalTheory.Core.Rk.SWLaw

theorem aP_levi_mul_nC : ∀ (D : D7) (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c → aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A p a c hp
  have hM : Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) ⬝ (dblDec A).jX = (dblDec A).jX ⬝ a.1 := by
    rw [hp, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, HypDec.nC_jX, HypDec.levi_jX]
  apply Units.ext
  rw [GlobalTheory.Doubling.val_aOf]
  show (GlobalTheory.Doubling.leviMat finSumFinEquiv (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  set M := Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) with hMdef
  have key : GlobalTheory.Doubling.leviMat finSumFinEquiv M * rat A.gram⁻¹ = rat A.gram⁻¹ * a.1 := by
    ext i j
    have h := congrFun (congrFun hM (finSumFinEquiv (Sum.inl i))) j
    simp only [HypDec.jX, dblDec, rat, stackRows, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Fin.sum_univ_add, finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, id] at h
    simp only [GlobalTheory.Doubling.leviMat, rat, Matrix.mul_apply, Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.of_apply, Matrix.submatrix_apply, Matrix.map_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      add_mul, Finset.sum_add_distrib]
    exact h
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_nonsing_inv_det _ (gram_det_ne A).isUnit).map _
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at hd
  exact hu.mul_left_cancel hd

end GlobalTheory.Core.Rk.SWLaw
end
