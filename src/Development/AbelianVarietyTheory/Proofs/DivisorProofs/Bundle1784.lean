module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransportOfLatClaims
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.LocTwist

variable {R : Type} [CommRing R]

theorem map_Phi (a : ℕ) (c : R →+* R) : c.mapMatrix (GlobalTheory.Tw.Phi a R) = GlobalTheory.Tw.Phi a R := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem Phi_mul_self (a : ℕ) : GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) := by
  ext i k
  simp only [Matrix.mul_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i.rev]
  · have h1 : (i : ℕ) + (i.rev : ℕ) + 1 = a := by rw [Fin.val_rev]; omega
    rw [if_pos h1]
    by_cases h : k = i
    · subst h
      rw [if_pos (by rw [Fin.val_rev]; omega), Matrix.one_apply_eq, mul_one, ← pow_add]
      congr 1
      rw [Fin.val_rev]; omega
    · rw [if_neg (fun h2 => h (Fin.ext (by rw [Fin.val_rev] at h2; omega))), Matrix.one_apply_ne (Ne.symm h), mul_zero, mul_zero]
  · intro j _ hj
    rw [if_neg (fun h => hj (Fin.ext (by rw [Fin.val_rev]; omega))), zero_mul]
  · simp

theorem thetaGL_val (a : ℕ) (c : R →+* R) (g : GL (Fin a) R) :
    (thetaGL a c g).val = GlobalTheory.Tw.Phi a R * (c.mapMatrix (g⁻¹).val)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ := rfl

theorem thetaGL_thetaGL (a : ℕ) (c : R →+* R) (hc : ∀ x, c (c x) = x) (g : GL (Fin a) R) :
    thetaGL a c (thetaGL a c g) = g := by
  apply Units.ext
  have hT : ∀ M : Matrix (Fin a) (Fin a) R, c.mapMatrix Mᵀ = (c.mapMatrix M)ᵀ := fun M => rfl
  have hcc : ∀ M : Matrix (Fin a) (Fin a) R, c.mapMatrix (c.mapMatrix M) = M := fun M => by
    ext i j; exact hc _
  rw [thetaGL_val, ← map_inv, thetaGL_val, inv_inv, map_mul, map_mul, map_Phi, hT, hT, map_Phi, hcc]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hP := Phi_mul_self (R := R) a
  have hPt : (GlobalTheory.Tw.Phi a R)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) := by
    rw [← Matrix.transpose_mul, hP, Matrix.transpose_smul, Matrix.transpose_one]
  have e : ∀ X : Matrix (Fin a) (Fin a) R, GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R * (X * (GlobalTheory.Tw.Phi a R)ᵀ)) * (GlobalTheory.Tw.Phi a R)ᵀ
      = (GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R) * X * ((GlobalTheory.Tw.Phi a R)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ) := by
    intro X; simp only [Matrix.mul_assoc]
  rw [e, hP, hPt, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow]
  simp

theorem continuous_thetaGL [TopologicalSpace R] [IsTopologicalRing R] (a : ℕ) (c : R →+* R) (hc : Continuous c) :
    Continuous (thetaGL a c) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · change Continuous fun g : GL (Fin a) R => GlobalTheory.Tw.Phi a R * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ
    exact (continuous_const.matrix_mul ((Units.continuous_coe_inv.matrix_map hc).matrix_transpose)).matrix_mul
      continuous_const
  · have : (fun g : GL (Fin a) R => ((thetaGL a c g)⁻¹).val) =
        fun g => GlobalTheory.Tw.Phi a R * (g.val.map c)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ := by
      funext g
      rw [← map_inv, thetaGL_val, inv_inv]
      rfl
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.matrix_map hc).matrix_transpose)).matrix_mul
      continuous_const

end GlobalTheory.LocTwist

theorem GlobalTheory.BCT.thL_continuous_involutive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := by
  intro E _ _ _ hU n w
  obtain ⟨hcont, hinv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  unfold thL
  split_ifs
  · exact ⟨continuous_id, fun g => rfl⟩
  · exact ⟨GlobalTheory.LocTwist.continuous_thetaGL n (cj w) hcont, GlobalTheory.LocTwist.thetaGL_thetaGL n (cj w) hinv⟩
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ExInertUnit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eventually_mem_integers (a : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) a ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) a).2

theorem mem_KGL_of_entries (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem entries_of_mem_KGL {w : Pl E} {k : GLw n w} (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    k.val i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨a, rfl⟩ := hk
  exact (a.val i j).2

theorem mul_entries {w : Pl E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E) (hB : ∀ i j, B i j ∈ w.adicCompletionIntegers E)
    (i j : Fin n) : (A * B) i j ∈ w.adicCompletionIntegers E := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)



theorem local_step (hE : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (M G : Matrix (Fin n) (Fin n) E)
    (hG : IsUnit G) (hGh : cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G)
    (hMG : cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G)
    (hM : ∀ i j, algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E)
    (hG1 : ∀ i j, algebraMap E (w.adicCompletion E) (G i j) ∈ w.adicCompletionIntegers E)
    (hG2 : ∀ i j, algebraMap E (w.adicCompletion E) (G⁻¹ i j) ∈ w.adicCompletionIntegers E) :
    ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = M.charpoly.map (algebraMap E (w.adicCompletion E)) := by
  obtain ⟨-, -, hv, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hE w
  obtain ⟨hconj, ⟨ϖ, q, hU, -⟩, -⟩ := hns hw
  let f := algebraMap E (w.adicCompletion E)
  let c := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hcT : ∀ A : Matrix (Fin n) (Fin n) E, cT (cj w) (f.mapMatrix A) = f.mapMatrix (cT c A) := by
    intro A
    refine Matrix.ext fun i j => ?_
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
    exact hconj _
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGu : IsUnit (f.mapMatrix G) := hG.map _
  have hginv : ((hGu.unit)⁻¹ : GLw n w).val = f.mapMatrix G⁻¹ := by
    have h : f.mapMatrix G⁻¹ * f.mapMatrix G = 1 := by
      rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
    exact Matrix.inv_eq_left_inv h
  have hgK : hGu.unit ∈ GlobalTheory.LFun.KGL w (n := n) :=
    mem_KGL_of_entries w _ (fun a b => by rw [IsUnit.unit_spec]; exact hG1 a b)
      (fun a b => by rw [hginv]; exact hG2 a b)
  have hgh : cT (cj w) hGu.unit.val = hGu.unit.val := by
    rw [IsUnit.unit_spec, hcT, hGh]
  obtain ⟨k, hk, hkk⟩ := GlobalTheory.LFun.InertChart.exists_norm hU hgK hgh
  have hMu : IsUnit M := by
    have h : (G⁻¹ * cT c M * G) * M = 1 := by
      have h' := hMG
      simp only [Matrix.mul_assoc] at h' ⊢
      rw [h', Matrix.nonsing_inv_mul _ hdet]
    exact (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse h)
  have hMwu : IsUnit (f.mapMatrix M) := hMu.map _
  have hmG : cT (cj w) hMwu.unit.val * hGu.unit.val * hMwu.unit.val = hGu.unit.val := by
    rw [IsUnit.unit_spec, IsUnit.unit_spec, hcT, ← map_mul, ← map_mul, hMG]
  have hkinv : cT (cj w) (k⁻¹ : GLw n w).val * cT (cj w) k.val = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  set γ0 : GLw n w := k * hMwu.unit * k⁻¹ with hγ0
  have hγU : cT (cj w) γ0.val * 1 * γ0.val = 1 := by
    calc cT (cj w) γ0.val * 1 * γ0.val
        = cT (cj w) (k⁻¹ : GLw n w).val * (cT (cj w) hMwu.unit.val * (cT (cj w) k.val * k.val) * hMwu.unit.val)
            * (k⁻¹ : GLw n w).val := by
          rw [hγ0, Units.val_mul, Units.val_mul, cT_mul, cT_mul]
          simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = cT (cj w) (k⁻¹ : GLw n w).val * (cT (cj w) k.val * k.val) * (k⁻¹ : GLw n w).val := by
          rw [hkk, hmG]
      _ = 1 := by
          simp only [← Matrix.mul_assoc]
          rw [hkinv, Matrix.one_mul, Units.mul_inv]
  have hγUL : γ0 ∈ UL n w := by
    rw [UL, if_neg hw]
    exact hγU
  refine ⟨⟨γ0, hγUL⟩, ?_, ?_⟩
  · rw [KL, Subgroup.mem_subgroupOf]
    have hinv : cT (cj w) γ0.val = (γ0⁻¹ : GLw n w).val := by
      rw [Matrix.coe_units_inv]
      exact (Matrix.inv_eq_left_inv (by simpa using hγU)).symm
    have hint : ∀ a b, γ0.val a b ∈ w.adicCompletionIntegers E := by
      intro a b
      rw [hγ0, Units.val_mul, Units.val_mul]
      refine mul_entries (mul_entries (entries_of_mem_KGL hk) (fun i j => ?_))
        (entries_of_mem_KGL (inv_mem hk)) a b
      rw [IsUnit.unit_spec]
      exact hM i j
    refine mem_KGL_of_entries w γ0 hint (fun a b => ?_)
    rw [← hinv]
    have h0 := hint b a
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h0 ⊢
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [hv]
    exact h0
  · show (k.val * hMwu.unit.val * (k⁻¹ : GLw n w).val).charpoly = _
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj, IsUnit.unit_spec]
    exact Matrix.charpoly_map M f

end GlobalTheory.ExInertUnit
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.PrincCong

open Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_cj (w : Pl E) (x : w.adicCompletion E) : cj w (cj w x) = x := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · obtain ⟨hc, he⟩ := GlobalTheory.ConjAtPlace.cj_spec w h
    have := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) E w).equalizer (hc.comp hc) continuous_id
      (funext fun k => by simp only [Function.comp_apply, id, he, IsCMField.complexConj_apply_apply])
    exact congrFun this x
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; rfl

theorem cj_lt_one (w : Pl E) {z : w.adicCompletion E} (hz : Valued.v z < 1) : Valued.v (cj w z) < 1 := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · exact GlobalTheory.ConjAtPlace.lt_one_of_continuous _ (GlobalTheory.ConjAtPlace.cj_spec w h).1 hz
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; exact hz

theorem v_cj (w : Pl E) (x : w.adicCompletion E) : Valued.v (cj w x) = Valued.v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hsx : cj w x ≠ 0 := fun h => hx (by rw [← cj_cj w x, h, map_zero])
  have p1 : 0 < Valued.v x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
  have p2 : 0 < Valued.v (cj w x) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hsx)
  rcases lt_trichotomy (Valued.v (cj w x)) (Valued.v x) with hlt | heq | hgt
  · exfalso
    have h1 : Valued.v (cj w x / x) < 1 := by rw [map_div₀, div_lt_one₀ p1]; exact hlt
    have h2 := cj_lt_one w h1
    rw [map_div₀ (cj w), cj_cj, map_div₀, div_lt_one₀ p2] at h2
    exact absurd h2 (not_lt.2 hlt.le)
  · exact heq
  · exfalso
    have h1 : Valued.v (x / cj w x) < 1 := by rw [map_div₀, div_lt_one₀ p2]; exact hgt
    have h2 := cj_lt_one w h1
    rw [map_div₀ (cj w), cj_cj, map_div₀, div_lt_one₀ p1] at h2
    exact absurd h2 (not_lt.2 hgt.le)

def congIdeal (w : Pl E) (k : ℕ) : Ideal (Ov E w) where
  carrier := {x | Valued.v (x : w.adicCompletion E) ≤ WithZero.exp (-(k : ℤ))}
  add_mem' := fun {a b} ha hb => by
    show Valued.v ((a : w.adicCompletion E) + b) ≤ _
    exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  zero_mem' := by
    show Valued.v ((0 : w.adicCompletion E)) ≤ _
    simp
  smul_mem' := fun c x hx => by
    show Valued.v ((c : w.adicCompletion E) * x) ≤ _
    have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
    rw [map_mul]
    exact mul_le_of_le_one_of_le hc hx

end GlobalTheory.PrincCong

namespace GlobalTheory.PrincCong

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def congSub (w : Pl E) (n k : ℕ) : Subgroup (GLw n w) :=
  ((GeneralLinearGroup.map (Ideal.Quotient.mk (congIdeal w k)) : GL (Fin n) (Ov E w) →* _).ker).map
    (bc (Ov E w).subtype)

theorem mem_ker_iff (w : Pl E) (n k : ℕ) (h : GL (Fin n) (Ov E w)) :
    h ∈ (GeneralLinearGroup.map (Ideal.Quotient.mk (congIdeal w k)) : GL (Fin n) (Ov E w) →* _).ker ↔
      ∀ i j, Valued.v ((((h : Matrix (Fin n) (Fin n) (Ov E w)) i j : Ov E w) : w.adicCompletion E) -
        (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  apply forall_congr'; intro i; apply forall_congr'; intro j
  change Ideal.Quotient.mk _ ((h : Matrix (Fin n) (Fin n) (Ov E w)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j ↔ _
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq]
    rw [← map_one (Ideal.Quotient.mk (congIdeal w k)), Ideal.Quotient.eq]
    show Valued.v (((_ - 1 : Ov E w)) : w.adicCompletion E) ≤ _ ↔ _
    push_cast; rfl
  · simp only [Matrix.one_apply_ne hij, Ideal.Quotient.eq_zero_iff_mem, sub_zero]
    rfl

theorem mem_congSub_iff (w : Pl E) (n k : ℕ) (g : GLw n w) :
    g ∈ congSub w n k ↔ g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j -
      (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, rfl⟩, (mem_ker_iff w n k h).1 hh⟩
  · rintro ⟨⟨h, rfl⟩, hg⟩
    exact ⟨h, (mem_ker_iff w n k h).2 hg, rfl⟩

end GlobalTheory.PrincCong

namespace GlobalTheory.PrincCong

open Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_mem_Ov (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ Ov E w) : cj w x ∈ Ov E w := by
  change Valued.v (cj w x) ≤ 1
  rw [v_cj]; exact hx

theorem thL_mem_congSub (w : Pl E) (hw : ¬ IsSplitAt w) (n k : ℕ) (g : GLw n w) (hg : g ∈ congSub w n k) :
    thL n w g ∈ congSub w n k := by
  obtain ⟨h, hh, rfl⟩ := hg
  have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hw]
  rw [ht]
  let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (cj_mem_Ov w)
  have hI : congIdeal w k ≤ (congIdeal w k).comap c' := by
    intro x hx
    show Valued.v (cj w (x : w.adicCompletion E)) ≤ _
    rw [v_cj]; exact hx
  let c'' := Ideal.quotientMap (congIdeal w k) c' hI
  refine ⟨thetaGL n c' h, ?_, GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) h⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker] at hh ⊢
  rw [GlobalTheory.ThetaPull.map_thetaGL (Ideal.Quotient.mk (congIdeal w k)) c' c''
    (fun x => (Ideal.quotientMap_mk).symm) h, hh, map_one]

theorem isOpen_ball (w : Pl E) (m : ℤ) : IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_ball_subset (w : Pl E) {U : Set (w.adicCompletion E)} {x : w.adicCompletion E} (hU : U ∈ 𝓝 x) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y, Valued.v (y - x) ≤ WithZero.exp (-(N : ℤ)) → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun N hN y hy => hγ ?_⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  refine hy.trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hne]
  rw [WithZero.exp_lt_exp]
  omega

theorem isOpen_congSub (w : Pl E) (n k : ℕ) : IsOpen (congSub w n k : Set (GLw n w)) := by
  have hs : (congSub w n k : Set (GLw n w)) = (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∩
      ⋂ i, ⋂ j, {g : GLw n w | Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
        WithZero.exp (-(k : ℤ))} := by
    ext g
    simp only [SetLike.mem_coe, mem_congSub_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hs]
  refine (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  exact (isOpen_ball w _).preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem exists_mat_subset (w : Pl E) (n : ℕ) {C : Set (Matrix (Fin n) (Fin n) (w.adicCompletion E))}
    (hC : C ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E),
      (∀ i j, Valued.v (M i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(N : ℤ))) → M ∈ C := by
  have h1 : C ∈ Filter.pi fun i => Filter.pi fun j => 𝓝 ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) := by
    have e : 𝓝 (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
        Filter.pi fun i => Filter.pi fun j => 𝓝 ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) := by
      change 𝓝 (fun i j => (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) = _
      rw [nhds_pi]; congr 1; funext i; rw [nhds_pi]
    rw [← e]; exact hC
  obtain ⟨I, -, t, ht, hsub⟩ := Filter.mem_pi.1 h1
  have h2 : ∀ i, ∃ t' : Fin n → Set (w.adicCompletion E),
      (∀ j, t' j ∈ 𝓝 ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) ∧ Set.univ.pi t' ⊆ t i := by
    intro i
    obtain ⟨J, -, t', ht', hs'⟩ := Filter.mem_pi.1 (ht i)
    exact ⟨t', ht', fun x hx => hs' fun j _ => hx j (Set.mem_univ j)⟩
  choose t' ht' hs' using h2
  have h3 : ∀ i j, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y, Valued.v (y - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(N : ℤ)) → y ∈ t' i j := fun i j => exists_ball_subset w (ht' i j)
  choose N₀ hN₀ using h3
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => N₀ p.1 p.2, fun N hN M hM => hsub fun i _ => hs' i fun j _ => ?_⟩
  refine hN₀ i j N ?_ _ (hM i j)
  exact le_trans (Finset.le_sup (f := fun p : Fin n × Fin n => N₀ p.1 p.2) (Finset.mem_univ (i, j))) hN

end GlobalTheory.PrincCong

namespace GlobalTheory.PrincCong

open Filter Topology

end GlobalTheory.PrincCong
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.ToricCoordAlg

theorem isAlgebraic_coordIn : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀)
    (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s)
    (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ)
    (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  intro hA K _ _ d δ ι h2 hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q χ T hV
  classical
  obtain ⟨hQ, hχ, hfin, S, hS, rfl⟩ := hV
  have htriv := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, GlobalTheory.TwistedTransportProof.coordIn_eq, Finset.mul_sum]
  refine (mem_algebraicClosure_iff (F := ℚ) (E := ℂ)).1 (sum_mem fun q _ => ?_)
  have e : coordIn E d s κ Ω₀ 1 * (((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0) =
      ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * coordIn E d s κ Ω₀ (S q 0) := by
    rw [GlobalTheory.TwistedTransportProof.coordIn_eq d s κ Ω₀ (S q 0)]; ring
  rw [e]
  have h1 := hA K d δ ι h2 hd hδ Λ₀ Ω₀ hΛ hΩ E I φ s 𝔣 Q ⟨hE, hφ, hφK, hs, h𝔣, hQ⟩ κ q.out (S q) (hS q)
  have h3 : IsAlgebraic ℚ ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ)) :=
    (GlobalTheory.ToricRatioBridge.isAlgebraic_finPart hχ.2.2.1 htriv q.out).mul
      (GlobalTheory.TwistedTransportProof.isAlgebraic_modF_pow q.out s)
  refine mul_mem (inv_mem ?_) ?_ <;> rw [mem_algebraicClosure_iff] <;> assumption

end GlobalTheory.ToricCoordAlg
end
end
