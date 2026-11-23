module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.MkLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle001
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem matrix_two_by_two_congr {R : Type} {a b c d a' b' c' d' : R} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h1, h2, h3, h4]

private theorem gl_val (z : A E) : (gl (nU z)).val = !![1, z; 0, 1] := rfl

private theorem inv_nU (z : A E) : (gl (nU z))⁻¹ = gl (nU (-z)) := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Units.ext
  rw [Units.val_mul, gl_val, gl_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem act_entry (D : Dat F E) (z : A E) (X : V4 F) :
    (gl (nU (-z))).val * D.herm X * ((gl (nU (-z))).val.map D.bar)ᵀ =
      !![D.mkE (X 1) 0 - z * D.mkE (X 2) (-X 3) - (D.mkE (X 2) (X 3) - z * D.mkE (X 0) 0) * D.bar z,
         D.mkE (X 2) (X 3) - z * D.mkE (X 0) 0;
         D.mkE (X 2) (-X 3) - D.mkE (X 0) 0 * D.bar z, D.mkE (X 0) 0] := by
  rw [gl_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem weilAction_unipotent_null (D : Dat F E) (a b : A F) (hN : a ^ 2 - rt D.δ * b ^ 2 = 0) (X : V4 F) :
    D.act (gl (nU (-D.mkE a b))) X =
      ![X 0, X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3)), X 2 - a * X 0, X 3 - b * X 0] := by
  obtain ⟨hmul, hadd, -, hco, -, hbar, -⟩ := mkLaws F E D
  have hsub : ∀ u t u' t', D.mkE u t - D.mkE u' t' = D.mkE (u - u') (t - t') := by
    intro u t u' t'
    rw [sub_eq_iff_eq_add, hadd, sub_add_cancel, sub_add_cancel]
  have e00 : D.mkE (X 1) 0 - D.mkE a b * D.mkE (X 2) (-X 3) -
      (D.mkE (X 2) (X 3) - D.mkE a b * D.mkE (X 0) 0) * D.bar (D.mkE a b) =
      D.mkE (X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3))) 0 := by
    simp only [hbar, hmul, hsub]
    congr 1
    · linear_combination (X 0) * hN
    · ring
  have e01 : D.mkE (X 2) (X 3) - D.mkE a b * D.mkE (X 0) 0 = D.mkE (X 2 - a * X 0) (X 3 - b * X 0) := by
    simp only [hmul, hsub]
    congr 1 <;> ring
  rw [Dat.act, act_entry, e00, e01]
  ext1 i
  fin_cases i
  · change D.co (D.mkE (X 0) 0) 0 = X 0
    rw [hco]; rfl
  · change D.co (D.mkE (X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3))) 0) 0 = _
    rw [hco]; rfl
  · change D.co (D.mkE (X 2 - a * X 0) (X 3 - b * X 0)) 0 = _
    rw [hco]; rfl
  · change D.co (D.mkE (X 2 - a * X 0) (X 3 - b * X 0)) 1 = _
    rw [hco]; rfl

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.actN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) D.δ → θ ≠ 0 → ∀ s,
      nu F (nbar D v θ s) = 1 ∧
      ∀ X, away v (D.act (nbar D v θ s)⁻¹ X) = away v X ∧ mat v θ (D.act (nbar D v θ s)⁻¹ X) = mat v θ X * !![1, 0; -s, 1] := by
  intro F E _ _ _ _ _ D v θ hθ hθ0 s
  obtain ⟨sadd, smul, scp, -, -, -, -, -, -, -⟩ := sgLaws F v
  have h2 : (2 : Kv v) ≠ 0 := by norm_num
  have hδ : cp v (rt D.δ) = θ ^ 2 := hθ.symm ▸ rfl
  have s0 : sg v 0 = 0 := by
    have := sadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have sneg : ∀ x, sg v (-x) = -sg v x := by
    intro x
    have := sadd x (-x)
    rw [add_neg_cancel, s0] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  refine ⟨?_, fun X => ?_⟩
  · have : Matrix.GeneralLinearGroup.det (nbar D v θ s) = 1 := by
      apply Units.ext
      simp [nbar, Matrix.det_fin_two]
    rw [nu, this, map_one]
  set a := sg v (s / 2) with ha
  set b := sg v (-(s / (2 * θ))) with hb
  have hN : a ^ 2 - rt D.δ * b ^ 2 = 0 := by
    rw [pow_two, pow_two, ← mul_assoc]
    rw [ha, hb, smul, smul, smul, scp, scp, hδ, sub_eq_zero]
    congr 1
    field_simp
  let d : Fin 4 → Kv v := ![0, -(s * cp v (X 2)) - s * θ * cp v (X 3), -(s / 2 * cp v (X 0)), s / (2 * θ) * cp v (X 0)]
  have hX : D.act (nbar D v θ s)⁻¹ X = fun i => X i + sg v (d i) := by
    rw [nbar, inv_nU, weilAction_unipotent_null D a b hN X]
    ext1 i
    fin_cases i
    · simp [d, s0]
    · have e0 : d 1 = -(cp v (2 * X 2) * (s / 2)) + cp v (2 * (rt D.δ * X 3)) * (-(s / (2 * θ))) := by
        change -(s * cp v (X 2)) - s * θ * cp v (X 3) = _
        rw [map_mul, map_mul, map_mul, hδ, map_ofNat]
        field_simp
        ring
      have e1 : sg v (d 1) = -(2 * (a * X 2)) + 2 * (rt D.δ * (b * X 3)) := by
        rw [e0, sadd, sneg, ← smul, ← smul]
        ring
      change X 1 - 2 * (a * X 2) + 2 * (rt D.δ * (b * X 3)) = X 1 + sg v (d 1)
      rw [e1]
      ring
    · have e0 : d 2 = -(cp v (X 0) * (s / 2)) := by
        change -(s / 2 * cp v (X 0)) = _
        ring
      have e1 : sg v (d 2) = -(a * X 0) := by
        rw [e0, sneg, ← smul]
        ring
      change X 2 - a * X 0 = X 2 + sg v (d 2)
      rw [e1]
      ring
    · have e0 : d 3 = -(cp v (X 0) * (-(s / (2 * θ)))) := by
        change s / (2 * θ) * cp v (X 0) = _
        ring
      have e1 : sg v (d 3) = -(b * X 0) := by
        rw [e0, sneg, ← smul]
        ring
      change X 3 - b * X 0 = X 3 + sg v (d 3)
      rw [e1]
      ring
  have hcp : ∀ i, cp v (D.act (nbar D v θ s)⁻¹ X i) = cp v (X i) + d i := by
    intro i
    rw [hX]
    change cp v (X i + sg v (d i)) = _
    rw [map_add (f := _), scp]
  constructor
  · funext i
    change D.act (nbar D v θ s)⁻¹ X i - sg v (cp v (D.act (nbar D v θ s)⁻¹ X i)) = X i - sg v (cp v (X i))
    rw [hcp, sadd, hX]
    change X i + sg v (d i) - _ = _
    ring
  · simp only [mat, hcp]
    rw [Matrix.mul_fin_two]
    refine matrix_two_by_two_congr ?_ ?_ ?_ ?_
    · change cp v (X 1) + (-(s * cp v (X 2)) - s * θ * cp v (X 3)) = _
      ring
    · change cp v (X 2) + -(s / 2 * cp v (X 0)) + (cp v (X 3) + s / (2 * θ) * cp v (X 0)) * θ = _
      field_simp
      ring
    · change cp v (X 2) + -(s / 2 * cp v (X 0)) - (cp v (X 3) + s / (2 * θ) * cp v (X 0)) * θ = _
      field_simp
      ring
    · change cp v (X 0) + 0 = _
      ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

section Alg
variable {R : Type} [CommRing R]

private def pe (e : R) (he : e * e = e) : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 2) (Fin 2) R where
  toFun M := 1 + e • (M - 1)
  map_one' := by simp
  map_mul' A B := by
    obtain ⟨X, rfl⟩ : ∃ X, A = 1 + X := ⟨A - 1, by abel⟩
    obtain ⟨Y, rfl⟩ : ∃ Y, B = 1 + Y := ⟨B - 1, by abel⟩
    have h1 : (1 + X) * (1 + Y) - 1 = X + Y + X * Y := by noncomm_ring
    change 1 + e • ((1 + X) * (1 + Y) - 1) = (1 + e • (1 + X - 1)) * (1 + e • (1 + Y - 1))
    rw [h1, add_sub_cancel_left, add_sub_cancel_left]
    simp only [smul_add, mul_add, add_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, he]
    abel

private theorem pe_val (e : R) (he : e * e = e) (M : Matrix (Fin 2) (Fin 2) R) :
    pe e he M = 1 + e • (M - 1) := rfl

private theorem idem_compl (e : R) (he : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  linear_combination he

private theorem comm0 (c : R) (X Y : Matrix (Fin 2) (Fin 2) R) (h : c • Y = 0) :
    Commute (1 + c • X) (1 + Y) := by
  have h1 : (c • X) * Y = 0 := by rw [Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_zero]
  have h2 : Y * (c • X) = 0 := by rw [Matrix.mul_smul, ← Matrix.smul_mul, h, Matrix.zero_mul]
  change _ * _ = _ * _
  simp only [mul_add, add_mul, one_mul, mul_one, h1, h2]
  abel

private theorem split (e : R) (he : e * e = e) (M : Matrix (Fin 2) (Fin 2) R) :
    M = pe (1 - e) (idem_compl e he) M * pe e he M := by
  obtain ⟨X, rfl⟩ : ∃ X, M = 1 + X := ⟨M - 1, by abel⟩
  have h0 : (1 - e) * e = 0 := by linear_combination -he
  have h1 : ((1 - e) • X) * (e • X) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h0, zero_smul]
  have e1 : pe (1 - e) (idem_compl e he) (1 + X) = 1 + (1 - e) • X := by
    rw [pe_val, add_sub_cancel_left]
  have e2 : pe e he (1 + X) = 1 + e • X := by rw [pe_val, add_sub_cancel_left]
  rw [e1, e2]
  simp only [mul_add, add_mul, one_mul, mul_one, h1]
  rw [sub_smul, one_smul]
  abel

end Alg

section Ad
variable {E : Type} [Field E] [NumberField E]

private theorem fin_of_inf (g : GL (Fin 2) (A E))
    (hg : ∀ i j, (g.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1) :
    g = finGL E 2 (Matrix.GeneralLinearGroup.map (pFin E) g) := by
  have h1 := map_cornerGL_of_zero (sFin E) (RingHom.fst (InfiniteAdeleRing E) (Af E)) (fun _ => rfl)
    (Matrix.GeneralLinearGroup.map (pFin E) g)
  have h2 := pFin_finGL (E := E) (a := 2) (Matrix.GeneralLinearGroup.map (pFin E) g)
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · have h3 : ((finGL E 2 (Matrix.GeneralLinearGroup.map (pFin E) g)).val i j).1 =
        (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing E)) i j :=
      congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing E) => x.val i j) h1
    rw [hg, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · exact (congrArg (fun x : GL (Fin 2) (Af E) => x.val i j) h2).symm

end Ad

section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem two_ne (v : P F) : (2 : Kv v) ≠ 0 := by
  intro h
  have h' : algebraMap F (Kv v) 2 = 0 := by rw [map_ofNat]; exact h
  exact two_ne_zero ((map_eq_zero _).1 h')

private theorem sg_zero (v : P F) : sg v 0 = 0 := by
  obtain ⟨hadd, -⟩ := sgLaws F v
  have := hadd 0 0
  simpa using this

private theorem mk_zero (D : Dat F E) : D.mkE 0 0 = 0 := by simp [Dat.mkE]

private theorem pm (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (a b c d : Kv v) :
    D.mkE (sg v a) (sg v b) * D.mkE (sg v c) (sg v d) =
      D.mkE (sg v (a * c + θ ^ 2 * (b * d))) (sg v (a * d + b * c)) := by
  obtain ⟨hmul, -⟩ := mkLaws F E D
  obtain ⟨hadd, hsm, hcp, -⟩ := sgLaws F v
  have hr : cp v (rt D.δ) = θ ^ 2 := by rw [hθ]; rfl
  rw [hmul, hadd, hadd]
  simp only [hsm, hcp, hr]

private noncomputable def ee (D : Dat F E) (v : P F) (θ : Kv v) : A E := D.mkE (sg v (1 / 2)) (sg v (-(1 / (2 * θ))))

private theorem ee_idem (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) :
    ee D v θ * ee D v θ = ee D v θ := by
  have h2 := two_ne v
  rw [ee, pm D v θ hθ]
  congr 2
  · field_simp; ring
  · field_simp; ring

private theorem ee_sE (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (k : Kv v) :
    ee D v θ * sE D v θ k = 0 := by
  have h2 := two_ne v
  rw [ee, sE, pm D v θ hθ]
  have e1 : (1 / 2 * (k / 2) + θ ^ 2 * (-(1 / (2 * θ)) * (k / (2 * θ))) : Kv v) = 0 := by field_simp; ring
  have e2 : (1 / 2 * (k / (2 * θ)) + -(1 / (2 * θ)) * (k / 2) : Kv v) = 0 := by field_simp; ring
  rw [e1, e2, sg_zero, mk_zero]

private theorem squareRoot_idempotent_embed (D : Dat F E) (v : P F) (θ : Kv v) (hθ : θ ^ 2 = algebraMap F (Kv v) D.δ) (h0 : θ ≠ 0) (s : Kv v) :
    ee D v θ * D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))) = D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))) := by
  have h2 := two_ne v
  rw [ee, pm D v θ hθ]
  congr 2
  · field_simp; ring
  · field_simp; ring

private theorem ee_fst (D : Dat F E) (v : P F) (θ : Kv v) : (ee D v θ).1 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hs, -, -⟩ := sgLaws F v
  have h : ∀ x, (AdeleBaseChange.adeleMap F E (sg v x)).1 = 0 := fun x => by
    change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = 0
    rw [(hs x).1, map_zero]
  change (AdeleBaseChange.adeleMap F E _).1 + (AdeleBaseChange.adeleMap F E _).1 * (rt D.θ).1 = 0
  rw [h, h, zero_mul, add_zero]

end Main

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.decomp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (v : P F) (θ : Kv v) (J : GLv v →* GL (Fin 2) (A E)), Splt D v θ J → ∀ h : GL (Fin 2) (A E),
      ∃ h' k, h = h' * finGL E 2 k ∧ (∀ s, Commute h' (nbar D v θ s)) ∧ ∀ x, Commute (finGL E 2 k) (J x) := by
  intro F E _ _ _ _ _ _ D v θ J hs h
  have he := ee_idem D v θ hs.sq hs.ne
  obtain ⟨k, hk⟩ : ∃ k, Units.map (pe (ee D v θ) he) h = finGL E 2 k := by
    refine ⟨_, fin_of_inf _ fun i j => ?_⟩
    change ((1 + ee D v θ • (h.val - 1) : Matrix (Fin 2) (Fin 2) (A E)) i j).1 = _
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    change ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1 + (ee D v θ).1 * _ = _
    rw [ee_fst, zero_mul, add_zero]
  refine ⟨Units.map (pe (1 - ee D v θ) (idem_compl _ he)) h, k, ?_, fun s => ?_, fun x => ?_⟩
  · rw [← hk]
    exact Units.ext (split _ he h.val)
  · have hn : (nbar D v θ s).val = 1 + !![0, D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))); 0, 0] := by
      ext i j
      change (!![1, D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))); 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j = _
      fin_cases i <;> fin_cases j <;> simp
    have hz := squareRoot_idempotent_embed D v θ hs.sq hs.ne s
    refine Units.ext ?_
    have := comm0 (1 - ee D v θ) (h.val - 1) !![0, D.mkE (sg v (s / 2)) (sg v (-(s / (2 * θ)))); 0, 0] (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sub_mul, hz])
    rw [← hn] at this
    exact this.eq
  · rw [← hk]
    have hj : (J x).val = 1 + Matrix.of fun i j => sE D v θ (x.val i j - (1 : M2 v) i j) := by
      ext i j
      rw [hs.val]; rfl
    refine Units.ext ?_
    have := comm0 (ee D v θ) (h.val - 1) (Matrix.of fun i j => sE D v θ (x.val i j - (1 : M2 v) i j)) (by
      ext i j
      simp [ee_sE D v θ hs.sq hs.ne])
    rw [← hj] at this
    exact this.eq
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.ptN :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : M2 v → ℂ) (X : M2 v),
      (∀ b, ψl v (-(b * X.det)) * Pt a X = Pt (fun m => a (m * !![1, b; 0, 1])) X) ∧
      ∀ s, Pt a (X * !![1, 0; -s, 1]) = Pt (fun m => ψl v (-(s * m.det)) * a m) X := by
  intro F _ _ v a X
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  have hadd := (UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.2.1
  refine ⟨fun b => ?_, fun s => ?_⟩
  · unfold Pt
    rw [← integral_const_mul,
      ← integral_add_right_eq_self (μ := μ2 v) (fun c' => ψl v (-(b * X.det)) *
        (a (cols (fun i => X i 1) c') * ψl v (X 0 0 * c' 1 - X 1 0 * c' 0)))
        (b • fun i => X i 1)]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    have hm : cols (fun i => X i 1) c' * !![1, b; 0, 1]
        = cols (fun i => X i 1) (c' + b • fun i => X i 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cols, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have hp : ψl v (-(b * X.det)) * ψl v (X 0 0 * (c' + b • fun i => X i 1) 1
          - X 1 0 * (c' + b • fun i => X i 1) 0) = ψl v (X 0 0 * c' 1 - X 1 0 * c' 0) := by
      rw [← hadd]
      congr 1
      simp [Matrix.det_fin_two]
      ring
    simp only [hm]
    rw [mul_left_comm, hp]
  · unfold Pt
    rw [show (fun i => (X * !![1, 0; -s, 1]) i 1) = (fun i => X i 1) by
      funext i
      simp [Matrix.mul_apply, Fin.sum_univ_two]]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    have hp : ψl v ((X * !![1, 0; -s, 1]) 0 0 * c' 1 - (X * !![1, 0; -s, 1]) 1 0 * c' 0)
        = ψl v (-(s * (cols (fun i => X i 1) c').det)) * ψl v (X 0 0 * c' 1 - X 1 0 * c' 0) := by
      rw [← hadd]
      congr 1
      simp [cols, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    simp only []
    rw [hp]
    ring
end
