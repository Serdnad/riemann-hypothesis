module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1937
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1938
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle049
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

theorem GlobalTheory.BotPairSmall.iop_skew_conj_mem_TT : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have s0 := VacMove.sd_of_moves (VacMove.moves_one D a)
  have s0' := VacMove.sd_of_moves (VacMove.moves_one D d)
  have heT : e0 ∈ TT D (tor0 D ⊤ δ) a d := hlc.1 _ _ s0 s0' e0 hv.1
  have hne : D.host.conj • (D.host.conj • 𝔪) ≠ ⊥ :=
    GlobalTheory.BotPairSmall.conj_smul_ne_bot D (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)
  obtain ⟨M, hM, hMs⟩ := GlobalTheory.BotPairSmall.CosetTheta.skewLat_nsmul_le (D := D) (D.host.conj • 𝔪) hne d
  exact GlobalTheory.BotPairSmall.CosetTheta.iop_mem_TT hc hM
    (fun x hx => GlobalTheory.BotPairSmall.CosetTheta.La_nsmul_mem (L := stdL D a) ⊤ δ M hMs hx) heT
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.GlueUnitary

theorem tri_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (e1 e2 e3 : R) (h12 : e1 * e2 = 0) (h13 : e1 * e3 = 0) (h23 : e2 * e3 = 0)
    (A B C A' B' C' : Matrix n n R) :
    (e1 • A + e2 • B + e3 • C) * (e1 • A' + e2 • B' + e3 • C') =
      (e1 * e1) • (A * A') + (e2 * e2) • (B * B') + (e3 * e3) • (C * C') := by
  have h21 : e2 * e1 = 0 := by rw [mul_comm]; exact h12
  have h31 : e3 * e1 = 0 := by rw [mul_comm]; exact h13
  have h32 : e3 * e2 = 0 := by rw [mul_comm]; exact h23
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h12, h13, h23, h21, h31, h32,
    zero_smul, add_zero, zero_add]

theorem st_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] (s : R →+* R) (A B : Matrix n n R) :
    ((A * B).map s).transpose = (B.map s).transpose * (A.map s).transpose := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem st_smul {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (c : R) (A : Matrix n n R) :
    ((c • A).map s).transpose = s c • (A.map s).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply]

theorem st_add {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (A B : Matrix n n R) :
    ((A + B).map s).transpose = (A.map s).transpose + (B.map s).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply]

theorem st_one {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] (s : R →+* R) :
    (((1 : Matrix n n R)).map s).transpose = 1 := by
  ext i j; by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem st_st {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (hs : ∀ y, s (s y) = y)
    (A : Matrix n n R) : ((((A.map s).transpose).map s).transpose) = A := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply, hs]

end GlobalTheory.GlueUnitary

namespace GlobalTheory.GlueUnitary

theorem key_alg {R : Type*} [CommRing R] (z p d f fb g : R) (hg : g = 1 - f - fb) (h : fb * f = 0) :
    z - (f * z + fb * p + g * d) = (z - fb * p - (1 - fb) * d) * (1 - f) := by
  subst hg; linear_combination (d - p) * h

theorem glue_unitary : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)) (a : ℕ) (Z : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) (f w : AE D), f ∈ OhE D → w ∈ OhE D → f * f = f → f * sgA D f = 0 → f = inc D ((Z.det : 𝓞 D.host.E) : D.host.E) * w → 1 - f ∈ hatId D 𝔫 → ∃ k ∈ intG D a, ∀ i l, (Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D 𝔫 := by
  intro D 𝔫 a Z f w hf hw hff hffb hfdet h1f
  set s := sgA D with hs
  have hss : ∀ y, s (s y) = y := VacMove.sgA_sgA D
  set φ : 𝓞 D.host.E →+* AE D := (inc D).comp (algebraMap (𝓞 D.host.E) D.host.E) with hφ
  have hφapp : ∀ z : 𝓞 D.host.E, φ z = inc D (z : D.host.E) := fun z => rfl
  have hφint : ∀ z : 𝓞 D.host.E, φ z ∈ OhE D := fun z => VacMove.inc_int D z
  set fb := s f with hfb
  set g := 1 - f - fb with hg
  have hfbf : fb * f = 0 := by rw [mul_comm]; exact hffb
  have hfbfb : fb * fb = fb := by rw [hfb, ← map_mul, hff]
  have hfg : f * g = 0 := by rw [hg]; linear_combination -hff - hffb
  have hfbg : fb * g = 0 := by rw [hg]; linear_combination -hfbf - hfbfb
  have hgg : g * g = g := by rw [hg]; linear_combination hff + hfbfb + 2 * hffb
  have hsg : s g = g := by rw [hg, map_sub, map_sub, map_one, hss]; ring
  have hfO : fb ∈ OhE D := VacMove.sgA_mem D hf
  have hgO : g ∈ OhE D := by
    rw [hg]; exact sub_mem (sub_mem (one_mem _) hf) hfO
  let st : Matrix (Fin a) (Fin a) (AE D) → Matrix (Fin a) (Fin a) (AE D) := fun M => (M.map s).transpose
  let Zi : Matrix (Fin a) (Fin a) (AE D) := Z.map φ
  let P : Matrix (Fin a) (Fin a) (AE D) := w • Z.adjugate.map φ
  have hZP : Zi * P = f • (1 : Matrix (Fin a) (Fin a) (AE D)) := by
    simp only [Zi, P, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
    rw [hfdet]
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.smul_apply, hφapp, mul_comm]
    · simp [Matrix.smul_apply, Matrix.one_apply, h]
  let X : Matrix (Fin a) (Fin a) (AE D) := f • Zi + fb • st P + g • 1
  let X' : Matrix (Fin a) (Fin a) (AE D) := f • P + fb • st Zi + g • 1
  have hXX' : X * X' = 1 := by
    simp only [X, X']
    rw [tri_mul f fb g hffb hfg hfbg, ← st_mul s Zi P, hZP]
    simp only [st, st_smul, st_one, hff, hfbfb, hgg, Matrix.mul_one, smul_smul]
    rw [← hfb, hfbfb, ← add_smul, ← add_smul, hg]; simp
  have hstX' : st X' = X := by
    simp only [X, X', st, st_add, st_smul, st_one, hsg]
    rw [← hfb, hss, st_st s hss]
    abel
  have hX'X : X' * X = 1 := mul_eq_one_comm.mp hXX'
  let u : GL (Fin a) (AE D) := ⟨X', X, hX'X, hXX'⟩
  have huGA : u ∈ GA D a := by
    rw [PtsMem.mem_GA]
    change st X' * X' = 1
    rw [hstX', hXX']
  let k : GA D a := ⟨u, huGA⟩
  have hkinv : (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = X := rfl
  have hentO : ∀ (M : Matrix (Fin a) (Fin a) (AE D)), (∀ i j, M i j ∈ OhE D) → ∀ i j, st M i j ∈ OhE D := by
    intro M hM i j; exact VacMove.sgA_mem D (hM j i)
  have hZiO : ∀ i j, Zi i j ∈ OhE D := fun i j => hφint _
  have hPO : ∀ i j, P i j ∈ OhE D := fun i j => mul_mem hw (hφint _)
  have h1O : ∀ i j, (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := by
    intro i j; by_cases h : i = j
    · subst h; simp [one_mem]
    · simp [Matrix.one_apply, h, zero_mem]
  have hXO : ∀ i j, X i j ∈ OhE D := by
    intro i j
    simp only [X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (add_mem (mul_mem hf (hZiO i j)) (mul_mem hfO (hentO P hPO i j))) (mul_mem hgO (h1O i j))
  have hX'O : ∀ i j, X' i j ∈ OhE D := by
    intro i j
    simp only [X', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (add_mem (mul_mem hf (hPO i j)) (mul_mem hfO (hentO Zi hZiO i j))) (mul_mem hgO (h1O i j))
  refine ⟨k, ?_, ?_⟩
  · rw [mem_intG]
    intro i j
    exact ⟨hX'O i j, hXO i j⟩
  · intro i l
    rw [hkinv]
    have hZ : Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) = Zi := rfl
    rw [hZ]
    rw [Matrix.sub_apply]
    simp only [X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [key_alg (Zi i l) (st P i l) ((1 : Matrix (Fin a) (Fin a) (AE D)) i l) f fb g hg hfbf]
    refine GlobalTheory.CongIdx.mul_mem_hatId ?_ h1f
    exact sub_mem (sub_mem (hZiO i l) (mul_mem hfO (hentO P hPO i l))) (mul_mem (sub_mem (one_mem _) hfO) (h1O i l))

end GlobalTheory.GlueUnitary
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.DetCong

variable {D : D7}

theorem inc_mul_mem_hatId {I J : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} (hb : b ∈ I) {y : AE D}
    (hy : y ∈ hatId D J) : inc D (b : D.host.E) * y ∈ hatId D (I * J) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨b * c, Ideal.mul_mem_mul hb hc, s, hs, ?_⟩
    rw [← mul_assoc, ← map_mul]; rfl
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

theorem sgA_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {y : AE D} (hy : y ∈ hatId D 𝔪) :
    sgA D y ∈ hatId D (D.host.conj • 𝔪) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨D.host.conj • c, Ideal.smul_mem_pointwise_smul _ _ _ hc, sgA D s,
      VacMove.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]; rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg _ _ h => rw [map_neg]; exact neg_mem h

theorem prod_sub_prod_mem {𝔪 : Ideal (𝓞 D.host.E)} {ι : Type*} (s : Finset ι) (f g : ι → AE D)
    (hf : ∀ i ∈ s, f i ∈ OhE D) (hg : ∀ i ∈ s, g i ∈ OhE D) (h : ∀ i ∈ s, f i - g i ∈ hatId D 𝔪) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i ∈ hatId D 𝔪 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, sub_self]; exact zero_mem _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    refine add_mem (mul_mem_hatId (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))))
      (mem_hatId_mul (prod_mem fun i hi => hg i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s)))

theorem det_sub_one_mem_hatId_of {𝔪 : Ideal (𝓞 D.host.E)} {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D))
    (hM : ∀ i j, M i j ∈ OhE D) (hC : ∀ i j, (M - 1) i j ∈ hatId D 𝔪) : M.det - 1 ∈ hatId D 𝔪 := by
  have h1 : ∀ i j, (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← Matrix.det_one (R := AE D) (n := Fin a), Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine sum_mem fun σ _ => ?_
  rw [← smul_sub]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · rw [one_smul]
    exact prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _)
  · rw [Units.neg_smul, one_smul]
    exact neg_mem (prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _))

theorem det_sub_one_mem : ∀ (D : D7) {a : ℕ} (𝔪 : Ideal (𝓞 D.host.E)), IsCoprime 𝔪 (D.host.conj • 𝔪) →
    ∀ k : GA D a, k ∈ intG D a → CongOne D 𝔪 k →
      ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) - 1 ∈
        hatId D (𝔪 * D.host.conj • 𝔪) := by
  intro D a 𝔪 hco k hk hc
  set u : AE D := ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) with hu
  have hint := (mem_intG k).1 hk
  have huO : u ∈ OhE D := VacMove.det_int D _ hint
  have h1 : u - 1 ∈ hatId D 𝔪 := by
    rw [hu, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_sub_one_mem_hatId_of _ (fun i j => (hint i j).1) hc
  have hn : u * sgA D u = 1 := VacMove.det_norm D k
  have h2 : u - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : u - 1 = -(u * sgA D (u - 1)) := by
      rw [map_sub, map_one, mul_sub, hn]; ring
    rw [e]
    exact neg_mem (mul_mem_hatId huO (sgA_mem_hatId h1))
  have hsup : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ := by
    rw [← Ideal.add_eq_sup, Ideal.isCoprime_iff_add.1 hco, Ideal.one_eq_top]
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ D.host.conj • 𝔪 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  have e : u - 1 = inc D (s : D.host.E) * (u - 1) + inc D (t : D.host.E) * (u - 1) := by
    rw [← add_mul, ← map_add (f := _), show (s : D.host.E) + t = ((s + t : 𝓞 D.host.E) : D.host.E) from rfl, hst]; simp
  rw [e]
  refine add_mem (inc_mul_mem_hatId hs h2) ?_
  rw [mul_comm 𝔪]
  exact inc_mul_mem_hatId ht h1

end GlobalTheory.FunObj.StdDatum.DetCong

end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShortTop

theorem geoBound_of_abstract : Quoted → BertiniNF → HeightTie → SlopeBound → GeoBound := by
  intro hQ hB hT hS F _ _ X Λ₀ hG h hh
  obtain ⟨dd, f, hdpos, hf, hfh⟩ := hh
  obtain ⟨hdel, Q, hQ0, hQs⟩ := hB F X.toTuple X.geom hG.bir dd f hf
  have hHyp := GlobalTheory.T.hilbertSamuelLatticeSystem_hyp F X Λ₀ hG
  have hFlat := GlobalTheory.T.hilbertSamuel_filtration_at_good_sections hQ F X Λ₀ hG dd f Q hQs
  have hirr : Irreducible f := GlobalTheory.ChowHt.irreducible_of_irreducible_map hf.irred
  obtain ⟨hpos, hcl⟩ := hS F (Tot X.toGeo) (sysOf X Λ₀) hHyp dd f Q (by omega) hf.homog hirr hQ0 hFlat
  have hfr : Module.finrank F ((sysOf X Λ₀).V (sysOf X Λ₀).T) = X.d := by
    rw [X.d_eq_finrank]; exact (inclEquiv X X.T).finrank_eq.symm
  have hdeg : deg ((sysOf X Λ₀).nm (sysOf X Λ₀).T) ((sysOf X Λ₀).M (sysOf X Λ₀).T) = X.degM X.T := by
    have := GlobalTheory.IsoDeg.deg_map_eq F (X.V X.T) (LinearMap.range (incl X X.T)) (X.nm X.T)
      (comap (X.nm X.T) (inclEquiv X X.T).symm.toLinearMap (inclEquiv X X.T).symm.injective) (inclEquiv X X.T)
      (fun σ m c g => by simp only [csq, HermTools.comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]) (X.M X.T) (X.full X.T).fg
    exact this
  have hTie := (hT F X.toHermSys X.abelian₂ hHyp.lat h ⟨dd, f, hdpos, hf, hfh⟩ dd 1 f 1 hf le_rfl one_ne_zero).2
  rw [hfr, hdeg] at hcl
  have hd' : ((X.del : ℤ) : ℝ) = (dd : ℝ) := by rw [← hdel]; push_cast; rfl
  rw [hd']
  refine GlobalTheory.T.hermitianSystemSlopeBound_of_determinantSlopeInequality X.T X.D X.n X.abelian₂ X.beta Λ₀ X.LamD X.LamT dd h _ X.d (X.degM X.T)
    (by exact_mod_cast hHyp.one_le) hHyp.le_T (by exact_mod_cast X.one_le_n) hHyp.lat.one_le hHyp.one_le_beta
    (by exact_mod_cast hdpos) ?_ hcl
  have h2 : h - (Real.log X.n + 1) / 2 ≤ ht X.w X.A f / (((X.D : ℝ) + 1) * dd) := by
    simp at hTie; linarith
  exact h2

end GlobalTheory.HSShortTop
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.heisenbergEigen_doubledCoords_productFunction : ∀ {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ ξ' : E) (JA : Matrix α α E) (JB : Matrix β β E)
    {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)),
    IsDblCoord c ξ JA JB d dd → ∀ ψ : AddChar R ℂ, (∀ t, ‖ψ t‖ = 1) → ∀ (Λ : Set (Matrix α β E)) (f : (κ → R) → ℂ),
    (∀ w ∈ Λ, d.rho ψ w f = ψ (⅟(2 : R) * symp c ξ' JA JB w w) • f) →
    ∀ z : Matrix α (β ⊕ β) E, z.toCols₁ ∈ Λ → z.toCols₂ ∈ Λ →
      dd.rho ψ z (boxFun f (fun x => star (f x))) = ψ (⅟(2 : R) * symp c ξ' JA (dbl JB) z z) • boxFun f (fun x => star (f x)) := by
  first | exact @GlobalTheory.DblBoxRho.boxrho | exact GlobalTheory.DblBoxRho.boxrho | (intros; apply GlobalTheory.DblBoxRho.boxrho <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.traceSymplecticForm_unitaryGroupAction_invariant : ∀ {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB)
    (x y : Matrix α β E), symp c ξ JA JB (actB c g x) (actB c g y) = symp c ξ JA JB x y := by
  first | exact @GlobalTheory.DblVacEigen.SympAct.symp_actB | exact GlobalTheory.DblVacEigen.SympAct.symp_actB | (intros; apply GlobalTheory.DblVacEigen.SympAct.symp_actB <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped NNReal Matrix Topology ContDiff
open GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.UAut.RightTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isRealLine_conj (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1 :=
    fun x => (archEquiv J h τ x).2
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have u1 := hu (projArch σ J w a)
  have u2 := hu (projArch σ J w a)⁻¹
  refine ⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_,
    fun t => ?_⟩
  · generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    generalize J.map τ.1 = Q at u1 u2 hZ ⊢
    have e1 : M'ᴴ * Q = Q * M := by
      conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : Q * M' = Mᴴ * Q := by
      conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]
    calc (M' * Z * M)ᴴ * Q + Q * (M' * Z * M) = Mᴴ * Zᴴ * (M'ᴴ * Q) + (Q * M') * Z * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
    · show a⁻¹ * γ t * a = _
      rw [e1]
      refine GAd_ext σ J (fun u => ?_) fun v => by simp
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ J e]
    · rw [map_mul, map_mul, e2]
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
      have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
      rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.UAut.RightTranslate


open GlobalTheory.UAut.RightTranslate in
theorem GlobalTheory.UAut.isSm_mul_right_of_isCMExt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E), IsCMExt F E σ → ∀ (f : GlobalTheory.AdelicU.GAd σ J → ℂ) (a : GlobalTheory.AdelicU.GAd σ J), GlobalTheory.UAut.IsSm σ J f → GlobalTheory.UAut.IsSm σ J (fun x => f (x * a)) := by
  intro F E _ _ _ _ _ σ n J h f a hf
  intro k γ hγ g
  have hc : ∀ l : List (GAd σ J), (l.map fun x => a⁻¹ * x * a).prod = a⁻¹ * l.prod * a := fun l => by
    induction l with
    | nil => simp
    | cons x l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih]; simp [mul_assoc]
  have e : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)) =
      fun t => f (g * a * (List.ofFn fun i => a⁻¹ * γ i (t i) * a).prod) := funext fun t => by
    rw [show (List.ofFn fun i => a⁻¹ * γ i (t i) * a) = (List.ofFn fun i => γ i (t i)).map fun x => a⁻¹ * x * a from by
      rw [List.map_ofFn]; rfl, hc]
    simp [mul_assoc]
  show ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)
  rw [e]
  exact hf k (fun i t => a⁻¹ * γ i t * a) (fun i => isRealLine_conj h (hγ i) a) (g * a)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

theorem _root_.GlobalTheory.T.mem_isotropicFlagLevi_of_keeps_weights : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ g : GAd σ J, (∀ a b, wt d M a ≠ wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J g).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0) → (∀ a b, wt d M a ≠ wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J g⁻¹).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0) → g ∈ leviFlag σ J X Y d := by
  first | exact @GlobalTheory.UAut.mem_leviFlag_of_keeps_weights | exact GlobalTheory.UAut.mem_leviFlag_of_keeps_weights | (intros; apply GlobalTheory.UAut.mem_leviFlag_of_keeps_weights <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

theorem _root_.GlobalTheory.T.splitTorusElement_mem_isotropicFlagLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  first | exact @GlobalTheory.UAut.TorusLevi.torus_mem_leviFlag | exact GlobalTheory.UAut.TorusLevi.torus_mem_leviFlag | (intros; apply GlobalTheory.UAut.TorusLevi.torus_mem_leviFlag <;> assumption)
end
