module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUniformizerHermitianIdeal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle001
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem leftInvRes_gen {a : ℕ} {K : Type} [CommRing K] (ϖ : Fv F v) (hϖ : IsUnif v ϖ)
    (π : Red.OR (E := E) v →+* K) (hsurj : Function.Surjective π)
    (hker : ∀ x : Red.OR (E := E) v, π x = 0 ↔ (x : Fv F v ⊗[F] E) ∈ PO (E := E) v ϖ)
    (hLK : ∀ Mb : Matrix (Fin n) (Fin a) K, Function.Injective Mb.mulVec →
      ∃ Nb : Matrix (Fin a) (Fin n) K, Nb * Mb = 1)
    (M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E)) (hM : ∀ k i, M k i ∈ OEv (E := E) v)
    (hsat : ∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) :
    ∃ N0 : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), ∃ B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      (∀ i k, N0 i k ∈ OEv (E := E) v) ∧ (∀ i j, B i j ∈ OEv (E := E) v) ∧
      N0 * M = 1 + sc (E := E) v ϖ • B := by
  classical
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  set Mo : Matrix (Fin n) (Fin a) (Red.OR (E := E) v) := fun k i => ⟨M k i, hM k i⟩ with hMo
  have hcoe : (Red.OR (E := E) v).subtype = (Red.OR (E := E) v).subtype := rfl

  have hinj : Function.Injective (Mo.map π).mulVec := by
    intro x y hxy
    have hz : (Mo.map π).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    obtain ⟨cO, hcO⟩ : ∃ cO : Fin a → Red.OR (E := E) v, ∀ i, π (cO i) = (x - y) i :=
      ⟨fun i => (hsurj ((x - y) i)).choose, fun i => (hsurj ((x - y) i)).choose_spec⟩
    have hred : ∀ k, π ((Mo.mulVec cO) k) = 0 := by
      intro k
      rw [RingHom.map_mulVec]
      have : (π ∘ cO) = x - y := funext hcO
      rw [this, hz]
      rfl
    have hPO : ∀ k, ∃ m ∈ OEv (E := E) v, ((Mo.mulVec cO k : Red.OR (E := E) v) : Fv F v ⊗[F] E) =
        sc (E := E) v ϖ * m := fun k => (hker _).1 (hred k)
    choose m hmO hm using hPO
    have hc : ∀ i, sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
      refine hsat _ fun k => ?_
      have e : Matrix.mulVec M (fun i => sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E)) k =
          sc (E := E) v ϖ⁻¹ * ((Mo.mulVec cO k : Red.OR (E := E) v) : Fv F v ⊗[F] E) := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        rw [show ((∑ i, Mo k i * cO i : Red.OR (E := E) v) : Fv F v ⊗[F] E) =
            ∑ i, ((Mo k i : Fv F v ⊗[F] E) * (cO i : Fv F v ⊗[F] E)) by push_cast; rfl]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, hm k, ← mul_assoc, sc_mul, inv_mul_cancel₀ h0, sc_one, one_mul]
      exact hmO k
    funext i
    have : π (cO i) = 0 := by
      rw [hker]
      refine ⟨sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E), hc i, ?_⟩
      rw [← mul_assoc, sc_mul, mul_inv_cancel₀ h0, sc_one, one_mul]
    rw [← sub_eq_zero, ← Pi.sub_apply, ← hcO i, this]
  obtain ⟨Nb, hNb⟩ := hLK _ hinj
  obtain ⟨NO, hNO⟩ : ∃ NO : Matrix (Fin a) (Fin n) (Red.OR (E := E) v), ∀ i k, π (NO i k) = Nb i k :=
    ⟨fun i k => (hsurj (Nb i k)).choose, fun i k => (hsurj (Nb i k)).choose_spec⟩
  have hmap : (NO * Mo).map π = 1 := by
    rw [Matrix.map_mul]
    have : NO.map π = Nb := by ext i k; exact hNO i k
    rw [this, hNb]
  set P : Matrix (Fin a) (Fin a) (Red.OR (E := E) v) := NO * Mo with hP
  have hPO : ∀ i j, ∃ b ∈ OEv (E := E) v, (((P - 1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j :
      Red.OR (E := E) v) : Fv F v ⊗[F] E) = sc (E := E) v ϖ * b := by
    intro i j
    refine (hker _).1 ?_
    have := congrFun (congrFun hmap i) j
    simp only [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    simp [Matrix.one_apply]
  choose B hBO hB using hPO
  refine ⟨NO.map (Red.OR (E := E) v).subtype, fun i j => B i j, fun i k => (NO i k).2, hBO, ?_⟩
  have hM' : M = Mo.map (Red.OR (E := E) v).subtype := by ext k i; rfl
  rw [hM', ← Matrix.map_mul, ← hP]
  ext i j
  have h1 := hB i j
  rw [Matrix.sub_apply] at h1
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have e1 : (Red.OR (E := E) v).subtype (P i j) =
      (((P i j - (1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E) +
        (((1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E)) := by
    show (P i j : Fv F v ⊗[F] E) = _
    push_cast; ring
  rw [e1, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [add_comm] <;> rfl

end PI.OmVd
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem hR_smulE_right (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_sum_right {ι : Type} (s : Finset ι) (x : Fin n → Fv F v ⊗[F] E) (f : ι → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ i ∈ s, f i) = ∑ i ∈ s, hR (Fv F v) σ J x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hR_zero_right σ J v x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hR_add_right, ih]

theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, _, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, _, rfl⟩ := hy
      rw [← map_mul]
      exact Submodule.subset_span ⟨a * b, trivial, by simp⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

end Gen

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem lat_oev_smul (v : PlX X) {c : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E} (hc : c ∈ OEv (E := X.B.I.E) v)
    {x : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E} (hx : x ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) :
    c • x ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨o, _, rfl⟩ := hc
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨o • l, X.B.I.L.smul_mem o hl, ?_⟩
      funext i
      simp only [ratV, Pi.smul_apply, smul_eq_mul]
      rw [← map_mul]
      rfl
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
    | smul d x _ h =>
      beta_reduce
      beta_reduce at h
      have e : inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • (d • x) =
          d • (inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • x) := by
        funext i
        change _ * ((d : Fv X.B.I.F v) • x i) = (d : Fv X.B.I.F v) • (_ * x i)
        rw [mul_smul_comm]
      rw [e]; exact Submodule.smul_mem _ d h
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add c c' _ _ h1 h2 => rw [add_smul]; exact Submodule.add_mem _ h1 h2
  | smul d c _ h =>
    have e : (d • c) • x = d • (c • x) := by
      funext i
      change ((d : Fv X.B.I.F v) • c) * x i = (d : Fv X.B.I.F v) • (c * x i)
      rw [smul_mul_assoc]
    rw [e]; exact Submodule.smul_mem _ d h

abbrev zi : Fin (D.R.rS + 1 + D.R.rS) := Fin.castAdd D.R.rS (Fin.last D.R.rS)

theorem gramE_entry (j i : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i = if i = piv D.R.rS j then cD X u' j else 0 := by
  rw [gram_eq, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm]
  by_cases h : i = piv D.R.rS j
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (fun e => h e.symm), if_neg h, mul_zero]

def OmVMem : Prop := ∀ (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)), yTup X u' v i ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

def OmVZPrim : Prop :=
  ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → ∀ c : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E,
    c • yTup X u' v (zi (D := D)) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) → c ∈ OEv (E := X.B.I.E) v

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

section

noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix PI.OmLocU Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  exact h

theorem natCast_div_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∈ v.asIdeal) {ϖ : Fv F v} (hϖ : IsUnif v ϖ) :
    ((t : ℕ) : Fv F v) * ϖ⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  have hlt : Valued.v ((t : ℕ) : Fv F v) < 1 := by
    rw [h1]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans_lt ?_
    erw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 ht
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hv]
  calc Valued.v ((t : ℕ) : Fv F v) * (WithZero.exp (-1 : ℤ))⁻¹
      ≤ WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ := by gcongr; exact le_exp_neg_one hlt
    _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

def iz : Fin (D.R.rS + 1 + D.R.rS) := ⟨D.R.rS, by omega⟩

theorem piv_iz : piv D.R.rS (iz (D := D)) = iz := by
  apply Fin.ext
  simp [piv, iz]

theorem eq_iz_of_piv {a : Fin (D.R.rS + 1 + D.R.rS)} (h : piv D.R.rS a = iz) : a = iz := by
  have := congrArg (piv D.R.rS) h
  rwa [piv_invol D.R.rS a, piv_iz] at this

theorem gramE_apply (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b = if piv D.R.rS a = b then cD X u' a else 0 := by
  rw [gram_eq, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm]
  by_cases h : piv D.R.rS a = b <;> simp [h]

theorem cD_iz : cD X u' (iz (D := D)) = -((Tw u' : ℕ) : X.B.I.E) := by
  simp [cD, iz]

def diagonalShiftOneMinus (a : Fin (D.R.rS + 1 + D.R.rS)) : X.B.I.E :=
  if a.val = D.R.rS then 1 - ((Tw u' : ℕ) : X.B.I.E) else 1

theorem prod_diagonalShiftOneMinus : ∏ a, diagonalShiftOneMinus X u' a = 1 - ((Tw u' : ℕ) : X.B.I.E) := by
  rw [Finset.prod_eq_single (iz (D := D))]
  · simp [diagonalShiftOneMinus, iz]
  · intro b _ hb
    have : b.val ≠ D.R.rS := fun e => hb (Fin.ext e)
    simp [diagonalShiftOneMinus, this]
  · simp

end PI.OmVg
end
end

section

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PrimT (a : ℕ) : Set (TupV (E := E) v n a) := {X | IsPrim v Λ X}

def prodEtaB (n a : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (n - a) n, (1 - (etaV (E := E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)))

def GoodP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  StdHyp σ J ψ ∧ (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) ∧
  IsSDLoc σ J v Λ ∧ UnramAt (E := E) v ∧ a ≤ n ∧ IsPrim v Λ Y

def OrbP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y

def FibP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) →
    (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) → (∃ fib, IsOm σ J ψ v a fib) →
    ∀ ϖ : Fv F v, IsUnif v ϖ →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) (PrimT v Λ a) =
      dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) / dT σ ψ v a (HermP v σ a ϖ)

def CountP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) → ∀ ϖ : Fv F v, IsUnif v ϖ →
    dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) =
      ENNReal.ofReal (qv v ^ (-((a : ℤ) ^ 2)) * prodEtaB (E := E) v n a) * dX σ J ψ v a (LamT v Λ a)

def PrimCos (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∀ X ∈ PrimT v Λ a, ∀ Z ∈ lamN v Λ ϖ a 0, X + Z ∈ PrimT v Λ a

theorem smul_prim {a : ℕ} (k : HA (Fv F v) σ J) (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (Y : TupV (E := E) v n a) (hY : IsPrim v Λ Y) : IsPrim v Λ (k • Y) := by
  have hki : ∀ i, (k • Y) i =
      Matrix.mulVec ((HA.mat (Fv F v) σ J k : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) (Y i) :=
    fun i => rfl
  refine ⟨fun i => ?_, fun c hc => hY.2 c ?_⟩
  · rw [hki]; exact (hk (Y i)).1 (hY.1 i)
  · have e : (∑ i, c i • (k • Y) i) =
        Matrix.mulVec ((HA.mat (Fv F v) σ J k : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _)
          (∑ i, c i • Y i) := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.mulVec_smul, hki]
    rw [e] at hc
    exact (hk _).2 hc

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def OmVdEx : Prop := ∀ v : PlX X, StdHyp X.B.I.cm.sig X.B.I.J ψ →
  (∃ μ, SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS) μ) ∧
    ∃ ν, SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS) ν

def OmVdUniq : Prop := ∀ v : PlX X, OmUnique X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

def OmVdOrb : Prop := ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
  OrbP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdFib : Prop := ∀ v : PlX X, FibP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdCnt : Prop := ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
  CountP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdSdW : Prop := ∀ v : PlX X, SdVolW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS)

def OmVdSdH : Prop := ∀ v : PlX X, SdVolH X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

theorem a_le_n' : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem omVBadT_of (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hEx : OmVdEx X ψ) (hUq : OmVdUniq X ψ) (hOrb : OmVdOrb X u' ψ) (hFib : OmVdFib X u' ψ)
    (hCnt : OmVdCnt X u' ψ) (hW : OmVdSdW X ψ) (hH : OmVdSdH X ψ) : OmVBadT X u' ψ := by
  intro hC hS v hv hSD hUn hP
  have hS' := hStd hC hS
  have hG : GoodP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) :=
    ⟨hS', hLat, hSD, hUn, a_le_n' X, hP⟩
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  obtain ⟨hWe, hHe⟩ := hEx v hS'
  rw [← hGram v]
  set T := gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) with hTdef
  set ω := omAt X.B.I.cm.sig X.B.I.J ψ v T with hω
  set O := {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} with hO
  have hsub : O ⊆ PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS) := by
    rintro Z ⟨k, hk, rfl⟩
    exact smul_prim X.B.I.cm.sig X.B.I.J v (abelian₂ X) k hk _ hP
  have hsup : PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS) ⊆
      O ∪ {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ := by
    intro Z hZ
    by_cases hg : gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T
    · exact Or.inl (hOrb v hv hG Z hZ hg)
    · exact Or.inr hg
  have hEq : ω O = ω (PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS)) := by
    apply le_antisymm (measure_mono hsub)
    calc ω (PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
        ≤ ω (O ∪ {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ) := measure_mono hsup
      _ ≤ ω O + ω {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ := measure_union_le _ _
      _ = ω O := by rw [omAt_compl_zero X.B.I.cm.sig X.B.I.J ψ v T, add_zero]
  show ω O = _
  rw [hEq, hω, hFib v hG hWe hHe (hUq v hS').1 ϖ hϖ, hCnt v hv hG hWe ϖ hϖ, hW v hS' hLat hSD hUn hWe,
    hH v hS' hUn hHe ϖ hϖ]
  have hq := qv_pos v
  have hd := absV_dV_pos v
  rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg hd.le _), ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  have e : absV v (dV v) ^ ((X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) -
      ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) =
      absV v (dV v) ^ ((X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ)) /
        absV v (dV v) ^ (((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) := Real.rpow_sub hd _ _
  rw [e]
  unfold prodEtaB
  have : (0 : ℝ) < qv v ^ (-(((D.R.rS + 1 + D.R.rS : ℕ) : ℤ) ^ 2)) := zpow_pos hq _
  have : (0 : ℝ) < absV v (dV v) ^ (((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) := Real.rpow_pos_of_pos hd _
  field_simp

end Loc

end PI.OmVd
end
end
