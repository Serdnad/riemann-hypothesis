module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace


theorem _root_.GlobalTheory.T.doubledSpace_boxProduct_inner_factorizes : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D),
    ∃ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T))) (𝓕 : Set (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T)))
      (μ₁ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕₁ : Set (Formalism.IndefR.Datum.WO S T)),
      μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL (GlobalTheory.Doubling.dblSp T) S) 𝓕 μ ∧
      μ₁.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕₁ μ₁ ∧
      ∀ a a' b b' : Formalism.IndefR.Datum.WO S T → ℂ, Formalism.IndefR.Datum.IsThetaFunO ψ S T a → Formalism.IndefR.Datum.IsThetaFunO ψ S T a' →
        Formalism.IndefR.Datum.IsThetaFunO ψ S T b → Formalism.IndefR.Datum.IsThetaFunO ψ S T b' →
        ∫ w in 𝓕, GlobalTheory.DblBox.box a b w * star (GlobalTheory.DblBox.box a' b' w) ∂μ =
          (∫ u in 𝓕₁, a u * star (a' u) ∂μ₁) * star (∫ u in 𝓕₁, b u * star (b' u) ∂μ₁) := by
  first | exact @GlobalTheory.DblBoxHaar.box_integral | exact GlobalTheory.DblBoxHaar.box_integral | (intros; apply GlobalTheory.DblBoxHaar.box_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace


theorem _root_.GlobalTheory.T.isThetaFun_doubledSpaceBoxProduct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
    Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      Formalism.IndefR.Datum.IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (GlobalTheory.DblBox.box f₁ f₂) := by
  first | exact @GlobalTheory.DblBoxTheta.isThetaFunO_box | exact GlobalTheory.DblBoxTheta.isThetaFunO_box | (intros; apply GlobalTheory.DblBoxTheta.isThetaFunO_box <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.BlockIdx

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))

theorem gen_mem_hatId {b : 𝓞 D.host.E} (hb : b ∈ 𝔪) {s : AE D} (hs : s ∈ OhE D) :
    inc D (b : D.host.E) * s ∈ hatId D 𝔪 :=
  AddSubgroup.subset_closure ⟨b, hb, s, hs, rfl⟩

theorem mul_mem_hatId {s : AE D} (hs : s ∈ OhE D) {x : AE D} (hx : x ∈ hatId D 𝔪) :
    s * x ∈ hatId D 𝔪 := by
  have h : AddSubgroup.closure {y | ∃ b ∈ 𝔪, ∃ t ∈ OhE D, y = inc D (b : D.host.E) * t} ≤
      (hatId D 𝔪).comap (AddMonoidHom.mulLeft s) := by
    rw [AddSubgroup.closure_le]
    rintro y ⟨b, hb, t, ht, rfl⟩
    show s * (inc D (b : D.host.E) * t) ∈ hatId D 𝔪
    rw [mul_left_comm]
    exact gen_mem_hatId D 𝔪 hb (mul_mem hs ht)
  exact h hx

theorem absNorm_mul_mem_hatId {w : AE D} (hw : w ∈ OhE D) :
    (Ideal.absNorm 𝔪 : AE D) * w ∈ hatId D 𝔪 := by
  have := gen_mem_hatId D 𝔪 (Ideal.absNorm_mem 𝔪) hw
  simpa using this

theorem exists_red (h𝔪 : 𝔪 ≠ ⊥) (x : AE D) (hx : x ∈ OhE D) :
    ∃ r : 𝓞 D.host.E, x - inc D (r : D.host.E) ∈ hatId D 𝔪 := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  obtain ⟨r, hr, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D _ hn x hx
  refine ⟨⟨r, (mem_integralClosure_iff ℤ _).2 hr⟩, ?_⟩
  show x - inc D r ∈ hatId D 𝔪
  rw [e, add_sub_cancel_left]
  exact absNorm_mul_mem_hatId D 𝔪 hw

theorem mem_blockJ_of_congr {a N : ℕ} {k₁ k₂ : GA D N} (h₁ : k₁ ∈ intG D N) (h₂ : k₂ ∈ intG D N)
    (h : ∀ i j, ((k₂ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      ((k₁ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪) :
    k₁⁻¹ * k₂ ∈ blockJ D 𝔪 a N := by
  apply Subgroup.subset_closure
  refine ⟨(intG D N).mul_mem ((intG D N).inv_mem h₁) h₂, fun i j hj hi => ?_⟩
  have hij : i ≠ j := fun e => by subst e; omega
  have hinv := (mem_intG k₁).1 h₁
  have e : (((k₁⁻¹ * k₂ : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      (((k₁ : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        (((k₂ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) -
          ((k₁ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) + 1 := by
    rw [Matrix.mul_sub, Units.inv_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    abel
  rw [e, Matrix.add_apply, Matrix.one_apply_ne hij, add_zero, Matrix.mul_apply]
  exact AddSubgroup.sum_mem _ fun l _ => mul_mem_hatId D 𝔪 ((hinv i l).2) (h l j)

end GlobalTheory.BotPairSmall.BlockIdx

namespace GlobalTheory.BotPairSmall


open BlockIdx in
theorem blockJ_relIndex : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (a N : ℕ),
    (GlobalTheory.BotPairSmall.blockJ D 𝔪 a N).relIndex (intG D N) ≠ 0 ∧
      (GlobalTheory.BotPairSmall.blockJ D 𝔪 a N).relIndex (intG D N) ≤ Ideal.absNorm 𝔪 ^ (N ^ 2) := by
  intro D 𝔪 h𝔪 a N
  have hent : ∀ k : intG D N, ∀ i j,
      (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D :=
    fun k i j => (((mem_intG _).1 k.2) i j).1
  choose r hr using fun (k : intG D N) i j => exists_red D 𝔪 h𝔪 _ (hent k i j)
  let H := (blockJ D 𝔪 a N).subgroupOf (intG D N)
  let f : (intG D N ⧸ H) → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) :=
    fun q i j => Ideal.Quotient.mk 𝔪 (r q.out i j)
  have hf : Function.Injective f := by
    intro q₁ q₂ e
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv]
    refine mem_blockJ_of_congr D 𝔪 q₁.out.2 q₂.out.2 fun i j => ?_
    have e' : Ideal.Quotient.mk 𝔪 (r q₁.out i j) = Ideal.Quotient.mk 𝔪 (r q₂.out i j) :=
      congrFun (congrFun e i) j
    rw [Ideal.Quotient.eq] at e'
    have := sub_mem (sub_mem (hr q₂.out i j) (gen_mem_hatId D 𝔪 e' (one_mem (OhE D)))) (hr q₁.out i j)
    convert this using 1
    push_cast
    rw [map_sub]
    ring
  have hcard : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  haveI : Finite (intG D N ⧸ H) := Finite.of_injective f hf
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  show H.index ≤ _
  rw [Subgroup.index]
  calc Nat.card (intG D N ⧸ H) ≤ Nat.card (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) := Nat.card_le_card_of_injective f hf
    _ = Ideal.absNorm 𝔪 ^ (N ^ 2) := by
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, hcard, ← pow_mul, sq]

end GlobalTheory.BotPairSmall
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall

theorem hatId_mul_of_mem_OhE (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {x y : AE D} (hx : x ∈ OhE D)
    (hy : y ∈ hatId D 𝔪) : x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, (OhE D).mul_mem hx hs, by ring⟩
  | zero => simp
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h

def blockUpperSub (R : Type) [CommRing R] (N a : ℕ) : Subalgebra R (Matrix (Fin N) (Fin N) R) where
  carrier := {A | ∀ i j : Fin N, j.1 < a → a ≤ i.1 → A i j = 0}
  mul_mem' {A B} hA hB i j hj hi := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.1 < a
    · rw [hA i l hl hi, zero_mul]
    · rw [hB l j hj (not_lt.1 hl), mul_zero]
  add_mem' {A B} hA hB i j hj hi := by simp [hA i j hj hi, hB i j hj hi]
  algebraMap_mem' r i j hj hi := by
    have : i ≠ j := fun e => by subst e; omega
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne this]

theorem blockUpper_of_mul_eq_one {R : Type} [CommRing R] {N a : ℕ} {A B : Matrix (Fin N) (Fin N) R}
    (hAB : A * B = 1) (hA : ∀ i j : Fin N, j.1 < a → a ≤ i.1 → A i j = 0) :
    ∀ i j : Fin N, j.1 < a → a ≤ i.1 → B i j = 0 := by
  have hA' : A ∈ blockUpperSub R N a := hA
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  set p := A.charpoly
  have hq : Polynomial.aeval A p.divX ∈ blockUpperSub R N a :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hA') (Polynomial.aeval_mem_adjoin_singleton R _)
  have hCH : Polynomial.aeval A p = 0 := Matrix.aeval_self_charpoly A
  rw [← Polynomial.X_mul_divX_add p, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
  have h2 : p.coeff 0 • B = -Polynomial.aeval A p.divX := by
    have := congrArg (fun M => B * M) hCH
    simp only [mul_add, ← mul_assoc, hBA, one_mul, mul_zero, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      mul_one] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact this
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
  have hB : B ∈ blockUpperSub R N a := by
    have hu : ((-1) ^ Fintype.card (Fin N) * B.det) * p.coeff 0 = 1 := by linear_combination hdet
    have : B = ((-1) ^ Fintype.card (Fin N) * B.det) • (p.coeff 0 • B) := by rw [smul_smul, hu, one_smul]
    rw [this, h2]
    exact Subalgebra.smul_mem _ (neg_mem hq) _
  exact hB

def blockLevelSub (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Subgroup (GA D N) where
  carrier := blockSet D 𝔪 a N
  one_mem' := by
    refine ⟨one_mem _, fun i j hj hi => ?_⟩
    have hij : i ≠ j := fun e => by subst e; omega
    simp [Matrix.one_apply_ne hij]
  mul_mem' {x y} hx hy := by
    have hX := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have hY := (GlobalTheory.NormSum.mem_intG y).1 hy.1
    refine ⟨mul_mem hx.1 hy.1, fun i j hj hi => ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    by_cases hl : l.1 < a
    · rw [mul_comm]; exact hatId_mul_of_mem_OhE D 𝔪 (hY l j).1 (hx.2 i l hl hi)
    · exact hatId_mul_of_mem_OhE D 𝔪 (hX i l).1 (hy.2 l j hj (not_lt.1 hl))
  inv_mem' {x} hx := by
    refine ⟨inv_mem hx.1, fun i j hj hi => ?_⟩
    have hI := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    let J : Ideal (OhE D) :=
      { carrier := {z | (z : AE D) ∈ hatId D 𝔪}
        add_mem' := fun {u v} hu hv => by simpa using add_mem hu hv
        zero_mem' := by simp
        smul_mem' := fun c z hz => by simpa using hatId_mul_of_mem_OhE D 𝔪 c.2 hz }
    let M : Matrix (Fin N) (Fin N) (OhE D) := fun i j => ⟨_, (hI i j).1⟩
    let M' : Matrix (Fin N) (Fin N) (OhE D) := fun i j => ⟨_, (hI i j).2⟩
    have hMM : M * M' = 1 := by
      have hinj : Function.Injective fun A : Matrix (Fin N) (Fin N) (OhE D) => A.map (OhE D).subtype :=
        fun A B e => by
          ext i j
          exact congrFun (congrFun e i) j
      apply hinj
      change (M * M').map (OhE D).subtype = (1 : Matrix (Fin N) (Fin N) (OhE D)).map (OhE D).subtype
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have e1 : M.map (OhE D).subtype = ((x : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
        ext; rfl
      have e2 : M'.map (OhE D).subtype =
          (((x : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
        ext; rfl
      rw [e1, e2, Units.mul_inv]
    have hred := blockUpper_of_mul_eq_one (a := a) (A := M.map (Ideal.Quotient.mk J))
      (B := M'.map (Ideal.Quotient.mk J))
      (by rw [← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)])
      (fun i j hj hi => by
        rw [Matrix.map_apply]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hx.2 i j hj hi)) i j hj hi
    rw [Matrix.map_apply] at hred
    have hm := Ideal.Quotient.eq_zero_iff_mem.1 hred
    exact hm

theorem blockJ_mem_iff_blockSet : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) (h : GA D N),
    h ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 a N ↔ h ∈ GlobalTheory.BotPairSmall.blockSet D 𝔪 a N := by
  intro D 𝔪 a N h
  constructor
  · intro hh
    exact (Subgroup.closure_le (blockLevelSub D 𝔪 a N)).2 (fun _ hx => hx) hh
  · intro hh
    exact Subgroup.subset_closure hh

end GlobalTheory.BotPairSmall
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.BlockMem

variable {D : D7}

theorem hatId_mul_mem (𝔪 : Ideal (𝓞 D.host.E)) {x y : AE D} (hx : x ∈ hatId D 𝔪) (hy : y ∈ OhE D) :
    x * y ∈ hatId D 𝔪 := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, s * y, mul_mem hs hy, by ring⟩
  | zero => simp [zero_mem]
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

def hatIdeal (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) : Ideal (OhE D) where
  carrier := {x | (x : AE D) ∈ hatId D 𝔪}
  add_mem' := fun {x y} hx hy => by
    show ((x : AE D) + (y : AE D)) ∈ hatId D 𝔪
    exact add_mem hx hy
  zero_mem' := by
    show ((0 : OhE D) : AE D) ∈ hatId D 𝔪
    exact zero_mem _
  smul_mem' := fun c x hx => by
    show (c : AE D) * (x : AE D) ∈ hatId D 𝔪
    rw [mul_comm]; exact hatId_mul_mem 𝔪 hx c.2

def liftM {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE D)) (hg : ∀ i j, g i j ∈ OhE D) :
    Matrix (Fin d) (Fin d) (OhE D) :=
  Matrix.of fun i j => ⟨g i j, hg i j⟩

theorem liftM_map {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE D)) (hg : ∀ i j, g i j ∈ OhE D) :
    (liftM g hg).map (OhE D).subtype = g := by
  ext i j; rfl

def blk (a : ℕ) {d : ℕ} (i : Fin d) : ℕ := if a ≤ i.1 then 1 else 0

theorem blk_lt {a d : ℕ} (i j : Fin d) : blk a j < blk a i ↔ j.1 < a ∧ a ≤ i.1 := by
  unfold blk; split_ifs <;> omega

theorem cond_iff {d : ℕ} (𝔪 : Ideal (𝓞 D.host.E)) (a : ℕ) (g : Matrix (Fin d) (Fin d) (AE D))
    (hg : ∀ i j, g i j ∈ OhE D) :
    (∀ i j : Fin d, j.1 < a → a ≤ i.1 → g i j ∈ hatId D 𝔪) ↔
      ((liftM g hg).map (Ideal.Quotient.mk (hatIdeal D 𝔪))).BlockTriangular (blk a) := by
  constructor
  · intro h i j hij
    rw [blk_lt] at hij
    simp only [Matrix.map_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact h i j hij.1 hij.2
  · intro h i j hj hi
    have := h ((blk_lt i j).2 ⟨hj, hi⟩)
    simp only [Matrix.map_apply] at this
    exact (Ideal.Quotient.eq_zero_iff_mem).1 this

theorem bt_transfer {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    {X Y : Matrix (Fin d) (Fin d) R} (h : Y * X = 1) (b : Fin d → ℕ) (hX : (X.map f).BlockTriangular b) :
    (Y.map f).BlockTriangular b := by
  have h' : Y.map f * X.map f = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ f.map_zero f.map_one]
  letI : Invertible (X.map f) := ⟨Y.map f, h', mul_eq_one_comm.mp h'⟩
  have := Matrix.blockTriangular_inv_of_blockTriangular hX
  rwa [Matrix.inv_eq_left_inv h'] at this

theorem mem_iff (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) (h : GA D d) :
    h ∈ blockLev D 𝔪 d a ↔ h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 →
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪 := by
  refine ⟨fun hh => ?_, fun hh => Subgroup.subset_closure hh⟩
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨one_mem _, fun i j hj hi => ?_⟩
    have hne : i ≠ j := fun e => by subst e; omega
    simp [Matrix.one_apply_ne hne, zero_mem]
  | mul x y _ _ hx hy =>
    refine ⟨mul_mem hx.1 hy.1, fun i j hj hi => ?_⟩
    have ix := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have iy := (GlobalTheory.NormSum.mem_intG y).1 hy.1
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    by_cases hl : l.1 < a
    · exact hatId_mul_mem 𝔪 (hx.2 i l hl hi) (iy l j).1
    · rw [mul_comm]
      exact hatId_mul_mem 𝔪 (hy.2 l j hj (not_lt.1 hl)) (ix i l).1
  | inv x _ hx =>
    refine ⟨inv_mem hx.1, ?_⟩
    have ix := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have hX : ∀ i j, ((x : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ OhE D :=
      fun i j => (ix i j).1
    have hY : ∀ i j, (((x⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ OhE D :=
      fun i j => by simpa using (ix i j).2
    rw [cond_iff 𝔪 a _ hY]
    have hXc := (cond_iff 𝔪 a _ hX).1 hx.2
    set X := liftM _ hX
    set Y := liftM _ hY
    have hYX : Y * X = 1 := by
      have key : (Y * X).map (OhE D).subtype = (1 : Matrix (Fin d) (Fin d) (OhE D)).map (OhE D).subtype := by
        rw [Matrix.map_mul, liftM_map, liftM_map, Matrix.map_one _ (map_zero _) (map_one _)]
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      exact Matrix.map_injective (fun u v huv => Subtype.ext huv) key
    exact bt_transfer (Ideal.Quotient.mk (hatIdeal D 𝔪)) hYX (blk a) hXc

end GlobalTheory.FunObj.StdDatum.BlockMem

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylSpan

theorem pure_eq_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    pure f φ = pureA F (⇑f) (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) := by
  rfl

theorem schA_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  intro F _ _ κ _
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, g, hg, rfl⟩
    let L : ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
      { toFun := fun g => pureA F (⇑f) g
        map_add' := fun a b => by funext x; simp [pureA, mul_add]
        map_smul' := fun c a => by funext x; simp [pureA]; ring }
    have h := GlobalTheory.SBSpan.mem_span_restrictedProd F κ g hg
    have h2 : L g ∈ Submodule.map L (Submodule.span ℂ _) := Submodule.mem_map_of_mem h
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨p, ⟨φ, hφ, hcof, rfl⟩, rfl⟩
    exact ⟨f, φ, hφ, hcof, (pure_eq_pureA f φ).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, φ, hφ, hcof, rfl⟩
    refine Submodule.subset_span ⟨f, _, ?_, pure_eq_pureA f φ⟩
    exact ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩

end GlobalTheory.WeylSpan

end
end
