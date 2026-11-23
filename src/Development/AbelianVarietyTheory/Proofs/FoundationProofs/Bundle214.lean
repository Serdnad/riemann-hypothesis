module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivationProdPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle197
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle206
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle152
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle208
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodSquarefreeLabelTuplesWeightGe
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
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm GlobalTheory.JointHarm.Minor

namespace GlobalTheory.DeltaHighest

def ext0 {l : ℕ} (a : Fin l → ℕ) (i : ℕ) : ℕ := if h : i < l then a ⟨i, h⟩ else 0

theorem partitionExtendByZero_antitone {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) : Antitone (ext0 a) := by
  intro i j hij
  unfold ext0
  split_ifs with h h'
  · exact ha (by simpa using hij)
  · omega
  · omega
  · omega

def leadProd {σ : Type} {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) (z : Fin n × Fin l → σ) :
    MvPolynomial σ ℂ :=
  ∏ i : Fin l, lead z (n := i.1 + 1) (le_trans i.2 h) i.2 ^ (ext0 a i - ext0 a (i + 1))

theorem partition_row_difference_eq_extendByZero_difference {l : ℕ} (a : Fin l → ℕ) (i : Fin l) :
    a i - nextRow a i = ext0 a i - ext0 a (i + 1) := by
  simp [ext0, nextRow]

theorem leadProd_rows {σ : Type} {n l : ℕ} (h : l ≤ n) {a : Fin l → ℕ} (ha : Antitone a)
    (z : Fin n × Fin l → σ) (hz : Function.Injective z) :
    (∀ c d : Fin n, c < d → rowDer z c d (leadProd h a z) = 0) ∧
      ∀ c : Fin n, rowDer z c c (leadProd h a z) = (ext0 a c : ℂ) • leadProd h a z := by
  have := what₂ z hz (ext0 a) (partitionExtendByZero_antitone ha) l (fun i hi => dif_neg (by omega))
    (fun i => le_trans i.2 h) (fun i => i.2)
  simpa only [rowOp_eq_rowDer, leadProd] using this

theorem leadProd_kill {σ : Type} {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) (z : Fin n × Fin l → σ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (hD : ∀ w, D (X (z w)) = 0) :
    D (leadProd h a z) = 0 := by
  rw [leadProd, derivation_prod_pow D _ _ _ (fun _ => 0)]
  · simp
  · intro i
    rw [zero_smul, lead, derivation_det]
    refine Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [Matrix.updateRow_self]
    exact hD _

theorem rowDer_X_other {σ : Type} {n l : ℕ} (z : Fin n × Fin l → σ) (c d : Fin n) (v : σ)
    (hv : ∀ w, z w ≠ v) : rowDer z c d (X v) = 0 := by
  classical
  rw [← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pderiv_X_of_ne (hv _).symm, mul_zero]

variable (p q n : ℕ)

def vp : Fin n × Fin p → Ln p q n 0 := fun w => (Sum.inl w.2, Sum.inl w.1)

def vm : Fin n × Fin q → Ln p q n 0 := fun w => (Sum.inr w.2, Sum.inl w.1.rev)

theorem vp_inj : Function.Injective (vp p q n) := fun u w h => by
  simpa [vp, Prod.ext_iff, and_comm] using h

theorem vm_inj : Function.Injective (vm p q n) := fun u w h => by
  simpa [vm, Prod.ext_iff, and_comm] using h

theorem top_eq (h : p ≤ n) (a : Fin p → ℕ) :
    minorProd a (zPlus p q n) (topRows h) = leadProd h a (vp p q n) := by
  unfold minorProd leadProd
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [partition_row_difference_eq_extendByZero_difference]
  rfl

theorem bot_eq (h : q ≤ n) (a : Fin q → ℕ) :
    ∃ u : ℂ, minorProd a (zMinus p q n) (botRows h) = u • leadProd h a (vm p q n) := by
  refine ⟨∏ i : Fin q, ((Equiv.Perm.sign (Fin.revPerm (n := i.1 + 1)) : ℤ) : ℂ) ^
    (ext0 a i - ext0 a (i + 1)), ?_⟩
  unfold minorProd leadProd
  rw [Algebra.smul_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [partition_row_difference_eq_extendByZero_difference, map_pow, ← mul_pow, map_intCast, lead, ← Matrix.det_permute]
  congr 2
  ext1 c b
  simp only [zMinus, vm, Matrix.submatrix_apply, Matrix.of_apply, id]
  congr 3
  apply Fin.ext
  have := i.2
  have := c.2
  simp [botRows, Fin.revPerm, Fin.val_rev]
  omega

theorem act_eq (c d : Fin n) (P : Pol p q n 0) :
    fockAct2 p q n 0 (Eab (.inl c) (.inl d)) P =
      rowDer (vp p q n) c d P - rowDer (vm p q n) d.rev c.rev P +
        (if c = d then ((p : ℂ) - q) / 2 else 0) • P := by
  rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, ← rowOp_eq_rowDer,
    ← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply, GlobalTheory.Capelli.rowOp_apply]
  simp only [omE_pos_pos (l := (.inl _, .inl c)) (l' := (.inl _, .inl d)) rfl rfl,
    omE_neg_neg (l := (.inr _, .inl c)) (l' := (.inr _, .inl d)) rfl rfl, vp, vm, Fin.rev_rev,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_smul]
  by_cases h : c = d <;> simp [h] <;> module

theorem delta_mem_hwSub : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ),
    Antitone ap → Antitone am → delta hn ap am ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) := by
  intro p q n hn ap am hp hm
  have h1 : p ≤ n := by omega
  have h2 : q ≤ n := by omega
  obtain ⟨u, hu⟩ := bot_eq p q n h2 am
  have e : delta hn ap am = u • (leadProd h1 ap (vp p q n) * leadProd h2 am (vm p q n)) := by
    rw [delta, top_eq, hu, mul_smul_comm]
  rw [e]
  refine Submodule.smul_mem _ _ ?_
  have a1 := leadProd_rows h1 hp _ (vp_inj p q n)
  have a2 := leadProd_rows h2 hm _ (vm_inj p q n)
  have k1 : ∀ c d, rowDer (vp p q n) c d (leadProd h2 am (vm p q n)) = 0 := fun c d =>
    leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]
  have k2 : ∀ c d, rowDer (vm p q n) c d (leadProd h1 ap (vp p q n)) = 0 := fun c d =>
    leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, Sum.forall,
    posC, IsEmpty.forall_iff, implies_true, and_true, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, act_eq, Derivation.leibniz, k1, k2, a1.2, a2.2, if_true]
  refine ⟨fun c => ?_, fun c d hcd => ?_⟩
  · have hw : ((wtH n ap am (.inl c) : ℚ) : ℂ) =
        (ext0 ap c : ℂ) - (ext0 am c.rev : ℂ) + ((p : ℂ) - q) / 2 := by
      have := c.2
      have hr := c.val_rev
      simp only [wtH, ext0]
      split_ifs with h h' h'
      · omega
      all_goals simp
    rw [hw]
    generalize leadProd h1 ap (vp p q n) = A
    generalize leadProd h2 am (vm p q n) = B
    simp only [mul_zero, zero_add, add_zero, smul_eq_mul, mul_smul_comm, mul_comm B A]
    module
  · rw [a1.1 c d hcd, a2.1 _ _ (Fin.rev_lt_rev.2 hcd), if_neg hcd.ne]
    simp

end GlobalTheory.DeltaHighest

end
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk.Semisimple

theorem dia_sub_smul (k : ℤ) (σ : SL(2, ℤ)) (f g : ℍ → ℂ) (c : ℂ) :
    GlobalTheory.Hk.dia k σ (f - c • g) = GlobalTheory.Hk.dia k σ f - c • GlobalTheory.Hk.dia k σ g := by
  unfold GlobalTheory.Hk.dia
  rw [sub_eq_add_neg, SlashAction.add_slash, ← _root_.neg_smul, ModularForm.SL_smul_slash, _root_.neg_smul,
    ← sub_eq_add_neg]

theorem heckeT_zero (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) : GlobalTheory.Hk.heckeT k q σ 0 = 0 := by
  funext τ
  simp [GlobalTheory.Hk.heckeT, GlobalTheory.Hk.uOp, GlobalTheory.Hk.vOp]

section
variable {N l : ℕ} {k : ℤ}

local notation "P" => GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k

theorem pet_zero_right (hN : 0 < N) (hl : 0 < l) (f : CuspForm (GlobalTheory.Hk.lev N l) k) :
    P ⇑f 0 = 0 := by
  have h := (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f 0 0 1).1
  simp only [CuspForm.coe_zero, smul_zero, add_zero, one_mul] at h
  linear_combination -h

theorem pet_smul_right (hN : 0 < N) (hl : 0 < l) (f h : CuspForm (GlobalTheory.Hk.lev N l) k) (c : ℂ) :
    P ⇑f (c • ⇑h) = c * P ⇑f ⇑h := by
  have e := (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f 0 h c).1
  simp only [CuspForm.coe_zero, zero_add] at e
  rw [e, pet_zero_right hN hl f, zero_add]

theorem pet_lin_right (hN : 0 < N) (hl : 0 < l) (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (a b : ℂ) :
    P ⇑f (a • ⇑g - b • ⇑h) = a * P ⇑f ⇑g - b * P ⇑f ⇑h := by
  have e := (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f (a • g) h (-b)).1
  rw [CuspForm.coe_smul, _root_.neg_smul, ← sub_eq_add_neg] at e
  rw [e, pet_smul_right hN hl]
  ring

theorem pet_conj (hN : 0 < N) (hl : 0 < l) (f g : CuspForm (GlobalTheory.Hk.lev N l) k) :
    P ⇑g ⇑f = (starRingEnd ℂ) (P ⇑f ⇑g) :=
  (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f g 0 0).2

theorem pet_lin_left (hN : 0 < N) (hl : 0 < l) (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (a b : ℂ) :
    P (a • ⇑g - b • ⇑h) ⇑f = (starRingEnd ℂ) a * P ⇑g ⇑f - (starRingEnd ℂ) b * P ⇑h ⇑f := by
  have e : a • ⇑g - b • ⇑h = ⇑(a • g - b • h) := by
    rw [CuspForm.coe_sub, CuspForm.coe_smul, CuspForm.coe_smul]
  rw [e, pet_conj hN hl, CuspForm.coe_sub, CuspForm.coe_smul, CuspForm.coe_smul,
    pet_lin_right hN hl, map_sub, map_mul, map_mul, ← pet_conj hN hl, ← pet_conj hN hl]

theorem eq_zero_of_pet_self (hN : 0 < N) (hl : 0 < l) (f : CuspForm (GlobalTheory.Hk.lev N l) k)
    (h : P ⇑f ⇑f = 0) : f = 0 := by
  by_contra hf
  have := (GlobalTheory.T.peterssonCosetIntegralSum_self_pos_gamma1InterGamma0 N l k hN hl f hf).1
  rw [h] at this
  simp at this

theorem eigen_dia (hN : 0 < N) (hl : 0 < l) {q : ℕ} {σ : SL(2, ℤ)} (hq : q.Prime)
    (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ) (c : ℂ) (u v : CuspForm (GlobalTheory.Hk.lev N l) k)
    (hv : ⇑v = GlobalTheory.Hk.dia k σ ⇑u) (hu : GlobalTheory.Hk.heckeT k q σ ⇑u = c • ⇑u) :
    c • ⇑u = (starRingEnd ℂ) c • ⇑v := by
  have h1 : P ⇑v ⇑v = P ⇑u ⇑u := by
    rw [hv]; exact GlobalTheory.T.peterssonCosetIntegralSum_diamondOperator_unitary N l k q σ hN hl hσ u u
  have h2 : (starRingEnd ℂ) c * P ⇑u ⇑v = c * P ⇑u ⇑u := by
    have h := GlobalTheory.T.peterssonCosetIntegralSum_heckeT_adjoint N l q k σ σ hN hl hq hqN hσ hσ u u
    rw [hu, ← hv, pet_smul_right hN hl, ← CuspForm.coe_smul, pet_conj hN hl, CuspForm.coe_smul,
      pet_smul_right hN hl, map_mul, ← pet_conj hN hl] at h
    exact h
  have h3 : c * P ⇑v ⇑u = (starRingEnd ℂ) c * P ⇑u ⇑u := by
    have h := congrArg (starRingEnd ℂ) h2
    rw [map_mul, map_mul, ← pet_conj hN hl, ← pet_conj hN hl, Complex.conj_conj] at h
    exact h
  have e : ⇑(c • u - (starRingEnd ℂ) c • v) = c • ⇑u - (starRingEnd ℂ) c • ⇑v := by
    rw [CuspForm.coe_sub, CuspForm.coe_smul, CuspForm.coe_smul]
  have hw : c • u - (starRingEnd ℂ) c • v = 0 := by
    apply eq_zero_of_pet_self hN hl
    have := pet_lin_left hN hl (c • u - (starRingEnd ℂ) c • v) u v c ((starRingEnd ℂ) c)
    rw [← e] at this
    rw [this, e, pet_lin_right hN hl, pet_lin_right hN hl, h1, h2, h3]
    ring
  rw [hw, CuspForm.coe_zero] at e
  exact (sub_eq_zero.mp e.symm)

theorem ker_sq (hN : 0 < N) (hl : 0 < l) {q : ℕ} {σ : SL(2, ℤ)} (hq : q.Prime)
    (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ) (c : ℂ) (g u : CuspForm (GlobalTheory.Hk.lev N l) k)
    (hg : ⇑u = GlobalTheory.Hk.heckeT k q σ ⇑g - c • ⇑g) (hu : GlobalTheory.Hk.heckeT k q σ ⇑u = c • ⇑u) :
    u = 0 := by
  obtain ⟨v, hv⟩ := GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 N l k q σ hN hσ u
  obtain ⟨dg, hdg⟩ := GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 N l k q σ hN hσ g
  obtain ⟨sdg, hsdg⟩ := GlobalTheory.T.heckeTOperatorExplicit_cuspForm N l q k σ hN hq hqN hσ dg
  have hw := eigen_dia hN hl hq hqN hσ c u v hv hu
  have hcomm : GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.dia k σ ⇑g)
      = GlobalTheory.Hk.dia k σ (GlobalTheory.Hk.heckeT k q σ ⇑g) :=
    GlobalTheory.T.hecke_operator_commutes_diamond N l q k q σ σ hN hq hqN hσ hσ (CuspForm.toModularFormₗ g)
  have hv' : ⇑v = (1 : ℂ) • ⇑sdg - c • ⇑dg := by
    rw [hv, hg, dia_sub_smul, ← hcomm, hsdg, hdg, one_smul]
  have h1 : P ⇑v ⇑v = P ⇑u ⇑u := by
    rw [hv]; exact GlobalTheory.T.peterssonCosetIntegralSum_diamondOperator_unitary N l k q σ hN hl hσ u u
  have h2 : P ⇑sdg ⇑v = (starRingEnd ℂ) c * P ⇑dg ⇑v := by
    have h := GlobalTheory.T.peterssonCosetIntegralSum_heckeT_adjoint N l q k σ σ hN hl hq hqN hσ hσ dg u
    rw [← hsdg, ← hv, hu, hw, pet_smul_right hN hl] at h
    exact h
  apply eq_zero_of_pet_self hN hl
  have h3 := pet_lin_left hN hl v sdg dg 1 c
  rw [← hv', h1, h2] at h3
  rw [h3]
  simp

end

theorem heckeT_semisimple : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (c : ℂ) (n : ℕ), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, (fun h => GlobalTheory.Hk.heckeT k q σ h - c • h)^[n] ⇑f = 0 → GlobalTheory.Hk.heckeT k q σ ⇑f = c • ⇑f := by
  intro N l q k σ c n hN hl hq hqN hσ
  induction n with
  | zero =>
    intro f hf
    have hf' : ⇑f = 0 := hf
    rw [hf', heckeT_zero, smul_zero]
  | succ n ih =>
    intro f hf
    obtain ⟨sf, hsf⟩ := GlobalTheory.T.heckeTOperatorExplicit_cuspForm N l q k σ hN hq hqN hσ f
    have e : ⇑(sf - c • f) = GlobalTheory.Hk.heckeT k q σ ⇑f - c • ⇑f := by
      rw [CuspForm.coe_sub, CuspForm.coe_smul, hsf]
    rw [Function.iterate_succ_apply] at hf
    have hu := ih (sf - c • f) (by rw [e]; exact hf)
    have h0 := ker_sq hN hl hq hqN hσ c f (sf - c • f) e hu
    rw [h0, CuspForm.coe_zero] at e
    exact sub_eq_zero.mp e.symm

end GlobalTheory.Hk.Semisimple
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

private theorem slz_const_mul (k : ℕ) (δ : M2) (c : ℂ) (g : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => c * g σ) τ = c * slz k δ g τ := by
  unfold slz; ring

private theorem slz_sub (k : ℕ) (δ : M2) (g g' : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => g σ - g' σ) τ = slz k δ g τ - slz k δ g' τ := by
  unfold slz; ring

private theorem slz_sum {ι : Type} (s : Finset ι) (k : ℕ) (δ : M2) (g : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun σ => ∑ i ∈ s, g i σ) τ = ∑ i ∈ s, slz k δ (g i) τ := by
  unfold slz; rw [Finset.mul_sum]

theorem qs_Vo_slz (k l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    qs (Vo l a) τ = ((l : ℂ) ^ (k - 1))⁻¹ * slz k !![(l : ℤ), 0; 0, 1] (qs a) τ := by
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have him : 0 < ((l : ℂ) * (τ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hl) τ.im_pos
  have hV := (GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl ha).2 τ ⟨(l : ℂ) * τ, him⟩ rfl
  rw [hV]
  unfold slz
  simp only [Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  simp only [zero_mul, zero_add, mul_one, mul_zero, sub_zero, add_zero, div_one, one_pow, inv_one]
  rw [ofComplex_apply_of_im_pos him]
  field_simp

end GlobalTheory.EisM

namespace GlobalTheory.EisM

private theorem qs_smul (t : ℂ) (a : ℕ → ℂ) : qs (t • a) = fun τ => t * qs a τ := by
  funext τ; unfold qs
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem sum_slz_repL_Vo : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (t : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k N (ch ε) h → To k (ch ε l) l h = t • h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ = ch ε⁻¹ l * (t * qs (Vo l h) τ - (l : ℂ)⁻¹ * qs h τ) := by
  intro k N l ε h t hk hN hl hlN hMF hT τ
  have hl0 : 0 < l := hl.pos
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  set F := qs h with hF
  set D : M2 := !![(l : ℤ), 0; 0, 1] with hD
  set E : M2 := !![(1 : ℤ), 0; 0, (l : ℤ)] with hE
  have hcoc := GlobalTheory.T.slashIntMatrixPosDet_properties k

  have hTq := (GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum k l (ch ε) h hk hl0 (by simp [ch]) hMF.1).2
  rw [hT, qs_smul] at hTq
  have hind := GlobalTheory.T.heckeCharacterSlashSum_indep_reps k N N ε (DT N l) (Option (Fin l)) (Option (Fin l)) (repT l) (repL N l) F hk dvd_rfl
    (fun δ hδ => ⟨by rw [hδ.1]; exact_mod_cast hl0, hδ.2⟩) (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator N l hl hlN) (GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepLowerLevel N l hl hlN) hMF.2
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have hu : IsUnit (((l : ℤ) : ZMod N)) := by
    rw [Int.cast_natCast]; exact (ZMod.isUnit_iff_coprime l N).2 hcop
  have hεl : ch ε l ≠ 0 := by
    unfold ch; exact (IsUnit.map ε hu).ne_zero
  have hinv : ch ε⁻¹ l = (ch ε l)⁻¹ := by
    unfold ch; rw [MulChar.inv_apply_eq_inv']
  have key : ∀ σ : ℍ, ∑ j : Fin l, slz k (repL N l (some j)) F σ = (ch ε l)⁻¹ * (t * F σ - slz k E F σ) := by
    intro σ
    have h1 := congrFun hTq σ
    rw [hind] at h1
    unfold hsum at h1
    rw [Fintype.sum_option] at h1
    have h2 : repL N l none = E := rfl
    rw [h2] at h1
    have h3 : ∀ j : Fin l, ch ε (repL N l (some j) 0 0) = ch ε l := by
      intro j; simp [repL]
    have h4 : ch ε (E 0 0) = 1 := by simp [hE, ch]
    simp only [h3, h4, one_mul, ← Finset.mul_sum] at h1
    field_simp
    rw [← hF] at h1
    linear_combination -h1
  have hVfun : qs (Vo l h) = fun σ => ((l : ℂ) ^ (k - 1))⁻¹ * slz k D F σ := by
    funext σ; exact qs_Vo_slz k l hl0 h hMF.1 σ
  have hdetD : 0 < D.det := by simp [hD, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hdetE : 0 < E.det := by simp [hE, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hdetA : ∀ (L : ℕ) (j : Fin l), 0 < (repL L l (some j)).det := by
    intro L j; simp [repL, Matrix.det_fin_two_of]; exact_mod_cast hl0
  have hmat : ∀ j : Fin l, D * repL (N * l) l (some j) = repL N l (some j) * D := by
    intro j
    ext i m; fin_cases i <;> fin_cases m <;> simp [hD, repL, Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring
  have hED : E * D = !![((l : ℕ) : ℤ), 0; 0, ((l : ℕ) : ℤ)] := by
    ext i m; fin_cases i <;> fin_cases m <;> simp [hD, hE, Matrix.mul_apply, Fin.sum_univ_two]
  have hterm : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ =
      ((l : ℂ) ^ (k - 1))⁻¹ * slz k D (slz k (repL N l (some j)) F) τ := by
    intro j
    rw [hVfun, slz_const_mul]
    congr 1
    rw [← (hcoc F hk).1 D _ hdetD (hdetA _ j), hmat j, (hcoc F hk).1 _ D (hdetA _ j) hdetD]
  simp only [hterm]
  rw [← Finset.mul_sum, ← slz_sum]
  have hfun : (fun σ => ∑ j : Fin l, slz k (repL N l (some j)) F σ) = fun σ => (ch ε l)⁻¹ * (t * F σ - slz k E F σ) := by
    funext σ; exact key σ
  rw [hfun, slz_const_mul, slz_sub, slz_const_mul]
  have hDE : slz k D (slz k E F) τ = (l : ℂ) ^ k / (l : ℂ) ^ 2 * F τ := by
    rw [← (hcoc F hk).1 E D hdetE hdetD, hED]
    exact (hcoc F hk).2.2.2.2 l τ hl0
  rw [hDE, hinv]
  have hV := qs_Vo_slz k l hl0 h hMF.1 τ
  rw [hV]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

end GlobalTheory.EisM
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.hecke_letter_preserves_basis_set : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T : Letter, admitted N l T → ∀ b ∈ X.B N l w, X.op N l T b ∈ X.B N l w := by
  first | exact @GlobalTheory.KZ.B_stable_op | exact GlobalTheory.KZ.B_stable_op | (intros; apply GlobalTheory.KZ.B_stable_op <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.geometricGalois_coboundary_cong_zero_modPrimePow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt (p := p) w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong (p := p) k (τ w - w) o → Cong (p := p) k o 0 := by
  first | exact @GlobalTheory.K5.KernLoc.main | exact GlobalTheory.K5.KernLoc.main | (intros; apply GlobalTheory.K5.KernLoc.main <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.goodSquarefreeLabelTuples_weight_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ (N m q d : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → 2 ^ 12 ≤ g → (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → 1 - (badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / g) ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  first | exact @GlobalTheory.BadShare.goodSet_weight_ge | exact GlobalTheory.BadShare.goodSet_weight_ge | (intros; apply GlobalTheory.BadShare.goodSet_weight_ge <;> assumption)
end
