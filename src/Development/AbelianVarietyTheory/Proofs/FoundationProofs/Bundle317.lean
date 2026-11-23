module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsion
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

noncomputable section

open Formalism.UG Formalism.IndefR.Mult GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.InertThetaCompare

namespace GlobalTheory.LFun.UnitaryDiv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q n : ℕ}

theorem exists_cartan (hU : IsUnramInv ϖ σ q) (g : GL (Fin n) L) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ GLint (Fin n) (intL L), ∃ k₂ ∈ GLint (Fin n) (intL L),
      (g : Matrix (Fin n) (Fin n) L) = (k₁ : Matrix (Fin n) (Fin n) L) *
        Matrix.diagonal (fun i => ϖ ^ a i) * (k₂ : Matrix (Fin n) (Fin n) L) := by
  have hnt := P.fSatake_nontriv hU
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hA : IsDiscreteValuationRing A := Valuation.valuationSubring_isDiscreteValuationRing _
  have : IsPrincipalIdealRing (intL L) := inferInstanceAs (IsPrincipalIdealRing A)
  obtain ⟨c, hc0, hg, -⟩ := P.glint_exists_denom (n := Fin n) A g
  refine P.cartan_decomp_gen (intL L) Valued.v (fun _ => Iff.rfl) ϖ (unif_ne_zero hU) (fun x hx => ?_) g c hc0 hg
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  rw [hϖ, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log hx']

theorem good_of_mem (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h1 : d.length = n) (h2 : d.Pairwise fun a b => b ≤ a)
    {g : GL (Fin n) L} (hg : g ∈ GU σ n) {k₁ k₂ : GL (Fin n) L} (h₁ : k₁ ∈ GLint (Fin n) (intL L))
    (h₂ : k₂ ∈ GLint (Fin n) (intL L))
    (e : g.1 = k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * k₂.1) : Good n d := by
  have hπ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨π', hπ', a, ha, b, hb, e'⟩ := GlobalTheory.DualDivU.hasDiv_dualLab _ σ n d _ hU.2.1 h1 hg
    ⟨ϖ, hπ, k₁, h₁, k₂, h₂, e⟩
  have l1 : (dualLab d).length = n := by simpa [dualLab] using h1
  have l2 : (dualLab d).Pairwise fun a b => b ≤ a := by
    rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact h2.imp fun h => neg_le_neg h
  rw [e] at e'
  have ent := fun {x} (hx : x ∈ GLint (Fin n) (intL L)) => GlobalTheory.DualDivU.entry_mem _ hx
  refine ⟨h1, h2, eq_of_getD l1 h1 (congrFun (eq_of_tails fun k => le_antisymm ?_ ?_))⟩
  · refine tail_le hπ' hπ (anti_getD l1 l2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (inv_mem h₁) ha)) (ent (mul_mem hb (inv_mem h₂))) ?_ k
    calc _ = (k₁⁻¹).1 * (k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * k₂.1) * (k₂⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [e']; simp only [Units.val_mul, Matrix.mul_assoc]
  · refine tail_le hπ hπ' (anti_getD h1 h2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (inv_mem ha) h₁)) (ent (mul_mem h₂ (inv_mem hb))) ?_ k
    calc _ = (a⁻¹).1 * (a.1 * Matrix.diagonal (fun i : Fin n => π' ^ (dualLab d).getD i.1 0) * b.1) * (b⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← e']; simp only [Units.val_mul, Matrix.mul_assoc]

theorem exists_good_div : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ d : List ℤ, GlobalTheory.InertThetaCompare.Good n d ∧
      ∃ a ∈ GLint (Fin n) (intL L), ∃ b ∈ GLint (Fin n) (intL L),
        ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) *
          Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * (b : Matrix (Fin n) (Fin n) L) := by
  intro L _ _ ϖ σ q n hU g
  obtain ⟨a, ha, k₁, h₁, k₂, h₂, e⟩ := exists_cartan hU (g : GL (Fin n) L)
  have hd : ∀ i : Fin n, (List.ofFn a).getD i.1 0 = a i := fun i => by simp [List.getD_eq_getElem?_getD]
  have e' : ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      k₁.1 * Matrix.diagonal (fun i : Fin n => ϖ ^ (List.ofFn a).getD i.1 0) * k₂.1 := by
    simp only [hd]; exact e
  exact ⟨List.ofFn a, good_of_mem hU List.length_ofFn
    (List.pairwise_ofFn.2 fun i j hij => ha hij.le) g.2 h₁ h₂ e', k₁, h₁, k₂, h₂, e'⟩

end GlobalTheory.LFun.UnitaryDiv

end
end

section

noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.SatCoef

open GlobalTheory.InertThetaCompare

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ : L}


open Classical in
def cellSum (ϖ : L) (h : GU σ n → ℂ) (a : Fin (n / 2) → ℤ) : ℂ :=
  ∑ᶠ x : GU σ n ⧸ KU σ n, if Cell ϖ a x then h x.out else 0

theorem exists_of_cellSum {h : GU σ n → ℂ} {a : Fin (n / 2) → ℤ} (ha : cellSum ϖ h a ≠ 0) :
    ∃ x : GU σ n ⧸ KU σ n, h x.out ≠ 0 ∧ Cell ϖ a x := by
  classical
  by_contra hne
  push Not at hne
  refine ha (finsum_eq_zero_of_forall_eq_zero fun x => ?_)
  split_ifs with hx
  · by_contra h0
    exact hne x h0 hx
  · rfl

theorem finite_supp (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {x : GU σ n ⧸ KU σ n | h x.out ≠ 0}.Finite :=
  P.finite_support_cosets (P.isCommensurated_integral_unitary_of_unramified hU n) hh.2

theorem finite_cellSum (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {a | cellSum ϖ h a ≠ 0}.Finite := by
  refine ((finite_supp hU hh).biUnion (t := fun x => {a | Cell ϖ a x}) fun x _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro a ⟨u, hu, k, hk, e⟩ a' ⟨u', hu', k', hk', e'⟩
    exact P.fSatake_cell_unique hU (Nat.mul_div_le n 2) hu hu' hk hk' (e.symm.trans e')
  · intro a ha
    obtain ⟨x, hx⟩ := exists_of_cellSum ha
    exact Set.mem_biUnion hx.1 hx.2

theorem cellSum_dosetInd (hU : IsUnramInv ϖ σ q) (t : GU σ n) (ε : Fin (n / 2) → ℤ)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε) :
    cellSum ϖ (dosetInd ℂ (KU σ n) t) ε ≠ 0 := by
  classical
  have hf : {x : GU σ n ⧸ KU σ n | Cell ϖ ε x ∧ dosetInd ℂ (KU σ n) t x.out ≠ 0}.Finite :=
    (finite_supp hU (Final.DosetIndMem _ _ ℂ t)).subset fun x hx => hx.2
  have key : ∀ x : GU σ n ⧸ KU σ n, ∀ [Decidable (Cell ϖ ε x)],
      (if Cell ϖ ε x then dosetInd ℂ (KU σ n) t x.out else 0) = if x ∈ hf.toFinset then 1 else 0 := by
    intro x _
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_cases h1 : Cell ϖ ε x
    · by_cases h2 : dosetInd ℂ (KU σ n) t x.out = 0
      · simp [h1, h2]
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]
        unfold dosetInd at h2 ⊢
        exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero h2) _
    · simp [h1]
  unfold cellSum
  rw [finsum_congr fun x => @key x _, finsum_eq_sum_of_support_subset (s := hf.toFinset) _ (fun x hx => by
    by_contra h
    exact hx (if_neg h)), Finset.sum_congr rfl fun x hx => if_pos hx]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
  refine Finset.ne_empty_of_mem (a := (QuotientGroup.mk t : GU σ n ⧸ KU σ n)) ?_
  rw [Set.Finite.mem_toFinset]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ n) t
  refine ⟨⟨1, ⟨P.fSatake_borel_one, fun i => by simp⟩, k, k.2, ?_⟩, ?_⟩
  · rw [hk]
    simp only [Subgroup.coe_mul, Units.val_mul, ht, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  · rw [hk]
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k.1, k.2, by rw [one_mul]⟩ :
      t * k.1 ∈ DoubleCoset.doubleCoset t (KU σ n : Set (GU σ n)) (KU σ n : Set (GU σ n)))]
    exact one_ne_zero

theorem satU_laurent : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ h ∈ Hecke ℂ (KU σ n), ∃ s : (Fin (n / 2) → ℤ) →₀ ℂ, (∀ α : Fin (n / 2) → ℂ, SatU ϖ q h α = s.sum fun a c => c * ∏ i, α i ^ a i) ∧ (∀ κ, s κ ≠ 0 → ∃ g : GU σ n, h g ≠ 0 ∧ ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧ ∀ (t : GU σ n) (ε : Fin (n / 2) → ℤ), ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε → h = dosetInd ℂ (KU σ n) t → s ε ≠ 0 := by
  intro L _ _ ϖ σ q n hU h hh
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  let f : (Fin (n / 2) → ℤ) → ℂ := fun a =>
    (∏ i : Fin (n / 2), (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) * cellSum ϖ h a
  have hf : (Function.support f).Finite := (finite_cellSum hU hh).subset fun a ha => right_ne_zero_of_mul ha
  refine ⟨Finsupp.ofSupportFinite f hf, fun α => ?_, fun κ hκ => ?_, fun t ε ht e => ?_⟩
  · have e : SatU ϖ q h α = ∑ᶠ a, f a * ∏ i, α i ^ a i := by
      unfold SatU
      refine finsum_congr fun a => ?_
      rw [Finset.prod_mul_distrib, mul_comm (∏ i, α i ^ a i), mul_right_comm]
      rfl
    rw [e, Finsupp.sum]
    exact finsum_eq_sum_of_support_subset _ fun a ha =>
      Finset.mem_coe.2 (Finsupp.mem_support_iff.2 (left_ne_zero_of_mul ha))
  · obtain ⟨x, h1, h2⟩ := exists_of_cellSum (right_ne_zero_of_mul (show f κ ≠ 0 from hκ))
    exact ⟨x.out, h1, h2⟩
  · subst e
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq) (cellSum_dosetInd hU t ε ht)

end GlobalTheory.LFun.SatCoef

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.FWT

namespace GlobalTheory.Cmp.ExtremalNegativeSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Idx

variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_negS {a : Fin n} : a ∈ negS ε ↔ ε a = false := by simp [negS]

theorem revNeg_anti {a b : Fin n} (hab : a < b) (ha : ε a = false) (hb : ε b = false) :
    revNeg ε b < revNeg ε a := by
  have ha' : a ∈ negS ε := mem_negS.2 ha
  have hb' : b ∈ negS ε := mem_negS.2 hb
  rw [show revNeg ε a = (revOn ε ⟨a, ha'⟩ : Fin n) from Equiv.Perm.ofSubtype_apply_of_mem _ ha',
    show revNeg ε b = (revOn ε ⟨b, hb'⟩ : Fin n) from Equiv.Perm.ofSubtype_apply_of_mem _ hb']
  have h1 : ((negS ε).orderIsoOfFin rfl).symm ⟨a, ha'⟩ < ((negS ε).orderIsoOfFin rfl).symm ⟨b, hb'⟩ :=
    (OrderIso.lt_iff_lt _).2 (Subtype.mk_lt_mk.2 hab)
  exact ((negS ε).orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h1)

end Idx

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end GlobalTheory.Cmp.ExtremalNegativeSets

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharLocProd

noncomputable def evalAt {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun x := x P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem val_algebraMap {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem evalAt_algebraMap {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    evalAt P (algebraMap E (FiniteAdeleRing (𝓞 E) E) a) = algebraMap E (P.adicCompletion E) a := rfl

theorem eq_prod_of_components {E : Type} [Field E] [NumberField E] {R A B : Type} [CommRing R] [CommRing A]
    [CommRing B] (p : R →+* A) (q : R →+* B) (inc : E →+* R)
    (ev : ∀ P : HeightOneSpectrum (𝓞 E), B →+* P.adicCompletion E)
    (hinc : ∀ P a, ev P (q (inc a)) = algebraMap E _ a)
    (I : AddSubgroup B) (hint : ∀ y, y ∈ I ↔ ∀ P, Valued.v (ev P y) ≤ 1)
    (e : HeightOneSpectrum (𝓞 E) → R) (hinf : ∀ P, p (e P) = 0) (h1 : ∀ P, ev P (q (e P)) = 1)
    (h0 : ∀ P P', P' ≠ P → ev P' (q (e P)) = 0) (c : Rˣ →* Circle) (N : ℕ) (hN : 0 < N)
    (hker : ∀ x : Rˣ, (p x = 1 ∧ q x ∈ I ∧ q (x⁻¹ : Rˣ) ∈ I) → (∃ y ∈ I, q x - 1 = N • y) → c x = 1)
    (x : Rˣ) (hx : p x = 1) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : HeightOneSpectrum (𝓞 E) → Eˣ)
    (l : HeightOneSpectrum (𝓞 E) → Rˣ) (hl : ∀ P, (l P : R) = 1 + e P * (inc (k P) - 1))
    (hS : ∀ P ∈ S, Valued.v (ev P (q x)) = P.valuation E (k P : E) ∧
      Valued.v (ev P (q x) - algebraMap E _ (k P : E)) ≤ P.valuation E (N : E) * P.valuation E (k P : E))
    (hS' : ∀ P, P ∉ S → Valued.v (ev P (q x)) = 1 ∧ (N : 𝓞 E) ∉ P.asIdeal) :
    c x = ∏ P ∈ S, c (l P) := by
  classical
  obtain ⟨u, hud⟩ : ∃ u : Rˣ, u = ∏ P ∈ S, l P := ⟨_, rfl⟩
  have hu : (u : R) = ∏ P ∈ S, (l P : R) := by
    simp only [hud, Units.coe_prod]
  have huinf : p u = 1 := by
    rw [hu, map_prod]
    refine Finset.prod_eq_one fun P _ => ?_
    simp [hl, hinf]
  have hloc1 : ∀ P, ev P (q (l P)) = algebraMap E _ (k P : E) := by
    intro P
    simp only [hl, map_add (f := _), map_mul, map_sub, map_one, h1, hinc]
    ring
  have hloc0 : ∀ P Q, Q ≠ P → ev Q (q (l P)) = 1 := by
    intro P Q hQ
    simp only [hl, map_add (f := _), map_mul, map_sub, map_one, h0 P Q hQ]
    ring
  have huS : ∀ P ∈ S, ev P (q u) = algebraMap E _ (k P : E) := by
    intro P hP
    rw [hu, map_prod, map_prod, Finset.prod_eq_single P, hloc1]
    · intro Q _ hQ; exact hloc0 Q P hQ.symm
    · intro h; exact absurd hP h
  have huS' : ∀ P, P ∉ S → ev P (q u) = 1 := by
    intro P hP
    rw [hu, map_prod, map_prod]
    refine Finset.prod_eq_one fun Q hQ => hloc0 Q P ?_
    rintro rfl; exact hP hQ
  obtain ⟨y, hy⟩ : ∃ y : Rˣ, y = x * u⁻¹ := ⟨_, rfl⟩
  have hxu : x = y * u := by rw [hy, inv_mul_cancel_right]
  have hyu : (y : R) * u = x := by
    rw [← Units.val_mul, hxu]
  have hyinf : p y = 1 := by
    have := congrArg p hyu
    rwa [map_mul, huinf, hx, mul_one] at this
  have hyev : ∀ P, ev P (q y) * ev P (q u) = ev P (q x) := by
    intro P
    rw [← map_mul, ← map_mul, hyu]
  have hk0 : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (k P : E) ≠ 0 :=
    fun P => (Valuation.ne_zero_iff _).2 (k P).ne_zero
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hyv : ∀ P, Valued.v (ev P (q y)) = 1 := by
    intro P
    have := congrArg Valued.v (hyev P)
    rw [map_mul] at this
    by_cases hP : P ∈ S
    · rw [huS P hP, val_algebraMap, (hS P hP).1] at this
      exact mul_right_cancel₀ (hk0 P) (by rw [this, one_mul])
    · rwa [huS' P hP, map_one, mul_one, (hS' P hP).1] at this
  have hyv' : ∀ P, Valued.v (ev P (q (y⁻¹ : Rˣ))) = 1 := by
    intro P
    have : Valued.v (ev P (q y)) * Valued.v (ev P (q (y⁻¹ : Rˣ))) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
    rwa [hyv, one_mul] at this
  have hcong : ∀ P, Valued.v (ev P (q y) - 1) ≤ P.valuation E (N : E) := by
    intro P
    by_cases hP : P ∈ S
    · have h2 := (hS P hP).2
      rw [← hyev P, huS P hP, ← sub_one_mul, map_mul, val_algebraMap] at h2
      exact le_of_mul_le_mul_right h2 (zero_lt_iff.2 (hk0 P))
    · have h2 : P.valuation E (N : E) = 1 := by
        have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P
          (r := (N : 𝓞 E))).2 (hS' P hP).2
        simpa using this
      rw [h2]
      exact Valuation.map_sub_le _ (hyv P).le (by rw [map_one])
  have hcy : c y = 1 := by
    refine hker y ⟨hyinf, (hint _).2 fun P => (hyv P).le, (hint _).2 fun P => (hyv' P).le⟩
      ⟨q (inc (N : E)⁻¹) * (q y - 1), (hint _).2 fun P => ?_, ?_⟩
    · rw [map_mul, map_mul, hinc, val_algebraMap, map_sub, map_one, map_inv₀]
      have hv : 0 < P.valuation E (N : E) :=
        zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0)
      exact (inv_mul_le_one₀ hv).2 (hcong P)
    · rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (q.comp inc) N,
        RingHom.comp_apply, ← map_mul, ← map_mul, mul_inv_cancel₀ hN0, map_one, map_one, one_mul]
  rw [hxu, map_mul, hcy, one_mul, hud, map_prod]

theorem char_eq_prod_locK : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∃ N : ℕ, 0 < N ∧ ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ), (∀ P ∈ S, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) ∧ Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤ P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k P : D.host.E)) → (∀ P, P ∉ S → Valued.v (ι (finPart D (x : AE D)) P) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal) → ((c x : Circle) : ℂ) = ∏ P ∈ S, ((χ.locK P (k P) : ℂˣ) : ℂ) := by
  intro D ι hι hint hidem c χ hc
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1.1
  refine ⟨N, hN, fun x hx S k hS hS' => ?_⟩
  choose e he hinf h1 h0 using hidem
  have key := eq_prod_of_components (infPart D) (finPart D) (incA D)
    (fun P => (evalAt P).comp ι.toRingHom)
    (fun P a => (congrArg (evalAt P) (hι a)).trans (evalAt_algebraMap P a))
    (intAE D) hint e hinf h1 h0 c N hN hker x hx S k (fun P => locU (he P).1 (k P)) (fun _ => rfl) hS hS'
  rw [key]
  exact (map_prod Circle.coeHom _ _).trans
    (Finset.prod_congr rfl fun P _ => hc.2 P (e P) (he P) (k P) _ rfl)

end GlobalTheory.CharLocProd
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.weilPairing_galois_equivariant_cm_torsion : ∀ D : D7, WeilPairingGaloisAlt D := by
  first | exact @GlobalTheory.WeilPairingGalois.weilPairingGalois_all | exact GlobalTheory.WeilPairingGalois.weilPairingGalois_all | (intros; apply GlobalTheory.WeilPairingGalois.weilPairingGalois_all <;> assumption)
end
