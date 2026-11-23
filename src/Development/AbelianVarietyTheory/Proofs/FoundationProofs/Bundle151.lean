module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle146
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle058
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Data.Nat.Prime.Int

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNSep

theorem finite_nat_roots (a b c : ℂ) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    {n : ℕ | a + (n : ℂ) * b + (n : ℂ) ^ 2 * c = 0}.Finite := by
  set P : Polynomial ℂ := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hPdef
  have hP : P ≠ 0 := by
    intro h0
    apply h
    have e0 := congrArg (fun q => q.coeff 0) h0
    have e1 := congrArg (fun q => q.coeff 1) h0
    have e2 := congrArg (fun q => q.coeff 2) h0
    simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  have hf := (Polynomial.finite_setOf_isRoot hP).preimage (f := (Nat.cast : ℕ → ℂ)) Nat.cast_injective.injOn
  refine hf.subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hn ⊢
  rw [Polynomial.IsRoot.def]
  simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  linear_combination hn

theorem vmul_apply {N : ℕ} (a b : ZMod N) (α : GL (Fin 2) (ZMod N)) (j : Fin 2) :
    vmul ![a, b] α j = a * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 j + b * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 j := by
  simp [vmul, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)) (hx : x ≠ 0) : vmul x α ≠ 0 := by
  intro h
  apply hx
  have : Matrix.vecMul (vmul x α) ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [vmul, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  rw [← this, h, Matrix.zero_vecMul]

end GlobalTheory.FNSep

namespace GlobalTheory.FNSep

theorem eq_or_eq_neg_of_rows {N : ℕ} (α β : GL (Fin 2) (ZMod N))
    (h0 : vmul ![1, 0] α = vmul ![1, 0] β ∨ vmul ![1, 0] α = -vmul ![1, 0] β)
    (h1 : vmul ![0, 1] α = vmul ![0, 1] β ∨ vmul ![0, 1] α = -vmul ![0, 1] β)
    (h2 : vmul ![1, 1] α = vmul ![1, 1] β ∨ vmul ![1, 1] α = -vmul ![1, 1] β) :
    α = β ∨ α = -β := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
  · have E0 : ∀ j, _ := fun j => congrFun h0 j
    have E1 : ∀ j, _ := fun j => congrFun h1 j
    have E2 : ∀ j, _ := fun j => congrFun h2 j
    simp only [Pi.neg_apply, vmul_apply] at E0 E1 E2
    first
    | (left; apply Units.ext; ext i j; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> first | linear_combination E0 j | linear_combination E1 j | linear_combination E2 j - E0 j | linear_combination E2 j - E1 j)
    | (right; apply Units.ext; ext i j; rw [Units.val_neg, Matrix.neg_apply]; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> first | linear_combination E0 j | linear_combination E1 j | linear_combination E2 j - E0 j | linear_combination E2 j - E1 j)

theorem sep_family : ∀ (N : ℕ) [NeZero N], ∃ c₁ c₂ : ℕ, ∀ α β : GL (Fin 2) (ZMod N), (fun τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ) = (fun τ => wp N (vmul ![1, 0] β) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] β) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] β) τ) → α = β ∨ α = -β := by
  intro N _
  classical
  let u : GL (Fin 2) (ZMod N) × GL (Fin 2) (ZMod N) → (Fin 2 → ZMod N) → ℍ → ℂ :=
    fun p e τ => wp N (vmul e p.1) τ - wp N (vmul e p.2) τ
  let S : Set ℕ := ⋃ p : GL (Fin 2) (ZMod N) × GL (Fin 2) (ZMod N),
    {n : ℕ | ¬ (∀ τ, u p ![1, 0] τ = 0 ∧ u p ![0, 1] τ = 0 ∧ u p ![1, 1] τ = 0) ∧
      ∀ τ, u p ![1, 0] τ + (n : ℂ) * u p ![0, 1] τ + (n : ℂ) ^ 2 * u p ![1, 1] τ = 0}
  have hfin : Finite (GL (Fin 2) (ZMod N)) :=
    Finite.of_injective (fun a : GL (Fin 2) (ZMod N) => (a : Matrix (Fin 2) (Fin 2) (ZMod N))) fun a b h => Units.ext h
  have hS : S.Finite := by
    refine Set.finite_iUnion fun p => ?_
    by_cases hz : ∀ τ, u p ![1, 0] τ = 0 ∧ u p ![0, 1] τ = 0 ∧ u p ![1, 1] τ = 0
    · exact Set.finite_empty.subset fun n hn => absurd hz hn.1
    · obtain ⟨τ, hτ⟩ := not_forall.mp hz
      exact (finite_nat_roots _ _ _ hτ).subset fun n hn => hn.2 τ
  obtain ⟨n, hn⟩ := hS.infinite_compl.nonempty
  refine ⟨n, n ^ 2, fun α β hfun => ?_⟩
  have hroot : ∀ τ, u (α, β) ![1, 0] τ + (n : ℂ) * u (α, β) ![0, 1] τ + (n : ℂ) ^ 2 * u (α, β) ![1, 1] τ = 0 := by
    intro τ
    have := congrFun hfun τ
    push_cast at this
    simp only [u]
    linear_combination this
  have hz : ∀ τ, u (α, β) ![1, 0] τ = 0 ∧ u (α, β) ![0, 1] τ = 0 ∧ u (α, β) ![1, 1] τ = 0 := by
    by_contra hz
    exact hn (Set.mem_iUnion.mpr ⟨(α, β), hz, hroot⟩)
  rcases Nat.lt_or_ge 1 N with hN | hN
  · haveI : Fact (1 < N) := ⟨hN⟩
    obtain ⟨z0, z1, z2⟩ := hz UpperHalfPlane.I
    have ne0 : (![1, 0] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    have ne1 : (![0, 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 1; simp at this
    have ne2 : (![1, 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    exact eq_or_eq_neg_of_rows α β
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne0) (vmul_ne_zero _ β ne0) (sub_eq_zero.mp z0))
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne1) (vmul_ne_zero _ β ne1) (sub_eq_zero.mp z1))
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne2) (vmul_ne_zero _ β ne2) (sub_eq_zero.mp z2))
  · have h1 : N = 1 := le_antisymm hN (Nat.pos_of_ne_zero (NeZero.ne N))
    subst h1
    left
    apply Units.ext
    ext i j
    exact Subsingleton.elim _ _

end GlobalTheory.FNSep
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RightRepU

lemma adj_repL (L l : ℕ) (j : Fin l) :
    (repL L l (some j)).adjugate = !![(1:ℤ), 0; -((L:ℤ) * ((j:ℕ):ℤ)), (l:ℤ)] := by
  simp [repL, Matrix.adjugate_fin_two_of]

lemma dvd_10 {L : ℕ} (γ : Gamma0 L) : (L:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 γ.2)

lemma not_dvd_00 {L l : ℕ} (hl : l.Prime) (hlL : l ∣ L) (γ : Gamma0 L) :
    ¬ (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 0 0 := by
  intro h
  have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))
  rw [Matrix.det_fin_two] at hdet
  have hc' : (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0 := dvd_trans (Int.natCast_dvd_natCast.2 hlL) (dvd_10 γ)
  have h1 : (l:ℤ) ∣ 1 := by
    rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right hc' _)
  have := Int.eq_one_of_dvd_one (by positivity) h1
  exact hl.one_lt.ne' (by exact_mod_cast this)

end GlobalTheory.EisM.RightRepU

namespace GlobalTheory.EisM.RightRepU

theorem rrep (L l : ℕ) (hl : l.Prime) (hlL : l ∣ L) (hL : 0 < L) :
    RRep L (DU L l) (fun j : Fin l => (repL L l (some j)).adjugate) := by
  haveI := Fact.mk hl
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hpr : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
  have hlpos : (0:ℤ) < l := by exact_mod_cast hl.pos
  simp only [RRep, adj_repL]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j, γ⟩ -
    have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.det_mul]
      rw [hdet, Matrix.det_fin_two_of]; ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)) (dvd_mul_of_dvd_right (dvd_10 γ) _)
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using not_dvd_00 hl hlL γ
  · rintro ⟨j, γ⟩ - ⟨j', γ'⟩ - h
    simp only at h
    have e := fun r s => congrArg (fun M : M2 => M r s) h
    have h00 := e 0 0
    have h01 := e 0 1
    have h10 := e 1 0
    have h11 := e 1 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    obtain ⟨c1, hc1⟩ := dvd_10 γ
    obtain ⟨c1', hc1'⟩ := dvd_10 γ'
    have hLz : (0:ℤ) < L := by exact_mod_cast hL
    have hk : (L:ℤ) * ((((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0) = (L:ℤ) * ((l:ℤ) * (c1' - c1)) := by
      rw [hc1, hc1', ← h00] at h10
      linear_combination h10
    have hk2 := mul_left_cancel₀ hLz.ne' hk
    have hdv : (l:ℤ) ∣ (((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0 := ⟨_, hk2⟩
    have hjj := (hpr.dvd_or_dvd hdv).resolve_right (not_dvd_00 hl hlL γ)
    have hj0 : ((j':ℕ):ℤ) - (j:ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hjj
      have := j.isLt; have := j'.isLt
      rw [abs_lt]; constructor <;> omega
    have hjeq : j = j' := Fin.ext (by omega)
    subst hjeq
    have h10' : ((γ : SL(2,ℤ)) : M2) 1 0 = ((γ' : SL(2,ℤ)) : M2) 1 0 := by
      rw [← h00] at h10
      exact mul_left_cancel₀ hlpos.ne' (by linear_combination h10)
    have h11' : ((γ : SL(2,ℤ)) : M2) 1 1 = ((γ' : SL(2,ℤ)) : M2) 1 1 := by
      rw [← h01] at h11
      exact mul_left_cancel₀ hlpos.ne' (by linear_combination h11)
    refine Prod.ext rfl (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ (fun r s => ?_)))
    fin_cases r <;> fin_cases s
    · exact h00
    · exact h01
    · exact h10'
    · exact h11'
  · rintro δ ⟨hdet, hc, ha⟩
    rw [Matrix.det_fin_two] at hdet
    obtain ⟨c1, hc1⟩ := hc
    obtain ⟨L1, hL1⟩ := hlL
    have hLl : (L:ℤ) = l * L1 := by rw [hL1]; push_cast; ring
    have hd : (l:ℤ) ∣ δ 1 1 := by
      have : (l:ℤ) ∣ δ 0 0 * δ 1 1 :=
        ⟨1 + L1 * c1 * δ 0 1, by linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * c1 * hLl⟩
      exact (hpr.dvd_or_dvd this).resolve_left ha
    obtain ⟨d1, hd1⟩ := hd
    have ha0 : ((δ 0 0 : ℤ) : ZMod l) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨x, hx⟩ : ∃ x : ZMod l, x = -(c1 : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹ := ⟨_, rfl⟩
    let j : Fin l := ⟨x.val, ZMod.val_lt x⟩
    have hj : (l:ℤ) ∣ c1 + ((j:ℕ):ℤ) * δ 0 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [j, ZMod.natCast_val, ZMod.cast_id', id]
      rw [hx, mul_assoc, inv_mul_cancel₀ ha0]; ring
    obtain ⟨m, hm⟩ := hj
    let M : M2 := !![δ 0 0, δ 0 1; (L:ℤ) * m, d1 + L1 * ((j:ℕ):ℤ) * δ 0 1]
    have hM : M.det = 1 := by
      rw [Matrix.det_fin_two_of]
      apply mul_left_cancel₀ hlpos.ne'
      linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * L * hm - ((j:ℕ):ℤ) * δ 0 0 * δ 0 1 * hLl - δ 0 0 * hd1
    let g : SL(2,ℤ) := ⟨M, hM⟩
    have hmem : g ∈ Gamma0 L := by
      rw [Gamma0_mem]; simp [g, M]
    refine ⟨(j, ⟨g, hmem⟩), trivial, ?_⟩
    ext r s
    fin_cases r <;> fin_cases s
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -(L:ℤ) * hm - hc1
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -hd1 - ((j:ℕ):ℤ) * δ 0 1 * hLl

end GlobalTheory.EisM.RightRepU
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma repL_det (L q : ℕ) (i : Option (Fin q)) : (repL L q i).det = q := by
  cases i <;> simp [repL, Matrix.det_fin_two_of]

lemma gamma0_lower_dvd {L : ℕ} (γ : Gamma0 L) : (L : ℤ) ∣ ((γ : SL(2, ℤ)) : M2) 1 0 := by
  have := Gamma0_mem.mp γ.2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast this)

lemma exists_kernel_param {K : Type*} [Field K] (a b c d l : K) (hl : l ≠ 0)
    (hdet : a * d - b * c = 0) (hbd : b ≠ 0 ∨ d ≠ 0) : ∃ u, a = l * u * b ∧ c = l * u * d := by
  by_cases hd : d = 0
  · have hb : b ≠ 0 := hbd.resolve_right (by simpa using hd)
    refine ⟨a / (l * b), by field_simp, ?_⟩
    subst hd
    have : b * c = 0 := by linear_combination -hdet
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hb
    · simp [h]
  · refine ⟨c / (l * d), ?_, by field_simp⟩
    field_simp
    linear_combination hdet

theorem repL_LRep : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repL L q) := by
  intro L q hq hqL
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqLZ : ¬ (q : ℤ) ∣ L := by exact_mod_cast hqL
  haveI := Fact.mk hq
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨γ, i⟩ -
    refine ⟨?_, ?_⟩
    · simp [Matrix.det_mul, repL_det]
    · have h := gamma0_lower_dvd γ
      cases i with
      | none => simpa [repL, Matrix.mul_apply, Fin.sum_univ_two] using h
      | some j =>
        simp only [repL, Matrix.mul_apply, Fin.sum_univ_two]
        simp
        exact dvd_add (dvd_mul_of_dvd_left h _) (Dvd.dvd.mul_left (dvd_mul_right _ _) _)
  · rintro ⟨γ, i⟩ - ⟨γ', i'⟩ - h
    dsimp only at h
    have hd := (γ : SL(2, ℤ)).2
    have hd' := (γ' : SL(2, ℤ)).2
    rw [Matrix.det_fin_two] at hd hd'
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    have e11 := congrFun (congrFun h 1) 1
    have hq0' : q ≠ 0 := hq.ne_zero
    have hq1 : ¬ (q : ℤ) ∣ 1 := hqZ.not_dvd_one
    rcases i with _ | j <;> rcases i' with _ | j' <;>
      simp [repL, Matrix.mul_apply, Fin.sum_univ_two, hq0'] at e00 e01 e10 e11
    · refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)) rfl
      fin_cases i <;> fin_cases j <;> simp <;> assumption
    · exact absurd (Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 * ((γ : SL(2, ℤ)) : M2) 1 1 -
          ((γ : SL(2, ℤ)) : M2) 0 1 * ((γ' : SL(2, ℤ)) : M2) 1 0)
        (by linear_combination hd' + ((γ' : SL(2, ℤ)) : M2) 0 0 * e11 - ((γ' : SL(2, ℤ)) : M2) 1 0 * e01)) hq1
    · exact absurd (Dvd.intro (((γ : SL(2, ℤ)) : M2) 0 0 * ((γ' : SL(2, ℤ)) : M2) 1 1 -
          ((γ' : SL(2, ℤ)) : M2) 0 1 * ((γ : SL(2, ℤ)) : M2) 1 0)
        (by linear_combination hd - ((γ : SL(2, ℤ)) : M2) 0 0 * e11 + ((γ : SL(2, ℤ)) : M2) 1 0 * e01)) hq1
    · have h0 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 0 1 :=
        Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 - ((γ : SL(2, ℤ)) : M2) 0 0)
          (by linear_combination -e00 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e01)
      have h1 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 1 1 :=
        Dvd.intro (((γ' : SL(2, ℤ)) : M2) 1 0 - ((γ : SL(2, ℤ)) : M2) 1 0)
          (by linear_combination -e10 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e11)
      have hjj : (q : ℤ) ∣ ((j : ℕ) - (j' : ℕ) : ℤ) := by
        by_contra hn
        have hLj : ¬ (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) := fun hh =>
          (hqZ.dvd_or_dvd hh).elim hqLZ hn
        have a0 := (hqZ.dvd_or_dvd h0).resolve_left hLj
        have a1 := (hqZ.dvd_or_dvd h1).resolve_left hLj
        apply hq1
        rw [← hd]
        exact (Dvd.dvd.mul_left a1 _).sub (Dvd.dvd.mul_right a0 _)
      have hj := j.isLt
      have hj' := j'.isLt
      have hz := Int.eq_zero_of_abs_lt_dvd hjj (abs_sub_lt_iff.mpr ⟨by omega, by omega⟩)
      have hjeq : j = j' := Fin.ext (by omega)
      subst hjeq
      refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i k => ?_)) rfl
      have f00 : ((γ : SL(2, ℤ)) : M2) 0 0 = ((γ' : SL(2, ℤ)) : M2) 0 0 :=
        mul_right_cancel₀ hq0 (by linear_combination e00 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e01)
      have f10 : ((γ : SL(2, ℤ)) : M2) 1 0 = ((γ' : SL(2, ℤ)) : M2) 1 0 :=
        mul_right_cancel₀ hq0 (by linear_combination e10 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e11)
      fin_cases i <;> fin_cases k <;> simp <;> assumption
  · rintro δ ⟨hdet, hL⟩
    rw [Matrix.det_fin_two] at hdet
    by_cases hbd : (q : ℤ) ∣ δ 0 1 ∧ (q : ℤ) ∣ δ 1 1
    · obtain ⟨⟨b', hb⟩, ⟨d', hd⟩⟩ := hbd
      have hdet1 : (!![δ 0 0, b'; δ 1 0, d'] : M2).det = 1 := by
        rw [Matrix.det_fin_two_of]
        apply mul_left_cancel₀ hq0
        rw [hb, hd] at hdet
        linear_combination hdet
      let g : SL(2, ℤ) := ⟨_, hdet1⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]
        have : ((δ 1 0 : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL
        simpa [g] using this
      refine ⟨(⟨g, hg⟩, none), trivial, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two, hb, hd] <;> ring
    · have hu : ∃ u : ZMod q, ((δ 0 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 0 1 : ℤ) : ZMod q) ∧
          ((δ 1 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 1 1 : ℤ) : ZMod q) := by
        apply exists_kernel_param
        · rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqL
        · have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
          simpa using this
        · by_contra hn
          push_neg at hn
          exact hbd ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.1,
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.2⟩
      obtain ⟨u, hu0, hu1⟩ := hu
      set j : Fin q := ⟨u.val, ZMod.val_lt u⟩ with hjdef
      have hju : (((j : ℕ) : ℤ) : ZMod q) = u := by simp [hjdef]
      obtain ⟨x, hx⟩ : (q : ℤ) ∣ δ 0 0 - L * (j : ℕ) * δ 0 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hju ⊢
        rw [hju, hu0]; ring
      obtain ⟨z, hz⟩ : (q : ℤ) ∣ δ 1 0 - L * (j : ℕ) * δ 1 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hju ⊢
        rw [hju, hu1]; ring
      have hcop : IsCoprime (L : ℤ) (q : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqL).symm
      have hLz : (L : ℤ) ∣ z := by
        apply hcop.dvd_of_dvd_mul_left
        rw [← hz]
        exact dvd_sub hL (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _)
      have hdet1 : (!![x, δ 0 1; z, δ 1 1] : M2).det = 1 := by
        rw [Matrix.det_fin_two_of]
        apply mul_left_cancel₀ hq0
        linear_combination -(δ 1 1) * hx + δ 0 1 * hz + hdet
      let g : SL(2, ℤ) := ⟨_, hdet1⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]
        have : ((z : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hLz
        simpa [g] using this
      refine ⟨(⟨g, hg⟩, some j), trivial, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hx | linear_combination -hz

end GlobalTheory.EisM
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_of_ne_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [FaithfulSMul G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ σ : G, σ ≠ 1 → Moves v ⊤ σ := by
  intro L _ v p hp hp0 hp1 G _ _ _ _ hinv ζ hζ hζfix hroot σ hσ
  obtain ⟨N, hNn, hNmem, i, hi, hNi⟩ := GlobalTheory.T.exists_normal_subgroup_not_moves_uniform_bound L v G hinv
  by_contra hmov
  have hσN : σ ∈ N := (hNmem σ).2 hmov
  have hfixN : ∀ τ ∈ N, ∀ x ∈ Fix L N, τ • x = x := fun τ hτ x hx => hx ⟨τ, hτ⟩
  have hdesc : ∀ τ : G, τ ∉ N → Moves v (Fix L N) τ := fun τ hτ =>
    GlobalTheory.T.movesIntegersAlmostUnitDistance_fixedSubfield L v G hinv N i hi hNi τ (by_contra fun h => hτ ((hNmem τ).2 h))
  have hsep : AlmostSep v N := GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers L v G hinv N hNn inferInstance hdesc
  have hF : ApproxRoot p v (Fix L N) := GlobalTheory.T.approxPthRoot_fixedSubfield_of_almostEtale L v p hp hp0 hp1 G hinv N inferInstance hsep hroot
  have hpg : IsPGroup p N := by
    intro τ
    set n := orderOf (τ : G) with hn
    have hn0 : n ≠ 0 := (orderOf_pos (τ : G)).ne'
    set k := n.factorization p
    refine ⟨k, ?_⟩
    have hcop : Nat.Coprime (n / p ^ k) p := (Nat.coprime_ordCompl hp hn0).symm
    have hτ' : ((τ : G) ^ (p ^ k)) ∈ N := N.pow_mem τ.2 _
    by_contra hne
    have hne' : (τ : G) ^ (p ^ k) ≠ 1 := by
      intro h; apply hne; ext; simpa using h
    have hl : ((τ : G) ^ (p ^ k)) ^ (n / p ^ k) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.ordProj_dvd n p), hn, pow_orderOf_eq_one]
    obtain ⟨y, hy⟩ : ∃ y : L, ((τ : G) ^ (p ^ k)) • y ≠ y := by
      by_contra h
      push_neg at h
      exact hne' (eq_of_smul_eq_smul (α := L) (fun y => by rw [h y, one_smul]))
    exact (hNmem _).1 hτ' (GlobalTheory.T.movesIntegersAlmostUnit_of_coprime_order L v p hp (Fix L N) hF hp0 hp1 G hinv _ (hfixN _ hτ') _ hcop hl ⟨y, hy⟩)
  haveI : Nontrivial N := ⟨⟨⟨σ, hσN⟩, 1, fun h => hσ (congrArg Subtype.val h)⟩⟩
  haveI : FaithfulSMul N L := ⟨fun {a b} h => Subtype.ext (eq_of_smul_eq_smul (α := L) h)⟩
  obtain ⟨σ₀, α, hα0, hσα, hαp⟩ := GlobalTheory.T.exists_lagrange_resolvent_of_pGroup_faithful L p hp N hpg ζ hζ (fun g => hζfix g)
  have hαF : α ^ p ∈ Fix L N := fun g => hαp g
  exact (hNmem _).1 σ₀.2 (GlobalTheory.T.kummer_automorphism_moves_integers_almost_unit L v p hp (Fix L N) hF hp0 hp1 G (σ₀ : G) (hfixN _ σ₀.2) ζ α hζ hα0 hαF hσα)

end GlobalTheory.AlmostEt
end

end

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_weierstrassP_family_separating_gl2ZMod : ∀ (N : ℕ) [NeZero N], ∃ c₁ c₂ : ℕ, ∀ α β : GL (Fin 2) (ZMod N), (fun τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ) = (fun τ => wp N (vmul ![1, 0] β) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] β) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] β) τ) → α = β ∨ α = -β := by
  first | exact @GlobalTheory.FNSep.sep_family | exact GlobalTheory.FNSep.sep_family | (intros; apply GlobalTheory.FNSep.sep_family <;> assumption)

end
end

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepLowerLevel : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repL L q) := by
  first | exact @GlobalTheory.EisM.repL_LRep | exact GlobalTheory.EisM.repL_LRep | (intros; apply GlobalTheory.EisM.repL_LRep <;> assumption)

end
end

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.isRightGamma0CosetDecomposition_heckeU : ∀ L l : ℕ, 0 < L → l.Prime → l ∣ L → RRep L (DU L l) (fun j : Fin l => (repL L l (some j)).adjugate) := by
  first | exact @GlobalTheory.EisM.RightRepU.rrep | exact GlobalTheory.EisM.RightRepU.rrep | (intros; apply GlobalTheory.EisM.RightRepU.rrep <;> assumption)

end
end
