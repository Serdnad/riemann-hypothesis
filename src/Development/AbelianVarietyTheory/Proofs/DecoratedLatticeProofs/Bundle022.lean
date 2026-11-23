module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem conj_embA_lowU {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (d : Fin c → kˣ)
    (C : Matrix (Fin c) n k) :
    embA n (GlobalTheory.SplitFlip.diagGL d) * lowU (diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) * C) *
      (embA n (GlobalTheory.SplitFlip.diagGL d))⁻¹ = lowU C := by
  apply Units.ext
  have hinv : ((embA n (GlobalTheory.SplitFlip.diagGL d))⁻¹ : GL (n ⊕ Fin c) k).val =
      fromBlocks 1 0 0 (diagonal fun i => (((d i)⁻¹ : kˣ) : k)) := by
    rw [← map_inv]; rfl
  rw [Units.val_mul, Units.val_mul, hinv]
  change fromBlocks 1 0 0 (diagonal fun i => (d i : k)) * fromBlocks 1 0 _ 1 * _ = fromBlocks 1 0 C 1
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp [← Matrix.mul_assoc, diagonal_mul_diagonal]

theorem rowE_mem_symLev_of_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ u : XIx (Fin κ) t j → k, u ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev j (c + 1 + 1) (by omega)).J := by
  intro k _ _ _ _ s κ S t _ _ hP j c H r hc u hu
  have hr : r < S.ρ := by have := S.odd; omega
  let o := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  let d : Fin (c + 1 + 1) → kˣ := fun i => S.ϖ ^ (i.val + 1)
  let C : Matrix (Fin (c + 1 + 1)) (XIx (Fin κ) t j) k := Matrix.of fun l x => if l.val + 1 = r + 1 then u x else 0
  let C' := diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) * C
  have hC' : ∀ l x, C' l x = if l.val = r then (((S.ϖ ^ (r + 1))⁻¹ : kˣ) : k) * u x else 0 := by
    intro l x
    simp only [C', C, d, diagonal_mul, of_apply, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h; rfl
    · simp
  have hint : ∀ l x, C' l x ∈ 𝒪[k] := by
    intro l x
    rw [hC']
    split_ifs
    · rw [Valuation.mem_integer_iff, map_mul]
      have h0 : 0 < valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by simp [zero_lt_iff]
      rw [Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_one₀ h0]
      exact hu x
    · exact zero_mem _
  have e1 : (typeFrame S.ϖ o).conj ((reGL o).symm (lowU C')) = rowE (c + 1 + 1) (r + 1) u := by
    rw [LatFrame.conj_apply]
    change embA _ (GlobalTheory.SplitFlip.diagGL d) * reGL o ((reGL o).symm (lowU C')) * (embA _ (GlobalTheory.SplitFlip.diagGL d))⁻¹ = _
    rw [MulEquiv.apply_symm_apply]
    exact conj_embA_lowU d C
  show (typeFrame S.ϖ o).conj.symm (rowE (c + 1 + 1) (r + 1) u) ∈ (S.P.iter t S.μ S.tame j).J
  rw [← e1, MulEquiv.symm_apply_apply, hP]
  have hfb : ∀ (M : Matrix (Fin (c + 1 + 1)) (XIx (Fin κ) t j) k), (∀ l x, M l x ∈ 𝒪[k]) →
      ∀ y z, (fromBlocks 1 0 M 1 : Matrix (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) y z ∈ 𝒪[k] := by
    intro M hM y z
    rcases y with y | y <;> rcases z with z | z
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp [zero_mem, one_mem]
    · simp [zero_mem]
    · simpa using hM y z
    · simp only [fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs <;> simp [zero_mem, one_mem]
  refine ⟨?_, ?_⟩
  · rw [mem_KO, ← map_inv]
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [reGL_symm_val, submatrix_apply]; exact hfb C' hint _ _
    · rw [reGL_symm_val, submatrix_apply]
      exact hfb (-C') (fun l x => by simpa using neg_mem (hint l x)) _ _
  · intro a b hnf
    suffices h : (lowU C').val (o a) (o b) = (1 : Matrix _ _ k) a b by
      rw [reGL_symm_val, submatrix_apply, h, sub_self, map_zero]; exact zero_lt_one
    have h1 : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t j) (Ix (Fin κ ⊕ Fin (s + 1)) t j) k) a b =
        (1 : Matrix (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) (o a) (o b) := by
      simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
    rw [h1]
    change (fromBlocks 1 0 C' 1 : Matrix (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) (o a) (o b) = _
    rcases hoa : o a with y | l <;> rcases hob : o b with z | z
    · simp [Matrix.one_apply]
    · simp [one_apply]
    · rw [fromBlocks_apply₂₁, Matrix.one_apply, if_neg (by simp), hC']
      split_ifs with hl
      · exfalso
        have ha : a = Sum.inl (Sum.inr ⟨l.val, by omega⟩) :=
          o.injective (by rw [hoa]; exact (standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (by omega) l).symm)
        subst ha
        rcases z with (z | z) | z
        · have hb : b = Sum.inl (Sum.inl z) :=
            o.injective (by rw [hob]; exact (stdOrd_eps (Fin κ) t j (c + 1 + 1) (by omega) z).symm)
          subst hb
          exact hnf (by simp only [FreeIx, FreeTop]; omega)
        · have hb : b = Sum.inl (Sum.inr ⟨c + 1 + 1 + z.val, by omega⟩) :=
            o.injective (by rw [hob]; exact (stdOrd_f (Fin κ) t j (c + 1 + 1) (by omega) z).symm)
          subst hb
          exact hnf (by simp only [FreeIx, FreeTop, Fin.mk_lt_mk]; omega)
        · have hb : b = Sum.inr z :=
            o.injective (by rw [hob]; exact (stdOrd_d (Fin κ) t j (c + 1 + 1) (by omega) z).symm)
          subst hb
          exact hnf trivial
      · rfl
    · simp [Matrix.one_apply]

end GlobalTheory.SymChain
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain.ExchangeCol

section SlopeTestRemainingChoices
variable {k : Type} [Field k] {ι ι' n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

theorem coords_typeFrame_apply (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (typeFrame ϖ o).coords (typeFrame ϖ o') x a b =
      Sum.elim (fun _ => 1) (fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) (o a) * x (o a) (o' b) *
        Sum.elim (fun _ => 1) (fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) (o' b) := by
  have e : ((typeFrame ϖ o).bas⁻¹).val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change fromBlocks 1 0 0 (diagonal _) * _ = _
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have e' : (typeFrame ϖ o').bas.val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) := rfl
  unfold LatFrame.coords
  rw [e, e', ← diagonal_one, ← diagonal_one, fromBlocks_diagonal, fromBlocks_diagonal, submatrix_apply,
    mul_diagonal, diagonal_mul]
  rfl

theorem coords_add (F : LatFrame k ι (n ⊕ Fin c)) (F' : LatFrame k ι' (n' ⊕ Fin c'))
    (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) :
    F.coords F' (x + y) = F.coords F' x + F.coords F' y := by
  unfold LatFrame.coords
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

end SlopeTestRemainingChoices

theorem phi_add_col (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t)
    (j c : ℕ) (H : j + c = s) (q : Fin c) (hρ : q.val + 1 ≤ S.ρ) (hc : q.val + 2 ≤ c)
    (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k)
    (hx : ∀ r, x (Sum.inl r) (Sum.inr q.succ) = 0) (w : XIx (Fin κ) t (j + 1) → k) :
    (S.T t).Phi j c H (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0) =
      if ∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1 then (S.T t).Phi j c H x else 0 := by
  have H1 : j + 1 + c = s + 1 := by omega
  have H2 : j + (c + 1) = s + 1 := by omega
  have hPhi : ∀ z, (S.T t).Phi j c H z = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ (stdOrd (Fin κ) t (j + 1) c H1)).coords
        (typeFrame S.ϖ (stdOrd (Fin κ) t j (c + 1) H2)) z).submatrix (ixSucc _ t j) id) := fun _ => rfl
  split_ifs with hw
  · rw [hPhi, hPhi, coords_add, Matrix.submatrix_add, Pi.add_apply, Pi.add_apply]
    refine (S.P.iter t S.μ S.tame j).Phi_add (S.tame _) _ fun a b => ?_
    rw [submatrix_apply, coords_typeFrame_apply, of_apply]
    split_ifs with hb
    · rw [hb]
      rcases stdOrd (Fin κ) t (j + 1) c H1 (ixSucc _ t j a) with r | r
      · simpa [mul_comm] using hw r
      · simp
    · simp
  · by_contra h
    rw [← Ne, hPhi, TypeDatum.Phi_ne_zero_iff] at h
    obtain ⟨⟨g, hg, e⟩, hb⟩ := h
    refine hw fun r => ?_
    obtain ⟨a, ha⟩ := ((ixSucc _ t j).trans (stdOrd (Fin κ) t (j + 1) c H1)).surjective (.inl r)
    simp only [Equiv.trans_apply] at ha
    have hq : q.succ.val < s + 1 := by have := q.succ.2; omega
    have hcol : stdOrd (Fin κ) t j (c + 1) H2 (.inl (.inr ⟨q.succ.val, hq⟩)) = .inr q.succ :=
      standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1) H2 q.succ
    have key : (((typeFrame S.ϖ (stdOrd (Fin κ) t (j + 1) c H1)).coords
        (typeFrame S.ϖ (stdOrd (Fin κ) t j (c + 1) H2))
        (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0)).submatrix (ixSucc _ t j) id)
        a (.inl (.inr ⟨q.succ.val, hq⟩)) = ((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r := by
      rw [submatrix_apply, coords_typeFrame_apply, id, ha, hcol]
      simp [hx, mul_comm]
    rw [← key]
    rcases a with a | a
    · have hne : ¬ FreeIx S.ρ a (.inl (.inr ⟨q.succ.val, hq⟩)) ∧ a ≠ .inl (.inr ⟨q.succ.val, hq⟩) := by
        rcases a with (a | a) | a
        · simp only [FreeIx, FreeTop, Fin.val_succ]
          exact ⟨by omega, by simp⟩
        · have hac : c ≤ a.val := by
            by_contra hlt
            have := standardOrderExtendedBasis_apply_low_block (Fin κ) t (j + 1) c H1 ⟨a.val, by omega⟩
            exact Sum.inr_ne_inl (this.symm.trans ha)
          simp only [FreeIx, FreeTop, Fin.lt_def, Fin.val_succ, ne_eq, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff]
          omega
        · simp [FreeIx]
      have := ((hP j g).1 hg).2 a _ hne.1
      rw [e, Matrix.one_apply_ne hne.2, sub_zero] at this
      exact this
    · exact hb a _

end GlobalTheory.SymChain.ExchangeCol
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.PrImage

section Plain
variable {k : Type*} [Field k] {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}

variable (k n c) in
def fixX : Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {v | ∀ r x, v.val r (.inl x) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inl x)}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro v w hv hw r x
    have : (v.val * w.val) r (.inl x) = (v.val * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) := by
      simp only [Matrix.mul_apply, hw _ x]
    rw [Units.val_mul, this, Matrix.mul_one, hv]
  inv_mem' := by
    intro v hv r x
    have : ((v⁻¹).val * v.val) r (.inl x) = ((v⁻¹).val * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) := by
      simp only [Matrix.mul_apply, hv _ x]
    rw [Matrix.mul_one, Units.inv_mul] at this
    exact this.symm

theorem N_le_fixX : N k n c 1 ≤ fixX k n c := by
  refine (Subgroup.closure_le _).2 fun g hg r x => hg r (.inl x) ?_
  rcases r with r | r <;> simp [RootEx.lev]

theorem embA_mem_fixX (D : GL (Fin c) k) : embA n D ∈ fixX k n c := by
  intro r x
  change (fromBlocks 1 0 0 D.val : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inl x) = _
  rcases r with r | r <;> simp [Matrix.one_apply]

theorem embX_mul_embA (g : GL n k) (D : GL (Fin c) k) : embX c g * embA n D = embA n D * embX c g := by
  refine Units.ext ?_
  change (fromBlocks g.val 0 0 1 * fromBlocks 1 0 0 D.val : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) =
    fromBlocks 1 0 0 D.val * fromBlocks g.val 0 0 1
  simp [fromBlocks_multiply]

theorem mul_embX_inl {w : GL (n ⊕ Fin c) k} (hw : w ∈ fixX k n c) (g : GL n k) (r : n ⊕ Fin c) (x : n) :
    (w * embX c g).val r (.inl x) = (embX c g).val r (.inl x) := by
  have : (w.val * (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) =
      ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k))
        r (.inl x) := by
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, hw r, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero]
  rw [Matrix.one_mul] at this
  exact this

theorem embX_inr (g : GL n k) (r : n ⊕ Fin c) (i : Fin c) :
    (embX c g).val r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) := by
  change (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) = _
  rcases r with r | r <;> simp [Matrix.one_apply]

theorem conj_symm_apply (F : LatFrame k ι (n ⊕ Fin c)) (y : GL (n ⊕ Fin c) k) :
    F.conj.symm y = (reGL F.ord).symm (F.bas⁻¹ * y * F.bas) := by
  rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply]; simp [mul_assoc]

theorem entry_cases (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) {w : GL (n ⊕ Fin c) k} (hw : w ∈ fixX k n c) (g : GL n k)
    (a b : ι) :
    ((typeFrame ϖ o).conj.symm (embX c g)).val a b = ((typeFrame ϖ o).conj.symm (w * embX c g)).val a b ∨
      ((typeFrame ϖ o).conj.symm (embX c g)).val a b = (1 : Matrix ι ι k) a b := by
  obtain ⟨D, hD⟩ : ∃ D, (typeFrame ϖ o).bas = embA n D := ⟨_, rfl⟩
  have ho : (typeFrame ϖ o).ord = o := rfl
  have e1 : (embA n D)⁻¹ * embX c g * embA n D = embX c g := by
    rw [mul_assoc, embX_mul_embA, inv_mul_cancel_left]
  have e2 : (embA n D)⁻¹ * (w * embX c g) * embA n D = ((embA n D)⁻¹ * w * embA n D) * embX c g := by
    simp only [mul_assoc, embX_mul_embA]
  have hw' : (embA n D)⁻¹ * w * embA n D ∈ fixX k n c :=
    mul_mem (mul_mem (inv_mem (embA_mem_fixX D)) hw) (embA_mem_fixX D)
  rw [conj_symm_apply, conj_symm_apply, hD, ho, e1, e2, reGL_symm_val, reGL_symm_val, submatrix_apply,
    submatrix_apply, ← submatrix_one_equiv o, submatrix_apply]
  rcases o b with x | i
  · exact Or.inl (mul_embX_inl hw' g _ x).symm
  · exact Or.inr (embX_inr g _ i)

end Plain

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}

theorem prX_eq_comap (P : Level (GL ι k)) (Fr : ι → ι → Prop)
    (hP : ∀ g, g ∈ P.J ↔ g ∈ KO k ι ∧ ∀ a b, ¬ Fr a b → valuation k (g.val a b - (1 : Matrix ι ι k) a b) < 1)
    (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) :
    prX (Cgrp (P.map (typeFrame ϖ o).conj).J 1) = (P.map (typeFrame ϖ o).conj).J.comap (embX c) := by
  have key : ∀ g : GL n k, g ∈ prX (Cgrp (P.map (typeFrame ϖ o).conj).J 1) →
      IntM ((typeFrame ϖ o).conj.symm (embX c g)).val ∧ ∀ a b, ¬ Fr a b →
        valuation k (((typeFrame ϖ o).conj.symm (embX c g)).val a b - (1 : Matrix ι ι k) a b) < 1 := by
    rintro g ⟨u, hu, hg⟩
    have h := (mem_Cgrp.1 hg).2
    rw [inv_one, one_mul, mul_one, Level.mem_map, hP] at h
    refine ⟨fun a b => ?_, fun a b hab => ?_⟩
    · rcases entry_cases ϖ o (N_le_fixX hu) g a b with e | e <;> rw [e]
      · exact intM_of_mem_KO h.1 a b
      · exact intM_one a b
    · rcases entry_cases ϖ o (N_le_fixX hu) g a b with e | e <;> rw [e]
      · exact h.2 a b hab
      · simp
  ext g
  rw [Subgroup.mem_comap]
  refine ⟨fun hg => ?_, fun hg => ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, by simpa using hg⟩⟩⟩
  · rw [Level.mem_map, hP]
    refine ⟨mem_KO.2 ⟨(key g hg).1, ?_⟩, (key g hg).2⟩
    rw [← map_inv, ← map_inv]
    exact (key g⁻¹ (inv_mem hg)).1
  · rw [one_mul]
    exact Subgroup.mem_sup_left ⟨g, rfl⟩

theorem prLevel_of_pattern (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (h : S.Pattern t) : S.PrLevel t :=
  fun j c H => prX_eq_comap (S.P.iter t S.μ S.tame j).toLevel (FreeIx S.ρ) (h j) S.ϖ (stdOrd (Fin κ) t j c H)

end GlobalTheory.SymChain.PrImage
end
end

section

open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.LevZeroGen
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

def xZero (κ t : Type) : κ ≃ XIx κ t 0 := (Equiv.sumEmpty κ (Fin 0)).symm.trans (Equiv.sumEmpty (κ ⊕ Fin 0) (Fin 0 × t)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def upZero : GL (Fin κ ⊕ Fin (s + 1)) k ≃* GL (XIx (Fin κ) t 0 ⊕ Fin (s + 1)) k :=
  (reGL (ixZero (Fin κ ⊕ Fin (s + 1)) t)).trans (typeFrame S.ϖ (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _))).conj

theorem upZero_apply (x : GL (Fin κ ⊕ Fin (s + 1)) k) : upZero S t x =
    (S.T t).bas 0 (s + 1) (Nat.zero_add _) *
      reGL (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)) (reGL (ixZero (Fin κ ⊕ Fin (s + 1)) t) x) *
      ((S.T t).bas 0 (s + 1) (Nat.zero_add _))⁻¹ := rfl


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {s κ : ℕ} (S : _root_.GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] in
theorem _root_.GlobalTheory.LevZeroGen.upZero_mem_lev (x : GL (Fin κ ⊕ Fin (s + 1)) k) :
    _root_.GlobalTheory.LevZeroGen.upZero S t x ∈
        ((S.T t).lev 0 (s + 1)
          (Nat.zero_add _)).J ↔
      x ∈ S.P.J := by
  show _ ∈ (_root_.GlobalTheory.StepData.Level.map _ _).J ↔ _
  rw [_root_.GlobalTheory.StepData.Level.mem_map, _root_.GlobalTheory.LevZeroGen.upZero,
    MulEquiv.trans_apply]
  erw [MulEquiv.symm_apply_apply]
  rw [_root_.GlobalTheory.StepData.TypeDatum.iter_zero]
  unfold _root_.GlobalTheory.StepData.TypeDatum.reindex
  show _ ∈ (_root_.GlobalTheory.StepData.Level.map _ _).J ↔ _
  rw [_root_.GlobalTheory.StepData.Level.mem_map, MulEquiv.symm_apply_apply]

end GlobalTheory.LevZeroGen
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChainSupport

theorem phi_support_periodic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ)
      (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + c = s)
      (x z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k),
      ((S.T t).Phi j c H x ≠ 0 →
        IntM (((embA (XIx (Fin κ) t (j + 1))
          (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val :
            Matrix _ _ k) * x * (embA (XIx (Fin κ) t j)
          (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val)) ∧
      (MaxM (((embA (XIx (Fin κ) t (j + 1))
          (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val :
            Matrix _ _ k) * z * (embA (XIx (Fin κ) t j)
          (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val) →
        (S.T t).Phi j c H (x + z) = (S.T t).Phi j c H x) := by
  intro k _ _ _ _ s κ S t _ _ j c H x z
  set o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  set o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  set F := typeFrame (k := k) S.ϖ o
  set F' := typeFrame (k := k) S.ϖ o'
  have hPhi : ∀ y, (S.T t).Phi j c H y = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((F.coords F' y).submatrix (ixSucc _ t j) id) := fun y => rfl
  constructor
  · intro hx i l
    rw [hPhi] at hx
    have := TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm i)) (o'.symm l)
    simpa [LatFrame.coords, F, F', typeFrame] using this
  · intro hz
    rw [hPhi, hPhi]
    have e : F.coords F' (x + z) = F.coords F' x + F.coords F' z := by
      unfold LatFrame.coords; rw [Matrix.mul_add, Matrix.add_mul]; rfl
    rw [e]
    exact TypeDatum.Phi_add _ (S.tame _) _ (y := (F.coords F' z).submatrix (ixSucc _ t j) id) fun _ _ => hz _ _

end GlobalTheory.SymChainSupport
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricLevelChain_phi_support_periodic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + c = s) (x z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), ((S.T t).Phi j c H x ≠ 0 → IntM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * x * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val)) ∧ (MaxM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * z * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val) → (S.T t).Phi j c H (x + z) = (S.T t).Phi j c H x) := by
  intro k _ _ _ _ s κ S t _ _ j c H x z
  set o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  set o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  set F := typeFrame (k := k) S.ϖ o
  set F' := typeFrame (k := k) S.ϖ o'
  have hPhi : ∀ y, (S.T t).Phi j c H y = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((F.coords F' y).submatrix (ixSucc _ t j) id) := fun y => rfl
  constructor
  · intro hx i l
    rw [hPhi] at hx
    have := TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm i)) (o'.symm l)
    simpa [LatFrame.coords, F, F', typeFrame] using this
  · intro hz
    rw [hPhi, hPhi]
    have e : F.coords F' (x + z) = F.coords F' x + F.coords F' z := by
      unfold LatFrame.coords; rw [Matrix.mul_add, Matrix.add_mul]; rfl
    rw [e]
    exact TypeDatum.Phi_add _ (S.tame _) _ (y := (F.coords F' z).submatrix (ixSucc _ t j) id) fun _ _ => hz _ _
end
