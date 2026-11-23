module

public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.ChainEmbInj
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.TieFPowMulFree
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section lat2
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

theorem wv_ne_xi (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : wv D i c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [wv, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  have h1 := congrArg Fin.val h.1
  rw [finPos_pos_val hB, Fin.val_last] at h1
  have := pos_succ_lt hB i
  omega

theorem ev_ne_xi (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : ev D i c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [ev, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  have h1 := congrArg Fin.val h.1
  rw [finPos_succ_val hB, Fin.val_last] at h1
  have := pos_succ_lt hB i
  omega

theorem wU_ne_xi (c d : Fin r) : wU D c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [wU, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact (Fin.castSucc_lt_last _).ne h.1

theorem yz_pol {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ Pol p r LL :=
  (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).1).1

theorem yz_y {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ Y p (r := r) LL J M :=
  (Submodule.mem_inf.1 hy).1

theorem yz_int {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ IntPol p (Fin N × Fin r) :=
  (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).2).2

theorem yz_mk {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (h1 : y ∈ Y p (r := r) LL J M) (h2 : y ∈ IntPol p (Fin N × Fin r)) :
    y ∈ YZ p (r := r) LL J M :=
  Submodule.mem_inf.2 ⟨h1, Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 h1).1, h2⟩⟩

omit [NeZero r] in
theorem biHom_span {r' : ℕ} {w e : Fin r' → BVar N r D.T.t} {a b : ℕ} {S : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])}
    (h : ∀ x ∈ S, BiHom w e a b x) : ∀ x ∈ Submodule.span ℤ_[p] S, BiHom w e a b x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hxS => exact h x hxS
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h' | h'
    · exact hx m h'
    · exact hy m h'
  | smul a x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)

theorem biHom_tie (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    ∀ x ∈ Lat p D (r := r) j jp, BiHom (wv D i) (ev D i) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i)))
      ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1))) x := by
  intro x hx
  refine biHom_span (S := {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}) ?_ x hx
  rintro _ ⟨y, hy, g, hg, rfl⟩ m hm
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_gen (p := p) (D := D) (hm := hm)
  have hdeg : MultiDeg (D.lettersAt j jp) m1 :=
    ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 (yz_pol hy)) hm1
  have hxi := (xi_supp (p := p) (D := D) (hg := hg) (hm2 := hm2))
  constructor
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (wv D i c) = m1 (D.letterAt (D.T.pos i), c) := fun c => by
      rw [wv_chain (hB := hB), Finsupp.mapDomain_apply_of_injective (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (wv D i c) = 0 := fun c => hxi.1 _ (fun d => wv_ne_xi hB i c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (ev D i c) = m1 (D.letterAt (D.T.pos i + 1), c) := fun c => by
      rw [ev_chain (hB := hB), Finsupp.mapDomain_apply_of_injective (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (ev D i c) = 0 := fun c => hxi.1 _ (fun d => ev_ne_xi hB i c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _

theorem biHom_plus (j : Fin D.T.t → ℕ) (jp : ℕ) :
    ∀ x ∈ Lat p D (r := r) j jp, BiHom (wU D) (xiVar N r D.T.t) ((D.lettersAt j jp).deg D.uPos) (D.B - jp) x := by
  intro x hx
  refine biHom_span (S := {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}) ?_ x hx
  rintro _ ⟨y, hy, g, hg, rfl⟩ m hm
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_gen (p := p) (D := D) (hm := hm)
  have hdeg : MultiDeg (D.lettersAt j jp) m1 :=
    ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 (yz_pol hy)) hm1
  have hxi := (xi_supp (p := p) (D := D) (hg := hg) (hm2 := hm2))
  constructor
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (wU D c) = m1 (D.uPos, c) := fun c => by
      show Finsupp.mapDomain (chainEmb N r D.T.t) m1 (chainEmb N r D.T.t (D.uPos, c)) = _
      rw [Finsupp.mapDomain_apply_of_injective (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (wU D c) = 0 := fun c => hxi.1 _ (fun d => wU_ne_xi c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (xiVar N r D.T.t c) = 0 := fun c =>
      Finsupp.mapDomain_notin_range _ _ (xi_notin (D := D) c)
    simp only [e1, Finset.sum_const_zero, zero_add]
    exact hxi.2

end lat2

end Formalism.InvariantFactorPaths.KP.LL
end

section

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

def PairStep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (r : ℕ) (w e : Fin r → σ) (zv sv : σ), 1 ≤ r → (∀ c, w c ≠ zv ∧ e c ≠ zv) →
    ∀ (o n z L u : ℕ) (Λ : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])),
      (∀ l, ∀ x ∈ Λ l, ∀ m, min (o - l) (n - l) < m → (tieF w e ^ m) x = 0) →
      (∀ l m, m ≤ min o n → ∀ x ∈ Λ l,
        (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF w e ^ m) x) ∈ Λ (l + m)) →
      r * L + Nat.log p (o + n + r + z) ≤ u →
      ∀ l ≤ min o n, ∀ x ∈ Λ l,
        ((p : ℚ_[p]) ^ u • (ehP w e zv sv ^ l * (X zv ^ z * x)) ∈ Submodule.span ℤ_[p]
          {v | ∃ l' ≤ min o n, ∃ x' ∈ Λ l', v = ehP w e zv sv ^ l' * tieP w e zv sv (o - l') (n - l') z x'}) ∧
        ((p : ℚ_[p]) ^ u • (ehP w e zv sv ^ l * tieP w e zv sv (o - l) (n - l) z x) ∈ Submodule.span ℤ_[p]
          {v | ∃ l' ≤ min o n, ∃ x' ∈ Λ l', v = ehP w e zv sv ^ l' * (X zv ^ z * x')})

section block
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)

def HypJoin : Prop :=
  ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    Formalism.GM.tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y ∈
      Y p (r := r) (D.lettersAt (Function.update j i (j i + 1)) jp) D.T.J D.T.thr

def HypU : Prop :=
  ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (c : Fin r), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    pderiv (D.uPos, c) y ∈ Y p (r := r) (D.lettersAt j (jp + 1)) D.T.J D.T.thr

noncomputable def midGen (k : ℕ) (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus *
    PL p D ((List.finRange D.T.t).drop k) j jp x

noncomputable def Mid (k : ℕ) : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {v | ∃ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp ∧ ∃ x ∈ Lat p D (r := r) j jp,
    v = midGen p D k j jp x}

noncomputable def MidP : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {v | ∃ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp ∧ ∃ x ∈ Lat p D (r := r) j jp,
    v = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
      Pplus p D jp (PL p D (List.finRange D.T.t) j jp x)}

end block

def LatPlus : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → HypU p (r := r) D →
    ∀ (j : Fin D.T.t → ℕ) (jp m L : ℕ), Nat.log p m ≤ L → ∀ x ∈ Lat p D (r := r) j jp,
      (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF (wU D) (xiVar N r D.T.t) ^ m) x) ∈
        Lat p D (r := r) j (jp + m)

def LatTie : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → HypJoin p (r := r) D →
    ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) (m L : ℕ), Nat.log p m ≤ L → ∀ x ∈ Lat p D (r := r) j jp,
      (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF (wv D i) (ev D i) ^ m) x) ∈
        Lat p D (r := r) (j + Pi.single i m) jp

def PLLin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ),
    (∃ T : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p],
      ∀ x, T x = PL p D L j jp x) ∧
    ∃ T : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p],
      ∀ x, T x = Pplus p D jp x

def CommPL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK →
    ∀ (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp m : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
      (∀ k : Fin D.T.t, k ∉ L →
        (tieF (wv D k) (ev D k) ^ m) (PL p D L j jp x) = PL p D L j jp ((tieF (wv D k) (ev D k) ^ m) x)) ∧
      (tieF (wU D) (xiVar N r D.T.t) ^ m) (PL p D L j jp x) =
        PL p D L j jp ((tieF (wU D) (xiVar N r D.T.t) ^ m) x)

def ParamPL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK →
    ∀ (L : List (Fin D.T.t)) (j j' : Fin D.T.t → ℕ) (jp jp' : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
      (∀ i ∈ L, j i = j' i) → PL p D L j jp x = PL p D L j' jp' x

def MidTop : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), Mid p (r := r) D D.T.t = D.SSZ p (r := r)

def MidPEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), MidP p (r := r) D = D.PSZ p (r := r)

def JoinCondition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a u : ℕ), D.BlockOK → 1 ≤ r →
    (∀ x, D.LL.deg x ≤ 2 * a) → (∀ i, D.T.z i ≤ 2 * a) → HypJoin p (r := r) D →
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u → ∀ k < D.T.t,
      (∀ v ∈ Mid p (r := r) D (k + 1), (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D k) ∧
      (∀ v ∈ Mid p (r := r) D k, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D (k + 1))

def PlusCondition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a u : ℕ), D.BlockOK → 1 ≤ r →
    (∀ x, D.LL.deg x ≤ 2 * a) → D.B ≤ 2 * a → D.zPlus ≤ 2 * a → HypU p (r := r) D →
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u →
      (∀ v ∈ Mid p (r := r) D 0, (p : ℚ_[p]) ^ u • v ∈ MidP p (r := r) D) ∧
      (∀ v ∈ MidP p (r := r) D, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D 0)

end Formalism.InvariantFactorPaths.KP.LL
end
