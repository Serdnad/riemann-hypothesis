module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetModuleInStagesRefinedBlocks
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZpowMulMemPow
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle058
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle059
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.PEquiv
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Basic.PEquiv

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.CuspMax

theorem subsingleton_jacquet_of_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) {N N' : Subgroup G} (g : G) (h : ∀ u ∈ N, g * u * g⁻¹ ∈ N')
    (hN : Subsingleton (Jacquet π N)) : Subsingleton (Jacquet π N') := by
  have h1 : twKer π N 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 hN
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)
  have h2 : twKer π N 1 ≤ (twKer π N' 1).comap (π g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    refine Submodule.subset_span ⟨⟨_, h u u.2⟩, π g w, ?_⟩
    simp [← Module.End.mul_apply, ← map_mul]
  have h3 : π g⁻¹ v ∈ twKer π N 1 := h1 ▸ Submodule.mem_top
  have h4 : π g (π g⁻¹ v) ∈ twKer π N' 1 := h2 h3
  simpa [← Module.End.mul_apply, ← map_mul] using h4

variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]

theorem mem_unipRad_iff_entries {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  apply GlobalTheory.JacStagesProof.mem_unipRad_iff_entries' <;> assumption

theorem unipRad_ne_bot_iff [Nontrivial R] {e : (Σ a, m a) ≃ n} :
    unipRad R e ≠ ⊥ ↔ ∃ i j, blk e i < blk e j := by
  constructor
  · intro h
    by_contra hc
    refine h ((Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_)
    ext i j
    exact mem_unipRad_iff_entries.1 hu i j fun hij => hc ⟨i, j, hij⟩
  · rintro ⟨i, j, hij⟩ hb
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    let u : GL n R := ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp,
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp⟩
    have hu : u ∈ unipRad R e := mem_unipRad_iff_entries.2 fun a b hab => by
      show Matrix.transvection i j (1 : R) a b = _
      rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact hab hij
    rw [hb, Subgroup.mem_bot] at hu
    have : Matrix.transvection i j (1 : R) i j = (1 : Matrix n n R) i j :=
      congrArg (fun g : GL n R => (g : Matrix n n R) i j) hu
    simp [Matrix.transvection] at this

theorem subsingleton_jacquet_of_perm {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n R) V) {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n} (σ : Equiv.Perm n)
    (h : ∀ i j, blk e (σ i) < blk e (σ j) → blk e' i < blk e' j)
    (hN : Subsingleton (Jacquet π (unipRad R e))) : Subsingleton (Jacquet π (unipRad R e')) := by
  let g : GL n R := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
  refine subsingleton_jacquet_of_conj π g (fun u hu => ?_) hN
  refine mem_unipRad_iff_entries.2 fun i j hij => ?_
  show (σ.toPEquiv.toMatrix * (u : Matrix n n R) * σ.symm.toPEquiv.toMatrix : Matrix n n R) i j = _
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  simp only [Matrix.submatrix_apply, id, Equiv.symm_symm]
  rw [mem_unipRad_iff_entries.1 hu _ _ fun hh => hij (h i j hh)]
  simp [Matrix.one_apply]

theorem isCuspidal_iff_maximal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal π ↔ IsSmooth π ∧ ∀ (r t : ℕ) (h : r + t = N), 0 < r → 0 < t →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h)))) := by
  refine and_congr_right fun _ => ⟨fun H r t h hr ht => ?_, fun H s d e he => ?_⟩
  · let f : Fin N → Fin 2 := fun i => if blk (two (stdSum h)) i then 1 else 0
    let e : (Σ a : Fin 2, Fin (Fintype.card {i // f i = a})) ≃ Fin N :=
      (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // f i = a}).symm).trans
        (Equiv.sigmaFiberEquiv f)
    have hb : ∀ i, blk e i = f i := fun i => rfl
    have hlt : ∀ i j, blk e i < blk e j ↔ blk (two (stdSum h)) i < blk (two (stdSum h)) j := by
      intro i j
      rw [hb, hb]
      simp only [f]
      cases blk (two (stdSum h)) i <;> cases blk (two (stdSum h)) j <;> decide
    refine subsingleton_jacquet_of_perm π (e := e) 1 (fun i j hij => (hlt i j).1 hij)
      (H 2 _ e (unipRad_ne_bot_iff.2 ⟨two (stdSum h) ⟨false, ⟨0, hr⟩⟩, two (stdSum h) ⟨true, ⟨0, ht⟩⟩,
        (hlt _ _).2 ?_⟩))
    rw [blk_apply, blk_apply]
    decide
  · obtain ⟨i₀, j₀, hij⟩ := unipRad_ne_bot_iff.1 he
    let p : Fin N → Prop := fun i => blk e i ≤ blk e i₀
    have hsum : Fintype.card {i // p i} + Fintype.card {i // ¬ p i} = N := by
      rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl p), Fintype.card_fin]
    let τ : Fin (Fintype.card {i // p i}) ⊕ Fin (Fintype.card {i // ¬ p i}) ≃ Fin N :=
      (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl p)
    refine subsingleton_jacquet_of_perm π (τ.symm.trans (stdSum hsum)) (fun i j hh => ?_)
      (H _ _ hsum (Fintype.card_pos_iff.2 ⟨⟨i₀, le_rfl⟩⟩) (Fintype.card_pos_iff.2 ⟨⟨j₀, hij.not_ge⟩⟩))
    obtain ⟨i, rfl⟩ := τ.surjective i
    obtain ⟨j, rfl⟩ := τ.surjective j
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hh
    rcases i with i | i <;> rcases j with j | j
    · rw [← two_false, ← two_false, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
    · have h1 : p (τ (.inl i)) := ((Fintype.equivFin {i // p i}).symm i).2
      have h2 : ¬ p (τ (.inr j)) := ((Fintype.equivFin {i // ¬ p i}).symm j).2
      exact lt_of_le_of_lt h1 (not_le.1 h2)
    · rw [← two_false, ← two_true, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
    · rw [← two_true, ← two_true, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)

end GlobalTheory.SmGL.CuspMax
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

variable {k : Type} [Field k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
theorem aff_low (x₀ : Matrix n n' k) (y) (w : n' → k) (s : k) :
    affPt (c := c + 1) 1 x₀ y *ᵥ Sum.elim w (Pi.single 0 s) = Sum.elim (x₀ *ᵥ w) (Pi.single 0 s) := by
  ext (r | l)
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, affPt, basePt, Free, Pi.single_apply]
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, affPt, basePt, Free, Pi.single_apply]

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
theorem aff_row (x₀ : Matrix n n' k) (y) (w : n' → k) (i : Fin (c + 1)) (s : k) (l : Fin c) :
    (affPt (c := c) 1 x₀ y *ᵥ Sum.elim w (Pi.single i s)) (.inr l) = affPt 1 x₀ y (.inr l) (.inr i) * s := by
  have : ∀ r, affPt (c := c) 1 x₀ y (.inr l) (.inl r) = 0 := fun r => by simp [affPt, basePt, Free]
  simp [mulVec, dotProduct, Fintype.sum_sum_type, this, Pi.single_apply]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem aff_diag (x₀ : Matrix n n' k) (y) (i l : Fin c) (h : i ≤ l) :
    affPt (c := c) 1 x₀ y (.inr l) (.inr i.castSucc) = if l = i then 1 else 0 := by
  have : ¬ l < i := not_lt.2 h
  simp [affPt, basePt, Free, this, Fin.ext_iff]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [DecidableEq n]
  [DecidableEq n'] in
theorem exists_supp {p : ℕ} {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k}
    (h : opE ψ ν p Ψ x₀ ≠ 0) : ∃ y, Ψ (affPt p x₀ y) ≠ 0 := by
  by_contra H
  push Not at H
  exact h (by simp [opE, H])

theorem bounds (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1) [ν.IsAddHaarMeasure]
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) (i : Fin (c + 1)) {a : ℤ}
    (ha : topCoord (latOf h) i = powInt ϖ a) : e' i.succ - 1 ≤ a ∧ a ≤ e' i.castSucc := by
  constructor
  · obtain ⟨v, hv, hv0, hvi⟩ : (ϖ : k) ^ a ∈ topCoord (latOf h) i := ha ▸ (zpow_mem_pow hϖ).2 le_rfl
    have key : -((ϖ : k) * ((ϖ : k) ^ (-e' i.succ) * (ϖ : k) ^ a)) ∈ 𝒪[k] := by
      refine Unram.mem_of_psi hψ fun t ht => ?_
      let y : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k :=
        Matrix.of fun r s => if s = .inr i.succ then t * (ϖ : k) ^ (-e' i.succ) * v r else 0
      have hy : MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) := fun w hw => by
        have : y *ᵥ w = (t * ((ϖ : k) ^ (-e' i.succ) * w (.inr i.succ))) • v := by
          ext r; simp [y, mulVec, dotProduct]; ring
        rw [this]
        refine smul_mem_lat (mul_mem ht ?_) hv
        rw [← mem_pow_zero (ϖ := ϖ), zpow_mul_mem_pow]
        simpa using (mem_nf.1 hw).2 i.succ
      have := Unram.psi_ch_eq_one ψ ν Ψ x₀ h0 ((ϖ : k) • y) (fun r s hf => ?_) fun x => hp x y hy
      · convert this using 2
        simp [ch, y, hvi]; ring
      · simp only [y, Matrix.smul_apply, Matrix.of_apply]
        split_ifs with e
        · subst e
          rcases r with r | r
          · simp [Free] at hf
          · rw [hv0 r (by simp only [Free, Fin.val_succ] at hf; rw [Fin.lt_def]; omega)]; simp
        · simp
    rw [neg_mem_iff, ← mem_pow_zero (ϖ := ϖ), ← zpow_add₀ ϖ.ne_zero, ← zpow_one_add₀ ϖ.ne_zero,
      zpow_mem_pow hϖ] at key
    omega
  · obtain ⟨y, hy⟩ := exists_supp h0
    have := hs _ hy _ (col_mem_nf i.castSucc ((zpow_mem_pow hϖ).2 le_rfl))
    rw [← zpow_mem_pow hϖ, ← ha]
    refine ⟨_, this, fun l hl => ?_, ?_⟩
    · rw [aff_row, aff_diag _ _ _ _ hl.le, if_neg hl.ne', zero_mul]
    · rw [aff_row, aff_diag _ _ _ _ le_rfl, if_pos rfl, one_mul]

omit [BorelSpace k] in
theorem first_mem (hϖ : valuation k (ϖ : k) = uniformizer k)
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) :
    ((ϖ ^ e' 0 : kˣ) : k) • (Sum.elim (x₀ *ᵥ z') (Pi.single 0 1) : n ⊕ Fin (c + 1) → k) ∈ latOf h ∧
      ∀ w ∈ latOf g', (Sum.elim (x₀ *ᵥ w) 0 : n ⊕ Fin (c + 1) → k) ∈ latOf h := by
  obtain ⟨y, hy⟩ := exists_supp h0
  constructor
  · have := hs _ hy _ (col_mem_nf 0 ((zpow_mem_pow hϖ).2 le_rfl))
    rw [aff_low] at this
    convert this using 1
    ext (r | l)
    · simp [mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    · simp [Pi.single_apply]
  · intro w hw
    have := hs _ hy (Sum.elim w (Pi.single 0 0)) (mem_nf.2 ⟨by simpa using hw, fun i => by simpa using zero_mem_pow⟩)
    rw [aff_low] at this
    simpa using this

theorem step_normal (H : NormalFormModN k) (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
    [ν.IsAddHaarMeasure] {j : ℕ} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k}
    (he' : ∀ i, -(j : ℤ) ≤ e' i ∧ e' i ≤ 0) (hz' : ∀ i, z' i ∈ 𝒪[k]) {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ 1 e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ 1 e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) :
    ∃ r ∈ R k n (c + 1) 1, ∃ (e : Fin (c + 1) → ℤ) (z : n → k),
      (∀ i, -((j + 1 : ℕ) : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
        latOf (r * h) = latOf (normalBasis ϖ e z) := by
  obtain ⟨u, hu, g, e, z, hl, hm⟩ := H ϖ hϖ n (c + 1) h
  have ht : ∀ i, topCoord (latOf h) i = powInt ϖ (e i) := fun i => by
    rw [← topCoord_R (Subgroup.mem_sup_right hu) h i, hl, topCoord_nf]
  refine ⟨embX _ g⁻¹ * u, mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right hu), e,
    (g⁻¹).val *ᵥ z, fun i => ?_, ?_, ?_⟩
  · have := bounds hϖ hψ hs hp h0 i (ht i)
    have := he' i.succ
    have := he' i.castSucc
    push_cast
    omega
  · obtain ⟨h1, h2⟩ := first_mem hϖ hs h0
    have h3 := (hm _).1 (h2 z' (mem_latOf_one.2 hz'))
    rw [← mulVec_mem_latOf u, N_fix hu _ (fun l hl => by simp [Fin.ext_iff, hl.ne']), hl] at h1
    have h4 := smul_mem_lat (t := (ϖ : k) ^ (-e' 0))
      (mem_pow_zero.1 ((zpow_mem_pow hϖ).2 (by have := he' 0; omega))) (mem_nf.1 h1).1
    have h5 := sub_mem h3 h4
    change z ∈ latOf g
    convert h5 using 1
    have : (ϖ : k) ^ e' 0 ≠ 0 := zpow_ne_zero _ ϖ.ne_zero
    ext r
    simp
    field_simp
    ring
  · rw [mul_assoc, latOf_mul_congr _ hl, embX_mul_nf, inv_mul_cancel, nfBasis_one]

end GlobalTheory.LatClass
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ R k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) s ≤ Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ (1 ≤ ρ → ρ < c → ∀ g : GL (n ⊕ Fin c) k, g ∈ RFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) := by
  first | exact @GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff | exact GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff | (intros; apply GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.PrCompactOpen

theorem eq_one_of_isCompact {G : Type} [Group G] [TopologicalSpace G] (f : G → ℝ)
    (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x * f y) (hp : ∀ x, 0 < f x)
    {P : Subgroup G} (hP : IsCompact (P : Set G)) {g : G} (hg : g ∈ P) : f g = 1 := by
  have h1 : f 1 = 1 := by
    have e : f 1 * f 1 = f 1 * 1 := by rw [mul_one, ← hm, one_mul]
    exact mul_left_cancel₀ (hp 1).ne' e
  have hpow : ∀ x : G, ∀ m : ℕ, f (x ^ m) = f x ^ m := by
    intro x m
    induction m with
    | zero => simp [h1]
    | succ m ih => rw [pow_succ, hm, ih, pow_succ]
  obtain ⟨B, hB⟩ := (hP.image hc).bddAbove
  have hle : ∀ x ∈ P, f x ≤ 1 := by
    intro x hx
    by_contra hlt
    have hlt := not_le.mp hlt
    obtain ⟨m, hm'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop B).exists
    have : f (x ^ m) ≤ B := hB ⟨x ^ m, P.pow_mem hx m, rfl⟩
    rw [hpow] at this
    linarith
  have hprod : f g * f g⁻¹ = 1 := by rw [← hm, mul_inv_cancel, h1]
  have a := hle g hg
  have b := hle g⁻¹ (P.inv_mem hg)
  nlinarith [mul_le_mul_of_nonneg_left b (hp g).le, hp g⁻¹]

theorem isCO_prX_Cgrp (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (hJ : IsCO J) (h : GL (n ⊕ Fin c) k) :
    IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h),
      valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by
  have := GlobalTheory.SplitWeil.t2Space k
  have key : ∀ F : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k, Continuous (fun x => (F x).val) →
      IsClosed {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} := by
    intro F hF
    have e : {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} = ⋂ r, ⋂ s, {x | lev 1 s ≤ lev 1 r →
        (r.isRight ∨ s.isRight) → (F x).val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, GlobalTheory.RootEx.VolN.InR]
    rw [e]
    exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_imp isOpen_const
      (isClosed_imp isOpen_const (isClosed_eq (hF.matrix_elem r s) continuous_const))
  have hRcl : IsClosed (R k n c 1 : Set (GL (n ⊕ Fin c) k)) := by
    have e : (R k n c 1 : Set (GL (n ⊕ Fin c) k)) =
        {x | GlobalTheory.RootEx.VolN.InR 1 (id x)} ∩ {x | GlobalTheory.RootEx.VolN.InR 1 x⁻¹} := by
      ext x
      exact GlobalTheory.RootEx.VolN.mem_R_iff
    rw [e]
    exact (key id Units.continuous_val).inter (key (fun x => x⁻¹) Units.continuous_coe_inv)
  have hconj : {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} = (fun y => h * y * h⁻¹) '' (J : Set _) := by
    ext x
    constructor
    · intro hx
      exact ⟨h⁻¹ * x * h, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      show h⁻¹ * (h * y * h⁻¹) * h ∈ J
      have e : h⁻¹ * (h * y * h⁻¹) * h = y := by group
      rw [e]
      exact hy
  have hCset : (Cgrp J h : Set (GL (n ⊕ Fin c) k)) =
      {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} ∩ (R k n c 1 : Set _) := by
    ext x
    exact GlobalTheory.StepData.mem_Cgrp.trans and_comm
  have hCc : IsCompact (Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
    rw [hCset, hconj]
    exact (hJ.2.image ((continuous_const.mul continuous_id).mul continuous_const)).inter_right hRcl
  have hOpen : IsOpen (prX (Cgrp J h) : Set (GL n k)) := by
    apply Subgroup.isOpen_of_mem_nhds
    have hV : IsOpen {g : GL n k | h⁻¹ * embX c g * h ∈ J} :=
      hJ.1.preimage ((continuous_const.mul GlobalTheory.QuotInt.continuous_embX).mul continuous_const)
    have h1V : (1 : GL n k) ∈ {g : GL n k | h⁻¹ * embX c g * h ∈ J} := by
      show h⁻¹ * embX c 1 * h ∈ J
      rw [map_one, mul_one, inv_mul_cancel]
      exact J.one_mem
    refine Filter.mem_of_superset (hV.mem_nhds h1V) ?_
    intro g hg
    refine GlobalTheory.StepData.mem_prX.mpr ⟨1, one_mem _, GlobalTheory.StepData.mem_Cgrp.mpr ⟨?_, ?_⟩⟩
    · rw [one_mul]
      exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    · rw [one_mul]
      exact hg
  have hblk : ∀ {A : GL (n ⊕ Fin c) k → Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}, Continuous A →
      Continuous (fun r => (A r).toBlocks₁₁) :=
    fun hA => continuous_pi fun i => continuous_pi fun j => hA.matrix_elem _ _
  have hΦ : Continuous (fun r : GL (n ⊕ Fin c) k =>
      ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁,
        MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) :=
    (hblk Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hblk Units.continuous_coe_inv))
  have himg : Units.embedProduct (Matrix n n k) '' (prX (Cgrp J h) : Set (GL n k)) =
      (fun r : GL (n ⊕ Fin c) k =>
        ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁,
          MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) ''
        (Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨u, hu, huC⟩ := GlobalTheory.StepData.mem_prX.mp hg
      refine ⟨u * embX c g, huC, ?_⟩
      have hinv : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      simp only [hinv, GlobalTheory.QuotInt.block_right g hu, GlobalTheory.QuotInt.block_left g⁻¹ (inv_mem hu),
        Units.embedProduct_apply]
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hrR, -⟩ := GlobalTheory.StepData.mem_Cgrp.mp hr
      obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hrR
      refine ⟨x, GlobalTheory.StepData.mem_prX.mpr ⟨embX c x * u * (embX c x)⁻¹,
        GlobalTheory.RootEx.Radical.conj_mem x hu, by rwa [inv_mul_cancel_right]⟩, ?_⟩
      have hinv : (embX c x * u)⁻¹ = u⁻¹ * embX c x⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      simp only [hinv, GlobalTheory.QuotInt.block_left x hu, GlobalTheory.QuotInt.block_right x⁻¹ (inv_mem hu),
        Units.embedProduct_apply]
  have hcpt : IsCompact (prX (Cgrp J h) : Set (GL n k)) := by
    rw [Units.isEmbedding_embedProduct.isCompact_iff, himg]
    exact hCc.image hΦ
  refine ⟨⟨hOpen, hcpt⟩, fun g hg => ?_⟩
  have hdet : Continuous (fun g : GL n k => Matrix.GeneralLinearGroup.det g) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · have e : (Units.val ∘ fun g : GL n k => Matrix.GeneralLinearGroup.det g) =
          fun g : GL n k => (g : Matrix n n k).det := by
        funext g
        exact Matrix.GeneralLinearGroup.val_det_apply g
      rw [e]
      exact Units.continuous_val.matrix_det
    · have e : (fun g : GL n k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
          fun g : GL n k => ((g⁻¹ : GL n k) : Matrix n n k).det := by
        funext g
        rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
      rw [e]
      exact Units.continuous_coe_inv.matrix_det
  have h1 := eq_one_of_isCompact (fun g : GL n k => nabs k (Matrix.GeneralLinearGroup.det g))
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).continuous.comp hdet)
    (fun x y => by
      simp only [map_mul]
      exact GlobalTheory.SplitWeil.nabs_mul k _ _)
    (fun x => GlobalTheory.SplitWeil.nabs_pos k _) hcpt hg
  refine ⟨(GlobalTheory.SplitWeil.nabs_eq_one_iff _).mp h1, ?_⟩
  show nabs k (Matrix.GeneralLinearGroup.det g) ^ ((c : ℤ) - 1) = 1
  rw [h1, _root_.one_zpow]

end GlobalTheory.PrCompactOpen
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.parabolicHaarVolume_conjIntersection_eq_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), IsOpen (prX (Cgrp J h) : Set (GL n k)) → ∀ m : Measure (GL n k), volR ν m (Cgrp J h) = volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) * m (prX (Cgrp J h)) := by
  first | exact @GlobalTheory.CosetVolProd.volR_Cgrp | exact GlobalTheory.CosetVolProd.volR_Cgrp | (intros; apply GlobalTheory.CosetVolProd.volR_Cgrp <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.exists_isSymmetricPositionLevel :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ →
      ∀ ρ κ l : ℕ, ∃ P : GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l),
        GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P :=
  @GlobalTheory.SymLevelExists.exists_isSymLevel
end
