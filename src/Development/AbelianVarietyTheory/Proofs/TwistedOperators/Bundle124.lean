module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle051
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainStepSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D]
    {j : GL (A ⊕ D) k} (hj : j ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D) : j.1.toBlocks₂₂.det ≠ 0 :=
  (_root_.GlobalTheory.ParahoricLowerBlock.lower_block_tame k A D 1 (fun _ _ => rfl) j hj).1


variable (k) in
def reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) : GL m k ≃* GL n k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k e).toMulEquiv

theorem val_reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) (g : GL m k) :
    (reGL k e g).1 = reindex e e g.1 := rfl

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.reGL_mem_KO {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g : GL m k} (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k m) :
    _root_.GlobalTheory.ChainStepSupp.reGL k e g ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simpa [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply] using hg.1 (e.symm i) (e.symm j)
  · rw [← map_inv]
    simpa [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply] using hg.2 (e.symm i) (e.symm j)

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.reGL_torusElt {m n : Type} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (ϖ : kˣ) (f : m → ℤ) :
    _root_.GlobalTheory.ChainStepSupp.reGL k e (_root_.GlobalTheory.GLDoubling.torusElt k m ϖ f) =
      _root_.GlobalTheory.GLDoubling.torusElt k n ϖ (f ∘ e.symm) := by
  ext i j
  simp [_root_.GlobalTheory.ChainStepSupp.val_reGL, _root_.GlobalTheory.GLDoubling.val_torusElt, Matrix.reindex_apply,
    Matrix.diagonal_apply]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.reGL_reGL_symm {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n)
    (g : GL n k) : _root_.GlobalTheory.ChainStepSupp.reGL k e (_root_.GlobalTheory.ChainStepSupp.reGL k e.symm g) = g := by
  ext i j
  simp [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply]


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D]
    {x : GL A k} {y : GL D k} (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k A)
    (hy : y ∈ _root_.GlobalTheory.SplitWeil.KO k D) :
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (A ⊕ D)) (x, y) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D := by
  have hb (g : GL A k × GL D k) :
      (SmGL.emb₂ k (Equiv.refl (A ⊕ D)) g : Matrix (A ⊕ D) (A ⊕ D) k) =
        Matrix.fromBlocks g.1.val 0 0 g.2.val := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [SmGL.emb₂, SmGL.leviEmb, SmGL.leviTwo, SmGL.two,
        Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_ne]
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hx hy
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric, _root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · change ((_: GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k) i j ∈ _
    rw [hb]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.reindex_apply, hx.1, hy.1]
  · have hx₂ := hx.2
    have hy₂ := hy.2
    simp only [Matrix.coe_units_inv] at hx₂ hy₂
    rw [← map_inv, Prod.inv_mk]
    change ((_: GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k) i j ∈ _
    rw [hb]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.reindex_apply, hx₂, hy₂]
  · rw [hb]
    simp [Matrix.reindex_apply]


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.emb₂_one_torusElt {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (ϖ : kˣ)
    (f : D → ℤ) :
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (A ⊕ D)) (1, _root_.GlobalTheory.GLDoubling.torusElt k D ϖ f) =
      (_root_.GlobalTheory.ZonalCellDecomposition.mtor ϖ f : GL (A ⊕ D) k) := by
  have hb (g : GL A k × GL D k) :
      (SmGL.emb₂ k (Equiv.refl (A ⊕ D)) g : Matrix (A ⊕ D) (A ⊕ D) k) =
        Matrix.fromBlocks g.1.val 0 0 g.2.val := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [SmGL.emb₂, SmGL.leviEmb, SmGL.leviTwo, SmGL.two,
        Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_ne]
  have h : (_root_.GlobalTheory.ZonalCellDecomposition.mtor ϖ f : GL (A ⊕ D) k) =
      _root_.GlobalTheory.GLDoubling.torusElt k (A ⊕ D) ϖ (0 ⊕ᵥ f) := rfl
  rw [h]
  ext i j
  change ((_: GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k) i j = _
  rw [hb]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, _root_.GlobalTheory.GLDoubling.val_torusElt, Matrix.diagonal_apply,
      Matrix.one_apply]


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.support_dcell : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ : kˣ →* ℂˣ), _root_.GlobalTheory.SplitWeil.IsTame ξ → ¬ _root_.GlobalTheory.SplitWeil.IsUnram ξ →
  ∀ φ : GL (Fin r ⊕ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) k → ℂ, _root_.GlobalTheory.ZonalCellDecomposition.IsBiType ξ φ →
    (∀ x y, φ (_root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (Fin r ⊕ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t)) (x, y)) ≠ 0 →
      x ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin r)) →
    ∀ g, φ g ≠ 0 → ∃ e : Fin (l * t) → ℤ, Antitone e ∧
      g ∈ _root_.GlobalTheory.ZonalCellDecomposition.dcell ϖ (e ∘ (_root_.GlobalTheory.ZonalCellDecomposition.blkEquiv l t).symm) := by
  intro k _ _ _ _ ϖ hϖ r l t ξ hT hU φ hφ hL g hg
  obtain ⟨x, y, j, hj, j', hj', rfl⟩ :=
    _root_.GlobalTheory.ParHeckeSupp.support_levi k (Fin r) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) ξ hT hU φ hφ
      g hg
  have hne : φ (_root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (x, y)) ≠ 0 := by
    intro h0
    apply hg
    have hd := _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero hj
    have hd' := _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero hj'
    rw [mul_assoc, (hφ j hj (Units.mk0 _ hd) rfl _).1, (hφ j' hj' (Units.mk0 _ hd') rfl _).2, h0,
      mul_zero, mul_zero]
  have hx := hL x y hne
  set E := _root_.GlobalTheory.ZonalCellDecomposition.blkEquiv l t
  obtain ⟨⟨e, he⟩, hy⟩ := Set.mem_iUnion.1 ((Set.eq_univ_iff_forall.1
    (_root_.GlobalTheory.GLDoubling.iUnion_cell (N := l * t) hϖ)) (_root_.GlobalTheory.ChainStepSupp.reGL k E.symm y))
  unfold _root_.GlobalTheory.GLDoubling.cell at hy
  rw [DoubleCoset.mem_doubleCoset] at hy
  obtain ⟨κ₁, hκ₁, κ₂, hκ₂, hyeq⟩ := hy
  refine ⟨e, he, ?_⟩
  unfold _root_.GlobalTheory.ZonalCellDecomposition.dcell
  rw [DoubleCoset.mem_doubleCoset]
  have hy' : y = _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁ *
      _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm) * _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂ := by
    rw [← _root_.GlobalTheory.ChainStepSupp.reGL_torusElt, ← map_mul, ← map_mul, ← hyeq]
    exact (_root_.GlobalTheory.ChainStepSupp.reGL_reGL_symm E y).symm
  refine ⟨j * _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁),
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k _ _).mul_mem hj
      (_root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric hx
        (_root_.GlobalTheory.ChainStepSupp.reGL_mem_KO E hκ₁)),
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (1, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) * j',
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k _ _).mul_mem
      (_root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric (Subgroup.one_mem _)
        (_root_.GlobalTheory.ChainStepSupp.reGL_mem_KO E hκ₂)) hj', ?_⟩
  rw [← _root_.GlobalTheory.ChainStepSupp.emb₂_one_torusElt, hy']
  have hprod : ((x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁ *
      _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm) * _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) :
        GL (Fin r) k × GL (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) k) =
      (x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁) * (1, _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm)) *
        (1, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) := by
    simp [Prod.mk_mul_mk]
  rw [hprod, map_mul, map_mul]
  simp only [mul_assoc]

end GlobalTheory.ChainStepSupp
end
end

section

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel Matrix

namespace GlobalTheory.SmGL.EmptyBlocks

section General

variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem jhMult_comp_surjective (φ : H →* G) (hφ : Function.Surjective φ) (σ : Representation F G W)
    (ρ : Representation F G V) :
    jhMult (σ.comp φ : Representation F H W) (ρ.comp φ : Representation F H V) = jhMult σ ρ := by
  have : ∀ r, OccursTimes (σ.comp φ : Representation F H W) (ρ.comp φ : Representation F H V) r ↔
      OccursTimes σ ρ r := fun r => by
    constructor
    · rintro ⟨S, T, h1, h2, h3⟩
      let up : Subrepresentation (ρ.comp φ : Representation F H V) → Subrepresentation ρ := fun S =>
        ⟨S.toSubmodule, fun g v hv => by
          obtain ⟨h, rfl⟩ := hφ g
          exact S.apply_mem_toSubmodule h hv⟩
      refine ⟨fun i => up (S i), fun i => up (T i), h1, h2, fun i => (h3 i).map fun ψ =>
        .mk ψ.toLinearEquiv fun g => ?_⟩
      obtain ⟨h, rfl⟩ := hφ g
      exact ψ.isIntertwining' h
    · rintro ⟨S, T, h1, h2, h3⟩
      let down : Subrepresentation ρ → Subrepresentation (ρ.comp φ : Representation F H V) := fun S =>
        ⟨S.toSubmodule, fun h v hv => S.apply_mem_toSubmodule (φ h) hv⟩
      exact ⟨fun i => down (S i), fun i => down (T i), h1, h2, fun i => (h3 i).map fun ψ =>
        .mk ψ.toLinearEquiv fun h => ψ.isIntertwining' (φ h)⟩
  simp only [jhMult, this]

end General

section Blocks

variable (R : Type) [CommRing R] {β n : Type} [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n]
  {c : β → Type} [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n)

def torusToLevi : (n → Rˣ) →* Levi R c :=
  (leviProj R f).comp ((diagT R n).codRestrict (parab R f) fun t => mem_parab.2 fun i j h => by
    rw [val_diagT, diagonal_apply_ne]
    rintro rfl
    exact lt_irrefl _ h)

theorem val_torusToLevi (t : n → Rˣ) (j : β) :
    (torusToLevi R f t j : Matrix (c j) (c j) R) = diagonal fun x => (t (f ⟨j, x⟩) : R) := by
  ext x y
  show (diagT R n t : Matrix n n R) (f ⟨j, x⟩) (f ⟨j, y⟩) = _
  rw [val_diagT]
  simp [diagonal_apply]

theorem leviEmb_torusToLevi (t : n → Rˣ) : leviEmb R f (torusToLevi R f t) = diagT R n t := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective j
  by_cases h : a = b
  · subst h
    simp [leviEmb, val_torusToLevi, val_diagT, diagonal_apply]
  · have hij : f ⟨a, i⟩ ≠ f ⟨b, j⟩ := fun h' => h (congrArg Sigma.fst (f.injective h'))
    simp [leviEmb, blockDiagonal'_apply, h, val_diagT, diagonal_apply_ne, hij]

theorem det_torusToLevi (t : n → Rˣ) (j : β) :
    GeneralLinearGroup.det (torusToLevi R f t j) = ∏ x, t (f ⟨j, x⟩) := by
  ext
  simp [val_torusToLevi]

theorem prod_det_torusToLevi (χ : β → Rˣ →* ℂˣ) (t : n → Rˣ) :
    ∏ j, χ j (GeneralLinearGroup.det (torusToLevi R f t j)) = ∏ i, χ (blk f i) (t i) := by
  rw [← f.prod_comp, Fintype.prod_sigma]
  simp [det_torusToLevi]

theorem torusToLevi_surjective (hf : Function.Injective (blk f)) :
    Function.Surjective (torusToLevi R f) := by
  intro g
  refine ⟨fun i => GeneralLinearGroup.det (g (blk f i)), funext fun j => ?_⟩
  ext x y
  have hs : ∀ u v : c j, u = v := fun u v => by
    have : f ⟨j, u⟩ = f ⟨j, v⟩ := hf (by simp)
    simpa using this
  obtain rfl := hs x y
  haveI : Unique (c j) := ⟨⟨x⟩, fun u => hs _ _⟩
  rw [val_torusToLevi, diagonal_apply_eq, blk_apply, GeneralLinearGroup.val_det_apply,
    det_unique, hs default x]


omit [LinearOrder β] [DecidableEq n] [∀ j, DecidableEq (c j)] in
theorem sum_card_blocks (P : β → Prop) [DecidablePred P] :
    ∑ b with P b, (Fintype.card (c b) : ℤ) = ∑ i with P (blk f i), (1 : ℤ) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← f.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [blk_apply]
  split_ifs <;> simp

variable [LinearOrder n]


omit [DecidableEq n] [∀ j, DecidableEq (c j)] in
theorem modExp_blk (hf : StrictMono (blk f)) (i : n) :
    modExp c (blk f i) = modExp (fun _ : n => Unit) i := by
  unfold modExp
  rw [sum_card_blocks f, sum_card_blocks f]
  simp [hf.lt_iff_lt]

theorem unipRad_eq (hf : StrictMono (blk f)) : unipRad R f = unipB R n := by
  ext g
  rw [mem_unipRad, mem_unipB, mem_parab]
  simp only [hf.lt_iff_lt]
  refine and_congr Iff.rfl ⟨fun h i => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := f.surjective i
    simpa using h a x x
  · have : f ⟨a, x⟩ = f ⟨a, y⟩ := hf.injective (by simp)
    obtain rfl : x = y := by simpa using this
    simpa using h _

end Blocks

theorem jhMult_jac_eq_jacB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n]
    [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)]
    (f : (Σ j, c j) ≃ n) (hf : StrictMono (blk f)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ) :
    jhMult (ofChar (leviChar c χ)) (jac f π) =
      jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  have h1 : ((ofChar (leviChar c χ)).comp (torusToLevi k f) : Representation ℂ (n → kˣ) ℂ) =
      ofChar (torusChar fun i => χ (blk f i)) := by
    refine MonoidHom.ext fun t => LinearMap.ext fun y => ?_
    show ofChar _ _ y = _
    rw [ofChar_apply, ofChar_apply, leviChar_apply, torusChar_apply, prod_det_torusToLevi]
  have h2 : ∀ t, deltaHalf k c (torusToLevi k f t) =
      deltaHalf k (fun _ : n => Unit) (leviTorus k n t) := fun t => by
    have hd : ∀ i, GeneralLinearGroup.det (leviTorus k n t i) = t i :=
      congrFun ((leviTorus k n).left_inv t)
    rw [deltaHalf_apply, deltaHalf_apply,
      prod_det_torusToLevi k f fun a => absPow k ((modExp c a : ℂ) / 2)]
    simp only [hd, modExp_blk f hf]
  have h3 : twKer π (unipRad k f) 1 = twKer π (unipB k n) 1 := by rw [unipRad_eq k f hf]
  rw [← jhMult_comp_surjective (torusToLevi k f) (torusToLevi_surjective k f hf.injective), h1]
  refine jhMult_congr_right _ (.mk (Submodule.quotEquivOfEq _ _ h3) fun t => ?_)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show Submodule.quotEquivOfEq _ _ h3 (jac f π (torusToLevi k f t) (Submodule.Quotient.mk v)) =
    jac (points n) π (leviTorus k n t) (Submodule.Quotient.mk v)
  rw [jac_mk, jac_mk, map_smul, h2, leviEmb_torusToLevi]
  simp only [Submodule.quotEquivOfEq_mk]
  have heq : diagT k n t = leviEmb k (points n) (leviTorus k n t) := by
    ext i j
    rw [val_diagT]
    simp [leviEmb, leviTorus, points, GeneralLinearGroup.coe_scalar, Matrix.scalar, diagonal_apply]
  rw [heq]
  congr 4

end GlobalTheory.SmGL.EmptyBlocks
end
end
