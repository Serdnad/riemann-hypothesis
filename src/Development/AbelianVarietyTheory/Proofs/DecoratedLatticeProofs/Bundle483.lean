module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle250
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle418
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle248
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle467
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle286
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle472
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLatticeSplitsAlongWittNormalFrames
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.KappaLeft

theorem latV_mem_idAt {D : D7} {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : ∀ r, y r ∈ idAt D P := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, s, -, rfl⟩ := hw
    intro r
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => intro r; exact zero_mem _
  | add x y _ _ hx hy => intro r; exact add_mem (hx r) (hy r)
  | neg x _ hx => intro r; exact neg_mem (hx r)

end GlobalTheory.Corev.KappaLeft



theorem GlobalTheory.Corev.kappa_mem_latO_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x : WO S B'.L, MxAt P x → ((B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ)) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) ∈ intAt D P) := by
  intro D k _ _ _ _ ι p I P hP n' _ _ ρ σ B B' l S α α₀ M LS Λ hM hLS hα x hx
  have hcA : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  have hMx : MxAt P ((B.o.resS S).symm (0, l.κ S x)) :=
    (GlobalTheory.KapLatSupp.mxAt_embed_kappa D ρ B B'.L B'.ζ l S B'.V₀ B'.A B'.o P x hx).1
  have hu : (B.o.resS S).symm (0, l.κ S x) = l.κ S x ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]

  have hline : ∀ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ v : Fin L.rank → AE D,
      (∀ r, v r ∈ idAt D P) → ∃ c : AE D, c ∈ idAt D P ∧ v = c • ratV ζ := by
    intro L ζ hL v hv
    obtain ⟨hrk, hne⟩ := hL
    have hr : ∀ r r' : Fin L.rank, r = r' := fun r r' => Fin.ext (by omega)
    let r₀ : Fin L.rank := ⟨0, by omega⟩
    have hζ : ζ r₀ ≠ 0 := by
      intro h0
      apply hne
      have : ζ = 0 := funext fun r => by rw [hr r r₀, h0]; rfl
      rw [this, Matrix.mulVec_zero, dotProduct_zero]
    refine ⟨v r₀ * incA D (ζ r₀)⁻¹, Ideal.mul_mem_right _ _ (hv r₀), ?_⟩
    funext r
    rw [hr r r₀, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hζ, map_one, mul_one]
  have hjB : ∀ c : AE D, B.o.jB *ᵥ (c • ratV B.ζ) = fun r => c * incA D (vecB B.o B.ζ r) := by
    intro c
    funext r

    simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, ratV, Pi.smul_apply, smul_eq_mul, vecB,
    map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpj : ∀ c : AE D, B.o.pB *ᵥ (B.o.jB *ᵥ (c • ratV B.ζ)) = c • ratV B.ζ := by
    intro c
    rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]

  have hsupp : ∀ m : Fin B.V₀.rank → AE D, ∀ r, (((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ m) r ∈ idAt D P := by
    intro m r
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hMx r j)

  have hpair : ∀ (y : Fin S.rank → AE D) (d c : AE D), (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ →
      (∑ i, ∑ j, cA D (y i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ)) j) =
        incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) := by
    intro y d c hxy
    rw [GlobalTheory.T.besselLinkKappa_adjoint_tau_factor D ρ B B'.L B'.ζ l S x (c • ratV B.ζ) y]
    have h1 : ((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ y = d • ratV (-B.ζ) := by
      rw [← Matrix.mulVec_mulVec, hxy, Matrix.mulVec_smul, ← l.map]
      congr 1
      ext i
      simp [rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [h1]
    have hh : incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) =
        ∑ i, ∑ j, incA D (star (B.ζ i)) * incA D (HSpace.gram B.L i j) * incA D (B.ζ j) := by

      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Finset.mul_sum, mul_assoc]
    rw [hh, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, ratV, Pi.neg_apply, map_mul, map_neg, hcA, star_neg]
    ring
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D B.V₀ S M LS hM hLS P, GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces D k ι p I P hP S LS]
  constructor
  · rintro ⟨-, h⟩ y hy
    have hz : ∀ r, ((x : Matrix _ _ (AE D)) *ᵥ y) r ∈ idAt D P := by
      intro r
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx r j)
    obtain ⟨d, hdI, hxd⟩ := hline B'.L B'.ζ B'.line _ hz
    refine ⟨d, hdI, hxd, fun c hc hl => ?_⟩
    have hm : (fun r => c * incA D (vecB B.o B.ζ r)) ∈ latV B.V₀ M P :=
      (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα c hc).2 hl
    have h1 := h _ hm
    have hI := hsupp (fun r => c * incA D (vecB B.o B.ζ r))
    have heq : ((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ (fun r => c * incA D (vecB B.o B.ζ r)) =
        (l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ) := by
      rw [hu, ← hjB, ← Matrix.mulVec_mulVec, hpj]
    rw [heq] at h1 hI
    have h2 := (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S LS hLS P _ hI).1 h1 y hy
    rwa [hpair y d c hxd] at h2
  · intro h
    refine ⟨hMx, fun m hm => ?_⟩
    have hv : ∀ r, (B.o.pB *ᵥ m) r ∈ idAt D P := by
      intro r
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (GlobalTheory.Corev.KappaLeft.latV_mem_idAt hm j)
    obtain ⟨c, hc, hcv⟩ := hline B.L B.ζ B.line _ hv
    have hjp := GlobalTheory.T.lineProjection_mem_splitCoreCompletion D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα m hm
    rw [hcv, hjB] at hjp
    have hl := (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα c hc).1 hjp
    have hI := hsupp m
    have heq : ((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ m = (l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ) := by
      rw [hu, ← Matrix.mulVec_mulVec, hcv]
    rw [heq] at hI ⊢
    refine (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S LS hLS P _ hI).2 fun s hs => ?_
    obtain ⟨d, -, hxd, hd⟩ := h s hs
    rw [hpair s d c hxd]
    exact hd c hc hl
end

section

open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.CoreIdele

variable {D : D7}

theorem card_eq_of_inv {k : Type} [Field k] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (b : Matrix m n k) (b' : Matrix n m k) (h : b * b' = 1) (h' : b' * b = 1) : Fintype.card n = Fintype.card m := by
  have h1 : Fintype.card m ≤ Fintype.card n := by
    have := Matrix.rank_mul_le_left b b'
    rw [h, Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width b)
  have h2 : Fintype.card n ≤ Fintype.card m := by
    have := Matrix.rank_mul_le_left b' b
    rw [h', Matrix.rank_one] at this
    exact this.trans (Matrix.rank_le_card_width b')
  omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_sumFrame' (p : SplitPt D k) {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E}
    (hζ : IsLineVec L ζ) {n : Type} [Fintype n] [DecidableEq n] (β : Frame p A n) :
    ∃ β₀ : Frame p S (n ⊕ Fin 1), IsSumFrame o ζ β β₀ := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let r : Fin L.rank → D.host.E := (star ζ ⬝ᵥ L.gram *ᵥ ζ)⁻¹ • (star ζ ᵥ* L.gram)
  have hr : r ⬝ᵥ ζ = 1 := by
    simp only [r]
    rw [smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hζ.2]
  let bE : Matrix (Fin S.rank) (Fin A.rank ⊕ Fin 1) D.host.E := fromCols o.iA (replicateCol (Fin 1) (o.iB *ᵥ ζ))
  let bE' : Matrix (Fin A.rank ⊕ Fin 1) (Fin S.rank) D.host.E := fromRows o.qA (replicateRow (Fin 1) (r ᵥ* o.qB))
  have h1 : bE' * bE = 1 := by
    simp only [bE, bE']
    rw [fromRows_mul_fromCols, ← Matrix.fromBlocks_one]
    congr 1
    · exact o.qA_iA
    · rw [← replicateCol_mulVec, Matrix.mulVec_mulVec, o.qA_iB, Matrix.zero_mulVec]; rfl
    · rw [← replicateRow_vecMul, Matrix.vecMul_vecMul, show o.qB * o.iA = 0 from o.symm.qA_iB, Matrix.vecMul_zero]; rfl
    · ext i j
      rw [replicateRow_mul_replicateCol_apply, dotProduct_mulVec, Matrix.vecMul_vecMul,
        show o.qB * o.iB = 1 from o.symm.qA_iA, Matrix.vecMul_one, hr, Subsingleton.elim i j, Matrix.one_apply_eq]
  have hn : Fintype.card n = A.rank := by simpa using card_eq_of_inv β.b β.b' β.bb' β.b'b
  let X : Matrix (Fin A.rank ⊕ Fin 1) (n ⊕ Fin 1) k := fromBlocks β.b 0 0 1
  let X' : Matrix (n ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b' 0 0 1
  have hX : X' * X = 1 := by
    simp only [X, X', fromBlocks_multiply, β.b'b]; simp
  have g1 : (X' * bE'.map f) * (bE.map f * X) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bE'.map f), ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.one_mul, hX]
  have hc : Fintype.card (Fin S.rank) = Fintype.card (n ⊕ Fin 1) := by
    have := o.rank_add; have := hζ.1
    simp only [Fintype.card_fin, Fintype.card_sum, hn]; omega
  have g2 : (bE.map f * X) * (X' * bE'.map f) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).2 g1
  obtain ⟨β₀, h₀⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character D).2 k p).1 S (n ⊕ Fin 1) _ _ g2 g1
  refine ⟨β₀, ?_⟩
  rw [IsSumFrame, h₀]
  simp only [bE, X, fromCols_map, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  ext i (j | j) <;> rfl

theorem line_of_orth {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (v : Pl D) (ho : OrthAt o M LA LL v) (a : AE D) :
    a • ratV (vecB o ζ) ∈ latV S M (· = v) ↔ a • ratV ζ ∈ latV L LL (· = v) := by
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.FinPl.CoreIdele

theorem GlobalTheory.FinPl.CoreIdele.lineLat_idele : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ m : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * cA D (m : AE D) * incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) * a ∈ intAt D (· = x)) → ∃ LL : Lat L, IsSelfDualC L LL ∧ ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP L ζ hζ m hm
  set h := star ζ ⬝ᵥ L.gram *ᵥ ζ with hhdef
  have hh : star h = h := by
    have hG : ∀ i j, star (L.gram i j) = L.gram j i := fun i j => by
      have := congrFun (congrFun (gram_conjTranspose L) j) i
      simpa [Matrix.conjTranspose_apply] using this
    have e : star (star ζ ⬝ᵥ L.gram *ᵥ ζ) = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
      simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum, hG]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    exact e
  obtain ⟨m', hoff, hon⟩ := GlobalTheory.T.exists_idele_change_finitely_many_split_places D k ι p I P hP h hζ.2 hh m
  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.T.exists_fractionalIdeal_of_hermIdele D m'
  have key : ∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), ((m'⁻¹ : (AE D)ˣ) : AE D) * a = ((m⁻¹ : (AE D)ˣ) : AE D) * a := by
    intro x hx a ha
    have h1 : ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
    have h2 := (hoff x hx _ h1).1
    rw [← mul_assoc (m : AE D), Units.mul_inv, one_mul] at h2
    calc ((m'⁻¹ : (AE D)ˣ) : AE D) * a = ((m'⁻¹ : (AE D)ˣ) : AE D) * ((m' : AE D) * (((m⁻¹ : (AE D)ˣ) : AE D) * a)) := by
          rw [h2]
      _ = ((m⁻¹ : (AE D)ˣ) : AE D) * a := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have hloc : ∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔
      (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
    intro x a ha
    by_cases hx : P x
    · exact hon x hx a ha
    · have h1 : incA D h * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
      have h2 : cA D (m : AE D) * (incA D h * a) ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ h1
      have e : (m' : AE D) * cA D (m' : AE D) * incA D h * a = (m : AE D) * cA D (m : AE D) * incA D h * a := by
        rw [mul_assoc, mul_assoc, (hoff x hx _ h1).2, (hoff x hx _ h2).1, ← mul_assoc, ← mul_assoc]
      rw [e]
      exact hm x hx a ha
  have hsd := GlobalTheory.T.fractionalIdeal_hermitianSelfDual_of_local_generators D h 𝔞 m' h𝔞 hloc
  have hζ0 : ζ ≠ 0 := fun e => hζ.2 (by rw [e]; simp)
  refine ⟨GlobalTheory.SeeSaw.LiftModel.lineLat L ζ 𝔞, GlobalTheory.SeeSaw.LiftModel.isSelfDualC_lineLat D L ζ hζ 𝔞 hsd, fun x hx a ha => ?_⟩
  rw [GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ0 𝔞 x a ha, h𝔞 x a ha, key x hx a ha]


open GlobalTheory.FinPl.CoreIdele GlobalTheory.SeeSaw.CoreGlue in
theorem GlobalTheory.FinPl.CoreIdele.exists_core : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (q : Unif k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (β : ∀ i, Frame (p i) B.A n) (Q : ι → Pair k n) (LA : Lat B.A), IsSelfDualC B.A LA → (∀ i, (β i).IsLat LA (Q i).lat) → (∀ i, valuation k ((p i).pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = valuation k ((q.1 : 𝒪[k]) : k)) → ∀ m : (AE D)ˣ, (∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * a ∈ intAt D (· = x)) → (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m : AE D) * cA D (m : AE D) * incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a ∈ intAt D (· = x)) → ∃ (M : Lat B.V₀) (β₀ : ∀ i, Frame (p i) B.V₀ (n ⊕ Fin 1)), IsSelfDualC B.V₀ M ∧ (∀ i, GluedCore B M q (β i) (β₀ i) (Q i)) ∧ (∀ x, ¬ P x → ∃ LL : Lat B.L, IsSelfDualC B.L LL ∧ OrthAt B.o M LA LL x ∧ ∀ a ∈ idAt D (· = x), a • ratV B.ζ ∈ latV B.L LL (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧ ∀ x, ∀ a ∈ idAt D (· = x), a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D k _ _ _ _ ι p I P hP q n _ _ ρ B β Q LA hLA _ hnorm m hmP hmoff
  obtain ⟨LL, hLL, hline⟩ := lineLat_idele D k ι p I P hP B.L B.ζ B.line m hmoff
  obtain ⟨M₁, hM₁, horth⟩ := exists_orthSum B.o hLA hLL
  have frames : ∀ i, ∃ β₀ : Frame (p i) B.V₀ (n ⊕ Fin 1), IsSumFrame B.o B.ζ (β i) β₀ :=
    fun i => exists_sumFrame' (p i) B.o B.line (β i)
  choose β₀ hβ₀ using frames
  obtain ⟨M, hM, hlat, hoff⟩ := exists_modify hP.inj β₀ (fun i => gluedS q 1 (Q i).ker (Q i).vec)
    (fun i => by haveI := (Q i).ker_isLat; infer_instance) hM₁ I
  have glued : ∀ i, GluedCore B M q (β i) (β₀ i) (Q i) := fun i =>
    ⟨hP.unit i, hβ₀ i, hnorm i, hlat i (hP.all i)⟩
  have offP : ∀ x, ¬ P x → ∀ i, x ≠ (p i).v := fun x hx i e => hx ((hP.mem x).2 ⟨i, e⟩)
  have horthM : ∀ x, ¬ P x → OrthAt B.o M LA LL x := fun x hx y => by
    rw [hoff x (offP x hx)]
    exact horth x y
  refine ⟨M, β₀, hM, glued, fun x hx => ⟨LL, hLL, horthM x hx, hline x hx⟩, fun x a ha => ?_⟩
  by_cases hx : P x
  · obtain ⟨i, rfl⟩ := (hP.mem x).1 hx
    rw [line_of_glued hM (glued i) ha]
    have hma : ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_left _ _ ha
    have := hmP _ hx _ hma
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this.symm
  · rw [line_of_orth B.o B.ζ M LA LL x (horthM x hx) a]
    exact hline x hx a ha
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSawStep

variable {D : D7}

theorem per_smul_right {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (b : ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ (b • f) = b * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem per_smul_left {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (a : ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ (a • φ) f = a * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem trc_smul {V : HSp D} (e : GA D V →₀ ℂ) (b : ℂ) (f : GA D V → ℂ) : trc e (b • f) = b • trc e f := by
  funext g
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

theorem liftS_smul {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (b : ℂ) (G : GA D T → ℂ)
    (f : WO S T → ℂ) : liftS om ν 𝓕 (b • G) f = b • liftS om ν 𝓕 G f := by
  funext g
  simp only [liftS_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem rapidDec_smul {V : HSp D} (b : ℂ) (F : GA D V → ℂ) (hF : RapidDec V F) : RapidDec V (b • F) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨fun γ hγ g => by simp only [Pi.smul_apply, h1 γ hγ g], h2.const_smul b, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h3 N
  refine ⟨‖b‖ * C, fun g => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg b)

theorem contAut_zero (V : HSp D) : IsContAut V (fun _ => (0 : ℂ)) := ⟨fun _ _ _ => rfl, continuous_const⟩

theorem perF_smul {c : Comm D} (tt : Tup c) (n ρ : ℕ) (h : n + 2 * ρ + 2 = D.R.m) (φ : tt.Ch n → GA D (c.X n) → ℂ) (b : ℂ)
    (f : GA D (c.V n) → ℂ) : tt.perF n ρ h φ (b • f) = b * tt.perF n ρ h φ f := by
  simp only [Tup.perF, trc_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => per_smul_right _ _ _ _ _

theorem perF_comb (hPS : PerSum D) {c : Comm D} (hc : c.Is) (tt : Tup c) (n ρ : ℕ) (h : n + 2 * ρ + 2 = D.R.m) (k : ℂ)
    (co : c.Fr n →₀ ℂ) (φ : tt.Ch n → c.Fr n → GA D (c.X n) → ℂ) (hφ : ∀ β y, IsContAut (c.X n) (φ β y))
    (f : GA D (c.V n) → ℂ) (hf : IsContAut (c.V n) f) :
    tt.perF n ρ h (fun β => k • ∑ y' ∈ co.support, co y' • φ β y') f =
      k * ∑ y' ∈ co.support, co y' * tt.perF n ρ h (fun β => φ β y') f := by
  have e : ∀ β, (c.B n ρ h).per c.ψ (k • ∑ y' ∈ co.support, co y' • φ β y') (trc (tt.e n β) f) =
      k * ∑ y' ∈ co.support, co y' * (c.B n ρ h).per c.ψ (φ β y') (trc (tt.e n β) f) := by
    intro β
    have hT : IsContAut _ (trc (tt.e n β) f) :=
      (((GlobalTheory.T.besselPeriod_linear_and_translationCombination D c.ψ hc.std ρ (c.B n ρ h) (fun _ => 0) (contAut_zero _)).2 (tt.e n β) f hf).1)
    rw [per_smul_left]
    congr 1
    exact hPS c.ψ hc.std ρ (c.B n ρ h) (trc (tt.e n β) f) hT (c.Fr n) co.support co (fun y' => φ β y') (fun y' _ => hφ β y')
  simp only [Tup.perF, e]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.mul_sum]



theorem stepX_of_laws : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D →
    RapidVal D → ValMove D → PerSum D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ValX t → TwoX t → RdX t → StepX t := by
  intro hHC D c 𝒯 t hDS hRV hVM hPS hc ht hloc hVal hTwo hRd
  intro j σ h I _ s α ψ G hψ hvan y v
  obtain ⟨χ0, hχ0⟩ := hRd j (by omega)
  have hφ : ∀ i a, IsContAut (c.X j) ((t (s i)).rd j a (ψ i) y) := fun i a => (hχ0 (s i) (ψ i) (hψ i) a y).1
  have hspan : GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) (c.M (j + 1 + 1)) (c.It (j + 1)) := hc.span (j + 1) (by omega)
  simp only [Tup.per]
  refine GlobalTheory.T.period_linear_relation_density_of_unfolding_steps hHC D c 𝒯 t hc j (σ + 1) h I s (fun i => α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)))
    (fun i a => (t (s i)).rd j a (ψ i) y) (fun i => (t (s i)).io j ((t (s i)).io (j + 1) (G i))) ht hφ
    (c.V (j + 1 + 1)) (c.V (j + 1 + 1)) (c.par (j + 1 + 1)) (c.M (j + 1 + 1)) (c.It (j + 1)) hspan ?_ v
  intro P₁ P₂ v''
  have key : ∀ i, ((t (s i)).cI j * (t (s i)).cI (j + 1)) •
      ((t (s i)).io j ((t (s i)).io (j + 1) (G i))).1 (c.It j P₁ (c.It (j + 1) P₂ v'')) =
      liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'') ((t (s i)).pt (j + 1) P₂))
        ((t (s i)).pt j P₁) := by
    intro i
    rw [(ht (s i)).io (j + 1) (by omega) (G i) P₂ v'', liftS_smul, (ht (s i)).io j (by omega) _ P₁ _, smul_smul, mul_comm]
  have e : ∀ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) * (t (s i)).perF j (σ + 1) h (fun a => (t (s i)).rd j a (ψ i) y)
      (((t (s i)).io j ((t (s i)).io (j + 1) (G i))).1 (c.It j P₁ (c.It (j + 1) P₂ v''))) =
      α i * (t (s i)).perF j (σ + 1) h (fun a => (t (s i)).rd j a (ψ i) y)
        (liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
          (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'') ((t (s i)).pt (j + 1) P₂))
          ((t (s i)).pt j P₁)) := by
    intro i
    rw [← key i, perF_smul, mul_assoc]
  rw [Finset.sum_congr rfl fun i _ => e i]
  have hR0 : ∀ i, RapidDec _ ((G i).1 v'') := by
    intro i
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1 + 1) (by omega)
    exact hRV c.θ hc.inf _ _ (c.M (j + 1 + 1)) J χ (G i).1 (hJ (G i).2) v''
  have hR1 : ∀ i, RapidDec _ (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'')
      ((t (s i)).pt (j + 1) P₂)) := by
    intro i
    rw [(ht (s i)).io (j + 1) (by omega) (G i) P₂ v'']
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1) (by omega)
    exact rapidDec_smul _ _ (hRV c.θ hc.inf _ _ (c.M (j + 1)) J χ _ (hJ ((t (s i)).io (j + 1) (G i)).2) _)
  refine GlobalTheory.T.seeSaw_periods_linearRelations_doubleStep D c 𝒯 t hDS hc ht hloc j σ h P₁ P₂ I s α (fun i a => (t (s i)).rd j a (ψ i) y) (fun i => (G i).1 v'')
    hφ hR0 hR1 ?_
  intro a ha a' ha'
  obtain ⟨C, hC, hCe⟩ := hVal j σ h P₁ P₂ a ha a' ha'
  obtain ⟨co, hco⟩ := hTwo j (by omega) C hC y
  obtain ⟨sm, hsm⟩ := GlobalTheory.RealTransSm.rTrans_eq_map D c.θ (c.V (j + 1 + 1)) (c.par (j + 1 + 1)) (c.M (j + 1 + 1)) hc.inf a' ha'
  refine ⟨fun i => (t (s i)).cV j * (t (s i)).perF (j + 1 + 1) σ (idx_step h)
      ((t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C) (rTrans a' ((G i).1 v'')),
    fun i => hCe (s i) (ψ i) (hψ i) y (G i) v'', ?_⟩
  obtain ⟨χ2, hχ2⟩ := hRd (j + 1 + 1) (by omega)
  have hψ'' : ∀ i, (t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i))) ∈ (t (s i)).Ram (j + 1 + 1) := fun i =>
    (ht (s i)).stabK (j + 1) (by omega) _ ((ht (s i)).stabK j (by omega) _ ((ht (s i)).stabS j (by omega) _ (hψ i)))
  have term : ∀ i, α i * ((t (s i)).cV j * (t (s i)).perF (j + 1 + 1) σ (idx_step h)
      ((t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C) (rTrans a' ((G i).1 v''))) =
      ∑ y' ∈ co.support, co y' * (α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1)) *
        (t (s i)).per (j + 1 + 1) σ (idx_step h) ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (G i) y' (sm v'')) := by
    intro i
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1 + 1) (by omega)
    have hw : rTrans a' ((G i).1 v'') = (G i).1 (sm v'') := (hsm J χ (G i).1 (hJ (G i).2) v'').symm
    have htwo : (t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C = fun β =>
        ((t (s i)).cK j * (t (s i)).cK (j + 1)) • ∑ y' ∈ co.support, co y' •
          (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y' :=
      funext (hco (s i) _ ((ht (s i)).stabS j (by omega) _ (hψ i)))
    have hGw : RapidDec _ ((G i).1 (sm v'')) := hRV c.θ hc.inf _ _ (c.M (j + 1 + 1)) J χ (G i).1 (hJ (G i).2) _
    rw [hw, htwo, perF_comb hPS hc _ _ _ _ _ co _ (fun β y' => (hχ2 (s i) _ (hψ'' i) β y').1) _ ⟨hGw.1, hGw.2.1⟩]
    simp only [Tup.per, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl fun i _ => term i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [← Finset.mul_sum, hvan y' (sm v''), mul_zero]

end GlobalTheory.SeeSawStep

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselLattice_splits_along_witt_normalFrames : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.MonoAt ((y.bes j ρ h).lev (a.x j).vol).d (N j) (M j ρ h) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.MonoBes.besLat_monoAt | exact GlobalTheory.MonoBes.besLat_monoAt | (intros; apply GlobalTheory.MonoBes.besLat_monoAt <;> assumption)
end
