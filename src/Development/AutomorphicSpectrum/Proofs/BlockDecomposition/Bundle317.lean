module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import GroundTheory.AutomorphicForms.GeometricLemmaCells
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle299
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import GroundTheory.AutomorphicForms.InductionParabolicGroups

@[expose] public section

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

section Abstract

variable {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]

def AvgVanish (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ) (f : cIndSpace H σ) (p : G) : Prop :=
  ∃ (L : Subgroup G) (hL : L ≤ U), IsCompact (L : Set G) ∧ ∃ g : cIndSpace H σ,
    f - g ∈ twKer (cInd H σ) L (θ.comp (Subgroup.inclusion hL)) ∧
    (∀ l : L, cInd H σ (l : G) g = ((θ (Subgroup.inclusion hL l) : ℂˣ) : ℂ) • g) ∧
    ∀ u ∈ U, (g : smoothPart (ind H σ)).1.1 (p * u) = 0

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def piPerm (i t : ℕ) : Equiv.Perm (Fin ((i + 1) + t + 1)) :=
  (finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)).trans ((ePG i (t + 1)).symm.trans (eGP (i + 1) t))


variable (k) in
def wGL (i t : ℕ) : GL (Fin ((i + 1) + t + 1)) k where
  val := Equiv.Perm.permMatrix k (piPerm i t)⁻¹
  inv := Equiv.Perm.permMatrix k (piPerm i t)
  val_inv := by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  inv_val := by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]


variable (k) in
def wEl (i t : ℕ) : Mir k ((i + 1) + t + 1) := levi k _ (wGL k i t)


variable (k) in
def sEmb (n : ℕ) : Mir k n →* Mir k (n + 1) := (levi k (n + 1)).comp (Mir k n).subtype


variable (k) in
def dEmb (i t : ℕ) (d : Fin (t + 1) → k) : Mir k ((i + 1) + t + 1) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) d)), MirU_le_Mir k _ ⟨_, rfl⟩⟩


variable (k) in
def Cl (i t : ℕ) : Set (Mir k ((i + 1) + t + 1)) :=
  {p | ∀ c : Fin (i + 1), (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castLE (by omega) c) = 0}


variable (k) in
def castM {a b : ℕ} (h : a = b) : Mir k a ≃* Mir k b := h ▸ MulEquiv.refl _

section Fibre

variable {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))

abbrev sigX : Representation ℂ (HPG k (i + 1) (t + 1)) (τ.V ⊗[ℂ] σ.V) :=
  (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k (i + 1) (t + 1))

abbrev XS : Submodule ℂ (smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))) := cIndSpace (HPG k (i + 1) (t + 1)) (sigX τ σ)

abbrev evX {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (p : Mir k ((i + 1) + (t + 1))) : τ.V ⊗[ℂ] σ.V :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.1 p

abbrev sigC : Representation ℂ (MirabolicParabolic k (i + 1) t) ((psiN τ).V ⊗[ℂ] σ.V) :=
  (extTensor ((psiN τ).tw (((t + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres σ) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProj k (i + 1) t)

abbrev sigO (ψ : AddChar k Circle) : Representation ℂ (HPG k i (t + 1)) ((phiN ψ τ).V ⊗[ℂ] σ.V) :=
  (extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (t + 1))

def qC : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (psiN τ).V ⊗[ℂ] σ.V :=
  LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ

def qO (ψ : AddChar k Circle) : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
  LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ


variable (k) in
def muD (t : ℕ) : @MeasureTheory.Measure (Fin t → k) (borel _) :=
  letI : MeasurableSpace (Fin t → k) := borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  MeasureTheory.Measure.addHaar

def intC (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    τ.V ⊗[ℂ] σ.V :=
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1))
    (fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y))

def intO {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) : τ.V ⊗[ℂ] σ.V :=
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => evX f (dEmb k i t d * y))

def eC (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (m : Mir k ((i + 1) + t)) :
    (psiN τ).V ⊗[ℂ] σ.V :=
  ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m))

def eO (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (m : Mir k (i + (t + 1))) :
    (phiN ψ τ).V ⊗[ℂ] σ.V :=
  ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) •
    qO τ σ ψ (intO f (wEl k i t * sEmb k _ (castM k (by omega) m)))

end Fibre

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Parabolic DoubleCoset

namespace GlobalTheory.CompanionTheory.Rodier.CellOrder

def blkNat {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (i : Fin N) : ℕ :=
  ((blk (stdBlocks d hd) i : Fin h) : ℕ)

def idxNat {N : ℕ} (i : Fin N) : ℕ := i

theorem card_filter_le_of_antitone {N : ℕ} (β : Fin N → ℕ) (u w : Equiv.Perm (Fin N))
    (hu : Antitone (β ∘ u)) (a b : ℕ) :
    (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (w j)).card ≤
      (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (u j)).card := by
  classical
  by_cases hsub : ∀ j : Fin N, (j : ℕ) ≤ b → a ≤ β (u j)
  · apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, hsub j hj.1⟩
  · push Not at hsub
    obtain ⟨i, hib, hia⟩ := hsub
    have hdown : ∀ j : Fin N, a ≤ β (u j) → (j : ℕ) ≤ b := by
      intro j hj
      by_contra hjb
      push Not at hjb
      have hij : i ≤ j := by
        rw [Fin.le_iff_val_le_val]
        omega
      exact absurd (le_trans hj (hu hij)) (not_le.2 hia)
    have e1 : (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (u j)) =
        Finset.univ.filter fun j : Fin N => a ≤ β (u j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hdown j h, h⟩⟩
    rw [e1]
    calc (Finset.univ.filter fun j : Fin N => (j : ℕ) ≤ b ∧ a ≤ β (w j)).card
        ≤ (Finset.univ.filter fun j : Fin N => a ≤ β (w j)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact hj.2
      _ = (Finset.univ.filter fun j : Fin N => a ≤ β (u j)).card := by
          apply Finset.card_bij' (fun j _ => u.symm (w j)) (fun j _ => w.symm (u j)) <;> simp_all

theorem exists_diag_mul_unip {k : Type} [Field k] {N : ℕ} (b : GL (Fin N) k)
    (hb : b ∈ blockUpper k N (idxNat (N := N))) :
    ∃ t : GL (Fin N) k, (∀ i j, i ≠ j → (t : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∃ n ∈ unipB k (Fin N), b = t * n := by
  classical
  have hb' : (b : Matrix (Fin N) (Fin N) k).BlockTriangular id := fun i j h => hb h
  have hdet : ∏ i, (b : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
    rw [← Matrix.det_of_upperTriangular hb']
    exact (Matrix.isUnits_det_units b).ne_zero
  have hD : ∀ i, (b : Matrix (Fin N) (Fin N) k) i i ≠ 0 :=
    fun i => (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  let D : Fin N → k := fun i => (b : Matrix (Fin N) (Fin N) k) i i
  let t : GL (Fin N) k := ⟨Matrix.diagonal D, Matrix.diagonal D⁻¹, by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hD i), by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (hD i)⟩
  refine ⟨t, fun i j hij => Matrix.diagonal_apply_ne _ hij, t⁻¹ * b, ?_, (mul_inv_cancel_left t b).symm⟩
  have hval : ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal D⁻¹ * (b : Matrix (Fin N) (Fin N) k) := rfl
  have hP : ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular
      (GlobalTheory.SmGL.blk (GlobalTheory.SmGL.points (Fin N))) := by
    rw [hval]
    exact (Matrix.blockTriangular_diagonal _).mul (fun i j h => hb h)
  show t⁻¹ * b ∈ GlobalTheory.SmGL.unipRad k (GlobalTheory.SmGL.points (Fin N))
  unfold GlobalTheory.SmGL.unipRad
  rw [Subgroup.mem_map]
  refine ⟨⟨t⁻¹ * b, hP⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  funext a
  apply Units.ext
  ext x y
  change ((t⁻¹ * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) a a = (1 : Matrix Unit Unit k) x y
  rw [hval, Matrix.diagonal_mul, Subsingleton.elim x y, Matrix.one_apply_eq]
  exact inv_mul_cancel₀ (hD a)

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem parab_eq_blockUpper :
    parab k (stdBlocks d hd) = blockUpper k N (blkNat d hd) := by
  ext g
  exact Iff.rfl


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem unipB_le_blockUpper : unipB k (Fin N) ≤ blockUpper k N (idxNat (N := N)) := by
  intro g hg
  obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.1 hg
  exact fun i j h => p.2 h

theorem cell_eq_doubleCoset (w : Equiv.Perm (Fin N)) :
    cell k d hd w = doubleCoset (pm k w) (blockUpper k N (blkNat d hd) : Set (GL (Fin N) k))
      (blockUpper k N (idxNat (N := N))) := by
  ext g
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨p, hp, n, hn, rfl⟩
    rw [parab_eq_blockUpper] at hp
    exact ⟨p, hp, n, unipB_le_blockUpper k hn, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    obtain ⟨t, ht, n, hn, rfl⟩ := exists_diag_mul_unip q hq
    refine ⟨p * (pm k w * t * (pm k w)⁻¹), ?_, n, hn, by group⟩
    rw [parab_eq_blockUpper]
    refine Subgroup.mul_mem _ hp ?_
    unfold pm
    rw [GroundTheory.Automorphic.Parabolic.conj_permGL_mem_blockUpper_iff]
    intro i j hij
    exact ht i j (fun h => by subst h; exact lt_irrefl _ hij)

theorem antitone_blkNat_wOpen : Antitone (blkNat d hd ∘ wOpen d hd) := by
  intro i j hij
  have hm := Tuple.monotone_sort (wKey d hd) hij
  simp only [Function.comp_apply] at hm ⊢
  unfold wOpen blkNat
  unfold wKey at hm
  rcases (Prod.Lex.toLex_le_toLex).1 hm with h1 | ⟨h1, -⟩
  · exact (Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 h1)).le
  · exact le_of_eq (congrArg Fin.val (OrderDual.toDual_inj.1 h1)).symm

theorem cellRank_le_wOpen (w : Equiv.Perm (Fin N)) (a b : ℕ) :
    cellRank (blkNat d hd) idxNat (pm k w) a b ≤
      cellRank (blkNat d hd) idxNat (pm k (wOpen d hd)) a b := by
  unfold pm
  rw [GroundTheory.Automorphic.Parabolic.cellRank_permGL, GroundTheory.Automorphic.Parabolic.cellRank_permGL]
  exact card_filter_le_of_antitone (blkNat d hd) (wOpen d hd) w (antitone_blkNat_wOpen d hd) a b

theorem cells_cover_height :
    (∀ g : GL (Fin N) k, ∃ w, g ∈ cell k d hd w) ∧ ∃ ht : GL (Fin N) k → ℕ,
      (∀ w, ∀ g ∈ cell k d hd w, ht g = ht (pm k w)) ∧
      (∀ w, closure (cell k d hd w) ⊆ cell k d hd w ∪ {x | ht x < ht (pm k w)}) ∧
      ∀ w, cell k d hd w ≠ cell k d hd (wOpen d hd) → ht (pm k w) < ht (pm k (wOpen d hd)) := by
  refine ⟨fun g => ?_, GroundTheory.Automorphic.Parabolic.cellHeight (blkNat d hd) idxNat, fun w g hg => ?_,
    fun w => ?_, fun w hw => ?_⟩
  · obtain ⟨w, hw⟩ := GroundTheory.Automorphic.Parabolic.exists_permGL_mem_doubleCoset
      (F := k) (β := blkNat d hd) (γ := idxNat) g
    refine ⟨w, ?_⟩
    rw [cell_eq_doubleCoset]
    exact hw
  · rw [cell_eq_doubleCoset] at hg
    exact GroundTheory.Automorphic.Parabolic.cellHeight_of_mem_doubleCoset hg
  · rw [cell_eq_doubleCoset]
    exact GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset _
  · by_contra hle
    push Not at hle
    have hr := GroundTheory.Automorphic.Parabolic.cellRank_eq_of_le_of_cellHeight_le
      (fun a b => cellRank_le_wOpen k d hd w a b) hle
    have hmem := GroundTheory.Automorphic.Parabolic.mem_doubleCoset_of_cellRank_eq hr
    apply hw
    rw [cell_eq_doubleCoset, cell_eq_doubleCoset, DoubleCoset.doubleCoset_eq_of_mem hmem]

theorem cells_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ g : GL (Fin N) k, ∃ w, g ∈ cell k d hd w) ∧ ∃ ht : GL (Fin N) k → ℕ, (∀ w, ∀ g ∈ cell k d hd w, ht g = ht (pm k w)) ∧ (∀ w, closure (cell k d hd w) ⊆ cell k d hd w ∪ {x | ht x < ht (pm k w)}) ∧ ∀ w, cell k d hd w ≠ cell k d hd (wOpen d hd) → ht (pm k w) < ht (pm k (wOpen d hd)) := by
  intro k _ _ _ _ h N d hd
  exact cells_cover_height k d hd

end GlobalTheory.CompanionTheory.Rodier.CellOrder
end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

theorem ses_of_subQuot {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {ρ₃ : Representation ℂ G V₃} (S : Subrepresentation ρ₂) (e₁ : (subQuot S ⊥).Equiv ρ₁)
    (e₂ : (subQuot ⊤ S).Equiv ρ₃) : Ses ρ₁ ρ₂ ρ₃ := by
  let p : Submodule ℂ S.toSubmodule :=
    (⊥ : Subrepresentation ρ₂).toSubmodule.comap S.toSubmodule.subtype
  have hp : p = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    exact (Submodule.mem_bot ℂ).2 (Subtype.ext hs)
  let q : S.toSubmodule ≃ₗ[ℂ] (S.toSubmodule ⧸ p) :=
    LinearEquiv.ofBijective p.mkQ ⟨by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]; exact hp, p.mkQ_surjective⟩
  have hq : ∀ (x : G) (w : S.toSubmodule ⧸ p),
      (q.symm (subQuot S ⊥ x w) : V₂) = ρ₂ x (q.symm w : V₂) := by
    intro x w
    obtain ⟨s, rfl⟩ := q.surjective w
    have : subQuot S ⊥ x (q s) = q (S.toRepresentation x s) := rfl
    rw [this, q.symm_apply_apply, q.symm_apply_apply]
    rfl
  let t : V₂ →ₗ[ℂ] (⊤ : Subrepresentation ρ₂).toSubmodule :=
    LinearMap.codRestrict _ LinearMap.id (fun _ => trivial)
  let r : Submodule ℂ (⊤ : Subrepresentation ρ₂).toSubmodule :=
    S.toSubmodule.comap (⊤ : Subrepresentation ρ₂).toSubmodule.subtype
  let f : V₁ →ₗ[ℂ] V₂ :=
    S.toSubmodule.subtype ∘ₗ q.symm.toLinearMap ∘ₗ e₁.toLinearEquiv.symm.toLinearMap
  let g : V₂ →ₗ[ℂ] V₃ := e₂.toLinearEquiv.toLinearMap ∘ₗ r.mkQ ∘ₗ t
  have hf1 : ∀ v, f v = (q.symm (e₁.symm v) : V₂) := fun _ => rfl
  have hg1 : ∀ v, g v = e₂ (r.mkQ (t v)) := fun _ => rfl
  refine ⟨f, g, fun x v => ?_, fun x v => ?_, ?_, ?_, ?_⟩
  · rw [hf1, hf1, eint e₁.symm, hq]
  · rw [hg1, hg1, ← eint e₂]
    rfl
  · intro a b hab
    exact e₁.symm.injective (q.symm.injective (Subtype.ext hab))
  · intro c
    obtain ⟨w, rfl⟩ := e₂.surjective c
    obtain ⟨⟨v, hv⟩, rfl⟩ := r.mkQ_surjective w
    exact ⟨v, rfl⟩
  · ext v
    constructor
    · rintro ⟨a, rfl⟩
      rw [LinearMap.mem_ker, hg1, hf1]
      have : r.mkQ (t (q.symm (e₁.symm a) : V₂)) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact (q.symm (e₁.symm a)).2
      rw [this, map_zero]
    · intro hv
      rw [LinearMap.mem_ker, hg1] at hv
      have h0 : r.mkQ (t v) = 0 := e₂.injective (hv.trans (map_zero e₂).symm)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      have hvS : v ∈ S.toSubmodule := h0
      refine ⟨e₁ (q ⟨v, hvS⟩), ?_⟩
      rw [hf1, e₁.symm_apply_apply, q.symm_apply_apply]

theorem ses_of_mext (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (A B C : MRep k n) : MExt A B C → Ses A.ρ B.ρ C.ρ := by
  rintro ⟨S, ⟨e₁⟩, ⟨e₂⟩⟩
  exact ses_of_subQuot S e₁ e₂

end GlobalTheory.CompanionTheory.LeibOrd

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeLiftEx

theorem exists_unit_lift {B : Type} [CommRing B] (J : Ideal B) (hJ : ∀ x ∈ J, IsNilpotent x) (u : (B ⧸ J)ˣ) :
    ∃ w : Bˣ, Ideal.Quotient.mk J (w : B) = (u : B ⧸ J) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ J)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (B ⧸ J)ˣ) : B ⧸ J)
  have hmem : a * b - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hb, Units.mul_inv, map_one, sub_self]
  have hu : IsUnit (a * b) := by
    have := (hJ _ hmem).isUnit_one_add
    simpa using this
  exact ⟨(isUnit_of_mul_isUnit_left hu).unit, by simpa using ha⟩

theorem nonempty_cLiftK : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (s : ℕ), Nonempty (CLiftK (KS q s (𝒱D D)).ι D) := by
  intro K _ X q D s
  have hp : ∀ c : (KS q s (𝒱D D)).FullSubcategory,
      ∃ p : Spec (CommRingCat.of (c.obj.B ⧸ c.obj.J)) ⟶ D.Y, p ≫ D.f = pt c.obj := by
    intro c
    obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := c.property.2
    have hr : Set.range (pt c.obj) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt c.obj) hr ≫ σ, ?_⟩
    rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]
  choose p hp using hp
  have hw : ∀ {c c' : (KS q s (𝒱D D)).FullSubcategory} (φ : c ⟶ c'),
      ∃ w : (((KS q s (𝒱D D)).ι).obj c').Bˣ, ∀ (h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f),
        Ideal.Quotient.mk (((KS q s (𝒱D D)).ι).obj c').J w = (Scheme.ΓSpecIso (CommRingCat.of ((((KS q s (𝒱D D)).ι).obj c').B ⧸ (((KS q s (𝒱D D)).ι).obj c').J))).hom.hom
          (D.u (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) (p c') h) := by
    intro c c' φ
    by_cases h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f
    · obtain ⟨w, hw⟩ := exists_unit_lift (((KS q s (𝒱D D)).ι).obj c').J
        (fun x hx => GlobalTheory.CompanionTheory.SiteNil.thick_J_isNilpotent _ x hx)
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((((KS q s (𝒱D D)).ι).obj c').B ⧸ (((KS q s (𝒱D D)).ι).obj c').J))).hom.hom.toMonoidHom
          (D.u _ _ h))
      exact ⟨w, fun _ => hw⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose w hw using @hw
  exact ⟨{ p := p, hp := hp, w := fun φ => w φ, hw := fun φ h => hw φ h }⟩

end GlobalTheory.CompanionTheory.ConeLiftEx
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_cech_cohomology_finite : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ),
    Module.Finite O ((cechH (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) r).cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.GrCech.main_thm | exact GlobalTheory.CompanionTheory.GrCech.main_thm | (intros; apply GlobalTheory.CompanionTheory.GrCech.main_thm <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

theorem _root_.GlobalTheory.T.divided_power_envelope_expansion : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (z : (pq B).P), ∃ b : ℕ →₀ B, z = b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1) := by
  first | exact @GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow | exact GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow | (intros; apply GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow <;> assumption)
end
