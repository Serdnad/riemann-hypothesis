module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle369
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle337
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle367
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle368
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle370
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle371
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle372
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle373
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd

theorem _root_.GlobalTheory.T.jacquet_multiplicity_order_embedding : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (zz : Fin n → IrrGL (k := k)) (σ : Fin p ↪o Fin n) (c : Fin n → ℕ), (∀ a, c (σ a) = (zz (σ a)).1) → (∀ j, j ∉ Set.range σ → c j = 0) → ∀ (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N), jm (fun a => zz (σ a)) hz π ≠ 0 → jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (jac f π) ≠ 0 := by
  exact @GlobalTheory.CompanionTheory.WordProd.RowCell.jhMult_row
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibCompact

theorem exists_right_invariant {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (f : cIndSpace H ρ) :
    ∃ S : Set G, IsOpen S ∧ (1 : G) ∈ S ∧ ∀ s ∈ S, ∀ p : G, f.1.1.1 (p * s) = f.1.1.1 p := by
  have hopen : IsOpen {s : G | GlobalTheory.PRep.ind H ρ s f.1.1 = f.1.1} := f.1.2
  refine ⟨_, hopen, ?_, fun s hs p => ?_⟩
  · show GlobalTheory.PRep.ind H ρ 1 f.1.1 = f.1.1
    simp
  · have hs' : GlobalTheory.PRep.ind H ρ s f.1.1 = f.1.1 := hs
    exact congrFun (congrArg Subtype.val hs') p

theorem exists_compact_support {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (f : cIndSpace H ρ) :
    ∃ C : Set G, IsCompact C ∧ ∀ p : G, f.1.1.1 p ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, p = h * c :=
  f.2

section Column

variable (k : Type) [Field k]

def col (n : ℕ) (p : Mir k n) : Fin n → k :=
  fun j => ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc j) (Fin.last n)

theorem last_last (n : ℕ) (p : Mir k n) :
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  have h := congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2) (Fin.last n)
  simpa [GlobalTheory.BZMir.eLast] using h

theorem last_column_entry_product_formula (n : ℕ) (a : Fin n → k) (A : Matrix (Fin n) (Fin n) k)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hP : P (Fin.last n) (Fin.last n) = 1) (j : Fin n) :
    ((1 + colMat k n a) * glEmbMat k n A * P) (Fin.castSucc j) (Fin.last n) =
      a j + (A.mulVec (fun l => P (Fin.castSucc l) (Fin.last n))) j := by
  rw [add_mul, one_mul, GlobalTheory.BZMir.colMat_mul_glEmbMat, add_mul, Matrix.add_apply]
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, Matrix.mulVec,
    dotProduct, hP, Fin.castSucc_ne_last]
  all_goals ring

theorem col_uM_levi_mul (n : ℕ) (a : Fin n → k) (g : GL (Fin n) k) (p : Mir k n) :
    col k n (uM k n a * levi k n g * p) = a + (g : Matrix (Fin n) (Fin n) k).mulVec (col k n p) := by
  funext j
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.last_column_entry_product_formula k n a (g : Matrix (Fin n) (Fin n) k)
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.last_last k n p) j

theorem col_one (n : ℕ) : col k n 1 = 0 := by
  funext j
  simp [GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col, Matrix.one_apply, Fin.castSucc_ne_last]

theorem col_uM_levi (n : ℕ) (a : Fin n → k) (g : GL (Fin n) k) :
    col k n (uM k n a * levi k n g) = a := by
  have h := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi_mul k n a g 1
  rwa [mul_one, GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_one, Matrix.mulVec_zero, add_zero] at h

end Column

section Top

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_midV (i t : ℕ) : Continuous (midV k i t) := by
  refine continuous_pi fun j => ?_
  induction j using Fin.addCases with
  | left l =>
    show Continuous fun v : Fin t → k => Fin.append (0 : Fin i → k) v (Fin.castAdd t l)
    simp only [Fin.append_left, Pi.zero_apply]
    exact continuous_const
  | right l =>
    show Continuous fun v : Fin t → k => Fin.append (0 : Fin i → k) v (Fin.natAdd i l)
    simp only [Fin.append_right]
    exact continuous_apply l

theorem continuous_col_inv (n : ℕ) : Continuous (fun c : Mir k n => col k n c⁻¹) :=
  continuous_pi fun j =>
    (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem (Fin.castSucc j) (Fin.last n)

theorem isLocallyConstant_uM {Z : Type} (n : ℕ) (F : Mir k n → Z) (S : Set (Mir k n)) (hS : IsOpen S)
    (h1 : (1 : Mir k n) ∈ S) (hF : ∀ s ∈ S, ∀ p, F (p * s) = F p) (g : GL (Fin n) k) :
    IsLocallyConstant (fun y : Fin n → k => F (uM k n y * levi k n g)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y₀
  have hu := GlobalTheory.CompanionTheory.BZPsiPG.Cont.continuous_uM k n
  set L := GlobalTheory.BZMir.levi k n g
  let φ : (Fin n → k) → GlobalTheory.BZMir.Mir k n := fun y => L⁻¹ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y - y₀) * L
  have hφ : Continuous φ :=
    (continuous_const.mul (hu.comp (continuous_id.sub continuous_const))).mul continuous_const
  refine ⟨φ ⁻¹' S, hS.preimage hφ, ?_, fun y hy => ?_⟩
  · show L⁻¹ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y₀ - y₀) * L ∈ S
    rw [sub_self, GlobalTheory.CompanionTheory.BZPsiPG.uM_zero, mul_one, inv_mul_cancel]
    exact h1
  · have hadd : GlobalTheory.CompanionTheory.BZPsiPG.uM k n y =
        GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y - y₀) := by
      rw [← GlobalTheory.CompanionTheory.BZPsiPG.uM_add]
      congr 1
      abel
    have hy' : GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * L = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * L * φ y := by
      rw [hadd]
      simp only [φ]
      group
    show F (GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * L) = F (GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * L)
    rw [hy']
    exact hF _ hy _

end Top

theorem fibV_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k), IsLocallyConstant (fibV f g) ∧ HasCompactSupport (fibV f g) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ _ f g
  constructor
  · obtain ⟨S, hS, h1, hSf⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.exists_right_invariant _ _ f
    exact (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.isLocallyConstant_uM k (i + t) _ S hS h1 hSf g).comp_continuous
      (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.continuous_midV k i t)
  · obtain ⟨C, hC, hCf⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.exists_compact_support _ _ f
    let proj : GlobalTheory.BZMir.Mir k (i + t) → Fin t → k := fun c j =>
      -(((g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹) (Fin.natAdd i j))
    have hproj : Continuous proj := continuous_pi fun j =>
      ((continuous_apply (Fin.natAdd i j)).comp
        (continuous_const.matrix_mulVec (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.continuous_col_inv k (i + t)))).neg
    refine HasCompactSupport.of_support_subset_isCompact (hC.image hproj) ?_
    intro v hv
    obtain ⟨h, hh, c, hc, hp⟩ := hCf (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) g) hv
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, q, hxq⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t ⟨h, hh⟩
    have hxq' : h = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) *
        GlobalTheory.BZMir.levi k (i + t) q := hxq
    have key : GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x = GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v +
        (g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹ := by
      rw [← GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi_mul, hp, mul_inv_cancel_right, hxq',
        GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi]
    funext j
    have hj := congrFun key (Fin.natAdd i j)
    simp only [GlobalTheory.CompanionTheory.BZPsiPG.topV, GlobalTheory.CompanionTheory.BZPsiPG.midV, Fin.append_right, Pi.add_apply, Pi.zero_apply] at hj
    show -(((g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹) (Fin.natAdd i j)) = v j
    rw [neg_eq_iff_add_eq_zero, add_comm]
    exact hj.symm

end GlobalTheory.CompanionTheory.BZPsiPG.FibCompact

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.induced_vanishing_on_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (a : cIndSpace (HPG k i t) (hRep τ σ)), (∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), fibV a κ = 0) → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_zero_of_fibV_eq_zero | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_zero_of_fibV_eq_zero | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_zero_of_fibV_eq_zero <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.locally_constant_compact_support_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)),
  IsLocallyConstant (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) ∧
    HasCompactSupport (fun d : Fin (t + 1) → k => evX f (dEmb k i t d * y)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport | exact GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

theorem fibV_one_bump : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → fibV b 1 = (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)).indicator (fun _ => z) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ c K₁ hK z b h1 h2
  funext v
  by_cases hv : v ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c
  · rw [Set.indicator_of_mem (show v ∈ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)) from hv)]
    have hm : midV k i t v ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt (i + t) c := by
      intro j
      induction j using Fin.addCases with
      | left j =>
        show Fin.append (0 : Fin i → k) v (Fin.castAdd t j) ∈ _
        rw [Fin.append_left]
        exact (zero_mem (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt i c)) j
      | right j =>
        show Fin.append (0 : Fin i → k) v (Fin.natAdd i j) ∈ _
        rw [Fin.append_right]
        exact hv j
    have hp : uM k (i + t) (midV k i t v) * levi k (i + t) 1 ∈
        GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK := ⟨_, hm, 1, one_mem _, rfl⟩
    have e := h1 1 _ hp
    rw [map_one] at e
    simpa [fibV] using e
  · rw [Set.indicator_of_notMem (show v ∉ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)) from hv)]
    apply h2
    rintro ⟨h, β, hβ, e⟩
    obtain ⟨x, q, hq⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t h
    obtain ⟨y, hy, b', hb', rfl⟩ := hβ
    rw [hq, uM_levi_mul_uM_levi] at e
    obtain ⟨e1, e2⟩ := uM_levi_inj _ (show uM k (i + t) (midV k i t v) * levi k (i + t) 1 = _ from e)
    have hq' : (q : GL (Fin (i + t)) k) = b'⁻¹ := eq_inv_of_mul_eq_one_left e2.symm
    apply hv
    intro j
    have e3 := congrFun e1 (Fin.natAdd i j)
    have e4 : midV k i t v (Fin.natAdd i j) = v j := Fin.append_right _ _ _
    have e5 : topV k i t x (Fin.natAdd i j) = 0 := Fin.append_right _ _ _
    rw [Pi.add_apply, e4, e5, zero_add, hq'] at e3
    rw [e3]
    exact mulVec_mem_latt (hK (inv_mem hb')) hy _

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ

theorem smInt_zero_fun {X Z : Type} [MeasurableSpace X] [AddCommGroup Z] [Module ℂ Z]
    (μ : MeasureTheory.Measure X) (φ : X → Z) (h : ∀ x, φ x = 0) : smInt μ φ = 0 := by
  unfold smInt
  apply finsum_eq_zero_of_forall_eq_zero
  intro v
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have hempty : φ ⁻¹' {v} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hv (hx.symm.trans (h x))
    rw [hempty]
    simp

theorem mem_of_eq_mul (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k))
    (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (y : Fin (i + t) → k) (g : GL (Fin (i + t)) k)
    (h : HPG k i t) (β : Mir k (i + t)) (hβ : β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK)
    (e : uM k (i + t) y * levi k (i + t) g = (h : Mir k (i + t)) * β) :
    ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b' := by
  obtain ⟨y', _, b', hb', hβe⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_Bgrp.1 hβ
  obtain ⟨x, q, hx⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t h
  have e2 : uM k (i + t) y * levi k (i + t) g =
      uM k (i + t) (topV k i t x + ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y') *
        levi k (i + t) ((q : GL (Fin (i + t)) k) * b') := by
    calc uM k (i + t) y * levi k (i + t) g = (h : Mir k (i + t)) * β := e
      _ = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) *
            (uM k (i + t) y' * levi k (i + t) b') := by rw [hx, hβe]
      _ = _ := GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_levi_mul_uM_levi _ _ _ _ _
  exact ⟨q, b', hb', (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_levi_inj _ e2).2⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ μ c K₁ hK b hb g hg
  have hz : ∀ v, fibV b g v = 0 := by
    intro v
    by_contra hne
    have hex : ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
        uM k (i + t) (midV k i t v) * levi k (i + t) g = (h : Mir k (i + t)) * β := by
      by_contra hno
      exact hne (hb _ hno)
    obtain ⟨h, β, hβ, e⟩ := hex
    exact hg (mem_of_eq_mul k i t c K₁ hK _ g h β hβ e)
  show clT τ W (smInt μ (fibV b g)) = 0
  rw [smInt_zero_fun μ _ hz, map_zero]

end GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fibre_integral_vanishing_open_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ b' ∈ K₁, ∀ g : GL (Fin (i + t)) k, fibV b (g * b') = fibV b g := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibInvK.fibV_mul_right_eq | exact GlobalTheory.CompanionTheory.BZPsiPG.FibInvK.fibV_mul_right_eq | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibInvK.fibV_mul_right_eq <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fibre_subgroup_open_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) → IsOpen (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) ∧ IsCompact (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp | exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.kuenneth_product_local_global : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (d : ℕ), Nonempty (Coord q V d) → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Right.kun_right | exact GlobalTheory.CompanionTheory.KunGlue.Right.kun_right | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Right.kun_right <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.cone_zeta_special_value_denominator_bound : ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ), r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) → ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelValue_mem_zInv' | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelValue_mem_zInv' | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelValue_mem_zInv' <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.ray_class_parametrization_exists : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 → ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.tensor_lift_surjective_kernel_level : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _)) ∧ ∀ z : TensorProduct (Ainf l) (Acris l) A.W, Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _) z = 0 ↔ z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.tens_base_change | exact GlobalTheory.CompanionTheory.PerfFil.tens_base_change | (intros; apply GlobalTheory.CompanionTheory.PerfFil.tens_base_change <;> assumption)
end
