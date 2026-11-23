module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AutomorphicArithmetic.LocalEmbeddings.ArchSz
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle015

@[expose] public section

section

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

open Matrix in
theorem UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame_fin :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {a' : ℕ} (σ : A ⊕ Fin a' ≃ D) (X : Matrix A D k), IsPrimFrame (GlobalTheory.SplitFlip.stdLat k D) X → ∃ κ ∈ GlobalTheory.SplitWeil.KO k D, X = X0 k σ * (invT κ).val := by
  intro k _ _ _ _ A D _ _ _ _ a' σ X hX
  have hXint : ∀ i j, X i j ∈ 𝒪[k] := mem_matLat_stdLat.1 hX.2.1
  obtain ⟨R, hRint, hXR⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hX
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).1 hX.1
  set Y : Matrix (Fin a') D k := Y0 k σ * (h : Matrix D D k) with hYeq
  have hYX : Y * X.transpose = 0 := by
    rw [hh]
    exact frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero σ h
  have hYrank : Y.rank = a' := by
    have hY0 : Y0 k σ * (Y0 k σ).transpose = 1 := by
      ext i j
      simp [Y0, Matrix.mul_apply, Matrix.one_apply, Finset.sum_ite_eq']
    have hW : Y * (((h⁻¹ : GL D k) : Matrix D D k) * (Y0 k σ).transpose) = 1 := by
      rw [hYeq, Matrix.mul_assoc, ← Matrix.mul_assoc (h : Matrix D D k), ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.one_mul, hY0]
    have h1 := Matrix.rank_mul_le_left Y (((h⁻¹ : GL D k) : Matrix D D k) * (Y0 k σ).transpose)
    rw [hW, Matrix.rank_one, Fintype.card_fin] at h1
    have h2 := Matrix.rank_le_card_height Y
    rw [Fintype.card_fin] at h2
    omega
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.PrimFrameExist.exists_gl_mul_isPrimFrame k a' D (fun _ => 1) Y hYrank
  set Y' : Matrix (Fin a') D k := (g₀ : Matrix (Fin a') (Fin a') k) * Y with hY'eq
  have hY'prim : IsPrimFrame (stdLat k D) Y' := hg₀
  have hY'int : ∀ i j, Y' i j ∈ 𝒪[k] := mem_matLat_stdLat.1 hY'prim.2.1
  obtain ⟨S, hSint, hY'S⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hY'prim
  have hY'X : Y' * X.transpose = 0 := by
    rw [hY'eq, Matrix.mul_assoc, hYX, Matrix.mul_zero]
  have hRX : R.transpose * X.transpose = 1 := by
    rw [← Matrix.transpose_mul, hXR, Matrix.transpose_one]
  set S' : Matrix D (Fin a') k := S - X.transpose * (R.transpose * S) with hS'eq
  have hRS' : R.transpose * S' = 0 := by
    rw [hS'eq, Matrix.mul_sub, ← Matrix.mul_assoc, hRX, Matrix.one_mul, sub_self]
  have hY'S' : Y' * S' = 1 := by
    rw [hS'eq, Matrix.mul_sub, ← Matrix.mul_assoc, hY'X, Matrix.zero_mul, sub_zero, hY'S]
  have mulInt : ∀ {m n o : Type} [Fintype n] (P : Matrix m n k) (Q : Matrix n o k),
      (∀ i j, P i j ∈ 𝒪[k]) → (∀ i j, Q i j ∈ 𝒪[k]) → ∀ i j, (P * Q) i j ∈ 𝒪[k] := by
    intro m n o _ P Q hP hQ i j
    rw [Matrix.mul_apply]
    exact sum_mem fun x _ => mul_mem (hP _ _) (hQ _ _)
  have hS'int : ∀ i j, S' i j ∈ 𝒪[k] := by
    intro i j
    rw [hS'eq, Matrix.sub_apply]
    refine sub_mem (hSint i j) ?_
    exact mulInt _ _ (fun a b => hXint b a) (mulInt _ _ (fun a b => hRint b a) hSint) i j
  let K : Matrix D D k := (Matrix.fromRows R.transpose Y').submatrix σ.symm (Equiv.refl D)
  let N : Matrix D D k := (Matrix.fromCols X.transpose S').submatrix (Equiv.refl D) σ.symm
  have hKN : K * N = 1 := by
    simp only [K, N]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromRows_mul_fromCols, hRX, hRS', hY'X, hY'S',
      Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  have hNK : N * K = 1 := mul_eq_one_comm.1 hKN
  let κ : GL D k := ⟨K, N, hKN, hNK⟩
  refine ⟨κ, ?_, ?_⟩
  · rw [mem_KO_iff]
    constructor
    · intro e d
      show K e d ∈ 𝒪[k]
      simp only [K, Matrix.submatrix_apply, Equiv.refl_apply]
      rcases σ.symm e with i | j
      · simpa using hRint d i
      · simpa using hY'int j d
    · intro d e
      show N d e ∈ 𝒪[k]
      simp only [N, Matrix.submatrix_apply, Equiv.refl_apply]
      rcases σ.symm e with i | j
      · simpa using hXint i d
      · simpa using hS'int d j
  · ext i d
    rw [frameMatrixFirstColumnBlock_mul_apply]
    show X i d = N d (σ (Sum.inl i))
    simp [N]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace UpperTheory.IteratedPhiSize

open GlobalTheory.StepData ValuativeRel Formalism.L2.Host GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim MeasureTheory

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {K : Type} [Field K] (ι τ : K →+* ℂ)

private theorem lam_principal_un {a : Type*} [Fintype a] [DecidableEq a] (g : (TypeDatum.principal k a).J) :
    Un ι τ (((TypeDatum.principal k a).lam g : ℂˣ) : ℂ) := by
  change Un ι τ ((1 : ℂˣ) : ℂ)
  rw [Units.val_one]
  exact Un.one

private theorem lam_reindex_un {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (P : TypeDatum k a)
    (e : a ≃ b) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ)) (g : (P.reindex e).J) :
    Un ι τ (((P.reindex e).lam g : ℂˣ) : ℂ) :=
  hP _

private theorem lam_step_un {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (P : TypeDatum k a)
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ)) (hμF : ∀ x, Un ι τ ((μ x : ℂˣ) : ℂ))
    (h : (P.step t μ hμ).J) : Un ι τ (((P.step t μ hμ).lam h : ℂˣ) : ℂ) := by
  rw [P.step_lam μ hμ h (P.corner h) (P.corner_val h), Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  exact ((hP _).mul (hμF _).inv).mul (hμF _)

private theorem lam_iter_un {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ))
    (hμF : ∀ j x, Un ι τ ((μ j x : ℂˣ) : ℂ)) (j : ℕ) : ∀ g, Un ι τ (((P.iter t μ hμ j).lam g : ℂˣ) : ℂ) := by
  induction j with
  | zero => exact lam_reindex_un ι τ P _ hP
  | succ j ih => exact lam_reindex_un ι τ _ _ (lam_step_un ι τ _ _ _ ih (hμF _))

private theorem Phi_sz {a t : Type*} [Fintype a] [DecidableEq a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ)
    (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ)) (hμF : ∀ x, Un ι τ ((μ x : ℂˣ) : ℂ)) (x : Matrix (a ⊕ t) a k) :
    Sz ι τ (P.Phi t μ x) 1 := by
  by_cases h : P.Phi t μ x = 0
  · rw [h]; exact Sz.zero zero_le_one
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
    rw [P.Phi_of_mem μ ⟨g, hg⟩ e h2, Units.val_inv_eq_inv_val]
    exact ((hP _).mul (hμF _).inv).sz

private theorem iterPhi_sz {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ))
    (hμF : ∀ j x, Un ι τ ((μ j x : ℂˣ) : ℂ)) (j : ℕ) (x : Matrix (Ix r t (j + 1)) (Ix r t j) k) :
    Sz ι τ (P.iterPhi t μ hμ j x) 1 :=
  Phi_sz ι τ _ _ (lam_iter_un ι τ P μ hμ hP hμF j) (hμF _) _

private theorem parPhi_sz {r s s' : Type*} [Fintype r] [DecidableEq r] (δ : kˣ →* ℂˣ)
    (hδ : ∀ x, Un ι τ ((δ x : ℂˣ) : ℂ)) (x : Matrix (r ⊕ s) (r ⊕ s') k) : Sz ι τ (parPhi δ x) 1 := by
  by_cases h : parPhi δ x = 0
  · rw [h]; exact Sz.zero zero_le_one
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 h
    rw [parPhi_of_mem δ hg e h21 h12 h22, Units.val_inv_eq_inv_val]
    exact (hδ _).inv.sz

private theorem indicator_one_sz {X : Type*} (S : Set X) (x : X) : Sz ι τ (S.indicator (1 : X → ℂ) x) 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs
  · exact Sz.one
  · exact Sz.zero zero_le_one

end Local

section Global

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {K : Type} [Field K] (ι τ : K →+* ℂ)
  (w : Pl D.host.E)

private theorem muBase_un (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (c : ℕ) (x : (Kw w)ˣ) :
    Un ι τ (((muBase L c).loc w x : ℂˣ) : ℂ) := by
  rcases c with _ | c
  · simpa [muBase, HChar.loc] using (Un.one : Un ι τ 1)
  · simp only [muBase]
    split_ifs with h
    · exact hmu _ _
    · simpa [HChar.loc] using (Un.one : Un ι τ 1)

variable {t : T} (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (hxi : ∀ x, Un ι τ ((L.xiH t).loc w x : ℂ))
include hmu hxi

private theorem stepFn_sz (j : ℕ) (x) : Sz ι τ (stepFn L t w j x) 1 := by
  unfold stepFn
  split_ifs
  · refine iterPhi_sz ι τ _ _ _ (lam_principal_un ι τ) (fun c y => ?_) _ _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact (muBase_un ι τ w hmu c y).inv
  · refine parPhi_sz ι τ _ (fun y => ?_) _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact (hxi y).inv
  · exact indicator_one_sz ι τ _ _

private theorem givenDatum_sz (B : Frames G) (Φ : G.Datum) (b : Edge) (x) : Sz ι τ (givenDatum t w B Φ b x) 1 := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · rcases i with _ | i
    · simp only [givenDatum]
      exact stepFn_sz ι τ w hmu hxi _ _
    · simp only [givenDatum]
      exact Sz.zero zero_le_one
  · rcases j with _ | j
    · simp only [givenDatum]
      split_ifs
      · exact indicator_one_sz ι τ _ _
      · exact Sz.zero zero_le_one
    · simp only [givenDatum]
      exact Sz.zero zero_le_one

end Global

end UpperTheory.IteratedPhiSize

theorem UpperTheory.localGrid_tensor_size_le_one_of_unimodular :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {K : Type} [Field K] (ι τ : K →+* ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E), (∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) → (∀ x, Un ι τ ((L.xiH t).loc w x : ℂ)) → ∀ z : (locGrid G t w).Args, Sz ι τ ((givenStage t w B Φ).tensor z) 1 := by
  intro D T L sc G K _ ι τ B t Φ w hmu hxi z
  show Sz ι τ ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b (z b)).prod 1
  refine Sz.list_prod fun y hy => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
  exact UpperTheory.IteratedPhiSize.givenDatum_sz ι τ w hmu hxi B Φ b _
end
