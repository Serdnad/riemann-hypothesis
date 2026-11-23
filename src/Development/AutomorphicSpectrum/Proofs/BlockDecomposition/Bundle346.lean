module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle115
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle322
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle324
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormula
public import Formalism.RealPlaceAnalysis.Bundle003
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle323
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.RootOfNe
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped Matrix

namespace GlobalTheory.CompanionTheory.ThetaInv

theorem thetaW_val_apply {A : Type} [CommRing A] (N : ℕ) (g : GL (Fin N) A) (i j : Fin N) :
    (thetaW A N g).1 i j = (g⁻¹).1 (Fin.rev j) (Fin.rev i) := by
  simp [thetaW, invT, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix,
    Matrix.transpose_apply, Fin.revPerm]

theorem thetaW_thetaW_ring {A : Type} [CommRing A] (N : ℕ) (g : GL (Fin N) A) :
    thetaW A N (thetaW A N g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaW_val_apply, ← map_inv, thetaW_val_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]

theorem thetaW_thetaW {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (g : GL (Fin N) k) :
    thetaW k N (thetaW k N g) = g :=
  thetaW_thetaW_ring N g

end GlobalTheory.CompanionTheory.ThetaInv

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcWords

section Maps

variable {α β : Type*}

theorem interleave_map (f : α → β) {u v w : List α} (h : Comb.Interleave u v w) :
    Comb.Interleave (u.map f) (v.map f) (w.map f) := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem shuffle_map (f : α → β) {us : List (List α)} {w : List α} (h : Comb.Shuffle us w) :
    Comb.Shuffle (us.map (List.map f)) (w.map f) := by
  induction h with
  | nil => exact .nil
  | cons _ hi ih => exact .cons ih (interleave_map f hi)

end Maps

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_sNu_iterate (x : CuspT k) (j : ℕ) : (sNu^[j] x).1 = x.1.nu j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    show (sNu^[j] x).1.nu 1 = _
    rw [ih, IrrGL.nu_nu]
    push_cast
    rfl

theorem sNu_injective : Function.Injective (sNu (k := k)) := by
  intro x y h
  have h1 : x.1.nu 1 = y.1.nu 1 := congrArg Subtype.val h
  have h2 := congrArg (fun r => IrrGL.nu r (-1)) h1
  simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h2
  exact Subtype.ext h2

theorem sNu_aperiodic (t : CuspT k) (j : ℕ) (hj : 0 < j) : sNu^[j] t ≠ t := by
  intro h
  have h1 : t.1.nu j = t.1 := (val_sNu_iterate t j).symm.trans (congrArg Subtype.val h)
  have h2 : t.1.nu ((j : ℝ) : ℂ) = t.1 := by simpa using h1
  have h3 : (j : ℝ) = 0 := (IrrGL.nu_ofReal_eq_self t.2.1).1 h2
  have h4 : j = 0 := by exact_mod_cast h3
  omega

theorem toA_injective : Function.Injective (toA (k := k)) := by
  intro Δ Δ' h
  have h1 : Δ.first = Δ'.first := congrArg (fun a => (Comb.ASeg.start a).1) h
  have h2 : Δ.len = Δ'.len := congrArg Comb.ASeg.len h
  exact Segment.ext_first h1 h2

theorem image_carrier (Δ : Segment k) : Subtype.val '' ((toA Δ).carrier sNu) = Δ.carrier := by
  ext x
  rw [Segment.mem_carrier]
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (val_sNu_iterate (toA Δ).start i).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨sNu^[a] (toA Δ).start, ⟨a, ha, rfl⟩, val_sNu_iterate (toA Δ).start a⟩

theorem carrier_subset {Δ Δ' : Segment k} (h : Δ.carrier ⊆ Δ'.carrier) :
    (toA Δ).carrier sNu ⊆ (toA Δ').carrier sNu :=
  (Set.image_subset_image_iff Subtype.val_injective).1 (by rwa [image_carrier, image_carrier])

theorem precedes_of_aPrecedes {Δ Δ' : Segment k} (h : Comb.APrecedes sNu (toA Δ) (toA Δ')) : Δ.Precedes Δ' := by
  obtain ⟨⟨⟨Γ, hΓ⟩, h1, h2⟩, j, hj, hs⟩ := h
  refine ⟨⟨⟨Segment.ofFirst Γ.start.1 Γ.start.2 Γ.len Γ.len_pos, ?_⟩, fun e => h1 (carrier_subset e),
    fun e => h2 (carrier_subset e)⟩, j, hj, ?_⟩
  · have e : toA (Segment.ofFirst Γ.start.1 Γ.start.2 Γ.len Γ.len_pos) = Γ := rfl
    rw [← image_carrier, e, hΓ, Set.image_union, image_carrier, image_carrier]
  · exact (congrArg Subtype.val hs).trans (val_sNu_iterate _ j)

theorem decW_eq (Δ : Segment k) : decW Δ = ((toA Δ).dec sNu).map Subtype.val := by
  apply List.ext_getElem
  · simp [decW, Comb.ASeg.dec, toA]
  · intro i h1 h2
    have hl : i < Δ.len := by simpa [decW] using h1
    simp only [decW, Comb.ASeg.dec, List.getElem_ofFn, List.getElem_map, List.getElem_reverse, List.getElem_range,
      Segment.term, val_sNu_iterate, Fin.val_rev]
    simp only [toA, List.length_range]
    rw [show Δ.len - 1 - i = Δ.len - (i + 1) by omega]

theorem reverse_ofFn {α : Type*} {h : ℕ} (f : Fin h → α) :
    (List.ofFn f).reverse = List.ofFn fun i => f (Fin.rev i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [Fin.rev]
    congr 2
    omega

theorem wtW_eq {h : ℕ} (Δ : Fin h → Segment k) :
    wtW Δ = (Comb.wt sNu ((List.ofFn Δ).map toA)).map Subtype.val := by
  rw [wtW, Comb.wt, List.map_flatten, ← List.map_reverse, reverse_ofFn, List.map_map, List.map_map, List.map_ofFn]
  congr 2
  funext i
  exact decW_eq _

instance : Nonempty (CuspT k) :=
  ⟨⟨IrrGL.ofChar 1 isSmoothChar_one, IrrGL.isCusp_ofChar 1 isSmoothChar_one⟩⟩

theorem inSh_of_inShW {𝔫 : Multiset (Segment k)} {h : ℕ} {Δ : Fin h → Segment k} (H : InShW 𝔫 (wtW Δ)) :
    Comb.InSh sNu (𝔫.map toA) (Comb.wt sNu ((List.ofFn Δ).map toA)) := by
  obtain ⟨Ls, rfl, hS⟩ := H
  have hg : Function.LeftInverse (Function.invFun (Subtype.val : CuspT k → IrrGL (k := k))) Subtype.val :=
    Function.leftInverse_invFun Subtype.val_injective
  have hback : ∀ l : List (CuspT k), (l.map Subtype.val).map (Function.invFun (Subtype.val : CuspT k → IrrGL (k := k))) = l :=
    fun l => by
      rw [List.map_map, hg.comp_eq_id, List.map_id]
  refine ⟨Ls.map toA, by simp, ?_⟩
  have h1 := shuffle_map (Function.invFun (Subtype.val : CuspT k → IrrGL (k := k))) hS
  rw [wtW_eq, hback, List.map_map] at h1
  have h2 : (List.map (Function.invFun (Subtype.val : CuspT k → IrrGL (k := k)))) ∘ decW = Comb.ASeg.dec sNu ∘ toA := by
    funext D
    simp only [Function.comp, decW_eq, hback]
  rw [h2, ← List.map_map] at h1
  exact h1

theorem aOrdered_of_isOrderedForm {h : ℕ} {Δ : Fin h → Segment k} {𝔪 : Multiset (Segment k)}
    (H : IsOrderedForm Δ 𝔪) : Comb.AOrdered sNu ((List.ofFn Δ).map toA) := by
  rw [Comb.AOrdered, List.pairwise_map, List.pairwise_ofFn]
  exact fun i j hij hp => H.2 i j hij (precedes_of_aPrecedes hp)

theorem coe_map_ofFn {h : ℕ} {Δ : Fin h → Segment k} {𝔪 : Multiset (Segment k)} (H : IsOrderedForm Δ 𝔪) :
    (((List.ofFn Δ).map toA : List _) : Multiset _) = 𝔪.map toA := by
  rw [← H.1, Fin.univ_val_map, Multiset.map_coe]

theorem eq_of_inShW_wtW : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (h h' : ℕ) (Δ : Fin h → Segment k)
    (Γ : Fin h' → Segment k), IsOrderedForm Δ 𝔪 → IsOrderedForm Γ 𝔫 → InShW 𝔫 (wtW Δ) → InShW 𝔪 (wtW Γ) → 𝔪 = 𝔫 := by
  intro k _ _ _ _ _ 𝔪 𝔫 h h' Δ Γ hΔ hΓ h1 h2
  have hL := coe_map_ofFn hΔ
  have hM := coe_map_ofFn hΓ
  have key := GlobalTheory.T.shuffle_weight_antisymmetric_eq sNu sNu_injective sNu_aperiodic ((List.ofFn Δ).map toA) ((List.ofFn Γ).map toA)
    (aOrdered_of_isOrderedForm hΔ) (aOrdered_of_isOrderedForm hΓ) (by rw [hM]; exact inSh_of_inShW h1)
    (by rw [hL]; exact inSh_of_inShW h2)
  rw [hL, hM] at key
  exact Multiset.map_injective toA_injective key

end GlobalTheory.CompanionTheory.ZcWords

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.DetPG

def sumSig (a b : Type) : a ⊕ b ≃ Σ x, Two a b x where
  toFun y := match y with
    | Sum.inl i => ⟨false, i⟩
    | Sum.inr j => ⟨true, j⟩
  invFun x := match x with
    | ⟨false, i⟩ => Sum.inl i
    | ⟨true, j⟩ => Sum.inr j
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro ⟨_ | _, _⟩ <;> rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_hpg (i T : ℕ) (h : HPG k i T) :
    GeneralLinearGroup.det ((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) =
      GeneralLinearGroup.det ((pgProj k i T h).1 : GL (Fin (i + 1)) k) *
        GeneralLinearGroup.det (pgProj k i T h).2 := by
  ext
  rw [Units.val_mul, GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
    GeneralLinearGroup.val_det_apply]
  let φ : Fin (i + 1) ⊕ Fin T ≃ Fin (i + T + 1) := (sumSig _ _).trans (ePG i T)
  have hz : ∀ (b : Fin T) (a : Fin (i + 1)),
      (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) : Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k)
        (ePG i T ⟨true, b⟩) (ePG i T ⟨false, a⟩) = 0 := fun b a =>
    mem_parab_iff.1 h.2 true false b a (by decide)
  have hb : (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) :
        Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k).submatrix φ φ =
      fromBlocks (((pgProj k i T h).1 : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k)
        (Matrix.of fun a b => (((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) :
          Matrix (Fin (i + T + 1)) (Fin (i + T + 1)) k) (φ (Sum.inl a)) (φ (Sum.inr b))) 0
        ((pgProj k i T h).2 : Matrix (Fin T) (Fin T) k) := by
    ext x y
    rcases x with a | b <;> rcases y with c | d
    · exact (leviProj_apply k (ePG i T) (hpgIncl k i T h) false a c).symm
    · rfl
    · exact hz b c
    · exact (leviProj_apply k (ePG i T) (hpgIncl k i T h) true b d).symm
  rw [← det_submatrix_equiv_self φ, hb]
  exact det_fromBlocks_zero₂₁ _ _ _

theorem dpowM_hpg (i T : ℕ) (s : ℝ) (h : HPG k i T) :
    dpowM (i + T) s (h : Mir k (i + T)) = dpowM i s (pgProj k i T h).1 * dpow T s (pgProj k i T h).2 := by
  show detChar (Fin (i + T + 1)) (absPow k (s : ℂ)) ((h : Mir k (i + T)) : GL (Fin (i + T + 1)) k) =
    detChar (Fin (i + 1)) (absPow k (s : ℂ)) ((pgProj k i T h).1 : GL (Fin (i + 1)) k) *
      detChar (Fin T) (absPow k (s : ℂ)) (pgProj k i T h).2
  rw [detChar_apply, detChar_apply, detChar_apply, det_hpg, map_mul]

theorem dpow_add' (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n s * dpow n t := by
  ext g
  simp [dpow, Complex.ofReal_add, absPow_add]

theorem dpow_zero' (n : ℕ) : dpow (k := k) n 0 = 1 := by
  ext g
  simp [dpow, absPow_zero]

theorem dpowM_add' (n : ℕ) (s t : ℝ) : dpowM (k := k) n (s + t) = dpowM n s * dpowM n t := by
  ext g
  simp [dpowM, dpow_add']

theorem dpowM_zero' (n : ℕ) : dpowM (k := k) n 0 = 1 := by
  ext g
  simp [dpowM, dpow_zero']

theorem complex_units_mul_eq_one_of_mul_eq_one (A B X Y Z : ℂˣ) (h₁ : A * B = 1) (h₂ : X * Y * Z = 1) : A * X * Y * (B * Z) = 1 := by
  have : A * X * Y * (B * Z) = (A * B) * (X * Y * Z) := by ac_rfl
  rw [this, h₁, h₂, one_mul]

theorem exponents_cancel (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (h : HPG k i (t + 1)) :
    ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ) *
      (((dpowM i (1 / 2) (pgProj k i (t + 1) h).1 : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 : ℂˣ) : ℂ)) = 1 := by
  have e1 : dpowM (k := k) i (-1 / 2) (pgProj k i (t + 1) h).1 * dpowM i (1 / 2) (pgProj k i (t + 1) h).1 = 1 := by
    have : dpowM (k := k) i (-1 / 2 + 1 / 2) = dpowM i (-1 / 2) * dpowM i (1 / 2) := dpowM_add' _ _ _
    rw [show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, dpowM_zero'] at this
    rw [← MonoidHom.mul_apply, ← this, MonoidHom.one_apply]
  have e2 : dpow (k := k) (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 * dpow (t + 1) 1 (pgProj k i (t + 1) h).2 *
      dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2 = 1 := by
    have : dpow (k := k) (t + 1) (-1 / 2 + 1 + -1 / 2) = dpow (t + 1) (-1 / 2) * dpow (t + 1) 1 * dpow (t + 1) (-1 / 2) := by
      rw [dpow_add', dpow_add']
    rw [show (-1 / 2 + 1 + -1 / 2 : ℝ) = 0 by norm_num, dpow_zero'] at this
    rw [← MonoidHom.mul_apply, ← MonoidHom.mul_apply, ← this, MonoidHom.one_apply]
  have e : dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) * dpow (t + 1) 1 (pgProj k i (t + 1) h).2 *
      (dpowM i (1 / 2) (pgProj k i (t + 1) h).1 * dpow (t + 1) (-1 / 2) (pgProj k i (t + 1) h).2) = 1 := by
    rw [dpowM_hpg]
    exact complex_units_mul_eq_one_of_mul_eq_one _ _ _ _ _ e1 e2
  have := congrArg (Units.val) e
  simpa only [Units.val_mul, Units.val_one] using this

end GlobalTheory.CompanionTheory.BZPhiPG.DetPG

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem dpowM_hgp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : ℝ) (h : MirabolicParabolic k (i + 1) t), dpowM ((i + 1) + t) s (h : Mir k ((i + 1) + t)) = dpow (i + 1) s (gpProj k (i + 1) t h).1 * dpow (t + 1) s (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := by
  intro k _ _ _ _ i t s h
  have key : ∀ (n : ℕ) (g : GL (Fin n) k),
      GlobalTheory.BZMir.Leib.dpow n s g = GlobalTheory.SmGL.absPow k (s : ℂ) (Matrix.GeneralLinearGroup.det g) :=
    fun _ _ => rfl
  have hdet : Matrix.GeneralLinearGroup.det
      ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) =
      Matrix.GeneralLinearGroup.det (GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 *
        Matrix.GeneralLinearGroup.det
          (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).2 : GlobalTheory.BZMir.Mir k t) :
            GL (Fin (t + 1)) k) := by
    have hp := GlobalTheory.SmGL.det_parab k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
      (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h)
    rw [Fintype.prod_bool] at hp
    exact hp.trans (mul_comm _ _)
  rw [show GlobalTheory.RgGu.Leib.dpowM ((i + 1) + t) s (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) =
      GlobalTheory.BZMir.Leib.dpow ((i + 1) + t + 1) s
        ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) from rfl,
    key, key, key, hdet, map_mul]

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.twist_twist_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : GRep k n) (s s' : ℝ), GIso ((A.tw s).tw s') (A.tw (s + s')) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw | exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.derivative_functor_twist_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k (j + 1)) W) (t : ℝ),
    Nonempty ((phiMinus k ψ (twist τ (dpowM (j + 1) t))).Equiv (twist (phiMinus k ψ τ) (dpowM j t))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhiTw.phiMinus_twist_equiv | exact GlobalTheory.CompanionTheory.LeibPhiTw.phiMinus_twist_equiv | (intros; apply GlobalTheory.CompanionTheory.LeibPhiTw.phiMinus_twist_equiv <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.twist_product_distributes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (A : GRep k r) (B : GRep k t) (s : ℝ), GIso ((A.prod B).tw s) ((A.tw s).prod (B.tw s)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod | exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.modulus_parabolic_proj_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp | exact GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp <;> assumption)
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.mean_value_formula : Equi → CountBd → MeanVal := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd | exact GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd <;> assumption)
end

section

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeSM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem qminor_restrict {n m t : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (ι : Fin m → Fin n)
    (hι : Function.Injective ι) (a b : Fin t → Fin m) (w : ℂ) :
    qminor (fun a b => E (ι a) (ι b)) a b w = qminor E (ι ∘ a) (ι ∘ b) w := by
  unfold qminor Tm
  simp only [Function.comp, hι.eq_iff]

end GlobalTheory.CompanionTheory.RgHeSM
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SchwartzFib



set_option synthInstance.maxSize 2000 in
theorem exists_real_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n M : ℕ),
    ∃ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _ n M
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let t := GlobalTheory.Core.Rk.RapidInt.tupEquiv F E (Module.finBasis F E) M n
  let L := (Module.finBasis ℝ (Fin n → Fin M → Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F)).equivFun.toContinuousLinearEquiv
  refine ⟨_, t.toAddEquiv.trans L.toLinearEquiv.toAddEquiv, ?_, ?_⟩
  · exact L.continuous.comp t.continuous
  · exact t.symm.continuous.comp L.symm.continuous

end GlobalTheory.CompanionTheory.SW.SchwartzFib
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tensor_product_rank_le_one : ∀ {α : Type} [Fintype α] (M : α → Type) [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)], (∀ a, Module.rank ℂ (M a) ≤ 1) → Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one | exact GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one | (intros; apply GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one <;> assumption)
end
