module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviFubini

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev parB {a b n : ℕ} (h : a + b = n) (w : Pl E) : Subgroup (GLw n w) :=
  GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))

def levH {a b n : ℕ} (h : a + b = n) (w : Pl E) : parB h w →* GLw a w × GLw b w :=
  (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom.comp
    (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)))

theorem blk_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blk h w m X ∈ parB h w := by
  rw [GlobalTheory.SmGL.mem_parab_two]
  intro j i
  rw [CtLevel.blk_val]
  show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
    (CtLevel.blkEq h (Sum.inr j)) (CtLevel.blkEq h (Sum.inl i)) = 0
  simp

theorem blk_mul_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) (m m' : GLw a w × GLw b w)
    (X X' : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m X * blk h w m' X' = blk h w (m * m') (X' + (m'.1⁻¹).val * X * m'.2.val) := by
  ext1
  rw [Units.val_mul, CtLevel.blk_val, CtLevel.blk_val, CtLevel.blk_val, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, fromBlocks_multiply]
  congr 1
  simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add,
    Matrix.mul_add]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (m'.1.val) ((m'.1⁻¹ : GLw a w).val), Units.mul_inv, Matrix.one_mul]

theorem blk_one_zero {a b n : ℕ} (h : a + b = n) (w : Pl E) : blk h w 1 0 = 1 := by
  ext1
  rw [CtLevel.blk_val, Prod.fst_one, Prod.snd_one, Units.val_one, Units.val_one, Matrix.mul_zero, fromBlocks_one,
    reindex_apply, submatrix_one_equiv]
  rfl

def sM {a b n : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* parB h w where
  toFun m := ⟨blk h w m 0, blk_mem h w m 0⟩
  map_one' := Subtype.ext (blk_one_zero h w)
  map_mul' m m' := Subtype.ext (by simp [blk_mul_blk])

def uN {a b n : ℕ} (h : a + b = n) (w : Pl E) : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* parB h w where
  toFun X := ⟨blk h w 1 (Multiplicative.toAdd X), blk_mem h w 1 _⟩
  map_one' := Subtype.ext (by simpa using blk_one_zero h w)
  map_mul' X Y := Subtype.ext (by simp [blk_mul_blk, add_comm])

theorem sM_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    (sM h w m : GLw n w) = blk h w m 0 := rfl

theorem uN_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    (uN h w X : GLw n w) = blk h w 1 (Multiplicative.toAdd X) := rfl

theorem sM_mul_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    ((sM h w m * uN h w X : parB h w) : GLw n w) = blk h w m (Multiplicative.toAdd X) := by
  rw [Subgroup.coe_mul, sM_val, uN_val, blk_mul_blk]
  simp

theorem levH_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : levH h w ⟨blk h w m X, blk_mem h w m X⟩ = m := by
  have key : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x),
      ((GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ x :
        GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j = ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m x : GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j := by
    intro x i j
    rw [GlobalTheory.SmGL.leviProj_apply, CtLevel.blk_val]
    cases x
    · show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
        (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = _
      simp [GlobalTheory.SmGL.leviTwo]
    · show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
        (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = _
      simp [GlobalTheory.SmGL.leviTwo]
  have : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ =
      GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m := by
    funext x; exact Units.ext (Matrix.ext fun i j => key x i j)
  simp only [levH, MonoidHom.coe_comp, Function.comp_apply, this]
  simp

theorem levH_sM {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) : levH h w (sM h w m) = m :=
  levH_blk h w m 0

theorem levH_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    levH h w (uN h w X) = 1 :=
  levH_blk h w 1 _

theorem uN_injective {a b n : ℕ} (h : a + b = n) (w : Pl E) : Function.Injective (uN h w) := by
  intro X Y hXY
  have h1 := congrArg (fun p : parB h w => ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hXY
  simp only [uN_val, CtLevel.blk_val] at h1
  have h2 := congrArg (fun M => M.toBlocks₁₂) ((reindex (CtLevel.blkEq h) (CtLevel.blkEq h)).injective h1)
  simpa using h2

theorem exists_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (p : parB h w) (hp : levH h w p = 1) :
    ∃ X, uN h w X = p := by
  have hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) p = 1 := by
    have := congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) hp
    simpa [levH] using this
  have hd : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x),
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, i⟩) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, j⟩) =
        (1 : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j := by
    intro x i j
    rw [← GlobalTheory.SmGL.leviProj_apply, hl]
    rfl
  have h0 := (GlobalTheory.SmGL.mem_parab_two _).1 p.2
  refine ⟨Multiplicative.ofAdd
    ((((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).submatrix (CtLevel.blkEq h) (CtLevel.blkEq h)).toBlocks₁₂),
    Subtype.ext (Units.ext ?_)⟩
  rw [uN_val, CtLevel.blk_val]
  refine Matrix.ext fun i j => ?_
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [fromBlocks_apply₁₁]
    exact (hd false i j).symm
  · simp [toBlocks₁₂]
  · rw [fromBlocks_apply₂₁]
    exact (h0 i j).symm
  · rw [fromBlocks_apply₂₂]
    exact (hd true i j).symm

end GlobalTheory.LeviFubini
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.eventually_definiteUnitaryLocalPoint_mem_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, locPt w γ ∈ KL n w := by
  first | exact @GlobalTheory.BCT.GoodInt.locPt_mem_KL | exact GlobalTheory.BCT.GoodInt.locPt_mem_KL | (intros; apply GlobalTheory.BCT.GoodInt.locPt_mem_KL <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.eventually_finiteAdelicUnitaryComponent_mem_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ x : finU (E := E) (n := n), ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  first | exact @GlobalTheory.BCT.LocAE.eventually_mem_KL | exact GlobalTheory.BCT.LocAE.eventually_mem_KL | (intros; apply GlobalTheory.BCT.LocAE.eventually_mem_KL <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.norm_complexEmbedding_entry_definiteUnitaryRational_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n) (τ : E →+* ℂ) (i j : Fin n), ‖τ (γ.1.val i j)‖ ≤ 1 := by
  first | exact @GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one | exact GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one | (intros; apply GlobalTheory.BCT.SuppFin.norm_emb_entry_le_one <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.norm_embedding_entry_definiteUnitaryRationalPoint_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n) (τ : E →+* ℂ) (i j : Fin n), ‖τ ((γ : GL (Fin n) E).val i j)‖ ≤ 1 := by
  first | exact @GlobalTheory.BCT.FinPart.norm_emb_entry_le_one | exact GlobalTheory.BCT.FinPart.norm_emb_entry_le_one | (intros; apply GlobalTheory.BCT.FinPart.norm_emb_entry_le_one <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtReg

theorem exists_ne_of_avg_ne {H : Type} [Group H] {u : H → ℂ} (h : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [avg, finsum_eq_zero_of_forall_eq_zero (fun q => hc _), mul_zero]

theorem exists_ne_of_hint_ne {H : Type} [Group H] {K : Subgroup H} {u : H → ℂ} (h : hint K u ≠ 0) :
    ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [hint, finsum_eq_zero_of_forall_eq_zero (fun q => hc _), mul_zero]

theorem charpoly_conj_GL {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (k g : GL ι R) :
    ((k⁻¹ * g * k : GL ι R) : Matrix ι ι R).charpoly = (g : Matrix ι ι R).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]

theorem ctMu_regAt2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w →
    (∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a b w (ctMu h w μ f) := by
  intro E _ _ _ a b n h w μ f hw hf m hm
  have hct : ct h w (fun y => f (toSub _ y)) m ≠ 0 := by
    intro h0; apply hm; rw [ctMu, h0, mul_zero]
  rw [ct] at hct
  obtain ⟨X, hX⟩ := exists_ne_of_hint_ne (right_ne_zero_of_mul hct)
  obtain ⟨k, hk⟩ := exists_ne_of_avg_ne hX
  have hsep := hf _ hk
  have hmem : ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k) ∈ UL n w := by
    rw [UL, if_pos hw]; exact Subgroup.mem_top _
  have e0 : (toSub (UL n w) ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)).1 =
      (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k := by
    rw [toSub, dite_eq_left hmem]
  rw [e0, charpoly_conj_GL, blk_val, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁] at hsep
  have e1 : nrmL a w m.1 = m.1 := by rw [nrmL, if_pos hw]
  have e2 : nrmL b w m.2 = m.2 := by rw [nrmL, if_pos hw]
  rw [e1, e2]
  exact hsep

end GlobalTheory.BCT.CtReg
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryHeckeCharCM_locK_nonsplit_eq_neg_one_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w : Pl E, ¬ IsSplitAt w → ∀ k : Eˣ, ((μ.locK w k : ℂˣ) : ℂ) = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (k : E)) := by
  first | exact @GlobalTheory.BCT.inertChar_muLocK | exact GlobalTheory.BCT.inertChar_muLocK | (intros; apply GlobalTheory.BCT.inertChar_muLocK <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitChar

theorem locK_mul_locK_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w u : Pl E, u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ k : Eˣ, μ.locK u k * μ.locK w (Units.map (MonoidHomClass.toMonoidHom (IsCMField.complexConj E)) k) = 1 := by
  intro E _ _ _ μ e h w u hne hunder k
  have hc : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv u w := by
    have hw : w ∈ aboveF (L := E) (maximalRealSubfield E) (u.under (𝓞 (maximalRealSubfield E))) := by
      simp [aboveF, hunder]
    exact ((GlobalTheory.CuspRep.NormTriv.mem_aboveF_iff u w).1 hw).resolve_left (Ne.symm hne)
  have h1 := GlobalTheory.CuspRep.NormTriv.normFin_loc _ μ hc k
  refine (Eq.trans ?_ h1.symm).trans ?_
  · rfl
  · rw [GlobalTheory.CuspRep.NormTriv.normFin, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MonoidHom.mul_apply, MonoidHom.id_apply, map_mul, GlobalTheory.BCT.MuProps.finId_conjFin, ← GlobalTheory.PolChar.ideleConj_eq]
    rw [map_mul]
    exact GlobalTheory.BCT.MuProps.mu_mul_conj h _

end GlobalTheory.BCT.SplitChar
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.VanishNumberField

open GlobalTheory.AbLaw

theorem subsingleton_of_tensor {k E V : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]
    (h : Subsingleton (TensorProduct k E V)) : Subsingleton V := by
  by_contra hV
  rw [not_subsingleton_iff_nontrivial] at hV
  exact not_nontrivial_iff_subsingleton.2 h (Module.FaithfullyFlat.lTensor_nontrivial k E V)

theorem subsingleton_coh_of_pull {k E : Type} [Field k] [Field E] [Algebra k E] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of k)} {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X} [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ)
    (h : Subsingleton (coh (twist (structureModule X') (M.pull π)) n)) :
    Subsingleton (coh (twist (structureModule X) M) n) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have cechIso {R : Type} [CommRing R] {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of R))
      (N : LB Z) {κ : Type} [LinearOrder κ] (U : κ → Z.Opens) :
      letI := algebraΓOfHom g
      cechLB g N U ≅ cech R (LB.toMod N) ⊤ U := by
    letI := algebraΓOfHom g
    exact (cechFunctor κ R).mapIso (Cube.isoMk (fun s => LinearEquiv.ofBijective
      (M := SecOnR g N (⨅ i ∈ s, U i)) (M₂ := sectionsOn (LB.toMod N) (⊤ ⊓ ⨅ i ∈ s, U i))
      (SecOnR.restrict g N (inf_le_right : ⊤ ⊓ (⨅ i ∈ s, U i) ≤ ⨅ i ∈ s, U i))
      (SecOnR.restrict_bijective g _ (le_inf le_top le_rfl)))
      fun {s t} ht x => (SecOnR.restrict_restrict g _ inf_le_right x).trans
        (SecOnR.restrict_restrict g inf_le_right (cechOpen_anti ⊤ U ht) x).symm)
  have cohEquiv {R : Type} [CommRing R] {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of R))
      {N : LB Z} (hN : N.IsLB) {κ : Type} [LinearOrder κ] [Finite κ] {U : κ → Z.Opens}
      (hu : ⨆ i, U i = ⊤) (hU : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (i : ℕ) :
      letI := algebraΓOfHom g
      Nonempty ((cechLB g N U).homology i ≃ₗ[R] coh (twist (structureModule Z) N) i) := by
    letI := algebraΓOfHom g
    haveI := LB.isQuasicoherent_toMod hN
    exact ⟨((HomologicalComplex.homologyFunctor _ _ i).mapIso (cechIso g N U)).toLinearEquiv ≪≫ₗ
      cechHEquivCoh R hu hU (LB.toMod N) i ≪≫ₗ (cohOn.mapIso R ⊤ i (Twist.unitTwistIso N)).symm⟩
  have homologyEquiv {R : Type} (O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O]
      (C : CochainComplex (ModuleCat.{0} R) ℕ) (i : ℕ) :
      Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
        C).homology i ≃ₗ[O] TensorProduct R O (C.homology i)) := by
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
    have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
    obtain ⟨e⟩ := Semicont.nonempty_extendScalars_obj_equiv O (C.homology i)
    exact ⟨((C.sc i).mapHomologyIso
      (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩
  obtain ⟨e₁⟩ := cohEquiv f hM hc hD' n
  obtain ⟨e₂⟩ := cohEquiv f' (LB.isLB_pull hM π) (U := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := homologyEquiv E (cechLB f M D) n
  have bcIso (g : k →+* E)
      (H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
      ((ModuleCat.extendScalars g).mapHomologicalComplex _).obj (cechLB f M D) ≅
        cechLB f' (M.pull π) (fun i => π ⁻¹ᵁ D i) := by
    letI := g.toAlgebra
    let φ : (secCube f M D ⋙ ModuleCat.extendScalars g) ⟶
        secCube f' (M.pull π) (fun i => π ⁻¹ᵁ D i) :=
      Cube.homMk (Fin m) E (fun s => SecOnR.baseChangeHom M H'.w _ _ (preimage_biInf D π s).ge)
        fun {s t} ht x => SecOnR.baseChangeHom_restrict H'.w (iInf_le_iInf_of_subset D ht)
          (iInf_le_iInf_of_subset (fun i => π ⁻¹ᵁ D i) ht) (preimage_biInf D π s).ge
          (preimage_biInf D π t).ge x
    exact @asIso _ _ _ _ (cechComparison (ModuleCat.extendScalars g) (secCube f M D))
      (isIso_cechComparison _ _) ≪≫
      @asIso _ _ _ _ (cechComplexMap φ)
        (isIso_cechComplexMap _ fun s hs => SecOnR.baseChangeHom_bijective hM H' (hD' s hs) (preimage_biInf D π s).symm)
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (bcIso (algebraMap k E) H)).toLinearEquiv
  have h₁ : Subsingleton (TensorProduct k E ((cechLB f M D).homology n)) :=
    (e₃.symm.toEquiv.trans (e₄.toEquiv.trans e₂.toEquiv)).subsingleton_congr.2 h
  exact e₁.symm.toEquiv.subsingleton_congr.2 (subsingleton_of_tensor h₁)

theorem topologicalKrullDim_eq_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} [Nonempty Y] (p : Y ⟶ Sp k) (D : ℕ)
    (h : SmoothOfRelativeDimension D p) : topologicalKrullDim Y = D := by
  have key : topologicalKrullDim (Set.univ : Set Y) = D := by
    refine topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun x _ => ?_
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    replace hU : IsAffineOpen (X := Y) U := hU
    refine ⟨U, U.isOpen, hx, ?_⟩
    rw [Set.inter_univ, topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ p _ h U hU ⟨x, hx⟩)
  rw [← key]
  exact (topologicalKrullDim_eq_of_isEmbedding (e := (id : Y → Y)) Topology.IsEmbedding.id Set.range_id).symm

theorem vanishFrom_adj : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle G.LA)) 0 := by
  intro Q K _ _ G hnef hbig j hj q hq
  lift j to ℕ using hj
  let Ω := AlgebraicClosure K
  let S := G.toLinSys
  have hV : S.IsVariety := G.geom.alg.variety
  have hV' := hV.baseChange Ω
  have hH := S.isPullback_baseChange Ω
  haveI : IsIntegral (S.baseChange Ω).Y := hV'.isIntegral
  haveI : SmoothOfRelativeDimension G.D (S.baseChange Ω).str := hV'.smooth
  obtain ⟨hprop, A₀, hA₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hV.proj
  haveI := hprop
  have hstr : strHom K G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom K (X := G.Y)) := hstr ▸ hV.proj
  haveI : IsProper (strHom K (X := G.Y)) := hstr ▸ hprop

  have hLnef : IsNef K G.L := IsGenerated.isNef_of_isProjOver (L := G.L) ⟨G.N, G.b, G.geom.alg.bpf⟩ hV.proj
  have hLj : IsNef K (lbPow G.L j) := hLnef.pow hA₀ j
  have hNnef : IsNef K (tens G.LA (lbPow G.L j)) := hnef.tens_of_isProjOver hLj hV.proj
  have hNbig : IsBig K (tens G.LA (lbPow G.L j)) := hbig.tens_nef Q.nef hproj hnef hLj

  haveI : IsIntegralHom (spMap (algebraMap K Ω)) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  haveI : IsIntegralHom (S.bcFst Ω) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hH.flip ‹_›
  let π := S.bcFst Ω

  have hN'nef : IsNef Ω ((tens G.LA (lbPow G.L j)).pull π) :=
    PosBaseChange.isNef_pull hNnef hA₀ (hA₀.pull_of_isAffineHom π) π π.isClosedMap
  have hN'big : IsBig Ω ((tens G.LA (lbPow G.L j)).pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hNbig.3
    have hD : topologicalKrullDim G.Y = G.D := topologicalKrullDim_eq_of_smooth G.str G.D hV.smooth
    obtain rfl : D₀ = G.D := by exact_mod_cast hD₀.symm.trans hD
    have hL := LB.isLB_pull hNbig.1 π
    refine (isBig_iff (f := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj
      (topologicalKrullDim_eq_of_smooth _ G.D hV'.smooth)).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hNbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hNbig.1, cls_pull (isLB_lbPow hNbig.1 m), cls_lbPow hNbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull hH (isLB_lbPow hNbig.1 m) 0).symm

  have hM' := LB.isLB_pull (G.isLB_adj j) π
  have hKV : Subsingleton (coh (twist (structureModule (S.baseChange Ω).Y) ((G.adj j).pull π)) q) :=
    Q.kv.twist (k := Ω) (p := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj (G.K.baseChange hH) hN'nef hN'big hM'
      (by
        rw [cls_pull (G.isLB_adj j) π]
        erw [cls_pull G.K.isLB π, cls_pull hNnef.isLB π]
        rw [← map_add (f := _)]
        congr 1
        erw [cls_tens (isLB_tens G.K.isLB G.isLBA) (Twist.isLB_lbZPow G.isLB j), cls_tens G.K.isLB G.isLBA,
          cls_tens G.isLBA (isLB_lbPow G.isLB j)]
        exact add_assoc _ _ _) hq

  have hY : Subsingleton (coh (twist (structureModule G.Y) (G.adj j)) q) :=
    subsingleton_coh_of_pull (f := G.str) (f' := (S.baseChange Ω).str) hH (G.isLB_adj j) q hKV
  have hB : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule G.Y) hB (Twist.isLB_lbZPow G.isLB j)
    (G.isLB_adj j) rfl
  exact (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q
    ((twistFunctor (lbZPow G.L j)).mapIso (Twist.unitTwistIso (tens G.K.bundle G.LA)).symm ≪≫ i)).toEquiv.subsingleton_congr.2 hY

end GlobalTheory.HSCore.VanishNumberField
end
end
