module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle005
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle016
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle336
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbSumFibreEquiv
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle334
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryStabilizerSubspaceProd

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St.WittT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Witt

variable {D : D7}

abbrev Ix (D : D7) : Type := Fin D.R.rS ⊕ (Fin D.R.rS ⊕ Unit)

def mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) : Ix D → (VS D).V
  | Sum.inl a => e a
  | Sum.inr (Sum.inl a) => f a
  | Sum.inr (Sum.inr _) => z

def gstd (T : D.host.E) : Ix D → Ix D → D.host.E
  | Sum.inl a, Sum.inr (Sum.inl b) => if a = b then 1 else 0
  | Sum.inr (Sum.inl a), Sum.inl b => if a = b then 1 else 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => -T
  | _, _ => 0

def swp : Ix D → Ix D
  | Sum.inl a => Sum.inr (Sum.inl a)
  | Sum.inr (Sum.inl a) => Sum.inl a
  | Sum.inr (Sum.inr t) => Sum.inr (Sum.inr t)

def cstd (T : D.host.E) : Ix D → D.host.E
  | Sum.inr (Sum.inr _) => -T
  | _ => 1

theorem gram_mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) (T : D.host.E)
    (hee : ∀ a b, (VS D).hT (e a) (e b) = 0) (hff : ∀ a b, (VS D).hT (f a) (f b) = 0)
    (hef : ∀ a b, (VS D).hT (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, (VS D).hT (e a) z = 0) (hfz : ∀ a, (VS D).hT (f a) z = 0) (hzz : (VS D).hT z z = -T) :
    ∀ i j, (VS D).hT (mkFr e f z i) (mkFr e f z j) = gstd T i j := by
  rintro (a | a | ⟨⟩) (b | b | ⟨⟩)
  · exact hee a b
  · exact hef a b
  · exact hez a
  · show (VS D).hT (f a) (e b) = if a = b then 1 else 0
    rw [← (VS D).herm.eq (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · exact hff a b
  · exact hfz a
  · show (VS D).hT z (e b) = 0
    rw [← (VS D).herm.eq (e b) z, hez b, map_zero]
  · show (VS D).hT z (f b) = 0
    rw [← (VS D).herm.eq (f b) z, hfz b, map_zero]
  · exact hzz

theorem gstd_swp (T : D.host.E) (i j : Ix D) : gstd T (swp j) i = if i = j then cstd T j else 0 := by
  rcases i with a | a | ⟨⟩ <;> rcases j with b | b | ⟨⟩ <;>
    simp [gstd, swp, cstd, eq_comm]

theorem indep_of_dual {ι : Type} [Fintype ι] [DecidableEq ι] (v d : ι → (VS D).V) (c : ι → D.host.E)
    (hc : ∀ j, c j ≠ 0) (hd : ∀ i j, (VS D).hT (d j) (v i) = if i = j then c j else 0) :
    LinearIndependent D.host.E v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg ((VS D).hT (d j)) hg

  simp only [map_sum, map_smul, map_zero, hd, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
  Finset.mem_univ, if_true] at h
  exact (mul_eq_zero.1 h).resolve_right (hc j)

theorem indep_mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) (T : D.host.E) (hT : T ≠ 0)
    (hG : ∀ i j, (VS D).hT (mkFr e f z i) (mkFr e f z j) = gstd T i j) :
    LinearIndependent D.host.E (mkFr e f z) := by
  refine indep_of_dual (mkFr e f z) (fun j => mkFr e f z (swp j)) (cstd T) ?_ ?_
  · rintro (a | a | ⟨⟩) <;> simp [cstd, hT]
  · intro i j
    rw [hG, gstd_swp]

theorem witt_family {ι : Type} [Fintype ι] [DecidableEq ι] (v w : ι → (VS D).V)
    (hv : LinearIndependent D.host.E v) (hw : LinearIndependent D.host.E w)
    (hG : ∀ i j, (VS D).hT (v i) (v j) = (VS D).hT (w i) (w j)) :
    ∃ g : (VS D).V ≃ₗ[D.host.E] (VS D).V, (∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y) ∧ ∀ i, g (v i) = w i := by
  set U := Submodule.span D.host.E (Set.range v) with hU
  let b : Module.Basis ι D.host.E U := Module.Basis.span hv
  let f : U →ₗ[D.host.E] (VS D).V :=
    Finsupp.linearCombination D.host.E w ∘ₗ (b.repr : U →ₗ[D.host.E] (ι →₀ D.host.E))
  have hfb : ∀ i, f (b i) = w i := by
    intro i
    simp [f, Module.Basis.repr_self, Finsupp.linearCombination_single]
  have hbv : ∀ i, ((b i : U) : (VS D).V) = v i := by
    intro i
    exact congrArg Subtype.val (Module.Basis.span_apply hv i)
  have hinj : Function.Injective f := by
    have h2 : Function.Injective (Finsupp.linearCombination D.host.E w) := hw
    exact h2.comp b.repr.injective
  have hB : ((VS D).hT.comp f).compl₂ f = ((VS D).hT.comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hfb, Submodule.subtype_apply, hbv]
    exact (hG i j).symm
  have hiso : ∀ x y : U, (VS D).hT (f x) (f y) = (VS D).hT x y := by
    intro x y
    have h := congrArg (fun B => B x y) hB
    simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply] using h
  obtain ⟨g, hg, hgf⟩ := _root_.witt_extension_theorem D.host.E (VS D).V (VS D).hT
    (fun x y => (VS D).herm.eq x y) (fun x hx => (VS D).nondeg.1 x hx) U f hinj hiso
  refine ⟨g, hg, fun i => ?_⟩
  have h := hgf (b i)
  rw [hbv, hfb] at h
  exact h

theorem hypF_zmOf (u : D.what₂.Word) (a : Fin D.R.rS) : (VS D).hT (D.sp.hypF a) (D.zmOf u) = 0 := by
  unfold D7.zmOf
  rw [map_smul, ← (VS D).herm.eq D.sp.zm (D.sp.hypF a), (D.sp.hyp_orthz a).2, map_zero, smul_zero]

theorem wittExists_holds (D : D7) : WittExists D := by
  intro X u
  have hT : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hGX := gram_mkFr X.eX X.fY (X.zu u) (((D.mem u).A.T : ℕ) : D.host.E) X.ee X.ff X.ef
    (fun a => (X.zu_orth u a).1) (fun a => (X.zu_orth u a).2) (X.zu_norm u)
  have hGR := gram_mkFr D.sp.hypE D.sp.hypF (D.zmOf u) (((D.mem u).A.T : ℕ) : D.host.E) D.sp.hyp_ee D.sp.hyp_ff
    D.sp.hyp_ef (fun a => (Formalism.MainNotions.S.Inh.tie_flag0 D u).z_orth a) (hypF_zmOf u) (Formalism.MainNotions.S.Inh.tie_zmOf_norm D u)
  obtain ⟨g, hg, hgi⟩ := witt_family (mkFr X.eX X.fY (X.zu u)) (mkFr D.sp.hypE D.sp.hypF (D.zmOf u))
    (indep_mkFr _ _ _ _ hT hGX) (indep_mkFr _ _ _ _ hT hGR) (fun i j => by rw [hGX, hGR])
  exact ⟨g, hg, fun a => hgi (Sum.inl a), fun a => hgi (Sum.inr (Sum.inl a)), hgi (Sum.inr (Sum.inr ()))⟩

end Witt

theorem wittExists : ∀ D : D7, WittExists D := wittExists_holds

end GlobalTheory.St.WittT

end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

private theorem sum_castLE_lemma {M : Type} [AddCommMonoid M] {l N : ℕ} (h : l ≤ N) (g : Fin N → M)
    (hg : ∀ a : Fin N, l ≤ (a : ℕ) → g a = 0) :
    ∑ a, g a = ∑ a : Fin l, g (Fin.castLE h a) := by
  symm
  calc ∑ a : Fin l, g (Fin.castLE h a) = ∑ x ∈ Finset.univ.map (Fin.castLEEmb h), g x :=
        (Finset.sum_map Finset.univ (Fin.castLEEmb h) g).symm
    _ = ∑ a, g a := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro a _ ha
        apply hg
        by_contra hlt
        exact ha (Finset.mem_map.2 ⟨⟨(a : ℕ), Nat.lt_of_not_le hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem leadMinorE_unitri_both {E : Type} [Field E] {N : ℕ} (Z U U' : Matrix (Fin N) (Fin N) E)
    (hU : IsUpUni U) (hU' : IsUpUni U') (l : ℕ) :
    leadMinorE (U.transpose * Z * U') l = leadMinorE Z l := by
  have hz : ∀ i j : Fin N, j < i → U i j = 0 := fun i j hij => (hU i j).1 hij
  have hz' : ∀ i j : Fin N, j < i → U' i j = 0 := fun i j hij => (hU' i j).1 hij
  unfold leadMinorE
  by_cases h : l ≤ N
  · rw [dite_eq_left h, dite_eq_left h]
    have key : (U.transpose * Z * U').submatrix (Fin.castLE h) (Fin.castLE h) =
        (U.submatrix (Fin.castLE h) (Fin.castLE h)).transpose * Z.submatrix (Fin.castLE h) (Fin.castLE h) *
          U'.submatrix (Fin.castLE h) (Fin.castLE h) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
      rw [sum_castLE_lemma h]
      · refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [sum_castLE_lemma h]
        intro a ha
        have hi := i.isLt
        rw [hz a (Fin.castLE h i) (by rw [Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
      · intro b hb
        have hj := j.isLt
        rw [hz' b (Fin.castLE h j) (by rw [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]
    have t1 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro a b hab
      exact (hU (Fin.castLE h a) (Fin.castLE h b)).1 hab
    have t2 : (U'.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro a b hab
      exact (hU' (Fin.castLE h a) (Fin.castLE h b)).1 hab
    have d1 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_upperTriangular t1]
      exact Finset.prod_eq_one (fun a _ => (hU (Fin.castLE h a) (Fin.castLE h a)).2 rfl)
    have d2 : (U'.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_upperTriangular t2]
      exact Finset.prod_eq_one (fun a _ => (hU' (Fin.castLE h a) (Fin.castLE h a)).2 rfl)
    rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, d1, d2, one_mul, mul_one]
  · rw [dite_eq_right h, dite_eq_right h]

theorem gval_eq_of_movesTo : ∀ (D : D7) {T T' : D.host.E} (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), MovesTo F0 F0' F F' ρ U U' → Gval F F' = Gval F0 F0' := by
  intro D T T' F0 F F0' F' ρ U U' h
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := h
  have hiso : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ
  have hstar : IsUpUni (U.map star) := by
    refine fun i j => ⟨fun hij => ?_, fun hij => ?_⟩
    · rw [Matrix.map_apply, (hU i j).1 hij, star_zero]
    · rw [Matrix.map_apply, (hU i j).2 hij, star_one]
  have hZ : Formalism.MainNotions.S.Zhat F.fl F'.fl = (U.map star).transpose * Formalism.MainNotions.S.Zhat F0.fl F0'.fl * U' := by
    ext a b
    simp only [Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]
    rw [← hiso (F.fl.fvec a) (F'.fl.fvec b), hF a, hF' b]

    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, frame, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    ring
  show Formalism.MainNotions.S.Gflag F.fl F'.fl = Formalism.MainNotions.S.Gflag F0.fl F0'.fl
  unfold Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
  rw [hZ, leadMinorE_unitri_both _ _ _ hstar hU', leadMinorE_unitri_both _ _ _ hstar hU']

end GlobalTheory.HL
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL

theorem leadMinor_triMul {E : Type} [Field E] {m : ℕ} (A B Z : Matrix (Fin m) (Fin m) E)
    (hA : ∀ i j, i < j → A i j = 0) (hA1 : ∀ i, A i i = 1)
    (hB : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) (l : ℕ) :
    leadMinorE (A * Z * B) l = leadMinorE Z l := by
  unfold leadMinorE
  by_cases hl : l ≤ m
  · rw [dite_eq_left hl, dite_eq_left hl]
    have red : ∀ g : Fin m → E, (∀ i : Fin m, l ≤ (i : ℕ) → g i = 0) →
        ∑ i, g i = ∑ i : Fin l, g (Fin.castLE hl i) := by
      intro g hg
      refine (Finset.sum_of_injOn (Fin.castLE hl) (Fin.castLE_injective hl).injOn
        (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun i _ hi => hg i ?_) (fun _ _ => rfl)).symm
      by_contra h
      exact hi ⟨⟨i, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
    have key : (A * Z * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        A.submatrix (Fin.castLE hl) (Fin.castLE hl) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
          B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [red]
      · refine Finset.sum_congr rfl fun d _ => ?_
        rw [red]
        intro i hi
        rw [hA _ _ (by simp [Fin.lt_def]; omega), zero_mul]
      · intro i hi
        rw [hB _ _ (by simp [Fin.lt_def]; omega), mul_zero]
    have hdA : (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
      rw [Matrix.det_of_lowerTriangular]
      · simp [hA1]
      · intro i j hij
        have h2 : i < j := OrderDual.toDual_lt_toDual.1 hij
        exact hA _ _ (Fin.lt_def.2 (Fin.lt_def.1 h2))
    have hdB : (B.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · simp [hB1]
      · intro i j hij
        have h2 : j < i := hij
        exact hB _ _ (Fin.lt_def.2 (Fin.lt_def.1 h2))
    rw [key, Matrix.det_mul, Matrix.det_mul, hdA, hdB, one_mul, mul_one]
  · rw [dite_eq_right hl, dite_eq_right hl]

variable {D : D7}

theorem zhat_movesTo {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T')
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (h : MovesTo F0 F0' F F' ρ U U') :
    Zhat F.fl F'.fl = U.conjTranspose * Zhat F0.fl F0'.fl * U' := by
  obtain ⟨hρ, -, -, hU, hU'⟩ := h
  have hρ' : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ
  refine Matrix.ext fun a b => ?_
  have e1 : Zhat F.fl F'.fl a b = (VS D).hT (ρ (frame F a)) (ρ (frame F' b)) := by
    rw [hρ']; rfl
  rw [e1, hU a, hU' b]

  simp only [Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, LinearMap.sum_apply,
  map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  simp only [RingHom.id_apply, frame, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem gval_movesTo : ∀ {D : D7} {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), MovesTo F0 F0' F F' ρ U U' → Gval F F' = Gval F0 F0' := by
  intro D T T' F0 F0' F F' ρ U U' h
  have hZ := zhat_movesTo F0 F0' F F' ρ U U' h
  obtain ⟨-, hu, hu', -, -⟩ := h
  have hl : ∀ l, Dl F.fl F'.fl l = Dl F0.fl F0'.fl l := by
    intro l
    show leadMinorE (Zhat F.fl F'.fl) l = leadMinorE (Zhat F0.fl F0'.fl) l
    rw [hZ]
    refine leadMinor_triMul _ _ _ (fun i j hij => ?_) (fun i => ?_) (fun i j hij => (hu' i j).1 hij)
      (fun i => (hu' i i).2 rfl) l
    · simp [Matrix.conjTranspose_apply, (hu j i).1 hij]
    · simp [Matrix.conjTranspose_apply, (hu i i).2 rfl]
  show Gflag F.fl F'.fl = Gflag F0.fl F0'.fl
  unfold Gflag
  rw [hl, hl]

end GlobalTheory.HL
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.CritLevelGap

private theorem VV_eq_vand_lamSH_of_standingHypotheses (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT : ℝ) (hT : Ties D) (hS : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hL : 1 ≤ Cl * large₂.sc.L)
    (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by

  have hanti : StrictAnti (lamSH D.R (D.hc τ)) := (GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1
  have hd : D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hDs D large₂ C' Cl Cg cb Cu cT CT hT hS hL τ
  have hN : 2 * D.R.rS + D.R.k + 1 = D.R.r := dimS_eq D.R
  have hpos : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [hd, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← hN]
  field_simp

theorem tcritLow_along_family_gap :
    Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusBranching.admF5 Fm Cg cb Cu cT CT C0 := by
  intro _ hH _ Cg cb Cu cT CT C0
  refine ⟨40, fun eps Fm _ hCl _ => ?_⟩
  unfold VanishingOnXAndXPlusBranching.admF5 OwnEv
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨hxk, hb⟩ := GlobalTheory.CritLevel.sizes_low _ (Fm.sizes x hx1 i)
  have hL1 : 1 ≤ (Fm.L x i).sc.L := by
    show 1 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps
    exact Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hL : 1 ≤ sCl Fm * (Fm.L x i).sc.L := by nlinarith
  intro h0
  exact GlobalTheory.CritLevel.tcrit_low _ _ _ _ _ _ _ _ _ _ hCl
    (fun τ => VV_eq_vand_lamSH_of_standingHypotheses hH.2.2.2 _ _ _ _ _ _ _ _ _ (Fm.ties x i) h0.1 hL τ) hb hxk h0

end GlobalTheory.CritLevelGap
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb

theorem lat0_eq_img_latIn_Ub (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V)
    (e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W)
    (he : ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ
      = GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  ext w
  rw [GlobalTheory.Mass.Transp.mem_img]
  have hd : ((e (e.symm w) : W) : (VS D).V) - (((e.symm w : GlobalTheory.RowsOrb.Ub X u) : GlobalTheory.RowsOrb.Wb X) : (VS D).V)
      ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X :=
    (le_sup_right : GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X ≤ _) (he (e.symm w))
  rw [LinearEquiv.apply_symm_apply] at hd
  have h1 : w ∈ GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ ↔
      (w : (VS D).V) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl
  have h2 : e.symm w ∈ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ↔
      (((e.symm w : GlobalTheory.RowsOrb.Ub X u) : GlobalTheory.RowsOrb.Wb X) : (VS D).V)
        ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl
  rw [h1, h2]
  constructor
  · intro h
    simpa using Submodule.sub_mem _ h hd
  · intro h
    simpa using Submodule.add_mem _ hd h

end GlobalTheory.RowsOrb
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.StabSet

open GlobalTheory.Mass Formalism.HermitianLatticesTheory GlobalTheory.Mass.RowMean

theorem main : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (M₀ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)) (ψ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u) → ℝ≥0∞), (∀ (s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u)) (M : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)), ψ (s • M) = ψ M) → GlobalTheory.Mass.Stable (GlobalTheory.RowsOrb.Gz X u) {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} ∧ ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L)) = ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L) := by
  intro D X u M₀ ψ hψ
  have hU : ∀ v, v ∈ GlobalTheory.RowsOrb.Ub X u ↔ GlobalTheory.RowsOrb.hb X (GlobalTheory.RowsOrb.zb X u) v = 0 :=
    fun v => GlobalTheory.RowsOrb.mem_Ub X u v
  have hπ : ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)),
      GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L) =
        resZ (GlobalTheory.RowsOrb.hb X) hU g • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L :=
    fun g L => StabSplit.latIn_smul (GlobalTheory.RowsOrb.hb X) (GlobalTheory.RowsOrb.Ub X u) g.1 (smul_compl _ hU g) L
  have hY : Stable (isom (GlobalTheory.RowsOrb.hU X u)) (genus (GlobalTheory.RowsOrb.hU X u) M₀) :=
    Transp.genus_stable (R := 𝓞 D.host.E) (K := D.host.E) (V := GlobalTheory.RowsOrb.Ub X u) (h := GlobalTheory.RowsOrb.hU X u) M₀
  refine ⟨?_, fun g L => by rw [hπ]; exact hψ _ _⟩
  rintro g L ⟨h1, h2, h3, h4⟩
  have H := Formalism.HermitianLatticesTheory.isomAct (𝓞 D.host.E) D.host.E (GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.hb X) g.1.1 g.1.2 L
  refine ⟨H.2.2.2.2.2 h1, H.2.2.2.1.2 h2, fun t => ?_, ?_⟩
  · have hg : g.1.1 (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u := g.2
    have hs : g.1.1.symm (t • GlobalTheory.RowsOrb.zb X u) = t • GlobalTheory.RowsOrb.zb X u :=
      g.1.1.symm_apply_eq.2 (by rw [map_smul, hg])
    change t • GlobalTheory.RowsOrb.zb X u ∈ Formalism.HermitianLatticesTheory.gmap (g.1.1 : GlobalTheory.RowsOrb.Wb X ≃ₗ[D.host.E] GlobalTheory.RowsOrb.Wb X) L ↔ _
    rw [isomAct_mem_gmap, hs, h3]
  · let s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u) := resZ (GlobalTheory.RowsOrb.hb X) hU g
    have k : s • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ genus (GlobalTheory.RowsOrb.hU X u) M₀ := hY s _ h4
    have e : GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L) = s • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L := hπ g L
    exact Eq.mpr (congrArg (fun N => N ∈ genus (GlobalTheory.RowsOrb.hU X u) M₀) e) k

end GlobalTheory.RowsOrb.StabSet
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction : VolumeStep → VolumeRatio := by
  first | exact @GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep | exact GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep | (intros; apply GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep <;> assumption)
end
