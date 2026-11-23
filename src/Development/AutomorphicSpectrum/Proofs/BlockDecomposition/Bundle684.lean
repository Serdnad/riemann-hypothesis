module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups
public import GroundTheory.AutomorphicForms.AnisotropicUnitaryRes
public import GroundTheory.AutomorphicForms.ReductionHeight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundCompact
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
import Development.WeilBound.ThetaLifts.Reductions.SiegelHaar
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical Kronecker
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtAdj

section Generic

variable {H : Type} [Group H]

theorem rStab_conj (u : H → ℂ) : rStab (fun x => starRingEnd ℂ (u x)) = rStab u := by
  ext k
  constructor
  · intro hk x
    exact (starRingEnd ℂ).injective (hk x)
  · intro hk x
    show starRingEnd ℂ (u (x * k)) = starRingEnd ℂ (u x)
    rw [hk x]

theorem finsum_conj {α : Type} (g : α → ℂ) : ∑ᶠ q, starRingEnd ℂ (g q) = starRingEnd ℂ (∑ᶠ q, g q) :=
  (AddMonoidHom.map_finsum_of_injective (starRingEnd ℂ).toAddMonoidHom (starRingEnd ℂ).injective g).symm

theorem hint_conj (K : Subgroup H) (u : H → ℂ) :
    hint K (fun x => starRingEnd ℂ (u x)) = starRingEnd ℂ (hint K u) := by
  unfold hint
  rw [rStab_conj, map_mul, map_inv₀, map_natCast, finsum_conj]

theorem avg_conj (u : H → ℂ) : avg (fun x => starRingEnd ℂ (u x)) = starRingEnd ℂ (avg u) := by
  unfold avg
  rw [rStab_conj, map_mul, map_inv₀, map_natCast, finsum_conj]

end Generic

theorem det_lr {k : Type} [Field k] {a b : ℕ} (A : Matrix (Fin a) (Fin a) k) (B : Matrix (Fin b) (Fin b) k)
    (L : Matrix (Fin a) (Fin b) k →ₗ[k] Matrix (Fin a) (Fin b) k) (hL : ∀ X, L X = A * X * B) :
    LinearMap.det L = A.det ^ b * B.det ^ a := by
  let e : Matrix (Fin a) (Fin b) k ≃ₗ[k] (Fin a × Fin b → k) := (LinearEquiv.curry k k (Fin a) (Fin b)).symm
  have h : (e.toLinearMap ∘ₗ L ∘ₗ e.symm.toLinearMap) = Matrix.toLin' (A ⊗ₖ Bᵀ) := by
    apply LinearMap.ext
    intro v
    funext ⟨i, j⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hL, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    show (A * (Matrix.of fun l c => v (l, c)) * B) i j = _
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [← LinearMap.det_conj L e, h, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose,
    Fintype.card_fin, Fintype.card_fin]

variable {E : Type} [Field E] [NumberField E]

theorem absHalf_one (w : Pl E) : absHalf w (1 : w.adicCompletion E) = 1 := by
  have h := GlobalTheory.LeviDesc.absHalf_mul E w 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  have h0 := GlobalTheory.LeviDesc.absHalf_ne_zero' w (1 : w.adicCompletion E)
  exact (mul_right_cancel₀ h0 (by rw [one_mul]; exact h)).symm

theorem absHalf_inv_mul (w : Pl E) {x : w.adicCompletion E} (hx : x ≠ 0) :
    absHalf w x⁻¹ * absHalf w x = 1 := by
  rw [← GlobalTheory.LeviDesc.absHalf_mul E w _ _ (inv_ne_zero hx) hx, inv_mul_cancel₀ hx, absHalf_one]

theorem conj_absHalf (w : Pl E) (x : w.adicCompletion E) : starRingEnd ℂ (absHalf w x) = absHalf w x := by
  unfold absHalf
  exact Complex.conj_ofReal _

variable [IsCMField E]

def negL {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) :
    Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E) where
  toFun X := -(m.1.val * X * (m.2⁻¹).val)
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem det_inv_val {k : ℕ} {w : Pl E} (g : GLw k w) : (g⁻¹).val.det = (g.val.det)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

theorem det_ne_zero {k : ℕ} {w : Pl E} (g : GLw k w) : g.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

theorem v_det_negL {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) :
    Valued.v (LinearMap.det (negL m)) = Valued.v (m.1.val.det ^ b / m.2.val.det ^ a) := by
  have h : LinearMap.det (negL m) = (-m.1.val).det ^ b * (m.2⁻¹).val.det ^ a :=
    det_lr _ _ _ fun X => by simp [negL, Matrix.neg_mul]
  rw [h, det_inv_val, Matrix.det_neg, Fintype.card_fin, div_eq_mul_inv, map_mul, map_mul, map_pow, map_mul, map_pow,
    map_pow, map_pow, map_inv₀, map_inv₀, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, inv_pow]

theorem det_negL_ne_zero {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) : LinearMap.det (negL m) ≠ 0 := by
  intro h0
  have h := v_det_negL m
  rw [h0, map_zero] at h
  exact div_ne_zero (pow_ne_zero _ (det_ne_zero m.1)) (pow_ne_zero _ (det_ne_zero m.2))
    ((Valuation.zero_iff _).1 h.symm)

theorem ct_adj {n a b : ℕ} (h : a + b = n) (w : Pl E) (F : GLw n w → ℂ)
    (hF : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' F) (m : GLw a w × GLw b w) :
    ct h w (fun y => starRingEnd ℂ (F y⁻¹)) m = starRingEnd ℂ (ct h w F m⁻¹) := by
  obtain ⟨hU, hcs⟩ := GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport E n a b h w F hF m⁻¹
  have hJ := GlobalTheory.T.normalisedMatrixIntegral_comp_linearEquiv_det E w a b (negL m)
    (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ X)) (det_negL_ne_zero m) hU hcs
  have hpt : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      avg (fun k : GlobalTheory.LFun.KGL w (n := n) => starRingEnd ℂ (F ((((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k))⁻¹))) =
      starRingEnd ℂ (GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) := by
    intro X
    unfold GlobalTheory.LeviDesc.cavg
    rw [← avg_conj]
    congr 1
    funext k
    have e : ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹ =
        (k : GLw n w)⁻¹ * blk h w m⁻¹ (negL m (Multiplicative.toAdd X)) * k := by
      have e2 : blk h w m⁻¹ (negL m (Multiplicative.toAdd X)) = (blk h w m (Multiplicative.toAdd X))⁻¹ :=
        (CtLevel.blk_inv h w m _).symm
      rw [e2]
      group
    rw [e]
  have hD0 : m.1.val.det ^ b / m.2.val.det ^ a ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (det_ne_zero m.1)) (pow_ne_zero _ (det_ne_zero m.2))
  have hinv : (m⁻¹).1.val.det ^ b / (m⁻¹).2.val.det ^ a = (m.1.val.det ^ b / m.2.val.det ^ a)⁻¹ := by
    rw [Prod.fst_inv, Prod.snd_inv, det_inv_val, det_inv_val, inv_pow, inv_pow, inv_div, div_eq_mul_inv, inv_inv, mul_comm,
      div_eq_mul_inv]
  have hc : absHalf w (LinearMap.det (negL m)) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) :=
    GlobalTheory.BCT.AbsHalfInv.absHalf_congr (v_det_negL m)
  have h1 : hint (intMat a b w) (fun X => avg fun k : GlobalTheory.LFun.KGL w (n := n) =>
        starRingEnd ℂ (F (((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹))) =
      starRingEnd ℂ (hint (intMat a b w) fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) := by
    rw [← hint_conj]
    congr 1
    funext X
    exact hpt X
  have hJ' : (hint (intMat a b w) fun X =>
      GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) =
      (absHalf w (LinearMap.det (negL m)) ^ 2)⁻¹ * hint (intMat a b w) (fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (Multiplicative.toAdd X))) := hJ
  show absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) (fun X => avg fun k : GlobalTheory.LFun.KGL w (n := n) =>
        starRingEnd ℂ (F (((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹))) =
      starRingEnd ℂ (absHalf w ((m⁻¹).1.val.det ^ b / (m⁻¹).2.val.det ^ a) * hint (intMat a b w) (fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (Multiplicative.toAdd X))))
  rw [h1, hJ', hc, hinv, map_mul, map_mul, map_inv₀, map_pow, conj_absHalf, conj_absHalf]
  have hA := GlobalTheory.LeviDesc.absHalf_ne_zero' w (m.1.val.det ^ b / m.2.val.det ^ a)
  rw [eq_inv_of_mul_eq_one_left (absHalf_inv_mul w hD0)]
  field_simp

theorem mu_conj {K : Type} [Group K] (μ : K →* ℂˣ) (hμ : ∀ u, ‖((μ u : ℂˣ) : ℂ)‖ = 1) (x : K) :
    ((μ x⁻¹ : ℂˣ) : ℂ) = starRingEnd ℂ ((μ x : ℂˣ) : ℂ) := by
  rw [map_inv, Units.val_inv_eq_inv_val]
  exact Complex.inv_eq_conj (hμ x)

theorem ctStar : PositivityTheory.Rg.BcB.F.MLM.CtStar := by
  intro E _ _ _ n a ha w hw μ hμ f hf
  have hU : UL n w = ⊤ := if_pos hw
  funext m
  have hH := GlobalTheory.CompanionTheory.CtMulSplit.isHk_of_isHecke hU hf
  have hF : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' (fun y => f (toSub (UL n w) y)) :=
    ⟨GlobalTheory.LFun.KGL w (n := n), (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, hH.2.2.1, fun k hk x =>
      ⟨by simpa using hH.2.2.2 k hk 1 (Subgroup.one_mem _) x, by simpa using hH.2.2.2 1 (Subgroup.one_mem _) k hk x⟩⟩
  have hstar : (fun y => PositivityTheory.Rg.BcB.F.Eig.lstar f (toSub (UL n w) y)) =
      fun y => starRingEnd ℂ (f (toSub (UL n w) y⁻¹)) := by
    funext y
    show starRingEnd ℂ (f (toSub (UL n w) y)⁻¹) = _
    have e : (toSub (UL n w) y)⁻¹ = toSub (UL n w) y⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_inv, GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hU, GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hU])
    rw [e]
  show ((μ _ : ℂˣ) : ℂ) * ct _ w (fun y => PositivityTheory.Rg.BcB.F.Eig.lstar f (toSub (UL n w) y)) m =
    starRingEnd ℂ (((μ _ : ℂˣ) : ℂ) * ct _ w (fun y => f (toSub (UL n w) y)) m⁻¹)
  rw [hstar, ct_adj _ w (fun y => f (toSub (UL n w) y)) hF m, map_mul (starRingEnd ℂ)]
  congr 1
  rw [← mu_conj μ hμ]
  congr 2
  have hs : (((-1 : (w.adicCompletion E)ˣ) ^ (a * (n - a)))⁻¹) = (-1) ^ (a * (n - a)) := by
    rw [← inv_pow]
    simp
  simp only [Prod.fst_inv, Prod.snd_inv, map_inv, inv_pow, mul_inv, inv_inv, hs]

end GlobalTheory.CompanionTheory.CtAdj
end
end

section

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
  GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.LeviOne

section Frame

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem pfr_swap (hF : PFr s Jm Xm Ym) : PFr s Jm Ym Xm :=
  ⟨hF.ss, hF.herm, hF.yy, hF.xx, hF.yx⟩

theorem coef_mul_eq_one (hF : PFr s Jm Xm Ym) {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * Jm * g = Jm)
    {d d' : Fin r → R} (e : g * Xm = Xm * diagonal d) (e' : g * Ym = Ym * diagonal d') (i : Fin r) :
    s (d' i) * d i = 1 := by
  have h := hF.inv_coef hg e
  rw [e', ← Matrix.mul_assoc, hF.xy, Matrix.one_mul] at h
  have h2 : cT s (diagonal d') = diagonal (fun i => s (d' i)) := Matrix.ext fun a b => by
    by_cases hab : a = b
    · subst hab
      simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
  rw [h2, diagonal_mul_diagonal] at h
  simpa using congrFun (congrFun h i) i

theorem inv_act {g g' : Matrix (Fin n) (Fin n) R} (hg : g' * g = 1) {d e : Fin r → R}
    (he : ∀ i, e i * d i = 1) (h : g * Xm = Xm * diagonal d) : g' * Xm = Xm * diagonal e := by
  have h1 : diagonal d * diagonal e = (1 : Matrix (Fin r) (Fin r) R) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [mul_comm, he i]
  calc g' * Xm = g' * (Xm * (diagonal d * diagonal e)) := by rw [h1, Matrix.mul_one]
    _ = g' * g * Xm * diagonal e := by
        rw [← Matrix.mul_assoc Xm, ← h]
        simp only [Matrix.mul_assoc]
    _ = Xm * diagonal e := by rw [hg, Matrix.one_mul]

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem one_mem_minParOne : (1 : GAd σ J) ∈ minParOne σ J X :=
  ⟨1, Matrix.blockTriangular_one, by simp, fun i => ⟨1, by simp, map_one _⟩⟩

theorem mul_mem_levi {a b : GAd σ J} (ha : a ∈ leviMin σ J X Y) (hb : b ∈ leviMin σ J X Y) :
    a * b ∈ leviMin σ J X Y := by
  obtain ⟨d₁, d₁', e₁, e₁'⟩ := ha
  obtain ⟨d₂, d₂', e₂, e₂'⟩ := hb
  refine ⟨d₁ * d₂, d₁' * d₂', ?_, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, e₁, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂', ← Matrix.mul_assoc, e₁', Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl

theorem inv_mem (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {m : GAd σ J}
    (hm : m ∈ leviMin σ J X Y) (hm1 : m ∈ minParOne σ J X) :
    m⁻¹ ∈ leviMin σ J X Y ∧ m⁻¹ ∈ minParOne σ J X := by
  have hF := pfrA h hJ hW
  obtain ⟨d, d', e, e'⟩ := hm
  have hu := unitaryA_matHom m
  have h1 := coef_mul_eq_one hF hu e e'
  have hss := hF.ss
  have hinv : (matHom _ σ J m⁻¹).1 * (matHom _ σ J m).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : ∀ i, d i * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (d' i) = 1 := fun i => by rw [mul_comm, h1 i]
  have h3 : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (d i) * d' i = 1 := coef_mul_eq_one (pfr_swap hF) hu e' e
  have f := inv_act hinv h1 e
  have f' := inv_act hinv h3 e'
  refine ⟨⟨_, _, f, f'⟩, ?_⟩
  obtain ⟨B, -, eB, hB⟩ := hm1
  have hBd : B = diagonal d := by rw [← Bm_eq hF eB, Bm_eq hF e]
  refine ⟨_, Matrix.blockTriangular_diagonal _, f, fun i => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := hB i
  refine ⟨u⁻¹, ?_, by rw [map_inv, hu2, inv_one]⟩
  have hd : d i = u := by rw [← hu1, hBd, Matrix.diagonal_apply_eq]
  rw [Matrix.diagonal_apply_eq]
  exact (Units.inv_eq_of_mul_eq_one_left (by rw [← hd]; exact h1 i)).symm ▸ rfl

theorem leviMin_eq (hF : PFr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (adMat F X) (adMat F Y)) :
    leviMin σ J X Y = {m | (matHom _ σ J m).1 * adMat F X = adMat F X * diagonal (fun i => Bm σ J X Y m i i)} ∩
      {m | (matHom _ σ J m).1 * adMat F Y = adMat F Y * diagonal (fun i => Bm σ J Y X m i i)} := by
  ext m
  constructor
  · rintro ⟨d, d', e, e'⟩
    have a1 : (fun i => Bm σ J X Y m i i) = d := funext fun i => by
      rw [Bm_eq hF e, Matrix.diagonal_apply_eq]
    have a2 : (fun i => Bm σ J Y X m i i) = d' := funext fun i => by
      rw [Bm_eq (pfr_swap hF) e', Matrix.diagonal_apply_eq]
    exact ⟨by simpa only [Set.mem_setOf_eq, a1] using e, by simpa only [Set.mem_setOf_eq, a2] using e'⟩
  · rintro ⟨e, e'⟩
    exact ⟨_, _, e, e'⟩

theorem isClosed_leviMin (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (leviMin σ J X Y) := by
  have hF := pfrA h hJ hW
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hc : ∀ {X' Y' : Matrix (Fin n) (Fin r) E}, Continuous fun m : GAd σ J =>
      adMat F X' * diagonal (fun i => Bm σ J X' Y' m i i) := fun {X' Y'} => by
    have hd : Continuous fun m : GAd σ J => diagonal (fun i => Bm σ J X' Y' m i i) :=
      continuous_matrix fun a b => by
        by_cases hab : a = b
        · subst hab
          simpa using (continuous_Bm (σ := σ) (J := J) (X := X') (Y := Y')).matrix_elem a a
        · simpa [Matrix.diagonal_apply_ne _ hab] using continuous_const
    exact continuous_const.matrix_mul hd
  rw [leviMin_eq hF]
  exact (isClosed_eq ((continuous_matHom_val (σ := σ) (J := J)).matrix_mul continuous_const) hc).inter
    (isClosed_eq ((continuous_matHom_val (σ := σ) (J := J)).matrix_mul continuous_const) hc)

end GlobalTheory.CompanionTheory.ParCocompact.LeviOne


open GlobalTheory.CompanionTheory.ParCocompact.LeviOne in
theorem GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ L : Subgroup (GAd σ J), (L : Set (GAd σ J)) = leviMin σ J X Y ∩ minParOne σ J X ∧ IsClosed (L : Set (GAd σ J)) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  refine ⟨{ carrier := leviMin σ J X Y ∩ minParOne σ J X
            mul_mem' := fun {a b} ha hb => ⟨mul_mem_levi ha.1 hb.1, (minParOne_props h hJ hW).2 a ha.2 b hb.2⟩
            one_mem' := ⟨one_mem_leviMin σ J X Y, one_mem_minParOne⟩
            inv_mem' := fun {a} ha => inv_mem h hJ hW ha.1 ha.2 }, rfl, ?_⟩
  exact (isClosed_leviMin h hJ hW).inter (minParOne_props h hJ hW).1

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor

theorem _root_.GlobalTheory.T.unitary_points_height_bound_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω := by
  exact @GlobalTheory.CompanionTheory.RedCov.MahlerU.mahler_unitary_set
end
