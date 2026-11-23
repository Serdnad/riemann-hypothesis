module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle064
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.FormalDegreeBessel.Bundle002
public import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.MXMulVecMid
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle066
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle084
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfUnitWords
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

open scoped ContDiff

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jdh_ckOn_of_contDiff {k r : ℕ} {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {f : B.Mat k r → E'}
    (hf : ContDiff ℝ ∞ f) (UU : Set (B.Mat k r)) : B.CkOn ⊤ UU f :=
  fun _ _ => ⟨Set.univ, f, isOpen_univ, trivial, hf.contDiffOn, fun _ _ _ => rfl⟩

theorem jdh_opOrder_le {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o : ℕ) (Θ : B.DiffOp k r Wp Wq)
    (h : ∀ Tm ∈ Θ, Tm.word.length ≤ o) : B.opOrder Θ ≤ o := by
  unfold B.opOrder
  induction Θ with
  | nil => simp
  | cons T Θ ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h T (List.mem_cons_self ..)) (ih fun Tm hTm => h Tm (List.mem_cons_of_mem _ hTm))

theorem jdh_pd_star {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ P) :
    U.IsPolyDeg κ (fun g => star (P g)) := by
  obtain ⟨q, hq, he⟩ := h
  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, fun g => ?_⟩
  · refine (MvPolynomial.totalDegree_rename_le _ _).trans (le_trans ?_ hq)
    exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  · show star (P g) = _
    rw [he g, MvPolynomial.eval_rename, MvPolynomial.eval_map]
    show (starRingEnd ℂ) (MvPolynomial.eval₂ (RingHom.id ℂ) _ q) = _
    rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext x
    rcases x with x | x <;> simp

theorem polynomial_decay_admissible : JDPolyOK := by
  apply GlobalTheory.HatNF.polyOp_ok <;> assumption

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellDecomposition

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF

def CellDecomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), ∀ g ∈ GV k r, (∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ n ∈ Nset k r, ∃ n' ∈ Nset k r, ∃ c : Fin r → ℂ, (∀ a, c a ≠ 0) ∧
      ∃ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k ∧ g = n⁻¹ * bigCell k r c μ * n'

variable {k r : ℕ}

theorem bigCell_one_fixes_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) : bigCell k r c 1 *ᵥ z = z := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have key : ∀ j, bigCell k r c 1 i j * z j = if j = i then z i else 0 := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
      split_ifs with h
      · subst h
        exact (hz _ hj).symm
      · rfl
    · have hj1 : ¬ j.val < r := by omega
      have hj2 : j.val ≤ r + k := by omega
      simp only [bigCell, dif_neg hj1, dif_pos hj2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · simp only [dif_pos hi, Matrix.one_apply]
        by_cases hij : j = i
        · subst hij
          simp
        · have hne : (⟨i.val - r, by omega⟩ : Fin (k + 1)) ≠ ⟨j.val - r, by omega⟩ := by
            intro h
            apply hij
            ext
            simp only [Fin.mk.injEq] at h
            omega
          simp [hne, hij]
      · simp only [dif_neg hi, zero_mul]
        rw [if_neg]
        rintro rfl
        omega
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp

theorem n_inv_S {z : Fin (2 * r + k + 1) → ℂ} {n : Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw z, n⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn, (one_mul _).symm⟩

theorem n_S {z : Fin (2 * r + k + 1) → ℂ} {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw z, n, hn, (one_mul n).symm⟩

end Formalism.FourierDecayAlt.P.BigCellDecomposition

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF

theorem jf_psiOnto_of_cellDecomp (hCD : BigCellDecomposition.CellDecomp) : Formalism.FourierDecayAlt.JF.PsiOnto := by
  intro k r Wp Wq _ _ _ _ D g hg
  obtain ⟨n, hn, n', hn', c, hc, μ, hμ, rfl⟩ := hCD k r D.z D.z' g hg.1 hg.2.1
  set ζ := herm (Hb k) (μ *ᵥ wbPart k r D.z') (wbPart k r D.z) with hζdef
  have hmin := bigCellMinors k r D.z D.z' c μ D.z_mem D.z'_mem

  have hG : 0 < Gf k r D.z D.z' (bigCell k r c μ) := by
    have := hg.2.2
    rwa [gInv k r D.z D.z' D.z_mem D.z'_mem _ (BigCellDecomposition.n_inv_S hn) _ (BigCellDecomposition.n_S hn')] at this
  have hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq ζ := by
    have hz := hmin.2.2 hc
    rw [BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r c μ) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r c μ) (Fin.last (r + 1)) = ζ * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r c μ) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    unfold Gf at hG
    rw [hlast, ← hP, Complex.normSq_mul] at hG
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith

  have hfac := bruhat_big_cell_factorization k r c μ
  have huw := unipotent_weyl_properties k r
  have hm : embWb k r μ ∈ UWb k r := TwoByOneBlock.emb_mem_UWb hμ
  have hmz : herm (Hpk k r) (embWb k r μ *ᵥ D.z') D.z = ζ := by
    have e1 : embWb k r μ *ᵥ D.z' = bigCell k r c μ *ᵥ D.z' := by
      rw [hfac.2, ← Matrix.mulVec_mulVec, BigCellDecomposition.bigCell_one_fixes_vector D.z'_mem]
    rw [e1, BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem]
  obtain ⟨h, hh, h', hh', hmeq⟩ := b2_rank_one_coord k r D.z D.z' D.μsec D.k_pos D.z_mem D.z'_mem D.T_pos
    D.T'_pos D.sec (embWb k r μ) hm (by rw [hmz]; exact hζ)
  rw [hmz] at hmeq
  have hu1 := WeylGroupFacts.isUnit_of_uh hh.1
  have hu2 := WeylGroupFacts.isUnit_of_uh hh'.1
  have hun := WeylGroupFacts.isUnit_of_uh hn.1
  have hcomm : bigCell k r c 1 * h⁻¹ = h⁻¹ * bigCell k r c 1 :=
    (huw.2.2 c h⁻¹ (huw.2.1 D.z (BigCellInversePair.uw_inv hh))).symm

  refine ⟨((h, h * n * h⁻¹), (h', h' * n' * h'⁻¹)), ⟨hh,
      (uWNormal k r D.z D.z_mem h hh n hn).1, hh', (uWNormal k r D.z' D.z'_mem h' hh' n' hn').1⟩,
    (c, ζ), ⟨hc, hζ⟩, ?_⟩
  show n⁻¹ * bigCell k r c μ * n' = h⁻¹ * (h * n * h⁻¹)⁻¹ * bigCell k r c (D.μsec ζ) * (h' * n' * h'⁻¹) * h'
  rw [hfac.1, hmeq, (bruhat_big_cell_factorization k r c (D.μsec ζ)).1]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu1]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu2, Matrix.mul_one]
  rw [← Matrix.mul_assoc (bigCell k r c 1) h⁻¹, hcomm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu1]

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PositiveOrbitOpen

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section local_

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_local {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) {X : Mat k r} (hX : inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → RdV X f₁ x = RdV X f₂ x := by
  intro x hx hxG
  have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt x X 0
  have hγ0 : x * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = x := by simp
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x * NormedSpace.exp ((t : ℂ) • X) ∈ V :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hV.mem_nhds hx)
  show deriv (fun t : ℝ => f₁ (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f₂ (x * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hmem] with t ht
  exact h _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hxG hX t)

theorem rw_local {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) (w : List (Mat k r)) (hw : ∀ X ∈ w, inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → Rw w f₁ x = Rw w f₂ x := by
  induction w with
  | nil => exact h
  | cons X w ih =>
    intro x hx hxG
    exact rdV_local hV (ih (fun Y hY => hw Y (List.mem_cons_of_mem X hY))) (hw X (by simp)) x hx hxG

theorem rw_smul (w : List (Mat k r)) (c : ℂ) (f : Mat k r → E) : Rw w (c • f) = c • Rw w f := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show RdV X (Rw w (c • f)) = c • RdV X (Rw w f)
    rw [ih]
    funext g
    simp only [RdV, Pi.smul_apply]
    exact deriv_const_smul_field (f := fun t : ℝ => Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) c

end local_

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wq] in
theorem zhat_cont (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (fun g : Mat k r => Zhat k r z z' g) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold Zhat herm
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))

omit [FiniteDimensional ℂ Wq] in
theorem dmin_cont (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    Continuous (fun g : Mat k r => Dmin k r z z' g l) := by
  unfold Dmin
  exact ((zhat_cont z z').matrix_submatrix _ _).matrix_det

omit [FiniteDimensional ℂ Wq] in
theorem gf_cont (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (fun g : Mat k r => Gf k r z z' g) := by
  unfold Gf
  exact (Complex.continuous_normSq.comp (dmin_cont z z' _)).sub
    (continuous_const.mul (Complex.continuous_normSq.comp (dmin_cont z z' _)))

omit [FiniteDimensional ℂ Wq] in
theorem omPlus_open (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Q.OmPlus k r z z') := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have h1 : ∀ᶠ x in 𝓝 g, ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' x l ≠ 0 := by
    refine Filter.eventually_all.2 fun l => ?_
    by_cases hl : l.val ≤ r
    · filter_upwards [(dmin_cont z z' l).continuousAt.eventually_ne (hg.1 l hl)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hl
  have h2 : ∀ᶠ x in 𝓝 g, 0 < Gf k r z z' x := continuousAt_const.eventually_lt (gf_cont z z').continuousAt hg.2
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

omit [FiniteDimensional ℂ Wq] in
theorem sgs_S (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ ∈ Sset k r D.z ∧
      (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ Sset k r D.z' := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_inv_rev]
    exact ⟨_, BigCellInversePair.uw_inv h1, _, WeylGroupFacts.mem_n_inv h2, rfl⟩
  · exact (sGroup k r D.z' D.z'_mem).2.1 _ ⟨1, BigCellZetaMinors.one_uw _, _, h4, (Matrix.one_mul _).symm⟩ _
      ⟨_, h3, 1, WeylGroupFacts.mem_n_one, (Matrix.mul_one _).symm⟩

omit [FiniteDimensional ℂ Wq] in
theorem sgs_GV (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {y : Mat k r} (hy : y ∈ GV k r) :
    sgs p y ∈ GV k r := by
  rw [B5.sgs_eq]
  exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv (B5.inSS_left D hp)) hy) (B5.inSS_right D hp)

omit [FiniteDimensional ℂ Wq] in
theorem sgs_Om (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {y : Mat k r} (hy : y ∈ Om k r D.z D.z') :
    sgs p y ∈ Om k r D.z D.z' := by
  refine ⟨sgs_GV D hp hy.1, fun l hl => ?_, ?_⟩
  · rw [BigCellZetaMinors.dmin_sgs D hp]; exact hy.2.1 l hl
  · obtain ⟨hs, hs'⟩ := sgs_S D hp
    show 0 < Gf k r D.z D.z' (sgs p y)
    rw [B5.sgs_eq, gInv k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' y]
    exact hy.2.2


end Formalism.FourierDecayAlt.P.PositiveOrbitOpen

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section

theorem Formalism.FourierDecayAlt.P.polynomial_map_proper : Formalism.FourierDecayAlt.C2.PolyProper :=
  PI.PolynomialProperness.polyProper_of_mx PI.PolynomialProperness.mxFacts
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

theorem quadratic_local_family_holds : GQLFam := by
  intro Wp Wq _ _ _ _ _ _ P Bs _ _ Dc Φ hF Y a b
  obtain ⟨hO, hD, hM, hS, hFF⟩ := hF
  refine ⟨hO, hD, hM, ?_, ?_⟩
  · exact Formalism.FourierDecayAlt.P.transfer_joint_smooth _ _ _ _ _ _ _ Φ (Y : ℂ) a b hO hS
  · intro c hc
    exact Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms _ _ _ _ _ _ _ _ _ _ (Y : ℂ) a b Bs.z_mem Bs.z'_mem (hD c hc) _ (hFF c hc)

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hsVec_contDiff {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    ContDiff ℝ ∞ (fun A : W →L[ℂ] V => B.hsVec A) := by
  let L : (W →L[ℂ] V) →ₗ[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℂ W) => V) :=
    { toFun := fun A => B.hsVec A
      map_add' := fun A A' => by ext i; simp [B.hsVec]
      map_smul' := fun c A => by ext i; simp [B.hsVec] }
  haveI : FiniteDimensional ℝ (W →L[ℂ] V) := FiniteDimensional.complexToReal _
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem wq_contDiff (k r : ℕ) (TT : ℝ) : ContDiff ℝ ∞ (fun x : MA.E r => MA.wq k x TT) := by
  have hn : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
    simp_rw [Complex.normSq_eq_norm_sq]
    exact contDiff_norm_sq ℝ
  unfold MA.wq
  apply ContDiff.mul
  · apply contDiff_prod
    intro l _
    exact (hn.comp ((contDiff_apply ℝ (fun _ => ℂ) l).comp contDiff_fst)).pow _
  · exact ((hn.comp contDiff_snd).sub contDiff_const).pow _

theorem wq_pos {k r : ℕ} {TT : ℝ} {x : MA.E r} (hx : x ∈ MA.Qset r TT) : 0 < MA.wq k x TT := by
  obtain ⟨h1, h2⟩ := hx
  unfold MA.wq
  apply mul_pos
  · apply Finset.prod_pos
    intro l _
    exact pow_pos (Complex.normSq_pos.mpr (h1 l)) _
  · exact pow_pos (by linarith) _

theorem trace_smoothness : TrSmooth := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hIP e he J hJ ρ
  obtain ⟨-, -, -, hTz, hTz', -, -⟩ := hIP
  have hsub : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
      q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    have h2 : (D.parOf S v).TT < Complex.normSq q.2 := hq.2
    have h3 : (D.parOf S v).TT = (D.parOf S v).T * (D.parOf S v).T' := rfl
    rw [h3, ← hTz, ← hTz'] at h2
    exact h2
  have hgq : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
      B.gq (T v).base q ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v := fun q hq =>
    om_sub' (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base (hsub q hq))
  have hgqS : ContDiffOn ℝ ∞ (fun q => B.gq (T v).base q) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    (contDiffOn_infty.mpr fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn (T v).base n).mono hsub
  have hJq : ContDiffOn ℝ ∞ (fun q => B.hsVec (J (B.gq (T v).base q)))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := by
    intro x hx
    obtain ⟨U, F, hU, hxU, hF, hJF⟩ := hJ.1 _ (hgq x hx)
    have hFat : ContDiffAt ℝ ∞ F (B.gq (T v).base x) := hF.contDiffAt (hU.mem_nhds hxU)
    have h1 : ContDiffWithinAt ℝ ∞ (fun q => F (B.gq (T v).base q))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) x := hFat.comp_contDiffWithinAt x (hgqS x hx)
    have h2 : ContDiffWithinAt ℝ ∞ (fun q => B.hsVec (F (B.gq (T v).base q)))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) x :=
      (hsVec_contDiff (V := Wp (S.pl v)) (W := Wq (S.pl v))).contDiffAt.comp_contDiffWithinAt x h1
    refine h2.congr_of_eventuallyEq ?_ ?_
    · have hpre := (hgqS x hx).continuousWithinAt.preimage_mem_nhdsWithin (hU.mem_nhds hxU)
      filter_upwards [hpre, self_mem_nhdsWithin] with y hyU hyQ
      rw [hJF _ hyU (hgq y hyQ).1]
    · rw [hJF _ hxU (hgq x hx).1]
  have he2 : ContDiffOn ℝ ∞ (fun q : MA.E (D.parOf S v).r => B.hsVec (e ρ q.2))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    (hsVec_contDiff (V := Wp (S.pl v)) (W := Wq (S.pl v))).comp_contDiffOn
      ((he.1 ρ).comp contDiff_snd.contDiffOn (fun q hq => hq.2))
  have hw0 : ContDiffOn ℝ ∞ (fun q : MA.E (D.parOf S v).r => Real.sqrt (MA.wq S.G.k q (D.parOf S v).TT))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    (wq_contDiff _ _ _).contDiffOn.sqrt fun q hq => (wq_pos hq).ne'
  have hw : ContDiffOn ℝ ∞ (fun q : MA.E (D.parOf S v).r =>
      ((Real.sqrt (MA.wq S.G.k q (D.parOf S v).TT) : ℝ) : ℂ))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hw0
  have hF := hw.mul (ContDiffOn.inner ℂ he2 hJq)
  show ContDiffOn ℝ MA.sm (MA.ext _) (MA.Qset (D.parOf S v).r (D.parOf S v).TT)
  refine hF.congr ?_
  intro x hx
  rw [MA.ext, dite_eq_left hx]

end Formalism.FourierDecayAlt.P.CutMP.En
end
