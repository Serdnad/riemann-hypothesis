module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle002
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Lemma44IdentityOfRawTail
import Formalism.SharpRestriction.GrowthBounds.PolBridge
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle009
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LatticeCountingFormula
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnCongruence
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.WedgeSplitTan
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXRen
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXSeg
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.KGShift
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentChainDegreeEven
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolyLinearMapClosed

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

structure ColSys (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O) (mu : ℝ) (β : GlobalTheory X)
    (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) where
  ι : Type
  fin : Fintype ι
  Kc : ι → MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)
  dK : ι → Fin (2 * segS X.TT j + 1) → ℕ
  pl : ι → MonH X
  fC : ι → RHH O X
  oC : ι → ℕ
  dgC : ι → X.TT × Bool → ℕ
  a0 : ℕ
  KInt : ∀ a, Kc a ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)
  KPol : ∀ a, Kc a ∈ Pol (KK O) X.m (dK a)
  digit_le_one : ∀ a i, dK a i ≤ 1
  dKsum : ∀ i, ∑ a, dK a i = (L.LL j).deg i
  Kprod : ∏ a, Kc a = G
  facC : ∀ a, IsFac w (fC a) (oC a)
    (monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)))
  homC : ∀ a, HomW (ndHom X) (oC a)
    (monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)))
  fPol : ∀ a, fC a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC a)
  polC : ∀ a, monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC a)
  plQ : ∀ a l, multideg (pl a) l ≤ X.p ^ X.G'
  dgCQ : ∀ a l, dgC a l ≤ X.p ^ X.G'
  dgCY : ∀ a j', dgC a (topEnd X j', false) = 0
  a0le : (a0 : ℤ) + ∑ i : Fin (segS X.TT j), (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg i : ℤ) else 0) ≤
    (X.seg C0 CE1 CE2 j).A0 X.p
  plSum : ∑ a, pl a = Finsupp.single ((topStart X j, true), 0) ((X.seg C0 CE1 CE2 j).Qj X.p * a0) +
    ∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)))
  oSum : ∑ a, oC a = (∑ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i *
      (L.LL j).deg ⟨2 * (i : ℕ), by have := i.2; omega⟩) + (L.LL j).deg ⟨2 * segS X.TT j, by omega⟩

def ColsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β) (j : Fin (numSeg X.TT)) (y : Tx X.m (L.LL j)),
      y ∈ sAll (L.LL j) (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr →
      Nonempty (ColSys C0 CE1 CE2 X O S.w (mm + (n : ℝ) * ka1 X) β L j (psiR (KK O) (L.LL j) y))

def RestCols : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ColsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.PolBridge

section Span

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

theorem lattice_le_span_psi_image {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ N) :
    YjtZ O (r := r) LL J M ≤ Submodule.span O (psiR (KK O) LL '' sAll LL J M) := by
  have hp : p.Prime := Fact.out
  have hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  obtain ⟨hli, hspan⟩ := hA2 O N r (⟨LL.vec⟩ : Letters (Fin N)) LL.deg
  have hli' : LinearIndependent O (psiR (r := r) O LL) := hli
  have hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg := by
    rw [← hspan]
    congr 1
    ext G
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1.1, x.1.2, x.2, rfl⟩
    · rintro ⟨P, I, h, rfl⟩; exact ⟨⟨(P, I), h⟩, rfl⟩
  have hfin : Finite (Tx r LL) := tx_finite LL hli' hrange
  obtain ⟨Bd, hBd⟩ := exists_bound (r := r) (Lt := (⟨LL.vec⟩ : Letters (Fin N))) (B := LL.deg)
  have hC1 := one_cond D LL hrange hspan (fun th M => (hA3 p O S N r _ LL.deg th M).1) Bd hBd J M hJ
  intro F hF
  obtain ⟨hY, G, hG⟩ := hF
  let φ : MvPolynomial (Fin N × Fin r) O →ₗ[O] MvPolynomial (Fin N × Fin r) (KK O) :=
    (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O))).toLinearMap
  have hG' : MvPolynomial.map (algebraMap O (KK O)) G = F := hG
  have hY' : MvPolynomial.map (algebraMap O (KK O)) G ∈ Yjt (KK O) (r := r) LL J M := by rw [hG']; exact hY
  rw [Yjt, Submodule.mem_inf, Submodule.mem_iInf] at hY'
  have hGP : G ∈ Pol O r LL.deg := (map_mem_Pol_iff _ hinj _ G).1 hY'.1
  have hGs : G ∈ Submodule.span O (psiR O LL '' sAll LL J M) :=
    mem_span_iInter hli' (sK LL J M) (hrange ▸ hGP) (fun k => (hC1 k G hGP).1 (hY'.2 k))
  have h1 : F ∈ Submodule.map φ (Submodule.span O (psiR O LL '' sAll LL J M)) := ⟨G, hGs, hG⟩
  rw [Submodule.map_span, ← Set.image_comp] at h1
  have h2 : (φ ∘ psiR (r := r) O LL) = psiR (KK O) LL := funext fun x => psiR_map LL x
  rwa [h2] at h1

end Span

section Xi

variable {O : Type} [CommRing O] [IsDomain O]

theorem xiVar_inj (N r t : ℕ) : Function.Injective (xiVar N r t) := by
  intro c d h
  simpa [xiVar] using h

theorem xiSpan (N r t b : ℕ) :
    XiPolZ O N r t b ≤ Submodule.span O
      {g : MvPolynomial (BVar N r t) (KK O) | ∃ γ : Fin r → ℕ, ∑ c, γ c = b ∧ g = ∏ c, X (xiVar N r t c) ^ γ c} := by
  intro f hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  obtain ⟨g, rfl⟩ := LinearMap.mem_range.1 h2
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  have hmap : ∀ p : MvPolynomial (BVar N r t) O,
      (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial (BVar N r t) O →ₐ[O] _).toLinearMap p =
        MvPolynomial.map (algebraMap O (KK O)) p := fun p => rfl
  have hsup : ∀ m ∈ g.support, (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b := by
    intro m hm
    have hm' : m ∈ (MvPolynomial.map (algebraMap O (KK O)) g).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
      exact (map_ne_zero_iff _ hinj).2 (MvPolynomial.mem_support_iff.1 hm)
    rw [hmap] at h1
    exact ((MvPolynomial.mem_restrictSupport_iff (KK O)).1 h1) (Finset.mem_coe.2 hm')

  rw [hmap, MvPolynomial.as_sum g, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  obtain ⟨hv, hb⟩ := hsup m hm
  have hmon : m.prod (fun v e => (X v : MvPolynomial (BVar N r t) (KK O)) ^ e) =
      ∏ c, X (xiVar N r t c) ^ m (xiVar N r t c) := by
    rw [Finsupp.prod, ← Finset.prod_image (fun c _ c' _ h => xiVar_inj N r t h)
      (f := fun v => (X v : MvPolynomial (BVar N r t) (KK O)) ^ m v)]
    apply Finset.prod_subset
    · intro v hv'
      obtain ⟨c, rfl⟩ := hv v hv'
      exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
    · intro v _ hv'
      have h0 : m v = 0 := by simpa using hv'
      rw [h0, pow_zero]
  have hprod1 : m.prod (fun v e => (X v : MvPolynomial (BVar N r t) (KK O)) ^ e) = MvPolynomial.monomial m 1 := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  have hterm : MvPolynomial.map (algebraMap O (KK O)) (MvPolynomial.monomial m (g.coeff m)) =
      g.coeff m • ∏ c, X (xiVar N r t c) ^ m (xiVar N r t c) := by
    rw [← hmon, hprod1, MvPolynomial.smul_monomial, Algebra.smul_def, mul_one, MvPolynomial.map_monomial]
  rw [hterm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun c => m (xiVar N r t c), hb, rfl⟩)

end Xi

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

theorem genSet_le {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (B : BlockData N) (hJ : ∀ k, B.T.J k ≤ N) :
    genSet O (r := r) B ⊆ Submodule.span O (colGens O (r := r) B) := by
  intro x hx
  simp only [genSet, Set.mem_iUnion] at hx
  obtain ⟨j, jp, hok, y, hy, g, hg, rfl⟩ := hx
  have key : ∀ y ∈ Submodule.span O (psiR (KK O) (B.lettersAt j jp) '' sAll (B.lettersAt j jp) B.T.J B.T.thr),
      ∀ g ∈ Submodule.span O {g : MvPolynomial (BVar N r B.T.t) (KK O) |
        ∃ γ : Fin r → ℕ, ∑ c, γ c = B.B - jp ∧ g = ∏ c, X (xiVar N r B.T.t c) ^ γ c},
      ((∏ i, B.Ehat O (r := r) i ^ j i) * B.Eplus O (r := r) ^ jp *
          (∏ i, X (scalZ N r B.T.t (Fin.castSucc i)) ^ B.T.z i) * X (scalZ N r B.T.t (Fin.last B.T.t)) ^ B.zPlus) * rename (chainEmb N r B.T.t) y * g ∈ Submodule.span O (colGens O (r := r) B) := by
    intro y hy g hg
    induction hy using Submodule.span_induction with
    | mem y0 hy0 =>
      induction hg using Submodule.span_induction with
      | mem g0 hg0 =>
        obtain ⟨yy, hyy, rfl⟩ := hy0
        obtain ⟨γ, hγ, rfl⟩ := hg0
        exact Submodule.subset_span ⟨j, jp, hok, yy, hyy, γ, hγ, rfl⟩
      | zero => simp
      | add g1 g2 _ _ h1 h2 =>
        rw [mul_add]
        exact Submodule.add_mem _ h1 h2
      | smul a g1 _ h1 =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ a h1
    | zero => simp
    | add y1 y2 _ _ h1 h2 =>
      rw [map_add (f := _), mul_add, add_mul]
      exact Submodule.add_mem _ h1 h2
    | smul a y1 _ h1 =>
      rw [AlgHom.map_smul_of_tower, mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ a h1
  exact key y (lattice_le_span_psi_image (r := r) hA2 hA3 S (B.lettersAt j jp) B.T.J B.T.thr hJ hy) g
    (xiSpan (O := O) N r B.T.t (B.B - jp) hg)

theorem blockData_J_le (p : ℕ) {s r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (k : Fin (blockData p S aTop aPlus m b).T.q) : (blockData p S aTop aPlus m b).T.J k ≤ 2 * s + 1 := by
  show (if h : (k : ℕ) < S.t then 2 * (uTop S ⟨k, h⟩ : ℕ) + 1 else 2 * s + 1) ≤ 2 * s + 1
  split_ifs with h
  · have := (uTop S ⟨k, h⟩).isLt
    omega
  · exact le_rfl

end Gen

theorem asmRTAt_of_facSys {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D)
    {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hF : FacSysAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    AsmRTAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro _ _ X _ _ O _ _ _ _ S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s hs
  have hmem : symFam (KK O) X.p C0 CE1 CE2 X β s ∈
      liftSub C0 Cde CE1 CE2 X O S.w mm n (ordFam C0 CE1 CE2 X β) :=
    symFam_span β (fun j => colGens O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j))) _
      (fun s' hs' => (hF X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s' hs').some.liftable S.w_irr.ne_zero) s
      (fun j => genSet_le hA2 hA3 S _ (blockData_J_le _ _ _ _ _ _) (hs j))
  obtain ⟨raw, hc, τ, hτ, hw⟩ := hmem
  exact ⟨raw, τ, hc, hτ, hw⟩

theorem restAsmRT_of_facSys {D : Formalism.BasicNotions.D7} (hA : admitted D) (h : FacSysCondition) : RestAsmRT := by
  unfold admitted at hA
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, -, -, -, h15, -⟩ := hA
  intro Cc hCc
  obtain ⟨T0, hT0, h1⟩ := h Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h2⟩ := h1 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 Cm hE1 hE2 hm => ?_⟩
  obtain ⟨T2, hT2, h3⟩ := h2 CE1 CE2 Cm hE1 hE2 hm
  exact ⟨T2, hT2, fun CYb Cde Ck CD Cb a b c d e =>
    asmRTAt_of_facSys (D := D) h15 h6 (h3 CYb Cde Ck CD Cb a b c d e)⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.LemmaBAlt.B2 Formalism.MainNotions.ColumnSystems.Pf.Col Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {β : GlobalTheory X} (j : Fin (numSeg X.TT))
  (ka : Fin (2 * segS X.TT j + 1 + 1) → Fin X.m → ℤ) (I'' : ℤ → Finset (Fin X.m))

theorem monomial_sum_eq_prod {ι : Type} (s : Finset ι) (a : ι → MonH X) :
    (monomial (∑ i ∈ s, a i) (1 : KK O) : RHH O X) = ∏ i ∈ s, (monomial (a i) (1 : KK O) : RHH O X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, ← ih, monomial_mul, one_mul]

def colPsiS (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (j : Fin (numSeg X.TT)) :
    MvPolynomial (Fin (2 * segS X.TT j + 1 + 1) × Fin (1 + X.m)) O →+* RHH O X :=
  (rename (phiS X j)).toRingHom.comp (powSubst X.p (LLseg X j) (zS X j)).toRingHom

theorem colPsiS_X (t : Fin (2 * segS X.TT j + 1 + 1)) (v : Fin (1 + X.m)) :
    colPsiS X O j (MvPolynomial.X (t, v)) = (MvPolynomial.X (phiS X j (t, v)) : RHH O X) ^ PS X j t := by
  show rename (phiS X j) (powSubst X.p (LLseg X j) (zS X j) (MvPolynomial.X (t, v))) = _
  unfold powSubst
  rw [aeval_X, map_pow, rename_X]
  rfl

theorem col_ioD_X (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioD ioA
  exact aeval_X _ _

theorem col_tan_eq (c : ℤ) (J : Finset (Fin X.m)) :
    ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) J)) =
      KG c (hsOf ka c) (fun a b => colPsiS X O j (xOf O (2 * segS X.TT j + 1 + 1) (1 + X.m) (a + 1) (Fin.natAdd 1 b)))
        (2 * segS X.TT j + 1) J := by
  rw [Kcol_eq_KG (KK O) ka c (2 * segS X.TT j + 1) le_rfl]
  have e1 := map_KG ((ioD O C0 CE1 CE2 mu X β j).toRingHom.comp
      (rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t)).toRingHom) c
    (hsOf ka c) (xOf (KK O) (2 * segS X.TT j + 1) X.m) (2 * segS X.TT j + 1) J
  have e1' : ioD O C0 CE1 CE2 mu X β j (rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t)
      (KG c (hsOf ka c) (xOf (KK O) (2 * segS X.TT j + 1) X.m) (2 * segS X.TT j + 1) J)) = _ := e1
  rw [e1']
  refine congrFun (KG_congr c (2 * segS X.TT j + 1) (fun _ _ => rfl) (fun a ha => ?_)) J
  funext b
  have ha' : a + 1 < 2 * segS X.TT j + 1 + 1 := by omega
  show ioD O C0 CE1 CE2 mu X β j (rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t)
      (xOf (KK O) (2 * segS X.TT j + 1) X.m a b)) = _
  unfold xOf
  rw [dite_eq_left ha, dite_eq_left ha', rename_X, col_ioD_X]
  have e2 : (⟨a + 1, ha'⟩ : Fin (2 * segS X.TT j + 1 + 1)) = (⟨a, ha⟩ : Fin (2 * segS X.TT j + 1)).succ := rfl
  rw [e2, colPsiS_X, phiS_succ X j C0 CE1 CE2 ⟨a, ha⟩ b]
  unfold PS
  rw [lev_succ X j C0 CE1 CE2 ⟨a, ha⟩ b]
  rfl

variable {vecc : Fin (2 * segS X.TT j + 1) → Bool} {B : Fin (2 * segS X.TT j + 1) → ℕ}

theorem col_sym_eq (h : PH vecc B ka (nuS C0 CE1 CE2 mu X β j)) (c : ℤ) :
    rename (phiS X j) (powSubst X.p (LLseg X j) (zS X j)
        (plTanCol O (muP (nuS C0 CE1 CE2 mu X β j) ka) c (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))) =
      monomial (plS C0 CE1 CE2 mu X β j c) 1 *
        ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) (I'' c))) := by
  have e := symbol_eq h O (colPsiS X O j) c (I'' c)
  have e' : rename (phiS X j) (powSubst X.p (LLseg X j) (zS X j)
        (plTanCol O (muP (nuS C0 CE1 CE2 mu X β j) ka) c (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))) = _ := e
  rw [e', col_tan_eq]
  congr 1
  unfold plS
  rw [monomial_sum_eq_prod, Finset.prod_range]
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases hc : nuS C0 CE1 CE2 mu X β j t.val < c ∧ c ≤ nuS C0 CE1 CE2 mu X β j (t.val + 1)
  · rw [if_pos hc, if_pos hc]
    unfold xOf
    rw [dite_eq_left t.isLt, colPsiS_X, X_pow_eq_monomial]
  · rw [if_neg hc, if_neg hc]
    rfl

theorem col_powSubst_int {N k : ℕ} (LL : LiftLetters (Fin N)) (z : ℤ) (F : MvPolynomial (Fin N × Fin k) O) :
    InA (powSubst X.p (O := O) LL z F) := by
  rw [← mem_intSub]
  unfold powSubst
  induction F using MvPolynomial.induction_on with
  | C a => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hp hq
  | mul_X p v hp => rw [map_mul, aeval_X]; exact Subalgebra.mul_mem _ hp (Subalgebra.pow_mem _ (X_mem_goodSub v rfl) _)

theorem colFac (S : UniformizedDVR X.p O) (hS : S.SqP) (hn : 1 ≤ X.n') (h2 : 2 ≤ numSeg X.TT)
    (h : PH vecc B ka (nuS C0 CE1 CE2 mu X β j)) (hvec : ∀ a, (lamS X j a.succ).2 = vecc a) (c : ℤ) :
    IsFac S.w (fCS C0 CE1 CE2 mu X β j ka O I'' c) (oCS C0 CE1 CE2 mu X β j ka c)
      (monomial (plS C0 CE1 CE2 mu X β j c) 1 *
        ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kcol (KK O) ka c (2 * segS X.TT j + 1) (I'' c)))) := by
  have hOK : ColOK (LLseg X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c := h.colOK (LLseg X j) rfl hvec c
  have hposc := h.posc (LLseg X j) hvec (fun i i' hlt hv => posS_lt X j i i' hlt hv) c
  have hg1 : IsGLW (1 : Matrix (Fin (1 + X.m)) (Fin (1 + X.m)) (WF X.p X.n')) := isGLW_one' _
  rw [← col_sym_eq j ka I'' h c]
  refine ⟨?_, fun g hg => ?_, ?_, ?_⟩
  · exact inA_rename _ _ (column_kernel_components_integral X.p X.n' (LLseg X j) 1 hg1 (zS X j) _ c _)
  · exact (inWjRg_rename S.w 1 (LLseg X j) (hhLetters X.TT) (lamS X j) (lamS_injective X j h2) (fun _ => rfl)
      (pos_congr X j) (Nat.add_comm 1 X.m) g _ _).2
      (lifted_column_order X.p X.n' (frobCong X.p X.n' hn) S hS (LLseg X j) 1 _ hg1 (isGLW_submatrix_cast _ g hg) (zS X j) _ c hOK
        (posS_mono X j) (position_le_segment_end X j) hposc _)
  · have hc := lifted_column_congruence X.p X.n' S (LLseg X j) 1 hg1 (zS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c (posS_mono X j)
      (position_le_segment_end X j) hposc (SgVanish_of (LLseg X j) _ c hOK) (fun J => plTanCol_eq_SgW O (LLseg X j) _ c hOK h.dom J)
      (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c))
    have hr := inWj_rename (phiS X j) S.w _ _ hc
    have e1 : lift1 X O S.w (fCS C0 CE1 CE2 mu X β j ka O I'' c) =
        rename (phiS X j) (liftSubst X.p X.n' O S.w 1 (LLseg X j) 1
          (KKc X.p X.n' (O := O) (LLseg X j) 1 (zS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c
            (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))) := by
      have := liftSubst_rename S.w 1 (LLseg X j) (hhLetters X.TT) (lamS X j) (fun _ => rfl) (pos_congr X j)
        (Nat.add_comm 1 X.m) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (KKc X.p X.n' (O := O) (LLseg X j) 1 (zS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c
            (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))
      rw [one_submatrix_cast] at this
      exact this
    rw [e1, ← C_mul_eq_smul, map_pow]
    rw [map_sub, map_mul, rename_C] at hr
    exact hr
  · exact inA_rename _ _ (col_powSubst_int _ _ _)

end

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def segMon (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (A : MonH X) : RHH O X :=
  (∏ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
    (MvPolynomial.X ((topOdd X j i, true), c) ^ A ((topOdd X j i, true), c) *
      MvPolynomial.X ((topOdd X j i, false), c) ^ A ((topOdd X j i, false), c))) *
  ∏ c : Fin (X.m + 1), (MvPolynomial.X ((topEnd X j, true), c) ^ A ((topEnd X j, true), c) *
      MvPolynomial.X ((topEnd X j, false), c) ^ A ((topEnd X j, false), c))

def chW {s : ℕ} (i : Fin s) : Fin (2 * s + 1) := ⟨2 * i.val, by omega⟩
def chE {s : ℕ} (i : Fin s) : Fin (2 * s + 1) := ⟨2 * i.val + 1, by omega⟩
def chU (s : ℕ) : Fin (2 * s + 1) := ⟨2 * s, by omega⟩

def nuSeg (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ)
    (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) : ℕ :=
  (∑ i : Fin (segS X.TT j), ((X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
    (∑ c : Fin X.m, A ((topOdd X j i, true), c.succ)) + A ((topOdd X j i, false), 0))) +
  (jp + du (chU _) + ∑ c : Fin X.m, A ((topEnd X j, true), c.succ))

def SegCoreAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β),
    ∀ e : ℕ, 1 ≤ e → e < n →
    ∀ (j : Fin (numSeg X.TT)) (ju : Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ), (∀ i, ju i ≤ L.lv j i) →
    ∀ (Gu : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) (du : Fin (2 * segS X.TT j + 1) → ℕ),
      Gu ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m) →
      Gu ∈ Pol (KK O) X.m du → (∀ a, du a ≤ (L.LL j).deg a) →
      (∀ k, Gu ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
        ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k + (((X.N1 * e : ℕ) : ℤ) : WithTop ℤ))) →
    ∀ A : MonH X,

      (∀ i : Fin (segS X.TT j), (β j).rz i 0 + (X.seg C0 CE1 CE2 j).P X.p i *
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
            (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) ≤
          A ((topOdd X j i, true), 0) + X.p ^ X.G' * e) →
      (∀ i : Fin (segS X.TT j), ∑ c : Fin X.m, (A ((topOdd X j i, true), c.succ) - (β j).rz i c.succ) ≤ X.p ^ X.G' * e) →
      (∀ i : Fin (segS X.TT j), A ((topOdd X j i, false), 0) ≤ (β j).ry i 0 + (X.seg C0 CE1 CE2 j).P X.p i *
          (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) + X.p ^ X.G' * e) →
      (∑ c : Fin X.m, A ((topEnd X j, true), c.succ) ≤ X.p ^ X.G' * e) →
      A ((topEnd X j, false), 0) = 0 → (∀ c : Fin X.m, A ((topEnd X j, false), c.succ) = L.γ j c) →

      (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
        ∑ c, A ((topOdd X j i, true), c) = (X.seg C0 CE1 CE2 j).bTop i) →
      (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) +
        ∑ c, A ((topOdd X j i, false), c) = segATop X.TT X.aT j i) →
      (L.jp j + du (chU _) + ∑ c, A ((topEnd X j, true), c) = segAPlus X.TT X.aT j) →
      ∃ b' : SegBlock (segS X.TT j) X.m,
        BLk C0 Cde CE1 CE2 X (((X.c - (n - e) : ℕ) : ℝ) * ka1 X) j b' ∧
        blockOrd X.p (X.seg C0 CE1 CE2 j) b' = nuSeg C0 CE1 CE2 X j ju (L.jp j) du A ∧
        ∃ u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
            (mm + ((n - e : ℕ) : ℝ) * ka1 X) b').SSZ O (r := X.m),
          L.head O j ju Gu * segMon O X j A = ioBlock (KK O) X.p C0 CE1 CE2 X j b' u

def RestSegCore : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SegCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end
