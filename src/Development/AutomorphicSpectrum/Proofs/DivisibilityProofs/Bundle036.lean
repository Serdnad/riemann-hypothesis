module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LowerBoundOfBaseSetting
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle011
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle017
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagRatioTrdeg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle013
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle026
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (FlBlock FlIdx PFl xLine xDeg yFl fsHerm ΩFl refNorm)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Top.HhLabel

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def blockMap (σ : Equiv.Perm Ψ) : FlBlock Ψ N → FlBlock Ψ N := fun q => (σ q.1, q.2)

def coordMap (σ : Equiv.Perm Ψ) : (Σ q : FlBlock Ψ N, FlIdx Ψ N q) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨(σ p.1.1, p.1.2), p.2⟩

theorem blockMap_bijective (σ : Equiv.Perm Ψ) : Function.Bijective (blockMap (N := N) σ) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    simp only [blockMap, Prod.mk.injEq] at h
    rw [σ.injective h.1, h.2]
  · rintro ⟨τ, i⟩
    exact ⟨(σ.symm τ, i), by simp [blockMap]⟩

theorem coordMap_injective (σ : Equiv.Perm Ψ) : Function.Injective (coordMap (N := N) σ) := by
  rintro ⟨⟨τ, i⟩, A⟩ ⟨⟨τ', i'⟩, A'⟩ h
  simp only [coordMap, Sigma.mk.inj_iff, Prod.mk.injEq] at h
  obtain ⟨⟨h1, rfl⟩, h2⟩ := h
  obtain rfl := σ.injective h1
  cases eq_of_heq h2
  rfl

theorem coordMap_surjective (σ : Equiv.Perm Ψ) : Function.Surjective (coordMap (N := N) σ) := by
  rintro ⟨⟨τ, i⟩, A⟩
  refine ⟨⟨(σ.symm τ, i), A⟩, Sigma.ext (by simp [coordMap]) HEq.rfl⟩

theorem isBlockMap (σ : Equiv.Perm Ψ) : IsBlockMap (blockMap (N := N) σ) (coordMap σ) :=
  ⟨(blockMap_bijective σ).1, coordMap_injective σ, fun _ => rfl, fun q _ => coordMap_surjective σ q⟩

def matEquiv (N : ℕ) (σ : Equiv.Perm Ψ) : (Ψ × Fin N × Fin N) ≃ (Ψ × Fin N × Fin N) :=
  Equiv.prodCongr σ (Equiv.refl _)

def fieldAut (σ : Equiv.Perm Ψ) : ΩFl Ψ N ≃+* ΩFl Ψ N :=
  IsFractionRing.ringEquivOfRingEquiv (renameEquiv ℚ (matEquiv N σ)).toRingEquiv

theorem yFl_coordMap (σ : Equiv.Perm Ψ) (p : Σ q : FlBlock Ψ N, FlIdx Ψ N q) :
    yFl Ψ N (coordMap σ p) = fieldAut σ (yFl Ψ N p) := by
  unfold yFl fieldAut
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  show _ = (renameEquiv ℚ (matEquiv N σ)).toRingEquiv.toRingHom _
  rw [RingHom.map_det]
  congr 1
  refine Matrix.ext fun a b => ?_
  exact (rename_X (R := ℚ) (matEquiv N σ) (p.1.1, Fin.castLE (GroundTheory.Heights₂.Heights.LowerBoundFree.step_le p.1.2) a, p.2.1 b)).symm

theorem mCoordIdeal_ringHom {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    (i : Ω₀ →+* Ω) (y₀ : (Σ k, J k) → Ω₀) : mCoordIdeal (fun p => i (y₀ p)) = mCoordIdeal y₀ := by
  have key : ∀ f : MRing J, mConeMap (fun p => i (y₀ p)) f = MvPolynomial.map i (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp => simp only [map_mul, hp]; simp [mConeMap]
  ext f
  show mConeMap _ f = 0 ↔ mConeMap _ f = 0
  rw [key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective i i.injective)

theorem imageZ_PFl (σ : Equiv.Perm Ψ) : imageZ (coordMap σ) (PFl Ψ N) = PFl Ψ N := by
  unfold PFl
  rw [← GroundTheory.Heights₂.Heights.Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v (isBlockMap σ),
    ← mCoordIdeal_ringHom (fieldAut (N := N) σ : ΩFl Ψ N →+* ΩFl Ψ N) (yFl Ψ N)]
  congr 1
  funext p
  exact yFl_coordMap σ p

theorem blockFnField_coordMap (σ : Equiv.Perm Ψ) :
    blockFnField (yFl Ψ N ∘ coordMap σ) = blockFnField (yFl Ψ N) := by
  unfold blockFnField
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨coordMap σ p, coordMap σ q, by simp [coordMap, hpq], rfl⟩
  · rintro ⟨p, q, hpq, rfl⟩
    obtain ⟨p', rfl⟩ := coordMap_surjective σ p
    obtain ⟨q', rfl⟩ := coordMap_surjective σ q
    exact ⟨p', q', (blockMap_bijective σ).1 hpq, rfl⟩

theorem xDeg_blockMap (σ : Equiv.Perm Ψ) (p : Ψ × Fin N) (q : FlBlock Ψ N) :
    xDeg Ψ N (σ p.1, p.2) (blockMap σ q) = xDeg Ψ N p q := by
  by_cases h : q.1 = p.1 <;> simp [xDeg, blockMap, h]

theorem isPullHerm_xLine (σ : Equiv.Perm Ψ) (p : Ψ × Fin N) :
    IsPullHerm (blockMap σ) (coordMap σ) (xLine Ψ N p) (xLine Ψ N (σ p.1, p.2)) := by
  refine ⟨?_, fun z' => ?_⟩
  · show xDeg Ψ N (σ p.1, p.2) = pullDeg (blockMap σ) (xDeg Ψ N p)
    funext q
    obtain ⟨q', rfl⟩ := (blockMap_bijective σ).2 q
    unfold pullDeg
    rw [(blockMap_bijective σ).1.extend_apply, xDeg_blockMap]
  · show refNorm (xDeg Ψ N (σ p.1, p.2)) z' = refNorm (xDeg Ψ N p) fun r => z' (coordMap σ r)
    unfold refNorm
    refine (Fintype.prod_bijective (blockMap σ) (blockMap_bijective σ) _ _ fun k => ?_).symm
    rw [xDeg_blockMap]
    rfl

theorem degree_mapDomain {J J' : Type} (f : J → J') (m : J →₀ ℕ) : (m.mapDomain f).degree = m.degree := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), ha, hb]
  | single a n => simp [Finsupp.mapDomain_single, Finsupp.degree_single]

end GlobalTheory.CompanionTheory.Ar.Top.HhLabel

namespace GlobalTheory.CompanionTheory.Ar.Top


open HhLabel in
theorem hhFl_labelInv : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ]
    (N : ℕ) [Nonempty Ψ], 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) →
    LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  intro II hII Ψ _ _ N _ _ hP σ F
  have key : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N,
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (σ (w k).1, (w k).2)) =
        II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (w k)) := by
    intro w
    have himg := imageZ_PFl (N := N) σ
    have hPF := hII.2.2.1 (FlBlock Ψ N) (FlIdx Ψ N) (FlBlock Ψ N) (FlIdx Ψ N) (blockMap σ) (coordMap σ) (ΩFl Ψ N)
      (yFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (w k)) (fun k => xLine Ψ N (σ (w k).1, (w k).2))
      (isBlockMap σ) hP (by show IsArithVar (imageZ (coordMap σ) (PFl Ψ N)) _; rw [himg]; exact hP)
      (fun _ => GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)
      (fun j => isPullHerm_xLine σ (w j))
    rw [blockFnField_coordMap, IntermediateField.relfinrank_self, Nat.cast_one, one_mul] at hPF
    exact hPF.trans (congrArg (fun P => II (FlBlock Ψ N) (FlIdx Ψ N) P (dimFl Ψ N + 1) fun k => xLine Ψ N (w k)) himg)
  induction F using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | monomial m c =>
    rw [rename_monomial]
    by_cases hm : m.degree = dimFl Ψ N + 1
    · obtain ⟨w, rfl⟩ := RootFieldNumerics.HH.exists_word _ m hm
      have hmap : (∑ k, Finsupp.single (w k) (1 : ℕ)).mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) =
          ∑ k, Finsupp.single (σ (w k).1, (w k).2) 1 := by
        rw [Finsupp.mapDomain_finsetSum]
        simp only [Finsupp.mapDomain_single]
      have hwd := RootFieldNumerics.HH.hhFl_word II hII.1 hP (fun k => (σ (w k).1, (w k).2)) c
      rw [hmap, hwd, RootFieldNumerics.HH.hhFl_word II hII.1 hP w c, key w]
    · rw [HhModel.hhFl_monomial_of_ne II _ _ (by rwa [degree_mapDomain]), HhModel.hhFl_monomial_of_ne II _ _ hm]

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagRatioTrdeg GroundTheory.Heights₂.Heights.LowerBoundFree.FlagArithVar

theorem pivotRatio_algebraicIndependent (F : Type) [Field F] (Ψ : Type) (n : ℕ) :
    AlgebraicIndependent F (pivotRatio F Ψ n) := by
  classical
  have hy := pivot_indep F Ψ n
  let δ : PivotIdxLe Ψ n → PivotIdxLe Ψ n :=
    fun q => (q.1, ⟨q.2.1, ⟨Fin.castLE (Nat.sub_le n 1) q.2.1, by simp⟩⟩)
  have hz := ratio_indep F hy δ (fun q => rfl)
  let incl : PivotIdx Ψ n → PivotIdxLe Ψ n := fun q => (q.1, ⟨q.2.1, ⟨q.2.2.1, q.2.2.2.le⟩⟩)
  have hincl : Function.Injective incl := by
    rintro ⟨τ, a, b, hb⟩ ⟨τ', a', b', hb'⟩ h
    simp only [incl, Prod.mk.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨h0, h1, h2⟩ := h
    subst h0 h1
    simp only [heq_eq_eq, Subtype.mk.injEq] at h2
    subst h2
    rfl
  have hrat : (fun q : PivotIdxLe Ψ n => if δ q = q then pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 else
      pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 / pivotMinor (genMatFr F Ψ n (δ q).1) (δ q).2.1 (δ q).2.2.1) ∘
        incl = pivotRatio F Ψ n := by
    funext q
    have hne : δ (incl q) ≠ incl q := by
      intro h
      have := congrArg (fun r : PivotIdxLe Ψ n => ((r.2.2.1 : Fin n) : ℕ)) h
      simp only [δ, incl, Fin.val_castLE] at this
      have := q.2.2.2
      omega
    simp only [Function.comp_apply, hne, if_false]
    rfl
  exact hrat ▸ hz.comp incl hincl

theorem flag_mem_of_le (F : Type) [Field F] {K : Type} [Field K] [Algebra F K] {m : ℕ}
    (g : Matrix (Fin m) (Fin m) K) (A : IntermediateField F K) (hL : ∀ a, IndefiniteRowSideFullHecke.Inter.leadMinor g a ≠ 0)
    (j : Fin (m - 1))
    (hA : ∀ (a : Fin (m - 1)) (b : Fin m), (a : ℕ) ≤ j → (a : ℕ) < b → pivotMinor g a b / IndefiniteRowSideFullHecke.Inter.leadMinor g a ∈ A)
    (S : PluckerBlocks m m j) : flagMinor g j S / IndefiniteRowSideFullHecke.Inter.leadMinor g j ∈ A := by
  have hj : (j : ℕ) + 1 ≤ m := by have := j.2; omega
  have hent : ∀ (a : Fin (m - 1)) (b : Fin m), (a : ℕ) ≤ j → pivotMinor g a b / IndefiniteRowSideFullHecke.Inter.leadMinor g a ∈ A := by
    intro a b haj
    rcases lt_trichotomy (b : ℕ) a with h | h | h
    · rw [pivotMinor_eq_zero g a b h, zero_div]
      exact A.zero_mem
    · have e : b = Fin.castLE (Nat.sub_le m 1) a := Fin.ext h
      subst e
      show IndefiniteRowSideFullHecke.Inter.leadMinor g a / IndefiniteRowSideFullHecke.Inter.leadMinor g a ∈ A
      rw [div_self (hL a)]
      exact A.one_mem
    · exact hA a b haj h
  let U : Matrix (Fin (j + 1)) (Fin (j + 1)) K := Matrix.of fun r s =>
    pivotMinor g ⟨r, by have := r.2; have := j.2; omega⟩ (S.1.orderEmbOfFin S.2 s) /
      IndefiniteRowSideFullHecke.Inter.leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩
  have hP : (pivotMatrix g).submatrix (Fin.castLE hj) (S.1.orderEmbOfFin S.2) =
      Matrix.diagonal (fun r : Fin (j + 1) => IndefiniteRowSideFullHecke.Inter.leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) * U := by
    ext r s
    rw [Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, U]
    rw [dite_eq_left (by simp only [Fin.val_castLE]; have := r.2; have := j.2; omega)]
    rw [mul_div_cancel₀ _ (hL _)]
    rfl
  have hdet : flagMinor (pivotMatrix g) j S =
      (∏ r : Fin (j + 1), IndefiniteRowSideFullHecke.Inter.leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) * U.det := by
    unfold flagMinor
    rw [hP, Matrix.det_mul, Matrix.det_diagonal]
  have hid := FlagPivotIdentity.proof K m g j S
  rw [prod_Iic_fin, hdet] at hid
  have hne : (∏ r : Fin (j + 1), IndefiniteRowSideFullHecke.Inter.leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => hL _
  have hU : flagMinor g j S / IndefiniteRowSideFullHecke.Inter.leadMinor g j = U.det := by
    rw [div_eq_iff (hL j)]
    apply mul_right_cancel₀ hne
    linear_combination hid
  rw [hU, Matrix.det_apply]
  refine A.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (A.prod_mem fun r _ => hent _ _ (by have := r.2; simp only; omega)) _

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

abbrev PivPos (j : K → FlBlock Ψ N) : Type := Σ k : K, {b : Fin N // ((j k).2 : ℕ) < b}

def pivPosIncl (j : K → FlBlock Ψ N) (x : PivPos j) : PivotIdx Ψ N := ((j x.1).1, ⟨(j x.1).2, x.2⟩)

theorem pivPosIncl_injective {j : K → FlBlock Ψ N} (hj : Function.Injective j) :
    Function.Injective (pivPosIncl j) := by
  rintro ⟨k, b, hb⟩ ⟨k', b', hb'⟩ h
  simp only [pivPosIncl, Prod.mk.injEq, Sigma.mk.inj_iff] at h
  obtain ⟨h0, h1, h2⟩ := h
  have hk : k = k' := hj (Prod.ext h0 h1)
  subst hk
  simp only [heq_eq_eq, Subtype.mk.injEq] at h2
  subst h2
  rfl

theorem card_pivPos [Fintype K] (j : K → FlBlock Ψ N) : Fintype.card (PivPos j) = cellDim j := by
  rw [Fintype.card_sigma, cellDim]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun b : Fin N => ((j k).2 : ℕ) < b) =
      Finset.Ioi (Fin.castLE (Nat.sub_le N 1) (j k).2) := by
    ext b
    simp [Fin.lt_def]
  rw [this, Fin.card_Ioi]
  simp

theorem pivotRatio_algebraicIndependent_of_eq (Ψ : Type) (N : ℕ) (I : Algebra ℚ (ΩFl Ψ N))
    (hI : I = OreLocalization.instAlgebra) :
    @AlgebraicIndependent _ ℚ (ΩFl Ψ N) (pivotRatio ℚ Ψ N) _ _ I := by
  subst hI
  exact pivotRatio_algebraicIndependent ℚ Ψ N

theorem pivotRatio_rat_algebraicIndependent (Ψ : Type) (N : ℕ) :
    AlgebraicIndependent ℚ (pivotRatio ℚ Ψ N : PivotIdx Ψ N → ΩFl Ψ N) :=
  pivotRatio_algebraicIndependent_of_eq Ψ N _ (Subsingleton.elim _ _)

theorem isArithVar_pPart (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [Nonempty K]
    (j : K → FlBlock Ψ N) (hj : IsChain j) : IsArithVar (PPart j) (cellDim j + 1) := by
  classical
  let e : PivPos j ≃ Fin (cellDim j) := Fintype.equivFinOfCardEq (card_pivPos j)
  let t : Fin (cellDim j) → ΩFl Ψ N := fun i => pivotRatio ℚ Ψ N (pivPosIncl j (e.symm i))
  let c : ∀ k, PIdx j k := fun k => leadIdx Ψ N (j k)
  have hL : ∀ (τ : Ψ) (a : Fin (N - 1)), IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr ℚ Ψ N τ) a ≠ 0 := fun τ a =>
    GenLeadMinorNeZero.full ℚ Ψ N τ a
  have hc : ∀ k, yPart j ⟨k, c k⟩ ≠ 0 := fun k => by
    show yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ ≠ 0
    rw [yFl_lead]
    exact hL _ _
  have hind : AlgebraicIndependent ℚ t := by
    exact (pivotRatio_rat_algebraicIndependent Ψ N).comp _
      ((pivPosIncl_injective hj.inj).comp e.symm.injective)
  have hmem : ∀ i, t i ∈ IntermediateField.adjoin ℚ (coneRatios (yPart j) c) := by
    intro i
    refine IntermediateField.subset_adjoin ℚ _ ?_
    show pivotRatio ℚ Ψ N (pivPosIncl j (e.symm i)) ∈ coneRatios (yPart j) c
    obtain ⟨k, b, hb⟩ := e.symm i
    let S : PluckerBlocks N N (j k).2 := ⟨Finset.univ.image (pivotCols (j k).2 b), card_image_pivotCols _ b hb.le⟩
    refine ⟨⟨k, ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩
    have h1 := flagMinor_eq_yFl Ψ N (j k).1 (j k).2 S
    have h2 := pivotMinor_eq_flagMinor (genMatFr ℚ Ψ N (j k).1) (j k).2 b hb.le
    have h3 := yFl_lead Ψ N (j k)
    show yFl Ψ N ⟨j k, ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ /
      yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ = pivotMinor (genMatFr ℚ Ψ N (j k).1) (j k).2 b /
        IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr ℚ Ψ N (j k).1) (j k).2
    rw [h3]
    congr 1
    exact h1.symm.trans h2.symm
  have halg : ∀ r ∈ coneRatios (yPart j) c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r := by
    rintro _ ⟨⟨k, A⟩, rfl⟩
    have hT : ∀ (k' : K) (b : Fin N) (h : ((j k').2 : ℕ) < b),
        pivotMinor (genMatFr ℚ Ψ N (j k').1) (j k').2 b / IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr ℚ Ψ N (j k').1) (j k').2 ∈
          IntermediateField.adjoin ℚ (Set.range t) := fun k' b h =>
      IntermediateField.subset_adjoin ℚ _ ⟨e ⟨k', b, h⟩, by
        show pivotRatio ℚ Ψ N (pivPosIncl j (e.symm (e ⟨k', b, h⟩))) = _
        rw [e.symm_apply_apply]
        rfl⟩
    have hm : yPart j ⟨k, A⟩ / yPart j ⟨k, c k⟩ ∈ IntermediateField.adjoin ℚ (Set.range t) := by
      show yFl Ψ N ⟨j k, A⟩ / yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ ∈ _
      rw [yFl_lead, yFl_eq_flagMinor]
      refine flag_mem_of_le ℚ (genMatFr ℚ Ψ N (j k).1) _ (hL _) (j k).2 (fun a b ha hb => ?_) _
      obtain ⟨k', hk'⟩ := hj.down k ((j k).1, a) rfl ha
      have h := hT k' b (by rw [hk']; exact hb)
      rw [hk'] at h
      exact h
    exact isAlgebraic_algebraMap (⟨_, hm⟩ : IntermediateField.adjoin ℚ (Set.range t))
  exact CoordConeArithVar.full K (PIdx j) (ΩFl Ψ N) (yPart j) c (cellDim j) t ‹_› hc hind hmem halg

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end
