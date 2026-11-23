module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem hasSignature_diag_signs (p q : ℕ) : Formalism.UG.HasSignature
    (Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ)) p q := by
  have hne : ∀ (i : Fin p) (j : Fin q), Fin.castAdd q i ≠ Fin.natAdd p j := fun i j h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  refine ⟨(finSumFinEquiv (m := p) (n := q)).symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply,
      Matrix.one_apply, (Fin.castAdd_injective p q).eq_iff]
    simp [Examples₂.sgn, Nat.not_le.2 i.isLt]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne i j)]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne j i).symm]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply,
      Matrix.neg_apply, Matrix.one_apply, (Fin.natAdd_injective q p).eq_iff]
    split_ifs <;> simp [Examples₂.sgn]

theorem exists_isV : ∀ (D : D7) (ν q : ℕ), q ≤ ν → ∃ X : LSp D, X.IsV ν q := by
  intro D ν q h
  obtain ⟨p, rfl⟩ : ∃ p, ν = p + q := ⟨ν - q, by omega⟩
  refine ⟨⟨diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q, GlobalTheory.PlaceModel.latFrame _⟩, rfl, fun τ => ?_,
    fun τ => ?_, GlobalTheory.PlaceModel.isSelfDualC_latFrame _⟩
  · have hg : (diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ =
        Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ) := by
      rw [diagSp_gram]
      ext i j
      change τ (if i = j then _ else 0) = if i = j then _ else 0
      by_cases hij : i = j <;> simp [hij, Examples₂.map_sgn]
    change Formalism.UG.HasSignature ((diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ) p q
    rw [hg]
    exact hasSignature_diag_signs p q
  · rw [Nat.add_sub_cancel]
    rfl

end GlobalTheory.ChiGrid
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigPull

theorem pull_top_injective {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Sp k) (g : Y ⟶ X) (hg : Dense (Set.range g)) (B : LB X) (hB : B.IsLB) :
    Function.Injective (H0.pull (p := p) (B := B) (O := ⊤) g (W := ⊤) le_top) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  obtain ⟨σ, rfl⟩ := (H0.bijective_ofSec_top (p := p) (B := B)).2 f
  by_contra hne
  have hσ : σ ≠ 0 := fun h => hne (by rw [h, map_zero])
  have hgen := (sec_ne_zero_iff σ).1 hσ
  obtain ⟨y, hy⟩ : ∃ y, g y ∈ nonzeroLocus σ := by
    obtain ⟨_, hy, ⟨y, rfl⟩⟩ := hg.inter_open_nonempty _ (nonzeroLocus σ).isOpen ⟨_, hgen⟩
    exact ⟨y, hy⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hB.cover.ge (trivial : g y ∈ (⊤ : X.Opens)))
  have hj : y ∈ (B.pull g).U (fun _ => i) := mem_pull.2 hi
  have e := H0.germ_pull (p := p) (B := B) (O := ⊤) g (W := ⊤) le_top (fun _ => i) y trivial hj
    (H0.ofSec p ⊤ σ)
  rw [hf, map_zero] at e
  have hu : IsUnit ((g.stalkMap y).hom (H0.germ (p := p) (O := ⊤) i (g y) (show g y ∈ (⊤ : X.Opens) from trivial) hi (H0.ofSec p ⊤ σ))) :=
    IsUnit.map _ ((H0.germ_ofSec (p := p) (O := ⊤) _ _ (show g y ∈ (⊤ : X.Opens) from trivial) hi σ).symm ▸ (isUnit_ger_iff σ hi).2 hy)
  rw [← e] at hu
  exact not_isUnit_zero hu

theorem finite_H0_top {E : Type} [Field E] {Y : Scheme.{0}} (p : Y ⟶ Sp E) (B : LB Y) :
    letI := algebraΓOfHom p
    Module.Finite E (coh (twist (structureModule Y) B) 0) → Module.Finite E (H0 p B ⊤) := by
  letI := algebraΓOfHom p
  intro h
  letI : Module E B.Sec := Module.compHom _ (algebraMap E Γ(Y, ⊤))
  haveI : IsScalarTower E Γ(Y, ⊤) B.Sec := IsScalarTower.of_compHom _ _ _
  have e (c : E) : algebraMap E Γ(Y, ⊤) c = algX p ⊤ c := by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  exact Module.Finite.equiv (((cohZeroTwistEquiv B).restrictScalars E).trans
    (LinearEquiv.ofBijective { H0.ofSec p ⊤ with
      map_smul' := fun c σ => (e c ▸ H0.ofSec_smul c σ :) } H0.bijective_ofSec_top))

theorem isBig_pull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (g : Y ⟶ X), IsProjOver (g ≫ p) → topologicalKrullDim Y = topologicalKrullDim X →
    Dense (Set.range g) → ∀ N : LB X, (letI := algebraΓOfHom p; IsBig k N) →
    (letI := algebraΓOfHom (g ≫ p); IsBig k (N.pull g)) := by
  intro k _ X Y _ p g hp hd hg N hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (g ≫ p)
  have hL : ∀ m, (lbPow (N.pull g) m).IsLB := fun m => isLB_lbPow (LB.isLB_pull hN.isLB g) m
  have hfin : ∀ m, Module.Finite k (coh (twist (structureModule Y) (lbPow (N.pull g) m)) 0) :=
    fun m => finite_coh_zero_twist_of_isProjOver (fun _ => rfl) hp (hL m)
  have hle : ∀ m, lbH0 k (lbPow N m) ≤ lbH0 k (lbPow (N.pull g) m) := by
    intro m
    have hB := isLB_lbPow hN.isLB m
    have hB' := LB.isLB_pull hB g
    have ec := (cls_eq_iff (hL m) hB').2 (lbIso_lbPow_pull hN.isLB g m)
    rw [lineBundleGlobalSectionsDim_congr_picardClass (hL m) hB' ec, ← H0.finrank_top p, ← H0.finrank_top (g ≫ p)]
    haveI := finite_H0_top (g ≫ p) ((lbPow N m).pull g)
      (finite_coh_zero_twist_congr hB' (hL m) ec.symm (hfin m))
    exact LinearMap.finrank_le_finrank_of_injective (pull_top_injective p g hg _ hB)
  obtain ⟨D, hD, c, hc, hm⟩ := hN.growth
  exact ⟨LB.isLB_pull hN.isLB g, hfin, D, hd.trans hD, c, hc,
    hm.mono fun m h => h.trans (by exact_mod_cast hle m)⟩

end GlobalTheory.BigPull
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.LB (toMod)
open Limits (pullback)

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}


variable (p) in
def ratFibre : Scheme.{0} := pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))

namespace ratFibre

variable (p)

def fst : ratFibre p ⟶ X := pullback.fst _ _

def snd : ratFibre p ⟶ Sp ℚ := pullback.snd _ _

instance algebra : Algebra ℚ Γ(ratFibre p, ⊤) := algebraΓOfHom (snd p)

theorem isPullback : IsPullback (fst p) (snd p) (p ≫ spMap (Int.castRingHom k))
    (spMap (Int.castRingHom ℚ)) := IsPullback.of_hasPullback _ _

theorem strHom_eq : strHom ℚ (ratFibre p) = snd p := GlobalTheory.strHom_eq fun _ => rfl

end ratFibre


variable (p) in
def ratDeg (L : LB X) : ℤ := degOfRank ℚ (toMod (L.pull (ratFibre.fst p))) 1

abbrev CxPts.pt (y : CxPts p σ) : X := y.1 (IsLocalRing.closedPoint ℂ)

def germOrd {W : X.Opens} (f : Γ(X, W)) {x : X} (hx : x ∈ W) : ℕ :=
  (Ring.ord (X.presheaf.stalk x) (X.presheaf.germ W x hx f)).toNat

theorem exists_mem_chart {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i :=
  Opens.mem_iSup.1 (hL.cover.ge (Opens.mem_top x))

def secOrd {L : LB X} (hL : L.IsLB) (s : L.Sec) (x : X) : ℕ :=
  germOrd (s.f (exists_mem_chart hL x).choose) (exists_mem_chart hL x).choose_spec

end GlobalTheory
end
end

section

open GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem vdm_cast_eq_range {ι : Type} [Fintype ι] {N : ℕ} (la : ι → Fin N → ℤ) (v : ι → ℕ → ℝ)
    (hv : ∀ τ (i : Fin N), v τ i = la τ i) :
    ((GlobalTheory.CompHt.vdm la : ℤ) : ℝ) = ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l) := by
  rw [show ((GlobalTheory.CompHt.vdm la : ℤ) : ℝ) = _ from GlobalTheory.CompHt.map_vdm (Int.castRingHom ℝ) la]
  unfold GlobalTheory.CompHt.vdm
  refine Finset.prod_congr rfl fun τ _ => ?_
  have lhs : ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ((Int.castRingHom ℝ) (la τ i) - (Int.castRingHom ℝ) (la τ l))
      = ∏ i ∈ Finset.range N, ∏ l ∈ Finset.range N, (if i < l then v τ i - v τ l else 1) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ l ∈ Finset.range N, (if i < l then v τ i - v τ l else 1)) N]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun l => if (i : ℕ) < l then v τ i - v τ l else 1) N, ← Finset.prod_filter]
    refine Finset.prod_congr (by ext l; simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]) fun l _ => ?_
    rw [hv, hv]
    rfl
  have rhs : ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l)
      = ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range N, (if i < l then v τ i - v τ l else 1) := by
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [← Finset.prod_filter]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    have := Finset.mem_range.1 hl
    ext i
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · intro h; exact ⟨by omega, h⟩
    · intro h; exact h.2
  rw [lhs, rhs, Finset.prod_comm]

theorem rho_div_le : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : GlobalTheory.MeanTop.Wts ι N) (H : ℝ), W.Hyp → W.IsDiv →
    (∀ τ, StrictAnti (W.u1 τ)) → (∀ τ, 0 < W.w τ) → 4 * ((W.c0 : ℝ) + 2 * N + W.T + W.Dd + 1) ≤ H →
    24 * (N : ℝ) * W.T ≤ H →
    (∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) = W.p → H ≤ ((W.u τ a - W.u τ b : ℤ) : ℝ)) →
    GlobalTheory.CompHt.rhoOf W.u' W.u1 ≤
      3 * N * ∑ τ, ((N : ℝ) * N * (2 * ((W.T : ℝ) + W.Dd + 1)) / H + 2 * N * N * W.T / W.w τ) := by
  intro ι _ N W H hW hd hanti hw hH1 hH2 hbar
  have hk := hW.kc_pos
  have hkp := hW.kc_lt
  have hpN := hW.p_lt
  have hc0 : (0 : ℝ) ≤ W.c0 := by exact_mod_cast hW.weightConst_nonneg
  have hT1 : 4 * (W.Dd : ℝ) + 4 ≤ W.T := by exact_mod_cast hW.h1
  have hD : (0 : ℝ) ≤ W.Dd := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) < W.T := by linarith
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (W.T : ℝ) + W.Dd + 1 := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : 0 < M := by linarith
  have hMT : M ≤ 5 / 4 * W.T := by linarith
  have hNT : 0 < (N : ℝ) * W.T := mul_pos hN0 hT0
  have hHpos : 0 < H := by linarith
  obtain ⟨g1, hg1⟩ : ∃ g1 : ℝ, g1 = H / (2 * M) := ⟨_, rfl⟩
  have hg : 3 * (N : ℝ) < g1 := by
    rw [hg1, lt_div_iff₀ (by positivity)]
    have : (N : ℝ) * M ≤ N * (5 / 4 * W.T) := mul_le_mul_of_nonneg_left hMT hN0.le
    nlinarith
  obtain ⟨U, hU⟩ : ∃ U : ι → ℕ → ℝ, ∀ τ (i : Fin N), U τ i = W.u1 τ i :=
    ⟨fun τ n => if h : n < N then (W.u1 τ ⟨n, h⟩ : ℝ) else 0, fun τ i => by simp [i.2]⟩
  have hU' : ∀ τ (i : Fin N), (if (i : ℕ) < W.p then U τ i else U τ i + 3 * N) = ((W.u' τ i : ℤ) : ℝ) := by
    intro τ i
    rw [hU]
    unfold Wts.u'
    split_ifs <;> push_cast <;> ring

  obtain ⟨a, ha⟩ : ∃ a : Fin N, (a : ℕ) = W.p - 1 := ⟨⟨W.p - 1, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin N, (b : ℕ) = W.p := ⟨⟨W.p, hpN⟩, rfl⟩
  have hab : (b : ℕ) = a + 1 := by omega
  have hbarGap : ∀ τ, g1 ≤ (W.u1 τ a : ℝ) - W.u1 τ b := by
    intro τ
    have e := (hd τ).2 a b hab
    rw [if_pos hb] at e
    have hG := hbar τ a b hab hb
    have hMi : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
    have h3 := Int.emod_lt_of_pos (W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2))) hMi
    have h4 := Int.mul_ediv_add_emod (W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2))) ((W.T : ℤ) + W.Dd + 1)
    rw [← e] at h4
    have h5 : W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2)) - ((W.T : ℤ) + W.Dd + 1) <
        ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) := by linarith
    have h6 : ((W.u τ a - W.u τ b : ℤ) : ℝ) - W.c0 - 2 * N + 2 - M < M * ((W.u1 τ a : ℝ) - W.u1 τ b) := by
      rw [hM]
      have := (Int.cast_lt (R := ℝ)).2 h5
      push_cast at this ⊢
      linarith
    rw [hg1, div_le_iff₀ (by positivity)]
    have h7 : H ≤ 2 * (M * ((W.u1 τ a : ℝ) - W.u1 τ b)) := by linarith
    linarith
  have hdec : ∀ τ i l, i < l → l < N → U τ l < U τ i := by
    intro τ i l h1 h2
    have := hU τ ⟨i, by omega⟩
    have := hU τ ⟨l, h2⟩
    simp only at *
    have h := hanti τ (show (⟨i, by omega⟩ : Fin N) < ⟨l, h2⟩ from h1)
    have h' : (W.u1 τ ⟨l, h2⟩ : ℝ) < W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast h
    linarith
  have hgap : ∀ τ i l, i < W.p → W.p ≤ l → l < N → g1 ≤ U τ i - U τ l := by
    intro τ i l h1 h2 h3
    have e1 := hU τ ⟨i, by omega⟩
    have e2 := hU τ ⟨l, h3⟩
    simp only at e1 e2
    rw [e1, e2]
    have m1 : W.u1 τ a ≤ W.u1 τ ⟨i, by omega⟩ := (hanti τ).antitone (show (⟨i, by omega⟩ : Fin N) ≤ a by
      rw [Fin.le_def]; simp only; omega)
    have m2 : W.u1 τ ⟨l, h3⟩ ≤ W.u1 τ b := (hanti τ).antitone (show b ≤ (⟨l, h3⟩ : Fin N) by
      rw [Fin.le_def]; simp only; omega)
    have m1' : (W.u1 τ a : ℝ) ≤ W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast m1
    have m2' : (W.u1 τ ⟨l, h3⟩ : ℝ) ≤ W.u1 τ b := by exact_mod_cast m2
    linarith [hbarGap τ]
  have hcl : ∀ τ i l, i < W.kc → W.p ≤ l → l < N → W.w τ / (2 * W.T) ≤ U τ i - U τ l := by
    intro τ i l h1 h2 h3
    have e1 := hU τ ⟨i, by omega⟩
    have e2 := hU τ ⟨l, h3⟩
    simp only at e1 e2
    rw [e1, e2]
    have c1 := (GlobalTheory.MeanTop.divided_entries ι N W hW hd τ ⟨i, by omega⟩).2.2 h1
    have c1' : (0 : ℝ) ≤ W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast c1
    have c2 := ((GlobalTheory.MeanTop.nodes_far_and_spread ι N W hW hd τ).1 ⟨l, h3⟩ (by simp only; omega)).1
    linarith
  have L := GlobalTheory.degree_ratio_shift_bound ι N W.p W.kc U (fun _ => g1) W.w (W.T : ℝ) hkp.le hpN.le hT0 hw
    (fun _ => hg) hdec hgap hcl
  dsimp only at L
  obtain ⟨-, -, L3⟩ := L
  unfold GlobalTheory.CompHt.rhoOf
  rw [vdm_cast_eq_range W.u' (fun τ i => if i < W.p then U τ i else U τ i + 3 * N) (fun τ i => hU' τ i),
    vdm_cast_eq_range W.u1 U hU]
  refine L3.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity))
  have hwt := hw τ
  have e : ((W.p - W.kc : ℕ) : ℝ) * ((N - W.p : ℕ) : ℝ) / g1 = ((W.p - W.kc : ℕ) : ℝ) * ((N - W.p : ℕ) : ℝ) * (2 * M) / H := by
    rw [hg1]; field_simp
  rw [e]
  have i1 : ((W.p - W.kc : ℕ) : ℝ) ≤ N := by exact_mod_cast (show W.p - W.kc ≤ N by omega)
  have i2 : ((N - W.p : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N - W.p ≤ N by omega)
  have i3 : (W.kc : ℝ) ≤ N := by exact_mod_cast (show W.kc ≤ N by omega)
  gcongr

end GlobalTheory.MeanTop
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatBound

variable {E : Type} [Field E] [NumberField E]

theorem coord_mul (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z * z') w = z w * z' w := rfl

theorem coord_add (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z + z') w = z w + z' w := rfl

theorem integral_of_int (b : 𝓞 E) (w : HeightOneSpectrum (𝓞 E)) :
    (algebraMap E (Af E) (algebraMap (𝓞 E) E b)) w ∈ w.adicCompletionIntegers E :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
    ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le (w.valuation_le_one b))

theorem integral_natCast (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    ((n : Af E)) w ∈ w.adicCompletionIntegers E := by
  have := integral_of_int (E := E) (n : 𝓞 E) w
  simpa using this

theorem exists_nat_mul_integral (z : Af E) :
    ∃ d : ℕ, 0 < d ∧ ∀ w : HeightOneSpectrum (𝓞 E), ((d : Af E) * z) w ∈ w.adicCompletionIntegers E := by
  obtain ⟨x, a, ha, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E 1 one_pos).1 z
  obtain ⟨m, hm0, hm⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x))
  have hint : IsIntegral ℤ ((m.natAbs : E) * x) := by
    rcases Int.natAbs_eq m with h1 | h1
    · have : ((m.natAbs : E) * x) = m • x := by
        rw [zsmul_eq_mul, ← Int.cast_natCast, ← h1]
      rw [this]; exact hm
    · have h1' : (m.natAbs : ℤ) = -m := by omega
      have : ((m.natAbs : E) * x) = -(m • x) := by
        rw [zsmul_eq_mul, ← Int.cast_natCast, h1', Int.cast_neg, neg_mul]
      rw [this]; exact hm.neg
  refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, fun w => ?_⟩
  have e : (m.natAbs : Af E) * z =
      algebraMap E (Af E) (algebraMap (𝓞 E) E ⟨_, hint⟩) + (m.natAbs : Af E) * a := by
    rw [h, one_smul, mul_add]
    congr 1
    show _ = algebraMap E (Af E) ((m.natAbs : E) * x)
    rw [map_mul, map_natCast]
  rw [e, coord_add, coord_mul]
  exact add_mem (integral_of_int _ w) (mul_mem (integral_natCast _ w) (ha w))

theorem integral_of_mem_hatO [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : z ∈ hatO c)
    (w : HeightOneSpectrum (𝓞 E)) : z w ∈ w.adicCompletionIntegers E := by
  obtain ⟨a, -, ha, hza⟩ := (GlobalTheory.CMVal.HatPlace.mem_hatO_iff E c hc z).1 hz
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : Valued.v (z w - a w) ≤ 1 :=
    (hza w).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have h2 : z w = (z w - a w) + a w := by ring
  rw [h2]
  exact Valuation.map_add_le _ h1 (ha w)

theorem lattice_between : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ y : (Af E)ˣ,
    ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ lattice c y) ∧
      ∀ x ∈ lattice c y, IsIntegral ℤ ((N : E) * x) := by
  intro E _ _ _ c hc y
  obtain ⟨d₁, hd₁, h₁⟩ := exists_nat_mul_integral (y : Af E)
  obtain ⟨d₂, hd₂, h₂⟩ := exists_nat_mul_integral (↑y⁻¹ : Af E)
  have hN₁ : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  refine ⟨Ideal.absNorm c * d₁ * d₂, by positivity, fun x => ?_, fun x hx => ?_⟩
  · rw [mem_lattice]
    have hY : ∀ w : HeightOneSpectrum (𝓞 E),
        (algebraMap E (Af E) (algebraMap (𝓞 E) E x) * (d₁ : Af E) * ((d₂ : Af E) * (↑y⁻¹ : Af E))) w ∈
          w.adicCompletionIntegers E := fun w => by
      rw [coord_mul, coord_mul]
      exact mul_mem (mul_mem (integral_of_int x w) (integral_natCast d₁ w)) (h₂ w)
    have key := GlobalTheory.CMVal.PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hY
    convert key using 1
    rw [map_natCast, map_natCast, map_mul, map_natCast]
    push_cast
    ring
  · rw [mem_lattice] at hx
    have hz := integral_of_mem_hatO hc hx
    have hint : ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E ((d₁ : E) * x) ≤ 1 := fun w => by
      have e : algebraMap E (Af E) ((d₁ : E) * x) =
          (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * ((d₁ : Af E) * (y : Af E)) := by
        rw [map_mul, map_natCast]
        have : (↑y⁻¹ : Af E) * (y : Af E) = 1 := Units.inv_mul y
        linear_combination (-(d₁ : Af E) * algebraMap E (Af E) x) * this
      have h3 : (algebraMap E (Af E) ((d₁ : E) * x)) w ∈ w.adicCompletionIntegers E := by
        rw [e, coord_mul]; exact mul_mem (hz w) (h₁ w)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h3
      exact h3
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ hint
    have e2 : ((Ideal.absNorm c * d₁ * d₂ : ℕ) : E) * x =
        algebraMap (𝓞 E) E (((Ideal.absNorm c * d₂ : ℕ) : 𝓞 E) * b) := by
      rw [map_mul, hb, map_natCast]; push_cast; ring
    rw [e2]
    exact RingOfIntegers.isIntegral_coe _

end GlobalTheory.CMVal.LatBound
end
end
