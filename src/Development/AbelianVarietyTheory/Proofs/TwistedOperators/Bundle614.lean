module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeColumnsOffFiniteSet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateTsumLeOfThetaLevelMultiple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignIndependent
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle044
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle608
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteHeisenbergTranslateSelfDualVacuumFockJets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle609
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.StairLine

variable {D : D7}

open GlobalTheory.SeeSaw

theorem incA_mul_mem_idV {𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} (x : D.host.E) {t : AE D} (ht : t ∈ idV 𝔟 v) :
    incA D x * t ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔟) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hy
    rw [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul]
    exact GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv
      (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ x) hb)
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy

theorem mem_idV_inv_mul {𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} {x : D.host.E} (hx : x ≠ 0) (s : AE D) :
    s ∈ idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟) v ↔ incA D x * s ∈ idV 𝔟 v := by
  constructor
  · intro h
    have := incA_mul_mem_idV x h
    rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hx,
      FractionalIdeal.spanSingleton_one, one_mul] at this
  · intro h
    have := incA_mul_mem_idV x⁻¹ h
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul] at this

theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : 2 * p.1 + 1 ≠ c) :
    (d.aᴴ * B.gram * d.a) ⟨c - 1 - p.1, by omega⟩ = Pi.single p 1 ∧
      (d.aᴴ * B.gram * frameMat B A d.ι) = 0 := by
  refine ⟨?_, ?_⟩
  · have e := d.gram
    change d.aᴴ * B.gram * d.a = _ at e
    rw [e]
    funext q
    simp only [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, Pi.single_apply, Fin.ext_iff]
    have := p.2; have := q.2
    by_cases hq : q.1 = p.1
    · rw [if_pos (by omega), if_neg (by omega), if_pos hq]
    · rw [if_neg (by omega), if_neg hq]
  · have e := d.perp
    change (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 at e
    have hg : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq (B.frame j) (B.frame i)
    have := congrArg Matrix.conjTranspose e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hg,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at this

theorem line_mem {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FI D) (v : GlobalTheory.FinPl.Pl D) (p : Fin c) (hp : 2 * p.1 + 1 ≠ c) (t : AE D) :
    (fun k => t * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ t ∈ idV (𝔟 p) v := by
  classical
  obtain ⟨hf1, hf2⟩ := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero d p hp
  generalize (⟨c - 1 - p.1, by omega⟩ : Fin c) = q at hf1
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin B.rank → D.host.E, φ = (d.aᴴ * B.gram) q := ⟨_, rfl⟩
  have hφa : ∀ u : Fin c → D.host.E, φ ⬝ᵥ (d.a *ᵥ u) = u p := by
    intro u
    rw [Matrix.dotProduct_mulVec, hφ]
    have : (d.aᴴ * B.gram) q ᵥ* d.a = (d.aᴴ * B.gram * d.a) q := rfl
    rw [this, hf1]
    simp [Pi.single_apply, dotProduct]
  have hφM : ∀ y, φ ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, hφ]
    have : (d.aᴴ * B.gram) q ᵥ* frameMat B A d.ι = (d.aᴴ * B.gram * frameMat B A d.ι) q := rfl
    rw [this, hf2]
    exact zero_dotProduct y
  have h3 : ∑ l, φ l * d.a l p = 1 := by
    have := congrFun hf1 p
    rw [Pi.single_eq_same, Matrix.mul_apply] at this
    rw [hφ]; exact this
  let Φ : (Fin B.rank → AE D) →+ AE D :=
    { toFun := fun z => ∑ l, incA D (φ l) * z l
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] }
  constructor
  · intro h
    have hle : latV B (d.lat Λ 𝔟) (· = v) ≤ (idV (𝔟 p) v).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, hαv, a', ha', x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at ha'
      subst ha'
      obtain ⟨y, -, u, hu, rfl⟩ := hx
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show ∑ l, incA D (φ l) * _ ∈ _
      simp only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_sum]
      have : ∑ l, φ l * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) l = u p := by
        have h1 := hφa u
        have h2 := hφM y
        rw [← h1, ← add_zero (φ ⬝ᵥ (d.a *ᵥ u)), ← h2, ← dotProduct_add, add_comm]
        rfl
      rw [this]
      exact GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv (hu p)
    have h2 : Φ (fun k => t * incA D (d.a k p)) ∈ idV (𝔟 p) v := hle h
    have e : Φ (fun k => t * incA D (d.a k p)) = t := by
      show ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t
      calc ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t * incA D (∑ l, φ l * d.a l p) := by

            rw [map_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_mul, mul_left_comm]
        _ = t := by rw [h3, map_one, mul_one]
    rwa [e] at h2
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hs
      refine AddSubgroup.subset_closure ⟨α, hα, hαv, 1, rfl, d.a *ᵥ Pi.single p b,
        ⟨0, Λ.zero_mem, Pi.single p b, fun r => ?_, by simp⟩, ?_⟩
      · by_cases hr : r = p
        · subst hr; simpa using hb
        · rw [Pi.single_eq_of_ne hr]; exact (𝔟 r).zero_mem
      · funext k
        rw [mul_comm, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    | zero =>
      convert (latV B (d.lat Λ 𝔟) (· = v)).zero_mem using 1
      funext k; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      funext k; simp [add_mul]
    | neg x _ hx =>
      convert neg_mem hx using 1
      funext k; simp [neg_mul]


open GlobalTheory.ChiGrid in
theorem colMul_dJ_mem_iff : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ), ∀ a ∈ idAt D (· = v), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔ a ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i.1) * (G.pl.stAbar sc ^ (i.1 + 1))⁻¹)) v := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h v i a ha
  obtain ⟨hc, he, -⟩ := hF.hJ ρ h
  have hx : ((-D.host.xi0) ^ (i.1 + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a = fun k => (incA D ((-D.host.xi0) ^ (i.1 + 1)) * a) *
      incA D ((G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) i)) := by
    funext k
    show a * incA D ((F.dJ ρ h).e k i) = _
    rw [he]
    show a * incA D ((-D.host.xi0) ^ (i.1 + 1) * _) = _
    rw [map_mul, ← mul_assoc, mul_comm a]
  have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat _ _ _
  have hi := i.2
  rw [e1, e2, line_mem _ _ _ v _ (by simp only [Fin.val_castLE]; omega), mem_idV_inv_mul hx]
  simp only [stairId, Fin.val_castLE, Nat.add_sub_cancel]

end GlobalTheory.StairLine
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselLevel_columns_carry_latticeLines_offExceptional : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, ColsAt (F.dB ρ h) (xZero (F.dJ ρ h)) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  first | exact @GlobalTheory.StairCols.colsAt_xZero | exact GlobalTheory.StairCols.colsAt_xZero | (intros; apply GlobalTheory.StairCols.colsAt_xZero <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

open scoped Topology

namespace GlobalTheory.BumpMixLevel

variable {D : D7}

theorem symplOH_ext_fin {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ)
    (ha : a.map (infPart D) = 0) :
    symplOH S T (d.extX T x) (d.extY T a) = pairA D.host.F 0 (symplOH S T (d.extX T x) (d.extY T a)).2 := by
  have hfin : (d.extY T a).map (infPart D) = 0 := by
    rw [HypDec.extY_apply, Matrix.map_mul, ha, Matrix.zero_mul]
  have h3 : GlobalTheory.FinTranslate.eInf D * symplOH S T (d.extX T x) (d.extY T a) = 0 := by
    rw [← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin hfin, GlobalTheory.FinTranslate.symplOH_zero_right]
  exact Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl

theorem exists_level_pair (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (K : Set (Mx D T.rank ρ)) (hK : IsCompact K) :
    ∃ U : AddSubgroup (Mx D T.rank ρ), IsOpen (U : Set (Mx D T.rank ρ)) ∧
      ∀ a ∈ U, a.map (infPart D) = 0 → ∀ k ∈ K, ψ (symplOH S T (d.extX T k) (d.extY T a)) = 1 := by
  have hX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have hs : Continuous fun p : Mx D T.rank ρ × Mx D T.rank ρ => (symplOH S T (d.extX T p.1) (d.extY T p.2)).2 :=
    continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hX.comp continuous_fst) (hY.comp continuous_snd))
  have hZ := GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1
  have hO := (isOpen_interior (s := {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1})).preimage hs
  have hsub : K ×ˢ ({0} : Set (Mx D T.rank ρ)) ⊆
      (fun p : Mx D T.rank ρ × Mx D T.rank ρ => (symplOH S T (d.extX T p.1) (d.extY T p.2)).2) ⁻¹'
        interior {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1} := by
    rintro ⟨k, a⟩ ⟨-, ha⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simp only [Set.mem_preimage, map_zero, GlobalTheory.FinTranslate.symplOH_zero_right, Prod.snd_zero]
    exact mem_interior_iff_mem_nhds.2 hZ
  obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hO hsub
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.MixSumBound.finite_points_in_nhds D T.rank ρ v (hv.mem_nhds (h0v rfl))
  refine ⟨U, hUo, fun a ha hfin k hk => ?_⟩
  have h1 := huv (Set.mk_mem_prod (hKu hk) (hU a ha hfin))
  have h2 : (symplOH S T (d.extX T k) (d.extY T a)).2 ∈ {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1} :=
    interior_subset h1
  rw [symplOH_ext_fin d k a hfin]
  exact h2

theorem poinX_heis_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (poinX ψ d T β) = poinX ψ d T β := by
  intro D ψ hψ S S₀ T ρ d h0 β hβ
  haveI : LocallyCompactSpace (Mx D T.rank ρ) := (GlobalTheory.MixModel.lattice_Mx D T.rank ρ).2.1
  obtain ⟨Uβ, hUβo, hUβ⟩ := hβ.level
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : Mx D T.rank ρ)
  obtain ⟨UC, hUCo, hUC⟩ := GlobalTheory.MixSumBound.finite_points_in_nhds D T.rank ρ C hC0
  obtain ⟨UY, hUYo, hUY⟩ := GlobalTheory.BumpMixLevel.exists_level_pair ψ hψ d (tsupport β ∪ C) (hβ.supp.isCompact.union hC)
  let pX : WO S T →+ Mx D T.rank ρ :=
    { toFun := fun u => u ⬝ d.jX, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
  let pY : WO S T →+ Mx D T.rank ρ :=
    { toFun := fun u => u ⬝ d.jY, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
  have hpX : Continuous pX := continuous_id.matrix_mul continuous_const
  have hpY : Continuous pY := continuous_id.matrix_mul continuous_const
  refine ⟨(Uβ ⊓ UC).comap pX ⊓ UY.comap pY, ((hUβo.inter hUCo).preimage hpX).inter (hUYo.preimage hpY), ?_⟩
  intro u hu hfin
  have hsub0 : ∀ z : WO S₀ T, z = 0 := fun z => Matrix.ext fun i j => absurd j.isLt (by omega)
  have hw : ∀ w : WO S T, w = d.extX T (w ⬝ d.jX) + d.extY T (w ⬝ d.jY) := fun w => by
    conv_lhs => rw [eq_coords d w]
    rw [hsub0 (w ⬝ d.j0), map_zero, add_zero]
  have hx₀ : u ⬝ d.jX ∈ Uβ ∧ u ⬝ d.jX ∈ UC := hu.1
  have ha₀ : u ⬝ d.jY ∈ UY := hu.2
  have hfx : (u ⬝ d.jX).map (infPart D) = 0 := by rw [Matrix.map_mul, hfin, Matrix.zero_mul]
  have hfa : (u ⬝ d.jY).map (infPart D) = 0 := by rw [Matrix.map_mul, hfin, Matrix.zero_mul]
  have h00 : ψ (symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (u ⬝ d.jY))) = 1 :=
    hUY _ ha₀ hfa _ (Or.inr (hUC _ hx₀.2 hfx))
  funext w
  have hs : symplOH S T w u = symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) -
      symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY)) := by
    conv_lhs => rw [hw w, hw u]
    simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, d.symplOH_extX_extX,
      d.symplOH_extY_extY, zero_add, add_zero]
    rw [GlobalTheory.MixModel.symplOH_skew S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY))]
    abel
  simp only [heisO, poinX]
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  rw [Matrix.add_mul, Matrix.add_mul]
  have hb : β (w ⬝ d.jX + u ⬝ d.jX + rat γ) = β (w ⬝ d.jX + rat γ) := by
    rw [add_right_comm]; exact hUβ _ hx₀.1 hfx _
  rw [hb]
  by_cases hk : β (w ⬝ d.jX + rat γ) = 0
  · rw [hk, mul_zero, mul_zero, mul_zero]
  have hkK : ψ (symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY))) = 1 :=
    hUY _ ha₀ hfa _ (Or.inl (subset_tsupport β hk))
  rw [← mul_assoc, ← d.symplOH_extX_extY T, ← d.symplOH_extX_extY T, ← AddChar.map_add_eq_mul, hs]
  have he : symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) -
      symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY)) +
      symplOH S T (d.extX T (w ⬝ d.jX + u ⬝ d.jX + 2 • rat γ)) (d.extY T (w ⬝ d.jY + u ⬝ d.jY)) =
      symplOH S T (d.extX T (w ⬝ d.jX + 2 • rat γ)) (d.extY T (w ⬝ d.jY)) +
        (symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY)) +
          symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY))) +
        symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) := by
    simp only [map_add (f := _), two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]
    abel
  rw [he]
  simp only [AddChar.map_add_eq_mul, hkK, h00, mul_one]

end GlobalTheory.BumpMixLevel
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLevel.PairTriv

variable {D : D7}

theorem partAt_eq_smul {S T : HSp D} (a : AE D) (w : WO S T) : GlobalTheory.LiftLevel.partAt a w = a • w := by
  ext i j
  rfl

theorem hatA_tens_mono {S T : HSp D} (Λ : Lt D.host.E S.rank) {L L' : Lt D.host.E T.rank} (h : L ≤ L') :
    hatA S T (tens Λ L) ≤ hatA S T (tens Λ L') := by
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, y, hy, rfl⟩
  refine ⟨α, hα, y, ?_, rfl⟩
  refine (AddSubgroup.closure_mono ?_) hy
  rintro z ⟨v, hv, u, hu, rfl⟩
  exact ⟨v, hv, u, h hu, rfl⟩

theorem actO_back {S T : HSp D} (k : GA D S) (x : WO S T) : actO S T k 1 (actO S T k⁻¹ 1 x) = x := by
  have := GlobalTheory.WeilVacMove.actO_inv_actO (S := S) (T := T) k⁻¹ (1 : GA D T) x
  simpa using this

theorem pair_trivial : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), ∀ t ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1 := by
  intro D S T C hn ΛT hΛT hAA βS βT hβS hβT Pg Q ξ hPg hodd e he a k₀ Λ' hab hmov hgen hmv Lv hLv u hu t ht
  have hsd : SelfD C.X (Lv.sh C.X.Λ) :=
    GlobalTheory.SW.Lev.selfD_idq Lv.ne_bot Lv.proper Lv.cop (GlobalTheory.SW.Lev.selfD_of_sympl C.sympl)
  have hV := GlobalTheory.SW.Base.stdL_mem_Vset (E := D.host.E) S.rank 1

  have hw : actO S T k₀⁻¹ 1 u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) :=
    (GlobalTheory.TensLatMove.mem_hatA_iff S T C.m.gS k₀⁻¹ 1 Λ' (stdL D.host.E S.rank) (Lv.sh C.X.Λ) (Lv.sh C.X.Λ) hmv
      (GlobalTheory.OneMapRef.Term.isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩

  obtain ⟨ht1, ht2, ht3⟩ := ht
  have hh0 : IsHalf (cA D e) (actO S T k₀⁻¹ 1 t) := GlobalTheory.WeilVacMove.isHalf_actO _ _ _ ht1
  have hfr := hmov.2.2 _ hh0
  rw [actO_back] at hfr
  have ht0 : actO S T k₀⁻¹ 1 t ∈ hatA S T (tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ)) :=
    ((hgen _ hh0).2).1 ⟨hfr ▸ ht2, fun PP hPP => hfr ▸ ht3 PP hPP⟩
  rw [← hLv] at ht0
  have ht0' := hatA_tens_mono (stdL D.host.E S.rank) (GlobalTheory.SW.Lev.smul_le_idq Lv.𝔪 (conjI Lv.𝔪) C.X.Λ) ht0
  have hF := GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C
  set t₀ := actO S T k₀⁻¹ 1 t with ht₀
  set w := actO S T k₀⁻¹ 1 u with hw₀
  have et : t = actO S T k₀ 1 t₀ := (actO_back k₀ t).symm
  have eu : GlobalTheory.LiftLevel.partAt e u = actO S T k₀ 1 (e • w) := by
    rw [partAt_eq_smul, GlobalTheory.OneMapRef.Term.actO_smul, actO_back]
  have hhalf : cA D e • t₀ = t₀ := by
    ext i j
    exact hh0 i j
  have key : symplO S T t (GlobalTheory.LiftLevel.partAt e u) = symplO S T t₀ w := by
    rw [et, eu, hF.2.2.2.2.2.2.1, (hF.2.2.2.2.2.1 t₀ (e • w) 0).2, GlobalTheory.SplitScalar.symplO_smul, hhalf,
      ← (hF.2.2.2.2.2.1 t₀ w 0).2]
  rw [key]
  exact GlobalTheory.OneMapRef.Term.char_hatA C hV hsd t₀ ht0' w hw

end GlobalTheory.LiftLevel.PairTriv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.exists_algebraicDatum_thetaTransform_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ f : WO S X → ℂ, IsFinF ψ θ ε A B f → ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD f := by
  first | exact @GlobalTheory.VacDatum.vacDatum_exists | exact GlobalTheory.VacDatum.vacDatum_exists | (intros; apply GlobalTheory.VacDatum.vacDatum_exists <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


theorem _root_.GlobalTheory.T.finiteHeisenbergTranslate_selfDualVacuum_fockJets : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E))
    (κ : ℂ) (F : WO (G.pS p) (G.pT p) → ℂ), SD D Ls → SD D Lt →
    Differentiable ℂ (Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p)) →
    IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (inV (frS S.N p) Ls) (inV (frT S.N p) Lt) F →
    (∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ, fockIn W S.N.frC p F (MvPolynomial.monomial k 1) 0 =
      S.Z.c0 p * opp p ((k.prod fun v e => period S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z =>
        κ * Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p) z)) →
    ∀ (n : ℕ), 0 < n → ∀ w : WO (G.pS p) (G.pT p), n • w ∈ latO _ _ (inV (frS S.N p) Ls) (inV (frT S.N p) Lt) (fun _ => True) →
    ∃ (ζ : Qbar) (s : VC D (G.pS p).rank (G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ n • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt ∧
    ∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ, fockIn W S.N.frC p (heisO W.ψ _ _ w F) (MvPolynomial.monomial k 1) 0 =
      S.Z.c0 p * opp p ((k.prod fun v e => period S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z =>
        κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK S.Z.δ) s
          (Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p)) z)) := by
  first | exact @GlobalTheory.HeisTrans.main | exact GlobalTheory.HeisTrans.main | (intros; apply GlobalTheory.HeisTrans.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise


theorem _root_.GlobalTheory.T.totalTensorThetaLift_eq_of_schwartz_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ₁ τ₂ : TotT G p) (φ₁ φ₂ : PureT G p → PureT G p), (∀ d ∈ τ₁.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₁ d) d) → (∀ d ∈ τ₂.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₂ d) d) → (∀ x : GlobalTheory.FlipRun.ArgT G p, GlobalTheory.FlipRun.HalfAll e p x → (τ₁.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₁ d) x) = τ₂.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₂ d) x) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₁) F = liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₂) F := by
  first | exact @GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd | exact GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd | (intros; apply GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd <;> assumption)
end

end

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix


theorem _root_.GlobalTheory.T.poincareSumHalfWitt_heisenberg_level_of_zero_core : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (poinX ψ d T β) = poinX ψ d T β := by
  first | exact @GlobalTheory.BumpMixLevel.poinX_heis_level | exact GlobalTheory.BumpMixLevel.poinX_heis_level | (intros; apply GlobalTheory.BumpMixLevel.poinX_heis_level <;> assumption)

end
end
end
