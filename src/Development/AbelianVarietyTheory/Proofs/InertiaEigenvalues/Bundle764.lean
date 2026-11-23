module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle746
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle750
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle741
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle542
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle130
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle753
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCusp

open GlobalTheory.MixModel

variable {D : D7}

theorem mem_span_cols {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (v : Fin n → D.host.E) :
    v ∈ Submodule.span D.host.E (Set.range I.transpose) ↔ ∃ a, I *ᵥ a = v := by
  change v ∈ Submodule.span D.host.E (Set.range I.col) ↔ _
  rw [← Matrix.range_mulVecLin]; rfl

theorem exists_mul_eq_mul {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (M : Matrix (Fin n) (Fin n) D.host.E)
    (h : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      M *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose)) :
    ∃ A : Matrix (Fin s) (Fin s) D.host.E, M * I = I * A := by
  have h1 : ∀ j, ∃ b, I *ᵥ b = M *ᵥ I.transpose j := fun j =>
    (mem_span_cols I _).1 (h _ (Submodule.subset_span ⟨j, rfl⟩))
  choose f hf using h1
  refine ⟨Matrix.of fun i j => f j i, ?_⟩
  refine Matrix.ext fun k j => ?_
  have := congrFun (hf j) k
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at this
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simpa using this.symm

theorem frame_gram_mul {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (J c c' : Matrix (Fin n) (Fin n) D.host.E)
    (hc : c * c' = 1) (hu : cᴴ * J * c = J) : Iᴴ * J * c = (c' * I)ᴴ * J := by
  have h1 : (c * c')ᴴ = 1 := by rw [hc, Matrix.conjTranspose_one]
  calc Iᴴ * J * c = Iᴴ * (c * c')ᴴ * J * c := by rw [h1, Matrix.mul_one]
    _ = Iᴴ * c'ᴴ * (cᴴ * J * c) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (c' * I)ᴴ * J := by rw [hu, Matrix.conjTranspose_mul]

theorem mul_mul_mul_eq_zero {R : Type} [CommRing R] {n s : ℕ} (C C' m : Matrix (Fin n) (Fin n) R)
    (I : Matrix (Fin n) (Fin s) R) (A' : Matrix (Fin s) (Fin s) R) (h : C' * I = I * A') (h0 : m * I = 0) :
    C * m * C' * I = 0 := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.mul_assoc C, h0, Matrix.mul_zero, Matrix.zero_mul]

theorem mul_mul_mul_eq_zero' {R : Type} [CommRing R] {n s : ℕ} (C C' m : Matrix (Fin n) (Fin n) R)
    (K : Matrix (Fin s) (Fin n) R) (A' : Matrix (Fin s) (Fin s) R) (h : K * C = A' * K) (h0 : K * m = 0) :
    K * (C * m * C') = 0 := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_assoc A', h0, Matrix.mul_zero, Matrix.zero_mul]



theorem conj_mem_NI : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ γ : GQ W, GlobalTheory.RallisCusp.lagAct W γ Y = Y → ∀ n ∈ NI W I, (γ : GA D W) * n * (γ : GA D W)⁻¹ ∈ NI W I := by
  intro D W Y s I _ hS γ hY n hn
  set c := gqMat W γ with hc_def
  set c' := gqMat W γ⁻¹ with hc'_def
  have hcc' : c * c' = 1 := gqMat_mul_inv W γ
  have hc'c : c' * c = 1 := gqMat_inv_mul W γ
  have memS : ∀ v, v ∈ Submodule.span D.host.E (Set.range I.transpose) ↔ ((v, 0) : _ × _) ∈ Y.1 := by
    intro v; rw [hS, Submodule.mem_comap, LinearMap.inl_apply]
  have memY : ∀ y, y ∈ Y.1 ↔ (c' *ᵥ y.1, y.2) ∈ Y.1 := by
    intro y; conv_lhs => rw [← hY]
    exact mem_lagAct W γ Y y
  have hcS : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      c *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose) := by
    intro v hv
    rw [memS, memY]
    simpa [Matrix.mulVec_mulVec, hc'c] using (memS v).1 hv
  have hc'S : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      c' *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose) := by
    intro v hv
    rw [memS]
    exact (memY _).1 ((memS v).1 hv)
  obtain ⟨A, hA⟩ := exists_mul_eq_mul I c' hc'S
  obtain ⟨B, hB⟩ := exists_mul_eq_mul I c hcS
  have hIc : Iᴴ * W.gram * c = Aᴴ * (Iᴴ * W.gram) := by
    rw [frame_gram_mul I W.gram c c' hcc' (gqMat_unitary W γ), hA, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hIc' : Iᴴ * W.gram * c' = Bᴴ * (Iᴴ * W.gram) := by
    rw [frame_gram_mul I W.gram c' c hc'c (gqMat_unitary W γ⁻¹), hB, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hrat : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), M.map (incA D) = rat M := fun _ => rfl
  have hγ : mt W (γ : GA D W) = rat c := (rat_gqMat W γ).symm
  have hγ' : mt W ((γ : GA D W)⁻¹) = rat c' := (rat_gqMat W γ⁻¹).symm
  have hle : NI W I ≤ (NI W I).comap (MulAut.conj (γ : GA D W)).toMonoidHom := by
    unfold NI
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨h1, h2, h3⟩ := hg
    apply Subgroup.subset_closure
    have hm : (matHom W ((MulAut.conj (γ : GA D W)).toMonoidHom g)).1 - 1 = rat c * ((matHom W g).1 - 1) * rat c' := by
      change mt W ((γ : GA D W) * g * (γ : GA D W)⁻¹) - 1 = rat c * (mt W g - 1) * rat c'
      rw [mt_mul, mt_mul, hγ, hγ', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← rat_mul, hcc', rat_one]
    rw [cT_sig, hrat] at h2 h3
    rw [hrat] at h1
    have hA' : rat c' ⬝ rat I = rat I ⬝ rat A := by rw [← rat_mul, hA, rat_mul]
    have hIc2 : rat (Iᴴ * W.gram) ⬝ rat c = rat Aᴴ ⬝ rat (Iᴴ * W.gram) := by rw [← rat_mul, hIc, rat_mul]
    have hB' : rat c ⬝ rat I = rat I ⬝ rat B := by rw [← rat_mul, hB, rat_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm, hrat]
      exact mul_mul_mul_eq_zero (rat c) (rat c') _ (rat I) (rat A) hA' h1
    · rw [hm, cT_sig, hrat]
      exact mul_mul_mul_eq_zero' (rat c) (rat c') _ (rat (Iᴴ * W.gram)) (rat Aᴴ) hIc2 h2
    · intro x hx
      rw [cT_sig] at hx
      have hx' : (Iᴴ * W.gram) *ᵥ (c' *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hIc', ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      obtain ⟨a, ha⟩ := h3 (c' *ᵥ x) hx'
      refine ⟨rat B *ᵥ a, ?_⟩
      have hv : rat c' *ᵥ (fun i => incA D (x i)) = fun i => incA D ((c' *ᵥ x) i) := by
        funext i; exact (RingHom.map_mulVec (incA D) c' x i).symm
      rw [hm, hrat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, ha, Matrix.mulVec_mulVec, hB',
        Matrix.mulVec_mulVec]
  exact hle hn

end GlobalTheory.RallisCusp

end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.CellDec.RowPos
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_val (v : HeightOneSpectrum (𝓞 E)) (x : GA E n) (i j : Fin n) :
    (compV E n v x).val i j = pLoc E v (pFin E (x.val i j)) := rfl

theorem row_unip_mul {R : Type} [CommRing R] {m : ℕ} {U : GL (Fin (m + 1)) R}
    (hU : U ∈ GlobalTheory.SmGL.unipB R (Fin (m + 1))) (K : GL (Fin (m + 1)) R) (i : Fin (m + 1)) :
    (U * K).val (Fin.last m) i = K.val (Fin.last m) i := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hU
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · rw [h2, one_mul]
  · intro j _ hj
    rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sub_single_apply {m : ℕ} (y : Fin (m + 1) → Af E) (i : Fin (m + 1)) (v : HeightOneSpectrum (𝓞 E)) :
    (((y - Pi.single (Fin.last m) (1 : Af E)) : Fin (m + 1) → Af E) i) v = y i v - if i = Fin.last m then 1 else 0 := by
  change pLoc E v ((y - Pi.single (Fin.last m) (1 : Af E) : Fin (m + 1) → Af E) i) = pLoc E v (y i) - _
  rw [Pi.sub_apply, map_sub]
  congr 1
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]

theorem val_sub_ite_le_one {v : HeightOneSpectrum (𝓞 E)} {x : v.adicCompletion E} (hx : Valued.v x ≤ 1) (p : Prop)
    [Decidable p] : Valued.v (x - if p then 1 else 0) ≤ 1 := by
  refine (Valuation.map_sub _ _ _).trans (max_le hx ?_)
  split_ifs
  · rw [map_one]
  · rw [map_zero]; exact zero_le'

end GlobalTheory.CellDec.RowPos


open GlobalTheory.CellDec GlobalTheory.CellDec.RowPos in
theorem GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      ((fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈
        GlobalTheory.ThetaPoisson.latt (m + 1) J ↔
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J) := by
  intro E _ _ m T ϖ hϖ J hJ g hg l hl
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hgv : ∀ v i, (pFin E ((u * k).val (Fin.last m) i)) v = (compV E (m + 1) v k).val (Fin.last m) i := by
    intro v i
    change pLoc E v _ = _
    rw [← compV_val, map_mul, row_unip_mul (compV_mem_unipB v hu)]
  have htv : ∀ v i, (pFin E ((tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) v =
      ((ϖ v ^ (l.1 v (Fin.last m)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) *
        (pFin E ((u * k).val (Fin.last m) i)) v := by
    intro v i
    change pLoc E v _ = _ * pLoc E v _
    rw [← compV_val, ← compV_val, map_mul (compV E (m + 1) v), compV_tl, Units.val_mul, GlobalTheory.IwaCell.val_tD,
      Matrix.diagonal_mul]
  refine forall_congr' fun i => ?_
  rw [GroundTheory.Global.mem_idealFiniteAdeles, GroundTheory.Global.mem_idealFiniteAdeles]
  refine forall_congr' fun v => ?_
  rw [sub_single_apply, sub_single_apply]
  beta_reduce
  rw [htv]
  by_cases hv : v ∈ T
  · rw [l.2 v hv]
    simp
  · rw [hJ v hv]
    have hK := (GlobalTheory.AdelicU.mem_GLint_iff.1 (mem_US.1 hk v hv)).1 (Fin.last m) i
    have hK' : Valued.v ((compV E (m + 1) v k).val (Fin.last m) i) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hK
    have hϖ1 : Valued.v ((ϖ v : v.adicCompletion E)) ≤ 1 := by
      rw [hϖ v]; exact le_of_lt (by decide)
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (hl v)
    have hp : Valued.v (((ϖ v ^ (l.1 v (Fin.last m)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)) ≤ 1 := by
      rw [ha, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_one' hϖ1 a
    rw [hgv, neg_zero, WithZero.exp_zero]
    refine ⟨fun _ => val_sub_ite_le_one hK' _, fun _ => val_sub_ite_le_one ?_ _⟩
    rw [map_mul]
    exact mul_le_one' hp hK'
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.CrystallineDescent


private theorem descend_element_of_le_of_eq_K0 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ) (m : ℕ)
    (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) :
    ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m),
      ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') :=
  GlobalTheory.T.inv_Q_pow_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT m y' hy'

set_option maxHeartbeats 60000000 in
private theorem descend_of_eq_K0_of_isCrys (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := by
  let W := (HW l).W K s LL h
  let W' := (HW l).W K' s LL h'
  let T' := @resLt l _ K K' LL hle T
  let toBase := @toTW l _ K K' LL hle T
  let f := @fMap l _ K K' W.GKs W'.GKs hm' htop
  -- Direct elimination avoids the cost of `cases` on the dependent goal.
  refine (descend_element_of_le_of_eq_K0 D HW F l K s LL h K' h' hle hK0 T hT m y' hy').elim fun y hy => ?_
  refine (GlobalTheory.T.X_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT z' hz').elim fun z hz => ?_
  refine ((GlobalTheory.WittTensorFixed.main l K' LL T').1
    (((F l).E K' s LL h').tie.jD T' y')).elim fun b' hb' => ?_
  refine (@cl_fit l _ D HW F K' s LL h' T' y' z' hyz' b' hb').elim fun c' hc' => ?_
  refine (@push_cocycle l _ (D.loc l) (D.locA l) K K' LL hle T W.GKs W'.GKs hm' htop c').elim
    fun c hc => ?_
  have hZf := hc.2
  let b := toBase b'
  have hb := (@toTW_φ l _ K K' LL hle T b').trans ((congrArg toBase hb').trans hy.2.symm)
  have hone (g : ↥W.GKs) : W'.resΓ (f g).1 = 1 ↔ W.resΓ g.1 = 1 :=
    (@resΓ_one_iff l _ (D.loc l) K' LL _ W' (f g).1).trans
      (@resΓ_one_iff l _ (D.loc l) K LL _ W g.1).symm
  have hzero (g : ↥W.GKs) (hg : W.resΓ g.1 = 1) :=
    (hZf b' g).trans ((congrArg toBase (hc'.2.1 (f g) ((hone g).2 hg))).trans
      (@toTW_zero l _ K K' LL hle T))
  refine (@lam_exists l _ D HW K' s LL h').elim fun lam' hlam' => ?_
  refine hlam'.2.2.2.1.elim fun g' hg' => ?_
  let lam := lam'.comp (@fHom l _ K K' W.GKs W'.GKs hm' htop)
  have hlamc : Continuous lam := hlam'.1.comp (@fMap_cont l _ K K' W.GKs W'.GKs hm' htop)
  have hlam1 (g : ↥W.GKs) (hg : lam g = 1) := (hone g).1 ((hlam'.2.1 (f g)).1 hg)
  let g₁ := @eMap l _ K K' hle W.GKs W'.GKs hm g'
  have hfe : f g₁ = g' := Subtype.ext (Subtype.ext rfl)
  have hg₁ : lam g₁ = Multiplicative.ofAdd 1 := (congrArg (fun g => lam' g) hfe).trans hg'
  have hZ₁ := (hZf b' g₁).trans
    ((congrArg (fun g => toBase (Zf (D.locA l) T' W'.GKs c' b' g)) hfe).trans
      ((congrArg toBase (hc'.2.2 g' ((hlam'.2.2.1 g').1 hg'))).trans hz.2.symm))
  have hall := GlobalTheory.T.cyclotomicCocycle_mem_image_of_crystalline D HW F l K s LL h T hT c b lam hlamc hlam1 hzero g₁ hg₁ z hz.1 hZ₁
  refine (@lam_exists l _ D HW K s LL h).elim fun _ hlamK => ?_
  refine hlamK.2.2.2.1.elim fun g₀ hg₀ => ?_
  have hγ := (hlamK.2.2.1 g₀).1 hg₀
  refine (hall g₀).elim fun z₀ hz₀ => ?_
  have hyz := GlobalTheory.T.herr_cocycle_of_witt_tensor_relations D HW F l K s LL h T c b y z₀ g₀ hγ hb hz₀.2
  have hcl := GlobalTheory.T.herr_class_of_cocycle_values D HW F l K s LL h T c b y z₀ hyz g₀ hγ hb hzero hz₀.2
  exact ⟨y, z₀, hyz, hy.1, hz₀.1, c, c', hcl, hc'.1, hc.1⟩


set_option maxHeartbeats 4000000 in
theorem descend (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := descend_of_eq_K0_of_isCrys D HW F l K s LL h K' h' hle hK0 htop hm hm' T hT m y' z' hyz' hy' hz'

set_option maxHeartbeats 60000000 in
private theorem wach_pow_smul_of_good_ext : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  intro D HW F Cm l p K s LL h W E C T hT M hh hJ κ hκ
  refine (@base_setup l p D HW K s LL h).elim fun K' hK' =>
    hK'.elim fun h' hh' => hh'.elim fun hle hbase => ?_
  have htop := hbase.2.1
  have hiff := hbase.2.2
  let W' := (HW l).W K' s LL h'
  let T' := @resLt l p K K' LL hle T
  have hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ W.GKs :=
    fun g => (hiff _).2 g.2
  have hm' : ∀ g : ↥W.GKs, (g.1 : GQ l) ∈ GK K' := fun g => (hiff g.1).1 g.2
  have hT' := @restrict_crys l p D K K' LL hle T hT
  have hJ' := @restrict_jumps l p D HW K s LL h K' h' hle T hT M hh hJ
    (@GlobalTheory.T.hodgeTateJump_restrict_finite_ext l p (D.loc l) (D.locA l) (D.locT l)
      K K' LL hle T.V T.acg T.modLL T.modQp T.towQp T.fdim T.ρ hT)
  refine (@pull_h1f l p (D.loc l) K K' LL hle T W.GKs W'.GKs hm κ hκ).elim fun cκ hcκ =>
    hcκ.elim fun cκ' hκ' => ?_
  refine (@GlobalTheory.T.H1f_class_of_wach_pair D HW F Cm l p K' s LL h' T' hT' htop
    (fun _ => mx M) (fun _ => mx hh) hJ' (Submodule.Quotient.mk cκ') hκ'.2.1).elim
    fun n hn => hn.elim fun y' hy' => hy'.elim fun z' hz' => hz'.elim fun hyz' hpair' => ?_
  have : Nonempty (Let K') := ⟨0⟩
  have hmx : mx (fun _ : Let K' => mx M) = mx M := ciSup_const
  have hy'mx := (congrArg (fun k : ℕ => y' ∈ invN W' T' (W'.Q ^ k)) hmx).mp hpair'.1
  refine (@descend D HW F l p K s LL h K' h' hle hbase.1 htop hm hm' T hT (mx M) y' z' hyz' hy'mx hpair'.2.1).elim
    fun y hy => hy.elim fun z hz => hz.elim fun hyz hpair => ?_
  refine hpair.2.2.elim fun c hc => hc.elim fun c' hcc' => ?_
  have hpush := @push_class l p K K' LL hle T W.GKs W'.GKs hm hm' htop c cκ c' cκ' hcc'.2.2 hκ'.2.2
    (l ^ n) (hcc'.2.1.trans hpair'.2.2)
  exact ⟨n, y, z, hyz, hpair.1, hpair.2.1,
    hcc'.1.symm.trans (hpush.trans (congrArg (fun x => (l ^ n : ℕ) • x) hκ'.1))⟩


set_option maxHeartbeats 4000000 in
theorem pow_smul_from_complex : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := wach_pow_smul_of_good_ext

end GlobalTheory.NL.CrystallineDescent
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem sFin_sLoc_eq (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    sFin E (sLoc E w y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA E 0 (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y) := by
  classical
  refine Prod.ext rfl ?_
  refine Subtype.ext (funext fun v => ?_)
  change (sLoc E w y) v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y v
  by_cases h : v = w
  · subst h
    rw [GlobalTheory.StdDual.singleV_self]
    exact (Pi.single_eq_same v y : (Pi.single v y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = y)
  · rw [GlobalTheory.StdDual.singleV_of_ne _ h]
    exact (Pi.single_eq_of_ne h y : (Pi.single w y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = 0)

theorem exists_stdPsi : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  intro E _ _
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.StdCharUnique.existsUnique_isStdChar E
  let L : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf E →+ ℂ :=
    AddMonoidHom.mk' (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℂ)) fun a b => by
      rw [GlobalTheory.StdCharUnique.traceInf_add, Complex.ofReal_add]
  have hL : Continuous L := Complex.continuous_ofReal.comp (GlobalTheory.StdCharUnique.continuous_traceInf E)
  have hT : ∀ x : E, L (algebraMap E _ x) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := fun x => by
    show ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E (algebraMap E _ x) : ℝ) : ℂ) = _
    rw [GlobalTheory.StdCharUnique.traceInf_algebraMap, Complex.ofReal_ratCast]
  have hinf : ∀ x, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf E ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x)) := fun x => by
    rw [hψ.2, GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf]
    congr 1
    show _ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ) = -(_ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ))
    ring
  have hv : ∀ v, ∃ y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV E ψ v y ≠ 1 := fun v => by
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one_of_trace (GlobalTheory.StdAdelicChar.isCharAF_inv hψ.1) (fun a => by
      rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, AddChar.inv_apply', ← Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, hinf, hT, ← Complex.exp_neg, neg_neg]) v
    refine ⟨y, fun h1 => hy ?_⟩
    rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV] at h1 ⊢
    rw [AddChar.inv_apply', h1, inv_one]
  refine ⟨ψ, hψ.1.1, hψ.1.2.1, hψ.1.2.2.1, fun x h => GlobalTheory.RatAnnih.adele_rat hψ.1 hv L hL hT hinf x h, ?_⟩
  intro w
  obtain ⟨y, hy⟩ := hv w
  refine ⟨y, ?_⟩
  rw [sFin_sLoc_eq]
  exact hy

end GlobalTheory.CuspGeneric

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.wittCompletedTilt_columns_of_right_inverse_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (d d' n : ℕ) (Q : Matrix (Fin d) (Fin d') (WCb l)) (S : Matrix (Fin d') (Fin d) (WCb l)) (U Uinv : Matrix (Fin d') (Fin d') (WCb l)) (J : Finset (Fin d')), 1 ≤ n → (∀ i j, (l : WCb l) ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → Uinv * U = 1 → U * Uinv = 1 → (∀ j ∉ J, ∀ i, (l : WCb l) ^ n ∣ (Q * U) i j) → (∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, (l : WCb l) ∣ (Uinv *ᵥ v) j) → ∃ e : Fin d ≃ J, IsUnit (Q * U.submatrix id (fun k => (e k : Fin d'))) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Q - (Q * U.submatrix id (fun k => (e k : Fin d'))) * Uinv.submatrix (fun k => (e k : Fin d')) id) i j := by
  first | exact @GlobalTheory.CardJ.exists_cols_of_rightInv_WCb | exact GlobalTheory.CardJ.exists_cols_of_rightInv_WCb | (intros; apply GlobalTheory.CardJ.exists_cols_of_rightInv_WCb; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

theorem _root_.GlobalTheory.T.crystalline_character_jump_one_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  first | exact @GlobalTheory.HWL.charRep_crys_jump_one | exact GlobalTheory.HWL.charRep_crys_jump_one | (intros; apply GlobalTheory.HWL.charRep_crys_jump_one <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.local_absorption_length_bound_of_blochKato : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), BlochKatoDuality.Conclusion1 D ∧ BlochKatoDuality.Conclusion2 D := by
  first | exact @GlobalTheory.ClosingStatement.main | exact GlobalTheory.ClosingStatement.main | (intros; apply GlobalTheory.ClosingStatement.main <;> assumption)
end
