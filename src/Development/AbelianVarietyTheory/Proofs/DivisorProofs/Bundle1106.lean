module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.RingTheory.LocalRing.Module
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField GlobalTheory.AllWt

namespace GlobalTheory.CutNum

open Module Formalism.HermitianLatticesTheory

section Maj

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)

theorem fcoord_add' (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
    funext i
    simp [vecAt]
  simp only [fcoord, hv, Matrix.mulVec_add]

theorem fcoord_smul' (a : K) (x : V) : fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i
    simp [vecAt]
  simp only [fcoord, hv, Matrix.mulVec_smul]

theorem normAt_add_sq (x y : V) :
    normAt b X v (x + y) ^ 2 = normAt b X v x ^ 2 + normAt b X v y ^ 2 + 2 * (majAt b X v x y).re := by
  simp only [normAt, cnorm, majAt, fcoord_add']
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_smul_left' (a : K) (x y : V) :
    majAt b X v (a • x) y = star (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem majAt_add_right' (x y z : V) : majAt b X v x (y + z) = majAt b X v x y + majAt b X v x z := by
  simp only [majAt, fcoord_add', Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem star_majAt' (x y : V) : star (majAt b X v x y) = majAt b X v y x := by
  simp only [majAt, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem selfAdj_of_pyth (hv : v.IsComplex) (e : V →ₗ[K] V)
    (h : ∀ x y, normAt b X v (e x + (y - e y)) ^ 2 = normAt b X v (e x) ^ 2 + normAt b X v (y - e y) ^ 2) (x y : V) :
    majAt b X v (e x) y = majAt b X v x (e y) := by
  have hre : ∀ x y, (majAt b X v (e x) (y - e y)).re = 0 := by
    intro x y
    have h1 := normAt_add_sq b X v (e x) (y - e y)
    have h2 := h x y
    linarith
  obtain ⟨a, ha⟩ : ∃ a : K, (v.embedding a).im ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply InfinitePlace.isComplex_iff.mp hv
    first
    | exact fun t => Complex.conj_eq_iff_im.mpr (hcon t)
    | (rw [ComplexEmbedding.isReal_iff]; ext t; exact Complex.conj_eq_iff_im.mpr (hcon t))
  have hzero : ∀ x y, majAt b X v (e x) (y - e y) = 0 := by
    intro x y
    have h0 := hre x y
    have h1 := hre (a • x) y
    rw [map_smul, majAt_smul_left'] at h1
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, h0] at h1
    have hm : (v.embedding a).im * (majAt b X v (e x) (y - e y)).im = 0 := by linarith
    refine Complex.ext (by simpa using h0) ?_
    rcases mul_eq_zero.mp hm with hm | hm
    · exact absurd hm ha
    · simpa using hm
  have hL : majAt b X v (e x) y = majAt b X v (e x) (e y) := by
    have := majAt_add_right' b X v (e x) (e y) (y - e y)
    rw [hzero, add_zero, show e y + (y - e y) = y by abel] at this
    exact this
  have hR : majAt b X v x (e y) = majAt b X v (e x) (e y) := by
    have := majAt_add_right' b X v (e y) (e x) (x - e x)
    rw [hzero, add_zero, show e x + (x - e x) = x by abel] at this
    rw [← star_majAt' b X v (e y) x, this, star_majAt']
  rw [hL, hR]

end Maj

theorem numeric {dg db μ μg m lg δ Q : ℝ} (hd : 0 < dg + db) (hdg : 0 ≤ dg) (hdb : 0 ≤ db)
    (hcut : (dg + db) * μ ≤ dg * μg + db * (m + lg)) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 12) (hb : db ≤ 3 * δ * (dg + db))
    (hm : m ≤ Q) (hμ : -Q ≤ μ) (hlg : lg ≤ Q) (hlg0 : 0 ≤ lg) : μ - 12 * δ * Q ≤ μg := by
  have hQ : 0 ≤ Q := by linarith
  have hδdb : δ * db ≤ 1 / 12 * db := mul_le_mul_of_nonneg_right hδ' hdb
  have hdg0 : 0 < dg := by
    rcases lt_or_eq_of_le hdg with h | h
    · exact h
    · subst h
      nlinarith
  have h4 : db ≤ 4 * δ * dg := by nlinarith
  have k1 : db * (-Q) ≤ db * μ := mul_le_mul_of_nonneg_left hμ hdb
  have k2 : db * Q ≤ 4 * δ * dg * Q := mul_le_mul_of_nonneg_right h4 hQ
  have k3 : db * m ≤ db * Q := mul_le_mul_of_nonneg_left hm hdb
  have k4 : db * lg ≤ db * Q := mul_le_mul_of_nonneg_left hlg hdb
  have key : dg * (μ - 12 * δ * Q) ≤ dg * μg := by nlinarith
  exact le_of_mul_le_mul_left key hdg0

theorem slope_good_ge : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L M : Submodule (𝓞 K) V) (e : V →ₗ[K] V) (g : ℕ) (δ Q : ℝ), HasGram N → M.FG → L ≤ M → L ≠ ⊥ → e ∘ₗ e = e → (∀ σ x y, N σ (e x + (y - e y)) ^ 2 = N σ (e x) ^ 2 + N σ (y - e y) ^ 2) → 1 ≤ g → (∀ x ∈ L, (g : K) • e x ∈ L) → 0 ≤ δ → δ ≤ 1 / 12 → (Formalism.HN.rkK (L ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ≤ 3 * δ * Formalism.HN.rkK L → slopeMax_sq N M ≤ Q → -Q ≤ slope_sq N L → 2 * Real.log g ≤ Q → slope_sq N L - 12 * δ * Q ≤ slope_sq N (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) := by
  intro K V _ _ _ _ _ _ _ N L M e g δ Q hGram hM hLM hL0 hee hpyth hg hint hδ hδ' hrk hmax hmin hlog
  letI : StarRing K := starRingOfComm
  obtain ⟨F⟩ := hGram
  obtain ⟨n, ⟨⟨b, X⟩, hG⟩⟩ := F
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  have hLfg : L.FG := Submodule.FG.of_le hM hLM
  have hRfg : (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)).FG :=
    Submodule.FG.of_le hM (inf_le_left.trans hLM)
  have hsa : ∀ v x y, majAt b X v (e x) y = majAt b X v x (e y) := by
    intro v
    apply selfAdj_of_pyth b X v (IsTotallyComplex.isComplex v) e
    intro x y
    simp only [(hG v).2]
    exact hpyth v.embedding x y
  obtain ⟨hrkadd, hcut, hmaj⟩ := Formalism.ExtensionFiltration.goodBadCut K V (Fin n) b X hX e g L hLfg hg hee hsa hint
  have hM0 : M ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hLM))
  rw [slope_sq_eq hG hLfg] at hmin ⊢
  rw [slope_sq_eq hG hRfg]
  rw [(slopeMax_slopeMin_eq hG hM hM0).1] at hmax
  have hne := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b L hL0
  have hrkR : (Formalism.HN.rkK L : ℝ) = (Formalism.HN.rkK (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (Formalism.HN.rkK (L ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) := by
    exact_mod_cast hrkadd.symm
  have hpos : (0 : ℝ) < Formalism.HN.rkK L := by exact_mod_cast Nat.pos_of_ne_zero hne
  have hmj := hmaj M hM hLM
  have hlg0 : 0 ≤ 2 * Real.log g := by
    have : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have := Real.log_nonneg this
    linarith
  rw [hrkR] at hcut hrk hpos
  exact numeric hpos (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith) hδ hδ' hrk hmax hmin hlog hlg0

end GlobalTheory.CutNum
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.LastSideProof

theorem lastSide_of_logT_le : ∀ (CY CT : ℝ) (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau)
    (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)),
    WeightTie N W pl u δ → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T u : ℝ) ≤ CT * N.R.m * N.sc.L →
    1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R CT (lastLog W u) := by
  intro CY CT N X Pr W pl u δ J _ eJ R hWT hS hSR hlogT hT hR
  obtain ⟨C, hC⟩ := GlobalTheory.BranchLogBound.orthNormLogBound
  have hW : W.Ok := hWT.1
  have hk := N.R.m_add_three_le_k
  have hm := N.R.two_le_m
  obtain ⟨hL, ha, -, -, hmR, -, hkR, hNn, hSc, hη, hb', -⟩ := hR.nums
  obtain ⟨-, -, -, -, -, hnodes, hcloud, -, hbT, hoff⟩ := id hSR
  have hNq : ((N.Nm : ℕ) : ℝ) = (N.R.k : ℝ) + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) := by
    unfold NumDatum.Nm Ranks.N; push_cast; ring

  let lam1 : RPl N.R → ℝ := fun z => (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ)
  let D0 : RPl N.R → ℝ := fun z => ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
  let D1 : RPl N.R → ℝ := fun z =>
    ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
  let logc : RPl N.R → ℝ := fun z => (R.Nn - 1) * D1 z * Real.log (2 * R.a)
  let logxi : RPl N.R → ℝ := fun _ => R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)
  let bT : RPl N.R → ℝ := fun z => ((N.bT z.2 : ℚ) : ℝ)

  have hrow : ∀ z, (W.hc u (pl z)).v = (N.hc z).v ∧ (W.hc u (pl z)).b = (N.hc z).b ∧ (W.hc u (pl z)).e = (N.hc z).e := fun z =>
    ⟨congrArg RowPar.v (hWT.2.2 z).1, congrArg RowPar.b (hWT.2.2 z).1, congrArg RowPar.e (hWT.2.2 z).1⟩
  have hu0 : ∀ z, (W.hc u (pl z)).u ⟨0, by omega⟩ = (N.hc z).u ⟨0, by omega⟩ := fun z =>
    ((hWT.2.2 z).2 _).trans (uW_first N δ z _)
  have hul : ∀ z, (W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ = (N.hc z).u ⟨N.R.k - 1, by omega⟩ := fun z =>
    ((hWT.2.2 z).2 _).trans (uW_last N δ z _)
  have hlam1 : ∀ z, lam1 z = (((N.hc z).u ⟨0, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 -
      (N.R.m : ℝ) * (((N.R.t : ℝ) + 1) / 2) := by
    intro z
    have h := congrArg (fun q : ℚ => (q : ℝ)) (ext_lam_lo W u (pl z) 0 (by omega))
    rw [hu0 z] at h
    push_cast at h
    show (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ) = _
    rw [h]; ring
  have hsumB : ∀ z, ((∑ B ∈ Finset.range N.R.m, ((RowPar.of (W.hc u (pl z))).eAt B - (RowPar.of (W.hc u (pl z))).bAt B -
      ((N.R.t : ℚ) + 1) / 2) : ℚ) : ℝ) ≤ (N.R.m : ℝ) * N.eta := by
    intro z
    push_cast
    have : ∀ B ∈ Finset.range N.R.m, (((RowPar.of (W.hc u (pl z))).eAt B : ℚ) : ℝ) - (((RowPar.of (W.hc u (pl z))).bAt B : ℚ) : ℝ) -
        ((N.R.t : ℝ) + 1) / 2 ≤ N.eta := by
      intro B hB
      rw [Finset.mem_range] at hB
      rw [RowPar.eAt_of _ hB, RowPar.bAt_of _ hB, (hrow z).2.1, (hrow z).2.2]
      have h1 := hnodes z ⟨B, hB⟩ ⟨B, hB⟩
      have h2 := neg_abs_le ((((N.hc z).b ⟨B, hB⟩ - (N.hc z).e ⟨B, hB⟩ : ℚ) : ℝ))
      push_cast at h1 h2
      have ht : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
      linarith
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hD0 : ∀ z, D0 z ≤ N.Sc + (N.R.m : ℝ) * N.eta + (if z ∈ R.TT then bT z else 0) := by
    intro z
    have h := castQ (bottomRank_sum_le_two_mul_totalRank W hW u (pl z))
    push_cast at h
    have hB := hsumB z
    push_cast at hB
    have hv0 := hcloud z ⟨0, by omega⟩
    rw [← (hrow z).1] at hv0
    have hv0' : (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) ≤ N.Sc := hv0.2
    have hkR' : (5 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 5 ≤ N.R.k)
    show ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤ _
    split_ifs with htop
    · obtain ⟨h1, h2⟩ := (hR.tops z).1 htop
      have hbz : bT z = -(((N.hc z).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 := by
        show ((N.bT z.2 : ℚ) : ℝ) = _
        obtain ⟨b, t⟩ := z
        simp only at h1
        subst h1
        unfold NumDatum.bT
        push_cast
        rfl
      rw [hbz, ← hul z]
      linarith
    · have hzero : (0 : ℚ) ≤ (N.hc z).v ⟨N.R.k - 2, by omega⟩ := (hcloud z ⟨N.R.k - 2, by omega⟩).1
      obtain ⟨hlast, -, -⟩ := hoff z (fun h => htop ((hR.tops z).2 h)) (by omega)
      have hl : (((W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) = (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) - 1 / 2 := by
        rw [hul z, hlast]; push_cast; ring
      have hzero' : (0 : ℝ) ≤ (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hzero
      rw [hl] at h
      linarith
  have hD1 : ∀ z, D1 z ≤ 3 * D0 z + N.Sc + N.eta := by
    intro z
    have h := castQ (dOne_le_place W hW u (pl z))
    push_cast at h
    have hv0 := (hcloud z ⟨0, by omega⟩).2
    have hvk := (hcloud z ⟨N.R.k - 2, by omega⟩).1
    rw [← (hrow z).1] at hv0 hvk
    have hvk' : (0 : ℝ) ≤ (((W.hc u (pl z)).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hvk
    have hu1 : (((W.hc u (pl z)).u ⟨1, by omega⟩ : ℚ) : ℝ) < (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) := by
      exact_mod_cast (W.hc u (pl z)).v_gt_u ⟨0, by omega⟩
    rw [RowPar.eAt_of _ (by omega : N.R.m - 1 < N.R.m), RowPar.eAt_of _ (by omega : 0 < N.R.m)] at h
    have hg := (W.hc u (pl z)).gap_be ⟨0, by omega⟩
    have hg' : ((((W.hc u (pl z)).b ⟨0, by omega⟩ : ℚ)) : ℝ) ≤ (((W.hc u (pl z)).e ⟨0, by omega⟩ : ℚ) : ℝ) := by
      have ht : (0 : ℚ) ≤ N.R.t := Nat.cast_nonneg _
      exact_mod_cast (by linarith : (W.hc u (pl z)).b ⟨0, by omega⟩ ≤ (W.hc u (pl z)).e ⟨0, by omega⟩)
    have hn := hnodes z ⟨0, by omega⟩ ⟨N.R.m - 1, by omega⟩
    rw [← (hrow z).2.1, ← (hrow z).2.2] at hn
    have hn' := neg_abs_le ((((W.hc u (pl z)).b ⟨0, by omega⟩ - (W.hc u (pl z)).e ⟨N.R.m - 1, by omega⟩ : ℚ) : ℝ))
    push_cast at hn hn'
    have hkR' : (5 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 5 ≤ N.R.k)
    have hmt : (0 : ℝ) ≤ ((N.R.m : ℝ) - 1) * ((N.R.t : ℝ) + 1) := by
      have : (1 : ℝ) ≤ N.R.m := by exact_mod_cast (by omega : 1 ≤ N.R.m)
      have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _

      have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
      nlinarith
    show ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤
      3 * ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) + N.Sc + N.eta
    linarith
  refine ⟨bT, fun z => lam1 z - D0 z, lam1, D0, D1, logc, logxi, ?_, fun z => le_rfl, fun z => le_rfl, fun z => rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hI : (∀ τ, Br.Interlace (N_m_succ N.R) (W.lamTrue u N.R.m τ) (W.sgTrue τ)) ∧ ∀ τ, Br.SameShift (W.lamTrue u N.R.m τ) (W.sgTrue τ) :=
      ⟨fun τ => GlobalTheory.BranchMembers.interlace W hW u τ, fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.members_sameShift W hW u τ⟩
    have hsp : ∀ τ, (((W.lamTrue u N.R.m τ).spread : ℤ) : ℝ) ≤ 2 * N.sc.a := fun τ => hS.spread_le u N.R.m le_rfl τ
    obtain ⟨-, hlog, -⟩ := hC X.Tau (N.R.N N.R.m) (N.R.N N.R.m - 1) (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue
      hI.1 N.sc.a hsp
    have hA : lastLog W u = -((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) * Real.log (Pr.T u : ℝ) +
        Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue) := rfl
    have h0 : ∀ z, ext (W.lamTrue u N.R.m (pl z)) 0 = (W.lamTrue u N.R.m (pl z)).w ⟨0, N.R.N_pos N.R.m⟩ := fun z =>
      ext_of _ ⟨0, _⟩
    have hn : ((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) = ∑ z, (lam1 z - D0 z) := by
      rw [Int.cast_sum, ← Equiv.sum_comp pl]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [nBr_eq_sub (N_m_succ N.R)]
      show _ = ((ext (W.lamTrue u N.R.m (pl z)) 0 : ℤ) : ℝ) -
        ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
      rw [h0]
      push_cast
      rfl
    have hre : ∑ τ, (2 * (((N.R.N N.R.m : ℕ) : ℝ) - 1) *
          ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) +
          ((N.R.N N.R.m : ℕ) : ℝ) * (((N.R.N N.R.m : ℕ) : ℝ) - 1) / 2) * Real.log (2 * N.sc.a) =
        ∑ z, (2 * logc z + logxi z) := by
      rw [← Equiv.sum_comp pl]
      refine Finset.sum_congr rfl fun z _ => ?_
      show _ = 2 * ((R.Nn - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) *
        Real.log (2 * R.a)) + R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)
      rw [hNn, ha]
      unfold NumDatum.Nm
      ring
    show lastLog W u ≤ -(∑ z, (lam1 z - D0 z) * R.logT) + ∑ z, (2 * logc z + logxi z)
    rw [hA, hn, hR.logT, ← Finset.sum_mul, ← hre]
    linarith
  · intro z hz
    obtain ⟨h1, h2⟩ := (hR.tops z).1 hz
    obtain ⟨b, t⟩ := z
    simp only at h1
    subst h1
    rw [hlam1, hR.aT t h2, hNn, hkR, hNq]
    unfold NumDatum.aT
    push_cast
    ring
  · intro z hz
    obtain ⟨-, hS1, -⟩ := hoff z (fun h => hz ((hR.tops z).2 h)) (by omega)
    have hv := (hcloud z ⟨0, by omega⟩).1
    have hv' : (0 : ℝ) ≤ (((N.hc z).v ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hv
    rw [hlam1, hSc, hNn, hNq]
    push_cast at hS1
    linarith
  · intro z
    rw [hSc, hmR, hη]
    exact hD0 z
  · intro z
    rw [hSc, hη]
    exact hD1 z
  · intro z hz
    obtain ⟨h1, h2⟩ := (hR.tops z).1 hz
    obtain ⟨b, t⟩ := z
    simp only at h1
    subst h1
    rw [hb']
    exact (hbT t h2).2
  · rw [hR.logT]
    exact Real.log_nonneg (by exact_mod_cast hT)
  · rw [hR.logT, hmR, hL]
    exact hlogT

end GlobalTheory.ColRows.LastSideProof
end

section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

namespace GlobalTheory.QCoh


open TensorProduct in
theorem nontrivial_fibre_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    Nontrivial (q.ResidueField ⊗[S] N) ↔ Nontrivial (p.ResidueField ⊗[R] M) := by
  letI : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap R S) hpq).toAlgebra
  haveI : IsScalarTower R p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun r =>
      (IsScalarTower.algebraMap_apply R S q.ResidueField r).trans
        (Ideal.ResidueField.map_algebraMap _ _ _ hpq r).symm
  have e₁ : q.ResidueField ⊗[S] N ≃ₗ[S] q.ResidueField ⊗[S] (S ⊗[R] M) :=
    LinearEquiv.lTensor q.ResidueField hl.equiv.symm
  have e₂ : q.ResidueField ⊗[S] (S ⊗[R] M) ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R S q.ResidueField q.ResidueField M
  have e₃ : q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[R] M) ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange R p.ResidueField q.ResidueField q.ResidueField M
  rw [e₁.toEquiv.nontrivial_congr, e₂.toEquiv.nontrivial_congr, ← e₃.toEquiv.nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right p.ResidueField q.ResidueField

theorem mem_support_of_isBaseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (q : PrimeSpectrum S) :
    q ∈ Module.support S N ↔ PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M := by
  haveI : Module.Finite S N := Module.Finite.equiv hl.equiv
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  exact nontrivial_fibre_of_isBaseChange hl _ _ rfl

theorem support_pullback {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [IsFiniteQC G] :
    support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G := by
  ext y
  obtain ⟨U, V, hU, hV, hy, -, e⟩ := exists_affine_pair f y (W := ⊤) trivial
  have hfy : f y ∈ V := e hy
  rw [Set.mem_preimage, mem_support_iff_primeIdealOf hU ⟨y, hy⟩,
    mem_support_iff_primeIdealOf hV ⟨f y, hfy⟩]
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  have := finite_sections G hV
  rw [mem_support_of_isBaseChange (isBaseChange_pullbackSections f G hU hV e)]
  have h := IsAffineOpen.comap_primeIdealOf_appLE V hV U hU e hy
  convert Iff.rfl using 2
  exact h.symm

end GlobalTheory.QCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleFamilyAtPoint_lambda_trivial : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) (N : LB (A ⊗ T).left), Fam A N → Triv (abelian₂ (GlobalTheory.TwistFlat.bc A φ) (GlobalTheory.TwistFlat.twist A φ N)) := by
  first | exact @GlobalTheory.TwistFlat.triv_lam_twist | exact GlobalTheory.TwistFlat.triv_lam_twist | (intros; apply GlobalTheory.TwistFlat.triv_lam_twist <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

theorem _root_.GlobalTheory.T.exists_kernelAction_triple_overlap : ∀ (S : Scheme.{0}) (A N T : Over S) [GrpObj A] [GrpObj N] (i : N ⟶ A) (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsCharacter χ → ∃ (W : Scheme.{0}) (m₁₂ m₂₃ m₁₃ : W ⟶ (A ⊗ (N ⊗ T)).left), IsPullback m₁₂ m₂₃ (actMap i T).left (prMap A N T).left ∧ m₁₃ ≫ (prMap A N T).left = m₁₂ ≫ (prMap A N T).left ∧ m₁₃ ≫ (actMap i T).left = m₂₃ ≫ (actMap i T).left ∧ pullTop m₁₃ (pullTop (snd A (N ⊗ T)).left χ) = pullTop m₁₂ (pullTop (snd A (N ⊗ T)).left χ) * pullTop m₂₃ (pullTop (snd A (N ⊗ T)).left χ) := by
  first | exact @GlobalTheory.CharKer.triOverlap | exact GlobalTheory.CharKer.triOverlap | (intros; apply GlobalTheory.CharKer.triOverlap <;> assumption)
end
