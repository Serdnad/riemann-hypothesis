module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Compactness.Paracompact
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma fixA_comb {K : Type} [Field K] [NumberField K] {n : ℕ} {κ : Measure (archCompact K n)}
    {e : archCompact K n → ℂ} (he : IdemA κ e) (hc : CompactSpace (archCompact K n))
    (ha : Continuous (arc1 : archCompact K n → G1 K n)) {f f' : G1 K n → ℂ} (hf : Continuous f)
    (hf' : Continuous f') (c : ℂ) (h₁ : FixA κ e f) (h₂ : FixA κ e f') : FixA κ e (f + c • f') := by
  intro g
  haveI := he.haar.prob
  have hi : ∀ {p : G1 K n → ℂ}, Continuous p → Integrable (fun k => e k * p (g * arc1 k)) κ := by
    intro p hp
    exact (he.cont.mul (hp.comp (continuous_const.mul ha))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e₁ : (fun k => e k * (f + c • f') (g * arc1 k)) =
      fun k => e k * f (g * arc1 k) + c * (e k * f' (g * arc1 k)) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e₁, integral_add (hi hf) ((hi hf').const_mul c), integral_const_mul, h₁ g, h₂ g]
  simp

private lemma flat_comb {K : Type} [Field K] [NumberField K] (f f' : G1 K (2 + 2) → ℂ) (c : ℂ) :
    flat 0 (f + c • f') = flat 0 f + c • flat 0 f' := by
  funext x
  simp only [flat, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma block_frame_conjugation_identity {G H : Type} [Group G] [Group H] (p : H →* G) (x : G) (a b : H) :
    x * p b * p a = x * p a * p (a⁻¹ * b * a) := by
  simp [mul_assoc]

private lemma lev_exists (K : Type) [Field K] [NumberField K] (n : ℕ) :
    ∃ U : ∀ w : Pl K, Subgroup (Gw n w), Lev U :=
  ⟨fun w => GLnLocal.integralGL (w.adicCompletion K) n, fun w =>
    ⟨⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩, le_rfl⟩⟩

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.zMem :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ), IdemA κ e → (∀ S φ, φ ∈ Zs τ₁ τ₂ κ e S ↔ IsZ τ₁ τ₂ κ e S φ) ∧
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι → ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), IsOpen {g | rS ι g φ = φ} ∧ ∀ g, rS ι g φ ∈ Zs τ₁ τ₂ κ e (im w) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e he
  obtain ⟨⟨sec0, secLin⟩, secFlat, -, secT⟩ := secTr μ₂ τ₁ τ₂ κ e he
  have hZero : ∀ S, IsZ τ₁ τ₂ κ e S 0 := by
    intro S
    obtain ⟨U, hU⟩ := lev_exists K (2 + 2)
    refine ⟨0, sec0, fun g => by simp, ⟨U, hU, fun u _ g => rfl⟩, ?_⟩
    funext x
    simp [flat]
  have hComb : ∀ S φ φ' (c : ℂ), IsZ τ₁ τ₂ κ e S φ → IsZ τ₁ τ₂ κ e S φ' → IsZ τ₁ τ₂ κ e S (φ + c • φ') := by
    rintro S _ _ c ⟨f, hf, ha, ⟨U, hU, hx⟩, rfl⟩ ⟨f', hf', ha', ⟨U', hU', hx'⟩, rfl⟩
    obtain ⟨-, hL, -, hA, hC, -⟩ := levLaws (K := K) (2 + 2) S
    obtain ⟨hLev, hEq⟩ := hL U U' hU hU'
    refine ⟨f + c • f', secLin f f' hf hf' c, fixA_comb he hC hA hf.cont hf'.cont c ha ha',
      ⟨_, hLev, ?_⟩, (flat_comb f f' c).symm⟩
    rw [hEq]
    intro u hu g
    simp only [Pi.add_apply, Pi.smul_apply, hx u hu.1 g, hx' u hu.2 g]
  have hZ : ∀ S φ, φ ∈ Zs τ₁ τ₂ κ e S ↔ IsZ τ₁ τ₂ κ e S φ := by
    intro S φ
    refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
    induction h using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact hZero S
    | add x y _ _ hx hy =>
      have := hComb S x y 1 hx hy
      simpa using this
    | smul c x _ hx =>
      have := hComb S 0 x c (hZero S) hx
      simpa using this
  refine ⟨hZ, ?_⟩
  intro r w ι hw hι φ hφ
  obtain ⟨f, hf, ha, ⟨U, hU, hx⟩, rfl⟩ := (hZ _ _).1 hφ
  obtain ⟨L₁, -, -, -, -, L₂⟩ := levLaws (K := K) (2 + 2) (im w)
  have hfix : FixF (levOn (im w) U) (flat 0 f) := ((secFlat f hf.cont).2 _ (L₁ U hU).2).2 hx
  refine ⟨?_, fun g => ?_⟩
  · have hcι : Continuous ι := ((embEx (K := K) (2 + 2) w hw).2 ι hι).1
    have hO : IsOpen (ι ⁻¹' (levOn (im w) U : Set (FA K (2 + 2)))) := (L₁ U hU).1.2.preimage hcι
    let T : Subgroup (GS (2 + 2) w) :=
      { carrier := {g | rS ι g (flat 0 f) = flat 0 f}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hO.mem_nhds (by simp [one_mem])) ?_)
    intro g hg
    show rS ι g (flat 0 f) = flat 0 f
    funext x
    exact hfix _ hg x
  · obtain ⟨f', hf', ha', he'⟩ := secT f (ι g) hf ha
    obtain ⟨U', hU', hc⟩ := L₂ w ι hw hι rfl U hU g
    have hr : rS ι g (flat 0 f) = flat 0 f' := by
      funext x
      rw [he']
      rfl
    rw [hr]
    refine Submodule.subset_span ⟨f', hf', ha', ⟨U', hU', ?_⟩, rfl⟩
    refine ((secFlat f' hf'.cont).2 _ (L₁ U' hU').2).1 ?_
    intro u hu x
    rw [he', he', block_frame_conjugation_identity (MultiplicityOne.finProj K (2 + 2)) x (ι g) u]
    exact hfix _ (hc u hu) (x * fin1 (ι g))
end

section

section Par

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem unip_corner {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) :
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 ((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ 0 (1 : Matrix (Fin b) (Fin b) R) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Matrix.toBlocks₁₂, Fin.ext_iff] <;> omega

private theorem unip_any {a b : ℕ} {R : Type} [CommRing R] (B : Matrix (Fin a) (Fin b) R) : ∃ X : UPos (a + b) a → R,
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks 1 B 0 (1 : Matrix (Fin b) (Fin b) R) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 B 0 0) p.1.1 p.1.2, ?_⟩
  rw [unip_corner]
  congr 1
  ext i j
  have : (Fin.castAdd b i : Fin (a + b)) ≠ Fin.natAdd a j := by
    simp [Fin.ext_iff]; omega
  simp [unipMatrix, blockEntry_apply, Matrix.toBlocks₁₂, this]

private theorem split_par {a b : ℕ} {R : Type} [CommRing R] (g : GL (Fin (a + b)) R)
    (h : (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ (c : GL (Fin a) R) (d : GL (Fin b) R) (X : UPos (a + b) a → R), g = unipGL X * blk c d := by
  have e1 : g.val.submatrix finSumFinEquiv finSumFinEquiv * g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv =
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) := by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hg : ∀ M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R, g.val.submatrix finSumFinEquiv finSumFinEquiv = M →
      g.val = M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rintro _ rfl
    simp
  generalize g.val.submatrix finSumFinEquiv finSumFinEquiv = M at *
  generalize g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv = N at *
  have hM := (Matrix.fromBlocks_toBlocks M).symm
  rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, h, h', Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e1
  obtain ⟨e1, -, -, e2⟩ := e1
  obtain ⟨X, hX⟩ := unip_any (M.toBlocks₁₂ * N.toBlocks₂₂)
  refine ⟨⟨_, _, e1, mul_eq_one_comm.1 e1⟩, ⟨_, _, e2, mul_eq_one_comm.1 e2⟩, X, Units.ext ?_⟩
  have hX' : unipMatrix X = (Matrix.fromBlocks 1 (M.toBlocks₁₂ * N.toBlocks₂₂) 0 1).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hX]; simp
  rw [Units.val_mul, coe_unipGL, hX', hg M rfl]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_assoc, mul_eq_one_comm.1 e2, Matrix.mul_one]
  rw [← h, ← hM]

private theorem par_of_low {K : Type} [Field K] [NumberField K] (s : G1 K (2 + 2))
    (h : ((s : AdelicGLn.AdelicGL K (2 + 2)).val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : ((s : AdelicGLn.AdelicGL K (2 + 2))⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ X m₁ m₂ t, s = nn X * lv m₁ m₂ t := by
  obtain ⟨hlv, -, -, -, hdet, -⟩ := blkLaws (K := K)
  obtain ⟨a, d, X, hX⟩ := split_par (s : AdelicGLn.AdelicGL K (2 + 2)) h h'
  refine ⟨X, retractOne a, retractOne d, Real.log (detModule K 2 a).1, ?_⟩
  have h1 : detModule K 2 a * detModule K 2 d = 1 := by
    have := mem_normOneGL_iff_detModule.1 s.2
    rwa [hX, map_mul, mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL _), one_mul, hdet] at this
  have z1 : zt K (Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 a) := by
    unfold zt
    congr 1
    exact Subtype.ext (Real.exp_log (detModule K 2 a).2)
  have z2 : zt K (-Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 d) := by
    unfold zt
    congr 1
    refine Subtype.ext ?_
    rw [eq_inv_of_mul_eq_one_right h1]
    show Real.exp (-Real.log _) = _
    rw [Real.exp_neg, Real.exp_log (detModule K 2 a).2]
    rfl
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, hlv, z1, z2, coe_retractOne, coe_retractOne, inv_mul_cancel_right, inv_mul_cancel_right]
  exact hX

private theorem low_of_borel {K : Type} [Field K] [NumberField K] {b : AdelicGLn.AdelicGL K (2 + 2)} (hb : b ∈ adelicBorel) :
    (b.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
  ext i j
  refine mem_adelicBorel.1 hb ?_
  show finSumFinEquiv (Sum.inl j) < finSumFinEquiv (Sum.inr i)
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

end Par

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical NumberField.AdeleRing

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem snd_entry (x : AdelicGLn.FiniteAdelicGL K n) (a b : Fin n) :
    ((finEmb K n x : AdelicGLn.AdelicGL K n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd K n (finEmb K n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

private theorem cf_snd (v : Pl K) (x : AdelicGLn.AdelicGL K n) : GM.cf v (AdelicGLn.prodEquiv K n x).2 = finAt v x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb K n (AdelicGLn.prodEquiv K n x).2 : AdelicGLn.AdelicGL K n) a b).2 v = (x a b).2 v
  rw [snd_entry, AdelicGLn.prodEquiv_apply_snd]

private theorem cf_mul (v : Pl K) (x y : AdelicGLn.FiniteAdelicGL K n) : GM.cf v (x * y) = GM.cf v x * GM.cf v y := by
  unfold GM.cf
  rw [map_mul, finAt_mul]

private theorem central_borel (s : {r : ℝ // 0 < r}) : centralSection K n s ∈ adelicBorel := by
  refine mem_adelicBorel.2 ?_
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]
  exact Matrix.blockTriangular_diagonal _

private theorem fin_borel (y : AdelicGLn.FiniteAdelicGL K n)
    (hy : ∀ v : Pl K, ∀ i j : Fin n, j < i → GM.cf v y i j = 0) : finEmb K n y ∈ adelicBorel := by
  refine mem_adelicBorel.2 fun i j hij => ?_
  have hij' : j < i := hij
  refine adele_ext (fun w => ?_) fun v => ?_
  · have e1 : (finEmb K n y i j).1 = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j :=
      congrArg (fun z => z.1 i j) (prodEquiv_finEmb y)
    rw [e1, Matrix.one_apply_ne hij'.ne']
    rfl
  · exact hy v i j hij'

private theorem proj_borel (y : AdelicGLn.FiniteAdelicGL K n) (h : finEmb K n y ∈ adelicBorel) :
    (MultiplicityOne.finProj K n y : AdelicGLn.AdelicGL K n) ∈ adelicBorel := by
  rw [MultiplicityOne.coe_finProj]
  exact mul_mem h (inv_mem (central_borel _))

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.finIwa :
    ∀ {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ (h : FA K (2 + 2)) (k : archCompact K (2 + 2)), ∃ X m₁ m₂ t g u, (∀ U, u ∈ levOn (im w) U) ∧
        arc1 k * fin1 h = nn X * lv m₁ m₂ t * arc1 k * fin1 (ι₄ g) * fin1 u := by
  intro K _ _ r w ι hw hι h k
  obtain ⟨-, -, hoff, hdec, hcomm, -⟩ := (embEx (K := K) (2 + 2) w hw).2 ι hι
  obtain ⟨b, hb, c, hc, e⟩ := exists_adelicBorel_mul_maxCompact (finEmb K (2 + 2) h)
  have hh : h = (AdelicGLn.prodEquiv K (2 + 2) b).2 * (AdelicGLn.prodEquiv K (2 + 2) c).2 := by
    have := congrArg (fun x => (AdelicGLn.prodEquiv K (2 + 2) x).2) e
    simpa [prodEquiv_finEmb, map_mul] using this
  obtain ⟨g₁, b', eb, hb'⟩ := hdec (AdelicGLn.prodEquiv K (2 + 2) b).2
  obtain ⟨g₂, u, eu, hu⟩ := hdec (AdelicGLn.prodEquiv K (2 + 2) c).2
  have hcb : ι g₂ * b' = b' * ι g₂ := (hcomm g₂ b' hb').eq
  have hh2 : h = ι (g₁ * g₂) * b' * u := by
    rw [hh, eb, eu, map_mul, mul_assoc (ι g₁), ← mul_assoc b', ← hcb]
    simp only [mul_assoc]

  have hb1 : ∀ v ∉ im w, GM.cf v b' = finAt v b := fun v hv => by
    rw [← cf_snd, eb, cf_mul, hoff g₁ v hv, one_mul]
  have hu1 : ∀ v ∉ im w, GM.cf v u = finAt v c := fun v hv => by
    rw [← cf_snd, eu, cf_mul, hoff g₂ v hv, one_mul]
  have hup : finEmb K (2 + 2) b' ∈ adelicBorel := by
    refine fin_borel b' fun v i j hij => ?_
    by_cases hv : v ∈ im w
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hb' l]
      exact Matrix.one_apply_ne hij.ne'
    · rw [hb1 v hv]
      change (b i j).2 v = 0
      rw [mem_adelicBorel.1 hb hij]
      rfl
  have hs := proj_borel b' hup
  obtain ⟨X, m₁, m₂, t, hX⟩ := par_of_low (fin1 b') (low_of_borel hs) (low_of_borel (inv_mem hs))
  refine ⟨X, m₁, m₂, t, g₁ * g₂, u, fun U v => ?_, ?_⟩
  · by_cases hv : v ∈ im w
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      beta_reduce
      rw [if_pos hv]
      change GM.cf (w l) u ∈ U (w l)
      rw [hu l]
      exact one_mem _
    · beta_reduce
      rw [if_neg hv]
      change GM.cf v u ∈ _
      rw [hu1 v hv]
      exact hc.2 v
  · have c1 : Commute (arc1 k) (fin1 b') := (levLaws (K := K) (2 + 2) (im w)).2.2.1 k b'
    have c2 : fin1 (ι (g₁ * g₂)) * fin1 b' = fin1 b' * fin1 (ι (g₁ * g₂)) := by
      rw [← map_mul, ← map_mul, (hcomm (g₁ * g₂) b' hb').eq]
    have e3 : fin1 (ι (g₁ * g₂) * b' * u) = fin1 (ι (g₁ * g₂)) * fin1 b' * fin1 u :=
      (map_mul _ _ _).trans (congrArg (· * fin1 u) (map_mul _ _ _))
    rw [← hX, hh2, e3, c2, ← c1.eq]
    simp only [mul_assoc]
end
