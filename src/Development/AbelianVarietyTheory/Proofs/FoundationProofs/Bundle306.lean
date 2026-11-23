module

public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.IntPtsUnitary

section General
variable {L : Type} [Field L] [TopologicalSpace L] [IsTopologicalRing L] {n : Type} [Fintype n] [DecidableEq n]

omit [TopologicalSpace L] [IsTopologicalRing L] in
theorem coe_GLint (O : Subring L) : (GLint n O : Set (GL n L)) =
    {g : GL n L | ∀ i j, (g : Matrix n n L) i j ∈ O} ∩ {g : GL n L | ∀ i j, ((g⁻¹ : GL n L) : Matrix n n L) i j ∈ O} :=
  Set.ext fun g => ⟨fun h => ⟨P.cartan_entries_of_mem O g h, P.cartan_entries_of_mem O _ (inv_mem h)⟩,
    fun h => P.cartan_mem_of_entries O g h.1 h.2⟩

theorem isOpen_GLint (O : Subring L) (hO : IsOpen (O : Set L)) : IsOpen (GLint n O : Set (GL n L)) := by
  rw [coe_GLint]
  simp only [Set.ofPred_forall]
  refine IsOpen.inter ?_ ?_
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (Units.continuous_val.matrix_elem i j)
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (Units.continuous_coe_inv.matrix_elem i j)

theorem isCompact_GLint [T2Space L] (O : Subring L) (hO : IsCompact (O : Set L)) :
    IsCompact (GLint n O : Set (GL n L)) := by
  have hM : IsCompact {A : Matrix n n L | ∀ i j, A i j ∈ O} := by
    have := isCompact_univ_pi fun _ : n => isCompact_univ_pi fun _ : n => hO
    have e : {A : Matrix n n L | ∀ i j, A i j ∈ O} =
        Set.univ.pi fun _ : n => Set.univ.pi fun _ : n => (O : Set L) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ this
  have := (Units.isClosedEmbedding_embedProduct (α := Matrix n n L)).isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))
  convert this using 1
  rw [coe_GLint]
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL n L) : Matrix n n L) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

end General

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isCompact_intL [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    IsCompact (intL L : Set L) := by
  obtain ⟨-, -, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  exact isCompact_iff_compactSpace.2 hp

theorem coe_KU (σ : L →+* L) (n : ℕ) :
    (KU σ n : Set (GU σ n)) = Subtype.val ⁻¹' (GLint (Fin n) (intL L) : Set (GL (Fin n) L)) := by
  ext g
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem isOpen_isCompact_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q →
      IsOpen (KU σ n : Set (GU σ n)) ∧ IsCompact (KU σ n : Set (GU σ n)) := by
  intro L _ _ _ ϖ σ q n h
  rw [coe_KU]
  refine ⟨(isOpen_GLint _ (Valued.isOpen_integer L)).preimage continuous_subtype_val, ?_⟩
  have hc : IsClosed (GU σ n : Set (GL (Fin n) L)) :=
    isClosed_eq (((Units.continuous_val.matrix_map (GlobalTheory.LGrp.continuous_of_unramInv h)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul Units.continuous_val) continuous_const
  exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_GLint _ (isCompact_intL h))

end GlobalTheory.LFun.IntPtsUnitary
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.OddThetaTranslate

theorem coordB_add (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (z x : VC D N N') : coordB D T b k (z + x) = coordB D T b k z + coordB D T b k x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coordB_nsmul (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (n : ℕ) (z : VC D N N') : coordB D T b k (n • z) = n * coordB D T b k z := by
  simp only [coordB, Pi.smul_apply, nsmul_eq_mul, mul_assoc, Finset.mul_sum]

theorem U_pullB (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ)
    (hP : ∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) =
      ∑ k, coordB D T b k z * (starRingEnd ℂ) (coordB D T b k w)) (x z : VC D N N') :
    U D T x (pullB D T b g) z = ∏ k, U1 T.abelian₂ (coordB D T b k x) g (coordB D T b k z) := by
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  simp only [coordB_add]
  congr 2
  rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem half_not_mem {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    w₁ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
  rw [AddSubgroup.mem_closure_pair]
  rintro ⟨m, n, hmn⟩
  have h0 := (LinearIndependent.pair_iff.1 h) (2 * (m : ℝ) - 1) (2 * (n : ℝ)) (by
    simp only [zsmul_eq_mul] at hmn
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * hmn)
  have h1 : (2 * m - 1 : ℤ) = 0 := by exact_mod_cast h0.1
  omega

theorem exp_neg_pi_I_even (m : ℤ) (a : ℝ) (ha : a = 2 * m) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (a : ℂ)) = 1 := by
  rw [ha, ← Complex.exp_int_mul_two_pi_mul_I (-m)]
  congr 1
  push_cast
  ring

theorem translate_level_four : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → Differentiable ℂ (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) ∧ ∃ t : VC D N N', 2 • t ∈ LaB D (tor0 D cc δ) b ∧ U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) 0 ≠ 0 ∧ ∀ ω ∈ LaB D (tor0 D cc δ) b, U D (tor0 D cc δ) (4 • ω) (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) = U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) := by
  intro D hG cc δ hC N N' r b hb
  obtain ⟨w₁, w₂, hli, hΛ⟩ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧
      lamOf D cc δ = AddSubgroup.closure {w₁, w₂} := by
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_periodPair_idealCurveLattice D cc δ hC
    refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
    ext z
    rw [hL, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp only [zsmul_eq_mul]
  obtain ⟨-, -, hP, hL, hbij⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  obtain ⟨⟨hd, -, -, hU⟩, hz, -⟩ := GlobalTheory.OddTheta.sgStar_laws (lamOf D cc δ) ⟨w₁, w₂, hli, hΛ⟩
  obtain ⟨-, -, hint, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (LaB D (tor0 D cc δ) b)
    (Or.inl ⟨r, b, hb, rfl⟩)
  have hw : w₁ ∈ lamOf D cc δ := by rw [hΛ]; exact AddSubgroup.subset_closure (by simp)
  have hw2 : w₁ / 2 ∉ lamOf D cc δ := by rw [hΛ]; exact half_not_mem hli
  obtain ⟨t, ht⟩ := hbij.2 (fun _ => w₁ / 2)
  have ht' : ∀ k, coordB D (tor0 D cc δ) b k t = w₁ / 2 := fun k => congrFun ht k
  have h2t : 2 • t ∈ LaB D (tor0 D cc δ) b := by
    rw [hL]
    intro k
    rw [coordB_nsmul, ht']
    have : ((2 : ℕ) : ℂ) * (w₁ / 2) = w₁ := by push_cast; ring
    rw [this]; exact hw
  refine ⟨?_, t, h2t, ?_, ?_⟩
  · have hc : ∀ k, Differentiable ℂ (coordB D (tor0 D cc δ) b k) := by
      intro k
      unfold coordB
      fun_prop
    unfold pullB
    fun_prop
  · simp only [U, zero_add, pullB, ht']
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => ?_) (Complex.exp_ne_zero _)
    exact fun h => hw2 ((hz _).1 h)
  · intro ω hω
    have hfix : U D (tor0 D cc δ) (4 • ω) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) =
        pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)) := by
      funext z
      rw [U_pullB D _ b _ hP]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hk := (hL ω).1 hω k
      have h4 : coordB D (tor0 D cc δ) b k (4 • ω) ∈ lamOf D cc δ :=
        (hL _).1 (AddSubgroup.nsmul_mem _ hω 4) k
      have h2 : coordB D (tor0 D cc δ) b k (4 • ω) / 2 ∈ lamOf D cc δ := by
        have : coordB D (tor0 D cc δ) b k (4 • ω) / 2 =
            coordB D (tor0 D cc δ) b k ω + coordB D (tor0 D cc δ) b k ω := by
          rw [coordB_nsmul]; push_cast; ring
        rw [this]; exact add_mem hk hk
      have := hU _ h4 (coordB D (tor0 D cc δ) b k z)
      rw [if_pos h2, one_mul] at this
      exact this
    obtain ⟨m, hm⟩ := hint ω hω _ h2t
    have ha : (Hf D (tor0 D cc δ) (4 • ω) t).im = 2 * m := by
      rw [Hf_nsmul_right] at hm
      rw [Hf_nsmul_left, ← hm]
      simp
      ring
    have hb' : (Hf D (tor0 D cc δ) t (4 • ω)).im = 2 * ((-m : ℤ) : ℝ) := by
      rw [Hf_im_swap, ha]; push_cast; ring
    funext z
    have e := U_U D (tor0 D cc δ) t (4 • ω) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) z
    rw [hfix, exp_neg_pi_I_even _ _ hb', one_mul] at e
    rw [U_U, exp_neg_pi_I_even _ _ ha, one_mul, e, add_comm]

end GlobalTheory.OddThetaTranslate
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem adicCompletion_exists_approx_lt (L : Type) [Field L] [NumberField L]
    (P : HeightOneSpectrum (𝓞 L)) (y c : P.adicCompletion L) (hc : c ≠ 0) :
    ∃ k : L, Valued.v (y - algebraMap L (P.adicCompletion L) k) < Valued.v c := by
  have ho : IsOpen {z : P.adicCompletion L | Valued.v (y - z) < Valued.v c} := by
    have h0 := (Valued.isOpen_ball (P.adicCompletion L)
      ((Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).restrict c)).preimage
        (continuous_sub_left y)
    simpa only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] using h0
  have hy : y ∈ {z : P.adicCompletion L | Valued.v (y - z) < Valued.v c} := by
    show Valued.v (y - y) < Valued.v c
    rw [sub_self, map_zero]
    exact (Valuation.pos_iff _).2 hc
  obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) (K := L)
    (v := P)).exists_mem_open ho ⟨y, hy⟩
  exact ⟨k, hk⟩

private lemma valued_v_algebraMap_adicCompletion_foundation (L : Type) [Field L] [NumberField L]
    (P : HeightOneSpectrum (𝓞 L)) (k : L) :
    Valued.v (algebraMap L (P.adicCompletion L) k) = P.valuation L k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) (v := P) k

theorem adicCompletion_exists_unit_approx (L : Type) [Field L] [NumberField L] (N : ℕ) (hN : 0 < N)
    (P : HeightOneSpectrum (𝓞 L)) (y : P.adicCompletion L) (hy : y ≠ 0) :
    ∃ k : Lˣ, Valued.v y = P.valuation L (k : L) ∧
      Valued.v (y - algebraMap L _ (k : L)) ≤ P.valuation L (N : L) * P.valuation L (k : L) ∧
      Valued.v (y - algebraMap L _ (k : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k : L) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer L
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hN0 : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hN1 : P.valuation L (N : L) ≤ 1 := by
    simpa using P.valuation_le_one (K := L) (N : 𝓞 L)
  have he1 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  set c := y * algebraMap L (P.adicCompletion L) ((N : L) * π) with hcdef
  have hc : c ≠ 0 := mul_ne_zero hy ((map_ne_zero _).2 (mul_ne_zero hN0 hπ0))
  obtain ⟨k₀, hk₀⟩ := adicCompletion_exists_approx_lt L P y c hc
  have hvc : Valued.v c = Valued.v y * (P.valuation L (N : L) * WithZero.exp (-1 : ℤ)) := by
    rw [hcdef, map_mul, valued_v_algebraMap_adicCompletion_foundation, map_mul, hπ]
  have hlt : Valued.v (y - algebraMap L _ k₀) < Valued.v y := by
    refine hk₀.trans_le ?_
    rw [hvc]
    exact mul_le_of_le_one_right' (mul_le_one' hN1 he1)
  have hyk : P.valuation L k₀ = Valued.v y := by
    rw [← valued_v_algebraMap_adicCompletion_foundation]
    apply Valuation.map_eq_of_sub_lt
    rwa [Valuation.map_sub_swap]
  have hk0 : k₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hyk
    exact hy ((Valuation.zero_iff _).1 hyk.symm)
  refine ⟨Units.mk0 k₀ hk0, ?_, ?_, ?_⟩
  · rw [Units.val_mk0, hyk]
  · rw [Units.val_mk0, hyk]
    refine (hk₀.trans_eq hvc).le.trans ?_
    rw [mul_comm (Valued.v y)]
    gcongr ?_ * _
    exact mul_le_of_le_one_right' he1
  · rw [Units.val_mk0, hyk]
    refine (hk₀.trans_eq hvc).le.trans ?_
    rw [mul_comm (Valued.v y)]
    gcongr ?_ * _
    exact mul_le_of_le_one_left' hN1

theorem finiteIdele_exists_local_approx :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N → ∀ x : (FiniteAdeleRing (𝓞 L) L)ˣ, ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (k : HeightOneSpectrum (𝓞 L) → Lˣ), (∀ P ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ P.valuation L (N : L) * P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k P : L)) ∧ ∀ P, P ∉ S → Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = 1 ∧ (N : 𝓞 L) ∉ P.asIdeal := by
  intro L _ _ N hN x
  obtain ⟨hx0, hx1⟩ := FiniteAdeleRing.isUnit_iff.1 x.isUnit
  choose k hk using fun P => adicCompletion_exists_unit_approx L N hN P _ (hx0 P)
  have hN0 : (N : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h2 : {P : HeightOneSpectrum (𝓞 L) | P.asIdeal ∣ Ideal.span {(N : 𝓞 L)}}.Finite :=
    Ideal.finite_factors (by simpa using hN0)
  have hfin := (Filter.eventually_cofinite.1 hx1).union h2
  refine ⟨hfin.toFinset, k, fun P _ => hk P, fun P hP => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hP
  obtain ⟨hP1, hP2⟩ := hP
  simp only [Set.mem_ofPred_eq, not_not] at hP1 hP2
  exact ⟨hP1, fun hmem => hP2 (Ideal.dvd_span_singleton.2 hmem)⟩

end GlobalTheory
end
