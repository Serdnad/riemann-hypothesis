module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle025
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLSeriesContinuation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinTranslate

open GlobalTheory.WeilVacMove

theorem eq_one_of_pow_near {z : ℂ} (hz : ‖z‖ = 1) (h : ∀ k : ℕ, ‖z ^ k - 1‖ < 1) : z = 1 := by
  apply GlobalTheory.IrredSB.eq_one_of_forall_pow <;> assumption

theorem eventually_fin_eq_one {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∀ᶠ c : Af F in 𝓝 0, ψ (pairA F 0 c) = 1 := by
  have hp : Continuous fun α : Af F => pairA F 0 α := continuous_const.prodMk continuous_id
  have hc : Continuous fun α : Af F => ‖ψ (pairA F 0 α) - 1‖ := ((hψ.1.comp hp).sub continuous_const).norm
  have h0 : ‖ψ (pairA F 0 0) - 1‖ < 1 := by
    have : pairA F 0 0 = 0 := rfl
    rw [this, AddChar.map_zero_eq_one, sub_self, norm_zero]
    exact one_pos
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F {α | ‖ψ (pairA F 0 α) - 1‖ < 1}
    ((isOpen_lt hc continuous_const).mem_nhds h0)
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  refine eq_one_of_pow_near (hψ.2.1 _) fun k => ?_
  have e : pairA F 0 (N • k • a) = k • pairA F 0 (N • a) :=
    Prod.ext (smul_zero k).symm (smul_comm N k a)
  have h1 : ‖ψ (pairA F 0 (N • k • a)) - 1‖ < 1 := h (k • a) fun v => nsmul_mem (ha v) k
  rwa [e, AddChar.map_nsmul_eq_pow] at h1

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def annSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : WO S T) : AddSubgroup (WO S T) where
  carrier := {u | ψ (symplOH S T u a) = 1 ∧ ψ (symplOH S T a u) = 1}
  zero_mem' := ⟨by rw [symplOH_zero_left, AddChar.map_zero_eq_one],
    by rw [symplOH_zero_right, AddChar.map_zero_eq_one]⟩
  add_mem' hx hy := ⟨by rw [symplOH_add_left, AddChar.map_add_eq_mul, hx.1, hy.1, one_mul],
    by rw [symplOH_add_right, AddChar.map_add_eq_mul, hx.2, hy.2, one_mul]⟩
  neg_mem' {x} hx := by
    constructor
    · have : ψ (symplOH S T (-x + x) a) = 1 := by rw [neg_add_cancel, symplOH_zero_left, AddChar.map_zero_eq_one]
      rwa [symplOH_add_left, AddChar.map_add_eq_mul, hx.1, mul_one] at this
    · have : ψ (symplOH S T a (-x + x)) = 1 := by rw [neg_add_cancel, symplOH_zero_right, AddChar.map_zero_eq_one]
      rwa [symplOH_add_right, AddChar.map_add_eq_mul, hx.2, mul_one] at this

theorem isOpen_annSub (hψ : IsCharAF D.host.F ψ) {a : WO S T} (ha : a.map (infPart D) = 0) :
    IsOpen (annSub ψ S T a : Set (WO S T)) := by
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  refine (annSub ψ S T a).isOpen_of_mem_nhds (g := 0) ?_
  have key : ∀ φ : WO S T → AF D.host.F, Continuous φ → φ 0 = 0 → (∀ u, fstA D.host.F (φ u) = 0) →
      ∀ᶠ u in 𝓝 (0 : WO S T), ψ (φ u) = 1 := by
    intro φ hφ h0 h1
    have hc : Continuous fun u => sndA D.host.F (φ u) := continuous_snd.comp hφ
    have ht : Filter.Tendsto (fun u => sndA D.host.F (φ u)) (𝓝 0) (𝓝 0) :=
      hc.tendsto' 0 0 (by rw [h0, map_zero])
    refine (ht.eventually (eventually_fin_eq_one hψ)).mono fun u hu => ?_
    have e : pairA D.host.F 0 (sndA D.host.F (φ u)) = φ u := Prod.ext (h1 u).symm rfl
    rwa [e] at hu
  exact (key (fun u => symplOH S T u a) (continuous_symplOH S T continuous_id continuous_const)
      (symplOH_zero_left S T a) fun u => fst_symplOH S T u a (Or.inr ha)).and
    (key (fun u => symplOH S T a u) (continuous_symplOH S T continuous_const continuous_id)
      (symplOH_zero_right S T a) fun u => fst_symplOH S T a u (Or.inl ha))

theorem isTheta_heisO_fin (hψ : IsCharAF D.host.F ψ) {a : WO S T} (ha : a.map (infPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (heisO ψ S T a f) := {
  quasi := heisO_quasi ψ S T a f hf.quasi
  level := by
    obtain ⟨U, hU, h1⟩ := hf.level
    refine ⟨U ⊓ annSub ψ S T a, hU.inter (isOpen_annSub hψ ha), fun u hu h0 => ?_⟩
    have h2 : ψ (symplOH S T u a) = 1 ∧ ψ (symplOH S T a u) = 1 := hu.2
    conv_rhs => rw [← h1 u hu.1 h0]
    rw [heisO_heisO, heisO_heisO, h2.1, h2.2, add_comm]
  cont := by
    haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
    haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
    exact (hψ.1.comp (continuous_symplOH S T continuous_id continuous_const)).mul
      (hf.cont.comp (continuous_id.add continuous_const))
  smooth k L h1 h2 w := by
    have e : (fun t => heisO ψ S T a f (w + L t)) = fun t => ψ (symplOH S T w a) * f (w + a + L t) := by
      funext t
      rw [heisO, symplOH_add_left, (symplOH_fin_real S T a (L t) ha (h2 t)).2, add_zero, add_right_comm]
    rw [e]
    exact contDiff_const.mul (hf.smooth k L h1 h2 (w + a)) }

theorem isTheta_sum_heisO_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ), (∀ i ∈ s, (a i).map (infPart D) = 0) → IsThetaFunO ψ S T (∑ i ∈ s, c i • heisO ψ S T (a i) f) := by
  intro D ψ S T hψ f hf ι s a c ha
  exact Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => isTheta_add) isTheta_zero
    fun i hi => isTheta_smul _ (isTheta_heisO_fin hψ (ha i hi) hf)

end GlobalTheory.FinTranslate

end
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isKum_of_finrank_prime (p : ℕ) (F E : Type) [Field F] [Field E] [Algebra F E]
    [IsGalois F E] (ζ : F) (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hr : Module.finrank F E = p) :
    ∃ (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (hr ▸ hp.pos)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (E ≃ₐ[F] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hr])
  have hK : (primitiveRoots (Module.finrank F E) F).Nonempty :=
    ⟨ζ, by rw [hr, mem_primitiveRoots hp.pos]; exact hζ⟩
  obtain ⟨θ, ⟨δ, hδ⟩, hθ⟩ := exists_root_adjoin_eq_top_of_isCyclic F E hK
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top hδ.symm hθ
  rw [hr] at hirr hδ
  have hmin : (X ^ p - C δ : F[X]) = minpoly F θ :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hδ]) (monic_X_pow_sub_C _ hp.ne_zero)
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (K := F) (L := E) (x := algebraMap F E ζ * θ)
    (y := θ) (Algebra.IsAlgebraic.isAlgebraic θ) (by
      rw [← hmin]
      rw [map_sub, map_pow, aeval_X, aeval_C, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul,
        hδ, sub_self])
  refine ⟨δ, θ, σ, hp, hζ, (X_pow_sub_C_irreducible_iff_of_prime hp).1 hirr, hδ.symm, hσ, ?_⟩
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic θ), hθ, IntermediateField.top_toSubalgebra]

theorem np_of_finrank_prime_of_isPrimitiveRoot : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [IsGalois F E] (ζ : F), p.Prime → IsPrimitiveRoot ζ p → Module.finrank F E = p → NP F E := by
  intro p F E _ _ _ _ _ _ _ ζ hp hζ hr x hx hloc
  classical
  obtain ⟨δ, θ, σ, hk⟩ := exists_isKum_of_finrank_prime p F E ζ hp hζ hr
  have hδ0 : δ ≠ 0 := fun h => hk.nonpow 0 (by rw [h, zero_pow hp.ne_zero])
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F {Units.mk0 δ hδ0, Units.mk0 x hx} ∅
  obtain ⟨S, hS, hadm⟩ := (exists_admissiblePlaces_superset_and_mono p F hp.pos).1 S₁
  have hfin : Units.mk0 x hx ∈ finNorm p F δ S := by
    simp only [finNorm, Subgroup.mem_iInf]
    intro v _
    exact GlobalTheory.T.mem_unitsLocalKummerNorms_of_baseChange_norm p F E (v.adicCompletion F) ζ δ θ σ hk (Units.mk0 x hx) (hloc.1 v)
  have hx' := GlobalTheory.T.sUnit_mem_kummerNorms_of_local_norms p F ζ (Units.mk0 δ hδ0) S hp hζ hadm (hS₁ S hS _ (by simp))
    hk.nonpow (Units.mk0 x hx) (hS₁ S hS _ (by simp)) hfin
  obtain ⟨y, hy⟩ := (mem_kNorm p (RingHom.id F) δ _).1 hx'
  obtain ⟨-, -, -, -, -, ⟨e⟩, -⟩ := kummer_galois p F E ζ δ θ σ hk
  refine ⟨e.symm y, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv]
  exact hy

end GlobalTheory.CNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem _root_.GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x y : WO S T), (x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) → ψ (symplOH S T x y) = Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  first | exact @GlobalTheory.OrientedChar.char_symplOH | exact GlobalTheory.OrientedChar.char_symplOH | (intros; apply GlobalTheory.OrientedChar.char_symplOH <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrientedRealForm

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem map_inv_of_det_ne {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E) (h : G.det ≠ 0) :
    (G.map φ)⁻¹ = G⁻¹.map φ := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.2 h), Matrix.map_one _ φ.map_zero φ.map_one]

theorem trace_eq_sum {m n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (P * yᴴ * Q * x).trace = ∑ a, ∑ b, ∑ e, ∑ d, P a b * starRingEnd ℂ (y e b) * Q e d * x d a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  rfl

variable {D : D7}

theorem formAt_eq (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    formAt S T τ x y =
      2 * (tauE D τ D.host.xi0 * ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x).trace).re := by
  rw [trace_eq_sum]
  unfold formAt gramAt
  rw [map_inv_of_det_ne _ _ (gram_det_ne S)]
  rfl

theorem realPlace_imaginaryGenerator_re_eq_zero (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  have h := tauE_star τ D.host.xi0
  rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg] at h
  have h2 := congrArg Complex.re h
  rw [Complex.neg_re, Complex.conj_re] at h2
  linarith

theorem cplxO_add {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (x + y) = cplxO s t x + cplxO s t y := by
  unfold cplxO
  rw [Matrix.mul_add, Matrix.add_mul, smul_add]

theorem cplxO_smul {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]

def jO (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) : RW T S →ₗ[ℝ] RW T S where
  toFun z := fun τ => cplxO (sS τ) (sT τ) (z τ)
  map_add' x y := by funext τ; exact cplxO_add _ _ _ _
  map_smul' c x := by funext τ; exact cplxO_smul _ _ c _

theorem exists_real_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ (om : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S →ₗ[ℝ] ℝ) (J : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S), (∀ x y : WO S T, y.map (finPart D) = 0 → ψ (symplOH S T x y) = Complex.exp (-(Real.pi * Complex.I) * (om (GlobalTheory.FockCompare.piW θ T S x) (GlobalTheory.FockCompare.piW θ T S y) : ℝ))) ∧ (∀ z τ, J z τ = cplxO (sS τ) (sT τ) (z τ)) ∧ (∀ v, om v v = 0) ∧ (∀ v, J (J v) = -v) ∧ (∀ x y, om x (J y) = om y (J x)) ∧ ∀ v, v ≠ 0 → 0 < om v (J v) := by
  intro D ψ θ S T sS sT hψ hθ hS hT
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have key := fun τ => GlobalTheory.CartanTrace.cplxO_pos T.rank S.rank (gramAt D S τ) (sS τ) (gramAt D T τ) (sT τ) (tauE D τ D.host.xi0)
    (realPlace_imaginaryGenerator_re_eq_zero τ) (xi_zero_im_pos D τ) (hS τ) (hT τ)
  have hom : ∀ x y : RW T S, omO S T x y = ∑ τ, formAt S T τ (x τ) (y τ) := fun _ _ => rfl
  have hJ : ∀ (z : RW T S) τ, jO S T sS sT z τ = cplxO (sS τ) (sT τ) (z τ) := fun _ _ => rfl
  refine ⟨omO S T, jO S T sS sT, fun x y hy => ?_, hJ, omO_self h, fun v => ?_, fun x y => ?_, fun v hv => ?_⟩
  · rw [← psi_symplOH h hψ, h.iota_pi (V := T) (W := S) hy]
  · funext τ
    exact (key τ).2.1 (v τ)
  · rw [hom, hom]
    refine Finset.sum_congr rfl fun τ _ => ?_
    refine (formAt_eq S T τ _ _).trans (Eq.trans ?_ (formAt_eq S T τ _ _).symm)
    exact congrArg (2 * ·) ((key τ).2.2.1 (x τ) (y τ))
  · rw [hom]
    have hp : ∀ τ, v τ ≠ 0 → 0 < formAt S T τ (v τ) (jO S T sS sT v τ) := fun τ h0 =>
      lt_of_lt_of_eq (mul_pos two_pos ((key τ).2.2.2 (v τ) h0)) (formAt_eq S T τ _ _).symm
    obtain ⟨τ₀, h₀⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun τ _ => ?_) ⟨τ₀, Finset.mem_univ _, hp τ₀ h₀⟩
    by_cases h0 : v τ = 0
    · rw [h0]
      simp [formAt]
    · exact (hp τ h0).le

end GlobalTheory.OrientedRealForm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalHermitianRankOneLattice_selfDual : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ (n : ℕ) (s s' : Fin n → Fin S.rank → D.host.E), (∀ i, s i ∈ ΛS ∧ s' i ∈ ΛS) ∧ ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0) → ∀ ρ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ρ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔ ∀ ℓ ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)), ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T ρ ℓ) = n := by
  first | exact @GlobalTheory.LatVac.latRat_selfDual | exact GlobalTheory.LatVac.latRat_selfDual | (intros; apply GlobalTheory.LatVac.latRat_selfDual <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N → IsOpen {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - N • l).map (finPart D) = 0} := by
  first | exact @GlobalTheory.LatOpen.isOpen_nsmul_latO | exact GlobalTheory.LatOpen.isOpen_nsmul_latO | (intros; apply GlobalTheory.LatOpen.isOpen_nsmul_latO <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem two_le_absNorm_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  omega

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem one_sub_mul_natCast_cpow_neg_ne_zero {c : ℂ} (hc : ‖c‖ ≤ 1) {n : ℕ} (hn : 2 ≤ n)
    {s : ℂ} (hs : 0 < s.re) : 1 - c * (n : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : c * (n : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖(n : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < n)) (by linarith)
  have h3 := congrArg norm h1
  rw [norm_mul, norm_one] at h3
  nlinarith [norm_nonneg c, norm_nonneg ((n : ℂ) ^ (-s))]


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.idealCharacterL_continuation_ne_zero_one :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ)
    (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) →
    (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) →
    (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) →
    ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} →
    (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) →
    (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) →
    (∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1) → ∀ c : HeightOneSpectrum (𝓞 K) → ℂ,
    (∀ P, ‖c P‖ ≤ 1) → (∀ P, ¬ m ≤ P.asIdeal → c P = X P.asIdeal) →
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s | 0 < s.re} ∧ (∀ s : ℂ, 1 < s.re →
      L s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))) ∧ L 1 ≠ 0 := by
  intro K _ _ m X φ hm hXbot hXmul hXnorm hXzero hφmul hφsmul hφsmooth hφnorm hXφ hJ c hc hcX
  have hXtop : X ⊤ = 1 := by
    have h1 := hXnorm ⊤ top_ne_bot (top_sup_eq m)
    have h2 : X ⊤ = X ⊤ * X ⊤ := by rw [← hXmul, Ideal.top_mul]
    have h3 : X ⊤ ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
    exact mul_left_cancel₀ h3 (by rw [mul_one]; exact h2.symm)
  have hXle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · rw [hI, hXbot, norm_zero]
      exact zero_le_one
    by_cases hIm : I ⊔ m = ⊤
    · rw [hXnorm I hI hIm]
    · rw [hXzero I hIm, norm_zero]
      exact zero_le_one
  obtain ⟨Z, hZd, hZ, hZ1⟩ := _root_.GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hXbot hXmul hXnorm
    hXzero hφmul hφsmul hφsmooth hφnorm hXφ
  have hZ0 := hZ1 hJ
  let LX : ℂ → ℂ := dslope Z 1
  have hLXd : Differentiable ℂ LX := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd.differentiableOn
  have hLX : ∀ s : ℂ, 1 < s.re → LX s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [← _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hXbot hXtop hXmul hXle s hs]
    simp only [LX, dslope_of_ne _ hs1, slope_def_field, hZ s hs, hZ0, sub_zero]
    field_simp
  obtain ⟨Zζ, hZζd, hZζ⟩ := _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun P : HeightOneSpectrum (𝓞 K) =>
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-σ) :=
    fun σ hσ => ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2
  have hne : Nonempty (HeightOneSpectrum (𝓞 K)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩
  have hLX1 : LX 1 ≠ 0 := _root_.GlobalTheory.eulerProduct_ne_zero_one_of_entire (HeightOneSpectrum (𝓞 K))
    (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum
    (fun P => hXle _) hsum hne Zζ LX hZζd hLXd hZζ hLX
  have hfin : {P : HeightOneSpectrum (𝓞 K) | P.asIdeal ∣ m}.Finite := Ideal.finite_factors hm
  let S := hfin.toFinset
  have hmemS : ∀ P, P ∈ S ↔ m ≤ P.asIdeal := fun P => by simp [S, Ideal.dvd_iff_le]
  have hfac : ∀ (P : HeightOneSpectrum (𝓞 K)) (s : ℂ), 0 < s.re →
      1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 :=
    fun P s hs => one_sub_mul_natCast_cpow_neg_ne_zero (hc P) (two_le_absNorm_heightOneSpectrum P) hs
  let F : ℂ → ℂ := ∏ P ∈ S, fun s => (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  have hF : ∀ s, F s = ∏ P ∈ S, (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ :=
    fun s => by simp [F, Finset.prod_apply]
  refine ⟨fun s => LX s * F s, ?_, ?_, ?_⟩
  · apply hLXd.differentiableOn.mul
    apply DifferentiableOn.finsetProd
    intro P _
    refine DifferentiableOn.inv ?_ (fun s hs => hfac P s hs)
    refine DifferentiableOn.const_sub ?_ _
    refine DifferentiableOn.const_mul ?_ _
    intro s _
    refine DifferentiableAt.differentiableWithinAt ?_
    exact differentiableAt_id.neg.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (by have := two_le_absNorm_heightOneSpectrum P; omega)))
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    obtain ⟨hsa, -⟩ := (_root_.GlobalTheory.eulerProduct_eq_exp_and_pos (HeightOneSpectrum (𝓞 K))
      (fun P => Ideal.absNorm P.asIdeal) (fun P => X P.asIdeal) two_le_absNorm_heightOneSpectrum
      (fun P => hXle _) hsum).1 s hs
    have hsplit : ∀ P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) =
        -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)) +
        (if P ∈ S then -Complex.log (1 - c P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))
          else 0) := by
      intro P
      by_cases hP : P ∈ S
      · rw [if_pos hP]
        have hXP : X P.asIdeal = 0 := hXzero _ (by
          rw [sup_eq_left.mpr ((hmemS P).mp hP)]
          exact P.isPrime.ne_top)
        rw [hXP, zero_mul, sub_zero, Complex.log_one, neg_zero, zero_add]
      · rw [if_neg hP, add_zero, hcX P (fun h => hP ((hmemS P).mpr h))]
    show LX s * F s = _
    rw [tsum_congr hsplit, hsa.tsum_add (summable_of_ne_finset_zero (s := S) fun P hP => if_neg hP),
      tsum_eq_sum (s := S) (fun P hP => if_neg hP), Complex.exp_add, ← hLX s hs, hF,
      Complex.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [if_pos hP, Complex.exp_neg, Complex.exp_log (hfac P s hs0)]
  · show LX 1 * F 1 ≠ 0
    rw [hF]
    exact mul_ne_zero hLX1 (Finset.prod_ne_zero_iff.mpr fun P _ => inv_ne_zero (hfac P 1 (by simp)))

end GlobalTheory
end
