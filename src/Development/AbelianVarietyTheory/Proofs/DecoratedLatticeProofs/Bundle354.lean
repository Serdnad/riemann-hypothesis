module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle337
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc




namespace GlobalTheory.InertFrameLoc

theorem cA_algebraMap_place (D : D7) (ε : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) ε) = algebraMap (AF D.host.F) (AE D) ε := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  show sigR _ _ _ = _
  simp [sigR]

theorem placeIdem_mul {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (a : AE D) : algebraMap (AF D.host.F) (AE D) ε * a = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v a) := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hα : α = singleFin v 1 := FiniteAdeleRing.ext _ fun u => by
    change evalV D.host.F u α = evalV D.host.F u (singleFin v 1)
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self, h1]
    · rw [evalV_singleFin_ne e, h0 u e]
  have h2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = GlobalTheory.EmbChart.tensAt D.host.E v 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply, hα, Algebra.TensorProduct.one_def, GlobalTheory.EmbChart.tensAt_tmul]
    rfl
  rw [h2, GlobalTheory.EmbChart.tensAt_mul_right, one_mul]

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem pair_mem_intL (S : HSp D) {s : Fin S.rank → D.host.E} (hs : s ∈ L0c D S)
    {z : Fin S.rank → w.adicCompletion D.host.E} (hz : z ∈ latAt w (frameLat S)) :
    ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * z m ∈
      Formalism.UG.intL (w.adicCompletion D.host.E) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx

    simp only [← map_mul, ← map_sum]
    have hX : ∑ k, s k • S.frame k ∈ S.L0 := hs
    have hY : ∑ m, y m • S.frame m ∈ S.L0 := (mem_frameLat S y).1 hy
    have hd : ∑ m, y m • S.frame m ∈ Formalism.HermitianLatticesTheory.dual S.hT S.L0 := by rw [S.baseLattice_isUnimodular]; exact hY
    have h1 := Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 hd (∑ k, s k • S.frame k)) hX
    rw [Submodule.mem_comap] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    have e : ∑ m, (∑ k, star (s k) * S.gram k m) * y m = algebraMap (𝓞 D.host.E) D.host.E o := by
      rw [ho]

      simp only [LinearMap.restrictScalars_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [starRingEnd_apply, RingHom.id_apply]
      ring
    rw [e]
    rw [GlobalTheory.InertLoc.mem_intL, GlobalTheory.Idele.valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one w o
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact add_mem hx hy
  | smul c x _ hx =>
    have e : ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * (c • x) m =
        (c : w.adicCompletion D.host.E) * ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * x m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Pi.smul_apply]
      show _ * ((c : w.adicCompletion D.host.E) * x m) = _
      ring
    rw [e]
    exact mul_mem (show Valued.v (c : w.adicCompletion D.host.E) ≤ 1 from c.2) hx

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

def piW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (compFin D.host.F D.host.E v)

theorem secW_piW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (a : AE D) :
    secW hw h (piW hw h a) = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v a) := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm
    (GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a))) = _
  rw [RingEquiv.symm_apply_apply]

theorem piW_tmul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
    (m : D.host.E) : piW hw h (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      complMap h (evalV D.host.F v α) * algebraMap D.host.E (w.adicCompletion D.host.E) m := rfl

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem latO_frame_int (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {k : w.adicCompletion D.host.E} {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)}
    {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)} (hk : GlobalTheory.InertLoc.IsGen D w k)
    (haS : IsFrameAt w (frameLat S) aS) (haT : IsFrameAt w (frameLat T) aT) {u : WO S T}
    (hu : u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) (i : Fin T.rank) (j : Fin S.rank) :
    (k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1)) i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  induction hu using AddSubgroup.closure_induction generalizing i j with
  | mem x hx =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hx
    let c0 := complMap h (evalV D.host.F v α)
    let t' : Fin T.rank → w.adicCompletion D.host.E := fun l => algebraMap D.host.E _ (t l)
    let r : Fin S.rank → w.adicCompletion D.host.E :=
      fun m => algebraMap D.host.E _ (∑ l, star (s l) * S.gram l m)
    have e1 : Matrix.map (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j) :
        WO S T) (piW hw h) = (c0 * algebraMap D.host.E _ a) • vecMulVec t' r := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, piW_tmul, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
        map_mul, map_mul]
      simp only [mul_assoc]
      rfl
    rw [e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, smul_smul, Matrix.smul_apply,
      vecMulVec_apply, smul_eq_mul]
    have h1 : c0 ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := complMap_mem h (hα v)
    have h2 : k⁻¹ * algebraMap D.host.E _ a ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := hk.2.2 a ha
    have h3 : ((aT⁻¹).1 *ᵥ t') i ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
      refine (haT ((aT⁻¹).1 *ᵥ t')).2 ?_ i
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨t, (mem_frameLat T t).2 ht, rfl⟩
    have h4 : (r ᵥ* aS.1) j ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
      have hcol : (fun m => aS.1 m j) ∈ latAt w (frameLat S) := by
        have := (haS (Pi.single j 1)).1 fun l => by
          by_cases e : l = j
          · subst e; simp
          · simp [e]
        rwa [Matrix.mulVec_single_one] at this
      show ∑ m, r m * aS.1 m j ∈ _
      exact pair_mem_intL S hs hcol
    have e2 : k⁻¹ * (c0 * algebraMap D.host.E (w.adicCompletion D.host.E) a) * (((aT⁻¹).1 *ᵥ t') i * (r ᵥ* aS.1) j) =
        c0 * (k⁻¹ * algebraMap D.host.E _ a) * (((aT⁻¹).1 *ᵥ t') i * (r ᵥ* aS.1) j) := by ring
    rw [e2]
    exact mul_mem (mul_mem h1 h2) (mul_mem h3 h4)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, smul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.add_apply]
    exact add_mem (hx i j) (hy i j)
  | neg x _ hx =>
    rw [Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.neg_apply]
    exact neg_mem (hx i j)

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem exists_uPt_of_half : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ e e', IsPrimeIdem w e e' → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → ∃ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) ∧ uPt hw h k aS aT x = u := by
  intro D v w hw h S T k aS aT hk haS haT e e' he u hu hhalf
  obtain ⟨ε, hε, -, -, hee⟩ := GlobalTheory.VacFixInert.inert_data (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw h)
  obtain ⟨rfl, -⟩ := hee e e' he
  rw [h] at hε
  have hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
    rcases hhalf with h1 | h1
    · exact h1
    · rwa [cA_algebraMap_place] at h1
  have hent : ∀ i j, secW hw h (piW hw h (u i j)) = u i j := fun i j => by
    rw [secW_piW, ← placeIdem_mul hε, hh i j]
  refine ⟨k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1), fun i j => latO_frame_int hw h hk haS haT hu i j, ?_⟩
  have e1 : k • ((aT.1 * (k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1))) * (aS⁻¹).1) = u.map (piW hw h) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hk.1, one_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  ext i j
  rw [uPt, e1, Matrix.map_apply, Matrix.map_apply, hent]

end GlobalTheory.InertFrameLoc
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc




namespace GlobalTheory.InertFrameLoc

section Rigid

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem ringHom_eq_id_of_int (f : w.adicCompletion E →+* w.adicCompletion E)
    (h1 : ∀ x : E, f (algebraMap E _ x) = algebraMap E _ x)
    (h2 : ∀ z, Valued.v z ≤ 1 → Valued.v (f z) ≤ 1) : f = RingHom.id _ := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  set t : w.adicCompletion E := algebraMap E _ (a : E) with ht
  have hft : f t = t := h1 _
  have ht1 : Valued.v t < 1 := by
    rw [ht, GlobalTheory.Idele.valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha
  have htz : t ≠ 0 := by
    rw [ht, map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]
    exact ha0
  have key : ∀ (n : ℕ) z, Valued.v z ≤ Valued.v t ^ n → Valued.v (f z) ≤ Valued.v t ^ n := by
    intro n z hz
    have htn : t ^ n ≠ 0 := pow_ne_zero _ htz
    have hz' : z = t ^ n * (z / t ^ n) := by field_simp
    rw [hz', map_mul, map_pow, hft, Valuation.map_mul, Valuation.map_pow]
    refine mul_le_of_le_one_right' (h2 _ ?_)
    rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ hz zero_le'
  have hcont : Continuous f := by
    refine continuous_of_continuousAt_zero f (Metric.tendsto_nhds.2 fun ε hε => ?_)
    have h1' : ‖t‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 ht1
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε h1'
    have hne : Valued.v t ^ m ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 htz)
    filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := E) w (WithZero.log (Valued.v t ^ m))).mem_nhds
      (x := 0) (by simp)] with z hz
    rw [map_zero, dist_zero_right]
    refine (Valued.toNormedField.norm_le_iff.2 ?_).trans_lt ((norm_pow t m).trans_lt hm)
    rw [map_pow]
    refine key m z ?_
    have hz' : Valued.v z ≤ WithZero.exp (WithZero.log (Valued.v t ^ m)) := hz
    rwa [WithZero.exp_log hne] at hz'
  exact RingHom.coe_inj ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hcont continuous_id
    (funext fun x => h1 x))

end Rigid

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

section Cond

open GlobalTheory.EmbChart

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem tensAt_mul_tensAt (y y' : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    tensAt D.host.E v y * tensAt D.host.E v y' = tensAt D.host.E v (y * y') := by
  rw [tensAt_mul_right, compFin_tensAt]

theorem compFin_incA (x : D.host.E) :
    compFin D.host.F D.host.E v (incA D x) = (1 : Fv D.host.F v) ⊗ₜ[D.host.F] x := by
  show evFin D.host.F v 1 ⊗ₜ x = _
  rw [map_one]

theorem tensAt_one_mul_incA (x : D.host.E) :
    tensAt D.host.E v 1 * incA D x = tensAt D.host.E v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
  rw [tensAt_mul_right, one_mul, compFin_incA]

theorem secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z z' : w.adicCompletion D.host.E) : secW hw h (z * z') = secW hw h z * secW hw h z' := by
  show tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (z * z')) =
    tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) *
      tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z')
  rw [map_mul, tensAt_mul_tensAt]

theorem complEquiv_symm_algebraMap (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (x : D.host.E) : (GlobalTheory.LFun.InertChart.complEquiv hw h).symm (algebraMap D.host.E _ x) =
      (1 : Fv D.host.F v) ⊗ₜ[D.host.F] x := by
  rw [RingEquiv.symm_apply_eq]
  show _ = GlobalTheory.LFun.toCompl h ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x)
  rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

theorem isPrimeIdem_tensAt (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) :
    IsPrimeIdem w (tensAt D.host.E v 1) (tensAt D.host.E v 1) := by
  refine Or.inr ⟨rfl, ⟨v, atPlace v 1, ⟨GlobalTheory.AdelicU.singleFin v 1, rfl, GlobalTheory.AdelicU.evalV_singleFin_self v 1,
    fun u hu => GlobalTheory.AdelicU.evalV_singleFin_ne hu 1⟩, rfl⟩, fun x hx => ?_⟩
  rw [tensAt_one_mul_incA, finPart_tensAt_mem_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h, GlobalTheory.LFun.toCompl_tmul,
    map_one, one_mul]
  show _ ↔ ¬ (Valued.v (algebraMap D.host.E (w.adicCompletion D.host.E) (x : D.host.E)⁻¹) ≤ 1)
  have h0 : w.valuation D.host.E (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [GlobalTheory.Idele.valued_algebraMap, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 h0),
    HeightOneSpectrum.valuation_lt_one_iff_mem]

end Cond

theorem thW_cond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsStdChar D ψ (-1) → IsConjAt D.sp.cm.sig h c → IsUnramInv ϖ c (qV D.host.F v) → GlobalTheory.InertLoc.IsGen D w k → ∀ z, (∀ u ∈ Formalism.UG.intL (w.adicCompletion D.host.E), thW ψ hw h (k * c k) (z * u) = 1) ↔ z ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  intro D ψ v w hw h c ϖ k hψ hconj hU hk z
  have he := isPrimeIdem_tensAt (D := D) hw h
  obtain ⟨ϖ0, σ0, q0, π0, hU0, -, hch, hV⟩ := GlobalTheory.InertLoc.exists_chart (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw h) he
  have hsec_e : ∀ y, GlobalTheory.EmbChart.tensAt D.host.E v 1 * secW hw h y = secW hw h y := fun y => by
    show GlobalTheory.EmbChart.tensAt D.host.E v 1 * GlobalTheory.EmbChart.tensAt D.host.E v _ = GlobalTheory.EmbChart.tensAt D.host.E v _
    rw [tensAt_mul_tensAt, one_mul]
  let f0 : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E :=
    { toFun := fun z => π0 (secW hw h z)
      map_one' := by
        show π0 (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm 1)) = 1
        rw [map_one]
        exact hch.pi_idem
      map_mul' := fun z z' => by
        show π0 (secW hw h (z * z')) = π0 (secW hw h z) * π0 (secW hw h z')
        rw [secW_mul, map_mul]
      map_zero' := by
        show π0 (secW hw h 0) = 0
        rw [map_zero, map_zero]
      map_add' := fun z z' => by
        show π0 (secW hw h (z + z')) = π0 (secW hw h z) + π0 (secW hw h z')
        rw [map_add (f := _), map_add (f := _)] }
  have hf0 : f0 = RingHom.id _ := ringHom_eq_id_of_int w f0 (fun x => by
      show π0 (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (algebraMap D.host.E _ x))) = _
      rw [complEquiv_symm_algebraMap, ← tensAt_one_mul_incA, map_mul, hch.pi_idem, one_mul, hch.2.2.2.1])
    (fun z hz => by
      refine (hch.2.2.2.2.2 (secW hw h z)).1 ?_
      rw [hsec_e]
      show finPart D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) ∈ intAE D
      rw [GlobalTheory.EmbChart.finPart_tensAt_mem_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h]
      show (GlobalTheory.LFun.InertChart.complEquiv hw h) ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) ∈ Ov D.host.E w
      rw [RingEquiv.apply_symm_apply]
      exact hz)
  have hpi : ∀ z, π0 (secW hw h z) = z := fun z => RingHom.congr_fun hf0 z
  have hsec : ∀ z, hch.sec z = secW hw h z := fun z =>
    hch.ext (hch.mul_sec z) (hsec_e z) (by rw [hch.pi_sec, hpi])
  have hσc : ∀ x : D.host.E, σ0 (algebraMap D.host.E _ x) = c (algebraMap D.host.E _ x) := fun x => by
    calc σ0 (algebraMap D.host.E _ x) = σ0 (π0 (incA D x)) := by rw [hch.2.2.2.1]
      _ = π0 (cA D (incA D x)) := (hch.2.2.2.2.1 _).symm
      _ = algebraMap D.host.E _ (D.sp.cm.sig x) := hch.2.2.2.1 (D.sp.cm.sig x)
      _ = c (algebraMap D.host.E _ x) := (GlobalTheory.LFun.InertChart.conj_algebraMap hconj x).symm
  have hg := ringHom_eq_id_of_int w (c.comp σ0) (fun x => by
      rw [RingHom.comp_apply, hσc, hU.1])
    (fun z hz => by
      rw [RingHom.comp_apply, hU.2.1, hU0.2.1]
      exact hz)
  have hσ : ∀ z, σ0 z = c z := fun z => by
    have h1 : c (σ0 z) = z := RingHom.congr_fun hg z
    calc σ0 z = c (c (σ0 z)) := (hU.1 _).symm
      _ = c z := by rw [h1]
  have hth : ∀ z, GlobalTheory.InertLoc.th ψ hch k z = thW ψ hw h (k * c k) z := fun z => by
    rw [GlobalTheory.InertLoc.th_apply, thW_apply, hσ, hsec]
  obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
  have hi : 0 < D.sp.X'.rank := by
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Formalism.BasicNotions.Ranks.rankX', Formalism.BasicNotions.Ranks.r]
    omega
  have := GlobalTheory.InertLoc.th_cond hψ hch hU0.2.1 hβ ⟨0, hi⟩ hk z
  simpa only [hth] using this

end GlobalTheory.InertFrameLoc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section
namespace GlobalTheory.LocOm

theorem exists_integral_multiplier {k : Type} [Field k] [ValuativeRel k] (a : k) :
    ∃ b : k, b ≠ 0 ∧ b ∈ 𝒪[k] ∧ b * a ∈ 𝒪[k] := by
  by_cases ha : a ∈ 𝒪[k]
  · exact ⟨1, one_ne_zero, Subring.one_mem _, by simpa using ha⟩
  · have ha0 : a ≠ 0 := by rintro rfl; exact ha (Subring.zero_mem _)
    refine ⟨a⁻¹, inv_ne_zero ha0, ?_, by simp [ha0, Subring.one_mem]⟩
    rw [Valuation.mem_integer_iff] at ha ⊢
    rw [map_inv₀]
    push_neg at ha
    exact inv_le_one_of_one_le₀ ha.le

theorem exists_common_integral_multiplier {k : Type} [Field k] [ValuativeRel k]
    {ι : Type} [Fintype ι] (f : ι → k) :
    ∃ c : k, c ≠ 0 ∧ c ∈ 𝒪[k] ∧ ∀ i, c * f i ∈ 𝒪[k] := by
  classical
  choose b hb0 hbO hbf using fun i => exists_integral_multiplier (f i)
  refine ⟨∏ i, b i, Finset.prod_ne_zero_iff.mpr fun i _ => hb0 i,
    Subring.prod_mem _ fun i _ => hbO i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i), mul_comm (b i), mul_assoc]
  exact Subring.mul_mem _ (Subring.prod_mem _ fun j _ => hbO j) (hbf i)

theorem enl_scalar_denominator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k), ∃ c : kˣ, ∀ zk : GL Y k, (zk : Matrix Y Y k) = (c : k) • (1 : Matrix Y Y k) → Enl gk (hk * zk⁻¹) ∧ Enl (1 : GL Y' k) zk⁻¹ := by
  intro k _ _ _ _ Y Y' _ _ _ _ gk hk
  obtain ⟨c, hc0, hcO, hc⟩ := exists_common_integral_multiplier
    (fun p : Y × Y × Y' × Y' => (↑(hk⁻¹) : Matrix Y Y k) p.1 p.2.1 * (↑gk : Matrix Y' Y' k) p.2.2.1 p.2.2.2)
  refine ⟨Units.mk0 c hc0, fun zk hz => ⟨?_, ?_⟩⟩
  · intro x hx r q
    have : ((↑((hk * zk⁻¹)⁻¹) : Matrix Y Y k)) = c • (↑(hk⁻¹) : Matrix Y Y k) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hz]
      simp
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Subring.sum_mem _ fun t _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Subring.sum_mem _ fun s _ => ?_
    have h1 := hc (r, s, t, q)
    have h2 := hx s t
    simp only at h1
    have : c * ((↑(hk⁻¹) : Matrix Y Y k) r s * x s t * (↑gk : Matrix Y' Y' k) t q) =
      (c * ((↑(hk⁻¹) : Matrix Y Y k) r s * (↑gk : Matrix Y' Y' k) t q)) * x s t := by ring
    rw [this]
    exact Subring.mul_mem _ h1 h2
  · intro x hx r q
    rw [inv_inv, hz]
    simp only [Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      smul_eq_mul, Units.val_mk0]
    exact Subring.mul_mem _ hcO (hx r q)

end GlobalTheory.LocOm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.real_intertwiner_values_kFinite : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ P v, It P v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) := by
  first | exact @GlobalTheory.ItKFin.itKFin | exact GlobalTheory.ItKFin.itKFin | (intros; apply GlobalTheory.ItKFin.itKFin <;> assumption)
end
