module

public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.StepTransl
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoExt
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle134
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle136
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameCont
open Matrix

theorem gram_det_isUnit {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) :
    IsUnit S.gram.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ v : Fin S.rank → E, S.gram *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h0 : ∑ j, v j • S.frame j = 0 := by
      apply S.nondeg.2
      intro x
      rw [← S.frame.sum_repr x]

      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at hi
      calc _ = (starRingEnd E) (S.frame.repr x i) * ∑ j, S.hT (S.frame i) (S.frame j) * v j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hi, mul_zero]
    funext j
    exact Fintype.linearIndependent_iff.1 S.frame.linearIndependent v h0 j
  intro a b hab
  have := key (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
  exact sub_eq_zero.1 this

theorem continuous_of_parts {A T m : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace T] [Fintype m] [DecidableEq m] (σ : A →+* A) (hσ : Continuous σ) (e : A)
    (J : Matrix m m A) (hJ : IsUnit J.det) (M N : T → Matrix m m A)
    (hU : ∀ t, Formalism.UG.cT σ (N t) * J * N t = J) (hNM : ∀ t, N t * M t = 1)
    (hs : ∀ t i j, (e + σ e) * (M t - 1) i j = (M t - 1) i j)
    (hM : Continuous fun t => e • M t) (hN : Continuous fun t => e • N t) : Continuous M := by
  have hc : ∀ t, σ e • M t = J⁻¹ * Formalism.UG.cT σ (e • N t) * J := by
    intro t
    have h1 : J * M t = Formalism.UG.cT σ (N t) * J := by
      calc J * M t = Formalism.UG.cT σ (N t) * J * N t * M t := by rw [hU]
        _ = Formalism.UG.cT σ (N t) * J := by rw [Matrix.mul_assoc _ (N t) (M t), hNM, Matrix.mul_one]
    have h2 : Formalism.UG.cT σ (e • N t) = σ e • Formalism.UG.cT σ (N t) := by
      ext a b; simp [Formalism.UG.cT]
    rw [h2, Matrix.mul_assoc, Matrix.smul_mul, ← h1, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
  have hC : Continuous fun t => σ e • M t := by
    simp only [hc]
    exact (continuous_const.matrix_mul (hN.matrix_map hσ).matrix_transpose).matrix_mul continuous_const
  have hsum : M = fun t => (1 - (e + σ e) • (1 : Matrix m m A)) + (e • M t + σ e • M t) := by
    funext t
    ext i j
    have h := hs t i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
    linear_combination -h
  rw [hsum]
  exact continuous_const.add (hM.add hC)

theorem continuous_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  have h := IsModuleTopology.continuous_of_linearMap (R := R) (LinearMap.baseChange R σ.toLinearMap)
  refine h.congr fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem unitary_mt {D : D7} {S : HSp D} (x : GA D S) :
    Formalism.UG.cT (cA D) (mt S x) * S.gram.map (incA D) * mt S x = S.gram.map (incA D) := (PI.FT.toHR x).2

theorem mt_inv_mul {D : D7} {S : HSp D} (x : GA D S) : mt S x⁻¹ * mt S x = 1 := by
  show (matHom S x⁻¹).val * (matHom S x).val = 1
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem gram_map_det_isUnit {D : D7} (S : HSp D) : IsUnit (S.gram.map (incA D)).det := by
  have h0 := (gram_det_isUnit S).map (incA D)
  rw [RingHom.map_det] at h0
  exact h0

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem e_mul_entry (β : Frame p S n) (g : GL n k) (i j : Fin S.rank) :
    p.e * mt S (β.gl g) i j = p.sec ((β.b * g.val * β.b') i j) := by
  rw [← p.sec_pr, ← β.gl_mat g]; rfl

theorem continuous_e_smul (β : Frame p S n) : Continuous fun g : GL n k => p.e • mt S (β.gl g) := by
  refine continuous_matrix fun i j => ?_
  refine (p.cont_sec.comp (((continuous_const.matrix_mul
    (Units.continuous_val (M := Matrix n n k))).matrix_mul continuous_const).matrix_elem i j)).congr
      fun g => (e_mul_entry β g i j).symm

theorem continuous_mt (β : Frame p S n) : Continuous fun g : GL n k => mt S (β.gl g) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  refine continuous_of_parts (cA D) (continuous_sigR _ _) p.e (S.gram.map (incA D)) (gram_map_det_isUnit S)
    (fun g => mt S (β.gl g)) (fun g => mt S (β.gl g⁻¹)) (fun g => unitary_mt _) (fun g => ?_)
    (fun g => β.gl_supp g) (continuous_e_smul β) ((continuous_e_smul β).comp continuous_inv)
  show mt S (β.gl g⁻¹) * mt S (β.gl g) = 1
  rw [map_inv]
  exact mt_inv_mul _

theorem continuous_gl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), Continuous β.gl := by
  intro D k _ _ _ _ p S n _ _ β
  refine (PI.FT.cont_HA_iff (AF D.host.F) (fun g : GL n k => β.gl g)).2 ⟨continuous_mt β, ?_⟩
  have h := (continuous_mt β).comp (continuous_inv (G := GL n k))
  refine h.congr fun g => ?_
  show mt S (β.gl g⁻¹) = PI.FT.mtI (β.gl g)
  rw [map_inv]; rfl

end GlobalTheory.FrameCont
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.FinPl
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

def intV (D : D7) (v : Pl D) : AddSubgroup (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {y | ∃ a ∈ v.adicCompletionIntegers D.host.F, ∃ x : 𝓞 D.host.E, y = a ⊗ₜ[D.host.F] (x : D.host.E)}

def sigV (D : D7) (v : Pl D) : Fv D.host.F v ⊗[D.host.F] D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E :=
  Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig

end GlobalTheory.FixedUnitNorm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UkPart

open Formalism.L2.SG.Pf.unitaryCongruence

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

local notation "RA" => X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F

theorem natCast_int (c : ℕ) : (c : RA) ∈ IntAf X.B.I.F X.B.I.E := natCast_mem _ c

theorem sigA_natCast (c : ℕ) : sigA X.B.I (c : RA) = c := map_natCast _ c

theorem natsmul_Lf (c : ℕ) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : (c : RA) • y ∈ X.B.I.Lf := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy c

theorem natsmul_mL (c : ℕ) {y : VA X.B.I} (hy : y ∈ mL X.B.I X.B.g) : (c : RA) • y ∈ mL X.B.I X.B.g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy c

theorem mL_le_Lf : mL X.B.I X.B.g ≤ X.B.I.Lf := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  exact natsmul_Lf X _ hy

theorem intsmul_Lf {t : RA} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    t • y ∈ X.B.I.Lf := by
  have h := X.B.I.Lf.smul_mem (⟨t, ht⟩ : IntAf X.B.I.F X.B.I.E) hy
  rwa [Subring.smul_def] at h

theorem Z_int {t : RA} (ht : ZMod' X.B.I X.B.g t) : t ∈ IntAf X.B.I.F X.B.I.E := by
  obtain ⟨s, hs, rfl⟩ := ht; exact mul_mem (natCast_int X _) hs

theorem hA_ef (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
  rw [hA_incl]
  have h := GlobalTheory.St.hform_crd_setting X (X.eX a) (X.fY b)
  rw [X.ef] at h
  have h' : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.fR b) = if a = b then 1 else 0 := by
    apply X.ιE.injective
    refine h.trans ?_; split_ifs <;> simp
  rw [h']; split_ifs <;> simp

theorem hA_fe (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if a = b then 1 else 0 := by
  rw [hA_symm X.B.I (incl X.B.I (X.eR a)), hA_ef]; split_ifs <;> simp

theorem exists_mult : ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ∀ b : Fin D.R.rS,
    (c : RA) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g ∧
    (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g := by
  choose ce hce using fun b => (X.basisApprox b).1
  choose cf hcf using fun b => (X.basisApprox b).2
  refine ⟨∏ b, ce b * cf b, Nat.Coprime.prod_left fun b _ => Nat.Coprime.mul_left (hce b).1 (hcf b).1, fun b => ?_⟩
  have hd : ce b * cf b ∣ ∏ b, ce b * cf b := Finset.dvd_prod_of_mem _ (Finset.mem_univ b)
  obtain ⟨k, hk⟩ := hd
  rw [hk]
  constructor
  · have : ((ce b * cf b * k : ℕ) : RA) • (X.e0 b - incl X.B.I (X.eR b)) =
        ((cf b * k : ℕ) : RA) • ((ce b : RA) • (X.e0 b - incl X.B.I (X.eR b))) := by
      rw [smul_smul]; push_cast; ring_nf
    rw [this]; exact natsmul_mL X _ (hce b).2
  · have : ((ce b * cf b * k : ℕ) : RA) • (X.f0 b - incl X.B.I (X.fR b)) =
        ((ce b * k : ℕ) : RA) • ((cf b : RA) • (X.f0 b - incl X.B.I (X.fR b))) := by
      rw [smul_smul]; push_cast; ring_nf
    rw [this]; exact natsmul_mL X _ (hcf b).2

theorem hA_sum_right (p : VA X.B.I) (v : Fin D.R.rS → VA X.B.I) :
    hA X.B.I p (∑ b, v b) = ∑ b, hA X.B.I p (v b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [hL_apply] using map_sum (hL X.B.I p) v Finset.univ

theorem core (u : D.what₂.Word) (m : X.B.I.Gf) (hmK : m ∈ X.B.I.Kset) (hmN : m ∈ X.NfinU u) (c : ℕ)
    (hc : ∀ b : Fin D.R.rS, (c : RA) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g ∧
      (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g)
    {p w : VA X.B.I} (hp : p ∈ X.B.I.Lf) (hw : w ∈ X.B.I.Lf)
    (ht : ∀ b, ZMod' X.B.I X.B.g (hA X.B.I (incl X.B.I (X.eR b)) ((c : RA) • w)))
    (hpe : ∀ b, ZMod' X.B.I X.B.g ((c : RA) * hA X.B.I p (incl X.B.I (X.eR b)))) :
    ZMod' X.B.I X.B.g ((c : RA) ^ 4 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w)) := by
  have hf : ∀ b, (c : RA) • incl X.B.I (X.fR b) ∈ X.B.I.Lf := fun b => by
    have e : (c : RA) • incl X.B.I (X.fR b) = (c : RA) • X.f0 b - (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) := by
      rw [smul_sub, sub_sub_cancel]
    rw [e]; exact sub_mem (natsmul_Lf X c (X.vectorsInLattice.1 b).2) (mL_le_Lf X (hc b).2)
  set W := (c : RA) • w with hWdef
  have hW : W ∈ X.B.I.Lf := natsmul_Lf X c hw
  set t : Fin D.R.rS → RA := fun b => hA X.B.I (incl X.B.I (X.eR b)) W with htdef
  set W' := W - ∑ b, t b • incl X.B.I (X.fR b) with hW'def
  have hperp : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) W' = 0 := fun a => by
    rw [hW'def, hA_sub_right, hA_sum_right]
    simp only [hA_smul_right, hA_ef, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [htdef]; exact sub_self _
  have hv := hmN.2.2 W' hperp
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun RA).1 hv
  have hlam_eq : ∀ a, hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ W') = lam a := fun a => by
    rw [← hlam, hA_sum_right]
    simp only [hA_smul_right, hA_fe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

  have hcW' : (c : RA) • W' ∈ X.B.I.Lf := by
    rw [hW'def, smul_sub, Finset.smul_sum]
    refine sub_mem (natsmul_Lf X c hW) (sum_mem fun b _ => ?_)
    rw [smul_comm]; exact intsmul_Lf X (Z_int X (ht b)) (hf b)
  have hlam_int : ∀ a, (c : RA) ^ 2 * lam a ∈ IntAf X.B.I.F X.B.I.E := fun a => by
    have h := hA_int X.B.I (hf a) (K_sub_mv X.B.I hmK hcW')
    rw [Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_natCast, hlam_eq] at h
    rw [pow_two, mul_assoc]; exact h

  have h1 : ZMod' X.B.I X.B.g ((c : RA) ^ 3 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ W')) := by
    rw [← hlam, hA_sum_right, Finset.mul_sum]
    refine Z_sum X.B.I X.B.g _ _ fun b _ => ?_
    rw [hA_smul_right]
    have e : (c : RA) ^ 3 * (lam b * hA X.B.I p (incl X.B.I (X.eR b))) =
        ((c : RA) ^ 2 * lam b) * ((c : RA) * hA X.B.I p (incl X.B.I (X.eR b))) := by ring
    rw [e]; exact Z_smul X.B.I X.B.g (hlam_int b) (hpe b)

  have h2 : ZMod' X.B.I X.B.g ((c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ∑ b, t b • incl X.B.I (X.fR b))) := by
    rw [Matrix.mulVec_sum, hA_sum_right, Finset.mul_sum]
    refine Z_sum X.B.I X.B.g _ _ fun b _ => ?_
    rw [Matrix.mulVec_smul, hA_smul_right]
    have e : (c : RA) * (t b * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (X.fR b))) =
        hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ((c : RA) • incl X.B.I (X.fR b))) * t b := by
      rw [Matrix.mulVec_smul, hA_smul_right]; ring
    rw [e]; exact Z_smul X.B.I X.B.g (hA_int X.B.I hp (K_sub_mv X.B.I hmK (hf b))) (ht b)
  have hsplit : W = W' + ∑ b, t b • incl X.B.I (X.fR b) := by rw [hW'def, sub_add_cancel]
  have e : (c : RA) ^ 4 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w) =
      (c : RA) ^ 3 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ W') +
      (c : RA) ^ 2 * ((c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ∑ b, t b • incl X.B.I (X.fR b))) := by
    have e2 : (c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w) =
        hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ W') +
        hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ∑ b, t b • incl X.B.I (X.fR b)) := by
      rw [← hA_add_right, ← Matrix.mulVec_add, ← hsplit, hWdef, Matrix.mulVec_smul, hA_smul_right]
    calc (c : RA) ^ 4 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w)
        = (c : RA) ^ 3 * ((c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w)) := by ring
      _ = _ := by rw [e2]; ring
  rw [e]
  exact Z_add X.B.I X.B.g h1 (Z_smul X.B.I X.B.g (pow_mem (natCast_int X c) 2) h2)

theorem conj_sub (x m : X.B.I.Gf) (v : VA X.B.I) :
    (X.B.I.fmat (x⁻¹ * m * x) - 1) *ᵥ v = X.B.I.fmat x⁻¹ *ᵥ ((X.B.I.fmat m - 1) *ᵥ (X.B.I.fmat x *ᵥ v)) := by
  rw [fmat_mul, fmat_mul]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← mul_assoc,
    fmat_inv_mul, one_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, fmat_inv_mul, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem term (u : D.what₂.Word) (m : X.B.I.Gf) (hmK : m ∈ X.B.I.Kset) (hmN : m ∈ X.NfinU u) (c : ℕ)
    (hc : ∀ b : Fin D.R.rS, (c : RA) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g ∧
      (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g) (i j : Fin D.R.k) :
    ZMod' X.B.I X.B.g ((c : RA) ^ 4 *
      hA X.B.I (X.bwd i) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ X.bw j)) := by
  have hbw : X.bw j ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 j).1
  have hbwd : X.bwd i ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 i).2
  have hfix : ∀ b, X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) :=
    fun b => (X.xu_fix u b).1
  rw [conj_sub, PIW.NormChiNBi.hA_left_inv X.B.I (X.xu u)⁻¹, inv_inv]
  refine core X u m hmK hmN c hc (K_mv X.B.I (X.xu_K u) hbwd) (K_mv X.B.I (X.xu_K u) hbw) (fun b => ?_) (fun b => ?_)
  ·
    rw [← hfix b, hA_smul_right, PIW.NormChiNBi.hA_fmat']
    have e : (c : RA) * hA X.B.I (incl X.B.I (X.eR b)) (X.bw j) =
        (c : RA) * hA X.B.I (X.e0 b) (X.bw j) - hA X.B.I ((c : RA) • (X.e0 b - incl X.B.I (X.eR b))) (X.bw j) := by
      rw [hA_smul_left, sigA_natCast, PIW.NormChiNBi.hA_sub_left]; ring
    rw [e]
    exact Z_sub X.B.I X.B.g (Z_smul X.B.I X.B.g (natCast_int X c) ((X.weightVectorsIntegral j).2.2 b).1)
      (PIW.NormChiNBi.hA_mL_left X.B.I X.B.g (hc b).1 hbw)
  ·
    rw [← hfix b, PIW.NormChiNBi.hA_fmat']
    have e : (c : RA) * hA X.B.I (X.bwd i) (incl X.B.I (X.eR b)) =
        (c : RA) * hA X.B.I (X.bwd i) (X.e0 b) - hA X.B.I (X.bwd i) ((c : RA) • (X.e0 b - incl X.B.I (X.eR b))) := by
      rw [hA_smul_right, PIW.NormChiNBi.hA_sub_right]; ring
    rw [e]
    exact Z_sub X.B.I X.B.g (Z_smul X.B.I X.B.g (natCast_int X c) ((Formalism.L2.SG.Pf.reference_frame_congruences X).2.2.1 i b))
      (PIW.NormChiNBi.hA_mL_right X.B.I X.B.g (hc b).1 hbwd)

theorem ukPart_zmod : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf),
    m ∈ X.B.I.Kset → m ∈ X.NfinU u → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) := by
  intro D X u m hmK hmN
  obtain ⟨c, hcop, hc⟩ := exists_mult X
  refine ⟨c ^ 4, Nat.Coprime.pow_left 4 hcop, ?_⟩
  rw [Finset.mul_sum]
  refine Z_sum X.B.I X.B.g _ _ fun i _ => ?_
  split_ifs with h
  · push_cast; exact term X u m hmK hmN c hc i _
  · rw [mul_zero]; exact Z_zero X.B.I X.B.g

end GlobalTheory.UkPart
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Fold

theorem exists_cutoff_srat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (Fs : Set X.B.I.GA), IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ β : X.B.I.GA → ENNReal, Measurable β ∧ (∀ x, ∑' σ : Srat X u, β ((σ : X.B.I.GA) * x) = 1) ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := by
  intro D X u Fs hFs
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hR.2.2.2.2
  haveI : DiscreteTopology (Srat X u) := Formalism.L2.SG.Pf.srat_discrete X u
  haveI : Countable (Srat X u) := Formalism.L2.SG.Pf.countable_of_discrete _
  obtain ⟨_, hleft, _⟩ := Formalism.L2.SG.EvalTOntoExt.instances X
  obtain ⟨F', hF'm, h1, h2⟩ := Formalism.L2.SG.Pf.exists_strictFund (Srat X u)
  have hF' := Formalism.L2.SG.Pf.isFund_of_strict (Srat X u) hF'm h1 h2 (X.B.I.muA X.B.μf)
  refine ⟨F'.indicator 1, measurable_one.indicator hF'm, ?_, ?_⟩
  · intro x
    obtain ⟨s, hs, hsx⟩ := h1 x
    rw [tsum_eq_single (⟨s, hs⟩ : Srat X u)]
    · simp [Set.indicator_of_mem hsx]
    · intro t ht
      have hne : ((t : X.B.I.GA) * x) ∉ F' := by
        intro htx
        apply ht
        have := h2 _ hsx ((t : X.B.I.GA) * s⁻¹) ((Srat X u).mul_mem t.2 ((Srat X u).inv_mem hs))
          (by simpa [mul_assoc] using htx)
        exact Subtype.ext (by simpa [mul_inv_eq_one] using this)
      simp [Set.indicator_of_notMem hne]
  · intro F hFm hFinv
    rw [hFs.setLIntegral_eq hF' F (fun g x => by simpa [Subgroup.smul_def, smul_eq_mul] using hFinv g g.2 x)]
    rw [← lintegral_indicator hF'm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ F' <;> simp [Set.indicator, hx]

end GlobalTheory.Core.Mi.Fold
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.integral_tsum_normal_eigenfunctions_eq_zero : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ M : Subgroup N), Countable Γ → DiscreteTopology Γ → M.Normal → IsClosed (M : Set N) → (∃ K : Set M, IsCompact K ∧ ∀ m, ∃ γ ∈ Γ.subgroupOf M, ∃ k ∈ K, m = γ * k) → ∀ 𝓝 : Set N, IsFundamentalDomain Γ 𝓝 ν → ν 𝓝 ≠ ⊤ → ∀ (I C : Type) [Countable I] (κ : I → C) (F : I → N → ℂ), (∀ i, Measurable (F i)) → (∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B) → (∀ γ ∈ Γ, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n) → (∀ c, ∀ γ ∈ Γ, γ ∈ M → ∀ n, ∑' i : {i // κ i = c}, F i (γ * n) = ∑' i : {i // κ i = c}, F i n) → (∀ c, ∃ u ∈ M, ∃ a : ℂ, a ≠ 1 ∧ ∀ i, κ i = c → ∀ m ∈ M, ∀ n, F i (m * u * n) = a * F i (m * n)) → ∫ n in 𝓝, ∑' i, F i n ∂ν = 0 := by
  first | exact @GlobalTheory.CutSum.integral_tsum_eq_zero | exact GlobalTheory.CutSum.integral_tsum_eq_zero | (intros; apply GlobalTheory.CutSum.integral_tsum_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.lintegral_unfold_sum_transitive_orbit : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (y₀ : Y), (∀ y, ∃ γ : Γ, γ • y₀ = y) → ∀ (𝓕 𝓖 : Set H), IsFundamentalDomain Γ 𝓕 ν → IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype) 𝓖 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → (∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν) ∧ (∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → ∫ h in 𝓖, Φ y₀ h ∂ν = ∫ h in 𝓕, ∑' y, Φ y h ∂ν) := by
  first | exact @GlobalTheory.Unf.lintegral_integral_unfold_transitive | exact GlobalTheory.Unf.lintegral_integral_unfold_transitive | (intros; apply GlobalTheory.Unf.lintegral_integral_unfold_transitive <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.lowerIntegral_to_integral_coordinates : ∀ (X U Y : Type) [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace Y] (G : Type) [MeasurableSpace G] (ν : Measure X) (νU : Measure U) (μ : Measure Y) [SFinite νU] [SFinite μ] (i : X → G) (p : U → Y → G) (Inv : (G → G) → Prop), Measurable i → Measurable (Function.uncurry p) → ∀ (Dom : Set G), (∀ f : G → ENNReal, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → ∫⁻ x, f (i x) ∂ν = ∫⁻ u, ∫⁻ y, f (p u y) ∂μ ∂νU) → ∀ f : G → ℂ, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → Integrable (fun x => f (i x)) ν → Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) ∧ ∫ x, f (i x) ∂ν = ∫ u, ∫ y, f (p u y) ∂μ ∂νU := by
  first | exact @GlobalTheory.lowerIntegral_to_integral_coords | exact GlobalTheory.lowerIntegral_to_integral_coords | (intros; apply GlobalTheory.lowerIntegral_to_integral_coords <;> assumption)
end
