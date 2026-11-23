module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetUnipotentOnBesselModels
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle287
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle320
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle321
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle322
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017

@[expose] public section

section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realIntegralUnipotent_besselModels_countable_subgroup : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u).Countable ∧
    (fun _ => Matrix.of.symm 1) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      GlobalTheory.DegVol.mulP m m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      (fun τ => Matrix.of.symm (Matrix.of (m τ))⁻¹) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    ∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ τ, Matrix.of (m τ) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  first | exact @GlobalTheory.CovGrp.cov_grp | exact GlobalTheory.CovGrp.cov_grp | (intros; apply GlobalTheory.CovGrp.cov_grp <;> assumption)
end

section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.strictFundamentalSet_unipotent_on_besselModels : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    GlobalTheory.DegVol.IsFund (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u)
      (GlobalTheory.DegVol.RP D.R.k D.R.rS (fun _ => 1)) (trI C '' Y.FN u) := by
  first | exact @GlobalTheory.TypeAsm.CovTrans.isFund_trI | exact GlobalTheory.TypeAsm.CovTrans.isFund_trI | (intros; apply GlobalTheory.TypeAsm.CovTrans.isFund_trI <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.residue_cmFieldFiniteAdeleTensorEquiv_eq_natCast : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E) (ha : GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (m : ℕ), a ∈ ReciprocityTheory.Aut.ALint D.host.E → Valued.v (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) < 1 → Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩ = (m : Formalism.L2.DIV.kP s.w) := by
  first | exact @GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast | exact GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast | (intros; apply GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.exists_splitPlace_eq_fixedTypePrimePlace : ∀ (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k), ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = D.naut.plGw kv.1 kv.2 := by
  first | exact @GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw | exact GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw | (intros; apply GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.sum_seriesIdempotentCoeff_rightTranslation : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (c : GAf D.host.E D.R.r) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf) (lf : G0g D.nd → GAf D.host.E D.R.r), FrameRed X h t PY c red → IsSec X red sec → (∀ γ, PY.ψ (lf γ) = kap X h t (sec γ)) → ∀ (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (τ : Tup2 D), HasTuple D π τ → ∀ φ ∈ π.S, (∀ k ∈ X.B.I.Kg X.B.g, ∀ κ, PY.ψ κ = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r κ φ = φ) → ∑ᶠ γ, serCoef τ γ • Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ = φ := by
  first | exact @GlobalTheory.LabFix.sum_serCoef_rt | exact GlobalTheory.LabFix.sum_serCoef_rt | (intros; apply GlobalTheory.LabFix.sum_serCoef_rt <;> assumption)
end

section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

theorem _root_.GlobalTheory.T.besselModel_linearMap_matrix_exists : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (m : (VS D).V →ₗ[D.host.E] (VS D).V),
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  first | exact @GlobalTheory.TypeAsm.phiV_linMat_all | exact GlobalTheory.TypeAsm.phiV_linMat_all | (intros; apply GlobalTheory.TypeAsm.phiV_linMat_all <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_maximalCompactUnitary_of_splitPlaceLift : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace L) (g : ℕ), g.Prime → ((g : 𝓞 L) ∈ s.w.asIdeal) → ∀ (x : Formalism.AUTREP.GAf L n) (γ : GL (Fin n) (ZMod g)), GlobalTheory.LabPin.IsLift s x γ → x ∈ ReciprocityTheory.Aut.Umax L n := by
  first | exact @GlobalTheory.LiftInt.mem_Umax_of_isLift | exact GlobalTheory.LiftInt.mem_Umax_of_isLift | (intros; apply GlobalTheory.LiftInt.mem_Umax_of_isLift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.fixedVectorIdentity_isotypic_conjugateType : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (π : Formalism.L2.NG.FinTyp D.host.E n) (U : Set (GAf D.host.E n)) (ι : Type) [Finite ι] (a : ι → ℂ) (lf : ι → GAf D.host.E n), (∀ φ ∈ π.S, (∀ κ ∈ U, Formalism.L2.NG.rt D.host.E n κ φ = φ) → ∑ᶠ i, a i • Formalism.L2.NG.rt D.host.E n (lf i) φ = φ) → ∀ S ∈ isotIn ρ C (FinTyp.conjT π), (∀ κ ∈ U, ρ κ S = S) → ∑ᶠ i, star (a i) • ρ (lf i) S = S := by
  first | exact @GlobalTheory.IsotConjFix.isotIn_conjT_fix_sum | exact GlobalTheory.IsotConjFix.isotIn_conjT_fix_sum | (intros; apply GlobalTheory.IsotConjFix.isotIn_conjT_fix_sum <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.StabRat
open Formalism.HermitianLatticeCounting.S6

section Conj
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem xa_map {F G : FlagD H r} (g : V ≃ₗ[K] V) (he : ∀ a, G.e a = g (F.e a)) (a : ℕ) :
    G.Xa a = (F.Xa a).map (g : V →ₗ[K] V) := by
  unfold FlagD.Xa
  rw [Submodule.map_span, Set.image_image]
  congr 1
  exact Set.image_congr fun b _ => he _

theorem inN_conj {F G : FlagD H r} (g : V ≃ₗ[K] V) (hg : ∀ x y, H.B (g x) (g y) = H.B x y)
    (he : ∀ a, G.e a = g (F.e a)) (n : V ≃ₗ[K] V) :
    G.InN (n : V →ₗ[K] V) ↔ F.InN ((g⁻¹ * n * g : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  have hc : ∀ x, (g⁻¹ * n * g) x = g.symm (n (g x)) := fun x => rfl
  have hX := xa_map g he
  unfold FlagD.InN FlagD.X
  simp only [LinearEquiv.coe_coe, hc]
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨fun x y => ?_, (g⁻¹ * n * g).bijective, fun a => ?_, fun y hy => ?_⟩
    · rw [← hg (g.symm (n (g x))), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, h1, hg]
    · have := h3 a
      rw [he, hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply] at this
      exact this
    · have := h4 (g y) fun a => by rw [he, hg, hy]
      rw [hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply] at this
      exact this
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨fun x y => ?_, n.bijective, fun a => ?_, fun y hy => ?_⟩
    · have := h1 (g.symm x) (g.symm y)
      simp only [LinearEquiv.apply_symm_apply] at this
      rw [← hg (g.symm (n x)), ← hg (g.symm x)] at this
      simpa only [LinearEquiv.apply_symm_apply] using this
    · rw [he, hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply]
      exact h3 a
    · have hy' : ∀ a : Fin r, H.B (F.e a.castSucc) (g.symm y) = 0 := fun a => by
        rw [← hg, LinearEquiv.apply_symm_apply, ← he, hy]
      have := h4 (g.symm y) hy'
      rw [LinearEquiv.apply_symm_apply] at this
      rw [hX, Submodule.mem_map_equiv, map_sub]
      exact this

end Conj

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

theorem frF_xa (F : FlagG S r T) (hT : T ≠ 0) (a : ℕ) : (frF F hT).Xa a = F.Xa a := by
  unfold FlagD.Xa FlagG.Xa
  congr 1
  exact Set.image_congr fun b _ => fv_cast F b

theorem flagToFrameOfNonzeroLevel_isotropic_eq (F : FlagG S r T) (hT : T ≠ 0) : (frF F hT).X = F.X := by
  rw [FlagD.X, frF_xa]
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, i.2, h⟩⟩

theorem inN_frF_iff (F : FlagG S r T) (hT : T ≠ 0) (n : S.V ≃ₗ[E] S.V) :
    (frF F hT).InN (n : S.V →ₗ[E] S.V) ↔ n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ j, ∀ x ∈ F.Xa (j + 1), n x - x ∈ F.Xa j) ∧
      (∀ x ∈ orth S F.X, n x - x ∈ F.X) := by
  have he : ∀ a : Fin r, (frF F hT).e a.castSucc = F.e a := fv_cast F
  have hB : ∀ x y, (spH S).B x y = S.hT y x := fun _ _ => rfl
  unfold FlagD.InN
  simp only [LinearEquiv.coe_coe, frF_xa, flagToFrameOfNonzeroLevel_isotropic_eq, he, hB]
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨fun x y => h1 y x, fun j x hx => ?_, fun x hx => h4 x fun a => ?_⟩
    · have : F.Xa (j + 1) ≤ (F.Xa j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, hb, rfl⟩
        have hb' : b.val < j + 1 := hb
        have hle : F.Xa b.val ≤ F.Xa j :=
          Submodule.span_mono (Set.image_mono fun c hc => lt_of_lt_of_le hc (Nat.lt_succ_iff.1 hb'))
        exact hle (h3 b)
      exact this hx
    · have h0 : S.hT (F.e a) x = 0 := by
        simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
        exact hx _ (Submodule.subset_span ⟨a, rfl⟩)
      rw [a_herm, h0, star_zero]
  · rintro ⟨h1, h3, h4⟩
    refine ⟨fun x y => h1 y x, n.bijective, fun a => ?_, fun y hy => h4 y ?_⟩
    · exact h3 a.val _ (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)
    · simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      have : F.X ≤ LinearMap.ker (S.hT y) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, rfl⟩
        exact hy b
      rw [a_herm, LinearMap.mem_ker.1 (this hx), star_zero]

theorem mem_NLam_iff (Λ : Submodule (𝓞 E) S.V) (L : LFlag S r T) (hT : T ≠ 0) (n : S.V ≃ₗ[E] S.V) :
    n ∈ NLam Λ L ↔ (frF L.fl hT).InN (n : S.V →ₗ[E] S.V) ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
  rw [inN_frF_iff]
  exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c, d⟩, b⟩, fun ⟨⟨a, c, d⟩, b⟩ => ⟨⟨a, b⟩, c, d⟩⟩

theorem fvec_mapLF (g : S.V ≃ₗ[E] S.V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (L : LFlag S r T) (a : Fin (r + 1)) :
    (mapLF g L).fl.fvec a = g (L.fl.fvec a) := by
  rw [mapLF, dite_eq_left hg]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · rw [fv_last, fv_last]; rfl
  · rw [fv_cast, fv_cast]; rfl

end Gen
end GlobalTheory.TypeAsm.StabRat

namespace GlobalTheory.TypeAsm
open StabRat GlobalTheory.DegAsm.AdaptInv

theorem gam_iff_nLam : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (t : Formalism.L2.SG.TermOp.GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS), AdT t N → ∀ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, n ∈ N.Gam t.lam ↔ (n ∈ NLam t.lam (lf D (X.Fu u)) ∧ t.lin⁻¹ * n * t.lin ∈ NLam t.lam' (lf D (X.Fu u))) := by
  intro D large₂ X Y u _ t N hN n
  obtain ⟨-, h, h'⟩ := hN
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hlam : t.lin • t.lam' = t.lam := t.rep.2.2.2.1
  have e1 : N.F.InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) ↔ (F0 X u).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) :=
    ⟨inN_of (sameGr_symm h) _, inN_of h _⟩
  have e2 : N.F'.InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) ↔ (Ft t).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) :=
    ⟨inN_of (sameGr_symm h') _, inN_of h' _⟩
  have e3 := inN_conj (F := F0 X u) (G := Ft t) t.lin (fun x y => hiso y x)
    (fvec_mapLF t.lin hiso (lf D (X.Fu u))) n
  have hL : ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (m : (VS D).V ≃ₗ[D.host.E] (VS D).V),
      m ∈ NLam Λ (lf D (X.Fu u)) ↔ (F0 X u).InN (m : (VS D).V →ₗ[D.host.E] (VS D).V) ∧ m • Λ = Λ :=
    fun Λ m => mem_NLam_iff Λ _ (tu_ne D u) m
  have e4 : (t.lin⁻¹ * n * t.lin) • t.lam' = t.lam' ↔ n • t.lam = t.lam := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff, hlam]
  rw [GlobalTheory.DegCnt.NF.Gam, Subgroup.mem_inf, GlobalTheory.UnipStab.mem_R, MulAction.mem_stabilizer_iff, e1, e2, e3, hL, hL, e4]
  tauto
end GlobalTheory.TypeAsm
end

section

noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm
open Formalism.HermitianLatticeCounting.S6

section EmbGen
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}

def frPerp (F : FlagD H r) : Submodule K V where
  carrier := {v | ∀ a, H.B (F.e a) v = 0}
  add_mem' := by
    intro x y hx hy a
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add (f := _), hx a, hy a, add_zero]
  zero_mem' := by
    intro a
    simp
  smul_mem' := by
    intro c x hx a
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smulₛₗ, hx a, smul_zero]

theorem mem_frPerp (F : FlagD H r) (v : V) : v ∈ frPerp F ↔ ∀ a, H.B (F.e a) v = 0 := Iff.rfl

theorem B_right_nondeg (H : HermSpace K V) (w : V) (h : ∀ v, H.B v w = 0) : w = 0 :=
  H.nondeg w (fun y => by rw [← H.herm y w, h y, star_zero])

theorem fr_indep (F : FlagD H r) : LinearIndependent K F.e := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hz : c (Fin.last r) = 0 := by
    have h : H.B (∑ a, c a • F.e a) (F.e (Fin.last r)) = 0 := by rw [hc, map_zero, LinearMap.zero_apply]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [F.zperp, F.zz, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add] at h
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd (neg_eq_zero.1 h) F.hT
  have hc' : ∑ a : Fin r, c a.castSucc • F.e a.castSucc = 0 := by
    rw [Fin.sum_univ_castSucc, hz, zero_smul, add_zero] at hc
    exact hc
  have hcs := Fintype.linearIndependent_iff.1 F.indep (fun a => c a.castSucc) hc'
  intro i
  induction i using Fin.lastCases with
  | last => exact hz
  | cast a => exact hcs a

def frMap (F : FlagD H r) : V →ₗ[K] (Fin (r + 1) → K) :=
  LinearMap.pi fun a => H.B.flip (F.e a)

theorem frMap_apply (F : FlagD H r) (v : V) (a : Fin (r + 1)) : frMap F v a = H.B v (F.e a) := rfl

theorem ker_frMap (F : FlagD H r) : LinearMap.ker (frMap F) = frPerp F := by
  ext v
  rw [LinearMap.mem_ker, mem_frPerp, funext_iff]
  refine forall_congr' fun a => ?_
  rw [frMap_apply, Pi.zero_apply, ← H.herm (F.e a) v]
  exact ⟨fun h => by rw [← star_star (H.B (F.e a) v), h, star_zero], fun h => by rw [h, star_zero]⟩

theorem range_frMap (F : FlagD H r) : LinearMap.range (frMap F) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  set c : Fin (r + 1) → K := fun a => f (fun j => if a = j then 1 else 0) with hcdef
  have hfx : ∀ x, f x = ∑ a, x a * c a := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]

    simp only [map_sum, map_smul, smul_eq_mul, hcdef]
  have hv : ∀ v, H.B v (∑ a, star (c a) • F.e a) = 0 := by
    intro v
    have h1 : f (frMap F v) = 0 := by
      have : f (frMap F v) ∈ Submodule.map f (LinearMap.range (frMap F)) :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self _ v)
      rw [hf] at this
      exact (Submodule.mem_bot K).1 this
    rw [hfx] at h1

    rw [map_sum]
    simp only [map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul]
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [frMap_apply, mul_comm]
  have hw := B_right_nondeg H _ hv
  have hc := Fintype.linearIndependent_iff.1 (fr_indep F) _ hw
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [hfx]
  simp only [LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : c a = 0 := by simpa using hc a
  rw [this, mul_zero]

theorem finrank_frPerp [FiniteDimensional K V] (F : FlagD H r) :
    Module.finrank K (frPerp F) + (r + 1) = Module.finrank K V := by
  have h := LinearMap.finrank_range_add_finrank_ker (frMap F)
  rw [range_frMap, ker_frMap, finrank_top, Module.finrank_fin_fun] at h
  omega

theorem X_le_frPerp (F : FlagD H r) : F.X ≤ frPerp F := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, -, rfl⟩ a
  induction a using Fin.lastCases with
  | last => rw [← H.herm (F.e b.castSucc) (F.e (Fin.last r)), F.zperp b, star_zero]
  | cast a => exact F.iso a b

theorem finrank_X (F : FlagD H r) : Module.finrank K F.X = r := by
  have h : F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
    show Submodule.span K _ = _
    congr 1
    ext x
    simp
  rw [h, finrank_span_eq_card F.indep, Fintype.card_fin]

def resH (H : HermSpace K V) (W : Submodule K V) (hnd : ∀ x : W, (∀ y : W, H.B x y = 0) → x = 0) :
    HermSpace K W where
  B := (H.B.comp W.subtype).compl₂ W.subtype
  herm x y := H.herm x y
  nondeg x h := hnd x h

theorem exists_emb [FiniteDimensional K V] (F : FlagD H r) (τ₀ : K →+* ℂ) (hP : ∀ σ : K →+* ℂ, F.PosDefAt σ) :
    ∃ (W : Submodule K V) (HW : HermSpace K W), GlobalTheory.DegAsm.IsEmb F HW W.subtype ∧
      Module.finrank K W + (2 * r + 1) = Module.finrank K V ∧ GlobalTheory.Mass.PD HW.B.flip := by
  obtain ⟨Y, hY⟩ := Submodule.exists_isCompl F.X
  set W := Y ⊓ frPerp F with hW
  have hsup : F.X ⊔ W = frPerp F := by
    rw [hW, ← sup_inf_assoc_of_le Y (X_le_frPerp F), hY.sup_eq_top, top_inf_eq]
  have hinf : F.X ⊓ W = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    exact hY.inf_eq_bot ▸ ⟨hx.1, hx.2.1⟩
  have hpos : ∀ (σ : K →+* ℂ) (x : W), x ≠ 0 → 0 < (σ (H.B x x)).re := by
    intro σ x hx
    refine hP σ x ((mem_frPerp F _).1 x.2.2) fun hxX => hx ?_
    have : (x : V) ∈ F.X ⊓ W := ⟨hxX, x.2⟩
    rw [hinf] at this
    exact Subtype.ext ((Submodule.mem_bot K).1 this)
  have hnd : ∀ x : W, (∀ y : W, H.B x y = 0) → x = 0 := by
    intro x h
    by_contra hx
    have := hpos τ₀ x hx
    rw [h x, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨W, resH H W hnd, ⟨fun x y => rfl, fun v => ?_⟩, ?_, fun σ x hx => hpos σ x hx⟩
  · rw [← mem_frPerp, Submodule.range_subtype, sup_comm, hsup]
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq F.X W
    rw [hsup, hinf, finrank_bot, finrank_X] at h1
    have h2 := finrank_frPerp F
    omega

end EmbGen

theorem embC : EmbC := by
  intro D large₂ X u _
  have hpos : ∀ σ : D.host.E →+* ℂ, (F0 X u).PosDefAt σ := fun σ =>
    Formalism.MainNotions.KappaEndpoints.nf_pos (lf D (X.Fu u)) (tu_ne D u)
      (p_posX D (Tu D u) (D.mem u).A.T_prime.pos _) σ
  let τ₀ : D.host.E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := D.host.E)).toRingHom
  obtain ⟨W, HW, h1, h2, h3⟩ := exists_emb (F0 X u) τ₀ hpos
  refine ⟨W, HW, h1, ?_, h3⟩
  have hV : Module.finrank D.host.E (VS D).V = D.R.rankY 0 := by
    rw [(VS D).rank_eq]
    exact D.sp.Y_rank 0 (Nat.zero_le _)
  have hR : D.R.rankY 0 = 2 * D.R.rS + D.R.k + 1 := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r, zero_mul, add_zero]
    omega
  rw [hV, hR] at h2
  omega

end GlobalTheory.TypeAsm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.exists_degreeOne_prime_frame_reduced_matrices : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (N p : ℕ) (hN : I.n = N) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)), p.Prime → Nat.card (𝓞 I.E ⧸ w.asIdeal) = p → ∃ fr : GlobalTheory.RowLev.PlFrame I N p w, ∀ k ∈ I.Kset, ∀ M : Matrix (Fin N) (Fin N) (ZMod p), (∀ (i j : Fin N) (hij : ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (Fin.cast hN.symm i) (Fin.cast hN.symm j) ∈ Formalism.L2.Herm.intAf I.F I.E), Formalism.L2.DIV.resS I.F w ⟨_, hij⟩ = ((M i j).val : Formalism.L2.DIV.kP w)) → fr.ActsAs k M := by
  first | exact @GlobalTheory.RowLev.exists_plFrame_of_isFrame | exact GlobalTheory.RowLev.exists_plFrame_of_isFrame | (intros; apply GlobalTheory.RowLev.exists_plFrame_of_isFrame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.reducedMatrix_of_actsAs_degree_one_prime_frame : ∀ (I : AutInst) (N p : ℕ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) (fr : GlobalTheory.RowLev.PlFrame I N p w) (x : I.Gf), x ∈ I.Kset → ∀ M : Matrix (Fin N) (Fin N) (ZMod p), fr.ActsAs x M → Formalism.L2.SG.Pf.RowDictPf.RedMat0 I w p x M := by
  first | exact @GlobalTheory.RowLev.redMat0_of_actsAs | exact GlobalTheory.RowLev.redMat0_of_actsAs | (intros; apply GlobalTheory.RowLev.redMat0_of_actsAs <;> assumption)
end
