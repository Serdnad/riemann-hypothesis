module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle062
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle198
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle168
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle304
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLevelSplit

theorem lemB_pf : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : GA D V), L.Pg ⊆ T → L.Q ⊆ T → x ∈ GfC V → finE V x ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T → x ∈ levS V β L ∧ levChi V β L x = 1 := by
  intro D V β L T x hg hq hx hK
  have h3 : ∀ PP ∈ T, Formalism.L2.DIV.redFn β PP (finE V x) = 1 := by
    have h1 : finE V x ∈ ⨅ PP ∈ T, Formalism.L2.DIV.princAt β PP := hK.2
    exact fun PP hP => (Formalism.L2.DIV.mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  refine ⟨⟨hx, Formalism.L2.DIV.Kg_le_lev hg hq hK⟩, ?_⟩
  have hr : Formalism.L2.DIV.rTup β L (finE V x) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn β PP.1 (finE V x)) = 1
    rw [h3 PP.1 (hg PP.2)]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi Formalism.L2.DIV.levFn
  rw [hr, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · rfl
  · intro PP hP
    rw [h3 PP (hq hP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (hg hP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

theorem int_of_lt {D : D7} {n : ℕ} (y : Matrix (Fin n) (Fin n) (EAf D))
    (h : ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin n), Valued.v (GlobalTheory.StdFrames.cpt Q (y a b - (1 : Matrix (Fin n) (Fin n) (EAf D)) a b)) < 1)
    (a b : Fin n) : y a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h1 : (1 : Matrix (Fin n) (Fin n) (EAf D)) a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h2 : y a b - (1 : Matrix (Fin n) (Fin n) (EAf D)) a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    (GlobalTheory.AdIsom.mem_OA _).2 fun Q => le_of_lt (h Q a b)
  have := add_mem h2 h1
  rwa [sub_add_cancel] at this


theorem glInt_of_int {D : D7} {n : ℕ} (y : GL (Fin n) (EAf D))
    (i1 : ∀ a b, y.val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i2 : ∀ a b, (y⁻¹).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ z : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.intGL D.host.F D.host.E n z = y ∧
      ∀ a b, ((z.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = y.val a b := by
  let φ : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) →+* Matrix (Fin n) (Fin n) (EAf D) :=
    RingHom.mapMatrix (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have inj : Function.Injective φ := fun M N h => Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
  let zM : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) := Matrix.of fun a b => ⟨_, i1 a b⟩
  let zI : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) := Matrix.of fun a b => ⟨_, i2 a b⟩
  have e1 : φ zM = y.val := by ext a b; rfl
  have e2 : φ zI = (y⁻¹).val := by ext a b; rfl
  have m1 : zM * zI = 1 := inj (show φ (zM * zI) = φ 1 by rw [map_mul, map_one, e1, e2, Units.mul_inv])
  have m2 : zI * zM = 1 := inj (show φ (zI * zM) = φ 1 by rw [map_mul, map_one, e1, e2, Units.inv_mul])
  exact ⟨⟨zM, zI, m1, m2⟩, Units.ext e1, fun a b => rfl⟩


theorem kg_of_cpt : ∀ (D : D7) (V : HSp D) (β x : GL (Fin V.rank) (EAf D)) (T : Finset (Formalism.L2.DIV.Pl D.host.E)), x ∈ Formalism.L2.DIV.UA D.sp.cm V.gram → (∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * x * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → (∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * x⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → x ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T := by
  intro D V β x T hU h1 h2
  have hyi : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  have i1 := int_of_lt (β⁻¹ * x * β).val h1
  have i2 := int_of_lt ((β⁻¹ * x * β)⁻¹).val (by rw [hyi]; exact h2)
  obtain ⟨z, hz0, hzv⟩ := glInt_of_int (β⁻¹ * x * β) i1 i2
  have hz : Formalism.L2.DIV.frGL β z = x := by
    show β * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank z * β⁻¹ = x
    rw [hz0]; group
  have hS : x ∈ Formalism.L2.DIV.St β := ⟨z, hz⟩
  have hred : ∀ PP, Formalism.L2.DIV.redFn β PP x = 1 := by
    intro PP
    rw [← hz, Formalism.L2.DIV.redFn_frGL]
    apply Units.ext
    ext a b
    show Formalism.L2.DIV.resS D.host.F PP (z.val a b) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP PP)) a b
    have h0 : Formalism.L2.DIV.resS D.host.F PP (z.val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b) = 0 := by
      rw [GlobalTheory.AdIsom.resS_eq_zero_iff_cpt]
      have e3 : ((z.val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
          (β⁻¹ * x * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b := by
        rw [← hzv a b, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
      rw [e3]; exact h1 PP a b
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  exact ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun _ => Formalism.L2.DIV.mem_princAt.2 ⟨hS, hred PP⟩⟩

theorem trivOutside_inv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside T x) : TrivOutside T x⁻¹ := fun v hv => by
  have h1 : (((x⁻¹ : Formalism.AUTREP.GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
  have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1
  simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  exact h2

theorem lemA_pf (hC2 : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ T : Finset (Formalism.L2.DIV.Pl D.host.E), finE V (P.ψ κ) ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T := by
  intro D V n hF P β Λ N hS hβ s
  obtain ⟨h, hh⟩ := hC2 D V n hF P β Λ N hS hβ s
  refine ⟨h, fun κ hκ hk T => ?_⟩
  have hk' : h⁻¹ * s.loc n κ⁻¹ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) := by
    have := Subgroup.inv_mem _ hk
    rwa [show (h⁻¹ * s.loc n κ * h)⁻¹ = h⁻¹ * (s.loc n κ)⁻¹ * h by group, ← map_inv] at this
  have e : finE V (P.ψ κ⁻¹) = (finE V (P.ψ κ))⁻¹ := by rw [map_inv, map_inv]
  refine kg_of_cpt D V β (finE V (P.ψ κ)) T (GlobalTheory.LevSplit.finE_mem_UA V _) (hh κ hκ hk) ?_
  have := hh κ⁻¹ (trivOutside_inv hκ) hk'
  rwa [e] at this

theorem stdFrame_splitPlace_entries_off_place (hA : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), TrivOutside {s.v} κ → ∀ (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal → ∀ (a b : Fin V.rank), GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b) = GlobalTheory.StdFrames.cpt Q ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) (hC : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) (hDd : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) (hE : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (s : SplitPlace D.host.E) (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal → Q = s.w ∨ Q = GlobalTheory.IdemSupport.cP s.w) : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V n hF P β Λ N hS hβ s
  obtain ⟨h, hh⟩ := hDd D V n hF P β hS s
  refine ⟨h, fun κ hκ hk Q a b => ?_⟩
  by_cases hQ : Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal
  · rcases hE D hF s Q hQ with rfl | rfl
    · exact hh κ hκ hk a b
    · have hk' : h⁻¹ * s.loc n κ⁻¹ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) := by
        have := Subgroup.inv_mem _ hk
        rwa [show (h⁻¹ * s.loc n κ * h)⁻¹ = h⁻¹ * (s.loc n κ)⁻¹ * h by group, ← map_inv] at this
      refine hC D V β Λ N hβ (P.ψ κ) s.w (fun a b => ?_) a b
      have := hh κ⁻¹ (trivOutside_inv hκ) hk' a b
      rwa [map_inv, map_inv] at this
  · rw [map_sub, hA D V n hF P β hS s κ hκ Q hQ a b, sub_self, map_zero]
    exact zero_lt_one

end GlobalTheory.RowLevelSplit
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.CoordW



theorem exists_jW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ mj : GlobalTheory.RealGeo.MjTie R.toRealDat F.lv2, ∃ jW : ∀ i : Fin D.R.m, (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1), ∀ (i : Fin D.R.m) v, mj.eW i (jW i v) = (R.FW i).j (sg0 D A3.A) (Fintype.linearCombination D.what₂.LL (R.toRealDat.bL F.lv2 false i) v) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH mj
  have key : ∀ i : Fin D.R.m, ∃ g : (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL]
      D.what₂.Mj ((i : ℕ) + 1), ∀ v, mj.eW i (g v) = GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i v := by
    intro i
    have he : Function.Injective (mj.eW i) :=
      GlobalTheory.Mem.LiftForms.inj_of_norm_sq _ (RealDat.nP_pos (F := F.lv2) false) (mj.eW_norm i)
    have hspan : Submodule.span ℂ (Set.range fun k =>
        GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i (Pi.single k 1)) = LinearMap.range (mj.eW i) :=
      (GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i).trans
        ((hH.aux.levelW false i _).trans (mj.eW_range i).symm)
    have hmem : ∀ v, GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i v ∈ LinearMap.range (mj.eW i) := by
      intro v
      rw [← hspan, GlobalTheory.Mem.LiftTheta.semi_expand]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    choose s hs using fun v => LinearMap.mem_range.1 (hmem v)
    exact ⟨{ toFun := s
             map_add' := fun a b => he ((hs (a + b)).trans (((map_add _ a b).trans
               (congrArg₂ (· + ·) (hs a).symm (hs b).symm)).trans (map_add (mj.eW i) (s a) (s b)).symm))
             map_smul' := fun c a => he ((hs (c • a)).trans (((LinearMap.map_smulₛₗ _ c a).trans
               (congrArg (D.what₂.embLL c • ·) (hs a).symm)).trans (LinearMap.map_smul (mj.eW i) _ (s a)).symm)) }, hs⟩
  choose jW hjW using key
  exact ⟨jW, fun i v => (hjW i v).trans
    (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _).symm)⟩

end GlobalTheory.Mem.CoordW
end
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2.HostK

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.UnusedSlot33.HK
open scoped BigOperators

variable {R : Ranks} (H : Host R)

theorem emb_conj (f : H.E →+* ℂ) (y : H.E) : f (H.conj y) = starRingEnd ℂ (f y) := Formalism.HC.HostAx.conjE_apply _ _ _

theorem sqrt_mem : H.sqrtMinusD ∈ H.K := bE_mem H

theorem φ₀_sqrt : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem exists_coords {x : H.E} (hx : x ∈ H.K) : ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqrtMinusD :=
  by apply _root_.GlobalTheory.CoordsOfMemAdjoin.exists_rat_coords <;> assumption

theorem conj_coords (a b : ℚ) :
    H.conj ((a : H.E) + (b : H.E) * H.sqrtMinusD) = (a : H.E) - (b : H.E) * H.sqrtMinusD := by
  rw [map_add (f := _), map_mul, map_ratCast, map_ratCast, H.conj_sqrtMinusD]
  ring

theorem conj_mem {x : H.E} (hx : x ∈ H.K) : H.conj x ∈ H.K := by
  obtain ⟨a, b, rfl⟩ := exists_coords H hx
  rw [conj_coords]
  exact sub_mem (SubfieldClass.ratCast_mem _ a) (mul_mem (SubfieldClass.ratCast_mem _ b) (sqrt_mem H))

def conjK : H.K →+* H.K :=
  RingHom.codRestrict ((H.conj : H.E →+* H.E).comp H.K.val.toRingHom) H.K (fun x => conj_mem H x.2)

theorem coe_conjK (x : H.K) : ((conjK H x : H.K) : H.E) = H.conj (x : H.E) := rfl

theorem conjK_conjK (x : H.K) : conjK H (conjK H x) = x := Subtype.ext (conj_conj H x)

theorem exists_norm_int (x : 𝓞 H.K) : ∃ m : ℤ, (x : H.K) * conjK H x = m :=
  ⟨Algebra.intNorm ℤ (𝓞 H.K) x, Subtype.ext (by
    have := norm_int H x
    simpa [coe_conjK] using this.symm)⟩

theorem isGalois_over : IsGalois H.K H.E := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  exact IsGalois.tower_top_of_isGalois ℚ _ _

theorem coe_trace (y : H.E) : ((Algebra.trace H.K H.E y : H.K) : H.E) = ∑ τ : H.E ≃ₐ[H.K] H.E, τ y := by
  have := isGalois_over H
  exact trace_eq_sum_automorphisms (K := H.K) y

theorem conj_comm (τ : H.E ≃ₐ[H.K] H.E) (y : H.E) : H.conj (τ y) = τ (H.conj y) :=
  H.φ₀.injective (by
    rw [emb_conj H H.φ₀ (τ y)]
    exact (emb_conj H (H.φ₀.comp (τ : H.E →+* H.E)) y).symm)

theorem trace_conj (y : H.E) : Algebra.trace H.K H.E (H.conj y) = conjK H (Algebra.trace H.K H.E y) := by
  apply Subtype.ext

  rw [coe_conjK, coe_trace, coe_trace, map_sum]
  exact Finset.sum_congr rfl fun τ _ => (conj_comm H τ y).symm

theorem trace_pos (y : H.E) (hy : y ≠ 0) : ∃ a : ℚ, 0 < a ∧ Algebra.trace H.K H.E (y * H.conj y) = (a : H.K) := by
  obtain ⟨a, b, hab⟩ := exists_coords H (Algebra.trace H.K H.E (y * H.conj y)).2
  have hfix : H.conj ((Algebra.trace H.K H.E (y * H.conj y) : H.K) : H.E)
      = ((Algebra.trace H.K H.E (y * H.conj y) : H.K) : H.E) := by
    rw [← coe_conjK, ← trace_conj, map_mul, conj_conj, mul_comm]
  rw [hab, conj_coords] at hfix
  have hb : (b : H.E) * H.sqrtMinusD = 0 := by linear_combination (-1 / 2 : H.E) * hfix
  rw [hb, add_zero] at hab
  refine ⟨a, ?_, Subtype.ext (by rw [hab]; simp)⟩
  have h1 := congrArg H.φ₀ hab

  rw [coe_trace, map_sum, map_ratCast] at h1
  have h2 : ∀ τ : H.E ≃ₐ[H.K] H.E, H.φ₀ (τ (y * H.conj y)) = ((Complex.normSq (H.φ₀ (τ y)) : ℝ) : ℂ) := by
    intro τ
    rw [map_mul, ← conj_comm, map_mul, emb_conj, Complex.mul_conj]
  simp only [h2] at h1
  have h3 : ∑ τ : H.E ≃ₐ[H.K] H.E, Complex.normSq (H.φ₀ (τ y)) = (a : ℝ) := by
    exact_mod_cast h1
  have h4 : (0 : ℝ) < a := by
    rw [← h3]
    refine Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ?_) Finset.univ_nonempty
    simpa using hy
  exact_mod_cast h4

theorem card_tau : Fintype.card (Tau R) = Module.finrank H.K H.E := by
  have := isGalois_over H
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  exact Fintype.card_of_bijective (GlobalTheory.InducedType.galK_bijective H)

theorem embT_K (τ : Tau R) (a : H.K) : embT H τ (a : H.E) = H.φ₀ (a : H.E) := by
  change H.φ₀ (H.sigmaOf _ _) = _
  rw [sigmaOf_fix_K H _ τ.2 _ a.2]

theorem sum_embT (y : H.E) : ∑ τ, embT H τ y = H.φ₀ ((Algebra.trace H.K H.E y : H.K) : H.E) := by

  rw [coe_trace, map_sum]
  exact Fintype.sum_bijective (GlobalTheory.InducedType.galK H) (GlobalTheory.InducedType.galK_bijective H) _ _ (fun τ => rfl)

theorem isIntegral_half : IsIntegral ℤ ((1 + (⟨H.sqrtMinusD, sqrt_mem H⟩ : H.K)) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := by
    have := H.hyp.2.2.2.1
    exact ⟨(H.d + 1) / 4, by omega⟩
  have hs : (⟨H.sqrtMinusD, sqrt_mem H⟩ : H.K) ^ 2 = -(H.d : H.K) := Subtype.ext (by simpa using H.sqrtMinusD_sq)
  have hm' : (H.d : H.K) + 1 = 4 * m := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp only [eq_intCast, Int.cast_natCast]
  linear_combination (1 / 4 : H.K) * hs - (1 / 4 : H.K) * hm'

end GlobalTheory.Mem.Col2.HostK

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.ChiDet

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem detId_stdL (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)) : Th.detId H (Th.stdL H N) M = detSub M := by
  classical
  unfold Th.detId detSub
  congr 1
  ext z
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨fun j i => A i j, fun j => ?_, (Matrix.det_transpose A).symm⟩
    have h1 : (Pi.single j 1 : Fin N → H.E) ∈ Th.stdL H N := fun k _ => by
      by_cases e : k = j
      · subst e
        rw [Pi.single_eq_same]
        exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne e]
        exact Submodule.zero_mem _
    have h2 := hA _ h1
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(Matrix.of x).transpose, fun v hv => ?_, (Matrix.det_transpose _).symm⟩
    choose b hb using fun i => Submodule.mem_one.1 (hv i trivial)
    have e : (Matrix.of x).transpose.mulVec v = ∑ i, b i • x i := by
      funext j
      rw [Finset.sum_apply]
      show ∑ i, x i j * v i = ∑ i, b i • x i j
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, hb, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx i)

theorem ordSub_detSub_stdL (N : ℕ) (w : HeightOneSpectrum (𝓞 H.E)) : ordSub w (detSub (Th.stdL H N)) = 0 := by
  rw [← detId_stdL, detId_std, Submodule.one_eq_span]
  have h := ordSub_span_singleton w (1 : H.Eˣ)
  rw [Units.val_one] at h
  rw [h]
  simp [_root_.Formalism.L2.Host.ordF]

theorem tildeD_eq_chiId : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : _root_.Formalism.L2.Host.HChar H.E), _root_.Formalism.L2.Host.IsChiPsi H χ → ∀ (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)), Submodule.IsLattice H.E M → ∀ x : DtT H, (QuotientGroup.mk x : DtT H ⧸ UOT H) = relDetT H N (Th.stdL H N) M → ((tildeD H χ x : ℂˣ) : ℂ) = chiId χ (Th.detId H (Th.stdL H N) M) := by
  intro R H χ hχ N M hM x hx
  have hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
    (KerDet.kernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v y hy _ => hχ.unr v y hy) fun v _ => hχ.unr v
  have hU := (ChiLaws.chi_laws R H χ hχ).1
  have hfin : {w : HeightOneSpectrum (𝓞 H.E) | ordSub w (detSub M) ≠ 0}.Finite := by
    by_cases h : ∃ k : H.Eˣ, (k : H.E) ∈ detSub M
    · obtain ⟨k, hk⟩ := h
      exact DetOrd.ordSub_finite (DetOrd.isFractional_detSub M hM.fg) k hk
    · have hz : ∀ w, ordSub w (detSub M) = 0 := by
        intro w
        unfold ordSub
        have he : {n : ℤ | ∃ k : H.Eˣ, (k : H.E) ∈ detSub M ∧ _root_.Formalism.L2.Host.ordF w k = n} = ∅ := by
          ext n
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨k, hk, _⟩
          exact h ⟨k, hk⟩
        rw [he]
        simp
      simp [hz]
  unfold relDetT at hx
  have h1 := hU _ (QuotientGroup.eq.1 hx)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [h1, tildeD_mk H hK, detId_stdL]
  unfold chiId
  congr 1
  simp only [ordSub_detSub_stdL, sub_zero]
  have h2 : Function.HasFiniteMulSupport fun w : HeightOneSpectrum (𝓞 H.E) =>
      _root_.Neutral.B1.localIdele H.E w (_root_.Formalism.L2.Host.atFin w (_root_.Formalism.L2.Host.unif w)) ^ (ordSub w (detSub M)).toNat := by
    refine hfin.subset fun w hw h0 => hw ?_
    simp only [h0, Int.toNat_zero, pow_zero]
  refine ((χ.1.comp (finPartI H.E)).map_finprod h2).trans (finprod_congr fun w => ?_)
  rw [map_pow, MonoidHom.comp_apply, KerDet.finPartI_localIdele]
  rfl

end GlobalTheory.Mem.ChiDet
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke

section
variable {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
  [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']

theorem mem_loc_map_equiv (res : R →+* k) (g : V ≃ₗ[R] V) (M : Submodule R V) (y : V) :
    y ∈ loc res (M.map (g : V →ₗ[R] V)) ↔ g.symm y ∈ loc res M := by
  rw [mem_loc, mem_loc]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [Submodule.mem_map_equiv, map_smul]

theorem act_pairOf_value (res : R →+* k) (g : V ≃ₗ[R] V) (M M' : Submodule R V) (pr : M →+ W) (pr' : M' →+ W')
    (φ : Module.Dual k W) (φ' : Module.Dual k W')
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z)
    (t : R) (z : M) (e : V) (he : t • e = z.1) (h1 : φ (pr z) = 1)
    (hm : e ∈ loc res (M'.map (g : V →ₗ[R] V)))
    (h : ∀ (x : M') (hx : t • g x.1 ∈ M), φ' (pr' x) = φ (pr ⟨_, hx⟩)) :
    ((pairOf res M' pr' φ').act g).f e = 1 := by
  rw [mem_loc_map_equiv] at hm
  obtain ⟨s, hs0, hx⟩ := (mem_loc _ _ _).1 hm
  have e1 : t • g (s • g.symm e) = (s • z : M).1 := by
    rw [map_smul, g.apply_symm_apply, smul_comm, he]; rfl
  have hx2 : t • g (s • g.symm e) ∈ M := by rw [e1]; exact (s • z).2
  have h2 := h ⟨_, hx⟩ hx2
  have e2 : (⟨_, hx2⟩ : M) = s • z := Subtype.ext e1
  rw [locExt_spec res M' pr' hs' _ hm s hx, map_smul, e2, hs, map_smul, h1] at h2
  show φ' (locExt res M' pr' (g.symm e)) = 1
  exact smul_right_injective k hs0 h2

end


theorem up_move_incidence : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (z : ↥(Ld D u i hi c)) (γ : GL (Fin (D.R.N i)) D.host.E), (D.fm u).fv i v c (P.pr v c z) = 1 → loc (A.res v) (mulLat γ.1 (clsCrd D u i hi c')) = loc (A.res v) (Ld D u i hi c) → loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (Ld D u i hi c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) → (∀ (x : ↥(Ld D u i hi c')) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1 *ᵥ x.1) ∈ Ld D u i hi c), (D.fm u).fv i v c' (P.pr v c' x) = (D.fm u).fv i v c (P.pr v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).IsKer (pc P v c).L ∧ ∃ e, ((pc P v c').act (glE γ)).f e = 1 ∧ locExt (A.res v) (Ld D u i hi c) (P.pr v c) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • e) = P.pr v c z := by
  intro D u A i hi P K v c c' z γ h1 h2 h3 h4
  have hT : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have he : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1) = z.1 := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hT, one_smul]
  refine ⟨fun y => ?_, (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1, ?_, ?_⟩
  · rw [Pr.mem_act]
    have h5 := pc_isKer P K v c' ((glE γ).symm y)
    rw [GlobalTheory.T.classLattice_sup_primeDual_localization_eq D u A i hi K v c', ← mem_loc_map_equiv, map_glE, h2] at h5
    exact h5
  · refine act_pairOf_value (A.res v) (glE γ) _ _ (P.pr v c) (P.pr v c') _ _ (P.pr_smul v c) (P.pr_smul v c')
      _ z _ he h1 ?_ h4
    rw [map_glE, h3]
    exact le_loc _ _ (Submodule.mem_sup_right (Submodule.subset_span rfl))
  · rw [he]; exact locExt_coe _ _ _ (P.pr_smul v c) z

end GlobalTheory.LevelHecke
end
