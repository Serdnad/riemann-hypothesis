module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ReductionConjugacy
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle346
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle011
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.RationalFrame

open NumberField Formalism.L2.SG.PoincareInHH

theorem hJ_lin {n : ℕ} (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (x : Fin n → ℂ) (g : ι → ℂ)
    (y : ι → Fin n → ℂ) (c : ℂ) (w : Fin n → ℂ) :
    hJ ε x (∑ i, g i • y i + c • w) = ∑ i, g i * hJ ε x (y i) + c * hJ ε x w := by
  unfold hJ
  simp only [mulVec_add, mulVec_sum, mulVec_smul, dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem frame_linearIndependent (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    LinearIndependent ℂ (Formalism.L2.SG.RealObj.frm X u 1 v) := by
  have hfr : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam (fun a => rv X.B.I v (X.eR a))
      (rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]
  have hze : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.eR a)) = 0 := by
    intro a
    refine (Cut.hJ_crd X v _ _).trans ?_
    have h := (VS D).herm.eq (X.eX a) (X.zu u)
    rw [(X.zu_orth u a).1] at h
    rw [← h]
    simp
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) ≠ 0 := by
    rw [HidaSetting.zR, Cut.hJ_crd X v, X.zu_norm]
    simp only [map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]
    exact ((D.mem u).A.T_prime).ne_zero
  have hfe : ∀ j a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR a)) = if a = j then 1 else 0 := by
    intro j a
    refine (Cut.hJ_crd X v _ _).trans ?_
    rw [Cut.hT_f_e X]
    split_ifs <;> simp
  have hfz : ∀ j, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.zR u)) = 0 := by
    intro j
    refine (Cut.hJ_crd X v _ _).trans ?_
    rw [(X.zu_orth u j).2]
    simp
  rw [hfr, Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_castSucc] at hg
  simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last] at hg
  have hlast : g (Fin.last _) = 0 := by
    have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.zR u))) hg
    rw [hJ_lin] at h
    simp only [hze, mul_zero, Finset.sum_const_zero, zero_add] at h
    unfold hJ at h
    simp only [mulVec_zero, dotProduct_zero] at h
    exact (mul_eq_zero.1 h).resolve_right hzz
  intro i
  refine Fin.lastCases hlast (fun j => ?_) i
  have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg
  rw [hJ_lin, hfz] at h
  simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero] at h
  unfold hJ at h
  simp only [mulVec_zero, dotProduct_zero] at h
  exact h

end GlobalTheory.RationalFrame
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Sloc.OneDim

theorem nV_pos (D : D7) : 0 < nV D := by
  have h := D.sp.Y_rank 0 (Nat.zero_le _)
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  show 0 < (D.sp.Y 0).rank
  rw [h]
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, zero_mul, add_zero]
  omega

def lineMap (D : D7) : D.host.E →ₗ[𝓞 D.host.E] (VS D).V :=
  (LinearMap.toSpanSingleton D.host.E (VS D).V ((VS D).frame ⟨0, nV_pos D⟩)).restrictScalars (𝓞 D.host.E)

theorem lineMap_injective (D : D7) : Function.Injective (lineMap D) := by
  intro a b h
  have h' : a • (VS D).frame ⟨0, nV_pos D⟩ = b • (VS D).frame ⟨0, nV_pos D⟩ := h
  exact smul_left_injective D.host.E ((VS D).frame.ne_zero _) h'

theorem localLattice_map (D : D7) (Z : LocDat D) (p : PlF D) (K : Submodule (𝓞 D.host.E) D.host.E) :
    lattice₂ D Z.M p (K.map (lineMap D)) =
      (Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (K : Set D.host.E))).map
        ((LinearMap.toSpanSingleton (D.s.atP p).Ep (Vp D p) (Pi.single ⟨0, nV_pos D⟩ 1)).restrictScalars (Z.M p).L.O) := by
  have key : ∀ k : D.host.E, baseChange₂ D p (lineMap D k) =
      LinearMap.toSpanSingleton (D.s.atP p).Ep (Vp D p) (Pi.single ⟨0, nV_pos D⟩ 1) ((D.s.atP p).ιE k) := by
    intro k
    have h1 : lineMap D k = k • (VS D).frame ⟨0, nV_pos D⟩ := rfl
    rw [h1, baseChange_smul₂, baseChangeAt_frame, LinearMap.toSpanSingleton_apply]
  unfold Formalism.L2.SG.TermLoc.lattice₂
  rw [Submodule.map_span]
  congr 1
  ext v
  simp only [Submodule.map_coe, Set.mem_image, SetLike.mem_coe, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨(D.s.atP p).ιE k, ⟨k, hk, rfl⟩, (key k).symm⟩
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨lineMap D k, ⟨k, hk, rfl⟩, key k⟩

private theorem le_of_locP_eq_forall_heightOneSpectrum {D : D7} {A B : Submodule (𝓞 D.host.E) (VS D).V}
    (h : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B) : A ≤ B := by
  intro x hx
  by_contra hxB
  let c : Ideal (𝓞 D.host.E) := B.comap (LinearMap.toSpanSingleton (𝓞 D.host.E) (VS D).V x)
  have hc : c ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 D.host.E) ∈ c := htop ▸ Submodule.mem_top
    apply hxB
    simpa [c, LinearMap.toSpanSingleton_apply] using h1
  obtain ⟨M, hM, hcM⟩ := Ideal.exists_le_maximal c hc
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E) :=
    ⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField D.host.E)).ne'⟩
  have hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A :=
    show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ A from ⟨1, P.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩
  rw [h P] at hxA
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ B := hxA
  exact hs (hcM (show s ∈ c by simpa [c, LinearMap.toSpanSingleton_apply] using hsx))

end GlobalTheory.Sloc.OneDim


open GlobalTheory.Sloc.OneDim in
theorem GlobalTheory.Sloc.fg_eq_of_completions : ∀ (D : D7) (Z : LocDat D) (I J : Submodule (𝓞 D.host.E) D.host.E), I.FG → J.FG → (∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (I : Set D.host.E)) = Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (J : Set D.host.E))) → I = J := by
  intro D Z I J hI hJ hloc
  have hlat : ∀ p : PlF D, lattice₂ D Z.M p (I.map (lineMap D)) = lattice₂ D Z.M p (J.map (lineMap D)) := by
    intro p
    rw [localLattice_map, localLattice_map, hloc p]
  have hEq := Formalism.L2.SG.Pf.locEqC_holds D Z
  unfold Formalism.L2.SG.Pf.LocEqC at hEq
  have hP : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (I.map (lineMap D)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (J.map (lineMap D)) := by
    intro P
    let p : PlF D := ⟨P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _,
      fun h => P.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)⟩
    exact (hEq p _ _ (hI.map _) (hJ.map _)).1 (hlat p) P rfl
  have hAB : I.map (lineMap D) = J.map (lineMap D) :=
    le_antisymm (OneDim.le_of_locP_eq_forall_heightOneSpectrum hP) (OneDim.le_of_locP_eq_forall_heightOneSpectrum fun P => (hP P).symm)
  exact Submodule.map_injective_of_injective (lineMap_injective D) hAB
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem coeff_goodAt_eq (D : D7) (X : HidaSetting D) (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ b, a * b = b * a)
    (x : X.B.I.Gf) (γ γ' : G0g D.nd) (h : GoodAt X x γ) (h' : GoodAt X x γ') : a.coeff γ' = a.coeff γ := by
  have hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      γ' kv = P⁻¹ * γ kv * P := by
    intro kv
    exact Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw kv.1 kv.2))
      (D.host.g kv.1) (D.host.g_prime kv.1)
      (by rw [Formalism.L2.SG.Pf.RowDictPf.card_wB, Formalism.L2.SG.Pf.RowDictPf.card_res_host]) D.R.r X.n_eq.symm x (γ kv) (γ' kv)
      ((Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ x _).1 (h kv))
      ((Formalism.L2.SG.Pf.RowDictPf.redMat_iff X _ _ x _).1 (h' kv))
  choose P hP using hP
  have e : γ' = (P : G0g D.nd)⁻¹ * γ * P := funext fun kv => hP kv
  rw [e]
  exact Formalism.L2.SG.Pf.RowDictPf.coeff_conj_of_central ha γ P

theorem coeff_chosenRed_eq_redHom : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd), IsRedHom X red →
    ∀ a : MonoidAlgebra ℂ (G0g D.nd), (∀ b, a * b = b * a) → ∀ x : X.B.I.Gf,
    (if h : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ then
      a.coeff (Classical.choose h.2) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0) =
    if x ∈ X.B.I.Kset then a.coeff (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0 := by
  intro D X red hred a ha x
  by_cases hx : x ∈ X.B.I.Kset
  · have hc : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ := ⟨hx, red x, hred.1 x hx⟩
    rw [dite_eq_left hc, if_pos hx,
      coeff_goodAt_eq D X a ha x (red x) (Classical.choose hc.2) (hred.1 x hx) (Classical.choose_spec hc.2)]
  · rw [dite_eq_right (fun h => hx h.1), if_neg hx]

end GlobalTheory
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u), ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∧ ∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
  first | exact @GlobalTheory.GamRat.gam_rat | exact GlobalTheory.GamRat.gam_rat | (intros; apply GlobalTheory.GamRat.gam_rat <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_unitary_fixing_mem_rationalStabiliser : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ₀ : GL (Fin X.B.I.n) X.B.I.E), γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ γ : Gam X u, (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
  first | exact @GlobalTheory.St.rat_unitary_fixing_mem_gam | exact GlobalTheory.St.rat_unitary_fixing_mem_gam | (intros; apply GlobalTheory.St.rat_unitary_fixing_mem_gam <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct ENNReal

namespace GlobalTheory.TraceSelfDual

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [Field R] [Algebra F R]
  (ι : Type) [Fintype ι]

noncomputable def traceBilin : LinearMap.BilinForm R (ι → R ⊗[F] E) :=
  LinearMap.mk₂ R (fun x y => ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i))
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])

theorem traceBilin_apply (x y : ι → R ⊗[F] E) :
    traceBilin R ι x y = ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i) := rfl

theorem traceBilin_symm (x y : ι → R ⊗[F] E) : traceBilin R ι x y = traceBilin R ι y x := by
  simp only [traceBilin_apply, mul_comm]

variable [NumberField F] [NumberField E]

theorem eq_zero_of_traceBilin {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : ι → R ⊗[F] E)
    (hx : ∀ y, traceBilin R ι x y = 0) : x = 0 := by
  classical
  funext j
  refine GlobalTheory.SelfDualFinite.eq_zero_of_trace R h _ fun c => ?_
  have := hx (Pi.single j c)
  rw [traceBilin_apply, Finset.sum_eq_single j] at this
  · rwa [Pi.single_eq_same, mul_comm] at this
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mul_zero, map_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Form

theorem exists_selfDual_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), (∃ r, psiV F ψ v r ≠ 1) → ∀ (ι : Type) [Fintype ι], ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i))) := by
  intro F E _ _ _ _ _ σ h ψ hψ v hne ι _
  let χ : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom
    ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)
  have hc : Continuous χ :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖χ t‖ = 1 := fun t => hψ.2.1 _
  exact (GlobalTheory.SelfDualFinite.existsUnique_of_bilin v χ hc hu hne _ (traceBilin (Fv F v) ι)
    (traceBilin_symm _ ι) (eq_zero_of_traceBilin _ ι h)).exists

end GlobalTheory.TraceSelfDual
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.measure_preimage_reindex_scale_complex_le : ∀ (ι ι' κ κ' : Type) [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] (e : ι ≃ ι') (f : κ ≃ κ') (ρ c : ℝ) (d : κ → ℕ), 1 ≤ ρ → c ≤ 1 → ∀ A : Set (ι → κ → ℂ), MeasurableSet A → (MeasureTheory.Measure.pi fun _ : ι' => MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ((fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
  first | exact @GlobalTheory.CoordScale.measure_preimage_reindex_scale_le | exact GlobalTheory.CoordScale.measure_preimage_reindex_scale_le | (intros; apply GlobalTheory.CoordScale.measure_preimage_reindex_scale_le <;> assumption)
end
