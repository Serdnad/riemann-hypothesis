module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle106
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle293
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle301
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle294
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.PairSetting

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GlobalTheory.Cusp.wittIndex (Vc D i) = 0 ∧ (Wc D i).rank < D.R.t ∧ ∃ cA : GlobalTheory.Mem.Th.CptF (Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.HidaSetting R.θ (Wc D i) (Vc D i) (cart (R.MW i σ)) (fun _ => 1) D.R.t cA ∧ ∀ U ∈ R.Wall i σ, ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, U (fun ρ => v ρ) ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := by
  intro D G _ _ Pl0 T' A Ks _ _ _ R F hC _ i σ
  have hi1 : 1 ≤ (i : ℕ) + 1 := Nat.le_add_left 1 _
  have hi2 : (i : ℕ) + 1 ≤ D.R.m := i.isLt
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ hi1 hi2
  have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ hi1 hi2
  have hk := D.R.rank_add_five_le
  have hm := D.R.two_le_m
  obtain ⟨cA, hF, hcart, hJ, hA0⟩ := GlobalTheory.T.multiplicity_map_apply_mem_A0_of_kfin D R.θ hC.models.inf (Wc D i) (D.sp.W_sig _) _ (R.MW i σ)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig (↑i + 1) (tauE D τ)
    rw [hC.models.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  refine ⟨GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Per.isAniso_of_posDef (D.sp.V_sig _) (hC.models.vpos i)), ?_, cA, ⟨?_, ?_, ?_, hC.models.inf, D.sp.W_sig _, hF, hcart, fun τ => ⟨by simp, by simp, by simpa using hpos τ⟩, hJ⟩, ?_⟩
  · rw [hW]; simp only [Ranks.r] at *; omega
  · rw [hW]; simp only [Ranks.r] at *; omega
  · simp only [Ranks.r] at *; omega
  · rw [hV, hW]; rfl
  · intro U hU v
    exact hA0 _ _ U hU (fun ρ => v ρ) (fun τ => GlobalTheory.T.lowestKType_mem_discreteSeriesKFiniteVectors D (Wc D i) _ (R.MW i σ) τ (v τ))

end GlobalTheory.PairSetting
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.boxProducts_orthogonalSum_target_cartan_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → ∃ (sB : RealMat B) (LB : Lat B), (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧ IsSelfDualC B LB ∧ (∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA sB (o.boxT A Φ Φ')) ∧ ∀ (LA : Lat A) (Sf : Finset (FinPl D)) Φ Φ', IsSphOff ψ A W LA (frameLat W) Sf Φ → IsSphOff ψ A H LA (frameLat H) Sf Φ' → IsSphOff ψ A B LA LB Sf (o.boxT A Φ Φ') := by
  first | exact @GlobalTheory.Core.Rk.SumBox.box_sum_target | exact GlobalTheory.Core.Rk.SumBox.box_sum_target | (intros; apply GlobalTheory.Core.Rk.SumBox.box_sum_target <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.FockSlice

theorem exists_finset_inf_eq_iInf {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (U : I → Submodule K V) : ∃ F : Finset I, F.inf U = ⨅ i, U i := by
  classical
  have hex : ∃ n, ∃ F : Finset I, Module.finrank K ((F.inf U : Submodule K V)) = n := ⟨_, ∅, rfl⟩
  obtain ⟨F, hF⟩ := Nat.find_spec hex
  refine ⟨F, le_antisymm (le_iInf fun i => ?_) (Finset.le_inf fun i _ => iInf_le U i)⟩
  have hle : (insert i F).inf U ≤ F.inf U := Finset.inf_mono (Finset.subset_insert i F)
  have hmin : Nat.find hex ≤ Module.finrank K (((insert i F).inf U : Submodule K V)) := Nat.find_min' hex ⟨_, rfl⟩
  have heq : (insert i F).inf U = F.inf U := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq]
  exact Finset.inf_le (Finset.mem_insert_self i F)

theorem exists_eval_recon {Y : Type} (W : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (S : Finset Y) (g' : Y → Y → ℂ), (∀ y, g' y ∈ W) ∧ ∀ g ∈ W, g = ∑ y ∈ S, g y • g' y := by
  classical
  let U : Y → Submodule ℂ W := fun y => LinearMap.ker ((LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp W.subtype)
  obtain ⟨S, hS⟩ := exists_finset_inf_eq_iInf U
  let R : W →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun s => (LinearMap.proj (s : Y) : (Y → ℂ) →ₗ[ℂ] ℂ).comp W.subtype
  have hR : LinearMap.ker R = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hmem : w ∈ S.inf U := by
      rw [Submodule.mem_finsetInf]
      intro y hy
      have := congrFun hw ⟨y, hy⟩
      simpa [U, R] using this
    rw [hS, Submodule.mem_iInf] at hmem
    ext y
    simpa [U] using hmem y
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
  refine ⟨S, fun y => if h : y ∈ S then (L (Pi.single ⟨y, h⟩ 1) : Y → ℂ) else 0, fun y => ?_, fun g hg => ?_⟩
  · by_cases h : y ∈ S
    · simp only [h, dite_true]; exact (L _).2
    · simp only [h, dite_false]; exact W.zero_mem
  · have h1 : (⟨g, hg⟩ : W) = L (R ⟨g, hg⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨g, hg⟩ = ∑ s : S, g s • (Pi.single s 1 : S → ℂ) := by
      ext t
      simp [R, Finset.sum_apply, Pi.single_apply]
    have h3 := congrArg Subtype.val h1

    rw [h2, map_sum] at h3
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
    refine h3.trans ?_
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [s.2]

end GlobalTheory.StdUnn.FockSlice

namespace GlobalTheory.StdUnn.FockSlice

theorem mem_fockA_of_slices : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), ∀ φ ∈ schwartzA θ V.rank n, (∀ x₀ : Mx D V.rank n, ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ x : Mx D V.rank n, x.map (finPart D) = x₀.map (finPart D) → φ x = evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x)) → φ ∈ fockA θ V n l s := by
  intro D θ hθ V n l s φ hφ hslice
  classical
  obtain ⟨k, c, t, rfl⟩ := Submodule.mem_span_set'.1 hφ
  choose F G hG hFG using fun i => (t i).2
  let fin : Mx D V.rank n → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun x i j => finPart D (x i j)
  let Pre : ((Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) →ₗ[ℂ] (Mx D V.rank n → ℂ) :=
    LinearMap.funLeft ℂ ℂ fin
  let W : Submodule ℂ (Mx D V.rank n → ℂ) := Submodule.span ℂ (Set.range fun i => Pre (G i))
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  obtain ⟨S, g', hg'W, hrec⟩ := exists_eval_recon W
  have hWle : W ≤ (WeilM.SB _).map Pre := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨G i, hG i, rfl⟩)
  choose g'' hg''SB hg''eq using fun y => hWle (hg'W y)
  choose pt hpt _ using fun x y : Mx D V.rank n => GlobalTheory.T.existsUnique_adelicMatrix_realComponents_finitePart D θ hθ V.rank n (fun τ => compAt θ τ x) y
  choose p hp using hslice
  set Φ : Mx D V.rank n → ℂ := ∑ i, c i • (t i : Mx D V.rank n → ℂ) with hΦ
  have hΦx : ∀ x, Φ x = ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin x)) := by
    intro x
    simp only [hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFG i]
  have hpt' : ∀ x y, Φ (pt x y) = ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) := by
    intro x y
    rw [hΦx]
    have e1 : (fun τ a b => compAt θ τ (pt x y) a b) = (fun τ a b => compAt θ τ x a b) := by
      funext τ a b; rw [(hpt x y).1 τ]
    have e2 : fin (pt x y) = fin y := by
      funext a b
      have := congrFun (congrFun (hpt x y).2 a) b
      simpa [fin, Matrix.map_apply] using this
    rw [e1, e2]
  have hG' : ∀ i x, G i (fin x) = ∑ y ∈ S, G i (fin y) * g' y x := by
    intro i x
    have := congrFun (hrec (Pre (G i)) (Submodule.subset_span ⟨i, rfl⟩)) x
    simpa [Pre, LinearMap.funLeft_apply, Finset.sum_apply, smul_eq_mul] using this
  have key : ∀ x, Φ x = ∑ y ∈ S, Φ (pt x y) * g' y x := by
    intro x
    rw [hΦx]
    calc ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin x))
        = ∑ i, ∑ y ∈ S, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) * g' y x :=
          Finset.sum_congr rfl fun i _ => by
            rw [hG' i x, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ y ∈ S, ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) * g' y x := Finset.sum_comm
      _ = ∑ y ∈ S, Φ (pt x y) * g' y x := Finset.sum_congr rfl fun y _ => by rw [hpt', Finset.sum_mul]
  have hfin : ∀ x y, (pt x y).map (finPart D) = y.map (finPart D) := fun x y => (hpt x y).2
  have hcomp : ∀ x y, (fun τ => compAt θ τ (pt x y)) = (fun τ => compAt θ τ x) := fun x y => funext (hpt x y).1
  have hEq : Φ = ∑ y ∈ S, (fun x => evalPoly (p y) (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g'' y (fun i j => finPart D (x i j))) := by
    funext x
    rw [key x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hp y (pt x y) (hfin x y), hcomp x y]
    congr 1
    rw [← hg''eq y]
    rfl
  rw [hEq]
  exact Submodule.sum_mem _ fun y _ => Submodule.subset_span ⟨p y, g'' y, hg''SB y, rfl⟩

end GlobalTheory.StdUnn.FockSlice
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.FinComb

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem isFinComb_zero : IsFinComb ψ S T f₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩

theorem isFinComb_add {f g : WO S T → ℂ} (hf : IsFinComb ψ S T f₀ f) (hg : IsFinComb ψ S T f₀ g) :
    IsFinComb ψ S T f₀ (f + g) := by
  obtain ⟨n, c, x, hx, rfl⟩ := hf
  obtain ⟨m, c', x', hx', rfl⟩ := hg
  refine ⟨n + m, Fin.append c c', Fin.append x x', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]; exact hx i
    · rw [Fin.append_right]; exact hx' i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem isFinComb_smul (a : ℂ) {f : WO S T → ℂ} (hf : IsFinComb ψ S T f₀ f) : IsFinComb ψ S T f₀ (a • f) := by
  obtain ⟨n, c, x, hx, rfl⟩ := hf
  exact ⟨n, fun k => a * c k, x, hx, by rw [Finset.smul_sum]; simp only [smul_smul]⟩

theorem isFinComb_single (a : ℂ) (x : WO S T) (hx : x.map (infPart D) = 0) :
    IsFinComb ψ S T f₀ (a • heisO ψ S T x f₀) :=
  ⟨1, fun _ => a, fun _ => x, fun _ => hx, by simp⟩

end GlobalTheory.AdForm.FinComb

namespace GlobalTheory.AdForm

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.AdForm.FinComb

theorem isFinComb_of_isThetaAt : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D) (f₀ Φ f : WO S T → ℂ),
    IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → e * e = e → infPart D e = 0 →
    IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ →
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f →
    IsFinComb ψ S T f₀ f := by
  intro D ψ S T ΛS ΛT e f₀ Φ f hψ hS hT he hinf hΦ hθ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  rw [hall Tm hTm]
  clear hall
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy]
    refine isFinComb_single _ _ ?_
    have h1 := infPart_of_half hinf ((isHalf_iff S T).2 hx)
    have h2 := infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy)
    ext i j
    have a1 := congrFun (congrFun h1 i) j
    have a2 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at a1 a2 ⊢
    rw [RingHom.map_add (f := _), a1, a2, add_zero]
  | zero => rw [LinearMap.map_zero]; exact isFinComb_zero
  | add g g' _ _ hg hg' => rw [LinearMap.map_add (f := _)]; exact isFinComb_add hg hg'
  | smul c g _ hg => rw [LinearMap.map_smul]; exact isFinComb_smul c hg

end GlobalTheory.AdForm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FinRestComm

variable {D : D7}

theorem finPart_finRat_sub {S T : HSp D} (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank)
    (j : Fin S.rank) : finPart D (GlobalTheory.VacUnique.finRat S T M i j - incA D (M i j)) = 0 := by
  rw [RingHom.map_sub]
  exact sub_eq_zero.2 ((GlobalTheory.LatVac.finPart_pair 1 (M i j)).trans (GlobalTheory.LatVac.finPart_incA (M i j)).symm)

theorem infPart_of_idemSum {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hI : IsIdemSum e SS) :
    infPart D e = 0 := by
  obtain ⟨⟨es, hes, he⟩, -⟩ := hI
  subst he
  induction SS using Finset.induction_on with
  | empty => rw [Finset.sum_empty, RingHom.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem (hes a (Finset.mem_insert_self a s)).1,
      ih fun PP hPP => hes PP (Finset.mem_insert_of_mem hPP), add_zero]

theorem smul_rest_eq_zero {S T : HSp D} {e : AE D} (hee : e * e = e) (hinf : infPart D e = 0)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    e • (GlobalTheory.VacUnique.finRat S T M - M.map (fun r => e * incA D r)) = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.zero_apply, smul_eq_mul, mul_sub,
    ← mul_assoc, hee, ← mul_sub]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]
  · rw [RingHom.map_mul, finPart_finRat_sub, mul_zero, RingHom.map_zero]

theorem char_sympl_rest_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplO S T ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r)) (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y'))) = 1 := by
  intro D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP x' hx' y' hy'
  have hZ := GlobalTheory.T.halfA_components_mem_completedLattice_offPrimes D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP x' hx'
  have hY := GlobalTheory.T.halfB_components_mem_completedLattice_offConj D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP y' hy'
  have heZ := smul_rest_eq_zero (S := S) (T := T) (GlobalTheory.PlaceDatum.idemSum_mul_self hI) (infPart_of_idemSum hI)
    (LinearMap.toMatrix' x')
  have hsplit : GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') =
      (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') -
        (LinearMap.toMatrix' y').map (fun r => cA D e * incA D r)) +
      cA D e • (LinearMap.toMatrix' y').map (incA D) := by
    have : (LinearMap.toMatrix' y').map (fun r => cA D e * incA D r) =
        cA D e • (LinearMap.toMatrix' y').map (incA D) := Matrix.ext fun i j => rfl
    rw [this, sub_add_cancel]
  rw [hsplit, ← GlobalTheory.LatVac.symplHom_apply, map_add (f := _), AddChar.map_add_eq_mul, GlobalTheory.LatVac.symplHom_apply,
    GlobalTheory.LatVac.symplHom_apply, ← GlobalTheory.SplitScalar.symplO_smul, heZ, GlobalTheory.SplitScalar.symplO_zero_left,
    AddChar.map_zero_eq_one, mul_one]
  exact GlobalTheory.LatVac.char_sympl_eq_one hP.std hN hN' hZ hY

end GlobalTheory.FinRestComm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartScalarForm_adelicPoint_eq_classTransport : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b (c : (I.chain l u a).cls j) (d : (I.stp u a j).D c.1)
    (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (z : TC.GA B (B.R.N j)), x ∈ GfC _ →
    z.1 = finM _ (rankN (I.rec7 l Z) j hj) x → TC.PtOf (z * A.kb j b) (extTo I.SQ d.1.1) →
    A.chOf j ((I.stp u a j).cl c.1 d) = b →
    cosetIn d = cosetIn ((I.stp u a j).rep ((I.stp u a j).cl c.1 d)) → ∀ y,
      A.rd θ j hj b φ y x = (I.stp u a j).trTo B.fields.emb B.embLL c.1 d (φ ((I.stp u a j).cl c.1 d)) y := by
  first | exact @GlobalTheory.AdForm.rd_trTo | exact GlobalTheory.AdForm.rd_trTo | (intros; apply GlobalTheory.AdForm.rd_trTo <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.standardUnitaryChart_mem_rational_iff : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g, g ∈ GQ (dblSp A) ↔ κ g ∈ GF D A.rank := by
  first | exact @GlobalTheory.StdUnn.chart_mem_GF_iff | exact GlobalTheory.StdUnn.chart_mem_GF_iff | (intros; apply GlobalTheory.StdUnn.chart_mem_GF_iff <;> assumption)
end
