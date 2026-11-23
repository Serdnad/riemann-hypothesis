module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle048
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle432
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle376
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.MainNotions.SumRepresentations.At
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
theorem chiIne_main_alt : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → Formalism.MainNotions.SumRepresentations.adm5 D → MuInt D.nd D.naut →
    ChiIne D.nd D.naut :=
  fun D h0 h2 h5 hMu => _root_.GlobalTheory.SplitRead.chiIne_of_lp_aut_admissible_mult_one D.nd D.naut h0.1 h0.2.1 h2 h5 hMu
end GlobalTheory.SplitRead
end
end
end

section



section
noncomputable section
namespace GlobalTheory.Pass
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
variable {D : D7}
def StepTypeAlt : Prop :=
  ∀ (D : D7) (P : Pend D), admDZ P → SumRepresentations.tie0 D → SumRepresentations.adm1 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → TypeLGC P
def GlobalStatement : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (eρ eχ : ℕ),
    GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → ResSpan i ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r →
    TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → (∃ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S) → π ∈ D.nd.Z i → π ∈ Xs →
    (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw ∧
      LocBoundP i w hw r Xs (WpO D.nd i ρ π) eρ ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, LocBoundP i w hw r Xs (chiRatO D.nd i c) eχ) →
    Br.sFin D.loc D.nbr i ρ π →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    vccCut i Xs π ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * (eρ + D.R.t * eχ) : ℕ) : ℚ) +
      Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) +
      (padicValNat (D.nd.l i) (hE D.host) : ℚ) + 4 * (D.R.nV : ℚ) * D.nd.vdel i +
      (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, vZeta i q
def ResidueStatement : Prop :=
  ∀ D : D7, ResidualAbsIrreducible (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
      ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ResSpan i ρ π
def NoCutStatement : Prop :=
  CentralIdemCoeff ∧ StepCentral ∧ StepDeg ∧ _root_.GlobalTheory.Pass.StepTypeAlt ∧ StepPotDirect ∧ StepPotDual ∧ StepJumpDirect ∧
    StepJumpDual ∧ StepLift ∧ StepSub ∧ StepCont ∧ StepLocDirect ∧ StepLocDual ∧ StepHfChar ∧ _root_.GlobalTheory.Pass.ResidueStatement ∧ _root_.GlobalTheory.Pass.GlobalStatement
end GlobalTheory.Pass
end
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.galoisRepsCusp_of_adm2 : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  first | exact @_root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt | exact _root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt | (intros; apply _root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt <;> assumption)
end
end

section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.TypePrimeEta
end GlobalTheory.TypePrimeEta
namespace GlobalTheory
theorem typePrimeBound_of_etaBound_alt : ∀ (D : D7) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C →
    _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (EtaBound CT) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro D C CT hC hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h7 h8
  obtain ⟨c, hη, hL⟩ := hQ i k k' hkk hl r ρ hr hadm eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hv : (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ 2 * D.R.f * (D.R.r : ℝ) ^ 2 := by
    exact_mod_cast TypePrimeEta.val_cardG0g_le D k k' hkk h2
  have key : ∀ π ∈ D.nd.Zgood i,
      (c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ) ≤ rhs C eta i ρ π := by
    intro π hπ
    obtain ⟨N, r', hN2, hN, hr1, hr4, hc⟩ := hL π hπ
    have hA := TypePrimeEta.first_le D.R.f D.R.r D.R.t CT N r' eta D.R.nV C hC hN2 hN hr4 rfl
    unfold rhs eT
    linarith
  have hη' : (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i,
      (D.nd.mult i π : ℝ) * ((c π : ℝ) + (padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard : ℝ)) := by
    exact_mod_cast hη
  exact hη'.trans (Finset.sum_le_sum fun π hπ => mul_le_mul_of_nonneg_left (key π hπ) (Nat.cast_nonneg _))
end GlobalTheory
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.MuBlock
theorem split_step_o_alt (D : D7) (hT : SumRepresentations.tie0 D) (h3 : SumRepresentations.adm3 D) (h7 : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D)
    (hRS : GlobalTheory.RowCopy.RowSize D) (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)) (hσ : D.what₂.isot (D.nd.j i) σ ≠ ⊥) (hth : thetaOf D.nd D.naut i σ P)
    (hB : IsBCV D.nd D.naut i P Pa) (w : PlE D.host) (hs : IsSplitPl D.host w)
    (hPa : ∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) (hμ : D.naut.unr (D.naut.locG (D.naut.muC i) w)) :
    (∃ p ∈ Pa, D.R.t ≤ p.d) ∧ ∀ p ∈ Pa, D.R.t ≤ p.d → p.d = D.R.t ∧
      D.naut.frobEig (D.naut.locG p.π w) = D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) := by
  have hLP := hT.1
  have hAut := hT.2.1
  have heu := D.naut.etaT_unr w
  have hed : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ _
  obtain ⟨e, he⟩ := frobEig_eq_single D.nd D.naut _ heu hed
  have hen : ‖e‖ = 1 := (D.naut.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; exact Multiset.mem_singleton_self e)
  have he0 : e ≠ 0 := by intro h; rw [h] at hen; simp at hen
  obtain ⟨hbu, hbe⟩ := D.naut.etaTinv_def w
  have hbd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {e⁻¹} := by rw [hbe, he]; simp
  have hbn : ‖e⁻¹‖ = 1 := by rw [norm_inv, hen, inv_one]
  obtain ⟨m, hm⟩ := frobEig_eq_single D.nd D.naut _ hμ (D.naut.locG_dim _ _)
  have hmn : ‖m‖ = 1 := (D.naut.tempered_unr _ hμ).1 (hAut.2.2.2 i w) m (by rw [hm]; exact Multiset.mem_singleton_self m)
  have htw : D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {m * e⁻¹} := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ (e⁻¹) hμ hbu hbd hb, hm]; simp
  have hV := h3 i σ P hth w hs
  have hiso := frobEig_isoLoc D.nd D.naut Pa w hPa
  have hVu : D.naut.unr (D.naut.locV i P w) := by rw [← hB.2.2.2.1 w hs]; exact hiso.1
  have hinv : D.naut.lpChar (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) = D.naut.lpUnr w {1} := by
    have hu := D.naut.unr_char _ _ hed hbu heu
    rw [D.naut.unr_eq_lpUnr _ hu, D.naut.frobEig_char _ _ e hbu heu hed he, hb]; simp [he0]
  have hX : D.naut.lpChar (D.naut.locV i P w) (D.naut.locG D.naut.etaT w) =
      D.naut.lpSum (D.naut.locW i σ w) (spehLoc D.nd D.naut (muPart D.nd D.naut i) w) := by
    rw [hV, (hLP w (D.naut.lpSum (D.naut.locW i σ w) (spehLoc D.nd D.naut (muPart D.nd D.naut i) w))
      (D.naut.locW i σ w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0 hbd hed).2.2.2.1, hinv]
    exact (hLP w _ (D.naut.locW i σ w) (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaT w) 0 hed hed).2.2.2.2.1
  have hXu : D.naut.unr (D.naut.lpSum (D.naut.locW i σ w) (spehLoc D.nd D.naut (muPart D.nd D.naut i) w)) := by
    rw [← hX]; exact D.naut.unr_char _ _ hed hVu heu
  obtain ⟨hWu, hSu⟩ := (D.naut.unr_sum _ _).1 hXu
  have hmu := frobEig_spehLoc D.nd D.naut (muPart D.nd D.naut i) w hμ
  dsimp only [muPart] at hmu
  have hVe : D.naut.frobEig (D.naut.locV i P w) =
      (D.naut.frobEig (D.naut.locW i σ w)).map (· * e⁻¹) +
      ((List.range D.R.t).map fun k => ({(m * e⁻¹) * ((normV w : ℕ) : ℂ) ^
        (((((D.R.t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum := by
    rw [hV, D.naut.frobEig_char _ _ _ hXu hbu hbd hb, D.naut.frobEig_sum _ _ hWu hSu, Multiset.map_add (f := _)]
    dsimp only [muPart]
    rw [hmu.2, hm]
    congr 1
    rw [← Multiset.coe_mapAddMonoidHom, map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Multiset.coe_mapAddMonoidHom, Multiset.map_singleton]
    ring_nf
  have key := UpperTheory.GalN.string_count (normV w) D.R.t (Pa.map fun p => (p.d, D.naut.frobEig (D.naut.locG p.π w)))
    ((D.naut.frobEig (D.naut.locW i σ w)).map (· * e⁻¹)) (m * e⁻¹)
    (by exact_mod_cast GlobalTheory.LocalInv.one_lt_normV w) D.R.t_odd.pos
    (by rw [norm_mul, hmn, hbn, one_mul])
    (by
      intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
      rw [norm_mul, hbn, mul_one]
      have := hRS i σ hσ w hs hWu α hα
      rwa [absNorm_eq_normV] at this)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      have k := _root_.GlobalTheory.PartUnitary.frobEig_openB_and_norm_one_of_isBCV D hT h7 i P Pa hB p hp w (hPa p hp)
      refine ⟨(hB.1 p hp).2.1, ?_, fun α hα => (k α hα).1, fun ht α hα =>
        (k α hα).2 (UpperTheory.GalN.rank_one_of_long hB.2.2.1 hp (hB.1 p hp).1 ht)⟩
      intro h0
      change D.naut.frobEig (D.naut.locG p.π w) = 0 at h0
      have h1 := D.naut.frobEig_card _ (hPa p hp)
      rw [h0, D.naut.locG_dim] at h1
      have := (hB.1 p hp).1
      simp at h1
      omega)
    (by
      have hiso2 := hiso.2
      simp only [GlobalTheory.LocalInv.list_coe, List.map_map] at hiso2
      rw [List.map_map]
      exact hiso2.symm.trans ((congrArg D.naut.frobEig (hB.2.2.2.1 w hs)).trans hVe))
  refine ⟨?_, fun p hp hpt => ?_⟩
  · obtain ⟨x, hx, hxt⟩ := key.1
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact ⟨p, hp, hxt⟩
  · obtain ⟨h1, h2⟩ := key.2 _ (List.mem_map_of_mem (f := fun p : Part D.naut.CG => (p.d, D.naut.frobEig (D.naut.locG p.π w))) hp) hpt
    exact ⟨h1, h2.trans htw.symm⟩
end GlobalTheory.MuBlock
end
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.PassOp
open Formalism.MainNotions.N.PlaceLabelTeichmuller
section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
end Tensor
local instance  (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
local instance  (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
theorem exists_isBCV_twistIso_append_mu_of_mem_Z (D : D7) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h5 : SumRepresentations.adm5 D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D)
    (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ D.nd.Z i) (PI : D.naut.AV i) (hPI : D.naut.ptV i PI = some x) :
    ∃ Sig, IsBCV D.nd D.naut i PI
      (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  obtain ⟨P0, hP0, Pa0, hB0, hm⟩ := (D.Z_tie i x).1 hx
  obtain ⟨Pa, hB⟩ := h1 i PI
  have hperm : Pa0.Perm Pa := ((h41 i).2.1 P0 PI (by rw [hP0]; exact Option.some_ne_none x)
    (hP0.trans hPI.symm)).1 Pa0 Pa hB0 hB
  have hm' := hperm.subset hm
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm'
  set m : Part D.naut.CG := ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ with hmdef
  have hperm2 : (l₁ ++ m :: l₂).Perm ((l₁ ++ l₂) ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hB' := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm2 hB
  have hL : ∀ p ∈ l₁ ++ l₂, 1 ≤ p.a := fun p hp => (hB.1 p (by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))).1
  refine ⟨twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT, ?_⟩
  have e : twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT ++ [muPart D.nd D.naut i])
      D.naut.etaTinv = (l₁ ++ l₂) ++ [m] := by
    rw [show twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT ++ [muPart D.nd D.naut i])
        D.naut.etaTinv = twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT) D.naut.etaTinv ++
          twistIso D.nd D.naut [muPart D.nd D.naut i] D.naut.etaTinv from List.map_append ..,
      twistIso_eta D h0.1 h5.1 _ hL]
    rfl
  rw [e]
  exact hB'
theorem onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem (D : D7) (Q : PairedCharacterCondition.Pend D) (hSer : GlobalTheory.TypeLeaf.SerLoc D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D)
    (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ D.nd.Z i)
    (PI : D.naut.AV i) (hPI : D.naut.ptV i PI = some x) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ D.naut.typeV i PI) :
    (x ∈ D.nd.Zgood i → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F) ∧
    (x ∉ D.nd.Zgood i → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0) := by
  have hon : ∀ σ' : D.ntypes.Par, F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' →
      (D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F) ∧
      (¬ D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0) := fun σ' hF' =>
    idempotent_action_on_forms D (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i)) σ' F fun k v f hf => hSer i σ' k v f F hF' hf
  have hmem : ∀ Sig (σ' : D.ntypes.Par), (∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w) →
      IsBCV D.nd D.naut i PI (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) →
      F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
    intro Sig σ' hσ hB
    have hle : D.naut.typeV i PI ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
      rw [D.mtpar_tie i σ']
      exact le_iSup₂_of_le PI ⟨Sig, fun w => (hσ w).symm, hB⟩ le_rfl
    exact hle hF
  constructor
  · intro hg
    obtain ⟨-, Sig, ⟨P2, hP2, hB2⟩, hgs⟩ := (D.Zgood_tie i x).1 hg
    obtain ⟨Pa, hB⟩ := h1 i PI
    have hperm := ((h41 i).2.1 P2 PI (by rw [hP2]; exact Option.some_ne_none x)
      (hP2.trans hPI.symm)).1 _ Pa hB2 hB
    have hBPI := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hB
    obtain ⟨σ', hσ⟩ := Q.Par_surj i x Sig ⟨P2, hP2, hB2⟩
    exact (hon σ' (hmem Sig σ' hσ hBPI)).1 ((goodPar_iff_goodSig D Sig σ' fun w => (hσ w).symm).2 hgs)
  · intro hg
    obtain ⟨Sig, hB⟩ := _root_.GlobalTheory.PassOp.exists_isBCV_twistIso_append_mu_of_mem_Z D h0 h1 h5 h41 i x hx PI hPI
    obtain ⟨σ', hσ⟩ := Q.Par_surj i x Sig ⟨PI, hPI, hB⟩
    refine (hon σ' (hmem Sig σ' hσ hB)).2 fun hgp => hg ?_
    rw [D.Zgood_tie i x]
    exact ⟨(D.Z_tie i x).1 hx, Sig, ⟨PI, hPI, hB⟩, (goodPar_iff_goodSig D Sig σ' fun w => (hσ w).symm).1 hgp⟩
theorem main_alt_alt : ∀ (D : D7) (Q : PairedCharacterCondition.Pend D), GlobalTheory.Pass.EigSpan Q → GlobalTheory.Pass.CentralElt D → GlobalTheory.TypeLeaf.SerLoc D →
    _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.tieLab D → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm5 D → KillingConditions.CommutingEndomorphismCondition D := by
  intro D Q hEig hCen hSer h41 _ h0 h1 h5 i _ _
  classical
  let zc : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) →
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    fun p => (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose
  let z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    ∑ p, if goodVec D p then zc p else 0
  have hp : ∀ p, PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (zc p : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • tens (fun kv => ESer D kv (p kv)) := by
    intro p
    obtain ⟨L, hnd, hall, he⟩ := (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose_spec
    rw [he]
    congr 1
    have e1 : (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        L.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, prod_plc _ L hnd]
    congr 1
    funext j
    rw [if_pos (hall j)]
  have hz : PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0 := by
    rw [e0_eq, eGood, Finset.smul_sum, AddSubmonoidClass.coe_finsetSum]
    show MonoidAlgebra.mapRingHom _ (iotaO D.nd D.naut i) _ = _

    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact hp p
    · simp
  have hcen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
    Subalgebra.mem_center_iff.2 fun b => (goodElement_mem_center_groupAlgebra D b).symm
  have hact : ∀ F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F := by
    intro F
    rw [hz]
    unfold NTypes.onMt
    rw [dite_eq_left (Subalgebra.smul_mem _ hcen _), dite_eq_left hcen, ← LinearMap.smul_apply, ← map_smul]
    rfl
  refine ⟨Q.zO i z, Q.zO_comm i z, ?_, ?_⟩
  · intro x hx u hu
    have hZ : x ∈ D.nd.Z i := (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1
    have := hEig i z x (D.what₂.restRowsFiniteGroupCard : D.nd.O i) (fun PI hPI F hF => by
      rw [hact, (_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x hZ PI hPI F hF).1 hx, map_natCast]) u hu
    rw [this, ← algebraMap_smul (KK D.nd i) (D.what₂.restRowsFiniteGroupCard : D.nd.O i) u, map_natCast, Int.cast_natCast]
  · intro x hx hxg u hu
    have := hEig i z x 0 (fun PI hPI F hF => by
      rw [hact, (_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x hx PI hPI F hF).2 hxg, smul_zero, map_zero, zero_smul]) u hu
    rw [this, zero_smul]
end GlobalTheory.PassOp
end
end
end

section



section
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section HC
variable {R : Ranks} (P : HCParam R)
end HC
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section JB
variable {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau}
end JB
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section Core
variable {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau}
end Core
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Classical
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
theorem stmtJ_holds_alt (D : D7) : _root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D := by
  intro L hA
  obtain ⟨hG2, hCr, hG2g, hDi, hRd, hP⟩ := hA
  have hF : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ := fun j h1 h2 ρ => jFacts_of hP j h1 h2 ρ
  have hpar : L.etaSz + D.R.t + L.Sc ≤ L.sc.b := by
    have := L.Sc_pos; have := L.etaSz_pos
    have : (0 : ℝ) ≤ D.R.t := by positivity
    linarith [hP.1, hP.2.1]
  exact ⟨_root_.GlobalTheory.JumpSets.jumpLemma_a_of_admissible_alt_alt hP hG2 hCr hG2g hDi hRd, jumpSetBound_of_realPlaceFacts hF, jumpSetCloud_of_realPlaceFacts hF, jumpSetDistinct_of_realPlaceFacts hF,
    jumpSetEta_of_realPlaceFacts hF hpar D.R.t_odd.pos L.Sc_pos L.etaSz_pos, jumpSetFinal_of_realPlaceFacts hF, jumpSetGap_of_realPlaceFacts hF⟩
end GlobalTheory.JumpSets
end
end
end

section



section
noncomputable section
namespace GlobalTheory.TameEig
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
abbrev _root_.GlobalTheory.TameEig.eigPd_holds_tyz : Prop :=  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D → _root_.GlobalTheory.StringRepresentationDecomposition.LocalGlobalCompatible D → RbEx D → EigPd D
end GlobalTheory.TameEig
end
end
end

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace GlobalTheory.MuCharProof
abbrev _root_.GlobalTheory.MuCharProof.muChar_holds_tyz : Prop :=  _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition
end GlobalTheory.MuCharProof
end
end
end
