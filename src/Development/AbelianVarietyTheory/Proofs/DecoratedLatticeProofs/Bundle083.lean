module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle081
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle081
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle041
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.ZonalCoeff

open Formalism.UG

theorem apply_heckeVec {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}
    (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Formalism.UG.Hecke ℂ K) (ρ : Representation ℂ G V) (x : V)
    (l : V →ₗ[ℂ] ℂ) : l (GlobalTheory.LFun.heckeVec ρ K h x) = ∑ᶠ c : G ⧸ K, h c.out * l (ρ c.out x) :=
  (l.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK hh ρ x)).trans (finsum_congr fun c => by simp)

theorem eq_zero_of_doset_sum {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K) {w : G → ℂ}
    (hw : IsBiInv K w) (g : G) (e : ∑ᶠ c : G ⧸ K, dosetInd ℂ K g c.out * w c.out = 0) : w g = 0 := by
  classical
  have hfin := Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem G K ℂ g).2
  have hmem : ∀ c ∈ hfin.toFinset, c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K := fun c hc => by
    by_contra hn
    exact (hfin.mem_toFinset.1 hc) (Set.indicator_of_notMem hn _)
  have h1 : ∀ c ∈ hfin.toFinset, dosetInd ℂ K g c.out * w c.out = w g := fun c hc => by
    obtain ⟨a, ha, b, hb, e'⟩ := DoubleCoset.mem_doubleCoset.1 (hmem c hc)
    rw [dosetInd, Set.indicator_of_mem (hmem c hc), Pi.one_apply, one_mul, e']
    exact hw ⟨a, ha⟩ ⟨b, hb⟩ g
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ fun c hc =>
      hfin.mem_toFinset.2 (left_ne_zero_of_mul hc),
    Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul] at e
  refine (mul_eq_zero.1 e).resolve_left (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), ?_⟩))
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  refine hfin.mem_toFinset.2 ?_
  change dosetInd ℂ K g _ ≠ 0
  rw [dosetInd, Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩)]
  exact one_ne_zero

theorem coeff_zero_or_zonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x = 0 → ∀ g, ℓ (ρ g x) = 0) ∧ (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α fun g => ℓ (ρ g x) / ℓ x) := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ x α hx l hl
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have hbi : IsBiInv (KU σ n) fun g => l (ρ g x) := fun a b g => by
    beta_reduce
    rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ b.2, hl _ a.2]
  refine ⟨fun h0 g => eq_zero_of_doset_sum hK hbi g ?_, fun h0 => ⟨fun a b g => ?_, ?_, fun h hh => ?_⟩⟩
  · have hm := Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g
    rw [← apply_heckeVec hK hm, hx.2.2 _ hm, map_smul, h0, smul_zero]
  · exact congrArg (· / l x) (hbi a b g)
  · simpa using div_self h0
  · have e := apply_heckeVec hK hh ρ x ((l x)⁻¹ • l)
    rw [hx.2.2 h hh, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ h0, mul_one] at e
    rw [e]
    exact finsum_congr fun c => by simp [div_eq_inv_mul]

end GlobalTheory.ZonalCoeff
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.schwartzBruhat_mul_addChar_linearForm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] (f : Matrix R Q k →ₗ[k] k) (z : k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => (ψ (f x + z) : ℂ) * Φ x) ∈ SB (Matrix R Q k) := by
  first | exact @GlobalTheory.PartRed.sb_mul_addChar_linear | exact GlobalTheory.PartRed.sb_mul_addChar_linear | (intros; apply GlobalTheory.PartRed.sb_mul_addChar_linear <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LocValSplit
open GlobalTheory.LFun (LvTw_eq eulerFac_eq_prod etaU locL etaFam_of_unram eulerFac_singleton mem_aboveF)

theorem LvTw_div_dv_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (s : ℂ), IsSplit (E := E) v → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → m w * m w' = 1 → LvTw B m v (s + 1 / 2) / dv E r b v s = eulerFac ((B w).map ((m w)⁻¹ * ·)) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))) := by
  intro F E _ _ _ _ _ B m v w w' r b s hsplit hunr hne hv hqw hqw' hB' hm1
  classical
  set X : ℂ := GlobalTheory.LFun.npow w (-(s + 1 / 2)) with hXdef
  set μ : ℂ := (m w : ℂ) with hμ
  have hX' : GlobalTheory.LFun.npow w' (-(s + 1 / 2)) = X := by rw [hXdef, GlobalTheory.LFun.npow, GlobalTheory.LFun.npow, hqw, hqw']
  have hinv : ((m w' : ℂ))⁻¹ = μ := inv_eq_of_mul_eq_one_left (by rw [hμ, ← Units.val_mul, hm1, Units.val_one])
  have e : Formalism.L2.Host.aboveF (L := E) F v = {w, w'} := by ext u; simp [mem_aboveF, hv]
  have hL : LvTw B m v (s + 1 / 2) = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod *
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [LvTw_eq, e, Finset.prod_pair hne, hB', Multiset.map_map, hX', hinv]
    simp only [Function.comp_def, Units.val_inv_eq_inv_val]
    rfl
  have hr1 : eulerFac ((B w).map ((m w)⁻¹ * ·)) X = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val, hμ]
    ring
  have hr2 : eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) X =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv, inv_inv, hμ]
    ring
  have hd : dv E r b v s = (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))))⁻¹ := by
    rw [← Finset.prod_inv_distrib, dv]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hu : etaU E v = 1 := by unfold etaU; rw [if_pos hsplit]
    rw [locL, etaFam_of_unram hunr, hu, one_pow, eulerFac_singleton, Units.val_one, one_mul, GlobalTheory.LFun.npow, qV, hqw]
  rw [hd, div_inv_eq_mul, hL, hr1, hr2]

end GlobalTheory.LocValSplit
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.heisenbergInvariant_factors_contraction : GlobalTheory.LocFlat.ContrFactor := by
  first | exact @GlobalTheory.LocFlat.contrFactor | exact GlobalTheory.LocFlat.contrFactor | (intros; apply GlobalTheory.LocFlat.contrFactor <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.ParHeckeCard

section general
variable {G : Type} [Group G]

def dcos (J : Subgroup G) (g : G) : Set G := {x | ∃ a ∈ J, ∃ b ∈ J, x = a * g * b}

theorem dcos_eq_iUnion (J : Subgroup G) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    dcos J g = ⋃ j ∈ R, (fun x => (j * g)⁻¹ * x) ⁻¹' (J : Set G) := by
  ext x
  simp only [dcos, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨j', ⟨hj'R, hj'⟩, -⟩ := h2 a ha
    refine ⟨j', hj'R, ?_⟩
    have e : (j' * g)⁻¹ * (a * g * b) = ((j' * g)⁻¹ * (a * g)) * b := by group
    rw [e]; exact J.mul_mem hj' hb
  · rintro ⟨j, hjR, hj⟩
    exact ⟨j, h1 j hjR, (j * g)⁻¹ * x, hj, by group⟩

theorem pairwiseDisjoint_cosets (J : Subgroup G) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    (R : Set G).PairwiseDisjoint (fun j => (fun x => (j * g)⁻¹ * x) ⁻¹' (J : Set G)) := by
  intro j₁ hj₁ j₂ hj₂ hne
  refine Set.disjoint_left.2 fun x hx₁ hx₂ => hne ?_
  simp only [Set.mem_preimage, SetLike.mem_coe] at hx₁ hx₂
  have hm : (j₁ * g)⁻¹ * (j₂ * g) ∈ J := by
    have e : (j₁ * g)⁻¹ * (j₂ * g) = ((j₁ * g)⁻¹ * x) * ((j₂ * g)⁻¹ * x)⁻¹ := by group
    rw [e]; exact J.mul_mem hx₁ (J.inv_mem hx₂)
  have hself : (j₂ * g)⁻¹ * (j₂ * g) ∈ J := by simp
  exact (h2 j₂ (h1 j₂ (Finset.mem_coe.1 hj₂))).unique ⟨Finset.mem_coe.1 hj₁, hm⟩ ⟨Finset.mem_coe.1 hj₂, hself⟩

theorem dcos_inv (J : Subgroup G) (g : G) : dcos J g⁻¹ = Inv.inv ⁻¹' dcos J g := by
  ext x
  simp only [dcos, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, by group⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, ?_⟩
    rw [← inv_inv x, h]; group

theorem measure_dcos [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (J : Subgroup G) (hJ : MeasurableSet (J : Set G)) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    μ (dcos J g) = R.card * μ J := by
  rw [dcos_eq_iUnion J g R h1 h2, measure_biUnion_finset (pairwiseDisjoint_cosets J g R h1 h2)
    (fun j _ => measurable_const_mul _ hJ)]
  simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]

theorem card_eq_of_unimodular [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (J : Subgroup G) (hJo : IsOpen (J : Set G)) (hJt : μ J ≠ ⊤) (g : G) (R R' : Finset G)
    (h1 : ∀ j ∈ R, j ∈ J) (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J)
    (h1' : ∀ j ∈ R', j ∈ J) (h2' : ∀ j ∈ J, ∃! j', j' ∈ R' ∧ (j' * g⁻¹)⁻¹ * (j * g⁻¹) ∈ J) :
    R.card = R'.card := by
  haveI : μ.IsInvInvariant := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have h0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have e1 := measure_dcos μ J hJo.measurableSet g R h1 h2
  have e2 := measure_dcos μ J hJo.measurableSet g⁻¹ R' h1' h2'
  rw [dcos_inv, Measure.measure_preimage_inv, e1] at e2
  have h := (ENNReal.mul_left_inj h0 hJt).1 e2
  exact_mod_cast h

end general

theorem card_isReps_inv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k)
    (R R' : Finset (GL (A ⊕ D) k)) (d d' : GL (A ⊕ D) k → kˣ) :
    IsReps g R d → IsReps g⁻¹ R' d' → R.card = R'.card ∧ R.Nonempty := by
  intro hR hR'
  letI : MeasurableSpace (GL (A ⊕ D) k) := borel _
  haveI : BorelSpace (GL (A ⊕ D) k) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GL (A ⊕ D) k) := inferInstance
  haveI : LocallyCompactSpace (GL (A ⊕ D) k) := inferInstance
  haveI : SecondCountableTopology (GL (A ⊕ D) k) := inferInstance
  haveI : TopologicalSpace.PseudoMetrizableSpace (GL (A ⊕ D) k) :=
    TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology (GL (A ⊕ D) k)
  haveI : SigmaCompactSpace (GL (A ⊕ D) k) := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨hJo, hJc⟩ := GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric k A D

  have hRI : ∀ (μ : Measure (GL (A ⊕ D) k)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
    intro μ hμ
    haveI : IsFiniteMeasureOnCompacts μ := hμ.toIsFiniteMeasureOnCompacts
    haveI : SigmaFinite μ := SigmaFinite.of_isFiniteMeasureOnCompacts μ
    haveI : μ.InnerRegular :=
      Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaCompactSpaceOfBorelSpaceOfSigmaFinite μ
    refine ⟨fun g => ?_⟩
    have h : Measure.modularCharacter g = 1 := by
      refine GlobalTheory.SplitFlip.hom_eq_one_of_center Measure.modularCharacter (fun z hz => ?_) g
      have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
      rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
        Measure.IsMulLeftInvariant.map_mul_left_eq_self] at h1
      have h2 := congrArg (fun m : Measure (GL (A ⊕ D) k) => m (KO k (A ⊕ D))) h1
      have hne : μ (KO k (A ⊕ D)) ≠ 0 := (GlobalTheory.SplitFlip.isOpen_KO.measure_pos μ ⟨1, one_mem _⟩).ne'
      have hnt : μ (KO k (A ⊕ D)) ≠ ⊤ := GlobalTheory.SplitFlip.isCompact_KO.measure_lt_top.ne
      simp only [Measure.coe_nnreal_smul_apply] at h2
      have h3 : (Measure.modularCharacterFun z : ENNReal) = 1 :=
        (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
      exact_mod_cast h3
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g, show Measure.modularCharacterFun g = 1 from h, one_smul]
  haveI := hRI (Measure.haar : Measure (GL (A ⊕ D) k))
  refine ⟨card_eq_of_unimodular (Measure.haar : Measure (GL (A ⊕ D) k)) (parahoric k A D) hJo
    hJc.measure_lt_top.ne g R R' (fun j hj => (hR.1 j hj).1) hR.2
    (fun j hj => (hR'.1 j hj).1) hR'.2, ?_⟩
  obtain ⟨j', ⟨hj', -⟩, -⟩ := hR.2 1 (one_mem _)
  exact ⟨j', hj'⟩

end GlobalTheory.ParHeckeCard
end
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem norm_eq_one_of_quad_root {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (N : ℕ) (hN : ¬ l ∣ N)
    (hx : x ^ 2 - x + (N : ℂ_[l]) = 0) : ‖x‖ = 1 := by
  have hNn : ‖(N : ℂ_[l])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN
  have hle : ∀ y : ℂ_[l], y ^ 2 - y + (N : ℂ_[l]) = 0 → ‖y‖ ≤ 1 := by
    intro y hy
    by_contra h
    push_neg at h
    have h1 : y ^ 2 = y - N := by linear_combination hy
    have h2 : ‖y - (N : ℂ_[l])‖ ≤ max ‖y‖ ‖(N : ℂ_[l])‖ := by
      rw [sub_eq_add_neg, ← norm_neg (N : ℂ_[l])]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [hNn, max_eq_left h.le] at h2
    have h3 : ‖y‖ ^ 2 ≤ ‖y‖ := by rw [← norm_pow, h1]; exact h2
    nlinarith
  have h1 := hle x hx
  have h2 := hle (1 - x) (by linear_combination hx)
  have hprod : x * (1 - x) = N := by linear_combination -hx
  have h4 : ‖x‖ * ‖1 - x‖ = 1 := by rw [← norm_mul, hprod, hNn]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = ‖x‖ * ‖1 - x‖ := h4.symm
    _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg x)
    _ = ‖x‖ := mul_one _

theorem endOmega_holds : EndOmega := by
  intro d L hd hL l _ hl5 hld hsq ι g2 g3 hG n
  obtain ⟨-, -, h2, h3, hΔ, lam, hlam, rfl, rfl⟩ := hG
  have hc0 : ι.symm lam ≠ 0 := by simpa using hlam
  obtain ⟨L', -, hg2, hg3, -, hCM⟩ := GlobalTheory.T.exists_homothetic_periodPair_lattice L (ι.symm lam) hc0
  have hιc : ι (ι.symm lam) = lam := ι.apply_symm_apply lam
  have e2 : ι L'.g₂ = lam ^ 4 * ι L.g₂ := by rw [hg2, map_mul, map_pow, hιc]
  have e3 : ι L'.g₃ = lam ^ 6 * ι L.g₃ := by rw [hg3, map_mul, map_pow, hιc]
  have hL' : HasCMBy d L' := hCM d hL
  have hq := GlobalTheory.T.omegaK_sq_sub_self_add_eq_zero d hd
  set N := (d + 1) / 4 with hNdef
  have hN0 : 0 < N := by omega
  have hlN : ¬ l ∣ N := by
    intro h
    apply hsq
    refine ⟨1, ?_⟩
    have h4 : 4 * N = d + 1 := by omega
    have h5 : ((4 * N : ℕ) : ZMod l) = 0 := by
      rw [Nat.cast_mul, (ZMod.natCast_eq_zero_iff N l).mpr h, mul_zero]
    rw [h4] at h5
    push_cast at h5
    linear_combination h5
  have hιβ : ‖ι (omegaK d)‖ = 1 := by
    apply norm_eq_one_of_quad_root _ N hlN
    have := congrArg ι hq
    simpa using this
  have hNz : ∀ z, omegaK d * z ∈ L'.lattice → (N : ℂ) * z ∈ L'.lattice := by
    intro z hz
    have hz2 : omegaK d * (omegaK d * z) ∈ L'.lattice := hL' _ hz
    have e : (N : ℂ) * z = omegaK d * z - omegaK d * (omegaK d * z) := by linear_combination z * hq
    rw [e]
    exact sub_mem hz hz2
  have key := GlobalTheory.T.formalGroup_mulBy_integral_of_kernel_prime_to_l L' l hl5 ι (by rw [e2]; exact h2) (by rw [e3]; exact h3)
    (by rw [e2, e3]; exact hΔ) (omegaK d) N hL' hιβ hN0 hlN hNz
  rw [e2, e3] at key
  rw [Formalism.L2.Th1.A.uSerEq ℂ_[l]]
  exact key n

end GlobalTheory.Honda
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KJInf

def evalLin {ι : Type} {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) : PY ι a →ₗ[ℂ] ℂ where
  toFun := evalAt y
  map_add' F G := by simp [evalAt]
  map_smul' c F := by simp [evalAt, MvPolynomial.smul_eval]

theorem evalLin_apply {ι : Type} {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalLin y F = evalAt y F := rfl

theorem exists_evalAt_span (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ)
    (W : Type) [AddCommGroup W] [Module ℂ W] (T : PY ι a →ₗ[ℂ] W) :
    ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → W),
      (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, T F = ∑ j, evalAt (y j) F • P j := by
  classical
  set V := Vn lam n with hV
  haveI : FiniteDimensional ℂ V := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam n).1
  have hsep : ∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0 :=
    (GlobalTheory.T.fockSubstitution_identities ι a a le_rfl).2.2.2.2.2.2.1
  let S : Set (Module.Dual ℂ V) :=
    {φ | ∃ y : ι → Matrix (Fin a) (Fin a) ℂ, IsInv y ∧ φ = (evalLin y).comp V.subtype}
  obtain ⟨f, hfS, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ S
  choose y hy hfy using hfS
  let Φ := LinearMap.pi f
  have hinj : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro F hF
    have h0 : ∀ φ ∈ Submodule.span ℂ S, φ F = 0 := by
      intro φ hφ
      rw [← hspan] at hφ
      induction hφ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact congrFun hF j
      | zero => simp
      | add x z _ _ hx hz => simp [hx, hz]
      | smul c x _ hx => simp [hx]
    have hF0 : (F : PY ι a) = 0 := by
      apply hsep
      intro z hz
      have := h0 ((evalLin z).comp V.subtype) (Submodule.subset_span ⟨z, hz, rfl⟩)
      simpa [evalLin_apply] using this
    exact Subtype.ext hF0
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective Φ hinj
  refine ⟨_, y, fun j => T (L (Pi.single j 1) : PY ι a), hy, ?_⟩
  intro F hF
  have hΦ : Φ ⟨F, hF⟩ = ∑ j, evalAt (y j) F • (Pi.single j 1 : Fin _ → ℂ) := by
    ext i
    simp only [Φ, LinearMap.pi_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hfy i]
    rfl
  have key : (⟨F, hF⟩ : V) = L (Φ ⟨F, hF⟩) := by
    rw [← LinearMap.comp_apply, hL]; rfl
  calc T F = T ((⟨F, hF⟩ : V) : PY ι a) := rfl
    _ = T ((L (Φ ⟨F, hF⟩) : V) : PY ι a) := by rw [← key]
    _ = ∑ j, evalAt (y j) F • T (L (Pi.single j 1) : PY ι a) := by

      rw [hΦ, map_sum]
      simp [map_smul, Submodule.coe_sum, Submodule.coe_smul]

end GlobalTheory.KJInf
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.twistParahoricChain_lastSteps_agree_columns : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → LastAgree Ch sel mu cst σ₀ P ι s W ν L := by
  first | exact @GlobalTheory.TwLast.lastAgree | exact GlobalTheory.TwLast.lastAgree | (intros; apply GlobalTheory.TwLast.lastAgree <;> assumption)
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.integralVectorBases_bounded_finite_unitaryClasses : ∀ (I : AutInst) (N : ℕ) (R : ℝ), ∃ S : Set (Fin N → Fin I.n → I.E), S.Finite ∧ (∀ e₀ ∈ S, IsZBasis I e₀) ∧ ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e → BddType I R e → ∃ e₀ ∈ S, ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ ∀ j, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ e j = e₀ j := by
  first | exact @GlobalTheory.BasesFin.bases_finite_classes | exact GlobalTheory.BasesFin.bases_finite_classes | (intros; apply GlobalTheory.BasesFin.bases_finite_classes <;> assumption)
end

section

namespace GlobalTheory.SymBridge

theorem matchAtType : MatchAtType := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν hν h
  exact ⟨GlobalTheory.T.identityCoset_entry_proportional_columnDatum X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h,
    GlobalTheory.T.psiDatum_agree_columnDatum_at_typePrime X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h,
    GlobalTheory.T.stepDatum_completion_eq_columnTestFunction X Pr R Ch sel S₀ mu cst σ₀ P k ι s S ν hν h⟩

end GlobalTheory.SymBridge
end
