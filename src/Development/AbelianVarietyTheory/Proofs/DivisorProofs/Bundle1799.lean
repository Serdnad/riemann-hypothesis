module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Formalism.LocalToGlobal.HermitianColumns.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem isPlacesIdem_mul_self {F : Type} [Field F] [NumberField F] {S₁ : Finset (InfinitePlace F)}
    {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  apply GlobalTheory.StrongApproximationSL2.idem_of_isPlacesIdem <;> assumption

theorem strongApprox_nrm_one : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∃ p q : AF F, ε * (algebraMap F (AF F) b - (p ^ 2 - algebraMap F (AF F) a * q ^ 2)) = 0) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb S₁ S₂ ε hε hS hpq g hg
  by_cases hiso : ∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0
  · exact GlobalTheory.T.strongApproximation_normOne_splitQuaternionAlgebra F a b ha hb hiso S₁ S₂ ε hε hS g hg
  · have hdiv : ∀ x : ℍ[F, a, b], nrm x = 0 → x = 0 := fun x hx =>
      by_contra fun h => hiso ⟨x, h, hx⟩
    obtain ⟨p, q, hpq⟩ := hpq
    refine GlobalTheory.T.mem_closure_normOne_of_strongApproximation F a b ha hb hdiv S₁ S₂ ε hε hS (fun t => ?_) g hg
    have h2 : IsUnit (2 : AF F) := by
      have : IsUnit (algebraMap F (AF F) 2) := (IsUnit.mk0 (2 : F) two_ne_zero).map _
      rwa [map_ofNat] at this
    exact GlobalTheory.T.quaternion_norm_one_prescribed_re_at_idempotent (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b) ε p q
      (isPlacesIdem_mul_self hε) ((IsUnit.mk0 a ha).map _) ((IsUnit.mk0 b hb).map _) h2 hpq t

end GlobalTheory.QSA
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory

theorem kfin_span_raising_words_lowK : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} = ⊤ := by
  intro n ε H _ _ σ D E lam hHC hCh hDS hK
  obtain ⟨_, hKS, hne, hkill⟩ := GlobalTheory.T.lowestKTypeSpace_holomorphicKModule_killed n ε H σ D E lam hHC hCh hDS hK
  haveI : CompleteSpace H := hDS.1
  set L := (lowKSub ε lam σ).comap D.subtype with hL
  set S := Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
    ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hS
  have hstab : ∀ a b, ∀ x ∈ S, E a b x ∈ S := fun a b x hx =>
    GlobalTheory.T.raisingWordSpan_stable_of_lowering_kill n ε D E hK.gl L hKS hkill a b x hx
  have hLS : L ≤ S := by
    intro x hx
    apply Submodule.subset_span
    exact ⟨[], by simp, x, hx, by simp⟩
  rcases GlobalTheory.T.kFiniteModule_irreducible_of_irreducible_unitaryRep n ε H σ D E hDS.1 hDS.2.2.1 hDS.2.2.2.1 hK S hstab with h | h
  · exfalso
    apply hne
    exact le_bot_iff.mp (h ▸ hLS)
  · exact h

end GlobalTheory
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder Matrix

noncomputable section

namespace GlobalTheory.LastPeriod

open GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum GlobalTheory.ColNorms GlobalTheory.PeriodClassSum

theorem gramSum_one {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) :
    gramSum hN (1 : Matrix (Fin n) (Fin n) K) 1 = 1 := by
  ext a b
  have ha := a.2
  have hb := b.2
  simp only [gramSum, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff, Br.iL]
  split_ifs <;> first | rfl | omega

theorem coefOpLe_brAt (hL : LastMapNorm) {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι]
    {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (T : ℝ) (hT : 0 < T) (t : ι → K)
    (ht : ∀ τ, star (σ (t τ)) * σ (t τ) = (T : ℂ)) :
    CoefOpLe σ lam sg (Br.brAt hN lam sg t) (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * orthNormSq hN lam sg) := by
  intro x
  have h := (hL ℂ (RingHom.id ℂ) (fun _ => rfl) ι N n hN lam sg hI hS (fun _ => 1)
    (fun _ => by simpa using Matrix.PosDef.one) T hT (fun _ => 1) (fun τ => σ (t τ))
    (fun τ => by simpa using ht τ)).2.2.1
    ⟨MvPolynomial.map σ (x : Pol K ι N), GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩
  simp only [gramSum_one] at h
  rw [GlobalTheory.JetBase.sqAt_eq σ lam x ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩ rfl]
  refine le_of_eq_of_le (GlobalTheory.JetBase.sqAt_eq σ sg _ _ ?_) h
  simp only [Br.brAt, Br.brStd, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.coe_smul, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_prod σ]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (map_zpow₀ σ _ _).symm

theorem sqAt_eq_dot {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (x : Formalism.L2.DIV.VV K lam) :
    sqAt σ lam x = (star (fun i => σ ((bVV K lam).repr x i)) ⬝ᵥ (GlobalTheory.TestLat.Compare.gramB K lam).map σ *ᵥ
      fun i => σ ((bVV K lam).repr x i)).re := by
  simp only [sqAt, pairK_one_basis, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply,
    starRingEnd_apply, mul_assoc]

theorem sum_pair_le {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ}
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (B : Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K sg) (t : ℝ)
    (hB : CoefOpLe σ lam sg B t) {C : Type} [Fintype C] (w : C → ℕ) (x : C → Formalism.L2.DIV.VV K lam)
    (y : C → Formalism.L2.DIV.VV K sg) :
    ‖σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c))‖ ^ 2 ≤
      t * (∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ lam (x c)) * ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (y c) := by
  have hG := (gramB_posDef sg σ).posSemidef
  have hre : ∀ z : C → Formalism.L2.DIV.VV K sg, (wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ)
      (fun c i => σ ((bVV K sg).repr (z c) i)) (fun c i => σ ((bVV K sg).repr (z c) i))).re =
      ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (z c) := fun z => by
    rw [wForm, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sqAt_eq_dot, ← Complex.re_ofReal_mul]
    push_cast
    rfl
  have e3 : σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c)) = wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ)
      (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i)) := by

    rw [map_sum, wForm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_inv₀, map_natCast, star_star, map_pairBK]
  have h := wForm_le w hG (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i))
  rw [wForm_star w (by rw [← Matrix.transpose_map, GlobalTheory.TestLat.Compare.gramB_transpose]), ← e3] at h
  have h0 := (Complex.nonneg_iff.1 (wForm_nonneg w hG (fun c i => σ ((bVV K sg).repr (y c) i)))).1
  rw [hre] at h0
  rw [hre fun c => B (x c), hre] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ h0)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

theorem sqAt_nonneg {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) : 0 ≤ sqAt σ lam x := by
  rw [sqAt_eq_dot]
  exact (Complex.nonneg_iff.1 ((gramB_posDef lam σ).posSemidef.dotProduct_mulVec_nonneg _)).1

theorem re_inv_mul (w : ℕ) (z : ℂ) : ((w : ℂ)⁻¹ * z).re = (w : ℝ)⁻¹ * z.re := by
  rw [← Complex.re_ofReal_mul]
  push_cast
  rfl

end GlobalTheory.LastPeriod

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem isBaseFrame_of_isLatBasis {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (h : IsLatBasis V rfl β) :
    IsBaseFrame V β (GlobalTheory.Member.latC V) 1 := by
  refine ⟨fun x => ?_, Formalism.L2.Herm.coordinate_lattice_self_dual D.sp.cm V, Nat.one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := GlobalTheory.LiftLevel.swap_surj x
    refine Iff.trans ?_ (h z)
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1]
    exact (GlobalTheory.LevSplit.latHat_iff _ z).symm
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq] at hx
    simpa using hx
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    simpa using hx

theorem not_isConjPl_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H)
    {w w' : Formalism.L2.DIV.Pl D.host.E} (hw : l.Mb ≤ w.asIdeal) (hw' : l.Mb ≤ w'.asIdeal) : ¬ IsConjPl w w' := by
  intro h
  apply w'.isPrime.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le hw' (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
  obtain ⟨c', hc', e⟩ := h a (hw ha)
  have : H.bar a = c' := by
    apply RingOfIntegers.coe_injective
    exact (H.bar_eq a).trans e.symm
  show H.bar a ∈ w'.asIdeal
  rw [this]; exact hc'

theorem finR_rfl {D : D7} (V : HSp D) (κ : GA D V) : finR V rfl κ = finE V κ := by
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.GeoLevel
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.exists_integers_approximating_root_of_unity_twists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ (τ : E →+* ℂ) (h : ℕ), 0 < h → ∀ (lab : ZMod h → (E →+* ℂ)), (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) → ∀ z : X.C, z ^ (p ^ h - 1) = 1 → (∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1) → ∀ r : ℝ, ∃ a : 𝓞 E, (∀ s, (r : WithTop ℝ) ≤ vX_vp X (embX io X (lab s) a - z ^ p ^ s.val)) ∧ ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a) := by
  first | exact @GlobalTheory.PrimePart.exists_approx_root_twists | exact GlobalTheory.PrimePart.exists_approx_root_twists | (intros; apply GlobalTheory.PrimePart.exists_approx_root_twists <;> assumption)
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.label_directions_integral_basis_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), UnramIn E p → ∀ [DecidableEq (Lt1 Dw)], ∃ L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C, (∀ a b, IsIntV (vX_vp X) (L a b)) ∧ L * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 ∧ (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1 := by
  first | exact @GlobalTheory.PrimePart.exists_integral_inverse_lieVec | exact GlobalTheory.PrimePart.exists_integral_inverse_lieVec | (intros; apply GlobalTheory.PrimePart.exists_integral_inverse_lieVec <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Source

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem span_jVx (hV : R.models_HV) (hj : R.models_jV) : Submodule.span ℂ (Set.range (jVx R i A.μ0)) = ⊤ := by
  have h0 : (R.HV i A.μ0).e '' Set.range (jVx R i A.μ0) = Set.range (R.B.jL i A.μ0) :=
    (Set.range_comp _ _).symm.trans (congrArg Set.range (funext (hj i A.μ0)))
  have h1 : (Submodule.span ℂ (Set.range (jVx R i A.μ0))).map (R.HV i A.μ0).e = (⊤ : Submodule ℂ _).map (R.HV i A.μ0).e :=
    ((Submodule.map_span _ _).trans (congrArg (Submodule.span ℂ) h0)).trans
      ((GlobalTheory.PresBasic.ext_span (R.B.L i A.μ0).pres).trans ((hV i A.μ0).2.1.symm.trans (LinearMap.range_eq_map _)))
  exact Submodule.map_injective_of_injective (hV i A.μ0).1 h1

end Source

section Target

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem eval_inj (hW : R.models_HW) {v₀ : (R.MW i (sg0 D A)).Vec} (hv : IsChosenExtremalVector R i (sg0 D A) v₀) {x y : (R.HW i (sg0 D A)).H}
    (h : (R.HW i (sg0 D A)).e x v₀ = (R.HW i (sg0 D A)).e y v₀) : x = y := by
  have h0 : (R.HW i (sg0 D A)).e (x - y) v₀ = 0 := by
    rw [LinearMap.map_sub]
    exact sub_eq_zero.2 h
  have h1 := (hW i (sg0 D A)).2.2 (x - y) (x - y)
  rw [ipAt, GlobalTheory.EvalAtUnitVector.ipM_self_eq_zero _ _ _ _ v₀ (IsChosenExtremalVector.norm R hv) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

theorem eC_idem (hr : R.grp_record) : GoodBasisCentralIdempotents.IsCentralIdem (RealDat.eC (A := A) (sg0 D A)) := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  have h0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : ∀ g, RealDat.eC (A := A) (sg0 D A) g = D.ntypes.e0.coeff (eR g) := fun g => by rw [h0]; exact h g
  obtain ⟨h2, h3⟩ := GlobalTheory.GoodLatCompare.isCentralIdempotent_of_goodSeriesIdempotent (D := D) (RingHom.id ℂ) (eC := fun g => D.ntypes.e0.coeff g) fun _ => rfl
  refine ⟨fun g k => ?_, fun g => ?_⟩
  · rw [h1, h1, map_mul eR, map_mul eR, map_inv eR]
    exact h2 _ _
  · rw [h1]
    refine Eq.trans (Fintype.sum_equiv eR.toEquiv _ _ fun k => ?_) (h3 (eR g))
    rw [h1, h1, map_mul eR, map_inv eR]
    rfl

theorem postOn_of_good {P : LevelP R.Pg D.R.r ℂ} {U : MMap (R.MW i (sg0 D A))} (hU : U ∈ R.Wat i (sg0 D A) P) :
    postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) U = U :=
  sub_eq_zero.1 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hU).2)

end Target

section Geometric

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

structure DictFacts : Prop where
  dom : ∀ g, (O.dict g).2 ∈ ((C.U ((i : ℕ) + 1) O.s0).X (O.dict g).1).dom
  mu : ∀ g, ‖O.mu g‖ = 1
  cc : ∀ k, ‖cc k‖ = 1
  lifts : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)

variable {O cc} (hd : DictFacts O cc)
include hd

omit hd

variable (O cc)

variable {O cc}

include hd

omit hd

end Geometric

section Main

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

variable {T R F κ v₀ O}

variable (T R F κ v₀ O)

end Main

end GlobalTheory.LiftScalarCompare

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped Classical


theorem _root_.GlobalTheory.T.exists_factor_pureTensor_component_at_place : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∃ r : (κ → AF F) → ℂ, (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z → r (x + z) = r x) ∧
      ∀ ψ₀ : (κ → Fv F v₁) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v₁ ψ₀) := by
  first | exact @GlobalTheory.PureFactor.exists_rest_factor | exact GlobalTheory.PureFactor.exists_rest_factor | (intros; apply GlobalTheory.PureFactor.exists_rest_factor <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v) {m n : Type} (P₀ P₁ : Matrix m n (Fv F v)), ∃ u : Matrix m n (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) u ∧ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = P₀ ∧ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = P₁ := by
  first | exact @GlobalTheory.SplitComps.exists_mat_comps | exact GlobalTheory.SplitComps.exists_mat_comps | (intros; apply GlobalTheory.SplitComps.exists_mat_comps <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = 0 → u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k, ∑ l, (-(JA.map τ * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) * (JB.map τ)ᵀ)) k l * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) k l := by
  first | exact @GlobalTheory.HTensSplitPair.hTens_split_pair | exact GlobalTheory.HTensSplitPair.hTens_split_pair | (intros; apply GlobalTheory.HTensSplitPair.hTens_split_pair <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.SchrKeepsSchA

theorem schr_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (p : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ p Φ ∈ schA F κ := by
  intro F _ _ ψ hψ κ _ p Φ hΦ
  exact GlobalTheory.HeisSchA.schr_mem_schA ψ hψ p Φ hΦ

end GlobalTheory.SchrKeepsSchA
end
