module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle462
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle153
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle083
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle483
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle363
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle484
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle485
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeLevelPrimePow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL.UnitaryOrder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hasCentralChar_nu (x : IrrGL (k := k)) {ω : kˣ →* ℂˣ} (h : HasCentralChar x.rep ω) (s : ℂ) :
    HasCentralChar (x.nu s).rep (ω * absPow k s ^ x.1) := by
  have h1 := hasCentralChar_twist h (absPow k s)
  rw [Fintype.card_fin] at h1
  exact hasCentralChar_of_equiv (x.twEquiv _ _) h1

theorem norm_eq_one_of_isUnitarisable {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    {ρ : Representation ℂ G X} (hU : IsUnitarisable ρ) {g : G} {c : ℂ} (hc : ∀ v, ρ g v = c • v) : ‖c‖ = 1 := by
  obtain ⟨B, -, hp, hi⟩ := hU
  obtain ⟨v, hv⟩ := exists_ne (0 : X)
  have h := hi g v v
  have h0 : B v v ≠ 0 := fun e => by simpa [e] using hp v hv
  rw [hc, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Complex.mul_conj, mul_eq_right₀ h0] at h
  have h2 : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

theorem log_norm_mul_absPow (ω : kˣ →* ℂˣ) (t : ℝ) (d : ℕ) (z : kˣ) :
    Real.log ‖(((ω * absPow k (t : ℂ) ^ d) z : ℂˣ) : ℂ)‖ =
      Real.log ‖(ω z : ℂ)‖ + d * t * Real.log (nabs k z) := by
  have hz := nabs_pos' k z
  have hω : ‖(ω z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 (ω z).ne_zero
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, val_absPow_ofReal,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hz.le _),
    Real.log_mul hω (pow_ne_zero _ (Real.rpow_pos_of_pos hz _).ne'), Real.log_pow, Real.log_rpow hz]
  ring

theorem sum_range_mul_two (l : ℕ) : (∑ i ∈ Finset.range l, (i : ℝ)) * 2 = l * ((l : ℝ) - 1) := by
  induction l with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

theorem log_norm_centralChar {δ : IrrGL (k := k)} {Δ : Segment k} (hL : IsLSeg Δ δ.rep) (hU : IsUnitarisable δ.rep)
    {ω : kˣ →* ℂˣ} (hω : HasCentralChar Δ.first.rep ω) (z : kˣ) :
    Real.log ‖(ω z : ℂ)‖ = -((Δ.d : ℝ) * ((Δ.len : ℝ) - 1) / 2) * Real.log (nabs k z) := by
  obtain ⟨hd, hi, f, hf, -⟩ := hL
  have hterm : ∀ a : Fin Δ.len,
      HasCentralChar (Δ.term a).rep (ω * absPow k (((a : ℕ) : ℝ) : ℂ) ^ Δ.d) := fun a => by
    have h := hasCentralChar_nu Δ.first hω ((a : ℕ) : ℂ)
    rw [Complex.ofReal_natCast]
    exact h
  have hsc : ∀ v, δ.rep (GeneralLinearGroup.scalar (Fin δ.1) z) v =
      (∏ a : Fin Δ.len, (((ω * absPow k (((a : ℕ) : ℝ) : ℂ) ^ Δ.d) z : ℂˣ) : ℂ)) • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf v
    have h1 := GlobalTheory.BoundaryMaps.multiProd_scalar (stdBlocks (fun a => (Δ.term a).1) hd)
      (fun a => (Δ.term a).rep) _ hterm z w
    rw [← f.isIntertwining]
    exact (congrArg f h1).trans (map_smul f _ _)
  haveI := Model.nontrivial_of_isIrreducible hi
  have hc := congrArg Real.log (norm_eq_one_of_isUnitarisable hU hsc)
  rw [norm_prod, Real.log_one, Real.log_prod fun a _ => norm_ne_zero_iff.2 (Units.ne_zero _)] at hc
  simp only [log_norm_mul_absPow] at hc
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (i : ℝ)) Δ.len] at hc
  have hS := sum_range_mul_two Δ.len
  have hl : (Δ.len : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Δ.len_pos.ne'
  apply mul_left_cancel₀ hl
  linear_combination hc - ((Δ.d : ℝ) * Real.log (nabs k z) / 2) * hS

theorem add_one_le_of_precedes (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k) (hL : IsLSeg Δ δ.rep) (hU : IsUnitarisable δ.rep) (hL' : IsLSeg Δ' δ'.rep)
    (hU' : IsUnitarisable δ'.rep) (x y : ℝ) (hP : (Δ.nu x).Precedes (Δ'.nu y)) : x + 1 ≤ y := by
  obtain ⟨⟨-, -, hnsub⟩, j, hj, hfirst⟩ := hP
  have hf : Δ'.first.nu (y : ℂ) = (Δ.first.nu (x : ℂ)).nu (j : ℂ) := hfirst
  have hρ' : Δ'.first = Δ.first.nu (((x + j - y : ℝ)) : ℂ) := by
    have h1 := congrArg (fun r => r.nu (-(y : ℂ))) hf
    simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h1
    rw [h1]
    congr 1
    push_cast
    ring
  have hd : Δ'.d = Δ.d := congrArg Sigma.fst hρ'
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar Δ.first.2.rep.smooth Δ.first.2.rep.irr
  have hω' : HasCentralChar Δ'.first.rep (ω * absPow k (((x + j - y : ℝ)) : ℂ) ^ Δ.first.1) := by
    rw [hρ']
    exact hasCentralChar_nu _ hω _
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hne : nabs k ϖ ≠ 1 := fun e => uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have hL0 : Real.log (nabs k ϖ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) hne
  have hA := log_norm_centralChar hL hU hω ϖ
  have hA' := log_norm_centralChar hL' hU' hω' ϖ
  rw [log_norm_mul_absPow, hd] at hA'
  have hdL : (Δ.d : ℝ) * Real.log (nabs k ϖ) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 Δ.d_pos.ne') hL0
  have ht : x + j - y = ((Δ.len : ℝ) - Δ'.len) / 2 := by
    apply mul_left_cancel₀ hdL
    have e1 : (Δ.first.1 : ℝ) = Δ.d := rfl
    rw [e1] at hA'
    linear_combination hA' - hA
  have hlen : Δ.len < j + Δ'.len := by
    by_contra hcon
    push_neg at hcon
    apply hnsub
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hw
    refine Segment.mem_carrier.2 ⟨j + a, ?_, ?_⟩
    · have ha' : a < Δ'.len := ha
      show j + a < Δ.len
      omega
    · rw [hfirst, IrrGL.nu_nu]
      push_cast
      rfl
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hl1 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len := by exact_mod_cast hlen
  linarith

end GlobalTheory.LocGL.UnitaryOrder
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isUnramChar_of_isCusp_of_isSpherical : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (x : IrrGL (k := k)), x.IsCusp → IsSpherical x.rep → x.IsUnramChar := by
  intro hG hBZ hZ k _ _ _ _ _ x hx hs
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have h1 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => unrChar k (α i)) hχ x.2.rep hα
  have h2 : HasSupport x.rep {x} := hasSupport_self hx
  have he := GlobalTheory.T.supercuspidalSupport_unique_GL hG hBZ hZ k x _ _ h1 h2
  have hmem : x ∈ (Finset.univ.val.map fun i => IrrGL.ofChar (unrChar k (α i)) (hχ i)) := by
    rw [he]; exact Multiset.mem_singleton_self x
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), hi.symm⟩

end GlobalTheory.LocLanglands
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.BlochKatoDuality.Br

namespace GlobalTheory.TatePair

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]
    {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL)

theorem cup_coboundary_right (hopen : IsOpen (Set.range (algebraMap O LL))) (c : ↥(divisibleCocycles LA'))
    (d : ↥(latticeCocycles LA)) (hc : (c : G → A'.V ⧸ LA'.T) ∈ BD LA') :
    cupModuloIntegers PD hd L1 hL1 c d ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := by
  obtain ⟨w, hw⟩ := hc
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hcg : ∀ h, (c : G → A'.V ⧸ LA'.T) h =
      repD LA' h (Submodule.Quotient.mk v) - Submodule.Quotient.mk v := fun h =>
    (congrFun hw h).symm
  have hT : IsOpen (L1.T : Set LL) := integers_isOpen PD L1 hL1 hopen
  have hcont : Continuous fun g : G => P ((d : G → A.V) g) (A'.ρ g v) :=
    (IsModuleTopology.continuous_bilinear_of_finite_left P).comp
      (d.2.1.1.prodMk (A'.cont v))
  have hlc : IsLocallyConstant fun g : G =>
      -(Submodule.Quotient.mk (P ((d : G → A.V) g) (A'.ρ g v)) : LL ⧸ L1.T) :=
    (locConst_mk L1.T hT _ hcont).neg
  refine ⟨fun g => -torsionPairing PD hd L1 hL1 (repD LA' g (Submodule.Quotient.mk v)) (evT LA g d),
    ⟨hlc, fun _ => Submodule.mem_top⟩, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  show repD L1 g (-torsionPairing PD hd L1 hL1 (repD LA' h (Submodule.Quotient.mk v)) (evT LA h d))
      - -torsionPairing PD hd L1 hL1 (repD LA' (g * h) (Submodule.Quotient.mk v)) (evT LA (g * h) d)
      + -torsionPairing PD hd L1 hL1 (repD LA' g (Submodule.Quotient.mk v)) (evT LA g d) =
    cupModuloIntegers PD hd L1 hL1 c d (g, h)
  rw [cup_apply_alt]
  simp only [hcg, map_neg, ← torsionPairing_equivariant, lattice_cocycle_mul, map_mul, Module.End.mul_apply, map_add (f := _),
    map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

end Gen

theorem integral_pairing : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type)
    [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
      (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m →
    ∃ β : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ L1.T),
      (∀ d c, β d c = 0 ↔ CobO (P.PD K) L1 (cupLD LA' m d.1 c.1)) ∧
      (∀ d c, d.1 ∈ latticeCoboundaries LA → β d c = 0) ∧ ∀ d c, c.1 ∈ BD LA' → β d c = 0 := by
  intro hT l _ P K LL _ _ _ O _ _ hG L1 hL1 A A' LA LA' m hd
  obtain ⟨e⟩ := GlobalTheory.T.tate_H2_period_datum hT l P K LL O hG L1 hL1
  obtain ⟨⟨hO, hDVR, hFr⟩, -, -, htr, hopen⟩ := hG
  haveI := hO
  haveI := hDVR
  haveI := hFr
  haveI := htr
  obtain ⟨pr, hpr⟩ := exists_pr (P.PD K) hopen hd L1 hL1
  refine ⟨(pr.compr₂ e.toLinearMap).flip ∘ₗ Submodule.mkQ _, ?_, ?_, ?_⟩
  · intro d c
    show e (pr c (Submodule.Quotient.mk d)) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact hpr c d
  · intro d c hdB
    show e (pr c (Submodule.Quotient.mk d)) = 0
    rw [LinearEquiv.map_eq_zero_iff, hpr c d]
    unfold CobO
    rw [← cup_eq_pairing (P.PD K) hd L1 hL1 c d]
    exact cup_mem_coboundaries (P.PD K) hd L1 hL1 c d hdB
  · intro d c hc
    show e (pr c (Submodule.Quotient.mk d)) = 0
    rw [LinearEquiv.map_eq_zero_iff, hpr c d]
    unfold CobO
    rw [← cup_eq_pairing (P.PD K) hd L1 hL1 c d]
    exact cup_coboundary_right (P.PD K) hd L1 hL1 hopen c d hc

end GlobalTheory.TatePair
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.LocTensorK

private theorem ιB_algebraMap_Kur {l : ℕ} [Fact l.Prime] (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  have hint : IsIntegral ℚ_[l] (c : Om l) := Algebra.IsIntegral.isIntegral _
  obtain ⟨K, hc⟩ : ∃ K : FinExt l, (c : Om l) ∈ K0 K :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {(c : Om l)},
      IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] (c : Om l), c.2⟩
  have h := (P.PD K).ι.commutes (⟨c, hc⟩ : ↥(K0 K))
  rw [P.PD_ι] at h
  exact h

private theorem indep_of_frac {k Ω B D : Type} [Field k] [Field Ω] [CommRing B] [CommRing D] [Algebra k Ω]
    [IsGalois k Ω] (hD : IsField D) (o : Ω →+* D) (ι : B →+* D) (hι : Function.Injective ι)
    (hk : ∀ c : k, ∃ a : B, ι a = o (algebraMap k Ω c))
    (hfrac : ∀ (a b : B) (x : Ω), b ≠ 0 → ι a = o x * ι b → x ∈ (algebraMap k Ω).range)
    (m : ℕ) (x : Fin m → Ω) (hx : LinearIndependent k x) (b : Fin m → B)
    (hb : ∑ i, o (x i) * ι (b i) = 0) : ∀ i, b i = 0 := by
  letI : Field D := hD.toField
  have hcl : ∀ y : D, y ∈ Subring.closure (Set.range ι) ↔ ∃ a, ι a = y := by
    intro y
    have : Subring.closure (Set.range ι) = ι.range := by
      rw [← RingHom.coe_range, Subring.closure_eq]
    rw [this]; rfl
  have key := GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent k Ω D o (Subfield.closure (Set.range ι)) (by
    intro y
    constructor
    · intro hy
      obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.1 hy
      obtain ⟨a, rfl⟩ := (hcl u).1 hu
      obtain ⟨c, rfl⟩ := (hcl v).1 hv
      by_cases hc : c = 0
      · subst hc
        rw [map_zero, div_zero] at huv
        have : y = 0 := o.injective (by rw [map_zero]; exact huv.symm)
        rw [this]; exact zero_mem _
      · have hc' : ι c ≠ 0 := fun h => hc (hι (by rw [h, map_zero]))
        refine hfrac a c y hc ?_
        rw [← huv, div_mul_cancel₀ _ hc']
    · rintro ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := hk c
      exact Subfield.subset_closure ⟨a, ha⟩) m x hx (fun i => ι (b i))
    (fun i => Subfield.subset_closure ⟨b i, rfl⟩) hb
  intro i
  exact hι (by rw [map_zero]; exact key i)

private theorem tied_tensor_inj : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (m : ℕ) (x : Fin m → Om l), LinearIndependent ↥(MaximalUnramifiedExtension l) x → ∀ b : Fin m → P.R.B, ∑ i, algebraMap (Om l) P.R.BdR (x i) * P.ιB (b i) = 0 → ∀ i, b i = 0 := by
  intro l _ P AI T m x hx b hb
  obtain ⟨hD, -, hι, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  haveI : IsGalois ℚ_[l] (Om l) := inferInstance
  haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := inferInstance
  refine indep_of_frac (k := ↥(MaximalUnramifiedExtension l)) hD (algebraMap (Om l) P.R.BdR) (P.ιB : P.R.B →+* P.R.BdR) hι
    (fun c => ⟨algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c, ιB_algebraMap_Kur P c⟩) ?_ m x hx b hb
  intro a c y hc h
  exact ⟨⟨y, GlobalTheory.T.mem_maxUnramified_of_crystallineRatio l P AI T a c y hc h⟩, rfl⟩

end GlobalTheory.LocTensorK


theorem _root_.GlobalTheory.T.injective_tensor_Bcris_to_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (m : ℕ) (x : Fin m → ↥K.1), LinearIndependent ↥(K0 K) x → ∀ b : Fin m → P.R.B, ∑ i, algebraMap ↥K.1 P.R.BdR (x i) * P.ιB (b i) = 0 → ∀ i, b i = 0 := by
  intro l _ P AI hT K m x hx b hb
  refine GlobalTheory.LocTensorK.tied_tensor_inj l P AI hT m (fun i => (x i : Om l))
    (GlobalTheory.UnramDisjoint.linearIndependent_Kur l K m x hx) b ?_
  exact hb
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.fontaine_inequality_dcris_finite_concrete_rings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K LL : FinExt l, FontaineLe (P.PD K) ↥LL.1 ∧ ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) := by
  intro l _ P AI T K LL
  have key : ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
        Module.finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 V := by
    intro V _ _ _ _ _ ρ
    have := GlobalTheory.Per.FontaineBound.isDomain_cris (PD := P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T)
    have := (P.PD K).finK₀
    have := LL.2
    refine GlobalTheory.Per.FontaineBound.finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K b' b hb fun g hg => ?_) ρ
    have h1 := h ⟨g, hg⟩
    rw [P.PD_actB, P.PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  exact ⟨fun V _ _ _ _ _ ρ => (key V ρ).2, fun V _ _ _ _ _ ρ => (key V ρ).1⟩
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_psi_operator_etale_phiGamma_module : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ ψ : W.DD T →ₗ[↥(OL LL)] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧ (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x) := by
  first | exact @GlobalTheory.psiD_exists | exact GlobalTheory.psiD_exists | (intros; apply GlobalTheory.psiD_exists <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isDC_of_smaller_level_same_local {G : Type} [Group G] (J J' Lc : Subgroup G) (x : G) (A : Finset G)
    (hJJ : J' ≤ J) (hLc : J ⊓ Lc ≤ J')
    (hdec : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ y ∈ Lc, Commute k₂ y)
    (hx : x ∈ Lc) (hA : ∀ a ∈ A, a ∈ Lc) (hDC : Bridge.IsDC J x A) : Bridge.IsDC J' x A := by
  obtain ⟨h1, h2⟩ := hDC
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, rfl⟩ := h1 a ha
    obtain ⟨k₁, hk₁J, k₂, hk₂J, hk₁L, rfl, hk₂c⟩ := hdec k hk
    obtain ⟨k₁', hk₁'J, k₂', hk₂'J, hk₁'L, rfl, -⟩ := hdec k' hk'
    have e : k₁ * k₂ * x * (k₁' * k₂') = k₁ * x * k₁' * (k₂ * k₂') := by
      have c1 : k₂ * x = x * k₂ := (hk₂c x hx).eq
      have c2 : k₂ * k₁' = k₁' * k₂ := (hk₂c k₁' hk₁'L).eq
      calc k₁ * k₂ * x * (k₁' * k₂') = k₁ * (k₂ * x) * k₁' * k₂' := by group
        _ = k₁ * x * (k₂ * k₁') * k₂' := by rw [c1]; group
        _ = k₁ * x * (k₁' * k₂) * k₂' := by rw [c2]
        _ = k₁ * x * k₁' * (k₂ * k₂') := by group
    have haL := hA _ ha
    have hprodL : k₂ * k₂' ∈ Lc := by
      have : k₂ * k₂' = (k₁ * x * k₁')⁻¹ * (k₁ * k₂ * x * (k₁' * k₂')) := by rw [e]; group
      rw [this]
      exact Lc.mul_mem (Lc.inv_mem (Lc.mul_mem (Lc.mul_mem hk₁L hx) hk₁'L)) haL
    have hprod : k₂ * k₂' ∈ J' := hLc ⟨J.mul_mem hk₂J hk₂'J, hprodL⟩
    have hk₁ : k₁ ∈ J' := hLc ⟨hk₁J, hk₁L⟩
    have hk₁' : k₁' ∈ J' := hLc ⟨hk₁'J, hk₁'L⟩
    refine ⟨⟨k₁, hk₁⟩, ⟨k₁' * (k₂ * k₂'), J'.mul_mem hk₁' hprod⟩, ?_⟩
    simp only
    rw [e]; group
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, rfl⟩ := hg
    obtain ⟨k₁, hk₁J, k₂, hk₂J, hk₁L, rfl, hk₂c⟩ := hdec k (hJJ hk)
    have hk₁ : k₁ ∈ J' := hLc ⟨hk₁J, hk₁L⟩
    have hk₂ : k₂ ∈ J' := by
      have : k₂ = k₁⁻¹ * (k₁ * k₂) := by group
      rw [this]; exact J'.mul_mem (J'.inv_mem hk₁) hk
    obtain ⟨a, ⟨haA, haJ⟩, -⟩ := h2 (k₁ * x) ⟨⟨k₁, hk₁J⟩, 1, by simp⟩
    have haL : a⁻¹ * (k₁ * x) ∈ Lc := Lc.mul_mem (Lc.inv_mem (hA a haA)) (Lc.mul_mem hk₁L hx)
    have haJ' : a⁻¹ * (k₁ * x) ∈ J' := hLc ⟨haJ, haL⟩
    have c1 : k₂ * x = x * k₂ := (hk₂c x hx).eq
    refine ⟨a, ⟨haA, ?_⟩, ?_⟩
    · have : a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * (k₁ * x) * (k₂ * k') := by
        calc a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * k₁ * (k₂ * x) * k' := by group
          _ = a⁻¹ * (k₁ * x) * (k₂ * k') := by rw [c1]; group
      rw [this]
      exact J'.mul_mem haJ' (J'.mul_mem hk₂ hk')
    · rintro b ⟨hbA, hbJ'⟩
      have hgJ : ∃ m₁ m₂ : J, k₁ * k₂ * x * k' = (m₁ : G) * x * m₂ :=
        ⟨⟨k₁ * k₂, hJJ hk⟩, ⟨k', hJJ hk'⟩, rfl⟩
      obtain ⟨c, -, hc⟩ := h2 _ hgJ
      have haJg : a⁻¹ * (k₁ * k₂ * x * k') ∈ J := by
        have : a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * (k₁ * x) * (k₂ * k') := by
          calc a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * k₁ * (k₂ * x) * k' := by group
            _ = a⁻¹ * (k₁ * x) * (k₂ * k') := by rw [c1]; group
        rw [this]; exact J.mul_mem haJ (J.mul_mem hk₂J (hJJ hk'))
      rw [hc b ⟨hbA, hJJ hbJ'⟩, hc a ⟨haA, haJg⟩]

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.tate_pairing_lattice_level_primePow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), ∃ β : QuotientCohomology LA' _ hI' →ₗ[O] QuotientCohomology LA _ hI →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), (∀ c, (∀ y, β y c = 0) → c = 0) ∧ ∀ (d : ↥(latticeCocycles LA)) (h : redT LA _ d ∈ quotientCocycles LA _ hI) (c' : ↥(quotientCocycles LA' _ hI')), β (Submodule.Quotient.mk c') (Submodule.Quotient.mk ⟨redT LA _ d, h⟩) = 0 → CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T))) := by
  first | exact @GlobalTheory.TateLevel.tate_pairing_level | exact GlobalTheory.TateLevel.tate_pairing_level | (intros; apply GlobalTheory.TateLevel.tate_pairing_level <;> assumption)
end
