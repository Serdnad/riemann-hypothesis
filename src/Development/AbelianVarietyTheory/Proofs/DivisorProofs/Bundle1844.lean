module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1814
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingTermCoefEqResidueCardZpow
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

theorem _root_.GlobalTheory.T.baseTuple_thetaKernel_tameCharacter : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∀ ω φ, IsBaseKernel R i v (ownAt D v) ω φ → ∃ χ ξR, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ := by
  first | exact @GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel | exact GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel | (intros; apply GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV


theorem _root_.GlobalTheory.T.flatTensor_depends_below_and_small_translation_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → (∀ (x x' : ColArgs G) (y y' : RowArgs G), (∀ j, j < G.m → x j = x' j) → (∀ i, i < G.m → y i = y' i) → flatTensor hs ψ ν (moved G keep g T) x y = flatTensor hs ψ ν (moved G keep g T) x' y') ∧ ∃ n : ℕ, ∀ (x a : ColArgs G) (y b : RowArgs G), (∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → (∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → flatTensor hs ψ ν (moved G keep g T) (x + a) (y + b) = flatTensor hs ψ ν (moved G keep g T) x y := by
  first | exact @GlobalTheory.FunObj.FlatDep.flatTensor_dep_and_per | exact GlobalTheory.FunObj.FlatDep.flatTensor_dep_and_per | (intros; apply GlobalTheory.FunObj.FlatDep.flatTensor_dep_and_per <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA (Dinv xi_mem_Dinv int_of_xi)
open GlobalTheory.FunObj.Good (char_int mem_Dinv atPl_mul inc_mul_inc mem_intAE exists_pole isEquiv_Kw valued_alg psiAt_eq_one
  trace_inc_pair cpt_pair)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

namespace CondAA

theorem valued_genAt (w : Pl D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    Valued.v ((genAt w 𝔞 : (Kw w)ˣ) : Kw w) = WithZero.exp (-FractionalIdeal.count D.host.E w 𝔞) := by
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [genAt, Units.val_zpow_eq_zpow_val, map_zpow₀, hu, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

theorem exists_mem_valuation_eq (w : Pl D.host.E) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0) :
    ∃ c ∈ I, w.valuation D.host.E c = WithZero.exp (-FractionalIdeal.count D.host.E w I) := by
  have hw0 : (w.asIdeal : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot
  have hIw : I * w.asIdeal ≠ 0 := mul_ne_zero hI hw0
  have hne : ¬ I ≤ I * w.asIdeal := fun h => by
    have := FractionalIdeal.count_mono D.host.E w hI h
    rw [FractionalIdeal.count_mul D.host.E w hI hw0, FractionalIdeal.count_self] at this
    omega
  obtain ⟨c, hc, hc'⟩ := SetLike.not_le_iff_exists.1 hne
  refine ⟨c, hc, le_antisymm ((GlobalTheory.Idele.mem_iff_valuation_le hI c).1 hc w) ?_⟩
  by_contra hlt
  push_neg at hlt
  refine hc' ((GlobalTheory.Idele.mem_iff_valuation_le hIw c).2 fun Q => ?_)
  rw [FractionalIdeal.count_mul D.host.E Q hI hw0]
  by_cases hQ : w = Q
  · subst hQ
    rw [FractionalIdeal.count_self]
    rcases eq_or_ne (w.valuation D.host.E c) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · rw [← WithZero.exp_log h0, WithZero.exp_lt_exp] at hlt
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
  · rw [FractionalIdeal.count_maximal_coprime D.host.E Q hQ, add_zero]
    exact (GlobalTheory.Idele.mem_iff_valuation_le hI c).1 hc Q

end CondAA


open CondAA in
theorem hasConductor_psiAt_AA {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E) :
    HasConductor (psiAt W w) (genAt w D.host.AA * genAt w D.host.AAbar) := by
  classical
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have e := isEquiv_Kw w
  have hA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero hP D
  have hB : D.host.AAbar ≠ 0 := fun h => by
    have h1 := hP D.R D.host
    rw [h, mul_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hI : D.host.AA * D.host.AAbar ≠ 0 := mul_ne_zero hA hB
  set n := FractionalIdeal.count D.host.E w (D.host.AA * D.host.AAbar) with hn
  have hv : Valued.v (((genAt w D.host.AA * genAt w D.host.AAbar : (Kw w)ˣ)) : Kw w) = WithZero.exp (-n) := by
    rw [Units.val_mul, map_mul, valued_genAt, valued_genAt, ← WithZero.exp_add, hn,
      FractionalIdeal.count_mul D.host.E w hA hB, neg_add]
  have hint : ∀ y : Kw w, Valued.v y ≤ 1 → finPart D (atPl w y) ∈ intAE D := fun y hy => mem_intAE fun Q => by
    rw [(atPl_spec w y).2]
    by_cases h : Q = w
    · subst h; simpa using hy
    · simp [h]
  intro x
  rw [e x, hv]
  refine ⟨fun h => ?_, fun hx y hy => ?_⟩
  · by_contra hx
    obtain ⟨u, hu, hu1, hu2⟩ := exists_pole w
    refine hu (int_of_xi hP D fun a ha j hj => mem_Dinv.2 fun c => ?_)
    have hx1 : WithZero.exp (-n + 1) ≤ Valued.v x := by
      have h0 : Valued.v x ≠ 0 := fun h0 => hx (h0 ▸ zero_le')
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at hx
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
    have haj : w.valuation D.host.E (a * j) ≤ WithZero.exp (-n) :=
      (GlobalTheory.Idele.mem_iff_valuation_le hI (a * j)).1 (FractionalIdeal.mul_mem_mul ha hj) w
    have hn' : D.host.xi0 * (a * j) * c ∈ Dinv D := by
      rw [mul_comm]
      exact (Dinv D).coeToSubmodule.smul_mem c (xi_mem_Dinv hP D ha hj)
    have h1 := (psiAt_eq_one W w _).1 (h (algebraMap D.host.E (Kw w) (a * j * c) * algebraMap D.host.E (Kw w) u) (by
      rw [e, map_mul, valued_alg, valued_alg, map_mul]
      refine le_trans ?_ hx1
      calc _ ≤ WithZero.exp (-n) * 1 * WithZero.exp (1 : ℤ) :=
            mul_le_mul' (mul_le_mul' haj (w.valuation_le_one c)) hu1
        _ = _ := by rw [mul_one, ← WithZero.exp_add]))
    rw [atPl_mul, inc_mul_inc] at h1
    have h2 := char_int W.ψ_std hn' (z := pairA D.host.F 0 1 ⊗ₜ[D.host.F] u - atPl w (algebraMap D.host.E (Kw w) u))
      (by rw [RingHom.map_sub, GlobalTheory.LatVac.infPart_pair, (atPl_spec w _).1, sub_zero]) (mem_intAE fun Q => by
        rw [RingHom.map_sub, RingHom.map_sub, cpt_pair, (atPl_spec w _).2]
        by_cases hQ : Q = w
        · subst hQ; simp
        · rw [Pi.single_eq_of_ne hQ, sub_zero, valued_alg]
          exact hu2 Q hQ)
    rw [← mul_assoc D.host.xi0, ← mul_assoc D.host.xi0] at h1
    rw [← mul_assoc D.host.xi0] at h2
    have h3 : W.ψ (Algebra.trace (AF D.host.F) (AE D)
        (incA D (D.host.xi0 * a * j * c) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u))) = 1 := by
      rw [← sub_add_cancel (pairA D.host.F 0 1 ⊗ₜ[D.host.F] u : AE D) (atPl w (algebraMap D.host.E (Kw w) u)), mul_add,
        map_add, W.ψ.map_add_eq_mul, h1, h2, one_mul]
    rw [trace_inc_pair, one_mul, GlobalTheory.LatVac.char_rat W.ψ_std] at h3
    rwa [show D.host.xi0 * (a * (j * u)) * c = D.host.xi0 * a * j * c * u by ring]
  · obtain ⟨c, hc, hcv⟩ := exists_mem_valuation_eq w hI
    have hy1 : Valued.v y ≤ WithZero.exp (-n) := ((e y x).1 hy).trans hx
    have hξc : D.host.xi0 * c ∈ Dinv D := by
      rw [show Dinv D = _ from (Formalism.L2.Pj.dual_eq hP D).symm, mul_assoc]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hc
    have hvc : Valued.v (algebraMap D.host.E (Kw w) c) = WithZero.exp (-n) := by rw [valued_alg, hcv]
    have h0 : algebraMap D.host.E (Kw w) c ≠ 0 := fun h => by
      rw [h, map_zero] at hvc
      exact WithZero.exp_ne_zero hvc.symm
    rw [psiAt_eq_one, ← mul_inv_cancel_left₀ h0 y, atPl_mul, inc_mul_inc]
    refine char_int W.ψ_std hξc (atPl_spec w _).1 (hint _ ?_)
    rw [map_mul, map_inv₀, hvc]
    calc _ ≤ (WithZero.exp (-n))⁻¹ * WithZero.exp (-n) := mul_le_mul' le_rfl hy1
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero

end GlobalTheory.FunObj

end
end

section

namespace StabilizerBasis
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.StabBasis

theorem exists_bc_eq_of_entries {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (g : GL (Fin n) R)
    (h1 : ∀ i j, g.1 i j ∈ S) (h2 : ∀ i j, g⁻¹.1 i j ∈ S) :
    ∃ y : GL (Fin n) S, Formalism.UG.bc S.subtype y = g := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) S => A.map S.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem mem_St_of_inBasis_mem_KO : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)),
    (∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin n)) → x ∈ St β := by
  intro D n β x h
  have hent : ∀ (w : Pl D.host.E) (g : GL (Fin n) (Kw w)), g ∈ KO (Kw w) (Fin n) →
      ∀ i j, g.1 i j ∈ Formalism.UG.Ov D.host.E w := by
    intro w g hg i j
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hg
    obtain ⟨u, rfl⟩ := hg
    exact (u.1 i j).2
  have e2 : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  have a1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j =>
    (mem_OA_iff _).2 fun w => by
      have := hent w _ (h w) i j
      rwa [inBasis_apply] at this
  have a2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j =>
    (mem_OA_iff _).2 fun w => by
      have := hent w _ ((KO (Kw w) (Fin n)).inv_mem (h w)) i j
      rw [← map_inv, inBasis_apply] at this
      rwa [e2]
  obtain ⟨y, hy⟩ := exists_bc_eq_of_entries _ _ a1 a2
  refine ⟨y, ?_⟩
  have e : Formalism.L2.DIV.intGL D.host.F D.host.E n y = β⁻¹ * x * β := hy
  show β * Formalism.L2.DIV.intGL D.host.F D.host.E n y * β⁻¹ = x
  rw [e]; group

end GlobalTheory.CompanionTheory.StabBasis

end
end

end StabilizerBasis
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)), (∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin n)) → x ∈ St β := by
  first | exact @StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO | exact StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO | (intros; apply StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO <;> assumption)

end
end
end

section

namespace ReductionComponent
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.RedComp

variable {D : D7}

theorem val_lt_one_iff (PP : Pl D.host.E) (x : Kw PP) :
    valuation (Kw PP) x < 1 ↔ Valued.v x < 1 := by
  haveI : (Valued.v : Valuation (Kw PP) _).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (Kw PP)) Valued.v).lt_one_iff_lt_one

theorem cpt_oToS (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    cpt PP ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
      algebraMap D.host.E (Kw PP) (a : D.host.E) := by
  have h : toAd D ((algebraMap (𝓞 D.host.E) D.host.E a) ⊗ₜ[D.host.F] (1 : Af D.host.F)) = _ :=
    GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) _
  show (Formalism.UG.evalV D.host.E PP) (toAd D ((algebraMap (𝓞 D.host.E) D.host.E a) ⊗ₜ[D.host.F] (1 : Af D.host.F))) = _
  rw [h]
  rfl

theorem v_algebraMap_lt_one_iff (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    Valued.v (algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 ↔ a ∈ PP.asIdeal := by
  have h : Valued.v (algebraMap D.host.E (Kw PP) (a : D.host.E)) = PP.valuation D.host.E (a : D.host.E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' PP _
  rw [h]
  exact PP.valuation_lt_one_iff_mem a

def ballIdeal (PP : Pl D.host.E) : Ideal (Formalism.L2.Herm.intAf D.host.F D.host.E) where
  carrier := {s | Valued.v (cpt PP ((s : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) < 1}
  add_mem' := by
    intro s t hs ht
    show Valued.v (cpt PP (((s + t : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1
    rw [Subring.coe_add, map_add (f := _)]
    exact Valuation.map_add_lt _ hs ht
  zero_mem' := by
    show Valued.v (cpt PP (((0 : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1
    simp
  smul_mem' := by
    intro c s hs
    show Valued.v (cpt PP (((c * s : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1
    have hc : Valued.v (cpt PP ((c : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) ≤ 1 := (mem_OA_iff _).1 c.2 PP
    rw [Subring.coe_mul, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hs

theorem idS_le_ballIdeal (PP : Pl D.host.E) : idS D.host.F PP.asIdeal ≤ ballIdeal PP := by
  refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  show Valued.v (cpt PP ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) < 1
  rw [cpt_oToS]
  exact (v_algebraMap_lt_one_iff PP a).2 ha

theorem mem_idS_of_resS_eq_zero (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : resS D.host.F PP s = 0) : s ∈ idS D.host.F PP.asIdeal := by
  unfold resS at h
  rw [RingHom.comp_apply] at h
  have h2 : (RingEquiv.ofBijective (cmpS D.host.F PP.asIdeal) (cmpS_bij (F := D.host.F) PP.asIdeal PP.ne_bot)).symm
      (Ideal.Quotient.mk (idS D.host.F PP.asIdeal) s) = 0 := h
  have h3 := (RingEquiv.symm_apply_eq _).1 h2
  rw [map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.1 h3

theorem resS_eq_mk_iff (PP : Pl D.host.E) (z : Formalism.L2.Herm.intAf D.host.F D.host.E) (a : 𝓞 D.host.E) :
    resS D.host.F PP z = Ideal.Quotient.mk PP.asIdeal a ↔
      Valued.v (cpt PP ((z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS D.host.F PP z)
  have h0 : resS D.host.F PP (z - oToS D.host.F D.host.E b) = 0 := by
    rw [map_sub, resS_oToS, hb, sub_self]
  have hv : Valued.v (cpt PP ((z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - algebraMap D.host.E (Kw PP) (b : D.host.E)) < 1 := by
    have h1 := idS_le_ballIdeal PP (mem_idS_of_resS_eq_zero PP _ h0)
    have h2 : Valued.v (cpt PP (((z - oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1 := h1
    rwa [AddSubgroupClass.coe_sub, map_sub, cpt_oToS] at h2
  have hba : Valued.v (algebraMap D.host.E (Kw PP) ((b - a : 𝓞 D.host.E) : D.host.E)) < 1 ↔
      resS D.host.F PP z = Ideal.Quotient.mk PP.asIdeal a := by
    rw [v_algebraMap_lt_one_iff, ← hb, Ideal.Quotient.eq]
  have hsub : algebraMap D.host.E (Kw PP) ((b - a : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.E (Kw PP) (b : D.host.E) - algebraMap D.host.E (Kw PP) (a : D.host.E) := by
    rw [← map_sub]; rfl
  rw [← hba, hsub]
  constructor
  · intro h
    have := Valuation.map_add_lt _ hv h
    rwa [sub_add_sub_cancel] at this
  · intro h
    have h3 := Valuation.map_sub_lt (v := Valued.v) h hv
    rwa [sub_sub_sub_cancel_left] at h3

theorem redFn_entry_eq_mk_iff : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (PP : Pl D.host.E), x ∈ St β → ∀ (i j : Fin n) (a : 𝓞 D.host.E), ((redFn β PP x : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j = Ideal.Quotient.mk PP.asIdeal a ↔ valuation (Kw PP) ((inBasis rfl β PP x).1 i j - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  intro D n β x PP hx i j a
  obtain ⟨y, rfl⟩ := hx
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  rw [redFn_frGL, inBasis_apply, e1, val_lt_one_iff]
  exact resS_eq_mk_iff PP (y.1 i j) a

end GlobalTheory.CompanionTheory.RedComp

end
end

end ReductionComponent
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (PP : Pl D.host.E), x ∈ St β → ∀ (i j : Fin n) (a : 𝓞 D.host.E), ((redFn β PP x : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j = Ideal.Quotient.mk PP.asIdeal a ↔ valuation (Kw PP) ((inBasis rfl β PP x).1 i j - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  first | exact @ReductionComponent.GlobalTheory.CompanionTheory.RedComp.redFn_entry_eq_mk_iff | exact ReductionComponent.GlobalTheory.CompanionTheory.RedComp.redFn_entry_eq_mk_iff | (intros; apply ReductionComponent.GlobalTheory.CompanionTheory.RedComp.redFn_entry_eq_mk_iff <;> assumption)

end
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.T.originDatum_value_halfIntegerPow_placeAA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E), (∀ a : Kw w, valuation (Kw w) a ≤ valuation (Kw w) ((genAt w D.host.AA * genAt w D.host.AAbar : (Kw w)ˣ) : Kw w) → psiAt W w a = 1) → ∃ n : ℤ, (aaTerm W w).datum 0 0 = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧ |n| ≤ 8 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 * (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  first | exact @GlobalTheory.OriginBox.aaTerm_datum_origin | exact GlobalTheory.OriginBox.aaTerm_datum_origin | (intros; apply GlobalTheory.OriginBox.aaTerm_datum_origin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.T.unfoldingTerm_coef_eq_residueCard_zpow : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E), ∃ n : ℤ, (aaTerm W w).coef = (resCard (Kw w) : ℚ) ^ n ∧ |n| ≤ 2 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 * (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  first | exact @GlobalTheory.FunObj.AaCoef.aaTerm_coef_eq_zpow | exact GlobalTheory.FunObj.AaCoef.aaTerm_coef_eq_zpow | (intros; apply GlobalTheory.FunObj.AaCoef.aaTerm_coef_eq_zpow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_orthonormalBasis_splitSupported_adelicPoint : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK →
    (∀ τ, V.sig τ = (V.rank, 0)) → IsSelfDualC V Λ → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    ∃ (fr : GL (Fin V.rank) D.host.E) (u : GfC V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  first | exact @GlobalTheory.FunObj.StdVertex.exists_std_vertex | exact GlobalTheory.FunObj.StdVertex.exists_std_vertex | (intros; apply GlobalTheory.FunObj.StdVertex.exists_std_vertex <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

theorem _root_.GlobalTheory.T.detProductDepthInChart_eq_sum_factorDepths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), nuProdC Ch X cx = ∑ f : Lt1 Dw, nuFacC Ch X f (cx f) := by
  first | exact @GlobalTheory.FactorDepthProd.nuProdC_eq_sum | exact GlobalTheory.FactorDepthProd.nuProdC_eq_sum | (intros; apply GlobalTheory.FactorDepthProd.nuProdC_eq_sum <;> assumption)
end

section


theorem _root_.GlobalTheory.T.polyCoeff_vectors_lie_in_finiteDimensional_smooth : GlobalTheory.PsCo.Pc3.UFin := by
  first | exact @GlobalTheory.PsCo.Pc3.uFin | exact GlobalTheory.PsCo.Pc3.uFin | (intros; apply GlobalTheory.PsCo.Pc3.uFin <;> assumption)
end
