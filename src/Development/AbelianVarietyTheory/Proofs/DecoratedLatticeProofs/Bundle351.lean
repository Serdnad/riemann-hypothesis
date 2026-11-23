module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle333
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle336
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_linearLaw_halfVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Lat S)
    (ΛT : Lat T) (e : AE D) (f₀ : WO S T → ℂ)
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsSplitIdem D e → IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀) →
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ →
      om (g, h) (Tm Φ) = GlobalTheory.SplitLinear.fac S T χS χT x y • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  first | exact @GlobalTheory.SplitLinearHalf.law_half | exact GlobalTheory.SplitLinearHalf.law_half | (intros; apply GlobalTheory.SplitLinearHalf.law_half <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

theorem residue_pr_int_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ c : 𝓞 D.host.E,
    ∃ h : p.pr (incA D (algebraMap (𝓞 D.host.E) D.host.E c)) ∈ 𝒪[k], (residue 𝒪[k] ⟨_, h⟩ = 0 ↔ c ∈ P.asIdeal) := by
  intro D k _ _ _ _ p P hP c
  have h : p.pr (incA D (c : D.host.E)) ∈ 𝒪[k] := GlobalTheory.LocMod.FullLatFrame.pr_int_mem p c
  refine ⟨h, ?_⟩
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  by_cases hc : c = 0
  · subst hc
    have h0 : (⟨_, h⟩ : 𝒪[k]) = 0 := by
      apply Subtype.ext
      simp
    refine ⟨fun _ => zero_mem _, fun _ hu => ?_⟩
    exact not_isUnit_zero (h0 ▸ hu)
  have hc' : (c : D.host.E) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have hinv : p.pr (incA D (c : D.host.E)) * p.pr (incA D (c : D.host.E)⁻¹) = 1 := by
    rw [← RingHom.map_mul, ← map_mul (incA D), mul_inv_cancel₀ hc', map_one, map_one]
  rw [hP.2 c hc, ← p.sec_pr, ← p.int_iff]
  apply not_congr
  constructor
  · intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hy' : p.pr (incA D (c : D.host.E)) * (y : k) = 1 := congrArg Subtype.val hy
    have hne : p.pr (incA D (c : D.host.E)) ≠ 0 := left_ne_zero_of_mul_eq_one hinv
    have : p.pr (incA D (c : D.host.E)⁻¹) = y := mul_left_cancel₀ hne (hinv.trans hy'.symm)
    rw [this]; exact y.2
  · intro hi
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝒪[k]) (Subtype.ext hinv)

end GlobalTheory.PhiOneVal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

theorem residue_eq_zero_iff_val_lt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : 𝒪[k]) : residue 𝒪[k] t = 0 ↔ valuation k (t : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem resField_equiv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x : 𝓞 D.host.E, q.pr (incA D (x : D.host.E)) ∈ 𝒪[k]) ∧ ∃ ρ : 𝓀[k] ≃+* (𝓞 D.host.E ⧸ PP.asIdeal), ∀ (x : 𝓞 D.host.E) (t : 𝒪[k]), (t : k) = q.pr (incA D (x : D.host.E)) → ρ (residue 𝒪[k] t) = Ideal.Quotient.mk PP.asIdeal x := by
  intro D k _ _ _ _ q PP he
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  have hmem : ∀ x : 𝓞 D.host.E, q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := fun x => by
    rw [q.pr_mem_iff]
    exact mul_mem hint (Formalism.L2.DIV.oToS D.host.F D.host.E x).2
  refine ⟨hmem, ?_⟩
  let ψ : 𝓞 D.host.E →+* 𝒪[k] :=
    ((q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[k] hmem
  have hψ : ∀ x, (ψ x : k) = q.pr (incA D (x : D.host.E)) := fun x => rfl
  let φ : 𝓞 D.host.E →+* 𝓀[k] := (residue 𝒪[k]).comp ψ
  have hker : RingHom.ker φ = PP.asIdeal := by
    ext x
    have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
        toEAf D (incA D (x : D.host.E)) := rfl
    rw [RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff_val_lt, hψ, q.mem_iff_val_lt he, e1, prF_toEAf]
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    set z : EAf D := toEAf D (q.sec a) with hz
    have hprz : q.prF he z = a := by rw [hz, prF_toEAf, q.pr_sec]
    have hoff : (1 - toEAf D q.e) * z = 0 := by
      have he1 : toEAf D q.e * z = z := by
        rw [hz, ← RingHom.map_mul, ← q.sec_pr, q.pr_sec]
      rw [sub_mul, one_mul, he1, sub_self]
    have hzint : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      (q.mem_intAf_iff he z).2 ⟨by rw [hoff]; exact zero_mem _, by rw [hprz]; exact a.2⟩
    obtain ⟨x, hx0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot ⟨z, hzint⟩
    have hx : (⟨z, hzint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E x ∈
        Formalism.L2.DIV.idS D.host.F PP.asIdeal := hx0
    have hv := q.val_lt_of_mem_idS he hx
    refine ⟨x, ?_⟩
    show residue 𝒪[k] (ψ x) = residue 𝒪[k] a
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_val_lt]
    have e1 : (((⟨z, hzint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E x :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = z - toEAf D (incA D (x : D.host.E)) := rfl
    rw [e1, map_sub, hprz, prF_toEAf] at hv
    have e2 : ((ψ x - a : 𝒪[k]) : k) = -((a : k) - q.pr (incA D (x : D.host.E))) := by
      rw [AddSubgroupClass.coe_sub, hψ]; ring
    rw [e2, Valuation.map_neg]; exact hv
  refine ⟨((Ideal.quotEquivOfEq hker).symm.trans (RingHom.quotientKerEquivOfSurjective hsurj)).symm, ?_⟩
  intro x t ht
  have htx : t = ψ x := Subtype.ext (by rw [ht, hψ])
  rw [RingEquiv.symm_apply_eq, htx]
  rfl

end GlobalTheory.FinPl.SplitPt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_max_iff_val_lt_one (x : 𝒪[k]) : x ∈ IsLocalRing.maximalIdeal 𝒪[k] ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem pr_incA_int_mem (q : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] :=
  (q.pr_mem_iff _).2 (mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he).1
    (Formalism.L2.DIV.oToS D.host.F D.host.E x).2)

theorem exists_int_approx (q : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    {u : k} (hu : u ∈ 𝒪[k]) : ∃ z : 𝓞 D.host.E, valuation k (u - q.pr (incA D (z : D.host.E))) < 1 := by
  have h1 : toEAf D (q.e * q.sec u) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [map_mul]
    exact (q.pr_mem_iff (q.sec u)).1 (by rw [q.pr_sec]; exact hu)
  have h2 : q.pr (q.e * q.sec u) = u := by rw [← q.sec_pr, q.pr_sec, q.pr_sec]
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot
    (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
  have ha : (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈
    Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h3 := q.val_lt_of_mem_idS he ha
  have e2 : (((⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E a :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (q.e * q.sec u) - toEAf D (incA D (a : D.host.E)) := rfl
  rw [e2, RingHom.map_sub, prF_toEAf, prF_toEAf, h2] at h3
  exact ⟨a, h3⟩

theorem hasVal_of_int_vectors : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ (m : ℕ) (b b' : Matrix (Fin m) (Fin m) k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) → ∀ c₀ : 𝓞 D.host.E,
    (∀ z : Fin m → D.host.E, (∀ r, IsIntegral ℤ (z r)) → ∀ r : Fin m, r.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D ((c₀ : D.host.E) * z r)) ∧
        P.HasVal (b' *ᵥ fun r' => p.pr (incA D (z r'))) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m, r0.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D (c₀ : D.host.E)) * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s) := by
  intro D k _ _ _ _ p PP he m b b' hb _ P hlat c₀ hval u hu r0 hr0
  classical
  choose z hz using fun r => p.exists_int_approx he (hu r)
  obtain ⟨s, hs, hv⟩ := hval (fun r => (z r : D.host.E)) (fun r => (z r).isIntegral_coe) r0 hr0
  have hw : ∀ r, p.pr (incA D (z r : D.host.E)) ∈ 𝒪[k] := fun r => p.pr_incA_int_mem he (z r)
  let d : Fin m → 𝒪[k] := fun r => ⟨u r - p.pr (incA D (z r : D.host.E)), sub_mem (hu r) (hw r)⟩
  have hd : ∀ r, d r ∈ maximalIdeal 𝒪[k] := fun r => (mem_max_iff_val_lt_one (d r)).2 (hz r)
  have hcol : ∀ r, b' *ᵥ (Pi.single r 1 : Fin m → k) ∈ P.lat := fun r => (hlat _).2 fun r' => by
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have hker : ∑ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) ∈ P.ker :=
    Submodule.sum_mem _ fun r _ => Pair.smul_mem_ker (hd r) (hcol r)
  have hsum : b' *ᵥ u = (b' *ᵥ fun r' => p.pr (incA D (z r' : D.host.E))) +
      ∑ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) := by
    have : ∀ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) = b' *ᵥ (Pi.single r (d r : k) : Fin m → k) := fun r => by
      change (d r : k) • (b' *ᵥ (Pi.single r 1 : Fin m → k)) = _
      rw [← Matrix.mulVec_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun r _ => this r, ← Matrix.mulVec_sum, ← Matrix.mulVec_add, Finset.univ_sum_single]
    congr 1
    funext r
    simp [d]
  let c : 𝒪[k] := ⟨_, p.pr_incA_int_mem he c₀⟩
  refine ⟨s + c * d r0, ?_, ?_⟩
  · change (s : k) + p.pr (incA D (c₀ : D.host.E)) * (u r0 - p.pr (incA D (z r0 : D.host.E))) = _
    rw [hs, map_mul, map_mul]
    ring
  · rw [hsum, map_add (f := _), (IsLocalRing.residue_eq_zero_iff _).2 (Ideal.mul_mem_left _ c (hd r0))]
    exact hv.add (Pair.mem_ker.1 hker)

end GlobalTheory.FinPl.SplitPt

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.PinInhab

section SlopeTestRemainingChoices
open GlobalTheory.FinPl (SplitPt idAt idOff grpAt grpOff congGrp compAt)
open GlobalTheory.IdemSupport GlobalTheory.LocMod.SevPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_add (q : SplitPt D k) : q.e * (q.e + cA D q.e) = q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  rw [mul_add, h1, h2, add_zero]

theorem v_eq_under (q : SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt q.e P) :
    q.v = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨ε, hε, hs⟩ := q.above
  by_contra hne
  have h0 := (place_comp hΦ hε).2.2 P (fun e => hne e.symm)
  have h1 := ev_mul (Φ := Φ) q.e (q.e + cA D q.e) P
  rw [e_mul_add, hs, h0, mul_zero, (delta_of_isIdemAt hΦ h).2.1] at h1
  exact one_ne_zero h1

theorem idem_unique {P : HeightOneSpectrum (𝓞 D.host.E)} {e e' : Formalism.L2.Theta.AE D} (h : Formalism.L2.NTheta.IsIdemAt e P)
    (h' : Formalism.L2.NTheta.IsIdemAt e' P) : e = e' := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ h
  have hd' := delta_of_isIdemAt hΦ h'
  refine hΦ.ext' (by rw [hd.1, hd'.1]) fun Q => ?_
  by_cases hQ : Q = P
  · subst hQ; rw [hd.2.1, hd'.2.1]
  · rw [hd.2.2 Q hQ, hd'.2.2 Q hQ]

theorem mem_congGrp {V : HSp D} {I : Ideal (Formalism.L2.Theta.AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, (mt V g - 1) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (Formalism.L2.Theta.AE D ⧸ I) => x.1 i j) h
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem mem_idAt_of_supp (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D P := by
  obtain ⟨ε, hε, hs⟩ := q.above
  have h1 := ((GlobalTheory.FinPl.placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at h1 ⊢
  exact ⟨h1.1, fun w hw => h1.2 w fun e => hw (e ▸ hP)⟩

theorem pr_eq_zero_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (ha : a ∈ idOff D P) : q.pr a = 0 := by
  have he : q.e ∈ idAt D (· = q.v) := mem_idAt_of_supp q (P := (· = q.v)) rfl (by rw [mul_comm, e_mul_add])
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at he
  have hv : compAt D q.v a = 0 := by
    unfold idOff at ha
    rw [Submodule.mem_iInf] at ha
    exact RingHom.mem_ker.1 (ha ⟨q.v, hP⟩)
  refine pr_eq_zero q (GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero D _ ?_ fun w => ?_)
  · rw [RingHom.map_mul, he.1, zero_mul]
  · rw [RingHom.map_mul]
    by_cases hw : w = q.v
    · rw [hw, hv, mul_zero]
    · rw [he.2 w hw, zero_mul]

theorem map_mt_eq_one_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {V : HSp D} {g : GA D V}
    (hg : g ∈ grpOff V P) : (mt V g).map q.pr = 1 := by
  ext i j
  have h1 := pr_eq_zero_of_off q hP (mem_congGrp.1 hg i j)
  rw [Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, sub_eq_zero.1 h1]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

end SlopeTestRemainingChoices

end GlobalTheory.LocMod.PinInhab
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSawKernelLiftCombination_of_definiteClassData : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → KerX t := by
  first | exact @GlobalTheory.SeeSaw.kerX_of_clsPinD | exact GlobalTheory.SeeSaw.kerX_of_clsPinD | (intros; apply GlobalTheory.SeeSaw.kerX_of_clsPinD <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)

namespace GlobalTheory.FinPl

theorem sec_mul_sec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {D : D7}
    (p : SplitPt D k) (a : AE D) (u : k) : p.sec (p.pr a * u) = a * p.sec u := by
  have h1 : p.sec (p.pr a * u) = p.sec (p.pr (a * p.sec u)) := by rw [map_mul p.pr, p.pr_sec]
  have h2 : p.e * p.sec u = p.sec u := by rw [← p.sec_pr, p.pr_sec]
  rw [h1, p.sec_pr, mul_left_comm, h2]

theorem mulVec_sec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {D : D7}
    (p : SplitPt D k) {r : ℕ} (m : Matrix (Fin r) (Fin r) (AE D)) (u : Fin r → k) :
    m *ᵥ (fun i => p.sec (u i)) = fun i => p.sec ((m.map p.pr *ᵥ u) i) := by
  funext i

  simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, sec_mul_sec]

theorem single_mem_gluedS {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [DecidableEq n] (q : Unif k) (P : Pair k n) :
    (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ gluedS q 1 P.ker P.vec := by
  refine GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨q.1, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
  · have h0 : (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
      funext j
      simp
    rw [h0, zero_sub]
    exact neg_mem (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [Pi.single_eq_same, Unif.inv, inv_mul_cancel₀ q.ne_zero]

theorem zero_col_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), GluedCore B L₀ q β β₀ P → ∀ γ : GA D B.V₀, (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)) i)) ∈ latV B.V₀ L₀ (· = p.v) := by
  intro D k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hg γ hpres
  have he : p.sec 1 = p.e := by rw [← map_one p.pr, p.sec_pr, mul_one]
  have hvec : p.sec 1 • ratV (vecB B.o B.ζ) =
      fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)) i) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, he, mulVec_single_one, hg.sum]
    simp [p.sec_pr]
  have hmem : p.sec 1 • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) := by
    rw [hg.unit.2, hvec, ← hg.lat]
    exact single_mem_gluedS q P
  have := hpres _ hmem
  rwa [hg.unit.2, hvec] at this

theorem orbitGlued (D : D7) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ)
      (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1))
      (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P →
      ∀ γ ∈ grpAt B.V₀ (· = p.v),
        (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) →
          mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) →
        (∃ a ∈ grpAt B.A (· = p.v), ∃ κ, InK B.V₀ L₀ (· = p.v) κ ∧ γ = B.o.emb (a, 1) * κ) ∨
        ∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsFullLattice k),
          β₀.IsLatMoved γ L₀ (lastKer Λ) ∨ β₀.IsLatMoved γ L₀ (lastPair q Λ).lat := by
  intro k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hsd hg γ hγ hpres
  obtain ⟨hF1, -, -, hF4, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.V₀ (n ⊕ Fin 1) β₀
  obtain ⟨h, rfl⟩ := (hF1 γ).1 hγ
  have key : ∀ x, mt B.V₀ (β₀.gl h)⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) ↔
      x ∈ h • gluedS q 1 P.ker P.vec := by
    intro x
    rw [← map_inv, mulVec_sec, β₀.gl_mat, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, β₀.b'b,
      Matrix.mul_one, ← mulVec_mulVec, ← hg.lat, GlobalTheory.LatPair.mem_smul_iff]
    rfl
  have hz := (key _).1 (zero_col_mem D k p n q σ B L₀ β β₀ P hg _ hpres)
  have hint : ∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] :=
    fun x hx => GlobalTheory.T.gluedSplitPlace_lineCoordinate_integral D k p n q σ B L₀ β β₀ P hsd hg _ hγ hpres x ((key x).2 hx)
  rcases GlobalTheory.T.smul_gluedLatticeFirstPosition_cases k n q P h hz hint with ⟨Λ, hΛ, hM | hM⟩ | ⟨g, hM⟩
  · exact Or.inr ⟨Λ, hΛ, Or.inl fun x => by rw [← hM]; exact (key x).symm⟩
  · exact Or.inr ⟨Λ, hΛ, Or.inr fun x => by rw [← hM]; exact (key x).symm⟩
  · obtain ⟨hA1, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.A n β
    obtain ⟨Λ₀, -, hΛ₀, hK⟩ := hF4 L₀ hsd
    have hΛG : Λ₀ = gluedS q 1 P.ker P.vec := Submodule.ext fun x => (hΛ₀ x).trans (hg.lat x).symm
    refine Or.inl ⟨β.gl g, (hA1 _).2 ⟨g, rfl⟩, β₀.gl ((embX 1 g)⁻¹ * h), ?_, ?_⟩
    · rw [hK, hΛG, mul_smul, hM, inv_smul_smul]
    · rw [GlobalTheory.T.orthogonalEmbedding_splitPlace_blockDiagonal D k p n σ B β β₀ hg.sum g, ← map_mul, mul_inv_cancel_left]

end GlobalTheory.FinPl
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem isThetaFunO_sliceT :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (f : WO T S → ℂ) (y : WO T L),
      IsThetaFunO ψ T S f → IsThetaFunO ψ T A (fun w => f ((o.resT T).symm (w, y))) :=
  fun _ _ _ _ _ _ o _ y hf => GlobalTheory.SliceModelT.isThetaFunO_sliceT_left o hf y

end GlobalTheory.FinPl.ExtZero
end
