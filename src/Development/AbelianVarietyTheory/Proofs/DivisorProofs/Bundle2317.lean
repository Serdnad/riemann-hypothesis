module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismOpenAffineLineAbelianSchemeConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Mathlib.Data.Int.WithZero
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.Field.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

open IsDedekindDomain IsLocalRing

theorem exists_realValuation_of_discreteValuationSubring {Ω : Type} [Field Ω]
    (V : ValuationSubring Ω) [IsDiscreteValuationRing V] :
    ∃ ν : Valuation Ω ℝ≥0, (∀ x : V, ν (x : Ω) ≤ 1) ∧ ∀ x ∈ maximalIdeal V, ν (x : Ω) < 1 := by
  have hne : maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  let v : HeightOneSpectrum V := ⟨maximalIdeal V, inferInstance, hne⟩
  let hmono := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num))
  refine ⟨Valuation.map { WithZeroMulInt.toNNReal (e := 2) (by norm_num) with
    monotone' := hmono.monotone } (v.valuation Ω),
    fun x => ?_, fun x hx => ?_⟩
  · have h := v.valuation_le_one (K := Ω) x
    have := hmono.monotone h
    simpa using this
  · have h := (v.valuation_lt_one_iff_mem (K := Ω) x).mpr hx
    have := hmono h
    simpa using this

theorem isIntegral_of_forall_realValuation_le_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω], (⊤ : IntermediateField K Ω).FG → ∀ (A : Subalgebra K Ω), A.FG → ∀ t : Ω, (∀ ν : Valuation Ω ℝ≥0, (∀ a ∈ A, ν a ≤ 1) → ν t ≤ 1) → IsIntegral A t := by
  intro K Ω _ _ _ _ hfg A hA t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType K Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType A Ω := .of_comp K A Ω
  have : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).mp hA
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hic : IsIntegrallyClosedIn (integralClosure A Ω).toSubring Ω :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure A Ω).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := GlobalTheory.exists_discreteValuationSubring_of_valuationSubring (R := A) W
    (fun r => hW ((integralClosure A Ω).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  obtain ⟨ν, hν1, hνm⟩ := exists_realValuation_of_discreteValuationSubring V
  have hle : ν t ≤ 1 := ht ν fun a ha => hν1 ⟨a, h2 ⟨a, ha⟩⟩
  have hn3 : t⁻¹ ∈ V.nonunits := h3 _ rfl
  have htV : t⁻¹ ∈ V :=
    (V.valuation_le_one_iff _).mp (le_of_lt ((V.mem_nonunits_iff).mp hn3))
  have hm : (⟨t⁻¹, htV⟩ : V) ∈ maximalIdeal V :=
    (ValuationSubring.coe_mem_nonunits_iff (a := ⟨t⁻¹, htV⟩)).mp hn3
  have hlt : ν t⁻¹ < 1 := hνm _ hm
  have h1' : ν (t * t⁻¹) = 1 := by rw [mul_inv_cancel₀ ht0, map_one]
  rw [map_mul] at h1'
  have : ν t * ν t⁻¹ < 1 := lt_of_le_of_lt (mul_le_of_le_one_left zero_le hle) hlt
  exact absurd h1' this.ne

end GlobalTheory.DegVal
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (B : Type) [CommRing B] [Algebra Λ B] [Algebra.FiniteType Λ B] (p : Ideal B) [p.IsPrime], (∀ a : Λ, algebraMap Λ B a ∈ p → a = 0) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
  first | exact @GlobalTheory.prime_generically_regular_quotient | exact GlobalTheory.prime_generically_regular_quotient | (intros; apply GlobalTheory.prime_generically_regular_quotient <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Cell

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section Mat

variable {R : Type} [CommRing R] {m : ℕ}

def IsLowInv (L : Matrix (Fin m) (Fin m) R) : Prop := (∀ i j, i < j → L i j = 0) ∧ ∀ i, IsUnit (L i i)

end Mat

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

end Geo

end GlobalTheory.ShFam.Cell
end
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.isRegular_fibre_of_jacobian_derivations : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsRegularRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → ∀ (h : ℕ) (f : Fin h → S) (g : S) (d : Fin h → Derivation ℤ S S) (D : Fin h → Derivation ℤ T T), (∀ i x, D i (algebraMap S T x) = algebraMap S T (d i x)) → g ∉ Q → (∀ j, f j ∈ Q) → (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) → (Matrix.of fun i j => d i (f j)).det ∉ Q → IsRegularRing (T ⊗[S] K) := by
  first | exact @GlobalTheory.regular_fibre_of_jacobian | exact GlobalTheory.regular_fibre_of_jacobian | (intros; apply GlobalTheory.regular_fibre_of_jacobian <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem dlog_of_mul_eq {B : Type} [CommRing B] (a₁ a₂ l g : DualNumber B) (i₁ i₂ il ig : B)
    (h : a₁ * l = g * a₂) (h₁ : a₁.fst * i₁ = 1) (h₂ : a₂.fst * i₂ = 1) (hl : l.fst * il = 1)
    (hg : g.fst * ig = 1) : g.snd * ig = l.snd * il + (a₁.snd * i₁ - a₂.snd * i₂) := by
  have h0 : a₁.fst * l.fst = g.fst * a₂.fst := by simpa using congrArg TrivSqZeroExt.fst h
  have h1 : a₁.fst * l.snd + a₁.snd * l.fst = g.fst * a₂.snd + g.snd * a₂.fst := by
    have := congrArg TrivSqZeroExt.snd h
    rwa [DualNumber.snd_mul, DualNumber.snd_mul] at this
  have e1 : a₁.fst * ig * i₂ = il := by
    linear_combination (ig * i₂ * il) * h0 - (a₁.fst * ig * i₂) * hl + (a₂.fst * i₂ * il) * hg + il * h₂
  have e2 : l.fst * ig * i₂ = i₁ := by
    linear_combination (ig * i₂ * i₁) * h0 - (l.fst * ig * i₂) * h₁ + (a₂.fst * i₂ * i₁) * hg + i₁ * h₂
  linear_combination (-(ig * i₂)) * h1 + l.snd * e1 + a₁.snd * e2 - (a₂.snd * i₂) * hg - (g.snd * ig) * h₂

theorem valR_fst_mul_inv {Y : Scheme.{0}} {B : Type} [CommRing B] {x : Sp B ⟶ Y} {w : Sp (DualNumber B) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) (u : Γ(Y, O)ˣ) :
    (valR w O u.val).fst * valR x O u⁻¹.val = 1 := by
  have h' := le_preimage_of_red hw h
  subst hw
  have e : (valR w O u.val).fst = ev _ O h u.val := by
    rw [valR_eq_ev _ _ h', GlobalTheory.FlagMod.ev_spMap _ w O h']
    rfl
  rw [e, valR_eq_ev _ _ h, ← map_mul, Units.mul_inv, map_one]

theorem valR_iso_compat {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M)
    (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {S : Type} [CommRing S] (z : Sp S ⟶ Y)
    (h₁ : ⊤ ≤ z ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ z ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))) :
    valR z _ (wg.s (p₁, fun _ => j₁)).val * valR (z ≫ m) _ (L.g j₁ j₂).val =
      valR z _ (M.g p₁ p₂).val * valR z _ (wg.s (p₂, fun _ => j₂)).val := by
  have e := hwg (p₁, fun _ => j₁) (p₂, fun _ => j₂)
  have hz := GlobalTheory.FlagMod.le_preimage_inf h₁ h₂
  have hP : ⊤ ≤ z ⁻¹ᵁ ((L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂)) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_right h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_right h₂)
  have hM : ⊤ ≤ z ⁻¹ᵁ (M.U p₁ ⊓ M.U p₂) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₂)
  have hle : (L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂) ≤ m ⁻¹ᵁ (L.U j₁ ⊓ L.U j₂) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₁) PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₂) PUnit.unit))
  have hg : (L.pull m).g (fun _ => j₁) (fun _ => j₂) = res hle (pullU m _ (L.g j₁ j₂)) := by
    show ∏ _k : PUnit, (res hle (pullU m _ (L.g j₁ j₂))) ^ (1 : ℤ) = _
    simp
  have hl : valR (z ≫ m) _ (L.g j₁ j₂).val = valR z _ ((L.pull m).g (fun _ => j₁) (fun _ => j₂)).val := by
    rw [hg, valR_comp_app]
    exact (valR_resG z hle hP _).symm
  rw [hl]
  have hle₁ : (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) ⊓ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) ≤ M.U p₁ ⊓ M.U p₂ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have hle₂ : (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) ⊓ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) ≤
      (L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂) :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have e' : res (U := M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) inf_le_left (wg.s (p₁, fun _ => j₁)) =
      res hle₁ (M.g p₁ p₂) * (res hle₂ ((L.pull m).g (fun _ => j₁) (fun _ => j₂)))⁻¹ *
        res (U := M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) inf_le_right (wg.s (p₂, fun _ => j₂)) := e
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq] at e'
  have e2 := congrArg (fun u : Γ(Y, _)ˣ => ev z _ hz u.val) e'
  simp only [Units.val_mul, map_mul] at e2
  rw [← valR_eq_ev, ← valR_eq_ev, ← valR_eq_ev, ← valR_eq_ev] at e2
  exact (congrArg₂ (· * ·) (valR_resG z _ hz _) (valR_resG z _ hz _)).symm.trans
    (e2.trans (congrArg₂ (· * ·) (valR_resG z _ hz _) (valR_resG z _ hz _)))

theorem dlog_transition_iso : ∀ {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M) (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {B : Type} [CommRing B] (x : Sp B ⟶ Y) (w : Sp (DualNumber B) ⟶ Y) (hwx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) (h₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))), (valR w _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val = (valR (w ≫ m) _ (L.g j₁ j₂).val).snd * valR (x ≫ m) _ (L.g j₁ j₂)⁻¹.val + ((valR w _ (wg.s (p₁, fun _ => j₁)).val).snd * valR x _ (wg.s (p₁, fun _ => j₁))⁻¹.val - (valR w _ (wg.s (p₂, fun _ => j₂)).val).snd * valR x _ (wg.s (p₂, fun _ => j₂))⁻¹.val) := by
  intro Y Z m L M wg hwg j₁ j₂ p₁ p₂ B _ x w hwx h₁ h₂
  have hM : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ M.U p₂) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₂)
  have hL : ⊤ ≤ (x ≫ m) ⁻¹ᵁ (L.U j₁ ⊓ L.U j₂) :=
    GlobalTheory.FlagMod.le_preimage_inf
      (GlobalTheory.FlagMod.le_preimage_map m
        (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₁) PUnit.unit)) h₁)
      (GlobalTheory.FlagMod.le_preimage_map m
        (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₂) PUnit.unit)) h₂)
  have hwm : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (w ≫ m) = x ≫ m := by
    rw [← Category.assoc, hwx]
  exact dlog_of_mul_eq _ _ _ _ _ _ _ _
    (valR_iso_compat m L M wg hwg j₁ j₂ p₁ p₂ w (le_preimage_of_red hwx h₁) (le_preimage_of_red hwx h₂))
    (valR_fst_mul_inv hwx h₁ _) (valR_fst_mul_inv hwx h₂ _) (valR_fst_mul_inv hwm hL _) (valR_fst_mul_inv hwx hM _)

end GlobalTheory.CechKS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.morphism_open_affine_line_abelianScheme_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ B.left) (a b : Localization.Away P →ₐ[k] k), u ≫ B.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u = spMap b.toRingHom ≫ u := by
  first | exact @GlobalTheory.NoRatCurve.maps_from_open_line_const | exact GlobalTheory.NoRatCurve.maps_from_open_line_const | (intros; apply GlobalTheory.NoRatCurve.maps_from_open_line_const <;> assumption)
end
