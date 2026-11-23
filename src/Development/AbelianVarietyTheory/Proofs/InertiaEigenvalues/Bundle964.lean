module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Mathlib.Data.Multiset.Functor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormula
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle957
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle859
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle822
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle088
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle955
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle958
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle956
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle959
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleThetaValuedMapMemThetaData
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle902
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle789
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.localRankinSelberg_logarithm_formula : (∀ (q : ℕ) (A B : Multiset ℂˣ) (s : ℂ), 1 < q → (∀ α ∈ A, ∀ β ∈ B, ‖(α : ℂ) * (β : ℂ)‖ * (q : ℝ) ^ (-s.re) < 1) → ∃ L : ℂ, HasSum (fun r : ℕ => (A.map fun α => (α : ℂ) ^ (r + 1)).sum * (B.map fun β => (β : ℂ) ^ (r + 1)).sum * (q : ℂ) ^ (-(((r : ℂ) + 1) * s)) / ((r : ℂ) + 1)) L ∧ locL q A B s = Complex.exp L) ∧ (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => ‖((sat σ p.1.1).map fun α => (α : ℂ) ^ (p.2 + 1)).sum * ((sat σ' p.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (p.2 + 1)).sum * (Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * (x : ℂ))) / ((p.2 : ℂ) + 1)‖) ∧ HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (Complex.exp (∑' p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, ((sat σ p.1.1).map fun α => (α : ℂ) ^ (p.2 + 1)).sum * ((sat σ' p.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (p.2 + 1)).sum * (Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * (x : ℂ))) / ((p.2 : ℂ) + 1)))) := by
  first | (exact @GlobalTheory.JSLog.logRankinSelberg) | (exact GlobalTheory.JSLog.logRankinSelberg) | (intros; apply GlobalTheory.JSLog.logRankinSelberg  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)


theorem _root_.GlobalTheory.T.linearIndependent_complex_of_subfield_coeffLattice : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ F : Subfield ℂ, O ≤ F.toSubring →
  ∀ (I : Type) (f : I → Bridge.Gf S → PolF D T.rank S.rank), (∀ a h, f a h ∈ B.coefLat σ emb O h) → LinearIndependent F f → LinearIndependent ℂ f := by
  first | exact @GlobalTheory.PlaceIndep.linearIndependent_complex | exact GlobalTheory.PlaceIndep.linearIndependent_complex | (intros; apply GlobalTheory.PlaceIndep.linearIndependent_complex <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)


theorem _root_.GlobalTheory.T.class_sums_twisted_definite_forms_rational : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (rd : Rd ρ D.nexp i j b) (T : CellTie hρ D.nexp rd), RatTwist hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  ∀ k Q ψ, TwOK i k Q ψ → ClsQ (D := D) Q → ∀ f, ρ.sum i j b k Q ψ (T.rdV k Q ψ f) ∈ Set.range (rdK rd hρ k) := by
  first | exact @GlobalTheory.ClassSumRat.sum_mem_range | exact GlobalTheory.ClassSumRat.sum_mem_range | (intros; apply GlobalTheory.ClassSumRat.sum_mem_range <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.exists_levelPoint_reps_conjugate_half_mod_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') ∧ (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ Y.card = flipIdx V W T m := by
  first | exact @GlobalTheory.FlipReps.flip_reps | exact GlobalTheory.FlipReps.flip_reps | (intros; apply GlobalTheory.FlipReps.flip_reps <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct



namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_intMul_mem_MK {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks]
    [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] [Group G] (Φ : Formalism.IndefR.Arith.FormsL LL Ks WL W G)
    (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK) (x : WL) (hx : x ∈ Φ.WK) :
    ∃ a : 𝓞 Ks, a ≠ 0 ∧ a • x ∈ Φ.MK := by
  first
  | exact @_root_.GlobalTheory.ScalarMultipleMembership.main
  | exact _root_.GlobalTheory.ScalarMultipleMembership.main
  | (apply _root_.GlobalTheory.ScalarMultipleMembership.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ScalarMultipleMembership.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ScalarMultipleMembership.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ScalarMultipleMembership.main ..)

theorem exists_smul_mem_locBall : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j) → (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j hball f
  have hfull := GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j
  have hwk : (YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (Rl.FW j).WK :=
    ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2
  obtain ⟨a, ha, hamk⟩ := exists_intMul_mem_MK (Rl.FW j) hfull.2 _ hwk
  refine ⟨(YS.fi j).eK.symm (a : T0.Q.c.F), ?_, hball _ ?_⟩
  · intro h
    apply ha
    have : ((a : T0.Q.c.F)) = 0 := by
      have := congrArg (YS.fi j).eK h
      simpa using this
    exact_mod_cast this
  · rw [(YS.fi j).mkK]
    have h1 : ((show ↥(S.A ((j : ℕ) + 1)).WK from (YS.fi j).eK.symm (a : T0.Q.c.F) • f)).1 =
        (YS.fi j).eK.symm (a : T0.Q.c.F) • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 := rfl
    rw [h1, ← algebraMap_smul D.what₂.LL, map_smul, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply, algebraMap_smul,
      algebraMap_smul]
    exact hamk

end GlobalTheory.GeoTie
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section



namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BallSup

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem nrm_le_one_of_mem_locBall {f : NX.FmK S ((j : ℕ) + 1)} (hf : f ∈ locBall YS fw iC b j)
    (y : (Rl.FW j).Pt (placeC YS iC b)) :
    (Rl.FW j).nrm (placeC YS iC b) y (fw.e j (cuspOf YS fw j f)) ≤ 1 := by
  rw [fw.nrm_eq, Core.nrmM_le_one_iff]
  obtain ⟨q, hq⟩ := (fw.pt j (placeC YS iC b) y).2
  rcases q with ⟨qv, T, io, e, ho, y', hy', eta, heta, rfl⟩
  obtain ⟨k, hk⟩ := ReadExist.exists_isReading (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io e ho hy'
  obtain ⟨z, hz⟩ := PtC.exists_of_reading hk y' hy'
  have h1 := hf z
  rw [hz _ _ _ (cuspOf_mem_sec YS fw j f)] at h1
  obtain ⟨a, ha⟩ := (hk.int _).1 h1
  rw [← hq]
  change 0 ≤ nval T.V e (evI y' _)
  by_cases hx : evI y' (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)) = 0
  · rw [hx, nval_zero]; exact le_top
  · rw [nval_of_ne hx]
    exact EReal.coe_nonneg.2 (div_nonneg (Int.cast_nonneg
      ((GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff _).1 ⟨a, ha⟩)) (Nat.cast_nonneg _))

theorem one_tmul_mem_Bsup_of_mem_locBall
    (hiC : ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range)
    (f : NX.FmK S ((j : ℕ) + 1)) (hf : f ∈ locBall YS fw iC b j) :
    (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  obtain ⟨s, hs, hsM⟩ := GlobalTheory.supLattice_localisation_of_unitBall D.what₂.LL T0.Q.c.F _ _ _ (Rl.FW j)
    (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).2 (placeC YS iC b) (fw.e j (cuspOf YS fw j f))
    (nrm_le_one_of_mem_locBall YS fw iC b j hf)
  rw [e_cuspOf] at hsM
  set c : S.Ks := (YS.fi j).eK.symm (s : T0.Q.c.F) with hcdef
  have hc : (YS.fi j).e (c • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1) = s • (YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 := by
    rw [← algebraMap_smul D.what₂.LL c, LinearEquiv.map_smul, ← (YS.fi j).eK_LL c, hcdef, RingEquiv.apply_symm_apply,
      algebraMap_smul]
    exact (algebraMap_smul T0.Q.c.F s _)
  have hcM : c • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK := by
    rw [(YS.fi j).mkK, hc]; exact hsM

  have hgen : (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f)) ∈ NX.Bsup S i ((j : ℕ) + 1) b :=
    Submodule.subset_span ⟨c • f, hcM, rfl⟩
  have heK : eKs YS c = (s : T0.Q.c.F) := by
    apply (algebraMap T0.Q.c.F D.what₂.LL).injective
    rw [eKs_LL, ← (YS.fi j).eK_LL c, hcdef, RingEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ : ∃ x : FractionRing (D.ntw.O i), x = NX.ιK S i b c := ⟨_, rfl⟩
  have hn1 : ‖iC x‖ = 1 := by
    rw [hx]
    change ‖embS S iC b c‖ = 1
    rw [← embC_eKs YS iC b, heK]
    refine le_antisymm (norm_int_le_one _ s) (not_lt.1 fun h => hs ?_)
    exact (mem_placeAt _ s).2 h
  have hne : x ≠ 0 := fun h => by
    rw [h, map_zero, norm_zero] at hn1; exact zero_ne_one hn1
  obtain ⟨u, hu⟩ := (hiC x⁻¹).1 (by rw [map_inv₀, norm_inv, hn1, inv_one])
  have key : (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) =
      u • (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f)) := by
    rw [← algebraMap_smul (FractionRing (D.ntw.O i)) u, hu]
    have h1 : (c • (1 : NX.KB S i b)) = (show NX.KB S i b from x) := by
      rw [Algebra.smul_def, mul_one, hx]; rfl
    change (1 : NX.KB S i b) ⊗ₜ[S.Ks] f =
      (show NX.KB S i b from x⁻¹) • ((1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f) : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1))
    rw [← TensorProduct.smul_tmul, h1, TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    exact (inv_mul_cancel₀ hne).symm
  rw [key]
  exact Submodule.smul_mem _ u hgen

end BallSup

theorem one_tmul_mem_Bsup : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC hiC b j f hf
  exact one_tmul_mem_Bsup_of_mem_locBall YS fw iC b j hiC f hf

end GlobalTheory.GeoTie
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair


theorem _root_.GlobalTheory.T.referenceTuple_weilDatum_characters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).1 (R.C.mu0 i) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) := by
  first | exact @GlobalTheory.RefTupleChars.ref_chars | exact GlobalTheory.RefTupleChars.ref_chars | (intros; apply GlobalTheory.RefTupleChars.ref_chars <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair


theorem _root_.GlobalTheory.T.trilinearThetaForm_referenceTuple_invariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), φ ∈ GlobalTheory.RefTheta.Om Ad i hc → ∀ (Fm Fm' : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y y' : ↥X.C), (Fm' : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = NG.rt D.host.E D.R.nV h Fm → (y' : X.A) = X.ρ g y → GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.ThetaTri.valAct1 (GlobalTheory.RefTheta.omStd Ad i (GlobalTheory.RefTheta.t0 Y)) (h, g) φ) Fm' y' = GlobalTheory.RefTheta.lamV Ad i hc φ Fm y := by
  first | exact @GlobalTheory.RefTheta.lamV_inv | exact GlobalTheory.RefTheta.lamV_inv | (intros; apply GlobalTheory.RefTheta.lamV_inv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair


theorem _root_.GlobalTheory.T.referenceTuple_datumForm_reads_thetaLift_innerProducts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1)) (y : D.what₂.Mj (i.1 + 1)) (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)), (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x → inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.RefTheta.phi0 Y i) Fm ⟨X.φ y, X.φ_mem y⟩ := by
  first | exact @GlobalTheory.RefThetaRead.main | exact GlobalTheory.RefThetaRead.main | (intros; apply GlobalTheory.RefThetaRead.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair


theorem _root_.GlobalTheory.T.referenceTuple_forms_smoothAdmissibleUnitaryModule : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), GlobalTheory.RefTheta.IsCanonR Y i rfl X := by
  first | exact @GlobalTheory.RefRowMod.main | exact GlobalTheory.RefRowMod.main | (intros; apply GlobalTheory.RefRowMod.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair


theorem _root_.GlobalTheory.T.referenceTuple_thetaValued_map_mem_thetaData : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO R.ψ (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) (φ v)) → φ ∈ GlobalTheory.RefTheta.Om Ad i hc := by
  first | exact @GlobalTheory.RefTheta.mem_Om_of_theta | exact GlobalTheory.RefTheta.mem_Om_of_theta | (intros; apply GlobalTheory.RefTheta.mem_Om_of_theta <;> assumption)
end

section

namespace GlobalTheory

theorem grothendieckRingPolynomial_outright : GlobalTheory.Published.GrothendieckRingPolynomial :=
  CompanionTheory.Groth.grothendieckRingPolynomial_of_seg CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end
