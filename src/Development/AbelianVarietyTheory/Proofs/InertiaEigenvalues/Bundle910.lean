module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle859
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle897
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarMemCoefficientRingAuxiliaryLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProduc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle895
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle115
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle892
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle535
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle901
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivMapLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

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


theorem _root_.GlobalTheory.T.flipScalar_primePow_integral_at_levelPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)), ∃ c : ℕ, ∀ (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT M₀ x → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → Odd M₀ → Nat.Coprime M₀ (GlobalTheory.Tow.badN D) → (l : ℂ) ^ c * flipScal χW V W T M₀ x ∈ O := by
  first | exact @GlobalTheory.LevelSeries.flipScal_pow_mem | exact GlobalTheory.LevelSeries.flipScal_pow_mem | (intros; apply GlobalTheory.LevelSeries.flipScal_pow_mem <;> assumption)
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


theorem _root_.GlobalTheory.T.flipScalar_mem_coefficientRing_auxiliaryLevel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l pd : ℕ), ChiData χW χ M₀ → l.Prime → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime pd (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT pd x → flipScal χW V W T pd x ∈ O := by
  first | exact @GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit | exact GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit | (intros; apply GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.JSW
open scoped ENNReal

theorem _root_.GlobalTheory.T.hasProd_localRankinSelbergFactor_self_of_eulerProduct : ∀ (I : Type) (q : I → ℕ) (n : ℕ) (α : I → Fin n → ℂˣ), (∀ w, 2 ≤ q w) →
    (∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤) →
    (∀ x : ℝ, 1 < x →
      HasProd (fun w => locL (q w) (Finset.univ.val.map (α w))
          ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ))
        (((GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) ∧
      1 ≤ (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) ∧
    ContinuousOn (fun x => (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) (Set.Ioi 1) := by
  first | exact @GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL | exact GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL | (intros; apply GlobalTheory.RSPole.EulerPole.eulD_hasProd_locL <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.RSnmEul

open GlobalTheory.ZEul GlobalTheory.RSnmUnf

def padInt {m n : ℕ} (_h : m ≤ n) (v : Fin m → ℤ) : Fin n → ℤ :=
  fun i => if hi : (i : ℕ) < m then v ⟨i, hi⟩ else 0

theorem padInt_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (padInt h) := by
  intro v w hvw
  funext j
  have := congrFun hvw ⟨j, lt_of_lt_of_le j.2 h⟩
  simpa [padInt, j.2] using this

theorem padInt_zero {m n : ℕ} (h : m ≤ n) : padInt h (0 : Fin m → ℤ) = 0 := by
  funext i; simp only [padInt, Pi.zero_apply]; split_ifs <;> rfl

theorem padInt_valid {m n : ℕ} (h : m ≤ n) {v : Fin m → ℤ} (hv : (∀ i, 0 ≤ v i) ∧ Antitone v) :
    (∀ i, 0 ≤ padInt h v i) ∧ Antitone (padInt h v) := by
  have hnn : ∀ i, 0 ≤ padInt h v i := by
    intro i; unfold padInt; split_ifs
    · exact hv.1 _
    · exact le_rfl
  refine ⟨hnn, fun a b hab => ?_⟩
  by_cases hb : (b : ℕ) < m
  · have ha : (a : ℕ) < m := lt_of_le_of_lt hab hb
    simp only [padInt, ha, hb, dite_true]
    exact hv.2 (show (⟨a, ha⟩ : Fin m) ≤ ⟨b, hb⟩ from hab)
  · have : padInt h v b = 0 := by simp [padInt, hb]
    rw [this]; exact hnn a

theorem toNat_padInt {m n : ℕ} (h : m ≤ n) (v : Fin m → ℤ) :
    (fun i => (padInt h v i).toNat) = padNat (n := n) (fun i => (v i).toNat) := by
  funext i; simp only [padInt, padNat]; split_ifs <;> simp

theorem sum_padNat {m n : ℕ} (h : m ≤ n) (l : Fin m → ℕ) : ∑ i, padNat (n := n) l i = ∑ i, l i := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro c hc
    have : ¬ (c : ℕ) < m := fun hcm => hc ⟨⟨c, hcm⟩, Fin.ext rfl⟩
    simp [padNat, this]
  · intro i; simp [padNat, i.2]

theorem norm_rsTermNM_le (q : ℕ) (hq : 0 < q) {m n : ℕ} (h : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ)
    (v : Fin m → ℤ) :
    ‖rsTermNM q α β x v‖ ≤ (sqTerm q α x (padInt h v) + sqTerm q β x v) / 2 := by
  by_cases hv : (∀ i, 0 ≤ v i) ∧ Antitone v
  · rw [rsTermNM, if_pos hv, sqTerm, if_pos (padInt_valid h hv), sqTerm, if_pos hv, toNat_padInt h v,
      sum_padNat h, norm_mul, norm_mul, Complex.norm_conj, norm_cpow_pow q hq]
    have hw : 0 ≤ (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [mul_nonneg (sq_nonneg (‖schurAt (padNat (n := n) fun i => (v i).toNat) α‖ -
      ‖schurAt (fun i => (v i).toNat) β‖)) hw]
  · rw [rsTermNM, if_neg hv, norm_zero]
    exact div_nonneg (add_nonneg (sqTerm_nonneg _ _ _ _) (sqTerm_nonneg _ _ _ _)) zero_le_two

theorem rsTermNM_zero (q : ℕ) {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) : rsTermNM q α β x 0 = 1 := by
  have h : (fun _ : Fin m => (0 : ℕ)) = fun i => ((0 : Fin m → ℤ) i).toNat := by funext i; simp
  have hs : schurAt (padNat (n := n) fun i => ((0 : Fin m → ℤ) i).toNat) α = 1 := by
    rw [← h]
    have : (padNat (n := n) fun _ : Fin m => (0 : ℕ)) = fun _ => 0 := padNat_zero
    rw [this, schurAt, schur_zero]; simp
  have hs' : schurAt (fun i => ((0 : Fin m → ℤ) i).toNat) β = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  rw [rsTermNM, if_pos ⟨fun i => le_rfl, antitone_const⟩, hs, hs']
  simp

theorem rsTermNM_partVec (q : ℕ) {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ)
    (l : {l : Fin m → ℕ // Antitone l}) :
    rsTermNM q α β x (partVec l) =
      schurAt (padNat (n := n) l.1) α * conj (schurAt l.1 β) * ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) := by
  rw [rsTermNM, if_pos (partVec_valid l)]
  simp [partVec]

end GlobalTheory.RSnmEul

namespace GlobalTheory.RSnmEul

open GlobalTheory.ZEul GlobalTheory.RSnmUnf

theorem hasSum_rsTermNM_local (q : ℕ) {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (x : ℝ)
    (hs : Summable fun v : Fin m → ℤ => ‖rsTermNM q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v‖) :
    HasSum (fun v => rsTermNM q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v)
      (locL q (Finset.univ.val.map α) ((Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom))
        (x : ℂ)) := by
  set β' : Fin m → ℂˣ := fun j => Units.map (starRingEnd ℂ).toMonoidHom (β j) with hβ'
  have hconj : ∀ l : Fin m → ℕ, schurAt l (fun j => (β' j : ℂ)) = conj (schurAt l fun j => (β j : ℂ)) := by
    intro l
    rw [schurAt, schurAt, MvPolynomial.eval₂_comp_left, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ))
      (Int.castRingHom ℂ)]
    rfl
  have hpad : ∀ l : Fin m → ℕ, padTo hmn l = padNat (n := n) l := fun l => rfl
  have hm : (Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom) = Finset.univ.val.map β' :=
    Multiset.map_map _ _ _
  rw [hm]
  have hs' : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β' j : ℂ))‖ *
        ‖(q : ℂ) ^ (-(x : ℂ))‖ ^ (∑ i, l.1 i) := by
    refine (hs.comp_injective partVec_injective).congr fun l => ?_
    simp only [Function.comp, rsTermNM_partVec, hpad, hconj, norm_mul, norm_pow, Complex.norm_conj]
  have hc := cauchy_locL hmn α β' q (x : ℂ) hs'
  rw [← (partVec_injective (n := m)).hasSum_iff]
  · convert hc using 1
    funext l
    simp only [Function.comp, rsTermNM_partVec, hpad, hconj]
  · intro v hv
    by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
    · exact absurd (mem_range_partVec hval) hv
    · rw [rsTermNM, if_neg hval]

theorem euler_rsTermNM : ∀ {I : Type} (q : I → ℕ) {n m : ℕ}, m ≤ n → ∀ (α : I → Fin n → ℂˣ) (β : I → Fin m → ℂˣ) (x : ℝ), 1 < x →
    (∀ i, 2 ≤ q i) → GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    ∃ P : ℂ, HasProd (fun i => GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i))
        ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P ∧
      HasSum (fun l : I →₀ (Fin m → ℤ) => l.prod fun i v =>
        GlobalTheory.RSnmUnf.rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v) P := by
  intro I q n m hmn α β x _ hq hα hβ
  set f : I → (Fin m → ℤ) → ℂ := fun i v => rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v
    with hfdef
  have hf0 : ∀ i, f i 0 = 1 := fun i => rsTermNM_zero _ _ _ _
  have hA := summable_sqTerm q (fun i j => (α i j : ℂ)) x hα
  have hB := summable_sqTerm q (fun i j => (β i j : ℂ)) x hβ
  have hinj : Function.Injective fun p : I × {v : Fin m → ℤ // v ≠ 0} =>
      ((p.1, ⟨padInt hmn p.2.1, fun h0 => p.2.2 (padInt_injective hmn (h0.trans (padInt_zero hmn).symm))⟩) :
        I × {v : Fin n → ℤ // v ≠ 0}) := by
    intro p p' hp
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hp
    exact Prod.ext hp.1 (Subtype.ext (padInt_injective hmn hp.2))
  have hA' := hA.comp_injective hinj
  have hsum : Summable fun p : I × {v : Fin m → ℤ // v ≠ 0} => ‖f p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by
        simpa only [hfdef, Function.comp_apply] using norm_rsTermNM_le (q p.1) (by have := hq p.1; omega) hmn
          (fun j => (α p.1 j : ℂ)) (fun j => (β p.1 j : ℂ)) x p.2.1) ((hA'.add hB).div_const 2)
  obtain ⟨hN, hP, -⟩ := GlobalTheory.EulerSum.euler_product_intVec m f hf0 hsum
  have hloc : ∀ i, ∑' v, f i v = locL (q i) (Finset.univ.val.map (α i))
      ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) :=
    fun i => (hasSum_rsTermNM_local (q i) hmn (α i) (β i) x (GlobalTheory.EulerSum.summable_norm_local f hsum i)).tsum_eq
  refine ⟨∑' l : I →₀ (Fin m → ℤ), l.prod f, ?_, hN.of_norm.hasSum⟩
  simpa only [hloc] using hP

end GlobalTheory.RSnmEul
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatConj

open MvPolynomial GlobalTheory.SeriesTie.Scale

variable {D : D7} {n : ℕ}

def polLat {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule O (VV ℂ lam) :=
  Submodule.span O {y | ∃ F ∈ nabAtr emb lam M, y = GlobalTheory.CoefModel.mapVV σ lam F}

theorem coefLatFn_eq {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K))
    (O : Subring ℂ) (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    coefLatFn σ emb O lam M = (polLat σ emb O lam M).map ((coefLin lam).restrictScalars O) := by
  unfold coefLatFn polLat
  rw [Submodule.map_span]
  congr 1
  ext φ
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, ⟨F, hF, rfl⟩, coefFn_map σ lam _⟩
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F, hF, coefFn_map σ lam _⟩

theorem polLat_conj {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)}
    {O O' : Subring ℂ} {lam : D.what₂.Tau → DomWeight n} {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (τ : ℂ ≃+* ℂ)
    (hτ : ∀ a : K, τ (σ a) = σ a) (hO : ∀ a ∈ O, τ a ∈ O') {y : VV ℂ lam} (hy : y ∈ polLat σ emb O lam M) :
    GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y ∈ polLat σ emb O' lam M := by
  induction hy using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hF, rfl⟩ := h
    refine Submodule.subset_span ⟨F, hF, Subtype.ext ?_⟩
    change MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map σ F.1) = MvPolynomial.map σ F.1
    rw [MvPolynomial.map_map, show (τ : ℂ →+* ℂ).comp σ = σ from RingHom.ext hτ]
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul a y _ h1 =>
    have e : GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam (a • y) = (⟨τ a, hO a a.2⟩ : O') • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y := by
      rw [Subring.smul_def, Subring.smul_def, map_smulₛₗ]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ h1

theorem mapVV_symm_mapVV (lam : D.what₂.Tau → DomWeight n) (τ : ℂ ≃+* ℂ) (y : VV ℂ lam) :
    GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) lam (GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) lam y) = y := by
  refine Subtype.ext ?_
  change MvPolynomial.map (τ.symm : ℂ →+* ℂ) (MvPolynomial.map (τ : ℂ →+* ℂ) y.1) = y.1
  rw [MvPolynomial.map_map]
  have : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := RingHom.ext fun a => τ.symm_apply_apply a
  rw [this, MvPolynomial.map_id]

section Base

variable {i : Fin D.R.m} {B : Base (Vc D i) (Wc D i)}

theorem pq_le (hB : B.Good) (τ : D.what₂.Tau) : B.w.p τ + B.w.q τ ≤ (Wc D i).rank := by
  obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
  rw [← hB.sig τ] at e
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum] at this
  omega

variable (Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) {κ : ℂ}

theorem mem_coefLat_iff (hlam : B.w.lam = lamV D i) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (h : Bridge.Gf (Vc D i)) (x : VsV D i ℂ) :
    Φ x ∈ B.coefLat σ emb O h ↔ κ • x ∈ polLat σ emb O (lamV D i) (B.latAt h) := by
  show Φ x ∈ harmLat σ emb O _ B.w B.F.BS (B.latAt h) ↔ _
  rw [mem_harmLat, hlam, coefLatFn_eq, Submodule.mem_map]
  constructor
  · rintro ⟨-, y, hy, he⟩
    have e : coefLin (lamV D i) y = coefLin (lamV D i) (κ • x) := by
      rw [map_smul]
      exact he.trans (hκ x)
    exact coefLin_injective _ e ▸ hy
  · intro hx
    refine ⟨hval x, κ • x, hx, ?_⟩
    change coefLin (lamV D i) (κ • x) = _
    rw [map_smul, hκ]
    rfl

theorem existsUnique_eq (hB : B.Good) (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) :
    ∀ P ∈ B.valSpace, ∃! x : VsV D i ℂ, P = Φ x := by
  intro P hP
  have h1 : harmFn (Wc D i).rank B.w B.F.BS P ∈ (harm (Wc D i).rank B.w B.F.BS).map (harmFn (Wc D i).rank B.w B.F.BS) :=
    Submodule.mem_map_of_mem hP
  rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt (pq_le hB), hlam] at h1
  have hs : Submodule.span ℂ {φ | ∃ F : VV ℂ (lamV D i), φ = coefFn (RingHom.id ℂ) (lamV D i) (F : Pol ℂ D.what₂.Tau (Vc D i).rank)}
      ≤ LinearMap.range (coefLin (lamV D i)) :=
    Submodule.span_le.2 (by rintro _ ⟨F, rfl⟩; exact ⟨F, rfl⟩)
  obtain ⟨y, hy⟩ := hs h1
  have hy' : coefLin (lamV D i) y = harmFn (Wc D i).rank B.w B.F.BS P := hy
  have hv : ∀ x, harmFn (Wc D i).rank B.w B.F.BS (Φ x) = κ • coefLin (lamV D i) x := hκ
  refine ⟨κ⁻¹ • y, ?_, fun x hx => ?_⟩
  · have e : harmFn (Wc D i).rank B.w B.F.BS (Φ (κ⁻¹ • y) - P) = 0 := by
      rw [map_sub, hv, map_smul, smul_smul, mul_inv_cancel₀ hκ0, one_smul, hy', sub_self]
    exact (sub_eq_zero.1 (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt (pq_le hB) _ (sub_mem (hval _) hP) e)).symm
  · refine coefLin_injective (lamV D i) ?_
    have e := hv x
    rw [← hx, ← hy'] at e
    rw [map_smul, e, smul_smul, inv_mul_cancel₀ hκ0, one_smul]

theorem conj_mem_iff (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (τ : ℂ ≃+* ℂ) (hτ : ∀ a : K, τ (σ a) = σ a) (h : Bridge.Gf (Vc D i)) {x x' : VsV D i ℂ} (hx : ConjVec i τ x x') :
    Φ x ∈ B.coefLat σ emb O h ↔ Φ ((τ κ / κ) • x') ∈ B.coefLat σ emb (O.map (τ : ℂ →+* ℂ)) h := by
  rw [mem_coefLat_iff Φ hlam hval hκ, mem_coefLat_iff Φ hlam hval hκ]
  have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext hx
  have e : κ • ((τ κ / κ) • x') = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) (κ • x) := by
    rw [smul_smul, mul_div_cancel₀ _ hκ0, map_smulₛₗ, hx']
    rfl
  rw [e]
  constructor
  · exact polLat_conj τ hτ fun a ha => Subring.mem_map.2 ⟨a, ha, rfl⟩
  · intro h'
    have hτ' : ∀ a : K, τ.symm (σ a) = σ a := fun a => by rw [τ.symm_apply_eq, hτ]
    have := polLat_conj τ.symm hτ' (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 ha
      simpa using hb) h'
    rwa [mapVV_symm_mapVV] at this

theorem coefLat_eq_span (hB : B.Good) (hlam : B.w.lam = lamV D i) (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    (h : Bridge.Gf (Vc D i)) :
    B.coefLat σ emb O h = Submodule.span O
      {P | ∃ F ∈ nabAtr emb (lamV D i) (B.latAt h), P = Φ (κ⁻¹ • GlobalTheory.CoefModel.mapVV σ (lamV D i) F)} := by
  let Ψ : VsV D i ℂ →ₗ[O] PolF D (Wc D i).rank (Vc D i).rank := (Φ ∘ₗ (κ⁻¹ • LinearMap.id)).restrictScalars O
  have hΨ : ∀ y, Ψ y = Φ (κ⁻¹ • y) := fun _ => rfl
  have e : B.coefLat σ emb O h = (polLat σ emb O (lamV D i) (B.latAt h)).map Ψ := by
    ext P
    constructor
    · intro hP
      obtain ⟨x, rfl, -⟩ := existsUnique_eq Φ hB hlam hκ0 hval hκ P (Submodule.mem_inf.1 hP).1
      refine ⟨κ • x, (mem_coefLat_iff Φ hlam hval hκ σ emb O h x).1 hP, ?_⟩
      rw [hΨ, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
    · rintro ⟨y, hy, rfl⟩
      rw [hΨ, mem_coefLat_iff Φ hlam hval hκ, smul_smul, mul_inv_cancel₀ hκ0, one_smul]
      exact hy
  rw [e, polLat, Submodule.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F, hF, rfl⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨_, ⟨F, hF, rfl⟩, rfl⟩

end Base

end GlobalTheory.CoefLatConj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.hasDerivAt_fockVectors_targetLie_realPlace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (τ : D.what₂.Tau), ∃ κ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ → ℂ, ∀ Y ∈ lieAt (Wc D i) τ, ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (z : WO (Vc D i) (Wc D i)), HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) ((R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹) P + κ Y • P) z) 0 := by
  first | exact @GlobalTheory.FockLieW.hasDerivAt_fockVector | exact GlobalTheory.FockLieW.hasDerivAt_fockVector | (intros; apply GlobalTheory.FockLieW.hasDerivAt_fockVector <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.polynomial_mem_span_lifted_maps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (P : PolF D (Wc D i).rank (Vc D i).rank), ∃ Q ∈ Submodule.span ℂ {Q : PolF D (Wc D i).rank (Vc D i).rank | ∃ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : (R.cV i).W), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) ∧ Q = φ w}, ∃ E : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank), FiniteDimensional ℂ E ∧ (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → P₂ ∈ E) ∧ (∀ φ : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ, (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → ∀ l, φ P₂ l = φ P₁ (l ∘ₗ (R.cV i).ρ u)) → ∀ P₁ ∈ E, φ P₁ = 0) ∧ P - Q ∈ E := by
  first | exact @GlobalTheory.FockIsotypic.decomp | exact GlobalTheory.FockIsotypic.decomp | (intros; apply GlobalTheory.FockIsotypic.decomp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem exists_basisOf_of_classSum :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.admT4 D.nexp E → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∃ S, BasisOf D.nexp i j b (SgJ D.nexp E i j b) S :=
  fun D E h i hi j hj b =>
    GlobalTheory.TwistChoice.exists_basisOf D.nexp i j b _ (GlobalTheory.TwistChoice.th_fg D.nexp E h i hi j hj b)

end GlobalTheory.TwInputs
end
