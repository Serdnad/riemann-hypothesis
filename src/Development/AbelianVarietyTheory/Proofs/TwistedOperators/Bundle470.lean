module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle168
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetEigen

theorem heisO_lincomb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) :
    heisO ψ S T y (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • heisO ψ S T y (f i) := by
  funext w
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cosetSum_eigen : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (Λd : AddSubgroup (WO S T)) (R : Finset (WO S T)) (x : WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ Λd, ψ (symplO S T u y) = 1) → (∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) → (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → y = y') → (∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a → ψ (symplO S T x a) = 1) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → ∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → heisO ψ S T y (∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g) = ψ (symplO S T x y) • ∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g := by
  intro D ψ S T ΛS ΛT P e he Λd R x hR h2 h3 h4 g hg y hy hyd
  classical
  have hec : cA D e * cA D (cA D e) = 0 := by rw [cA_cA, mul_comm]; exact he.2
  have half_add : ∀ {a b : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) b → IsHalf (cA D e) (a + b) :=
    fun ha hb i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  have half_neg : ∀ {a : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) (-a) :=
    fun ha i j => by rw [Matrix.neg_apply, mul_neg, ha i j]
  have half_sub : ∀ {a b : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) b → IsHalf (cA D e) (a - b) :=
    fun ha hb => by rw [sub_eq_add_neg]; exact half_add ha (half_neg hb)
  have ann_add : ∀ {a b : WO S T}, (∀ u ∈ Λd, ψ (symplO S T u a) = 1) → (∀ u ∈ Λd, ψ (symplO S T u b) = 1) →
      ∀ u ∈ Λd, ψ (symplO S T u (a + b)) = 1 :=
    fun ha hb u hu => by rw [Formalism.IndefR.Fin.symplO_add_right, AddChar.map_add_eq_mul, ha u hu, hb u hu, one_mul]
  have ann_neg : ∀ {a : WO S T}, (∀ u ∈ Λd, ψ (symplO S T u a) = 1) → ∀ u ∈ Λd, ψ (symplO S T u (-a)) = 1 :=
    fun ha u hu => by rw [Formalism.IndefR.Fin.symplO_neg_right, AddChar.map_neg_eq_inv, ha u hu, inv_one]
  choose! f hfR hfΛ using h2
  have hyz : ∀ z ∈ R, IsHalf (cA D e) (y + z) ∧ ∀ u ∈ Λd, ψ (symplO S T u (y + z)) = 1 := fun z hz =>
    ⟨half_add hy (hR z hz).1, ann_add hyd (hR z hz).2⟩
  have hzy : ∀ z ∈ R, IsHalf (cA D e) (z + -y) ∧ ∀ u ∈ Λd, ψ (symplO S T u (z + -y)) = 1 := fun z hz =>
    ⟨half_add (hR z hz).1 (half_neg hy), ann_add (hR z hz).2 (ann_neg hyd)⟩
  have hfix : ∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a →
      heisO ψ S T a g = g := fun a ha hh =>
    Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac ψ hg he a ha (Or.inr hh)
  have key : ∀ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T y (heisO ψ S T z g) =
      ψ (symplO S T x y) • (ψ (-symplO S T x (f (y + z))) • heisO ψ S T (f (y + z)) g) := by
    intro z hz
    obtain ⟨hh, ha⟩ := hyz z hz
    have hσR := hfR _ hh ha
    have ha0 := hfΛ _ hh ha
    generalize f (y + z) = s at hσR ha0 ⊢
    have hσh := (hR _ hσR).1
    have ha0h : IsHalf (cA D e) (y + z - s) := half_sub hh hσh
    have e1 : heisO ψ S T y (heisO ψ S T z g) = heisO ψ S T s g := by
      rw [← Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_add_of_iso ψ
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.symplOH_half_zero hec hy (hR z hz).1)]
      have hsplit : y + z = s + (y + z - s) := by abel
      rw [hsplit, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_add_of_iso ψ
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.symplOH_half_zero hec hσh ha0h), hfix _ ha0 ha0h]
    have hlin : symplO S T x y + symplO S T x z = symplO S T x s + symplO S T x (y + z - s) := by
      rw [← Formalism.IndefR.Fin.symplO_add_right, ← Formalism.IndefR.Fin.symplO_add_right]
      congr 1; abel
    have hph : -symplO S T x z = symplO S T x y + -symplO S T x s + -symplO S T x (y + z - s) := by
      linear_combination (-1 : AF D.host.F) * hlin
    rw [e1, hph, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv ψ (symplO S T x (y + z - s)),
      h4 _ ha0 ha0h, inv_one, mul_one, smul_smul]
  rw [heisO_lincomb, Finset.sum_congr rfl key, ← Finset.smul_sum]
  congr 1
  refine Finset.sum_nbij' (fun z => f (y + z)) (fun z => f (z + -y)) (fun z hz => hfR _ (hyz z hz).1 (hyz z hz).2)
    (fun z hz => hfR _ (hzy z hz).1 (hzy z hz).2) (fun z hz => ?_) (fun z hz => ?_) (fun z hz => rfl)
  · have hs := hfR _ (hyz z hz).1 (hyz z hz).2
    have h1 := hfΛ _ (hyz z hz).1 (hyz z hz).2
    have h2' := hfΛ _ (hzy _ hs).1 (hzy _ hs).2
    have ht := hfR _ (hzy _ hs).1 (hzy _ hs).2
    have hsum := add_mem h1 h2'
    have heq : y + z - f (y + z) + (f (y + z) + -y - f (f (y + z) + -y)) = z - f (f (y + z) + -y) := by abel
    rw [heq] at hsum
    exact (h3 z hz _ ht hsum).symm
  · have ht := hfR _ (hzy z hz).1 (hzy z hz).2
    have h1 := hfΛ _ (hzy z hz).1 (hzy z hz).2
    have h2' := hfΛ _ (hyz _ ht).1 (hyz _ ht).2
    have hs := hfR _ (hyz _ ht).1 (hyz _ ht).2
    have hsum := add_mem h1 h2'
    have heq : z + -y - f (z + -y) + (y + f (z + -y) - f (y + f (z + -y))) = z - f (y + f (z + -y)) := by abel
    rw [heq] at hsum
    exact (h3 z hz _ hs hsum).symm

end GlobalTheory.CosetEigen
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.IdemHalf

theorem infPart_eq_zero_of_isSplitIdem {D : D7} {e : AE D} (h : IsSplitIdem D e) :
    infPart D e = 0 ∧ infPart D (cA D e) = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -, -⟩, hε⟩ := h
  have hz : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    show infPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  have hs : infPart D e + infPart D (cA D e) = 0 := by rw [← (infPart D).map_add, hε, hz]
  have hm : infPart D e * infPart D (cA D e) = 0 := by rw [← (infPart D).map_mul, h2, (infPart D).map_zero]
  have hi : infPart D e * infPart D e = infPart D e := by rw [← (infPart D).map_mul, h1]
  have hb : infPart D (cA D e) = - infPart D e := eq_neg_of_add_eq_zero_right hs
  rw [hb, mul_neg, hi] at hm
  have ha : infPart D e = 0 := neg_eq_zero.mp hm
  exact ⟨ha, by rw [hb, ha, neg_zero]⟩

theorem halfFin : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ {m n : ℕ} (y : Mx D m n), (IsHalf e y ∨ IsHalf (cA D e) y) → y.map (infPart D) = 0 := by
  intro D P e he m n y hy
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have h0 : infPart D (∑ PP ∈ P, es PP) = 0 := by

    rw [map_sum (infPart D)]
    exact Finset.sum_eq_zero fun PP hPP => (infPart_eq_zero_of_isSplitIdem (hes PP hPP).1).1
  have h1 : infPart D (cA D (∑ PP ∈ P, es PP)) = 0 := by

    rw [map_sum (cA D), map_sum (infPart D)]
    exact Finset.sum_eq_zero fun PP hPP => (infPart_eq_zero_of_isSplitIdem (hes PP hPP).1).2
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rcases hy with hy | hy
  · rw [← hy i j, (infPart D).map_mul, h0, zero_mul]
  · rw [← hy i j, (infPart D).map_mul, h1, zero_mul]

end GlobalTheory.IdemHalf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.IdemOffOrth

theorem symplO_compl_half : ∀ (D : D7) (S T : HSp D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ w x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → symplO S T ((1 - e - cA D e) • w) x = 0 := by
  intro D S T P e he w x hx
  have h1 : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have h2 : e * cA D e = 0 := he.2
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hz : symplO S T (0 : WO S T) x = 0 := by
    have := GlobalTheory.BigDat.symplO_cA_smul S T (0 : AE D) w x
    rw [map_zero, zero_smul, zero_smul, GlobalTheory.BigDat.symplO_zero_right'] at this
    exact this.symm
  rcases hx with hx | hx
  · have hxe : x = cA D (cA D e) • x := by
      rw [GlobalTheory.DualPairCheck.cA_cA]; exact (GlobalTheory.BigDat.smul_of_isHalf hx).symm
    rw [hxe, GlobalTheory.BigDat.symplO_cA_smul, smul_smul]
    have : cA D e * (1 - e - cA D e) = 0 := by linear_combination -c1 - (mul_comm e (cA D e) ▸ h2 : cA D e * e = 0)
    rw [this, zero_smul]; exact hz
  · rw [← GlobalTheory.BigDat.smul_of_isHalf hx, GlobalTheory.BigDat.symplO_cA_smul, smul_smul]
    have : e * (1 - e - cA D e) = 0 := by linear_combination -h1 - h2
    rw [this, zero_smul]; exact hz

end GlobalTheory.IdemOffOrth
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CombTheta

theorem comb_theta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (g : WO S T → ℂ), IsThetaFunO ψ S T g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsThetaFunO ψ S T (∑ z ∈ R, c z • heisO ψ S T (t z) g) ∧ ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ R, c z • heisO ψ S T (t z) g) φ = ∑ z ∈ R, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  classical
  intro D ψ θ S T hψ hθ g hg ι R c t ht
  have ft := GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ g hg
  have hth : ∀ z ∈ R, IsThetaFunO ψ S T (heisO ψ S T (t z) g) := fun z hz => (ft.2 (t z) (ht z hz)).1
  have key : ∀ s ⊆ R, IsThetaFunO ψ S T (∑ z ∈ s, c z • heisO ψ S T (t z) g) ∧
      ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
        (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ),
        pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ s, c z • heisO ψ S T (t z) g) φ =
          ∑ z ∈ s, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ⟨GlobalTheory.OrientedHeis.theta_zero, fun sS BS sT BT φ =>
        GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
    | insert i s hi ih =>
      intro hs
      have hiR : i ∈ R := hs (Finset.mem_insert_self i s)
      have ih' := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
      simp only [Finset.sum_insert hi]
      refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hth i hiR)) ih'.1, fun sS BS sT BT φ => ?_⟩
      rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (c i) (hth i hiR) ih'.1 φ, ih'.2,
        (ft.2 (t i) (ht i hiR)).2 sS BS sT BT φ]
  exact ⟨(key R subset_rfl).1, fun sS BS sT BT φ => (key R subset_rfl).2 sS BS sT BT φ⟩

end GlobalTheory.CombTheta

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockLatVac

theorem infPart_latO_any {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add (f := _), hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem theta_isLatVac_pureTensorO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T LS LT P) g → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) ∧ IsLatVac (heisO ψ S T) (latO S T LS LT P) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  intro D ψ θ S T hψ hθ LS LT P g hg hvac sS BS sT BT φ
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) := fun φ =>
    GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ sS BS sT BT hg φ
  refine ⟨hth φ, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hθ sS sT BS BT g hth (2 • u)
      (infPart_latO_any (AddSubgroup.nsmul_mem _ hu 2)) (hvac.1 u hu) φ
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hθ sS sT BS BT g hth u
      (infPart_latO_any hu) (hvac.2 e he u hu hh) φ

end GlobalTheory.FockLatVac

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeisJointEigen

theorem coeff_zero_of_separated {ι V : Type*} [AddCommGroup V] [Module ℂ V] [DecidableEq ι] (v : ι → V) :
    ∀ R : Finset ι, (∀ z ∈ R, v z ≠ 0) →
      (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ (A : V →ₗ[ℂ] V) (χ : ι → ℂ), (∀ z ∈ R, A (v z) = χ z • v z) ∧ χ y ≠ χ y') →
      ∀ c : ι → ℂ, ∑ z ∈ R, c z • v z = 0 → ∀ z ∈ R, c z = 0 := by
  intro R
  induction R using Finset.induction_on with
  | empty => intro _ _ c _ z hz; simp at hz
  | insert a s ha ih =>
    intro hv hsep c hsum
    have hv' : ∀ z ∈ s, v z ≠ 0 := fun z hz => hv z (Finset.mem_insert_of_mem hz)
    have hsep' : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' →
        ∃ (A : V →ₗ[ℂ] V) (χ : ι → ℂ), (∀ z ∈ s, A (v z) = χ z • v z) ∧ χ y ≠ χ y' := by
      intro y hy y' hy' hne
      obtain ⟨A, χ, hA, hχ⟩ := hsep y (Finset.mem_insert_of_mem hy) y' (Finset.mem_insert_of_mem hy') hne
      exact ⟨A, χ, fun z hz => hA z (Finset.mem_insert_of_mem hz), hχ⟩
    rw [Finset.sum_insert ha] at hsum
    have hs0 : ∀ b ∈ s, c b = 0 := by
      intro b hb
      have hab : b ≠ a := fun h => ha (h ▸ hb)
      obtain ⟨A, χ, hA, hχ⟩ := hsep b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a s) hab
      have key : ∑ z ∈ s, (c z * (χ z - χ a)) • v z =
          A (c a • v a + ∑ z ∈ s, c z • v z) - χ a • (c a • v a + ∑ z ∈ s, c z • v z) := by

        rw [map_add (f := _), map_sum, map_smul, hA a (Finset.mem_insert_self a s), smul_add, Finset.smul_sum,
        add_sub_add_comm, smul_comm (χ a) (c a), sub_self, zero_add, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [map_smul, hA z (Finset.mem_insert_of_mem hz), smul_smul, smul_smul, ← sub_smul]
        congr 1
        ring
      rw [hsum, map_zero, smul_zero, sub_zero] at key
      have h := ih hv' hsep' (fun z => c z * (χ z - χ a)) key b hb
      rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hχ
    have hsum0 : ∑ z ∈ s, c z • v z = 0 := Finset.sum_eq_zero fun z hz => by rw [hs0 z hz, zero_smul]
    rw [hsum0, add_zero] at hsum
    have hca : c a = 0 := (smul_eq_zero.1 hsum).resolve_right (hv a (Finset.mem_insert_self a s))
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hca
    · exact hs0 z hz

theorem sum_heisO_ne_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (R : Finset (WO S T)), (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf e u ∧ ψ (symplO S T u y) ≠ ψ (symplO S T u y')) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → g ≠ 0 → ∀ c : WO S T → ℂ, (∃ z ∈ R, c z ≠ 0) → ∑ z ∈ R, c z • heisO ψ S T z g ≠ 0 := by
  intro D ψ S T ΛS ΛT P e he R hsep g hg hg0 c hc hsum
  obtain ⟨z0, hz0, hcz⟩ := hc
  apply hcz
  classical
  refine coeff_zero_of_separated (fun z => heisO ψ S T z g) R ?_ ?_ c hsum z0 hz0
  · intro z _ h
    apply hg0
    funext w
    have h1 := congrFun h (w - z)
    simp only [heisO, Pi.zero_apply, sub_add_cancel] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (Formalism.IndefR.Fin.psi_ne_zero ψ _)
    · exact h2
  · intro y hy y' hy' hne
    obtain ⟨u, hu, hhalf, hψ⟩ := hsep y hy y' hy' hne
    have hfix : heisO ψ S T u g = g :=
      Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac ψ hg he u hu (Or.inl hhalf)
    refine ⟨Formalism.IndefR.Fin.heisL ψ S T u, fun z => ψ (symplO S T u z), fun z _ => ?_, hψ⟩
    have h1 := congrArg (fun L => L g) (Formalism.IndefR.Fin.heisL_comm ψ S T u z)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Formalism.IndefR.Fin.heisL_apply] at h1
    rw [hfix] at h1
    rw [Formalism.IndefR.Fin.heisL_apply]
    exact h1

end GlobalTheory.HeisJointEigen
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.HeckeLevel

theorem add_mul_sub_one {R : Type} [CommRing R] (m c : ℕ) (w : R) :
    1 + ((m * c : ℕ) : R) * w - 1 = m • ((c : R) * w) := by
  rw [nsmul_eq_mul]
  push_cast
  ring

theorem exists_level : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ∣ N → ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1 := by
  intro D ν hν
  obtain ⟨N₀, hN₀, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν.1
  refine ⟨N₀, hN₀, ?_⟩
  rintro N ⟨c, rfl⟩ u hu ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  have key : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E,
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z : Lev.EAf D) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E → z ∈ intAE D :=
    fun z hz => (GlobalTheory.IdemSupport.mem_intAE_iff z).2 hz
  have hint : ∀ (a : AE D) (v : Lev.EAf D), v ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
      toEAf D a = 1 + ((N₀ * c : ℕ) : Lev.EAf D) * v → finPart D a ∈ intAE D := by
    intro a v hv ha
    refine key _ ?_
    change toEAf D a ∈ _
    rw [ha]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) hv)
  refine hker u ⟨hu, hint _ w hw e, hint _ w' hw' e'⟩
    ⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm ((c : Lev.EAf D) * w), key _ ?_, ?_⟩
  · rw [AlgEquiv.apply_symm_apply]
    exact mul_mem (natCast_mem _ _) hw
  · apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    rw [map_sub, map_one, map_nsmul, AlgEquiv.apply_symm_apply]
    have e2 : (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (u : AE D)) : Lev.EAf D) =
      1 + ((N₀ * c : ℕ) : Lev.EAf D) * w := e
    rw [e2]
    exact add_mul_sub_one N₀ c w

end GlobalTheory.HeckeLevel
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CombFockTranslate

theorem isFockVacAt_comb : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ : D.what₂.Tau) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ J g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  intro D ψ θ S T hψ hθ J τ g hg hv ι R c t ht
  exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ g hg τ J hv ι R t c ht

end GlobalTheory.CombFockTranslate

end
end
