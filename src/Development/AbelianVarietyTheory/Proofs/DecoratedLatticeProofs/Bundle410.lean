module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle388
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle238
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle365
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle855
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle380
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle377
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle389
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem ratio_total_unitRatio_of_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)) (S : 𝒯 → ℕ → Prop) (s₀ : 𝒯), (∀ s, (t s).Is) → (∀ s, CVEq v (w s)) → (∀ j σ h, v.kap j σ h ≠ 0) → (∀ j, v.cG j ≠ 0) → (∀ s j, j < D.R.m → UnitRatio (S s) ((w s).sc j) ((w s₀).sc j) ∧ UnitRatio (S s) ((t s).cK j) ((t s₀).cK j)) → (∀ s j ρ, j + 2 * ρ + 2 = D.R.m → UnitRatio (S s) ((w s).cT j) ((w s₀).cT j) ∧ UnitRatio (S s) ((w s).cQ j / ((t s).cI j * (t s).cI (j + 1))) ((w s₀).cQ j / ((t s₀).cI j * (t s₀).cI (j + 1)))) → (∀ s, UnitRatio (S s) (t s).cP (t s₀).cP) → ∀ n, 2 * n = D.R.m → ∀ s, (t s).cTop n ≠ 0 ∧ (t s).cBot ≠ 0 ∧ UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
  intro D c v 𝒯 t w S s₀ hIs hCV hkap hcG hscK hTQ hcP n hn s
  obtain ⟨hrefl, hmul, -, hprod⟩ := GlobalTheory.Fam.unitRatio_laws (S s)
  have split : ∀ (f : ℕ → ℂ) (k : ℕ), ∏ j ∈ Finset.range (2 * k), f j =
      ∏ i ∈ Finset.range k, (f (2 * i) * f (2 * i + 1)) := by
    intro f k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
        Finset.prod_range_succ, mul_assoc]
  have hIs' : ∀ s j, j < D.R.m → (t s).cI j ≠ 0 := fun s j hj => (hIs s).cI j hj
  have hκ : ∀ i, i < n → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ s, (t s).cV (2 * i) =
      κ * ((w s).sc (2 * i) * (w s).sc (2 * i + 1)) * (w s).cQ (2 * i) * v.cG (2 * i) * (w s).cT (2 * i) := by
    intro i hi
    by_cases hlast : i + 1 = n
    · refine ⟨1, one_ne_zero, fun s => ?_⟩
      rw [one_mul]
      exact (hCV s).2 (2 * i) (by omega)
    · exact ⟨v.kap (2 * i) (n - i - 2) (by omega), hkap _ _ _, fun s => (hCV s).1 (2 * i) (n - i - 2) (by omega)⟩
  have hB : ∀ i, i < n → UnitRatio (S s)
      ((t s).cV (2 * i) * (t s).cK (2 * i) * (t s).cK (2 * i + 1) / ((t s).cI (2 * i) * (t s).cI (2 * i + 1)))
      ((t s₀).cV (2 * i) * (t s₀).cK (2 * i) * (t s₀).cK (2 * i + 1) / ((t s₀).cI (2 * i) * (t s₀).cI (2 * i + 1))) := by
    intro i hi
    obtain ⟨κ, hκ0, hκs⟩ := hκ i hi
    have hK0 : κ * v.cG (2 * i) ≠ 0 := mul_ne_zero hκ0 (hcG _)
    have hform : ∀ s', (t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) /
        ((t s').cI (2 * i) * (t s').cI (2 * i + 1)) =
        κ * v.cG (2 * i) *
          ((w s').sc (2 * i) * (w s').sc (2 * i + 1) * (w s').cT (2 * i) *
            ((w s').cQ (2 * i) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1))) *
            ((t s').cK (2 * i) * (t s').cK (2 * i + 1))) := by
      intro s'
      rw [hκs s']
      ring
    rw [hform s, hform s₀]
    have hsc1 := (hscK s (2 * i) (by omega)).1
    have hsc2 := (hscK s (2 * i + 1) (by omega)).1
    have homogComponent_comm_first_action := (hscK s (2 * i) (by omega)).2
    have homogComponent_comm_second_action := (hscK s (2 * i + 1) (by omega)).2
    have hcT := (hTQ s (2 * i) (n - i - 1) (by omega)).1
    have hcQ := (hTQ s (2 * i) (n - i - 1) (by omega)).2
    exact (hmul _ _ _ _ (hrefl _ hK0)
      (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ hsc1 hsc2).1 hcT).1 hcQ).1
        (hmul _ _ _ _ homogComponent_comm_first_action homogComponent_comm_second_action).1).1).1
  have hq : ∀ s', (t s').cTop n / (t s').cBot = (∏ i ∈ Finset.range n,
      ((t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1)))) *
      (t s').cP := by
    intro s'
    unfold Tup.cTop Tup.cBot
    rw [← hn, split (fun j => (t s').cI j) n, Finset.prod_div_distrib]
    ring
  have hall : UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
    rw [hq s, hq s₀]
    exact (hmul _ _ _ _ (hprod ℕ (Finset.range n) _ _ fun i hi => hB i (Finset.mem_range.mp hi)) (hcP s)).1
  have hbot : (t s).cBot ≠ 0 := by
    unfold Tup.cBot
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hIs' s j (Finset.mem_range.mp hj)
  have hne := (hmul _ _ _ _ hall hall).2.2
  refine ⟨fun h0 => hne ?_, hbot, hall⟩
  rw [h0, zero_div]

end GlobalTheory.SeeSaw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isRootOfSUnitRatioUpToRootOfUnity_closure_laws : ∀ S : ℕ → Prop, (∀ y : ℂ, y ≠ 0 → UnitRatio S y y) ∧ (∀ x y x' y' : ℂ, UnitRatio S x y → UnitRatio S x' y' → UnitRatio S (x * x') (y * y') ∧ UnitRatio S (x / x') (y / y') ∧ x ≠ 0) ∧ (∀ (x y : ℂ) (n : ℕ), y ≠ 0 → 0 < n → x ^ n = y ^ n → UnitRatio S x y) ∧ ∀ (I : Type) (s : Finset I) (x y : I → ℂ), (∀ i ∈ s, UnitRatio S (x i) (y i)) → UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) := by
  first | exact @GlobalTheory.Fam.unitRatio_laws | exact GlobalTheory.Fam.unitRatio_laws | (intros; apply GlobalTheory.Fam.unitRatio_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.valuation_eq_zero_of_rootOfSUnitRatio : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (S : ℕ → Prop) (x y : ℂ), GlobalTheory.Fam.UnitRatio S x y → (∀ p : ℕ, p.Prime → S p → (p : 𝓞 K) ∉ w.asIdeal) → ∀ a : K, σ a = x / y → Formalism.DivisionValues.vw w a = 0 := by
  first | exact @GlobalTheory.Fam.vw_eq_zero_of_unitRatio | exact GlobalTheory.Fam.vw_eq_zero_of_unitRatio | (intros; apply GlobalTheory.Fam.vw_eq_zero_of_unitRatio <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weilRep_orthogonal_sum_eq_unit_smul_product : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χA χB χT : (AE D)ˣ →* Circle) (omS : Om S T) (omA : Om A T) (omB : Om B T), IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB → ∀ a b h, ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → ∀ u v, omS (o.emb (a, b), h) f ((o.resS T).symm (u, v)) = (c : ℂ) * omA (a, h) (fun u' => omB (b, h) (fun v' => f ((o.resS T).symm (u', v'))) v) u := by
  first | exact @GlobalTheory.WeilSumScalar.omS_eq_smul_prod | exact GlobalTheory.WeilSumScalar.omS_eq_smul_prod | (intros; apply GlobalTheory.WeilSumScalar.omS_eq_smul_prod <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weilRep_commutes_slice_superposition_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resT S).symm (u, k w))) u₀ ∂μ := by
  first | exact @GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target | exact GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target | (intros; apply GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel

namespace GlobalTheory.Core.Mi

variable {D : D7}

structure SBes.FrameAt {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) (μ lam : D.host.E) : Prop where
  ne : μ ≠ 0
  sign : lam = (X.B.g : D.host.E) ∨ lam = -(X.B.g : D.host.E)
  e : B.d.e = GlobalTheory.Core.SBesEx.eM X h μ lam
  e' : B.d.e' = GlobalTheory.Core.SBesEx.e'M X h μ lam
  z : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u)

def SBes.FrameTied {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) : Prop :=
  ∃ μ lam, B.FrameAt μ lam

namespace LatMatch

def NormOneAt (v : GlobalTheory.FinPl.Pl D) (c : AE D) : Prop := c * cA D c = 1 ∧ c - 1 ∈ idAt D (· = v)

def CenAt (S : HSp D) (v : GlobalTheory.FinPl.Pl D) (a : GA D S) : Prop := a ∈ grpAt S (· = v) ∧ a ∈ Subgroup.center (GA D S)

def SMoves (S : HSp D) (c : AE D) (g : GA D S) (L M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV S L (· = v) ↔ c • (Formalism.L2.Theta.mt S g *ᵥ y) ∈ latV S M (· = v))

def LastAt (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S)
    (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ i : Fin ρ, i.1 + 1 = ρ → ∀ s ∈ idAt D (· = v),
    (∀ a : AE D, a ∈ idAt D (· = v) → a • ratV z ∈ latV S₀ M (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) ↔
      ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1

def coreLat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) : Lat S₀ :=
  L.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))

theorem mem_coreLat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (x : Fin S₀.rank → D.host.E) :
    x ∈ coreLat d L ↔ d.i₀ *ᵥ x ∈ L := Iff.rfl

abbrev latS (D : D7) : Lat (D.sp.Y 0) := Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0

abbrev lat0 {u : D.what₂.Word} (F : Formalism.L2.Forms.Forms0 D u) : Lat (D.sp.X 0) :=
  F.cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E
    (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))

def LineAt {S : HSp D} (z : Fin S.rank → D.host.E) (μ : D.host.E) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV z ∈ latV S M (· = v) ↔ incA D μ * a ∈ intAt D (· = v)

def SplitsAt {S A L : HSp D} (o : OrthDec S A L) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV S M (· = v) ↔ o.jA *ᵥ (o.pA *ᵥ y) ∈ latV S M (· = v) ∧ o.jB *ᵥ (o.pB *ᵥ y) ∈ latV S M (· = v))

def TraceAt {S A L : HSp D} (o : OrthDec S A L) (g : GA D A) (N : Lat A) (M : Lat S) (v : GlobalTheory.FinPl.Pl D) : Prop :=
  ∀ y : Fin A.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
    (y ∈ latV A N (· = v) ↔ o.jA *ᵥ (Formalism.L2.Theta.mt A g *ᵥ y) ∈ latV S M (· = v))

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def atW (p : SplitPt D k) {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin m) (Fin n) k :=
  x.map fun a => p.pr (incA D a)

def WShape (p : SplitPt D k) {S S₀ A Ln : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln)
    (ζ : Fin Ln.rank → D.host.E) (L : Lat S) (α α' : Fin ρ → k) (γ : k) (g : GA D A) (N : Lat A) : Prop :=
  ∀ (x x' : Fin ρ → k) (t : k) (y : Fin A.rank → k),
    (fun r => p.sec ((atW p d.e *ᵥ x + atW p d.e' *ᵥ x' + t • (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A g).map p.pr *ᵥ y)) r)) ∈ latV S L (· = p.v) ↔
      (∀ a, α a * x a ∈ 𝒪[k]) ∧ (∀ a, α' a * x' a ∈ 𝒪[k]) ∧ γ * t ∈ 𝒪[k] ∧ (fun r => p.sec (y r)) ∈ latV A N (· = p.v)

def GluedW {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1))
    (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n) : Prop :=
  ∀ x : n ⊕ Fin 1 → k, (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV S M (· = p.v) ↔
    Sum.elim (fun a => x (Sum.inl a)) (fun j => m * x (Sum.inr j)) ∈ GlobalTheory.LatPair.gluedS q 1 P.ker P.vec

end Split

theorem normOneAt_one (v : GlobalTheory.FinPl.Pl D) : NormOneAt v (1 : AE D) := ⟨by simp, by simp⟩

theorem sMoves_one {S : HSp D} (g : GA D S) (L M : Lat S) (v : GlobalTheory.FinPl.Pl D) : SMoves S 1 g L M v ↔ Moves S g L M (· = v) := by
  simp only [SMoves, Moves, one_smul]

end LatMatch

end GlobalTheory.Core.Mi

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.StabMoveTup

theorem unramAt_of_chrEq_mul {D : D7} {c : (AE D)ˣ →* Circle} {χ ξ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c (χ * ξ))
    (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) P) → χ.UnrAt P)
    (hξ : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ¬ ξ.UnrAt P → IsSplitPl D.host P)
    {v ε} (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) : GlobalTheory.WeilParts.UnramAt ε c := by
  refine GlobalTheory.UnramOver.unramAt_of_unrAt D c _ hc v ε hv.1 fun P hP => Formalism.L2.Host.HChar.UnrAt.mul (hu P fun k hk => ?_) ?_
  · obtain ⟨e, he⟩ := GlobalTheory.ChoiceAdm.exists_idem
      (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
    exact GlobalTheory.AdTh.RecPair.under_ne he hv hP
  · by_contra hn
    obtain ⟨e, he⟩ := GlobalTheory.ChoiceAdm.exists_idem (hξ P hn)
    exact GlobalTheory.AdTh.RecPair.under_ne he hv hP

theorem moveT_mul_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ k ∈ GfC _, ∀ k' ∈ GfC _, Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) k (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) k' (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g * k) (h * k') := by
  intro B X I hI hPins l Z ψ θ hψ hθ i hi vac hvac a μ om hchr hW c₀ g h hg hh hM k hk k' hk' mk mk' N N' hN hN' x y hx hy
  have hP := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hPins l Z ψ θ hψ hθ).1 i hi
  have b := StabMove.intG_of_moves _ mk
  have b' := StabMove.intG_of_moves _ mk'
  have a₁ := b.inv hP.gS
  have a₁' := b'.inv hP.gT
  rw [inv_inv] at a₁ a₁'
  have hξ : ∀ P, ¬ (I.xi a).UnrAt P → IsSplitPl B.host P := fun P hn =>
    ((GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host B.fields.K B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1.2.2.2 P hn).1
  obtain ⟨x₁, y₁, rx, ry, e⟩ := StabMove.om_vac hP hW
    (fun v ε hv => unramAt_of_chrEq_mul hchr (I.C.isMu0 ⟨i, hi⟩).unr hξ hv) hvac hk hk' a₁ a₁'
  obtain ⟨x₀, sx⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 g
  obtain ⟨y₀, sy⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 h
  have e0 := hM N N' (StabMove.moves_of_mul _ a₁ b hN) (StabMove.moves_of_mul _ a₁' b' hN') x₀ y₀ sx sy
  have ex := StabMove.root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sx rx) hx
  have ey := StabMove.root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sy ry) hy
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, e, map_smul, ex, ey]
  refine (GlobalTheory.AdForm.VacAll.xiS_smul _ _ _ _ _).trans ?_
  funext z
  have e1 := congrFun e0 z
  rw [e1]
  simp only [map_mul, Circle.coe_mul, Circle.coe_inv, mul_inv]
  ring

end GlobalTheory.AdForm.StabMoveTup
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepLev

theorem comm_inf_fin {D : D7} (V : HSp D) {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  have ha' : finHom V a = 1 := ha
  have hb' : infHom V b = 1 := hb
  have h := GlobalTheory.LevelCut.eq_one_of_parts V (a * b * (b * a)⁻¹)
    (show infHom V _ = 1 by simp [hb']) (show finHom V _ = 1 by simp [ha'])
  exact mul_inv_eq_one.mp h

theorem per_hand_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)}
    {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (g : GA D B.V) (q₁ : GA D J.W) (q₂ k : GA D B'.V)
    (s : ℂ) (hs : s ≠ 0) (hom : s₂.om (1, k) Φ₂ = s⁻¹ • Φ₂) (f f' : GA D B'.V → ℂ) (hf : f' = s • f) :
    B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ (q₂ * k)) f' = B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ q₂) f := by
  have e : ((q₁, q₂ * k) : GA D J.W × GA D B'.V) = (q₁, q₂) * (1, k) := by simp
  have hh := GlobalTheory.HandHom.handFB_smul s₂ vL 1 s⁻¹
  simp only [one_smul, star_one, one_mul] at hh
  unfold Chain.hand
  rw [hf, e, map_mul, Module.End.mul_apply, hom, LinearMap.map_smul, GlobalTheory.HandHom.flatFB_smul, hh, GlobalTheory.HandHom.per_smul,
    inv_mul_cancel₀ hs, one_mul]

theorem rTrans_eigen {G : Type} [Group G] (a b k q : G) (F : G → ℂ) (s : ℂ) (hcm : a * k = k * a)
    (h : rTrans k (rTrans b F) = s • rTrans b F) :
    rTrans (q * k) (rTrans (a * b) F) = s • rTrans q (rTrans (a * b) F) := by
  funext g
  have := congrFun h (g * q * a)
  simp only [rTrans, Pi.smul_apply] at this ⊢
  rw [show g * (q * k) * (a * b) = g * q * a * k * b by
    rw [mul_assoc (g * q) a k, hcm]; simp only [mul_assoc], this]
  simp only [mul_assoc]

theorem vac_comb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (LS : Lat S) (LT : Lat T)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (P Q : Pl D → Prop) (hPQ : ∀ p, Q p → ¬ P p) (e : WO S T →₀ ℂ)
    (he : CombAt Q e) (f : WO S T → ℂ) (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P (comb ψ S T e f) := by
  have h0 : Vac ψ S T LS LT P f := by
    have e : (fun p : Pl D => P p ∨ ¬ P p) = fun _ => True := by
      funext p; exact propext ⟨fun _ => trivial, fun _ => em _⟩
    refine (((GlobalTheory.DisjComb.main D ψ hψ S T P (fun p => ¬ P p) (fun p hp hq => hq hp)).2.2.2.2 LS LT f hS hT).1 ?_).1
    rw [e]; exact hf
  exact ((GlobalTheory.DisjComb.main D ψ hψ S T Q P hPQ).2.1 e he).2 _ _ _ h0



theorem integ_mul_level : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ k ∈ v.JG (j + 1 + 1), ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (q₂ * k) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ _ hΨ₂ φ _ G x a ha f hf k hk q₁ q₂
  have hlt : j + 1 + 1 < D.R.m := by omega
  obtain ⟨s, hs, h1, -, h3⟩ := hF.lawG (j + 1) hlt k hk
  have hom := h1 _ (vac_comb c.ψ hc.std _ _ _ _ (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) hlt) (· ∈ v.gP) (· ∈ w.Q)
    (fun p hp => Finset.disjoint_left.1 hF.disjG hp) _ (hF.atQ (j + 1)).1 Ψ₂ hΨ₂)
  have hkf : k ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ k ((hv.JG _ hlt).1 hk)
  have hr : rTrans (q₂ * k) f = s • rTrans q₂ f := by
    rw [hf]; exact rTrans_eigen a _ k q₂ _ s (comm_inf_fin _ ha hkf) (h3 G x)
  rw [← (ht.sFB j σ h).1] at hom
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (w.ε j α g * ·) (per_hand_mul (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ (φ α) g q₁ q₂ k
    s hs hom _ _ hr)

end GlobalTheory.DStepLev
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStep


open GlobalTheory.NormalFramePeriod in
theorem valK_nEquiv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ Ξ, ∀ g ∈ N Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ (rTrans (Q.gl₂ g) f) = (Q.ψk (simpleSum g) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f := by
  intro D ψ hψ σ S Q c₁ c₂ _ _ φ _ Λ _ Ξ g hg f hf
  have hc : IsContAut S.B'.V f := by
    have := hf.1 1
    rwa [map_one, rTrans_one] at this
  unfold valK
  rw [per_flagN S.B' ψ hψ _ f hc.1 (GlobalTheory.LocGrp.mem_flagN_of_mem_N (ofSplit Q.q) S.B' _ Q.F.F₂ Q.F.G₂ Q.F.bes' (Q.gl₂ g) g hg (Q.loc₂ g)),
    GlobalTheory.LocBesChar.psiBes_isLoc D Q.k (ofSplit Q.q) ψ Q.ψk Q.char σ S.B' _ Q.n₂ (Q.c + 1) Q.F.F₂ Q.F.G₂ Q.F.bes' (Q.gl₂ g) g hg (Q.loc₂ g)]

end GlobalTheory.TriStep
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TriStep

theorem val_eq_tensorVal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ), (∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1) → ∀ Φ₁ Φ₂ (f : GlobalTheory.TriStep.space Q), HasTensorVal (fun Ψ Φ₀ => app (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1) := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁ hU₂ hCL T hT Φ₁ Φ₂ f
  have hcQ : Q.c + 1 + 1 = 2 * (σ + 1) := by have := Q.F.bes.1; omega
  obtain ⟨hψc, hψ1⟩ := GlobalTheory.hasConductor_one_continuous_ne_one Q.k Q.ψk Q.cond
  have hsd : IsSelfDual Q.ψk Q.ν := ((GlobalTheory.SplitWeil.selfDual_measure Q.k Q.ψk hψc hψ1).2.1 Q.cond Q.ν).1 Q.unitVol
  obtain ⟨hcol, hrow, hop, ⟨m, Ψ, Φ₀, hfl⟩, hsum⟩ :=
    GlobalTheory.LocFlat.ContrSum.contr_flat_eq_sum Q.k Q.ψk hψc hψ1 Q.ν hsd Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) hcQ Q.μ₁ Φ₁ Φ₂
  obtain ⟨Ξ, hΞ, hΛΞ⟩ := hCL ⟨_, hcol⟩ ⟨_, hrow⟩
  refine ⟨m, Ψ, Φ₀, hfl, ?_⟩
  have e1 : S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1 = valK S Q c₁ c₂ φ Λ Ξ f.1 := by
    unfold Dbl2.val Dbl2.con valK
    rw [show ((1 : GA D S.B.V), (1 : GA D S.J.W)) = 1 from rfl, show ((1 : GA D S.J.W), (1 : GA D S.B'.V)) = 1 from rfl,
      map_one, map_one, rTrans_one, Module.End.one_apply, Module.End.one_apply, hU₁ Φ₁ ⟨_, hcol⟩ rfl,
      hU₂ Φ₂ ⟨_, hrow⟩ rfl, hΛΞ]
  have e2 : Ξ = ∑ i, GlobalTheory.LocFlat.CFac.prodSB (Ψ i) ⟨_, hop (Φ₀ i)⟩ := by
    apply Subtype.ext
    funext x
    rw [hΞ, hsum m Ψ Φ₀ hfl x]
    simp [Submodule.coe_sum, Finset.sum_apply, GlobalTheory.LocFlat.CFac.prodSB_apply]

  rw [e1, ← hT, e2, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) (Ψ i)) ⟨_, hop (Φ₀ i)⟩
  exact (LinearMap.congr_fun h f).symm

end GlobalTheory.TriStep
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, (∀ PP ∈ c.Pg, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (c.chi (k + 1) PP)⁻¹ ∧ GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (c.chi (k + 1) PP)⁻¹) ∧ GlobalTheory.StepLaw.UnrOff (c.chS (k + 1)) c.Pg ∧ GlobalTheory.StepLaw.UnrOff (c.chT (k + 1)) c.Pg := by
  first | exact @GlobalTheory.ChainOnto.levRes_step | exact GlobalTheory.ChainOnto.levRes_step | (intros; apply GlobalTheory.ChainOnto.levRes_step <;> assumption)
end
