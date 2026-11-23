module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PVerticalGenericDeg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def plToIncr {j m N s : ℕ} (hs : s = j) (hN : j + m = N) (I : PlIdx j m) : PlueckerData.Incr s N :=
  ⟨fun a => Fin.cast hN (I.1.orderEmbOfFin I.2 (Fin.cast hs a)), fun a b hab => by
    rw [Fin.lt_def] at hab ⊢
    simp only [Fin.val_cast]
    exact (I.1.orderEmbOfFin I.2).strictMono (by rw [Fin.lt_def]; simpa using hab)⟩

section Block

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ)

def grFlKappa (hj : 1 ≤ j) (hjN : j ≤ N - 1) : Fin (Fintype.card Ψ) → FlBlock Ψ N :=
  fun t => ((Fintype.equivFin Ψ).symm t, ⟨j - 1, by omega⟩)

def grFlV (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    (Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨grFlKappa Ψ N j hj hjN p.1, plToIncr (by simp only [grFlKappa]; omega) (by omega) p.2⟩

end Block

section Lines

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def linForm (ℓ : Ψ × Fin N → ℤ) : RootPoly Ψ N := ∑ p, (ℓ p : ℚ) • X p

def linDeg (ℓ : Ψ × Fin N → ℤ) : FlBlock Ψ N → ℤ := fun q => ∑ p, ℓ p * xDeg Ψ N p q

def linLine (ℓ : Ψ × Fin N → ℤ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine (FlIdx Ψ N) := fsHerm (ι := FlIdx Ψ N) (linDeg Ψ N ℓ)

variable (j : ℕ)

def muForm : Ψ × Fin N → ℤ := fun p => if (p.2 : ℕ) < j then 0 else 1

abbrev VandPair : Type :=
  {t : Ψ × Fin N × Fin N // t.2.1 < t.2.2 ∧ ((t.2.1 : ℕ) < j ↔ (t.2.2 : ℕ) < j)}

def vandForm (t : VandPair Ψ N j) : Ψ × Fin N → ℤ := fun p =>
  (if p = (t.1.1, t.1.2.1) then 1 else 0) - (if p = (t.1.1, t.1.2.2) then 1 else 0)

def vandCount : ℕ := Fintype.card (VandPair Ψ N j)

def vandLine (i : Fin (vandCount Ψ N j)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine (FlIdx Ψ N) :=
  linLine Ψ N (vandForm Ψ N j ((Fintype.equivFin (VandPair Ψ N j)).symm i))

end Lines

def FlagArithVar.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    IsArithVar (PFl Ψ N) (dimFl Ψ N + 1)

def FlagImageGrass.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N - 1),
    imageZ (grFlV Ψ N j hj hjN) (PFl Ψ N) = grassIdeal (Fintype.card Ψ) j (N - j)

def VandCount.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → dimN Ψ N j + vandCount Ψ N j = dimFl Ψ N

def HFlProdLinear.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N d : ℕ) (c : ℚ)
    (ℓ : Fin d → Ψ × Fin N → ℤ),
    IsIntersectionSystem II → 2 ≤ N → d = dimFl Ψ N + 1 →
    hFl Ψ N II (C c * ∏ i, linForm Ψ N (ℓ i)) =
      (c : ℝ) * II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) d (fun i => linLine Ψ N (ℓ i))

def FsInvPow.Statement : Prop :=
  ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (d : ℕ), IsIntersectionSystem II → IsArithVar P d →
    II K ι P d (fun _ => fsHerm (ι := ι) (fun _ => -1)) = (-1) ^ d * II K ι P d (fun _ => GroundTheory.Heights₂.Heights.fsMulti ι)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.CoordinateConeArithVar

theorem FnFieldTrdeg.full : FnFieldTrdeg.Statement := by
  intro K _ ι _ Ω _ y d hbir harith
  obtain ⟨_, ⟨hprime, _, hrel⟩, hhor, hdim⟩ := harith
  have hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
  have htr := ConeTrdeg.full K ι Ω y hbir hne hhor
  have hA := IntDomainDim.full (MRing ι ⧸ mCoordIdeal y) (algebraMap_injective _ hhor)
  rw [hA, htr] at hdim
  have h1 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat + 1 = ((d + 1 + Fintype.card K : ℕ) : ℕ∞) :=
    WithBot.coe_injective hdim
  rw [map_add (f := _), Cardinal.toENat_nat] at h1
  have h2 : (Algebra.trdeg ℤ Ω).toENat = (d : ℕ∞) := by
    have h3 : (Algebra.trdeg ℤ Ω).toENat + ((Fintype.card K + 1 : ℕ) : ℕ∞) = (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
      push_cast at h1 ⊢
      rw [← add_assoc, h1]; ring
    exact WithTop.add_right_cancel (ENat.coe_ne_top _) h3
  exact Cardinal.toENat_eq_natCast.mp h2

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def DivisorPreimageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (M : CxModel P d) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas),
    IsPtsNull P d {z | M.proj z ∉ R.Yo}

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ModelLogIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (L : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (u : M.Xc → ℝ) (C C' : ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → IsPtsNull P e N → @Measurable M.Xc ℝ (borel M.Xc) _ u →
    (∀ x ∈ R.Yo, |u x| ≤ C + C' * Real.log (R.r x)) →
    (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ R.Yo → g z = u (M.proj z)) →
      IsPtsIntegrable P (fun (_ : Fin e) z => c * Real.log (L.h z)) g

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ProjSmoothAlong.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D) (g : M.Xc → ℝ),
    M.atlas.Smooth g → SmoothAlong (mcPts (mCoordIdeal D.y)) (fun z => g (M.proj z))

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def VertFactorSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ), p ∈ D.S →
    (∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      D.vertFactor p (torusSmul c z) = (∏ k, ‖c k‖ ^ D.vdeg p k) * D.vertFactor p z) ∧
    SmoothAlong (mcPts (mCoordIdeal D.y)) (D.vertFactor p)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.HilbertSamuel

namespace VerticalTwistGenDeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem intNum_snoc_eq_zero {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {n p : ℕ} {b : K → ℤ} {f g : MRing ι}
    (hP : IsArithVar P (n + 1 + 1)) (hp : p.Prime) (hV : IsVerticalDivisorAt P p b f g)
    (L : Fin n → K → ℤ) :
    NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ)))
      (Fin.snoc (α := fun _ => K → ℤ) L b) = 0 := by
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφ
  have hPN : NumbersDVR.IsMultiProjPrime P := (Bridge.isMultiProjPrime_iff P).mpr hP.2.1
  have : P.IsPrime := hPN.isPrime
  have hPh : IsHorizontal P := hP.2.2.1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpP : (C (p : ℤ) : MRing ι) ∉ P := by
    intro h
    have h0 : (p : ℤ) ∈ P.comap (C : ℤ →+* MRing ι) := h
    rw [hPh, Ideal.mem_bot] at h0
    exact hp0 h0
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  have hfN : NumbersDVR.IsMultiHomog f bf := (Bridge.isMultiHomog_iff f bf).mpr hf
  have hgN : NumbersDVR.IsMultiHomog g bg := (Bridge.isMultiHomog_iff g bg).mpr hg

  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_fibre P ‹_› le_rfl hP.2.1.2.2 hpP
  obtain ⟨u', v', e, e', hu', hv', hdeg, hu'P, hv'P, huv'⟩ :=
    NumbersDVR.exists_form_pair hPN.multiHomog le_rfl hfN hgN hV.num_not_mem hV.den_not_mem hu hv huv

  have hkey : ∀ W' : Ideal (MRingOver ℚ ι), W'.IsPrime → P.map φ ≤ W' → NumbersDVR.IsRelevant W' →
      NumbersDVR.divCycle (P.map φ) (φ v') W' = NumbersDVR.divCycle (P.map φ) (φ u') W' := by
    intro W' hW' hle hrel
    have hPle : P ≤ W'.comap φ := fun x hx => hle (Ideal.mem_map_of_mem φ hx)
    have hrel' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (W'.comap φ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel k
      refine ⟨i, fun h => hi ?_⟩
      have h' : φ (X ⟨k, i⟩) ∈ W' := h
      rwa [hφ, map_X] at h'
    have hpW' : (C (p : ℤ) : MRing ι) ∉ W'.comap φ := by
      intro h
      have hu : IsUnit (φ (C (p : ℤ))) := by
        rw [hφ, map_C]
        exact (isUnit_iff_ne_zero.mpr (by simpa using hp0)).map C
      exact hW'.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    obtain ⟨s, t, hs, ht, hst⟩ := hV.unit_off_fibre _ (Ideal.comap_isPrime φ W') hPle hrel' hpW'
    have h1 : g * (s * v' - t * u') ∈ P := by
      have e1 : g * (s * v' - t * u') = u' * (s * f - t * g) - s * (u' * f - v' * g) := by ring
      rw [e1]
      exact P.sub_mem (P.mul_mem_left _ hst) (P.mul_mem_left _ huv')
    have h2 : s * v' - t * u' ∈ P := (‹P.IsPrime›.mem_or_mem h1).resolve_left hV.den_not_mem
    have h3 : φ s * φ v' - φ t * φ u' ∈ P.map φ := by
      rw [← map_mul, ← map_mul, ← map_sub]
      exact Ideal.mem_map_of_mem φ h2
    have hs' : φ s ∉ W' := hs
    have ht' : φ t ∉ W' := ht
    exact NumbersDVR.divCycle_eq_of_mul_sub_mem hs' ht' h3
  have hrat : NumbersDVR.ratDiv (P.map φ) (φ v') (φ u') = 0 := by
    funext W'
    show NumbersDVR.divCycle _ _ W' - NumbersDVR.divCycle _ _ W' = 0
    by_cases h1 : NumbersDVR.divCycle (P.map φ) (φ v') W' = 0
    · by_cases h2 : NumbersDVR.divCycle (P.map φ) (φ u') W' = 0
      · rw [h1, h2, sub_zero]
      · obtain ⟨a1, a2, a3⟩ := NumbersDVR.le_and_isRelevant_of_divCycle_ne_zero h2
        rw [hkey W' a1 a2 a3, sub_self]
    · obtain ⟨a1, a2, a3⟩ := NumbersDVR.le_and_isRelevant_of_divCycle_ne_zero h1
      rw [hkey W' a1 a2 a3, sub_self]

  have hX : IsProjVarF (P.map φ) (n + 1) := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map φ) := (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hv'Q : φ v' ∉ P.map φ := fun h => hv'P ((NineStatements.VerticalGenericDeg.map_mem_map_iff ‹_› hPh v').mp h)
  have hu'Q : φ u' ∉ P.map φ := fun h => hu'P ((NineStatements.VerticalGenericDeg.map_mem_map_iff ‹_› hPh u').mp h)
  have hab : ∀ k, (e' k : ℤ) - e k = b k := by
    intro k
    have h1 : (e' k : ℤ) + bg k = e k + bf k := by exact_mod_cast congrFun hdeg k
    have h2 : (bf k : ℤ) - bg k = b k := congrFun hb k
    rw [← h2]
    linarith
  have hR := NumbersDVR.IntNumRatSection.proof FieldNumbers.CutRational.full ℚ K ι n (P.map φ) hXN hX.2
    L b (φ v') (φ u') e' e (NineStatements.VerticalGenericDeg.isMultiHomog_map hv')
    (NineStatements.VerticalGenericDeg.isMultiHomog_map hu') hv'Q hu'Q hab
  rw [hrat] at hR
  rw [hR]
  simp [NumbersDVR.cycEval]

end VerticalTwistGenDeg

theorem VerticalTwistGenDeg.proof : VerticalTwistGenDeg.Statement := by
  intro K _ ι _ P d a s b f g hP hs
  classical
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφ
  obtain _ | n := d
  · unfold genDeg
    congr 1
    funext i
    exact i.elim0
  have hX : IsProjVarF (P.map φ) (n + 1) := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map φ) := (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hd : FieldNumbers.relDim (P.map φ) = (n + 1 : ℕ) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hX.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  set F := intNumMultilinear (P.map φ) (n + 1) hXN.multiHomog hXN.relevant hd with hF

  have hposition : ∀ p ∈ s, ∀ (bs : Fin (n + 1) → K → ℤ) (i : Fin (n + 1)), bs i = b p → F bs = 0 := by
    intro p hps bs i hi
    obtain ⟨hp, hV⟩ := hs p hps
    have h := FieldNumbers.IntNumSymm.full ℚ K ι (P.map φ) (n + 1) bs (Equiv.swap i (Fin.last n))
    rw [hF, intNumMultilinear_apply, ← h]
    have e1 : bs ∘ Equiv.swap i (Fin.last n) = Fin.snoc (α := fun _ => K → ℤ)
        (fun j => bs (Equiv.swap i (Fin.last n) (Fin.castSucc j))) (b p) := by
      funext j
      induction j using Fin.lastCases with
      | last => simp [hi]
      | cast j => simp
    rw [e1]
    exact VerticalTwistGenDeg.intNum_snoc_eq_zero hP hp hV _

  have hB : ∀ (bs : Fin (n + 1) → K → ℤ) (i : Fin (n + 1)), bs i = ∑ p ∈ s, b p → F bs = 0 := by
    intro bs i hi
    have e2 : bs = Function.update bs i (∑ p ∈ s, b p) := by rw [← hi, Function.update_eq_self]

    rw [e2, ← MultilinearMap.toLinearMap_apply, map_sum]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [MultilinearMap.toLinearMap_apply]
    exact hposition p hp _ i (Function.update_self _ _ _)
  have hg : ∀ c, genDeg P (n + 1) c = F (fun _ => c) := fun c => by
    rw [hF, intNumMultilinear_apply, genDeg]
  rw [hg, hg, show (fun _ : Fin (n + 1) => a + ∑ p ∈ s, b p) =
    (fun _ => a) + (fun _ => ∑ p ∈ s, b p) from rfl, F.map_add_univ,
    Finset.sum_eq_single Finset.univ]
  · rw [Finset.piecewise_univ]
  · intro S _ hS
    obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra h
      exact hS (Finset.eq_univ_iff_forall.2 fun i => not_not.1 (not_exists.1 h i))
    exact hB _ i (by simp [Finset.piecewise, hi])
  · intro h
    exact absurd (Finset.mem_univ _) h

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def genMat0Fr (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) : Matrix (Fin n) (Fin n) (GenFrac F Ψ n) :=
  Matrix.of fun a b => if (a : ℕ) < j ∧ j ≤ (b : ℕ) then 0 else genMatFr F Ψ n τ a b

def flagMinorRatio0 (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (q : Ψ × Σ i : Fin (n - 1), PluckerBlocks n n i) :
    GenFrac F Ψ n :=
  flagMinor (genMat0Fr F Ψ n j q.1) q.2.1 q.2.2 / leadMinor (genMat0Fr F Ψ n j q.1) q.2.1

def HodgeFlagMinorTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n j : ℕ), j ≤ n →
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio0 F Ψ n j))) =
      ((Fintype.card Ψ * (j * (j - 1) / 2 + (n - j) * (n - j - 1) / 2) : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagRatioTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n : ℕ),
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio F Ψ n))) =
      ((Fintype.card Ψ * _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.flagDim n : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def GenLeadMinorNeZero.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) (a : Fin (n - 1)), leadMinor (genMatFr F Ψ n τ) a ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
