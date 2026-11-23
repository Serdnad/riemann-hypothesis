module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle186
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle221
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle220
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MoveLatticeIsTermSameDatumWithWitnesses
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle187
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle222
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle223
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle047
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle082
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.MeanCov

theorem lintegral_div_inv (κ : ℝ) (hκ : 0 < κ) (w : ℝ → ENNReal) :
    ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) / ENNReal.ofReal t
      = ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  have himg : (fun t : ℝ => κ / t) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact div_pos hκ ht
    · intro hs
      have hs0 : s ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hs)
      refine ⟨κ / s, div_pos hκ hs, ?_⟩
      field_simp
  have hder : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => κ / t) (κ * -(t ^ 2)⁻¹) (Set.Ioi 0) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ht)
    have h1 : HasDerivAt (fun y : ℝ => κ * y⁻¹) (κ * -(t ^ 2)⁻¹) t := (hasDerivAt_inv ht0).const_mul κ
    have h2 : (fun y : ℝ => κ / y) = fun y => κ * y⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
    rw [h2]
    exact h1.hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => κ / t) (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha0 : a ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ha)
    have hb0 : b ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hb)
    have hk0 : κ ≠ 0 := ne_of_gt hκ
    simp only at hab
    field_simp at hab
    nlinarith [hab]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj
    (fun s => w (κ / s) / ENNReal.ofReal s)
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht' : 0 < t := Set.mem_Ioi.mp ht
  have hq : 0 < κ / t := div_pos hκ ht'
  have habs : |κ * -(t ^ 2)⁻¹| = κ / t * t⁻¹ := by
    rw [abs_mul, abs_neg, abs_of_pos hκ, abs_of_pos (by positivity)]
    field_simp
  have hkk : κ / (κ / t) = t := by
    field_simp
  simp only
  rw [habs, hkk, ENNReal.ofReal_mul hq.le, ENNReal.ofReal_inv_of_pos ht', div_eq_mul_inv, div_eq_mul_inv]
  have hne : ENNReal.ofReal (κ / t) ≠ 0 := by simpa using hq
  calc ENNReal.ofReal (κ / t) * (ENNReal.ofReal t)⁻¹ * (w t * (ENNReal.ofReal (κ / t))⁻¹)
      = (ENNReal.ofReal (κ / t) * (ENNReal.ofReal (κ / t))⁻¹) * (w t * (ENNReal.ofReal t)⁻¹) := by ring
    _ = w t * (ENNReal.ofReal t)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top, one_mul]

theorem measurable_detNorm (E : Type) [Field E] [NumberField E] (j : ℕ) :
    Measurable (_root_.GlobalTheory.FlagMeas.detNorm E j) := by
  have hc : Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ =>
      ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2) := by
    refine continuous_finsetProd _ (fun w _ => ?_)
    exact ((Continuous.matrix_det
      (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w)) (continuous_apply w)).norm).pow 2
  exact hc.measurable

theorem ae_detNorm_pos (E : Type) [Field E] [NumberField E] (j : ℕ) (hj : 1 ≤ j) :
    ∀ᵐ g ∂(haarGL E j), 0 < _root_.GlobalTheory.FlagMeas.detNorm E j g := by
  have hm := GlobalTheory.FlagBase.MeanCov.measurable_detNorm E j
  rw [ae_iff]
  have hs : MeasurableSet {g : MatInf E j | ¬ 0 < _root_.GlobalTheory.FlagMeas.detNorm E j g} :=
    (measurableSet_lt measurable_const hm).compl
  have hz : ∀ g ∈ {g : MatInf E j | ¬ 0 < _root_.GlobalTheory.FlagMeas.detNorm E j g},
      ENNReal.ofReal ((_root_.GlobalTheory.FlagMeas.detNorm E j g)⁻¹ ^ j) = 0 := by
    intro g hg
    have hnn : 0 ≤ _root_.GlobalTheory.FlagMeas.detNorm E j g := by
      unfold _root_.GlobalTheory.FlagMeas.detNorm
      exact Finset.prod_nonneg fun w _ => by positivity
    have h0 : _root_.GlobalTheory.FlagMeas.detNorm E j g = 0 := le_antisymm (not_lt.mp hg) hnn
    rw [h0, _root_.inv_zero, zero_pow (by omega), ENNReal.ofReal_zero]
  unfold haarGL
  refine (withDensity_apply _ hs).trans ?_
  refine (setLIntegral_congr_fun hs hz).trans ?_
  simp

private theorem covol_covAt (E : Type) [Field E] [NumberField E] (hE : IsTotallyComplex E)
    (j : ℕ) (hj : 1 ≤ j) (w : ℝ → ENNReal) (hw : Measurable w)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsFullLattice E Λ) :
    covol (autGL E j Λ) ((haarGL E j).withDensity fun g => w (covAt E j (latAt E j Λ g)))
        {g | 0 < _root_.GlobalTheory.FlagMeas.detNorm E j g} =
      slabVol E j Λ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  obtain ⟨κ, hκ, hL⟩ :=
    (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE j).1 Λ hΛ
  have hF : Measurable fun t : ℝ => w (κ / t) := hw.comp (measurable_const.div measurable_id)
  have hd : (haarGL E j).withDensity (fun g => w (covAt E j (latAt E j Λ g)))
      = (haarGL E j).withDensity (fun g => w (κ / _root_.GlobalTheory.FlagMeas.detNorm E j g)) := by
    refine withDensity_congr_ae ?_
    filter_upwards [GlobalTheory.FlagBase.MeanCov.ae_detNorm_pos E j hj] with g hg
    rw [(hL g hg).2.1]
  rw [hd]
  refine (GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq E hE j hj _ hΛ
    (fun t => w (κ / t)) hF).trans ?_
  congr 1
  exact GlobalTheory.FlagBase.MeanCov.lintegral_div_inv κ hκ w

theorem latMean_covAt : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ w : ℝ → ENNReal, Measurable w → latMean E j (fun L => w (covAt E j L)) = glVol E j * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  intro E _ _ hE j hj w hw
  unfold latMean glVol
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun c => ?_
  obtain ⟨Λ, hΛ⟩ := c.out
  exact covol_covAt E hE j hj w hw Λ hΛ

end GlobalTheory.FlagBase.MeanCov
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagSat

theorem mem_of_isSat (I : AutInst) (x : I.GA) {N : Submodule (𝓞 I.E) (Fin I.n → I.E)}
    (hN : Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) N) {y : Fin I.n → I.E}
    (hy : y ∈ lamX I x) (hy' : y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E))) : y ∈ N := by
  set A : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
    lamX I x ⊓ (Submodule.span I.E (N : Set (Fin I.n → I.E))).restrictScalars (𝓞 I.E) with hA
  have hle : N ≤ A := fun z hz => ⟨hN.1 hz, Submodule.subset_span hz⟩
  have hAL : A ≤ lamX I x := inf_le_left
  have e : N = A := by
    by_contra hne
    have h1 := GlobalTheory.PointFlag.rkK_lt _ _ (GlobalTheory.PointFlag.frm_unit I x) (GlobalTheory.PointFlag.fg_of_le I x hAL)
      (GlobalTheory.PointFlag.isSat_of_le _ _ hN hle hAL) hne
    have h2 : Submodule.span I.E (A : Set (Fin I.n → I.E)) ≤ Submodule.span I.E (N : Set (Fin I.n → I.E)) :=
      Submodule.span_le.2 fun z hz => hz.2
    exact absurd h1 (not_lt.2 (Submodule.finrank_mono h2))
  rw [e]
  exact ⟨hy, hy'⟩

theorem exists_isSatFlag : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)) (x : I.GA), x ∈ typeSet I j B → ∃ S, IsSatFlag I (lamX I (1, x.2)) j S ∧ sizesAt I x.2 S x.1 ∈ B := by
  rintro I a j B x ⟨τ, hτ, S, hS, hj⟩
  refine ⟨S, ⟨hS.1, hS.2.1.monotone, hj, fun i y => ?_, ?_⟩, ?_⟩
  · have h := GlobalTheory.PointFlag.flag_sat hS i
    exact ⟨fun hy => ⟨h.1 hy, Submodule.subset_span hy⟩, fun hy => mem_of_isSat I x h hy.1 hy.2⟩
  · rw [hS.2.2.1]
    exact (GlobalTheory.FlagIso.flag_isotropic I x).1
  · have e : sizesAt I x.2 S x.1 = τ := funext fun i => (hS.2.2.2.2.1 i).2.2.2
    rw [e]
    exact hτ

end GlobalTheory.FlagSat
end
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.gap_near_placeParameter_half_noncompactGap : ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r → GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) := by
  first | exact @GlobalTheory.GapNear.gap_near | exact GlobalTheory.GapNear.gap_near | (intros; apply GlobalTheory.GapNear.gap_near <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.majorantLengthTailBound_primed_of_unprimed : ∀ (D : D7) (τ : D.what₂.Tau) (w : D.what₂.Word) (θ : ℝ) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (q : ℕ) (H₁ : ℝ), (∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z W.νS A.Φ q H₁) → ∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z' W.νS' A.Φ' q H₁ := by
  first | exact @GlobalTheory.TypeAsm.tailBd_primed_of_unprimed | exact GlobalTheory.TypeAsm.tailBd_primed_of_unprimed | (intros; apply GlobalTheory.TypeAsm.tailBd_primed_of_unprimed <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_common_sublattice_small_det : ∀ (D : D7) (L M A' A'' B' B'' : LatW D), IsPosDef (D.sp.X 0).hT → L.FG → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L → M ≤ A' → M ≤ A'' → A' ≤ L → A'' ≤ L → B' ≤ A' → B'' ≤ A'' → rkW D B' = rkW D A' → rkW D B'' = rkW D A'' → ∃ P : LatW D, P ≤ M ∧ P ≤ B' ∧ P ≤ B'' ∧ rkW D P = rkW D M ∧ detW D P ≤ detW D M * (idxW D A' B' : ℝ) * (idxW D A'' B'' : ℝ) := by
  first | exact @GlobalTheory.LoopC.CommonSub.main | exact GlobalTheory.LoopC.CommonSub.main | (intros; apply GlobalTheory.LoopC.CommonSub.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianTermCount_frameClass_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (j : ℕ), (S.nT d C fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  first | exact @GlobalTheory.HL.TermCount.nT_cardI_le | exact GlobalTheory.HL.TermCount.nT_cardI_le | (intros; apply GlobalTheory.HL.TermCount.nT_cardI_le <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.move_lattice_isTerm_same_datum_with_witnesses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∃ n₀ ∈ S.N, ∃ n₀' ∈ S.N', ∃ n'' ∈ S.N', (∀ v, n₀ v = eich L S.Hm x u s v) ∧ (∀ v, n₀⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v, n₀' v = eich L S.Hm x' u s v) ∧ (∀ v ∈ perp L S.Hm S.X', n'' v = v) ∧ ((n₀⁻¹ • Λ : Submodule L.O S.V) : Set S.V) = S.moved Λ x u s ∧ S.IsTermW d (n₀⁻¹ • Λ) (n₀⁻¹ * (S.wit d Λ).1) (n'' * n₀' * (S.wit d Λ).2) := by
  first | exact @GlobalTheory.HL.MoveWit.main | exact GlobalTheory.HL.MoveWit.main | (intros; apply GlobalTheory.HL.MoveWit.main <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem IsChoice.eq_of_mem {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (h : IsChoice I g Pl w) {k k' : Fin 2}
    (u : HeightOneSpectrum (𝓞 I.E)) (h1 : ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal) (h2 : ((g k' : ℕ) : 𝓞 I.E) ∈ u.asIdeal) :
    k = k' := by
  by_contra hkk
  have hg : g k ≠ g k' := by
    intro e
    apply hkk
    fin_cases k <;> fin_cases k'
    · rfl
    · exact absurd e h.2.1
    · exact absurd e.symm h.2.1
    · rfl
  obtain ⟨a, b, hab⟩ : IsCoprime (g k : ℤ) (g k') :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (h.1 k) (h.1 k')).mpr hg)
  have e : (a : 𝓞 I.E) * ((g k : ℕ) : 𝓞 I.E) + (b : 𝓞 I.E) * ((g k' : ℕ) : 𝓞 I.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 I.E) hab
    push_cast at this
    exact this
  apply u.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem IsChoice.ne_of_ne {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (h : IsChoice I g Pl w) {a b : Σ k, Pl k} (hab : b ≠ a) :
    w b.1 b.2 ≠ w a.1 a.2 ∧ ¬ IsConj I (w a.1 a.2) (w b.1 b.2) := by
  obtain ⟨ka, va⟩ := a
  obtain ⟨kb, vb⟩ := b
  dsimp only
  have hmem := h.2.2.2.1
  by_cases hk : kb = ka
  · subst hk
    have hv : vb ≠ va := fun e => hab (by rw [e])
    exact ⟨fun e => hv (h.2.2.2.2.1 kb e), h.2.2.2.2.2.1 kb va vb⟩
  · refine ⟨fun e => hk (h.eq_of_mem (w kb vb) (hmem kb vb).1 (by rw [e]; exact (hmem ka va).1)), fun hcj => hk ?_⟩
    have hx := (hcj ((g ka : ℕ) : 𝓞 I.E) ((g ka : ℕ) : 𝓞 I.E) (by simp)).mp (hmem ka va).1
    exact (h.eq_of_mem (w kb vb) hx (hmem kb vb).1).symm

theorem PlFrame.actsAs_one_of_mem {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
    {x : I.Gf} (hx : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I w.asIdeal • I.Lf) : fr.ActsAs x 1 := by
  intro y h
  rw [Matrix.one_mulVec, ← sub_eq_zero, ← map_sub]
  refine (fr.c_ker _).mpr ?_
  have e : ((⟨_, h⟩ - y : I.Lf) : Fin I.n → _) = (I.fmat x - 1) *ᵥ (y : Fin I.n → _) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Submodule.coe_sub]
  rw [e]
  exact hx _ y.2

private theorem val_eq_lemma {I : AutInst} {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} {fr : ∀ k v, PlFrame I N (g k) (w k v)}
    {ρ : I.Gf → GProd N g Pl} (hρ : ActsBy fr ρ) {x : I.Gf} (hx : x ∈ I.Kset) (kv : Σ k, Pl k)
    {M : GL (Fin N) (ZMod (g kv.1))} (hM : (fr kv.1 kv.2).ActsAs x (M : Matrix (Fin N) (Fin N) (ZMod (g kv.1)))) :
    ρ x kv = M :=
  Units.ext (PlFrame.ActsAs.unique (fr kv.1 kv.2) hx (hρ x hx kv.1 kv.2) hM)

theorem exists_red_actsBy : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)) [∀ k, Finite (Pl k)],
    I.n = N → IsChoice I g Pl w → ∃ ρ : Red I (g 0 * g 1) (GProd N g Pl), ActsBy fr ρ.toFun := by
  intro I N g Pl w fr _ hn hc
  classical
  obtain ⟨ρ, hρ, hmul⟩ := exists_actsBy fr
  have hK1 : (1 : I.Gf) ∈ I.Kset := (Inhab.mem_Ksub I 1).mp (Inhab.Ksub I).one_mem
  have hKmul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, x * y ∈ I.Kset := fun x hx y hy =>
    (Inhab.mem_Ksub I _).mp
      ((Inhab.Ksub I).mul_mem ((Inhab.mem_Ksub I x).mpr hx) ((Inhab.mem_Ksub I y).mpr hy))
  have hone : ∀ x ∈ I.Kset, ∀ kv : (Σ k, Pl k), (fr kv.1 kv.2).ActsAs x 1 → ρ x kv = 1 :=
    fun x hx kv h => val_eq_lemma hρ hx kv (M := 1) (by rw [Units.val_one]; exact h)
  have : Fintype (Σ k, Pl k) := Fintype.ofFinite _
  refine ⟨⟨ρ, hmul, fun x hx => ?_, fun q => ?_⟩, hρ⟩
  · rw [← GlobalTheory.T.trivial_mod_chosen_primes_iff_mem_Kg I N g Pl w fr hn hc x hx]
    constructor
    · intro h1 k v y h
      rw [hρ x hx k v y h, h1]
      simp
    · intro h
      funext kv
      exact hone x hx kv (fun y hy => by rw [h kv.1 kv.2 y hy, Matrix.one_mulVec])
  · have key : ∀ s : Finset (Σ k, Pl k), ∃ x ∈ I.Kset, ρ x = fun kv => if kv ∈ s then q kv else 1 := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · exact ⟨1, hK1, funext fun kv => by simpa using hone 1 hK1 kv (fr kv.1 kv.2).actsAs_one⟩
      · intro a s ha ih
        obtain ⟨xs, hxs, es⟩ := ih
        obtain ⟨xa, hxa, hact, hoth⟩ := GlobalTheory.T.exists_mem_Kset_acts_as_GL_mod_splitPrime I N (g a.1) (w a.1 a.2) (fr a.1 a.2) hn (hc.1 a.1)
          (hc.2.2.2.1 a.1 a.2).2 (hc.2.2.2.2.2.1 a.1 a.2 a.2) (q a)
        refine ⟨xa * xs, hKmul xa hxa xs hxs, ?_⟩
        rw [hmul xa hxa xs hxs, es]
        funext kv
        by_cases hk : kv = a
        · rw [hk, Pi.mul_apply, val_eq_lemma hρ hxa a hact]
          simp [ha]
        · have hne := IsChoice.ne_of_ne hc hk
          rw [Pi.mul_apply, hone xa hxa kv (PlFrame.actsAs_one_of_mem _ (hoth _ hne.1 hne.2))]
          simp [hk]
    obtain ⟨x, hx, e⟩ := key Finset.univ
    exact ⟨x, hx, by rw [e]; simp⟩

end GlobalTheory.RowLev
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.reproducing_formula_fixedVector_moderateGrowth : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) (C : ℝ), T y = y → IsContRep B y f → (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) → (∃ Φ : B.I.GA → ℝ, Integrable Φ (B.I.muA B.μf) ∧ ∀ x g, ‖phe B d g * f (x * g)‖ ≤ (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g) ∧ ∀ x, f x = ∫ g, phe B d g * f (x * g) ∂(B.I.muA B.μf) := by
  first | exact @GlobalTheory.ReproducingFixed.reproducing_fixed | exact GlobalTheory.ReproducingFixed.reproducing_fixed | (intros; apply GlobalTheory.ReproducingFixed.reproducing_fixed <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.truncatedLeastLatticeSize_bounded_below_unipotentRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (x : I.GA), I.IsIsot W → ∃ c : ℝ, 0 < c ∧ ∀ m ∈ I.NA W, c ≤ tau1 I (m * x) := by
  first | exact @GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot | exact GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot | (intros; apply GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot <;> assumption)
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.canonicalLatticeFlag_isotropic_selfDual : ∀ (I : AutInst) (x : I.GA), (∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2), Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) ∧ (∀ v, rkK (stepLt I x (1 / 2)) ≤ rkR (I.ε v)) ∧ ∀ R : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → ∀ y ∈ Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)), (∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ y' ∈ perpIn I x R, y - y' ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := by
  first | exact @GlobalTheory.FlagIso.flag_isotropic | exact GlobalTheory.FlagIso.flag_isotropic | (intros; apply GlobalTheory.FlagIso.flag_isotropic <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem isUnimod_GG : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  intro k r μ hμ
  obtain ⟨hG, h⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hM, hR⟩ := h μ hμ
  refine ⟨fun s hs => hR s hs, ?_⟩
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf measurable_invM]
  exact GlobalTheory.HaarInversion.lintegral_inv_eq _ (GG k r) μ hG hM hR f hf

end GlobalTheory.SgInf
end
