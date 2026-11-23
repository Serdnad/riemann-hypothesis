module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimates
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermsSameDoubleCosetSameDatum
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle282
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle271
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle270
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle246
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle036
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle276
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle258
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle179
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFrameSecondFactorReversedDualBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceFirstFactorLocalFrame
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLiftEmbeddedDatumOfTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeMiddleLayerEichlerLe
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle286
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernelWeight

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.KernelWeight.hf_add_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (a + b) y =
      _root_.GlobalTheory.HL.hf L Hm a y + _root_.GlobalTheory.HL.hf L Hm b y := by
  have h := _root_.GlobalTheory.HL.DualInter.sub_l L Hm (a + b) b y
  rw [add_sub_cancel_right] at h
  linear_combination -h

open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.KernelWeight.hf_smul_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (c • a) y = c * _root_.GlobalTheory.HL.hf L Hm a y :=
  _root_.GlobalTheory.HL.DualInter.smul_l L Hm c a y

def hfLin (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := hf_add_left L Hm a b y
  map_smul' c a := hf_smul_left L Hm c a y

theorem exists_coord {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ al : Fin (r + 1) → E, x = ∑ i, al i • n (g i) ∧ al j.castSucc = S.h x (gs j) := by
  apply GlobalTheory.HL.MoveTotal.exists_coords <;> assumption

end

theorem kernel_weight : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ‖∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d Λ hT hF
  have hW := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).2.1
  have hom : ‖S.om d Λ‖ = 1 := (GlobalTheory.T.term_invariants_independent_of_witnesses L r k S d Λ _ _ hW).2.2.2.2
  have hchi : ∀ b u, ‖S.chiM j d Λ b u‖ = 1 := fun b u =>
    (GlobalTheory.FramePsi.psi_unitary_character L r k S).2.2.2 _

  have hmove : ∀ w, S.Mv (j + 1) d Λ w → ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ S.IsTerm d Λ₁ ∧
      S.om d Λ₁ = S.om d Λ * S.chiM j d Λ w.1 w.2.1 := by
    intro w hw
    obtain ⟨Λ₁, h1, h2, -, -, h5⟩ := GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character L r k S j β βJ d Λ hT hF _ _ _ _ hw
    refine ⟨Λ₁, ⟨hw, h1⟩, h2, ?_⟩
    obtain ⟨al, hal, hal1⟩ := exists_coord S S.f S.es S.dual _ hW.2.2.1 j _ hw.1
    obtain ⟨al', hal', hal1'⟩ := exists_coord S S.f' S.es' S.dual' _ hW.2.2.2.1 j _ hw.2.1
    rw [h5 al al' hal hal', hal1, hal1']
    rfl
  have huniq : ∀ w Λ₁ Λ₂, S.MvTo (j + 1) d Λ Λ₁ w → S.MvTo (j + 1) d Λ Λ₂ w → Λ₁ = Λ₂ :=
    fun w Λ₁ Λ₂ h1 h2 => SetLike.coe_injective (h1.2.trans h2.2.symm)
  let P : Submodule L.O S.V → Prop := fun y => S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y
  let G : S.MW → ℂ := fun w => if ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ then
    S.om d Λ * S.chiM j d Λ w.1 w.2.1 else 0
  obtain ⟨hGn, hGs⟩ := (GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split L r k S j β βJ d Λ hT hF).2.2.2.2 P (S.om d) G
    (by
      intro w Λ₁ hw
      by_cases hP : P Λ₁
      · obtain ⟨Λ₂, h1, -, h3⟩ := hmove w hw.1
        rw [if_pos hP, huniq w Λ₁ Λ₂ hw h1, h3]
        exact if_pos ⟨Λ₁, hw, hP⟩
      · rw [if_neg hP]
        refine if_neg ?_
        rintro ⟨Λ₂, h1, h2⟩
        exact hP (huniq w Λ₂ Λ₁ h1 hw ▸ h2))
    (by
      intro w hw
      refine if_neg ?_
      rintro ⟨Λ₂, h1, -⟩
      exact hw h1.1)
  obtain ⟨-, hLn, hHn, -, hLb, hHb⟩ := GlobalTheory.T.hermitianMoves_total_measure_estimates L r k S hk j β βJ d Λ hT hF
  obtain ⟨hadd, hsm, -, -⟩ := GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound (S.refA (j + 1) Λ)
  set H : S.MW → ℂ := fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1 with hH
  obtain ⟨hn2, hc2⟩ := hsm (-S.om d Λ) H hHn
  obtain ⟨hn3, hc3, -⟩ := hadd G _ hGn hn2
  have hb := (hadd _ _ hn3 hLn).2.2 (by
    intro w
    simp only [Pi.add_apply, hH, ind, G]
    by_cases hw : S.Mv (j + 1) d Λ w
    · by_cases hex : ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁
      · rw [if_pos hex, if_pos hw]
        split_ifs <;> simp
      · have hl : ¬ S.NoLeak Λ w.2.1 := by
          intro hl
          obtain ⟨Λ₁, h1, h2, -⟩ := hmove w hw
          exact hex ⟨Λ₁, h1, h2, GlobalTheory.T.hermitianDoubleCoset_inFamily_moved_of_not_leak L r k S j β βJ d Λ hT hF _ _ _ _ hw hl Λ₁ h1.2⟩
        rw [if_neg hex, if_pos hw, if_pos ⟨hw, hl⟩]
        simp [hom, hchi]
    · have hex : ¬ ∃ Λ₁, S.MvTo (j + 1) d Λ Λ₁ w ∧ P Λ₁ := by
        rintro ⟨Λ₂, h1, -⟩
        exact hw h1.1
      rw [if_neg hex, if_neg hw, if_neg (fun h => hw h.1)]
      simp)
  rw [hc3, hc2] at hb
  have hcK : 0 ≤ S.cK β βJ := by
    unfold Frames.cK
    positivity
  have hG : ‖cint (S.refA (j + 1) Λ) G‖ ≤
      (cint (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1)).re +
        ‖cint (S.refA (j + 1) Λ) H‖ := by
    have e : cint (S.refA (j + 1) Λ) G =
        (cint (S.refA (j + 1) Λ) G + -S.om d Λ * cint (S.refA (j + 1) Λ) H) +
          S.om d Λ * cint (S.refA (j + 1) Λ) H := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add hb ?_)
    rw [norm_mul, hom, one_mul]
  have := mul_le_mul_of_nonneg_left hG hcK
  show ‖∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * S.om d y‖ ≤ _
  rw [hGs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcK]
  linarith

end GlobalTheory.HL.KernelWeight
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.exists_smooth_average_lowest_KType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  first | exact @GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf | exact GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf | (intros; apply GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.FixedConj

def adeleEquiv (D : Formalism.BasicNotions.D7) (hF : D.host.F = maximalRealSubfield D.host.E) :
    ReciprocityTheory.Aut.AL D.host.E ≃+* Formalism.IndefR.Lev.EAf D :=
  (GlobalTheory.StdFrame.tensCastR hF).symm.trans
    (Algebra.TensorProduct.comm (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ↥D.host.F) D.host.E).toRingEquiv

def primeComap {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (ι : E ≃+* E')
    (w : HeightOneSpectrum (𝓞 E')) : HeightOneSpectrum (𝓞 E) where
  asIdeal := Ideal.comap (RingOfIntegers.mapRingEquiv ι) w.asIdeal
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := congrArg (Ideal.map (RingOfIntegers.mapRingEquiv ι)) h
    rwa [Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv ι).surjective, Ideal.map_bot] at this

end GlobalTheory.FixedConj

end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.localTerms_same_doubleCoset_same_datum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (t₁ t₂ : Term V M r), H.IsTerm t₁ → H.IsTerm t₂ → t₂.abelian₂ = t₁.abelian₂ → t₂.T = t₁.T → t₂.T' = t₁.T' → ∀ n ∈ NU H t₁.f, ∀ m ∈ NU H t₁.f', img (n * m) t₁.abelian₂ = t₁.abelian₂ → Tri E t₁.f t₂.f → Tri E (fun b => (n * m) (t₁.f' b)) t₂.f' → (M.split ≠ none → ∀ x' ∈ t₁.abelian₂, ∀ x ∈ t₁.abelian₂, x' ∈ H.perp (H.X t₁.f') → x ∈ H.perp (H.X t₁.f) → (Cong H t₁.abelian₂ t₁.f t₁.f' (x - x') ↔ Cong H t₁.abelian₂ t₂.f t₂.f' (x - (n * m) x'))) → ∀ d : Datum P, Over P d t₁ → Over P d t₂ := by
  first | exact @GlobalTheory.LocOver.SameDC.same_datum | exact GlobalTheory.LocOver.SameDC.same_datum | (intros; apply GlobalTheory.LocOver.SameDC.same_datum <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDoubleCoset_kernel_row_sum_near_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → |(∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, S.kern β (j + 1) βJ d Λ y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  first | exact @GlobalTheory.HL.kern_row_sum | exact GlobalTheory.HL.kern_row_sum | (intros; apply GlobalTheory.HL.kern_row_sum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.localSpanOfLatticeAtPlace_eq_for_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → {v : HeightOneSpectrum (𝓞 F) | loc v L ≠ loc v M}.Finite := by
  first | exact @GlobalTheory.St.G.loc_eq_almost_all | exact GlobalTheory.St.G.loc_eq_almost_all | (intros; apply GlobalTheory.St.G.loc_eq_almost_all <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem tidx_arith {ι : Type} (s : Finset ι) (r : ι → ℕ) (T f : ℕ) (hT : T.Prime) (hcard : s.card = f)
    (hdvd : ∏ i ∈ s, r i ∣ T ^ (2 * f)) (hlow : ∀ i ∈ s, r i ≠ 0 → T ^ 2 ≤ r i) : ∀ i ∈ s, r i = T ^ 2 := by
  have hT0 : 0 < T := hT.pos
  have hpow0 : T ^ (2 * f) ≠ 0 := pow_ne_zero _ hT.ne_zero

  have hprod0 : ∏ i ∈ s, r i ≠ 0 := by
    intro h
    rw [h] at hdvd
    exact hpow0 (zero_dvd_iff.mp hdvd)
  have hge : ∀ i ∈ s, T ^ 2 ≤ r i := fun i hi =>
    hlow i hi (fun h => hprod0 (Finset.prod_eq_zero hi h))

  have hle : ∏ i ∈ s, r i ≤ ∏ _i ∈ s, T ^ 2 := by
    rw [Finset.prod_const, hcard, ← pow_mul]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hpow0) hdvd
  intro i hi
  by_contra hne
  have hlt : ∏ _i ∈ s, T ^ 2 < ∏ i ∈ s, r i :=
    Finset.prod_lt_prod₀ (fun j _ => pow_pos hT0 2) hge ⟨i, hi, lt_of_le_of_ne (hge i hi) (Ne.symm hne)⟩
  exact absurd hle (not_le.mpr hlt)

theorem tLat_local_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup = T ^ 2 ∧ ∃ d ∈ loc v (dualL cm.sig J L), ∀ x ∈ loc v (dualL cm.sig J L), ∃ a ∈ intV E v, x - a • d ∈ loc v L := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT hs hdeg hL v hv
  obtain ⟨hncard, hloc⟩ := GlobalTheory.St.G.SplitPrime.split_place F E cm T hT hs

  have hF : Module.finrank ℚ F = f := by
    have h := Module.finrank_mul_finrank ℚ F E
    rw [cm.deg2, hdeg] at h
    omega
  have hfin : {w : HeightOneSpectrum (𝓞 F) | (T : 𝓞 F) ∈ w.asIdeal}.Finite :=
    Set.finite_of_ncard_pos (by rw [hncard]; exact Module.finrank_pos)
  have hcard : hfin.toFinset.card = f := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, hncard, hF]

  have hlow : ∀ w ∈ hfin.toFinset,
      (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup ≠ 0 →
      T ^ 2 ≤ (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup := by
    intro w hw h0
    have hw' : (T : 𝓞 F) ∈ w.asIdeal := (Set.Finite.mem_toFinset hfin).mp hw
    obtain ⟨_, _, sp, hsp1, hsp2⟩ := hloc w hw'
    exact GlobalTheory.T.prime_sq_le_local_hermitian_dual_index F E cm n J hJ hdet T f L hT hs hdeg hL w hw' sp hsp1 hsp2
      (GlobalTheory.T.split_place_dual_quotient_components_iff F E cm n J hJ hdet T f L hT hs hdeg hL w hw' sp hsp1 hsp2) h0

  have hdvd := GlobalTheory.T.prod_local_relIndex_dvd_hermitian_dual F E cm n J hJ hdet T f L hT hs hdeg hL hfin.toFinset
    (fun w hw => (Set.Finite.mem_toFinset hfin).mp hw)
  rw [hL.2.2.2.1] at hdvd
  have heq := tidx_arith hfin.toFinset
    (fun w => (loc w L).toAddSubgroup.relIndex (loc w (dualL cm.sig J L)).toAddSubgroup)
    T f hT hcard hdvd hlow v ((Set.Finite.mem_toFinset hfin).mpr hv)
  refine ⟨heq, ?_⟩
  obtain ⟨_, _, sp, hsp1, hsp2⟩ := hloc v hv
  exact GlobalTheory.T.local_hermitian_dual_quotient_cyclic_split_place F E cm n J hJ hdet T f L hT hs hdeg hL v hv sp hsp1 hsp2
    (GlobalTheory.T.split_place_dual_quotient_components_iff F E cm n J hJ hdet T f L hT hs hdeg hL v hv sp hsp1 hsp2) heq

end GlobalTheory.St.G
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.localFrame_secondFactor_reversedDualBasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (0, 1) → ∀ (b bd : Fin n → Fin n → E ⊗[F] v.adicCompletion F), (∀ i, b i ∈ loc v L) → (∀ i, bd i ∈ loc v L) → (∀ i, b i = e • b i) → (∀ i, bd i = sigR cm.sig (v.adicCompletion F) e • bd i) → (∀ i j, ∃ s ∈ intV E v, hR cm.sig J (v.adicCompletion F) (bd i) (b j) - (if i = j then e else 0) = (g : E ⊗[F] v.adicCompletion F) * s) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range b ∪ Set.range bd) y) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ c, (sp (y c)).1 = x c) ↔ ∀ c, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) ∧ ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1)) = lamJ ψ (fun _ => 1) n t 0 n (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  first | exact @GlobalTheory.St.G.local_frame_second_factor | exact GlobalTheory.St.G.local_frame_second_factor | (intros; apply GlobalTheory.St.G.local_frame_second_factor <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.splitPlace_firstFactor_localFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (1, 0) → ∀ (b bd : Fin n → Fin n → E ⊗[F] v.adicCompletion F), (∀ i, b i ∈ loc v L) → (∀ i, bd i ∈ loc v L) → (∀ i, b i = e • b i) → (∀ i, bd i = sigR cm.sig (v.adicCompletion F) e • bd i) → (∀ i j, ∃ s ∈ intV E v, hR cm.sig J (v.adicCompletion F) (bd i) (b j) - (if i = j then e else 0) = (g : E ⊗[F] v.adicCompletion F) * s) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range b ∪ Set.range bd) y) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ c, (sp (y c)).1 = x c) ↔ ∀ c, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) ∧ ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1)) = lamJ ψ (fun _ => 1) n t 0 n (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  first | exact @GlobalTheory.St.G.FirstFactorFrame.local_frame_first_factor | exact GlobalTheory.St.G.FirstFactorFrame.local_frame_first_factor | (intros; apply GlobalTheory.St.G.FirstFactorFrame.local_frame_first_factor <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.definiteLift_embedded_datum_of_term : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ H' : HermSpace K N.Wt, (∀ x y, H'.B x y = H.B x y) ∧ GlobalTheory.Mass.PD H'.B.flip ∧ GlobalTheory.Mass.IsIntLat H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) ∧ (GlobalTheory.Mass.discN H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) : ℝ) = N.NT ^ 2 ∧ GenBy (Formalism.HermitianLatticesTheory.dual H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ))) (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) 1 ∧ IsDat H' g (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) N.j (N.gI g Λ) (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F' N.F Λ), (iotaGraph N.F N.F' Λ (g : 𝓞 K)).comap ((N.Wt.subtype.prodMap N.Wt.subtype).restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.DegCnt.ToLift.main | exact GlobalTheory.DegCnt.ToLift.main | (intros; apply GlobalTheory.DegCnt.ToLift.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.haarInvVolume_middleLayer_eichler_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.Split Λ → GlobalTheory.HL.invVol ((N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.R1) ⊔ N.ZI) ((N.Gam Λ ⊓ N.R1) ⊔ N.ZI) ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) := by
  first | exact @GlobalTheory.DegCnt.MidLayer.invVol_mid_layer_le | exact GlobalTheory.DegCnt.MidLayer.invVol_mid_layer_le | (intros; apply GlobalTheory.DegCnt.MidLayer.invVol_mid_layer_le <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DerEx


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothOnG_comb {n : ℕ} {ε : Fin n → Bool} {f g : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hg : SmoothOnG ε g) : SmoothOnG ε (fun x => c * f x + g x) := by
  intro x hx
  obtain ⟨U, F, hU, hxU, hF, hFf⟩ := hf x hx
  obtain ⟨U', G, hU', hxU', hG, hGg⟩ := hg x hx
  refine ⟨U ∩ U', fun y => c * F y + G y, hU.inter hU', ⟨hxU, hxU'⟩,
    (contDiffOn_const.mul (hF.mono Set.inter_subset_left)).add (hG.mono Set.inter_subset_right), ?_⟩
  intro y hy hyJ
  simp only [hFf y hy.1 hyJ, hGg y hy.2 hyJ]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothOnG_zero {n : ℕ} (ε : Fin n → Bool) : SmoothOnG ε (fun _ => 0) := fun _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem exists_isDer_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsDer ε σ V E ∧ lowKSub ε lam σ ≤ V := by
  intro n ε lam H _ _ _ σ hσ hK
  let S : Set H := {v | ∃ (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), SmoothOnG ε α ∧
    HasCompactSupport (fun g : UJ ε => α (umat g)) ∧
    ∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ}
  have hder : ∀ v ∈ Submodule.span ℂ S, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X →
      ∃ v' ∈ Submodule.span ℂ S,
        HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
    intro v hv X hX
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      obtain ⟨β, v', k1, k2, k3, k4⟩ :=
        (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).2 X hX
      exact ⟨v', Submodule.subset_span ⟨β, s, k1, k2, k3⟩, k4⟩
    | zero => exact ⟨0, zero_mem _, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', hda⟩ := ha
      obtain ⟨b', hb', hdb⟩ := hb
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      simp only [map_add (f := _)]
      exact hda.add hdb
    | smul c a _ ha =>
      obtain ⟨a', ha', hda⟩ := ha
      refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
      simp only [map_smul]
      exact hda.const_smul c
  have hzero := smoothOnG_zero ε
  have hsm : ∀ v ∈ Submodule.span ℂ S, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ) := by
    intro v hv y
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨α, s, h1, h2, h3⟩ := hv
      exact (GlobalTheory.GardingStep.garding_step n ε H σ α s v hσ h1 h2 h3).1 y
    | zero => simpa using hzero
    | add a b _ _ ha hb => simpa [inner_add_right] using smoothOnG_comb 1 ha hb
    | smul c a _ ha => simpa [inner_smul_right] using smoothOnG_comb c ha hzero
  obtain ⟨E, hE⟩ := GlobalTheory.DerOf.exists_isDer n ε H σ (Submodule.span ℂ S) hσ hder hsm
  obtain ⟨α, h1, h2, h3⟩ := GlobalTheory.exists_smooth_fix_lowKSub n ε lam H σ hσ hK
  exact ⟨_, E, hE, fun s hs => Submodule.subset_span ⟨α, s, h1, h2, h3 s hs⟩⟩

end GlobalTheory.DerEx
end
