module

public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle834
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle318
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

namespace GlobalTheory.TanVec

theorem exists_coords_derivs {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) :
    ∃ (x : Fin D → A) (d : Fin D → A →+ A),
      (∀ c a b, d c (a * b) = a * d c b + b * d c a) ∧
      ∀ a c, d c (x a) = if a = c then 1 else 0 := by
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  let B := P.basisKaehler.reindex e
  have hB : ∀ i, KaehlerDifferential.D k A (P.val (e.symm i)) = B i := fun i => by
    simp [B]
  refine ⟨fun i => P.val (e.symm i), fun c =>
    { toFun := fun s => B.coord c (KaehlerDifferential.D k A s)
      map_zero' := by simp
      map_add' := fun s t => by simp }, fun c a b => ?_, fun a c => ?_⟩
  · change B.coord c (KaehlerDifferential.D k A (a * b)) =
      a * B.coord c (KaehlerDifferential.D k A b) + b * B.coord c (KaehlerDifferential.D k A a)
    rw [Derivation.leibniz, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · change B.coord c (KaehlerDifferential.D k A (P.val (e.symm a))) = _
    rw [hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

def jetHom {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (d : A →+ A)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a) : A →+* DualNumber K where
  toFun s := (φ s, φ (d s))
  map_one' := by
    have h1 : d 1 = 0 := by
      have := hd 1 1
      simpa using this
    refine TrivSqZeroExt.ext (map_one φ) ?_
    change φ (d 1) = 0
    rw [h1, map_zero]
  map_zero' := by
    refine TrivSqZeroExt.ext (map_zero φ) ?_
    change φ (d 0) = 0
    rw [map_zero, map_zero]
  map_add' s t := by
    refine TrivSqZeroExt.ext (map_add φ s t) ?_
    change φ (d (s + t)) = φ (d s) + φ (d t)
    rw [map_add (f := _), map_add (f := _)]
  map_mul' s t := by
    refine TrivSqZeroExt.ext (map_mul φ s t) ?_
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    change φ (d (s * t)) = φ s * φ (d t) + φ (d s) * φ t
    rw [hd, map_add (f := _), map_mul, map_mul, mul_comm (φ t)]

theorem exists_tangent_matrix : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] {K : Type} [Field K] (z : Sp K ⟶ Y), ∃ (O : Y.Opens) (_ : ⊤ ≤ z ⁻¹ᵁ O) (x : Fin D → Γ(Y, O)) (w : Fin D → (Sp (DualNumber K) ⟶ Y)), (∀ b, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = z) ∧ ∀ hwO : (∀ b, ⊤ ≤ w b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (w b) O (hwO b) (x a)).snd).det ≠ 0 := by
  intro k _ Y p D _ K _ z
  obtain ⟨V, hV, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top (GlobalTheory.Adelic.ptOf z))
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), GlobalTheory.Adelic.ptOf z ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨x, d, hl, hd⟩ := exists_coords_derivs h₂
  have hO : IsAffineOpen (Y.basicOpen (t : Γ(Y, V))) := IsAffineOpen.basicOpen hV _
  have hzO : ⊤ ≤ z ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := (GlobalTheory.Adelic.le_iff_ptOf_mem z _).2 hxt
  choose w hw he using fun c => exists_evalPt_eq hO (jetHom (evalPt z _ hzO) (d c) (hl c))
  refine ⟨_, hzO, x, w, fun b => ?_, fun hwO => ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw b (Set.mem_univ _)
    refine ext_evalPt hO h' hzO (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ (w b) _ (hw b) h' f).trans ?_
    rw [he]
    rfl
  · have hm : (Matrix.of fun a b => (evalPt (w b) _ (hwO b) (x a)).snd) = (1 : Matrix (Fin D) (Fin D) K) := by
      ext a b
      have e1 : (evalPt (w b) _ (hwO b) (x a)).snd = evalPt z _ hzO (d b (x a)) := by
        rw [he]
        rfl
      rw [Matrix.of_apply, e1, hd, Matrix.one_apply]
      split_ifs <;> simp
    rw [hm, Matrix.det_one]
    exact one_ne_zero

end GlobalTheory.TanVec
end
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem haarChart_exists (X : Data E r) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ HaarChart X c := GlobalTheory.T.exists_haarIntegral_eq_unitriangularChart X

theorem haar_trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (hp : X.p0 = X'.p0) (φ : Frame X'.Ψ r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ (trF X X' e (frameOf X g)) ∂haarR X = ∫⁻ g, φ (frameOf X' g) ∂haarR X' := GlobalTheory.T.lintegral_transportHermitianFrame_realUnitary X X' e hp φ hφ

theorem muF_trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (hp : X.p0 = X'.p0) (φ : Frame X'.Ψ r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ z, φ (trF X X' e (cpt X (baseFr X) z)) ∂muF X (baseFr X) =
      ∫⁻ z, φ (cpt X' (baseFr X') z) ∂muF X' (baseFr X') := GlobalTheory.T.lintegral_transportHermitianFrame_chartMeasure X X' e hp φ hφ

theorem test_exists (X : Data E r) : ∃ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ ∧
    (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧
    ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ 0 ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ ⊤ :=
  GlobalTheory.T.exists_borelInvariant_testFunction_frameChart X

theorem isFundamentalDomain_sat (X : Data E r) {c : ℝ≥0∞} (hc : HaarChart X c) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) (Λ : Subgroup (RealGrp X))
    (hΛ : ∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) :
    IsFundamentalDomain Λ (frameOf X ⁻¹' GlobalTheory.Unfold.satFrames X x0 FF) (haarR X) := GlobalTheory.T.isFundamentalDomain_saturated_fundamentalSet_frames X hc ho hF Λ hΛ

theorem trF_rmul {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (y b : Frame X.Ψ r) :
    trF X X' e (rmul y b) = rmul (trF X X' e y) (fun τ' => b (e.symm τ')) := by
  funext τ'
  show (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * (mat y (e.symm τ') * mat b (e.symm τ')) :
      Matrix (Fin r) (Fin r) ℂ) =
    mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat y (e.symm τ') * mat b (e.symm τ')
  simp only [Matrix.mul_assoc]

theorem continuous_trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) : Continuous (trF X X' e) := by
  refine continuous_pi fun τ' => ?_
  have hM : Continuous fun y : Frame X.Ψ r => mat y (e.symm τ') := continuous_apply _
  exact continuous_const.matrix_mul hM

theorem trF_mem_dom {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (hp : X.p0 = X'.p0) {y : Frame X.Ψ r} (hy : y ∈ X.dom) : trF X X' e y ∈ X'.dom := by
  intro τ'
  set τ := e.symm τ'
  have hb := GlobalTheory.PeterssonCompare.det_baseFr X τ
  have hb' := GlobalTheory.PeterssonCompare.det_baseFr X' τ'
  set M : Matrix (Fin r) (Fin r) ℂ := (mat (baseFr X) τ)⁻¹ * mat y τ
  have hy' : mat y τ = mat (baseFr X) τ * M := (Matrix.mul_nonsing_inv_cancel_left _ _ hb.isUnit).symm
  have ht : mat (trF X X' e y) τ' = mat (baseFr X') τ' * M := by
    show mat (baseFr X') τ' * (mat (baseFr X) τ)⁻¹ * mat y τ = mat (baseFr X') τ' * ((mat (baseFr X) τ)⁻¹ * mat y τ)
    rw [Matrix.mul_assoc]
  have hg : gram τ'.1 X'.Gm (mat (trF X X' e y) τ') = gram τ.1 X.Gm (mat y τ) := by
    rw [ht, hy', FrameDegreeData.gram_mul, FrameDegreeData.gram_mul, baseFr_mem X τ, baseFr_mem X' τ', hp]
  refine ⟨?_, fun i => ?_⟩
  · rw [ht, Matrix.det_mul]
    refine mul_ne_zero hb' ?_
    intro h0
    apply (hy τ).1
    rw [hy', Matrix.det_mul, h0, mul_zero]
  · have := (hy τ).2 i
    unfold dmin at this ⊢
    rw [hg, ← hp]
    exact this

theorem haarChart_unique {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (hp : X.p0 = X'.p0) (hn : X.Ψ.card = X'.Ψ.card) {c c' : ℝ≥0∞} (hc : HaarChart X c) (hc' : HaarChart X' c') :
    c = c' := by
  have e : X.Ψ ≃ X'.Ψ := Fintype.equivOfCardEq (by simpa using hn)
  obtain ⟨φ, hφm, hφB, h0, htop⟩ := test_exists X'
  have hm : Measurable (fun y => φ (trF X X' e y)) := hφm.comp (continuous_trF X X' e).measurable
  have hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (trF X X' e (rmul x b)) = φ (trF X X' e x) := by
    intro x hx b hb
    rw [trF_rmul]
    exact hφB _ (trF_mem_dom X X' e hp hx) _ fun τ' => hb (e.symm τ')
  have h1 := hc _ hm hB
  rw [haar_trF X X' e hp φ hφm, hc' φ hφm hφB, muF_trF X X' e hp φ hφm] at h1
  exact ((ENNReal.mul_left_inj h0 htop).1 h1).symm

theorem countable_image (X : Data E r) {Λ : Subgroup (RealGrp X)}
    (hΛ : ∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) : Countable Λ := by
  haveI := FundSetPf.countable_GL (E := E) (r := r)
  choose f hf using fun s : Λ => (hΛ s.1).1 s.2
  refine Function.Injective.countable (f := f) fun s t h => Subtype.ext ?_
  apply GlobalTheory.PeterssonCompare.frameOf_injective X
  rw [← (hf s).2, ← (hf t).2, h]

theorem quotInt_eq_of_haarChart (X : Data E r) {c : ℝ≥0∞} (hc : HaarChart X c) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) {Φ : Frame X.Ψ r → ℝ≥0∞}
    (hΦ : Measurable Φ) (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x)
    (hB : ∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) :
    quotInt X Φ = c * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  classical
  obtain ⟨Λ, hΛ, -⟩ := GlobalTheory.ArithImage.exists_discrete_image E r X
  haveI := countable_image X hΛ
  set S := GlobalTheory.Unfold.satFrames X x0 FF
  have hS : MeasurableSet S := GlobalTheory.Unfold.measurableSet_satFrames X ho hF.1 hF.2.1
  rw [GlobalTheory.PeterssonCompare.quotInt_eq X hΛ (isFundamentalDomain_sat X hc ho hF Λ hΛ) hΓ]
  have hpre : MeasurableSet (frameOf X ⁻¹' S) := GlobalTheory.PeterssonCompare.measurable_frameOf X hS
  rw [← lintegral_indicator hpre]
  have e1 : (frameOf X ⁻¹' S).indicator (fun g => Φ (frameOf X g)) = fun g => S.indicator Φ (frameOf X g) := by
    funext g; by_cases h : frameOf X g ∈ S <;> simp [h]
  have hIB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, S.indicator Φ (rmul x b) = S.indicator Φ x := by
    intro x hx b hb
    rw [Set.indicator_apply, Set.indicator_apply, GlobalTheory.Unfold.rmul_mem_satFrames_iff X x0 FF x hb, hB b hb x hx]
  have hbo : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
  rw [e1, hc _ (hΦ.indicator hS) hIB,
    GlobalTheory.FrameMeasureClosed.measInv_holds r X (baseFr X) x0 hbo ho _ (hΦ.indicator hS) hIB,
    ← lintegral_indicator hF.1]
  congr 1
  refine lintegral_congr fun z => ?_
  rw [Set.indicator_apply, Set.indicator_apply, GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho]

end

end GlobalTheory.FlagQuotHaar

open GlobalTheory.FlagQuotHaar in
theorem GlobalTheory.FlagQuotHaar.quotInt_eq_const_mul : ∀ (r p0 n : ℕ), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : Data E r), X.p0 = p0 → X.Ψ.card = n → ∀ (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (Φ : Frame X.Ψ r → ℝ≥0∞), IsOrth X x0 → IsFundSet X x0 FF → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt X Φ = κ * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  intro r p0 n
  by_cases h : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (X : Data E r),
      X.p0 = p0 ∧ X.Ψ.card = n
  · obtain ⟨E₁, _, _, _, X₁, hp₁, hn₁⟩ := h
    obtain ⟨c₁, h0, htop, hc₁⟩ := haarChart_exists X₁
    refine ⟨c₁, h0, htop, fun E _ _ _ X hp hn x0 FF Φ ho hF hΦ hΓ hB => ?_⟩
    obtain ⟨c, -, -, hc⟩ := haarChart_exists X
    rw [quotInt_eq_of_haarChart X hc ho hF hΦ hΓ hB,
      haarChart_unique X X₁ (hp.trans hp₁.symm) (hn.trans hn₁.symm) hc hc₁]
  · refine ⟨1, one_ne_zero, ENNReal.one_ne_top, fun E _ _ _ X hp hn => ?_⟩
    exact absurd ⟨E, inferInstance, inferInstance, inferInstance, X, hp, hn⟩ h
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

def leftStab {G : Type} [Group G] (φ : G → ℂ) : Subgroup G where
  carrier := {γ | ∀ g, φ (γ * g) = φ g}
  one_mem' := fun g => by simp
  mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
  inv_mem' := fun {a} ha g => by rw [← ha (a⁻¹ * g), mul_inv_cancel_left]

theorem stdPar_eq_flag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S = GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ∧ GlobalTheory.StdPar.levi σ J X Y S = GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ∧ ∀ (K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ), GlobalTheory.StdPar.IsAutOn σ J X Y S K φ ↔ GlobalTheory.UAut.IsAutOn σ J (GlobalTheory.UAut.leftGrp σ J (X.submatrix id (Fin.castLE hs)) d) K φ := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  have hu := le_antisymm (GlobalTheory.T.hermitianWittFrame_unipotent_le_flag_unipotent F E σ h n J hJ r X Y hW S s hs hS d hd) (GlobalTheory.T.unipotent_radical_graded_isotropic_flag_le F E σ h n J hJ r X Y hW S s hs hS d hd)
  have hl := le_antisymm (GlobalTheory.T.leviSubgroup_le_gradedIsotropicFlagLevi F E σ h n J hJ r X Y hW S s hs hS d hd) (GlobalTheory.T.gradedIsotropicFlagLevi_le_leviSubgroup F E σ h n J hJ r X Y hW S s hs hS d hd)
  have hg := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).2.2.1
  refine ⟨hu, hl, fun K φ => ⟨fun hφ => ⟨?_, hφ.level, hφ.cont, hφ.smooth, hφ.growth, GlobalTheory.UAut.kfin_iff.1 hφ.kfin, hφ.zfin⟩,
    fun hφ => ⟨fun u hu' g => hφ.left u ?_ g, fun γ hγ hγ' g => hφ.left γ ?_ g, hφ.level, hφ.cont, hφ.smooth, hφ.growth,
      GlobalTheory.UAut.kfin_iff.2 hφ.kfin, hφ.zfin⟩⟩⟩
  · rw [hg]
    have : GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ⊔ (ratPts σ J ⊓ GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d) ≤ leftStab φ :=
      sup_le (fun u hu' => hφ.leftN u (hu ▸ hu')) (fun γ hγ => hφ.leftM γ hγ.1 (hl ▸ hγ.2))
    exact fun γ hγ => this hγ
  · rw [hg]; exact Subgroup.mem_sup_left (hu ▸ hu')
  · rw [hg]; exact Subgroup.mem_sup_right ⟨hγ, hl ▸ hγ'⟩

end GlobalTheory.TieStd
end

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.AutomorphicL2Unitary (LeftInv)

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem ratPts_inf_subgroupOf {N P : Subgroup (GAd σ J)} (hNP : N ≤ P) :
    (ratPts σ J ⊓ P).subgroupOf N = (ratPts σ J).subgroupOf N := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hNP x.2⟩⟩

theorem isConstTermOn_iff_ratPts_inf {N P : Subgroup (GAd σ J)} [LocallyCompactSpace N] (hNP : N ≤ P)
    (hc : Cocompact (ratPts σ J) N) {φ c : GAd σ J → ℂ} (hφ : LeftInv (ratPts σ J ⊓ P) φ) :
    IsConstTermOn σ J N φ c ↔ c = constTermOn (ratPts σ J ⊓ P) N φ := by
  have e := ratPts_inf_subgroupOf (σ := σ) (J := J) hNP
  constructor
  · intro h
    obtain ⟨μ, 𝓕, h1, h2, h3⟩ := exists_mass_one hc
    funext g
    rw [h μ 𝓕 h1 h2 h3 g, GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g]
  · rintro rfl μ 𝓕 h1 h2 h3 g
    exact GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g

theorem cocompact_ratPts_inf {N P : Subgroup (GAd σ J)} (hNP : N ≤ P) (hc : Cocompact (ratPts σ J) N) :
    Cocompact (ratPts σ J ⊓ P) N := by
  unfold Cocompact
  rw [ratPts_inf_subgroupOf hNP]
  exact hc

section Witt

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include h hJ hW

theorem locallyCompact_unip (S : Finset (Fin r)) : LocallyCompactSpace (unip σ J X S) :=
  (isClosed_unip S h hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem cocompact_unip_std (S : Finset (Fin r)) : Cocompact (ratPts σ J) (unip σ J X S) := by
  by_cases hS0 : S = ∅
  · subst hS0
    refine ⟨{1}, isCompact_singleton, fun u => ⟨u⁻¹, ?_, by simp⟩⟩
    have hu : (u : GAd σ J) = 1 := Subgroup.mem_bot.1 (le_of_eq (unip_empty (σ := σ) (J := J) (X := X)) u.2)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_inv, hu, inv_one]
    exact one_mem _
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  rw [GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ h n J hJ r X Y hW S m hm hm']
  exact cocompact_unipFlag hJ (sigma_sigma h) (isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ m.2) _

theorem conj_mem_unip_of_subset {S T : Finset (Fin r)} (hTS : T ⊆ S) {p u : GAd σ J} (hp : p ∈ unip σ J X S)
    (hu : u ∈ unip σ J X T) : p * u * p⁻¹ ∈ unip σ J X T := by
  by_cases hT0 : T = ∅
  · subst hT0
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ T, ∀ k ∈ T, k ≤ m := ⟨T.max' (Finset.nonempty_iff_ne_empty.2 hT0),
    T.max'_mem _, fun k hk => T.le_max' k hk⟩
  have hσ := sigma_sigma h
  have eT := GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ h n J hJ r X Y hW T m hm hm'
  rw [eT] at hu ⊢
  exact conj_mem_unipFlag hJ hσ (isIsoCols_of_isWittFrame hW hσ hJ m.2) _
    (GlobalTheory.ConstTrans.unip_le_parFlag F E σ h n J hJ r X Y hW S T m hTS hm hm' hp) hu

theorem constAlong_cocompact_unique_stages :
    (∀ S : Finset (Fin r), Cocompact (ratPts σ J) (unip σ J X S) ∧
      ∃ (μ : Measure (unip σ J X S)) (𝓕 : Set (unip σ J X S)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratPts σ J).subgroupOf (unip σ J X S)) 𝓕 μ ∧ μ 𝓕 = 1) ∧
    (∀ S T : Finset (Fin r), T ⊆ S → unip σ J X T ≤ unip σ J X S ∧ levi σ J X Y S ≤ levi σ J X Y T) ∧
    (∀ (S : Finset (Fin r)) (φ c c' : GAd σ J → ℂ), IsConstAlong σ J X S φ c → IsConstAlong σ J X S φ c' → c = c') ∧
    (∀ (S : Finset (Fin r)) (φ : GAd σ J → ℂ), (∀ γ ∈ ratPts σ J, γ ∈ unip σ J X S → ∀ g, φ (γ * g) = φ g) →
      ∃ c, IsConstAlong σ J X S φ c) ∧
    (∀ (S T : Finset (Fin r)) (φ c c' : GAd σ J → ℂ), T ⊆ S → Continuous φ →
      (∀ γ ∈ ratPts σ J, γ ∈ unip σ J X S → ∀ g, φ (γ * g) = φ g) →
      IsConstAlong σ J X T φ c → IsConstAlong σ J X S c c' → IsConstAlong σ J X S φ c') := by
  refine ⟨fun S => ?_, fun S T hTS => ⟨unip_mono_of_subset F E σ h n J hJ r X Y hW S T hTS, ?_⟩,
    fun S φ c c' h1 h2 => ?_, fun S φ hφ => ?_, fun S T φ c c' hTS hφc hφ hc hc' => ?_⟩
  · haveI := locallyCompact_unip h hJ hW S
    exact ⟨cocompact_unip_std h hJ hW S, exists_mass_one (cocompact_unip_std h hJ hW S)⟩
  · intro g hg
    simp only [levi, Subgroup.mem_iInf] at hg ⊢
    exact fun k hk => hg k (hTS hk)
  · haveI := locallyCompact_unip h hJ hW S
    exact IsConstTermOn.unique (cocompact_unip_std h hJ hW S) h1 h2
  · haveI := locallyCompact_unip h hJ hW S
    exact ⟨_, isConstTermOn_constTermOn (N := unip σ J X S) fun γ hγ g => hφ γ hγ.1 hγ.2 g⟩
  · haveI := locallyCompact_unip h hJ hW S
    haveI := locallyCompact_unip h hJ hW T
    have hle : unip σ J X T ≤ unip σ J X S := unip_mono_of_subset F E σ h n J hJ r X Y hW S T hTS
    have cS := cocompact_unip_std h hJ hW S
    have cT := cocompact_unip_std h hJ hW T
    have hfΓ : LeftInv (ratPts σ J ⊓ unip σ J X S) φ := fun γ hγ g => hφ γ hγ.1 hγ.2 g
    have hnorm : ∀ p ∈ unip σ J X S, ∀ u ∈ unip σ J X T, p * u * p⁻¹ ∈ unip σ J X T :=
      fun p hp u hu => conj_mem_unip_of_subset h hJ hW hTS hp hu
    have hc0 : c = constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ :=
      (isConstTermOn_iff_ratPts_inf hle cT hfΓ).1 hc
    subst hc0
    have hcΓ : LeftInv (ratPts σ J ⊓ unip σ J X S) (constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ) :=
      fun γ hγ g => GlobalTheory.Cusp.constTermOn_mul_left_of_normalizer hfΓ hγ
        (fun m => ⟨hnorm _ hγ.2 m, fun hm => by simpa [mul_assoc] using hnorm _ (inv_mem hγ.2) _ hm⟩) g
    have st : constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X S) φ =
        constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X S)
          (constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ) := funext fun x =>
      GlobalTheory.Cusp.Stages.constTermOn_stages (GAd σ J) (ratPts σ J ⊓ unip σ J X S) (unip σ J X S) (unip σ J X T) hle hnorm
        (cocompact_ratPts_inf le_rfl cS) (cocompact_ratPts_inf hle cT) φ hfΓ hφc x
    change IsConstTermOn σ J (unip σ J X S) _ c' at hc'
    change IsConstTermOn σ J (unip σ J X S) φ c'
    rw [isConstTermOn_iff_ratPts_inf le_rfl cS hcΓ] at hc'
    rw [isConstTermOn_iff_ratPts_inf le_rfl cS hfΓ, st]
    exact hc'

end Witt

end GlobalTheory.StdPar

end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.wittFrameUnipotentRadical_closed_fundDomain_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → IsClosed (unipRad σ J X : Set (GAd σ J)) ∧ ∃ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure ∧ IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν ∧ ν DN = 1 := by
  first | exact @GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one | exact GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one | (intros; apply GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one <;> assumption)
end
