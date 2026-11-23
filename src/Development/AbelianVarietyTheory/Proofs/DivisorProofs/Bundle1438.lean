module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThreeRankOneSphericalVectorCellValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory


theorem _root_.GlobalTheory.T.integral_fundamentalDomain_tsum_rationalTranslates : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ h : (κ → AF F) → ℂ, Continuous h →
      (∃ B : ℝ, ∀ x : κ → AF F, Summable (fun η : κ → F => ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖) ∧
        ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ ≤ B) →
      ∫ x in 𝓕₁, ∑' η : κ → F, h ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ = ∫ u, h u ∂μ := by
  first | exact @GlobalTheory.ThetaUnfoldInt.integral_fundamentalDomain_tsum | exact GlobalTheory.ThetaUnfoldInt.integral_fundamentalDomain_tsum | (intros; apply GlobalTheory.ThetaUnfoldInt.integral_fundamentalDomain_tsum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory


theorem _root_.GlobalTheory.T.integral_ratPairFundamentalDomain_adelic_iterated : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    letI : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ (lam : MeasureTheory.Measure ((κ → AF F) × (κ → AF F))), lam.IsAddHaarMeasure →
    ∀ 𝓖 : Set ((κ → AF F) × (κ → AF F)),
      MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) 𝓖 lam →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ G : (κ → AF F) × (κ → AF F) → ℂ, Measurable G →
      (∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w, G (γ + w) = G w) → (∃ B : ℝ, ∀ w, ‖G w‖ ≤ B) →
      ∫ w in 𝓖, G w ∂lam = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  first | exact @GlobalTheory.PeriodicIteratedIntegral.integral_ratPair_fundamentalDomain_eq_iterated | exact GlobalTheory.PeriodicIteratedIntegral.integral_ratPair_fundamentalDomain_eq_iterated | (intros; apply GlobalTheory.PeriodicIteratedIntegral.integral_ratPair_fundamentalDomain_eq_iterated <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem over_of_fib {K : Type} [Field K] [NumberField K] {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)}
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol)
    (u₀ : Sp (DualNumber K) ⟶ t₀.G.left) (w : epsR K ⟶ F.P₀.A) (h : u₀ ≫ m2.φ = w.left ≫ F.φ) :
    u₀ ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  haveI : Mono (spMap (algebraMap (𝓞 K) K)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  rw [← cancel_mono (spMap (algebraMap (𝓞 K) K)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, h,
    Category.assoc]
  have := F.fib.2.1.1.w
  erw [this, ← Category.assoc, Over.w w]
  rfl

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

theorem spMap_dualMap_algebraMap {S R : Type} [CommRing S] [CommRing R] (f : S →+* R) :
    spMap (dualMap f) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap R (DualNumber R)) ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_dualMap_id {S : Type} [CommRing S] : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
  have : dualMap (RingHom.id S) = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply TrivSqZeroExt.ext <;> simp [dualMap]
  simp only [spMap, this]
  exact Spec.map_id _

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_lift_eps {K Tf : Type} [CommRing K] [CommRing Tf] {G' : Over (Sp Tf)} {G : Over (Sp K)}
    (f : K →+* Tf) {φ : G'.left ⟶ G.left} (hp : IsPullback φ G'.hom G.hom (spMap f))
    (u₀ : Sp (DualNumber K) ⟶ G.left) (hu : u₀ ≫ G.hom = spMap (algebraMap K (DualNumber K))) :
    ∃ g : epsR Tf ⟶ G', g.left ≫ φ = spMap (dualMap f) ≫ u₀ :=
  ⟨Over.homMk (hp.lift (spMap (dualMap f) ≫ u₀) (spMap (algebraMap Tf (DualNumber Tf)))
      (by rw [Category.assoc, hu, spMap_dualMap_algebraMap])) (hp.lift_snd _ _ _), hp.lift_fst _ _ _⟩

theorem isLieComb_of_match {K : Type} [Field K] [NumberField K] {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)}
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) {T : CDVR} (iK : K →+* T.Fr)
    {t' : SAB H (Sp T.Fr)} (n' : SABMap t' t₀ (spMap iK)) {v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)}
    (hv' : IsLieBasis v')
    (hv'φ : ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (dualMap iK) ≫ (F.v k).left ≫ F.φ)
    (c : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A) (hw : IsLieComb c F.v w) (g : epsR T.Fr ⟶ t'.G)
    (hg : g.left ≫ n'.φ ≫ m2.φ = spMap (dualMap iK) ≫ w.left ≫ F.φ) :
    IsLieComb (fun k => iK (c k)) v' g := by
  obtain ⟨w', hw'⟩ := ((GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1).1 (fun k => iK (c k))).exists
  have hpb := IsGrpPullback.comp n'.cart m2.cart
  have hid : spMap (RingHom.id T.Fr) = 𝟙 _ := by
    simp only [spMap, CommRingCat.ofHom_id]
    exact Spec.map_id _
  have key := GlobalTheory.LamT.LetterInt.comb_match hpb F.fib.2.1 (RingHom.id T.Fr) iK
    (by rw [hid, Category.id_comp]) (v₁ := v') (v₂ := F.v)
    (fun k => by rw [spMap_dualMap_id, Category.id_comp]; exact hv'φ k) (c₁ := fun k => iK (c k)) (c₂ := c)
    (fun k => rfl) hw' hw
  rw [spMap_dualMap_id, Category.id_comp, ← hg] at key
  have : w' = g := Over.OverMorphism.ext (hpb.1.hom_ext key (by rw [Over.w w', Over.w g]))
  subst this
  exact hw'

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem comb_left_of_isCombAt {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Tf : Type} [CommRing Tf]
    {x : Sp Tf ⟶ Xo.X} {t' : SAB H (Sp Tf)} (m1' : SABMap t' Xo.univ.t x) {m : ℕ}
    (e : Fin m → (Sp (DualNumber Tf) ⟶ Xo.univ.t.G.left)) (cc : Fin m → Tf)
    (z : Sp (DualNumber Tf) ⟶ Xo.univ.t.G.left) (hz : IsCombAt x e cc z) (g : Fin m → (epsR Tf ⟶ t'.G))
    (hg : ∀ j, (g j).left ≫ m1'.φ = e j) (w'' : epsR Tf ⟶ t'.G) (hw : IsLieComb cc g w'') :
    w''.left ≫ m1'.φ = z := by
  obtain ⟨b, hb, rfl⟩ := hz
  obtain ⟨a, ha, rfl⟩ := hw
  have := GlobalTheory.LamT.LetterInt.prod_pull m1'.cart (epsR Tf) _ (𝟙 _) (by rw [Category.id_comp]; rfl) a b
    (fun j => by rw [hb j, Category.id_comp, ha j, Category.assoc, hg j]; rfl)
  rw [this, Category.id_comp]

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg

open GlobalTheory.PtDeg.FrameGen in
theorem frame_genFib_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (T : CDVR) (iK : K →+* T.Fr), letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x), m1'.φ = n'.φ ≫ m1.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → ∀ (i : Fin (Dw.mult ρ)) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) → u'' ≫ m1'.φ = y'.u ρ i → ∃ w'' : epsR T.Fr ⟶ t'.G, w''.left = u'' ∧ IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) v' w'' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ u hF T iK
  letI : Algebra c.F T.Fr := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hyT t' n' m1' h1 v' hv' hv'φ C a y' hchg i u'' hu''0 hu''1
  choose u₀ w hu₁ hu₂ hw using hF
  have hover : ∀ j, u₀ j ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) :=
    fun j => over_of_fib m2 F (u₀ j) (w j) (hu₂ j)
  choose g hg using fun j => exists_lift_eps iK n'.cart.1 (u₀ j) (hover j)
  have hg1 : ∀ j, (g j).left ≫ m1'.φ = yT.u ρ j := fun j => by
    rw [h1, ← Category.assoc, hg j, Category.assoc, hu₁ j]
    exact (hyT.2.1 ρ j).symm
  have hcomb : ∀ j, IsLieComb (fun k => iK (u j k)) v' (g j) := fun j =>
    isLieComb_of_match m2 F iK n' hv' hv'φ (u j) (w j) (hw j) (g j)
      (by rw [← Category.assoc, hg j, Category.assoc, hu₂ j])
  have hA := GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1
  have htan : ∀ j, IsTangent (g j) := fun j => hA.2.1 _ _ (hcomb j)
  have hB := GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ g htan
  obtain ⟨w'', hw''⟩ := (hB.1 (C ρ i)).exists
  have hleft : w''.left ≫ m1'.φ = y'.u ρ i :=
    comb_left_of_isCombAt m1' (yT.u ρ) (C ρ i) _ (hchg.2.1 ρ i) g hg1 w'' hw''
  refine ⟨w'', m1'.cart.1.hom_ext (by rw [hleft, hu''1]) (by rw [Over.w w'', hu''0]; rfl), ?_⟩
  exact hA.2.2.1 _ (fun j k => iK (u j k)) g (C ρ i) w'' hcomb hw''

end GlobalTheory.PtDeg
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.unitaryThreeRankOne_sphericalVector_cell_value : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), IsSphericalU q α φ → φ 1 = 1 →
    ∀ u : cellU y, φ (y⁻¹ * (u : GU σ n)) = (α k / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) := by
  first | exact @GlobalTheory.WeylCell.U21HeisenbergElement.value_point | exact GlobalTheory.WeylCell.U21HeisenbergElement.value_point | (intros; apply GlobalTheory.WeylCell.U21HeisenbergElement.value_point <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    (∀ j : ℤ, IsOpen (shellU k y j) ∧ IsCompact (shellU k y j) ∧ (1 : cellU y) ∈ shellU k y j ∧
      (∀ u v : cellU y, u ∈ shellU k y j → v ∈ shellU k y j → u * v ∈ shellU k y j) ∧
      (∀ u : cellU y, u ∈ shellU k y j → u⁻¹ ∈ shellU k y j)) ∧
    shellU k y 0 = (((KU σ n).subgroupOf (cellU y) : Subgroup (cellU y)) : Set (cellU y)) := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup | exact GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical

noncomputable section
open Filter Topology

namespace GlobalTheory.SBBounds

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tendsto_pow_zero {x : k} (h : valuation k x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem sb_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : k),
    t ≠ 0 → valuation k t < 1 → ∀ φ : Matrix (Fin n) (Fin n) k → ℂ, φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    ∃ N M : ℕ, (∀ X, φ X ≠ 0 → t ^ N • X ∈ intM k (Fin n) (Fin n)) ∧
      ∀ X E, E ∈ intM k (Fin n) (Fin n) → φ (X + t ^ M • E) = φ X := by
  intro k _ _ _ _ n t _ ht φ hφ
  obtain ⟨hlc, hcs⟩ := hφ
  have hU : IsOpen (intM k (Fin n) (Fin n)) := isOpen_intMatrix
  have hUc : IsCompact (intM k (Fin n) (Fin n)) := isCompact_intMatrix
  have h0 : (0 : Matrix (Fin n) (Fin n) k) ∈ intM k (Fin n) (Fin n) := fun i j => (𝒪[k]).zero_mem
  have htO : t ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 ht.le
  have hT := tendsto_pow_zero ht

  have hmono : Monotone fun N : ℕ => {X : Matrix (Fin n) (Fin n) k | t ^ N • X ∈ intM k (Fin n) (Fin n)} := by
    intro N N' hNN' X hX i j
    have e : t ^ N' • X = t ^ (N' - N) • (t ^ N • X) := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hNN']
    rw [e]
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact (𝒪[k]).mul_mem ((𝒪[k]).pow_mem htO _) (hX i j)
  obtain ⟨N, hN⟩ := hcs.isCompact.elim_directed_cover
    (fun N : ℕ => {X : Matrix (Fin n) (Fin n) k | t ^ N • X ∈ intM k (Fin n) (Fin n)})
    (fun N => hU.preimage (f := fun X : Matrix (Fin n) (Fin n) k => t ^ N • X) (continuous_const_smul _))
    (fun X _ => by
      have h1 : Tendsto (fun N : ℕ => t ^ N • X) atTop (𝓝 ((0 : k) • X)) := hT.smul_const X
      rw [zero_smul] at h1
      obtain ⟨N, hN⟩ := (h1.eventually (hU.mem_nhds h0)).exists
      exact Set.mem_iUnion.2 ⟨N, hN⟩)
    hmono.directed_le

  have hZ : IsOpen {p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k |
      φ (p.2.1 + p.1 • p.2.2) = φ p.2.1} := by
    have c1 : Continuous fun p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k =>
        p.2.1 + p.1 • p.2.2 := by fun_prop
    have c2 : Continuous fun p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k => p.2.1 := by fun_prop
    have := ((hlc.comp_continuous c1).comp₂ (hlc.comp_continuous c2) fun a b => a - b).isOpen_fiber 0
    simpa [Function.comp_def, sub_eq_zero] using this
  have hKU : IsCompact (tsupport φ ×ˢ intM k (Fin n) (Fin n)) := hcs.isCompact.prod hUc
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ q ∈ tsupport φ ×ˢ intM k (Fin n) (Fin n), φ (q.1 + c • q.2) = φ q.1 := by
    refine hKU.eventually_forall_of_forall_eventually fun q _ => ?_
    have hm : ((0 : k), q) ∈ {p : k × Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k |
      φ (p.2.1 + p.1 • p.2.2) = φ p.2.1} := by simp
    exact hZ.mem_nhds hm
  obtain ⟨M, hM⟩ := (hT.eventually hev).exists
  refine ⟨N, M, fun X hX => hN (subset_tsupport _ hX), fun X E hE => ?_⟩
  by_cases hX : X ∈ tsupport φ
  · exact hM (X, E) ⟨hX, hE⟩
  by_cases hX' : X + t ^ M • E ∈ tsupport φ
  · have hE' : -E ∈ intM k (Fin n) (Fin n) := fun i j => (𝒪[k]).neg_mem (hE i j)
    have := hM (X + t ^ M • E, -E) ⟨hX', hE'⟩
    simp only [smul_neg, add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

end GlobalTheory.SBBounds
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Matrix

namespace GlobalTheory.SkewSplitSurj

open GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem locMat_unitary_skew (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (skew : ∀ i j, σ (J j i) = -J i j) (g : GL (Fin n) (Fv F v)) :
    (GlobalTheory.LeviAtPlace.locMat h t J g)ᵀ * J.map (inclR (Fv F v)) *
      (GlobalTheory.LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ) = J.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (J.map (inclR (Fv F v))).map (splitProj τ) = J.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (J i j)
  have hs1 : ((GlobalTheory.LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj t) = conjComp t J g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, GlobalTheory.LeviAtPlace.locMat, pairMat_snd]
  have hs2 : ((GlobalTheory.LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, GlobalTheory.LeviAtPlace.locMat, pairMat_fst]
  have hJs : J.map (t.comp σ) = -(J.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, AlgHom.comp_apply, Matrix.neg_apply]
    rw [skew j i, map_neg]
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, GlobalTheory.LeviAtPlace.locMat, pairMat_fst, conjComp]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))ᵀ * Jt := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by
          rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.transpose_one,
            Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, GlobalTheory.LeviAtPlace.locMat, pairMat_snd, conjComp, hJs]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * -Jtᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))
        = -(Jtᵀ * A * (Jt * Jt⁻¹)ᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg,
            Matrix.neg_mul]
      _ = -(Jtᵀ * (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))) := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = -Jtᵀ := by rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.mul_one]

end GlobalTheory.SkewSplitSurj


open GlobalTheory.SkewSplitSurj in
theorem GlobalTheory.SkewSplitSurj.exists_locMat_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c x : GL (Fin d) (Fv F v)),
    ∃ h ∈ UAt σ W (evFin F v), locMat t c h = x := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v t c x
  have hcm := hB.cm
  have hJ : IsUnit (W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hW.sig (InfinitePlace.mk φ))
    have h1 : W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show W.J.map t = (t : E →+* Fv F v).mapMatrix W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  set g : GL (Fin d) (Fv F v) := c * x * c⁻¹ with hg
  let hU : UA σ W.J := ⟨GlobalTheory.LeviAtPlace.adelicGL hcm t W.J hJ g,
    GlobalTheory.LeviAtPlace.lift_unitary v σ W.J _ (locMat_unitary_skew hcm t W.J hJ hW.skew g)⟩
  have hmat : mat hU = GlobalTheory.LeviAtPlace.lift v (GlobalTheory.LeviAtPlace.locMat hcm t W.J g) := rfl
  have hpi : (mat hU).map (piW t) = g.val := by
    have e : ∀ M : Matrix (Fin d) (Fin d) (AE F E), M.map (piW t) = (M.map (compFin F E v)).map (splitProj t) :=
      fun M => by rw [Matrix.map_map]; rfl
    rw [hmat, e, GlobalTheory.LeviAtPlace.compFin_lift]
    exact GlobalTheory.LeviAtPlace.pairMat_fst hcm t _ _
  refine ⟨hU, ?_, ?_⟩
  · show At (evFin F v) (mat hU - 1)
    rw [hmat]
    exact GlobalTheory.LeviAtPlace.lift_sub_one_at v _
  · apply Units.ext
    rw [GlobalTheory.KSplit.locMat_val, hpi, hg]
    simp [Matrix.mul_assoc]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_haar_adelicVectors_bounds_pureTensors_slices : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) → ∀ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      ∃ μ : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        ∃ C c : ℝ≥0∞, C ≠ ⊤ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
          (∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μ ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) ∧
          ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
            ∀ y, c * ∫⁻ z, ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2 ≤ ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds | exact GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds | (intros; apply GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

theorem _root_.GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ),
      d.rho ψ u (pureA F f h) = pureA F (GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ)
        (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) f) h := by
  first | exact @GlobalTheory.ArchRhoPure.rho_pureA_schrF | exact GlobalTheory.ArchRhoPure.rho_pureA_schrF | (intros; apply GlobalTheory.ArchRhoPure.rho_pureA_schrF <;> assumption)
end

section

open scoped SchwartzMap Matrix

theorem _root_.GlobalTheory.T.exists_pairing_coordinates_schrodinger_folland : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := by
  first | exact @GlobalTheory.ArchUniq.exists_pairing_coords | exact GlobalTheory.ArchUniq.exists_pairing_coords | (intros; apply GlobalTheory.ArchUniq.exists_pairing_coords <;> assumption)
end
