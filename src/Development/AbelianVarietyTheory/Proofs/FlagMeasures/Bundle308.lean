module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.SatakeDualWeyl.DefsCS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle002
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle013
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle280
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle123
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle304
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle212
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle297
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle158
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.FrameExists2
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle133
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
public import Formalism.RealPlaceAnalysis.Bundle005
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle306
public import Formalism.LocalToGlobal.HermitianForms.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle305
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SelfDualPoint

open Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.CS

theorem mem_genus {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (hn : h.Nondegenerate) {L L' : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hL' : Submodule.IsLattice K L') (hd : dual h L = L) (hd' : dual h L' = L') :
    L' ∈ genus h L := by
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩
  have key : ∀ M : Submodule (𝓞 K) V, M.FG → dual h M = M → ∀ P : Ideal (𝓞 K), P.IsPrime →
      IsUnimodularAt h P M := fun M hM hdM P hP => by
    have a := (locDual (𝓞 K) K V h hs hstar M hM).1 P hP
    have b := a.2.trans a.1.symm
    rwa [hdM] at b
  have full : ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → dual h M = M →
      Submodule.IsFullLattice K M := by
    intro M hM hdM
    classical
    let b := Module.finBasis K V
    let B : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range b)
    let N := M ⊔ B
    have hNfg : N.FG := hM.fg.sup (Submodule.fg_span (Set.finite_range b))
    have hNspan : Submodule.span K (N : Set V) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← b.span_eq]
      apply Submodule.span_mono
      rintro x ⟨i, rfl⟩
      exact (show B ≤ N from le_sup_right) (Submodule.subset_span ⟨i, rfl⟩)
    have hN : Submodule.IsFullLattice K N :=
      { toIsLattice := Submodule.IsLattice.of_fg K hNfg, span_eq_top := hNspan }
    have hNd := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs hn hstar N hN).1
    have hle : dual h N ≤ M := by
      rw [← hdM]
      exact (dualBasic (𝓞 K) K V h hs hstar).1 M N le_sup_left
    letI : Submodule.IsFullLattice K (dual h N) := hNd
    letI : Submodule.IsLattice K M := hM
    exact Submodule.IsFullLattice.of_le K hle
  have hLf := full L hL hd
  have hL'f := full L' hL' hd'
  exact ⟨hL'f, fun P hP => GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt K V h hK hs hn L L' hLf hL'f P hP
    (key L hL.fg hd P hP.isPrime) (key L' hL'.fg hd' P hP.isPrime)⟩

theorem lamX_eq_globLat (I : AutInst) (xf : I.Gf) : lamX I (1, xf) = globLat xf.1 I.L := by
  have e : I.Lf = latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf latS
    congr 1
    ext u
    exact ⟨fun ⟨x, hx⟩ => ⟨x, x.2, hx⟩, fun ⟨x, hx, hx'⟩ => ⟨⟨x, hx⟩, hx'⟩⟩
  unfold lamX
  rw [e]
  exact Submodule.span_eq (globLat xf.1 I.L)

theorem exists_lamX_eq : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)), Submodule.IsLattice I.E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, Formalism.UG.hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ xf : I.Gf, lamX I (1, xf) = Λ := by
  intro I Λ hΛ hd
  have hs : ∀ e, (I.cm.sig : I.E →+* I.E) ((I.cm.sig : I.E →+* I.E) e) = e := fun e => star_star e
  have hfix : ∀ e : I.E, I.cm.sig e = e → ∃ a : I.F, algebraMap I.F I.E a = e := fun e he => (I.cm.fixed e).1 he
  let h : (Fin I.n → I.E) →ₗ⋆[I.E] (Fin I.n → I.E) →ₗ[I.E] I.E := formJ (I.cm.sig : I.E →+* I.E) hs I.J 1
  obtain ⟨hsym, hap⟩ := Formalism.UG.P.hermitian_form_symmetry_holds I.E _ hs (Fin I.n) I.J 1 (map_one _) I.J_herm
  replace hsym : h.IsSymm := hsym
  replace hap : ∀ x y, h x y = hform (starRingEnd I.E) I.J x y := fun x y => (hap x y).trans (one_mul _)
  have hr : ∀ y, (∀ x, h x y = 0) → y = 0 := fun y hy => by
    refine Matrix.eq_zero_of_mulVec_eq_zero I.J_det (funext fun i => ?_)
    have := hy (Pi.single i 1)
    rw [hap, hform, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at this
    simpa [Matrix.mulVec, dotProduct] using this
  have hn : h.Nondegenerate := ⟨fun x hx => hr x fun y => by rw [← hsym.eq, hx, map_zero], hr⟩
  have hdual : ∀ M : Submodule (𝓞 I.E) (Fin I.n → I.E),
      (∀ x, x ∈ M ↔ ∀ y ∈ M, hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) →
      dual h M = M := fun M hM => by
    ext x
    rw [dualBasic_mem_dual, hM x]
    simp only [hap, Submodule.mem_one, RingHom.mem_range]
  obtain ⟨g, hg, e⟩ := GlobalTheory.Mass.Genus.exists_globLat_eq (J := I.J) hs hfix (Module.Finite.iff_fg.2 I.L_fg)
    I.L_span Λ (mem_genus h I.cm.cmUnram hsym hn (Submodule.IsLattice.of_fg I.E I.L_fg) hΛ (hdual _ I.L_dual) (hdual _ hd))
  exact ⟨⟨g, hg⟩, (lamX_eq_globLat I _).trans e⟩

end GlobalTheory.SelfDualPoint
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselModel_projector_on_line : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l → (∀ u ∈ DD σ w, l2SG ν (fun x => l (σ x u)) = ENNReal.ofReal (‖u‖ ^ 2 / d)) ∧ (∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x ∈ GG k r, Afun (psiGen k r z c) π μS σ w v ξ x = ⟪l v, ξ⟫_ℂ • l (σ x w)) ∧ ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, rconv μG (eFun μG σ w) W y = ((d : ℂ) * ∫ g, ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ ∂ν) • l (σ y w) := by
  first | exact @GlobalTheory.SgInf.ProjLine.projector_line | exact GlobalTheory.SgInf.ProjLine.projector_line | (intros; apply GlobalTheory.SgInf.ProjLine.projector_line <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lintegral_besselCoefficient_compact_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u ∈ DD σ w, AEStronglyMeasurable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
  first | exact @GlobalTheory.SgInf.lint_Afun_compact_le | exact GlobalTheory.SgInf.lint_Afun_compact_le | (intros; apply GlobalTheory.SgInf.lint_Afun_compact_le <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lintegral_hsNormSq_doubleCoset_le_fatou : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∫⁻ γ, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal (d⁻¹ * (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).re * (⟪ξ', be (psiGen k r z' c') π' μS' σ x x ξ'⟫_ℂ).re) := by
  first | exact @GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le | exact GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le | (intros; apply GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountSum

theorem countHyp_mono {B : RowsAut} {Cg : ℝ} {n₀ n₁ : ℕ} {d : InfinitePlace B.I.F → ℝ} {p q : ℕ} {b : ℝ}
    (h : CountHyp B Cg n₀ d p q b) (hn : n₁ ≤ n₀) : CountHyp B Cg n₁ d p q b :=
  ⟨h.1, h.2.1, hn.trans h.2.2.1, h.2.2.2⟩

theorem countingTheorem_of_finite_of_bounds :
    (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ →
      CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) →
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.PtBound →
    GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare →
    GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hfinC hflag hpt hnear hfar hrare hdeep Cg
  by_cases hC : 0 ≤ Cg
  swap
  · exact ⟨8, fun B d p q b h => absurd (GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl h).1 hC⟩
  obtain ⟨n₁, hn₁⟩ := hnear Cg hC
  obtain ⟨n₂, hn₂⟩ := hfar Cg hC
  obtain ⟨n₃, hn₃⟩ := hrare
  obtain ⟨n₄, hn₄⟩ := hdeep Cg hC
  refine ⟨8 + n₁ + n₂ + n₃ + n₄ + ⌈Real.exp 15⌉₊, fun B d p q b H => ?_⟩
  have hfin := hfinC B Cg _ d p q b (by omega) H
  refine ⟨hfin, ?_⟩
  obtain ⟨-, -, hf1, -, hpq, h2q, hrk, hmin, hd, -, -, hts, h, -, hgap, -, h32, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b (by omega) H
  have H1 := countHyp_mono H (n₁ := n₁) (by omega)
  have H2 := countHyp_mono H (n₁ := n₂) (by omega)
  have H4 := countHyp_mono H (n₁ := n₄) (by omega)
  obtain ⟨hDS, hsig, hn, hq2, hrd, hlf, -, -, -, hg, -, hpr, h4, hsp, -⟩ := H
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have e := GlobalTheory.T.definiteUnitaryGroup_count_eq_mainTerm B d p ⟨hDS, hsig, by omega, hg, hpr, h4, hsp⟩ hfin
    rw [← e, sub_self, abs_zero]
    positivity
  have hn1 : 1 ≤ B.I.n := by omega
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  obtain ⟨-, -, hphe1, him, hre, -, hloc⟩ := hpt B d p q h hDS hsig hgap (by rw [hmin]; exact h120)
  obtain ⟨-, hv0, hvT, -⟩ := hflag B.I B.μf B.fund B.fund_spec p q hsig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using Nat.succ_le_of_lt hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hDS hloc
  have hI : Integrable (ph B d) (muInf B.I) := by
    have h0 := hint 0 le_rfl (fun v => Or.inr (by
      have h1 := h32 v
      rw [hrk v] at h1 ⊢
      have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq)
      have hqn : (q : ℝ) < B.I.n := by exact_mod_cast (by omega : q < B.I.n)
      have hn0 : (0 : ℝ) < B.I.n := by exact_mod_cast hn1
      have := mul_lt_mul_of_pos_left hqn (mul_pos hs hn0)
      nlinarith))
    simp only [zero_mul, Real.exp_zero, mul_one] at h0
    exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  obtain ⟨-, -, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hDS hI
  obtain ⟨-, Fc, -, -, -, hexp, hKi, hD, -⟩ := GlobalTheory.T.kernelB' B d h hDS hn1 hloc h32 hfin T hT
  obtain ⟨hsum, -⟩ := GlobalTheory.T.automorphicKernel_convergence_properties B d h hDS hn1 hloc h32
  obtain ⟨hmeas, hsplit⟩ := GlobalTheory.NearMeas.nearAbs_measurable_and_split B d hDS
  have hcl : Continuous (least B.I) := (GlobalTheory.LeastVar.least_variation_continuity B.I hn1).2.1
  set μ := (B.I.muA B.μf).restrict B.fund with hμ
  have : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hvT⟩
  have hM : MeasurableSet {x | tauStar B q b ≤ least B.I x} :=
    (isClosed_le continuous_const hcl).measurableSet
  have hvol : 0 < B.I.vol B.μf B.fund := ENNReal.toReal_pos hv0.ne' hvT.ne
  have hc0 : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hd.le hre
  have hmain : mainTerm B d = (∏ v, d v) * (B.e 1).re * B.I.vol B.μf B.fund := by
    unfold mainTerm AutInst.Dstar; ring
  have hm0 : 0 ≤ mainTerm B d := hmain ▸ mul_nonneg hc0 hvol.le
  have e1 : {x | tauStar B q b ≤ least B.I x} ∩ B.fund = {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x} :=
    Set.inter_comm _ _
  have e2 : {x | tauStar B q b ≤ least B.I x}ᶜ ∩ B.fund = GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b := by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, and_comm]
  have key := GlobalTheory.abs_integral_sub_const_mul_le_of_split B.I.GA μ {x | tauStar B q b ≤ least B.I x}
    (fun x => (kern B.I (phe B d) x x).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d)
    ((∏ v, d v) * (B.e 1).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d)
    (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d)
    ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) hM hKi.re
    (fun x => by
      simp only [hexp, Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_nonneg _)
    hmeas hc0 (mul_nonneg (Real.exp_pos _).le hm0) (mul_nonneg (Real.exp_pos _).le hm0) (by positivity)
    (fun x _ => by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hsplit x (hsum x x).1)
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      rw [Complex.sub_re, hphe1, Complex.re_ofReal_mul])
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₁ B d p q b hq H1)
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₂ B d p q b hq H2)
    (by rw [hμ, Measure.restrict_restrict hM.compl, e2]; exact hn₄ B d p q b hq H4)
  have hKD : ∫ x, (kern B.I (phe B d) x x).re ∂μ = (B.D : ℝ) := by
    have := integral_re hKi
    rw [hD] at this
    simpa using this
  have hU : (μ Set.univ).toReal = B.I.vol B.μf B.fund := by
    rw [hμ, Measure.restrict_apply_univ]; rfl
  have hP : (μ {x | tauStar B q b ≤ least B.I x}ᶜ).toReal ≤
      Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n)) * B.I.vol B.μf B.fund := by
    have h1 := hn₃ B p q hsig (by omega) hq2 hrd hlf
    unfold prob at h1
    rw [div_le_iff₀ hvol] at h1
    refine le_trans ?_ h1
    rw [hμ, Measure.restrict_apply hM.compl]
    refine ENNReal.toReal_mono ((measure_mono Set.inter_subset_right).trans_lt hvT).ne
      (measure_mono (Set.inter_subset_inter_left _ fun x hx => ?_))
    have hx' : ¬ tauStar B q b ≤ least B.I x := hx
    exact lt_trans (not_le.1 hx') (hts hq).1
  rw [hKD, hU, ← hmain] at key
  have hP' := mul_le_mul_of_nonneg_left hP hc0
  have hne : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 (by omega)
  have fin := GlobalTheory.abs_sub_le_exp_neg_sixteenth_mul (B.D : ℝ) (mainTerm B d) B.I.n B.I.f (by positivity) hm0 hne
    (by exact_mod_cast hf1) (by
      refine key.trans ?_
      unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
      simp only [neg_mul]
      rw [hmain] at *
      nlinarith [hP'])
  simpa only [neg_mul] using fin

end GlobalTheory.CountSum
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CapelliOfHC

open PI.UpqRep PI.HwUniqW GlobalTheory.BesselFrame GlobalTheory.SupNonzero

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

private theorem conj_blockW_exp_eq_exp_unitB {g : Mx k r} (hg : IsFrameW k r z g) (Z : Matrix (Fin k) (Fin k) ℂ) (t : ℝ) :
    g * blockW k r (NormedSpace.exp ((t : ℂ) • Z)) * g⁻¹ = NormedSpace.exp ((t : ℂ) •
      ∑ a, ∑ b, Z a b • Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b) := by
  have hunit : IsUnit g := by
    have hgg := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_eq ▸ hg.1)).2
    exact ⟨⟨g, g⁻¹, hgg.1, hgg.2⟩, rfl⟩
  have hs : ∀ a b : Fin k, Matrix.single a b (Z a b) = Z a b • Matrix.single a b (1 : ℂ) := fun a b => by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have hu : ∀ a b : Fin k, Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b =
      g * incl k r * Matrix.single a b (1 : ℂ) * ((incl k r)ᴴ * g⁻¹) := fun a b => by
    rw [unitB_eq, co_eq hg.1]
  rw [blockW_eq, ← exp_corner (incl k r) (incl k r)ᴴ incl_incl, ← Matrix.exp_conj g _ hunit]
  congr 1
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [hu, hs, Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, smul_smul]

theorem exists_eigen {u₀ : Fin k → ℝ} (hR : Qr.IsRepW k r z π) (h₀ : IsHCTypeW k r z u₀ π) :
    ∃ B : Fin k → (Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z] B ∧ ∃ v : W, v ≠ 0 ∧
      ∀ Y : ℂ, Formalism.REAL.qdet (Qr.EB π B) (Y + ((k : ℂ) - 1) / 2) v = (∏ s, (Y + (u₀ s : ℂ))) • v := by
  obtain ⟨g, hg, hU⟩ := h₀
  have hB : Q.IsFrameOf k r [z] (fun a => g *ᵥ bvec (bl k r a)) := isFrameOf hg
  refine ⟨fun a => g *ᵥ bvec (bl k r a), hB, ?_⟩
  have hgl := (Formalism.FourierDecayAlt.P.frame_general_linear W k r k z π _ hR hB).1
  refine qdet_eigen hU _ hgl ?_
  intro Z hZ v
  set X : Mx k r := ∑ a, ∑ b, Z a b • Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) a b with hXdef
  have hadj : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X := by
    simp only [hXdef, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.mul_sum, Finset.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, Formalism.FourierDecayAlt.P.QrCap.unitB_adj]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 := congrFun (congrFun hZ a) b
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at h1
    rw [h1, neg_smul]
  have hX1 : Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) X = X := by
    rw [Formalism.QuantumDeterminants.hpart1, hadj, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
    norm_num
  have hX2 : Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) X = 0 := by
    rw [Formalism.QuantumDeterminants.hpart2, hadj, add_neg_cancel, smul_zero]
  have hsum := Formalism.FourierDecayAlt.P.HermitianFormSums.ec_sum Formalism.FourierDecayAlt.P.elementary_lie_elements hR (Finset.univ : Finset (Fin k × Fin k))
    (fun p => Z p.1 p.2) (fun p => Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun a => g *ᵥ bvec (bl k r a)) p.1 p.2)
    (fun p => Formalism.FourierDecayAlt.P.QrD.frame_lie hB p.1 p.2) 0 (Formalism.FourierDecayAlt.P.SkewHermitianParts.inGl_zero z)
  rw [← Finset.univ_product_univ, Finset.sum_product] at hsum
  have hXlie : Formalism.FourierDecayAlt.P.QrD.InLieW k r z X := by
    have h := hsum.1.1
    rwa [hX1] at h
  have hec : ∑ a, ∑ b, Z a b • Qr.EB π (fun a => g *ᵥ bvec (bl k r a)) a b v = Formalism.FourierDecayAlt.P.QrD.dOp π X v := by
    have h := hsum.2
    have h' : Formalism.FourierDecayAlt.P.QrD.ecOp π X = Formalism.FourierDecayAlt.P.QrD.dOp π X := by
      rw [Formalism.FourierDecayAlt.P.QrD.ecOp, hX1, hX2, Formalism.FourierDecayAlt.P.SkewHermitianParts.dOp_zero, smul_zero, add_zero]
    rw [h'] at h
    rw [h]
    simp only [Finset.sum_product, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rfl
  have hexp : ∀ t : ℝ, g * blockW k r (NormedSpace.exp ((t : ℂ) • Z)) * g⁻¹ = NormedSpace.exp ((t : ℂ) • X) :=
    fun t => conj_blockW_exp_eq_exp_unitB hg Z t
  have hd := Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hR.1 hR.2 hXlie
  have hd' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (Formalism.FourierDecayAlt.P.QrD.dOp π X v) 0 := by
    have h2 := ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simpa [Function.comp_def] using h2
  rw [hec]
  convert hd' using 1
  funext t
  rw [hexp t]

theorem exists_isType : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u₀ : Fin k → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsHCTypeW k r z u₀ π → ∃ u : ℕ → ℝ, Q.IsType k r z π u := by
  intro k r Wp _ _ _ z π u₀ hz hT h₀
  obtain ⟨h1, hmul, hnorm, hcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT h₀
  have hR : Qr.IsRepW k r z π := ⟨⟨h1, hmul⟩, continuousOn_clm_apply.2 hcont⟩
  have ⟨g, hg, hU⟩ := h₀
  have hirr : ∀ S : Submodule ℂ Wp, (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    refine hU.2.2.2.2.2.1 S le_top ?_
    intro h hh v hv
    have hh' : hᴴ * h = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').1 hh.1
      rwa [Matrix.star_eq_conjTranspose] at this
    exact hS _ (Formalism.FourierDecayAlt.P.QrCap.emb_uw hg.1 hg.2.1 _ hg.2.2 hh') v hv
  obtain ⟨B, hB, v0, hv0, heig⟩ := exists_eigen hR h₀
  have hgl := (Formalism.FourierDecayAlt.P.frame_general_linear Wp k r k z π B hR hB).1
  have key : ∀ (w : ℂ) (v : Wp), Formalism.REAL.qdet (Qr.EB π B) w v =
      (∏ s, (w - ((k : ℂ) - 1) / 2 + (u₀ s : ℂ))) • v := by
    intro w
    set c : ℂ := ∏ s, (w - ((k : ℂ) - 1) / 2 + (u₀ s : ℂ)) with hc
    set S : Submodule ℂ Wp := LinearMap.ker (Formalism.REAL.qdet (Qr.EB π B) w - c • (1 : Module.End ℂ Wp)) with hSdef
    have hmem : ∀ v, v ∈ S ↔ Formalism.REAL.qdet (Qr.EB π B) w v = c • v := fun v => by
      rw [hSdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hv0S : v0 ∈ S := by
      rw [hmem]
      have := heig (w - ((k : ℂ) - 1) / 2)
      rwa [sub_add_cancel] at this
    have hstab : Qr.Stab (Qr.EB π B) S := by
      intro a b v hv
      rw [hmem] at hv ⊢
      have hcomm := Formalism.REAL.qDetCentral (Module.End ℂ Wp) k (Qr.EB π B) hgl w a b
      have := congrArg (fun T : Module.End ℂ Wp => T v) hcomm
      simp only [Module.End.mul_apply] at this
      rw [this, hv, map_smul]
    have hUW := Formalism.FourierDecayAlt.P.lie_stabilizer Wp k r z π B hz hT hR hB S hstab
    rcases hirr S hUW with hbot | htop
    · exact absurd (by rw [hbot] at hv0S; exact (Submodule.mem_bot ℂ).1 hv0S) hv0
    · intro v
      exact (hmem v).1 (htop ▸ Submodule.mem_top)
  refine ⟨fun i => if h : i - 1 < k then u₀ ⟨i - 1, h⟩ else 0, hU.1, ⟨h1, hmul⟩, continuousOn_clm_apply.2 hcont,
    hnorm, hirr, ?_⟩
  intro Bs hBs w v
  rw [(Formalism.FourierDecayAlt.P.frame_general_linear Wp k r k z π Bs hR hBs).2,
    GlobalTheory.capelli_det_frame_indep Wp k r z π Bs B hz hT hR hBs hB, key]
  congr 1
  refine Finset.prod_bij' (fun s _ => s.val + 1) (fun i hi => ⟨i - 1, by simp only [Finset.mem_Icc] at hi; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_Icc]
    omega
  · intro i _
    exact Finset.mem_univ _
  · intro s _
    exact Fin.ext (by simp)
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    show i - 1 + 1 = i
    omega
  · intro s _
    simp only [Nat.add_sub_cancel, s.isLt, dite_true, Fin.eta]
    ring

end GlobalTheory.CapelliOfHC

end
end

section


theorem _root_.GlobalTheory.T.binaryHermitianForm_represents_totallyPositive : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ a b n : K, star a = a → star b = b → star n = n → (∀ φ : K →+* ℂ, 0 < (φ a).re) → (∀ φ : K →+* ℂ, 0 < (φ b).re) → (∀ φ : K →+* ℂ, 0 < (φ n).re) → ∃ s t : K, a * (s * star s) + b * (t * star t) = n := by
  first | exact @GlobalTheory.BinaryRep.represents_totallyPositive | exact GlobalTheory.BinaryRep.represents_totallyPositive | (intros; apply GlobalTheory.BinaryRep.represents_totallyPositive <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions

theorem _root_.GlobalTheory.T.rankCondition_of_columns_equal_symmetricLevel : ∀ (D : D7), Formalism.L2.Forms.ColsTiedSym D → ∀ u : D.what₂.Word, StandardLattice.Mu0Tie D u := by
  first | exact @GlobalTheory.mu0Tie_of_colsTiedSym | exact GlobalTheory.mu0Tie_of_colsTiedSym | (intros; apply GlobalTheory.mu0Tie_of_colsTiedSym <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

theorem _root_.GlobalTheory.T.primitiveRows_map_bijective_columnLevel : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (Zs : DefSub A3.fam3.amb3) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs)), (R.toCx3 F).zs = Zs → HEq ((R.toCx3 F).data F.cr true) S1 → Function.Surjective ((A3.side3 F.P1 F.ψ1 Zs).Pq A3.A.μ0).mulVec ∧ Function.Surjective (S1.ι A3.A.μ0).mulVec := by
  first | exact @GlobalTheory.prim_rows_surjective | exact GlobalTheory.prim_rows_surjective | (intros; apply GlobalTheory.prim_rows_surjective <;> assumption)
end
