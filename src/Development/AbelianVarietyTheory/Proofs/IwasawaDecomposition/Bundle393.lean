module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRingActsFaithfullyOnLocalisedLattice
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle373
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle375
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStandardFactsOnLocalisationBase
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle374
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle239
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle249
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle371
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle369
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle311
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle003
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.exists_padicFiniteExt_containing_all_hecke_eigenvalues : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (E0 : PlEmb D.what₂), (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) → ∀ (j : ℕ) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ X : CoefIn D.what₂, X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∀ v k, GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k → ⨆ μ, (hKC (mt0 M) C.Q hR X j w v k).maxGenEigenspace μ = ⊤ := by
  first | exact @GlobalTheory.HeckeSplitField.exists_finExt_split | exact GlobalTheory.HeckeSplitField.exists_finExt_split | (intros; apply GlobalTheory.HeckeSplitField.exists_finExt_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.heckeEigenspace_ne_bot_every_localisation_point : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd)), ActHK B hs hd hL hAct → ∀ (i : LocT B) (x : XOf B i), heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x ≠ ⊥ := by
  first | exact @GlobalTheory.EigOcc.heckeEig_ne_bot | exact GlobalTheory.EigOcc.heckeEig_ne_bot | (intros; apply GlobalTheory.EigOcc.heckeEig_ne_bot <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.localBridges_at_placesOverResidueChar_of_large_coeff : ∀ (D : D7) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), F0.1 ≤ (X.Kx j w).1 → BrAt X j w := by
  first | exact @GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large | exact GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large | (intros; apply GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.heckeRing_acts_faithfully_on_localisedLattice : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B), MtLoc B (partCompl_of hs hd) → HeckeIntTw B → SemisimpleTw B → ActEx B (partCompl_of hs hd) := by
  first | exact @GlobalTheory.HeckeLocAct.actEx_of | exact GlobalTheory.HeckeLocAct.actEx_of | (intros; apply GlobalTheory.HeckeLocAct.actEx_of <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.liftedHeckeOperators_at_generators_commute : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) := by
  first | exact @GlobalTheory.HeckeLocCommute.hLC_commute | exact GlobalTheory.HeckeLocCommute.hLC_commute | (intros; apply GlobalTheory.HeckeLocCommute.hLC_commute <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.heckeOperators_on_localisation_space_semisimple : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X), HeckeStdPlain → (∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f) → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → SemisimpleTw (base M C hR X hS) := by
  first | exact @GlobalTheory.HeckeLocN.semisimpleTw_base | exact GlobalTheory.HeckeLocN.semisimpleTw_base | (intros; apply GlobalTheory.HeckeLocN.semisimpleTw_base <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.heckeStandardFacts_on_localisation_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) → HeckeStd0 (base M C hR X hS) := by
  first | exact @GlobalTheory.HeckeStdBase.heckeStd0_base | exact GlobalTheory.HeckeStdBase.heckeStd0_base | (intros; apply GlobalTheory.HeckeStdBase.heckeStd0_base <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.twistConductors_over_real_places_and_conj_stable : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), (∀ w, ¬ TwistedAt D w → C.Q w = ∅) → QOver C ∧ QConj C := by
  first | exact @GlobalTheory.HeckeLocN.CondConj.cond_over_conj | exact GlobalTheory.HeckeLocN.CondConj.cond_over_conj | (intros; apply GlobalTheory.HeckeLocN.CondConj.cond_over_conj <;> assumption)
end

section

set_option autoImplicit false

open Formalism.DegreeFormula MvPolynomial GlobalTheory.GoodMetric GlobalTheory.DomainDens

noncomputable section

namespace GlobalTheory.DomainDens

theorem coeff_charpolyRev_card {R : Type} [CommRing R] [Nontrivial R] {p : ℕ} (M : Matrix (Fin p) (Fin p) R) :
    M.charpolyRev.coeff p = (-1) ^ p * M.det := by
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Polynomial.revAt_le le_rfl, Nat.sub_self, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem chernTop_model_origin : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n), GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 = GlobalTheory.TrueCx.grassConst p q ^ Fintype.card ι := by
  intro ι _ p q n h
  have hc : ∀ τ : ι, chernPoly (fun u => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 p =
      C ((-1 : ℂ) ^ p) * (blockSym h τ).det := by
    intro τ
    rw [chernPoly, GlobalTheory.T.curvatureFormMatrix_boundedDomainModelMetric_at_zero ι p q n h τ, neg_neg, coeff_charpolyRev_card, map_pow, map_neg, map_one]
  have hs : (algebraMap ℝ ℂ ((-1 : ℝ) ^ p)) * (-1 : ℂ) ^ p = 1 := by
    rw [map_pow, map_neg, map_one, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have ha : aeval (fun x : ι × ℕ => chernPoly (fun u => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) x.1))⁻¹) 0 x.2)
      (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) = ∏ τ, (blockSym h τ).det ^ q := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, map_mul, aeval_X, aeval_C, hc τ, ← mul_assoc, MvPolynomial.algebraMap_apply, ← C_mul, hs, C_1,
      one_mul]
  have hn : n = Fintype.card ι * (p * q) := by
    rw [← h]; simp [Fintype.card_prod, Fintype.card_fin]
  have h1 : Fintype.card (Unit × Fin p × Fin q) = p * q := by simp [Fintype.card_prod, Fintype.card_fin]
  have e : (∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial)) =
      ((∏ i ∈ Finset.range p, (((q + i).factorial : ℝ) / i.factorial) : ℝ) : ℂ) := by push_cast; rfl
  simp only [chernTop]
  rw [ha, GlobalTheory.T.topDegreeFormCoeff_prod_blockSymbol_det_pow ι p q n h h1, GlobalTheory.T.topDegreeFormCoeff_blockSymbolDet_pow_cayley p q h1, e, ← Complex.ofReal_pow, Complex.ofReal_re, GlobalTheory.TrueCx.grassConst,
    div_pow, hn, pow_mul', div_eq_inv_mul]

end GlobalTheory.DomainDens
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem levCols_le_triv_and_finite : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  intro hF _ D G' _ _ Pl0 T A Ks _ _ _ R F _ hi _
  refine ⟨GlobalTheory.Mem.Th.EEat_le_triv R _, ?_⟩
  obtain ⟨U, hU, hJ⟩ := GlobalTheory.DefiniteEnd.exists_open_level (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))
  exact GlobalTheory.MultFinite.hcFinite hF hi ⟨U, hU, fun k hk hk' => by
    obtain ⟨h1, h2⟩ := hJ k hk
    have hm : k ∈ levS (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) := ⟨hk', h1⟩
    have hc : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 (R.levR F true))) k = 1 := congrArg Units.val h2
    obtain ⟨h3, h4⟩ := GlobalTheory.Mem.Th.principal_le_level (R.βY 0) (R.dat0 (R.levR F true)) (R.dat0 (R.levR F true)).P k hm
    exact ⟨h3, h4.trans hc⟩⟩

end GlobalTheory.Mem.SRe

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BesselIntegrable

theorem measure_le_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] {𝓕 K : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hK : ∀ n, ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k) : μ 𝓕 ≤ μ K := by
  rw [h.measure_eq_tsum K]
  refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hK n
  exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩

theorem norm_besChar {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) {A B : HSp D}
    {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (n : GA D B) : ‖besChar ψ d n‖ = 1 := by
  unfold besChar
  split_ifs with h
  · obtain ⟨a, b, -, -, e⟩ := h.choose_spec
    rw [e]
    exact hψ _
  · exact norm_one

theorem besInt : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, BesInt D := by
  intro hP D θ hθ ψ hψ A B ι hι d μ 𝓕 hq μN 𝓕N hμN h𝓕N s hs φ F hφ hF hA
  obtain ⟨-, a2, a3, a4, a5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, b2, b3, b4, b5, -, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have : Countable (NFlagQ B d.e) :=
    Function.Injective.countable (f := fun x : NFlagQ B d.e => (⟨x.1.1, x.2⟩ : GQ B))
      fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ B => z.1) h))
  have : SecondCountableTopology (NFlag B d.e) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨⟨K, hK, hcov⟩, -⟩ := GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D B d.ρ d.e d.e_iso
  have hfin : μN 𝓕N < ⊤ := (measure_le_of_cover _ μN h𝓕N hcov).trans_lt hK.measure_lt_top
  obtain ⟨C, hC⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ hF.1 hF.2
  obtain ⟨s', hs', hs'', -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  have hsc : Continuous s := by
    rw [show s = s' from funext fun h => (hs'' h _).1 (hs h)]
    exact hs'
  have hχ := (GlobalTheory.T.besselCharacter_generic_character_laws D ψ hψ A B ι hι d).2.2.1
  have hb : ∀ (h : GA D A) (n : NFlag B d.e), ‖star (φ h) * F ((n : GA D B) * s h * (d.y : GA D B)) *
      star (besChar ψ d (n : GA D B))‖ ≤ ‖φ h‖ * C := fun h n => by
    rw [norm_mul, norm_mul, norm_star, norm_star, norm_besChar hψ.1.2.1, mul_one]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hc : Continuous fun p : GA D A × NFlag B d.e => star (φ p.1) * F ((p.2 : GA D B) * s p.1 * (d.y : GA D B)) *
      star (besChar ψ d (p.2 : GA D B)) :=
    ((hφ.cont.comp continuous_fst).star.mul (hF.1.cont.comp
      (((continuous_subtype_val.comp continuous_snd).mul (hsc.comp continuous_fst)).mul continuous_const))).mul
      (hχ.comp continuous_snd).star
  refine ⟨fun h => Measure.integrableOn_of_bounded (M := ‖φ h‖ * C) hfin.ne
    (hc.comp (Continuous.prodMk_right h)).measurable.aestronglyMeasurable (.of_forall (hb h)), ?_⟩
  have hcusp : IsCuspForm θ A φ := ⟨hφ, hA.elim (fun h r C hC => absurd hC (h r C)) id⟩
  have hint := GlobalTheory.Mem.Th.petInt_of_cuspRapidDecay hP D θ hθ A μ 𝓕 hq (fun _ => 1) φ (isAutFunSm_const θ A 1) hcusp
  simp only [star_one, one_mul] at hint
  have : IsFiniteMeasure (μN.restrict 𝓕N) := isFiniteMeasure_restrict.2 hfin.ne
  refine Integrable.mono' ((hint.norm.mul_const C).mul_const (μN.real 𝓕N))
    (hc.stronglyMeasurable.integral_prod_right' (ν := μN.restrict 𝓕N)).aestronglyMeasurable (.of_forall fun h => ?_)
  exact norm_setIntegral_le_of_norm_le_const hfin fun n _ => hb h n

end GlobalTheory.Mem.BesselIntegrable
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.UpKeep3

section Abstract

theorem mem_span_of_op {K : Type} [Field K] {σ : K →+* ℂ} {V H : Type} [AddCommGroup V] [Module K V] [AddCommGroup H]
    [Module ℂ H] (j : V →ₛₗ[σ] H) {ι : Type} (b : ι → V) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    (C : H →ₗ[ℂ] H) (φ : V → V) (hC : ∀ z, C (j z) = j (φ z)) (v : H) :
    C v ∈ Submodule.span ℂ (Set.range fun z => j (φ z)) := by
  have hv : v ∈ Submodule.span ℂ (Set.range fun k => j (b k)) := hsp ▸ Submodule.mem_top
  have h : Submodule.span ℂ (Set.range fun k => j (b k)) ≤ (Submodule.span ℂ (Set.range fun z => j (φ z))).comap C := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show C (j (b k)) ∈ Submodule.span ℂ (Set.range fun z => j (φ z))
    rw [hC]
    exact Submodule.subset_span ⟨b k, rfl⟩
  exact h hv

theorem sum_apply_j {K : Type} [Field K] {σ : K →+* ℂ} {G V H : Type} [Group G] [Fintype G] [AddCommGroup V] [Module K V]
    [AddCommGroup H] [Module ℂ H] (j : V →ₛₗ[σ] H) (r : Representation K G V) (ρ : Representation ℂ G H)
    (hj : ∀ g z, j (r g z) = ρ g (j z)) (a : G → K) (z : V) :
    (∑ g, σ (a g) • ρ g) (j z) = j ((∑ g, a g • r g) z) := by

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hj]

theorem adjoint_comm {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) (π : H →ₗ[ℂ] H)
    (hπ : ∀ x, ‖π x‖ = ‖x‖) (ρ : E →ₗ[ℂ] E) (hρ : ∀ y, ‖ρ y‖ = ‖y‖) (h : ∀ y, Θ (ρ y) = π (Θ y)) (x : H) :
    ρ (LinearMap.adjoint Θ x) = LinearMap.adjoint Θ (π x) := by
  have hinj : Function.Injective ρ := (injective_iff_map_eq_zero ρ).2 fun y hy => by
    rw [← norm_eq_zero, ← hρ, hy, norm_zero]
  refine ext_inner_left ℂ fun v => ?_
  obtain ⟨y, rfl⟩ := LinearMap.surjective_of_injective hinj v
  rw [(LinearMap.norm_map_iff_inner_map_map ρ).1 hρ, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right, h,
    (LinearMap.norm_map_iff_inner_map_map π).1 hπ]

theorem mem_span_untwist {s : Bool} {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : ι → E) (z : E)
    (h : Tw.mk s z ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (f i))) : z ∈ Submodule.span ℂ (Set.range f) := by
  have hle : Submodule.span ℂ (Set.range fun i => Tw.mk s (f i)) ≤ Tw.sub s (Submodule.span ℂ (Set.range f)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (R := ℂ) (M := E) ⟨i, rfl⟩
  exact hle h

theorem adjoint_mem_span {K G V E H ι : Type} [Field K] {σ : K →+* ℂ} [Group G] [Fintype G] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (j : V →ₛₗ[σ] E) (b : ι → V) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (r : Representation K G V)
    (π : Representation ℂ G H) (hπ : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ) (Θ : E →ₗ[ℂ] H)
    (hρ : ∃ ρ : Representation ℂ G E, (∀ g z, j (r g z) = ρ g (j z)) ∧ (∀ g y, ‖ρ g y‖ = ‖y‖) ∧ ∀ g y, Θ (ρ g y) = π g (Θ y))
    (a l : G → K) (u : H) (ha : ∑ g, σ (a g) • π g u = u) (hl : ∑ g, σ (l g) • π g u = u) :
    LinearMap.adjoint Θ u ∈ Submodule.span ℂ (Set.range fun z => j ((∑ g, a g • r g) ((∑ g, l g • r g) z))) := by
  obtain ⟨ρ, hj, hn, hΘ⟩ := hρ
  have e1 : ∀ g, ρ g (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ (π g u) := fun g =>
    adjoint_comm Θ (π g) ((LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπ g)) (ρ g) (hn g) (hΘ g) u
  have fix : ∀ c : G → K, ∑ g, σ (c g) • π g u = u →
      (∑ g, σ (c g) • ρ g) (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ u := fun c hc => by
    conv_rhs => rw [← hc]

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, e1, map_sum, map_smul]
  have h := mem_span_of_op j b hsp ((∑ g, σ (a g) • ρ g) ∘ₗ (∑ g, σ (l g) • ρ g))
    (fun z => (∑ g, a g • r g) ((∑ g, l g • r g) z))
    (fun z => by rw [LinearMap.comp_apply, sum_apply_j j r ρ hj, sum_apply_j j r ρ hj]) (LinearMap.adjoint Θ u)
  rwa [LinearMap.comp_apply, fix l hl, fix a ha] at h

theorem untwist_adjoint {s : Bool} {E H ι κ : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) (u : H) (f : ι → E) (f' : κ → E)
    (hf : ∀ i, ∃ k, f i = f' k)
    (h : LinearMap.adjoint (Tw.map s Θ) (Tw.mk s u) ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (f i))) :
    LinearMap.adjoint Θ u ∈ Submodule.span ℂ (Set.range f') := by
  rw [Tw.adjoint_map] at h
  refine Submodule.span_mono ?_ (mem_span_untwist (s := s) f _ h)
  rintro _ ⟨i, rfl⟩
  exact (hf i).elim fun k hk => ⟨k, hk.symm⟩

theorem exists_lvl_coord {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (z : S.Forms) :
    ∃ x, S.gaOp r (lvlIdem P ψ) z = S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) := by
  obtain ⟨w, rfl⟩ := S.basis.equivFun.symm.surjective z
  have h : S.gaMat r (lvlIdem P ψ) *ᵥ w ∈ LinearMap.range (imE (S.gaMat r (lvlIdem P ψ))).mulVecLin := by
    rw [(image_idempotent_spec K _ _).2]
    exact ⟨w, rfl⟩
  obtain ⟨x, hx⟩ := h
  exact ⟨x, (GlobalTheory.Mem.LiftForms.gaOp_coord S r _ w).trans (congrArg _ hx.symm)⟩

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

theorem exists_rowForm {A : FamIn D.what₂.LL G Pl0 T D.R.m} {s : ℕ} (ok : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)
    (t : T) (z : (A.MtildeCSD t).Forms) :
    ∃ x, (A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X) ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (lvlIdem P ψ) z) =
      rowForm A P ψ t ((rE D A P ψ t).mulVec x) :=
  (exists_lvl_coord (A.MtildeCSD t) (A.leftGroupActionRight t) P ψ z).elim fun x hx =>
    ⟨x, (congrArg ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X)) hx).trans (GoodProj.rowForm_rE ok P ψ t x).symm⟩

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_lvl_fix (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (u : (R.toCx3 F).EE) (hu : u ∈ (R.toCx3 F).EEl true) :
    ∑ g, A3.A.fam.v0.embedding ((lvlIdem F.P1 F.ψ1).coeff g) • R.gEx F g u = u := by
  rw [(GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC).2] at hu
  refine GlobalTheory.RowsNonzero.sum_lvlIdem (R.gEx F) F.P1 F.ψ1 fun h => ?_
  have := (Submodule.mem_iInf _).1 hu h
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

theorem adjoint_mem_tw (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hH : Holds R F) (u : (R.toCx3 F).EE)
    (hu : u ∈ (R.toCx3 F).EEl true) :
    LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) u ∈ Submodule.span ℂ (Set.range fun z => (R.toCx3 F).jR A3.A.fam.μ0
      ((∑ g, (idemOf A3.A.X).coeff g • (A3.A.fam.R A3.A.fam.μ0).r g)
        ((∑ g, (lvlIdem F.P1 F.ψ1).coeff g • (A3.A.fam.R A3.A.fam.μ0).r g) z))) :=
  adjoint_mem_span (V := (A3.A.fam.R A3.A.fam.μ0).S.Forms) (E := (R.toCx3 F).FC A3.A.fam.μ0) ((R.toCx3 F).jR A3.A.fam.μ0)
    (Formalism.IndefR.Cx.CxData.bR (A := A3.fam3.amb3) A3.A.fam.μ0) (RealDat3.kFormR_of (F := F) hC.base.models A3.A.fam.μ0).2
    (A3.A.fam.R A3.A.fam.μ0).r (R.gEx F) hH.prim.gUnit.1 ((R.toCx3 F).Θ A3.A.fam.μ0)
    (GlobalTheory.RowsPosRed.exists_rho R F (s := 1) hH.ok hC.base.models hH.prim.gEquiv)
    (fun g => (idemOf A3.A.X).coeff g) (fun g => (lvlIdem F.P1 F.ψ1).coeff g) u
    (GlobalTheory.RowsPosRed.sum_idem_gEx R F (GlobalTheory.CoreOfWeak.core_of_weak R F hC hH.aux.ex).1 u) (sum_lvl_fix R F hC u hu)

theorem adjoint_mem_of_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hH : Holds R F) (w : R.HE.H)
    (hw : R.HE.e w ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) :
    LinearMap.adjoint (R.Th A3.A.μ0) w ∈ Submodule.span ℂ (Set.range fun x =>
      R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x))) :=
  untwist_adjoint (s := twAt D.what₂.embLL A3.A.v0) (R.Th A3.A.μ0) w
    (fun z => R.jX A3.A.μ0 ((A3.A.MtildeCSD A3.A.μ0).gaOp (A3.A.leftGroupActionRight A3.A.μ0) (idemOf A3.A.X)
      ((A3.A.MtildeCSD A3.A.μ0).gaOp (A3.A.leftGroupActionRight A3.A.μ0) (lvlIdem F.P1 F.ψ1) z))) _
    (fun z => (exists_rowForm hH.ok.ok2 F.P1 F.ψ1 A3.A.μ0 z).elim fun x hx => ⟨x, congrArg (R.jX A3.A.μ0) hx⟩)
    (adjoint_mem_tw R F hC hH (Tw.mk (twAt D.what₂.embLL A3.A.v0) w) hw)

end GlobalTheory.UpKeep3

namespace GlobalTheory.UpKeep3

theorem adjoint_mem_span_rowForm : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (uE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, (Y.Ish.jE y).1 = PiTensorProduct.lift (R.HE.e (uE y))) → ∀ y, LinearMap.adjoint (R.Th A3.A.μ0) (uE y) ∈ Submodule.span ℂ (Set.range fun x => R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x))) := by
  intro _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH uE hread y
  have hrow : R.HE.e (uE y) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) := by
    have h1 := (Y.Ish.jE y).2
    rw [hread y] at h1
    obtain ⟨m, hm, hm'⟩ := h1
    have e : m = R.HE.e (uE y) := (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).injective hm'
    rw [← e]
    exact hm
  exact adjoint_mem_of_row R F hP.char hH (uE y) hrow

end GlobalTheory.UpKeep3

end
end
