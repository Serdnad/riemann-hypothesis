module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMultiplicityWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle029
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle022
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle201
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNonzeroSectionWeightBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle226
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle088
import Formalism.LocalRingCardinality.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle944
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle809
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle829
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle815
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle128
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier

@[expose] public section

section



section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ValMultRun
section Algebra
open IsLocalRing IsDedekindDomain
open scoped NNReal
end Algebra
section Centre
open TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp)
open scoped NNReal
end Centre
section Component
open TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.TangentOrigin GlobalTheory.Vanishing.H0
open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp)
open GlobalTheory.AllWt (secZ exOf suppOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (genVal genPoint)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open scoped NNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
end Component
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic GlobalTheory.Vanishing in

theorem valuation_multiplicity_of_consecutive_run_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ValMult Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) (wtOf (dat p i) (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) 0) := by
  intro hP hGD hQ hS hT hL h2 h3 h4
  refine ((((_root_.GlobalTheory.T.exists_nonzero_section_weight_bound_alt_alt hP h2 h3 h4).and (_root_.GlobalTheory.T.exists_section_order_bound_hilbertSamuel_alt hP h2 h3 h4)).and (_root_.GlobalTheory.T.exists_phi_pos_of_centred_off_U0 hP h2 h3 h4)).and _root_.GlobalTheory.HSApp.wtBig_run_alt).imp
    fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C, hC, x0, hx⟩, ⟨C', hC', x1, hx1⟩⟩, ⟨C'', hC'', x2, hx2⟩⟩, ⟨C₃, hC₃, x3, hx3⟩⟩ := h
  refine ⟨C, hC, max (max x0 x1) (max x2 x3), fun x hx' hle ι p hp i hi Y hY Z => ?_⟩
  simp only [max_le_iff] at hle
  have hB := hx3 x hx' hle.2.2 ι p hp i hi
  have hP' := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨TF⟩ := @_root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt hP' _ _ _ _ _ _ _ Y.d.Xo₂ Y.d.c₂ hB.one_le
  obtain ⟨θ, hθ, -, hst⟩ := hx x hx' hle.1.1 ι p hp i hi Y hY Z TF
  have hJ := hx1 x hx' hle.1.2 ι p hp i hi Y hY Z TF _ (Or.inl rfl)
  have hD := hx2 x hx' hle.2.1 ι p hp i hi Y hY Z TF
  have hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by
    have h3 : Module.finrank ℚ (Fm.D x ι).host.E = 4 * (Fm.D x ι).R.ord :=
      (Fm.D x ι).host.finrank_cmField
    have h : 4 ≤ (Fm.D x ι).R.ord := (Fm.D x ι).host.four_le_n'
    omega
  have hCI : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY.1 hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF _⟩
  have hfree := _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP' hGD hQ hP.q15 hP.q16 hS hT.toroidalChartsForFan hL _ _ _ _ _ _ TF Z _ Y.U hY.1.geo
    hB.one_le _ (gaps_of_wtBig _ _ _ _ hB _ List.mem_cons_self).2 (hCI _)
  refine valMult_of_section TF.X Z Y.U (GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.1.geo) hCI ?_ hfree θ hθ
    fun y hy ν hν => ?_
  · rw [CompHt.uPrime]
    module
  obtain ⟨φ, hφ, hPh⟩ := hD y hy ν hν
  obtain ⟨w, hw, hwb⟩ := hJ y hy ν hν φ hPh
  refine ⟨w, hw, fun j hj j' hj' => ?_⟩
  obtain ⟨hw0, hwm⟩ := hwb j' hj'
  obtain ⟨zw, hzw⟩ := WithZero.ne_zero_iff_exists.1 hw0
  have ew : ν (H0.germ j' y (memTop y) hj' w) =
      ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zw)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [neg_neg, ofAdd_toAdd]; exact hzw.symm
  have bw := hwm _ ew
  by_cases h0 : ν (H0.germ j y (memTop y) hj θ) = 0
  · rw [h0, zero_pow three_ne_zero]
    exact zero_le'
  · obtain ⟨zt, hzt⟩ := WithZero.ne_zero_iff_exists.1 h0
    have et : ν (H0.germ j y (memTop y) hj θ) =
        ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zt)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      rw [neg_neg, ofAdd_toAdd]; exact hzt.symm
    have bt := hst y hy ν hν φ hPh j hj _ et
    have hle' : (3 * Multiplicative.toAdd zt : ℝ) ≤ (8 * Multiplicative.toAdd zw : ℝ) := by
      push_cast at bw bt ⊢
      linarith
    have hle'' : 3 * Multiplicative.toAdd zt ≤ 8 * Multiplicative.toAdd zw := by exact_mod_cast hle'
    rw [← hzt, ← hzw, ← WithZero.coe_pow, ← WithZero.coe_pow, WithZero.coe_le_coe, ← Multiplicative.toAdd_le,
      toAdd_pow, toAdd_pow]
    simpa using hle''
end GlobalTheory.ValMultRun
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ValMult Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) (wtOf (dat p i) (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) 0) := by
  first | exact @_root_.GlobalTheory.ValMultRun.valuation_multiplicity_of_consecutive_run_alt | exact _root_.GlobalTheory.ValMultRun.valuation_multiplicity_of_consecutive_run_alt | (intros; apply _root_.GlobalTheory.ValMultRun.valuation_multiplicity_of_consecutive_run_alt <;> assumption)
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SphNonSplit

theorem sphAU_of_not_split_m_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), ¬ IsSplitPl D.host w → D.nbc.sphAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _hCS hMI _hstar _hE hsp _hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hns
  set v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w with hv
  have hover : NG.OverPl w v := rfl
  rw [A.au.sph (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 _ w v hns hover]
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = X.nd.j i := by simp only [j]; omega
  have hvB := not_mem_bad D cf C tp hsp (X.nd.w i) j w v hover hns
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
    have key : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 →
        NG.HypOutside (M μ jj k1 k2).J (M μ jj k1 k2).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
      rintro μ jj k1 k2 rfl rfl
      exact hMI.hyp (X.nd.w i) j
    exact key _ _ _ _ (X.nd.mu_w i) hj.symm
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (hne P)
  have hry : (mlX M X i).real y ≠ 0 := fun h0 =>
    hy0 ((mlX M X i).real_inj (h0.trans (map_zero (mlX M X i).real).symm))
  have hT : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ := by
    rw [← (mlX M X i).real_range]; exact LinearMap.mem_range_self _ _
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.T.fixed_vector_of_mem_isotypic_component (mlX M X i).wt.ρ (F P)
    {κ | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {v} κ} (irr P) _ hy hry (by
      rintro κ ⟨hU, htr⟩
      have ht : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j))ᶜ κ := fun u hu =>
        htr u (by rintro rfl; exact hu hvB)
      have hJ : κ ∈ (mlX M X i).J := ((hyp κ ht).1).2 hU
      rw [hT.2 ⟨κ, hJ⟩, (hyp κ ht).2 hJ, Units.val_one, one_smul])
  have hsh : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 →
      ∀ s : SplitPlace D.host.E, s.v ∈ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j) → ∃ s₀ : SplitPlace D.host.E, s₀.v = s.v ∧
      ((∃ (r : ℕ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.LevelPara (M μ jj k1 k2).J (M μ jj k1 k2).χ s₀ r ξ) ∨
      ((∃ (g : ℕ) (_ : Fact g.Prime) (e : ℚ_[g] ≃+* s.w.adicCompletion D.host.E), Continuous e) ∧
        ∃ (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
          (ξ : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.LevelUni (M μ jj k1 k2).J (M μ jj k1 k2).χ s₀ r ψ₀ ξ ∧ NG.IsPsi0 s₀ ψ₀ ∧
          ∀ u : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
            Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1)) := by
    rintro μ jj k1 k2 rfl rfl s hs
    by_cases hg : s.v ∈ gPl D
    · obtain ⟨k, v', s₀, hw, hv'⟩ := GlobalTheory.PlaceUnderFixed.exists_splitPlace_under_plGw D s hg
      obtain ⟨ψ₀, ξ, hψ, hc, hU⟩ := hMI.uni (X.nd.w i) j k v' s₀ hw
      refine ⟨s₀, hv', Or.inr ⟨GlobalTheory.SplitTypeCompl.exists_padic_equiv D s hg, D.R.r, ψ₀, ξ, hU, hψ,
        GlobalTheory.AVGood.compAt_eq_one_of_tameAt s₀ _ (fun x hx hx' => ?_) ξ hc⟩⟩
      have loc_mul (a b : HChar D.host.E) (v : HeightOneSpectrum (𝓞 D.host.E))
          (x : (v.adicCompletion D.host.E)ˣ) :
          (a * b).loc v x = a.loc v x * b.loc v x := rfl
      rw [TupTied.tup, loc_mul, (cf.isMu0 j).tame _ x hx hx', tp.xi_tame _ _ x hx hx', one_mul]
    · obtain ⟨s₀, ξ, hv', -, hP⟩ := hMI.para (X.nd.w i) j s.v (hs.resolve_left hg)
      exact ⟨s₀, hv', Or.inl ⟨D.R.r, ξ, hP⟩⟩
  have hlev : GlobalTheory.RecT.Thread.LevelShape ({ (mlX M X i).wt with S := F P, irrS := irr P } : NG.AutRep D.host.E D.R.nV) :=
    ⟨(mlX M X i).J, (mlX M X i).χ, _, (mlX M X i).J_open, hyp, ⟨_, hy, hT, hry⟩, hsh _ _ _ _ (X.nd.mu_w i) hj.symm⟩
  have h0 : _root_.UpperTheory.One.M.New.Sph0 ({ (mlX M X i).wt with S := F P, irrS := irr P } : NG.AutRep D.host.E D.R.nV) v :=
    ⟨f, hfS, hf0, fun κ hU htr => hfix κ ⟨hU, htr⟩⟩
  exact _root_.UpperTheory.One.M.New.sphMk h0 fun _ =>
    GlobalTheory.RecT.Thread.good_of_levelShape UpperTheory.Zero.LLC.Pr.bz UpperTheory.Zero.LLC.Pr.zel _ hlev
end GlobalTheory.SphNonSplit
end
end
end
