module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle539
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfSpanOfStrict
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueJointTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle540
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHighestWeightHarmonicOfFockLowestKType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle538
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle519
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle537
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.adicTopologicalBasis_exists_comp : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι) (A' : Type) [CommRing A'] (t : A →+* A') (I' : Ideal A) (κ : Type) (TB' : TopBasis t I' κ), I' = I.map s → ∃ TC : TopBasis (t.comp s) I (ι × κ), (∀ i j, TC.b (i, j) = t (TB.b i) * TB'.b j) ∧ ∀ i j x, TC.c (i, j) x = TB.c i (TB'.c j x) := by
  first | exact @GlobalTheory.BSP.topBasis_comp_exists | exact GlobalTheory.BSP.topBasis_comp_exists | (intros; apply GlobalTheory.BSP.topBasis_comp_exists <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.coeff_zero_map_pow_null_facts : ∀ (S A ι : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (tb : TopBasis s I ι), (∀ x, (∀ i, tb.c i x = 0) → x = 0) ∧ (∀ (n : ℕ) x, x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n) ∧ (IsHausdorff I S → ∀ a : ι → S, (∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) → ∃ x, ∀ i, tb.c i x = a i) := by
  first | exact @GlobalTheory.BSP.TopBasis.coeff_facts | exact GlobalTheory.BSP.TopBasis.coeff_facts | (intros; apply GlobalTheory.BSP.TopBasis.coeff_facts <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F := by
  first | exact @GlobalTheory.BSP.exists_discMap_of_pow_dvd | exact GlobalTheory.BSP.exists_discMap_of_pow_dvd | (intros; apply GlobalTheory.BSP.exists_discMap_of_pow_dvd <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_of_pow_le_of_pow_le_same_adicTopology : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι) (I' : Ideal S) (n m : ℕ), IsHausdorff I S → 0 < n → 0 < m → I ^ n ≤ I' → I' ^ m ≤ I → ∃ TB' : TopBasis s I' ι, TB'.b = TB.b ∧ TB'.c = TB.c := by
  first | exact @GlobalTheory.BSP.TopBasis.exists_of_pow_le_of_pow_le | exact GlobalTheory.BSP.TopBasis.exists_of_pow_le_of_pow_le | (intros; apply GlobalTheory.BSP.TopBasis.exists_of_pow_le_of_pow_le <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_adicTopologicalBasis_of_span_of_strict : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 → I.FG → IsAdicComplete I S → IsAdicComplete (I.map s) A → (∀ x : A, ∃ a : ι →₀ S, x - a.sum (fun i y => s y * b i) ∈ I.map s) → (∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (I ^ m).map s → ∀ i, a i ∈ I ^ n) → ∃ TB : TopBasis s I ι, TB.b = b := by
  first | exact @GlobalTheory.BSP.exists_topBasis_of_span_of_strict | exact GlobalTheory.BSP.exists_topBasis_of_span_of_strict | (intros; apply GlobalTheory.BSP.exists_topBasis_of_span_of_strict <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

theorem _root_.GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal : ∀ (A : Type) [Ring A] [Algebra ℂ A] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (X : Fin N → Fin N → A), Formalism.REAL.GlRel X → ∀ u : ℂ, Formalism.REAL.qdet X (u + ((N : ℂ) - 1) / 2) - (List.ofFn fun i : Fin c => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)) (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod ∈ Submodule.span ℂ {y : A | ∃ (p q : Fin N) (w : A), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} := by
  first | exact @GlobalTheory.CapHC.qdet_blocks_congr | exact GlobalTheory.CapHC.qdet_blocks_congr | (intros; apply GlobalTheory.CapHC.qdet_blocks_congr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.jointHighestWeightHarmonic_multiplicity_one_covering : ∀ {σ : Type} {k l N : ℕ} (z : Fin k × Fin N → σ) (y : Fin l × Fin N → σ), Function.Injective z → Function.Injective y → (∀ u w, z u ≠ y w) → (∀ s, (∃ u, z u = s) ∨ ∃ w, y w = s) → ∀ κ : Fin N → ℂ, ∃ Q₀ : MvPolynomial σ ℂ, ∀ (α : Fin k → ℂ) (β : Fin l → ℂ) (f : MvPolynomial σ ℂ), GlobalTheory.CompactHarm.JointTop z y κ α β f → ∃ r : ℂ, f = r • Q₀ := by
  first | exact @GlobalTheory.CompactHarm.jointTop_line | exact GlobalTheory.CompactHarm.jointTop_line | (intros; apply GlobalTheory.CompactHarm.jointTop_line <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.isJointHighestWeightHarmonic_slice_outer_variables : ∀ {σ σ₀ : Type} [DecidableEq σ] (ι : σ₀ → σ), Function.Injective ι → ∀ {k l N : ℕ} (z : Fin k × Fin N → σ₀) (y : Fin l × Fin N → σ₀) (κ : Fin N → ℂ) (α : Fin k → ℂ) (β : Fin l → ℂ) (P : MvPolynomial σ ℂ), GlobalTheory.CompactHarm.JointTop (ι ∘ z) (ι ∘ y) κ α β P → ∃ (s : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → MvPolynomial σ₀ ℂ) (g : (σ →₀ ℕ) → MvPolynomial σ ℂ), P = ∑ i ∈ s, MvPolynomial.rename ι (f i) * g i ∧ (∀ i ∈ s, GlobalTheory.CompactHarm.JointTop z y κ α β (f i)) ∧ ∀ i ∈ s, ∀ v ∈ (g i).vars, v ∉ Set.range ι := by
  first | exact @GlobalTheory.jointTop_slice | exact GlobalTheory.jointTop_slice | (intros; apply GlobalTheory.jointTop_slice <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P : PolF D m n), GlobalTheory.LowestKType.IsHarm w P → GlobalTheory.LowestKType.IsNHw w lam P → GlobalTheory.LowestKType.IsKHw w P → ∀ τ : D.what₂.Tau, ∃ (α : Fin (min (w.p τ) m) → ℂ) (β : Fin (m - w.p τ) → ℂ), GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ)) (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (fun a => lam τ a - (m : ℂ) / 2 + ((m - w.p τ : ℕ) : ℂ)) α β P := by
  first | exact @GlobalTheory.JointDict.jointTop_of_lowestKType | exact GlobalTheory.JointDict.jointTop_of_lowestKType | (intros; apply GlobalTheory.JointDict.jointTop_of_lowestKType <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι), B.P.Separable → IsFrame B e π S → ∀ (I I' : Finset ι), I ⊆ S → I' ⊆ S → ∀ u s : B.A, IsUnit u → IsUnit s → {M ∈ B.Lin | term B π I I' u s M ≠ 0}.Finite := by
  first | exact @GlobalTheory.UnitLemma.Desc.finite_term_ne_zero | exact GlobalTheory.UnitLemma.Desc.finite_term_ne_zero | (intros; apply GlobalTheory.UnitLemma.Desc.finite_term_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeOperatorsRationalForms_commute : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y), CommG D → HkComm D →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) k P k' P', HkIdx i k P → HkIdx i k' P' →
      GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) *
                   GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) =
        GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) *
          GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) ∧
      ∀ g : S.G, GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) * rhoKG S j (Y.rho j h1 h2) g =
        rhoKG S j (Y.rho j h1 h2) g * GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) := by
  first | exact @GlobalTheory.HkKs.opK_comm | exact GlobalTheory.HkKs.opK_comm | (intros; apply GlobalTheory.HkKs.opK_comm <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem integral_fderiv_chart_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a,
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      ∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν =
        ∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2 :=
  fun E _ _ _ a X _ ν k γ hk φ hb g =>
    integral_fderiv_chart_eq_of ν k γ (fun p => GlobalTheory.T.rapidlyDecreasingKernel_mul_adjointConjCoefficient E a X ν k γ hk p) φ hb g

end GlobalTheory.JSW
end
