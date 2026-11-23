module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle481
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

variable {n : ℕ}

def typesIn (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (A : Set (Fin n → ℝ)) : Submodule ℂ H :=
  ⨆ μ : A, (sSup {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H)

theorem typesIn_kStable (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (A : Set (Fin n → ℝ)) : Formalism.MainNotions.S.IsKStableOn ε σ (typesIn ε σ A) := by
  intro g hg v hv
  unfold typesIn at hv ⊢
  refine Submodule.iSup_induction _ (motive := fun v => σ g v ∈ _) hv (fun μ y hy => ?_) (by simp) ?_
  · rw [sSup_eq_iSup] at hy
    refine Submodule.iSup_induction _ (motive := fun z => σ g z ∈ _) hy (fun S w hw => ?_) (by simp) ?_
    · refine Submodule.iSup_induction _ (motive := fun w => σ g w ∈ _) hw (fun hS u hu => ?_) (by simp) ?_
      · exact Submodule.mem_iSup_of_mem μ (Submodule.mem_sSup_of_mem hS (hS.2.2.1 g hg u hu))
      · intro a b ha hb; rw [map_add]; exact add_mem ha hb
    · intro a b ha hb; rw [map_add]; exact add_mem ha hb
  · intro a b ha hb; rw [map_add]; exact add_mem ha hb

theorem typesIn_fd (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) {A : Set (Fin n → ℝ)} (hA : A.Finite) :
    FiniteDimensional ℂ (typesIn ε σ A) := by
  have hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := by
    rw [mir_isURepOn_iff, mir_UJset_eq]; exact hσ
  have hadm := GlobalTheory.PsCo.TrAdm.isAdmissibleSub_top n ε H σ hσ' hirr
  haveI : Finite A := hA.to_subtype
  have : ∀ μ : A,
      FiniteDimensional ℂ (sSup {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) :=
    fun μ => hadm μ
  exact Submodule.finiteDimensional_iSup _

theorem irrepAveragesFinDimSmooth_of_kTypes_and_polyAverages : SumTypes → PolyAvg → RangeFD := by
  intro hST hPA n ε H _ _ _ σ hσ hirr d
  obtain ⟨A, hAf, hA⟩ := hPA n ε d
  set M := typesIn ε σ A with hMdef
  have hMf : FiniteDimensional ℂ M := typesIn_fd ε σ hσ hirr hAf
  have hMK : Formalism.MainNotions.S.IsKStableOn ε σ M := typesIn_kStable ε σ A
  have hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := by
    rw [mir_isURepOn_iff, mir_UJset_eq]; exact hσ
  have hMD : M ≤ smD ε σ := fun v hv => CompanionTheory.D.gk.HC.mem_smD_of_isKFin hσ' hirr ⟨M, hMf, hv, hMK⟩
  refine ⟨M.comap (smD ε σ).subtype, ?_, ?_, ?_⟩
  · exact (Submodule.comapSubtypeEquivOfLe hMD).symm.finiteDimensional
  · intro k hk x hx
    show σ k (x : H) ∈ M
    exact hMK k (by rw [mir_Kset_eq]; exact hk) x hx
  · intro P hP u
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hMD]
    obtain ⟨S, hSf, hSK, hSP, hSA⟩ := hA H σ hσ u
    refine (hST n ε H σ hσ S hSf hSK).trans (sSup_le fun S' hS' => ?_) (hSP P hP)
    obtain ⟨hS'S, μ, hμ⟩ := hS'
    obtain ⟨v, hv, hv0, hvw⟩ := hμ.2.2.2.1
    have hμA : μ ∈ A := hSA μ v (hS'S hv) hv0 hvw
    exact le_iSup_of_le (⟨μ, hμA⟩ : A) (le_sSup ⟨le_top, hμ⟩)

end GlobalTheory.PsCo.PcEF

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem rangeFD_closed : RangeFD := irrepAveragesFinDimSmooth_of_kTypes_and_polyAverages @GlobalTheory.PsCo.PcEF.finDimStable_isSumOfKTypes @GlobalTheory.PsCo.PcEF.polyAverages_finiteWeightStableSubspace

end GlobalTheory.PsCo.PcEF
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.GaussModulus
open Formalism.L2.Host (atFin IsUnitAt)

namespace GlobalTheory.GaussModulus

theorem exists_int_witness {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (ha : a ≠ 0) (hE : ExpAt χ w a) :
    ∃ (y : 𝓞 E) (u : Eˣ), (u : E) = y ∧ y ∉ w.asIdeal ∧ y - 1 ∈ w.asIdeal ^ (a - 1) ∧ χ.locK w u ≠ 1 := by
  have hnot : ¬ χ.LevelLe w (a - 1) := fun h => by
    have := (hE (a - 1)).mp h
    omega
  have hlev : χ.LevelLe w a := (hE a).mpr le_rfl
  simp only [Formalism.L2.Host.HChar.LevelLe, not_forall] at hnot
  obtain ⟨x, hxu, hx1, hxχ⟩ := hnot
  have hxv : Valued.v (x : w.adicCompletion E) = 1 := hxu
  obtain ⟨y, hy⟩ := exists_int_approx w hxv.le a
  have hlt : WithZero.exp (-(a : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hyv' : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = 1 := by
    rw [← hxv]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [Valuation.map_sub_swap, hxv]
    exact lt_of_le_of_lt hy hlt
  have hyv : w.valuation E (y : E) = 1 := by rwa [← valued_algebraMap]
  have hy0 : (y : E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hyv
    exact zero_ne_one hyv
  refine ⟨y, Units.mk0 (y : E) hy0, rfl, ?_, ?_, ?_⟩
  · rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E)]
    exact hyv
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← valued_algebraMap]
    have e : algebraMap E (w.adicCompletion E) ((algebraMap (𝓞 E) E) (y - 1)) =
        (algebraMap E (w.adicCompletion E) (y : E) - (x : w.adicCompletion E)) + ((x : w.adicCompletion E) - 1) := by
      simp
    rw [e]
    refine Valuation.map_add_le _ ?_ hx1
    rw [Valuation.map_sub_swap]
    refine hy.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  · intro hχ
    apply hxχ
    set u : Eˣ := Units.mk0 (y : E) hy0 with hu
    have hau : ((atFin w u : (w.adicCompletion E)ˣ) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (y : E) := rfl
    have h1 : χ.loc w (x * (atFin w u)⁻¹) = 1 := by
      refine hlev _ ?_ ?_
      · show Valued.v (((x * (atFin w u)⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = 1
        rw [Units.val_mul, Units.val_inv_eq_inv_val, hau, map_mul, map_inv₀, hxv, hyv', inv_one, one_mul]
      · rw [Units.val_mul, Units.val_inv_eq_inv_val, hau]
        have hne : algebraMap E (w.adicCompletion E) (y : E) ≠ 0 := by
          intro h; rw [h, map_zero] at hyv'; exact zero_ne_one hyv'
        rw [show (x : w.adicCompletion E) * (algebraMap E (w.adicCompletion E) (y : E))⁻¹ - 1 =
            ((x : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) *
              (algebraMap E (w.adicCompletion E) (y : E))⁻¹ by field_simp]
        rw [map_mul, map_inv₀, hyv', inv_one, mul_one]
        exact hy
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [h1]
    exact hχ

end GlobalTheory.GaussModulus

end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_deRham_class_of_rigidified_extension :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → AllPrim (dp0 R) (𝟙 _) A →
    Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A) (x : G.RigExt),
      ∃ (c : primDR A) (x' : G.RigExt), IsCan t c x' ∧ G.rigToExt x' = G.rigToExt x :=
  GlobalTheory.PtExt.exists_isCan_rigToExt_eq
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.RatSecCycle

open GlobalTheory.Cartier.CartierDiv

theorem exists_sec_divOfSec_eq {X : Scheme.{0}} [IsIntegral X] (E : CartierDiv X) (hE : E.Eff) :
    ∃ (s : (toLB E).Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s),
      divOfSec (isLB_toLB E) s hs = E := by
  have h := presents_toLB E
  obtain ⟨s, hs1⟩ := h.exists_rat_eq (f := 1) (mem_sections.2 hE)
  have hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s :=
    (h.generatesAt_rat_iff s).1 (hs1 ▸ E.generatesAt_genericPoint one_ne_zero)
  refine ⟨s, hs, Presents.unique (presents_divOfRatSec (isLB_toLB E) _) ⟨isLB_toLB E,
    isRatSec_ratOfSec s hs, fun i x hx => ?_⟩⟩
  have e : ratOfSec s hs i = i.1.2 := Units.ext (by
    rw [val_ratOfSec (gen_mem hx), ← h.rat_mul s i (gen_mem hx), hs1, one_mul])
  rw [e]
  exact h.isEqn i x hx

end GlobalTheory.RatSecCycle


open GlobalTheory.Cartier.CartierDiv in
theorem GlobalTheory.ratSec_cycle_formula : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (r : M.ι → X.functionFieldˣ) (hr : IsRatSec M r), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfRatSec hM hr).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ _ _ hp n hn M hM P hP r hr
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  set D := divOfRatSec hM hr with hD
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨E, hE, hDE⟩ := GlobalTheory.T.exists_effective_cartierDivisor_add_effective X H hH D
  have key : ∀ E' : CartierDiv X, E'.Eff →
      interNum κ (structureModule X) (Fin.cons (toLB E') P : Fin (n + 1) → LB X) =
        ∑ᶠ w, E'.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
    intro E' hE'
    obtain ⟨s, hs, e⟩ := GlobalTheory.RatSecCycle.exists_sec_divOfSec_eq E' hE'
    have := GlobalTheory.T.intersectionNumber_globalSection_eq_sum_cycle κ X hp n hn (toLB E') (isLB_toLB E') P hP s hs
    rw [e] at this
    exact this
  have hv := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ X) (structureModule X) hp
    (d := n + 1) (by rw [QCoh.suppDim_structureModule]; exact hn)
  have hc : CechPic.cls (toLB (D + E)) (isLB_toLB (D + E)) =
      CechPic.cls M hM + CechPic.cls (toLB E) (isLB_toLB E) := by
    rw [← toPic_apply, ← toPic_apply, map_add (f := _), (presents_divOfRatSec hM hr).toPic_eq]
  have ha := hv.interNum_cons_of_cls_eq_add le_rfl hP (isLB_toLB (D + E)) hM (isLB_toLB E) hc
  rw [key _ hDE, key _ hE] at ha
  have hfin : ∀ F : CartierDiv X, Function.HasFiniteSupport
      (fun w => F.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) :=
    fun F => (F.finite_support_mult).subset (Function.support_mul_subset_left _ _)
  have e2 : (∑ᶠ w, (D + E).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) =
      (∑ᶠ w, D.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) +
        ∑ᶠ w, E.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
    simp only [mult_add, add_mul]
    exact finsum_add_distrib (hfin D) (hfin E)
  rw [e2] at ha
  linarith
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.productFormula_arithmeticCurve_rationalFunction : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ f : Y.functionField, f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal f y‖ := by
  first | exact @GlobalTheory.CurveProd.product_formula_curve | exact GlobalTheory.CurveProd.product_formula_curve | (intros; apply GlobalTheory.CurveProd.product_formula_curve <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.CosetFin

variable {H : Type} [Group H]

theorem finite_mk_mul (A K : Subgroup H) (x : H) (h : (K.map (MulAut.conj x).toMonoidHom).relIndex A ≠ 0) :
    {q : H ⧸ K | ∃ a ∈ A, q = (QuotientGroup.mk (a * x) : H ⧸ K)}.Finite := by
  set S := (K.map (MulAut.conj x).toMonoidHom).subgroupOf A
  haveI : S.FiniteIndex := ⟨h⟩
  haveI : Finite (A ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_range (fun t : A ⧸ S => (QuotientGroup.mk ((t.out : H) * x) : H ⧸ K))).subset ?_
  rintro q ⟨a, ha, rfl⟩
  refine ⟨(QuotientGroup.mk (⟨a, ha⟩ : A) : A ⧸ S), ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul S (⟨a, ha⟩ : A)
  simp only
  rw [hu]
  have hu2 : ((u : A) : H) ∈ K.map (MulAut.conj x).toMonoidHom := u.2
  obtain ⟨k, hk, hke⟩ := hu2
  rw [QuotientGroup.eq]
  have : ((u : A) : H) = x * k * x⁻¹ := by rw [← hke]; rfl
  simp only [Subgroup.coe_mul, this]
  have e : (a * (x * k * x⁻¹) * x)⁻¹ * (a * x) = k⁻¹ := by group
  rw [e]; exact K.inv_mem hk

theorem finite_mk_dcoset (K₀ K : Subgroup H) (hc : K.relIndex K₀ ≠ 0)
    (hconj : ∀ y : H, (K.map (MulAut.conj y).toMonoidHom).relIndex K₀ ≠ 0) (s : H) :
    {q : H ⧸ K | ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, q = (QuotientGroup.mk (k₁ * s * k₂) : H ⧸ K)}.Finite := by
  set T := K.subgroupOf K₀
  haveI : T.FiniteIndex := ⟨hc⟩
  haveI : Finite (K₀ ⧸ T) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_iUnion (fun t : K₀ ⧸ T => finite_mk_mul K₀ K (s * (t.out : H)) (hconj _))).subset ?_
  rintro q ⟨k₁, hk₁, k₂, hk₂, rfl⟩
  refine Set.mem_iUnion.2 ⟨(QuotientGroup.mk (⟨k₂, hk₂⟩ : K₀) : K₀ ⧸ T), k₁, hk₁, ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul T (⟨k₂, hk₂⟩ : K₀)
  rw [hu, QuotientGroup.eq]
  have hu2 : ((u : K₀) : H) ∈ K := u.2
  simp only [Subgroup.coe_mul]
  have e : (k₁ * s * k₂)⁻¹ * (k₁ * (s * (k₂ * ((u : K₀) : H)))) = ((u : K₀) : H) := by group
  rw [e]; exact hu2

theorem finite_mk_support (K₀ K : Subgroup H) (hc : K.relIndex K₀ ≠ 0)
    (hconj : ∀ y : H, (K.map (MulAut.conj y).toMonoidHom).relIndex K₀ ≠ 0) (φ : H → ℂ) (S : Finset H)
    (hS : ∀ g, φ g ≠ 0 → ∃ s ∈ S, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, g = k₁ * s * k₂) :
    {q : H ⧸ K | ∃ g, φ g ≠ 0 ∧ q = (QuotientGroup.mk g : H ⧸ K)}.Finite := by
  refine (S.finite_toSet.biUnion fun s _ => finite_mk_dcoset K₀ K hc hconj s).subset ?_
  rintro q ⟨g, hg, rfl⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
  exact Set.mem_biUnion hs ⟨k₁, hk₁, k₂, hk₂, rfl⟩

theorem relIndex_ne_zero_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : Finite (K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (y : G) :
    IsOpen ((U.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
  have e : ((U.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) = (fun g => y⁻¹ * g * y) ⁻¹' (U : Set G) := by
    ext g
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have : y⁻¹ * ((MulAut.conj y).toMonoidHom k) * y = k := by
        show y⁻¹ * (y * k * y⁻¹) * y = k; group
      rw [this]; exact hk
    · intro h
      refine ⟨_, h, ?_⟩
      show y * (y⁻¹ * g * y) * y⁻¹ = g; group
  rw [e]
  exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)

end GlobalTheory.CosetFin

namespace GlobalTheory.CosetFin

theorem commensurable_map_conj {G : Type} [Group G] {A B : Subgroup G} (h : A.Commensurable B) (y : G) :
    (A.map (MulAut.conj y).toMonoidHom).Commensurable (B.map (MulAut.conj y).toMonoidHom) := by
  exact ⟨h.1.map _, h.2.map _⟩

end GlobalTheory.CosetFin


open GlobalTheory.CosetFin in
theorem GlobalTheory.testProd_support_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      (Function.support (fun q : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) =>
        f q.out.1 * f' q.out.2)).Finite := by
  intro p _ G L f hf _ K' f' hf' _
  obtain ⟨-, -, -, S, hS⟩ := hf
  obtain ⟨hc', -, -, S', hS'⟩ := hf'

  have hA : {a : G.GAf ⧸ L.K.toSubgroup | ∃ g, f g ≠ 0 ∧ a = (QuotientGroup.mk g : G.GAf ⧸ L.K.toSubgroup)}.Finite := by
    refine finite_mk_support L.K.toSubgroup L.K.toSubgroup ?_ ?_ f S hS
    · rw [Subgroup.relIndex_self]; exact one_ne_zero
    · intro y
      exact relIndex_ne_zero_open_compact _ _ (isOpen_map_conj _ L.K.isOpen y) L.compact

  have hB : {b : Gr G 1 ⧸ K' | ∃ g, f' g ≠ 0 ∧ b = (QuotientGroup.mk g : Gr G 1 ⧸ K')}.Finite := by
    refine finite_mk_support (KHT p G.m G.n 1 G.Fw) K' hc'.1.relIndex_ne_zero ?_ f' S' hS'
    intro y
    have h1 := (GlobalTheory.heckeOperator_integral p G 1 Nat.one_pos).1 y
    exact ((commensurable_map_conj hc' y).trans h1).1.relIndex_ne_zero
  let ψ : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) →
      (G.GAf ⧸ L.K.toSubgroup) × (Gr G 1 ⧸ K') :=
    fun q => ((QuotientGroup.mk q.out.1 : G.GAf ⧸ L.K.toSubgroup), (QuotientGroup.mk q.out.2 : Gr G 1 ⧸ K'))
  have hψ : Function.Injective ψ := by
    intro q r hqr
    simp only [ψ, Prod.mk.injEq, QuotientGroup.eq] at hqr
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
    apply QuotientGroup.eq.2
    exact Subgroup.mem_prod.2 ⟨by simpa using hqr.1, by simpa using hqr.2⟩
  refine ((hA.prod hB).preimage hψ.injOn).subset ?_
  intro q hq
  have h1 : f q.out.1 ≠ 0 := left_ne_zero_of_mul hq
  have h2 : f' q.out.2 ≠ 0 := right_ne_zero_of_mul hq
  exact ⟨⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.map_centralizer_regular_twistedCentraliser : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r → regular₂ G γ → IsNrm G r γ δ z → (Subgroup.centralizer {γ}).map (carry G r z) = GlobalTheory.BCT.twCent (sigG G r) δ := by
  first | (exact @GlobalTheory.CarryCent.map_centralizer_carry) | (exact GlobalTheory.CarryCent.map_centralizer_carry) | (intros; apply GlobalTheory.CarryCent.map_centralizer_carry  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.twistedConj_of_twistedNormConj_hermitianTriple_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z δ' z' : Gr G r), 0 < r → regular₂ G γ → IsNrm G r γ δ z → IsNrm G r γ δ' z' → ∃ g : Gr G r, δ' = g⁻¹ * δ * sigG G r g ∧ ∀ y ∈ Subgroup.centralizer {γ}, carry G r z' y = g⁻¹ * carry G r z y * g := by
  first | (exact @GlobalTheory.NrmUnique.nrm_unique) | (exact GlobalTheory.NrmUnique.nrm_unique) | (intros; apply GlobalTheory.NrmUnique.nrm_unique <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.exists_coordinates_specialisedForm_prod_linearForms : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin G.D → Fin G.N → E) (hs : (G.baseChange E).IsGood s) (δ : ℕ) (f : MvPolynomial (Fin (G.D + 1) × Fin G.N) F), Split G.toTuple E s → SimpleAt G.toTuple δ f E s → ∃ (Co : Coord (G.baseChange E) hs δ) (c : E), c ≠ 0 ∧ spec s f = C c * ∏ p, lin (Co.y p) := by
  first | exact @GlobalTheory.HSShort.SplitCoord.exists_coord_spec_eq | exact GlobalTheory.HSShort.SplitCoord.exists_coord_spec_eq | (intros; apply GlobalTheory.HSShort.SplitCoord.exists_coord_spec_eq <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.det_rational_sections_eq_pow_product_linearForms : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → S.deepRank s ≤ (Finset.univ.filter fun k => (col k).j = S.D).card → ∃ γ : E, ∀ l : Fin S.N → E, aeval (join (fun i k => algebraMap F E (s i k)) l) (S.det c col) = γ * (∏ p, ∑ k, l k * Φ.y p k) ^ S.expo := by
  first | exact @GlobalTheory.HSShort.det_rational_eq_pow | exact GlobalTheory.HSShort.det_rational_eq_pow | (intros; apply GlobalTheory.HSShort.det_rational_eq_pow <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.multiformHeight_lowerBound : HtLow := by
  first | exact @GlobalTheory.HtLowProof.htLow | exact GlobalTheory.HtLowProof.htLow | (intros; apply GlobalTheory.HtLowProof.htLow <;> assumption)
end
