module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle902
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle903
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle892
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links




attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie

theorem fg_of_eval {R G W I : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup W] [Module R W] [Finite I]
    (L : Submodule R (G → W)) (y : I → G) (C : I → Submodule R W) (hC : ∀ c, (C c).FG)
    (hmem : ∀ f ∈ L, ∀ c, f (y c) ∈ C c) (hinj : ∀ f ∈ L, (∀ c, f (y c) = 0) → f = 0) : L.FG := by
  haveI : ∀ c, IsNoetherian R (C c) := fun c => isNoetherian_of_fg_of_noetherian _ (hC c)
  let ev : L →ₗ[R] ∀ c, C c :=
    { toFun := fun f c => ⟨f.1 (y c), hmem f.1 f.2 c⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun f hf => ?_
    exact Subtype.ext (hinj f.1 f.2 fun c => congrArg Subtype.val (congrFun hf c))
  haveI : IsNoetherian R L := isNoetherian_of_injective ev hev
  exact Module.Finite.iff_fg.1 inferInstance

section Eval

variable {D : D7} {S T : HSp D} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
  {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ}

theorem eq_zero_of_reps (B : Base S T) (t : Twist D Circle) {I : Type} {y : I → Bridge.Gf S}
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) {f : Bridge.Gf S → PolF D T.rank S.rank} (hf : f ∈ B.formsC t)
    (h0 : ∀ c, f (y c) = 0) : f = 0 := by
  have hlaw : B.HasLaw t f := ((B.mem_formsC).1 hf).2
  funext h
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := hy h
  have h1 := hlaw γ (y c) k
  rw [h0 c, map_zero, smul_zero, ← e] at h1
  exact h1

theorem mtLat_fg_of_reps [IsNoetherianRing O] (B : Base S T) (t : Twist D Circle) {I : Type} [Finite I] {y : I → Bridge.Gf S}
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) (hfg : ∀ c, (B.coefLat σ emb O (y c)).FG) :
    (B.mtLat σ emb O t).FG :=
  fg_of_eval _ y (fun c => B.coefLat σ emb O (y c)) hfg (fun _ hf c => ((B.mem_mtLat σ emb O).1 hf).2 (y c))
    fun _ hf h0 => eq_zero_of_reps B t hy ((B.mem_mtLat σ emb O).1 hf).1 h0

end Eval

theorem latFG_of_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ρ.LatFG := by
  intro D N X ρ hρ i j b k Q ψ hT
  obtain ⟨hg, ha, -⟩ := GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good D N X ρ hρ i j b k Q ψ hT
  have hc := hρ.classes i j b _ hg ha
  haveI : IsNoetherianRing (ρ.eOk i b k).range :=
    isNoetherianRing_of_surjective (X.Ok i k) _ (ρ.eOk i b k).rangeRestrict (ρ.eOk i b k).rangeRestrict_surjective
  have hB := hρ.base i j b
  refine mtLat_fg_of_reps _ _ hc.reps fun c => ?_
  refine (GlobalTheory.T.fockHarmonicLattice_fg_and_spans_value_space D _ _ _ _ _ _ _ _ _ hB.wt (fun τ => ?_) (hρ.isCoefRing_k i b k) ?_).1
  · have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  · classical
    have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
        IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
      intro V Λ hΛ
      haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
      refine ⟨?_⟩
      obtain ⟨s, hs⟩ := hΛ.1.fg
      apply eq_top_iff.mpr
      intro y _
      let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
        ∑ i, ∑ j, star (x i) * V.gram i j * y j
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
      have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
        exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
      let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
        carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
        zero_mem' := by refine ⟨0, ?_⟩; simp [f]
        add_mem' := by
          rintro x z ⟨b, hb⟩ ⟨c, hc⟩
          refine ⟨b + c, ?_⟩
          change (b : D.host.E) + c = _
          rw [hb, hc]
          simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
        smul_mem' := by
          rintro c x ⟨b, hb⟩
          refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
          simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          change star (c : D.host.E) * _ = _
          ring }
      have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
        intro x hx
        obtain ⟨b, hb⟩ := ha x hx
        exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
      have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
        apply (hΛ.2 _).2
        intro x hx
        have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
        obtain ⟨b, hb⟩ := hxP
        refine ⟨b, ?_⟩
        rw [hb]
        dsimp only [f, Pi.smul_apply]
        simp only [smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
        Submodule.subset_span hy
      have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
        (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
      change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
        ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
      rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
      exact this
    haveI : Submodule.IsFullLattice D.host.E (ρ.B i j b).F.ΛS := hfull _ _ hB.frame.sdS
    haveI : Submodule.IsFullLattice D.host.E
        ((ρ.B i j b).latAt (finPt (Vc D j) (ρ.rep i j b (ρ.tw i b k Q ψ) c))) :=
      Formalism.UG.P.csGlob_lattice (F := D.host.F) (ρ.B i j b).F.ΛS (Module.Finite.iff_fg.2 hB.frame.sdS.1.fg)
        (Submodule.IsFullLattice.span_eq_top (A := D.host.E) (M := (ρ.B i j b).F.ΛS)) _
    infer_instance

end GlobalTheory.SeriesTie

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.harmonic_polys_reach_small_field_coefficient_functions : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b (F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam), ∃ P ∈ (Y.Z.ρ.B i j b).valSpace, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) := by
  first | exact @GlobalTheory.IntExpOnto.onto | exact GlobalTheory.IntExpOnto.onto | (intros; apply GlobalTheory.IntExpOnto.onto <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.good_form_reading_eq_good_model_vector_evaluation : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∃ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      Y.Z.rd i j b x = (Y.Z.ν i j b)⁻¹ • (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) := by
  first | exact @GlobalTheory.SeriesTie.rd_good_model | exact GlobalTheory.SeriesTie.rd_good_model | (intros; apply GlobalTheory.SeriesTie.rd_good_model <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem GlobalTheory.TrivTwistLevel.levS_triv_iff_and_levFn : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q →
    ∀ x : GL (Fin (Vc D j).rank) (Lev.EAf D),
      (x ∈ lev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ↔
        x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t) ∧
          X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U) ∧
      ∀ (hx : x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t))
        (hu : X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U),
        ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x : ℂˣ) : ℂ) =
          ((levFn (X.R.βV j) (Lev.flagL (X.R.datVt j t)) x : ℂˣ) : ℂ) *
            Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨_, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  classical
  intro D X E Y i j b t h1 h2 x
  have hB := Y.Z.good.base i j b
  have hbo := GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hL : X.R.toLevCh.Is X.A3.A.μ0 := X.char.lev
  have hQe : (Y.Z.ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  have hce : (Y.Z.ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).Good := by
    have g0 := Twist.triv_good (D := D) (A := Circle) splitSet_empty
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hce]; exact g0.isOpen
    · rw [hce]; exact g0.rat
    · rw [hce]; exact g0.real
    · rw [hQe]; exact g0.split
    · rw [hce, hQe]; exact g0.unram
    · rw [hQe]; intro PP hPP; exact absurd hPP (Finset.notMem_empty _)
  have hAdm : (Y.Z.ρ.B i j b).admitted (Y.Z.ρ.tw i b 0 ∅ 1).Q := by
    rw [hQe]
    exact ⟨by rw [Finset.union_empty]; exact hB.places, Finset.disjoint_empty_right _⟩
  have ht : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Y.Z.ρ.tw i b 0 ∅ 1) t :=
    ⟨by rw [hce, mul_one]; exact h1, by rw [hQe, Finset.union_empty]; exact h2⟩
  obtain ⟨hPg, hQ, hcg, hxq⟩ := GlobalTheory.ConjTwist.Test.levS_chars hbo hL hB hψ hAdm ht
  have rV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have htW : (Vc D j).rank - (Wc D j).rank = D.R.t := by omega
  have eβ : (Y.Z.ρ.B i j b).F.βS = X.R.βV j := hbo.βS
  have ebo : blkOf ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).t =
      blkOf (n := (Vc D j).rank) (X.R.datVt j t).r (X.R.datVt j t).t := by
    show blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank) = blkOf D.R.r D.R.t
    rw [htW, rW]
  have eb2 : blk2 (n := (Vc D j).rank) ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r = blk2 (X.R.datVt j t).r := by
    show blk2 (Wc D j).rank = blk2 D.R.r
    rw [rW]
  have hpar : ∀ y, y ∈ parLev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ↔
      y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t) := by
    intro y
    rw [mem_parLev, mem_parLev, eβ, ebo, eb2, hPg, hQ]

  have hrt : ∀ y (hy : y ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t)),
      rTup (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) y =
        Y.Z.ρ.eG i j b (X.cG (rTup (X.R.βV j) (X.R.datVt j t) y)) := by
    intro y hy
    have hy' := (hpar y).2 hy
    funext PP
    obtain ⟨P, hP⟩ := PP
    have h' : P ∈ X.R.Pg := by rw [← hbo.Pg]; exact hP
    apply Units.ext
    ext a c
    have hg := Y.Z.pin.grp i j b (X.cG (rTup (X.R.βV j) (X.R.datVt j t) y)) P hP h' a c
    refine Eq.trans ?_ hg.symm
    have m1 := blockTri_blkOf_le _ _ (parLev_g hy' hP)
    have m2 := blockTri_blkOf_le _ _ (parLev_g hy h')
    have hz := X.cG.symm_apply_apply (rTup (X.R.βV j) (X.R.datVt j t) y)
    rw [hz]
    simp only [rTup]
    rw [upper_block_val_submatrix _ m1, upper_block_val_submatrix _ m2]
    simp only [Matrix.submatrix_apply]
    rw [eβ]
    rfl

  refine ⟨?_, ?_⟩
  · rw [mem_lev, hpar x]
    constructor
    · rintro ⟨hx, hr⟩
      refine ⟨hx, ?_⟩
      rw [hrt x hx] at hr
      exact ((Y.Z.tie i j b).U_eq _).1 hr
    · rintro ⟨hx, hu⟩
      refine ⟨hx, ?_⟩
      rw [hrt x hx]
      exact ((Y.Z.tie i j b).U_eq _).2 hu
  · intro hx hu
    have hmem : Y.Z.ρ.eG i j b (X.cG (rTup (X.R.βV j) (X.R.datVt j t) x)) ∈ (Y.Z.ρ.B i j b).G.P.H :=
      ((Y.Z.tie i j b).U_eq _).2 hu
    have hmem' : rTup (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x ∈
        ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).P.H := by
      rw [hrt x hx]; exact hmem
    have f1 : ext1 ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).P.H ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).P.chi
        (rTup (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x) =
        (Y.Z.ρ.B i j b).G.P.chi ⟨_, hmem⟩ := by
      rw [extendOne_of_mem _ hmem']
      congr 1
      exact Subtype.ext (hrt x hx)
    have f1' : ext1 (Lev.flagL (X.R.datVt j t)).P.H (Lev.flagL (X.R.datVt j t)).P.chi
        (rTup (X.R.βV j) (Lev.flagL (X.R.datVt j t)) x) = 1 := by
      rw [extendOne_of_mem _ (show _ ∈ (Lev.flagL (X.R.datVt j t)).P.H from Subgroup.mem_top _)]
      rfl
    have f2 : (∏ PP ∈ ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).Pg,
        ∏ c ∈ Finset.range ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).s,
          ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).cg (c + 1) PP
            (dBlk (blkOf ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).t) (c + 1)
              (redFn (Y.Z.ρ.B i j b).F.βS PP x))) =
        ∏ PP ∈ (Lev.flagL (X.R.datVt j t)).Pg, ∏ c ∈ Finset.range (Lev.flagL (X.R.datVt j t)).s,
          (Lev.flagL (X.R.datVt j t)).cg (c + 1) PP
            (dBlk (blkOf (Lev.flagL (X.R.datVt j t)).r (Lev.flagL (X.R.datVt j t)).t) (c + 1) (redFn (X.R.βV j) PP x)) := by
      refine Finset.prod_congr hPg fun PP hP => Finset.prod_congr rfl fun c _ => ?_
      have h' : PP ∈ X.R.Pg := hP
      rw [hcg _ PP h', ebo, eβ]
      rfl
    have f3 : (∏ PP ∈ ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).Q,
          ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).xq PP
            (dBlk (blk2 ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)).r) 1 (redFn (Y.Z.ρ.B i j b).F.βS PP x))) =
        ∏ PP ∈ (Lev.flagL (X.R.datVt j t)).Q,
          (Lev.flagL (X.R.datVt j t)).xq PP (dBlk (blk2 (Lev.flagL (X.R.datVt j t)).r) 1 (redFn (X.R.βV j) PP x)) := by
      refine Finset.prod_congr hQ fun PP hP => ?_
      have h' : PP ∈ X.R.Q t := hP
      rw [hxq PP h', eb2, eβ]
      rfl
    unfold levFn
    rw [f1, f1', f2, f3, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_one,
      (Y.Z.tie i j b).psiU_eq ⟨_, hu⟩ hmem]
    ring
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockReadForms

theorem fockRead_mem_formsC : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∀ (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
      (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) = X.geo.v₀ j (sg0 D X.A3.A) →
    ∀ (z : Bridge.Gf (Vc D j)), z ∈ Subgroup.center (Bridge.Gf (Vc D j)) →
    (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1) := by
  intro D X E Y i j b t hxi hQ y hlaw u hu z hz
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have hBo : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Twist.triv Circle ∅) t := by
    classical
    exact ⟨by rw [hxi]; exact (mul_one _).symm, by rw [hQ]; exact (Finset.union_empty _).symm⟩
  have hact := (GlobalTheory.CoefActIo.act_ioP hC hG hBo (Twist.triv_good splitSet_empty) htup).2
  have hio : Formalism.IndefR.FWT.IoExt X.R.toRealDat :=
    GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hval : ∀ w, X.R.ioP j (PiTensorProduct.tprod ℂ u) w ∈ (Y.Z.ρ.B i j b).valSpace := by
    intro w
    have hcV : (X.R.cV j).Is := hC.models.cV j
    obtain ⟨u', w₀, hu', -, hw⟩ := Formalism.IndefR.FWT.IsChosenExtremalVector.io _ (Y.Z.vec j) hio
    have huu : u' = u := funext fun ρ => Subtype.ext ((hu' ρ).trans (congrFun hu ρ).symm)
    rw [huu] at hw
    have hT := Scale.io_act hC.lev hC.thP hG hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)
    have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
    rcases hcV.2.2.2.2 ((harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
        (X.R.ioP j (PiTensorProduct.tprod ℂ u))) (fun h => by
        obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
        rw [map_mul, hcV.1 k hk, mul_one]
        rintro _ ⟨w, hw', rfl⟩
        rw [Submodule.mem_comap, hT a ha]
        exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
          (X.R.ioP j (PiTensorProduct.tprod ℂ u)) := by
        rw [Submodule.mem_comap, hw, ← hBo.delta]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact (h ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
        (X.R.ioP j (PiTensorProduct.tprod ℂ u)))

  have hx : (X.R.HV j t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
      (levEnv _ (X.R.βV j) (X.R.datVt j t)).J (levEnv _ (X.R.βV j) (X.R.datVt j t)).χ :=
    (hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)
  rw [Base.mem_formsC]
  refine ⟨fun h => hval _, fun γ h k => ?_⟩
  have hzc := Subgroup.mem_center_iff.1 hz
  have e1 : Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j)) * z =
      Bridge.ratF (Vc D j) γ * (h * z) * (k : Bridge.Gf (Vc D j)) := by
    simp only [mul_assoc]
    rw [← hzc]
  have h2 : Bridge.ratF (Vc D j) γ * (h * z) * ((1 : (levEnv _ (X.R.βV j) (X.R.datVt j t)).J) : Bridge.Gf (Vc D j)) =
      Bridge.ratF (Vc D j) γ * (h * z) := by
    rw [OneMemClass.coe_one]
    exact mul_one _
  have e2 : (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z)) =
      (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
    calc (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))
        = (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z) *
            ((1 : (levEnv _ (X.R.βV j) (X.R.datVt j t)).J) : Bridge.Gf (Vc D j))) := congrArg _ h2.symm
      _ = (((levEnv _ (X.R.βV j) (X.R.datVt j t)).χ 1 : ℂˣ) : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
          hx γ (h * z) 1
      _ = (1 : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
          congrArg (fun c : ℂ => c • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)))
            (by rw [MonoidHom.map_one, Units.val_one])
      _ = (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) := one_smul ℂ _
  calc X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j)) * z))
      = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z) * (k : Bridge.Gf (Vc D j)))) :=
        congrArg (fun g => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y g)) e1
    _ = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))) :=
        congrArg (X.R.ioP j (PiTensorProduct.tprod ℂ u)) (hlaw _ k)
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))) :=
        map_smul _ _ _
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z))) :=
        congrArg (fun v => (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • X.R.ioP j (PiTensorProduct.tprod ℂ u) v) e2
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          (Y.Z.ρ.B i j b).act (γ : GA D (Vc D j)) (X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) :=
        congrArg (fun v => (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • v) (hact _ _ _).symm

end GlobalTheory.FockReadForms

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.averaged_series_full_rank_of_complex_span_good : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), Comparison₂ hρ rd → (∀ i j b, Faithful (rd i j b)) → ∀ (E : IntegralHeckeForms.XD D) (i : D.ntw.Tw), (∀ j b, RatBase (rd i j b)) → (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b) → SpanGood rd i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  first | exact @GlobalTheory.RankDescent.fullRk_of_spanGood | exact GlobalTheory.RankDescent.fullRk_of_spanGood | (intros; apply GlobalTheory.RankDescent.fullRk_of_spanGood <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isLevelLift_of_isLevelLift_realisation : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : X.Γ) (κ : GA D (Wc D j)),
    Lev.IsLevelLift (Wc D j) (X.R.βW j) (X.R.datWp j X.R.triv) (X.R.eG g) κ →
    Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b (X.cG (X.R.eG g))) κ := by
  first | exact @GlobalTheory.TwistLiftW.isLevelLift_base_of_realisation_lift | exact GlobalTheory.TwistLiftW.isLevelLift_base_of_realisation_lift | (intros; apply GlobalTheory.TwistLiftW.isLevelLift_base_of_realisation_lift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j, 1 ≤ j → j ≤ D.R.m → (Y.S.A j).IsKsForm) ∧ ∀ i b P, P ∉ D.ntw.S0 i → ∃ u : (D.ntw.O i)ˣ, Y.H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u := by
  first | exact @GlobalTheory.TwUnit.isKsForm_and_unit | exact GlobalTheory.TwUnit.isKsForm_and_unit | (intros; apply GlobalTheory.TwUnit.isKsForm_and_unit <;> assumption)
end
