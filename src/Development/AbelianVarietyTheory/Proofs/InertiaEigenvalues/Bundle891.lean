module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle879
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle825
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle551
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle596
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle880
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle881
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle882
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.DefiniteAbelian
open scoped CategoryTheory.Obj

namespace GlobalTheory.GoodDefinite

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem abLocus_eq_univ_of_definite (Xo : Moduli Dw l) (hq : Dw.q = 0) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X)
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x)
    (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) : abLocus G.G = Set.univ := by
  obtain ⟨m, hm, hw⟩ := exists_w0_relation H
  obtain ⟨b, hb⟩ := Spec.map_surjective (x ≫ Xo.s)
  let β : KA l →+* T.Fr := b.hom
  have hβ : x ≫ Xo.s = spMap β := hb.symm
  have : CharZero T.Fr := (RingHom.charZero_iff β.injective).1 inferInstance
  let ρ : T.Fr := β (baseKA l).ρ
  have hρ : ρ ^ 2 = -(H.d : T.Fr) := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hm' : (4 : T.Fr) * m = 1 + H.d := by exact_mod_cast hm
  let z : T.Fr := (1 + ρ) / 2
  have hz2 : 2 * z = 1 + ρ := mul_div_cancel₀ _ two_ne_zero
  have hz : z * z + m = z := mul_left_cancel₀ (show (4 : T.Fr) ≠ 0 by norm_num) (by
    linear_combination (2 * z + ρ - 1) * hz2 + hρ + hm')
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : T.V, algebraMap T.V T.Fr z₀ = z := by
    rcases ValuationRing.isInteger_or_isInteger T.V z with h | ⟨u, hu⟩
    · exact h
    · by_cases h0 : z = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      · refine ⟨1 - m * u, ?_⟩
        rw [map_sub, map_one, map_mul, map_natCast, hu]
        field_simp
        linear_combination -hz
  let L := AlgebraicClosure T.Fr
  let a : T.Fr →+* L := algebraMap T.Fr L
  have : CharZero L := (RingHom.charZero_iff a.injective).1 inferInstance
  have hdet := (Xo.univ.geom L (spMap a ≫ x) (a.comp β) (by rw [Category.assoc, hβ, sp_comp])).1
  have h₁ := actsBy_of_detCond Dw hq _ (spMap a ≫ x) _ (a z)
    (by rw [← map_ofNat a 2, ← map_mul, hz2, map_add (f := _), map_one]; rfl) hdet
  have h₂ := (actsBy_pull m₂.cart (m₂.act H.w0) (spMap a) _).1 ((actsBy_pull m₁.cart (m₁.act H.w0) (spMap a) _).2 h₁)
  have := G.semi.smooth
  have := G.semi.separated
  have := G.act.hom H.w0
  have h₃ : ActsBy G.G (G.act.act H.w0) (𝟙 _) z₀ := by
    refine actsBy_of_injective (a.comp (algebraMap T.V T.Fr))
      (a.injective.comp (IsFractionRing.injective T.V T.Fr)) _ _ ?_
    rw [Category.comp_id, ← sp_comp, RingHom.comp_apply, hz₀]
    exact h₂
  refine Set.eq_univ_of_forall fun p K _ _ t _ => ?_
  obtain ⟨j, hj⟩ := Spec.map_surjective t
  have h₄ := actsBy_baseChange (k := K) j.hom (𝟙 _) _ h₃
  have ht : spMap j.hom ≫ 𝟙 _ = t := (Category.comp_id _).trans hj
  rw [ht] at h₄
  obtain ⟨X⟩ := G.semi.fibres K t
  exact isProper_of_actsBy X (OAct.pullback t G.G G.act) H.d_prime hm hw _
    ((actsBy_pull (isGrpPullback_pullback G.G t) (pullback.lift_fst _ _ _) _ _).2 (by rwa [Category.id_comp]))

theorem good_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Good y := by
  intro E _ _ _ H Dw l Xo c hq T io y
  obtain ⟨G, t', m₁, m₂, -⟩ := y.2.2
  exact ⟨G, t', m₁, m₂, GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H Dw l Xo T _ G t' m₁ m₂
    (abLocus_eq_univ_of_definite Xo hq T _ G t' m₁ m₂)⟩

end GlobalTheory.GoodDefinite
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_pullback_section_to_levelCover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∃ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ := by
  first | exact @GlobalTheory.CovPull.exists_pull | exact GlobalTheory.CovPull.exists_pull | (intros; apply GlobalTheory.CovPull.exists_pull <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.BadSuppPf

theorem rank_le (D : D7) (i : Fin D.R.m) : (Wc D i).rank ≤ (Vc D i).rank := by
  rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]
  exact r_le_V i

theorem badSupp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ P hP e f hPf k hk hnot
  classical
  have hv := hL.thP.vP i t
  have hθ := GlobalTheory.VecTheta.isThetaFunO_thPVec hv
  obtain ⟨-, e', he', hth⟩ := hv
  obtain ⟨cV, hBV⟩ := hL.lev.βV i
  obtain ⟨cW, hBW⟩ := hL.lev.βW i
  rw [one_pow] at hBV hBW
  have hsdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βV i)
  have hsdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βW i)
  have hdat : (fun x : WO (Vc D i) (Wc D i) => if IsHalf (cA D e') x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) *
          omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
        else 0) = GlobalTheory.FinZeta.levDatum (Vc D i) (Wc D i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t) (R.xiR t) e' := by
    funext x
    simp only [GlobalTheory.FinZeta.levDatum, GlobalTheory.Survey.LevelVectorSizeBounds.omegaG_triv R i]
  rw [hdat] at hth
  obtain ⟨hkf, hk1⟩ := GlobalTheory.SuppLocal.suppF_local D (Wc D i) P e f k hPf hk
  have hZ : ∀ PP, PP ∈ R.Pg ∪ R.Q t ↔ PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ R.Q t := fun PP => Finset.mem_union
  have hsb := GlobalTheory.FinZeta.isSBHalf_levDatum D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv)
    (R.Q t) (R.xiR t) (R.Pg ∪ R.Q t) e' hsdV hsdW hBV.1 hBW.1 he'
  have horth := GlobalTheory.ThetaOrth.orth D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hF i t).datum (R.ΛV i) (R.ΛW i) hsdV hsdW
    (R.Pg ∪ R.Q t) e' he' (R.vacP i) _ (R.vP i t) hsb hth hθ μ 𝓕 hμ k hkf (fun x hx => by
      by_contra hx'
      obtain ⟨k', hk', hag⟩ := GlobalTheory.T.mem_level_of_levelDatum_ne_zero_translate D (Vc D i) (Wc D i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
        (R.xiR t) (R.Pg ∪ R.Q t) e' hsdW hBW.1 (rank_le D i) rfl he' hZ k hkf x hx hx'
      apply hnot
      have hlo := (GlobalTheory.FinZeta.LevelOff.level_offS D (Wc D i) (R.βW i) (R.ΛW i) (R.datWp i R.triv) ((R.Pg ∪ R.Q t).image (fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) hBW
        (fun PP hPP => Finset.mem_image_of_mem _ (by
          rcases hPP with h | h
          · exact Finset.mem_union_left _ h
          · exact absurd h (Finset.notMem_empty _)))).2.1 k hkf
      refine hlo.2 ⟨⟨k', hk', fun v hvS => ?_⟩, fun v hvS => ?_⟩
      · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hvS
        exact hag PP hPP
      · have hne : v ≠ P.under (𝓞 D.host.F) := fun h => hvS (h ▸ Finset.mem_image_of_mem _
          (hP.elim (fun h => Finset.mem_union_left _ h) (fun h => Finset.mem_union_right _ h)))
        rw [hk1 v hne]
        exact Subgroup.one_mem _)
  have h0 : thetaIP μ 𝓕 (R.ωP i t (1, k) (R.vP i t)) (R.vP i t) = 0 := by
    have h1 : Formalism.IndefR.Lift.pet μ 𝓕 (R.ωP i t (1, k) (R.vP i t)) (R.vP i t) = 0 := horth
    unfold Formalism.IndefR.Lift.pet at h1
    unfold thetaIP
    have h2 : (fun w => star (R.ωP i t (1, k) (R.vP i t) w) * R.vP i t w) =
        fun w => starRingEnd ℂ (R.ωP i t (1, k) (R.vP i t) w * starRingEnd ℂ (R.vP i t w)) := by
      funext w; simp [mul_comm]
    rw [h2, integral_conj, h1, map_zero]
  unfold coef
  rw [h0, zero_div]

end GlobalTheory.BadSuppPf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult



namespace GlobalTheory.SeriesTie.LevKProof

variable {D : D7}

theorem blkOf_zero_of_le {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

theorem secondBlockIndex_eq_zero_of_dim_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

theorem mem_blockTriangular_singleBlock_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [secondBlockIndex_eq_zero_of_dim_le h] at hik
  exact absurd hik (lt_irrefl _)

end GlobalTheory.SeriesTie.LevKProof

namespace GlobalTheory.SeriesTie


open LevKProof in
theorem levK_eq_levG_triv : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw}, RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG ρ hp i j b
  unfold Setup.levK levG
  rw [hp.frT]
  congr 1
  have hr : (Wc D j).rank ≤ D.R.r := (FWT.rank_Wc j).le
  have hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (flag1L (ρ.B i j b).G.levT) =
      parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv) := by
    unfold parLev
    have hP : (flag1L (ρ.B i j b).G.levT).Pg = (Rl.datWp j Rl.triv).Pg := hp.Pg i j b
    have hb : (blkOf (flag1L (ρ.B i j b).G.levT).r (flag1L (ρ.B i j b).G.levT).t : Fin (Wc D j).rank → ℕ) =
        blkOf (Rl.datWp j Rl.triv).r (Rl.datWp j Rl.triv).t :=
      (blkOf_zero_of_le le_rfl).trans (blkOf_zero_of_le hr).symm
    have hb2 : (blk2 (flag1L (ρ.B i j b).G.levT).r : Fin (Wc D j).rank → ℕ) = blk2 (Rl.datWp j Rl.triv).r :=
      (secondBlockIndex_eq_zero_of_dim_le le_rfl).trans (secondBlockIndex_eq_zero_of_dim_le hr).symm
    rw [hP, hb, hb2]
    rfl
  have h1 : (flag1L (ρ.B i j b).G.levT).P.H = ⊥ := rfl
  have h2 : (Rl.datWp j Rl.triv).P.H = ⊥ := rfl

  have key : ∀ (x : GL (Fin (Wc D j).rank) (Lev.EAf D)) (PP : Pl D.host.E) (e1 : PP ∈ (flag1L (ρ.B i j b).G.levT).Pg)
      (e2 : PP ∈ (Rl.datWp j Rl.triv).Pg) (a c : Fin (Wc D j).rank),
      (rTup (Rl.βW j) (flag1L (ρ.B i j b).G.levT) x ⟨PP, e1⟩).val a c =
        (rTup (Rl.βW j) (Rl.datWp j Rl.triv) x ⟨PP, e2⟩).val
          (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) := by
    intro x PP e1 e2 a c
    unfold rTup
    erw [upper_block_val_submatrix _ (mem_blockTriangular_singleBlock_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_singleBlock_of_le le_rfl _)]
    rfl
  have hiff : ∀ x : GL (Fin (Wc D j).rank) (Lev.EAf D),
      rTup (Rl.βW j) (flag1L (ρ.B i j b).G.levT) x = 1 ↔ rTup (Rl.βW j) (Rl.datWp j Rl.triv) x = 1 := by
    intro x
    constructor
    · intro h
      funext PP
      apply Units.ext
      ext a c
      have e1 : PP.1 ∈ (flag1L (ρ.B i j b).G.levT).Pg := by
        show PP.1 ∈ (ρ.B i j b).G.Pg
        rw [hp.Pg i j b]
        exact PP.2
      have hk := key x PP.1 e1 PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)
      rw [h] at hk
      refine hk.symm.trans ?_
      simp [Matrix.one_apply, Fin.ext_iff]
      erw [Matrix.one_apply]
      simp [Fin.ext_iff]
      rfl
    · intro h
      funext PP
      apply Units.ext
      ext a c
      have e2 : PP.1 ∈ (Rl.datWp j Rl.triv).Pg := by
        show PP.1 ∈ Rl.Pg
        rw [← hp.Pg i j b]
        exact PP.2
      have hk := key x PP.1 PP.2 e2 a c
      rw [h] at hk
      refine hk.trans ?_
      simp [Matrix.one_apply, Fin.ext_iff]
      rfl
  ext x
  change (x ∈ parLev _ _ _ _ ∧ rTup _ _ x ∈ _) ↔ (x ∈ parLev _ _ _ _ ∧ rTup _ _ x ∈ _)
  rw [hpar, h1, h2, Subgroup.mem_bot, Subgroup.mem_bot, hiff]

end GlobalTheory.SeriesTie
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalLevel

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (h : r = n) (g : GL (Fin n) κ) :
    upperLeftBlock hr g = 1 ↔ g = 1 := by
  subst h
  have hg : g ∈ blockTri (κ := κ) (blk2 r) := fun i j hij => by
    simp [blk2, i.2, j.2] at hij
  constructor
  · intro h1
    apply Units.ext
    ext i j
    have := congrArg (fun u : GL (Fin r) κ => (u : Matrix (Fin r) (Fin r) κ) i j) h1
    simp only [upper_block_val_submatrix hr hg, Matrix.submatrix_apply] at this
    have ei : Fin.castLE hr i = i := Fin.ext rfl
    have ej : Fin.castLE hr j = j := Fin.ext rfl
    rw [ei, ej] at this
    simpa using this
  · rintro rfl
    exact blockDiagonalExtendByOnePrimeField_one _ _

theorem mem_lev_whole {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D))
    (L : LevDat D.host.E ℂ n) (hr : L.r = n) (hQ : L.Q = ∅) (hP : L.P.H = ⊥) (x : GL (Fin n) (Lev.EAf D)) :
    x ∈ lev D.sp.cm J β L ↔ x ∈ UA D.sp.cm J ∧ x ∈ St β ∧ ∀ PP ∈ L.Pg, redFn β PP x = 1 := by
  have h0 : ∀ a : Fin n, blkOf L.r L.t a = 0 := fun a => by
    unfold blkOf
    rw [if_pos (by rw [hr]; exact a.2)]
  rw [mem_lev, mem_parLev, hP, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨h1, h2, -, -⟩, h3⟩
    exact ⟨h1, h2, fun PP hPP => (upperLeftBlock_eq_one_iff_of_mem_blockTri L.hr hr _).1 (congrFun h3 ⟨PP, hPP⟩)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2, fun PP _ i j hij => ?_, fun PP hPP => ?_⟩, funext fun PP => (upperLeftBlock_eq_one_iff_of_mem_blockTri L.hr hr _).2 (h3 PP.1 PP.2)⟩
    · rw [h0, h0] at hij
      exact absurd hij (lt_irrefl 0)
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)

theorem levK_eq_levG : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : GlobalTheory.SeriesTie.Setup D.ntw}, GlobalTheory.SeriesTie.RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG ρ hpin i j b
  show Lev.levG (Wc D j) (ρ.B i j b).F.βT (Lev.flag1L (ρ.B i j b).G.levT) = _
  rw [hpin.frT i j b]
  unfold Lev.levG
  congr 1
  ext x
  rw [mem_lev_whole _ _ _ rfl rfl rfl, mem_lev_whole _ _ _ (FWT.rank_Wc j).symm rfl rfl]
  have hg : (Lev.flag1L (ρ.B i j b).G.levT).Pg = (Rl.datWp j Rl.triv).Pg := hpin.Pg i j b
  rw [hg]

end GlobalTheory.PrincipalLevel
end

section

open scoped TensorProduct

namespace GlobalTheory.EvaluationSum

open GlobalTheory.SeriesTie

theorem evK_eq_sum {D : Formalism.BasicNotions.D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Γ Pl0 I0 (List Nat) T (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D))]
    {Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks}
    {cG : MulEquiv (Formalism.L2.DIV.G0 (Formalism.IndefR.Links.LevCh.Pg (Formalism.IndefR.Links.RealDat.toLevCh (Formalism.IndefR.Links.RealDat3.toRealDat Rl))) (Formalism.BasicNotions.Ranks.r (Formalism.BasicNotions.D7.R D))) (Formalism.BasicNotions.G0g (Formalism.BasicNotions.D7.nd D))}
    {S : Formalism.IndefR.NX.RatDat (Formalism.BasicNotions.D7.ntw D)} (YS : Formalism.IndefR.NX.NExpRealS Rl cG S)
    (v₀ : (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) → (σ : RingHom (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Complex) → Formalism.IndefR.Mult.DSModel.Vec (Formalism.IndefR.Links.RealDat.MW (Formalism.IndefR.Links.RealDat3.toRealDat Rl) j σ))
    {ρ : GlobalTheory.SeriesTie.Setup (Formalism.BasicNotions.D7.ntw D)} (hρ : GlobalTheory.SeriesTie.Setup.Good ρ)
    (i : Formalism.BasicNotions.NTw.Tw (Formalism.BasicNotions.D7.ntw D)) (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) (b : Bool)
    (t : TensorProduct (Formalism.IndefR.NX.RatDat.Ks S) (Formalism.IndefR.NX.KB S i b) (Formalism.IndefR.NX.FmK S ((j : ℕ) + 1))) :
    ∃ (n : ℕ) (a : Fin n → Formalism.IndefR.NX.KB S i b) (x : Fin n → Formalism.IndefR.NX.FmK S ((j : ℕ) + 1)),
      GlobalTheory.SeriesTie.evK YS v₀ hρ i j b t =
        ∑ k : Fin n, GlobalTheory.SeriesTie.Setup.e ρ i b (a k) • GlobalTheory.SeriesTie.evW YS v₀ j (x k).val := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a f => exact ⟨1, fun _ => a, fun _ => f, by simp [evK_tmul]⟩
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨n₁, a₁, x₁, e₁⟩ := h₁
    obtain ⟨n₂, a₂, x₂, e₂⟩ := h₂
    refine ⟨n₁ + n₂, Fin.append a₁ a₂, Fin.append x₁ x₂, ?_⟩
    rw [map_add (f := _), e₁, e₂, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

end GlobalTheory.EvaluationSum
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover

namespace GlobalTheory.FibreIdem

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem chi_eq_one_of_finPart : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A), IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := GlobalTheory.T.openKernel_ideleCharacter_trivial_finitePart_one

theorem chi_eq_one_of_cong : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := GlobalTheory.T.onePlaceTwist_trivial_on_congruent_units

theorem char_root_eq_one' (V : HSp D) {A : Type} [CommGroup A] (c : (AE D)ˣ →* A) (N : ℕ) (hN : Odd N)
    (hF : ∀ a, c (idF D a) = 1) (hinf : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1)
    (hcong : ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1)
    (g : GA D V) (x : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hg : ∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) : c x = 1 := by
  obtain ⟨w, hw, hwe⟩ := hg
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hwe
  have hn := GlobalTheory.RecDict.det_finHom_norm V g
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  have hcY : c Y = 1 := hcong Y ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩ ⟨p, hp, hY2 ▸ hpe⟩
  have hdet : (finHom V g).1.det = finPart D (matHom V g).1.det := ((finPart D).map_det _).symm
  have hxf : finPart D (x : AE D) =
      (finHom V g).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hdet, ← GlobalTheory.DetRootCong.finPart_sigR, ← RingHom.map_mul]
    exact congrArg _ hx
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom (x * Y⁻¹))
    (GlobalTheory.DetRootCong.quot_fixed (finPart D) _ x Y _ y y' hxf hroot hyy hY3)
  obtain ⟨a, ha⟩ := GlobalTheory.DetRootCong.exists_idF D b
  have hb' : finPart D (idF D a : AE D) = finPart D ((x * Y⁻¹ : (AE D)ˣ) : AE D) :=
    ha.trans (congrArg Units.val hb)
  have h1 := hinf (x * Y⁻¹ * (idF D a)⁻¹) (by
    rw [Units.val_mul, RingHom.map_mul, ← hb', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  simpa [hcY, hF a] using h1

end GlobalTheory.FibreIdem

namespace GlobalTheory.FibreIdem

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

end GlobalTheory.FibreIdem
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.admissibleConjugatePairPlaces_eq_of_twOK : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X),
  GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → admissibleConjugatePairPlaces X i Q M = Q := by
  first | exact @GlobalTheory.AdmAll.admissibleConjugatePairPlaces_eq_of_twist_condition | exact GlobalTheory.AdmAll.admissibleConjugatePairPlaces_eq_of_twist_condition | (intros; apply GlobalTheory.AdmAll.admissibleConjugatePairPlaces_eq_of_twist_condition <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.universalChar_spread_commutes_with_restriction : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (M : ℕ) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (Q Q' : Finset (Pl D.host.E)) (hQQ : Q' ⊆ Q), admissibleConjugatePairPlaces X i Q M = Q → admissibleConjugatePairPlaces X i Q' M = Q' → ∀ (hsub : ∀ w ∈ half ch (admissibleConjugatePairPlaces X i Q' M), w ∈ half ch (admissibleConjugatePairPlaces X i Q M)) (c : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : Pl D.host.E) (hv : v ∈ Q'), spread Y i Q M ch c ⟨v, hQQ hv⟩ = spread Y i Q' M ch (fun w => c ⟨w.1, hsub w.1 w.2⟩) ⟨v, hv⟩ := by
  first | exact @GlobalTheory.SpreadRestrict.spread_restrict | exact GlobalTheory.SpreadRestrict.spread_restrict | (intros; apply GlobalTheory.SpreadRestrict.spread_restrict <;> assumption)
end
