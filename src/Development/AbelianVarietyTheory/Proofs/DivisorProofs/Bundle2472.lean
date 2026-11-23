module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle354
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle004
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageRam

private theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

private theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

private theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) :
    (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

private theorem chrEq_pow {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) :
    ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

private theorem not_nonSplitAt_of_emb {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ¬ GlobalTheory.WeilParts.NonSplitAt D v ε := by
  intro h
  refine h.2 ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
  have he : ε = GlobalTheory.EmbChart.atPlace v 1 := by
    obtain ⟨α, rfl, h1, h0⟩ := hε
    rw [GlobalTheory.EmbChart.atPlace_apply]
    congr 1
    refine FiniteAdeleRing.ext _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
    by_cases e : u = v
    · subst e; rw [GlobalTheory.AdelicU.evalV_singleFin_self, h1]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, h0 u e]
  rw [he, GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]; rfl

private theorem levelLe_one_of_unrAt {L : Type} [Field L] [NumberField L] {χ : HChar L} {w : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt w) : χ.LevelLe w 1 :=
  fun x hx _ => h x hx

private theorem natCast_mem_of_card {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h : Nat.card (𝓞 E ⧸ P.asIdeal) = ℓ) : (ℓ : 𝓞 E) ∈ P.asIdeal := by
  have : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (h ▸ hℓ.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  have h0 : ((Fintype.card (𝓞 E ⧸ P.asIdeal) : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card, h] at h0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h0


open Classical in
theorem _root_.GlobalTheory.T.towerStage_finitePlaces_unramified_or_split : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W i j p q A A' WW X _ t v e he
  have hm1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have hm2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  have hα : ChrEq (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (alphaH Lc t i j) :=
    GlobalTheory.TwistChr.chrEq_mul (GlobalTheory.TwistChr.chrEq_mul (hL.mu0 j) (hL.xi t)) (chrEq_pow hL.eta _)
  have hβ : ChrEq (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (betaH G i j) :=
    GlobalTheory.TwistChr.chrEq_mul (G.ch.chi_eq _ hm1 hm2) (chrEq_pow hL.eta _)
  have hν : ChrEq (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))
      (nuH G t i j) := by
    rw [mul_div_mul_right_eq_div]
    exact chrEq_nu G t i j hL
  have hmu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ S1 D → (Lc.C.mu0 j).UnrAt P :=
    fun P hP => (Lc.C.isMu0 j).unr _ fun k hk => hP (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
  have hxi : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) → (Lc.xiH t).UnrAt P := fun P hP => by
    by_contra hc
    rcases (hL.Q_ram t P).1 hc with h | ⟨PP', h, hc'⟩
    · exact hP P h rfl
    · exact hP PP' h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc')
  have hchi : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (G.ch.chiH (D.R.m - i)).UnrAt P := fun P hP => G.ch.unr _ hm1 hm2 P hP
  have heta : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (Lc.C.eta ^ (rankV D i j % 2)).UnrAt P :=
    fun P => unrAt_pow (Lc.C.isEta.unr P) _
  by_cases hS : v ∈ G.pl.S0 ∨ ∃ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
  · right
    obtain ⟨w, hw, hwv⟩ : ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v := by
      rcases hS with h | ⟨PP, hP, hPv⟩
      · exact ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ h), G.pl.under_w h⟩
      · exact ⟨PP, Finset.mem_union_right _ hP, hPv⟩
    have hns : ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
      obtain ⟨τ⟩ := GlobalTheory.LocPlSplit.locPl_split hL t w hw
      rw [hwv] at τ
      exact not_nonSplitAt_of_emb he τ
    refine ⟨hns, fun hu => ?_, ?_⟩
    · have key : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → (nuH G t i j).UnrAt P :=
        fun P hP => (GlobalTheory.LFun.unrAt_iff_of_chrEq hν P).1 (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ v e he hu P hP)
      by_cases h0 : v = G.pl.v0
      · subst h0
        exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j (key _ (G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))))
      · by_cases h1 : v ∈ S1 D
        · have hv : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr h1)
          have hwv' := G.pl.under_w hv
          apply (G.ch.lev1 _ hm1 hm2 (G.pl.w v) (by rw [hwv']; exact h1)).2
          have ee : G.ch.chiH (D.R.m - i) = Lc.C.mu0 j * Lc.xiH t / nuH G t i j := by
            rw [nuH, div_div_cancel]
          rw [ee, div_eq_mul_inv]
          exact HChar.LevelLe.mul (HChar.LevelLe.mul ((Lc.C.isMu0 j).tame _) (hL.xi_tame t _))
            (HChar.LevelLe.inv (levelLe_one_of_unrAt (key _ hwv')))
        · obtain ⟨PP, hP, hPv⟩ := hS.resolve_left fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1
          apply (hL.Q_ram t PP).2 (Or.inl hP)
          have ee : Lc.xiH t = nuH G t i j * G.ch.chiH (D.R.m - i) / Lc.C.mu0 j := by
            rw [nuH, div_mul_cancel, mul_div_cancel_left]
          rw [ee, div_eq_mul_inv]
          exact ((key PP hPv).mul (hchi PP (by rw [hPv]; exact fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1))).mul
            (hmu PP (by rw [hPv]; exact h1)).inv
    · by_cases h0 : v = G.pl.v0
      · subst h0
        exact GlobalTheory.DifferentAtBasePlace.not_dvd_different G
      · by_cases h1 : v ∈ S1 D
        · exact GlobalTheory.DiffSOne.not_dvd_differentIdeal large₂ hR v h1
        · obtain ⟨PP, hP, hPv⟩ := hS.resolve_left fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1
          obtain ⟨⟨ℓ, hℓ, hcard, hℓ2, -⟩, -⟩ := hL.Q_pl t PP hP
          have hℓP : ((ℓ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := natCast_mem_of_card hℓ hcard
          have hle : v.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ PP.asIdeal := by
            rw [← hPv]
            exact Ideal.map_comap_le
          refine GlobalTheory.SplitUnram.not_dvd_different hℓ v ?_ ?_
          · rw [← hPv]
            show algebraMap _ (𝓞 D.host.E) _ ∈ PP.asIdeal
            rw [map_natCast]; exact hℓP
          · intro hv2
            have h' := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hv2
            rw [Ideal.map_pow, map_natCast] at h'
            exact hℓ2 (Ideal.pow_right_mono hle 2 h')
  · left
    push_neg at hS
    obtain ⟨hS0, hQ⟩ := hS
    have hS1 : v ∉ S1 D := fun h => hS0 (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
    refine ⟨GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hα v e he fun P hP => ?_, GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hβ v e he fun P hP => ?_⟩
    · exact ((hmu P (by rw [hP]; exact hS1)).mul (hxi P fun PP hPP h => hQ PP hPP (h.trans hP))).mul (heta P)
    · exact (hchi P (by rw [hP]; exact hS0)).mul (heta P)

end GlobalTheory.StageRam

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open IsLocalRing

theorem isUnit_det_of_span_eq_top (k A : Type) [CommRing k] [CommRing A] [Algebra k A] {N : ℕ} (g : Fin N → A)
    (bΩ : Module.Basis (Fin N) A Ω[A⁄k]) (hg : ∀ i, bΩ i = KaehlerDifferential.D k A (g i))
    (δ : Fin N → Derivation k A A) (hδ : Submodule.span A (Set.range δ) = ⊤) :
    IsUnit (Matrix.of fun i j => δ j (g i)).det := by
  classical
  have h : ∀ i, ∃ a : Fin N → A, ∑ j, a j • δ j = KaehlerDifferential.linearMapEquivDerivation k A (bΩ.coord i) :=
    fun i => (Submodule.mem_span_range_iff_exists_fun A).1 (hδ ▸ Submodule.mem_top)
  choose a ha using h
  have hm : (Matrix.of fun i j => δ j (g i)) * (Matrix.of fun j i => a i j) = 1 := by
    ext l i
    have h1 := congrArg (fun d : Derivation k A A => d (g l)) (ha i)
    simp only [KaehlerDifferential.linearMapEquivDerivation_apply_apply, ← hg] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h2 : (∑ j, a i j • δ j) (g l) = ∑ j, a i j * δ j (g l) := by
      have := map_sum (FunLike.coeAddMonoidHom (Derivation k A A) A A) (fun j => a i j • δ j) Finset.univ
      have h3 := congrFun this (g l)
      rw [Finset.sum_apply] at h3
      exact h3
    rw [h2] at h1
    simp only [Matrix.of_apply, mul_comm (δ _ _)]
    rw [h1]
    simp [Finsupp.single_apply]
  exact Matrix.isUnit_det_of_right_inverse hm

theorem det_mem_maximalIdeal (k A : Type) [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A] {N : ℕ}
    (g : Fin N → A) (bΩ : Module.Basis (Fin N) A Ω[A⁄k]) (hg : ∀ i, bΩ i = KaehlerDifferential.D k A (g i))
    (δ : Fin N → Derivation k A A) (t : A) (ht : t ∈ maximalIdeal A)
    (hd : KaehlerDifferential.D k A t ∉ (maximalIdeal A) • (⊤ : Submodule A Ω[A⁄k]))
    (hδ : ∀ j, δ j t ∈ Ideal.span {t}) : (Matrix.of fun i j => δ j (g i)).det ∈ maximalIdeal A := by
  classical
  set c : Fin N → A := fun i => bΩ.repr (KaehlerDifferential.D k A t) i with hc
  have hsum : KaehlerDifferential.D k A t = ∑ i, c i • bΩ i := (bΩ.sum_repr _).symm
  have hne : (fun i => residue A (c i)) ≠ 0 := by
    intro h0
    apply hd
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact (residue_eq_zero_iff _).1 (congrFun h0 i)
  rw [← residue_eq_zero_iff, RingHom.map_det]
  refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hne, ?_⟩
  funext j
  have h1 : δ j t = ∑ i, c i * δ j (g i) := by

    rw [← (δ j).liftKaehlerDifferential_comp_D t, hsum, map_sum]
    simp [hg]
  have h2 : residue A (δ j t) = 0 :=
    (residue_eq_zero_iff _).2 ((Ideal.span_singleton_le_iff_mem _).2 ht (hδ j))

  rw [h1, map_sum] at h2
  simpa [Matrix.vecMul, dotProduct] using h2

theorem derivation_mem_span_of_prod {k A : Type} [CommRing k] [CommRing A] [IsRegularLocalRing A] [Algebra k A] {n : ℕ}
    (f : Fin n → A) (hf : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp A n f) (J : Finset (Fin n)) {j : Fin n} (hj : j ∈ J)
    (δ : Derivation k A A) (hδ : δ (∏ i ∈ J, f i) ∈ Ideal.span {∏ i ∈ J, f i}) : δ (f j) ∈ Ideal.span {f j} := by
  classical
  have hD : IsDomain A := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hp := ReciprocityTheory.AnForm.R.prime_of_regular_params f hf.1 hf.2
  rw [Ideal.mem_span_singleton] at hδ ⊢
  rw [← Finset.mul_prod_erase J f hj, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hδ
  have h1 : f j ∣ (∏ i ∈ J.erase j, f i) * δ (f j) :=
    (dvd_add_right (dvd_mul_right _ _)).1 ((dvd_mul_right _ _).trans hδ)
  refine ((hp j).dvd_or_dvd h1).resolve_left fun h2 => ?_
  obtain ⟨i, hi, h3⟩ := (hp j).exists_mem_finset_dvd h2
  exact (ReciprocityTheory.AnForm.R.regular_params_spec f hf.1 hf.2).2 j i (Finset.ne_of_mem_erase hi).symm
    ((hp j).associated_of_dvd (hp i) h3)

theorem D_notMem_smul_top {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.FormallySmooth k (ResidueField A)] {t : A} (ht : t ∈ maximalIdeal A) (ht2 : t ∉ maximalIdeal A ^ 2) :
    KaehlerDifferential.D k A t ∉ (maximalIdeal A) • (⊤ : Submodule A Ω[A⁄k]) := by
  intro hm
  have h := GlobalTheory.AdaptedFrame.linearIndependent_tmul_D (k := k) (fun _ : Unit => t) (fun _ => ht)
    (linearIndependent_unique_iff.2 (by
      intro h0
      exact ht2 ((Ideal.toCotangent_eq_zero _ _).1 h0)))
  refine h.ne_zero () ?_
  generalize KaehlerDifferential.D k A t = w at hm
  refine Submodule.smul_induction_on hm (fun r hr w _ => ?_) (fun x y hx hy => ?_)
  · rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ResidueField.algebraMap_eq,
      (residue_eq_zero_iff _).2 hr, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, hx, hy, add_zero]

theorem derivation_mem_map {k R A : Type} [CommRing k] [CommRing R] [CommRing A] [Algebra k A] (φ : R →+* A)
    (I : Ideal R) (d : R → R) (hd : ∀ r ∈ I, d r ∈ I) (δ : Derivation k A A) (hδ : ∀ r, δ (φ r) = φ (d r))
    {a : A} (ha : a ∈ I.map φ) : δ a ∈ I.map φ := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    rw [hδ]
    exact Ideal.mem_map_of_mem _ (hd r hr)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx0 hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx0)

theorem exists_boundary_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∀ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx ((b j).1 r)) → x ∉ (j₀ TF.Y Z).opensRange → ∃ t ∈ IsLocalRing.maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x), KaehlerDifferential.D c.F ((X₀ TF.Y Z).presheaf.stalk x) t ∉ (IsLocalRing.maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x)) • (⊤ : Submodule ((X₀ TF.Y Z).presheaf.stalk x) Ω[(X₀ TF.Y Z).presheaf.stalk x⁄c.F]) ∧ ∀ j, δ j t ∈ Ideal.span {t} := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hx b δ hδ hn
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  obtain ⟨hreg, n, f, J, hf, ⟨j, hj⟩, hI⟩ := GlobalTheory.T.boundary_componentStalk_regular_boundaryIdeal_prod_params E H Dw l Xo c TF Z x U hx hn
  have hm : f j ∈ maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x) := hf.1 ▸ Ideal.subset_span ⟨j, rfl⟩
  refine ⟨f j, hm, ?_, fun i => ?_⟩
  · obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.1 (X₀ TF.Y Z).isBasis_affineOpens (show x ∈ (⊤ : (X₀ TF.Y Z).Opens) from trivial)
    haveI := GlobalTheory.AdaptedFrame.formallySmooth_residueField (s₀ TF.Y Z) (n := Dw.dim) hV x hxV (by
      ext t
      change ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (s₀ TF.Y Z) ⊤ t) =
        ((X₀ TF.Y Z).presheaf.germ V x hxV).hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (s₀ TF.Y Z) V t)
      rw [← GlobalTheory.TopForm.resG_comp_algX (s₀ TF.Y Z) (le_top : V ≤ ⊤), RingHom.comp_apply, germ_resG])
    exact D_notMem_smul_top hm ((ReciprocityTheory.AnForm.R.regular_params_spec f hf.1 hf.2).1 j)
  · refine derivation_mem_span_of_prod f hf J hj (δ i) ?_
    rw [← hI]
    refine derivation_mem_map _ _ (b i).1 (b i).2.2 (δ i) (hδ i) ?_
    rw [hI]
    exact Ideal.subset_span rfl

theorem local_topPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → (barComp TF.Y Z).ι x ∈ U.1 → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((b j).1 r)) → ∀ (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hU hxU ρ hρ b D hD U' ω hω hx
  have h1 := chartRestr_eq_germ E H Dw l Xo c TF Z x U hU hxU ρ hρ
  obtain ⟨δ, hδK, hδR⟩ := GlobalTheory.T.exists_componentStalkDerivation_of_functionField_extension E H Dw l Xo c TF Z x U hU hxU ρ h1 (fun j => (b j).1) D hD
  obtain ⟨g, bΩ, u, hg, hu, hform⟩ := frame_eq_unit_smul_dForm E H Dw l Xo c TF Z x U' ω hω hx
  letI := (stalkAlg TF Z x).toAlgebra
  have key : topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω) =
      algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField
        (u * (Matrix.of fun i j => δ j (g i)).det) := by
    rw [hform, LinearMap.map_smul, topPair_dForm, smul_eq_mul, map_mul, RingHom.map_det]
    congr 2
    ext i j
    exact hδK j (g i)
  refine ⟨⟨_, key.symm⟩, fun hU' => ?_, fun hr => ?_⟩
  · by_contra hn
    obtain ⟨t, htm, htd, htδ⟩ := exists_boundary_param E H Dw l Xo c TF Z x U hxU b δ hδR hn
    have hz := det_mem_maximalIdeal c.F _ g bΩ hg δ t htm htd htδ
    refine (zeroAt_iff.1 ⟨_, Ideal.mul_mem_left _ u hz, key.symm⟩).2 hU'
  · have hs := GlobalTheory.T.span_logDer_germs' E H Dw l Xo c TF Z x U hU hxU b δ hδR hr
    exact ⟨_, hu.mul (isUnit_det_of_span_eq_top c.F _ g bΩ hg δ hs), key.symm⟩

end GlobalTheory.LogKSDiv
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.balancedSymmetricPairMatrix_horizontal_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw), ∃ κ : Fin Dw.dim ≃ HIx Dw (psiSet H), ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (j : Fin Dw.dim) (k : HIx Dw (psiSet H)), f (GlobalTheory.LogKSDiv.symPair (R := R) e (ε j) (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩)) = (Pi.single (κ j) (1 : S) : HIx Dw (psiSet H) → S) k := by
  first | exact @GlobalTheory.LogKSDiv.PairEntry.symPair_horizontal_single | exact GlobalTheory.LogKSDiv.PairEntry.symPair_horizontal_single | (intros; apply GlobalTheory.LogKSDiv.PairEntry.symPair_horizontal_single <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem exists_torsion_map_of_isGrpPullback {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {f : X' ⟶ X'}
    {φ : G.left ⟶ G.left} (h : IsGrpPullback G G f φ) (hc : (mulN G n).left ≫ φ = φ ≫ (mulN G n).left) :
    ∃ τ : (torsion G n).left ⟶ (torsion G n).left,
      τ ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ φ ∧ τ ≫ (torsion G n).hom = (torsion G n).hom ≫ f := by
  have hP := GrpTangent.isPullback_torsion G n
  have hw : ((torsion.ι G n).left ≫ φ) ≫ (mulN G n).left =
      ((torsion G n).hom ≫ f) ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
    have e := eta_comp_of_isGrpPullback h
    rw [Category.assoc, ← hc, ← Category.assoc, hP.w]
    exact (Category.assoc _ _ _).trans
      ((congrArg ((torsion G n).hom ≫ ·) e).trans (Category.assoc _ _ _).symm)
  exact ⟨hP.lift _ _ hw, hP.lift_fst _ _ hw, hP.lift_snd _ _ hw⟩

theorem class_move : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X') (ρ : Γ →* Aut V) (hρ : ∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom)
    (ι : Γ →* (M ≃ₗ[𝓞 E] M)) (m : Γ → (G.left ⟶ G.left)) (hm : GlobalTheory.EqvAct.IsEqvAct ρ' G act m)
    (hmv : ∀ γ c, w c ≫ m γ = (ρ γ).asIso.hom ≫ w (ι γ c))
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (γ : Γ) (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hPQ : Q.left = P.left ≫ m γ) (x : Sp K) (cP cQ : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ), cQ = ι γ cP := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ _ hun act Γ _ ρ' ρ hρ ι m hm hmv K _ _ t γ P Q PT QT hPT hQT hPQ
    x cP cQ hcP hcQ
  haveI := mono_torsion_ι G n
  have hpb := hm.1 γ
  obtain ⟨τ, hτι, hτh⟩ := exists_torsion_map_of_isGrpPullback G n hpb
    (by rw [← act_natCast act n]; exact hm.2.1 γ _)
  have hPQT : PT ≫ τ = QT := by
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτι, reassoc_of% hPT, hQT, hPQ]
  have hq : τ (PT x) = QT x := by rw [← hPQT, Scheme.Hom.comp_apply]
  have hιh : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w _
  have hval : ValAt G n ℓ w (PT x) ((ι γ).symm cQ) := by
    intro Ω _ _ y z hyz
    rw [← hq] at hcQ
    have key := Scheme.SpecMap_stalkMap_fromSpecStalk τ (x := PT x)
    have h1 := hcQ Ω (y ≫ Spec.map (τ.stalkMap (PT x))) (z ≫ (ρ γ).asIso.hom) (by
      simp only [Category.assoc, reassoc_of% key, hτh, hρ, reassoc_of% hyz])
    simp only [Category.assoc, reassoc_of% key, hτι] at h1
    refine hpb.1.hom_ext ?_ ?_
    · simp only [Category.assoc, hmv, LinearEquiv.apply_symm_apply]
      exact h1
    · simp only [Category.assoc, hw, hιh]
      exact hyz
  rw [valAt_unique G n hn ℓ w hw hun (PT x) cP _ hcP hval, LinearEquiv.apply_symm_apply]

end GlobalTheory.TorsSpec
end
end
