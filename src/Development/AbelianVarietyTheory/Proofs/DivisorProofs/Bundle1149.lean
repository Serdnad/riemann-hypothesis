module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumPf
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Mathlib.Data.Matrix.PEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.IsModel (L := L) A G → ∀ (A' : Over (Sp L)) [GrpObj A'] (ψ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap (algebraMap K L)) ψ → ∃ φ : A'.left ⟶ G.left, IsGrpPullback A' G (spMap (algebraMap W L)) φ := by
  first | exact @GlobalTheory.SS.exists_isGrpPullback_of_isModel | exact GlobalTheory.SS.exists_isGrpPullback_of_isModel | (intros; apply GlobalTheory.SS.exists_isGrpPullback_of_isModel <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory.Rounding

variable {K : Type} [Field K] [NumberField K]

theorem lw_nonneg_here (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw K w := by
  unfold lw
  refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
  have : Ideal.absNorm w.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

theorem vAdd_int_nonneg (w : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ≠ 0) : 0 ≤ vAdd w (x : K) := by
  rw [← vla_span hx w]; exact Nat.cast_nonneg _

theorem vAdd_int_pos (w : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ≠ 0) (hm : x ∈ w.asIdeal) :
    1 ≤ vAdd w (x : K) := by
  rw [← vla_span hx w]
  have h0 : Ideal.span {x} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  have := (Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff w h0).2
    (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hm))
  omega

theorem finite_vla {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => (Formalism.L2.Pj.QAt.vla w I : ℝ)).Finite :=
  (Ideal.finite_factors hI).subset fun w h => by
    refine (Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff w hI).1 fun h0 => h ?_
    simp [h0]

theorem sum_vla_lw {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∑ᶠ w, (Formalism.L2.Pj.QAt.vla w I : ℝ) * lw K w = Real.log (Ideal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) := by
  rw [finsum_eq_sum_of_support_subset (s := (finite_vla hI).toFinset) _
    (by simpa using Function.support_mul_subset_left _ _)]
  have h1 := Formalism.L2.Pj.QAt.BeSumPf.sum_vla_log_fin I hI (finite_vla hI).toFinset fun v hv => by
    simpa using hv
  rw [← h1, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [lw, mul_div_assoc]

theorem vAdd_mul_here (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  simp only [vAdd, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]; ring

theorem vAdd_inv_here (w : HeightOneSpectrum (𝓞 K)) (x : K) : vAdd w x⁻¹ = -vAdd w x := by
  simp [vAdd, map_inv₀, WithZero.log_inv]

theorem count_inv_span (w : HeightOneSpectrum (𝓞 K)) {c : 𝓞 K} (hc : c ≠ 0) :
    FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K c)⁻¹) =
      vAdd w (algebraMap (𝓞 K) K c)⁻¹ := by
  have hspan : Ideal.span {c} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hI : ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hspan
  rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.coeIdeal_span_singleton, vAdd_inv_here]
  have h1 := FractionalIdeal.count_mul K w hI (inv_ne_zero hI)
  rw [mul_inv_cancel₀ hI, FractionalIdeal.count_one] at h1
  have h2 : FractionalIdeal.count K w ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      vAdd w (algebraMap (𝓞 K) K c) := by
    rw [FractionalIdeal.count_coe K w hspan]
    exact vla_span hc w
  omega

theorem vla_eq_count (w : HeightOneSpectrum (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (Formalism.L2.Pj.QAt.vla w I : ℤ) = FractionalIdeal.count K w (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  (FractionalIdeal.count_coe K w hI).symm

theorem exists_rounding (K : Type) [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (hB : ∀ p ∈ B, p.Prime) (hρ : (Function.support ρ).Finite)
    (hint : ∀ w : HeightOneSpectrum (𝓞 K), (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n) :
    ∃ (a : K) (𝔞 : Ideal (𝓞 K)), a ≠ 0 ∧ 𝔞 ≠ ⊥ ∧
      (∀ b ∈ 𝔞, b ≠ 0 → ∀ w, 0 ≤ (vAdd w ((b : K) * a) : ℝ) + ρ w) ∧
      (∑ᶠ w, ρ w * lw K w) - ∑ p ∈ B, Real.log p ≤
        -((∑ σ : K →+* ℂ, Real.log ‖σ a‖) / (Module.finrank ℚ K : ℝ)) -
          Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  set f : HeightOneSpectrum (𝓞 K) → ℤ := fun w => -⌊ρ w⌋ with hf
  have hfs : Function.support f ⊆ Function.support ρ := fun w h h0 => h (by simp [hf, h0])
  have hfin : ∀ᶠ w in Filter.cofinite, f w = 0 := by
    rw [Filter.eventually_cofinite]; exact hρ.subset hfs
  set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ f w with hJdef
  have hJ0 : J ≠ 0 := by
    rw [hJdef, finprod_eq_prod_of_mulSupport_subset (s := hρ.toFinset)]
    · exact Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot)
    · intro w hw
      simp only [Set.Finite.coe_toFinset]
      intro h0; apply hw; simp [hf, h0]
  have hcJ : ∀ w, FractionalIdeal.count K w J = f w := fun w => FractionalIdeal.count_finprod K w f hfin
  obtain ⟨c, 𝔞, hc, hJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
  set a : K := (algebraMap (𝓞 K) K c)⁻¹ with ha
  have ha0 : a ≠ 0 := inv_ne_zero (by simpa using hc)
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rintro rfl; apply hJ0; rw [hJ]; simp
  have hsa0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a ≠ 0 :=
    FractionalIdeal.spanSingleton_eq_zero_iff.not.2 ha0
  have h𝔞0 : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔞
  have hsum : ∀ w, vAdd w a + (Formalism.L2.Pj.QAt.vla w 𝔞 : ℤ) = f w := fun w => by
    rw [← hcJ w, hJ, FractionalIdeal.count_mul K w hsa0 h𝔞0, vla_eq_count w h𝔞, ha, count_inv_span w hc]
  refine ⟨a, 𝔞, ha0, h𝔞, ?_, ?_⟩
  · intro b hb hb0 w
    have hspan : Ideal.span {b} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    obtain ⟨e, he⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb)
    have he0 : e ≠ ⊥ := by rintro rfl; apply hspan; rw [he]; simp
    have hbK : (b : K) ≠ 0 := by simpa using hb0
    have h1 : vAdd w ((b : K) * a) = vAdd w (b : K) + vAdd w a := vAdd_mul_here w hbK ha0
    have h2 : vAdd w (b : K) = Formalism.L2.Pj.QAt.vla w 𝔞 + Formalism.L2.Pj.QAt.vla w e := by
      rw [← vla_span hb0 w, vla_eq_count w hspan, vla_eq_count w h𝔞, vla_eq_count w he0, he,
        FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K w h𝔞0 (FractionalIdeal.coeIdeal_ne_zero.2 he0)]
    have h3 : f w ≤ vAdd w ((b : K) * a) := by
      rw [h1, h2, ← hsum w]; have := (Formalism.L2.Pj.QAt.vla w e).zero_le; omega
    have h4 : (f w : ℝ) ≤ vAdd w ((b : K) * a) := by exact_mod_cast h3
    have h5 := Int.fract_nonneg (ρ w)
    rw [Int.fract] at h5
    simp only [hf, Int.cast_neg] at h4
    linarith
  · have e1 := lineDeg_num ha0
    unfold lineDeg at e1
    have e2 := sum_vla_lw h𝔞
    have e3 : (∑ᶠ w, (vAdd w a : ℝ) * lw K w) + ∑ᶠ w, (Formalism.L2.Pj.QAt.vla w 𝔞 : ℝ) * lw K w =
        ∑ᶠ w, (f w : ℝ) * lw K w := by
      rw [← finsum_add_distrib (fin_mul (finite_vAdd ha0) _) (fin_mul (finite_vla h𝔞) _)]
      refine finsum_congr fun w => ?_
      rw [← add_mul, ← hsum w]; push_cast; ring
    set n : ℕ := ∏ p ∈ B, p with hn
    have hn0 : n ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero
    have e4 : ∑ p ∈ B, Real.log p = ∑ᶠ w, (vAdd w (n : K) : ℝ) * lw K w := by
      rw [sum_vAdd_nat hn0, hn, Nat.cast_prod, Real.log_prod]
      intro p hp; exact_mod_cast (hB p hp).ne_zero
    have hfinf : (Function.support fun w => (f w : ℝ) * lw K w).Finite :=
      (hρ.subset fun w h h0 => h (by simp [hf, h0]))
    have e5 : (∑ᶠ w, ρ w * lw K w) + ∑ᶠ w, (f w : ℝ) * lw K w ≤ ∑ᶠ w, (vAdd w (n : K) : ℝ) * lw K w := by
      rw [← finsum_add_distrib (fin_mul hρ _) hfinf]
      refine finsum_le_finsum' ((fin_mul hρ _).union hfinf |>.subset (Function.support_add _ _))
        (fin_mul (finite_vAdd (Nat.cast_ne_zero.2 hn0)) _) fun w => ?_
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (lw_nonneg_here w)
      have hfr : ρ w + (f w : ℝ) = Int.fract (ρ w) := by
        show ρ w + ((-⌊ρ w⌋ : ℤ) : ℝ) = Int.fract (ρ w)
        rw [Int.fract, Int.cast_neg]; ring
      rw [hfr]
      have hnK : ((n : 𝓞 K) : K) = (n : K) := by simp
      have hn0' : (n : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn0
      by_cases h : ∃ p ∈ B, ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
      · obtain ⟨p, hp, hpw⟩ := h
        obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
        have hmem : (n : 𝓞 K) ∈ w.asIdeal := by
          rw [hn, hk, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpw
        have h1 := vAdd_int_pos w hn0' hmem
        rw [hnK] at h1
        have h2 : (1 : ℝ) ≤ vAdd w (n : K) := by exact_mod_cast h1
        linarith [Int.fract_lt_one (ρ w)]
      · push_neg at h
        obtain ⟨m, hm⟩ := hint w h
        have h1 := vAdd_int_nonneg w hn0'
        rw [hnK] at h1
        rw [hm, Int.fract_intCast]
        have h2 : (0 : ℝ) ≤ (vAdd w (n : K) : ℝ) := Int.cast_nonneg h1
        simpa using h2
    have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.2 (Module.finrank_pos (R := ℚ) (M := K))
    linarith

end GlobalTheory.Rounding
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.LevelRows

variable {D : D7}

theorem levelType_eigenfunction_of_liftable_element {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) (p : P.H)
    (hex : ∃ κ, IsLevelLift V β L p.1 κ) :
    actG0 V β L p.1 F = fun h => ((P.chi p : ℂˣ) : ℂ) * F h := by
  have hκ : IsLevelLift V β L p.1 hex.choose := hex.choose_spec
  have hp : rTup β L (finE V hex.choose) ∈ P.H := by rw [hκ.2.2]; exact p.2
  have hmem : hex.choose ∈ levG V β (withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
  have hc : levChi V β (withP L P) hex.choose = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) hex.choose := by
    unfold levChi
    rw [levFn_withP, extendOne_of_mem _ hp, Units.val_mul]
    congr 3
    exact Subtype.ext hκ.2.2
  have ha := levChi_ne_zero (β := β) (flagL L) hex.choose
  funext h
  unfold actG0
  rw [dite_eq_left hex, hF _ hmem h, hc]
  field_simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_lift_of_ne_zero (R : RealDat D A Ks) (hinj : Function.Injective R.HE.e) (hg : R.models_gE)
    {x : R.HE.H} (hx : x ≠ 0) (g : G) : ∃ κ, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) κ := by
  by_contra hk
  apply hx
  have h0 : R.gE g x = 0 := by
    apply hinj
    rw [hg g x, map_zero]
    ext v h
    show actG0 _ _ _ _ _ h = 0
    unfold actG0
    rw [dite_eq_right hk]
    rfl
  have : R.gE g⁻¹ (R.gE g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h0, map_zero]

theorem rowsOfLevel_of_models (R : RealDat D A Ks) (F : Face D A) (hE : R.models_HE) (hg : R.models_gE) :
    GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows.RowsOfLevel R F := by
  intro b x
  have hx : R.HE.e x ∈ R.EEat R.triv := hE.2.1 ▸ LinearMap.mem_range_self _ x
  unfold RealDat.EEat at hx ⊢
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  constructor
  · rintro ⟨h1, -⟩ g
    by_cases h0 : x = 0
    · simp [h0]
    apply hE.1
    rw [hg, map_smul]
    ext v h
    have hmem : R.eG g ∈ (R.levR F b).H := by
      show R.eG.symm (R.eG g) ∈ (F.lvl b).P
      rw [MulEquiv.symm_apply_apply]; exact g.2
    have h2 := levelType_eigenfunction_of_liftable_element (V := Yc D 0) (β := R.βY 0) (L := R.dat0 R.triv) (P := R.levR F b)
      (F := R.HE.e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG g, hmem⟩ (exists_lift_of_ne_zero R hE.1 hg h0 g)
    have h3 : (R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩ = g :=
      Subtype.ext (R.eG.symm_apply_apply g)
    refine (congrFun h2 h).trans ?_
    show D.what₂.embLL (((F.lvl b).ψ ((R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩) : D.what₂.LLˣ) : D.what₂.LL) * _ = _
    rw [h3]
    rfl
  · intro h
    refine ⟨⟨hx.1.aut, hx.1.cusp, fun v => ?_, hx.1.equiv, hx.1.cont⟩, hx.2⟩
    have hP : IsPLevel (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.levR F b) (R.HE.e x v) := by
      refine ⟨fun κ hκ y => hx.1.lev v κ hκ y, fun p => ?_⟩
      have h1 := congrArg (fun z => R.HE.e z v) (h ⟨R.eG.symm p.1, p.2⟩)
      simp only [hg _ x, map_smul] at h1
      have h2 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
      rw [h2] at h1
      exact h1
    exact fun κ hκ y => hP.hasType κ hκ y

end GlobalTheory.LevelRows

end
end

section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem typePlaces_card_and_residue_le : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → R.Pg.card = 2 * D.R.f ∧ ∀ PP ∈ R.Pg, min (D.host.g 0) (D.host.g 1) ≤ Nat.card (kP PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h
  obtain ⟨_, plg, iso, -⟩ := h
  refine ⟨?_, fun PP hPP => ?_⟩
  · rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_congr plg, Nat.card_sigma]
    have hk : ∀ k : Fin 2, Nat.card (D.nd.PlG k) = D.R.f := fun k => by
      rw [← D.nd.card_PlG k]
      exact @Nat.card_eq_fintype_card _ (_)
    simp only [hk, Fin.sum_univ_two, two_mul]
  · obtain ⟨kv, hkv⟩ := plg.surjective ⟨PP, hPP⟩
    have h1 : Nat.card (kP (plg kv).1) = D.host.g kv.1 := by
      rw [← Nat.card_congr (iso kv).toEquiv, Nat.card_zmod]
    rw [hkv] at h1
    change _ ≤ Nat.card (kP (⟨PP, hPP⟩ : R.Pg).1)
    rw [h1]
    generalize kv.1 = k
    fin_cases k
    · exact min_le_left _ _
    · exact min_le_right _ _

end GlobalTheory
end

section

noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

namespace GlobalTheory.OneFormTest

theorem model_of_pres {H Γ : Type} [Group H] [Group Γ] {ι : Γ →* H} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup H}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (H → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) :
    (∀ x y, ⟪j x, j y⟫_ℂ = σ (S.csum x.1 y.1)) ∧ Function.Injective j ∧ Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · rw [hM.2.2, hj, hj]
    exact h3 x y
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h4 : P.extL x = 0 := by rw [← hj, hx, map_zero]

    rw [← S.basis.sum_repr x, map_sum] at h4
    simp only [map_smulₛₗ] at h4
    have h5 := Fintype.linearIndependent_iff.1 h1 _ h4
    refine S.basis.repr.injective (Finsupp.ext fun i => ?_)
    rw [(map_eq_zero _).1 (h5 i), map_zero, Finsupp.zero_apply]
  · apply Submodule.map_injective_of_injective hM.1
    rw [Submodule.map_top, hM.2.1, Submodule.map_span, ← Set.range_comp, show M.e ∘ j = P.extL from funext hj, h2]

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem model_jX (hH : R.models_HX) (hj : R.models_jX) (t : T) :
    (∀ x y : (A.MtildeCSD t).Forms, ⟪R.jX t x, R.jX t y⟫_ℂ = D.what₂.embLL ((A.MtildeCSD t).csum x.1 y.1)) ∧
      Function.Injective (R.jX t) ∧ Submodule.span ℂ (Set.range (R.jX t)) = ⊤ :=
  model_of_pres (S := A.MtildeCSD t) (R.B.R t).pres (R.HX t) (hH t) (R.jX t) (hj t)

end Concrete

end GlobalTheory.OneFormTest
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField

namespace GlobalTheory.ColumnMultSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def permUnit (κ : Type) [CommRing κ] {r : ℕ} (π : Equiv.Perm (Fin r)) : GL (Fin r) κ where
  val := π.toPEquiv.toMatrix
  inv := π.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem reord_eq_conj {D : D7} {Pg : Finset (Pl D.host.E)} {r : ℕ} (π : Equiv.Perm (Fin r)) :
    ∃ w : G0 Pg r, ∀ g : G0 Pg r, reord π g = w * g * w⁻¹ := by
  refine ⟨fun PP => permUnit (kP PP.1) π, fun g => ?_⟩
  funext PP
  apply Units.ext
  show Matrix.reindexAlgEquiv (kP PP.1) (kP PP.1) π.symm (g PP : Matrix (Fin r) (Fin r) (kP PP.1)) =
    π.toPEquiv.toMatrix * (g PP : Matrix (Fin r) (Fin r) (kP PP.1)) * π.symm.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp

theorem columnMult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → R.Pg.card = 2 * D.R.f → (∀ PP ∈ R.Pg, min (D.host.g 0) (D.host.g 1) ≤ Nat.card (kP PP)) → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → (∀ χ ∈ A.X, IsAbsIrrChar χ) → (∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g)) → ∀ [Fintype F.P1], ∀ χ ∈ A.X, ∃ n : ℕ, (Nat.card F.P1 : D.what₂.LL)⁻¹ * ∑ h : F.P1, χ (h : G) * (((F.ψ1 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (n : D.what₂.LL) ∧ |(n : ℝ) - (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ)| ≤ 8 * (D.R.f : ℝ) * (D.R.r : ℝ) / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hlev hcard hq hadm hirr hprod _ χ hχ
  classical
  obtain ⟨ψ, hψ, -, π, -, hmem, hchi⟩ := hlev
  obtain ⟨w, hw⟩ := reord_eq_conj (D := D) (Pg := R.Pg) π
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hr : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  have hg : 0 < min (D.host.g 0) (D.host.g 1) := lt_min (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar (RingHom.id ℂ) R.Pg D.R.r fun g => D.what₂.embLL (χ (R.eG.symm g)) :=
    hprod χ hχ
  obtain ⟨⟨n, hn, hb⟩, -⟩ := GlobalTheory.FinGL.MultSharpObj.multSharp D.host.E ℂ (RingHom.id ℂ) R.Pg D.R.f
    (min (D.host.g 0) (D.host.g 1)) D.R.r D.R.rS D.R.k ψ hcard hk hr hg hadm hq hψ _ hp
  refine ⟨n, ?_, hb⟩
  have hm : ∀ g : G, R.eG g ∈ (R.levR F true).H ↔ g ∈ F.P1 := fun g => by
    show R.eG.symm (R.eG g) ∈ F.P1 ↔ _
    rw [MulEquiv.symm_apply_apply]
  have hc : ∀ (g : G) (h : R.eG g ∈ (R.levR F true).H), (((R.levR F true).chi ⟨R.eG g, h⟩ : ℂˣ) : ℂ) =
      D.what₂.embLL ((F.ψ1 ⟨g, (hm g).1 h⟩ : D.what₂.LLˣ) : D.what₂.LL) := fun g h => by
    show D.what₂.embLL ((F.ψ1 ⟨R.eG.symm (R.eG g), h⟩ : D.what₂.LLˣ) : D.what₂.LL) = _
    congr 4
    exact R.eG.symm_apply_apply g
  let e : F.P1 ≃ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ).H :=
    (R.eG.trans (MulAut.conj w)).toEquiv.subtypeEquiv fun g => by
      rw [← hm, hmem, hw]; rfl
  apply D.what₂.embLL.injective

  rw [map_natCast, ← hn, map_mul, map_inv₀, map_natCast, map_sum]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.levelMult
  rw [Nat.card_congr e]
  congr 1
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_boundedLevelClassGroupFamily R.Pg D.R.r
  letI : Fintype (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ).H := Fintype.ofFinite _
  refine Fintype.sum_equiv e _ _ fun x => ?_
  have h1 : R.eG x ∈ (R.levR F true).H := (hm x).2 x.2
  have h2 := (hmem _).1 h1
  have he : e x = ⟨reord π (R.eG x), h2⟩ := Subtype.ext (hw _).symm
  rw [he, ← hchi _ h1 h2, map_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, hc]
  congr 2
  show χ x = χ (R.eG.symm (reord π (R.eG x)))
  rw [hw, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, (hirr χ hχ).conj]

end GlobalTheory.ColumnMultSum

end
end
