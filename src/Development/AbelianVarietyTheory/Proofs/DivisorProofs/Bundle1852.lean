module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgUniq

theorem isPullback_square {S S' : Scheme.{0}} {G : Over S} {A : Over S'} {f : S' ⟶ S}
    {a : A.left ⟶ G.left} (hA : IsPullback a A.hom G.hom f)
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : Geo.Tor.IsSquare a φ₂) :
    IsPullback φ₂ (A ⊗ A).hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y)
    (c : Z ⟶ X) (e : b ≫ a = c) : LBIso (L.pull c) ((L.pull a).pull b) := by
  subst e
  exact LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem square_comp {S S' : Scheme.{0}} {G G' : Over S} {A : Over S'} {a : A.left ⟶ G.left}
    {a' : A.left ⟶ G'.left} {g : G ⟶ G'} (hg : a ≫ g.left = a')
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} {φ₂' : (A ⊗ A).left ⟶ (G' ⊗ G').left}
    (h : Geo.Tor.IsSquare a φ₂) (h' : Geo.Tor.IsSquare a' φ₂') : φ₂ ≫ (g ⊗ₘ g).left = φ₂' := by
  have h₁ := h.1
  have h₂ := h.2
  apply pullback.hom_ext
  · change _ ≫ (fst G' G').left = _ ≫ (fst G' G').left
    rw [Category.assoc, ← Over.comp_left, tensorHom_fst, Over.comp_left, reassoc_of% h₁, hg, h'.1]
  · change _ ≫ (snd G' G').left = _ ≫ (snd G' G').left
    rw [Category.assoc, ← Over.comp_left, tensorHom_snd, Over.comp_left, reassoc_of% h₂, hg, h'.2]

theorem exists_iso_algebraisation : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (B B' : Over (Spec (CommRingCat.of R))) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → IsProjBy B.hom → ∀ (b : ∀ e, (Y e).left ⟶ B.left) (b' : ∀ e, (Y e).left ⟶ B'.left), (∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) → (∀ e, β e ≫ b (e + 1) = b e) → (∀ e, IsGrpPullback (Y e) B' (thick R I e) (b' e)) → (∀ e, β e ≫ b' (e + 1) = b' e) → ∃ g : B ≅ B', IsMonHom g.hom ∧ (∀ e, b e ≫ g.hom.left = b' e) ∧ (∀ g' : B ⟶ B', (∀ e, b e ≫ g'.left = b' e) → g' = g.hom) ∧ (∀ (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b' e))) → LBIso M (M'.pull g.hom.left)) ∧ ∀ (P : LB (B ⊗ B).left) (P' : LB (B' ⊗ B').left) (b₂ : ∀ e, (Y e ⊗ Y e).left ⟶ (B ⊗ B).left) (b₂' : ∀ e, (Y e ⊗ Y e).left ⟶ (B' ⊗ B').left), P.IsLB → P'.IsLB → (∀ e, Geo.Tor.IsSquare (b e) (b₂ e)) → (∀ e, Geo.Tor.IsSquare (b' e) (b₂' e)) → (∀ e, LBIso (P.pull (b₂ e)) (P'.pull (b₂' e))) → LBIso P (P'.pull (g.hom ⊗ₘ g.hom).left) := by
  intro H R _ _ I hI Y _ β B B' _ _ hB hB' hp b b' hb hβ hb' hβ'
  have := hB.proper
  have := hB'.proper
  obtain ⟨g, hg, hu⟩ := H.exists_iso hI (fun e => (hb e).1) hβ (fun e => (hb' e).1) hβ'
  obtain ⟨k, hk, hk', -⟩ := GlobalTheory.T.grpHom_algebraisation_of_reductions H R I hI B B' hB.proper hB'.proper Y Y β β b b' hb hβ hb' hβ'
    (fun e => 𝟙 _) (fun e => inferInstance)
    (fun e => by rw [Over.id_left, Over.id_left, Category.comp_id, Category.id_comp])
  have hkg : k = g.hom := hu k fun e => by rw [hk', Over.id_left, Category.id_comp]
  refine ⟨g, hkg ▸ hk, hg, hu, fun M M' hM hM' h => ?_, fun P P' b₂ b₂' hP hP' hs hs' h => ?_⟩
  · exact GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions R I hI B hB.smooth hp hB.geomConnected Y b (fun e => (hb e).1) M _ hM
      (pull_isLB hM' _) fun e => (h e).trans (pull_isLB hM _) (pull_isLB hM' _)
        (pull_isLB (pull_isLB hM' _) _) (lbIso_pull_comp hM' _ _ _ (hg e))
  · have hBB := AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB
    exact GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions R I hI (B ⊗ B) hBB.smooth (isProjBy_tensor R B B hp hp) hBB.geomConnected
      (fun e => Y e ⊗ Y e) b₂ (fun e => isPullback_square (hb e).1 (hs e)) P _ hP
      (pull_isLB hP' _) fun e => (h e).trans (pull_isLB hP _) (pull_isLB hP' _)
        (pull_isLB (pull_isLB hP' _) _) (lbIso_pull_comp hP' _ _ _ (square_comp (hg e) (hs e) (hs' e)))

end GlobalTheory.AlgUniq
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

namespace GlobalTheory.HeckeEpsAbs

variable {E : Type} [Field E] [NumberField E]

theorem norm_gaussSumAt_sq (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ) (ha : a ≠ 0) (hχ : ExpAt χ w a)
    (hu : IsUnitary χ) (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) :
    ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := GlobalTheory.T.heckeLocalGaussSum_norm_sq_eq_absNorm_pow χ w a c ha hχ hu hc

theorem norm_locK {χ : HChar E} (hu : IsUnitary χ) (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) :
    ‖((χ.locK w x : ℂˣ) : ℂ)‖ = 1 := hu _

theorem absNorm_pos (w : HeightOneSpectrum (𝓞 E)) : 0 < Ideal.absNorm w.asIdeal :=
  Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem natCast_pow_cpow {N : ℕ} (hN : (N : ℂ) ≠ 0) (k : ℕ) (t : ℂ) :
    (((N ^ k : ℕ) : ℂ)) ^ t = (N : ℂ) ^ ((k : ℂ) * t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, ← Complex.cpow_add _ _ hN]
    congr 1; push_cast; ring

theorem prod_natCast_cpow {ι : Type} (S : Finset ι) (f : ι → ℕ) (t : ℂ) :
    ∏ i ∈ S, ((f i : ℕ) : ℂ) ^ t = (((∏ i ∈ S, f i : ℕ)) : ℂ) ^ t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

theorem locEps_eq_mul (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) (s : ℂ) :
    locEps χ w k s = locEps χ w k (1 / 2) * (((Ideal.absNorm w.asIdeal ^ (k + diffExp w) : ℕ) : ℂ) ^ (1 / 2 - s)) := by
  have hN : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (absNorm_pos w).ne'
  rw [natCast_pow_cpow hN]
  simp only [locEps]
  have e : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s * ((k + diffExp w : ℕ) : ℂ)) =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(1 / 2) * ((k + diffExp w : ℕ) : ℂ)) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((k + diffExp w : ℕ) : ℂ) * (1 / 2 - s)) := by
    rw [← Complex.cpow_add _ _ hN]; congr 1; ring
  rw [e]; ring

theorem norm_locEps_half {χ : HChar E} (hu : IsUnitary χ) {w : HeightOneSpectrum (𝓞 E)} {k : ℕ} (hk : ExpAt χ w k) :
    ‖locEps χ w k (1 / 2)‖ = 1 := by
  have hNpos : (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast absNorm_pos w
  have hG : ‖(if k = 0 then (1 : ℂ) else gaussSumAt χ w k (unif w ^ (k + diffExp w)))‖ =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
    split_ifs with h
    · simp [h]
    · have := norm_gaussSumAt_sq χ w k _ h hk hu (valuation_unif_pow w _)
      rw [← Real.sqrt_sq (norm_nonneg _), this, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      ring_nf
  rw [locEps, norm_mul, norm_mul, norm_mul, norm_locK hu, hG, Complex.norm_natCast_cpow_of_pos (absNorm_pos w),
    Complex.norm_natCast_cpow_of_pos (absNorm_pos w), one_mul, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  convert Real.rpow_zero _ using 2
  simp
  ring

theorem absNorm_different_eq_prod (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ w, w ∉ S → diffExp w = 0) :
    Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = ∏ w ∈ S, Ideal.absNorm w.asIdeal ^ diffExp w := by
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hm : ∀ w : HeightOneSpectrum (𝓞 E), w.maxPowDividing (differentIdeal ℤ (𝓞 E)) = w.asIdeal ^ diffExp w := by
    intro w
    rw [w.maxPowDividing_eq_pow_multiset_count hD, diffExp, HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hD]
  have h := Ideal.finprod_heightOneSpectrum_factorization hD
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_] at h
  · conv_lhs => rw [← h]
    rw [map_prod]
    simp only [hm, map_pow]
  · intro w hw
    by_contra h'
    apply hw
    show w.maxPowDividing _ = 1
    rw [hm, hS w h', pow_zero]

theorem finEps_eq (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ) :
    finEps χ a s = finEps χ a (1 / 2) *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s)) := by
  classical
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  set S : Finset (HeightOneSpectrum (𝓞 E)) := ((Ideal.finite_factors hD).union a.support.finite_toSet).toFinset with hSdef
  have hS : ∀ w, w ∉ S → diffExp w = 0 ∧ a w = 0 := by
    intro w hw
    simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, Finsupp.mem_support_iff,
      not_or, not_not] at hw
    exact ⟨multiplicity_eq_zero_of_not_dvd hw.1, hw.2⟩
  have hsub : ∀ f : HeightOneSpectrum (𝓞 E) → ℂ, (∀ w, diffExp w = 0 → a w = 0 → f w = 1) → Function.mulSupport f ⊆ S := by
    intro f hf w hw
    by_contra h
    exact hw (hf w (hS w h).1 (hS w h).2)
  have e1 : ∀ z, finEps χ a z = ∏ w ∈ S, locEps χ w (a w) z := fun z =>
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun w h0 h1 => by rw [h1]; exact locEps_eq_one χ h0 z)
  have e3 : (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ)) =
      ∏ w ∈ S, Ideal.absNorm w.asIdeal ^ (a w + diffExp w) := by
    rw [← absNorm_differentIdeal E (𝓞 E), absNorm_different_eq_prod S fun w hw => (hS w hw).1, Finsupp.prod,
      Finset.prod_subset (s₁ := a.support) (s₂ := S) ?_ ?_, ← Finset.prod_mul_distrib]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [← pow_add, add_comm]
    · intro w hw
      simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_coe]
      exact Or.inr hw
    · intro w _ hw
      rw [Finsupp.notMem_support_iff.1 hw, pow_zero]
  rw [e1, e1, e3, ← prod_natCast_cpow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => locEps_eq_mul χ w (a w) s

theorem norm_finEps_half {χ : HChar E} (hu : IsUnitary χ) {a : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) :
    ‖finEps χ a (1 / 2)‖ = 1 := by
  have hf := finite_mulSupport_locEps χ a (1 / 2)
  rw [finEps, finprod_eq_prod_of_mulSupport_subset _ hf.coe_toFinset.ge, norm_prod]
  exact Finset.prod_eq_one fun w _ => norm_locEps_half hu (ha w)

theorem norm_archEps {I : Type} [Fintype I] (n : I → ℤ) : ‖archEps n‖ = 1 := by
  simp [archEps]

end GlobalTheory.HeckeEpsAbs

namespace GlobalTheory.Published

open GlobalTheory.HeckeEpsAbs

theorem HeckeTateFunctionalEquation.abs (h : HeckeTateFunctionalEquation) : HeckeFunctionalEquationAbs := by
  intro E _ _ _ I _ φ hφ χ n a Λ Λ' hu hi hn ha hΛ hΛ'
  obtain ⟨Λ₀, Λ₀', h1, h2, h3⟩ := h E I φ hφ χ n a hu hi hn ha
  obtain rfl := hΛ.unique h1
  obtain rfl := hΛ'.unique h2
  refine ⟨archEps n * finEps χ a (1 / 2), ?_, fun s => ?_⟩
  · rw [norm_mul, norm_archEps, norm_finEps_half hu ha, one_mul]
  · rw [h3 s, finEps_eq χ a s]
    ring

end GlobalTheory.Published
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualKernel

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem evc_ker_iff {P : LB (A ⊗ B).left} (hP : P.IsLB) {T : Over S} (x : T ⟶ A) :
    evc hP (fst T B ≫ x) (snd T B) = 0 ↔ evc hP (snd B T ≫ x) (fst B T) = 0 := by
  constructor
  · intro h
    have e := congrArg (CechPic.pull (lift (snd B T) (fst B T)).left) h
    rwa [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e
  · intro h
    have e := congrArg (CechPic.pull (lift (snd T B) (fst T B)).left) h
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e

theorem evc_ker_mul {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) {T : Over S} (x y : T ⟶ A)
    (hx : evc hP (fst T B ≫ x) (snd T B) = 0) (hy : evc hP (fst T B ≫ y) (snd T B) = 0) :
    evc hP (fst T B ≫ (x * y)) (snd T B) = 0 := by
  rw [MonObj.comp_mul, (isAdditive_iff hP).1 hA, hx, hy, add_zero]

theorem evc_ker_one {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) (T : Over S) :
    evc hP (fst T B ≫ (1 : T ⟶ A)) (snd T B) = 0 := by
  rw [MonObj.comp_one]
  exact hA.evc_one hP _

theorem evc_ker_inv {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) {T : Over S} (x : T ⟶ A)
    (hx : evc hP (fst T B ≫ x) (snd T B) = 0) : evc hP (fst T B ≫ x⁻¹) (snd T B) = 0 := by
  have e := evc_ker_one hP hA T
  rw [← mul_inv_cancel x, MonObj.comp_mul, (isAdditive_iff hP).1 hA, hx, zero_add] at e
  exact e

end GlobalTheory.DualKernel

namespace GlobalTheory.DualKernel

theorem exists_closed_subgroup_ker : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P →
    ∃ (N : Over (Sp K)) (_ : GrpObj N) (i : N ⟶ A), IsMonHom i ∧ IsClosedImmersion i.left ∧
      Triv (ev P (fst N B ≫ i) (snd N B)) ∧
      ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → ∃ z : T ⟶ N, z ≫ i = x := by
  intro K _ _ A B _ _ P hA hB hD
  have hP := hD.isLB
  have hs : (swap P).IsLB := pull_isLB hP _
  have ht : (LB.triv (B ⊗ A).left).IsLB := LB.isLB_triv _
  have h0 : ∀ (Y : Over (Sp K)) (b : Y ⟶ B) (a : Y ⟶ A), evc ht b a = 0 := fun _ _ _ ↦ map_zero _
  have hN : Fam B (swap P) := ⟨hs, isDual_isAdditive_swap _ A B P hB hD⟩
  have hN' : Fam B (LB.triv (B ⊗ A).left) :=
    ⟨ht, (isAdditive_iff ht).2 fun _ _ _ _ ↦ by simp only [h0, add_zero]⟩
  haveI := hA.smooth
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨N, i, hi, hG⟩ := GlobalTheory.DualLocus.exists_closed_same (Sp K) B A hB (swap P) _ hN hN'
  have key : ∀ (T : Over (Sp K)) (x : T ⟶ A),
      evc hP (fst T B ≫ x) (snd T B) = 0 ↔ ∃ z : T ⟶ N, z ≫ i = x := fun T x ↦ by
    rw [← hG, same_iff hs ht, h0, evc_swap hP hs, evc_ker_iff]
  have hK : ∀ (T : Over (Sp K)) (z : T ⟶ N), evc hP (fst T B ≫ z ≫ i) (snd T B) = 0 :=
    fun T z ↦ (key T _).2 ⟨z, rfl⟩
  haveI : Mono i.left := inferInstance
  haveI : Mono i := Over.mono_of_mono_left i
  have hl : ∀ {T : Over (Sp K)} (x : T ⟶ A), evc hP (fst T B ≫ x) (snd T B) = 0 →
      ∃ z : T ⟶ N, z ≫ i = x := fun x h ↦ (key _ x).1 h
  obtain ⟨o, ho⟩ := hl (η[A] : 𝟙_ (Over (Sp K)) ⟶ A) (by
    have e := evc_ker_one hP hD.additive (𝟙_ (Over (Sp K)))
    rwa [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp] at e)
  obtain ⟨m, hm⟩ := hl ((i ⊗ₘ i) ≫ μ[A]) (by
    have e := evc_ker_mul hP hD.additive (fst N N ≫ i) (snd N N ≫ i) (hK _ _) (hK _ _)
    rwa [Hom.mul_def, ← lift_map_assoc, lift_fst_snd, Category.id_comp] at e)
  obtain ⟨n, hn⟩ := hl (i ≫ GrpObj.inv) (by
    have e := evc_ker_inv hP hD.additive i (by simpa using hK N (𝟙 N))
    rwa [Hom.inv_def] at e)
  obtain ⟨g, hg⟩ := GlobalTheory.exists_grpObj_of_mono i o m n ho hm hn
  refine ⟨N, g, i, hg, hi, (triv_ev_iff hP _ _).2 (by simpa using hK N (𝟙 N)), fun T x hx ↦ ?_⟩
  exact (key T x).1 ((triv_ev_iff hP _ _).1 hx)

end GlobalTheory.DualKernel
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KerAxes

theorem triv_of_local_evc {S : Scheme.{0}} {G T : Over S} [GrpObj G] (hG : IsAbelianScheme G)
    {P : LB (G ⊗ G).left} (hP : P.IsLB) (h2 : Triv (ev P (𝟙 G) (1 : G ⟶ G))) (x : T ⟶ G)
    (hloc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∀ (Y : Over S) (t : Y ⟶ T) (g : Y ⟶ G),
      (∀ z, t.left z ∈ V) → evc hP (t ≫ x) g = 0) :
    Triv (ev P (snd G T ≫ x) (fst G T)) := by
  rw [triv_ev_iff hP]
  obtain ⟨M, hM, hc⟩ := cls_surj (evc hP (snd G T ≫ x) (fst G T))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (G ⊗ T).left),
      Triv (M.pull f) ↔ CechPic.pull f (evc hP (snd G T ≫ x) (fst G T)) = 0 := by
    intro X f
    rw [← hc, ← cls_pull hM f (pull_isLB hM f)]
    exact (cls_eq_zero_iff (pull_isLB hM f)).symm
  refine (cls_eq_zero_iff hM).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hM (snd G T).left (lift 1 (𝟙 T)).left ?_
    (surj_restrict_snd hG T) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key, pull_evc, lift_snd_assoc, Category.id_comp, lift_fst]
    exact evc_one_right hP h2 x
  · intro p
    obtain ⟨V, hV, hz⟩ := hloc p
    refine ⟨V, hV, ?_⟩
    let U := (snd G T).left ⁻¹ᵁ V
    let Y : Over S := Over.mk (U.ι ≫ (G ⊗ T).hom)
    let i : Y ⟶ G ⊗ T := Over.homMk U.ι rfl
    show Triv (M.pull i.left)
    rw [key, pull_evc, ← Category.assoc]
    exact hz Y _ _ (fun z ↦ z.2)

theorem triv_of_memKL_pair : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a b : T ⟶ G), GlobalTheory.MemKL (G ⊗ G) P (lift a b) → (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (snd G T ≫ b) (fst G T)).left).Gen, t.IsGen) := by
  intro R _ _ G _ hG P hP h1 h2 hs T a b hx
  have hs' : (swap P).IsLB := pull_isLB hP _
  have h1' : Triv (ev P (1 : G ⟶ G) (𝟙 G)) := h1
  have h2' : Triv (ev P (𝟙 G) (1 : G ⟶ G)) := h2
  have add1 := (isAdditive_iff hP).1 (CubeNoeth.isAdditive_of_triv_axes hG hG hP h1' h2')
  have add2 := (isAdditive_iff hs').1 (CubeNoeth.isAdditive_swap_of_triv_axes hG hG hP h1' h2')
  have symm : ∀ (Y : Over (Sp R)) (u v : Y ⟶ G), evc hP v u = evc hP u v := by
    intro Y u v
    have e := congrArg (CechPic.pull (lift v u).left) ((cls_eq_iff hP hs').2 hs)
    exact e.trans (evc_swap hP hs' v u)
  have loc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∀ (Y : Over (Sp R)) (t : Y ⟶ T) (g : Y ⟶ G),
      (∀ z, t.left z ∈ V) → evc hP (t ≫ a) g = 0 ∧ evc hP (t ≫ b) g = 0 := by
    intro p
    obtain ⟨V, hV, hTV⟩ := hx p
    refine ⟨V, hV, fun Y t g ht ↦ ?_⟩
    have mk : ∀ u v : Y ⟶ G, evc hP ((t ≫ a) * u) ((t ≫ b) * v) = evc hP u v := by
      intro u v
      have e := pull_mul_eq hP hTV t ht (lift u v)
      have q : (t ≫ lift a b) * lift u v = lift ((t ≫ a) * u) ((t ≫ b) * v) := by
        ext <;> simp [MonObj.mul_comp]
      rw [q] at e
      exact e
    have e0 := mk 1 1
    rw [_root_.mul_one, _root_.mul_one, evc_one_left hP h1'] at e0
    constructor
    · have e1 := mk 1 g
      rw [_root_.mul_one, evc_one_left hP h1'] at e1
      have s := add2 Y (t ≫ b) g (t ≫ a)
      rw [evc_swap hP hs', evc_swap hP hs', evc_swap hP hs'] at s
      rw [s, e0, zero_add] at e1
      exact e1
    · have e3 := mk g 1
      rw [_root_.mul_one, evc_one_right hP h2'] at e3
      have s := add1 Y (t ≫ a) g (t ≫ b)
      rw [s, e0, zero_add] at e3
      rw [symm]
      exact e3
  refine ⟨triv_of_local_evc hG hP h2' a fun p ↦ ?_, triv_of_local_evc hG hP h2' b fun p ↦ ?_⟩
  · obtain ⟨V, hV, h⟩ := loc p
    exact ⟨V, hV, fun Y t g ht ↦ (h Y t g ht).1⟩
  · obtain ⟨V, hV, h⟩ := loc p
    exact ⟨V, hV, fun Y t g ht ↦ (h Y t g ht).2⟩

end GlobalTheory.KerAxes
end
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.holAtlas_isForm_del_dbar_smooth : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α : A.Fld), A.IsForm α →
    A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) := by
  first | exact @GlobalTheory.CxForm.isForm_del_dbar | exact GlobalTheory.CxForm.isForm_del_dbar | (intros; apply GlobalTheory.CxForm.isForm_del_dbar <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_splitPlaceBelowCMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w := by
  first | exact @GlobalTheory.SplitPlaceExists.exists_isSplitAt | exact GlobalTheory.SplitPlaceExists.exists_isSplitAt | (intros; apply GlobalTheory.SplitPlaceExists.exists_isSplitAt <;> assumption)
end
