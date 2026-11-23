module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle102
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle104
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosedImm

section Lattice
variable {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (N : ℕ)

def Alone (ε : X) : Prop := ∀ v : X, v ≠ 0 → q ε < q (ε + N • v)

variable {q N}

theorem Alone.short {ε : X} (h : Alone q N ε) : Short q N ε := fun m => by
  by_cases hm : m = 0
  · simp [hm]
  · exact (h m hm).le

theorem Alone.eq {ε β m : X} (h : Alone q N ε) (hβ : Short q N β) (e : β = ε + N • m) : β = ε := by
  by_cases hm : m = 0
  · simp [e, hm]
  · have h1 := hβ (-m)
    have h2 := h m hm
    rw [e] at h1
    simp only [smul_neg, add_neg_cancel_right] at h1
    exact absurd h2 (not_lt.2 h1)

theorem pos_of_tendsto [Module.Free ℤ X] (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) {v : X}
    (hv : v ≠ 0) : 0 < q v := by
  by_contra hn
  have hfin : {x : X | ¬ 0 < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • v) (smul_left_injective ℤ hv)
    (fun n => ?_) hfin
  change ¬ 0 < q (n • v)
  rw [q.map_smul, zsmul_eq_mul, Int.cast_mul]
  exact not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) (not_lt.1 hn))

theorem alone_zero [Module.Free ℤ X] (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (hN : N ≠ 0) :
    Alone q N (0 : X) := fun v hv => by
  rw [map_zero, zero_add]
  refine pos_of_tendsto hq ?_
  rw [← natCast_zsmul]
  exact smul_ne_zero (by exact_mod_cast hN) hv

end Lattice

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (e : U ≤ V) (a : R) : resG X e (constFn p V a) = constFn p U a := by
  unfold constFn
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  erw [Scheme.Hom.appLE_map]

theorem const_zero {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero]

theorem isRatio_lin {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {H : LB X} {J : Type} [Fintype J]
    {s : J → H.Sec} {a : J → k} {φ t : H.Sec} (h : IsLin p s a φ) {W : X.Opens} {r : J → Γ(X, W)}
    (hr : ∀ j, IsRatio (s j) t W (r j)) : IsRatio φ t W (∑ j, constFn p W (a j) * r j) := fun l => by

  rw [h l, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, res_const, res_const, hr j l, _root_.mul_assoc]

variable {k : Type} [Field k] (Φ : FibPre k)

theorem isLB_H (d : ℕ) : (Φ.H d).IsLB := by
  have key : ∀ (U V : Φ.E.B.left.Opens) (h : V ≤ U) (h' : Φ.D.q.left ⁻¹ᵁ V ≤ Φ.D.q.left ⁻¹ᵁ U)
      (u : Γ(Φ.E.B.left, U)ˣ),
      res h' (pullU Φ.D.q.left U u ^ d) = pullU Φ.D.q.left V (res h u) ^ d := by
    intro U V h h' u
    rw [map_pow]
    congr 1
    ext
    exact (congrArg (fun φ => φ.hom (u : Γ(Φ.E.B.left, U))) (Φ.D.q.left.naturality (homOfLE h).op)).symm
  refine ⟨?_, fun i => ?_, fun i j l => ?_⟩
  · show ⨆ l, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l = ⊤
    rw [← Scheme.Hom.preimage_iSup, Φ.isLB.cover]; rfl
  · have := congrArg (fun u => pullU Φ.D.q.left _ u ^ d) (Φ.isLB.g_self i)
    simp only [map_one, one_pow] at this
    exact (key _ _ _ (Scheme.Hom.preimage_mono _ (le_inf le_rfl le_rfl)) _).trans this
  · have := congrArg (fun u => pullU Φ.D.q.left _ u ^ d) (Φ.isLB.cocycle i j l)
    simp only [map_mul, mul_pow] at this
    rw [← key _ _ _ (Scheme.Hom.preimage_mono _ inf_le_left),
      ← key _ _ _ (Scheme.Hom.preimage_mono _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right)),
      ← key _ _ _ (Scheme.Hom.preimage_mono _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right))] at this
    exact this

theorem isRatio_pull {s t : Φ.N₀.Sec} {φ ψ : (Φ.H 1).Sec}
    (hφ : ∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (s.f l))
    (hψ : ∀ l, ψ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l))
    {V : Φ.E.B.left.Opens} {r : Γ(Φ.E.B.left, V)} (h : IsRatio s t V r) :
    IsRatio φ ψ (Φ.D.q.left ⁻¹ᵁ V) ((Φ.D.q.left.app V).hom r) := fun l => by
  have e := congrArg (Φ.D.q.left.app (V ⊓ Φ.N₀.U l)).hom (h l)
  rw [map_mul, app_res _ _ (Φ.D.q.left.preimage_mono inf_le_right),
    app_res _ _ (Φ.D.q.left.preimage_mono inf_le_left),
    app_res _ _ (Φ.D.q.left.preimage_mono inf_le_right)] at e
  rw [hφ, hψ]
  exact e

variable {Φ} {N : ℕ} {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X}
  {F : J → (Φ.H 1).Sec}

theorem pure_of_alone (hG : Φ.Good N q cls F) {ε : Φ.E.X} (hε : Alone q N ε) {i : J} (hi : cls i = ε) :
    Φ.Pure ε (F i) := fun β hβ => by
  obtain ⟨h1, m, hm⟩ := hG.supp i β hβ
  exact hε.eq h1 (hi ▸ hm)

theorem onto_of_alone (hG : Φ.Good N q cls F) {ε : Φ.E.X} (hε : Alone q N ε) {φ : (Φ.H 1).Sec}
    (hφ : Φ.Pure ε φ) : ∃ a : J → k, (∀ i, a i ≠ 0 → cls i = ε) ∧
      ∀ l, Φ.wt φ ε l = ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) ε l := by
  obtain ⟨a, ha, h⟩ := hG.onto ε hε.short φ hφ
  refine ⟨a, fun i hi => ?_, h⟩
  obtain ⟨m, hm⟩ := ha i hi
  exact hε.eq (m := -m) (hG.short i) (by rw [hm]; simp)

theorem isLin_of_alone (hG : Φ.Good N q cls F) {ε : Φ.E.X} (hε : Alone q N ε) {φ : (Φ.H 1).Sec}
    (hφ : Φ.Pure ε φ) : ∃ a : J → k, IsLin Φ.G.hom F a φ := by
  obtain ⟨a, ha, h⟩ := onto_of_alone hG hε hφ
  refine ⟨a, fun l => eq_of_weight_eq Φ.D (Φ.ch l) _ (Φ.aff l) (Φ.le l) fun χ => ?_⟩
  refine Eq.trans ?_ (WtLin.weight_sum Φ F a χ l).symm
  by_cases hχ : χ = ε
  · subst hχ
    exact h l
  · have h0 : Φ.wt φ χ l = 0 := by
      by_contra hne
      exact hχ (hφ ⟨l, hne⟩)
    refine h0.trans (Finset.sum_eq_zero fun i _ => ?_).symm
    by_cases hi : a i = 0
    · rw [hi, const_zero, zero_mul]
    · have h1 : Φ.wt (F i) χ l = 0 := by
        by_contra hne
        exact hχ (pure_of_alone hG hε (ha i hi) ⟨l, hne⟩)
      rw [h1, mul_zero]

theorem immBy_weight_zero : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → ImmBy Φ.G.hom (Φ.H 1) F {i | cls i = 0}) := by
  intro hL hL2 k _ _ Φ g N N' q J _ cls F π hB hG hg
  classical
  have h4 := hB.four
  have h0 : Alone q N (0 : Φ.E.X) := alone_zero hG.pos (by omega)
  obtain ⟨e, he, -⟩ := GlobalTheory.exists_basis_unique_min_and_sums_separated Φ.E.X q hG.pos _ g N N' _ rfl
    (by omega) hB.lll hB.sep
  have hp : ∀ i : {i // cls i = 0}, Φ.Pure 0 (F i.1) := fun i => pure_of_alone hG h0 i.2
  choose τ hτ₁ hτ₂ hτ₃ using fun i => (FibPre.pure_zero k Φ).2 _ (hp i)
  obtain ⟨m, t, ht⟩ := GlobalTheory.T.exists_closedImmersion_abelianPart_bundle hL hL2 k Φ N h4 π
  have := Φ.E.isAbelian.proper
  obtain ⟨hcov, hloc⟩ := GlobalTheory.T.isClosedImmersionBySections_of_span k _ Φ.E.B.hom Φ.N₀ Φ.isLB _ _ t τ ht fun n => by
    obtain ⟨φ, hφ, hφ'⟩ := (FibPre.pure_zero k Φ).1 (t n)
    obtain ⟨a, ha, h⟩ := onto_of_alone hG h0 hφ
    refine ⟨fun i => a i.1, fun l => ?_⟩
    rw [← hφ', h, ← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = 0),
      Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {i // ¬ cls i = 0} =>
        constFn Φ.E.B.hom _ (a i.1) * Φ.wt (F i.1) 0 l) fun i _ => by
          have : a i.1 = 0 := by_contra fun hne => i.2 (ha _ hne)
          rw [this, const_zero, zero_mul], add_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [hτ₁]
  refine ⟨?_, fun i hi => ?_⟩
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (show Φ.D.q.left x ∈ ⊤ from trivial))
    obtain ⟨-, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i.1, TopologicalSpace.Opens.mem_iSup.2 ⟨i.2, ?_⟩⟩
    rw [hτ₃]
    exact hi
  · obtain ⟨haff, ρ, hρ, hgen⟩ := hloc ⟨i, hi⟩ trivial
    have hle := (hτ₃ ⟨i, hi⟩).ge
    have hu := fun s => SecRatio.existsUnique_isRatio (isLB_H Φ 1) s (F i) _ hle
    have := Φ.D.q_affine
    rw [hτ₃ ⟨i, hi⟩]
    choose r hr hr' using fun j => hu (F j)
    refine ⟨haff.preimage _, r, hr, ?_⟩
    refine GlobalTheory.T.pureSection_ratios_generate_functions k Φ _ e (F i) _ haff (hp ⟨i, hi⟩) hle (GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at hL hL2 k Φ N h4 π) _
      (fun a => ?_) fun n φ y hφ hy => ?_
    · have ha : a ∈ Subring.closure _ := hgen.ge (Subring.mem_top a)
      refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ ha)
      rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
      · exact Subring.subset_closure (Or.inl ⟨c, (WtLin.app_constFn _ _ _ (Over.w Φ.D.q) _ c).symm⟩)
      · exact Subring.subset_closure (Or.inr ⟨j.1,
          (hr' _ _ (isRatio_pull Φ (hτ₂ j) (hτ₂ ⟨i, hi⟩) (hρ j))).symm⟩)
    · obtain ⟨a, ha⟩ : ∃ a : J → k, IsLin Φ.G.hom F a φ :=
        hφ.elim (isLin_of_alone hG fun v hv => (he n v hv).1) (isLin_of_alone hG fun v hv => (he n v hv).2)
      rw [(hu φ).unique hy (isRatio_lin _ ha hr)]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨_, rfl⟩))

end GlobalTheory.ZH.ClosedImm
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

section Bundles

variable {W X Y : Scheme.{0}}

theorem lbIso_pullback {L M : LB X} (h : LBIso L M) (j : Y ⟶ X) : LBIso (L.pull j) (M.pull j) :=
  LBIso.chartPull (GlobalTheory.chartPullPull L j) (GlobalTheory.chartPullPull M j) h

theorem lbIso_pull_pull {L : LB X} (hL : L.IsLB) {a : Y ⟶ X} (j : W ⟶ Y) {a' : W ⟶ X} (ha : a' = j ≫ a) :
    LBIso (L.pull a') ((L.pull a).pull j) :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (GlobalTheory.chartPullPull _ j) (lbIso_refl (pull_isLB hL a))

theorem lbIso_pull_comp {Z : Scheme.{0}} {L : LB X} {M : LB Z} {a : Y ⟶ X} {b : Y ⟶ Z} (j : W ⟶ Y) {a' : W ⟶ X}
    {b' : W ⟶ Z} (ha : a' = j ≫ a) (hb : b' = j ≫ b) (h : LBIso (L.pull a) (M.pull b)) :
    LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (chartPullSame M _ _ _ j fun _ => hb) h

theorem lbIso_pull_of_lbIso {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : W ⟶ Y) {a' : W ⟶ X}
    (ha : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (GlobalTheory.chartPullPull M j) (chartPullSame L _ _ _ j fun _ => ha) h

end Bundles

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_forall_mem {V : (Sp R).Opens} (hV : genericPoint (Sp R) ∈ V) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∈ V := by
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  refine ⟨a, ?_, fun R' _ g hg z => hle ?_⟩
  · rintro rfl
    simp at ha
  · exact fun h => z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hg)

theorem exists_forall_notMem {C : Set (Sp R)} (hC : IsClosed C)
    (h : ∀ z : Sp K, spMap (algebraMap R K) z ∉ C) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∉ C := by
  have hg : genericPoint (Sp R) ∈ Set.range (spMap (algebraMap R K)) := by
    rw [(IsGenericPointHom.fractionField R K).range_eq]; rfl
  obtain ⟨z, hz⟩ := hg
  exact exists_forall_mem (V := ⟨Cᶜ, hC.isOpen_compl⟩) (hz ▸ h z)

theorem exists_isPullback_stalk {Y Y₀ : Scheme.{0}} {p : Y ⟶ Sp R} {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap (algebraMap R K))) :
    ∃ p₁, IsPullback φ p₁ p ((Sp R).fromSpecStalk (genericPoint (Sp R))) := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  refine ⟨p₀ ≫ e.hom, h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) ?_⟩
  simpa using he.symm

theorem exists_lift_open {S S' Y Y' : Scheme.{0}} (p : Y ⟶ S) (V : S.Opens) {π : Y' ⟶ Y} {p' : Y' ⟶ S'}
    {t : S' ⟶ S} (w : π ≫ p = p' ≫ t) (ht : ∀ z, t z ∈ V) :
    ∃ l : Y' ⟶ pullback p V.ι, l ≫ pullback.fst p V.ι = π := by
  refine ⟨pullback.lift π (IsOpenImmersion.lift V.ι (p' ≫ t) ?_) ?_, pullback.lift_fst _ _ _⟩
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact ht _
  · exact w.trans (IsOpenImmersion.lift_fac _ _ _).symm

theorem exists_hom {Y X Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p] (q : X ⟶ Sp R)
    [LocallyOfFinitePresentation q] {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap (algebraMap R K))) (u₀ : Y₀ ⟶ X) (hu : u₀ ≫ q = φ ≫ p) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        ∃ u : Y' ⟶ X, u ≫ q = π ≫ p ∧ ∀ φ' : Y₀ ⟶ Y', φ' ≫ π = φ → φ' ≫ u = u₀ := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨V, hV, -, w, u, hw, hwu, hq⟩ := StalkLimit.exists_spread h₁ q u₀ hu
  obtain ⟨a, ha, H⟩ := exists_forall_mem hV
  refine ⟨a, ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V e (H R' g hg)
  refine ⟨l ≫ u, by rw [Category.assoc, hq, reassoc_of% hl], fun φ' hφ' => ?_⟩
  have : φ' ≫ l = w := by
    rw [← cancel_mono (pullback.fst p V.ι), Category.assoc, hl, hφ', hw]
  rw [reassoc_of% this, hwu]

theorem exists_lbIso {Y Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p]
    {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K} (h : IsPullback φ p₀ p (spMap (algebraMap R K))) {M N : LB Y}
    (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull φ) (N.pull φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        LBIso (M.pull π) (N.pull π) := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit h₁
  obtain ⟨V₀⟩ : Nonempty (StalkLimit.AffNhd (genericPoint (Sp R))) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((StalkLimit.diagram _ p).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V₀.1.ι)
  have : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V₀.1.ι)
  let ι₀ : (StalkLimit.diagram _ p).obj V₀ ⟶ Y := pullback.fst p V₀.1.ι
  have e₀ : φ = (StalkLimit.cone h₁).π.app V₀ ≫ ι₀ := (StalkLimit.cone_π_fst h₁ V₀).symm
  obtain ⟨V, i, HV⟩ := exists_lbIso_of_isLimit (StalkLimit.diagram _ p) (fun V => (StalkLimit.cone h₁).π.app V)
    (fun i => (StalkLimit.cone h₁).w i) hc (M.pull ι₀) (N.pull ι₀) (pull_isLB hM _) (pull_isLB hN _)
    (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hM _ e₀).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) H (lbIso_pull_pull hN _ e₀)))
  have e₁ : pullback.fst p V.1.ι = (StalkLimit.diagram _ p).map i ≫ ι₀ := (StalkLimit.diagram_map_fst _ p i).symm
  have HV' : LBIso (M.pull (pullback.fst p V.1.ι)) (N.pull (pullback.fst p V.1.ι)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _) (lbIso_pull_pull hM _ e₁)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) HV
        (lbIso_pull_pull hN _ e₁).symm)
  obtain ⟨a, ha, Ha⟩ := exists_forall_mem V.2.1
  refine ⟨a, ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V.1 e (Ha R' g hg)
  exact lbIso_pull_comp l hl.symm hl.symm HV'

theorem exists_projective_model {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Sp K) [IsProper f₀] {L₀ : LB X₀}
    (hL : IsAmpleLB L₀) (hL' : L₀.IsLB) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Sp R) (φ : X₀ ⟶ X) (H : LB X) (N : ℕ), IsProper f ∧
      IsPullback φ f₀ f (spMap (algebraMap R K)) ∧ H.IsLB ∧ IsAmpleLB H ∧ 1 ≤ N ∧ LBIso (lbPow L₀ N) (H.pull φ) := by
  obtain ⟨N, hN, M, s, hs⟩ := hL.exists_veryAmpleBy f₀
  obtain ⟨hs, hc⟩ := (ProjSpace.veryAmpleBy_iff f₀ s).1 hs
  let c := ProjSpace.toProj f₀ s hs
  let u := ProjSpace.baseChange M (algebraMap R K)
  have hu := ProjSpace.isPullback_baseChange M (algebraMap R K)
  have : Flat (spMap (algebraMap R K)) := flat_specMap_localization (nonZeroDivisors R) K
  have : Mono (spMap (algebraMap R K)) := mono_specMap_localization (nonZeroDivisors R) K
  have : Flat u := MorphismProperty.of_isPullback (P := @Flat) hu.flip inferInstance
  have : Mono u := MorphismProperty.of_isPullback (P := .monomorphisms _) hu.flip
    (inferInstanceAs (Mono (spMap (algebraMap R K))))
  have : QuasiCompact u := MorphismProperty.of_isPullback (P := @QuasiCompact) hu.flip inferInstance
  have hp := isPullback_toImage_of_isClosedImmersion (c ≫ u) c u rfl
  have := isProper_str R M
  refine ⟨(c ≫ u).image, (c ≫ u).imageι ≫ PSpace.str R M, (c ≫ u).toImage,
    (ProjSpace.O1 R M).pull (c ≫ u).imageι, N, inferInstance, ?_, pull_isLB (ProjSpace.O1_isLB R M) _,
    (isAmple_projective_O_one R M).pull_of_isClosedImmersion _, hN, ?_⟩
  · have := hp.flip.paste_vert hu
    rwa [ProjSpace.toProj_str] at this
  · have h1 {Y : Scheme.{0}} (F : Y ⟶ PSpace R M) := pull_isLB (ProjSpace.O1_isLB R M) F
    refine LBIso.trans (isLB_lbPow hL' _) (pull_isLB (ProjSpace.O1_isLB K M) c) (pull_isLB (h1 _) _)
      (ProjSpace.lbIso_pullback_O1_toProj f₀ s hs).symm ?_
    refine LBIso.trans (pull_isLB (ProjSpace.O1_isLB K M) c) (h1 (c ≫ u)) (pull_isLB (h1 _) _)
      (lbIso_pull_of_lbIso (ProjSpace.lbIso_pull_O1 M (algebraMap R K)).symm c rfl) ?_
    exact lbIso_pull_pull (ProjSpace.O1_isLB R M) _ (Scheme.Hom.toImage_imageι _).symm

theorem exists_isAmpleLB {X X₀ : Scheme.{0}} (f : X ⟶ Sp R) [QuasiCompact f] [QuasiSeparated f]
    {φ : X₀ ⟶ X} {f₀ : X₀ ⟶ Sp K} (h : IsPullback φ f₀ f (spMap (algebraMap R K))) {L H : LB X} {L₀ : LB X₀}
    (hL : L.IsLB) (hH : H.IsLB) (hL₀ : L₀.IsLB) (hA : IsAmpleLB H) {N : ℕ} (hN : 1 ≤ N)
    (e : LBIso L₀ (L.pull φ)) (e' : LBIso (lbPow L₀ N) (H.pull φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) →
        IsAmpleLB (L.pull π) := by
  obtain ⟨a, ha, Ha⟩ := exists_lbIso f h (isLB_lbPow hL N) hH
    (LBIso.trans (pull_isLB (isLB_lbPow hL N) _) (isLB_lbPow (pull_isLB hL _) N) (pull_isLB hH _)
      (lbIso_lbPow_pull hL φ N).symm
      (LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (isLB_lbPow hL₀ N) (pull_isLB hH _) (lbIso_lbPow e N).symm e'))
  refine ⟨a, ha, fun R' _ g hg X' π f' hp => ?_⟩
  have : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance
  refine (isAmpleLB_pow_iff (pull_isLB hL π) hN).1 ((hA.pull_of_isAffineHom π).of_lbIso
    (isLB_lbPow (pull_isLB hL _) N) ?_)
  exact LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _) (pull_isLB hH _)
    (lbIso_lbPow_pull hL π N) (Ha R' g hg X' π f' hp.w)

end GlobalTheory.GenSpread
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SS

theorem exists_finite_torusExtension_of_torusExt : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExt G) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k'), Nonempty (TorusExtension (fieldBaseChange k k' G)) := by
  intro k _ G _ ⟨T⟩
  have := T.q_hom
  have := T.i_hom
  obtain ⟨-, k', _, _, hfin, X, _, hfree, hX, e, he⟩ := GlobalTheory.torus_isAffineHom_and_splits_finite k T.T₀ T.isTorus
  refine ⟨k', inferInstance, inferInstance, hfin, ?_⟩
  let f : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hq := isPullback_overPullback_map_left f T.q
  have : IsMonHom e.inv := inferInstance
  refine ⟨{ X := X
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.inv ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }⟩
  have hk := T.isKernel.map (Over.pullback f)
  refine IsPullback.of_iso hk e (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact toUnit_unique _ _
  · simp
  · simp

end GlobalTheory.SS
end
