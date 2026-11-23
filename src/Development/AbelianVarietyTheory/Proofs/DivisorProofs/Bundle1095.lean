module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieFreeNearTwoPrimes
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTLie

open GlobalTheory.EigenSplit GlobalTheory.TanMod GlobalTheory.DetCompare GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs

theorem eq_zero_of_mem_eigenSub_of_sum {O k N : Type} [CommRing O] [Field k] [AddCommGroup N] [Module k N]
    (ρ : O →+* Module.End k N) (σ : O →+* k) {κ : Type} (χ : κ → O →+* k) (hχ : ∀ i, χ i ≠ σ)
    (s : Finset κ) : ∀ (m : N) (y : κ → N), m ∈ eigenSub ρ σ → (∀ i, y i ∈ eigenSub ρ (χ i)) →
      m = ∑ i ∈ s, y i → m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m y _ _ h; simpa using h
  | insert j s hj ih =>
    intro m y hm hy h
    obtain ⟨c, hc⟩ : ∃ c, χ j c ≠ σ c := by
      by_contra hcon
      push_neg at hcon
      exact hχ j (RingHom.ext hcon)
    let f : Module.End k N := ρ c - χ j c • LinearMap.id
    have hfm : f m = (σ c - χ j c) • m := by
      simp [f, mem_eigenSub.1 hm c, sub_smul]
    have hfy : ∀ i, f (y i) = (χ i c - χ j c) • y i := fun i => by
      simp [f, mem_eigenSub.1 (hy i) c, sub_smul]
    have h1 : (σ c - χ j c) • m = ∑ i ∈ s, (χ i c - χ j c) • y i := by

      rw [← hfm, h, Finset.sum_insert hj, map_add (f := _), map_sum, hfy j, sub_self, zero_smul, zero_add]
      exact Finset.sum_congr rfl fun i _ => hfy i
    have h2 := ih ((σ c - χ j c) • m) (fun i => (χ i c - χ j c) • y i)
      (Submodule.smul_mem _ _ hm) (fun i => Submodule.smul_mem _ _ (hy i)) h1
    have hne : σ c - χ j c ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
    exact (smul_eq_zero.1 h2).resolve_left hne

theorem exists_ringHom_avoid {F : Type} [Field F] [NumberField F] [IsCMField F] (bar : 𝓞 F ≃+* 𝓞 F)
    (bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F))
    (ω : 𝓞 F) (tr nm : ℤ) (tr_eq : ω + bar ω = (tr : 𝓞 F)) (nm_eq : ω * bar ω = (nm : 𝓞 F))
    (disc_neg : tr ^ 2 - 4 * nm < 0)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (ρ : k) (hρ : ρ ^ 2 - tr * ρ + nm = 0)
    (a : ℕ) (ha : 2 * a < Module.finrank ℚ F) (χ : Fin a → (𝓞 F →+* k)) :
    ∃ σ : 𝓞 F →+* k, σ ω = ρ ∧ ∀ i, χ i ≠ σ := by
  classical
  let cj : F →+* F := ((IsCMField.complexConj F : F ≃ₐ[maximalRealSubfield F] F) : F →+* F)
  have e1 : (ω : F) + ((bar ω : 𝓞 F) : F) = (tr : F) := by
    have := congrArg (fun z : 𝓞 F => (z : F)) tr_eq
    simpa using this
  have e2 : (ω : F) * ((bar ω : 𝓞 F) : F) = (nm : F) := by
    have := congrArg (fun z : 𝓞 F => (z : F)) nm_eq
    simpa using this
  have hcω : cj (ω : F) = (tr : F) - (ω : F) := by
    have : cj (ω : F) = ((bar ω : 𝓞 F) : F) := (bar_eq ω).symm
    rw [this]; linear_combination e1
  have hcc : ∀ z, cj (cj z) = z := fun z => IsCMField.complexConj_apply_apply F z
  have hroot : ∀ τ : F →+* k, τ ω ^ 2 - tr * τ ω + nm = 0 := by
    intro τ
    have h1 : (ω : F) ^ 2 - tr * (ω : F) + nm = 0 := by
      linear_combination (ω : F) * e1 - e2
    have := congrArg τ h1
    simpa using this
  have hne : ρ ≠ (tr : k) - ρ := by
    intro h
    have h3 : ((tr ^ 2 - 4 * nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (2 * ρ - tr) * h - 4 * hρ
    have h4 : tr ^ 2 - 4 * nm = 0 := by exact_mod_cast h3
    omega
  have hside : ∀ τ : F →+* k, τ ω ≠ ρ → τ ω = (tr : k) - ρ := by
    intro τ h
    have : (τ ω - ρ) * (τ ω - ((tr : k) - ρ)) = 0 := by
      linear_combination hroot τ - hρ
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd (sub_eq_zero.1 h') h
    · exact sub_eq_zero.1 h'
  have hconj : ∀ τ : F →+* k, (τ.comp cj) ω = (tr : k) - τ ω := by
    intro τ
    simp [hcω]
  let T := (Finset.univ : Finset (F →+* k)).filter (fun τ => τ ω = ρ)
  let Tc := (Finset.univ : Finset (F →+* k)).filter (fun τ => ¬ τ ω = ρ)
  have hcard : T.card = Tc.card := by
    refine Finset.card_nbij' (fun τ => τ.comp cj) (fun τ => τ.comp cj) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [T, Tc, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      rw [hconj, hτ]
      exact fun h => hne h.symm
    · intro τ hτ
      simp only [T, Tc, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      rw [hconj, hside τ hτ]; ring
    · intro τ _; ext z; simp [hcc]
    · intro τ _; ext z; simp [hcc]
  have htot : T.card + Tc.card = Module.finrank ℚ F := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, NumberField.Embeddings.card]
  by_contra hcon
  push_neg at hcon
  have hsub : T.image (fun τ => τ.comp (algebraMap (𝓞 F) F)) ⊆ Finset.univ.image χ := by
    intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hσ
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨i, hi⟩ := hcon (τ.comp (algebraMap (𝓞 F) F)) (by simpa using hτ)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hinj : Set.InjOn (fun τ : F →+* k => τ.comp (algebraMap (𝓞 F) F)) T := by
    intro τ _ τ' _ h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hle
  have hle2 := (Finset.card_image_le (s := (Finset.univ : Finset (Fin a))) (f := χ))
  rw [Finset.card_univ, Fintype.card_fin] at hle2
  omega

end GlobalTheory.HTLie

namespace GlobalTheory.HTLie

open GlobalTheory.EigenSplit GlobalTheory.TanMod GlobalTheory.DetCompare GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs

theorem exists_lieMult_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), 2 * D.a < Module.finrank ℚ D.F → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ σ : 𝓞 D.F →+* k, LieMult (o.act.toF D) x σ 0 := by
  intro p _ D R _ b N S s o ha k _ _ _ x β hx
  have hρ : β b.ρ ^ 2 - D.tr * β b.ρ + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  obtain ⟨σ, hσω, hσ⟩ := exists_ringHom_avoid D.bar D.bar_eq D.ω D.tr D.nm D.tr_eq D.nm_eq D.disc_neg k
    (β b.ρ) hρ D.a ha (fun i => β.comp (b.t i))
  refine ⟨σ, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun w hw =>
    ⟨Fin.elim0, ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩, fun c _ => funext fun i => Fin.elim0 i⟩⟩
  rw [List.ofFn_zero, List.prod_nil]
  obtain ⟨w', hw', hwprod⟩ := o.lie k β x hx w ⟨hw.1, by
    have := hw.2 D.ω
    rw [hσω] at this
    exact this⟩
  have hlie : ∀ i, IsLieEigen (o.act.toF D) x (β.comp (b.t i)) (w' i) :=
    fun i => ⟨(hw' i 0).1, fun c => (hw' i c).2⟩
  obtain ⟨h1, h2⟩ := (isLieEigen_iff _ x σ w).1 hw
  choose g1 g2 using fun i => (isLieEigen_iff _ x _ (w' i)).1 (hlie i)
  have hm := (mem_eigenspace_iff _ x σ _).1 h2
  have hy := fun i => (mem_eigenspace_iff _ x _ _).1 (g2 i)
  have hsum : lieEquiv x ⟨w, h1⟩ = ∑ i ∈ Finset.univ, lieEquiv x ⟨w' i, g1 i⟩ := by
    apply TanSp.ext
    rw [TanSp.pt_sum]
    show w = ∏ i, w' i
    rw [hwprod, List.prod_ofFn]
  have h0 := eq_zero_of_mem_eigenSub_of_sum _ σ (fun i => β.comp (b.t i)) hσ Finset.univ _ _ hm hy hsum
  exact congrArg TanSp.pt h0

end GlobalTheory.HTLie
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieCoordR

open ReciprocityTheory.ChartRestriction.G.Chart (sp fB sp_hom_fB)

section Iso

variable {W : Type} [CommRing W] {R' : Type} [CommRing R'] [Algebra W R']

theorem epsHom_w : 𝟙 (Spec (CommRingCat.of (DualNumber R'))) ≫ (sp (R₀ := W) (DualNumber R')).hom =
    (epsPtR (spMap (algebraMap W R'))).hom := by
  rw [Category.id_comp]
  exact (sp_hom_fB (R := W) (R' := R') (P := DualNumber R')).symm

theorem epsInv_w : 𝟙 (Spec (CommRingCat.of (DualNumber R'))) ≫ (epsPtR (spMap (algebraMap W R'))).hom =
    (sp (R₀ := W) (DualNumber R')).hom := by
  rw [Category.id_comp]
  exact sp_hom_fB (R := W) (R' := R') (P := DualNumber R')

def epsHom : epsPtR (spMap (algebraMap W R')) ⟶ sp (R₀ := W) (DualNumber R') :=
  Over.homMk (𝟙 (Spec (CommRingCat.of (DualNumber R')))) epsHom_w

def epsInv : sp (R₀ := W) (DualNumber R') ⟶ epsPtR (spMap (algebraMap W R')) :=
  Over.homMk (𝟙 (Spec (CommRingCat.of (DualNumber R')))) epsInv_w

end Iso

section Main
open GlobalTheory.SqZero
variable {W : Type} [CommRing W] {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR W ⟶ G)} {R' : Type} [CommRing R'] [Algebra W R']

theorem epsHom_epsInv : epsHom (W := W) (R' := R') ≫ epsInv = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp (𝟙 (Spec (CommRingCat.of (DualNumber R')))))

theorem epsInv_epsHom : epsInv (W := W) (R' := R') ≫ epsHom = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp (𝟙 (Spec (CommRingCat.of (DualNumber R')))))

theorem fst_left : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (fstS W R')).left =
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom := rfl

theorem isTanOver_epsInv (w : epsPtR (spMap (algebraMap W R')) ⟶ G)
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left =
        (1 : Over.mk (spMap (algebraMap W R')) ⟶ G).left) : IsTanOver (epsInv ≫ w) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, fst_left]
  exact (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·)
    (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) w.left)).trans hw


variable (v) in
def coordPt (c : Fin n → R') : epsPtR (spMap (algebraMap W R')) ⟶ G :=
  epsHom ≫ tanExp v c

theorem coordPt_injective [Smooth G.hom] (hv : IsLieBasis v) :
    Function.Injective (coordPt (R' := R') v) := by
  intro c c' h
  have h' := congrArg (epsInv ≫ ·) h
  simp only [coordPt] at h'
  rw [← Category.assoc, ← Category.assoc, epsInv_epsHom, Category.id_comp, Category.id_comp] at h'
  exact (LieTwo.isLieBasisOver_of_expBij (expBij (DualNumber R') hv)).1 c c' h'

theorem coordPt_range [Smooth G.hom] (hv : IsLieBasis v) (w : epsPtR (spMap (algebraMap W R')) ⟶ G) :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left =
        (1 : Over.mk (spMap (algebraMap W R')) ⟶ G).left ↔ w ∈ Set.range (coordPt v) := by
  constructor
  · intro hw
    obtain ⟨s, hs⟩ := (LieTwo.isLieBasisOver_of_expBij (expBij (DualNumber R') hv)).2 _
      (isTanOver_epsInv w hw)
    exact ⟨s, by rw [coordPt, ← hs, ← Category.assoc, epsHom_epsInv, Category.id_comp]⟩
  · rintro ⟨s, rfl⟩
    have := congrArg (fun f => Over.Hom.left f) (isTanOver_tanExp (S := R') hv.1 s)
    rw [Over.comp_left, fst_left] at this
    rw [coordPt, Over.comp_left]
    exact (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·)
      (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) (tanExp v s).left)).trans this

theorem coordPt_add (hv : IsLieBasis v) (c c' : Fin n → R') :
    coordPt v (c + c') = coordPt v c * coordPt v c' := by
  rw [coordPt, coordPt, coordPt, LieTwo.tanExp_add hv.1, MonObj.comp_mul]

theorem dualScale_eq (s : R') : (dualScale W s).toRingHom = ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR])
    (by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR, mul_comm])

theorem coordPt_smul (s : R') (c : Fin n → R') :
    (coordPt v (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (coordPt v c).left := by
  have h1 : s • c = fun i => c i * s := funext fun i => by simp [mul_comm]
  rw [coordPt, coordPt, Over.comp_left, Over.comp_left, h1, ← scl_tanExp, scl, Over.comp_left,
    ReciprocityTheory.ChartRestriction.G.Chart.spMap_left, dualScale_eq]
  exact (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) _).trans
    (congrArg (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ ·)
      (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) (tanExp v c).left)).symm


variable (v) in
def lieMat (hv : IsLieBasis v) (u : G ⟶ G) : Matrix (Fin n) (Fin n) W := by
  classical
  exact if h : ∀ i, IsTangent (v i ≫ u) then
    Matrix.transpose (Matrix.of fun i => (hv.2 _ (h i)).exists.choose) else 0

theorem isTangent_comp (hv : ∀ i, IsTangent (v i)) (u : G ⟶ G) [IsMonHom u] (i : Fin n) :
    IsTangent (v i ≫ u) := by
  unfold IsTangent at *
  rw [Over.comp_left, ← Category.assoc, hv i, ← Over.comp_left, IsMonHom.one_hom]

theorem comp_eq_tanExp (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (i : Fin n) :
    v i ≫ u = tanExp v (fun j => lieMat v hv u j i) := by
  have h := isTangent_comp hv.1 u
  have hc := (hv.2 _ (h i)).exists.choose_spec
  rw [isLieComb_iff_lieExp] at hc
  rw [hc]
  simp only [lieMat, dif_pos h, Matrix.transpose_apply, Matrix.of_apply]

theorem coordPt_comp (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (c : Fin n → R') :
    coordPt v c ≫ u = coordPt v (((lieMat v hv u).map (algebraMap W R')).mulVec c) := by
  have h1 : tanExp v c ≫ u = tanExp (fun i => v i ≫ u) c := by
    simp only [tanExp, lieExp]
    exact (map_prod (IsMonHom.monoidHom u (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := W) (DualNumber R'))) _ _).trans
      (Finset.prod_congr rfl fun i _ => by
        show (_ ≫ v i) ≫ u = _
        exact Category.assoc _ _ _)
  have hM : ∀ i, res (Algebra.ofId W R') (v i ≫ u) =
      tanExp v (Matrix.of (fun i j => algebraMap W R' (lieMat v hv u j i)) i) := by
    intro i
    rw [comp_eq_tanExp hv u i, res_tanExp]
    rfl
  have key : Matrix.vecMul c (Matrix.of (fun i j => algebraMap W R' (lieMat v hv u j i))) =
      ((lieMat v hv u).map (algebraMap W R')).mulVec c := by
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [coordPt, coordPt, Category.assoc, h1, LieTwo.tanExp_eq_vecMul hv.1 hM, key]

end Main

theorem exists_coords_baseChange : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∃ T : (Fin n → R') → (epsPtR (spMap β) ⟶ G), Function.Injective T ∧ (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (s : R') c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c) := by
  intro W _ _ G _ _ hsm
  haveI := hsm
  obtain ⟨n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis G hsm
  refine ⟨n, lieMat v hv, fun R' _ β => ?_⟩
  letI := β.toAlgebra
  exact ⟨coordPt v, coordPt_injective hv, coordPt_range hv, coordPt_add hv, coordPt_smul,
    fun u hu c => by haveI := hu; exact coordPt_comp hv u c⟩

end GlobalTheory.LieCoordR
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_eq_of_cohomologous : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c' → c = c' := by
  first | exact @GlobalTheory.LBObs.obU_eq_of_cohomologous | exact GlobalTheory.LBObs.obU_eq_of_cohomologous | (intros; apply GlobalTheory.LBObs.obU_eq_of_cohomologous <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundle_of_thinBasis_cocycle : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → IsCoc V hV u → ∃ L : LB X, L.IsLB ∧ IsFrame L V hV u := by
  first | exact @GlobalTheory.ThinGlue.exists_lb_frame | exact GlobalTheory.ThinGlue.exists_lb_frame | (intros; apply GlobalTheory.ThinGlue.exists_lb_frame <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundleLiftObstruction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀), L.IsLB → ∃ c, IsObL S α L c := by
  first | exact @GlobalTheory.LBObs.ObEx.exists_isObL | exact GlobalTheory.LBObs.ObEx.exists_isObL | (intros; apply GlobalTheory.LBObs.ObEx.exists_isObL <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (C D : Type) [Category.{0} C] [Category.{0} D] (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (_ : H ⋙ G ⟶ K), ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) → ObAt S α L K ((extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c) := by
  first | exact @GlobalTheory.LBObs.obAt_refine | exact GlobalTheory.LBObs.obAt_refine | (intros; apply GlobalTheory.LBObs.obAt_refine <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

theorem supS_mul_comm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (h t : GA E a), h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S →
    GeneralLinearGroup.map (pInf E) t = 1 →
    (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → h * t = t * h := by
  intro E _ _ _ a S h t hh ht htS
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, ht, mul_one, one_mul]
  · ext i j w
    have key : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (h * t) =
        GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (t * h) := by
      rw [map_mul, map_mul]
      by_cases hw : w ∈ S
      · rw [htS w hw, mul_one, one_mul]
      · rw [hh w hw, mul_one, one_mul]
    have e : ((GeneralLinearGroup.map (pFin E) (h * t)).val i j) w =
        ((GeneralLinearGroup.map (pFin E) (t * h)).val i j) w :=
      congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.val i j) key
    rw [e]

end GlobalTheory.JSW.MirSemi
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem Good.good_of_isPullback' {g : ℕ} {X Y X' Y' : Scheme.{0}} {k : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {h : Y' ⟶ Y} (sq : IsPullback k f' f h) (hf : Good g f) : Good g f' := by
  exact
    { proper := MorphismProperty.of_isPullback (P := @IsProper) sq hf.proper
      smooth := MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) sq hf.smooth
      conn := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq hf.conn }

theorem HasRep.baseChange (S : Scheme.{0}) (A S' S'' : Over S) [GrpObj A] (g : ℕ) (h : S'' ⟶ S')
    (H : HasRep A g S') : HasRep A g S'' := by
  obtain ⟨B, b, P, hRep, hGood⟩ := H

  have sq := IsPullback.of_hasPullback b h
  refine ⟨pullback b h, pullback.snd b h, ev P (fst A (pullback b h)) (snd A (pullback b h) ≫ pullback.fst b h),
    GlobalTheory.T.rep_ev_of_isPullback S A B S' S'' (pullback b h) b P h _ _ hRep sq, ?_⟩

  exact Good.good_of_isPullback' (sq.map (Over.forget S)) hGood

end GlobalTheory.DualCon
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.additiveLineBundleFamily_calculus_rules : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], (∀ (T Y : Over S) (N : LB (A ⊗ T).left) (y : Y ⟶ T), Fam A N → Fam A (ev N (fst A Y) (snd A Y ≫ y))) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : Fam A N) (hM : Fam A M) (y : Y ⟶ T) (u : Y ⟶ U) (D : LB (A ⊗ Y).left) (hD : D.IsLB), (cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) + GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB) ∨ cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) - GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB)) → Fam A D) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : N.IsLB) (hM : M.IsLB) (y : Y ⟶ T) (u : Y ⟶ U), Same A N M y u ↔ GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN) = GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) (z : Z ⟶ Y), N.IsLB → M.IsLB → Same A N M y u → Same A N M (z ≫ y) (z ≫ u)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (z : Z ⟶ Y) (u : Z ⟶ U), N.IsLB → M.IsLB → (Same A (ev N (fst A Y) (snd A Y ≫ y)) M z u ↔ Same A N M (z ≫ y) u)) := by
  first | exact @GlobalTheory.FamCalc.famCalc | exact GlobalTheory.FamCalc.famCalc | (intros; apply GlobalTheory.FamCalc.famCalc <;> assumption)
end
