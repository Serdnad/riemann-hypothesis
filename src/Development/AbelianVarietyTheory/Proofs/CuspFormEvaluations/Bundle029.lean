module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnValJetGlob


set_option backward.isDefEq.respectTransparency false in
theorem appLE_spMap_jetPt {N m : ℕ} {I : Type} {Z : Scheme.{0}} (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q)
    (χ : Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ I m) [IsLocalHom χ] (U : Z.Opens)
    (h : ⊤ ≤ (spMap χ ≫ jetPt q hq m) ⁻¹ᵁ U) :
    q 0 cpt ∈ U ∧ ∀ f : Γ(Z, U), (spMap χ ≫ jetPt q hq m).appLE U ⊤ h f =
      toΓ _ (χ (jetOf m fun v => valAt' (q v) U f)) := by
  have hU : q 0 cpt ∈ U := by
    have : (spMap χ ≫ jetPt q hq m) (IsLocalRing.closedPoint _) ∈ U :=
      h (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [Scheme.Hom.comp_apply, spMap, Spec_closedPoint, jetPt_closedPoint] at this
  refine ⟨hU, fun f => ?_⟩
  have hp : ⊤ ≤ jetPt q hq m ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (jetPt q hq m) (by rw [jetPt_closedPoint]; exact hU)).ge
  have k := specMap_comp_appLE (CommRingCat.ofHom χ) (jetPt q hq m) U h hp
  rw [jetPt_appLE q hq m U hU hp, Category.assoc, Iso.inv_hom_id_assoc, ← Iso.eq_comp_inv] at k
  have k' := ConcreteCategory.congr_hom k f
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, jetψ_apply] at k'
  exact k'


set_option backward.isDefEq.respectTransparency false in
theorem jetRd_pullGen : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (q : (Fin (n * g) → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q), (∀ v, Φ.GenRd φ ε t (q v) (fun k => Λ k (colsOf n g v)) 1) → Φ.JetRd m (fun k => (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt q hq m) ≫ φ k) ε (LB.pullGen L.L φ ε t (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt q hq m)) Λ := by
  intro S A _ _ L x0 g Φ n m Z K _ φ ε t Λ q hq H
  refine ⟨fun k => ?_, fun j h => ?_⟩
  · have he : ∀ v, q v ≫ φ k = (Φ.e (Λ k (colsOf n g v))).left := fun v => (H v).1 k
    have hol : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e (Λ k (colsOf n g v))).left) := by
      have h := isHolFam_comp q hq (φ k)
      rwa [show (fun v => q v ≫ φ k) = fun v => (Φ.e (Λ k (colsOf n g v))).left from funext he] at h
    refine ⟨hol, ?_⟩
    beta_reduce
    rw [Category.assoc, jetPt_comp q hq (φ k) _ hol he]
  · have : IsLocalHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) :=
      isLocalHom_jetMap (K := ℂ) (m := m) _ _
    have h' : ⊤ ≤ (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt q hq m) ⁻¹ᵁ LB.wchart L.L φ j := by
      intro x hx
      have hx' := h hx
      simp only [LB.wchart] at hx' ⊢
      exact Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hx' k
        simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using this
    obtain ⟨hU, hf⟩ := appLE_spMap_jetPt q hq _ _ h'
    have hj : jetOf m (fun v => valAt' (q v) (LB.wchart L.L φ j) (t.s j).val) =
        jetOf m (fun v => ∏ k, Φ.fr (j k) (Λ k (colsOf n g v)) ^ ε k) := by
      refine jetOf_congr m ((eventually_mem q hq hU).mono fun v hv => ?_)
      have := (H v).2 j hv
      rw [_root_.one_mul] at this
      exact this
    have hf' := hf (t.s j).val
    rw [hj] at hf'
    refine Eq.trans ?_ hf'
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    show ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom
      (((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE _).op).hom _) = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

end GlobalTheory.AnValJetGlob
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValGenCorr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem chart_iff {X Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (j : K → L.ι)
    (x : Sp ℂ ⟶ Z) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  constructor
  · intro h k p _
    have hp := h (Set.mem_univ p)
    exact Set.mem_iInter.1 hp k
  · intro h p _
    exact Set.mem_iInter.2 fun k => h k (Set.mem_univ p)

theorem exists_chart {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (x : Sp ℂ ⟶ X) : ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i := by
  have h : x cpt ∈ (⨆ i, L.U i : X.Opens) := by
    rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i, ReciprocityTheory.ChartRestriction.G.PullbackSections.top_le_of_mem hi⟩

theorem corr_val {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (hc : LB.Gen.Corr L φ ε φ' ε' t t')
    (J : (Y ⟶ X) → L.ι) (p : Sp ℂ ⟶ Y) (hJ : ∀ ψ, ⊤ ≤ (p ≫ ψ) ⁻¹ᵁ L.U (J ψ)) :
    valAt' p (LB.wchart L φ fun k => J (φ k)) (t.s fun k => J (φ k)).val =
      valAt' p (LB.wchart L φ' fun k => J (φ' k)) (t'.s fun k => J (φ' k)).val := by
  have h1 := (chart_iff L φ (fun k => J (φ k)) p).2 fun k => hJ _
  have h2 := (chart_iff L φ' (fun k => J (φ' k)) p).2 fun k => hJ _
  have h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ (fun k => J (φ k)) ⊓ LB.wchart L φ' fun k => J (φ' k)) :=
    fun z hz => ⟨h1 hz, h2 hz⟩
  have e0 := hc (fun k => J (φ k)) (fun k => J (φ' k)) (fun _ _ e => congrArg J e) (fun _ _ e => congrArg J e)
    (fun _ _ e => congrArg J e)
  have e := congrArg (fun u : Γ(Y, LB.wchart L φ (fun k => J (φ k)) ⊓ LB.wchart L φ' fun k => J (φ' k))ˣ =>
    valAt' p _ u.val) e0
  exact (vtf_val_res p _ h _).symm.trans (e.trans (vtf_val_res p _ h _))

theorem val_inv {Z : Scheme.{0}} (p : Sp ℂ ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, V)ˣ) :
    valAt' p V (u⁻¹).val = (valAt' p V u.val)⁻¹ := by
  have e := vtf_valU p h u (-1)
  rwa [zpow_neg_one, zpow_neg_one] at e

open scoped Classical in
theorem prod_fibre {T K : Type} [Fintype K] (φ : K → T) (ε : K → ℤ) (f : T → ℂ) (s : Finset T)
    (hs : ∀ k, φ k ∈ s) (hf : ∀ ψ ∈ s, f ψ ≠ 0) :
    ∏ k, f (φ k) ^ ε k = ∏ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
  have key : ∀ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) =
      ∏ k, if φ k = ψ then f (φ k) ^ ε k else 1 := by
    intro ψ hψ
    have h : ∀ u : Finset K, f ψ ^ (∑ k ∈ u, if φ k = ψ then ε k else 0) =
        ∏ k ∈ u, if φ k = ψ then f (φ k) ^ ε k else 1 := by
      intro u
      induction u using Finset.induction_on with
      | empty => simp
      | insert a u ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (hf ψ hψ), ih]
        congr 1
        split_ifs with h
        · rw [h]
        · simp
    exact h _
  rw [Finset.prod_congr rfl key, Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq, if_pos (hs k)]

theorem genRd_corr_mul_inv : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (φ' : K' → (Z ⟶ A.left)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (t' : LB.Gen (LB.LinComb L.L φ' ε')) (q : Sp ℂ ⟶ Z) (p : K → Fin g → ℂ) (p' : K' → Fin g → ℂ) (v v' : ℂ), Φ.GenRd φ ε t q p v → Φ.GenRd φ' ε' t' q p' v' → (LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι, (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧ v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k) ∧ (LB.Gen.Corr L.L φ ε φ' ε' t t' → LB.SameSum φ ε φ' ε' → (∃ π : (Z ⟶ A.left) → Fin g → ℂ, (∀ k, p k = π (φ k)) ∧ ∀ k, p' k = π (φ' k)) → v = v') ∧ Φ.GenRd (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' t t') q (Sum.elim p p') (v * v') ∧ Φ.GenRd φ (fun k => -ε k) (LB.invGen L.L φ ε t) q p v⁻¹ := by
  classical
  intro S A _ _ L x0 g Φ Z K K' _ _ φ ε φ' ε' t t' q p p' v v' h h'
  have hA : LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι,
      (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧
      v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k := by
    intro hc
    choose J hJ using fun ψ : Z ⟶ A.left => exists_chart L.L L.isLB (q ≫ ψ)
    refine ⟨J, hJ, ?_⟩
    have e := corr_val L.L φ ε φ' ε' t t' hc J q hJ
    have e1 := h.2 (fun k => J (φ k)) ((chart_iff L.L φ _ q).2 fun k => hJ _)
    have e2 := h'.2 (fun k => J (φ' k)) ((chart_iff L.L φ' _ q).2 fun k => hJ _)
    exact e1.symm.trans (e.trans e2)
  refine ⟨hA, ?_, ⟨?_, ?_⟩, ⟨h.1, ?_⟩⟩
  · rintro hc hs ⟨π, hπ, hπ'⟩
    obtain ⟨J, hJ, e⟩ := hA hc
    have n1 : ∀ k, Φ.fr (J (φ k)) (π (φ k)) ≠ 0 := fun k => by
      rw [← hπ k]; apply Φ.fr_ne; rw [← h.1 k]; exact hJ _
    have n2 : ∀ k, Φ.fr (J (φ' k)) (π (φ' k)) ≠ 0 := fun k => by
      rw [← hπ' k]; apply Φ.fr_ne; rw [← h'.1 k]; exact hJ _
    let s : Finset (Z ⟶ A.left) := Finset.univ.image φ ∪ Finset.univ.image φ'
    have hf : ∀ ψ ∈ s, Φ.fr (J ψ) (π ψ) ≠ 0 := by
      intro ψ hψ
      rcases Finset.mem_union.1 hψ with hψ | hψ
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hψ
        exact n1 k
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hψ
        exact n2 k
    have p1 := prod_fibre φ ε (fun ψ => Φ.fr (J ψ) (π ψ)) s
      (fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) hf
    have p2 := prod_fibre φ' ε' (fun ψ => Φ.fr (J ψ) (π ψ)) s
      (fun k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) hf
    have p3 : ∏ k, Φ.fr (J (φ k)) (π (φ k)) ^ ε k = ∏ k, Φ.fr (J (φ' k)) (π (φ' k)) ^ ε' k := by
      refine p1.trans (Eq.trans ?_ p2.symm)
      refine Finset.prod_congr rfl fun ψ _ => ?_
      congr 1
      exact hs ψ
    simp only [hπ, hπ'] at e
    rw [p3] at e
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (n2 k)) e
  · rintro (k | k)
    · exact h.1 k
    · exact h'.1 k
  · intro j hj
    have hj0 := (chart_iff L.L _ j q).1 hj
    have e1 := h.2 (j ∘ Sum.inl) ((chart_iff L.L φ _ q).2 fun k => hj0 (Sum.inl k))
    have e2 := h'.2 (j ∘ Sum.inr) ((chart_iff L.L φ' _ q).2 fun k => hj0 (Sum.inr k))
    refine (ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul q _ _ _).trans ?_
    refine (congrArg₂ (· * ·) ((vtf_val_res q _ hj _).trans e1) ((vtf_val_res q _ hj _).trans e2)).trans ?_
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  · intro j hj
    have e1 := h.2 j hj
    have e2 := val_inv q hj (t.s j)
    refine e2.trans ?_
    refine (congrArg (·⁻¹) e1).trans ?_
    simp only [mul_inv, zpow_neg, Finset.prod_inv_distrib]

end GlobalTheory.AnValGenCorr
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem semichar_herm_zero_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  simp [hermForm]

theorem semichar_herm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]

theorem semichar_herm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem semichar_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply]
  ring

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.exists_chart_lat : ∃ j, ∀ a ∈ Φ.lat, ⊤ ≤ (Φ.e a).left ⁻¹ᵁ L.L.U j := by
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  obtain ⟨j, hj⟩ : ∃ j, (Φ.e 0).left pt ∈ L.L.U j :=
    TopologicalSpace.Opens.mem_iSup.1 (L.isLB.cover.ge (Set.mem_univ _))
  have hj0 : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U j := fun z _ => by
    have hz : z = pt := Subsingleton.elim (α := PrimeSpectrum ℂ) z pt
    rw [hz]
    exact hj
  refine ⟨j, fun a ha => ?_⟩
  rw [(Φ.e_ker a).2 ha, ← (Φ.e_ker 0).2 Φ.lat.zero_mem]
  exact hj0

theorem AnFr.χ_add {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by
  obtain ⟨j, hj⟩ := Φ.exists_chart_lat
  have hab := Φ.lat.add_mem ha hb
  have h1 := Φ.fr_per a ha j 0 (hj 0 Φ.lat.zero_mem)
  have h2 := Φ.fr_per b hb j a (hj a ha)
  have h3 := Φ.fr_per (a + b) hab j 0 (hj 0 Φ.lat.zero_mem)
  have hne : Φ.fr j (a + b) ≠ 0 := Φ.fr_ne j _ (hj _ hab)
  rw [zero_add, h2] at h1
  rw [zero_add] at h3
  simp only [semichar_herm_zero_left, mul_zero, zero_add] at h1 h3
  have key : Φ.χ (a + b) * Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) =
      Φ.χ a * Φ.χ b * (Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm a a) *
        Complex.exp (↑Real.pi * hermForm Φ.Hm a b + ↑Real.pi / 2 * hermForm Φ.Hm b b)) := by
    have := h3.symm.trans h1
    apply mul_right_cancel₀ hne
    linear_combination this
  have hexp : Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm a a) *
      Complex.exp (↑Real.pi * hermForm Φ.Hm a b + ↑Real.pi / 2 * hermForm Φ.Hm b b) =
      Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) *
        Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [semichar_herm_add_left, semichar_herm_add_right, semichar_herm_add_right, semichar_herm_swap Φ.herm a b]
    have hsc : hermForm Φ.Hm a b - star (hermForm Φ.Hm a b) =
        2 * ((hermForm Φ.Hm a b).im : ℂ) * Complex.I := by
      rw [show star (hermForm Φ.Hm a b) = (starRingEnd ℂ) (hermForm Φ.Hm a b) from rfl, Complex.sub_conj]
      push_cast; ring
    linear_combination (↑Real.pi / 2 : ℂ) * hsc
  rw [hexp] at key
  have hE : Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hE
  linear_combination key

theorem AnFr.χ_ne_zero {a : Fin g → ℂ} (ha : a ∈ Φ.lat) : Φ.χ a ≠ 0 := fun h => by
  have := Φ.χ_norm a ha
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem AnFr.herm_im_swap (a b : Fin g → ℂ) : (hermForm Φ.Hm b a).im = -(hermForm Φ.Hm a b).im := by
  rw [semichar_herm_swap Φ.herm a b]
  simp

theorem AnFr.herm_im_int {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    ∃ k : ℤ, (hermForm Φ.Hm a b).im = k := by
  have h1 := Φ.χ_add ha hb
  have h2 := Φ.χ_add hb ha
  rw [add_comm b a, h1, Φ.herm_im_swap a b, mul_comm (Φ.χ b)] at h2
  have h3 := mul_left_cancel₀ (mul_ne_zero (Φ.χ_ne_zero ha) (Φ.χ_ne_zero hb)) h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3
  refine ⟨n, ?_⟩
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : (((hermForm Φ.Hm a b).im : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hπ
    push_cast at hn
    linear_combination hn
  exact_mod_cast this

theorem AnFr.herm_im_self (a : Fin g → ℂ) : (hermForm Φ.Hm a a).im = 0 := by
  have := Φ.herm_im_swap a a
  linarith

theorem AnFr.χ_add_self {a : Fin g → ℂ} (ha : a ∈ Φ.lat) : Φ.χ (a + a) = Φ.χ a ^ 2 := by
  rw [Φ.χ_add ha ha, Φ.herm_im_self]
  simp [sq]

theorem AnFr.χ_zero : Φ.χ 0 = 1 := by
  have h := Φ.χ_add_self Φ.lat.zero_mem
  rw [add_zero] at h
  apply mul_left_cancel₀ (Φ.χ_ne_zero Φ.lat.zero_mem)
  linear_combination -h

end

theorem anFr_semichar : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, ∀ b ∈ Φ.lat, (∃ k : ℤ, (hermForm Φ.Hm a b).im = k) ∧ Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ))) ∧ Φ.χ 0 = 1 ∧ ((∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ a ∈ Φ.lat, Φ.χ ((2 : ℂ) • a) = 1) := by
  intro S A _ _ L x0 g Φ
  refine ⟨fun a ha b hb => ⟨Φ.herm_im_int ha hb, Φ.χ_add ha hb⟩, Φ.χ_zero, fun h a ha => ?_⟩
  rw [two_smul, Φ.χ_add_self ha, h a ha]

end GlobalTheory.AnVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem polyDeriv_comp_linear_equiv {σ V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (e : V ≃L[ℂ] W) (P : MvPolynomial σ ℂ) (u : σ → V)
    (G : W → ℂ) (x : V) :
    I2.polyDeriv P u (fun z => G (e z)) x = I2.polyDeriv P (fun ℓ => e (u ℓ)) G (e x) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := e.iteratedFDerivWithin_comp_right G (s := Set.univ) uniqueDiffOn_univ (x := x)
    (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have h' : (fun z => G (e z)) = G ∘ e := rfl
  rw [h', h]
  rfl

theorem lintor_hf_neg_right {J : Type} [Fintype J] (v w : EuclideanSpace ℂ J) :
    I2.Hf v (-w) = -I2.Hf v w := by
  simp [I2.Hf]

theorem lintor_hf_neg_left {J : Type} [Fintype J] (v w : EuclideanSpace ℂ J) :
    I2.Hf (-v) w = -I2.Hf v w := by
  simp [I2.Hf]

theorem polyDeriv_prod_fock_eq_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (g : ℕ) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp X.dim) (Hm : Matrix (Fin g) (Fin g) ℂ) (θ : (Fin g → ℂ) → ℂ), (∀ z w, I2.Hf (ψ z) (ψ w) = hermForm Hm z w) → Differentiable ℂ θ → ∀ (n N : ℕ) (a : Fin n → Fin g → ℂ) (Io : Type) (P : MvPolynomial Io ℂ) (u : Io → Fin n → Fin g → ℂ), I2.polyDeriv P u (fun z => ∏ b, fock Hm ((N : ℤ) ^ 2) (a b) (fun w => θ ((N : ℂ) • w)) (z b)) 0 = I2.polyDeriv P (fun ℓ b => ψ (u ℓ b)) (X.U (N ^ 2) (fun b => -ψ (a b)) (I2.s0 X ((N : ℂ) • LinearMap.id) fun v => θ (ψ.symm (v 0)))) 0 := by
  intro E _ _ _ X g ψ Hm θ hH _ n N a Io P u
  let e : (Fin n → Fin g → ℂ) ≃L[ℂ] (Fin n → I2.Vsp X.dim) :=
    ContinuousLinearEquiv.piCongrRight fun _ => ψ.toContinuousLinearEquiv
  have he : ∀ z, e z = fun b => ψ (z b) := fun _ => rfl
  have key := polyDeriv_comp_linear_equiv e P u (X.U (N ^ 2) (fun b => -ψ (a b))
    (I2.s0 X ((N : ℂ) • LinearMap.id) fun v => θ (ψ.symm (v 0)))) 0
  rw [map_zero] at key
  refine Eq.trans ?_ key
  congr 1
  funext z
  rw [he]
  simp only [fock, I2.PT.U, I2.s0, I2.HC, lintor_hf_neg_right, lintor_hf_neg_left, hH, neg_neg,
    Finset.prod_mul_distrib, ← Complex.exp_sum, Pi.sub_apply, sub_neg_eq_add,
    LinearMap.smul_apply, LinearMap.id_apply, ← map_add, ← map_smul, LinearEquiv.symm_apply_apply]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div, mul_neg]
  push_cast
  rfl

end GlobalTheory.AnVal
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem fock_add {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (q : ℤ) (a b : Fin g → ℂ)
    (θ : (Fin g → ℂ) → ℂ) :
    fock Hm q (a + b) θ = fun z => Complex.exp ((q : ℂ) * Real.pi * Complex.I * ((hermForm Hm a b).im : ℂ)) *
      fock Hm q a (fock Hm q b θ) z := by
  have hl : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp [hermForm, add_dotProduct]
  have hr : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have hs : hermForm Hm b a = star (hermForm Hm a b) := by
    rw [hermForm, hermForm, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq,
      Matrix.dotProduct_mulVec]
  have hsc : hermForm Hm b a = hermForm Hm a b - 2 * Complex.I * ((hermForm Hm a b).im : ℂ) := by
    rw [hs]
    apply Complex.ext <;> simp
    ring
  funext z
  simp only [fock]
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add, add_assoc z a b]
  congr 2
  simp only [hl, hr, hsc]
  ring

theorem fock_sq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (a : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ) :
    fock Hm ((N : ℤ) ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock Hm 1 ((N : ℂ) • a) θ ((N : ℂ) • z) := by
  have h : ∀ z w, hermForm Hm ((N : ℂ) • z) ((N : ℂ) • w) = (N : ℂ) ^ 2 * hermForm Hm z w := fun z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      star_natCast]
    ring
  funext z
  simp only [fock, h, smul_add]
  congr 2
  push_cast
  ring

theorem fock_laws : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ (q : ℤ) (a b : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ), fock Φ.Hm q (a + b) θ = fun z => Complex.exp ((q : ℂ) * Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) * fock Φ.Hm q a (fock Φ.Hm q b θ) z) ∧ (∀ (N : ℕ) (a : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ), fock Φ.Hm ((N : ℤ) ^ 2) a (fun z => θ ((N : ℂ) • z)) = fun z => fock Φ.Hm 1 ((N : ℂ) • a) θ ((N : ℂ) • z)) ∧ ∀ θ, Φ.IsTh 1 θ → ∀ a ∈ Φ.lat, fock Φ.Hm 1 a θ = fun z => Φ.χ a * θ z := by
  intro S A _ _ L x0 g Φ
  refine ⟨fun q a b θ => fock_add Φ.herm q a b θ, fun N a θ => fock_sq Φ.Hm N a θ, fun θ hθ a ha => ?_⟩
  funext z
  simp only [fock, hθ.2 a ha z, AnFr.fac, zpow_one]
  have : Complex.exp (-(((1 : ℤ) : ℂ) * Real.pi * hermForm Φ.Hm z a) - ((1 : ℤ) : ℂ) * Real.pi * hermForm Φ.Hm a a / 2) *
      Complex.exp (Real.pi * hermForm Φ.Hm z a + Real.pi / 2 * hermForm Φ.Hm a a) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  linear_combination (Φ.χ a * θ z) * this

end GlobalTheory.AnVal
end
end
