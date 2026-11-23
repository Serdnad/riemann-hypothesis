module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle492
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.FieldTheory.KrullTopology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle495
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle496
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenIsoRatio

theorem gm_pullU_res {X Y : Scheme.{0}} (β : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (h : V ≤ β ⁻¹ᵁ U) (y : Y)
    (hy : y ∈ V) (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res h (pullU β U a)) = gm β y U a := by
  rw [gm_res (𝟙 Y) y h hy, gm_pull (𝟙 Y) β y U (h hy), Category.id_comp]

theorem gm_pull_g' {X Y : Scheme.{0}} (β : Y ⟶ X) (L : LB X) (y : Y) (i i' : L.ι) (hi : β y ∈ L.U i)
    (hi' : β y ∈ L.U i') :
    gm (𝟙 Y) y ((L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i'))
      ((L.pull β).g (fun _ => i) (fun _ => i')) = gm β y (L.U i ⊓ L.U i') (L.g i i') := by
  have hp : y ∈ (L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i') := ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU β _ (L.g i i'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hp _).trans ((gm_pull (𝟙 Y) β y (L.U i ⊓ L.U i') ⟨hi, hi'⟩ _).trans (by rw [Category.id_comp]))

theorem ratio : ∀ (X Y : Scheme.{0}) (β : Y ⟶ X) (P M : LB X) (N : LB Y), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull β) N) (w₁ : LB.Iso (P.pull β) N) (v : LB.Iso P M), w.IsGen → w₁.IsGen → v.IsGen → ∃ u : Γ(Y, ⊤)ˣ, ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ β ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (P.pull β).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.rs _ (le_top : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ ⊤) (u : Γ(Y, ⊤)) * (β.appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (M.pull β).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  intro X Y β P M N hP hM hN w w₁ v hw hw₁ hv
  let W : N.ι × P.ι × M.ι → Y.Opens := fun j =>
    N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1) ⊓ (M.pull β).U (fun _ => j.2.2)
  have l₁ : ∀ j, W j ≤ N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1) := fun j => inf_le_left
  have l₂ : ∀ j, W j ≤ N.U j.1 ⊓ (M.pull β).U (fun _ => j.2.2) := fun j =>
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have l₃ : ∀ j, W j ≤ β ⁻¹ᵁ (M.U j.2.2 ⊓ P.U j.2.1) := fun j y hy =>
    ⟨mem_pull.1 hy.2, mem_pull.1 hy.1.2⟩
  let r : ∀ j, Γ(Y, W j)ˣ := fun j =>
    res (l₁ j) (w₁.s (j.1, fun _ => j.2.1)) * (res (l₃ j) (pullU β _ (v.s (j.2.2, j.2.1))))⁻¹ *
      (res (l₂ j) (w.s (j.1, fun _ => j.2.2)))⁻¹
  have k : ∀ j (y : Y), y ∈ W j → gm (𝟙 Y) y (W j) (r j) =
      gm (𝟙 Y) y (N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1)) (w₁.s (j.1, fun _ => j.2.1)) *
        (gm β y (M.U j.2.2 ⊓ P.U j.2.1) (v.s (j.2.2, j.2.1)))⁻¹ *
        (gm (𝟙 Y) y (N.U j.1 ⊓ (M.pull β).U (fun _ => j.2.2)) (w.s (j.1, fun _ => j.2.2)))⁻¹ := by
    intro j y hy
    simp only [r, map_mul, map_inv]
    erw [gm_res (𝟙 Y) y (l₁ j) hy, gm_res (𝟙 Y) y (l₂ j) hy, gm_pullU_res β _ (l₃ j) y hy]
  obtain ⟨u, hu⟩ := glue_unit (⊤ : Y.Opens) W (fun _ => le_top)
    (fun y _ => by
      obtain ⟨n, hn⟩ := exists_chart hN y
      obtain ⟨i, hi⟩ := exists_chart hP (β y)
      obtain ⟨m, hm⟩ := exists_chart hM (β y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(n, i, m), ⟨hn, mem_pull.2 hi⟩, mem_pull.2 hm⟩) r
    (fun j j' y hy => by
      have hi := mem_pull.1 hy.1.1.2
      have hi' := mem_pull.1 hy.2.1.2
      have hm := mem_pull.1 hy.1.2
      have hm' := mem_pull.1 hy.2.2
      rw [k j y hy.1, k j' y hy.2,
        GlobalTheory.PartialCocycle.gm_iso hw₁ (𝟙 Y) y j.1 j'.1 (fun _ => j.2.1) (fun _ => j'.2.1) hy.1.1.1 hy.2.1.1
          hy.1.1.2 hy.2.1.2,
        GlobalTheory.PartialCocycle.gm_iso hw (𝟙 Y) y j.1 j'.1 (fun _ => j.2.2) (fun _ => j'.2.2) hy.1.1.1 hy.2.1.1
          hy.1.2 hy.2.2,
        GlobalTheory.PartialCocycle.gm_iso hv β y j.2.2 j'.2.2 j.2.1 j'.2.1 hm hm' hi hi',
        gm_pull_g' β P y _ _ hi hi', gm_pull_g' β M y _ _ hm hm']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨u, fun n i m hle => ?_⟩
  have e : res (l₁ (n, i, m)) (w₁.s (n, fun _ => i)) =
      res (le_top : W (n, i, m) ≤ ⊤) u * res hle (pullU β _ (v.s (m, i))) * res (l₂ (n, i, m)) (w.s (n, fun _ => m)) := by
    change _ = _ * res (l₃ (n, i, m)) (pullU β _ (v.s (m, i))) * _
    rw [hu (n, i, m)]
    simp only [r]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact congrArg Units.val e

end GlobalTheory.GenIsoRatio
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraInductionGL_isCharacter : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsChar ℂ ℂ α → IsChar ℂ ℂ β → IsChar ℂ ℂ (hc a b α β n) := by
  first | (exact @GlobalTheory.Shin.HCChar.hc_isChar) | (exact GlobalTheory.Shin.HCChar.hc_isChar) | (intros; apply GlobalTheory.Shin.HCChar.hc_isChar  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraInductionGL_trivial_orthogonal_hyperplaneFixer : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → 0 < b → ∀ (α : GL (Fin a) F → ℂ) (Y : GL (Fin n) F → ℂ), IsChar ℂ ℂ Y → HFree Y → ∑ᶠ x, hc a b α (fun _ => 1) n x * star (Y x) = 0 := by
  first | (exact @GlobalTheory.Shin.hc_one_orth_hfree) | (exact GlobalTheory.Shin.hc_one_orth_hfree) | (intros; apply GlobalTheory.Shin.hc_one_orth_hfree  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.exists_virtualCharacter_twistedHarishChandraInductionGL : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (a b n : ℕ), n = a + b → ∀ X ∈ Virt ℂ ℂ (GHat F F' a), ∃ Z ∈ Virt ℂ ℂ (GHat F F' n), ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'), Z (inl δ * inr t) = hcTw (t : F' →+* F') a b (fun d => X (inl d * inr t)) (fun _ => 1) n δ := by
  first | (exact @GlobalTheory.Shin.HatInd.hat_ind) | (exact GlobalTheory.Shin.HatInd.hat_ind) | (intros; apply GlobalTheory.Shin.HatInd.hat_ind <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ x : F, Transcendental k x → {v : Place k F | v.1 x < 1}.Finite ∧ ∑ᶠ v ∈ {v : Place k F | v.1 x < 1}, ord v x = Module.finrank k⟮x⟯ F := by
  first | exact @GlobalTheory.Nef.zeros_finite_sum_eq_degree | exact GlobalTheory.Nef.zeros_finite_sum_eq_degree | (intros; apply GlobalTheory.Nef.zeros_finite_sum_eq_degree <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.functionFieldPlace_local_index_colength : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (h : Matrix (Fin n) (Fin n) F), h.det ≠ 0 → (∀ i j, v.1 (h⁻¹ i j) ≤ 1) → ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = -ord v h.det ∧ ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 → ∀ i, v.1 (h.mulVec x i) ≤ 1 := by
  first | exact @GlobalTheory.Nef.local_index | exact GlobalTheory.Nef.local_index | (intros; apply GlobalTheory.Nef.local_index <;> assumption)
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.exists_jet_morphism_extending_translation : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {l : Λ} {k k' : K.K} (e : K.le l k' k), ∃ χ : K.jet k ⟶ K.jet k', χ.deg = l ∧ jet0 k ≫ χ = ptHom (K.triv k') e ≫ jet0 k' ∧ jet1 k ≫ χ = ptHom (K.triv k') e ≫ jet1 k' ∧ ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), (TrivSqZeroExt.fst (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) = sh e x.fst) ∧ ∀ a, TrivSqZeroExt.snd (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) a = sh e (x.snd a) := by
  first | exact @GlobalTheory.AnPer.Charts.jet_sh | exact GlobalTheory.AnPer.Charts.jet_sh | (intros; apply GlobalTheory.AnPer.Charts.jet_sh <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

open GlobalTheory.EtC.GalSmooth in

theorem _root_.GlobalTheory.T.galoisAction_finitarySheafSection_locallyConstant :
    ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
      ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
        (x : Sec F (Spec (CommRingCat.of Ω))),
        IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω =>
          Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x) := by
  intro R _ F hF K Ω _ _ _ _ x
  classical
  have elements :=
    (GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements
      (ULift.{1} R) (onRings F)).2.mp hF
  obtain ⟨s, y, hy⟩ := (elements (Finset Ω) (diag Ω) (cocone Ω) (coconeIsColimit Ω)).1 x
  have restrict_eq (τ : Ω ≃ₐ[K] Ω) :
      Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x =
        ((onRings F).map (CommRingCat.ofHom ((τ : Ω →+* Ω).comp (sr Ω s).subtype))).hom y := by
    rw [← hy, cocone_ι]
    show _ = ((onRings F).map (CommRingCat.ofHom (sr Ω s).subtype ≫
      CommRingCat.ofHom (τ : Ω →+* Ω))).hom y
    rw [Functor.map_comp]
    rfl
  rw [IsLocallyConstant.iff_eventually_eq]
  intro τ₀
  have : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun a _ => Algebra.IsIntegral.isIntegral a)
  have hopen : IsOpen {σ : Ω ≃ₐ[K] Ω |
      τ₀⁻¹ * σ ∈ (IntermediateField.adjoin K (s : Set Ω)).fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
  filter_upwards [hopen.mem_nhds (by simp)] with τ hτ
  have hs : Set.EqOn (τ : Ω →+* Ω) (τ₀ : Ω →+* Ω) (s : Set Ω) := fun b hb => by
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ b
      (IntermediateField.subset_adjoin K _ hb)
    simpa [AlgEquiv.mul_apply] using congrArg τ₀ hfix
  have hc : (τ : Ω →+* Ω).comp (sr Ω s).subtype =
      (τ₀ : Ω →+* Ω).comp (sr Ω s).subtype := by
    ext a
    exact RingHom.eqOn_set_closure hs a.2
  rw [restrict_eq τ, restrict_eq τ₀, hc]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem stalk_local_classes : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (Θ Θ₂ : Over S ⥤ Spc) (α : Θ ⟶ Θ₂), (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F (Θ.mapCone c)) → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F (Θ₂.mapCone c)) → ∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (α.app (Over.mk s)) F → ∀ (U : Over S), Etale U.hom → ∀ (g : Over.mk s ⟶ U) (n : ℤ), (∀ x : H R (Θ.obj U) F n, ∃ (V : Over S) (g₁ : Over.mk s ⟶ V) (h : V ⟶ U) (y : H R (Θ₂.obj V) F n), Etale V.hom ∧ g₁ ≫ h = g ∧ pull R (α.app V) F n y = pull R (Θ.map h) F n x) ∧ ∀ y : H R (Θ₂.obj U) F n, pull R (α.app U) F n y = 0 → ∃ (V : Over S) (g₁ : Over.mk s ⟶ V) (h : V ⟶ U), Etale V.hom ∧ g₁ ≫ h = g ∧ pull R (Θ₂.map h) F n y = 0 := by
  intro R _ F S Θ Θ' α hΘ hΘ' O _ s hs hα U hU g n
  obtain ⟨I, _, _, G, π, ⟨hl⟩, hG⟩ := GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' S O s hs
  haveI : IsConnected I := IsCofiltered.isConnected I
  have hcF : IsLimit ((Over.forget S).mapCone (Cone.mk _ π)) := isLimitOfPreserves (Over.forget S) hl
  haveI : ∀ i, IsAffine ((G ⋙ Over.forget S).obj i) := fun i => (hG i).1
  haveI : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((G ⋙ Over.forget S).map f) := fun _ => inferInstance
  haveI : LocallyOfFinitePresentation U.hom := inferInstance
  let t0 : G ⋙ Over.forget S ⟶ (Functor.const I).obj S :=
    { app := fun i => (G.obj i).hom, naturality := fun i j f => by simp }
  obtain ⟨j, u0, hu0, hu1⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (G ⋙ Over.forget S) t0 U.hom _ hcF g.left (by
      ext i
      exact (Over.w (π.app i)).trans (Over.w g).symm)
  let u : G.obj j ⟶ U := Over.homMk u0 hu1
  have hu : π.app j ≫ u = g := Over.OverMorphism.ext hu0
  have hπ : ∀ {i k : I} (f : k ⟶ i), π.app k ≫ G.map f = π.app i := fun f => by
    simpa using (π.naturality f).symm
  have hnat : ∀ {A B : Over S} (f : A ⟶ B) (y : H R (Θ'.obj B) F n),
      pull R (Θ.map f) F n (pull R (α.app B) F n y) = pull R (α.app A) F n (pull R (Θ'.map f) F n y) := by
    intro A B f y
    rw [← pull_comp, ← pull_comp, α.naturality]
  have cΘ := hΘ I G (Cone.mk _ π) hl (fun i => (hG i).1) n
  have cΘ' := hΘ' I G (Cone.mk _ π) hl (fun i => (hG i).1) n
  simp only [Functor.mapCone_π_app, Functor.comp_obj, Functor.comp_map] at cΘ cΘ'
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ := (hα n).2 (pull R (Θ.map g) F n x)
    obtain ⟨i, y0, hy0⟩ := cΘ'.1 w
    let k := IsCofiltered.min i j
    let fi : k ⟶ i := IsCofiltered.minToLeft i j
    let fj : k ⟶ j := IsCofiltered.minToRight i j
    let y1 := pull R (Θ'.map (G.map fi)) F n y0
    have hgh : π.app k ≫ (G.map fj ≫ u) = g := by rw [← Category.assoc, hπ, hu]
    have hd : pull R (Θ.map (π.app k)) F n
        (pull R (α.app (G.obj k)) F n y1 - pull R (Θ.map (G.map fj ≫ u)) F n x) = 0 := by
      have e1 : pull R (Θ.map (π.app k)) F n (pull R (α.app (G.obj k)) F n y1) = pull R (Θ.map g) F n x := by
        rw [hnat]
        show pull R (α.app (Over.mk s)) F n (pull R (Θ'.map (π.app k)) F n (pull R (Θ'.map (G.map fi)) F n y0)) = _
        rw [← pull_comp R (Θ'.map (π.app k)), ← Functor.map_comp, hπ, hy0]
        exact hw
      have e2 : pull R (Θ.map (π.app k)) F n (pull R (Θ.map (G.map fj ≫ u)) F n x) = pull R (Θ.map g) F n x := by
        rw [← pull_comp, ← Functor.map_comp, hgh]
      rw [map_sub, e1, e2, sub_self]
    obtain ⟨k', f', hf'⟩ := cΘ.2 k _ hd
    refine ⟨G.obj k', π.app k', G.map f' ≫ G.map fj ≫ u, pull R (Θ'.map (G.map f')) F n y1, (hG k').2, ?_, ?_⟩
    · rw [← Category.assoc, hπ, hgh]
    · rw [map_sub, sub_eq_zero, hnat] at hf'
      rw [hf', ← pull_comp, ← Functor.map_comp]
  · have h0 : pull R (Θ'.map g) F n y = 0 := (hα n).1 (by rw [map_zero, ← hnat, hy, map_zero])
    rw [← hu, Functor.map_comp, pull_comp] at h0
    obtain ⟨k, f, hf⟩ := cΘ'.2 j _ h0
    exact ⟨G.obj k, π.app k, G.map f ≫ u, (hG k).2, by rw [← Category.assoc, hπ, hu],
      by rw [Functor.map_comp, pull_comp, hf]⟩

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.Descent

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  intro R _ F T _ Cov _ Φ Φ' α hRef hS hI U
  obtain ⟨hneg, cl, hcl_surj, hcl_eq, hcl_zero, hpull⟩ := GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F
  have key := GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent T Cov (Φ' ⋙ HC R F) (Φ ⋙ HC R F) (Functor.whiskerRight α (HC R F)) ?_ ?_ ?_ ?_ U
  · exact (GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise R F _ _ (α.app U).unop).2 key
  · exact ⟨0, fun n hn V => ⟨hneg _ n hn, hneg _ n hn⟩⟩
  · intro U' V' g hg
    obtain ⟨X, a, h, hga, h1, h2⟩ := hRef U' V' g hg
    exact ⟨X, a, h, hga, fun n => ⟨GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ' U' X a h2 n, GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ U' X a h1 n⟩⟩
  · intro n U' z hz
    obtain ⟨V, g, hg, y, hy⟩ := hS U' n (cl (Φ.obj U').unop n z hz)
    obtain ⟨c, hc, rfl⟩ := hcl_surj (Φ'.obj V).unop n y
    obtain ⟨h1, e1⟩ := hpull _ _ (α.app V).unop n c hc
    obtain ⟨h2, e2⟩ := hpull _ _ (Φ.map g).unop n z hz
    rw [e1, e2, hcl_eq] at hy
    obtain ⟨y', hy'⟩ := hy
    exact ⟨V, g, hg, c, y', hc, hy'⟩
  · intro n U' c hc ⟨y, hy⟩
    have h0 : pull R (α.app U').unop F n (cl (Φ'.obj U').unop n c hc) = 0 := by
      obtain ⟨h1, e1⟩ := hpull _ _ (α.app U').unop n c hc
      rw [e1, hcl_zero]
      exact ⟨y, hy⟩
    obtain ⟨V, g, hg, hV⟩ := hI U' n _ h0
    obtain ⟨h2, e2⟩ := hpull _ _ (Φ'.map g).unop n c hc
    rw [e2, hcl_zero] at hV
    obtain ⟨b, hb⟩ := hV
    exact ⟨V, g, hg, b, hb.symm⟩

end GlobalTheory.EtC.Descent
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleFaithfullyFlat_filtered_colimit_finiteType : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Arrow CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj (Arrow.mk g)), Nonempty (IsColimit (Cocone.mk (Arrow.mk g) ι)) ∧ ∀ j, EtFF (D.obj j).hom ∧ Algebra.FiniteType ℤ (D.obj j).left ∧ Algebra.FiniteType ℤ (D.obj j).right := by
  first | (exact @GlobalTheory.EtC.etFF_filtered_colimit_finiteType) | (exact GlobalTheory.EtC.etFF_filtered_colimit_finiteType) | (intros; apply GlobalTheory.EtC.etFF_filtered_colimit_finiteType  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.locallyInjective_of_iso_on_finiteType_rings : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocInj EtFF ε := by
  first | (exact @GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType) | (exact GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType) | (intros; apply GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType  <;> assumption)
end
