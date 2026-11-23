module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle884
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDieudonneFunctorGluedConnectedEtale
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle938
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle826
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle880
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle939
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isPer_of_basis : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (K : Type) (W : K → A.left.affineOpens) (k : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ i j, ∀ z ∈ pre u.ex (W i).1, z ∈ pre u.ex (W j).1 → ∃ l, W l ≤ W i ∧ W l ≤ W j ∧ z ∈ pre u.ex (W l).1 ∧ (∀ a : Opposite.op (W i) ⟶ Opposite.op (W l), k l z = k i z + val u.ex (W l).1 (c.1.1 _ _ a) z) ∧ ∀ a : Opposite.op (W j) ⟶ Opposite.op (W l), k l z = k j z + val u.ex (W l).1 (c.1.1 _ _ a) z) → (∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, ∃ i, W i ≤ U ∧ z ∈ pre u.ex (W i).1) → (∀ i, DifferentiableOn ℂ (k i) (pre u.ex (W i).1)) → (∀ i, ∀ z ∈ pre u.ex (W i).1, fderiv ℂ (k i) z = evForm u.ex (W i).1 z (c.1.2 (Opposite.op (W i)))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i).1, k i (z + l) = k i z + q l) → IsPer u.ex u.Λ (Hyp1.mk _ c) q := by
  intro A _ g L u c K W k q hcomp hbasis hdiff hder hper
  classical
  obtain ⟨hopen, hvd, hpp, hvp, -, hmono, -, -, hres, halg, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hev := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u
  have hevres := GlobalTheory.T.evForm_restriction_eq A g L u
  let f : ∀ (U V : A.left.affineOpens), V ≤ U → Sec (str A) V.1 := fun U V h ↦
    c.1.1 (Opposite.op U) (Opposite.op V) (homOfLE h).op
  have hf : ∀ (U V T : A.left.affineOpens) (h : V ≤ U) (h' : T ≤ V), ∀ z ∈ pre u.ex T.1,
      val u.ex T.1 (f U T (h'.trans h)) z = val u.ex V.1 (f U V h) z + val u.ex T.1 (f V T h') z := by
    intro U V T h h' z hz
    have e : f U T (h'.trans h) = Sec.res (str A) h' (f U V h) + f V T h' :=
      cechDeRhamTotalCocyclesOne.comp c (homOfLE h).op (homOfLE h').op
    obtain ⟨ev, hev⟩ := halg T.1 z hz
    rw [← hres V.1 T.1 h' _ z hz, e]
    exact (hev _).trans ((map_add ev _ _).trans (congrArg₂ _ (hev _).symm (hev _).symm))
  let h : A.left.affineOpens → (Fin g → ℂ) → ℂ := fun U z ↦
    if hz : z ∈ pre u.ex U.1 then
      k (hbasis U z hz).choose z - val u.ex _ (f U _ (hbasis U z hz).choose_spec.1) z else 0
  have hh : ∀ (U : A.left.affineOpens) i (hi : W i ≤ U), ∀ z ∈ pre u.ex (W i).1,
      h U z = k i z - val u.ex _ (f U _ hi) z := by
    intro U i hi z hz
    have hzU : z ∈ pre u.ex U.1 := hmono _ _ hi hz
    obtain ⟨hj, hzj⟩ := (hbasis U z hzU).choose_spec
    simp only [h, dif_pos hzU]
    generalize_proofs p1 p2
    generalize p1.choose = j at *
    obtain ⟨l, hli, hlj, hzl, e1, e2⟩ := hcomp i j z hz hzj
    have a1 := hf U _ _ hi hli z hzl
    have a2 := hf U _ _ hj hlj z hzl
    have b1 : k l z = k i z + val u.ex _ (f _ _ hli) z := e1 _
    have b2 : k l z = k j z + val u.ex _ (f _ _ hlj) z := e2 _
    linear_combination b1 - b2 - a1 + a2
  have hnhds : ∀ (U : A.left.affineOpens) i (hi : W i ≤ U), ∀ z ∈ pre u.ex (W i).1,
      h U =ᶠ[nhds z] fun y ↦ k i y - val u.ex _ (f U _ hi) y := fun U i hi z hz ↦
    Filter.eventually_of_mem ((hopen _).mem_nhds hz) fun y hy ↦ hh U i hi y hy
  refine ⟨c, h, rfl, ⟨fun U z hz ↦ ?_, fun U V a z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    have n := (hopen _).mem_nhds hzi
    exact ((((hdiff i).differentiableAt n).sub ((hvd _ _).differentiableAt n)).congr_of_eventuallyEq
      (hnhds U i hi z hzi)).differentiableWithinAt
  · obtain ⟨i, hi, hzi⟩ := hbasis V z hz
    have hVU : V ≤ U := leOfHom a.unop
    have a1 := hf U V _ hVU hi z hzi
    change _ = _ + val u.ex V.1 (f U V hVU) z
    rw [hh V i hi z hzi, hh U i (hi.trans hVU) z hzi, a1]
    ring
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    have n := (hopen _).mem_nhds hzi
    refine (hnhds U i hi z hzi).fderiv_eq.trans ((fderiv_fun_sub ((hdiff i).differentiableAt n)
      ((hvd _ (f U _ hi)).differentiableAt n)).trans ?_)
    rw [hder i z hzi, sub_eq_iff_eq_add]
    refine (congrArg _ (cechDeRhamTotalCocyclesOne.conn c (homOfLE hi).op)).trans ((map_add _ _ _).trans ?_)
    exact congrArg₂ _ (hevres U (W i) (homOfLE hi).op _ z hzi) ((hev _ z hzi).2.2 _)
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    rw [hh U i hi z hzi, hh U i hi _ ((hpp _ l z).2 hzi), hper i l z hzi, hvp _ (f U _ hi)]
    ring

end GlobalTheory.CechPer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.SmallStepSurj

theorem spMap_comp_hom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem surj_of_smallExt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (∀ (k : Type) [Field k] (σ : R' →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ B.left) (w : IsPullback ψ s₀ B.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) := by
  intro R _ _ t R' _ σ' hσ' hker ht hm hfield hR' A _ g hA hg k _ σ hσ X₀ s₀ ψ w
  have hkerσ : RingHom.ker σ = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective σ hσ)
  by_cases htm : t ∈ IsLocalRing.maximalIdeal R
  ·
    let R₀ := R ⧸ IsLocalRing.maximalIdeal R
    let σ₀ : R →+* R₀ := Ideal.Quotient.mk _
    have hR₀ : IsField R₀ :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 (IsLocalRing.maximalIdeal.isMaximal R)
    have hse : SmallExt t σ' σ₀ := by
      refine ⟨hσ', hker, Ideal.Quotient.mk_surjective, fun a => ?_⟩
      rw [Ideal.Quotient.eq_zero_iff_mem]
      constructor
      · exact hm a
      · intro hat
        by_contra hna
        have hu : IsUnit a := by
          by_contra hnu
          exact hna ((IsLocalRing.mem_maximalIdeal a).2 hnu)
        exact ht (hu.mul_right_eq_zero.1 hat)

    have hP' := IsPullback.of_hasPullback A.hom (spMap σ')
    have hP₀ := IsPullback.of_hasPullback A.hom (spMap σ₀)
    obtain ⟨i', hg', hab', hsm'⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R' σ' A _ _ _ hP'
    obtain ⟨i₀, hg₀, hab₀, hsm₀⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R₀ σ₀ A _ _ _ hP₀
    have hstep := GlobalTheory.T.small_extension_primitive_lift R R' R₀ t σ' σ₀ g A _ _ _ _ hg' hg₀ hse hA hg
      (hR' _ g (hab' hA) (hsm' g hg)).2 (hfield R₀ hR₀ _ g (hab₀ hA) (hsm₀ g hg)).2.1

    have hle : RingHom.ker σ' ≤ RingHom.ker σ := by
      rw [hker, Ideal.span_le, Set.singleton_subset_iff, hkerσ]; exact htm
    let τ : R' →+* k := RingHom.liftOfRightInverse σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩
    have hτ : ∀ r, τ (σ' r) = σ r := fun r =>
      RingHom.liftOfRightInverse_comp_apply σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩ r
    have hτs : Function.Surjective τ := fun y => by
      obtain ⟨x, rfl⟩ := hσ y; exact ⟨σ' x, hτ x⟩
    have hcomp : spMap σ = spMap τ ≫ spMap σ' := by
      rw [← spMap_comp_hom]; congr 1; ext r; exact (hτ r).symm
    let ψ' : X₀ ⟶ pullback A.hom (spMap σ') := hP'.lift ψ (s₀ ≫ spMap τ) (by rw [w.w, hcomp, Category.assoc])
    have hψ' : ψ' ≫ pullback.fst A.hom (spMap σ') = ψ := hP'.lift_fst _ _ _
    have w' : IsPullback ψ' s₀ (pullback.snd A.hom (spMap σ')) (spMap τ) := by
      refine IsPullback.of_right ?_ (hP'.lift_snd _ _ _) hP'
      rw [hψ', ← hcomp]; exact w
    have hsurj := (hR' (Over.mk (pullback.snd A.hom (spMap σ'))) g (hab' hA) (hsm' g hg)).1 k τ hτs X₀ s₀ ψ' w'
    intro y
    obtain ⟨x', rfl⟩ := hsurj y
    obtain ⟨a, rfl⟩ := hstep x'
    refine ⟨a, ?_⟩
    exact ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 R R' A.left (pullback A.hom (spMap σ')) A.hom (pullback.snd A.hom (spMap σ'))
      σ' (pullback.fst A.hom (spMap σ')) hg'.1.w k X₀ s₀ τ ψ' w'.w σ ψ w.w hψ'.symm (fun r => (hτ r).symm)).1 a |>.symm
  ·
    have hu : IsUnit t := by
      by_contra hnu
      exact htm ((IsLocalRing.mem_maximalIdeal t).2 hnu)
    have hinj : Function.Injective σ := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      have hma : a ∈ IsLocalRing.maximalIdeal R := by rw [← hkerσ]; exact ha
      exact (hu.mul_left_eq_zero).1 (hm a hma)
    exact GlobalTheory.T.pull_h1_surjective_of_bijective R k σ A.left X₀ A.hom s₀ ψ w ⟨hinj, hσ⟩

end GlobalTheory.AbCoh.SmallStepSurj
end

section

namespace GlobalTheory.FinGL

open Formalism.L2.DIV Module

theorem finiteDimensional_coindV_blockTri {F : Type} [Field F] [Fintype F] {r : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) :
    FiniteDimensional ℂ (Representation.coindV (blockTri (κ := F) b).subtype σ) := by
  classical
  have : Finite (GL (Fin r) F) := inferInstance
  infer_instance

theorem nPos_parInd (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ) (ρ k : ℕ) (h : ρ + k + 1 ≤ r) :
    nPos ψ (parInd b σ) ρ k = ∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam (Fintype.card F) (k - j) := by
  have hfd := finiteDimensional_coindV_blockTri b σ
  induction ρ with
  | zero =>
    rw [GlobalTheory.T.symmetricPositionCharMultiplicity_eq_sum_degenerateWhittaker F ψ hψ r _ (parInd b σ) k (by omega)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [GlobalTheory.T.degenerateWhittakerDim_parabolicInduction_cuspidal F ψ hψ r V b σ hσ j (Or.inl (by omega)), GlobalTheory.T.levi_whittaker_eq_one_of_cuspidal F ψ hψ r V b σ hσ, mul_one, mul_comm]
  | succ ρ ih =>
    rw [← GlobalTheory.T.symmetricPositionCharMultiplicity_succ_eq F ψ hψ r _ (parInd b σ) ρ k (by omega)]
    exact ih (by omega)

end GlobalTheory.FinGL
end

section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_dieudonneFunctor_glued_connected_etale : ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn)) (Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt)), Bc.Katz → Be.EtDual Bc → ∃ B : GlobalTheory.Dieu.Base p (fun _ _ _ => True), B.Katz ∧ B.EtDual B := by
  first | exact @GlobalTheory.Dieu.Glue.exists_katz_etDual | exact GlobalTheory.Dieu.Glue.exists_katz_etDual | (intros; apply GlobalTheory.Dieu.Glue.exists_katz_etDual <;> assumption)
end

section

open scoped Classical

theorem _root_.GlobalTheory.T.esymm_mul_schurPolynomialJacobiTrudi : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  first | exact @GlobalTheory.JSW.esymm_mul_schur | exact GlobalTheory.JSW.esymm_mul_schur | (intros; apply GlobalTheory.JSW.esymm_mul_schur <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem period_fibre_eq_value : PFix := by
  intro I _ g Λ _ F B _ 𝒜 _ h𝒜 σ e z hz y hy A _ hA φ m L u hE τ hτ P hP c per hper l
  let u' : Unif (⟨(fibFam u).V, (fibFam u).τ.comp τ, fun l ↦ (fibFam u).hol (τ l)⟩ : Fam Empty g Λ)
      (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V)) :=
    { E := (fibUnif u).E
      w := (fibUnif u).w
      per := fun l p hp ↦ (fibUnif u).per (τ l) p hp
      hol := (fibUnif u).hol }
  have h1 := GlobalTheory.T.period_comp_translationGroup_hom (fibUnif u) τ u' rfl _ _ (hP (m.pull c))
  have h2 := GlobalTheory.AnPer.isPeriod_pull1_eq_comap u' e (GlobalTheory.abelianScheme_left_isSeparated_of_affine A hA)
    (GlobalTheory.abelianScheme_left_isSeparated_of_affine 𝒜 h𝒜) (fun _ ↦ z) analyticOnNhd_const (fun _ _ ↦ hz)
    LinearMap.id (AddMonoidHom.id Λ) (fun l _ _ ↦ (hτ l).symm) y φ m.isMor
    (fun x ↦ Hol.ext_fn fun p hp ↦ by rw [Hol.fn_algebraMap _ hp, Hol.fn_comap _ _ _ _ hp, hy])
    (fun p _ ↦ (hE p.2).symm) c.1 per _ hper h1 l
  have hp : (0 : Empty → ℂ) ∈ (fibFam u).V := trivial
  have h3 := congrArg (fun f ↦ Hol.fn f 0) h2
  simp only [Hol.fn_comap _ _ _ _ hp] at h3
  exact (Hol.fn_algebraMap _ hp).symm.trans h3

end GlobalTheory.AnPer
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem pLie_holds : PLie := by
  intro A _ g hA _ L u P hP x
  have hs := GlobalTheory.T.abelianScheme_isSeparated_of_affine_base A hA
  obtain ⟨K, -, -, hK, hsm, -⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map (fibUnif u) (fibUnif u) id analyticOnNhd_id (fun _ h ↦ h)
    LinearMap.id (AddMonoidHom.id _) (fun _ _ _ ↦ rfl)
  obtain ⟨r, hr, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine (fibUnif u) hs K hsm
  obtain ⟨k, hk⟩ := hK.1 0 trivial
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_firstOrderJet_algHom (K.W k) 0 hk (0, (x : Fin g → ℂ))
  obtain ⟨v, hv, ht, hd⟩ := GlobalTheory.T.exists_tangent_of_uniformisation_jet u hs (K.W k) (r.x k) (hr k)
    ((congrArg (r.x k ≫ ·) (Category.comp_id A.hom).symm).trans (r.w k)) hk x ρ hρ
  refine ⟨v, ⟨ht, fun f hf ↦ ?_⟩, hd⟩
  obtain ⟨q, G, hq, hG, hGk, hGl⟩ := GlobalTheory.T.exists_global_bound_of_period_class K hK r f _ (hP ⟨_, hf⟩ K r hr)
  rw [GlobalTheory.T.form_on_tangent_eq_derivative_bounding_function K r k 0 hk x ρ hρ v hv f _ q hq, Hol.fderiv_fn_congr _ (hGk k) hk]
  have hdG : ∀ p, DifferentiableAt ℂ G p := fun p ↦ (hG p trivial).differentiableAt
  have hi : ∀ w : Fin g → ℂ, HasFDerivAt (fun w : Fin g → ℂ ↦ ((0, w) : Tot Empty g))
      (ContinuousLinearMap.inr ℂ (Empty → ℂ) (Fin g → ℂ)) w := fun w ↦ hasFDerivAt_prodMk_right _ _
  have := GlobalTheory.fderiv_zero_eq_of_const_differences u.Λ u.full (fun w ↦ G (0, w)) (fun l ↦ P l ⟨_, hf⟩)
    (fun w ↦ (hdG _).comp w (hi w).differentiableAt)
    (fun l w ↦ (hGl l (0, w) trivial).trans (congrArg (G (0, w) + ·) (Hol.fn_algebraMap _ trivial))) x
  rw [← this]
  exact congrArg (fun D : (Fin g → ℂ) →L[ℂ] ℂ ↦ D x) ((hdG (0, 0)).hasFDerivAt.comp (0 : Fin g → ℂ) (hi 0)).fderiv

end GlobalTheory.AnPer
end
end

section

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem perCl_add' {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (p q r : Λ →+ Hol F.V) (h : ∀ l, r l = p l + q l) : K.perCl r = K.perCl p + K.perCl q := by
  unfold Charts.perCl
  rw [← map_add (f := _)]
  congr 1
  refine Subtype.ext ?_
  funext T T' f
  change algebraMap (Hol F.V) T'.C (r f.deg) = algebraMap (Hol F.V) T'.C (p f.deg) + algebraMap (Hol F.V) T'.C (q f.deg)
  rw [h]
  exact (algebraMap (Hol F.V) T'.C).map_add _ _

theorem perCl_smul' {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (a : Hol F.V) (p r : Λ →+ Hol F.V) (h : ∀ l, r l = a * p l) : K.perCl r = a • K.perCl p := by
  refine Eq.trans ?_ ((H1.mk K.Oc).map_smul a (K.perZ p))
  refine congrArg (H1.mk K.Oc) (Subtype.ext ?_)
  funext T T' f
  change algebraMap (Hol F.V) T'.C (r f.deg) = a • algebraMap (Hol F.V) T'.C (p f.deg)
  rw [h, map_mul, Algebra.smul_def]

theorem hol_point (f : Hol (⊤ : Opens (Empty → ℂ))) : algebraMap ℂ _ (f.fn 0) = f :=
  Hol.ext_fn fun p hp ↦ by rw [Hol.fn_algebraMap _ hp, Subsingleton.elim p 0]

theorem pHom_of (hE : PExist) (hU : PUniq) : PHom := by
  intro A _ g hA L u
  have : IsProper A.hom := hA.proper
  have : IsSeparated (A.hom ≫ 𝟙 _) := inferInstance
  have hB : (fibUnif u).Based := by
    let f : Sp ℂ ⟶ A.left := (u.ex 0).left
    have hs : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    let pt : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := (A.left.isBasis_affineOpens).exists_subset_of_mem_open
      (Set.mem_univ (f pt)) isOpen_univ
    refine ⟨U, hU, fun z _ q _ ↦ ?_⟩
    rw [Subsingleton.elim q pt]
    exact hx
  choose per hper using fun c : primDR A ↦ hE _ _ _ _ _ _ _ _ (fibUnif u) hB c.1
  have hadd : ∀ c c' : primDR A, per (c + c') = per c + per c' := fun c c' ↦
    hU _ _ _ _ _ _ _ _ (fibUnif u) _ _ _ (hper (c + c')) fun K r hr ↦ by
      rw [perCl_add' K (per c) (per c') _ fun _ ↦ rfl, ← hper c K r hr, ← hper c' K r hr, ← map_add (f := _)]
      rfl
  have hsmul : ∀ (a : ℂ) (c : primDR A), per (a • c) =
      (AddMonoidHom.mulLeft (algebraMap ℂ (Hol (fibFam u).V) a)).comp (per c) := fun a c ↦
    hU _ _ _ _ _ _ _ _ (fibUnif u) _ _ _ (hper (a • c)) fun K r hr ↦ by
      rw [perCl_smul' K (algebraMap ℂ (Hol (fibFam u).V) a) (per c) _ fun _ ↦ rfl, ← hper c K r hr, ← map_smulₛₗ]
      rfl
  let ev : Hol (fibFam u).V →ₐ[ℂ] ℂ := Hol.ev 0 trivial
  refine ⟨{ toFun x :=
              { toFun c := ev (per c x)
                map_add' c c' := by rw [hadd, AddMonoidHom.add_apply, map_add (f := _)]
                map_smul' a c := by
                  rw [hsmul]
                  change ev (algebraMap ℂ _ a * per c x) = a * _
                  rw [map_mul, AlgHom.commutes]; rfl }
            map_zero' := LinearMap.ext fun c ↦ by
              change ev (per c 0) = 0
              rw [map_zero, map_zero]
            map_add' x y := LinearMap.ext fun c ↦ by
              change ev (per c (x + y)) = ev (per c x) + ev (per c y)
              rw [map_add (f := _), map_add (f := _)] }, fun c ↦ ?_⟩
  convert hper c using 1
  refine AddMonoidHom.ext fun x ↦ ?_
  change algebraMap ℂ (Hol (fibFam u).V) (ev (per c x)) = per c x
  exact (congrArg _ (Hol.ev_apply (W := (fibFam u).V) 0 trivial (per c x))).trans (hol_point _)

theorem pHom : PHom := pHom_of GlobalTheory.T.periods_exist_affine_zero_section GlobalTheory.T.periods_of_deRham_classes_unique

end GlobalTheory.AnPer
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.deRham_crystal_two_reductions_agree : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁,
      Function.Bijective (N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀) ∧
      ∀ d : Crys κ (spMap π) A₀, crysToDR κ h d = crysToDR (divided₂ hJ) h₂ ((N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  first | exact @GlobalTheory.SqLift.crys_two_reductions | exact GlobalTheory.SqLift.crys_two_reductions | (intros; apply GlobalTheory.SqLift.crys_two_reductions <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.group_scheme_divided_power_lift_tower : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ F : Submodule R (HdR A), IsAdmissible h F → ∃ F₁ : Submodule R₁ (HdR A₁), IsAdmissible h₁ F₁ ∧
      ∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y := by
  first | exact @GlobalTheory.SqLift.isAdmissible_reduce | exact GlobalTheory.SqLift.isAdmissible_reduce | (intros; apply GlobalTheory.SqLift.isAdmissible_reduce <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.hodgeFiltration_comp_iso_lift_iff : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (σ : A₀ ⟶ B₀) [IsMonHom σ] [IsIso σ] (X : Over (Sp R)) (j : B₀.left ⟶ X.left)
    (wj : j ≫ X.hom = B₀.hom ≫ spMap π) (w : (σ.left ≫ j) ≫ X.hom = A₀.hom ≫ spMap π) (d : Crys κ (spMap π) A₀),
    d ∈ schemeFil κ A₀ X (σ.left ≫ j) w ↔ push κ (spMap π) σ d ∈ schemeFil κ B₀ X j wj := by
  first | exact @GlobalTheory.SqLift.schemeFil_comp_iso | exact GlobalTheory.SqLift.schemeFil_comp_iso | (intros; apply GlobalTheory.SqLift.schemeFil_comp_iso <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.hodgeFiltration_middle_eq_reduction_of_top : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _)) (F : Submodule R (HdR A)) (F₁ : Submodule R₁ (HdR A₁)),
      (∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y) →
      (∀ d₁, crysToDR κ₁ h₁ d₁ ∈ F₁ ↔ ∃ d, crysToDR κ h d ∈ F ∧ M.Corr d d₁) ∧
      ((∀ y : HdR A₁, y ∈ Fil A₁ ↔ ∃ x ∈ Fil A, (redMor h₂).Corr x y)) := by
  first | exact @GlobalTheory.FilRed.filtration_reduction | exact GlobalTheory.FilRed.filtration_reduction | (intros; apply GlobalTheory.FilRed.filtration_reduction <;> assumption)
end
