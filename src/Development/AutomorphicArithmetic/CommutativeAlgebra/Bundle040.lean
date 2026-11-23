module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.EtaleCohomology.EtaleSheaves.Bundle009
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle039
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle012
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle026
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsBijectiveCohomologyClassProductAdjunction
public import Development.AutomorphicArithmetic.CommutativeAlgebra.InjectiveProductPushforwardOfInjective
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OffDiagonalContinuationInductive
public import Development.EtaleCohomology.EtaleTrace.Bundle001
public import Development.EtaleCohomology.WeilConjectures.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle409
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.FunctionField.PlaceDefs

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

private theorem rcx_ge (R : Type) [CommRing R] (L : Cx R) [L.IsStrictlyGE 0] :
    ((rcx (Int.castRingHom R)).obj L).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (restr (Int.castRingHom R)).map_isZero (L.isZero_of_isStrictlyGE 0 i hi)

private theorem semi_bij (R : Type) [CommRing R] (L B : Cx R) [L.IsStrictlyGE 0] [B.IsStrictlyGE 0]
    (hL : ∀ s, Injective (L.X s)) (hB : ∀ s, Injective (B.X s)) (ρ : SemiMap L B) (E : Spc)
    (hs : ∀ (T : Scheme.{0}), Nonempty (Sx E 0 T) → ∀ (n : ℤ) (b : Sec (B.X n) T), Sec.map (B.d n (n + 1)) b = 0 →
      Loc T fun V g => ∃ (a : Sec (L.X n) V) (c : Sec (B.X (n - 1)) V), Sec.map (L.d n (n + 1)) a = 0 ∧
        ρ.app V n a = Sec.res g b + Sec.map (B.d (n - 1) n) c)
    (hi : ∀ (T : Scheme.{0}), Nonempty (Sx E 0 T) → ∀ (n : ℤ) (a : Sec (L.X n) T), Sec.map (L.d n (n + 1)) a = 0 →
      (∃ c : Sec (B.X (n - 1)) T, ρ.app T n a = Sec.map (B.d (n - 1) n) c) →
      Loc T fun V g => ∃ a' : Sec (L.X (n - 1)) V, Sec.map (L.d (n - 1) n) a' = Sec.res g a) (n : ℤ) :
    Function.Bijective (ρ.op.app E n) := by
  have gL := rcx_ge R L
  have gB := rcx_ge R B
  apply UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward
  haveI hC : (mappingCone ρ.toZ).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [mappingCone.isZero_X_iff]
    exact ⟨((rcx (Int.castRingHom R)).obj L).isZero_of_isStrictlyGE 0 _ (by omega),
      ((rcx (Int.castRingHom R)).obj B).isZero_of_isStrictlyGE 0 _ (by omega)⟩
  have hQ : ∀ {V U : Scheme.{0}} (a : V ⟶ U), Nonempty (Sx E 0 U) → Nonempty (Sx E 0 V) :=
    fun a ⟨x⟩ => ⟨Sx.res a x⟩
  have hsub : ∀ m, Subsingleton (CohomologyClass ((chains ℤ).obj E) (mappingCone ρ.toZ) m) :=
    UpperTheory.subsingleton_cohomologyClass_chains_of_acy_locally_exact (mappingCone ρ.toZ) (-1) E (UpperTheory.acy_mappingCone_semiMap_of_injective R L B hL hB ρ _)
      (UpperTheory.bijective_semiMap_of_locally_surjective_on_cocycles R L B ρ (fun T => Nonempty (Sx E 0 T)) hQ hs hi)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  constructor
  · have ex := (GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact ℤ ((chains ℤ).obj E) ρ.toZ m).2.2
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (ex x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · have ex := (GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact ℤ ((chains ℤ).obj E) ρ.toZ (m + 1)).1
    intro x
    exact (ex x).1 (Subsingleton.elim _ _)

theorem UpperTheory.injectiveComplex_productSection_map_quasiIso :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) (L I : Cx R) [L.IsStrictlyGE 0] [I.IsStrictlyGE 0],
        (∀ s, Injective (L.X s)) → (∀ s, Injective (I.X s)) →
        ∀ (ψ : ∀ (T : Scheme.{0}) (s : ℤ), Sec (L.X s) T →+ Sec (I.X s) (W ⨯ T)),
        (∀ {T' T : Scheme.{0}} (g : T' ⟶ T) (s : ℤ) (a : Sec (L.X s) T), Sec.res (prod.map (𝟙 W) g) (ψ T s a) = ψ T' s (Sec.res g a)) →
        (∀ (T : Scheme.{0}) (s t : ℤ) (a : Sec (L.X s) T), Sec.map (I.d s t) (ψ T s a) = ψ T t (Sec.map (L.d s t) a)) →
        ∀ Z : Scheme.{0} → Prop, (∀ {T' T : Scheme.{0}}, (T' ⟶ T) → Z T → Z T') →
        (∀ (T : Scheme.{0}), Z T → ∀ (n : ℤ) (b : Sec (I.X n) (W ⨯ T)), Sec.map (I.d n (n + 1)) b = 0 →
          Loc T fun V g => ∃ (a : Sec (L.X n) V) (c : Sec (I.X (n - 1)) (W ⨯ V)), Sec.map (L.d n (n + 1)) a = 0 ∧
            ψ V n a = Sec.res (prod.map (𝟙 W) g) b + Sec.map (I.d (n - 1) n) c) →
        (∀ (T : Scheme.{0}), Z T → ∀ (n : ℤ) (a : Sec (L.X n) T), Sec.map (L.d n (n + 1)) a = 0 →
          (∃ c : Sec (I.X (n - 1)) (W ⨯ T), ψ T n a = Sec.map (I.d (n - 1) n) c) →
          Loc T fun V g => ∃ a' : Sec (L.X (n - 1)) V, Sec.map (L.d (n - 1) n) a' = Sec.res g a) →
        ∀ E : Spc, (∀ T : Scheme.{0}, Nonempty (Sx E 0 T) → Z T) →
        ∃ Φ : ∀ n : ℤ, CohomologyClass ((chains R).obj E) L n →+ CohomologyClass ((chains R).obj (sch.obj W ⨯ E)) I n,
          (∀ n, Function.Bijective (Φ n)) ∧
          ∀ (n : ℤ) (α : Cocycle ((chains R).obj E) L n),
            (∃ β : Cocycle ((chains R).obj (sch.obj W ⨯ E)) I n, Φ n (CohomologyClass.mk α) = CohomologyClass.mk β ∧
              ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T),
                ev β.1 p s h T y = Sec.res (prod.lift (show T ⟶ W from y.map prod.fst) (𝟙 T)) (ψ T s (ev α.1 p s h T (y.map prod.snd)))) := by
  intro R _ W L I _ _ hL hI ψ hψn hψc Z hZ hs hi E hE
  let ρ : SemiMap L (UpperTheory.Bc.Bc W I) :=
    { app := fun T s => ψ T s
      nat := fun g s a => hψn g s a
      comm := fun T s t a => hψc T s t a }
  haveI : (UpperTheory.Bc.Bc W I).IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi'
    exact Functor.map_isZero (UpperTheory.Bc.pw R W) (I.isZero_of_isStrictlyGE 0 i hi')
  have hB : ∀ s, Injective ((UpperTheory.Bc.Bc W I).X s) := fun s => by
    haveI := hI s
    exact UpperTheory.injective_productPushforward_of_injective R W (I.X s)
  have hbij := semi_bij R L (UpperTheory.Bc.Bc W I) hL hB ρ E
    (fun T hT n b hb => hs T (hE T hT) n b hb) (fun T hT n a ha hc => hi T (hE T hT) n a ha hc)
  choose Θ hΘ hΘf using fun n => UpperTheory.exists_bijective_cohomologyClass_product_adjunction R W I E n
  refine ⟨fun n => (Θ n).comp (ρ.op.app E n), fun n => (hΘ n).comp (hbij n), ?_⟩
  intro n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).1 E n α
  have e1 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).2 E n α β' hβ'
  obtain ⟨β, hβ, hβf⟩ := hΘf n β'
  refine ⟨β, ?_, ?_⟩
  · show Θ n (ρ.op.app E n (CohomologyClass.mk α)) = _
    rw [e1, hβ]
  · intro p s h T y
    rw [hβf p s h T y, hβ' p s h T]
    rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.Cb.MuCohomologyGluing

private theorem sub_empty (q : ℕ) (Y : Scheme.{0}) [IsEmpty Y] (n i : ℤ) :
    Subsingleton (Ht q (sch.obj Y) n i) := by
  have e : Y ≅ ⊥_ Scheme.{0} := (isInitialOfIsEmpty (X := Y)).uniqueUpToIso initialIsInitial
  exact LateralTheory.EtaleTrace.H_sub (ZMod q) Y
    (LateralTheory.EWeil.EmptyVan₂.isZero_free.of_iso ((free (ZMod q)).mapIso (yoneda.mapIso e))) (tw q i) n

private theorem pl_le (q : ℕ) {X : Scheme.{0}} {A B C : X.Opens} (h1 : A ≤ B) (h2 : B ≤ C) (h3 : A ≤ C)
    (z : Ht q (sch.obj C) 1 1) :
    pl q 1 (X.homOfLE h1) 1 (pl q 1 (X.homOfLE h2) 1 z) = pl q 1 (X.homOfLE h3) 1 z := by
  rw [← pl_comp, Scheme.homOfLE_homOfLE]

private theorem van (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X] (hζ : Nonempty (Prim q Γ(X, ⊤)))
    (hq : IsUnit (q : Γ(X, ⊤))) (n : ℕ) (A : Fin n → X.Opens) (P : X.Opens) (hP : P ≤ ⨆ i, A i)
    (d : Ht q (sch.obj P) 1 1)
    (hd : ∀ i, pl q 1 (X.homOfLE (inf_le_right : A i ⊓ P ≤ P)) 1 d = 0) : d = 0 := by
  have hmem : ∀ x : P.toScheme, P.ι x ∈ P := fun x => by
    rw [← SetLike.mem_coe, ← P.range_ι]
    exact ⟨x, rfl⟩
  by_cases hne : Nonempty P.toScheme
  · haveI : IsIntegral P.toScheme := isIntegral_of_isOpenImmersion P.ι
    have hζ' : Nonempty (Prim q Γ(P.toScheme, ⊤)) := hζ.map (Prim.map P.ι.appTop.hom)
    have hq' : IsUnit (q : Γ(P.toScheme, ⊤)) := by simpa using hq.map P.ι.appTop.hom
    have key := UpperTheory.h1_pl_eq_zero_of_le_iSup_of_local_zero q P.toScheme hζ' hq' n (fun i => P.ι ⁻¹ᵁ A i) ⊤ (by
      intro x _
      have hx : P.ι x ∈ ⨆ i, A i := hP (hmem x)
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩) d (fun i => by
        have e : P.ι ⁻¹ᵁ A i ≤ P.ι ⁻¹ᵁ (A i ⊓ P) := by
          intro x hx
          exact ⟨hx, hmem x⟩
        have w : P.ι.resLE (A i ⊓ P) (P.ι ⁻¹ᵁ A i) e ≫ X.homOfLE (inf_le_right : A i ⊓ P ≤ P) =
            (P.ι ⁻¹ᵁ A i).ι := by
          rw [← cancel_mono P.ι]
          simp
        rw [← w, pl_comp, hd i, map_zero])
    have w : P.toScheme.topIso.inv ≫ (⊤ : P.toScheme.Opens).ι = 𝟙 _ := P.toScheme.topIso.inv_hom_id
    have := congrArg (pl q 1 P.toScheme.topIso.inv 1) key
    rw [← pl_comp, w, map_zero] at this
    simpa [pl, pull_id] using this
  · haveI : IsEmpty P.toScheme := not_nonempty_iff.1 hne
    haveI := sub_empty q P.toScheme 1 1
    exact Subsingleton.elim _ _

end UpperTheory.Cb.MuCohomologyGluing

open UpperTheory.Cb.MuCohomologyGluing in
theorem UpperTheory.exists_h1Mu_glue_of_compatible :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → ∀ (n : ℕ) (U : Fin n → X.Opens) (x : ∀ i, Ht q (sch.obj (U i)) 1 1), (∀ i j, pl q 1 (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) 1 (x i) = pl q 1 (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) 1 (x j)) → ∃ y : Ht q (sch.obj (⨆ i, U i : X.Opens)) 1 1, ∀ i, pl q 1 (X.homOfLE (le_iSup U i)) 1 y = x i := by
  intro q _ X _ hζ hq n
  induction n with
  | zero =>
    intro U x _
    exact ⟨0, fun i => i.elim0⟩
  | succ n ih =>
    intro U x hx
    set W : X.Opens := ⨆ i : Fin n, U i.castSucc with hW
    have hAW : ∀ i : Fin n, U i.castSucc ≤ W := fun i => le_iSup (fun i : Fin n => U i.castSucc) i
    obtain ⟨y, hy⟩ : ∃ y : Ht q (sch.obj W) 1 1, ∀ i : Fin n, pl q 1 (X.homOfLE (hAW i)) 1 y = x i.castSucc :=
      ih (fun i => U i.castSucc) (fun i => x i.castSucc) (fun i j => hx _ _)
    set B : X.Opens := U (Fin.last n) with hB
    have c : UpperTheory.Cb.OffDiagonalContinuation.Sq W B (W ⊔ B) (W ⊓ B) := ⟨rfl, rfl⟩
    obtain ⟨dd, hdd, -⟩ := UpperTheory.Cb.OffDiagonalContinuation.mv q 1
    have hex := (hdd c 1).2.2
    have d0 : pl q 1 (X.homOfLE (inf_le_left : W ⊓ B ≤ W)) 1 y -
        pl q 1 (X.homOfLE (inf_le_right : W ⊓ B ≤ B)) 1 (x (Fin.last n)) = 0 := by
      refine van q X hζ hq n (fun i => U i.castSucc) (W ⊓ B) inf_le_left _ (fun i => ?_)
      have h1 : U i.castSucc ⊓ (W ⊓ B) ≤ U i.castSucc ⊓ B := inf_le_inf_left _ inf_le_right
      rw [map_sub, pl_le q _ _ (inf_le_right.trans inf_le_left), pl_le q _ _ (inf_le_right.trans inf_le_right),
        ← pl_le q (inf_le_left : U i.castSucc ⊓ (W ⊓ B) ≤ U i.castSucc) (hAW i),
        ← pl_le q h1 (inf_le_right : U i.castSucc ⊓ B ≤ B), hy i, ← hx i.castSucc (Fin.last n),
        pl_le q h1 inf_le_left inf_le_left, sub_self]
    obtain ⟨z, hz⟩ := (hex (y, x (Fin.last n))).1 d0
    have hz1 : pl q 1 (X.homOfLE (le_sup_left : W ≤ W ⊔ B)) 1 z = y := congrArg Prod.fst hz
    have hz2 : pl q 1 (X.homOfLE (le_sup_right : B ≤ W ⊔ B)) 1 z = x (Fin.last n) := congrArg Prod.snd hz
    have hle : (⨆ i, U i : X.Opens) ≤ W ⊔ B := by
      refine iSup_le fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact le_sup_right
      · exact (hAW j).trans le_sup_left
    refine ⟨pl q 1 (X.homOfLE hle) 1 z, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [pl_le q _ _ le_sup_right, hz2]
    · rw [pl_le q _ _ ((hAW j).trans le_sup_left), ← pl_le q (hAW j) (le_sup_left : W ≤ W ⊔ B), hz1]
      exact hy j
end
