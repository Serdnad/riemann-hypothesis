module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle049
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCocycleTangentContractionCohomologousTorsor
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.Adjoin.PowerBasis
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory

theorem charpoly_mulLeft_eq_of_adjoin_eq_top {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (u : A) (P : F[X]) (hP : P.Monic) (hadj : Algebra.adjoin F {u} = ⊤)
    (hu : aeval u P = 0) (hdim : Module.finrank F A = P.natDegree) :
    (LinearMap.mulLeft F u).charpoly = P := by
  have hint : IsIntegral F u := ⟨P, hP, hu⟩
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hgen : pb.gen = u := PowerBasis.ofAdjoinEqTop_gen hint hadj
  have hmin : minpoly F u = P := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hP (minpoly.dvd F u hu) ?_).symm
    rw [← hdim, pb.finrank, PowerBasis.ofAdjoinEqTop_dim]
  have h1 := charpoly_leftMulMatrix pb
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, hgen, hmin] at h1
  exact h1

theorem charpoly_mulLeft_eq_map_symm : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (R : Type) [Field R] (e : K.E ≃+* R) (u : B.A) (Q : R[X]), Q.Monic → Algebra.adjoin K.E {u} = ⊤ → aeval u (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom := by
  intro K B R _ e u Q hQ hadj hu hdim
  exact charpoly_mulLeft_eq_of_adjoin_eq_top u _ (hQ.map _) hadj hu (by rw [hdim, hQ.natDegree_map])

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ParabLevel

open GlobalTheory.SmGL

section General

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  {n : Type} [Fintype n] [DecidableEq n]

theorem isClosed_parab_two {a b : Type} (e : a ⊕ b ≃ n) :
    IsClosed (parab R (two e) : Set (GL n R)) := by
  have h : (parab R (two e) : Set (GL n R)) =
      ⋂ (j : b) (i : a), {g : GL n R | (g : Matrix n n R) (e (.inr j)) (e (.inl i)) = 0} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_parab_two R
  rw [h]
  exact isClosed_iInter fun j => isClosed_iInter fun i =>
    isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const

theorem continuous_leviProj {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ x, Fintype (m x)]
    [∀ x, DecidableEq (m x)] (e : (Σ x, m x) ≃ n) : Continuous (leviProj R e) := by
  refine continuous_pi fun x => Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun p : parab R e => ((p : GL n R) : Matrix n n R) (e ⟨x, i⟩) (e ⟨x, j⟩)
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
  · have hc : Continuous fun p : parab R e => ((leviProj R e p⁻¹ x : GL (m x) R) : Matrix (m x) (m x) R) := by
      refine continuous_matrix fun i j => ?_
      show Continuous fun p : parab R e => (((p⁻¹ : parab R e) : GL n R) : Matrix n n R) (e ⟨x, i⟩) (e ⟨x, j⟩)
      exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_elem _ _
    refine hc.congr fun p => ?_
    rw [map_inv]
    rfl

theorem continuous_leviTwo_symm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    Continuous (leviTwo R a b).symm :=
  (continuous_apply false).prodMk (continuous_apply true)

end General

end GlobalTheory.ParabLevel
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem exists_pic_patch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (a : Pic X') (b : Pic Z), GlobalTheory.CechPic.pull i' a = GlobalTheory.CechPic.pull p' b → ∃ e : Pic X, GlobalTheory.CechPic.pull p e = a ∧ GlobalTheory.CechPic.pull i e = b := by
  have hA1 := GlobalTheory.T.exists_lineBundle_generator_off_closed_subscheme
  have hA2 := GlobalTheory.T.exists_matching_lineBundle_generators_near_pinching_point
  have hB := GlobalTheory.T.pinchingSquare_glue_lineBundle_of_local_generators
  intro X X' Z Z' p i i' p' hsq hp hi hgl a b hab
  obtain ⟨L', hL', rfl⟩ := cls_surj a
  obtain ⟨LZ, hLZ, rfl⟩ := cls_surj b
  rw [← cls_pull hL' i' (pull_isLB hL' i'), ← cls_pull hLZ p' (pull_isLB hLZ p')] at hab
  obtain ⟨w, hw⟩ := (cls_eq_iff _ _).1 hab
  refine hB X X' Z Z' p i i' p' hsq hgl L' LZ hL' hLZ w hw fun x => ?_
  by_cases hx : ∃ z, i z = x
  · obtain ⟨z, rfl⟩ := hx
    exact hA2 X X' Z Z' p i i' p' hsq hp hi hgl L' LZ hL' hLZ w hw z
  · push_neg at hx
    obtain ⟨W, s', hxW, hbot, hs'⟩ := hA1 X X' Z Z' p i i' p' hsq hp hi hgl L' hL' x hx
    have hno : ∀ y : Z, y ∉ i ⁻¹ᵁ W := fun y hy => by rw [hbot] at hy; exact hy
    refine ⟨W, s', fun _ => 1, hxW, hs', fun k l y _ _ hy => (hno y hy).elim,
      fun z j k _ _ hz _ => (hno _ hz).elim⟩

end GlobalTheory.PinchLift
end

section

open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

open MeasureTheory in
open scoped FourierTransform ContDiff in
private theorem mem_levSet_iff_unitriangular_below_r {n r : ℕ} {g : GL (Fin n) ℂ} :
    g ∈ _root_.GlobalTheory.JSW.levSet n r ↔
      ∀ i : Fin n, r ≤ (i : ℕ) →
        (∀ j < i, (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧ (g : Matrix (Fin n) (Fin n) ℂ) i i = 1 :=
  Iff.rfl

open MeasureTheory in
open scoped FourierTransform ContDiff in
private theorem mul_apply_eq_apply_of_unitriangular_index_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    {i : Fin n} (hA : (∀ j < i, A i j = 0) ∧ A i i = 1)
    (hB : ∀ k, i < k → ∀ j < k, B k j = 0) (j : Fin n) (hj : j ≤ i) :
    (A * B) i j = B i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA.2, one_mul]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hA.1 k hk, zero_mul]
    · rw [hB k hk j (lt_of_le_of_lt hj hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h


open MeasureTheory in
open scoped FourierTransform ContDiff in
theorem _root_.GlobalTheory.JSW.levSet_closed_subgroup : ∀ (n r : ℕ),
    (∀ g ∈ _root_.GlobalTheory.JSW.levSet n r, ∀ h ∈ _root_.GlobalTheory.JSW.levSet n r,
      g * h ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    (∀ g ∈ _root_.GlobalTheory.JSW.levSet n r, g⁻¹ ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    (∀ u ∈ _root_.GlobalTheory.SmGL.unipB ℂ (Fin n), u ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    IsClosed (_root_.GlobalTheory.JSW.levSet n r) := by
  intro n r
  refine ⟨fun g hg h hh => ?_, fun g hg => ?_, fun u hu => ?_, ?_⟩
  · rw [mem_levSet_iff_unitriangular_below_r] at hg hh ⊢
    intro i hi
    have hrow := mul_apply_eq_apply_of_unitriangular_index_le (hg i hi) (B := (h : Matrix (Fin n) (Fin n) ℂ))
      fun k hk => (hh k (hi.trans (Fin.lt_iff_val_lt_val.mp hk).le)).1
    rw [Units.val_mul]
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [hrow j hj.le]
      exact (hh i hi).1 j hj
    · rw [hrow i le_rfl]
      exact (hh i hi).2
  · rw [mem_levSet_iff_unitriangular_below_r] at hg ⊢
    have hgh : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
      Units.mul_inv g
    have key : ∀ m : ℕ, ∀ i : Fin n, r ≤ (i : ℕ) → n - (i : ℕ) ≤ m →
        (∀ j < i, ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
          ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1 := by
      intro m
      induction m with
      | zero =>
        intro i _ hm
        have := i.isLt
        omega
      | succ m ih =>
        intro i hi hm
        have hrow := mul_apply_eq_apply_of_unitriangular_index_le (hg i hi)
          (B := ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
          fun k hk => by
            have hik := Fin.lt_iff_val_lt_val.mp hk
            exact (ih k (hi.trans hik.le) (by omega)).1
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [← hrow j hj.le, hgh, Matrix.one_apply_ne hj.ne']
        · rw [← hrow i le_rfl, hgh, Matrix.one_apply_eq]
    exact fun i hi => key n i hi (Nat.sub_le _ _)
  · rw [_root_.GlobalTheory.SmGL.mem_unipB] at hu
    exact fun i _ => ⟨fun j hj => hu.1 i j hj, hu.2 i⟩
  · have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) i j :=
      fun i j => Units.continuous_val.matrix_elem i j
    have hset : _root_.GlobalTheory.JSW.levSet n r = ⋂ i : Fin n, ⋂ (_ : r ≤ (i : ℕ)),
        ((⋂ j : Fin n, ⋂ (_ : j < i), {g : GL (Fin n) ℂ | (g : Matrix (Fin n) (Fin n) ℂ) i j = 0}) ∩
          {g : GL (Fin n) ℂ | (g : Matrix (Fin n) (Fin n) ℂ) i i = 1}) := by
      ext g
      simp only [mem_levSet_iff_unitriangular_below_r, Set.mem_iInter, Set.mem_inter_iff,
        Set.mem_setOf_eq]
    rw [hset]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      (isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const).inter
        (isClosed_eq (hc i i) continuous_const)

end GlobalTheory.JSW
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.RatDarbouxPointsD



theorem ratL_iff_ratPair : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
  intro D S T κ _ e hrat w
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  · intro hp

    let bA := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)
    haveI : Module.Free (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := Module.Finite.of_basis bA
    have hAE : Module.finrank (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) =
        Module.finrank D.host.F D.host.E := by
      rw [Module.finrank_eq_card_basis bA, Fintype.card_fin]
    have hκ : 2 * Fintype.card κ = T.rank * S.rank * Module.finrank D.host.F D.host.E := by
      have h := e.finrank_eq
      have ha : Module.finrank (AF D.host.F)
          (Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
          T.rank * S.rank * Module.finrank D.host.F D.host.E := by
        show Module.finrank (AF D.host.F) (Fin T.rank → Fin S.rank → AF D.host.F ⊗[D.host.F] D.host.E) = _
        simp [Module.finrank_pi_fintype, hAE, mul_assoc]
      have hb : Module.finrank (AF D.host.F) ((κ → AF D.host.F) × (κ → AF D.host.F)) = 2 * Fintype.card κ := by
        rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
        ring
      rw [← hb, ← h, ha]

    let J1 : (κ → D.host.F) →ₗ[D.host.F] (κ → AF D.host.F) :=
      LinearMap.compLeft (Algebra.linearMap D.host.F (AF D.host.F)) κ
    let J : ((κ → D.host.F) × (κ → D.host.F)) →ₗ[D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) :=
      J1.prodMap J1
    let I : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F]
        Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E) :=
      (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
    let L := (e.toLinearMap.restrictScalars D.host.F).comp I
    have hJinj : Function.Injective J := by
      rintro ⟨y, z⟩ ⟨y', z'⟩ h
      have hi := AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F
      simp only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h
      refine Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)
      · exact congrFun h.1 i
      · exact congrFun h.2 i
    have hLinj : Function.Injective L := by
      have hr : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := RingHom.injective _
      intro x x' h
      have := e.injective h
      exact Matrix.ext fun i j => hr (congrFun (congrFun this i) j)
    have hle : LinearMap.range L ≤ LinearMap.range J := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, z, h⟩ := hrat x
      exact ⟨(y, z), by rw [show L x = e (incM D.host.F x) from rfl, h]; rfl⟩
    have heq : LinearMap.range L = LinearMap.range J := by
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]
      have hm : Module.finrank D.host.F (Matrix (Fin T.rank) (Fin S.rank) D.host.E) =
          T.rank * S.rank * Module.finrank D.host.F D.host.E := by
        show Module.finrank D.host.F (Fin T.rank → Fin S.rank → D.host.E) = _
        simp [Module.finrank_pi_fintype, mul_assoc]
      have hp2 : Module.finrank D.host.F ((κ → D.host.F) × (κ → D.host.F)) = 2 * Fintype.card κ := by
        rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
        ring
      rw [hm, hp2, hκ]
    obtain ⟨y, z, hw⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
    have hm : J (y, z) ∈ LinearMap.range L := heq ▸ LinearMap.mem_range_self J (y, z)
    obtain ⟨x, hx⟩ := hm
    refine ⟨x, ?_⟩
    have hx' : e (incM D.host.F x) = e w := by rw [hw]; exact hx
    exact e.injective hx'

end GlobalTheory.RatDarbouxPointsD

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaRatInv

theorem invOf_two_eq' {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] :
    ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

theorem thetaSum_schr_rat_add {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) {κ : Type} [Fintype κ] (Φ : (κ → AF F) → ℂ) (a b : κ → F)
    (w : (κ → AF F) × (κ → AF F)) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ ((fun i => algebraMap F (AF F) (a i), fun i => algebraMap F (AF F) (b i)) + w) Φ) =
      ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ (fun i => algebraMap F (AF F) (b i)) - (fun i => algebraMap F (AF F) (a i)) ⬝ᵥ w.2)) *
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ) := by
  set ra : κ → AF F := fun i => algebraMap F (AF F) (a i) with hra
  set rb : κ → AF F := fun i => algebraMap F (AF F) (b i) with hrb
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : κ → F => ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ rb - ra ⬝ᵥ w.2)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  set rξ : κ → AF F := fun i => algebraMap F (AF F) (ξ i) with hrξ
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rξ + ra := by
    funext i; simp [hrξ, hra]
  have e3 : ∀ c d : κ → F, (fun i => algebraMap F (AF F) (c i)) ⬝ᵥ (fun i => algebraMap F (AF F) (d i)) =
      algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [dotProduct]
  rw [e1]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have hx : rξ + (ra + w.1) = rξ + ra + w.1 := (add_assoc _ _ _).symm
  rw [hx]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  conv_rhs => rw [← mul_one (ψ _), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add (f := _), map_mul, ← invOf_two_eq', ← e3, ← e3]
  simp only [add_dotProduct, dotProduct_add]
  have t : ∀ z : AF F, ⅟(2 : AF F) * z + ⅟(2 : AF F) * z = z := fun z => by
    rw [← add_mul, invOf_two_add_invOf_two, one_mul]
  linear_combination t (ra ⬝ᵥ w.2)

theorem norm_thetaSum_schr_ratPair_add : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ),
    ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (γ + w) Φ)‖ = ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ := by
  intro F _ _ ψ hψ κ _ Φ γ hγ w
  obtain ⟨a, b, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff γ).mp hγ
  rw [thetaSum_schr_rat_add ψ hψ.2.2.1 Φ a b w, norm_mul, hψ.2.1, one_mul]

end GlobalTheory.ThetaRatInv

end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ y, IsUnitFr X y → y ∈ X.dom) ∧ (∀ x ∈ X.dom, ∃ y, IsUnitFr X y ∧ ∃ b ∈ Bor X.Ψ r, x = rmul y b) ∧ (∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, IsUnitFr X (rmul y b) → ∃ t : X.Ψ → Fin r → ℝ, b = (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom) ∧ (∀ y, IsUnitFr X y → ∀ γ ∈ X.Γ, IsUnitFr X (lact γ y)) ∧ (∀ y, IsUnitFr X y → ∀ Z ∈ unitLie X, IsUnitFr X (rmul y (expFr Z))) ∧ ∀ (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, P (rmul y b) = bchar la b * P y → X.pnorm la P (rmul y b) = ‖P y‖ := by
  first | exact @GlobalTheory.FlagGS.gram_schmidt_frames | exact GlobalTheory.FlagGS.gram_schmidt_frames | (intros; apply GlobalTheory.FlagGS.gram_schmidt_frames <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.chernCocycle_tangentContraction_cohomologous_torsor : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB →
    ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j →
    ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)),
    (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ →
      T''.J = ⊥ → w.1 T T' T'' a b = 0) →
    ∀ (i : (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).FullSubcategory → P.ι)
      (hi : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ P.U (i T))
      (U : ∀ T T' : (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).FullSubcategory, (T ⟶ T') → T'.obj.B)
      (ℓ : Z2 ((IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι ⋙ O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))),
    (∀ T T' φ, T'.obj.π (U T T' φ) = evalAt T'.obj.x (P.U (i T') ⊓ P.U (i T))
      (le_inf (hi T') (φ.hom.le_preimage (hi T))) (P.g (i T') (i T)).val) →
    (∀ T T' T'' φ ψ, (ℓ.1 T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (ℓ.1 T T' T'' φ ψ) * U T T'' (φ ≫ ψ) = ψ.hom.φ (U T T' φ) * U T' T'' ψ) →
    ∀ n : C1 ((IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι ⋙ O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)),
    d1 _ n = ((CoefMap.restrict (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))
      (IsSmall (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P.U).ι).pullbackTwoCocycle w).1 - ℓ.1 →
    ∀ κ : Fn1 A, IsContr w.1 v κ → Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull (cocOf P.U n) v)) := by
  first | exact @GlobalTheory.PtExt.ChernContr.contr_cohom | exact GlobalTheory.PtExt.ChernContr.contr_cohom | (intros; apply GlobalTheory.PtExt.ChernContr.contr_cohom <;> assumption)
end
