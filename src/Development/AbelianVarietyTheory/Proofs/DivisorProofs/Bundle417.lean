module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftBasicOpenPairAgree
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle360
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
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Regular.Flat
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

theorem _root_.GlobalTheory.T.coeff_single_derivationTaylorPowerSeries : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (j : Fin n) (f : A), MvPowerSeries.coeff (Finsupp.single j 1) (taylor ev (fun i => ⇑(ds i)) f) = ev (ds j f) := by
  first | exact @GlobalTheory.FormalOrigin.Extend.taylor_coeff_single | exact GlobalTheory.FormalOrigin.Extend.taylor_coeff_single | (intros; apply GlobalTheory.FormalOrigin.Extend.taylor_coeff_single <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_squareZeroLift_basicOpen_pair_agree : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by
  first | exact @GlobalTheory.SecGlue.exists_pair_lift_comb | exact GlobalTheory.SecGlue.exists_pair_lift_comb | (intros; apply GlobalTheory.SecGlue.exists_pair_lift_comb <;> assumption)
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory.PurityComplete

variable (R : Type) [CommRing R] [IsRegularLocalRing R]

theorem algebraMap_mem_maximalIdeal {r : R} (hr : r ∈ maximalIdeal R) :
    algebraMap R (AdicCompletion (maximalIdeal R) R) r ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ hr

theorem faithfullyFlat_adicCompletion :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  haveI : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem modDepthGE_two_baseChange (A : Type) [CommRing A] [Algebra R A]
    (h : ReciprocityTheory.CA.ModDepthGE R A 2) :
    ReciprocityTheory.CA.ModDepthGE (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) R ⊗[R] A) 2 := by
  obtain ⟨rs, hl, hm, hreg⟩ := h
  refine ⟨rs.map (algebraMap R (AdicCompletion (maximalIdeal R) R)), by simp [hl], ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    exact algebraMap_mem_maximalIdeal R (hm s hs)
  · haveI := faithfullyFlat_adicCompletion R
    exact hreg.of_faithfullyFlat_of_isBaseChange (S := AdicCompletion (maximalIdeal R) R)
      (TensorProduct.isBaseChange R A (AdicCompletion (maximalIdeal R) R))

theorem etale_baseChange (A : Type) [CommRing A] [Algebra R A]
    (he : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A))
    (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime]
    (hP : P ≠ maximalIdeal (AdicCompletion (maximalIdeal R) R)) :
    Algebra.Etale (Localization.AtPrime P)
      (TensorProduct (AdicCompletion (maximalIdeal R) R) (Localization.AtPrime P)
        (AdicCompletion (maximalIdeal R) R ⊗[R] A)) := by
  set C := AdicCompletion (maximalIdeal R) R
  set p : Ideal R := P.comap (algebraMap R C) with hpdef
  have hp : p ≠ maximalIdeal R := by
    intro h
    apply hP
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, ← hpdef, h]
  haveI := he p hp
  haveI : P.LiesOver p := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p P
  let e : Localization.AtPrime P ⊗[Localization.AtPrime p] (Localization.AtPrime p ⊗[R] A) ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime P ⊗[C] (C ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) (Localization.AtPrime P)
      (Localization.AtPrime P) A).trans
    (Algebra.TensorProduct.cancelBaseChange R C (Localization.AtPrime P)
      (Localization.AtPrime P) A).symm
  exact Algebra.Etale.of_equiv e

theorem free_of_free_baseChange (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A]
    (h : Module.Free (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal R) R ⊗[R] A)) :
    Module.Free R A := by
  haveI := faithfullyFlat_adicCompletion R
  haveI : Module.Flat R A := Module.Flat.of_flat_tensorProduct R A (AdicCompletion (maximalIdeal R) R)
  exact Module.free_of_flat_of_isLocalRing

end GlobalTheory.PurityComplete

namespace GlobalTheory.PurityStep

theorem purityFree_of_complete :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      (∀ (S : Type) [CommRing S] [IsRegularLocalRing S], IsAdicComplete (maximalIdeal S) S →
        ringKrullDim S = ringKrullDim R → GlobalTheory.PurityFree S) → GlobalTheory.PurityFree R := by
  intro R _ _ H A _ _ _ hd he
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
    GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R
  have hC := H (AdicCompletion (maximalIdeal R) R) inferInstance (UpperTheory.V.CA.g_dimcpl R)
  refine GlobalTheory.PurityComplete.free_of_free_baseChange R A ?_
  exact hC _ (GlobalTheory.PurityComplete.modDepthGE_two_baseChange R A hd)
    (fun P _ hP => GlobalTheory.PurityComplete.etale_baseChange R A he P hP)

end GlobalTheory.PurityStep
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PtClosed

theorem closed_of_points : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S), P R' x → P R'' (spMap g ≫ x)) →
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
     ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧
    ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), (∃ y : Sp R' ⟶ Z, y ≫ i = x) ↔ P R' x := by
  intro S P hBC hLoc hCov
  have hrep : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      Represents (ptQ P V hV) (killIdeal (ptQ P V hV)) := by
    intro V hV
    obtain ⟨s, hs, hJ⟩ := GlobalTheory.T.exists_basicOpen_cover_idealRepresents S P hCov V hV
    have hQbc : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'')
        (f : Γ(S, V) →+* R'), ptQ P V hV R' f → ptQ P V hV R'' (g.comp f) := by
      intro R' _ R'' _ g f hf
      have := hBC R' R'' g _ hf
      simpa [ptQ, spMap, CommRingCat.ofHom_comp, Spec.map_comp] using this
    have hQloc : ∀ (R' : Type) [CommRing R'] (f : Γ(S, V) →+* R') (t : Finset R'),
        Ideal.span (t : Set R') = ⊤ →
        (∀ r ∈ t, ptQ P V hV (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) →
        ptQ P V hV R' f := by
      intro R' _ f t ht H
      refine hLoc R' _ t ht fun r hr ↦ ?_
      have := H r hr
      simpa [ptQ, spMap, CommRingCat.ofHom_comp, Spec.map_comp] using this
    obtain ⟨J, hJ'⟩ := GlobalTheory.T.idealRepresents_of_away_cover Γ(S, V) (ptQ P V hV) hQbc hQloc s hs hJ
    exact represents_killIdeal hJ'
  let I : S.IdealSheafData :=
    { ideal := fun V ↦ killIdeal (ptQ P V.1 V.2)
      map_ideal_basicOpen := fun U f ↦ by
        have h1 := represents_restrict S P U.1 (S.basicOpen f) U.2 (U.2.basicOpen f) (S.basicOpen_le f) _
          (hrep U.1 U.2)
        exact (killIdeal_eq h1).symm }
  refine ⟨I.subscheme, I.subschemeι, inferInstance, fun R' _ x ↦ ?_⟩
  have key : I ≤ x.ker ↔ P R' x := by
    rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
    constructor
    · intro h
      exact GlobalTheory.T.affinePointProperty_of_le_ker_app S P hLoc hrep R' x fun V hV ↦ h ⟨V, hV⟩
    · intro h V
      exact GlobalTheory.T.idealKilledByRingMapsWithProperty_le_ker_app S P hBC R' x h V.1 V.2
  rw [← key]
  constructor
  · rintro ⟨y, rfl⟩
    have := y.le_ker_comp I.subschemeι
    rwa [Scheme.IdealSheafData.ker_subschemeι] at this
  · intro h
    exact ⟨IsClosedImmersion.lift I.subschemeι x (by rwa [Scheme.IdealSheafData.ker_subschemeι]),
      IsClosedImmersion.lift_fac _ _ _⟩
end GlobalTheory.PtClosed
end
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

namespace GlobalTheory.Nef

theorem ordVec_symMat_mulVec_triangular : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (P : Place k E) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) E), A 1 0 = 0 → A.det ≠ 0 → ∀ (q : Fin (m + 1) → E) (c : E) (s t : Fin m → E),
    c ≠ 0 → (∀ j, ![s j, t j] ≠ 0) →
    ∑ i : Fin (m + 1), C (q i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i) =
      C c * ∏ j, (C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X)) →
    ordVec P ((symMat m A).mulVec q) = ord P c + ∑ j, ordVec P (A.mulVec ![s j, t j]) := by
  intro k E _ _ _ P m A hA10 hdet q c s t hc hst hq
  classical
  let α : Fin m → E := fun j => s j * A 0 0 + t j * A 0 1
  let β : Fin m → E := fun j => t j * A 1 1
  have hfac : ∀ j, C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X) = C (α j) + C (β j) * X := by
    intro j
    simp only [α, β, C_add, C_mul]
    ring
  have hvec : (symMat m A).mulVec q = fun a : Fin (m + 1) => c * (∏ j, (C (α j) + C (β j) * X)).coeff a := by
    rw [symMat_mulVec, hq]
    funext a
    simp only [hfac, coeff_C_mul]
  have hsup : ∀ (n : ℕ) (x : Fin n → E), nrm P (fun a => c * x a) = P.1 c * nrm P x := by
    intro n x
    have h := Finset.comp_sup_eq_sup_comp (s := Finset.univ) (f := fun a => P.1 (x a)) (fun y => P.1 c * y)
      (fun a b => by
        rcases le_total a b with h | h
        · rw [sup_eq_right.2 h, sup_eq_right.2 (mul_le_mul' le_rfl h)]
        · rw [sup_eq_left.2 h, sup_eq_left.2 (mul_le_mul' le_rfl h)]) (by simp)
    simp only [nrm, map_mul]
    exact h.symm
  have hfin2 : ∀ f : Fin 2 → WithZero (Multiplicative ℤ), Finset.univ.sup f = max (f 0) (f 1) := by
    intro f
    refine le_antisymm (Finset.sup_le fun i _ => ?_) (max_le (Finset.le_sup (Finset.mem_univ 0))
      (Finset.le_sup (Finset.mem_univ 1)))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hw : ∀ j, nrm P (A.mulVec ![s j, t j]) = max (P.1 (α j)) (P.1 (β j)) := by
    intro j
    rw [nrm, hfin2]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hA10, zero_mul, zero_add, α, β]
    rw [mul_comm (A 0 0), mul_comm (A 0 1), mul_comm (A 1 1)]
  have hnz : ∀ j, nrm P (A.mulVec ![s j, t j]) ≠ 0 := by
    intro j h0
    have hne : A.mulVec ![s j, t j] ≠ 0 := fun h => hst j (Matrix.eq_zero_of_mulVec_eq_zero hdet h)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have h1 : P.1 (A.mulVec ![s j, t j] i) ≤ nrm P (A.mulVec ![s j, t j]) :=
      Finset.le_sup (f := fun i => P.1 (A.mulVec ![s j, t j] i)) (Finset.mem_univ i)
    rw [h0] at h1
    exact (Valuation.ne_zero_iff _).2 hi (le_antisymm h1 zero_le')
  have hPc : P.1 c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hlogprod : ∀ S : Finset (Fin m), WithZero.log (∏ j ∈ S, nrm P (A.mulVec ![s j, t j])) =
      ∑ j ∈ S, WithZero.log (nrm P (A.mulVec ![s j, t j])) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        WithZero.log_mul (hnz a) (Finset.prod_ne_zero_iff.2 fun j _ => hnz j), ih]
  have hmain : nrm P ((symMat m A).mulVec q) = P.1 c * ∏ j, nrm P (A.mulVec ![s j, t j]) := by
    rw [hvec, hsup, GlobalTheory.T.nrm_coeff_prod_linear' k E P m α β]
    simp only [hw]
  rw [ordVec, hmain, WithZero.log_mul hPc (Finset.prod_ne_zero_iff.2 fun j _ => hnz j), hlogprod, ord]
  simp only [ordVec, Finset.sum_neg_distrib]
  ring

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.compatible_higherForms_extend_along_functor : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), ∀ (j : ℕ), (∀ (T : C) (x : (FormExtJ.omjExt F j).obj T), (∀ t (u : T ⟶ G.obj t), mp (FormExtJ.omjExt F j) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (FormExtJ.omjExt F j).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (FormExtJ.omjExt F j) (G.map a) (s t u)) → ∃ x : (FormExtJ.omjExt F j).obj T, ∀ t u, mp (FormExtJ.omjExt F j) u x = s t u) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) j, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F j (G.map a) (η' t)) → ∃ η : W0 F j, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F j φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) := by
  first | exact @GlobalTheory.compat_forms_extend | exact GlobalTheory.compat_forms_extend | (intros; apply GlobalTheory.compat_forms_extend <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.higherForms_oneCocycle_coboundary_of_restrict : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), ∀ (j : ℕ), Function.Injective (CoefMap.restrict (FormExtJ.omjExt F j) G).pull1 → (∀ κ : W1 F j, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = pOm F j ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Om R (F.obj (G.obj t)) j, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F j (G.map a) (θ' t)) → ∃ θ : W0 F j, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F j φ (θ T)) := by
  first | exact @GlobalTheory.CechDR.FormExtJ.oneCocycle_coboundary_of_restrict_coboundary | exact GlobalTheory.CechDR.FormExtJ.oneCocycle_coboundary_of_restrict_coboundary | (intros; apply GlobalTheory.CechDR.FormExtJ.oneCocycle_coboundary_of_restrict_coboundary <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isLimit_finiteSubextensionSpecArrowCone : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω], IsColimit (GlobalTheory.SepCech.ringCocone K Ω) → Nonempty (IsLimit (Arrow.leftFunc.mapCone (GlobalTheory.SepCech.arrCone K Ω))) := by
  first | exact @GlobalTheory.SepCech.isLimit_leftFunc_arrCone | exact GlobalTheory.SepCech.isLimit_leftFunc_arrCone | (intros; apply GlobalTheory.SepCech.isLimit_leftFunc_arrCone <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.injective_etaleSheaf_retract_of_coinduced : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I], ∃ (J : Shv R) (_ : Injective J) (i : I ⟶ (coind φ).obj J) (r : (coind φ).obj J ⟶ I), i ≫ r = 𝟙 I := by
  first | exact @GlobalTheory.EtC.CoindRetract.coind_retract | exact GlobalTheory.EtC.CoindRetract.coind_retract | (intros; apply GlobalTheory.EtC.CoindRetract.coind_retract <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.discrete_glBundle_eq_trivialGLBundle : ∀ (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), V = trivV N (disc.obj F) := by
  first | (exact @GlobalTheory.EtC.disc_eq_trivV) | (exact GlobalTheory.EtC.disc_eq_trivV) | (intros; apply GlobalTheory.EtC.disc_eq_trivV  <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divisorsOfConstantsAllPrimes_of_closedFibre : GlobalTheory.VertUnits.DivConstLocal → GlobalTheory.VertUnits.DivConstAll := by
  first | exact @GlobalTheory.VertUnits.divConstAll_of_divConstLocal | exact GlobalTheory.VertUnits.divConstAll_of_divConstLocal | (intros; apply GlobalTheory.VertUnits.divConstAll_of_divConstLocal <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin : GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  first | (exact @GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (exact GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin  <;> assumption)
end
