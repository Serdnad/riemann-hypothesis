module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushHomBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.Labels

theorem eq_comp_of_genMap {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D' : DegData R (maximalIdeal R)}
    {A A' : PolAV (Sp (FractionRing R))} {G G' : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G)
    (π : A'.A ⟶ A.A) (h : (Over.pullback (jK R)).map p ≫ U.gen.hom = U'.gen.hom ≫ π) {T : Over (Sp (FractionRing R))}
    (a : T ⟶ A.A) (a' : T ⟶ A'.A) (e : a.left ≫ genMap U = a'.left ≫ genMap U' ≫ p.left) : a = a' ≫ π := by
  have hU := GlobalTheory.TauFormHom.isGrpPullback_genMap U
  have h' : U'.gen.inv ≫ (Over.pullback (jK R)).map p = π ≫ U.gen.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h'' : π.left ≫ U.gen.inv.left = U'.gen.inv.left ≫ ((Over.pullback (jK R)).map p).left := by
    rw [← Over.comp_left, ← Over.comp_left, h']
  have hf : ((Over.pullback (jK R)).map p).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ p.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  apply Over.OverMorphism.ext
  refine hU.1.hom_ext ?_ ?_
  · rw [e, Over.comp_left, genMap, genMap]
    simp only [Category.assoc]
    rw [reassoc_of% h'', hf]
  · rw [Over.w a, Over.w (a' ≫ π)]

theorem commutatorPairing_eighthPower_bundle : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P P' : PolAV S) (pr : Fin 8 → (P'.A ⟶ P.A)), (∀ a, IsMonHom (pr a)) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), LBIso P'.L (LB.LinComb (abelian₂ P.A P.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (n : ℕ) (T : Over S) (x y : T ⟶ P'.A), x ^ n = 1 → y ^ n = 1 → ∀ (c : Fin 8 → Fin 8 → Γ(T.left, ⊤)ˣ), (∀ a b, WeilIs P.A P.L n (x ≫ pr a) (y ≫ pr b) (c a b)) → WeilIs P'.A P'.L n x y (∏ ab : Fin 8 × Fin 8, (c ab.1 ab.2 * c ab.2 ab.1) ^ W ab.1 ab.2) := by
  intro S _ P P' pr hpr W hL n T x y hx hy c hc
  have hG := GlobalTheory.globalFns_holds
  have hΛ : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have hM := LB.isLB_linComb hΛ (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have hφ : ∀ ab : Fin 8 × Fin 8, IsMonHom (lift (pr ab.1) (pr ab.2)) := fun ab => by
    haveI := hpr ab.1
    haveI := hpr ab.2
    infer_instance
  have ht : ∀ {z : T ⟶ P'.A}, z ^ n = 1 → ∀ a, (z ≫ pr a) ^ n = 1 := fun {z} hz a => by
    haveI := hpr a
    rw [← MonObj.pow_comp, hz, MonObj.one_comp]
  have key := GlobalTheory.PairingComb.weilIs_linComb hG P'.isAb hΛ (fun ab : Fin 8 × Fin 8 => lift (pr ab.1) (pr ab.2)) hφ
    (fun ab => W ab.1 ab.2) (n := n) (x := x) (y := y) (fun ab => c ab.1 ab.2 * c ab.2 ab.1) (fun ab => by
      rw [comp_lift, comp_lift]
      exact GlobalTheory.T.weilPairing_mumfordLambda_square S P n T _ _ _ _ (ht hx _) (ht hx _) (ht hy _) (ht hy _) _ _ (hc ab.1 ab.2) (hc ab.2 ab.1))
  refine GlobalTheory.PELFamily.weilIs_of_lbIso hG P'.isAb P'.isLB hM ?_ key
  refine LBIso.trans P'.isLB hM (LB.isLB_pull hM _) hL ?_
  have := GlobalTheory.DescendedPrincipal.lbIso_pull_id hM
  simpa using this.symm

theorem sum_symmetrised_bilinear_matrix_eq {J X Y : Type} [Fintype J] [AddCommGroup X] [AddCommGroup Y] (W : Matrix J J ℤ) (c : J → (X →+ Y))
    (l : J → X) :
    ∑ ab : J × J, W ab.1 ab.2 • (c ab.1 (l ab.2) + c ab.2 (l ab.1)) =
      ∑ u, c u (∑ w, (W + W.transpose) u w • l w) := by
  rw [Fintype.sum_prod_type]

  simp only [smul_add, Finset.sum_add_distrib, map_add (f := _), map_sum, map_zsmul, Matrix.add_apply, Matrix.transpose_apply,
  add_smul]
  congr 1
  exact Finset.sum_comm

theorem label_proj_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ v : Fin 8, (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), IsUnit (k : R) → ∀ (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := R) F ⟶ A'.A), QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a.left ≫ genMap U = a'.left ≫ genMap U' ≫ (pG v).left → ∃ z, q.y = e q'.y v + k • z) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e he v F _ _ _ k hk
    q q' a a' hqa hqa' hla
  haveI := hdvr
  obtain ⟨hR, hR0⟩ := id hRb
  obtain ⟨-, -, -, hRc⟩ := id hR
  haveI := hRc
  haveI := hR0
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hkF : (k : F) ≠ 0 := by
    have h := hk.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))
    rw [map_natCast] at h
    exact h.ne_zero
  obtain ⟨f, ⟨i₁, s₁, q₁, -, w₁⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
  obtain ⟨f', ⟨i₂, -, -, -, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D' A' G' hG' U' F k hk1
  obtain rfl : a = f q := (i₁ q a).1 hqa
  obtain rfl : a' = f' q' := (i₂ q' a').1 hqa'
  have hav : f q = f' q' ≫ pr v := eq_comp_of_genMap U U' (pG v) (pr v) (hgen v) _ _ hla
  have hpw : ∀ w, (f' q' ≫ pr w) ^ k = 1 := fun w => by
    haveI := hpr w
    rw [← MonObj.pow_comp, p₂, MonObj.one_comp]
  choose qw hqw using fun w => s₁ _ (hpw w)
  have key : ∀ τ : Multiplicative D.toPre.X →* Fˣ, τ ^ k = 1 →
      τ (Multiplicative.ofAdd (q.y - e q'.y v)) = 1 := by
    intro τ hτ
    have hτk : ∀ x, τ x ^ k = 1 := fun x => by
      rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    let ev : D'.toPre.X →+ D.toPre.X := (Pi.evalAddMonoidHom (fun _ : Fin 8 => D.toPre.X) v).comp e.toAddMonoidHom
    let τ' : Multiplicative D'.toPre.X →* Fˣ := τ.comp (AddMonoidHom.toMultiplicative ev)
    have hτ' : τ' ^ k = 1 := MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact hτk _
    let τu : Fin 8 → (Multiplicative D.toPre.X →* Fˣ) := fun u => τ'.comp (AddMonoidHom.toMultiplicative (c u))
    have hτu : ∀ u, τu u ^ k = 1 := fun u => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact hτk _
    obtain ⟨tT', htT'y, htT'⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) hB' τ' hτ'
    choose tT htTy htT using fun u => GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) hB (τu u) (hτu u)
    have hproj : ∀ u, f (tT u) = f' tT' ≫ pr u := fun u =>
      eq_comp_of_genMap U U' (pG u) (pr u) (hgen u) _ _
        (hc u F (fun _ => rfl) k hk (τu u) τ' (tT u) tT' (f (tT u)) (f' tT') hτ' (fun _ => rfl) (htTy u) (htT u)
          htT'y htT' ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl))
    have hA : ∀ u w, WeilIs A.A A.L k (f' tT' ≫ pr u) (f' q' ≫ pr w)
        (unitOn (τ' (Multiplicative.ofAdd (c u (qw w).y)))) := fun u w => by
      rw [← hproj u, ← hqw w]
      exact (w₁ _ _ _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns (tT u) (qw w) (htTy u) (htT u))
    have hA' : WeilIs A'.A A'.L k (f' tT') (f' q') (unitOn (τ' (Multiplicative.ofAdd q'.y))) :=
      (w₂ _ _ _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns tT' q' htT'y htT')
    have hA₂ := commutatorPairing_eighthPower_bundle _ A A' pr hpr W hL k _ (f' tT') (f' q') (p₂ _) (p₂ _) _ hA
    have hval : (∏ ab : Fin 8 × Fin 8, (unitOn (τ' (Multiplicative.ofAdd (c ab.1 (qw ab.2).y))) *
        unitOn (τ' (Multiplicative.ofAdd (c ab.2 (qw ab.1).y)))) ^ W ab.1 ab.2) =
        unitOn (τ' (Multiplicative.ofAdd (∑ u, c u (∑ w, (W + W.transpose) u w • (qw w).y)))) := by
      let ψ : Multiplicative D'.toPre.X →* Γ(Sp F, ⊤)ˣ :=
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom).comp τ'
      have hψ : ∀ x, unitOn (τ' x) = ψ x := fun x => rfl
      simp only [hψ]
      rw [← sum_symmetrised_bilinear_matrix_eq W c (fun w => (qw w).y), ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun ab _ => ?_
      rw [ofAdd_zsmul, map_zpow, ofAdd_add, map_mul]
    rw [hval] at hA₂
    have hu := GlobalTheory.weilIs_unique_fieldPoint _ A'.A A'.L A'.isLB F _ k _ _ _ _ hA' hA₂
    have hinv : e (∑ u, c u (∑ w, (W + W.transpose) u w • (qw w).y)) = fun w => (qw w).y := by
      have := he (e.symm fun w => (qw w).y)
      rw [e.apply_symm_apply] at this
      rw [this, e.apply_symm_apply]
    have h₁ : τ (Multiplicative.ofAdd (e q'.y v)) = τ (Multiplicative.ofAdd (qw v).y) := by
      have := hu
      simp only [τ', ev, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
        AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, AddEquiv.coe_toAddMonoidHom, hinv] at this
      exact this
    obtain ⟨z, hz, -⟩ := (q₁ (qw v) q).1 (by rw [hqw, hav])
    rw [ofAdd_sub, map_div, h₁, hz, ofAdd_add, map_mul, ofAdd_nsmul, map_pow, hτk, _root_.mul_one, div_self']
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_eq_nsmul_of_forall_char_pow_eq_one _ F k hkF _ key
  exact ⟨z, by rw [← hz]; abel⟩

end GlobalTheory.Poinc.Eq8.Labels
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusOntoSpread

theorem restrict_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → ∀ ρ, Spread U U' g β ρ → Function.Surjective ρ := by
  intro R _ _ _ _ G _ _ hG D A U V _ _ _ _ G' _ _ _ D' A' U' g β _ ρ hsp
  obtain ⟨V₁, _, _, _, ψ, G₁, _, _, m₁, Ω, _, α, b, hb, GΩ, _, n, hn, n', hn', j, G₀, _, m₀, hm₀, h₀, hm₀',
    hψl, hm₁, hj, _, _, _, hΩ, h₀j⟩ := hsp
  haveI := hψl; haveI := hj
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ G G₁ m₁ hm₁ hG
  classical
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := GlobalTheory.TorusOnto.exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  have key : GlobalTheory.SplitTorus.torusMap (Sp V₁) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp V₁) 0 ≫ j := by
    haveI : IsSeparated G₁.hom := hG₁.separated
    have hjac : maximalIdeal V₁ ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    refine GlobalTheory.hom_eq_of_thickenings_of_isProper V₁ (maximalIdeal V₁) hjac (splitTorus (Sp V₁) F) G₁ _ _ fun e => ?_
    have hψ : ∀ x ∈ maximalIdeal R, ψ x ∈ maximalIdeal V₁ := fun x hx =>
      (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit ψ x hu)
    have hI : maximalIdeal V₁ ^ (e + 1) ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal V₁).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
    haveI : Nontrivial (V₁ ⧸ maximalIdeal V₁ ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (V₁ ⧸ maximalIdeal V₁ ^ (e + 1)) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let q : V₁ →+* V₁ ⧸ maximalIdeal V₁ ^ (e + 1) := Ideal.Quotient.mk _
    have he := isGrpPullback_pullback G₁ (thick V₁ (maximalIdeal V₁) e)
    have ha : ∀ x ∈ maximalIdeal R ^ (e + 1), (q.comp ψ) x = 0 := by
      intro x hx
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      have hle : Ideal.map ψ (maximalIdeal R ^ (e + 1)) ≤ maximalIdeal V₁ ^ (e + 1) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hψ) _
      exact hle (Ideal.mem_map_of_mem ψ hx)
    have hR : IsGrpPullback (thickObj V₁ (maximalIdeal V₁) e G₁) G (spMap (q.comp ψ))
        (pullback.fst G₁.hom (thick V₁ (maximalIdeal V₁) e) ≫ m₁) :=
      (he.comp hm₁).congr (by rw [spMap, spMap, ← Spec.map_comp]; rfl) rfl
    obtain ⟨-, hfac⟩ := GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt e) ha hR
    obtain ⟨ρe, hρe⟩ := hfac D'.toPre.X (GlobalTheory.TorusPart.pullTorus he j) inferInstance
    have hres : ∀ x ∈ maximalIdeal V₁ ^ (e + 1), residue V₁ x = 0 := fun x hx =>
      (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have ke := GlobalTheory.TorusPart.isGrpPullback_thickLift hres hm₀
    have ha' : ∀ x ∈ maximalIdeal R ^ (e + 1), ((residue V₁).comp ψ) x = 0 := fun x hx =>
      h₀ x (by rw [zero_add, pow_one]; exact Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have e1 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.pullTorus he j) = GlobalTheory.TorusPart.pullTorus hm₀ j :=
      GlobalTheory.TorusPart.pullTorus_pullTorus ke he hm₀ (GlobalTheory.TorusPart.thickPt_thick hres).symm
        (GlobalTheory.TorusPart.thickLift_fst hres hm₀).symm j
    have e2 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.gtTorus (U.gt e) ha hR) =
        GlobalTheory.TorusPart.gtTorus (U.gt e) ha' hm₀' :=
      GlobalTheory.TorusPart.pullTorus_gtTorus (σ := Ideal.Quotient.lift _ (residue V₁) hres) (U.gt e) ha ha' hR hm₀' ke
        (RingHom.ext fun x => rfl)
        (by rw [← Category.assoc, GlobalTheory.TorusPart.thickLift_fst])
    obtain ⟨hmono, hfac'⟩ := GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt e) ha' hm₀'
    obtain ⟨u, hu⟩ := hfac' D.toPre.X (GlobalTheory.TorusPart.gtTorus (U.gt 0) h₀ hm₀') inferInstance
    have e3 := congrArg (GlobalTheory.TorusPart.pullTorus ke) hρe
    rw [e1, GlobalTheory.TorusPart.pullTorus_torusMap_comp, e2, h₀j, hu, ← Category.assoc,
      ← GlobalTheory.SplitTorus.torusMap_comp, cancel_mono] at e3
    have e4 : ρe = ρ.comp u := (GlobalTheory.SplitTorus.torusMap_injective e3).symm
    have hstep : GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ l ≫ j) =
        GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ (0 : D'.toPre.X →+ F) ≫ j) := by
      rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hρe, ← Category.assoc,
        ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, e4,
        ← AddMonoidHom.comp_assoc, hlρ, AddMonoidHom.zero_comp, AddMonoidHom.zero_comp]
    have k1 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ l ≫ j)
    have k2 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ (0 : D'.toPre.X →+ F) ≫ j)
    rw [hstep] at k1
    have k3 := k1.symm.trans k2
    show pullback.fst (splitTorus (Sp V₁) F).hom (thick V₁ (maximalIdeal V₁) e) ≫ _ =
      pullback.fst (splitTorus (Sp V₁) F).hom (thick V₁ (maximalIdeal V₁) e) ≫ _
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k3]
  haveI : Mono (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hn') :=
    (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U'.gt 0) hb hn').1
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus hn) key
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩ] at e2
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.TorusOntoSpread
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.TorsExtend

theorem exists_section_of_isFinite {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ Sp R) [IsFinite p] (y : Sp K ⟶ Z)
    (h : y ≫ p = spMap (algebraMap R K)) : ∃ x : Sp R ⟶ Z, spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 _ := by
  first
  | exact @_root_.GlobalTheory.FactorAndSection.exists_section
  | exact _root_.GlobalTheory.FactorAndSection.exists_section
  | (apply _root_.GlobalTheory.FactorAndSection.exists_section <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorAndSection.exists_section <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorAndSection.exists_section <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorAndSection.exists_section ..)

theorem pow_eq_one_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} (z : T ⟶ G) :
    z ^ n = 1 ↔ z.left ≫ (mulA G n).left = T.hom ≫ (η[G]).left := by
  have e : (1 : T ⟶ G).left = T.hom ≫ (η[G]).left := by
    rw [Hom.one_def]; simp
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, ← e]
  exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩

theorem exists_torsion_section (hL : Laws) {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) {n : ℕ} (hn : 1 ≤ n)
    {s : Sp K ⟶ Sp R} (hs : s = spMap (algebraMap R K)) (y : Over.mk s ⟶ P.A) (hy : y ^ n = 1) :
    ∃ x : baseOver (Sp R) ⟶ P.A, x ^ n = 1 ∧ spMap (algebraMap R K) ≫ x.left = y.left := by
  subst hs
  haveI := (hL.mulN _ P n hn).1
  let e : Sp R ⟶ P.A.left := (η[P.A]).left
  have he : e ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  obtain ⟨x, h₁, h₂⟩ := exists_section_of_isFinite (pullback.snd (mulA P.A n).left e)
    (pullback.lift y.left (spMap (algebraMap R K)) ((pow_eq_one_iff _ _ _).1 hy)) (pullback.lift_snd _ _ _)
  have h₃ : (x ≫ pullback.fst (mulA P.A n).left e) ≫ (mulA P.A n).left = e := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.id_comp]
  refine ⟨Over.homMk (x ≫ pullback.fst _ _) ?_, (pow_eq_one_iff _ _ _).2 (h₃.trans (Category.id_comp _).symm), ?_⟩
  · rw [← Over.w (mulA P.A n), ← Category.assoc, h₃]
    exact he
  · show _ ≫ x ≫ pullback.fst _ _ = _
    rw [← Category.assoc, h₁, pullback.lift_fst]

theorem torsion_section_eq (hL : Laws) {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K]
    (P : PolAV (Sp R)) {n : ℕ} (hn : 1 ≤ n) (hu : IsUnit (n : R)) {x y : baseOver (Sp R) ⟶ P.A} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (s : Sp K ⟶ Sp R) (h : s ≫ x.left = s ≫ y.left) : x = y := by
  haveI := (hL.mulN _ P n hn).1
  haveI := (hL.mulN _ P n hn).2.2.2.1 (by simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  haveI : PreconnectedSpace (Sp R) := inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
  exact Over.OverMorphism.ext (eq_of_preconnected_of_unramified (T := Sp R) (mulA P.A n).left
    (((pow_eq_one_iff _ _ _).1 hx).trans ((pow_eq_one_iff _ _ _).1 hy).symm) s h)

theorem exists_labelled (hL : Laws) {R R₀ Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field Ω] [Algebra R Ω] [IsFractionRing R Ω] [CommRing R₀] (j₀ : R₀ →+* Ω)
    (P : PolAV (Sp R₀)) (P' : PolAV (Sp R)) (P₀ : PolAV (Sp Ω)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left)
    (ha : IsGrpPullback P₀.A P.A (spMap j₀) a) (ha' : IsGrpPullback P₀.A P'.A (spMap (algebraMap R Ω)) a')
    (hl : LBIso P₀.L (P.L.pull a)) (hl' : LBIso P₀.L (P'.L.pull a')) {n : ℕ} (hn : 1 ≤ n) (hu : IsUnit (n : R))
    {M : Type} [AddCommGroup M] (hM : ∀ x : M, n • x = 0) (pt : M → (baseOver (Sp R₀) ⟶ P.A))
    (add : ∀ x y, pt (x + y) = pt x * pt y)
    (bij : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R₀) (z : Over.mk x ⟶ P.A), z ^ n = 1 →
      ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₀)) ≫ pt c = z) :
    ∃ pt' : M → (baseOver (Sp R) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P'.A), z ^ n = 1 →
        ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt' c = z) ∧
      (∀ x y (c₀ : R₀ˣ) (c : Rˣ), j₀ c₀ = algebraMap R Ω c → WeilIs P.A P.L n (pt x) (pt y) (unitOn c₀) →
        WeilIs P'.A P'.L n (pt' x) (pt' y) (unitOn c)) ∧
      ∀ x, ∃ w0 : Sp Ω ⟶ P₀.A.left, w0 ≫ a = spMap j₀ ≫ (pt x).left ∧
        w0 ≫ a' = spMap (algebraMap R Ω) ≫ (pt' x).left := by
  haveI := P₀.isAb.comm
  haveI := P'.isAb.proper
  have hi := IsFractionRing.injective R Ω
  have hb := GenericKTriv.pushHom_bijective ha (baseOver (Sp Ω))
  have hb' := GenericKTriv.pushHom_bijective ha' (baseOver (Sp Ω))
  let h₀ : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap j₀) ⟶ baseOver (Sp R₀) := Over.homMk (spMap j₀) (by simp)
  let h : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap (algebraMap R Ω)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R Ω)) (by simp)
  have zero : pt 0 = 1 := by
    have := add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have smul : ∀ (k : ℕ) x, pt (k • x) = pt x ^ k := fun k x => by
    induction k with
    | zero => rw [zero_smul, zero, pow_zero]
    | succ k ih => rw [succ_nsmul, add, ih, pow_succ]
  have tor : ∀ x, pt x ^ n = 1 := fun x => by rw [← smul, hM, zero]
  choose w hw using fun x => hb.2 (h₀ ≫ pt x)
  have torw : ∀ x, w x ^ n = 1 := fun x => hb.1 (by
    rw [map_pow, hw, map_one, ← MonObj.comp_pow, tor, MonObj.comp_one])
  have addw : ∀ x y, w (x + y) = w x * w y := fun x y => hb.1 (by
    rw [map_mul, hw, hw, hw, add, MonObj.comp_mul])
  choose pt' tor' hpt' using fun x => exists_torsion_section hL P' hn (Category.id_comp _)
    (pushHom ha' (baseOver (Sp Ω)) (w x)) (by rw [← map_pow, torw, map_one])
  have hpt : ∀ x, h ≫ pt' x = pushHom ha' (baseOver (Sp Ω)) (w x) := fun x => Over.OverMorphism.ext (hpt' x)
  have e₀ : ∀ x, (w x).left ≫ a = spMap j₀ ≫ (pt x).left := fun x => congrArg (fun q => q.left) (hw x)
  have e₁ : ∀ x, (w x).left ≫ a' = spMap (algebraMap R Ω) ≫ (pt' x).left := fun x => (hpt' x).symm
  let F := AlgebraicClosure Ω
  let t : Sp F ⟶ Sp Ω := spMap (algebraMap Ω F)
  let g : Over.mk (t ≫ spMap j₀) ⟶ baseOver (Sp R₀) := Over.homMk (t ≫ spMap j₀) (by simp)
  have torg : ∀ x, (g ≫ pt x) ^ n = 1 := fun x => by rw [← MonObj.comp_pow, tor, MonObj.comp_one]
  have inj : Function.Injective pt' := fun x y e => by
    have e₂ : w x = w y := hb'.1 (by rw [← hpt, ← hpt, e])
    refine (bij F (t ≫ spMap j₀) (g ≫ pt y) (torg y)).unique (Over.OverMorphism.ext ?_) rfl
    show (t ≫ spMap j₀) ≫ (pt x).left = (t ≫ spMap j₀) ≫ (pt y).left
    rw [Category.assoc, Category.assoc, ← e₀, ← e₀, e₂]
  have ne : ∀ (K : Type) [Field K] (s : Sp K ⟶ Sp R), (n : K) ≠ 0 := fun K _ s => by
    have := hu.map (Spec.preimage s).hom
    rw [map_natCast] at this
    exact this.ne_zero
  have card : Nat.card M = n ^ (2 * P'.g) := by
    rw [← (hL.mulN _ P' n hn).2.2.2.2 F (t ≫ spMap (algebraMap R Ω)) (ne F (t ≫ spMap (algebraMap R Ω))),
      GenericKTriv.card_torsion ha' t rfl, ← GenericKTriv.card_torsion ha t rfl]
    refine Nat.card_eq_of_bijective (fun x => ⟨g ≫ pt x, torg x⟩) ⟨fun x y e => ?_, fun z => ?_⟩
    · exact (bij F (t ≫ spMap j₀) (g ≫ pt y) (torg y)).unique (congrArg Subtype.val e) rfl
    · obtain ⟨c, hc, -⟩ := bij F (t ≫ spMap j₀) z.1 z.2
      exact ⟨c, Subtype.ext hc⟩
  refine ⟨pt', fun x y => ?_, fun K _ _ s z hz => ?_, fun x y c₀ c hc H => ?_, fun x => ⟨(w x).left, e₀ x, e₁ x⟩⟩
  · have e : h ≫ pt' (x + y) = h ≫ (pt' x * pt' y) := by
      rw [MonObj.comp_mul, hpt, hpt, hpt, addw, map_mul]
    exact over_points_ext_of_injective _ P'.A R Ω _ hi _ _ _ (congrArg (fun q => q.left) e)
  · have hc := (hL.mulN _ P' n hn).2.2.2.2 K s (ne K s)
    let Φ : M → {x : Over.mk s ⟶ P'.A // x ^ n = 1} := fun c =>
      ⟨(Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ pt' c, by
        rw [← MonObj.comp_pow, tor', MonObj.comp_one]⟩
    have hΦ : Function.Injective Φ := fun c c' e =>
      inj (torsion_section_eq hL P' hn hu (tor' c) (tor' c') s (congrArg (fun q => q.1.left) e))
    have : Finite {x : Over.mk s ⟶ P'.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    obtain ⟨c, e⟩ := (hΦ.bijective_of_nat_card_le (by rw [hc, card])).2 ⟨z, hz⟩
    exact ⟨c, congrArg Subtype.val e, fun c' e' => hΦ ((Subtype.ext e').trans e.symm)⟩
  · refine MumPair.weilIs_of_spread Ω R _ hi P₀ P' a' ha' hl' n (w x) (w y) _ _ c hn (e₁ x) (e₁ y) (tor' x) (tor' y) ?_
    have H₁ := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h₀ H
    have H₂ := (weilIs_grpPullback_of_comm' (Sp R₀) (Sp Ω) P.A P₀.A (spMap j₀) a P.L P₀.L P.isLB P₀.isLB ha hl
      (baseOver (Sp Ω)) n (w x) (w y) (h₀ ≫ pt x) (h₀ ≫ pt y) _ (e₀ x).symm (e₀ y).symm).2 H₁
    have e := SpreadLevel.appTop_unitOn j₀ c₀ (Units.map (algebraMap R Ω).toMonoidHom c) hc
    exact e ▸ H₂

theorem isIntegrallyClosed_ringOn {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) :
    IsIntegrallyClosed (M.ringOn U) := by
  haveI := RatModel.isFractionRing_ringOn hU hne
  refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ⟨⟨x, RatModel.mem_ringOn.2 fun z hz => ?_⟩, rfl⟩
  have := RatModel.isIntegrallyClosed_O hM z
  letI : Algebra (M.ringOn U) (M.O z) := (Subalgebra.inclusion (RatModel.ringOn_le_O hz)).toRingHom.toAlgebra
  haveI : IsScalarTower (M.ringOn U) (M.O z) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := M.O z))
  exact hy ▸ y.2

theorem exists_labelled_on_chart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (P' : PolAV (Sp (X₁.M.ringOn U))) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → ∃ pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) ∧ (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) ∧ (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) := by
  intro g n F W Z i X₁ U P' P₀ a a' hU hne ha ha' hl hl'
  have hL : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  haveI := RatModel.isFractionRing_ringOn hU hne
  haveI := isIntegrallyClosed_ringOn X₁.M ((isNormalScheme_iff_pred _).1 X₁.normal) hU hne
  haveI := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  haveI : IsNoetherianRing (X₁.M.ringOn U) := isNoetherianRing_of_fg (fg_ringOn_of_isAffineOpen _ _ X₁.M U hU hne)
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (le_trans one_le_two X₁.S.N_ge)
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : X₁.M.ringOn U) := by
    have := X₁.S.unit.map (algebraMap X₁.o₁ (X₁.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', h₁, h₂, h₃, h₄⟩ := exists_labelled hL X₁.S.R.val.toRingHom X₁.ρ.P P' P₀ a a' ha ha' hl hl' hn hu
    (M := X₁.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.pt_bij
  refine ⟨pt', h₁, h₂, fun x y c hc => ?_, h₄⟩
  obtain ⟨c₀, hc₀⟩ := ((X₁.S.prim.isUnit (by positivity)).pow (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)).map
    (algebraMap X₁.o₁ X₁.S.R)
  refine h₃ x y c₀ c ?_ (X₁.ρ.weil x y c₀ hc₀)
  rw [hc₀, hc]
  rfl

end GlobalTheory.Poinc.TorsExtend
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.hasApproxPoincareSeries_nat_multiple : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ), 1 ≤ m → ApproxAt X₁ φ d → ApproxAt X₁ φ (d * m) := by
  first | exact @GlobalTheory.Poinc.approxAt_mul | exact GlobalTheory.Poinc.approxAt_mul | (intros; apply GlobalTheory.Poinc.approxAt_mul <;> assumption)
end
