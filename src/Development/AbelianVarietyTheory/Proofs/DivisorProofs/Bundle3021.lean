module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle062
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2994
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TransEven
open GlobalTheory.UU



theorem evenOn_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
      EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U a ha P hP hsym hcub
  have hG := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨wA, hwA⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre hG hS wA hwA
  set g := U.gt 0 with hg
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  have := hB.comm
  obtain ⟨O, h₁, h₂, h₃, hd⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ D.toPre.X (thickObj R (maximalIdeal R) 0 G)
    (thickObj R (maximalIdeal R) 0 D.toPre.P.A) hB g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj inferInstance g.isKernel
  obtain ⟨d, hdq, hdi⟩ := hd hB
  let Q : TQ (thickObj R (maximalIdeal R) 0 G) D.toPre.X :=
    { B := thickObj R (maximalIdeal R) 0 D.toPre.P.A
      isAb := hB
      q := g.q
      i := g.i
      q_hom := g.q_hom
      i_hom := g.i_hom
      q_flat := g.q_flat
      q_surj := g.q_surj
      q_affine := g.q_affine
      isKernel := g.isKernel
      loc := by
        have l := (TQ.ofGtDatum d).loc
        rw [show (TQ.ofGtDatum d).q = g.q from hdq, show (TQ.ofGtDatum d).i = g.i from hdi] at l
        exact l }
  obtain ⟨P₀, hlev⟩ := exists_isLevelCP (maximalIdeal R) 0 U'.P
  have hlev' := hlev
  obtain ⟨w₀, h₀⟩ := hlev
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U'.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U'.P.L.isLB _) _ (pullIso_isGen U'.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := GlobalTheory.ClosedPol.isCPMap_w hG U' 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U'.gt 0).pG)
  obtain ⟨M, wM, hM⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hG D.toPre)
  obtain ⟨w₄, k₄⟩ := GlobalTheory.ClosedPol.cpMap_congr rfl (Category.id_comp _) k₃
    (by rw [Category.assoc, pullback.condition, Category.id_comp]; simpa using Over.w (U'.gt 0).pG)
  obtain ⟨w₅, k₅, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M P₀ _ _ _ g.q.left
    ((Over.w g.q).trans (Category.comp_id _).symm) _ hM).2
    (toBase_mul_of_isMonHom g.q _) w₄ k₄
  have De : Q.Desc P₀ := ⟨M, w₅, k₅⟩
  obtain ⟨a₀, P', -, ha₀, hl', hL', hs', hc'⟩ := GlobalTheory.T.translatedCubicalBundle_closedFibre_uniformisation R D A G U a ha P hP hsym hcub P₀ hlev'
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_even_cubicalTriv_translate_order_two _ _ D.toPre.X Q P₀ ⟨De⟩ a₀ ha₀ P' hL' hs' hc'
  exact ⟨D.toPre.X, inferInstance, inferInstance, inferInstance, Q, P', hl', σ', hσ'⟩

end GlobalTheory.Mum.TransEven
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.SympQ.compatible_symplectic_bases : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ g : ℕ, g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → ∃ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) ∧ (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) ∧ (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) ∧ ∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F) := by
  intro R _ _ _ hR D F _ _ _ ζ hζ hζc g hg
  subst hg
  have hL : Laws := GlobalTheory.allSixLaws.1
  have gt : GlobalTheory.Ex.BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  have wp : GlobalTheory.Ex.BrWpSt := GlobalTheory.WeilValues.weil_eq_values gt (GlobalTheory.Ex.brFam hL GlobalTheory.allSixLaws.2.1)
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, ν, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL R D.toPre D.psi_even D.tau_bimult F ⊤ (fun _ => trivial)
  obtain ⟨-, -, gAdd, -, gQ⟩ := gt R D.toPre D.psi_even D.tau_bimult F N ν
  have hW := wp R D.toPre D.psi_even D.tau_bimult F N ν
  have hcl : ∀ n (p p' : QkPt D.toPre F n) v v', ν.QPt p v → ν.QPt p' v' →
      (QkPt.Equiv D.toPre F p p' ↔ (QuotientGroup.mk v : GlobalTheory.SympQ.Qq N n) = QuotientGroup.mk v') :=
    fun n p p' v v' h h' => ((gQ n).2.2 p p' v v' h h').trans (GlobalTheory.SympQ.qEq_iff_mk_eq N v v')
  have h1 : ∀ n (x y z : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n (x + y).toMul z.toMul = GlobalTheory.SympQ.wpQ N n x.toMul z.toMul * GlobalTheory.SympQ.wpQ N n y.toMul z.toMul := by
    intro n x y z
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨p'', hp''⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    simp only [toMul_add]
    rw [← hp, ← hp', ← hp'', ← QuotientGroup.mk_mul, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk,
      GlobalTheory.Ex.WpPairing.wp_mul_left]
  have h2 : ∀ n (x y z : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n x.toMul (y + z).toMul = GlobalTheory.SympQ.wpQ N n x.toMul y.toMul * GlobalTheory.SympQ.wpQ N n x.toMul z.toMul := by
    intro n x y z
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨p'', hp''⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    simp only [toMul_add]
    rw [← hp, ← hp', ← hp'', ← QuotientGroup.mk_mul, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk,
      GlobalTheory.Ex.WpPairing.wp_mul_right]
  have h3 : ∀ n (x : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n x.toMul x.toMul = 1 := by
    intro n x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← hp, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.Ex.NumD.wp_self]
  have h4 : ∀ n, 0 < n → ∀ x : Additive (GlobalTheory.SympQ.Qq N n), (∀ y : Additive (GlobalTheory.SympQ.Qq N n), GlobalTheory.SympQ.wpQ N n x.toMul y.toMul = 1) → x = 0 := by
    intro n hn x hx
    exact Additive.toMul.injective (GlobalTheory.T.reprModTrivialQuotient_pairing_nondegenerate R hR D F N ν n hn x.toMul fun y => hx (Additive.ofMul y))
  have h5 : ∀ n m, 0 < n → 0 < m → ∀ x y : Additive (GlobalTheory.SympQ.Qq N (n * m)), GlobalTheory.SympQ.wpQ N n ((GlobalTheory.SympQ.pushQ N (n * m) n).toAdditive x).toMul ((GlobalTheory.SympQ.pushQ N (n * m) n).toAdditive y).toMul = GlobalTheory.SympQ.wpQ N (n * m) x.toMul y.toMul ^ m := by
    intro n m hn hm x y
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    change GlobalTheory.SympQ.wpQ N n (GlobalTheory.SympQ.pushQ N (n * m) n x.toMul) (GlobalTheory.SympQ.pushQ N (n * m) n y.toMul) =
      GlobalTheory.SympQ.wpQ N (n * m) x.toMul y.toMul ^ m
    rw [← hp, ← hp', GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk]
    exact GlobalTheory.T.reprModTrivialQuotient_pairing_levelPush_eq_pow R hR D F N ν n m hn hm p p'
  have h6 : ∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x : Additive (GlobalTheory.SympQ.Qq N M), (GlobalTheory.SympQ.pushQ N n k).toAdditive ((GlobalTheory.SympQ.pushQ N M n).toAdditive x) = (GlobalTheory.SympQ.pushQ N M k).toAdditive x := by
    intro M n k hk hM hkn hnM x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    apply Additive.toMul.injective
    change GlobalTheory.SympQ.pushQ N n k (GlobalTheory.SympQ.pushQ N M n x.toMul) = GlobalTheory.SympQ.pushQ N M k x.toMul
    rw [← hp, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk]
    congr 1
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [GlobalTheory.SympQ.pushRep_fst N hkn, GlobalTheory.SympQ.pushRep_fst N hnM, GlobalTheory.SympQ.pushRep_fst N (hkn.trans hnM)]
    · have e : M / n * (n / k) = M / k := by
        obtain ⟨b, rfl⟩ := hkn
        obtain ⟨a, rfl⟩ := hnM
        have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
        rw [Nat.mul_div_cancel_left _ (Nat.mul_pos hk hb), Nat.mul_div_cancel_left _ hk, Nat.mul_assoc,
          Nat.mul_div_cancel_left _ hk, Nat.mul_comm]
      rw [GlobalTheory.SympQ.pushRep_snd N hkn, GlobalTheory.SympQ.pushRep_snd N hnM, GlobalTheory.SympQ.pushRep_snd N (hkn.trans hnM), ← pow_mul, e]
  obtain ⟨ev', hker, hsurj, htow, hweil⟩ := GlobalTheory.T.exists_compatible_symplectic_alt F ζ hζ hζc (D.toPre.P.g + Module.finrank ℤ D.toPre.X)
    (fun n => Additive (GlobalTheory.SympQ.Qq N n)) (fun n x y => GlobalTheory.SympQ.wpQ N n x.toMul y.toMul)
    (fun M n => (GlobalTheory.SympQ.pushQ N M n).toAdditive) (GlobalTheory.T.reprModTrivialQuotient_free_rank_twice_dimension R hR D F N ν) h1 h2 h3 h4 h5 h6
  have hrep : ∀ n a, ∃ q : N.QT n, (QuotientGroup.mk q : GlobalTheory.SympQ.Qq N n) = (ev' n a).toMul :=
    fun n a => QuotientGroup.mk_surjective _
  choose q hq using hrep
  choose P hP using fun n a => (gQ n).2.1 (q n a)
  refine ⟨P, fun n hn a b => ?_, fun n hn a b => ?_, fun n hn p => ?_, fun n m hn hm a => ?_, fun n hn a b => ?_⟩
  · obtain ⟨r, hr⟩ := (gQ n).2.1 (q n a * q n b)
    refine ⟨r, ?_, (gAdd _ _ _ _ _ _ (hP n a).2 (hP n b).2 hr.2).2 rfl, ?_⟩
    · rw [← hr.1, ← (hP n a).1, ← (hP n b).1, ← map_add (f := _)]
      rfl
    · rw [hcl n _ _ _ _ hr (hP n (a + b)), QuotientGroup.mk_mul, hq, hq, hq, map_add (f := _), toMul_add]
  · rw [hcl n _ _ _ _ (hP n a) (hP n b), hq, hq, Additive.toMul.injective.eq_iff]
    exact hker n hn a b
  · obtain ⟨v, hv⟩ := ((gQ n).1 p).exists
    obtain ⟨a, ha⟩ := hsurj n hn (Additive.ofMul (QuotientGroup.mk v))
    exact ⟨a, (hcl n _ _ _ _ (hP n a) hv).2 (by rw [hq, ha]; rfl)⟩
  · have hd : n ∣ n * m := dvd_mul_right n m
    obtain ⟨r, hr⟩ := (gQ n).2.1 (GlobalTheory.SympQ.pushRep N (n * m) n (q (n * m) a))
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [← hr.1, ← (hP (n * m) a).1, GlobalTheory.SympQ.pushRep_fst N hd]
    · refine (GlobalTheory.Ex.GtValues.isNsmul_val ν m (hP (n * m) a).2 hr.2).2 ?_
      rw [GlobalTheory.SympQ.pushRep_snd N hd, Nat.mul_div_cancel_left m hn]
    · rw [hcl n _ _ _ _ hr (hP n a), ← GlobalTheory.SympQ.pushQ_mk, hq, hq, ← htow n m hn hm a]
      rfl
  · refine (hW n hn (P n a) (P n b) (q n a) (q n b) _ (hP n a) (hP n b)).2 ?_
    rw [← GlobalTheory.SympQ.wpQ_mk, hq, hq]
    exact congrArg Units.val (hweil n hn a b).symm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

noncomputable section
namespace GlobalTheory.Mum


open GlobalTheory.TorsionFormCompare in
theorem exists_unif_move_iso_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] (ε : G ≅ G₀), IsMonHom ε.hom → IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ U : Unif (maximalIdeal R) D A₀ G, LBIso U.LG.L (U₀.LG.L.pull ε.hom.left) := by
  intro R _ _ _ hB D A₀ G G₀ _ _ _ _ ε hε hsa U₀
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have he : eSec G ≫ ε.hom.left = 𝟙 _ ≫ eSec G₀ := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε.hom)
  let L' : RigLB G := ⟨U₀.LG.L.pull ε.hom.left, rigPullOf ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig,
    LB.isLB_pull U₀.LG.isLB _,
    GlobalTheory.CubePullLawChecks.rigPullIsGen ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig U₀.LG.isLB U₀.LG.rigGen⟩
  let w : LB.Iso L'.L (U₀.LG.L.pull ε.hom.left) := idIso L'.L
  have hw : RigAlong ε.hom U₀.LG L' w :=
    ⟨idIso_isGen L'.isLB, (maps_iff w _ (fun _ => eSec G₀) _ L'.rig U₀.LG.rig (𝟙 _) _
      (rigPull_le _ _ he U₀.LG.L) (fun _ => rfl)).1 (idIso_maps L')⟩
  obtain ⟨W, hW, hψ⟩ := psiOnExists R (maximalIdeal R) hR D
  obtain ⟨hD, hid⟩ := exists_isIdPull R D.toPre W hW hψ
  obtain ⟨bc, U, -, hb, -, hgen, hU⟩ :=
    exists_unif_move R (maximalIdeal R) D A₀ G₀ G ε hR hsa hε U₀ L' w hw hD
  obtain ⟨-, w', hw', -⟩ := sameUnif_of_isPullUnif R (maximalIdeal R) D A₀ G₀ G ε hD hid bc U₀ U hb hgen hU
  exact ⟨U, w', hw'.1⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section
namespace GlobalTheory.Mum

theorem isPullUnif_of_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (D₁ : DegData R (maximalIdeal R)) (U₁ : Unif (maximalIdeal R) D₁ A G), LBIso U'.LG.L (U₁.LG.L.pull β) → ∃ (h : IsPullDeg ρ D₁.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf ρ)).obj G), bc.hom.left ≫ pullback.fst G.hom (specOf ρ) = β ∧ IsPullUnif ρ h bc U₁ U' := by
  intro R _ _ _ hRb R' _ _ _ ρ hfin D' A' G' _ _ hsa' U' G _ _ β hsa hgp A D₁ U₁ hL
  obtain ⟨hR', hinj, hfinite⟩ := hfin
  have hR := hRb.1
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hgp (isGrpPullback_pullback G (spMap ρ))
  subst hbc
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' :=
    GlobalTheory.ResidueGalois.map_maximalIdeal_le ρ hfinite.to_isIntegral
  have hP := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
  have sq : spMap (fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hinj).symm.trans (Category.id_comp _)
  obtain ⟨A'', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hinj)) A
  have gpA : IsGrpPullback A''.A A.A (spMap (fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U₁.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj G') G (spMap (fracMap hinj) ≫ jK R)
      (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback G' (jK R')).comp hgp).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₁.gen.inv.left ≫ U₁.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A''.L.pull eA.hom.left) (U₁.LG.L.pull (pullback.fst G'.hom (jK R') ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf ρ))) := by
    refine LBIso.trans (pull_isLB A''.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U₁.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A''.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₁.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U₁.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₁.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U₁.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ρ) = specOf ρ ≫ eSec G :=
    (cubeMapOf hgp).e_comm
  obtain ⟨w₀, hw₀⟩ := hL
  have hσ : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  obtain ⟨wL, gL, pL⟩ := GlobalTheory.UnifPreCompare.exists_rigidified U₁.LG.isLB U'.LG.isLB G'.hom (eSec G') hσ w₀ hw₀
    U'.LG.rig U'.LG.rigGen U₁.LG.rig U₁.LG.rigGen (specOf ρ) he
  have mL : LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig
      (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf ρ)) (specOf ρ) he U₁.LG.L U₁.LG.rig) :=
    (maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U₁.LG.rig (specOf ρ) _
      (rigPull_le (G' := G') (G := G) _ (specOf ρ) he U₁.LG.L) (fun _ => rfl)).2 pL
  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists R (maximalIdeal R) hR D₁
  have hgen : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective ρ hinj)
    rw [this]; exact hWo
  obtain ⟨D'', hD₁, U'', hLG, -, H₁⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds R R' (maximalIdeal R) (maximalIdeal R')
    hR hR' ρ hI D₁ A G hsa U₁ Wo hψ hgen G' bc mbc A'' dA eA mE wA U'.LG wL he gL mL
  obtain ⟨wL₀, g₀, m₀⟩ := exists_iso_of_eq hLG.symm
  have h6 := GlobalTheory.unifUniq GlobalTheory.abelianSchemeLaws_all.1.globalFns GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.ample
  obtain ⟨hD₂, hlev, -⟩ := h6 R' (maximalIdeal R') hR' D'' D' A'' A' G' hsa' U'' U' wL₀ g₀ m₀
  have hs := specOf_id R'
  haveI mR : IsMonHom (Iso.refl G').hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨bc₀, -, hbc₀⟩ := grpPullback_iso ((isGrpPullback_of_iso (Iso.refl G')).congr hs.symm rfl)
    (isGrpPullback_pullback G' (Out.specOf (RingHom.id R')))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst G'.hom (Out.specOf (RingHom.id R')) = 𝟙 _ := hbc₀
  have H₂ := isPullUnif_of_uniq U'' U' hD₂ wL₀ g₀ m₀ hlev bc₀ hbc₀'
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := GalMul.exists_isPullDeg_comp hinj (fun _ _ h => h) hD₁ hD₂
  have hb : bc.hom.left ≫ pullback.fst G.hom (specOf ((RingHom.id R').comp ρ)) =
      (bc₀.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R'))) ≫
        (bc.hom.left ≫ pullback.fst G.hom (specOf ρ)) := by
    rw [hbc₀', Category.id_comp]
  exact ⟨r, bc, rfl, GalMul.isPullUnif_comp r₁ r₂ r₃ T hb H₁ H₂⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem endU_genMap {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegData V (maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    (E : EndU U.toUnifPre) : E.aA.left ≫ genMap U = genMap U ≫ E.aG.left := by
  have h1 : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK V)).map E.aG := by
    rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
  have h1' : E.aA.left ≫ U.gen.inv.left = U.gen.inv.left ≫ ((Over.pullback (jK V)).map E.aG).left := by
    have := congrArg CommaMorphism.left h1
    simpa only [Over.comp_left] using this
  have h2 : ((Over.pullback (jK V)).map E.aG).left ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ E.aG.left :=
    pullback.lift_fst _ _ _
  unfold genMap
  rw [← Category.assoc, h1', Category.assoc, h2, Category.assoc]

theorem exists_ext : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (gm : A.A.left ⟶ H.left), IsGrpPullback A.A H (jK V ≫ ξ) gm → ∃ β : G.left ⟶ H.left, IsGrpPullback G H ξ β ∧ genMap U ≫ β = gm ∧ ∀ (E : EndU U.toUnifPre) (Fm : H ⟶ H), E.aA.left ≫ gm = gm ≫ Fm.left → E.aG.left ≫ β = β ≫ Fm.left := by
  intro B H _ _ hH V _ _ _ hV G _ _ hG D A U ξ gm hgm
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hV
  haveI := hN
  haveI := hIC
  have gpA : IsGrpPullback A.A G (jK V) (genMap U) := by
    have := U.gen_hom
    have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr
      (Category.id_comp _) rfl
  have : IsMonHom (Iso.refl H).hom := by show IsMonHom (𝟙 H); infer_instance
  have hHH : IsGrpPullback H H (𝟙 B) (𝟙 H.left) := isGrpPullback_of_iso (Iso.refl H)
  obtain ⟨β, hβ, hβg⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map V (𝟙 B) H H (𝟙 _) hH hHH G hG ξ (jK V ≫ ξ)
    (Category.comp_id _) A.A (genMap U) gm gpA hgm
  have hβg' : genMap U ≫ β = gm := by simpa using hβg
  refine ⟨β, hβ, hβg', ?_⟩
  intro E Fm hE
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsSchemeTheoreticallyDominant (genMap U) := .of_isPullback gpA.1.flip
  have key := endU_genMap U E
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant H.hom ?_ (genMap U) ?_
  · rw [Category.assoc, Category.assoc, Over.w Fm, hβ.1.w, ← Category.assoc, Over.w E.aG]
  · rw [← Category.assoc, ← key, Category.assoc, hβg', hE, ← Category.assoc, hβg']

end GlobalTheory.Poinc.Sep.Spz
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

theorem _root_.GlobalTheory.T.mumfordBundle_adjoint_of_generic_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] A.L) (cubeLB A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] A.L) → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) := by
  first | exact @GlobalTheory.PoincAdj.lbIso_adj_of_generic | exact GlobalTheory.PoincAdj.lbIso_adj_of_generic | (intros; apply GlobalTheory.PoincAdj.lbIso_adj_of_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_baseChange_semiAbelian_cubical_polarised_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R' → FinExt ρ → ∃ (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), IsSemiAbelian G₁ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) := by
  first | exact @GlobalTheory.Mum.exists_baseChange_semiAbelian_data | exact GlobalTheory.Mum.exists_baseChange_semiAbelian_data | (intros; apply GlobalTheory.Mum.exists_baseChange_semiAbelian_data <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_commonPullback_fractionField_finiteLocalExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegPre R) (E₁ E₂ : DegPre (FractionRing R)), IsPullDeg (algebraMap R (FractionRing R)) D₁ E₁ → IsPullDeg (algebraMap R (FractionRing R)) D₂ E₂ → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (E₃ : DegPre K'), io.Finite → IsPullDeg io E₁ E₃ → IsPullDeg io E₂ E₃ → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (E : DegPre (FractionRing R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) := by
  first | exact @GlobalTheory.CommonCover.exists_common_pull | exact GlobalTheory.CommonCover.exists_common_pull | (intros; apply GlobalTheory.CommonCover.exists_common_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generic_fibres_common_pullDeg_to_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ D' : DegPre W, IsPullDeg φ D₁.toPre D' → IsPullDeg φ D₂.toPre D' → ∃ (E₁ E₂ : DegPre (FractionRing R)) (L : Type) (_ : Field L) (β : FractionRing R →+* L) (E' : DegPre L), Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₁.toPre E₁) ∧ Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₂.toPre E₂) ∧ Nonempty (IsPullDeg β E₁ E') ∧ Nonempty (IsPullDeg β E₂ E') := by
  first | exact @GlobalTheory.Mum.exists_generic_common_pull | exact GlobalTheory.Mum.exists_generic_common_pull | (intros; apply GlobalTheory.Mum.exists_generic_common_pull <;> assumption)
end
