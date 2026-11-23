module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSquareDeterminantComparisonIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle040
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_periodLevel_of_siegel_point : ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (g k : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → ∃ (P : Out.PolAV (Sp ℂ)) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev := by
  first | exact @GlobalTheory.SiegelObject.exists_perLev_of_siegel | exact GlobalTheory.SiegelObject.exists_perLev_of_siegel | (intros; apply GlobalTheory.SiegelObject.exists_perLev_of_siegel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem Val.pow {x y : KeyIn ℂ} {j : ℕ} {t : ℂ} (hp : IsKeyPow y x j) (h : Val x t) : Val y (t ^ j) := by
  obtain ⟨τ, M, a, b, c, ⟨ha, hb⟩, hc, hN, rfl⟩ := h
  have ea : a = fun k => (((a k).re : ℝ) : ℂ) := by
    funext k
    rcases ha k with h | h <;> rw [h] <;> norm_num
  have eb : b = fun k => (((b k).re : ℝ) : ℂ) := by
    funext k
    rcases hb k with h | h <;> rw [h] <;> norm_num
  rw [ea, eb] at hN
  obtain ⟨e, τ', M', hdet, hN'⟩ := normalAt_pow x y j τ M _ _ c hp hN
  refine ⟨τ', M', _, _, c ^ j, ⟨fun p => ?_, fun p => ?_⟩, pow_ne_zero _ hc, hN', ?_⟩
  · rw [← congrFun ea]; exact ha _
  · rw [← congrFun eb]; exact hb _
  · rw [hdet, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm 4, Nat.mul_comm 8]

theorem isElliptic_cube_sub : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).IsElliptic := by
  refine ⟨Ne.isUnit ?_⟩
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem exists_known_rat : Out.Laws → ThetaUnifAV → ∀ g : ℕ, 1 ≤ g → ∃ y : KeyIn ℚ, y.P.g = g ∧ Known ℚ y := by
  intro _ hU g hg
  have := isElliptic_cube_sub
  obtain ⟨y₁, h₁, hval⟩ := EllipticKey.exists_keyIn_value_eq_discriminant hU ℚ ⟨0, 0, 0, -1, 0⟩
  obtain ⟨y, hy⟩ := exists_isKeyPow ℚ y₁ g hg
  refine ⟨y, ?_, (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ ^ g, fun e x hx => ?_⟩
  · obtain ⟨-, h, -⟩ := hy
    rw [← h, h₁, Nat.mul_one]
  · obtain ⟨x₁, hx₁⟩ := exists_keyPB_ring y₁ e
    obtain ⟨⟨τ, M, a, b, c, hab, hc, -, hN⟩, -⟩ := KeyNormalExists.exists_normalAt hU x₁
    have hv₁ : Val x₁ (e (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ) :=
      ⟨τ, M, a, b, c, hab, hc, hN, (hval e x₁ τ M a b c hx₁ hab hc hN).symm⟩
    obtain ⟨x', hx'⟩ := exists_isKeyPow ℂ x₁ g hg
    have hpb := keyPB_of_isKeyPow ℚ ℂ e y₁ y x₁ x' g hx₁ hy hx'
    have hid : KeyPB x x' (RingHom.id ℂ) := KeyCancel.keyPB_cancel ℚ ℂ ℂ y x' x e (RingHom.id ℂ) hpb hx
    rw [map_pow]
    exact ((GlobalTheory.T.normalForms_eq_of_keyDataIso_complex x' x hid).1 _).1 (hv₁.pow hx')

end GlobalTheory.KeyFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_keyData_near_two_primes : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), 1 ≤ Q.g → ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ (y : KeyIn (Localization.Away r)) (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap (algebraMap R (Localization.Away r))) φ := by
  first | exact @GlobalTheory.KeyFam.exists_keyIn_near_two | exact GlobalTheory.KeyFam.exists_keyIn_near_two | (intros; apply GlobalTheory.KeyFam.exists_keyIn_near_two <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.SimilLocal

open GlobalTheory.RelBasis GlobalTheory.SimilDet

theorem det_ne_zero : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (ξ : (Fin 4 → Fin N) → Fin 4 → Pt x) (w : ∀ I, LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ I r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (Q : Matrix (Fin 4 → Fin N) (Fin 4 → Fin N) K), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → Function.Injective ξ → (∀ I, (w I).IsGen) → (∀ I, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ I r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ I r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ I r)).left))) = (val (w I) ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left)))) → Q.det ≠ 0 := by
  intro laws K _ _ x m N al b ξ w Q hm hal hξ hw hE
  classical
  have hL := x.P.isLB
  intro h0
  obtain ⟨c, hc, hcQ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  obtain ⟨I₀, -⟩ := Function.ne_iff.1 hc
  refine hc ?_
  let S : Over (Sp K) := 𝟙_ _
  let T := Out.powObj x.P.A 4
  haveI : IsIntegral S.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of K)))
  haveI : Subsingleton S.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : S.left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : S.left ⟶ x.P.A.left => exists_chart hL (χ p)
  replace hJ : Good x.P.L p J := hJ
  let ev : Γ(S.left, ⊤) →+* S.left.presheaf.stalk p := (S.left.presheaf.germ ⊤ p trivial).hom
  have hev : ∀ (y : S ⟶ T) a, gs (y.left ≫ T.hom) p ⊤ a = ev a := fun y a => by
    rw [Over.w y]
    exact gs_eq (𝟙 S.left) p ⊤ trivial a
  let κ : K →+* S.left.presheaf.stalk p := ev.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  choose a ha using fun I v => exists_transl_ratio laws x m al (ξ I₀) (ξ I) (w I₀) (w I) (hw I₀) (hw I) v
  let u : (Fin 4 → Fin N) → (S ⟶ T) → (S.left.presheaf.stalk p)ˣ := fun I y =>
    val (w I₀) y.left p J * (val (w I) y.left p J)⁻¹
  have hu : ∀ I (v : ker x al) (y : S ⟶ T), (u I (v.1 * y)).val = ev (a I v) * (u I y).val := fun I v y => by
    have := ha I v _ y.left p J hJ
    rw [hev, ← Over.comp_left, pt_tr] at this
    rw [← this, ← Units.val_mul, inv_mul_cancel_right]
  let χ : (Fin 4 → Fin N) → ker x al →* S.left.presheaf.stalk p := fun I =>
    { toFun := fun v => ev (a I v)
      map_one' := by
        have := hu I 1 1
        rw [Submonoid.coe_one, _root_.one_mul] at this
        exact (Units.mul_left_inj (u I 1)).1 (this.symm.trans (_root_.one_mul _).symm)
      map_mul' := fun v v' => by
        have := hu I (v * v') 1
        rw [Submonoid.coe_mul, _root_.mul_assoc, hu, hu, ← _root_.mul_assoc] at this
        exact ((Units.mul_left_inj (u I 1)).1 this).symm }
  have hχ : Function.Injective χ := fun I I' h => by
    have e := GlobalTheory.T.eq_of_similitudeIso_quotient_kernel_invariant laws K x m al (ξ I) (ξ I') (w I) (w I') hm hal (hw I) (hw I') (fun v hv Z r z J hJ => by
      have e₁ : a I ⟨v, hv⟩ = a I' ⟨v, hv⟩ := fn_ext (X := S.left) fun y _ => by
        obtain rfl : y = p := Subsingleton.elim _ _
        exact (gs_eq (𝟙 S.left) p ⊤ trivial _).trans ((DFunLike.congr_fun h ⟨v, hv⟩).trans
          (gs_eq (𝟙 S.left) p ⊤ trivial _).symm)
      have e₂ := Units.ext ((ha I ⟨v, hv⟩ Z r z J hJ).trans (e₁ ▸ (ha I' ⟨v, hv⟩ Z r z J hJ).symm))
      have alg : ∀ {U : Type} [CommGroup U] (A B B' C D D' : U),
          A * B⁻¹ * (C * D⁻¹)⁻¹ = A * B'⁻¹ * (C * D'⁻¹)⁻¹ → B * D' = B' * D := fun A B B' C D D' h => by
        rw [mul_inv, mul_inv, inv_inv, inv_inv, _root_.mul_assoc, _root_.mul_assoc, mul_right_inj, mul_left_comm,
          mul_left_comm B'⁻¹, mul_right_inj, inv_mul_eq_iff_eq_mul] at h
        rw [h, mul_left_comm B', mul_inv_cancel_left]
      exact alg _ _ _ _ _ _ e₂)
    exact hξ e
  let θ : (Fin 4 → Fin N) → (S ⟶ T) → S.left.presheaf.stalk p := fun I y =>
    ∏ r, gs (y.left ≫ (alMap x al r (ξ I r)).left) p _ (x.th.f (J (y.left ≫ (alMap x al r (ξ I r)).left)))
  refine eq_zero_of_eigen κ χ hχ (fun v y => v.1 * y) (fun I y => θ I y * (u I y).val) (fun I v y => ?_)
    (fun I => ?_) c (fun y => ?_)
  · have e : θ I (v.1 * y) = θ I y := Finset.prod_congr rfl fun r _ =>
      congrArg (fun ψ : S.left ⟶ x.P.A.left => gs ψ p _ (x.th.f (J ψ))) (by
        rw [← Over.comp_left, ← Over.comp_left, ← pt_tr, Category.assoc, tr_alMap])
    simp only [hu, e]
    exact mul_left_comm _ _ _
  · obtain ⟨y, hy⟩ := GlobalTheory.SimilNonvan.exists_pt_isUnit laws K x m al (ξ I) hm hal
    exact ⟨y, mul_ne_zero (Finset.prod_ne_zero_iff.2 fun r _ => (hy p J hJ r).ne_zero) (Units.ne_zero _)⟩
  · have e : ∀ I, θ I y * (u I y).val = (val (w I₀) y.left p J).val * ∑ I', κ (Q I I') *
        ∏ c, gs (y.left ≫ (Out.powPr x.P.A c).left) p _ ((b (I' c)).f (J (y.left ≫ (Out.powPr x.P.A c).left))) :=
      fun I => by
      have e₁ : θ I y = _ := hE I _ y.left p J hJ
      rw [e₁, mul_right_comm, ← Units.val_mul, mul_comm (val (w I) y.left p J),
        inv_mul_cancel_right]
      refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
      rw [gs_cst, hev]
      rfl
    simp only [e, mul_left_comm _ (val (w I₀) y.left p J).val, ← Finset.mul_sum]
    refine mul_eq_zero_of_right _ ?_
    simp only [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun I' _ => ?_

    rw [← Finset.sum_mul, ← map_sum, show ∑ I, c I * Q I I' = 0 from congrFun hcQ I', map_zero, zero_mul]

theorem exists_coords_pow (laws : Out.Laws) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R)
    (m : ℕ) (hm : 1 ≤ m) (b : Fin (m ^ x.P.g) → RR x m) (hb : IsBasis x b) (n : ℕ)
    (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))) :
    ∃ q : (Fin n → Fin (m ^ x.P.g)) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J,
      Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) *
        ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left)))
          ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  refine GlobalTheory.T.boxProducts_span_external_powers_of_boxSpan R x.P.A x.P.L m _ b x.P.isLB (fun T => ?_) n s
  refine GlobalTheory.T.pullbackSectionsSpanTwisted_of_indep_span _ _ _ _ _ _ b _ _ x.P.isLB (GlobalTheory.T.pullbackSections_basis_of_affine_opens _ _ _ _ _ _ b _ _ ?_)
  refine GlobalTheory.T.pullbackSections_basis_affine_baseChange_of_affine R _ x.P.A.hom x.P.L _ _ b (fun R' _ f => ?_) _ _ T.hom _ _
    (IsPullback.of_hasPullback x.P.A.hom T.hom)
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.keyIn_baseChange laws.polBaseChange R R' x f
  obtain ⟨h₁, h₂⟩ := GlobalTheory.KeyVia.main R R' x x' f
  obtain ⟨φ, w, hv⟩ := h₁.1 hx'
  choose b' hb' using fun k => ((h₂ φ w hv).1 m (b k)).exists
  have hP : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f) := by
    obtain ⟨he, hg, F, ⟨hP, -⟩, -⟩ := hv
    exact hP
  exact ⟨_, x'.P.A.hom, φ, hP, GlobalTheory.T.basisBaseChange_relativeBasis_pulledBackSections R R' x x' f φ w m _ b b' hv hb'
    ((GlobalTheory.KeyBasis.main laws R x m hm).2 b hb R' f x' φ w b' hv hb')⟩

theorem exists_l2Val : Out.Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (m ^ x.P.g) → RR x m) (ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x), IsUnit (m : R) → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → (∀ I I', I ≠ I' → ∀ p : Sp R, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) → (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) → ∃ lam, IsSquareDeterminantComparison x m al b lam := by
  intro laws R _ _ _ _ x m al b ξ hm hal hb hξ hk
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := R) (by simpa using hm)
  obtain ⟨mu, hmu, hmu'⟩ := GlobalTheory.KeyKa.exists_normalised_mulPull laws R x m
  choose w hw using fun I => GlobalTheory.SimilPull.exists_gen_similitude_pull laws R x m al (ξ I) hal (hk I)
  choose rho hrho using fun I => GlobalTheory.SimilUnit.exists_normalising_unit R x m al (ξ I) mu (w I) hm0 hal (hk I) hmu (hw I)
  choose s hs using fun I => GlobalTheory.KeyQuot.exists_sec_quot _ _ x.P.L x.P.isLB _ _ _ _ (m : ℤ) x.th (w I) (hw I)
  choose Q hQ using fun I => exists_coords_pow laws R x m (Nat.one_le_iff_ne_zero.2 hm0) b hb 4 (s I)
  have hZ : ∀ I, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ I r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ I r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ I r)).left))) = (val (w I) ρ z J).val * ∑ I' : Fin 4 → Fin (m ^ x.P.g), gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left))) := by
    intro I Z ρ z J hJ
    rw [← hQ I Z ρ z J hJ]
    exact hs I Z ρ z J hJ
  have hE : ∀ I, ∀ (y : (Out.powObj x.P.A 4).left) J, Good x.P.L y J → ∏ r, gs (alMap x al r (ξ I r)).left y _ (x.th.f (J (alMap x al r (ξ I r)).left)) = (val (w I) (𝟙 _) y J).val * ∑ I' : Fin 4 → Fin (m ^ x.P.g), gs (𝟙 _) y ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) * ∏ c, gs (Out.powPr x.P.A c).left y (x.P.L.U (J (Out.powPr x.P.A c).left)) ((b (I' c)).f (J (Out.powPr x.P.A c).left)) := by
    intro I y J hJ
    have e₁ := hZ I _ (𝟙 _) y J hJ
    have c₁ : ∀ ψ : (Out.powObj x.P.A 4).left ⟶ x.P.A.left,
        gs (𝟙 _ ≫ ψ) y (x.P.L.U (J (𝟙 _ ≫ ψ))) (x.th.f (J (𝟙 _ ≫ ψ))) = gs ψ y (x.P.L.U (J ψ)) (x.th.f (J ψ)) :=
      fun ψ => by rw [Category.id_comp]
    have c₂ : ∀ (ψ : (Out.powObj x.P.A 4).left ⟶ x.P.A.left) k,
        gs (𝟙 _ ≫ ψ) y (x.P.L.U (J (𝟙 _ ≫ ψ))) ((b k).f (J (𝟙 _ ≫ ψ))) = gs ψ y (x.P.L.U (J ψ)) ((b k).f (J ψ)) :=
      fun ψ k => by rw [Category.id_comp]
    simpa only [c₁, c₂] using e₁
  have hdet : IsUnit (Matrix.det (Matrix.of Q)) := by
    let k := AlgebraicClosure (IsLocalRing.ResidueField R)
    let f : R →+* k := (algebraMap (IsLocalRing.ResidueField R) k).comp (IsLocalRing.residue R)
    obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.keyIn_baseChange laws.polBaseChange R k x f
    obtain ⟨h₁, h₂⟩ := GlobalTheory.KeyVia.main R k x x' f
    obtain ⟨φ, u, hv⟩ := h₁.1 hx'
    choose b' hb' using fun j => ((h₂ φ u hv).1 m (b j)).exists
    choose ξ' hξ' using fun I r => ((h₂ φ u hv).2.1 (ξ I r)).exists
    choose w' hw' hE' using fun I =>
      GlobalTheory.T.similitudeIso_thetaProduct_baseChange R k x x' f φ u m _ al b b' (ξ I) (ξ' I) (w I) (Q I) hv hb' (hξ' I) (hw I) (hZ I)
    have hinj : Function.Injective ξ' := fun I I' e => by
      by_contra hne
      obtain ⟨r, hr⟩ := hξ I I' hne (spMap f (IsLocalRing.closedPoint k))
      have e' : spMap f ≫ (ξ I r).left = spMap f ≫ (ξ I' r).left := by rw [← hξ' I r, ← hξ' I' r, e]
      exact hr (congrArg (fun q => q (IsLocalRing.closedPoint k)) e')
    have hne := det_ne_zero laws k x' m _ al b' ξ' w' ((Matrix.of Q).map f)
      (by simpa only [map_natCast] using (hm.map f).ne_zero) hal hinj hw' hE'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hne
    by_contra hu
    refine hne ?_
    have : IsLocalRing.residue R (Matrix.det (Matrix.of Q)) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hu
    show algebraMap (IsLocalRing.ResidueField R) k (IsLocalRing.residue R _) = 0
    rw [this, map_zero]
  refine ⟨hdet.unit ^ (2 * m ^ 2) * ∏ I, rho I ^ 2, ξ, mu, w, Matrix.of Q, rho, hξ, hk, hmu, hw,
    fun p J hJ => ⟨hmu' p J hJ, fun I => hrho I p J hJ⟩, hE, ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.coe_prod]

end GlobalTheory.SimilLocal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KnownScale

theorem val_scale {P : Out.PolAV (Sp ℂ)} {hg rig hr th hth v hv th' hth' v' hv'} {a : ℂ} (ha : a ≠ 0)
    {N : Matrix (Fin P.g) (Fin P.g) ℂ} (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i)
    (h₂ : ∀ i, IsLieComb (N i) v (v' i)) {t : ℂ} (h : Val ⟨P, hg, rig, hr, th, hth, v, hv⟩ t) :
    Val ⟨P, hg, rig, hr, th', hth', v', hv'⟩ (N.det ^ 4 / a ^ 8 * t) := by
  obtain ⟨τ, M, p, q, c, hpq, hc, ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩, rfl⟩ := h
  have := P.isAb.comm
  refine ⟨τ, N * M, p, q, a * c, hpq, mul_ne_zero ha hc, ⟨u, k₁, k₂, k₃, k₄, fun i z hz => ?_, fun i => ?_⟩, ?_⟩
  · refine ((congrArg (valAt' _ _) (h₁ i)).trans (valAt'_mul _ _ _ _)).trans ?_
    rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
    refine (congrArg (a * ·) (k₅ i z hz)).trans ?_
    simp only [_root_.mul_assoc]
  · have k := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 k₆ (h₂ i)
    have e : ∑ j, N i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (N * M) i := by
      simp only [smul_comm (N i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
      rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum]
      rfl
    rwa [e] at k
  · rw [Matrix.det_mul, mul_pow, mul_pow, div_mul_div_comm]

theorem det_map_cast {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') {m n : ℕ} (e : m = n)
    (M : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun i j : Fin m => f (M (i.cast e) (j.cast e))).det = f M.det := by
  subst e
  exact (f.map_det M).symm

theorem known_change {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'} (a : Kˣ)
    (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ (a : K) * LB.Sec.f th i)
    (h : Known K ⟨P, hg, rig, hr, th, hth, v, hv⟩) : Known K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ := by
  obtain ⟨t₀, ht₀⟩ := h
  have := P.isAb.comm
  choose N hN using fun i => (hv'.2 (v i) (hv.1 i)).exists
  have hdet : IsUnit (Matrix.of N).det :=
    ((GlobalTheory.LieComb.lieComb_algebra K P.A P.g v' hv'.1).2.2.2.2 (Matrix.of N) v hv' hN).1 hv
  have h₁' : ∀ i, LB.Sec.f th i = constFn P.A.hom _ ((a⁻¹ : Kˣ) : K) * LB.Sec.f th' i := fun i => by
    rw [h₁, ← _root_.mul_assoc, ← KeyPow.constFn_mul, Units.inv_mul, KeyPow.constFn_one, _root_.one_mul]
  refine ⟨((Matrix.of N).det)⁻¹ ^ 4 / (a : K) ^ 8 * t₀, fun e x hx => ?_⟩
  obtain ⟨Q, hgQ, rigQ, hrQ, s, hs, u, hu⟩ := x
  obtain ⟨eg⟩ : Nonempty (Q.g = P.g) := by
    obtain ⟨_, _, _, hg, _⟩ := hx
    exact ⟨hg⟩
  have := Q.isAb.comm
  obtain ⟨ex, -, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ Q.A Q.g u hu.1
  let N' : Matrix (Fin Q.g) (Fin Q.g) ℂ := Matrix.of fun i j => e (Matrix.of N (i.cast eg) (j.cast eg))
  have hd : N'.det = e (Matrix.of N).det := det_map_cast e eg (Matrix.of N)
  choose u₀ hu₀ using fun i => (ex (N' i)).exists
  have hb₀ : IsLieBasis u₀ := (bas N' u₀ hu hu₀).2 (hd ▸ hdet.map e)
  choose M hM using fun i => (hb₀.2 (u i) (hu.1 i)).exists
  have hMN : Matrix.of M * N' = 1 := by
    funext i
    have k := (hu.2 (u i) (hu.1 i)).unique (comp _ (fun j => N' j) u₀ (M i) (u i) hu₀ (hM i)) (sgl i)
    rw [← Matrix.vecMul_eq_sum] at k
    refine k.trans ?_
    simpa using (smul_one_row (1 : ℂ) i).symm
  have hMd : (Matrix.of M).det = (e (Matrix.of N).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hd, ← Matrix.det_mul, hMN, Matrix.det_one]
  obtain ⟨s₀, e₀, e₁, hle⟩ := exists_sec_div Q.A.hom (a := e a) (b := e ((a⁻¹ : Kˣ) : K))
    (by rw [← map_mul, Units.mul_inv, map_one]) s
  have hs₀ : ∀ p : Sp ℂ, ∃ z : Q.A.left, Q.A.hom z = p ∧ z ∈ Out.nonzeroLocus s₀ :=
    fun p => (hs p).imp fun z hz => ⟨hz.1, hle hz.2⟩
  have hx₀ := KeyPBScale.keyPB_scale K ℂ e P hg rig hr th' hth' v' hv' th hth v hv _ (Matrix.of N) Q eg hgQ rigQ hrQ
    s hs u hu s₀ hs₀ u₀ hb₀ h₁' hN e₀ hu₀ hx
  have k := val_scale (hth' := hs) (hv' := hu) (N := Matrix.of M) ((map_ne_zero e).2 a.ne_zero) e₁ hM (ht₀ e _ hx₀)
  rw [hMd] at k
  rwa [map_mul, map_div₀, map_pow, map_pow, map_inv₀]

theorem known_of_keyPB {K : Type} [Field K] {y y' : KeyIn K} (h : KeyPB y' y (RingHom.id K)) (hy : Known K y) :
    Known K y' :=
  hy.imp fun _ ht e x hx => ht e x (keyPB_trans _ _ _ y y' x (RingHom.id K) e h hx)

theorem known_of_polPB : Out.Laws → ∀ (K : Type) [Field K] (y y' : KeyIn K) (φ : y'.P.A.left ⟶ y.P.A.left), PolPB y'.P y.P (𝟙 _) φ → Known K y → Known K y' := by
  intro hL K _ y y' φ ⟨h₁, h₂, h₃⟩ hy
  have e : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  obtain ⟨rig, hr, th, hth, v, hv, hz⟩ := KeyTf.exists_keyPB_on K K (RingHom.id K) y y'.P φ y'.g_pos h₂ (e ▸ h₁) h₃
  obtain ⟨a, t, ht, hta, hid⟩ := (KeyOnPol.main hL K).2 ⟨y'.P, y'.g_pos, rig, hr, th, hth, v, hv⟩
    y'.rig y'.rig_gen y'.th y'.th_ne y'.v y'.basis
  exact known_of_keyPB hid (known_change a hta (known_of_keyPB hz hy))

end GlobalTheory.KnownScale
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.continuousOn_thetaFrameValue_holomorphicFamily : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → ∀ (S : Type) [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (y : KeyIn S) (m : ℕ) (B : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (S →ₐ[ℂ] ℂ)) (t : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a : S, DifferentiableOn ℂ (fun p => s p a) B) → (∀ p ∈ B, ∃ x : KeyIn ℂ, KeyPB x y (s p).toRingHom ∧ (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t p = M.det ^ 4 / c ^ 8)) → ContinuousOn t B := by
  first | exact @GlobalTheory.ThetaValueCont.continuousOn_value | exact GlobalTheory.ThetaValueCont.continuousOn_value | (intros; apply GlobalTheory.ThetaValueCont.continuousOn_value <;> assumption)
end
