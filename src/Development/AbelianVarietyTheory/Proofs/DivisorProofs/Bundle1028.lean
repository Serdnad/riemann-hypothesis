module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle999
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.PairPM

theorem rootSum_zero {K : Type} [Field K] (θ : AlgebraicClosure K →* ℂ) (P : K[X]) :
    rootSum θ 0 P = (P.natDegree : ℂ) := by
  simp only [rootSum, pow_zero, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

theorem natCard_ext (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Nat.card F' = Nat.card F ^ Module.finrank F F' := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI := Fintype.ofFinite F; haveI := Fintype.ofFinite F'
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := F')]

theorem sum_cusp_eq_zero {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (m e : ℕ) (hm : 0 < m)
    (h : ∀ a, ¬ e * Nat.card K ^ a ≡ 0 [MOD Nat.card K ^ m - 1]) :
    ∑ᶠ x, cusp θ m e x = 0 := by
  have H := finsum_cusp_mul_star_chG K θ hθ m e 0 hm
  have hf : (Finset.range m).filter (fun i => e * Nat.card K ^ i ≡ 0 [MOD Nat.card K ^ m - 1]) = ∅ := by
    ext i; simp [h i]
  rw [hf] at H
  have hc : ∀ x : GL (Fin m) K, star (chG (rootSum θ 0) m x) = (m : ℂ) := by
    intro x; simp [chG, rootSum_zero, Matrix.charpoly_natDegree_eq_dim]
  simp only [hc, Finset.card_empty, Nat.cast_zero, mul_zero] at H
  rw [← finsum_mul] at H
  exact (mul_eq_zero.1 H).resolve_right (by exact_mod_cast hm.ne')

theorem gram_lift {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (q l m k : ℕ) (hq : 2 ≤ q)
    (hl : 0 < l) (hm : 0 < m) (hK : Nat.card K = q ^ l) (hreg : Reg q (l * m) k) :
    ∀ i j, i < l → j < l → ∑ᶠ x, cusp θ m (k * q ^ i) x * star (chG (rootSum θ (k * q ^ j)) m x) =
      if i = j then (((-1 : ℤ) ^ (m - 1) : ℤ) : ℂ) * (Nat.card (GL (Fin m) K) : ℂ) else 0 := by
  intro i j hi hj
  rw [finsum_cusp_mul_star_chG K θ hθ m _ _ hm, hK]
  have h3 := (reg_step_of_dvd q l m k hq hl hm hreg).2.2 i j
  have hf : (Finset.range m).filter (fun a => k * q ^ i * (q ^ l) ^ a ≡ k * q ^ j [MOD (q ^ l) ^ m - 1]) =
      if i = j then {0} else ∅ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ha, h⟩
      obtain ⟨rfl, rfl⟩ := (h3 a hi hj ha).1 h
      simp
    · intro h
      by_cases hij : i = j
      · rw [if_pos hij, Finset.mem_singleton] at h
        subst h; subst hij
        exact ⟨hm, (h3 0 hi hi hm).2 ⟨rfl, rfl⟩⟩
      · rw [if_neg hij] at h
        simp at h
  rw [hf]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

theorem hfree_J {K : Type} [Field K] [Finite K] (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) :
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card K) p.1 p.2 ∧
      (2 ≤ p.1 ∨ ¬ p.2 ≡ 0 [MOD Nat.card K - 1])) → HFree (J θ L (deg L))
  | [], _ => by intro h; simp [deg] at h
  | p :: L, hL => by
    have hp := hL p (List.mem_cons_self ..)
    have hL' : ∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card K) p.1 p.2 ∧
        (2 ≤ p.1 ∨ ¬ p.2 ≡ 0 [MOD Nat.card K - 1]) := fun p' h' => hL p' (List.mem_cons_of_mem _ h')
    rw [J_cons]
    have hdeg : deg (p :: L) = p.1 + deg L := by simp [deg]
    exact GlobalTheory.T.hyperplaneFixerSumVanishes_harishChandraInduction K p.1 (deg L) (deg (p :: L)) hdeg _ _
      (GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular K θ hθ p.1 p.2 hp.1 hp.2.1).1
      (GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular K θ hθ L (fun p' h' => ⟨(hL' p' h').1, (hL' p' h').2.1⟩) _ rfl)
      (GlobalTheory.T.hyperplaneFixerSumVanishes_cuspidalCharacterGLFiniteField K θ hθ p.1 p.2 hp.2.2) (hfree_J θ hθ L hL')

end GlobalTheory.Shin.PairPM

namespace GlobalTheory.Shin.PairPM

theorem pairing_pm_one : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k n : ℕ, 0 < m → n = Module.finrank F F' * m → Reg (Nat.card F) n k → ∃ z : ℤ, (z = 1 ∨ z = -1) ∧
    ∑ᶠ x, psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n x *
      star (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n x) = z * (Nat.card (GL (Fin n) F') : ℂ) := by
  intro F F' _ _ _ _ s hl _ ι θ hθ m k n hm hn hreg
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have hK : Nat.card F' = Nat.card F ^ Module.finrank F F' := natCard_ext F F'
  set l := Module.finrank F F' with hl_def
  set q := Nat.card F with hq_def
  have hq : 2 ≤ q := Finite.one_lt_card
  have hl0 : 0 < l := hl.pos
  have hl2 : 2 ≤ l := hl.two_le
  have hreg' : Reg q (l * m) k := hn ▸ hreg
  have hR := reg_step_of_dvd q l m k hq hl0 hm hreg'
  have hLL : liftL q l [(n, k)] = (List.range l).map (fun i => (m, k * q ^ i)) := by
    simp [liftL, hn, Nat.mul_div_cancel_left _ hl0]
  obtain ⟨hdeg, hmem⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [(n, k)] hq hl0 (by
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact ⟨by rw [hn]; exact Nat.mul_pos hl0 hm, by rw [hn]; exact dvd_mul_right _ _, hreg⟩)
  have hdeg' : deg (liftL q l [(n, k)]) = n := by rw [hdeg]; simp [deg]
  have hY := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ (liftL q l [(n, k)]) (fun p hp => by rw [hK]; exact hmem p hp) n hdeg'.symm
  have hF := hfree_J θ hθ (liftL q l [(n, k)]) (by
    intro p hp
    refine ⟨(hmem p hp).1, by rw [hK]; exact (hmem p hp).2, ?_⟩
    rw [hLL, List.mem_map] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases h2 : 2 ≤ m
    · exact Or.inl h2
    · right
      have h1 : m = 1 := by omega
      have := hR.2.1 (by nlinarith) i
      rw [h1, mul_one] at this
      rw [hK]
      exact this)
  rw [hdeg'] at hF
  refine ⟨((-1 : ℤ) ^ (m - 1)) ^ l, ?_, ?_⟩
  · rw [← pow_mul]
    exact neg_one_pow_eq_or ℤ _
  · rw [GlobalTheory.T.finsum_psiG_mul_star_eq_chG F' _ n _ hY hF]
    have hS : chG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n =
        chG (fun P => ∏ j ∈ Finset.range l, rootSum θ (k * q ^ j) P) n := by
      funext x
      simp only [chG]
      exact GlobalTheory.T.prod_rootPowerSum_map_galois_eq F F' θ k _
    rw [hS]
    have hZ := GlobalTheory.T.pairing_cuspidalCharacterGL_rootPowerSumCharacter F' θ m (fun i => k * q ^ i) ((-1) ^ (m - 1))
      (fun i => sum_cusp_eq_zero θ hθ m _ hm (by
        intro a
        rw [hK, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
        exact hR.2.1 (by nlinarith) _))
      l (gram_lift θ hθ q l m k hq hl0 hm hK hreg') (List.range l) (Finset.range l) List.nodup_range
      (fun i hi => List.mem_range.1 hi) (fun j hj => Finset.mem_range.1 hj) (by simp) n
      (by rw [hn, List.length_range, mul_comm])
    rw [List.toFinset_range, if_pos rfl, List.length_range, ← hLL] at hZ
    have hst : ∀ (a b : GL (Fin n) F' → ℂ), ∑ᶠ x, a x * star (b x) = star (∑ᶠ x, b x * star (a x)) := by
      intro a b
      rw [show star (∑ᶠ x, b x * star (a x)) = starAddEquiv (∑ᶠ x, b x * star (a x)) from rfl,
        map_finsum _ (Set.toFinite _)]
      refine finsum_congr fun x => ?_
      simp [star_mul]
    rw [hst, hZ]
    push_cast
    simp [star_pow]

end GlobalTheory.Shin.PairPM
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundle_frame_thin_affine_basis : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∃ (C : Type) (_ : Category.{0} C) (_ : Quiver.IsThin C) (G : C ⥤ AffOp X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, opOf G T')ˣ), IsBas (opOf G) ∧ IsFrame L (opOf G) (opOf_le G) u := by
  first | exact @GlobalTheory.LBFrameEx.exists_frame | exact GlobalTheory.LBFrameEx.exists_frame | (intros; apply GlobalTheory.LBFrameEx.exists_frame <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isLineBundleFrameOnBasis_restrict_finer_opens : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) (C' : Type) [Category.{0} C'] (V' : C' → X.Opens) (hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T) (H : C' ⥤ C) (hH : ∀ T, V' T ≤ V (H.obj T)), IsFrame L V hV u → IsFrame L V' hV' fun T T' a ↦ res (hH T') (u _ _ (H.map a)) := by
  first | exact @GlobalTheory.LBObs.isFrame_restrict | exact GlobalTheory.LBObs.isFrame_restrict | (intros; apply GlobalTheory.LBObs.isFrame_restrict <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isMultiplicativeOneCocycleOpens_of_isLineBundleFrameOnBasis : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → IsFrame L V hV u → IsCoc V hV u := by
  first | exact @GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame | exact GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame | (intros; apply GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_common_affine_refinement_along_morphism : ∀ (X Z : Scheme.{0}) (φ : Z ⟶ X) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp Z), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ (Pair φ)ᵒᵖ) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K ⋙ pairSnd φ) ∧ Nonempty (H' ⋙ G' ⟶ K ⋙ pairFst φ) ∧ IsBas (opOf (K ⋙ pairFst φ)) := by
  first | exact @GlobalTheory.LBObs.exists_pair_refine | exact GlobalTheory.LBObs.exists_pair_refine | (intros; apply GlobalTheory.LBObs.exists_pair_refine <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lifting_obstruction_eq_of_cohomologous_cocycles : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c := by
  first | exact @GlobalTheory.LBObs.isObU_of_cob | exact GlobalTheory.LBObs.isObU_of_cob | (intros; apply GlobalTheory.LBObs.isObU_of_cob <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.existsUnique_unit_ratio_generators_isomorphic_lineBundles : ∀ (X : Scheme.{0}) (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ) (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ), L.IsLB → L'.IsLB → w.IsGen → IsGenOn L W τ → IsGenOn L' W τ' → ∃! t : Γ(X, W)ˣ, ∀ (m : L.ι) (m' : L'.ι), res (inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W) t * res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m') = res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (w.s (m', m)) * res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) := by
  first | exact @GlobalTheory.GenRatio.exists_unique_ratio | exact GlobalTheory.GenRatio.exists_unique_ratio | (intros; apply GlobalTheory.GenRatio.exists_unique_ratio <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → IsCoc V hV u → ∀ T₁ T₂ : C, ∃! g : Γ(X, V T₁ ⊓ V T₂)ˣ, ∀ (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T), res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b := by
  first | exact @GlobalTheory.LBTrans.transition_units | exact GlobalTheory.LBTrans.transition_units | (intros; apply GlobalTheory.LBTrans.transition_units <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

theorem obAt_pairPull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (D : Type) [Category.{0} D] (K : D ⥤ (Pair f₀)ᵒᵖ), ObAt S α L (K ⋙ pairSnd f₀) ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).pull2 c) → ObAt S' α (L.pull f₀) (K ⋙ pairFst f₀) ((extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairPull h)).pull2 c)) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ s₀ t₀ S S' f₀ h l hl hn L c D _ K hob
  obtain ⟨u, hfr, hu⟩ := hob
  let n : CoefMap (RingHom.id R₀) ((K ⋙ pairSnd f₀) ⋙ OAff s₀) ((K ⋙ pairFst f₀) ⋙ OAff t₀) :=
    { G := 𝟭 D
      α := fun T ↦ (pairPull h).α (K.obj T)
      naturality := fun a b ↦ (pairPull h).naturality (K.map a) b
      smul := fun T r b ↦ (pairPull h).smul (K.obj T) r b }
  have hH : ∀ T : D, opOf (K ⋙ pairFst f₀) T ≤ f₀ ⁻¹ᵁ opOf (K ⋙ pairSnd f₀) ((𝟭 D).obj T) :=
    fun T ↦ (K.obj T).unop.2
  refine ⟨_, isFrame_pull X₀ D _ (opOf_le (K ⋙ pairSnd f₀)) L u Z₀ f₀ D _ (opOf_le (K ⋙ pairFst f₀)) (𝟭 D) hH hfr, ?_⟩
  have key : (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairPull h)).pull2 c) =
      (extMap R₁ n).pull2 ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).pull2 c) := by
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    have hy : ∀ (T : D) (y : R₁ ⊗[R₀] (OAff s₀).obj ((pairSnd f₀).obj (K.obj T))),
        (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).α T ((extMap R₁ (pairPull h)).α (K.obj T) y) =
          (extMap R₁ n).α T ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).α T y) := by
      intro T y
      induction y using TensorProduct.induction_on with
      | zero => repeat erw [map_zero]
      | tmul x y => rfl
      | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]
    rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
    congr 1
    apply Subtype.ext
    funext T T' T'' a b
    simp only [CoefMap.pullCocycleTwo_apply]
    exact hy T'' _
  rw [key]
  refine isObU_pull R R₀ I hI π hπ hk R₁ α D _ ((ofSys S).restrict (K ⋙ pairSnd f₀)) D _
    ((ofSys S').restrict (K ⋙ pairFst f₀)) n (fun T ↦ l (K.obj T)) u _ _
    (fun T b ↦ hl (K.obj T) b) (fun T T' a b ↦ hn (K.map a) b) ?_ hu
  intro T T' a
  change (Z₀.presheaf.map _).hom ((f₀.app _).hom _) = (f₀.appLE _ _ _).hom _
  rfl

end GlobalTheory.LBObs
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isLineBundleFrameOnBasis_lineBundleCechTensor : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsFrame L V hV u → IsFrame L' V hV u' → IsFrame (tens L L') V hV fun T T' a ↦ u T T' a * u' T T' a := by
  first | exact @GlobalTheory.LBObs.isFrame_tens | exact GlobalTheory.LBObs.isFrame_tens | (intros; apply GlobalTheory.LBObs.isFrame_tens <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObsZero

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

def PCh (P : S.Presents s i) (L : LB X) : Type :=
  {p : X₀.affineOpens × L.ι // GlobalTheory.PresCharts.chartOpen P (Opposite.op p.1) ≤ L.U p.2}

instance (P : S.Presents s i) (L : LB X) : Preorder (PCh P L) := Preorder.lift fun p ↦ OrderDual.toDual p.1.1.1

def pG (P : S.Presents s i) (L : LB X) : PCh P L ⥤ AffOp X₀ where
  obj p := Opposite.op p.1.1
  map a := (homOfLE (leOfHom a)).op

theorem isAffineOpen_chartOpen (P : S.Presents s i) (T : AffOp X₀) :
    IsAffineOpen (GlobalTheory.PresCharts.chartOpen P T) := by
  haveI := P.isOpen T
  unfold GlobalTheory.PresCharts.chartOpen
  exact isAffineOpen_opensRange _

def pH (P : S.Presents s i) (L : LB X) : PCh P L ⥤ GlobalTheory.LBObs.Model.Ch L where
  obj p := ⟨(⟨GlobalTheory.PresCharts.chartOpen P (Opposite.op p.1.1), isAffineOpen_chartOpen P _⟩, p.1.2), p.2⟩
  map {p q} a := homOfLE (GlobalTheory.PresCharts.chartOpen_le P ((pG P L).map a))

theorem isBas_pG (hI : I ^ 2 = 0) (P : S.Presents s i) {L : LB X} (hL : L.IsLB) : IsBas (opOf (pG P L)) := by
  have k : ∀ (x : X₀) (U : X₀.Opens), x ∈ U → ∃ t : PCh P L, x ∈ opOf (pG P L) t ∧ opOf (pG P L) t ≤ U :=
    fun x U hx ↦ by
      obtain ⟨m, hm⟩ := LB.mem_of_cover hL (i x)
      obtain ⟨_, ⟨W, hW, rfl⟩, h1, h2⟩ :=
        X₀.isBasis_affineOpens.exists_subset_of_mem_open
          (show x ∈ ((U ⊓ i ⁻¹ᵁ L.U m : X₀.Opens) : Set X₀) from ⟨hx, hm⟩) (U ⊓ i ⁻¹ᵁ L.U m).isOpen
      refine ⟨⟨(⟨W, hW⟩, m), fun y hy ↦ ?_⟩, h1, fun y hy ↦ (h2 hy).1⟩
      obtain ⟨y₀, hy₀, rfl⟩ := GlobalTheory.PresCharts.exists_of_mem_chartOpen hI P _ y hy
      exact (h2 hy₀).2
  refine ⟨k, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  obtain ⟨t, h1, h2⟩ := k x (opOf (pG P L) t₁ ⊓ opOf (pG P L) t₂ ⊓ U) ⟨⟨h₁, h₂⟩, hx⟩
  exact ⟨t, ⟨homOfLE (h2.trans (inf_le_left.trans inf_le_left))⟩, ⟨homOfLE (h2.trans (inf_le_left.trans inf_le_right))⟩,
    h1, h2.trans inf_le_right⟩

end GlobalTheory.LBObsZero


open GlobalTheory.LBObsZero in
theorem GlobalTheory.LBObs.isObL_pull_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L : LB X), IsPullback i s₀ s (spMap π) → L.IsLB → IsObL S α (L.pull i) 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S X s i P L h hL
  have hH : ∀ T : PCh P L, opOf (pG P L) T ≤ i ⁻¹ᵁ opOf (GlobalTheory.LBObs.Model.chG L) ((pH P L).obj T) :=
    fun T ↦ GlobalTheory.PresCharts.le_preimage_chartOpen P _
  let w : ∀ (T T' : GlobalTheory.LBObs.Model.Ch L) (_ : T ⟶ T'), Γ(X, opOf (GlobalTheory.LBObs.Model.chG L) T')ˣ :=
    fun T T' a ↦ res (le_inf T'.2 ((opOf_le (GlobalTheory.LBObs.Model.chG L) a).trans T.2)) (L.g T'.1.2 T.1.2)
  have hw : IsFrame L _ _ w := GlobalTheory.LBObs.Model.isFrame_ch hL
  have hfr := isFrame_pull X _ _ _ L w X₀ i (PCh P L) (opOf (pG P L)) (opOf_le (pG P L)) (pH P L) hH hw
  have hcoc := GlobalTheory.LBObs.Model.isCoc_of_isFrame hL hw
  choose σ hσ using fun (T : PCh P L) ↦ GlobalTheory.Obs.Model.exists_isSig hI hπ α (((ofSys S).restrict (pG P L)).p T)
    (Pre.semi _ T) (Pre.surj _ T) (Pre.ker _ T)
  refine ⟨PCh P L, inferInstance, inferInstance, pG P L, isBas_pG hI P hL, _, hfr, ?_⟩
  rw [map_zero]
  refine ⟨fun T T' a ↦ Units.map (GlobalTheory.PresCharts.chartSec P ((pG P L).obj T')).hom.toMonoidHom (w _ _ ((pH P L).map a)),
    σ, 0, fun T T' a ↦ ?_, hσ, (map_zero _).symm, fun T T' T'' a b ↦ ⟨map_zero _, ?_⟩⟩
  · have := congrArg (fun f ↦ f.hom (w _ _ ((pH P L).map a)).val)
      (GlobalTheory.PresCharts.appLE_chartSec P ((pG P L).obj T') (hH T'))
    exact this.symm
  · have e0 : (0 : Z2 (ext R₁ ((pG P L) ⋙ OAff s₀))).1 T T' T'' a b = 0 := rfl
    rw [e0, map_zero, add_zero, _root_.one_mul]
    have e1 := hcoc ((pH P L).map a) ((pH P L).map b)
    rw [← Functor.map_comp] at e1
    have e2 := congrArg (fun f ↦ f.hom (w _ _ ((pH P L).map a)).val)
      (GlobalTheory.PresCharts.res_chartSec P ((pG P L).map b))
    show (mp S.F ((pG P L).map b)) ((GlobalTheory.PresCharts.chartSec P ((pG P L).obj T')).hom (w _ _ ((pH P L).map a)).val) *
        (GlobalTheory.PresCharts.chartSec P ((pG P L).obj T'')).hom (w _ _ ((pH P L).map b)).val =
      (GlobalTheory.PresCharts.chartSec P ((pG P L).obj T'')).hom (w _ _ ((pH P L).map (a ≫ b))).val
    rw [e1, Units.val_mul]
    erw [map_mul]
    congr 1
    exact e2.symm

end
end

section

open GlobalTheory GlobalTheory.LogDR


theorem _root_.GlobalTheory.T.logDifferential_mul_logCoordinateWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n) (I : Finset (Fin n)), (i ∈ I → ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = 0) ∧ (i ∉ I → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = ε • logWedge x (insert i I)) := by
  first | exact @GlobalTheory.LogDR.dlog_mul_logWedge | exact GlobalTheory.LogDR.dlog_mul_logWedge | (intros; apply GlobalTheory.LogDR.dlog_mul_logWedge <;> assumption)
end
