module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle117
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle176
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle177
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle074
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem ThetaFam.unram_of_mono {o : Type} [CommRing o] {g n N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} (F : ThetaFam n em C) {S : Scheme.{0}} (x : S ⟶ F.MM) [Mono x]
    {s : S ⟶ Sp o} (hs : x ≫ F.s = s) (t : TObj g (N' ^ 2) J b s) (ht : TMap t F.univ x) (K : Type) [Field K]
    (y : Sp (DualNumber K) ⟶ S) (t' : TObj g (N' ^ 2) J b (y ≫ s)) (hy : y ≫ s = constPt y ≫ s)
    (h₁ : TMap t' t y) (h₂ : TMap t' t (constPt y)) : y = constPt y := by
  subst hs
  have hc : constPt (y ≫ x) = constPt y ≫ x := by simp [constPt]
  rw [← cancel_mono x, ← hc]
  have key : ∀ (s' : Sp (DualNumber K) ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s'), s' = (y ≫ x) ≫ F.s →
      TMap t' F.univ (y ≫ x) → TMap t' F.univ (constPt (y ≫ x)) → y ≫ x = constPt (y ≫ x) := by
    rintro _ t' rfl h h'
    exact F.unram K (y ≫ x) t' (by rw [hc, Category.assoc, Category.assoc, hy]) h h'
  refine key _ t' (Category.assoc _ _ _).symm ?_ ?_
  · exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t t').2 x y ht).1 h₁
  · rw [hc]
    exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t t').2 x (constPt y) ht).1 h₂

theorem exists_thetaFam_isPEL_smooth : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∃ (F : ThetaFam n em (PELClass (b := b) D a bas ρ em)) (τ : SAB H F.MM), IsPEL D a bas ρ F.univ τ ∧ SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  intro h1 h2 hcrit hgen hU E _ _ _ H D g J _ a w w' bas hD hbas hw hw' ha n hn hodd
  obtain ⟨Mat, κ, hcl⟩ := GlobalTheory.T.isGoodThetaComplexClass_unitaryFullLevel h1 h2 hgen hU E H D g J a w w' bas hD hbas hw hw' ha
  obtain ⟨j₁, hj₁⟩ := hcl n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.nonempty_thetaObject_family_open_closure h1 h2 hcrit g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em ρ hρ hb => ?_⟩
  have hgood := hj₁ j (le_of_max_le_left hj) _ rfl o b em ρ hρ
  obtain ⟨F⟩ := hj₂ j (le_of_max_le_right hj) o b em _ _ hb hgood
  obtain ⟨τ, hτ⟩ := GlobalTheory.thetaFam_isPEL h1 h2 hgen E H D g J a w w' bas hD hbas hw hw' ha n _ o b em ρ hρ hb F
  refine ⟨F, τ, hτ, ThetaFam.smooth_genericFibre h1 h2 g n _ J Mat κ w w' o b em _ _ F hb hgood ?_⟩
  intro R _ _ _ _ _ x hx hs hem
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull o g _ J b _ _ F.s _ x F.univ hs
  obtain ⟨τ', hτ'⟩ := GlobalTheory.PELPull.isPEL_pull E H D g _ J a bas o b ρ _ _ F.s _ x F.univ t τ hs ht hτ
  have hρ2 : ρ ^ 2 = -(H.d : o) := hb.2.2 (by rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast])
  have hft : Algebra.FiniteType o R := by
    have := ((GlobalTheory.isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB F.s).1 F.qproj).1
    have h : LocallyOfFiniteType (spMap (algebraMap o R)) := hs ▸ inferInstance
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h)
  exact GlobalTheory.T.finrank_tangent_PEL_family_le_symmetricDomain h1 h2 hgen hU E H D g J a w w' bas hD hbas hw hw' ha _ o b ρ R t τ' hρ2 hτ' hft
    (fun y t' hy h₁ h₂ => F.unram_of_mono x hs t ht ℂ y t' hy h₁ h₂)

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelLargeLevel

theorem isAlgebraic_of_mem_ZP {p M : ℕ} (hM : M ≠ 0) {x : ℂ} (hx : x ∈ ZP p M) : IsAlgebraic ℤ x := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ, ← mem_algebraicClosure_iff]
  have hle : ZP p M ≤ (algebraicClosure ℚ ℂ).toSubalgebra.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (rfl | ⟨n, -, rfl⟩)
    · have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
      exact mem_algebraicClosure_iff.2
        (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hM) (h1 ▸ isAlgebraic_one))
    · exact (algebraicClosure ℚ ℂ).inv_mem (natCast_mem _ n)
  exact hle hx

theorem exists_siegelFamily_sRep : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h n : ℕ), 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → n ≠ p → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SRep Ag := by
  intro L L2 hθ hU h n hh hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.nonempty_siegelFamily_over_arithmetic_base L L2 hθ hU h n hh hn hodd
  refine ⟨max j₀ 1, fun j hj p hp hnp => ?_⟩
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  obtain ⟨o, _, b, em, i, hem, hζ, hi, hconst⟩ :=
    GlobalTheory.ZM.CycBase.exists_base n (j * 2) p ((n ^ j) ^ 2) hn hp hnp (by omega) (pow_mul n j 2).symm
  obtain ⟨F⟩ := hj₀ j (le_trans (le_max_left _ _) hj) o b em hem
  have h3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨m, rfl⟩
    omega
  have hk : 3 ≤ (n ^ j) ^ 2 := by
    rw [← pow_mul]
    exact h3.trans (Nat.le_self_pow (by omega) n)
  have hinj : Function.Injective i := fun x y hxy => hem.2.2 (by rw [← hi, ← hi, hxy])
  have halg : Algebra.IsAlgebraic ℤ o := ⟨fun x => by
    have hx : IsAlgebraic ℤ (em.toIntAlgHom x) := by
      change IsAlgebraic ℤ (em x)
      rw [← hi]
      exact isAlgebraic_of_mem_ZP (by omega) (i x).2
    exact (isAlgebraic_algHom_iff em.toIntAlgHom hem.2.2).1 hx⟩
  exact GlobalTheory.T.exists_siegelFamily_localised_cyclotomic_integers L L2 h _ p o _ i (hodd.pow.pow) hk hp hinj hζ hconst halg F

end GlobalTheory.ZM.SiegelLargeLevel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory

theorem exists_zon_ampFrames_component :
    Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1 := by
  intro h1 h2 hss hU hT hG E _ _ _ H g n hn ho
  obtain ⟨k, j₀, hk⟩ := GlobalTheory.exists_big_thetaSys_with_action h1 h2 E H g n hn ho
  refine ⟨k, j₀, ?_⟩
  intro j hj o Ω _ _ _ _ R J b u t₀ e v hR hfr he hL hth hfin
  obtain ⟨S, ρ, h, φ, act, hbig, hN, hfin', hcart, hLφ, hact, hadj, hprim⟩ :=
    hk j hj o Ω R J b u t₀ e v hR hfr he hL hth hfin
  have htests : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hss hU h1 h2 hT o Ω S ρ).1
  obtain ⟨m, a, GG, X, Z, U₀, EE, f, Xab, -, -, hNm, hO, hEE, -, -, -, hgen, hlast⟩ :=
    GlobalTheory.ZH.exists_minor_model o Ω S htests hfin'
  obtain ⟨Y⟩ := hG o Ω S ρ hbig Z U₀ EE hO hEE ⟨m, a, GG, hgen⟩
  have hopen : IsOpen (abLocus Y.G) := by
    rw [Y.ab]
    exact GlobalTheory.isOpen_setOf_TT_eq_bot o Ω S Z _ _ _ hO.div (fun z x₀ hx => (hlast z x₀ hx).2)
  obtain ⟨r₀, hr⟩ := GlobalTheory.exists_ampFrames_exponents h1 o Ω S ρ Z U₀ EE m a GG Y hNm hO hgen
  rw [hN] at hr
  exact GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames h1 h2 E H o Ω R t₀ S ρ h φ act Z U₀ EE Y (n ^ k) r₀ hR hfr hO hopen hcart hLφ
    hact hadj hprim hr

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelUniversal

theorem isAlgebraic_of_injective {p M : ℕ} (hM : M ≠ 0) {o : Type} [CommRing o] (i : o →+* ZP p M)
    (hi : Function.Injective i) : Algebra.IsAlgebraic ℤ o := by
  have hle : ZP p M ≤ (algebraicClosure ℚ ℂ).toSubalgebra.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (rfl | ⟨n, -, rfl⟩)
    · have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
      exact mem_algebraicClosure_iff.2
        (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hM) (h1 ▸ isAlgebraic_one))
    · exact (algebraicClosure ℚ ℂ).inv_mem (natCast_mem _ n)
  refine ⟨fun x => ?_⟩
  rw [← isAlgebraic_algHom_iff ((ZP p M).subtype.comp i).toIntAlgHom (Subtype.val_injective.comp hi),
    IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ, ← mem_algebraicClosure_iff]
  exact hle (i x).2

theorem exists_siegelFamily_siegRep : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ h n : ℕ, 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SiegRep Ag := by
  intro L L2 hθ hU h n hh hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.nonempty_siegelFamily_over_arithmetic_base L L2 hθ hU h n hh hn hodd
  refine ⟨max j₀ 1, fun j hj p hp hnp => ?_⟩
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  obtain ⟨o, _, b, em, i, hem, hζ, hi, hconst⟩ :=
    GlobalTheory.ZM.CycBase.exists_base n (j * 2) p ((n ^ j) ^ 2) hn hp hnp.symm (by omega) (pow_mul n j 2).symm
  obtain ⟨F⟩ := hj₀ j (le_trans (le_max_left _ _) hj) o b em hem
  have h3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨m, rfl⟩
    omega
  have hk : 3 ≤ (n ^ j) ^ 2 := by
    rw [← pow_mul]
    exact h3.trans (Nat.le_self_pow (by omega) n)
  have hinj : Function.Injective i := fun x y hxy => hem.2.2 (by rw [← hi, ← hi, hxy])
  obtain ⟨Ag, hAg⟩ := GlobalTheory.T.exists_siegelFamily_localised_cyclotomic_integers L L2 h _ p o _ i (hodd.pow.pow) hk hp hinj hζ hconst
    (isAlgebraic_of_injective (by omega) i hinj) F
  obtain ⟨F', -⟩ := F.exists_baseChange i hinj hζ
  obtain ⟨Ag', -, H⟩ := F'.exists_sRep_siegRep (by omega) Ag hAg
  exact ⟨Ag', H⟩

end GlobalTheory.ZM.SiegelUniversal
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Moduli

theorem siegelFamilies_closed : N0 :=
  GlobalTheory.T.exists_siegelFamily_localisation_prime_power_level GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.theorem_of_cube_polAbelianScheme GlobalTheory.T.theta_uniformisation_complex_abelian_varieties

end GlobalTheory.Moduli
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem moduli_nonempty_all_levels : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N1ab := by
  intro h1 h2 h3 h4 E _ _ _ H D l hD
  obtain ⟨n, hn, hodd, hl⟩ := GlobalTheory.T.exists_level_with_odd_prime_first_number E H l
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_moduli_prime_power_fullLevel h1 h2 h3 h4 E H D n hD hn hodd
  obtain ⟨l₀, l₂, hM, hA, h02, h2'⟩ := hl ((n ^ j) ^ 2) (pow_pos (pow_pos hn.pos j) 2)
  exact GlobalTheory.T.nonempty_cmModuli_of_deeper_level h1 h2 h3 E H D l l₂ hD h2'
    (GlobalTheory.T.nonempty_moduli_of_level_dvd h1 h2 E H D l₀ l₂ hD h02 (hj l₀ hM hA))

end GlobalTheory.ZM
end
