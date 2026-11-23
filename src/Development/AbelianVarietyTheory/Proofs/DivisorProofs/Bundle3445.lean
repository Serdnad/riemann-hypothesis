module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep



theorem exists_system_with_traits_and_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (M : Scheme.{0}) (_ : IsIntegral M) (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] ((n ^ j) ^ 2) (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty ∧ j₀ ≤ j ∧ IsCov C g z₁ ζ ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U ∧ IsMember ζ Φ Cm ξ y ρ e h := by
  intro E _ _ _ H Dw hpq l Xo c C φ V _ _ _ Cm hV ξ hξ n hn hodd j₀
  obtain ⟨j, X₁, π, z₁, ζ, hdom, U, Φ, y, ρ, e, h, c₀, hj, hcov, hU, hT, hM, hunit, hm1, hE, hCS⟩ :=
    GlobalTheory.T.exists_unitary_fourier_system_traits_chart E H Dw hpq l Xo c C φ V Cm hV ξ hξ n hn hodd (max j₀ 1)
  obtain ⟨-, -, hIC, -⟩ := GlobalTheory.T.modelStalk_normal_noetherian_fractionRing X₁ z₁
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hN : 3 ≤ (n ^ j) ^ 2 := by
    have h3 : 3 ≤ n := by
      rcases hodd with ⟨k, hk⟩
      have := hn.two_le
      omega
    have h2 : 3 ≤ n ^ j := le_trans h3 (Nat.le_self_pow (by omega) n)
    nlinarith
  have hLam : Φ.abelian₂ := GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) (by norm_num) hN hE
  have hFour : Φ.Four ((n ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_of_galois_class_sums (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hCS
  let v : ∀ y', (Φ.V y')ˣ := fun y' => (hunit y').unit⁻¹
  have happ : ∀ e' : ℕ, ∃ a : X₁.M.Z.presheaf.stalk z₁, ∀ y', Φ.ev y' a - ((v y')⁻¹ : (Φ.V y')ˣ) ∈
      (maximalIdeal (X₁.M.Z.presheaf.stalk z₁) ^ e').map (Φ.ev y') := by
    intro e'
    obtain ⟨a, ha⟩ := GlobalTheory.T.fourierTermSystem_indexZero_coefficient_approx (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hN hE hLam hFour
      (fun y₁ y₂ h₁ h₂ => (hm1 y₁ h₁).trans (hm1 y₂ h₂).symm) c₀ e'
    refine ⟨a, fun y' => ?_⟩
    simpa [v] using ha y'
  have hFour' : (Φ.rescale v).Four ((n ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_rescale_approximated_units (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hFour v happ
  have hLam' : (Φ.rescale v).abelian₂ := hLam
  refine ⟨j, X₁.M.Z, inferInstance, π, z₁, ζ, (Φ.rescale v).toVSys ((n ^ j) ^ 2) hLam' hFour', y, ρ, e, h, U, hU,
    le_trans (le_max_left _ _) hj, hcov, hT, ?_⟩
  obtain ⟨h1, h2, h3, h4, D, p, hT0⟩ := hM
  refine ⟨h1, h2, h3, h4, D, p, ?_⟩
  have h0 : Φ.term y (fun _ => e.symm 0) c₀ * ((v y : (Φ.V y)ˣ) : Φ.V y) = 1 := by
    have hz : (fun _ : Fin 1 => e.symm 0) = 0 := by
      funext a; simp
    rw [hz]
    simp [VPre.term, mono, qW, v]
  have := GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one (Φ.V y) D ((n ^ j) ^ 2) _ Φ.Q p.xe.symm
    (fun mu c => Φ.term y (fun _ => e.symm mu) c) (v y) c₀ hT0 h0
  refine cast (congrArg (fun T => GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) p.xe.symm T) ?_) this
  funext mu c
  show Φ.u y (fun _ => e.symm mu) c * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu) * ((v y : (Φ.V y)ˣ) : Φ.V y) =
    Φ.u y (fun _ => e.symm mu) c * ((v y : (Φ.V y)ˣ) : Φ.V y) * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu)
  exact mul_right_comm _ _ _

end GlobalTheory.USep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.FirstOrderSiegel

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

variable {h k : ℕ}

theorem isLocalRing_tsze (K : Type) [Field K] (r : ℕ) : IsLocalRing (TrivSqZeroExt K (Fin r → K)) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isArtinianRing_tsze (K : Type) [Field K] (r : ℕ) : IsArtinianRing (TrivSqZeroExt K (Fin r → K)) :=
  haveI : Module.Finite K (TrivSqZeroExt K (Fin r → K)) := inferInstanceAs (Module.Finite K (K × (Fin r → K)))
  IsArtinianRing.of_finite K _

theorem pull_exists {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (f : S' ⟶ S) (hf : f ≫ s = s') (c : SiegPre h k ζ s) :
    ∃ c' : SiegPre h k ζ s', SiegPB c' c f ∧ (c.Principal → c'.Principal) := by
  have e : f ≫ s = s' ≫ spMap (RingHom.id B) := by
    rw [hf]
    simp [spMap]
  have H := siegPre_pull_ringChange h k B B ζ ζ (RingHom.id B) S S' s s' f rfl e
  obtain ⟨c', hc'⟩ := H.1 c
  exact ⟨c', hc', H.2.1 c c' hc'⟩

theorem pb_symm {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}} {s : S ⟶ Sp B}
    {s' : S ⟶ Sp B'} {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} (m : SiegPB c' c (𝟙 S)) : SiegPB c c' (𝟙 S) :=
  pb_cancel m (by rw [Category.comp_id]; exact pb_id c)

theorem constPt_comp {K : Type} [Field K] {X Y : Scheme.{0}} (x : Sp (DualNumber K) ⟶ X) (z : X ⟶ Y) :
    constPt (x ≫ z) = constPt x ≫ z := by
  unfold constPt
  simp only [Category.assoc]

theorem base_map {K o V W : Type} [Field K] [CommRing o] [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W] (β : o →+* K)
    (L : V →ₗ[K] W) : spMap (TrivSqZeroExt.map L).toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K V)).comp β) =
      spMap ((algebraMap K (TrivSqZeroExt K W)).comp β) := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun z => (TrivSqZeroExt.map L).commutes (β z)

theorem fst_base {K o V : Type} [Field K] [CommRing o] [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] (β : o →+* K) :
    spMap (TrivSqZeroExt.fstHom K K V).toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K V)).comp β) = spMap β := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun z => (TrivSqZeroExt.fstHom K K V).commutes (β z)

theorem constPt_base {K o : Type} [Field K] [CommRing o] {X : Scheme.{0}} (β : o →+* K) (x : Sp (DualNumber K) ⟶ X)
    (s : X ⟶ Sp o) (hx : x ≫ s = spMap ((algebraMap K (DualNumber K)).comp β)) :
    constPt x ≫ s = x ≫ s := by
  unfold constPt
  rw [Category.assoc, Category.assoc, hx, fst_base, ← spMap_comp']

theorem dirMap_comp {K : Type} [Field K] {r m : ℕ} (mu : (Fin m → K) →ₗ[K] K) (L : (Fin r → K) →ₗ[K] (Fin m → K)) :
    spMap (dirMap (mu ∘ₗ L)) = spMap (dirMap mu) ≫ spMap (TrivSqZeroExt.map L).toRingHom := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dirMap]) (by simp [dirMap])

def drop (K : Type) [Field K] (d : ℕ) : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) := GlobalTheory.InnerAutomorphism.dropLast K d

def lastC (K : Type) [Field K] (d : ℕ) : (Fin (d + 1) → K) →ₗ[K] K := LinearMap.proj (Fin.last d)

def incl (K : Type) [Field K] (d : ℕ) : (Fin d → K) →ₗ[K] (Fin (d + 1) → K) where
  toFun w := Fin.snoc w 0
  map_add' w w' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' a w := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem bij_drop_last (K : Type) [Field K] (d : ℕ) : Function.Bijective ((drop K d).prod (lastC K d)) := by
  refine ⟨fun v w hvw => ?_, fun p => ⟨Fin.snoc p.1 p.2, ?_⟩⟩
  · have h1 := congrArg Prod.fst hvw
    have h2 := congrArg Prod.snd hvw
    simp only [LinearMap.prod_apply] at h1 h2
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h2
    · exact congrFun h1 j
  · ext j <;> simp [drop, lastC, GlobalTheory.InnerAutomorphism.dropLast]

theorem lam_decomp (K : Type) [Field K] (d : ℕ) (lam : (Fin (d + 1) → K) →ₗ[K] K) :
    lam = (lam ∘ₗ incl K d) ∘ₗ drop K d + lam (Pi.single (Fin.last d) 1) • lastC K d := by
  refine LinearMap.ext fun v => ?_
  have hv : v = incl K d (drop K d v) + v (Fin.last d) • Pi.single (Fin.last d) 1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [incl]
    · simp [incl, drop, GlobalTheory.InnerAutomorphism.dropLast, Pi.single_apply, Fin.castSucc_ne_last]
  conv_lhs => rw [hv]
  simp [lastC, mul_comm]

theorem classified_dualNumber_of_algClosed : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β₀ : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ _ β₀ c hc

  obtain ⟨c₀, hc₀, hc₀p⟩ := pull_exists (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (fst_base β₀) c
  obtain ⟨x₀, hx₀s, hx₀⟩ := GlobalTheory.T.siegel_family_classifies_principal_algClosed g n hg hn hodd F K β₀ c₀ (hc₀p hc)

  obtain ⟨y, hy₀, hys, hyinj⟩ := GlobalTheory.T.exists_firstOrder_tangentPoint_smooth F.X F.s (g * (g + 1) / 2) F.smooth K β₀ x₀ hx₀s
  obtain ⟨cy, hcy, hcyp⟩ := pull_exists y hys F.univ
  have h0y : SiegPB c₀ cy (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) :=
    pb_cancel hcy (by rw [hy₀]; exact hx₀)

  have hsq := GlobalTheory.T.trivial_square_zero_extension_pullback K (Fin (g * (g + 1) / 2 + 1) → K) (Fin (g * (g + 1) / 2) → K) K (drop K _) (lastC K _)
    (bij_drop_last K _)
  let β : CommRingCat.of (cycAway n) ⟶ CommRingCat.of (TrivSqZeroExt K (Fin (g * (g + 1) / 2 + 1) → K)) :=
    CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K (Fin (g * (g + 1) / 2 + 1) → K))).comp β₀)
  obtain ⟨c₁, hc₁, hc₁p⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by rw [Category.id_comp]; exact (base_map β₀ _).symm) cy
  obtain ⟨c₂, hc₂, hc₂p⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (lastC K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by rw [Category.id_comp]; exact (base_map β₀ _).symm) c
  obtain ⟨c₀', hc₀', -⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by
      rw [Category.id_comp]
      exact ((congrArg (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom ≫ ·)
        (base_map β₀ (drop K _))).trans (fst_base β₀)).symm) c₀
  have h01 : SiegPB c₀' c₁ (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) := by
    have := pb_comp (pb_comp (pb_symm hc₁) h0y) hc₀'
    rwa [Category.comp_id, Category.id_comp] at this
  have h02 : SiegPB c₀' c₂ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    have := pb_comp (pb_comp (pb_symm hc₂) hc₀) hc₀'
    rwa [Category.comp_id, Category.id_comp] at this
  obtain ⟨G, hGp, hG1, hG2⟩ := GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct g n hn hodd _ _ (CommRingCat.of (DualNumber K)) (CommRingCat.of K) _ _ _ _
    hsq (isLocalRing_tsze K _) (isArtinianRing_tsze K _) (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) β c₁ c₂ (hc₁p (hcyp F.princ)) (hc₂p hc) ⟨c₀', h01, h02⟩
  have hGy : SiegPB cy G (spMap (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) := by
    have := pb_comp hG1 (pb_symm hc₁)
    rwa [Category.id_comp] at this
  have hGc : SiegPB c G (spMap (dirMap (lastC K (g * (g + 1) / 2)))) := by
    have := pb_comp hG2 (pb_symm hc₂)
    rwa [Category.id_comp] at this

  have htb := GlobalTheory.T.siegelFamily_tangentBound_nonconstant g n hg hn hodd K (g * (g + 1) / 2 + 1) β₀ G hGp
  obtain ⟨lam, c', h1, h2, hlam⟩ : ∃ (lam : (Fin (g * (g + 1) / 2 + 1) → K) →ₗ[K] K)
      (c' : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))),
      SiegPB c' G (spMap (dirMap lam)) ∧ SiegPB c' G (constPt (spMap (dirMap lam))) ∧ lam ≠ 0 := by
    by_contra hne
    push_neg at hne
    have := htb fun lam c' h1 h2 => hne lam c' h1 h2
    omega
  obtain ⟨mu, a, hdec⟩ : ∃ (mu : (Fin (g * (g + 1) / 2) → K) →ₗ[K] K) (a : K),
      lam = mu ∘ₗ drop K _ + a • lastC K _ := ⟨_, _, lam_decomp K _ lam⟩
  by_cases ha : a = 0
  ·
    exfalso
    rw [ha, zero_smul, add_zero] at hdec
    subst hdec
    rw [dirMap_comp] at h1 h2
    rw [constPt_comp] at h2
    have k1 : SiegPB c' F.univ (spMap (dirMap mu) ≫ y) := pb_comp hcy (pb_cancel hGy h1)
    have k2 : SiegPB c' F.univ (constPt (spMap (dirMap mu) ≫ y)) := by
      rw [constPt_comp]
      exact pb_comp hcy (pb_cancel hGy h2)
    have hxs : (spMap (dirMap mu) ≫ y) ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) := by
      rw [Category.assoc, hys]
      exact base_map β₀ mu
    obtain ⟨c'', hc'', -⟩ := pull_exists (𝟙 _) (s' := (spMap (dirMap mu) ≫ y) ≫ F.s)
      (by rw [Category.id_comp, hxs]) c'
    have e := F.eq_constPt K (spMap (dirMap mu) ≫ y) c'' (constPt_base β₀ _ _ hxs).symm
      (by have := pb_comp k1 hc''; rwa [Category.id_comp] at this)
      (by have := pb_comp k2 hc''; rwa [Category.id_comp] at this)
    have := hyinj mu e
    subst this
    exact hlam (by simp)
  ·
    have hκ : lastC K (g * (g + 1) / 2) = ((-a⁻¹) • mu) ∘ₗ drop K _ + a⁻¹ • lam := by
      rw [hdec]
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, neg_mul]
      field_simp
      ring
    have k := GlobalTheory.T.siegelObject_tangentShift_constancy_direction_iso g n hn hodd K _ β₀ G hGp lam _ _ a⁻¹ c' c hκ h1 h2 hGc
    rw [dirMap_comp] at k
    refine ⟨spMap (dirMap ((-a⁻¹) • mu)) ≫ y, ?_, pb_comp hcy (pb_cancel hGy k)⟩
    rw [Category.assoc, hys]
    exact base_map β₀ _

end GlobalTheory.FirstOrderSiegel

end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem relRep_htPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (Z : Scheme.{0}) (π : Z ⟶ S) (u : Obj b N (π ≫ t)) (φu : u.A.left ⟶ c.A.left) (φ₂u : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A c.A π φu ∧ IsSquare φu φ₂u ∧ LBIso u.P (c.P.pull φ₂u) ∧ IsFinite π ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (t' : T ⟶ Sp R) (o : Obj b N t') (φ : o.A.left ⟶ c.A.left) (φ₂ : (G2 o.A).left ⟶ (G2 c.A).left), g ≫ t = t' → IsGrpPullback o.A c.A g φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → ∃! z : T ⟶ Z, z ≫ π = g ∧ ∃ m : ObjMap o u z, m.φ ≫ φu = φ := by
  intro p _ D R _ b N hN hNp h M B _ ζ S _ s₁ t c e he hc
  obtain ⟨E, πE, AE, _, _, φE, φ₂E, actE, ηE, hEn, hEf, pbE, sqE, rosE, etaE, univE⟩ :=
    GlobalTheory.T.exists_rep_adjointAction_level_siegelPullback p D R b N hNp h M B ζ S s₁ t c e he hc
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.harrisTaylor_lie_tate_loci_closed_siegelPullback p D R b N hN hNp h M B ζ S s₁ t c e he hc E πE AE φE φ₂E actE ηE
    pbE sqE rosE etaE
  have hZj := (hZ Z j).1 ⟨𝟙 Z, Category.id_comp _⟩
  obtain ⟨u, ψ, ψ₂, pbu, squ, isou, actu, etau⟩ := GlobalTheory.T.exists_harrisTaylorObject_over_lieTate_locus p D R b N hN hNp h M B ζ S s₁ t c e he hc E πE AE
    φE φ₂E actE ηE pbE sqE rosE etaE Z j hZj.1 hZj.2
  haveI : IsFinite πE := hEf
  haveI : Mono j := inferInstance
  refine ⟨Z, j ≫ πE, u, ψ ≫ φE, ψ₂, pbu.comp pbE, squ, isou, inferInstance, ?_⟩
  intro T g t' o φ φ₂ hgt pbo sqo isoo
  have rosO : RosatiFor D o.act (c.P.pull φ₂) :=
    RosatiFor.of_iso o.isLB (pull_isLB c.isLB _) isoo o.rosatiFor
  obtain ⟨z₀, ⟨hz₀, ψ₀, pb₀, hψ₀, act₀, eta₀⟩, uniq₀⟩ := univE T g o.A φ φ₂ o.act o.eta pbo sqo rosO o.etaOK
  have pbo' : IsGrpPullback o.A c.A (z₀ ≫ πE) φ := by rw [hz₀]; exact pbo
  have tr := GlobalTheory.T.harrisTaylorLie_tate_conditions_iff_pullbacks p D R b N S c.A c.P c.isLB E T πE z₀ AE o.A φE φ₂E φ φ₂ ψ₀ actE o.act ηE o.eta o.P
    o.isLB pbE sqE pbo' sqo pb₀ hψ₀ isoo act₀ eta₀
  have hpt : ∀ {R' : Type} [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ z₀ ≫ πE ≫ t = spMap β →
      x ≫ t' = spMap β := fun β x hx => by
    rw [← hgt, ← hz₀]; simpa [Category.assoc] using hx
  obtain ⟨z, hz⟩ := (hZ T z₀).2 ⟨fun R' _ β x hx => (tr.1 R' β x).1 (o.lieHer R' β x (hpt β x hx)),
    fun k _ _ x β hx => (tr.2 k x).1 (o.geomAt k x β (hpt β x hx))⟩
  have w : ψ₀ ≫ AE.hom = (o.A.hom ≫ z) ≫ j := by rw [pb₀.1.w, Category.assoc, hz]
  let ψ' := pbu.1.lift ψ₀ (o.A.hom ≫ z) w
  have h1 : ψ' ≫ ψ = ψ₀ := pbu.1.lift_fst _ _ _
  have h2 : ψ' ≫ u.A.hom = o.A.hom ≫ z := pbu.1.lift_snd _ _ _
  have hact : ∀ a : D.O, (o.act.act a).left ≫ ψ' = ψ' ≫ (u.act.act a).left := fun a => by
    apply pbu.1.hom_ext
    · rw [Category.assoc, h1, act₀, Category.assoc, actu, ← Category.assoc, h1]
    · rw [Category.assoc, h2, Category.assoc, Over.w (u.act.act a), h2, ← Category.assoc,
        Over.w (o.act.act a)]
  have heta : ∀ y, (o.eta y).left ≫ ψ' = z ≫ (u.eta y).left := fun y => by
    apply pbu.1.hom_ext
    · rw [Category.assoc, h1, eta₀, Category.assoc, etau, ← Category.assoc, hz]
    · rw [Category.assoc, h2, Category.assoc, Over.w (u.eta y), ← Category.assoc, Over.w (o.eta y)]
      simp
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_harrisTaylorObjectMap_of_common_pullback p D R b N S c.A c.P c.isLB T Z t' ((j ≫ πE) ≫ t) o u g (j ≫ πE) z φ φ₂
    (ψ ≫ φE) ψ₂ ψ' pbo sqo isoo (pbu.comp pbE) squ isou (by rw [← Category.assoc, hz, hz₀])
    (by rw [← Category.assoc, h1, hψ₀]) h2 hact heta
  refine ⟨z, ⟨by rw [← Category.assoc, hz, hz₀], m, by rw [hm, ← Category.assoc, h1, hψ₀]⟩, ?_⟩
  rintro z' ⟨hz', m', hm'⟩
  have e₀ : z' ≫ j = z₀ := uniq₀ (z' ≫ j) ⟨by rw [Category.assoc]; exact hz', m'.φ ≫ ψ, m'.cart.comp pbu,
    by rw [Category.assoc]; exact hm',
    fun a => by rw [← Category.assoc, m'.act a, Category.assoc, actu]; exact (Category.assoc _ _ _).symm,
    fun y => by rw [← Category.assoc, m'.eta y, Category.assoc, etau]; exact (Category.assoc _ _ _).symm⟩
  exact (cancel_mono j).1 (e₀.trans hz.symm)

end GlobalTheory.UPel.HT
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace GlobalTheory.EtC.GmStep

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem cechC_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] {R : Type} [CommRing R] (F : Shv R) (s : ℤ)
    (k : ℕ) (j : Fin (k + 2)) (y : H R (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) F s) :
    pull R (disc.map ((cechC A A').app (op ⦋k + 1⦌))) F s (pull R (disc.map ((cech (baseHom A A')).δ j)) F s y) =
      pull R (disc.map ((cech (laurentHom A A')).δ j)) F s (pull R (disc.map ((cechC A A').app (op ⦋k⦌))) F s y) := by
  simp only [SimplicialObject.δ]
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, (cechC A A').naturality]

theorem aug_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ) (j : Fin (k + 2)) :
    disc.map ((cech (laurentHom A A')).δ j) ≫ augK A A' k = augK A A' (k + 1) := by
  have h := (cechAug (laurentHom A A')).naturality (SimplexCategory.δ j).op
  exact (disc.map_comp _ _).symm.trans (congrArg disc.map (h.trans (Category.comp_id _)))

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

theorem rowExact_base (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Finite A A'] (hker : RingHom.ker (algebraMap A A') ≤ nilradical A)
    (j : ℤ) (p : ℕ) : RowExact (ZMod q) (cech (baseHom A A')) (tw q j) 0 p := by
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI, hS⟩ := spec_integral_surj (algebraMap A A') hint hker
  have hB := @GlobalTheory.EtC.b4 q _ _ (baseHom A A') hI hS (isUnit_gamma q A hq) j
  refine GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic (ZMod q) (tw q j) _ (fun k s hs => GlobalTheory.T.cech_cohomology_vanishes_positive q A hA hq A' inferInstance k s j hs) (fun m hm => ?_) p
  haveI : Subsingleton (H (ZMod q) (sch.obj (Spec (CommRingCat.of A))) (tw q j) m) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) m hm
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := (hB m).2 a
    obtain ⟨b', rfl⟩ := (hB m).2 b
    rw [Subsingleton.elim a' b']⟩

theorem gm_vanishing_step : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  intro q _ n hn IH A _ _ hA hq i
  suffices h : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨A', _, _, hfin, hker, hx⟩ := GlobalTheory.T.laurent_cohomology_finite_killing q A hA hq n i hn x
  haveI := hfin
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI', hS'⟩ := spec_integral_surj _ (laurentMap_isIntegral _ hint) (laurentMap_ker _ hker)
  have hqL : IsUnit (q : LaurentPolynomial A) := by simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  have hB := @GlobalTheory.EtC.b4 q _ _ (laurentHom A A') hI' hS' (isUnit_gamma q _ hqL) i
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
  apply (hB N).1
  rw [map_zero]
  obtain ⟨Δ, hΔ0, hΔ⟩ := GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base (laurentHom A A')
  refine GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact (ZMod q) (tw q i) (cech (laurentHom A A')) (yoneda.obj _) Δ hΔ0 N _ ?_ ?_
  · exact (pull_comp (ZMod q) Δ (cechAug (laurentHom A A')) (tw q i) N x).symm.trans
      ((congrArg (fun g => pull (ZMod q) g (tw q i) N x) hΔ).trans hx)
  · intro p hp
    rcases (by omega : (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 0 ∨ (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 1 ∨
        2 ≤ (N : ℤ) - ((p + 1 : ℕ) : ℤ)) with h0 | h1 | h2
    · rw [h0]
      exact rowExact_transfer (fun k => pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0)
        (fun k => GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero q A hA hq A' hfin k i) (fun k j y => cechC_face A A' _ _ k j y) p
        (rowExact_base q A hA hq A' hker i p)
    · rw [h1]
      refine rowExact_transfer (fun k => rowOne A A' q i k) (fun k => GlobalTheory.T.cech_degree_zero_bijective q A hA hq A' hfin k i) (fun k j y => ?_) p
        (rowExact_base q A hA hq A' hker (i - 1) p)
      simp only [rowOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [pull_cast, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1, cechC_face,
        ← pull_comp (ZMod q) (disc.map ((cech (laurentHom A A')).δ j)) (augK A A' k), aug_face]
    · intro y _
      haveI := GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton q N IH A hA hq A' hfin (p + 1) _ i h2 (by omega)
      exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩

end GlobalTheory.EtC.GmStep

end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegel_point_lifts_to_dual_numbers : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β₀ : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed | exact GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed | (intros; apply GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed <;> assumption)

end
end
