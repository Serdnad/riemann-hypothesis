module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle698
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle721
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle711
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle720
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle673
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle654
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle697
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle723
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle703
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle727
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.carriedFrames_specialise_flagComponent_localRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk := by
  first | exact @GlobalTheory.CarrySpec.carries_spec | exact GlobalTheory.CarrySpec.carries_spec | (intros; apply GlobalTheory.CarrySpec.carries_spec <;> assumption)
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.finite_balanced_cmIntegers_actions_siegelReduced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ), {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)}.Finite := by
  first | exact @GlobalTheory.RedTh.finite_balanced_actions | exact GlobalTheory.RedTh.finite_balanced_actions | (intros; apply GlobalTheory.RedTh.finite_balanced_actions <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqCorr

theorem psi_sq_terms_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)))  → ∀ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ ∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2 := by
  intro R _ _ _ hR G _ _ hsa D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht hc σ f hE
  obtain ⟨σ', f', hE', hrel⟩ := GlobalTheory.T.exists_bundleSquare_section_transport_expansion R hR G hsa D D' A A' U U' wL hwL σ
  refine ⟨σ', f', hE', fun β Z ρ z J J' hJ hJ' => ?_⟩
  have hφ : ∀ κ, D'.toPre.famφB (2 • β) κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB (xe (2 • β)) κ :=
    PsiCompare.famφB_comp Φ.hom (hc β)
  refine GlobalTheory.T.abelianPart_section_sq_eq_of_thickening_points R hR G hsa D D' A A' U U' Φ w hw (fun e => (hlev e).1) _ _ hφ (f _) (f' _)
    (fun e Z r z J J' hJ hJ' => ?_) Z ρ z J J' hJ hJ'
  have hB := GlobalTheory.T.termExpansion_weight_correspondence_at_level R hR G hsa D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht σ σ' f f' hE hE' hrel e Z r z J J' hJ hJ' (2 • β)
  have hC := GlobalTheory.T.torus_coord_squares_correspond' R hR G hsa D D' A A' U U' Φ w hw hΦ (fun e => (hlev e).1) xe ht β (hc β) e Z r z J J' hJ hJ'
  have hP := ExpTrans.prod_fam U'.toUnifPre e 2 (fun ψ => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ ψ)) (2 • β)

  set a := sval (f (xe (2 • β))) (r ≫ (U.gt e).pG.left) z J
  set b := sval (f' (2 • β)) (r ≫ (U'.gt e).pG.left) z J'
  set T := val ((U.gt e).t (xe (2 • β))) r z J
  set T' := val ((U'.gt e).t (2 • β)) r z J'
  set O := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)
  set P := ∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ
  set F := ∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ
  have hP' : F * P = O ^ 2 := hP
  have key : a ^ 2 * (P * T' ^ 2).val = F.val * b ^ 2 * (P * T' ^ 2).val := by
    calc a ^ 2 * (P * T' ^ 2).val = a ^ 2 * (T ^ 2).val := by rw [hC]
      _ = (a * T.val) ^ 2 := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = (O.val * b * T'.val) ^ 2 := by rw [hB]
      _ = (O ^ 2).val * b ^ 2 * (T' ^ 2).val := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = (F * P).val * b ^ 2 * (T' ^ 2).val := by rw [hP']
      _ = F.val * b ^ 2 * (P * T' ^ 2).val := by simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring
  exact (Units.mul_left_inj (P * T' ^ 2)).1 key

end GlobalTheory.SqCorr
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.flagSpaceComponent_classifyingMap_bijective_geomPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (Y' : Var F) (φ' : X.Fn →ₐ[F] Y'.Fn) (f' : Y'.X ⟶ X.X) (S' : Fr (ratOf Y') Dw.mult Dw.mult), Refines Eb S' φ' f' → ∃ h : C.Y.X ⟶ Y'.X, h ≫ f' = f ∧ ∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ C.Y.X => p ≫ h) := by
  first | exact @GlobalTheory.ShFam.ClsMap.main | exact GlobalTheory.ShFam.ClsMap.main | (intros; apply GlobalTheory.ShFam.ClsMap.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.ConstForm

theorem constForm : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → _root_.IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧ (∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) → Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧ ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m := by
  intro n a g r₀ K ζ Pair hK hζan hζli hζK hζ0 hζbd hstd huniq hprop hinner hS
  obtain ⟨hDo, hDc, hEa, hEm⟩ := Core.logDom_facts n a
  have hDp : _root_.IsPreconnected (logDom n a) := hDc.isPreconnected
  have hEd : Differentiable ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) := fun s => (hEa s).differentiableAt
  have hK' : IsLatFam (logDom n a) (fun s => K (logExp a s)) :=
    Core.isLatFam_comp n n g _ _ K (logExp a) hK hDo (fun s _ => hEa s) hEm
  have hin := fun s (hs : s ∈ logDom n a) => hinner _ (hEm hs) (fun k hk => Core.logExp_ne_zero n a s k hk)
  obtain ⟨lam, hlamD, hlamB⟩ := GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex n g (2 * g) (logDom n a) (fun s => K (logExp a s)) hDo hDc
    (fun s hs => GlobalTheory.T.exists_analytic_local_lattice_basis n g (logDom n a) (fun s => K (logExp a s)) s hK' hs (hin s hs).choose_spec.2.2.1)
  have hmem : ∀ s ∈ logDom n a, ∀ i, lam s i ∈ K (logExp a s) := fun s hs i => Core.mem_of_isLatBasis (hlamB s hs) i
  have hlamDi : ∀ i, DifferentiableOn ℂ (fun s => lam s i) (logDom n a) := fun i => differentiableOn_pi.1 hlamD i
  let s₀ : Fin n → ℂ := fun _ => (-1 / 2 : ℂ)
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    split_ifs <;> norm_num [s₀]
  obtain ⟨Hm₀, -, hpos₀, hspan₀, hint₀, hpair₀⟩ := hin s₀ hs₀
  have hMex : ∀ i j, ∃ m : ℤ, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = m := fun i j =>
    hint₀ _ (hmem s₀ hs₀ i) _ (hmem s₀ hs₀ j)
  obtain ⟨M, hM₀⟩ : ∃ M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ, ∀ i j, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = M i j :=
    ⟨fun i j => (hMex i j).choose, fun i j => (hMex i j).choose_spec⟩
  have hM : ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) →
      (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) →
        Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
          (Complex.exp_ne_zero _))) →
      ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j := by
    intro s hs Hm hint hpair i j
    obtain ⟨m', hm'⟩ := hint _ (hmem s hs i) _ (hmem s hs j)
    have key : m' = M i j := by
      apply Core.eq_of_exp_eq
      intro N hN
      have h1 := hpair₀ N _ _ hN (hmem s₀ hs₀ i) (hmem s₀ hs₀ j)
      have h2 := hprop n N (logDom n a) (logExp a) (fun s => lam s i) (fun s => lam s j) _ s₀ s hN hDo hDp
        hEd.differentiableOn hEm (hlamDi i) (hlamDi j) (fun b hb => ⟨hmem b hb i, hmem b hb j⟩) hs₀ hs h1
      have h3 := hpair N _ _ hN (hmem s hs i) (hmem s hs j)
      have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
      simp only [Units.val_mk0, hm', hM₀, Complex.ofReal_intCast] at h4
      exact h4
    rw [hm', key]
  have hζc : ContinuousOn ζ (Metric.ball 0 1) := hζan.continuousOn
  have hζEc : ∀ i, ContinuousOn (fun s => ζ (logExp a s) i) (logDom n a) := fun i =>
    (continuousOn_pi.1 (hζc.comp hEd.continuous.continuousOn hEm)) i
  have hAex : ∀ i, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a, ζ (logExp a s) i = ∑ k, m k • lam s k := fun i =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun s => ζ (logExp a s) i) s₀ hDp
      hlamD.continuousOn (hζEc i) hlamB (fun s hs => hζK _ (hEm hs) i) hs₀
  choose A hA using hAex
  have hz₁ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 := hEm hs₀
  have hsumK : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ z j ∈ K z := by
    intro z hz c
    obtain ⟨H, hH⟩ := hK.2.1 z hz
    have hj : ∀ j, ζ z j ∈ H := fun j => by rw [← SetLike.mem_coe, hH]; exact hζK z hz j
    rw [← hH]
    exact H.sum_mem fun j _ => H.zsmul_mem (hj j) _
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζan.differentiableOn
  have hsumD : ∀ c : Fin r₀ → ℤ, DifferentiableOn ℂ (fun z => ∑ j, c j • ζ z j) (Metric.ball 0 1) := by
    intro c
    have h : ∀ j ∈ (Finset.univ : Finset (Fin r₀)), DifferentiableOn ℂ (fun z => c j • ζ z j) (Metric.ball 0 1) :=
      fun j _ => (differentiableOn_pi.1 hζd j).const_smul (c j)
    refine (DifferentiableOn.sum h).congr fun z _ => ?_
    simp [Finset.sum_apply]
  have hsum_eq : ∀ s ∈ logDom n a, ∀ c : Fin r₀ → ℤ,
      ∑ j, c j • ζ (logExp a s) j = ∑ k, (∑ i, c i • A i) k • lam s k := by
    intro s hs c
    simp only [fun i => hA i s hs, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have hform : ∀ (s : Fin n → ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∀ x y : Fin (2 * g) → ℤ,
      (hermForm Hm (∑ k, x k • lam s k) (∑ k, y k • lam s k)).im =
      ((x ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ y : ℤ) : ℝ) := by
    intro s Hm hHm x y
    rw [Core.hermForm_im_sum]
    simp only [hHm, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdvd : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ c c' : Fin r₀ → ℤ, (fun j => (c j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, c i • A i) ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ (∑ i, c' i • A i) := by
    intro N hN
    obtain ⟨S, hcard, hSp⟩ := hS N hN
    refine ⟨S, hcard, fun c c' hc => ?_⟩
    have h1 := hSp c c' hc
    have h2 := hprop n N (Metric.ball 0 1) id (fun z => ∑ j, c j • ζ z j) (fun z => ∑ j, c' j • ζ z j) 1 0
      (logExp a s₀) hN Metric.isOpen_ball (convex_ball 0 1).isPreconnected differentiableOn_id (Set.mapsTo_id _)
      (hsumD c) (hsumD c') (fun b hb => ⟨hsumK b hb c, hsumK b hb c'⟩) (Metric.mem_ball_self one_pos) hz₁ h1
    have h3 := hpair₀ N _ _ hN (hsumK _ hz₁ c) (hsumK _ hz₁ c')
    have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
    simp only [Units.val_mk0, Units.val_one, id, hsum_eq s₀ hs₀, hform s₀ Hm₀ hM₀, Complex.ofReal_intCast] at h4
    exact Core.dvd_of_exp_eq_one _ N hN h4
  refine ⟨2 * g, lam, M, hlamD.continuousOn, fun s hs => ⟨(hlamB s hs).1.restrict_scalars' ℤ,
    Core.span_top_of_isLatBasis (hlamB s hs) (hin s hs).choose_spec.2.2.1, (hlamB s hs).2⟩, fun s hs => ?_, hM,
    fun N hN => ?_⟩
  · obtain ⟨Hm, -, hpos, -, hint, hpair⟩ := hin s hs
    exact ⟨Hm, hpos, hM s hs Hm hint hpair⟩
  · obtain ⟨S, hcard, hSd⟩ := hdvd N hN
    refine ⟨S, hcard, fun u u' hu s hs Hm hHm => ?_⟩
    obtain ⟨m, hm⟩ := hSd u u' hu
    refine ⟨m, ?_⟩
    rw [hsum_eq s hs u, hsum_eq s hs u', hform s Hm hHm, hm]
    push_cast
    ring

end GlobalTheory.ShFam.Hor.LogCh.ConstForm
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical


theorem _root_.GlobalTheory.T.grassmannProductIntegral_pointClass_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), intGr H Dw (pointPoly H Dw) = 1 := by
  first | exact @GlobalTheory.GrassTop.intGr_pointPoly | exact GlobalTheory.GrassTop.intGr_pointPoly | (intros; apply GlobalTheory.GrassTop.intGr_pointPoly <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier


theorem _root_.GlobalTheory.T.eigenMetricGram_smooth_in_familyFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ A ∈ S.S (under y), ∀ (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).re) y ∧ CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).im) y := by
  first | exact @GlobalTheory.LieBase.cInfAt_gramOf | exact GlobalTheory.LieBase.cInfAt_gramOf | (intros; apply GlobalTheory.LieBase.cInfAt_gramOf <;> assumption)
end
