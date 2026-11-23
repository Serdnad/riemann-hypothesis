module

public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AnalyticAtCoordinateZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticParamInverse
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.RelExp

theorem exists_lift {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m n : ℕ} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {U : G.left.Opens} {t : Fin g → Γ(G.left, U)} {f : Fin n → Γ(G.left, U)} {O : Set ((Fin m → ℂ) × (Fin n → ℂ))}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {Q : Set ((Fin m → ℂ) × (Fin g → ℂ))}
    {L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)} (hO : IsOpen O) (hQ : IsOpen Q)
    (hadd : ∀ b z w, e b (z + w) = e b z * e b w)
    (hinv : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → (b, crd0 t a) ∈ Q →
      e b (L (b, crd0 t a)) = a)
    {k : ℕ} {β : (Fin k → ℂ) → (Fin m → ℂ)} {x : ∀ w, Over.mk (y (β w)) ⟶ G} {w₀ : Fin k → ℂ} {z₀ : Fin g → ℂ}
    (hβ : AnalyticAt ℂ β w₀) (hx : HolAt (fun w => pt (x w)) w₀) (h0 : e (β w₀) z₀ = x w₀)
    (he : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 q.2)) (β w₀, z₀))
    (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U) (hO₀ : (β w₀, crd U f (pt (1 : Over.mk (y (β w₀)) ⟶ G))) ∈ O)
    (hQ₀ : (β w₀, 0) ∈ Q) (hL0 : L (β w₀, 0) = 0) (hL : AnalyticAt ℂ L (β w₀, 0)) :
    ∃ ζ : (Fin k → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in 𝓝 w₀, e (β w) (ζ w) = x w := by
  have h1 := HolAt.comp (φ := fun w => (β w, z₀)) (v₀ := w₀) he (hβ.prod analyticAt_const)
  have h2 := HolAt.inv (y := fun w => y (β w)) (a := fun w => e (β w) z₀) h1
  have ha : HolAt (fun w => pt (x w * (e (β w) z₀)⁻¹)) w₀ :=
    HolAt.mul (y := fun w => y (β w)) (a := x) (b := fun w => (e (β w) z₀)⁻¹) hx h2
  have ha0 : x w₀ * (e (β w₀) z₀)⁻¹ = 1 := by rw [h0, mul_inv_cancel]
  have hc : AnalyticAt ℂ (fun w => (β w, crd0 t (x w * (e (β w) z₀)⁻¹))) w₀ :=
    hβ.prod (HolAt.analyticAt_coordinate_zero (a := fun w => x w * (e (β w) z₀)⁻¹) ha ha0 hU)
  have hc0 : (β w₀, crd0 t (x w₀ * (e (β w₀) z₀)⁻¹)) = (β w₀, 0) := by
    rw [ha0]; exact Prod.ext rfl (sub_self _)
  refine ⟨fun w => L (β w, crd0 t (x w * (e (β w) z₀)⁻¹)) + z₀, ?_, ?_, ?_⟩
  · simp only [hc0, hL0, zero_add]
  · exact (AnalyticAt.comp (g := L) (hc0 ▸ hL) hc).add analyticAt_const
  · filter_upwards [HolAt.eventually_near (a := fun w => x w * (e (β w) z₀)⁻¹) ha hβ.continuousAt ha0 hO hU hO₀,
      hc.continuousAt.eventually (hQ.mem_nhds (by simpa only [hc0] using hQ₀))] with w h3 h4
    rw [hadd, hinv _ _ h3.1 h3.2 h4, inv_mul_cancel_right]

theorem exists_relative_exp_of_parts
    (hchart : ∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v')
    (htan : ∀ (X : Scheme.{0}) (G : Over X) (x : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk x ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → (∀ w, ∃! v : epsPt x ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ (U : G.left.Opens) (t : Fin g → Γ(G.left, U)), ⊤ ≤ (show Sp ℂ ⟶ G.left from (e 0).left) ⁻¹ᵁ U → (∀ (v v' : Sp (DualNumber ℂ) ⟶ G.left) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ G.hom = v' ≫ G.hom → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') → ((∀ v : epsPt x ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) ↔ Function.Injective (fderiv ℂ (fun z i => valAt' (e z).left U (t i)) 0)))
    (hexp : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)))
    (hsub : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp ℂ ⟶ X) (H : Subgroup (Over.mk x ⟶ G)) (U : G.left.Opens) (κ : Type) [Fintype κ] (f : κ → Γ(G.left, U)) (O : Set (κ → ℂ)), Smooth G.hom → GeometricallyConnected G.hom → IsOpen O → ⊤ ≤ (show Sp ℂ ⟶ G.left from (1 : Over.mk x ⟶ G).left) ⁻¹ᵁ U → (fun j => valAt' (1 : Over.mk x ⟶ G).left U (f j)) ∈ O → (∀ a : Over.mk x ⟶ G, ⊤ ≤ (show Sp ℂ ⟶ G.left from a.left) ⁻¹ᵁ U → (fun j => valAt' a.left U (f j)) ∈ O → a ∈ H) → H = ⊤) :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w := by
  intro k _ σ₀ X s₀ G _ g m B y b₀ e₀ _ hab hsm hB hb₀ _ hy ⟨he₀add, _, he₀hol, _, he₀tan⟩
  have := hab.comm
  have hy₀ : HolAt y b₀ := ⟨B, hB, hb₀, hy⟩
  obtain ⟨U, t, n, f, N, O, σ, hN, hO, hU, hO₀, hσ, hσN, hσinv, hunr⟩ :=
    hchart m g G.left X G.hom B y b₀ (pt (1 : Over.mk (y b₀) ⟶ G)) hsm hB hb₀ hy (Over.w _)
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_centred_chart hy₀ hN hU hO₀ hσ hσN hσinv
  obtain ⟨B', e, r, Q, L, hB', hb', hB'B, hr, hQ, hadd, hfib, hinv⟩ :=
    exists_global_exp hexp (hB.mem_nhds hb₀) hy₀ hO hU hO₀ hs1 hs2 hs3
  have hzero : ∀ {x : Sp ℂ ⟶ X} {u : (Fin g → ℂ) → (Over.mk x ⟶ G)}, (∀ z w, u (z + w) = u z * u w) → u 0 = 1 :=
    fun {x u} h => by
      have := h 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
  have he₀0 : e₀ 0 = 1 := hzero he₀add
  have he₀U : ⊤ ≤ pt (e₀ 0) ⁻¹ᵁ U := by rw [he₀0]; exact hU
  have hinj := ((htan X G (y b₀) g e₀ he₀hol).2 U t he₀U hunr).1 he₀tan
  set T₀ : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := fderiv ℂ (fun z => crd U t (pt (e₀ z))) 0 with hT₀
  have hsurj : Function.Surjective T₀ :=
    (LinearMap.injective_iff_surjective (f := (T₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)))).1 hinj
  let T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := ContinuousLinearEquiv.ofBijective T₀ (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hT : ∀ z, T z = T₀ z := fun _ => rfl
  have hhol : ∀ b ∈ B', ∀ z, HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 (T₀ q.2))) (b, z) :=
    fun b hb z => by
      have := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, T₀ q.2)) (v₀ := (b, z))
        ((hfib b hb).1 (T₀ z)) (analyticAt_fst.prod ((T₀.analyticAt _).comp analyticAt_snd))
      exact this
  refine ⟨B', fun b z => e b (T₀ z), r / (‖T₀‖ + 1), hB', hb', hB'B, ?_, by positivity,
    isHolTo_of_holAt (hB'.prod isOpen_univ) fun q hq => hhol q.1 hq.1 q.2, fun b hb => ?_, ?_⟩
  ·
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib b₀ hb'
    obtain ⟨ζ, hζ0, hζ, hζe⟩ := exists_lift hO hQ hadd hinv (β := fun _ : Fin g → ℂ => b₀) (x := e₀) (w₀ := 0)
      (z₀ := 0) analyticAt_const ⟨Set.univ, isOpen_univ, trivial, he₀hol⟩ ((hzero (hadd b₀)).trans he₀0.symm)
      (h1 0) h2 h3 h4 h6 h7
    have hd : HasFDerivAt ζ T₀ 0 := by
      have k1 := HasFDerivAt.comp (f := ζ) (0 : Fin g → ℂ) (hζ0.symm ▸ h5) hζ.differentiableAt.hasFDerivAt
      have k2 : HasFDerivAt (fun z => crd U t (pt (e₀ z))) _ 0 := k1.congr_of_eventuallyEq
        (hζe.mono fun z hz => by simp only [Function.comp, hz])
      rw [hT₀, k2.fderiv, ContinuousLinearMap.id_comp]
      exact hζ.differentiableAt.hasFDerivAt
    have tζ : Tendsto ζ (𝓝 0) (𝓝 0) := by simpa only [ContinuousAt, hζ0] using hζ.continuousAt
    have t1 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
    have t2 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto 0
    have t3 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.1 + p.2) (𝓝 0) (𝓝 0) := by simpa using t1.add t2
    have t4 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => ζ (p.1 + p.2) - (ζ p.1 + ζ p.2)) (𝓝 0) (𝓝 0) := by
      simpa using (tζ.comp t3).sub ((tζ.comp t1).add (tζ.comp t2))
    have hζT := eventuallyEq_of_additive_of_hasFDerivAt hd (by
      filter_upwards [t1.eventually hζe, t2.eventually hζe, t3.eventually hζe,
        t4.eventually (Metric.ball_mem_nhds 0 hr)] with p k1 k2 k3 k4
      refine sub_eq_zero.1 (h8 _ (mem_ball_zero_iff.1 k4) ?_)
      have k5 := hadd b₀ (ζ (p.1 + p.2) - (ζ p.1 + ζ p.2)) (ζ p.1 + ζ p.2)
      rw [sub_add_cancel, hadd b₀ (ζ p.1), k1, k2, k3, he₀add] at k5
      exact mul_eq_right.1 k5.symm)
    have key := addMonoidHom_eq_of_eventuallyEq
      (e := AddMonoidHom.mk' (fun z => Additive.ofMul (e b₀ (T₀ z))) fun z w => by rw [map_add (f := _), hadd]; rfl)
      (e' := AddMonoidHom.mk' (fun z => Additive.ofMul (e₀ z)) fun z w => by rw [he₀add]; rfl) (by
        filter_upwards [hζT, hζe] with z k1 k2
        exact congrArg Additive.ofMul (by rw [← k1]; exact k2))
    exact funext fun z => congrArg Additive.toMul (DFunLike.congr_fun key z)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib b hb
    have hH : IsHolTo Set.univ (fun z => pt (e b (T₀ z))) := isHolTo_of_holAt isOpen_univ fun z _ => by
      have := HolAt.comp (φ := fun z : Fin g → ℂ => (b, z)) (v₀ := z) (hhol b hb z)
        (analyticAt_const.prod analyticAt_id)
      exact this
    have hadd' : ∀ z w, e b (T₀ (z + w)) = e b (T₀ z) * e b (T₀ w) := fun z w => by rw [map_add (f := _), hadd]
    obtain ⟨k1, k2⟩ := htan X G (y b) g (fun z => e b (T₀ z)) hH
    refine ⟨⟨hadd', ?_, hH, k1, (k2 U t ?_ hunr).2 ?_⟩, fun z hz h => ?_⟩
    · refine Function.Surjective.comp (g := e b) ?_ hsurj
      let ε : (Fin g → ℂ) →+ Additive (Over.mk (y b) ⟶ G) :=
        AddMonoidHom.mk' (fun z => Additive.ofMul (e b z)) fun z w => by rw [hadd]; rfl
      have hc : Continuous fun u : Fin n ⊕ Fin g → ℂ => (b, fun j => u (Sum.inl j)) := by fun_prop
      have hc' : Continuous fun u : Fin n ⊕ Fin g → ℂ =>
        (b, (fun j => u (Sum.inr j)) - crd U t (pt (1 : Over.mk (y b) ⟶ G))) := by fun_prop
      have := hsub X G (y b) (AddSubgroup.toSubgroup' ε.range) U (Fin n ⊕ Fin g) (Sum.elim f t) _ hab.smooth
        hab.geomConnected ((hO.preimage hc).inter (hQ.preimage hc')) h2
        ⟨h3, by simpa only [Set.mem_preimage, Sum.elim_inr, sub_self] using h4⟩
        fun a ha hb => ⟨_, congrArg Additive.ofMul (hinv b a ha hb.1 hb.2)⟩
      intro a
      obtain ⟨z, hz⟩ : a ∈ AddSubgroup.toSubgroup' ε.range := this ▸ Subgroup.mem_top a
      exact ⟨z, congrArg Additive.toMul hz⟩
    · rw [hzero (u := fun z => e b (T₀ z)) hadd']; exact h2
    · have := HasFDerivAt.comp (f := T₀) (0 : Fin g → ℂ) (by rw [map_zero]; exact h5) T₀.hasFDerivAt
      have k3 : fderiv ℂ (fun z => crd U t (pt (e b (T₀ z)))) 0 = _ := this.fderiv
      rw [ContinuousLinearMap.id_comp] at k3
      exact k3.symm ▸ hinj
    · refine hinj ((h8 _ ((T₀.le_opNorm z).trans_lt ?_) h).trans (map_zero T₀).symm)
      rw [lt_div_iff₀ (by positivity)] at hz
      nlinarith [norm_nonneg z]
  · intro j W β x w₀ z₀ hW hw₀ hβ hβW hx h0
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib _ (hβW hw₀)
    obtain ⟨ζ, hζ0, hζ, hζe⟩ := exists_lift hO hQ hadd hinv (x := x)
      (SCV.analyticAt_of_differentiableOn hβ (hW.mem_nhds hw₀)) ⟨W, hW, hw₀, hx⟩ h0 (h1 _) h2 h3 h4 h6 h7
    refine ⟨fun w => T.symm (ζ w), by simp only [hζ0, ← hT, T.symm_apply_apply], (T.symm.analyticAt _).comp hζ, ?_⟩
    filter_upwards [hζe] with w hw
    rw [← hT, T.apply_symm_apply, hw]

theorem exists_relative_exp :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w :=
  exists_relative_exp_of_parts (RelChart.exists_chart_with_parameters EtaleFamily.exists_holomorphic_sections)
    vertical_derivative_in_coordinates exists_param_exp_log_pi OpenSubgroupPts.subgroup_eq_top_of_nhds_one

end GlobalTheory.RelExp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.RigidLinearisation

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ c := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

theorem gs_one {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) : gs f y ⊤ (1 : Γ(X, ⊤)) = 1 := by
  rw [gs_eq _ y ⊤ trivial, map_one, map_one]

theorem gs_pow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (c : Γ(X, ⊤)) (n : ℕ) : gs f y ⊤ (c ^ n) = gs f y ⊤ c ^ n := by
  rw [gs_eq _ y ⊤ trivial, gs_eq _ y ⊤ trivial, map_pow, map_pow]

theorem exists_good' {X Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (z : Z) : ∃ J, Good M z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hM (χ z)
  exact ⟨I, hI⟩

theorem val_eq_of_rigid {X Y S : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (e : S ⟶ Y) (he : ∀ c : Γ(Y, ⊤), (e.app ⊤).hom c = 1 → c = 1)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨c, hc⟩ := exists_ratio hM hF hu hu'
  have c1 : c = 1 := he c (fn_ext (V := ⊤) fun y _ => by
    obtain ⟨I, hI⟩ := exists_good' hM y
    have := hc _ e y I hI
    rw [h y I hI, mul_inv_cancel] at this
    refine (gs_pull (𝟙 S) e y ⊤ trivial c).trans ?_
    rw [Category.id_comp, ← this]
    exact (gs_one (𝟙 S) y).symm)
  have := hc Z r z J hJ
  rw [c1, gs_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem exists_gen_of_iso {Y : Scheme.{0}} (L : LB Y) (τ : Y ⟶ Y) (h : LBIso L (L.pull τ)) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ] ![1, -1]), t.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j ≤ (L.pull τ).U (fun _ => j 1) ⊓ L.U (j 0) :=
    fun j y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy 1), Set.mem_iInter.1 hy 0⟩
  refine ⟨⟨fun j => (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  have v : ∀ j : Fin 2 → L.ι, y ∈ LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j →
      gm (𝟙 Y) y (LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j) (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹ =
        (gw w (𝟙 Y) y (j 1) (j 0))⁻¹ := fun j hj =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res (𝟙 Y) y (le j) hj _))
  refine (v j hj).trans (Eq.trans ?_ (congrArg (_ * ·) (v j' hj')).symm)
  rw [hp Y (𝟙 Y) y (j 1) (j' 1) (j 0) (j' 0) (Set.mem_iInter.1 hj 1) (Set.mem_iInter.1 hj' 1)
    (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0), trF, Fin.prod_univ_two]
  show _ = gm (𝟙 Y ≫ 𝟙 Y) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 Y ≫ τ) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) * _
  rw [Category.id_comp (𝟙 Y), zpow_one, zpow_neg_one, mul_inv, mul_inv, inv_inv, mul_comm (_⁻¹) (gm (𝟙 Y) y _ _)]

theorem exists_normalised {X Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (p : Y ⟶ X) (e : X ⟶ Y) (he : e ≫ p = 𝟙 X)
    (ρ : X ⟶ X) (τ : Y ⟶ Y) (hτ : e ≫ τ = ρ ≫ e) (r : (L.pull e).Gen) (hr : r.IsGen) (h : LBIso L (L.pull τ)) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ] ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (b : Z ⟶ X) (z : Z) (J), Good L z J →
        val u (b ≫ e) z J = val r b z J * (val r (b ≫ ρ) z J)⁻¹ := by
  obtain ⟨t, ht⟩ := exists_gen_of_iso L τ h
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := ![𝟙 Y, τ]) (ε' := ![1, -1]) (fun U _ k => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fintype.prod_unique,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.assoc, hτ, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (p ≫ e))))
      (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ r p) (LB.invGen L _ _ (LB.pullGen L _ _ r (p ≫ ρ)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _))))
  refine ⟨u, hu, fun Z b z J hJ => ?_⟩
  have e₁ : (b ≫ e) ≫ p = b := by rw [Category.assoc, he, Category.comp_id]
  rw [hv Z _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_pull hJ, val_pull hJ,
    ← Category.assoc (b ≫ e) p e, ← Category.assoc (b ≫ e) p ρ, e₁, mul_inv_cancel, _root_.one_mul]

theorem exists_const {k : Type} [Field k] [IsAlgClosed k] {F : Scheme.{0}} [IsIntegral F] (q : F ⟶ Sp k)
    (c : Γ(F, ⊤)) {n : ℕ} (hn : n ≠ 0) (hc : c ^ n = 1) : ∃ a : Γ(Sp k, ⊤), (q.app ⊤).hom a = c := by
  let f : k →+* Γ(F, ⊤) := (q.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hs : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial k).Splits := IsAlgClosed.splits _
  have hm : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial k).Monic := Polynomial.monic_X_pow_sub_C _ hn
  have e := congrArg (Polynomial.eval₂ f c) (hs.eq_prod_roots_of_monic hm)
  rw [Polynomial.eval₂_multiset_prod, Multiset.map_map] at e
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_one, hc, sub_self,
    Polynomial.eval₂_one] at e
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 e.symm)
  simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at ha
  exact ⟨_, (sub_eq_zero.1 ha).symm⟩

theorem exists_linearisation : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left) (ρ : Γ →* Aut X) (τ : Γ →* Aut P.left) (L : LB P.left), e ≫ P.hom = 𝟙 X → GeometricallyIntegral P.hom → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → (∀ g, (τ g).asIso.hom ≫ P.hom = P.hom ≫ (ρ g).asIso.hom ∧ e ≫ (τ g).asIso.hom = (ρ g).asIso.hom ≫ e) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst P.hom x ≫ (τ g).asIso.hom = pullback.fst P.hom x) → L.IsLB → (∃ r : (L.pull e).Gen, r.IsGen) → (∀ g, LBIso L (L.pull (τ g).asIso.hom)) → ∃ u : ∀ g, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 P.left, (τ g).asIso.hom] ![1, -1]), (∀ g, (u g).IsGen) ∧ (∀ g h, LB.Gen.Corr L _ _ _ _ (u (h * g)) (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).asIso.hom))) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ P.left) g, y ≫ (τ g).asIso.hom = y → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u g) y) (LB.oneGen L) := by
  intro Γ _ _ X P e ρ τ L he hgi hrig hcomm hfix hL ⟨r, hr⟩ hiso
  choose u hu hn using fun g => exists_normalised hL P.hom e he (ρ g).asIso.hom (τ g).asIso.hom (hcomm g).2 r hr (hiso g)
  have rig : ∀ c : Γ(P.left, ⊤), (e.app ⊤).hom c = 1 → c = 1 := fun c hc =>
    hrig ⊤ c le_top (by
      have : e.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ le_top = e.app ⊤ := (e.app_eq_appLE (U := ⊤)).symm
      rw [this]; exact hc)
  have τm : ∀ g h, (τ (h * g)).asIso.hom = (τ g).asIso.hom ≫ (τ h).asIso.hom := fun g h => by rw [map_mul]; rfl
  have ρm : ∀ g h, (ρ (h * g)).asIso.hom = (ρ g).asIso.hom ≫ (ρ h).asIso.hom := fun g h => by rw [map_mul]; rfl
  have coc : ∀ g h (Z : Scheme.{0}) (s : Z ⟶ P.left) (z : Z) (J), Good L z J → val (u (h * g)) s z J =
      val (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).asIso.hom)) s z J := fun g h =>
    val_eq_of_rigid hL (fun U _ k => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, τm, Category.comp_id]
        simp) e rig (hu _)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hu g) (DVR.pullGen_isGen _ _ _ _ (hu h) _)) (fun y J hJ => by
        have a₁ := hn (h * g) X (𝟙 X) y J hJ
        have a₂ := hn g X (𝟙 X) y J hJ
        have a₃ := hn h X (ρ g).asIso.hom y J hJ
        simp only [Category.id_comp] at a₁ a₂
        rw [val_mul hJ, val_pull hJ, (hcomm g).2, a₁, a₂, a₃, ρm]
        simp)
  refine ⟨u, hu, fun g h => corr_of_val hL fun y J hJ => coc g h _ _ y J hJ, fun k _ _ y g hy => ?_⟩
  have hx : (y ≫ P.hom) ≫ (ρ g).asIso.hom = y ≫ P.hom := by
    rw [Category.assoc, ← (hcomm g).1, ← Category.assoc, hy]
  have hf := hfix k _ g hx
  have : IsIntegral (pullback P.hom (y ≫ P.hom)) :=
    hgi.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  obtain ⟨c, hc⟩ := exists_ratio hL (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ k => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hf, Category.comp_id]
      simp)
    (DVR.pullGen_isGen _ _ _ _ (hu g) (pullback.fst P.hom (y ≫ P.hom))) (u' := LB.oneGen L)
    (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.one_mul _)).symm)
  have hc' : ∀ (Z : Scheme.{0}) (s : Z ⟶ pullback P.hom (y ≫ P.hom)) (z : Z) (J), Good L z J →
      (val (u g) (s ≫ pullback.fst _ _) z J).val = gs s z ⊤ c := fun Z s z J hJ => by
    rw [← hc Z s z J hJ, val_pull hJ, val_one, inv_one, _root_.mul_one]
  have pw : ∀ (Z : Scheme.{0}) (s : Z ⟶ P.left) (z : Z) (J), Good L z J → s ≫ (τ g).asIso.hom = s →
      val (u g) s z J ^ orderOf g = 1 := fun Z s z J hJ hs => by
    have one : val (u 1) s z J = 1 := by
      have := coc 1 1 Z s z J hJ
      rw [val_mul hJ, val_pull hJ, _root_.mul_one, show s ≫ (τ 1).asIso.hom = s by rw [map_one]; exact Category.comp_id s] at this
      exact mul_eq_left.1 this.symm
    have all : ∀ n : ℕ, val (u (g ^ n)) s z J = val (u g) s z J ^ n := fun n => by
      induction n with
      | zero => rw [pow_zero, pow_zero, one]
      | succ n ih => rw [pow_succ, coc g (g ^ n) Z s z J hJ, val_mul hJ, val_pull hJ, hs, ih, pow_succ']
    rw [← all, pow_orderOf_eq_one, one]
  have cn : c ^ orderOf g = 1 := fn_ext fun z _ => by
    obtain ⟨J, hJ⟩ := exists_good' hL z
    rw [gs_pow, gs_one, ← hc' _ _ z J hJ, ← Units.val_pow_eq_pow_val,
      pw _ _ z J hJ (by rw [Category.assoc, hf]), Units.val_one]
  obtain ⟨a, ha⟩ := exists_const (pullback.snd P.hom (y ≫ P.hom)) c (orderOf_pos g).ne' cn
  have sec : ∀ (s : Sp k ⟶ pullback P.hom (y ≫ P.hom)) (z : Sp k), s ≫ pullback.snd _ _ = 𝟙 _ →
      gs s z ⊤ c = gs (𝟙 _) z ⊤ a := fun s z hs => by
    rw [← ha, ← hs]
    exact gs_pull s _ z ⊤ trivial a
  refine corr_of_val hL fun z J hJ => Units.ext ?_
  have b₁ := hc' _ (pullback.lift y (𝟙 _) (Category.id_comp _).symm) z J hJ
  have b₂ := hc' _ (pullback.lift ((y ≫ P.hom) ≫ e) (𝟙 _) (by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp])) z J hJ
  rw [sec _ z (pullback.lift_snd _ _ _), pullback.lift_fst] at b₁ b₂
  rw [hn g _ _ z J hJ, hx, mul_inv_cancel] at b₂
  rw [val_pull hJ, Category.id_comp, val_one, b₁, b₂]

end GlobalTheory.RigidLinearisation
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isAbelianScheme_of_common_generic_fibre
    {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B G : Over (Sp V)) [GrpObj B] [GrpObj G] (hB : IsAbelianScheme B) (hG : IsSemiAbelian G)
    (hext : ∀ f : (Over.pullback (spMap (algebraMap V K))).obj B ⟶ (Over.pullback (spMap (algebraMap V K))).obj G,
      IsMonHom f → ∃ F : B ⟶ G, (Over.pullback (spMap (algebraMap V K))).map F = f)
    (A : Over (Sp K)) [GrpObj A] {φ₁ : A.left ⟶ B.left} {φ₂ : A.left ⟶ G.left}
    (h₁ : IsGrpPullback A B (spMap (algebraMap V K)) φ₁) (h₂ : IsGrpPullback A G (spMap (algebraMap V K)) φ₂) :
    IsAbelianScheme G := by
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback B (spMap (algebraMap V K))) h₁
  obtain ⟨e', he', -⟩ := grpPullback_iso h₂ (isGrpPullback_pullback G (spMap (algebraMap V K)))
  obtain ⟨F, hF⟩ := hext (e.hom ≫ e'.hom) inferInstance
  refine isAbelianScheme_of_generically_surjective V K B G hB hG F ?_
  rintro x ⟨k, hk⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x k hk.symm
  have hsq : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G.hom (spMap (algebraMap V K)) =
      pullback.fst B.hom (spMap (algebraMap V K)) ≫ F.left := by
    simp
  rw [hF] at hsq
  have hid : (e ≪≫ e').inv.left ≫ (e.hom ≫ e'.hom).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Iso.trans_hom, Iso.inv_hom_id, Over.id_left]
  refine ⟨pullback.fst B.hom (spMap (algebraMap V K)) ((e ≪≫ e').inv.left z), ?_⟩
  calc F.left (pullback.fst B.hom (spMap (algebraMap V K)) ((e ≪≫ e').inv.left z))
      = ((e ≪≫ e').inv.left ≫ pullback.fst B.hom (spMap (algebraMap V K)) ≫ F.left) z := rfl
    _ = ((e ≪≫ e').inv.left ≫ (e.hom ≫ e'.hom).left ≫ pullback.fst G.hom (spMap (algebraMap V K))) z := by rw [hsq]
    _ = pullback.fst G.hom (spMap (algebraMap V K)) z := by rw [← Category.assoc, hid, Category.id_comp]
    _ = x := hz

theorem goodRedExt_of_isDiscreteValuationRing :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K], Y.GoodRedExt V K := by
  intro hext E _ _ _ H D l Xo c O _ β Y V K _ _ _ _ _ _ b y hy hex
  obtain ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, h𝒜, -, -, hp1, hp2, -⟩ := hex
  obtain ⟨y', t, m, hy's, hy'j, hab⟩ := GlobalTheory.model_point_extends E H D l Xo c O β Y V K b y hy
  refine ⟨y', hy's, hy'j, hab ?_⟩
  have hm := m.cart
  have hc := IsGrpPullback.comp hp2 Y.m.cart
  have hw : (φ₂ ≫ Y.m.cm.F) ≫ Y.t.G.hom = (A.hom ≫ spMap (algebraMap V K)) ≫ y' := by
    rw [hc.1.w, Category.assoc, hy'j]; rfl
  have h2 : IsGrpPullback A t.G (spMap (algebraMap V K)) (hm.1.lift _ _ hw) :=
    IsGrpPullback.cancel hm (hc.congr (by rw [hy'j]; rfl) (hm.1.lift_fst _ _ hw).symm) (hm.1.lift_snd _ _ hw)
  exact isAbelianScheme_of_common_generic_fibre 𝒜 t.G h𝒜 t.semi
    (fun f hf => (hext V K 𝒜 t.G (isSemiAbelian_of_isAbelianScheme 𝒜 h𝒜) t.semi f hf).exists.imp fun _ h => h.2)
    A hp1 h2

end GlobalTheory
end
