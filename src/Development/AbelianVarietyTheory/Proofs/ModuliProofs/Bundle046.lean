module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteClassesOfTraceFormDualEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
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
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.RelChart

open GlobalTheory.TangentOrigin

theorem evalPt_appLE {R : Type} [CommRing R] {X Y : Scheme.{0}} (v : Sp R ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV ((φ.appLE U V e).hom f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem top_le_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (v : Sp R ⟶ X) (φ : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ φ ⁻¹ᵁ U) (hV : ⊤ ≤ v ⁻¹ᵁ V) : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage]
  exact fun _ hp => e (hV hp)

theorem dual_ext {P R : Type} [CommRing P] [CommRing R] (ψ : P →+* R) (hψ : ψ.Etale)
    (F F' : R →+* DualNumber ℂ) (h : ∀ a, F (ψ a) = F' (ψ a)) (h0 : ∀ r, fstC (F r) = fstC (F' r)) : F = F' := by
  let _ := ψ.toAlgebra
  let _ : Algebra P (DualNumber ℂ) := (F'.comp ψ).toAlgebra
  have _ : Algebra.Etale P R := hψ
  let G : R →ₐ[P] DualNumber ℂ := { F with commutes' := h }
  let G₀ : R →ₐ[P] DualNumber ℂ := { F' with commutes' := fun _ => rfl }
  have hnil : IsNilpotent (RingHom.ker fstC) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' fstC hnil G G₀ h0
  exact RingHom.ext fun r => AlgHom.congr_fun hG r

theorem exists_chart_with_parameters :
    (∀ (m g : ℕ) (A R : Type) [CommRing A] [CommRing R] (ψ : MvPolynomial (Fin g) A →+* R) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (b₀ : Fin m → ℂ) (e : R →+* ℂ), ψ.Etale → IsOpen B → b₀ ∈ B → (∀ a, DifferentiableOn ℂ (fun b => φ b a) B) → (∀ a, e (ψ (MvPolynomial.C a)) = φ b₀ a) → ∃ (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (R →+* ℂ)) (n : ℕ) (f : Fin n → R) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))), IsOpen N ∧ IsOpen O ∧ (b₀, fun j => e (f j)) ∈ O ∧ (∀ a, DifferentiableOn ℂ (fun q => σ q a) N) ∧ (∀ q ∈ N, q.1 ∈ B ∧ (∀ a, σ q (ψ (MvPolynomial.C a)) = φ q.1 a) ∧ ∀ i, σ q (ψ (MvPolynomial.X i)) = q.2 i) ∧ ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → (b, fun j => x (f j)) ∈ O → (b, fun i => x (ψ (MvPolynomial.X i))) ∈ N ∧ σ (b, fun i => x (ψ (MvPolynomial.X i))) = x) → (∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') := by
  classical
  intro hring m g Z X p B y b₀ z₀ hp hB hb₀ hy hz₀
  obtain ⟨V, hV, U, hU, hz, hle, hsm⟩ :=
    hp.exists_isStandardSmoothOfRelativeDimension (z₀ (default : PrimeSpectrum ℂ))
  obtain ⟨ψ, hψC, hψ⟩ := hsm.exists_etale_mvPolynomial
  have hC : ∀ a, ψ (MvPolynomial.C a) = (p.appLE V U hle).hom a := fun a => RingHom.congr_fun hψC a
  have hzU : ⊤ ≤ z₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem z₀ U).2 hz
  have hy₀ : ⊤ ≤ y b₀ ⁻¹ᵁ V := hz₀ ▸ top_le_comp z₀ p hle hzU
  let φ : (Fin m → ℂ) → (Γ(X, V) →+* ℂ) := fun b =>
    if h : ⊤ ≤ y b ⁻¹ᵁ V then evalPt (y b) V h else evalPt (y b₀) V hy₀
  have hφ : ∀ b, ⊤ ≤ y b ⁻¹ᵁ V → ∀ a, φ b a = valAt' (y b) V a := fun b h a => by
    simp only [φ, dif_pos h, valAt'_eq_evalPt _ _ h]
  have hover : ∀ b (x : Sp ℂ ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = y b →
      ∀ a, evalPt x U hx (ψ (MvPolynomial.C a)) = φ b a := fun b x hx hxb a => by
    rw [hφ b (hxb ▸ top_le_comp x p hle hx), hC, ← valAt'_eq_evalPt, valAt'_appLE _ _ _ _ _ _ hx, hxb]
  obtain ⟨N, σ, n, f, O, hN, hO, h₀, hσd, hσ, hrec⟩ := hring m g Γ(X, V) Γ(Z, U) ψ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ V} φ b₀
    (evalPt z₀ U hzU) hψ (hy V 0).1 ⟨hb₀, hy₀⟩
    (fun a => (hy V a).2.congr fun b hb => hφ b hb.2 a) (hover b₀ z₀ hzU hz₀)
  choose s hsU hs using fun q => exists_evalPt_eq hU (σ q)
  have hval : ∀ q a, valAt' (s q) U a = σ q a := fun q a => by
    rw [valAt'_eq_evalPt _ _ (hsU q), hs]
  refine ⟨U, fun i => ψ (MvPolynomial.X i), n, f, N, O, s, hN, hO, hzU, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [valAt'_eq_evalPt _ _ hzU] using h₀
  · intro W a
    refine holFamily_of_affine valAt'_rules N Z s (fun q _ => ⟨U, hU, hsU q, ?_, fun r => ?_⟩) W a
    · simp only [hsU, and_true]
      exact hN
    · simp only [hsU, and_true, hval]
      exact hσd r
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hσ q hq
    refine ⟨ext_evalPt hV (top_le_comp _ p hle (hsU q)) h1.2 (RingHom.ext fun a => ?_), hsU q,
      fun i => (hval _ _).trans (h3 i)⟩
    rw [← evalPt_appLE _ p V U hle a (hsU q), hs, ← hC, h2, hφ _ h1.2, valAt'_eq_evalPt]
  · intro b x hxb hx hxO
    simp only [valAt'_eq_evalPt _ _ hx] at hxO ⊢
    obtain ⟨h1, h2⟩ := hrec b (evalPt x U hx) (hover b x hx hxb) hxO
    exact ⟨h1, ext_evalPt hU (hsU _) hx ((hs _).trans h2)⟩
  · intro v v' h h' hvp hv0 hvt
    refine ext_evalPt hU h h' (dual_ext ψ hψ _ _ (fun a => ?_) fun r => ?_)
    · have : (evalPt v U h).comp ψ = (evalPt v' U h').comp ψ := by
        refine MvPolynomial.ringHom_ext (fun c => ?_) hvt
        simp only [RingHom.comp_apply, hC]
        rw [evalPt_appLE v p V U hle c h (top_le_comp v p hle h),
          evalPt_appLE v' p V U hle c h' (top_le_comp v' p hle h')]
        simp only [hvp]
      exact RingHom.congr_fun this a
    · rw [← evalPt_spMap_comp fstC v U h ((top_le_preimage_iff v U).1 h),
        ← evalPt_spMap_comp fstC v' U h' ((top_le_preimage_iff v' U).1 h')]
      have hv0' : spMap fstC ≫ v = spMap fstC ≫ v' := hv0
      simp only [hv0']

end GlobalTheory.RelChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.GlueTwoLB

variable {X Y Z : Scheme.{0}}

def stU (f : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (f z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (f.stalkMap z).hom.toMonoidHom

theorem stU_gm (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    stU f z (gm g (f z) U a) = gm (f ≫ g) z U a := by
  rw [← gm_pull f g z U h]
  apply Units.ext
  rw [gm_val f z (g ⁻¹ᵁ U) h]
  show (f.stalkMap z).hom (gm g (f z) U a).val = _
  rw [gm_val g (f z) U h]
  exact Scheme.Hom.germ_stalkMap_apply f _ z h _

theorem stU_injective (f : Z ⟶ Y) [IsOpenImmersion f] (z : Z) : Function.Injective (stU f z) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (f.stalkMap z)).1

theorem stU_gm_id (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)ˣ) :
    stU f z (gm (𝟙 Y) (f z) U a) = gm f z U a := by
  rw [stU_gm f (𝟙 Y) z U h, Category.comp_id]

theorem exists_push (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (W : Z.Opens) (V : Y.Opens)
    (h : ∀ y ∈ V, ∃ z ∈ W, ψ z = y) (a : Γ(Z, W)ˣ) :
    ∃ b : Γ(Y, V)ˣ, ∀ z : Z, ψ z ∈ V → gm ψ z V b = gm (𝟙 Z) z W a := by
  have hle : V ≤ ψ ''ᵁ W := fun y hy => h y hy
  refine ⟨res hle (Units.map (ψ.appIso W).inv.hom.toMonoidHom a), fun z hz => ?_⟩
  have hW : z ∈ W := by
    obtain ⟨z', hz', e⟩ := h _ hz
    rwa [← ψ.isOpenEmbedding.injective e]
  rw [gm_res ψ z hle hz]
  apply Units.ext
  rw [gm_val ψ z _ (hle hz), gm_val (𝟙 Z) z W hW]
  have e := congrArg (fun q => q.hom a.val) (ψ.appIso_inv_app W)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact (congrArg (Z.presheaf.germ (ψ ⁻¹ᵁ ψ ''ᵁ W) z (hle hz)).hom e).trans
    (TopCat.Presheaf.germ_res_apply Z.presheaf _ z (hle hz) _)

theorem iso_self {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem isLB_of_stalk {L : LB X} (hc : ∀ x, ∃ i, x ∈ L.U i)
    (h : ∀ x i j k, x ∈ L.U i → x ∈ L.U j → x ∈ L.U k →
      gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (L.g j k) = gm (𝟙 X) x _ (L.g i k)) : L.IsLB := {
  cover := top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hc y)
  g_self i := unit_ext fun y hy => by
    rw [gm_res (𝟙 X) y _ hy, map_one]
    exact mul_eq_left.1 (h y i i i hy hy hy)
  cocycle i j k := unit_ext fun y hy => by
    rw [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy]
    exact h y i j k hy.1.1 hy.1.2 hy.2 }

theorem cocycle_descend {L : LB Y} (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (z : Z) {i j k : L.ι}
    (hi : ψ z ∈ L.U i) (hj : ψ z ∈ L.U j) (hk : ψ z ∈ L.U k)
    (h : gm ψ z _ (L.g i j) * gm ψ z _ (L.g j k) = gm ψ z _ (L.g i k)) :
    gm (𝟙 Y) (ψ z) _ (L.g i j) * gm (𝟙 Y) (ψ z) _ (L.g j k) = gm (𝟙 Y) (ψ z) _ (L.g i k) := by
  apply stU_injective ψ z
  rw [map_mul, stU_gm_id ψ z (L.U i ⊓ L.U j) ⟨hi, hj⟩, stU_gm_id ψ z (L.U j ⊓ L.U k) ⟨hj, hk⟩,
    stU_gm_id ψ z (L.U i ⊓ L.U k) ⟨hi, hk⟩, h]

theorem mem_of_mem_image (ψ : Z ⟶ Y) [IsOpenImmersion ψ] {W : Z.Opens} {z : Z} (h : ψ z ∈ ψ ''ᵁ W) : z ∈ W := by
  obtain ⟨z', hz', e⟩ := h
  rwa [← ψ.isOpenEmbedding.injective e]

theorem exists_push_inf (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (W W' : Z.Opens) (a : Γ(Z, W ⊓ W')ˣ) :
    ∃ b : Γ(Y, ψ ''ᵁ W ⊓ ψ ''ᵁ W')ˣ, ∀ z : Z, z ∈ W → z ∈ W' →
      gm ψ z (ψ ''ᵁ W ⊓ ψ ''ᵁ W') b = gm (𝟙 Z) z (W ⊓ W') a := by
  obtain ⟨b, hb⟩ := exists_push ψ (W ⊓ W') (ψ ''ᵁ W ⊓ ψ ''ᵁ W') (by
    rintro y ⟨⟨z, hz, rfl⟩, h'⟩
    exact ⟨z, ⟨hz, mem_of_mem_image ψ h'⟩, rfl⟩) a
  exact ⟨b, fun z h h' => hb z ⟨⟨z, h, rfl⟩, ⟨z, h', rfl⟩⟩⟩

theorem gen_stalk {Y₀ Y₁ Y₂ : Scheme.{0}} {φ₁ : Y₀ ⟶ Y₁} {φ₂ : Y₀ ⟶ Y₂} {L₁ : LB Y₁} {L₂ : LB Y₂}
    {w : LB.Iso (L₁.pull φ₁) (L₂.pull φ₂)} (hw : w.IsGen) (y : Y₀) {i i' : L₁.ι} {k k' : L₂.ι}
    (hi : φ₁ y ∈ L₁.U i) (hi' : φ₁ y ∈ L₁.U i') (hk : φ₂ y ∈ L₂.U k) (hk' : φ₂ y ∈ L₂.U k') :
    gw w (𝟙 Y₀) y k (fun _ => i) = gm φ₂ y _ (L₂.g k k') * (gm φ₁ y _ (L₁.g i i'))⁻¹ *
      gw w (𝟙 Y₀) y k' (fun _ => i') := by
  have := (isGen_iff w).1 hw Y₀ (𝟙 Y₀) y k k' (fun _ => i) (fun _ => i') hk hk' (mem_pull.2 hi) (mem_pull.2 hi')
  rw [gm_pull_g L₁ φ₁ (𝟙 Y₀) y _ _ (mem_pull.2 hi) (mem_pull.2 hi'), Category.id_comp, Category.id_comp] at this
  exact this

def pullChart (L : LB X) (F : Y ⟶ X) : ChartPull (L.pull F) L F where
  idx J := J PUnit.unit
  le _ _ hy := mem_pull.1 hy
  g y J J' hj hj' := (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp])

theorem glue : ∀ (Y Y₀ Y₁ Y₂ : Scheme.{0}) (ψ₁ : Y₁ ⟶ Y) (ψ₂ : Y₂ ⟶ Y) (φ₁ : Y₀ ⟶ Y₁) (φ₂ : Y₀ ⟶ Y₂) (L₁ : LB Y₁) (L₂ : LB Y₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → Set.range ψ₁ ∪ Set.range ψ₂ = Set.univ → L₁.IsLB → L₂.IsLB → LBIso (L₁.pull φ₁) (L₂.pull φ₂) → ∃ L : LB Y, L.IsLB ∧ LBIso L₁ (L.pull ψ₁) ∧ LBIso L₂ (L.pull ψ₂) := by
  intro Y Y₀ Y₁ Y₂ ψ₁ ψ₂ φ₁ φ₂ L₁ L₂ o₁ o₂ hp hcov h₁ h₂ ⟨w, hw⟩
  have p₁ : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback hp.flip o₂
  have hpt : ∀ y, ψ₁ (φ₁ y) = ψ₂ (φ₂ y) := fun y => congrArg (fun g => g y) hp.w
  have lift : ∀ y₁ y₂, ψ₁ y₁ = ψ₂ y₂ → ∃ y, φ₁ y = y₁ ∧ φ₂ y = y₂ := fun y₁ y₂ e =>
    Scheme.exists_preimage_of_isPullback hp y₁ y₂ e
  have hsq := hp.w
  choose g₁ hg₁ using fun i j => exists_push_inf ψ₁ _ _ (L₁.g i j)
  choose g₂ hg₂ using fun i j => exists_push_inf ψ₂ _ _ (L₂.g i j)
  have hm : ∀ (k : L₂.ι) (i : L₁.ι), ∃ b : Γ(Y, ψ₂ ''ᵁ L₂.U k ⊓ ψ₁ ''ᵁ L₁.U i)ˣ, ∀ y : Y₀,
      φ₂ y ∈ L₂.U k → φ₁ y ∈ L₁.U i → gm (φ₁ ≫ ψ₁) y _ b = gw w (𝟙 Y₀) y k (fun _ => i) := by
    intro k i
    obtain ⟨b, hb⟩ := exists_push (φ₁ ≫ ψ₁) ((L₂.pull φ₂).U (fun _ => k) ⊓ (L₁.pull φ₁).U (fun _ => i))
      (ψ₂ ''ᵁ L₂.U k ⊓ ψ₁ ''ᵁ L₁.U i) (by
        rintro y ⟨⟨y₂, h₂, rfl⟩, ⟨y₁, h₁, e⟩⟩
        obtain ⟨z, rfl, rfl⟩ := lift y₁ y₂ e
        exact ⟨z, ⟨mem_pull.2 h₂, mem_pull.2 h₁⟩, e⟩) (w.s (fun _ => k, fun _ => i))
    exact ⟨b, fun y hk hi => hb y ⟨⟨_, hk, (hpt y).symm⟩, ⟨_, hi, rfl⟩⟩⟩
  choose m hm using hm
  let L : LB Y :=
    { «ι» := L₁.ι ⊕ L₂.ι
      U := Sum.elim (fun i => ψ₁ ''ᵁ L₁.U i) (fun k => ψ₂ ''ᵁ L₂.U k)
      g := fun p q => match p, q with
        | .inl i, .inl j => g₁ i j
        | .inr k, .inr l => g₂ k l
        | .inr k, .inl i => m k i
        | .inl i, .inr k => (res (le_inf inf_le_right inf_le_left) (m k i))⁻¹ }

  have key : ∀ y : Y₀, ∃ t : L.ι → (Y₀.presheaf.stalk y)ˣ, ∀ p q, ψ₁ (φ₁ y) ∈ L.U p → ψ₁ (φ₁ y) ∈ L.U q →
      gm (φ₁ ≫ ψ₁) y _ (L.g p q) = t p * (t q)⁻¹ := by
    intro y
    obtain ⟨i₀, hi₀⟩ := exists_chart h₁ (φ₁ y)
    have ml : ∀ i, ψ₁ (φ₁ y) ∈ L.U (.inl i) → φ₁ y ∈ L₁.U i := fun i h => mem_of_mem_image ψ₁ h
    have mr : ∀ k, ψ₁ (φ₁ y) ∈ L.U (.inr k) → φ₂ y ∈ L₂.U k := fun k h => mem_of_mem_image ψ₂ (hpt y ▸ h)
    have mix : ∀ k i, φ₂ y ∈ L₂.U k → φ₁ y ∈ L₁.U i → gm (φ₁ ≫ ψ₁) y _ (m k i) =
        gw w (𝟙 Y₀) y k (fun _ => i₀) * (gm φ₁ y _ (L₁.g i i₀))⁻¹ := fun k i hk hi => by
      rw [hm k i y hk hi, gen_stalk hw y hi hi₀ hk hk, gm_self h₂ φ₂ y hk, _root_.one_mul, mul_comm]
    refine ⟨Sum.elim (fun i => gm φ₁ y _ (L₁.g i i₀)) (fun k => gw w (𝟙 Y₀) y k (fun _ => i₀)), ?_⟩
    rintro (i | k) (j | l) hp hq
    · have e := congrArg (stU φ₁ y) (hg₁ i j _ (ml i hp) (ml j hq))
      rw [stU_gm φ₁ ψ₁ y (ψ₁ ''ᵁ L₁.U i ⊓ ψ₁ ''ᵁ L₁.U j) ⟨hp, hq⟩, stU_gm_id φ₁ y (L₁.U i ⊓ L₁.U j) ⟨ml i hp, ml j hq⟩] at e
      refine e.trans ?_
      exact eq_mul_inv_of_mul_eq (gm_cocycle h₁ φ₁ y (ml i hp) (ml j hq) hi₀)
    · refine ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res (φ₁ ≫ ψ₁) y _
        (show (φ₁ ≫ ψ₁) y ∈ ψ₁ ''ᵁ L₁.U i ⊓ ψ₂ ''ᵁ L₂.U l from ⟨hp, hq⟩) _).trans
        (mix l i (mr l hq) (ml i hp))))).trans ?_
      rw [mul_inv_rev, inv_inv]; rfl
    · exact mix k j (mr k hp) (ml j hq)
    · have e := congrArg (stU φ₂ y) (hg₂ k l _ (mr k hp) (mr l hq))
      rw [stU_gm φ₂ ψ₂ y (ψ₂ ''ᵁ L₂.U k ⊓ ψ₂ ''ᵁ L₂.U l) ⟨⟨_, mr k hp, rfl⟩, ⟨_, mr l hq, rfl⟩⟩,
        stU_gm_id φ₂ y (L₂.U k ⊓ L₂.U l) ⟨mr k hp, mr l hq⟩, ← hsq] at e
      refine e.trans (eq_mul_inv_of_mul_eq ?_)
      have := gen_stalk hw y hi₀ hi₀ (mr k hp) (mr l hq)
      rw [gm_self h₁ φ₁ y hi₀, inv_one, _root_.mul_one] at this
      exact this.symm
  have hL : L.IsLB := by
    refine isLB_of_stalk (fun x => ?_) ?_
    · rcases (hcov.symm ▸ Set.mem_univ x : x ∈ Set.range ψ₁ ∪ Set.range ψ₂) with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · obtain ⟨i, hi⟩ := exists_chart h₁ y
        exact ⟨.inl i, y, hi, rfl⟩
      · obtain ⟨i, hi⟩ := exists_chart h₂ y
        exact ⟨.inr i, y, hi, rfl⟩
    have ov : ∀ x p q r (i : L₁.ι) (k : L₂.ι), x ∈ L.U (.inl i) → x ∈ L.U (.inr k) →
        x ∈ L.U p → x ∈ L.U q → x ∈ L.U r →
        gm (𝟙 Y) x _ (L.g p q) * gm (𝟙 Y) x _ (L.g q r) = gm (𝟙 Y) x _ (L.g p r) := by
      rintro x p q r i k ⟨y₁, -, rfl⟩ ⟨y₂, -, e⟩ hp hq hr
      obtain ⟨y, rfl, rfl⟩ := lift y₁ y₂ e.symm
      obtain ⟨t, ht⟩ := key y
      refine cocycle_descend (φ₁ ≫ ψ₁) y hp hq hr ?_
      rw [ht p q hp hq, ht q r hq hr, ht p r hp hr, _root_.mul_assoc, inv_mul_cancel_left]
    rintro x (i | i) (j | j) (k | k) hi hj hk
    · obtain ⟨y, hy, rfl⟩ := id hi
      have hj' := mem_of_mem_image ψ₁ hj
      have hk' := mem_of_mem_image ψ₁ hk
      refine cocycle_descend ψ₁ y hi hj hk ?_
      exact (congrArg₂ (· * ·) (hg₁ i j y hy hj') (hg₁ j k y hj' hk')).trans
        ((gm_cocycle h₁ (𝟙 _) y hy hj' hk').trans (hg₁ i k y hy hk').symm)
    · exact ov x _ _ _ i k hi hk hi hj hk
    · exact ov x _ _ _ i j hi hj hi hj hk
    · exact ov x _ _ _ i j hi hj hi hj hk
    · exact ov x _ _ _ j i hj hi hi hj hk
    · exact ov x _ _ _ j i hj hi hi hj hk
    · exact ov x _ _ _ k i hk hi hi hj hk
    · obtain ⟨y, hy, rfl⟩ := id hi
      have hj' := mem_of_mem_image ψ₂ hj
      have hk' := mem_of_mem_image ψ₂ hk
      refine cocycle_descend ψ₂ y hi hj hk ?_
      exact (congrArg₂ (· * ·) (hg₂ i j y hy hj') (hg₂ j k y hj' hk')).trans
        ((gm_cocycle h₂ (𝟙 _) y hy hj' hk').trans (hg₂ i k y hy hk').symm)
  let c₁ : ChartPull L₁ L ψ₁ := ⟨Sum.inl, fun i y hy => ⟨y, hy, rfl⟩, fun y i j hi hj => (hg₁ i j y hi hj).symm⟩
  let c₂ : ChartPull L₂ L ψ₂ := ⟨Sum.inr, fun i y hy => ⟨y, hy, rfl⟩, fun y i j hi hj => (hg₂ i j y hi hj).symm⟩
  exact ⟨L, hL, LBIso.chartPull c₁ (pullChart L ψ₁) (iso_self hL),
    LBIso.chartPull c₂ (pullChart L ψ₂) (iso_self hL)⟩

end GlobalTheory.GlueTwoLB
end
end

section

namespace GlobalTheory.MarkedGenus

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_fin_representatives {α β : Type*} [Finite β] (c : α → β) :
    ∃ (r : ℕ) (g : Fin r → α), ∀ a, ∃ j, c (g j) = c a := by
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range c)
  refine ⟨r, fun j => (e.symm j).2.choose, fun a => ⟨e ⟨c a, a, rfl⟩, ?_⟩⟩
  rw [(e.symm (e ⟨c a, a, rfl⟩)).2.choose_spec, Equiv.symm_apply_apply]

theorem finite_linearMap {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Finite R M] [Finite N] : Finite (M →ₗ[R] N) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine Finite.of_injective (fun φ : M →ₗ[R] N => fun x : (s : Set M) => φ x) ?_
  intro φ ψ h
  exact LinearMap.ext_on hs (fun x hx => congrFun h ⟨x, hx⟩)

theorem finite_quotient_nsmul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite ℤ R] [Module.Finite R M] {k : ℕ} (hk : 0 < k) :
    Finite (M ⧸ LinearMap.range (k • (LinearMap.id : M →ₗ[R] M))) := by
  set P := LinearMap.range (k • (LinearMap.id : M →ₗ[R] M))
  have hfin : Module.Finite ℤ (M ⧸ P) := Module.Finite.trans R (M ⧸ P)
  have hfg : AddGroup.FG (M ⧸ P) := Module.Finite.iff_addGroup_fg.mp hfin
  refine AddCommGroup.finite_of_fg_isAddTorsion _ (fun q => ?_)
  refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨k, hk, ?_⟩
  induction q using Submodule.Quotient.induction_on with
  | H m =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simp⟩

private lemma match_mod_lemma {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {k n : ℕ} (Dr : Fin n → Datum H) {A B : Datum H} (j1 j2 : Fin n)
    (e1 : A.La ≃ₗ[𝓞 E] (Dr j1).La) (e2 : B.La ≃ₗ[𝓞 E] (Dr j2).La)
    (he1 : ∀ x y, (Dr j1).EF (e1 x) (e1 y) = A.EF x y) (he2 : ∀ x y, (Dr j2).EF (e2 x) (e2 y) = B.EF x y)
    (fA : D.La →ₗ[𝓞 E] A.La) (fB : D.La →ₗ[𝓞 E] B.La)
    (h : (⟨j1, (LinearMap.range (k • (LinearMap.id : (Dr j1).La →ₗ[𝓞 E] (Dr j1).La))).mkQ.comp
        (e1.toLinearMap.comp fA)⟩ :
        Σ j : Fin n, D.La →ₗ[𝓞 E] ((Dr j).La ⧸ LinearMap.range (k • (LinearMap.id : (Dr j).La →ₗ[𝓞 E] (Dr j).La)))) =
      ⟨j2, (LinearMap.range (k • (LinearMap.id : (Dr j2).La →ₗ[𝓞 E] (Dr j2).La))).mkQ.comp
        (e2.toLinearMap.comp fB)⟩) :
    ∃ e : B.La ≃ₗ[𝓞 E] A.La, (∀ x y, A.EF (e x) (e y) = B.EF x y) ∧ ∀ x, ∃ y, e (fB x) = fA x + k • y := by
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h
  have hm := eq_of_heq hh
  refine ⟨e2.trans e1.symm, fun x y => ?_, fun x => ?_⟩
  · rw [← he1]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he2]
  · have hx := LinearMap.congr_fun hm x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at hx
    rw [Submodule.Quotient.eq] at hx
    obtain ⟨z, hz⟩ := hx
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hz
    refine ⟨-(e1.symm z), e1.injective ?_⟩
    have h2 : e2 (fB x) = e1 (fA x) - k • z := by rw [hz]; abel
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_add (f := _), map_neg, map_nsmul, h2,
      smul_neg, sub_eq_add_neg]

theorem finite_marked_data_in_genus :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k : ℕ) (ζ : ℂ), 0 < k → ∃ (r : ℕ) (Di : Fin r → Datum H) (fi : ∀ i, ℕ → D.La →ₗ[𝓞 E] (Di i).La) (νi : Fin r → ℕ → ℤ), (∀ i, ((Di i).p = D.p ∧ (Di i).q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, fi i (n * m) x = fi i n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, fi i n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = fi i n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ (Di i).EF (fi i n x) (fi i n x') - νi i n * D.EF x x') ∧ ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (νi i k : ℂ) / k)) ∧ ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → ∃ (i : Fin r) (e : D'.La ≃ₗ[𝓞 E] (Di i).La), (∀ x y, (Di i).EF (e x) (e y) = D'.EF x y) ∧ ∀ x, ∃ y, e (f k x) = fi i k x + k • y := by
  intro E _ _ _ H D k ζ hk
  obtain ⟨n, Dr, hDr, hcls⟩ := GlobalTheory.DatumClasses.finite_data_of_signature E H D.p D.q
  let Q : Fin n → Type := fun j =>
    (Dr j).La ⧸ LinearMap.range (k • (LinearMap.id : (Dr j).La →ₗ[𝓞 E] (Dr j).La))
  have hQ : ∀ j, Finite (D.La →ₗ[𝓞 E] Q j) := fun j => by
    have := D.fin
    have := (Dr j).fin
    have : Finite (Q j) := finite_quotient_nsmul hk
    exact finite_linearMap
  let Cond : (D' : Datum H) → (ℕ → D.La →ₗ[𝓞 E] D'.La) → (ℕ → ℤ) → Prop := fun D' f ν =>
    (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧
      (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧
      ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧
    ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k)
  let α := {a : Σ D' : Datum H, (ℕ → D.La →ₗ[𝓞 E] D'.La) × (ℕ → ℤ) // Cond a.1 a.2.1 a.2.2}
  choose jf ef hef using fun a : α => hcls a.1.1 a.2.1.1 a.2.1.2.1
  let c : α → Σ j : Fin n, (D.La →ₗ[𝓞 E] Q j) := fun a =>
    ⟨jf a, (LinearMap.range (k • (LinearMap.id : (Dr (jf a)).La →ₗ[𝓞 E] (Dr (jf a)).La))).mkQ.comp
      ((ef a).toLinearMap.comp (a.1.2.1 k))⟩
  obtain ⟨r, g, hg⟩ := exists_fin_representatives c
  refine ⟨r, fun i => (g i).1.1, fun i => (g i).1.2.1, fun i => (g i).1.2.2, fun i => (g i).2, ?_⟩
  intro D' f ν hc hζ
  obtain ⟨i, hi⟩ := hg ⟨⟨D', f, ν⟩, hc, hζ⟩
  exact ⟨i, match_mod_lemma Dr _ _ (ef (g i)) (ef ⟨⟨D', f, ν⟩, hc, hζ⟩) (hef (g i)) (hef _) _ _ hi⟩

end GlobalTheory.MarkedGenus
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.ObjMaps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab_id {S : Scheme.{0}} (t : SAB H S) : ∃ m : SABMap t t (𝟙 S), m.φ = 𝟙 _ :=
  ⟨ObjComp.sabMapId t, rfl⟩

theorem exists_sab_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m : SABMap t' t f) (m' : SABMap t'' t' g) : ∃ n : SABMap t'' t (g ≫ f), n.φ = m'.φ ≫ m.φ :=
  sabComp pullCubComp E H S S' S'' t t' t'' f g m m'

theorem exists_sab_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m : SABMap t' t f) (n : SABMap t'' t (g ≫ f)) : ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ :=
  sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n

end GlobalTheory.ObjMaps

namespace GlobalTheory

theorem ObjMaps.id_comp_cancel :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ o _ _ =>
    ⟨⟨ObjComp.objMapId o, rfl⟩, fun _ _ m => ⟨ObjComp.objMap_comp m, ObjComp.objMap_cancel m⟩⟩

end GlobalTheory
end
end
