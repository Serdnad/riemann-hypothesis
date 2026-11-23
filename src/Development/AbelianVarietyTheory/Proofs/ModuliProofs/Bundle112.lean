module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GoodPtOfIrredOfMulPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreFrameOfMemClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle100
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle106
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionDense

open GoodPoint

theorem exists_sec_lPow {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (T : Over S) (k : ℕ)
    (s : (lbPow L k).Sec) : ∃ s' : LB.Sec (LPow A L k T), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → (IsUnit (powVal s' r z J) ↔ (r ≫ (snd T A).left) z ∈ nonzeroLocus s) := by
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => (k : ℤ))
    (fun U _ h => by simp [Fintype.prod_sum_type, -Over.snd_left])
    (pullMulSec (L := L) (φ := fun _ : PUnit => 𝟙 A.left) (ε := fun _ => (k : ℤ)) s (snd T A).left
      (LB.oneGen L (Y := (T ⊗ A).left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)).symm))
  refine ⟨s', fun Z r z J hJ => ?_⟩
  have e := (hs' Z r z J hJ).trans (sval_pullMulSec _ _ _ _ r z hJ)
  refine (iff_of_eq (congrArg IsUnit e)).trans ?_
  rw [Units.isUnit_mul_units]
  exact (mem_nonzeroLocus_iff_pull s _ z (hJ.mem (fun _ : PUnit => 𝟙 A.left) _)).symm

variable {K : Type} [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K)))

theorem exists_mem_nonzeroLocus (hI : IrredSt) (hK : KerPowSt) (k : ℕ) (hk : 4 ≤ k) (hkK : (k : K) ≠ 0)
    (B : Set (baseOver (Spec (CommRingCat.of K)) ⟶ P.A)) (hB : ∀ w, w ^ k = 1 → ∀ b ∈ B, w * b ∈ B)
    (s t : (lbPow P.L k).Sec) (x : P.A.left) (hx : x ∈ nonzeroLocus s)
    (b : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (hb : b ∈ B)
    (p : (baseOver (Spec (CommRingCat.of K))).left) (ht : b.left p ∈ nonzeroLocus t) :
    ∃ b' ∈ B, ∃ p', b'.left p' ∈ nonzeroLocus s := by
  by_contra hcon
  obtain ⟨s', hs'⟩ := exists_sec_lPow P.isLB (baseOver _) k s
  obtain ⟨t', ht'⟩ := exists_sec_lPow P.isLB (baseOver _) k t
  rcases hI K P k (Or.inr hk) hkK (vanishing P.L _ B)
    (fun θ s s' h hsB q hq y J hJ => by
      obtain ⟨c, hc⟩ := powVal_act h (ptSecT P.A q).left hJ
      rw [← Over.comp_left, ptSecT_translT] at hc
      refine (congrArg (· ∈ IsLocalRing.maximalIdeal _) hc).mpr
        (Ideal.mul_mem_left _ _ (hsB _ (hB _ ?_ q hq) y J hJ))
      exact (hK _ P k (by omega) _ θ.pt).1 fun p => ⟨⊤, trivial, exists_isGen_pull _ θ.φ θ.isGen _⟩) with h | h
  · have hm : SecM.ofSec P.A s' ∈ vanishing P.L _ B := fun q hq y J hJ hu => by
      have := (hs' _ _ y J hJ).1 hu
      rw [← Over.comp_left, ptSecT_snd] at this
      exact hcon ⟨q, hq, y, this⟩
    rw [h, Submodule.mem_bot] at hm
    choose J hJ using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ x)
    have hu := (hs' _ (unitInv P.A).left x J hJ).2 (by rw [← Over.comp_left, unitInv_snd]; exact hx)
    have e : powVal s' (unitInv P.A).left x J = 0 :=
      (congrArg (gs _ x _) (congrFun (congrArg Subtype.val hm) _)).trans (gs_zero _ x _)
    rw [e] at hu
    exact not_isUnit_zero hu
  · choose J hJ using fun χ : (baseOver (Spec (CommRingCat.of K))).left ⟶ P.A.left => exists_chart P.isLB (χ p)
    have hm : SecM.ofSec P.A t' ∈ vanishing P.L _ B := by rw [h]; trivial
    exact hm b hb p J hJ ((ht' _ _ p J hJ).2 (by rw [← Over.comp_left, ptSecT_snd]; exact ht))

theorem dense_torsion [CharZero K] (hI : IrredSt) (hK : KerPowSt) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ x ^ n = 1}, Set.range x.left) := by
  have := P.isAb.comm
  have hA := isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample
  refine dense_iff_inter_open.2 fun U hU ⟨x, hx⟩ => ?_
  obtain ⟨n, hn, s, hs, hle, -⟩ := hA.exists_affine_le (x := x) (U := ⟨U, hU⟩) hx
  let p : (baseOver (Spec (CommRingCat.of K))).left := IsLocalRing.closedPoint K
  obtain ⟨m, hm, t, ht, -⟩ := hA.exists_affine ((1 : baseOver (Spec (CommRingCat.of K)) ⟶ P.A).left p)
  have e₁ := nonzeroLocus_secPow s (k := m * 4) (by omega)
  have e₂ := nonzeroLocus_secPow t (k := n * 4) (by omega)
  have hk : 4 ≤ n * (m * 4) := by nlinarith [Nat.mul_pos hn hm]
  obtain ⟨b, hb, q, hq⟩ := exists_mem_nonzeroLocus P hI hK (n * (m * 4)) hk (Nat.cast_ne_zero.2 (by omega))
    {x | ∃ n : ℕ, 0 < n ∧ x ^ n = 1} (fun w hw b ⟨l, hl, hb⟩ => ⟨n * (m * 4) * l, Nat.mul_pos (by omega) hl, by
      rw [mul_pow, pow_mul w, hw, one_pow, mul_comm _ l, pow_mul, hb, one_pow, _root_.one_mul]⟩)
    (secPow s (m * 4)) (secCast (by ring) (secPow t (n * 4))) x (e₁.ge hs) 1 ⟨1, one_pos, one_pow _⟩ p (e₂.ge ht)
  exact ⟨b.left q, hle (e₁.le hq), Set.mem_iUnion₂.2 ⟨b, hb, q, rfl⟩⟩

end GlobalTheory.TorsionDense
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ThetaFamily

theorem thetaChar_family {g m : ℕ} {B : Set (Fin m → ℂ)} {p q : Fin g → (Fin m → ℂ) → (Fin g → ℂ)}
    {h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hp : ∀ k, DifferentiableOn ℂ (p k) B)
    (hq : ∀ k, DifferentiableOn ℂ (q k) B)
    (hh : ∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h b).mulVec (p k b) = Pi.single k 1 ∧
      (h b).mulVec (q k b) = (τ b).mulVec (Pi.single k 1))
    {c₁ c₂ : Fin g → ℂ} (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) :
    DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ ((h bz.1).mulVec bz.2))
      (B ×ˢ Set.univ) ∧ ∀ b ∈ B, ∀ z, ∃ᶠ w in nhds z, thetaChar (τ b) c₁ c₂ ((h b).mulVec w) ≠ 0 := by
  have re : ∀ {c : Fin g → ℂ}, (∀ k, c k = 0 ∨ c k = 1 / 2) → ∃ a : Fin g → ℝ, c = fun i => (a i : ℂ) := fun {c} hc =>
    ⟨fun i => (c i).re, funext fun i => by rcases hc i with e | e <;> simp [e]⟩
  obtain ⟨a₁, rfl⟩ := re h₁
  obtain ⟨a₂, rfl⟩ := re h₂
  have hinv : ∀ b ∈ B, h b * Matrix.of (fun i k => p k b i) = 1 := fun b hb => by
    ext i k
    have := congrFun ((hh b hb).2 k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  have dh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B :=
    differentiableOn_left_inverse (fun i k => differentiableOn_pi.1 (hp k) i) hinv
  have dτ : ∀ i k, DifferentiableOn ℂ (fun b => τ b i k) B := fun i k => by
    refine (DifferentiableOn.fun_sum (u := Finset.univ) fun j _ =>
      (dh i j).mul (differentiableOn_pi.1 (hq k) j)).congr fun b hb => ?_
    have := congrFun ((hh b hb).2 k).2 i
    rw [Matrix.mulVec_single_one] at this
    exact this.symm
  have fst : ∀ {f : (Fin m → ℂ) → ℂ}, DifferentiableOn ℂ f B →
      DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => f bz.1) (B ×ˢ Set.univ) := fun hf =>
    hf.comp differentiableOn_fst fun _ h => h.1
  refine ⟨CanTh.differentiableOn_thetaChar (T := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => τ bz.1)
    (Z := fun bz => (h bz.1).mulVec bz.2) (fun i k => fst (dτ i k)) (differentiableOn_pi.2 fun i => ?_)
    (fun w hw => CanTh.mem_thetaDomain (hh _ hw.1).1) a₁ a₂, fun b hb => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun j _ => (fst (dh i j)).mul (by fun_prop)
  · have dl : Differentiable ℂ (fun w : Fin g → ℂ => (h b).mulVec w) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h b))).differentiable
    refine frequently_ne_zero_of_entire
      (θ := fun w => thetaChar (τ b) (fun i => (a₁ i : ℂ)) (fun i => (a₂ i : ℂ)) ((h b).mulVec w))
      ((CanTh.differentiable_thetaChar (CanTh.mem_thetaDomain (hh b hb).1) a₁ a₂).comp dl) fun h0 => ?_
    refine thetaChar_ne_zero (hh b hb).1 a₁ a₂ (funext fun w => ?_)
    have := congrFun h0 ((Matrix.of (fun i k => p k b i)).mulVec w)
    rwa [Matrix.mulVec_mulVec, hinv b hb, Matrix.one_mulVec] at this

theorem exists_thetaFrame_of_preconnected : Out.Laws → (∀ (k : Type) [Field k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶
    Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g →
    ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas
    a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h
    b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single
    (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) → ∀ b₀ ∈ B, ∃! cc : (Fin g → ℂ) × (Fin g →
    ℂ), ∃ c₁ c₂, cc = (c₁,
    c₂) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP {b₀} y (fun b z => (e
    b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z))) → (∀ (X
    : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (x : X), ∃ (V : X.Opens) (θ
    : ∀ i, Γ(P.A.left, P.A.hom ⁻¹ᵁ V ⊓ P.L.U i)), x ∈ V ∧ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ
    V) ∧ (∀ y ∈ V, ∃ (a : P.A.left) (i : P.L.ι), P.A.hom a = y ∧ a ∈ P.A.left.basicOpen (θ
    i))) → (∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ
    V] [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] (W : Set (V × V')) (f θ F
    : V × V' → ℂ), IsOpen W → DifferentiableOn ℂ f W → DifferentiableOn ℂ θ W → (∀ w ∈ W, F w * θ w = f w) → (∀ b, DifferentiableOn ℂ (fun z => F (b,
    z)) {z | (b, z) ∈ W}) → (∀ w ∈ W, ∃ᶠ z in nhds w.2, θ (w.1,
    z) ≠ 0) → DifferentiableOn ℂ F W) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty
    : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D'
    : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+
    (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m →
    ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧
    ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ
    (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b)
    z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧
    (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a
    : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas
    a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h
    b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single
    (.inr k) 1))) = (τ b).mulVec (Pi.single k
    1)) → IsOpen B → IsPreconnected B → IsHolPeriods D' ty B P → IsHolTo B y → IsHolTo (B ×ˢ
    Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1
    bz.2).left) → ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP B y (fun b z => (e
    b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) := by
  intro laws hsm hobj hpt hsec _ E _ _ _ H D l Xo σ g ty h1 h2 h3 D' t m B P y e bas sgn h τ hU hbas hh _ hc hP hy hol
  have pt := hpt E H D l Xo σ g ty h1 h2 h3 D' t m B P y e bas sgn h τ hU hbas hh
  have th := fun (c₁ c₂ : Fin g → ℂ) h₁ h₂ => thetaChar_family (c₁ := c₁) (c₂ := c₂)
    (p := fun k b => P b (bas (Pi.single (.inl k) 1))) (q := fun k b => P b (bas (Pi.single (.inr k) 1)))
    (fun k => hP.2 _) (fun k => hP.2 _) hh h₁ h₂
  have he : ∀ b ∈ B, ∀ z, (e b z).left ≫ Xo.univ.t.G.hom = y b := fun b _ z => Over.w (e b z)
  have he0 : ∀ b ∈ B, (e b 0).left = y b ≫ eSec Xo.univ.t.G := fun b hb => by
    rw [((hU b hb).2.2.2.1 0).2 (zero_mem _)]
    rfl
  have := Xo.smooth
  have := (hsm _ _ Xo.s (SmoothOfRelativeDimension.smooth D.dim Xo.s)).2.2
  obtain ⟨o₁, o₂, o₃, o₄⟩ := hobj E H D l _ _ _ _ Xo.univ
  have sec : ∀ b₀ ∈ B, ∃ (V : Xo.X.Opens) (θ₀ : ∀ j, Γ(Xo.univ.t.G.left, Xo.univ.t.G.hom ⁻¹ᵁ V ⊓ Xo.univ.t.PP.L.U j)),
      ⊤ ≤ y b₀ ⁻¹ᵁ V ∧ ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ V → SpansFibre Xo.univ.t.PP (y b) V θ₀ := fun b₀ _ => by
    obtain ⟨V, θ₀, m₀, s₀, n₀⟩ := hsec Xo.X
      { A := Xo.univ.t.G, isAb := o₁, g := _, smoothDim := o₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB
        rigid := o₃, sym := o₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv } (y b₀ (default : PrimeSpectrum ℂ))
    exact ⟨V, θ₀, (top_le_preimage_iff_mem _ _).2 m₀, fun b _ hb =>
      exists_ratio_fibre laws.globalSectionsRank Xo.univ (y b) V θ₀ s₀ n₀ hb⟩
  choose! c hc₁ hc₂ using pt
  let C₀ : Set (Fin g → ℂ) := Set.pi Set.univ fun _ => {0, 1 / 2}
  have fin : (C₀ ×ˢ C₀).Finite := (Set.Finite.pi fun _ => Set.toFinite _).prod (Set.Finite.pi fun _ => Set.toFinite _)
  have hc₃ : ∀ b ∈ B, (∀ k, (c b).1 k = 0 ∨ (c b).1 k = 1 / 2) ∧ (∀ k, (c b).2 k = 0 ∨ (c b).2 k = 1 / 2) ∧
      ∃ fr, IsFibreFrame Xo.univ.t.PP (y b) (fun z => (e b z).left)
        (fun z => thetaChar (τ b) (c b).1 (c b).2 ((h b).mulVec z)) fr := fun b hb => by
    obtain ⟨c₁, c₂, e₀, r₁, r₂, r₃⟩ := hc₁ b hb
    have r := isThetaFrame_singleton_iff.1 r₃
    rw [e₀]
    exact ⟨r₁, r₂, r⟩
  have const := eq_of_finite_of_closed_fibres hc fin c
    (fun b hb => ⟨fun k _ => (hc₃ b hb).1 k, fun k _ => (hc₃ b hb).2.1 k⟩) (fun k hk b hb hcl => by
      have k₁ := fun i => hk.1 i trivial
      have k₂ := fun i => hk.2 i trivial
      obtain ⟨V, θ₀, hV₀, hV⟩ := sec b hb
      obtain ⟨fr', h'⟩ := (hc₃ b hb).2.2
      have r := exists_fibreFrame_of_mem_closure (e := fun b z => (e b z).left)
        (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z)) he hol (th _ _ k₁ k₂).1 (th _ _ k₁ k₂).2 hb hV₀ hV
        (T := {b' ∈ B | c b' = k}) (fun b' hb' => by have r := (hc₃ b' hb'.1).2.2; rw [hb'.2] at r; exact r) hcl
        ((th _ _ (hc₃ b hb).1 (hc₃ b hb).2.1).2 b hb) h'
      exact (hc₂ b hb k ⟨k.1, k.2, rfl, k₁, k₂, (isThetaFrame_singleton_iff (y := y) (e := fun b z => (e b z).left)
        (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z))).2 r⟩).symm)
  obtain ⟨k, k₁, k₂, hk⟩ : ∃ k : (Fin g → ℂ) × (Fin g → ℂ), (∀ i, k.1 i = 0 ∨ k.1 i = 1 / 2) ∧
      (∀ i, k.2 i = 0 ∨ k.2 i = 1 / 2) ∧ ∀ b ∈ B, c b = k := by
    rcases B.eq_empty_or_nonempty with h0 | ⟨b₀, hb₀⟩
    · exact ⟨0, fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun b hb => absurd (h0 ▸ hb) (Set.notMem_empty b)⟩
    · exact ⟨c b₀, (hc₃ b₀ hb₀).1, (hc₃ b₀ hb₀).2.1, fun b hb => const b hb b₀ hb₀⟩
  exact ⟨k.1, k.2, k₁, k₂, isThetaFrame_of_fibreFrames (e := fun b z => (e b z).left)
    (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z)) he he0 hy hol (th _ _ k₁ k₂).1 (th _ _ k₁ k₂).2 sec
    fun b hb => by have r := (hc₃ b hb).2.2; rw [hk b hb] at r; exact r⟩

end GlobalTheory.ThetaFamily
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.levelMap_fibre_orbit : Out.Laws → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing
    B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s'
    : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
    : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b'
    : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s''
    : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
    : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
    : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
    f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
    f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B
    : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂
    : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m
    : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta
    a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s
    : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S'
    ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta
    a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B
    : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k : Type) [Field
    k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e
    : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : TateIso D k Q act e, ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f
    n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n
    : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n
    : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f
    n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo
    : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK
    : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l)
    : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA
    a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo
    : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK
    : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l)
    : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc
    : c.F = c₂.F) (rF
    : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion
    hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y'
    : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ
    : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g
    : Sim D) (ρ
    : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂ :=
  GlobalTheory.LevelFibre.levelMap_fibre_simply_transitive_of_laws
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_semiAbelianTriple_of_finiteQuotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (a' : OAct (𝓞 E) G') (φ : t.G.left ⟶ G'.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → IsSemiAbelian G' → IsGrpPullback t.G G' π φ → (∀ x, (t.act.act x).left ≫ φ = φ ≫ (a'.act x).left) → L'.IsLB → LBIso t.PP.L (L'.pull φ) → ∃ (t' : SAB H X') (ν : SABMap t t' π) (e : t'.G ≅ G'), ν.φ ≫ e.hom.left = φ := by
  first | exact @GlobalTheory.QuotTriple.exists_sab_of_quotient | exact GlobalTheory.QuotTriple.exists_sab_of_quotient | (intros; apply GlobalTheory.QuotTriple.exists_sab_of_quotient <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_triple_glue_two_opens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (U V : X.Opens) (t₁ : SAB H U.toScheme) (t₂ : SAB H V.toScheme) (t₀ : SAB H (U ⊓ V).toScheme) (m₁ : SABMap t₀ t₁ (X.homOfLE inf_le_left)) (m₂ : SABMap t₀ t₂ (X.homOfLE inf_le_right)), U ⊔ V = ⊤ → (IsReduced U.toScheme ∧ genericPoints U.toScheme ⊆ abLocus t₁.G) → (IsReduced V.toScheme ∧ genericPoints V.toScheme ⊆ abLocus t₂.G) → ∃ (t : SAB H X) (n₁ : SABMap t₁ t U.ι) (n₂ : SABMap t₂ t V.ι), m₁.φ ≫ n₁.φ = m₂.φ ≫ n₂.φ := by
  first | exact @GlobalTheory.TripleGlue.exists_sab_glue | exact GlobalTheory.TripleGlue.exists_sab_glue | (intros; apply GlobalTheory.TripleGlue.exists_sab_glue <;> assumption)
end
