module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetGen

theorem mul_dot_basis {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (f : X →+ ℂ) {c : ℂ}
    (hc : c ≠ 0) (χ : X) : c * (co bX χ ⬝ᵥ fun l => f (bX l) / c) = f χ := by
  conv_rhs => rw [← bX.sum_repr χ]

  rw [map_sum, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
  simp only [co]
  field_simp

theorem dual_alg (A : DualNumber ℂ) {c d c0 d0 l : ℂ} (hc : c ≠ 0) (hc0 : c0 ≠ 0) (hA : A.fst = 1)
    (hl : l = A.snd + d / c - d0 / c0) :
    A * (TrivSqZeroExt.inl c + TrivSqZeroExt.inr d) * TrivSqZeroExt.inl c0 =
      (1 + TrivSqZeroExt.inr l) * TrivSqZeroExt.inl c * (TrivSqZeroExt.inl c0 + TrivSqZeroExt.inr d0) := by
  ext
  · simp [hA]
  · simp [hA, hl]
    field_simp
    ring

theorem co_add {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (χ χ' : X) :
    co bX (χ + χ') = co bX χ + co bX χ' := by
  ext l; simp [co]

theorem tangent_generators : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X)
    (d : CD N g r bX) (G : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g → ℂ),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b →
    ∃ T : Fin r → ℂ, ∀ (χ : N.X) (ct : Fin g → ℂ), ct = d.t12 *ᵥ co bX χ →
      vE (gm.s (ν.eX χ)) (𝟙 _) ν.J * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) +
        TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) *
        TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) =
      (1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ T))) *
        TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) *
        (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) +
          TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) := by
  intro R _ _ _ _ D _ _ _ N ν g r bX d G gm W h0 hD

  set cf : (Fin g → ℂ) → ℂ := fun w => G.frG (ν.J (ν.eA (d.ex w)).left) w with hcf
  set df : (Fin g → ℂ) → ℂ := fun w => fderiv ℂ (G.frG (ν.J (ν.eA (d.ex w)).left)) w W with hdf
  have hc : ∀ w, cf w ≠ 0 := fun w => by
    simp only [hcf, ← G.fr_eq]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  set Dl : (Fin g → ℂ) → ℂ := fun w => df w / cf w with hDl
  set A : N.X → DualNumber ℂ := fun χ => vE (gm.s (ν.eX χ)) (𝟙 _) ν.J with hA
  have hA1 : ∀ χ, (A χ).fst = 1 := fun χ => GlobalTheory.T.torusExtension_characterValue_constantTerm_one ν gm h0 (ν.eX χ)
  set ct : N.X → (Fin g → ℂ) := fun χ => d.t12 *ᵥ co bX χ with hct
  have hct_add : ∀ χ χ', ct (χ + χ') = ct χ + ct χ' := fun χ χ' => by
    simp only [hct, co_add, Matrix.mulVec_add]
  have hx : ∀ χ, ν.eA (d.ex (ct χ)) = DegPre.cF D ℂ (ν.eX χ) := fun χ => by
    rw [← d.c_eq]; exact ν.c_eq χ
  have hprod := fun x y z j hj => GlobalTheory.T.cubeValue_complexPoints_eq_frameAlternatingProduct ν d.toAB d.cub G x y z j hj

  have hsnd : ∀ χ χ', (A (χ + χ')).snd + (Dl (ct χ + ct χ') + Dl 0 - Dl (ct χ) - Dl (ct χ')) =
      (A χ).snd + (A χ').snd := fun χ χ' => by
    have hm := GlobalTheory.T.torusExtension_dualCharValues_mul_cube ν gm (ν.eX χ) (ν.eX χ')
    rw [GlobalTheory.T.cube_value_eq_first_jet_alternating_product ν d.toAB G hprod W gm h0 hD _ _ (ct χ) (ct χ') (hx χ) (hx χ'), ← map_add (f := _)] at hm
    have e := congrArg TrivSqZeroExt.snd hm
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at e
    have e1 := hA1 (χ + χ'); have e2 := hA1 χ; have e3 := hA1 χ'
    simp only [hA] at e1 e2 e3 ⊢
    rw [e1, e2, e3] at e
    linear_combination e
  clear hprod
  set ℓ : N.X → ℂ := fun χ => (A χ).snd + Dl (ct χ) - Dl 0 with hℓ
  have hℓ_add : ∀ χ χ', ℓ (χ + χ') = ℓ χ + ℓ χ' := fun χ χ' => by
    have := hsnd χ χ'
    simp only [hℓ, hct_add]
    linear_combination this
  let ℓh : N.X →+ ℂ := AddMonoidHom.mk' ℓ hℓ_add
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨fun l => ℓ (bX l) / (2 * Real.pi * Complex.I), fun χ ct' hct' => ?_⟩
  have hT : (2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ fun l => ℓ (bX l) / (2 * Real.pi * Complex.I)) = ℓ χ :=
    mul_dot_basis bX ℓh h2pi χ
  rw [hT, hct']
  exact dual_alg (A χ) (hc _) (hc 0) (hA1 χ) rfl

end GlobalTheory.MBLow.Cl.JetGen

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

section Alg
variable {K : Type} [Field K]

theorem dualMap_fst {A : Type} [CommRing A] (f : A →+* K) (z : DualNumber A) : (dualMap f z).fst = f z.fst := by
  show (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) : DualNumber K).fst = _
  simp

theorem dualMap_snd {A : Type} [CommRing A] (f : A →+* K) (z : DualNumber A) : (dualMap f z).snd = f z.snd := by
  show (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) : DualNumber K).snd = _
  simp

theorem dn_snd_mul (u x : DualNumber K) : (u * x).snd = u.fst * x.snd + u.snd * x.fst := by
  rw [TrivSqZeroExt.snd_mul]
  simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

theorem unit_fst_ne (u : (DualNumber K)ˣ) : (u : DualNumber K).fst ≠ 0 := by
  intro h
  have h1 := congrArg TrivSqZeroExt.fst (Units.mul_inv u)
  rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at h1
  exact zero_ne_one h1

theorem unit_inv_fst (u : (DualNumber K)ˣ) : ((u⁻¹ : (DualNumber K)ˣ) : DualNumber K).fst = ((u : DualNumber K).fst)⁻¹ := by
  have h1 := congrArg TrivSqZeroExt.fst (Units.mul_inv u)
  rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_one] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem dualNumber_unit_mul_decomposition (U₁ : (DualNumber K)ˣ) (r : K) (hr : r ≠ 0) (P : DualNumber K) :
    (U₁ : DualNumber K) * P = TrivSqZeroExt.inl (((U₁ : DualNumber K) * TrivSqZeroExt.inl r).fst) *
      (TrivSqZeroExt.inl (P.fst / r) + TrivSqZeroExt.inr (P.snd / r +
        ((U₁ : DualNumber K) * TrivSqZeroExt.inl r).snd / ((U₁ : DualNumber K) * TrivSqZeroExt.inl r).fst * (P.fst / r))) := by
  have hu := unit_fst_ne U₁
  have e1 := dn_snd_mul (U₁ : DualNumber K) P
  have e2 := dn_snd_mul (U₁ : DualNumber K) (TrivSqZeroExt.inl r)
  ext
  · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    field_simp
  · rw [e1, dn_snd_mul]
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, e2, add_zero, zero_add, mul_zero]
    field_simp
    ring

theorem fst_U (Θ T ω : (DualNumber K)ˣ) (k : ℕ) (r : K) :
    (((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber K)ˣ) : DualNumber K) * TrivSqZeroExt.inl r).fst =
      (Θ : DualNumber K).fst * ((T : DualNumber K).fst)⁻¹ * (((ω : DualNumber K).fst)⁻¹) ^ k * r := by
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow,
    TrivSqZeroExt.fst_inl, unit_inv_fst]

theorem fst_eq_of (θ τ ω g m r p : K) (k : ℕ) (hτ : τ ≠ 0) (hω : ω ≠ 0) (h1 : θ * g ^ k = p) (h2 : τ * m ^ k = r)
    (h3 : ω * g = m) : θ * τ⁻¹ * ω⁻¹ ^ k * r = p := by
  subst h1 h2 h3
  rw [mul_pow, inv_pow]
  field_simp

variable {Ix : Type}

theorem ds_mul_left {f : Ix → DualNumber K} {s : DualNumber K} [TopologicalSpace K] [IsTopologicalRing K] (u : DualNumber K)
    (h : HasSum (fun a => (f a).fst) s.fst ∧ HasSum (fun a => (f a).snd) s.snd) :
    HasSum (fun a => (u * f a).fst) (u * s).fst ∧ HasSum (fun a => (u * f a).snd) (u * s).snd := by
  refine ⟨?_, ?_⟩
  · simp only [TrivSqZeroExt.fst_mul]
    exact h.1.mul_left _
  · simp only [dn_snd_mul]
    exact (h.2.mul_left _).add (h.1.mul_left _)

theorem ds_sum {n : ℕ} [TopologicalSpace K] [IsTopologicalRing K] (f : Fin n → Ix → DualNumber K) (s : Fin n → DualNumber K)
    (h : ∀ i, HasSum (fun a => (f i a).fst) (s i).fst ∧ HasSum (fun a => (f i a).snd) (s i).snd) :
    HasSum (fun a => (∑ i, f i a).fst) (∑ i, s i).fst ∧ HasSum (fun a => (∑ i, f i a).snd) (∑ i, s i).snd := by
  refine ⟨?_, ?_⟩
  · simp only [TrivSqZeroExt.fst_sum]
    exact hasSum_sum fun i _ => (h i).1
  · simp only [TrivSqZeroExt.snd_sum]
    exact hasSum_sum fun i _ => (h i).2

private theorem isChart_choose_and_symm_apply {B : Type} [CommRing B] [IsLocalRing B] {X : Scheme.{0}} (x : Sp B ⟶ X) (W : X.Opens)
    (h : x (IsLocalRing.closedPoint B) ∈ W) : ⊤ ≤ x ⁻¹ᵁ W := by
  intro p _
  have hle : (p : PrimeSpectrum B) ⤳ IsLocalRing.closedPoint B :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
  first
  | exact (hle.map x.continuous).mem_open W.isOpen h
  | exact (hle.map x.base.hom.continuous).mem_open W.isOpen h

end Alg

theorem value_at_tangent : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)) (yA : Sp (DualNumber C) ⟶ (TFK (R := V) C ⊗ A.A).left), IsTangent y → TanRel U.toUnifPre y gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → VecAt U.toUnifPre C y yA → ∀ (k : ℕ) (i₀ : A.L.ι), ⊤ ≤ (jFK (R := V) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ∃ c : C, ∀ (t : GlobalTheory.UT.SecA A C k) (s : Fam D.toPre C k), U.ExpandsF C k w₀ t s → (Summable fun α => (jc ν s gm α).fst / ν.rg ^ k) ∧ (Summable fun α => (jc ν s gm α).snd / ν.rg ^ k) ∧ valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := V) C)).U fun _ => i₀) (t.f fun _ => i₀) = TrivSqZeroExt.inl (valR (jFK (R := V) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) * (TrivSqZeroExt.inl (∑' α, (jc ν s gm α).fst / ν.rg ^ k) + TrivSqZeroExt.inr ((∑' α, (jc ν s gm α).snd / ν.rg ^ k) + c * ∑' α, (jc ν s gm α).fst / ν.rg ^ k)) := by
  intro V _ _ _ _ hV D A G _ _ hG U C _ _ _ _ _ _ hC N ν hν w₀ ρ hρ y gm₀ gm yA hy hrel hpull hvec k i₀ hi₀
  haveI : IsLocalRing (DualNumber V) := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber V
  obtain ⟨J0, hJ0⟩ := GlobalTheory.UU.exists_good_pt U.LG.isLB (Z := Sp (DualNumber V)) (IsLocalRing.closedPoint (DualNumber V))
  obtain ⟨J1, hJ1⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB (Z := Sp (DualNumber V)) (IsLocalRing.closedPoint (DualNumber V))
  have hjG : ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U (J0 y.left) := isChart_choose_and_symm_apply _ _ (hJ0 y.left)
  have hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J1 ψ) := fun ψ => isChart_choose_and_symm_apply _ _ (hJ1 ψ)
  have hgt : GtTan gm₀ := GlobalTheory.T.modelTangentVector_torusPoint_reduces_to_origin V hV D A G hG U y gm₀ hy hrel
  obtain ⟨W, hW1, hW2⟩ := GlobalTheory.T.integralSectionValue_tangent_eq_adicExpansionSum V hV D A G hG U y gm₀ hy hrel k (J0 y.left) J1 hjG hJ
  obtain ⟨T, hD, hT1, hT2⟩ := GlobalTheory.T.firstJetTerms_gauge_unit_mul_baseChange V D.toPre C N ν gm₀ gm hgt hpull k J1 hJ
  obtain ⟨Θ, hΘ1, hΘ2⟩ := GlobalTheory.T.sectionValue_genericTangent_eq_unit_mul_combination V (IsLocalRing.maximalIdeal V) D A G U.toUnifPre C w₀ ρ hρ y yA hy hvec k i₀
    (J0 y.left) hi₀ hjG
  obtain ⟨ω, hω⟩ : ∃ ω : (DualNumber C)ˣ, (ω : DualNumber C) = dualMap (toF V C) (W : DualNumber V) :=
    ⟨Units.map (dualMap (toF V C)).toMonoidHom W, rfl⟩
  have hωfst : (ω : DualNumber C).fst = toF V C (W : DualNumber V).fst := by rw [hω, dualMap_fst]
  have h3 : (ω : DualNumber C).fst * toF V C (rigVal U.LG (J0 y.left)) =
      toF V C (rigValD D.toPre (J1 gm₀.b.left)) := by
    rw [hωfst, ← map_mul, hW1]
  have hinj : Function.Injective (toF V C) := by
    show Function.Injective ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V)))
    rw [RingHom.coe_comp]
    exact (algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hm : toF V C (rigValD D.toPre (J1 gm₀.b.left)) ≠ 0 := by
    intro h0
    apply hD
    apply hinj
    rw [h0, map_zero]
  have hτ := unit_fst_ne T
  have hωne := unit_fst_ne ω
  have hr : ν.rg ^ k ≠ 0 := by
    rw [← hT1]
    exact mul_ne_zero hτ (pow_ne_zero _ hm)
  have hfst := (fst_U Θ T ω k (ν.rg ^ k)).trans (fst_eq_of _ _ _ _ _ _ _ k hτ hωne hΘ1 hT1 h3)
  refine ⟨(((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * TrivSqZeroExt.inl (ν.rg ^ k)).snd /
    (((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * TrivSqZeroExt.inl (ν.rg ^ k)).fst, ?_⟩
  intro t s hts
  obtain ⟨σ', hcar, n, cc, σ, fa, hexp, hlin, hslin⟩ := hts
  have hA : ∀ i, HasSum (fun α => (dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α)))).fst)
        (dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))).fst ∧
      HasSum (fun α => (dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α)))).snd)
        (dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))).snd := by
    intro i
    obtain ⟨h1, h2⟩ := GlobalTheory.T.hasSum_dualNumber_coords_of_adicSum V (IsLocalRing.maximalIdeal V) C hC _ _ (hW2 (σ i) (fa i) (hexp i))
    simp only [dualMap_fst, dualMap_snd]
    exact ⟨(Equiv.hasSum_iff (f := fun β => toF V C (termV J1 gm₀ (fa i β)).fst) ν.eX.toEquiv).2 h1,
      (Equiv.hasSum_iff (f := fun β => toF V C (termV J1 gm₀ (fa i β)).snd) ν.eX.toEquiv).2 h2⟩
  have hB := ds_mul_left (T : DualNumber C)
    (ds_sum (fun i α => TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α))))
      _ (fun i => ds_mul_left (TrivSqZeroExt.inl (cc i)) (hA i)))
  have hjc := hT2 s n cc fa hslin
  simp only [← hjc] at hB
  obtain ⟨hf, hs⟩ := hB
  have hS : ((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * ((T : DualNumber C) *
      ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) =
      (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left)) := by
    simp only [map_mul, map_pow, ← hω]
    have e1 : ∀ i, TrivSqZeroExt.inl (cc i) * ((ω : DualNumber C) ^ k * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) =
        (ω : DualNumber C) ^ k * (TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) :=
      fun i => by ring
    simp only [e1, ← Finset.mul_sum]
    have hb : ((T⁻¹ : (DualNumber C)ˣ) : DualNumber C) * (T : DualNumber C) = 1 := Units.inv_mul T
    have hw : ((ω⁻¹ : (DualNumber C)ˣ) : DualNumber C) ^ k * (ω : DualNumber C) ^ k = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination ((Θ : DualNumber C) * (∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) *
        ((ω⁻¹ : (DualNumber C)ˣ) : DualNumber C) ^ k * (ω : DualNumber C) ^ k) * hb +
      ((Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) * hw
  refine ⟨(hf.div_const _).summable, (hs.div_const _).summable, ?_⟩
  rw [(hf.div_const _).tsum_eq, (hs.div_const _).tsum_eq, hΘ2 t σ' hcar n cc σ hlin, ← hS, dualNumber_unit_mul_decomposition _ _ hr, hfst]

end GlobalTheory.MBLow.TanExp

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem sec_nsq_le {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (M : HermLB p) (u : M.B.Sec) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ C := by
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range ((M.cInf σ).continuous_nsq u)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  refine ⟨∑ τ, |K τ| + 1, ?_, fun σ y => (hK σ y).trans ?_⟩
  · linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  · have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]

theorem bounded_norm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ u : ℝ, 0 ≤ u ∧ f ∈ P.Bl a b (Real.exp u) := by
  intro k _ X _ p D hX P a b f hf
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a b
  obtain ⟨e, -, hrng, hnu, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P a b M hM
  obtain ⟨u, rfl⟩ : f ∈ Set.range e := by rw [hrng]; exact hf
  obtain ⟨C, hC1, hC⟩ := sec_nsq_le hX M u
  refine ⟨Real.log C, Real.log_nonneg hC1, hf, fun σ y => ?_⟩
  rw [Real.exp_log (by linarith)]
  have h1 := hnu u σ y
  have h2 := hC σ y
  have h3 : 0 ≤ P.nu a b σ y (e u) := by unfold Pair.nu; positivity
  nlinarith

end GlobalTheory.HSNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem exists_pos_nonzero_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ),
      ∃ (c : ℕ) (h : X.functionField), 0 < c ∧ h ≠ 0 ∧ h ∈ P.H a c := by
  intro k _ X _ p D hX P hA a
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a 0
  obtain ⟨b, hb, u, hu⟩ := exists_sec_finite_subset_nonzeroLocus k X p D hX M P.A hA {genericPoint X}
    (Set.finite_singleton _)
  have hA1 := (Pair.rep_base k X p P).2.1
  have hAb := Pair.rep_pow k X p P 0 1 P.A b hA1
  have hN := Pair.rep_tens k X p P a 0 _ _ M (P.A.pow b) hM hAb
  have e1 : a + (b : ℤ) * 0 = a := by ring
  have e2 : (0 : ℤ) + (b : ℤ) * 1 = b := by ring
  rw [e1, e2] at hN
  obtain ⟨e, -, hrange, -, hloc⟩ := RepDict.rep_dict k X p P a b _ hN
  have hmem : e u ∈ P.H a b := by
    have : e u ∈ Set.range e := Set.mem_range_self u
    rw [hrange] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ P.L.B.U i :=
    Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top _))
  obtain ⟨j, hj⟩ : ∃ j, genericPoint X ∈ P.A.B.U j :=
    Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top _))
  have hU := (hloc u (genericPoint X) i j hi hj).1 (hu rfl)
  refine ⟨b, e u, hb, fun h0 => ?_, hmem⟩
  have hz : ∀ x : X, ¬ UnitAt x (0 : X.functionField) := by
    rintro x ⟨w, hw, h⟩
    exact (hw.map (algebraMap _ X.functionField)).ne_zero h
  rw [h0] at hU
  have z : P.loc a b 0 i j = 0 := by simp [Pair.loc]
  rw [z] at hU
  exact hz _ hU

end GlobalTheory.HSNef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.hermLineBundlePair_balls_finite : GlobalTheory.Published.ArithHilbertSamuel → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (R : ℝ), GlobalTheory.Published.ArCalc → (P.Bl a c R).Finite := by
  first | exact @GlobalTheory.VolBr.BallFinite.bl_finite | exact GlobalTheory.VolBr.BallFinite.bl_finite | (intros; apply GlobalTheory.VolBr.BallFinite.bl_finite <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.sum_transgressionTopCoeffComplex_partitionOfUnity_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ι : Type} [Fintype ι] (ρ : ι → V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n), (∀ i, DifferentiableAt ℝ (ρ i) v) → (∀ x, ∑ i, ρ i x = 1) → ∑ i, corrC (ρ i) G₀ G₁ v = 0 := by
  first | exact @GlobalTheory.GoodTop.corrC_sum_eq_zero | exact GlobalTheory.GoodTop.corrC_sum_eq_zero | (intros; apply GlobalTheory.GoodTop.corrC_sum_eq_zero <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.transgressionTopCoeff_comp_holomorphic_jacobian_sq : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → DifferentiableAt ℝ ρ (φ w) → MContDiffAt 2 G₀ (φ w) → IsUnit (G₀ (φ w)).det → MContDiffAt 2 G₁ (φ w) → IsUnit (G₁ (φ w)).det → corrC (fun x => ρ (φ x)) (fun x => G₀ (φ x)) (fun x => G₁ (φ x)) w = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * corrC ρ G₀ G₁ (φ w) := by
  first | exact @GlobalTheory.GoodTop.corrC_comp_holo | exact GlobalTheory.GoodTop.corrC_comp_holo | (intros; apply GlobalTheory.GoodTop.corrC_comp_holo <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_padic_pow_mul_mem_tensorUnramifiedIntegers : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : KQ p K r), ∃ k : ℕ, (p : KQ p K r) ^ k * x ∈ intKQ p K r :=
  @_root_.GlobalTheory.TorCls.OpenP.exists_pow_mul_mem_intKQ
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_irreducible_codim_one_zero_ample_section_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d e : ℕ) (C : Set X) (f : X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim C → 0 < e → f ∈ P.H e 0 → ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ NV P e 0 f ∧ (d : WithBot ℕ∞) ≤ topologicalKrullDim C' := by
  first | exact @GlobalTheory.AmpleCut.exists_irreducible_diff_NV | exact GlobalTheory.AmpleCut.exists_irreducible_diff_NV | (intros; apply GlobalTheory.AmpleCut.exists_irreducible_diff_NV <;> assumption)
end
