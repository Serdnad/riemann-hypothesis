module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle529
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle135
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem isBig_of_smul_cls_eq_add_ampleAt : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N := by
  intro hnum k _ X _ q hq
  letI := algebraΓOfHom q
  intro N N₁ N₂ hN h₁ h₂ a x _ ha e hx hn₂
  have hf : ∀ r, algebraMap k Γ(X, ⊤) r = q.appTop ((Scheme.ΓSpecIso (.of k)).inv r) :=
    algebraΓOfHom_algebraMap q
  have hp : IsProjOver (strHom k (X := X)) := (strHom_eq hf) ▸ hq
  obtain ⟨m, A, s, hm, hA, hAmp, hxs⟩ := hx
  have hD := Semi.LB.isLB_div (isLB_lbPow h₁ m) hA
  have hsec : HasNonzeroSec (LB.div (lbPow N₁ m) A) := ⟨s, sec_ne_zero_of_mem hxs⟩
  have hB : IsBig k (tens (lbPow N₂ m) A) := (hn₂.pow hAmp m).isBig_tens_ample hnum hp hAmp
  have hP := isLB_lbPow hN (a * m)
  have e₂ : (a * m) • cls N hN = m • (cls N₁ h₁ + cls N₂ h₂) := by
    rw [← e, smul_smul, mul_comm a m]
  have hbig : IsBig k (lbPow N (a * m)) := hB.of_cls_eq_add hf hq hD hsec hP (by
    rw [cls_tens (isLB_lbPow h₂ m) hA, cls_div (isLB_lbPow h₁ m) hA hD, cls_lbPow hN, cls_lbPow h₂,
      cls_lbPow h₁, e₂]
    module)
  exact hbig.of_pow hN (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ha.ne' hm.ne'))
    fun n => finite_coh_zero_twist_of_isProjOver hf hq (isLB_lbPow hN n)

end GlobalTheory
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

open scoped Pointwise

namespace GlobalTheory.DefClassFin

def CCF : Prop :=
  ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime],
    letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
    ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
      (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
        ∀ z ∈ O, TC D σ β y (AfP p) z.1 → TC D σ β y ℚ_[p] z.2 → z ∈ U) →
      ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z, TC D σ β y (AfP p) z.1 →
        TC D σ β y ℚ_[p] z.2 →
        ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ γ.1).unop = algebraMap ℚ D γ.2 * β ∧ Commute (γ.1 : D) y ∧
          ∃ s ∈ S, ∃ u ∈ U, z = dg D p γ * s * u

theorem ccf_holds : CCF :=
  GlobalTheory.T.borel_finite_classNumber_centraliserTorus GlobalTheory.T.exists_polynomialLocus_similitudeCentralizerTorus GlobalTheory.classNumberFinite_holds

theorem finite_of_cover {H : Type} [Group H] (Γ K : Subgroup H) (S : Set H) (hS : S.Finite)
    (h : ∀ g : H, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K, g = γ * s * k) :
    Finite (DoubleCoset.Quotient (Γ : Set H) (K : Set H)) := by
  haveI : Finite S := hS.to_subtype
  refine Finite.of_surjective (fun s : S => DoubleCoset.mk Γ K (s : H)) fun q => ?_
  obtain ⟨γ, hγ, s, hs, k, hk, e⟩ := h q.out
  refine ⟨⟨s, hs⟩, ?_⟩
  change DoubleCoset.mk Γ K s = q
  conv_rhs => rw [← DoubleCoset.out_eq' q]
  exact (@DoubleCoset.eq _ _ Γ K _ _).2 ⟨γ, hγ, k, hk, e⟩

theorem cover_of_relIndex {A B : Type} [Group A] [Group B] (Γ : Subgroup (A × B)) (K₁ : Subgroup A)
    (K₂ K' : Subgroup B) (hK : K'.relIndex K₂ ≠ 0) (S : Set (A × B)) (hS : S.Finite)
    (h : ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K₁.prod K₂, g = γ * s * k) :
    ∃ S' : Set (A × B), S'.Finite ∧ ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S', ∃ k ∈ K₁.prod K', g = γ * s * k := by
  haveI : (K'.subgroupOf K₂).FiniteIndex := ⟨hK⟩
  let T : Set (A × B) := Set.range (fun c : K₂ ⧸ K'.subgroupOf K₂ => ((1 : A), ((c.out : K₂) : B)))
  have hT : T.Finite := Set.finite_range _
  refine ⟨S * T, hS.mul hT, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, k, hk, rfl⟩ := h g
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K₂) (⟨k.2, hk2⟩ : K₂)
  refine ⟨γ, hγ, s * (1, ((((⟨k.2, hk2⟩ : K₂) : K₂ ⧸ K'.subgroupOf K₂).out : K₂) : B)),
    Set.mul_mem_mul hs ⟨_, rfl⟩, (k.1, ((u : K₂) : B)⁻¹),
    Subgroup.mem_prod.2 ⟨hk1, K'.inv_mem (Subgroup.mem_subgroupOf.1 u.2)⟩, ?_⟩
  rw [hu]
  ext <;> simp [mul_assoc]

end GlobalTheory.DefClassFin

namespace GlobalTheory.DefClassFin

variable {p : ℕ} [Fact p.Prime]

theorem inT_of_TC (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) (h : TC G.C G.star β 1 R z) : InT G R β 1 z :=
  ⟨h.1, by rw [map_one]; exact Commute.one_right _⟩

theorem TC_of_inT (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) (h : InT G R β 1 z) : TC G.C G.star β 1 R z :=
  ⟨h.1, by rw [← Algebra.TensorProduct.one_def]; exact Commute.one_right _⟩

theorem psiAway_psiAway_inv (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (w : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) : psiAway G x (psiAway G x⁻¹ w) = w := by
  simp only [psiAway_apply, inv_inv]
  exact Prod.ext (by group) rfl

theorem cover_KHT (P : CCF) (G : HTGroup p) (L : G.Level) (B : GlobalTheory.LKDef.DForm G) :
    ∃ S : Set (G.GAf × Gr G 1), S.Finite ∧ ∀ g : G.GAf × Gr G 1, ∃ γ ∈ B.emb.range, ∃ s ∈ S,
      ∃ k ∈ L.K.toSubgroup.prod (KHT p G.m G.n 1 G.Fw), g = γ * s * k := by
  set x := B.trivAf.choose with hxdef
  set t := B.trivAf.choose_spec.choose with htdef
  have hx : Triv G (AfP p) B.β x t := B.trivAf.choose_spec.choose_spec
  have hemb : ∀ y, B.emb y = (toAfF G B.β x t hx y, toP1 G B.β y) := fun y => rfl
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  let U : Subgroup (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) :=
    (Subgroup.comap (psiAway G x) (L.K.toSubgroup.map (UPts G.star (AfP p)).subtype)).prod
      (Subgroup.comap (psiP G) (KHT p G.m G.n 1 G.Fw))
  obtain ⟨O₁, hO₁, h1O₁, hO₁U⟩ := exists_open_psiAway_mem_conj_level p G L B.β x t hx 1 1
  obtain ⟨O₂, hO₂, h1O₂, hO₂U⟩ := GlobalTheory.TorCls.OpenP.openp p G 1
  have hO : ∃ O : Set (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
      ∀ z ∈ O, TC G.C G.star (B.β : G.C) 1 (AfP p) z.1 → TC G.C G.star (B.β : G.C) 1 ℚ_[p] z.2 → z ∈ U := by
    refine ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, ⟨h1O₁, h1O₂⟩, fun z hz h1 _ => Subgroup.mem_prod.2 ⟨?_, ?_⟩⟩
    · obtain ⟨k, hk, e⟩ := hO₁U z.1 hz.1 (inT_of_TC G _ _ _ h1)
      exact ⟨k, hk, by simpa using e⟩
    · have := hO₂U z.2 hz.2
      simpa using this
  obtain ⟨S, hS⟩ := P G.C G.star (B.β : G.C) 1 p U hO

  let Neg : Prop := ∃ γ : G.Cˣ × ℚˣ, (γ.1 : G.C) * (B.β : G.C) * (G.star γ.1).unop =
    algebraMap ℚ G.C γ.2 * (B.β : G.C) ∧ (γ.2 : ℚ) < 0
  let gm : G.Cˣ × ℚˣ := if h : Neg then h.choose else 1
  let S₂ : Set (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) :=
    (S : Set _) ∪ (fun s => dg G.C p gm * s) '' (S : Set _)
  have hS₂ : S₂.Finite := S.finite_toSet.union (S.finite_toSet.image _)
  let Ψ : (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) →*
      ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × Gr G 1 := (psiAway G x).prodMap (psiP G)
  let fH : G.GAf × Gr G 1 →* ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × Gr G 1 :=
    (UPts G.star (AfP p)).subtype.prodMap (MonoidHom.id _)
  have hfH : Function.Injective fH := Prod.map_injective.2 ⟨Subtype.val_injective, Function.injective_id⟩
  refine ⟨fH ⁻¹' (Ψ '' S₂), (hS₂.image Ψ).preimage hfH.injOn, fun g => ?_⟩

  have hz₁ := inT_psiAway_inv_of_commute p G B.β x t hx 1 g.1 (by simp)
  simp only [OneMemClass.coe_one, Prod.fst_one, Units.val_one] at hz₁
  obtain ⟨z₂, hz₂, hψ₂⟩ := GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split p G B.β B.sym 1 g.2 (by simp)
  simp only [OneMemClass.coe_one, Prod.fst_one, Units.val_one] at hz₂
  set z₁ := psiAway G x⁻¹ (g.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) with hz₁def
  obtain ⟨γ, hγ, -, s, hs, u, hu, hz⟩ := hS (z₁, z₂) (TC_of_inT G _ _ _ hz₁) (TC_of_inT G _ _ _ hz₂)

  have key : ∃ δ : grp G B.β, ∃ s' ∈ S₂, (z₁, z₂) = dg G.C p (δ : G.Cˣ × ℚˣ) * s' * u := by
    rcases lt_or_gt_of_ne (Units.ne_zero γ.2) with hneg | hpos
    · have hN : Neg := ⟨γ, hγ, hneg⟩
      have hgm : gm = hN.choose := dif_pos hN
      obtain ⟨hgmf, hgmn⟩ := hN.choose_spec
      rw [← hgm] at hgmf hgmn
      have hδ := form_mul_inv G.star (B.β : G.C) γ.1 gm.1 γ.2 gm.2 hγ hgmf
      have hδpos : (0 : ℚ) < ((γ.2 * gm.2⁻¹ : ℚˣ) : ℚ) := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.2 hgmn)
      refine ⟨⟨γ * gm⁻¹, hδ, hδpos⟩, dg G.C p gm * s, Or.inr ⟨s, hs, rfl⟩, ?_⟩
      rw [hz]
      simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
    · exact ⟨⟨γ, hγ, hpos⟩, s, Or.inl hs, hz⟩
  obtain ⟨δ, s', hs', hz'⟩ := key
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_prod.1 hu
  obtain ⟨k₁, hk₁, ek₁⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hu1)
  have hk₂ : psiP G u.2 ∈ KHT p G.m G.n 1 G.Fw := Subgroup.mem_comap.1 hu2
  let k : G.GAf × Gr G 1 := (k₁, psiP G u.2)
  have hk : k ∈ L.K.toSubgroup.prod (KHT p G.m G.n 1 G.Fw) := Subgroup.mem_prod.2 ⟨hk₁, hk₂⟩
  refine ⟨B.emb δ, ⟨δ, rfl⟩, (B.emb δ)⁻¹ * g * k⁻¹, ⟨s', hs', ?_⟩, k, hk, by group⟩
  have hΨz : Ψ (z₁, z₂) = fH g := by
    refine Prod.ext ?_ hψ₂
    exact psiAway_psiAway_inv G x _
  have hΨd : Ψ (dg G.C p (δ : G.Cˣ × ℚˣ)) = fH (B.emb δ) := by
    refine Prod.ext ?_ ?_
    · exact (toAfF_eq_psiAway G B.β x t hx δ).symm
    · exact (formGroupToPadicPointsDegreeOne_eq_unitaryPoints G B.β δ).symm
  have hΨu : Ψ u = fH k := Prod.ext ek₁.symm rfl
  have e := congrArg Ψ hz'
  rw [map_mul, map_mul, hΨz, hΨd, hΨu] at e
  rw [map_mul, map_mul, map_inv, map_inv, e]
  group

end GlobalTheory.DefClassFin

namespace GlobalTheory.DefClassFin

theorem finite_doubleCoset : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level)
    (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ B : GlobalTheory.LKDef.DForm G,
    Finite (DoubleCoset.Quotient (B.emb.range : Set (G.GAf × Gr G 1))
      ((L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1))) := by
  intro p _ G _ L K' hK B
  obtain ⟨S, hS, hcov⟩ := cover_KHT ccf_holds G L B
  obtain ⟨S', hS', hcov'⟩ := cover_of_relIndex B.emb.range L.K.toSubgroup _ K' hK.1.relIndex_ne_zero S hS hcov
  exact finite_of_cover _ _ S' hS' hcov'

end GlobalTheory.DefClassFin
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem regularFibre_of_liftedPartialDerivations :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (B K : Type) [CommRing B] [IsRegularRing B] [Algebra (MvPolynomial σ Λ) B] [Field K] [Algebra (MvPolynomial σ Λ) K] [Algebra.EssFiniteType (MvPolynomial σ Λ) K], (∀ a : Λ, algebraMap (MvPolynomial σ Λ) K (MvPolynomial.C a) = 0 → a = 0) → (∀ s : σ, ∃ D : Derivation ℤ B B, ∀ x, D (algebraMap (MvPolynomial σ Λ) B x) = algebraMap (MvPolynomial σ Λ) B (MvPolynomial.pderiv s x)) → IsRegularRing (B ⊗[MvPolynomial σ Λ] K) := by
  intro Λ _ _ _ _ σ _ B K _ _ _ _ _ _ hΛ hlift
  obtain ⟨F, hF⟩ := (Algebra.essFiniteType_iff (R := MvPolynomial σ Λ) (S := K)).1 inferInstance
  let φ : MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ) →ₐ[MvPolynomial σ Λ] K :=
    MvPolynomial.aeval (fun z : ↥(F : Set K) => (z : K))
  letI : Algebra (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower (MvPolynomial σ Λ) (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  letI : Algebra (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) (MvPolynomial (↥(F : Set K)) B) :=
    (MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B)).toAlgebra
  have hC : ∀ x, algebraMap (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K (MvPolynomial.C x) =
      algebraMap (MvPolynomial σ Λ) K x := fun x => MvPolynomial.aeval_C _ _
  set Q := RingHom.ker (algebraMap (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) K) with hQdef
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  have hfrac : ∀ y : K, ∃ a b : MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ), b ∉ Q ∧
      y * algebraMap _ K b = algebraMap _ K a := by
    intro y
    obtain ⟨t, ht, htu, hyt⟩ := hF y
    rw [Algebra.adjoin_eq_range] at ht hyt
    obtain ⟨b, hb⟩ := ht
    obtain ⟨a, ha⟩ := hyt
    refine ⟨a, b, ?_, ?_⟩
    · rw [hQdef, RingHom.mem_ker]
      change φ b ≠ 0
      rw [show φ b = t from hb]
      exact htu.ne_zero
    · change y * φ b = φ a
      rw [show φ b = t from hb, show φ a = y * t from ha]
  have hΛQ : ∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0 := by
    intro a ha
    rw [hQdef, RingHom.mem_ker, hC] at ha
    exact hΛ a ha
  choose Dσ hDσ using hlift
  choose dσ hdσC hdσX using fun s : σ => GlobalTheory.T.exists_derivation_extend_mvPolynomial (MvPolynomial σ Λ) (↥(F : Set K))
    ((MvPolynomial.pderiv s : Derivation Λ (MvPolynomial σ Λ) (MvPolynomial σ Λ)).restrictScalars ℤ)
  choose Eσ hEσC hEσX using fun s : σ => GlobalTheory.T.exists_derivation_extend_mvPolynomial B (↥(F : Set K)) (Dσ s)
  let d : (↥(F : Set K)) ⊕ σ → Derivation ℤ (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ))
      (MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)) :=
    Sum.elim (fun t => (MvPolynomial.pderiv t).restrictScalars ℤ) dσ
  let D : (↥(F : Set K)) ⊕ σ → Derivation ℤ (MvPolynomial (↥(F : Set K)) B) (MvPolynomial (↥(F : Set K)) B) :=
    Sum.elim (fun t => (MvPolynomial.pderiv t).restrictScalars ℤ) Eσ
  have hcompat : ∀ u x, D u (algebraMap _ (MvPolynomial (↥(F : Set K)) B) x) =
      algebraMap _ (MvPolynomial (↥(F : Set K)) B) (d u x) := by
    intro u x
    change D u (MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B) x) =
      MvPolynomial.map (algebraMap (MvPolynomial σ Λ) B) (d u x)
    rcases u with t | s
    · exact MvPolynomial.pderiv_map
    · change Eσ s _ = MvPolynomial.map _ (dσ s x)
      induction x using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.map_C, hEσC, hDσ, hdσC, MvPolynomial.map_C]
        rfl
      | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
      | mul_X p t ih =>
        rw [map_mul, Derivation.leibniz, Derivation.leibniz, MvPolynomial.map_X, hEσX, hdσX, ih]
        simp [smul_eq_mul]
  obtain ⟨h, f, s, g, hg, hfQ, hQspan, hdet⟩ :=
    GlobalTheory.T.exists_generic_jacobian_data_iterated_alt Λ σ (↥(F : Set K)) Q hΛQ d (fun t x => rfl) (fun s x => hdσC s x) (fun s t => hdσX s t)
  have hreg : IsRegularRing (MvPolynomial (↥(F : Set K)) B ⊗[MvPolynomial (↥(F : Set K)) (MvPolynomial σ Λ)] K) :=
    GlobalTheory.T.isRegular_fibre_of_jacobian_derivations _ _ K Q rfl hfrac h f g (fun i => d (s i)) (fun i => D (s i))
      (fun i x => hcompat (s i) x) hg hfQ hQspan hdet
  obtain ⟨e⟩ := GlobalTheory.T.mvPolynomial_tensor_baseChange_ringEquiv' (MvPolynomial σ Λ) B K (↥(F : Set K))
  exact IsRegularRing.of_ringEquiv e

end GlobalTheory
end

section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.isIntegral_of_forall_valuation_le_one_of_fg : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω], (⊤ : IntermediateField K Ω).FG → ∀ (A : Subalgebra K Ω), A.FG → ∀ t : Ω, (∀ ν : Valuation Ω ℝ≥0, (∀ a ∈ A, ν a ≤ 1) → ν t ≤ 1) → IsIntegral A t := by
  first | exact @GlobalTheory.DegVal.isIntegral_of_forall_realValuation_le_one | exact GlobalTheory.DegVal.isIntegral_of_forall_realValuation_le_one | (intros; apply GlobalTheory.DegVal.isIntegral_of_forall_realValuation_le_one <;> assumption)
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem generically_regular_quotient_of_finiteType_int :
    ∀ (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧
      ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q →
        IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
  intro B _ _ p hp
  by_cases h : ∀ a : ℤ, algebraMap ℤ B a ∈ p → a = 0
  · exact GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime ℤ B p h
  push_neg at h
  obtain ⟨a, ha, ha0⟩ := h
  have hP : (p.comap (algebraMap ℤ B)) ≠ ⊥ := by
    intro hb
    apply ha0
    have : a ∈ p.comap (algebraMap ℤ B) := ha
    rw [hb] at this
    simpa using this
  obtain ⟨x, hx, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (Ideal.IsPrime.comap _) hP
  set l := x.natAbs with hl
  have hlp : l.Prime := Int.prime_iff_natAbs_prime.mp hxp
  haveI : Fact l.Prime := ⟨hlp⟩
  have hlmem : (l : B) ∈ p := by
    have hx' : algebraMap ℤ B x ∈ p := hx
    rcases Int.natAbs_eq x with h1 | h1
    · rw [h1] at hx'
      simpa [hl] using hx'
    · rw [h1] at hx'
      simpa [hl] using hx'
  set I : Ideal B := Ideal.span {(l : B)} with hI
  let mk := Ideal.Quotient.mk I
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker mk = I := Ideal.mk_ker
  have hIp : I ≤ p := by
    rw [hI, Ideal.span_le]; simpa using hlmem
  have hl0 : ∀ a ∈ Ideal.span {((l : ℕ) : ℤ)}, (Int.castRingHom (B ⧸ I)) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    have : ((l : ℕ) : B ⧸ I) = 0 := by
      have h0 : (Ideal.Quotient.mk I) (l : B) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span rfl)
      simpa using h0
    simp [this]
  let ψ : ZMod l →+* B ⧸ I :=
    (Ideal.Quotient.lift (Ideal.span {((l : ℕ) : ℤ)}) (Int.castRingHom (B ⧸ I)) hl0).comp
      (Int.quotientSpanNatEquivZMod l).symm.toRingHom
  letI : Algebra (ZMod l) (B ⧸ I) := ψ.toAlgebra
  haveI : IsScalarTower ℤ (ZMod l) (B ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.FiniteType (ZMod l) (B ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod l) (B ⧸ I)
  haveI : PerfectField (FractionRing (ZMod l)) := by
    have : Finite (FractionRing (ZMod l)) :=
      Finite.of_equiv _ (FractionRing.algEquiv (ZMod l) (ZMod l)).toEquiv.symm
    infer_instance

  have corr : ∀ (r : Ideal B), r.IsPrime → I ≤ r → (r.map mk).IsPrime ∧ (r.map mk).comap mk = r := by
    intro r hr hIr
    refine ⟨Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hIr), ?_⟩
    rw [Ideal.comap_map_of_surjective' mk hmk, hker]
    exact sup_eq_left.mpr hIr
  obtain ⟨p', hp', rfl⟩ : ∃ p' : Ideal (B ⧸ I), p'.IsPrime ∧ p'.comap mk = p :=
    ⟨p.map mk, corr p hp hIp⟩
  have hdom : ∀ a : ZMod l, algebraMap (ZMod l) (B ⧸ I) a ∈ p' → a = 0 := by
    intro a ha
    by_contra ha0
    exact hp'.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((IsUnit.mk0 a ha0).map _))
  obtain ⟨g', hg'p, hg'⟩ := GlobalTheory.T.exists_genericallyRegular_quotient_dominating_prime (ZMod l) (B ⧸ I) p' hdom
  obtain ⟨g, rfl⟩ := hmk g'
  refine ⟨g, fun hg => hg'p hg, ?_⟩
  intro q hq hpq hgq
  have hIq : I ≤ q := hIp.trans hpq
  obtain ⟨q', hq', rfl⟩ : ∃ q' : Ideal (B ⧸ I), q'.IsPrime ∧ q'.comap mk = q :=
    ⟨q.map mk, corr q hq hIq⟩
  have hpq' : p' ≤ q' := by
    intro y hy
    obtain ⟨y, rfl⟩ := hmk y
    exact hpq hy
  have hreg := hg' q' hpq' (fun h => hgq h)
  obtain ⟨e⟩ := GlobalTheory.localization_quotient_comap_equiv B (B ⧸ I) mk hmk p' q'
  exact IsRegularLocalRing.of_ringEquiv e.symm

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

theorem _root_.GlobalTheory.T.exists_linearCombination_tangentVectors_affineOpen : ∀ {K B : Type} [CommRing K] [CommRing B] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (Y₀ : Y.affineOpens) (φ : K →+* B) (x : Sp B ⟶ Y) (hx : x ≫ p = spMap φ) (hxY : ⊤ ≤ x ⁻¹ᵁ Y₀.1) {n : ℕ} (w : Fin n → (Sp (DualNumber B) ⟶ Y)) (hwp : ∀ a, w a ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ)) (hwx : ∀ a, spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w a = x) (c : Fin n → B), ∃ S : Sp (DualNumber B) ⟶ Y, S ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ) ∧ spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x ∧ ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O), (valR S O f).snd = ∑ a, c a * (valR (w a) O f).snd := by
  first | exact @GlobalTheory.CechKS.LinTan.exists_linComb | exact GlobalTheory.CechKS.LinTan.exists_linComb | (intros; apply GlobalTheory.CechKS.LinTan.exists_linComb <;> assumption)
end
