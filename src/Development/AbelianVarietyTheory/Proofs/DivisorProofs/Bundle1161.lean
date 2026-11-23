module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormDegreeLeFieldDegreeAlgebraicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1126
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.CompHt GlobalTheory.ChowHt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ImageModel

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω]

structure IsModelOf (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ)
    {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : HermLB p) (ψ : Ω →+* X.functionField)
    (s : W → L.B.Sec) : Prop where

  arith : IsArithVar p D

  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X

  bij : Function.Bijective ψ

  base : ∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)

  ratio : ∀ (w w' : W) (i : L.B.ι) (h : genericPoint X ∈ L.B.U i),
    ψ (ev w) * fnOf _ h ((s w').f i) = ψ (ev w') * fnOf _ h ((s w).f i)

  bpf : ⨆ w, nonzeroLocus (s w) = ⊤

  fs : ∃ (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W),
      IsFrame Nm W b g A ∧ (∀ k, (gw k : V) = ∑ j, g j k • b j) ∧ (∀ j, b j = ∑ k, c k j • (gw k : V)) ∧
      ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts p (σ.comp (algebraMap (𝓞 K) K))),
        (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2)

end GlobalTheory.ImageModel
end
end

section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.field_degree_le_chowForm_degree_algebraic_point : ∀ (K : Type) [Field K] [CharZero K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → IsChowFormInt (coneIdeal K y) 0 δ f → Module.finrank K (IntermediateField.adjoin K (Set.range y)) ≤ δ := by
  first | exact @GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt | exact GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt | (intros; apply GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt <;> assumption)
end

section

open NumberField
open scoped Classical


theorem _root_.GlobalTheory.T.norm_sq_semilinear_le_latticeFrame_norm_sq : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (σ : K →+* ℂ) (ℓ : W → ℂ), GlobalTheory.CompHt.IsFrame Nm W b g A → (∀ k, (gw k : V) = ∑ j, g j k • b j) → (∀ j, b j = ∑ k, c k j • (gw k : V)) → (∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ℓ x = ∑ k, σ (β k : K) * ℓ (u k)) → ∀ x : W, ‖ℓ x‖ ^ 2 ≤ Nm σ x ^ 2 * ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k)‖ ^ 2 := by
  first | exact @GlobalTheory.frame_semilinear_sq_le | exact GlobalTheory.frame_semilinear_sq_le | (intros; apply GlobalTheory.frame_semilinear_sq_le <;> assumption)
end

section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.rankGrowthLimsup_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  first | exact @GlobalTheory.GrowthShift.growth_shift_le | exact GlobalTheory.GrowthShift.growth_shift_le | (intros; apply GlobalTheory.GrowthShift.growth_shift_le <;> assumption)
end

section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.chowForm_degree_le_field_degree_algebraic_point : ∀ (K : Type) [Field K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → IsChowFormInt (coneIdeal K y) 0 δ f → δ ≤ Module.finrank K (IntermediateField.adjoin K (Set.range y)) := by
  first | exact @GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt | exact GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt | (intros; apply GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt <;> assumption)
end

section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.idealQuotientHilbertPoly_coneIdeal_eq_field_degree : ∀ (K : Type) [Field K] (N : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N), y j = 1 → GlobalTheory.idealHilbertPoly (coneIdeal K y) = Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  first | exact @GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | exact GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | (intros; apply GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.CMVal

namespace GlobalTheory.RoadE

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul_isIntegral (a : E) : ∃ k : ℕ, 0 < k ∧ IsIntegral ℤ ((k : E) * a) := by
  have h : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨k, hk, hi⟩ := h.exists_integral_multiple
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, ?_⟩
  rw [zsmul_eq_mul] at hi
  rw [Nat.cast_natAbs]
  rcases abs_choice k with h | h <;> rw [h]
  · exact hi
  · push_cast; rw [neg_mul]; exact hi.neg

theorem mem_one_iff_isIntegral (a : maximalRealSubfield E) :
    a ∈ (1 : Submodule (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ↔ IsIntegral ℤ (a : E) := by
  rw [Submodule.mem_one]
  have e : IsIntegral ℤ (a : E) ↔ IsIntegral ℤ a :=
    isIntegral_algebraMap_iff (R := ℤ) (A := maximalRealSubfield E) (B := E) (x := a) 
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨a, h⟩, rfl⟩⟩

def passMul (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (n : ℕ) : GlobalTheory.HilbFam.Lat (maximalRealSubfield E) where
  carrier := {x | ∃ y' ∈ lattice c y, (n : E) * y' = ptE t x}
  add_mem' := fun {x x'} ⟨u, hu, e⟩ ⟨u', hu', e'⟩ => ⟨u + u', (latticeSub c y).add_mem hu hu', by
    rw [mul_add, e, e']; simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring⟩
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [ptE]⟩
  smul_mem' := fun a x ⟨u, hu, e⟩ => ⟨algebraMap (OF E) E a * u, mul_mem_lattice (algebraMap_mem_orderC c a) hu, by
    rw [ptE_smul, ← e]; ring⟩

theorem exists_coord_integral [IsCMField E] {θ : E} (hθ : θ ∉ maximalRealSubfield E) :
    ∃ k : ℕ, 0 < k ∧ ∀ (z : E) (a b : maximalRealSubfield E), IsIntegral ℤ z → (k : E) * z = (a : E) * θ + b →
      IsIntegral ℤ (a : E) ∧ IsIntegral ℤ (b : E) := by
  set σ := IsCMField.complexConj E with hσ
  have hδ : θ - σ θ ≠ 0 := fun h => hθ ((IsCMField.complexConj_eq_self_iff E θ).1 (sub_eq_zero.1 h).symm)
  obtain ⟨k₁, h₁, i₁⟩ := exists_nat_mul_isIntegral (θ - σ θ)⁻¹
  obtain ⟨k₂, h₂, i₂⟩ := exists_nat_mul_isIntegral θ
  refine ⟨k₁ * k₂, Nat.mul_pos h₁ h₂, fun z a b hz e => ?_⟩
  have hσz : IsIntegral ℤ (σ z) := hz.map (σ : E →+* E).toIntAlgHom
  have ea : σ (a : E) = a := σ.commutes a
  have eb : σ (b : E) = b := σ.commutes b
  have e' : ((k₁ * k₂ : ℕ) : E) * σ z = (a : E) * σ θ + b := by
    have := congrArg σ e
    rwa [map_mul, map_add, map_mul, map_natCast, ea, eb] at this
  push_cast at e e'
  have hn : ∀ m : ℕ, IsIntegral ℤ (m : E) := fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  have ha : (a : E) = k₂ * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z)) := by
    field_simp
    linear_combination e' - e
  refine ⟨ha ▸ (hn k₂).mul (i₁.mul (hz.sub hσz)), ?_⟩
  have hb : (b : E) = k₁ * (k₂ * z) - (k₂ * θ) * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z)) := by
    linear_combination -e - θ * ha
  exact hb ▸ ((hn k₁).mul ((hn k₂).mul hz)).sub (i₂.mul (i₁.mul (hz.sub hσz)))

theorem exists_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (N₀ : ℕ),
    c ≠ ⊥ → θ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) → 0 < N₀ →
    ∃ (n N : ℕ) (L : GlobalTheory.HilbFam.Lat (maximalRealSubfield E)), 0 < n ∧ 0 < N ∧ N₀ ∣ N ∧ GlobalTheory.HilbFam.HasLevel N L ∧
      ∀ x : Fin 2 → maximalRealSubfield E, x ∈ L ↔ ∃ y' ∈ lattice c y,
        (n : E) * y' = ((x 0 : maximalRealSubfield E) : E) * θ + ((x 1 : maximalRealSubfield E) : E) := by
  intro E _ _ _ θ c y N₀ hc hθ hN₀
  obtain ⟨M, hM, hlo, hhi⟩ := GlobalTheory.CMVal.LatBound.lattice_between E c hc y
  obtain ⟨k, hk, hco⟩ := exists_coord_integral (θ := θ) fun h => hθ ⟨⟨θ, h⟩, rfl⟩
  obtain ⟨D, hD, iD⟩ := exists_nat_mul_isIntegral θ
  have hn : ∀ m : ℕ, IsIntegral ℤ (m : E) := fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  refine ⟨k * M, N₀ * (k * M * M * D), passMul θ c y (k * M), by positivity, by positivity, dvd_mul_right _ _,
    ⟨fun x hx => ?_, fun x hx => ?_⟩, fun x => Iff.rfl⟩
  · have h0 := (mem_one_iff_isIntegral _).1 (hx 0 trivial)
    have h1 := (mem_one_iff_isIntegral _).1 (hx 1 trivial)
    have hi : IsIntegral ℤ ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E))) :=
      (hn N₀).mul ((h0.mul iD).add ((hn D).mul h1))
    refine ⟨_, hlo ⟨_, hi⟩, ?_⟩
    rw [ptE_smul, map_natCast]
    show ((k * M : ℕ) : E) * ((M : E) * ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E)))) = _
    simp only [ptE]
    push_cast
    ring
  · obtain ⟨u, hu, e⟩ := hx
    obtain ⟨h0, h1⟩ := hco (M * u) (x 0) (x 1) (hhi u hu) (by rw [← mul_assoc, ← Nat.cast_mul]; exact e)
    intro i _
    fin_cases i
    · exact (mem_one_iff_isIntegral _).2 h0
    · exact (mem_one_iff_isIntegral _).2 h1

end GlobalTheory.RoadE
end
end

section

noncomputable section

open WittVector CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ConstDatum

theorem isLocalRing_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra h
  push_neg at h
  have h1 : v (algebraMap O C a) < 1 :=
    lt_of_le_of_ne (hv.map_le_one a) (fun e => h.1 (hv.isUnit_of_one' e))
  have h2 : v (algebraMap O C (1 - a)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) (fun e => h.2 (hv.isUnit_of_one' e))
  have h3 := v.map_add (algebraMap O C a) (algebraMap O C (1 - a))
  have h4 : algebraMap O C a + algebraMap O C (1 - a) = 1 := by rw [← map_add (f := _)]; simp
  rw [h4, v.map_one] at h3
  exact lt_irrefl _ (lt_of_le_of_lt h3 (max_lt h1 h2))

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem etale_al (ε : PreTilt O p) (h : ℕ) (y : Fin h → O) : (etale ε h).al y = y := by
  simp [Datum.al, etale, Matrix.map_one _ (map_zero _) (map_one _)]

theorem theta_mu {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : fontaineTheta O p (Sandwich.mu ε) = 0 := by
  rw [Sandwich.mu, map_sub, fontaineTheta_teichmuller, map_one, sub_eq_zero]
  exact hε.zeta_zero

theorem etale_bb {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (h : ℕ) (y : Fin h → O) :
    (etale ε h).bb y = 0 := by
  ext i
  simp [Datum.bb, etale, Matrix.mulVec, dotProduct, theta_mu hε]

theorem etale_Fil {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (h : ℕ) : (etale ε h).Fil = ⊤ :=
  eq_top_iff.2 fun y _ => etale_bb hε h y

end GlobalTheory.ConstDatum


open GlobalTheory.ConstDatum in
theorem GlobalTheory.PDivLat.hasDatum_of_isConst : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConst G → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  haveI := GlobalTheory.PointGroup.isIntegrallyClosedIn_of_integers hv
  haveI := isLocalRing_of_integers hv
  obtain ⟨hω, hbij⟩ := GlobalTheory.T.constantPDivGroup_omega_trivial_hodgeTate_basis p C v O hv G hG
  haveI := GlobalTheory.PointGroup.finite_tate hv G
  haveI := GlobalTheory.PointGroup.free_tate hv G
  have hrank : Module.finrank ℤ_[p] G.Tate = G.height := G.finrank_tate C
  let e : G.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hrank, Module.finrank_fin_fun])
  let b : Module.Basis (Fin G.height) ℤ_[p] G.Tate := Module.Basis.ofEquivFun e
  let Φ := LinearEquiv.ofBijective _ (hbij G.height b)
  let D := etale ε G.height
  have hF : D.Fil = ⊤ := etale_Fil hε G.height
  let fil : G.dual.omega ≃ₗ[O] D.Fil := Φ.symm ≪≫ₗ (LinearEquiv.ofTop _ hF).symm
  haveI : Subsingleton G.Lie :=
    ⟨fun f g => LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, map_zero]⟩
  haveI : Subsingleton ((Fin G.height → O) ⧸ D.Fil) :=
    ⟨fun a b => by
      obtain ⟨a, rfl⟩ := D.Fil.mkQ_surjective a
      obtain ⟨b, rfl⟩ := D.Fil.mkQ_surjective b
      exact (Submodule.Quotient.eq D.Fil).2 (by rw [hF]; exact Submodule.mem_top)⟩
  refine ⟨D, e, fil, LinearEquiv.ofSubsingleton _ _, fun t => ?_, fun x χ => ?_⟩
  · rw [etale_al]
    change toO e t = ((LinearEquiv.ofTop _ hF).symm (Φ.symm (hodgeTate G t)) : Fin G.height → O)
    rw [LinearEquiv.coe_ofTop_symm_apply, LinearEquiv.eq_symm_apply]
    change Fintype.linearCombination O (fun i => hodgeTate G (b i)) (toO e t) = hodgeTate G t
    rw [Fintype.linearCombination_apply]
    have hb : b.equivFun = e := Module.Basis.equivFun_ofEquivFun e
    conv_rhs => rw [← b.sum_equivFun t]

    rw [map_sum, hb]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hodgeTate_smul (padicToO p O)]
    rfl
  · rw [Subsingleton.elim x 0]
    simp [pairingO]
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieExt

theorem prod_ofFn_eq {X : Type*} [Monoid X] {V : Type*} [AddCommMonoid V] (T : V → X)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_eq T h0 hadd (fun i => w i.succ), Fin.sum_univ_succ, hadd]

theorem lie_ext : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (ρ : W) (t : Fin D.a → (𝓞 D.F →+* W)), (∀ i, t i D.ω = ρ) → ρ ^ 2 - D.tr * ρ + D.nm = 0 → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : W) → (∀ (R' : Type) [CommRing R'] (β : L →+* R'), ∀ v : epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O D.ω) (β (algebraMap W L ρ)) v → ∃ w : Fin D.a → (epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O c) (β (algebraMap W L (t i c))) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k) i, LieMult (act.toF D) (spMap (β.comp (algebraMap W L))) ((β.comp (algebraMap W L)).comp (t i)) D.m) → (∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∀ v : epsPtR (spMap β) ⟶ G, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O D.ω) (β ρ) v → ∃ w : Fin D.a → (epsPtR (spMap β) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) (β (t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k) i, LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m := by
  intro p _ D W L _ _ _ _ _ _ G _ _ hab act ρ t htω hρ hcomax hdisc hgen hrank
  have hsm : Smooth G.hom := hab.smooth
  obtain ⟨n, M, hM⟩ := GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group W G hsm

  have hT0 : ∀ {X : Type} [Group X] {V : Type} [AddCommMonoid V] (T : V → X),
      (∀ c c', T (c + c') = T c * T c') → T 0 = 1 := fun T h => by
    have := h 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  obtain ⟨T₀, hinj₀, -, hadd₀, -, heq₀⟩ := hM W (RingHom.id W)
  have hmap : ∀ X : Matrix (Fin n) (Fin n) W, X.map (RingHom.id W) = X := fun X => by ext; simp
  have hext : ∀ X Y : Matrix (Fin n) (Fin n) W, (∀ c, T₀ (X.mulVec c) = T₀ (Y.mulVec c)) → X = Y := by
    intro X Y h
    ext i j
    have := congrFun (hinj₀ (h (Pi.single j 1))) i
    simpa [Matrix.mulVec_single_one] using this
  let Am : 𝓞 D.F → Matrix (Fin n) (Fin n) W := fun c => M (act.act (algebraMap (𝓞 D.F) D.O c))
  have hAm : ∀ c x, T₀ x ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T₀ ((Am c).mulVec x) := fun c x => by
    simpa [hmap] using heq₀ _ (act.hom _) x
  let A : 𝓞 D.F →+* Matrix (Fin n) (Fin n) W := RingHom.mk'
    { toFun := Am
      map_one' := hext _ _ fun x => by
        rw [Matrix.one_mulVec, ← hAm, map_one, act.one, Category.comp_id]
      map_mul' := fun c d => hext _ _ fun x => by
        rw [← hAm, map_mul, act.mul, ← Category.assoc, hAm, hAm, Matrix.mulVec_mulVec] }
    (fun c d => hext _ _ fun x => by
      show T₀ ((Am (c + d)).mulVec x) = T₀ ((Am c + Am d).mulVec x)
      rw [← hAm, map_add (f := _), act.add, MonObj.comp_mul, hAm, hAm, ← hadd₀, Matrix.add_mulVec])
  have hA : ∀ c, A c = M (act.act (algebraMap (𝓞 D.F) D.O c)) := fun c => rfl

  have tanT : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (T : (Fin n → R') → (epsPtR (spMap β) ⟶ G)),
      Function.Injective T →
      (∀ (s : R') c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) →
      (∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c)) →
      (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
        (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) →
      ∀ (c : 𝓞 D.F) (s : R') (x : Fin n → R'),
        IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) s (T x) ↔ ((A c).map β).mulVec x = s • x := by
    intro R' _ β T hinj hscale heq hrange c s x
    have hact : T x ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T (((A c).map β).mulVec x) :=
      heq _ (act.hom _) x
    constructor
    · rintro ⟨-, h2⟩
      refine hinj (Over.OverMorphism.ext ?_)
      rw [← hact, h2, hscale]
    · intro hx
      refine ⟨(hrange _).2 ⟨x, rfl⟩, ?_⟩
      rw [hact, hx, hscale]
  have hωroot : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hβL : (RingHom.id L).comp (algebraMap W L) = algebraMap W L := RingHom.id_comp _
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := GlobalTheory.T.eigenPart_splits_by_idempotent_matrices_domain W L (𝓞 D.F) n D.a A D.ω D.tr D.nm ρ t hωroot hρ htω hcomax hdisc
    (by
      intro v hv
      obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM L ((RingHom.id L).comp (algebraMap W L))
      have tv := (tanT L _ T hinj hscale heq hrange D.ω ((RingHom.id L) (algebraMap W L ρ)) v).2
        (by rw [hβL, RingHom.id_apply]; exact hv)
      obtain ⟨w, hw, hvw⟩ := hgen L (RingHom.id L) (T v) tv
      have hy : ∀ i, ∃ y, w i = T y := fun i => by obtain ⟨y, h⟩ := (hrange _).1 (hw i 0).1; exact ⟨y, h.symm⟩
      choose y hy using hy
      refine ⟨y, fun i c => ?_, ?_⟩
      · have := (tanT L _ T hinj hscale heq hrange c _ (y i)).1 (by rw [← hy]; exact hw i c)
        rwa [hβL, RingHom.id_apply] at this
      · apply hinj
        rw [hvw, ← prod_ofFn_eq T (hT0 T hadd) hadd]
        exact congrArg List.prod (congrArg List.ofFn (funext hy)))
  have hmapsmul : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (s : W) (X : Matrix (Fin n) (Fin n) W),
      (s • X).map β = β s • X.map β := fun R' _ β s X => by ext; simp
  have heig : ∀ (R' : Type) [CommRing R'] (β : W →+* R') i c (x : Fin n → R'),
      ((A c).map β).mulVec (((Q i).map β).mulVec x) = β (t i c) • (((Q i).map β).mulVec x) := by
    intro R' _ β i c x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQ2, hmapsmul, Matrix.smul_mulVec]

  have rk : ∀ (k : Type) [Field k] (β : W →+* k) i,
      LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m ↔ ((Q i).map β).rank = D.m := by
    intro k _ β i
    obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM k β
    rw [GlobalTheory.T.lieMult_iff_finrank_common_eigenspace_coords W G (𝓞 D.F) (act.toF D) n k β T (fun c => (A c).map β) hinj hrange hadd hscale
      (fun c x => heq _ (act.hom _) x)]
    have hsub : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((A c).map β) - (β.comp (t i)) c • LinearMap.id) :
        Submodule k (Fin n → k)) = LinearMap.range ((Q i).map β).mulVecLin := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range, RingHom.comp_apply]
      constructor
      · intro h
        exact ⟨y, hQ4 k β i y h⟩
      · rintro ⟨z, rfl⟩ c
        exact heig k β i c z
    rw [hsub, Matrix.finrank_range_mulVecLin]
  refine ⟨fun R' _ β v hv => ?_, fun k _ _ β i => ?_⟩
  · obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM R' β
    obtain ⟨x, rfl⟩ := (hrange v).1 hv.1
    have hx := (tanT R' β T hinj hscale heq hrange D.ω (β ρ) x).1 hv
    refine ⟨fun i => T (((Q i).map β).mulVec x), fun i c =>
      (tanT R' β T hinj hscale heq hrange c _ _).2 (heig R' β i c x), ?_⟩
    rw [prod_ofFn_eq T (hT0 T hadd) hadd, ← hQ3 R' β x hx]
  · obtain ⟨r, hr⟩ := GlobalTheory.T.exists_rank_idempotent_matrix_local_ring_map_field W n (Q i) (hQ1 i)
    refine (rk k β i).2 ?_
    rw [hr, ← hr (AlgebraicClosure L) ((algebraMap L (AlgebraicClosure L)).comp (algebraMap W L))]
    exact (rk _ _ i).1 (hrank (AlgebraicClosure L) (algebraMap L (AlgebraicClosure L)) i)

end GlobalTheory.LieExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_eq_of_iso : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (C : Type) [Category.{0} C] (G : C ⥤ AffOp X₀) (d d' : GlobalTheory.CatCoh.H2 (ext R₁ (G ⋙ OAff s₀))), L.IsLB → L'.IsLB → LBIso L L' → ObAt S α L G d → ObAt S α L' G d' → d = d' := by
  first | exact @GlobalTheory.LBObsUniq.obAt_eq_of_iso | exact GlobalTheory.LBObsUniq.obAt_eq_of_iso | (intros; apply GlobalTheory.LBObsUniq.obAt_eq_of_iso <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_tensor_additive : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), IsObL S α L c → IsObL S α L' c' → IsObL S α (tens L L') (c + c') := by
  first | exact @GlobalTheory.LBObs.isObL_tens | exact GlobalTheory.LBObs.isObL_tens | (intros; apply GlobalTheory.LBObs.isObL_tens <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.dieudonneFunctorBase_functor_properties : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : GlobalTheory.Dieu.Base p P) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H K : PDivGroup p k) (hG : P k G) (hH : P k H) (hK : P k K), B.map hG hG (𝟙 G) = LinearMap.id ∧ (∀ (f : G ⟶ H) (g : H ⟶ K), B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g) ∧ (∀ f g : G ⟶ H, B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g) ∧ B.map hG hH (0 : G ⟶ H) = 0 ∧ (∀ (n : ℕ) (f : G ⟶ H) (m : B.M H hH), B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m)) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m)) ∧ Module.finrank (WittVector p k) (B.M G hG) = G.height ∧ ∀ (n : ℕ) (m : B.M G hG), p ^ n • m = 0 → m = 0 :=
  @GlobalTheory.Dieu.base_functor_props
end
