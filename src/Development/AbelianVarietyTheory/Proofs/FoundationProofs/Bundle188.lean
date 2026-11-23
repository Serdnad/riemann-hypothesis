module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle185
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle177
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle178
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

namespace GlobalTheory.IntegralElementNorm

theorem norm_algebraMap_le_one {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact (PadicAlgCl.norm_extends (p := l) _).trans_le (PadicInt.norm_le_one a)

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact l.Prime] {x : PadicAlgCl l} (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  apply GlobalTheory.PadicNormCastBounds.norm_le_one_of_isIntegral <;> assumption

theorem norm_le_one_of_mem {l : ℕ} [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {x : Formalism.ConjugateSelfDual.Qbar l}
    (hx : x ∈ UpperTheory.V.HV.Coef.O c) : ‖x‖ ≤ (1 : ℝ) := by

  have : Module.Finite ℤ_[l] c.O := c.fin
  have hint : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
  exact norm_le_one_of_isIntegral (hint.map c.O.val)

end GlobalTheory.IntegralElementNorm
end

section

namespace GlobalTheory.IntegralCoefficientNormBound

open Polynomial

theorem coeff_norm_le_one (l : ℕ) [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  rw [show algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] a)
      = ((algebraMap ℤ_[l] ℚ_[l] a : ℚ_[l]) : PadicAlgCl l) from rfl, PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l), IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) := by
  apply GlobalTheory.PadicNormCastBounds.norm_le_one_of_isIntegral <;> assumption

end GlobalTheory.IntegralCoefficientNormBound
end

section

namespace GlobalTheory.IntegralAlgebraMapNormBound

open Polynomial

lemma norm_algebraMap_le_one {l : ℕ} [Fact (Nat.Prime l)] (c : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) c‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  have h1 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] c)‖
      = ‖algebraMap ℤ_[l] ℚ_[l] c‖ := PadicAlgCl.norm_extends l _
  rw [h1]
  exact PadicInt.norm_le_one c

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  apply GlobalTheory.PadicNormCastBounds.norm_le_one_of_isIntegral <;> assumption

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l),
    IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) :=
  fun x hx => norm_le_one_of_isIntegral x hx

end GlobalTheory.IntegralAlgebraMapNormBound
end

section

namespace GlobalTheory.IntegralNormLeOne

open Polynomial

theorem norm_le_one_of_isIntegral {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  apply GlobalTheory.PadicNormCastBounds.norm_le_one_of_isIntegral <;> assumption

end GlobalTheory.IntegralNormLeOne
end

section

namespace GlobalTheory.PadicIntegralNormLeOne

open Polynomial

theorem norm_algebraMap_padicInt_le_one {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l),
    PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  apply GlobalTheory.PadicNormCastBounds.norm_le_one_of_isIntegral <;> assumption

end GlobalTheory.PadicIntegralNormLeOne
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.BlochKatoBaseChangeLe

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.TwistedSelmerCompare

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem mem_HfD_gen {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    (L : Lattice (O := O) ρ) (w : G → V ⧸ L.T) :
    w ∈ HfD PD L ↔ ∃ z ∈ finiteCocycles PD ρ, ∃ m : V, ∀ g, w g = Submodule.Quotient.mk (z g + (ρ g m - m)) := by
  constructor
  · intro h
    obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨z, hz, m, fun g => rfl⟩
  · rintro ⟨z, hz, m, h⟩
    refine Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk m, rfl⟩, ?_⟩
    funext g
    exact (h g).symm



omit [IsDomain O] in
theorem mem_HfD_iff (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (w : ↥(GK B.Kw) → (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) :
    w ∈ HfD (P.PD B.Kw) (Br.lat B M) ↔
      ∃ z ∈ finiteCocycles (P.PD B.Kw) (matRep (Br.locM B M)), ∃ m : Fin k → Br.LLw B, ∀ g,
        w g = Submodule.Quotient.mk (z g + ((Br.locM B M g).mulVec m - m)) :=
  mem_HfD_gen (P.PD B.Kw) (Br.lat B M) w


set_option synthInstance.maxHeartbeats 400000 in
def transport (B : LocBridge l E Ω Gw O) (k : ℕ) :
    (↥Gw → KOG O k) →ₛₗ[B.eO.toRingHom]
      (↥(GK B.Kw) → (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) where
  toFun c g := Br.phi B k (c (Br.ι B g))
  map_add' a b := by
    funext g
    exact (Br.phi B k).map_add _ _
  map_smul' c a := by
    funext g
    exact (Br.phi B k).map_smulₛₗ c _

theorem locM_apply (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK B.Kw)) (i j : Fin k) :
    Br.locM B M g i j = Br.toLLK B (algebraMap O (FractionRing O) (M (Br.ι B g) i j)) := by
  rw [Br.toLLK_alg]; rfl

theorem vecS_mulVec (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK B.Kw)) (u : Fin k → FractionRing O) :
    Br.vecS B k ((mapM (algebraMap O (FractionRing O)) M (Br.ι B g)).mulVec u) =
      (Br.locM B M g).mulVec (Br.vecS B k u) := by
  funext i
  change Br.toLLK B (∑ j, algebraMap O (FractionRing O) (M (Br.ι B g) i j) * u j) =
    ∑ j, Br.locM B M g i j * Br.toLLK B (u j)

  simp only [map_sum, map_mul, locM_apply]



theorem phi_mem_of_mem_bkG (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (c : ↥(Z1 (WKG M))) (hc : Submodule.Quotient.mk c ∈ Br.bkG B P (WKG M) M) :
    Br.Phi B (WKG M) c ∈ HfD (P.PD B.Kw) (Br.lat B M) := by
  obtain ⟨c₁, h₁, he⟩ := hc
  have he' : c₁ - c ∈ (ReciprocityTheory.Gal.B1 (WKG M)).comap (Z1 (WKG M)).subtype :=
    (Submodule.Quotient.eq _).1 he
  obtain ⟨x, hx⟩ := (mem_coboundaries1 _ _).1 he'
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hB : Br.Phi B (WKG M) (c₁ - c) ∈ HfD (P.PD B.Kw) (Br.lat B M) := by
    refine (mem_HfD_iff P B M _).2 ⟨0, Submodule.zero_mem _, Br.vecS B k u, fun g => ?_⟩
    have := congrArg (Br.phi B k) (hx (Br.ι B g))
    refine this.trans ?_
    rw [Pi.zero_apply, zero_add, ← vecS_mulVec, ← map_sub]
    rfl
  have h2 : c = c₁ - (c₁ - c) := by abel
  rw [h2, map_sub]
  exact Submodule.sub_mem _ h₁ hB



theorem push_mem (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l)
    (hσ : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹)
    (f : O₀ →+* O) (hf : Function.Injective f)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) {k : ℕ}
    (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (c₀ : ↥Gw → KOG O₀ k)
    (hc : (fun g => Br.phi B₀ k (c₀ (Br.ι B₀ g))) ∈ HfD (P.PD B₀.Kw) (Br.lat B₀ M₀)) :
    (fun g => Br.phi B k (pushKO f hf k (c₀ (Br.ι B g)))) ∈ HfD (P.PD B.Kw) (Br.lat B (mapM f M₀)) := by
  obtain ⟨φ, hφ⟩ := exists_coefMap B₀ B f hf hz
  obtain ⟨z, hzf, m, h⟩ := (mem_HfD_iff P B₀ M₀ _).1 hc
  let θ : ↥(GK B.Kw) →* ↥(GK B₀.Kw) := B₀.e.toMonoidHom.comp (Br.ι B)
  have hθι : ∀ g, Br.ι B₀ (θ g) = Br.ι B g := fun g => B₀.e.symm_apply_apply _
  have hθ : Continuous θ := B₀.e_cont.comp (Br.ι_cont B)
  have hσ' : ∀ g : ↥(GK B.Kw), (g : GQ l) = σ * (θ g : GQ l) * σ⁻¹ := fun g => by
    have := hσ (Br.ι B g)
    rwa [show B.e (Br.ι B g) = g from B.e.apply_symm_apply g] at this
  have hp : ∀ g (v : Fin k → ↥B₀.LL.1), (fun j => φ ((Br.locM B₀ M₀ (θ g)).mulVec v j)) =
      (Br.locM B (mapM f M₀) g).mulVec fun j => φ (v j) := by
    intro g v
    funext i
    change φ (∑ j, Br.locM B₀ M₀ (θ g) i j * v j) = ∑ j, Br.locM B (mapM f M₀) g i j * φ (v j)

    simp only [map_sum, map_mul, locM_apply, hφ, fracMap_alg, hθι]
    rfl
  refine (mem_HfD_iff P B _ _).2 ⟨_, crystallineCocycle_transport_conjugation P B₀.Kw B.Kw B₀.LL B.LL θ hθ σ hσ' _ _ φ.toLinearMap hp z hzf,
    fun j => φ (m j), fun g => ?_⟩
  have hg := h (θ g)
  simp only [hθι] at hg
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (c₀ (Br.ι B g))
  rw [← hu] at hg ⊢
  obtain ⟨n, hn⟩ : Br.vecS B₀ k u - (z (θ g) + ((Br.locM B₀ M₀ (θ g)).mulVec m - m)) ∈
      stdG (Br.Ow B₀) (Br.LLw B₀) k := (Submodule.Quotient.eq _).1 hg
  refine (Submodule.Quotient.eq (stdG (Br.Ow B) (Br.LLw B) k)).2
    ⟨fun j => B.eO (f (B₀.eO.symm (n j))), ?_⟩
  funext j
  have h1 := congrArg φ (congrFun hn j)
  have h2 : algebraMap (Br.Ow B₀) (Br.LLw B₀) (n j) =
      Br.toLLK B₀ (algebraMap O₀ (FractionRing O₀) (B₀.eO.symm (n j))) := by
    rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  change φ (algebraMap (Br.Ow B₀) (Br.LLw B₀) (n j)) =
    φ (Br.toLLK B₀ (u j) - (z (θ g) j + ((Br.locM B₀ M₀ (θ g)).mulVec m j - m j))) at h1
  rw [h2, hφ, fracMap_alg, Br.toLLK_alg, map_sub, map_add (f := _), map_sub, hφ, congrFun (hp g m) j] at h1
  exact h1


set_option synthInstance.maxHeartbeats 400000 in
theorem extCond_le_bkG : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O₀ O : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra ℤ_[l] O₀] [Module.Finite ℤ_[l] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l), (∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹) → ∀ (f : O₀ →+* O) (hf : Function.Injective f), (∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) → ∀ (k : ℕ) (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀), extCond f hf (WKG M₀) (Br.bkG B₀ P (WKG M₀) M₀) (WKG (mapM f M₀)) ≤ Br.bkG B P (WKG (mapM f M₀)) (mapM f M₀) := by
  intro l _ P E Ω _ _ _ Gw O₀ O _ _ _ _ _ _ _ _ _ _ _ _ B₀ B σ hσ f hf hz k M₀
  refine Submodule.map_mono ?_
  intro c hc
  have key : Submodule.span O {c : ↥Gw → KOG O k | ∃ c₀ : Z1 (WKG M₀),
      Submodule.Quotient.mk c₀ ∈ Br.bkG B₀ P (WKG M₀) M₀ ∧
      c = fun g => pushKO f hf k ((c₀ : ↥Gw → KOG O₀ k) g)} ≤
      (HfD (P.PD B.Kw) (Br.lat B (mapM f M₀))).comap (transport B k) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c₀, h₀, rfl⟩
    exact push_mem P B₀ B σ hσ f hf hz M₀ c₀ (phi_mem_of_mem_bkG P B₀ M₀ c₀ h₀)
  exact key hc

end GlobalTheory.BlochKatoBaseChangeLe

end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem conj_family_sep : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → (∀ i j, t i = t j → F i = F j) → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  intro g ι _ act act' m k N t t' F hN hA hA' ht ht' hF htF hc hq
  classical

  have key : ∀ i j, t i = t j ↔ t' i = t' j := by
    intro i j
    obtain ⟨a, ha, ha'⟩ := hc i
    obtain ⟨b, hb, hb'⟩ := hc j
    constructor
    · intro h
      have hab : a = b := HasQ.coeff_unique hN ha (h ▸ hb)
      subst hab
      exact HasQ.fun_unique ha' hb'
    · intro h
      have hab : (fun n => g (a n)) = fun n => g (b n) := HasQ.coeff_unique hN ha' (h ▸ hb')
      have : a = b := funext fun n => g.injective (congrFun hab n)
      subst this
      exact HasQ.fun_unique ha hb
  let s : Setoid ι := Setoid.ker t
  let κ := Quotient s
  have hs : ∀ i j, (Quotient.mk s i = Quotient.mk s j) ↔ t i = t j := fun i j =>
    ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  haveI : Fintype κ := Fintype.ofFinite κ
  let actκ : κ → SL(2, ℤ) → κ := fun c γ =>
    Quotient.lift (fun i => Quotient.mk s (act i γ)) (fun i j (h : t i = t j) => by
      apply (hs _ _).2
      rw [← ht i γ, ← ht j γ, h]) c
  let actκ' : κ → SL(2, ℤ) → κ := fun c γ =>
    Quotient.lift (fun i => Quotient.mk s (act' i γ)) (fun i j (h : t i = t j) => by
      apply (hs _ _).2
      rw [key, ← ht' i γ, ← ht' j γ, (key i j).1 h]) c
  let tκ : κ → ℍ → ℂ := fun c => Quotient.lift t (fun i j (h : t i = t j) => h) c
  let tκ' : κ → ℍ → ℂ := fun c => Quotient.lift t' (fun i j (h : t i = t j) => (key i j).1 h) c
  let Fκ : κ → ℍ → ℂ := fun c => Quotient.lift F (fun i j (h : t i = t j) => htF i j h) c
  have bij : ∀ (a : ι → SL(2, ℤ) → ι) (aκ : κ → SL(2, ℤ) → κ), ActBij a →
      (∀ i γ, aκ (Quotient.mk s i) γ = Quotient.mk s (a i γ)) → ActBij aκ := by
    intro a aκ hB hcomp γ
    rw [← Finite.surjective_iff_bijective]
    intro c
    induction c using Quotient.inductionOn with
    | h i =>
      obtain ⟨j, hj⟩ := (hB γ).2 i
      exact ⟨Quotient.mk s j, by simp only [hcomp, hj]⟩
  have hAκ : ActBij actκ := bij act actκ hA (fun _ _ => rfl)
  have hAκ' : ActBij actκ' := bij act' actκ' hA' (fun _ _ => rfl)
  have htκ : IsFam actκ m tκ := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact ht i γ
  have htκ' : IsFam actκ' m tκ' := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact ht' i γ
  have hFκ : IsFam actκ k Fκ := by
    intro c γ
    induction c using Quotient.inductionOn with
    | h i => exact hF i γ
  have hinj : Function.Injective tκ := by
    intro c d h
    induction c using Quotient.inductionOn with
    | h i =>
      induction d using Quotient.inductionOn with
      | h j => exact (hs i j).2 h
  have hcκ : ∀ c, QConj g N (tκ c) (tκ' c) := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact hc i
  have hqκ : ∀ c, ∃ a, HasQ N (Fκ c) a := by
    intro c
    induction c using Quotient.inductionOn with
    | h i => exact hq i
  obtain ⟨G, hG, hGc⟩ := GlobalTheory.T.exists_conjugate_family_of_injective g κ actκ actκ' m k N tκ tκ' Fκ hN hAκ hAκ' htκ htκ' hFκ hinj hcκ hqκ
  refine ⟨fun i => G (Quotient.mk s i), ?_, fun i => hGc (Quotient.mk s i)⟩
  intro i γ
  exact hG (Quotient.mk s i) γ

end GlobalTheory.FN
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.rightGamma0CosetDecomposition_adjugate_heckeT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → RRep L (DT L q) (fun i => (repT q i).adjugate) := by
  first | exact @GlobalTheory.EisM.rrep_DT_adj_repT | exact GlobalTheory.EisM.rrep_DT_adj_repT | (intros; apply GlobalTheory.EisM.rrep_DT_adj_repT <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.integrableOn_im_rpow_mul_exp_unitStrip_one_le : ∀ (r c : ℝ), 0 < c → IntegrableOn (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im)) {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
  first | exact @GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le | exact GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le | (intros; apply GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one : ∀ (s : ℝ), 0 < s → IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  first | exact @GlobalTheory.EisM.stripLow_integrableOn_im_rpow | exact GlobalTheory.EisM.stripLow_integrableOn_im_rpow | (intros; apply GlobalTheory.EisM.stripLow_integrableOn_im_rpow <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.almostPurity_of_normal_finiteIndex_subgroup : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ U : Subgroup G, U.Normal → U.FiniteIndex → (∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x) → AlmostSep v U := by
  first | exact @GlobalTheory.AlmostEt.almostSep_of_normal_finiteIndex | exact GlobalTheory.AlmostEt.almostSep_of_normal_finiteIndex | (intros; apply GlobalTheory.AlmostEt.almostSep_of_normal_finiteIndex <;> assumption)
end
