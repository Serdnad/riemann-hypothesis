module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WeakIdealLattices
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle712
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle204
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle597
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import GroundTheory.LocalFields.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle715
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle418
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle508
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle546
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle547
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle714
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle716
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle004
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

section

noncomputable section

namespace GlobalTheory.NL.RightExactKs

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.NL

section Generic

theorem dvd_pow_of_not_isUnit {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {p : O} (hp : ¬ IsUnit p) {a : O} (ha : a ≠ 0) : ∃ n : ℕ, a ∣ p ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have h1 : ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hp
  exact ⟨n, hn.dvd.trans (pow_dvd_pow_of_dvd h1 n)⟩

variable {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {LL : Type} [Field LL]
  {O : Type} [CommRing O] [Algebra O LL] [IsDomain O] [IsDiscreteValuationRing O]
  [IsFractionRing O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] {ρ : Representation LL G V}
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
  {ρ' : Representation LL G V'}

theorem lift_integral {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L')
    (hT : IsOpen (L.T : Set V)) {p : ℕ} (hp : ¬ IsUnit (p : O)) (c' : ↥(latticeCocycles L')) (c : G → V)
    (hc : c ∈ continuousCocycles ρ) (v : V') (hv : ∀ g, F.f (c g) - (c' : G → V') g = ρ' g v - v) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles L)), (∀ g, (c₁ : G → V) g = ((p : LL) ^ n) • c g) ∧
      F.H1map (Submodule.Quotient.mk c₁) = (p ^ n : ℕ) • (Submodule.Quotient.mk c' : LatticeCohomology L') := by
  obtain ⟨a, ha, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_fun_mem L hT c hc.1
  obtain ⟨b, hb, h'⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L' v
  obtain ⟨n, d, hd⟩ := dvd_pow_of_not_isUnit hp (mul_ne_zero ha hb)
  have h1 : (p : O) ^ n • c ∈ latticeCocycles L := by
    refine ⟨Submodule.smul_mem ((continuousCocycles ρ).restrictScalars O) _ hc, fun g _ => ?_⟩
    change (p : O) ^ n • c g ∈ L.T
    rw [hd, mul_assoc, mul_comm, mul_smul]
    exact L.T.smul_mem _ (h g)
  have h2 : (p : O) ^ n • v ∈ L'.T := by
    rw [hd, mul_comm, ← mul_assoc, mul_smul]
    exact L'.T.smul_mem _ h'
  refine ⟨n, ⟨_, h1⟩, fun g => ?_, ?_⟩
  · change (p : O) ^ n • c g = _
    rw [← algebraMap_smul LL, map_pow, map_natCast]
  · rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.eq _).2 ⟨_, h2, ?_⟩
    funext g
    change ρ' g ((p : O) ^ n • v) - (p : O) ^ n • v =
      F.f ((p : O) ^ n • c g) - ((p ^ n : ℕ) : O) • (c' : G → V') g
    rw [Nat.cast_pow, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, ← smul_sub,
      ← smul_sub, hv]

end Generic

theorem lift_integral_res {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] (hO : GoodO (Qp := Qp) LL O) (H : Subgroup G) [CompactSpace ↥H]
    (T₁ T₂ : LocLat G Qp LL O) (π : LatHom T₁.L T₂.L) {p : ℕ} (hp : ¬ IsUnit (p : O))
    (c₂ : ↥(latticeCocycles (resLat T₂ H))) (κ₂ : LatticeCohomology (resLat T₂ H)) (hκ : Submodule.Quotient.mk c₂ = κ₂)
    (c : ↥H → T₁.V) (hc : c ∈ continuousCocycles (T₁.ρ.comp H.subtype)) (v : T₂.V)
    (hv : ∀ g : ↥H, π.f (c g) - (c₂ : ↥H → T₂.V) g = T₂.ρ (g : G) v - v) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles (resLat T₁ H))) (κ₁ : LatticeCohomology (resLat T₁ H)),
      Submodule.Quotient.mk c₁ = κ₁ ∧ (∀ g, (c₁ : ↥H → T₁.V) g = ((p : LL) ^ n) • c g) ∧
      (resHom π H).H1map κ₁ = (p ^ n : ℕ) • κ₂ := by
  obtain ⟨hD, hDVR, hF⟩ := hO.1
  obtain ⟨n, c₁, h1, h2⟩ := lift_integral (resHom π H) (GlobalTheory.Cyc.locLat_isOpen hO T₁) hp c₂ c hc v hv
  exact ⟨n, c₁, _, rfl, h1, hκ ▸ h2⟩

theorem mem_continuousCocycles_restrictLattice {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) (H : Subgroup G) (c : ↥(latticeCocycles (resLat T H))) :
    (c : ↥H → T.V) ∈ continuousCocycles (T.ρ.comp H.subtype) := c.2.1

theorem smul_coboundary {Qp LL V B : Type} [Field Qp] [Field LL] [Algebra Qp LL] [AddCommGroup V]
    [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [CommRing B] [Algebra Qp B]
    (f : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B) (a : LL) {y y' : V} {x : V ⊗[Qp] B} (h : y' = a • y)
    (hx : y ⊗ₜ[Qp] (1 : B) = f x - x) : y' ⊗ₜ[Qp] (1 : B) = f (a • x) - a • x := by
  rw [h, map_smul, ← smul_sub, ← hx]
  rfl

variable {l : ℕ} [Fact l.Prime]

theorem not_isUnit_l (P : LocPrime l) (LL : FinExt l) : ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  have h1 : ((l : ℕ) : ↥LL.1) * (u : ↥LL.1) = 1 := by
    have := congrArg (algebraMap ↥(OL LL) ↥LL.1) hu
    rwa [map_mul, map_natCast, map_one] at this
  have h2 := congrArg (P.v LL) h1
  rw [AddValuation.map_mul, AddValuation.map_one, P.v_l] at h2
  have h3 : 0 ≤ P.v LL (u : ↥LL.1) := (P.v_O LL _).2 u.2
  have h4 : (1 : WithTop ℚ) ≤ 0 := h2 ▸ le_add_of_nonneg_right h3
  exact absurd h4 (by simp)

theorem continuous_incl {K E : FinExt l} (hle : K.1 ≤ E.1) :
    Continuous (Subgroup.inclusion (GK_le hle)) :=
  continuous_subtype_val.subtype_mk _

def resRep {K LL : FinExt l} (E : FinExt l) (hle : K.1 ≤ E.1) (T : Lt K LL) :
    GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := T.V
  ρ := T.ρ.comp (Subgroup.inclusion (GK_le hle))
  cont x := (T.cont x).comp (continuous_incl hle)



theorem lift_rational (P : LocPrime l) (AI : LocAinf l P) (hP : LocTied l P AI) {K LL : FinExt l}
    (E : FinExt l) (hle : K.1 ≤ E.1) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (hπ : Function.Surjective π.f) (h₁ : IsCrys (P.PD K) T₁.ρ) (h₂ : IsCrys (P.PD K) T₂.ρ)
    (c₂ : ↥H → T₂.V) (hc₂ : c₂ ∈ continuousCocycles (T₂.ρ.comp H.subtype))
    (x₂ : T₂.V ⊗[ℚ_[l]] P.R.B)
    (hx₂ : ∀ g : ↥H, c₂ g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) T₂.ρ (g : ↥(GK K)) x₂ - x₂) :
    ∃ c₁ ∈ continuousCocycles (T₁.ρ.comp H.subtype),
      (∃ x₁ : T₁.V ⊗[ℚ_[l]] P.R.B,
        ∀ g : ↥H, c₁ g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) T₁.ρ (g : ↥(GK K)) x₁ - x₁) ∧
      ∃ v : T₂.V, ∀ g : ↥H, π.f (c₁ g) - c₂ g = T₂.ρ (g : ↥(GK K)) v - v := by
  let a : ↥(GK E) → ↥H := fun g => ⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩
  let b : ↥H → ↥(GK E) := fun g => ⟨((g : ↥(GK K)) : GQ l), (hH _).1 g.2⟩
  have ha : Continuous a := (continuous_incl hle).subtype_mk _
  have hb : Continuous b := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hres := fun (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) =>
    (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l P AI hP K E LL hle T.V T.ρ).1 hT
  have hc' : c₂ ∘ a ∈ finiteCocycles (P.PD E) (resRep E hle T₂).ρ := by
    refine ⟨⟨hc₂.1.comp ha, fun g h => hc₂.2 (a g) (a h)⟩, x₂, fun g => ?_⟩
    exact (hx₂ (a g)).trans (congrArg (fun f : T₂.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T₂.V ⊗[ℚ_[l]] P.R.B => f x₂ - x₂)
      (GlobalTheory.Cyc.actVB_inclusion P K E LL hle T₂ g).symm)
  obtain ⟨c, ⟨hc, x, hx⟩, v, hv⟩ := GlobalTheory.T.bloch_kato_right_exact l P AI hP E ↥LL.1 ↥(OL LL)
    (GlobalTheory.LocalIntegers.good_integers l LL).1 (resRep E hle T₁) (resRep E hle T₂) π.f
    (fun g y => π.equiv _ y) hπ (hres T₁ h₁) (hres T₂ h₂) _ hc'
  refine ⟨c ∘ b, ⟨hc.1.comp hb, fun g h => hc.2 (b g) (b h)⟩, ⟨x, fun g => ?_⟩, v, fun g => ?_⟩
  · let x' : T₁.V ⊗[ℚ_[l]] P.R.B := x
    exact (hx (b g)).trans (congrArg (fun f : T₁.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T₁.V ⊗[ℚ_[l]] P.R.B => f x' - x')
      (GlobalTheory.Cyc.actVB_inclusion P K E LL hle T₁ (b g)))
  · exact (congrFun hv (b g)).symm

theorem compactSpace_sub {K E : FinExt l} (hle : K.1 ≤ E.1) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) : CompactSpace ↥H := by
  have := GlobalTheory.H1fGeneratorBoundAlt.compactSpace_GK E
  let a : ↥(GK E) → ↥H := fun g => ⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩
  have ha : Continuous a := (continuous_incl hle).subtype_mk _
  have hs : Function.Surjective a := fun g => ⟨⟨((g : ↥(GK K)) : GQ l), (hH _).1 g.2⟩, rfl⟩
  exact hs.compactSpace ha

theorem mem_GKs_iff (P : LocPrime l) {K LL : FinExt l} {s m : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) m) (hs : W.s = s) (x : ↥(GK K)) :
    x ∈ W.GKs ↔ (x : GQ l) ∈ GK (GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) := by
  rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, hs]
  rfl



theorem lift_cocycle (P : LocPrime l) (AI : LocAinf l P) (hP : LocTied l P AI) {K LL : FinExt l}
    {s m : ℕ} (hK : K.1 ≤ Ks K s) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) m) (hs : W.s = s)
    (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (hπ : Function.Surjective π.f) (h₁ : IsCrys (P.PD K) T₁.ρ) (h₂ : IsCrys (P.PD K) T₂.ρ)
    (c₂ : ↥(latticeCocycles (resLat T₂ W.GKs))) (κ₂ : LatticeCohomology (resLat T₂ W.GKs))
    (hκ : Submodule.Quotient.mk c₂ = κ₂) (x₂ : T₂.V ⊗[ℚ_[l]] P.R.B)
    (hx₂ : ∀ g : ↥W.GKs, (c₂ : ↥W.GKs → T₂.V) g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K) T₂.ρ (g : ↥(GK K)) x₂ - x₂) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles (resLat T₁ W.GKs))) (κ₁ : LatticeCohomology (resLat T₁ W.GKs)),
      Submodule.Quotient.mk c₁ = κ₁ ∧
      (∃ x₁ : T₁.V ⊗[ℚ_[l]] P.R.B, ∀ g : ↥W.GKs, (c₁ : ↥W.GKs → T₁.V) g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        actVB (P.PD K) T₁.ρ (g : ↥(GK K)) x₁ - x₁) ∧
      (resHom π W.GKs).H1map κ₁ = (l ^ n : ℕ) • κ₂ := by
  have hH := mem_GKs_iff P W hs
  have := compactSpace_sub (E := GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) hK W.GKs hH
  refine (lift_rational P AI hP (GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) hK W.GKs hH T₁ T₂ π hπ h₁ h₂ _
    (mem_continuousCocycles_restrictLattice T₂ W.GKs c₂) x₂ hx₂).elim fun c hc => hc.2.1.elim fun x hx =>
      hc.2.2.elim fun v hv => ?_
  refine (lift_integral_res (GlobalTheory.LocalIntegers.good_integers l LL).1
    W.GKs T₁ T₂ π (not_isUnit_l P LL) c₂ κ₂ hκ c hc.1 v hv).elim fun n h => h.elim fun c₁ h =>
      h.elim fun κ₁ h => ?_
  exact ⟨n, c₁, κ₁, h.1, ⟨((l : ↥LL.1) ^ n) • x, fun g => smul_coboundary _ _ (h.2.1 g) (hx g)⟩,
    h.2.2⟩

end GlobalTheory.NL.RightExactKs
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualOne

theorem isTwistRep_dual_of_pairing {G L : Type} [Group G] [Field L]
    {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    {V' : Type} [AddCommGroup V'] [Module L V'] [FiniteDimensional L V']
    (ρ : Representation L G V) (ρ' : Representation L G V') (χ : G →* Lˣ)
    (m : V →ₗ[L] V' →ₗ[L] L)
    (h1 : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : Lˣ) : L) * m x y)
    (h2 : ∀ y, (∀ x, m x y = 0) → y = 0) (h3 : finrank L V = finrank L V') :
    IsTwistRep χ ρ.dual ρ' := by
  have hinj : Function.Injective m.flip := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact h2 y fun x => by simpa using LinearMap.congr_fun hy x
  have hdim : finrank L V' = finrank L (Module.Dual L V) := by
    rw [Subspace.dual_finrank_eq, h3]
  let f : V' ≃ₗ[L] Module.Dual L V := m.flip.linearEquivOfInjective hinj hdim
  have hf : ∀ y x, f y x = m x y := fun y x => rfl
  refine ⟨f.symm, fun g φ => ?_⟩
  obtain ⟨y, rfl⟩ := f.surjective φ
  apply f.injective
  rw [map_smul, f.apply_symm_apply, f.symm_apply_apply]
  ext x
  have hx : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := h1 g (ρ g⁻¹ x) y
  rw [hx] at this
  rw [hf, this, LinearMap.smul_apply, Representation.dual_apply, smul_eq_mul]
  congr 1

theorem isCrys_of_isDual1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) ρ ρ' m → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' := by
  intro l _ P AI hT K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' m hD hρ
  obtain ⟨h1, -, h2, h3⟩ := hD
  have htw := isTwistRep_dual_of_pairing ρ ρ' _ m h1 h2 h3
  have hreg := (GlobalTheory.MemLoc.tied_regular_and_onto l P AI hT).1
  have hdual := GlobalTheory.Per.TiedDual.tied_isCrys_dual l P AI hT hreg K LL V ρ hρ
  have hcyc := (GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI hT K LL 1).1
  rw [zpow_one] at hcyc
  exact (GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift l P AI hT K LL _ ρ.dual V' ρ' _ htw hcyc hdual).1

end GlobalTheory.DualOne
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.H0_vanish_of_zero_multiplicity : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), IsDR (P.PD K) ρ → multV (P.PD K) ρ τ 0 = 0 → H0V ρ = ⊥ := by
  first | exact @GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero | exact GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero | (intros; apply GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.blochKato_exact_annihilators_periodDatum : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, bkACore (P.PD K) := by
  first | exact @GlobalTheory.BlochKatoAnn.bkA_exact_annihilators | exact GlobalTheory.BlochKatoAnn.bkA_exact_annihilators | (intros; apply GlobalTheory.BlochKatoAnn.bkA_exact_annihilators <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoFin

theorem finite_continuous_cocycles_localGaloisRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    (∀ v, Continuous fun g => ρ g v) → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := by
  intro l _ P K V _ _ _ _ _ _ _ ρ hc
  obtain ⟨ρ', m, hc', hD⟩ := GlobalTheory.T.exists_tateTwistDual_perfectPairing l P K V ρ hc
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] :=
    { V := Fin (finrank ℚ_[l] V) → ℚ_[l], ρ := ρ', cont := hc' }
  have hH := (GlobalTheory.T.finrank_H1_dual_pair CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler l P K ℚ_[l] ℤ_[l]
    GlobalTheory.Published.BlochKato.goodO_padicInt A A' m hD).1
  exact GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hH

end GlobalTheory.HyodoFin
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachIntegralComplex_cocycle_class_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2c D HW F := by
  first | exact @GlobalTheory.NL.IntComplex.main | exact GlobalTheory.NL.IntComplex.main | (intros; apply GlobalTheory.NL.IntComplex.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

namespace GlobalTheory.GenCountUnram

theorem admGenL_all : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll D.loc := by
  intro D l _ K LL
  unfold Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBound
  intro hbij T hT
  have ht := D.locT l
  have hgood := (GlobalTheory.LocalIntegers.good_integers l LL).1
  have h27 := GlobalTheory.T.h1fT_span_card_bound l (D.loc l) (D.locA l) ht K ↥LL.1 ↥(OL LL) hgood T
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) ht K LL T.V T.ρ hT).1
  have hgen := h27 hDR
  obtain ⟨s, hs, hcard⟩ := hgen
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := ⟨T.V, T.ρ, T.cont⟩
  have hseq0 := GlobalTheory.SeqDim.h1f_finrank l (D.loc l) (D.locA l) ht K ↥LL.1 ↥(OL LL) hgood A
  have hseq := (hseq0 hDR).2
  have hdR0 := GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) ht K LL T.V T.ρ
  haveI := hdR0.1
  have hdR := hdR0.2
  have hK : finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K) :=
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) hbij).toLinearEquiv.finrank_eq.symm
  refine ⟨s, hs, ?_⟩
  rw [hK] at hdR
  have hle : finrank ↥LL.1 ↥(DdR ((D.loc l).PD K) T.ρ ⊓ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0)
      ≤ finrank ↥LL.1 ↥(DdR ((D.loc l).PD K) T.ρ) := Submodule.finrank_mono inf_le_left
  have hmul : finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 T.V + finrank ↥LL.1 T.V
      = (finrank ℚ_[l] ↥(K0 K) + 1) * finrank ↥LL.1 T.V := by ring
  rw [← hmul]
  zify at hcard hdR hle ⊢
  linarith

end GlobalTheory.GenCountUnram
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

namespace GlobalTheory.CrysFormalism

theorem crysLit_all : ∀ D : D7, Formalism.MainNotions.tableLineDegreeTwo.adm22 D := by
  intro D l _ K LL _
  have T := D.locT l
  refine ⟨?_, ?_, ?_⟩
  · intro μ a _ hμ hm
    refine ⟨GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg l (D.loc l) (D.locA l) T K LL μ a hμ hm, ?_⟩
    intro V _ _ _ _ _ _ _ ρ ρ' _ hρ hρ'
    have htw : IsTwistRep μ ρ ρ' := ⟨LinearEquiv.refl _ _, fun g x => by simp [hρ']⟩
    obtain ⟨hc, hmult⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) T K LL
      V ρ V ρ' μ htw hμ hρ
    refine ⟨hc, fun τ b => ?_⟩
    have hj : IsJumpV ((D.loc l).PD K) (charRep μ) τ (a τ) := by
      rw [(GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (D.loc l) (D.locA l) T K LL _ (charRep μ) τ (a τ)).2.2, hm]
      simp
    have := hmult τ (b - a τ) (a τ) hj
    rwa [sub_add_cancel] at this
  · intro V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ ρ₂ ι π _ _ _ hι hπ hinj hsurj hex h1
    have h0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL V₀ ρ₀ V₁ ρ₁ ι hι).1 hinj h1
    have h2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hsurj h1).1
    have hdr := GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL V₁ ρ₁ h1
    refine ⟨h0, h2, fun τ a => ?_⟩
    exact ((GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) T K LL V₀ ρ₀ V₁ ρ₁ V₂ ρ₂ ι π
      hι hπ hinj hsurj hex hdr.1).2.2 τ a).2.1
  · intro V _ _ _ _ _ _ _ ρ _ τ
    obtain ⟨h1, _⟩ := GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) T K LL V ρ
    exact ⟨(h1 τ).1, (h1 τ).2.1⟩

end GlobalTheory.CrysFormalism
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct


theorem _root_.GlobalTheory.T.card_hodgeTate_jumps_crystalline_eq_dim : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (V : Type) [AddCommGroup V] [Module ↥LL.1 V]
      [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
      (ρ : Representation ↥LL.1 ↥(GK K) V) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      IsCrys (P.PD K) ρ →
      (∀ i τ, tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ → ∀ a, multV (P.PD K) ρ τ a = (U i).count a) →
      ∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 V := by
  first | exact @GlobalTheory.Per.LetterJumps.card_jumps_letter | exact GlobalTheory.Per.LetterJumps.card_jumps_letter | (intros; apply GlobalTheory.Per.LetterJumps.card_jumps_letter <;> assumption)
end

section


theorem _root_.GlobalTheory.T.decomposition_group_equiv_local_galois_group : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  first | exact @GlobalTheory.DecLocal.decEquiv | exact GlobalTheory.DecLocal.decEquiv | (intros; apply GlobalTheory.DecLocal.decEquiv <;> assumption)
end
