module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle025
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeDivisorIdealLattice
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.X_normal_join
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaIsomorphismTransport
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle055
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle056
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
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
public import Mathlib.Order.Int.LeastGreatest

@[expose] public section

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FlattenMany

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (N : I → ℕ) (V : I → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module Ω (V j)] (Γ : ∀ j, (∀ k, ι k) → AddSubgroup (V j)), (∀ j, Module.finrank Ω (V j) = N j ∧ IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → ∃ S : Finset (V j), Γ j c = spanOver (chartRing O (mseg x) c) (S : Set (V j)) ∧ Submodule.span Ω (S : Set (V j)) = ⊤) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j c, mseg (joinCoord x z) c ≠ 0 → LocFree (chartRing O (mseg (joinCoord x z)) c) (N j) (spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set (V j))) :=
  @PositivityTheory.Xgn.t_flatten_many

end GlobalTheory.CompanionTheory.Ar.FlattenMany
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FlattenLines

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ (I : Type) [Fintype I] (Γ : I → (∀ k, ι k) → AddSubgroup Ω), (∀ j, IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → Γ j c ≠ ⊥ ∧ ∃ S : Finset Ω, Γ j c = spanOver (chartRing O (mseg x) c) (S : Set Ω)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ ∀ j, ∃ a : K ⊕ K' → ℤ, IsLine O (joinCoord x z) 1 a fun c => spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set Ω) :=
  @PositivityTheory.Xgn.t_flatten_lines

end GlobalTheory.CompanionTheory.Ar.FlattenLines
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_span {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E}
    (h : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, h, (one_smul _ _).symm⟩

theorem bc_smul {C : Type} [Field C] [Algebra Ω C] {ι : Type} (w : Ω) (v : ι → Ω) :
    bcMap Ω C ι (w • v) = algebraMap Ω C w • bcMap Ω C ι v := by
  funext i
  show algebraMap Ω C (w * v i) = algebraMap Ω C w * algebraMap Ω C (v i)
  rw [map_mul]

theorem pow_one_smul_mem {E : Type} [AddCommGroup E] [Module Ω E] {R : Subalgebra o Ω} {N : ℕ}
    {L : AddSubgroup E} (hL : LocFree R N L) {p : ℕ} {w : Ω} (hw : ∃ c ∈ R, (p : Ω) = c * w) {v : E}
    (hv : w • v ∈ L) : ∃ m : ℕ, (p : Ω) ^ m • v ∈ L := by
  obtain ⟨c, hc, e⟩ := hw
  refine ⟨1, ?_⟩
  rw [pow_one, e, mul_smul]
  exact hL.1 c hc _ hv

end GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence


open GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence in
theorem GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → ∀ τ, D.imH R p τ (χ τ) = D.om τ ∧ D.kerH R p τ (χ τ) = divLat w (D.lie τ) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hN hF hI φ hT hG hG2 τ
  have hle := GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hN hF hI φ hT hG
  have hbc1 := GlobalTheory.T.lattice_image_base_change D R p w χ hc hb hG hle
  obtain ⟨hf2, hbc2⟩ := GlobalTheory.T.lattice_second_goodness D R p w χ hc hb hG hG2 hle
  have hp0 := hc.1
  have hw := hc.2.2.1
  obtain ⟨flie, -, fom, -⟩ := hb.free τ
  obtain ⟨i1, i2, i3, i4⟩ := hb.incl τ
  refine ⟨le_antisymm (fun v hv => ?_) (fun v hv => ?_), le_antisymm (fun v hv => ?_) (fun v hv => ?_)⟩
  · refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ fom v (pow_one_smul_mem fom hw ?_) ?_
    · obtain ⟨⟨b, c⟩, ⟨h, -⟩, rfl⟩ := hv
      exact i3 (((hb.del τ).2.1 c).1 ⟨b, h⟩)
    · intro C _ _ _ _ RC hRC
      have h : bcMap Ω C _ v ∈ (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) := by
        rw [hbc1 C RC hRC.2.2.2 τ]
        exact mem_span RC ⟨v, hv, rfl⟩
      have e := (hT C RC hRC).im τ
      exact e.le h
  · refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ (hG2.im τ) v (pow_one_smul_mem (hG2.im τ) hw ?_) ?_
    · exact ⟨(0, w • v), ⟨((hb.del τ).2.2.1 _).2 (i4 hv), zero_mem _, trivial⟩, rfl⟩
    · intro C _ _ _ _ RC hRC
      rw [← hbc1 C RC hRC.2.2.2 τ]
      have e := (hT C RC hRC).im τ
      exact e.ge (mem_span RC ⟨v, hv, rfl⟩)
  · show w • v ∈ D.lie τ
    refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ flie _ (pow_one_smul_mem flie hw ?_) ?_
    · obtain ⟨⟨a, b⟩, ⟨h, -⟩, rfl⟩ := hv
      exact i2 (((hb.gam τ).1 a).1 ⟨b, h⟩)
    · intro C _ _ _ _ RC hRC
      have h : bcMap Ω C _ v ∈ (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) := by
        rw [((hbc2 C RC hRC.2.2.2).2 τ).1]
        exact mem_span RC ⟨v, hv, rfl⟩
      have e := (hT C RC hRC).ker τ
      rw [bc_smul]
      exact e.le h
  · have hv' : w • v ∈ D.lie τ := hv
    refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ (hf2 τ).1 v (pow_one_smul_mem (hf2 τ).1 hw ?_) ?_
    · exact ⟨(w • v, 0), ⟨((hb.gam τ).2.2 _).2 (i1 hv'), trivial, zero_mem _⟩, rfl⟩
    · intro C _ _ _ _ RC hRC
      rw [← ((hbc2 C RC hRC.2.2.2).2 τ).1]
      have e := (hT C RC hRC).ker τ
      refine e.ge ?_
      show algebraMap Ω C w • bcMap Ω C _ v ∈ (D.bc RC).lie τ
      rw [← bc_smul]
      exact mem_span RC ⟨_, hv', rfl⟩
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.hodge_divisor_ideal_lattice : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, D.dId R p (χ τ) i = D.xId (χ τ) i) ∧ (∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i) ∧ ∀ τ i, (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _) = powSpan R p (D.xId (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main | exact GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.NormalJoin

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ NormalCharts O (joinCoord x z) := by
  exact @PositivityTheory.Xgn.t_normal_join

end GlobalTheory.CompanionTheory.Ar.NormalJoin
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.alpha_beta_isomorphism_transport : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d), IsIso B B₂ φ ψ lam → (∀ u, alpha B p (((lin φ 1).map (· ^ p)).mulVec u) = transH φ ψ lam (alpha B₂ p u)) ∧ ∀ y, beta B p (transH φ ψ lam y) = ((lin ψ 1).transpose.map (· ^ p)).mulVec (beta B₂ p y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.alpha_beta_of_isIso | exact GlobalTheory.CompanionTheory.Ar.Conj.alpha_beta_of_isIso | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.alpha_beta_of_isIso <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.beta_equivariant_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)), beta B p (rhoH B a y) = ((rho B (star a)).transpose.map (· ^ p)).mulVec (beta B p y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq | exact GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq <;> assumption)
end

section

noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]

def latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) : AddSubgroup V where
  carrier := {x | ∀ q, C.v i (b.repr x q) ≤ 1}
  zero_mem' := fun q => by simp
  add_mem' := fun {x y} hx hy q => by
    rw [map_add (f := _), Finsupp.add_apply]; exact (C.v i).map_add_le (hx q) (hy q)
  neg_mem' := fun {x} hx q => by
    rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]; exact hx q

theorem isLatOf_latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) :
    IsLatOf C i b (latOf C i b) := fun _ => Iff.rfl

def scale (L : C.I → AddSubgroup V) (c : C.I → Kˣ) : C.I → AddSubgroup V :=
  fun i => (L i).comap (DistribSMul.toAddMonoidHom V (((c i)⁻¹ : Kˣ) : K))

theorem mem_scale (L : C.I → AddSubgroup V) (c : C.I → Kˣ) (i : C.I) (x : V) :
    x ∈ scale C L c i ↔ (((c i)⁻¹ : Kˣ) : K) • x ∈ L i := Iff.rfl

theorem isLatOf_scale {L : C.I → AddSubgroup V} (c : C.I → Kˣ) {i : C.I} {n : ℕ}
    {b : Module.Basis (Fin n) K V} (h : IsLatOf C i b (L i)) :
    IsLatOf C i (b.unitsSMul fun _ => c i) (scale C L c i) := by
  intro x
  rw [mem_scale, h]
  refine forall_congr' fun q => ?_
  rw [Module.Basis.repr_unitsSMul, map_smul, Finsupp.smul_apply]
  rfl

theorem isBun_scale {L : C.I → AddSubgroup V} (c : C.I → Kˣ) (hc : {i | c i ≠ 1}.Finite)
    (h : IsBun C L) : IsBun C (scale C L c) := by
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h.1 i
    exact ⟨_, isLatOf_scale C c hb⟩
  · obtain ⟨b, hb⟩ := h.2
    refine ⟨b, (hb.union hc).subset fun i hi => ?_⟩
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn hi
    apply hi
    intro x
    rw [mem_scale, hn.2, inv_one, Units.val_one, one_smul]
    exact hn.1 x

theorem deg_scale [FiniteDimensional K V] {L : C.I → AddSubgroup V} (c : C.I → Kˣ)
    (hc : {i | c i ≠ 1}.Finite) (h : IsBun C L) :
    deg C (scale C L c) = deg C L +
      (Module.finrank K V : ℤ) * ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (c i)) := by
  choose b hb using h.1
  obtain ⟨hf, e⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (Module.finBasis K V) b h hb
  obtain ⟨-, e'⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V (scale C L c) _ (Module.finBasis K V)
    (fun i => (b i).unitsSMul fun _ => c i) (isBun_scale C c hc h)
    (fun i => isLatOf_scale C c (hb i))
  have hs1 : (Function.support fun i =>
      (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i)))).Finite := by
    refine hf.subset fun i hi => ?_
    intro h1
    exact hi (by simp [h1])
  have hs3 : (Function.support fun i => (Module.finrank K V : ℤ) *
      ((C.w i : ℤ) * WithZero.log (C.v i (c i)))).Finite := by
    refine hc.subset fun i hi => ?_
    intro h1
    exact hi (by simp [h1])
  rw [e, e', mul_finsum, ← finsum_add_distrib hs1 hs3]
  refine finsum_congr fun i => ?_
  have hd : (Module.finBasis K V).det ((b i).unitsSMul fun _ => c i) =
      (c i : K) ^ Module.finrank K V * (Module.finBasis K V).det (b i) := by
    have : ⇑((b i).unitsSMul fun _ => c i) = fun j => (c i : K) • b i j := by
      funext j; rw [Module.Basis.unitsSMul_apply]; rfl
    rw [this]
    have := (Module.finBasis K V).det.toMultilinearMap.map_smul_univ (fun _ => (c i : K)) (b i)
    simpa using this
  have h0 : C.v i ((Module.finBasis K V).det (b i)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact ((Module.finBasis K V).isUnit_det (b i)).ne_zero
  have h1 : C.v i (c i) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact (c i).ne_zero
  rw [hd, map_mul, map_pow, WithZero.log_mul (pow_ne_zero _ h1) h0, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

theorem exists_scale (i : C.I) {n m : ℕ} (b : Module.Basis (Fin n) K V)
    {b' : Module.Basis (Fin m) K V} {L : AddSubgroup V} (h : IsLatOf C i b' L) :
    ∃ c : Kˣ, 1 ≤ C.v i c ∧ ∀ x ∈ L, ((c⁻¹ : Kˣ) : K) • x ∈ latOf C i b := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image
    (insert (1 : K) (Finset.univ.image fun p : Fin m × Fin n => b.repr (b' p.1) p.2))
    (C.v i) (Finset.insert_nonempty _ _)
  have h1 : 1 ≤ C.v i c := by simpa using hc 1 (Finset.mem_insert_self _ _)
  have hpos : 0 < C.v i c := lt_of_lt_of_le zero_lt_one h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hpos
  refine ⟨Units.mk0 c hc0, h1, fun x hx q => ?_⟩
  have hle : C.v i (b.repr x q) ≤ C.v i c := by
    have hx' : b.repr x q = ∑ j, b'.repr x j * b.repr (b' j) q := by
      conv_lhs => rw [← b'.sum_repr x]

      rw [map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [hx']
    refine (C.v i).map_sum_le fun j _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * C.v i c := mul_le_mul' ((h x).1 hx j)
          (hc _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(j, q), Finset.mem_univ _, rfl⟩)))
      _ = _ := one_mul _
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
    map_inv₀, inv_mul_le_iff₀ hpos, mul_one]
  exact hle

theorem subDeg_bot [FiniteDimensional K V] (L : C.I → AddSubgroup V) : subDeg C L ⊥ = 0 := by
  unfold subDeg deg
  have : IsEmpty (Fin (Module.finrank K (⊥ : Submodule K V))) := by
    rw [finrank_bot]; infer_instance
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  simp [Module.Basis.det_apply]

theorem subDeg_bdd [FiniteDimensional K V] (L : C.I → AddSubgroup V) (h : IsBun C L) :
    ∃ B : ℤ, ∀ W : Submodule K V, subDeg C L W ≤ B := by
  classical
  obtain ⟨b, hb⟩ := h.2
  have key : ∀ i, ∃ c : Kˣ, (IsLatOf C i b (L i) → c = 1) ∧ 1 ≤ C.v i c ∧
      ∀ x ∈ L i, ((c⁻¹ : Kˣ) : K) • x ∈ latOf C i b := by
    intro i
    by_cases hi : IsLatOf C i b (L i)
    · refine ⟨1, fun _ => rfl, by simp, fun x hx => ?_⟩
      rw [inv_one, Units.val_one, one_smul]
      exact (hi x).1 hx
    · obtain ⟨b', hb'⟩ := h.1 i
      obtain ⟨c, h1, h2⟩ := exists_scale C i b hb'
      exact ⟨c, fun h' => absurd h' hi, h1, h2⟩
  choose c hc1 hc2 hc3 using key
  have hc : {i | c i ≠ 1}.Finite := hb.subset fun i hi h' => hi (hc1 i h')
  have h0 : IsBun C (fun i => latOf C i b) :=
    ⟨fun i => ⟨b, isLatOf_latOf C i b⟩, b, by simp [isLatOf_latOf]⟩
  set S : ℤ := ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (c i)) with hS
  have hS0 : 0 ≤ S := by
    refine finsum_nonneg fun i => mul_nonneg (Int.natCast_nonneg _) ?_
    have h1 : C.v i (c i) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (c i).ne_zero
    have := (WithZero.log_le_log one_ne_zero h1).2 (hc2 i)
    simpa using this
  refine ⟨(Module.finrank K V : ℤ) * S, fun W => ?_⟩
  have hW := (GlobalTheory.T.sub_and_quotient_bundles K C V _ W h0).1
  have e1 := GlobalTheory.T.degree_mono_lattice_le K C W (sub C L W) (scale C (sub C (fun i => latOf C i b) W) c)
    (GlobalTheory.T.sub_and_quotient_bundles K C V _ W h).1 (isBun_scale C c hc hW) (fun i x hx => hc3 i x hx)
  have e2 := deg_scale C c hc hW
  have e3 := GlobalTheory.T.sub_degree_nonpos_trivial_lattice K C V _ b (fun i => latOf C i b) W (fun i => isLatOf_latOf C i b)
  have e4 : (Module.finrank K W : ℤ) * S ≤ (Module.finrank K V : ℤ) * S :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast W.finrank_le) hS0
  unfold subDeg at e3 ⊢
  rw [← hS] at e2
  linarith

theorem subDeg_max : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : C.I → AddSubgroup V), IsBun C L →
    subDeg C L ⊥ = 0 ∧ ∃ W₀ : Submodule K V, ∀ W : Submodule K V, subDeg C L W ≤ subDeg C L W₀ := by
  intro K _ C V _ _ _ L h
  refine ⟨subDeg_bot C L, ?_⟩
  obtain ⟨B, hB⟩ := subDeg_bdd C L h
  obtain ⟨z, ⟨W₀, rfl⟩, hz⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ W : Submodule K V, subDeg C L W = z)
    ⟨B, by rintro _ ⟨W, rfl⟩; exact hB W⟩ ⟨_, ⊥, rfl⟩
  exact ⟨W₀, fun W => hz _ ⟨W, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax
end
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.degree_sum_eigen_sub_degrees : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.degree_eq_sum_eigen | exact GlobalTheory.CompanionTheory.Ar.Crv.degree_eq_sum_eigen | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.degree_eq_sum_eigen <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.short_exact_eigen_sub_degree : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ (ρ : O → V →ₗ[K] V) (ρ' : O →+* Module.End K V') (ρ'' : O → V'' →ₗ[K] V''), IsBun C L' → (∀ a, IsHom C L' L' (ρ' a)) → ShortExact C L L' L'' f g → (∀ a x, f (ρ a x) = ρ' a (f x)) → (∀ a y, g (ρ' a y) = ρ'' a (g y)) → ∀ s, subDeg C L' (eig (fun a => ρ' a) (fun a => algebraMap k K (χ s a))) = subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) + subDeg C L'' (eig (fun a => ρ'' a) (fun a => algebraMap k K (χ s a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.eigen_ses_subDeg | exact GlobalTheory.CompanionTheory.Ar.Crv.eigen_ses_subDeg | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.eigen_ses_subDeg <;> assumption)
end

section


theorem _root_.GlobalTheory.T.blow_up_fibre_semilocal : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main | exact GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.same_generic_bundle_chain : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N n : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : Fin (n + 1) → ChartBundle O (mseg x) N V), (∀ j, SameGeneric O x (E 0) (E j)) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω) (EB : Fin (n + 1) → ChartBundle O (mseg (joinCoord x z)) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin (n + 1) → Fin N → K ⊕ K' → ℤ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ fnField O (joinCoord x z) = fnField O x ∧ ∀ j, IsPull O x z (E j) (EB j) ∧ IsFlagFrame (joinCoord x z) (EB j) w (b j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CommonFlag.main | exact GlobalTheory.CompanionTheory.Ar.CommonFlag.main | (intros; apply GlobalTheory.CompanionTheory.Ar.CommonFlag.main <;> assumption)
end
