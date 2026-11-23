module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeExtendScalars
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReduceLatticeCoordsToResidue
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorsionFieldOfDefinition
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle071
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle072
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MlLift
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle047
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.hodge_lattice_extend_scalars : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs)) (bar : 𝓞 E ≃+* 𝓞 E)
    (R R' : Subring Ω) (hR : R ≤ R') (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HLx : Submodule R (Vs × Module.Dual Ω Vs)) (HLy : Submodule R' (Vs × Module.Dual Ω Vs))
    (C A : Type) [Field C] [CommRing A] [Algebra A C] (ψ : R' →+* C),
    (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) →
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    HodgeAt ρH HLx ℓ t → HodgeAt ρH HLy ℓ t →
    (∀ r : R, ψ ⟨r, hR r.2⟩ ∈ (algebraMap A C).range) →
    ∃ (ρC : 𝓞 E →+* Module.End C (Fin g → C))
      (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
      (ev : HLy →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
      (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C))),
      (∀ a y, (ρHC a y).1 = ρC a y.1) ∧ (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) ∧
      Tied ℓ ψ ρ ρC ∧ IsEval ℓ ψ ρH ρHC HLy ev ∧
      HV.map ((LinearMap.fst C (Fin g → C) (Module.Dual C (Fin g → C))).restrictScalars A) = stdLat A C g ∧
      (∀ f : Module.Dual C (Fin g → C), ((0 : Fin g → C), f) ∈ HV ↔
        ∀ e ∈ stdLat A C g, f e ∈ (algebraMap A C).range) ∧
      ∀ ht : ∀ i, t i ∈ HLy, HT.IsFreeOn ρHC HV (fun i => ev ⟨t i, ht i⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists.exists_eval | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists.exists_eval | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists.exists_eval <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.reduce_lattice_coords_to_residue : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] [Field C] [CharZero C] (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g n : ℕ)
    (ℓ : Fin g → Vs) (ψ : R' →+* C) (ρC : 𝓞 E →+* Module.End C (Fin g → C)) (σ : E →+* Ω) (σC : E →+* C)
    (b : Fin n → Vs) (x : Fin n → Fin g → R'),
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρC →
    (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) →
    (∀ i, b i = comb ℓ (x i)) → LinearIndependent Ω b →
    Submodule.span R' (Set.range b) = HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) →
    Module.finrank Ω (HT.eigSp ρ σ) = n →
    LinearIndependent C (fun i k => ψ (x i k)) ∧
      Submodule.span C (Set.range fun i k => ψ (x i k)) = HT.eigSp ρC σC := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalFrame.values_basis | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalFrame.values_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalFrame.values_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

section Core

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {N : ℕ}

theorem chartQ_ratEval_mem (x : Fin (N + 1) → Ω) (c : Fin (N + 1))
    (g : MRing (fun _ : Unit => Fin (N + 1))) : ratEval x c g ∈ chartQ x c := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem (chartQ x c) a
  | add a b ha hb => simpa using (chartQ x c).add_mem ha hb
  | mul_X a i ha =>
    have hi : x i.2 / x c ∈ chartQ x c := Algebra.subset_adjoin ⟨i.2, rfl⟩
    simpa using (chartQ x c).mul_mem ha hi

theorem adjoin_insert_eq_invAdj (R : Set Ω) (h : Ω) :
    Algebra.adjoin ℚ (insert h⁻¹ R) = invAdj (Algebra.adjoin ℚ R) h := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.insert_subset_insert Algebra.subset_adjoin)
  · refine Algebra.adjoin_le (Set.insert_subset (Algebra.subset_adjoin (Set.mem_insert _ _)) ?_)
    exact fun _ hs => Algebra.adjoin_mono (Set.subset_insert _ _) hs

theorem exists_sum_eq_one_of_span_eq_top {R : Type} [CommRing R] (T : Set R) (hT : Ideal.span T = ⊤) :
    ∃ (m : ℕ) (f a : Fin m → R), (∀ l, f l ∈ T) ∧ ∑ l, a l * f l = 1 := by
  classical
  have h1 : (1 : R) ∈ Ideal.span T := hT ▸ Submodule.mem_top
  obtain ⟨w, hw, hs⟩ := Submodule.mem_span_set.1 h1
  let ε := w.support.equivFin
  refine ⟨w.support.card, fun l => (ε.symm l : R), fun l => w (ε.symm l), fun l => hw (ε.symm l).2, ?_⟩
  rw [← hs, Finsupp.sum, ← Finset.sum_coe_sort w.support (fun i => w i • i)]
  exact Equiv.sum_comp ε.symm (fun i : w.support => w i • (i : R))

theorem chart_cover_core {P : Type} (u : P → Ω → Prop) (hu0 : ∀ p h, u p h → h ≠ 0) (C B : Set P)
    (Pt Bd : Set (Subring Ω)) (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (e : ℕ)
    (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1))))
    (h1 : ∀ p ∈ C, ∃ h ∈ chartQ x c, u p h ∧ ∃ (z : Fin e → invAdj (chartQ x c) h) (n : ℕ),
      IsSncPatch Pt Bd e (invAdj (chartQ x c) h) z n)
    (h2 : ∀ I : Ideal (chartQ x c), I.IsPrime → ∃ p ∈ C, ∀ s : chartQ x c, s ∉ I ↔ u p (s : Ω))
    (h3 : ∀ h, h ∈ chartQ x c → h ≠ 0 → ∀ q : Ideal (invAdj (chartQ x c) h), q.IsPrime →
      ∃ p ∈ C, (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ u p (s : Ω)) ∧
        ∀ (z : Fin e → invAdj (chartQ x c) h) (n : ℕ), IsSncPatch Pt Bd e (invAdj (chartQ x c) h) z n →
          (p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q))
    (h4 : ∀ p ∈ C, (p ∈ B ↔ ∀ g ∈ bd, ¬ u p (ratEval x c g))) :
    ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ chartQ x c) ∧ (∀ l, a l ∈ chartQ x c) ∧
      ∑ l, a l * f l = 1 ∧ ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω,
        S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range fun j => x j / x c)) →
        Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
          LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
          Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
          ∀ q : Ideal S, q.IsPrime →
            ((∀ g ∈ bd, ∀ s : S, (s : Ω) = ratEval x c g → s ∈ q) ↔
              ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  let T : Set (chartQ x c) := {t | (t : Ω) ≠ 0 ∧ ∃ (z : Fin e → invAdj (chartQ x c) (t : Ω)) (n : ℕ),
    IsSncPatch Pt Bd e (invAdj (chartQ x c) (t : Ω)) z n}
  have hT : Ideal.span T = ⊤ := by
    by_contra hne
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hp, hs⟩ := h2 I hI.isPrime
    obtain ⟨h, hh, hu, z, n, hz⟩ := h1 p hp
    have hmem : (⟨h, hh⟩ : chartQ x c) ∈ T := ⟨hu0 p h hu, z, n, hz⟩
    exact (hs ⟨h, hh⟩).2 hu (hle (Ideal.subset_span hmem))
  obtain ⟨m, f, a, hf, hsum⟩ := exists_sum_eq_one_of_span_eq_top T hT
  refine ⟨m, fun l => f l, fun l => a l, fun l => (f l).2, fun l => (a l).2, ?_, ?_⟩
  · have := congrArg (Subtype.val) hsum
    simpa using this
  · intro l hl S hS
    rw [adjoin_insert_eq_invAdj] at hS
    subst hS
    obtain ⟨-, z, n, hz⟩ := hf l
    refine ⟨hz.smooth, z, n, hz.le, hz.li, hz.span, fun q hq => ?_⟩
    obtain ⟨p, hp, hs, hb⟩ := h3 _ (f l).2 hl q hq
    rw [← hb z n hz, h4 p hp]
    constructor
    · intro H g hg hu
      exact (hs ⟨ratEval x c g, le_invAdj _ _ (chartQ_ratEval_mem x c g)⟩).2 hu (H g hg _ rfl)
    · intro H g hg s hsg
      by_contra hn
      exact H g hg (hsg ▸ (hs s).1 hn)

end Core

theorem range_ratios_unit {Ω : Type} [Field Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) :
    (Set.range fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2 / x (c p.1)) =
      Set.range fun j => x j / x (c ()) := by
  ext w
  constructor
  · rintro ⟨⟨_, j⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨(), j⟩, rfl⟩

theorem isSncModel_of_chart_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)) (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1)))), (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → ∃ h ∈ Mdl.chartQ x c, unitAt ξ p h ∧ ∃ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n) → (∀ c, x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ ∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) → (∀ c h, x c ≠ 0 → h ∈ Mdl.chartQ x c → h ≠ 0 → ∀ q : Ideal (Mdl.invAdj (Mdl.chartQ x c) h), q.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.invAdj (Mdl.chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧ ∀ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n → (p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) → (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → (p ∈ B ↔ ∀ g ∈ bd, ¬ unitAt ξ p (Mdl.ratEval x c g))) → Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd := by
  intro Ω _ _ X ξ N x e B bd h1 h2 h3 h4
  unfold Cmp.IsSncModel
  intro c hc
  have hx : x (c ()) ≠ 0 := hc ()
  have key := chart_cover_core (P := Cpt ξ) (fun p h => unitAt ξ p h) (fun p h hh => hh.1)
    {p | Char0 ξ p ∧ InChart ξ x (c ()) p} B (Pts ξ) (regAt ξ '' B) x (c ()) e bd
    (fun p hp => h1 _ p hp.1 hp.2)
    (fun I hI => by
      obtain ⟨p, a, b, d⟩ := h2 _ hx I hI
      exact ⟨p, ⟨a, b⟩, d⟩)
    (fun h hh h0 q hq => by
      obtain ⟨p, a, b, d, f⟩ := h3 _ h hx hh h0 q hq
      exact ⟨p, ⟨a, b⟩, d, f⟩)
    (fun p hp => h4 _ p hp.1 hp.2)
  beta_reduce
  rw [range_ratios_unit x c]
  exact key

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.chart_prime_gives_component : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.component_gives_chart_prime : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → ∀ p : Cpt ξ, Char0 ξ p → InChart ξ x c p → ∃ I : Ideal (Mdl.chartQ x c), I.IsPrime ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_prime_chartQ | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_prime_chartQ | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_prime_chartQ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem torsion_defined_over_numberField : ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (P : Out.PolAV (Sp L)) (n : ℕ), 0 < n → ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (e : L →+* F), (∀ x, ((e x : F) : ℂ) = σ x) ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ y : Sp F ⟶ P.A.left, y ≫ P.A.hom = spMap e ∧ spMap (algebraMap F ℂ) ≫ y = x.left :=
  @PositivityTheory.Xgn.torsion_field_of_definition

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.hermitian_period_linear_algebra : ∀ (p q g : ℕ) (T T' : (Fin g → ℂ) → (Fin g → ℂ)) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ) (π : Fin p ⊕ Fin q → Fin g → ℂ) (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ), IsLinearMap ℂ T → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → S.det ≠ 0 → LinearIndependent ℂ V → LinearIndependent ℂ W → (∀ n, T (π n) ∈ Submodule.span ℂ (Set.range V)) → (∀ n, T' (π n) ∈ Submodule.span ℂ (Set.range W)) → (∀ m n, hermForm Hm (T (π m)) (T (π n)) - star (hermForm Hm (T' (π m)) (T' (π n))) = 2 * Complex.I * S m n) → ∃! x : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ × Matrix (Fin q) (Fin p ⊕ Fin q) ℂ × ℂ, (∀ n, T' (π n) = ∑ j, x.2.1 j n • W j) ∧ (∀ j n, ∑ m, x.1 j m * S m n = x.2.1 j n) ∧ x.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, ∀ a, T (∑ m, C a m • π m) = V a) ∧ ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • π m) = V a) → (Matrix.fromRows C x.1).det = x.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra | exact GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra | (intros; apply GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem _root_.GlobalTheory.T.algebraic_independent_of_adjoin : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (u v : ι → K), AlgebraicIndependent Ω u → (∀ a, u a ∈ IntermediateField.adjoin Ω (Set.range v)) → AlgebraicIndependent Ω v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range <;> assumption)
end

section

open TensorProduct

namespace GlobalTheory.CompanionTheory.FinAlgFlat

theorem isPushout_cancel (R k A B T U : Type*) [CommRing R] [CommRing k] [CommRing A] [CommRing B]
    [CommRing T] [CommRing U]
    [Algebra R k] [Algebra R A] [Algebra R B] [Algebra R T] [Algebra R U]
    [Algebra A B] [Algebra A T] [Algebra A U] [Algebra B U] [Algebra k T] [Algebra k U]
    [Algebra T U]
    [IsScalarTower R A B] [IsScalarTower R A T] [IsScalarTower R A U] [IsScalarTower R B U]
    [IsScalarTower R k T] [IsScalarTower R k U] [IsScalarTower k T U] [IsScalarTower A T U]
    [IsScalarTower A B U]
    (h₁ : Algebra.IsPushout R A k T) (h₂ : Algebra.IsPushout R B k U) :
    Algebra.IsPushout A B T U := by
  rw [Algebra.isPushout_iff] at h₁ h₂ ⊢
  refine IsBaseChange.of_comp (R := R) (S := A) (T := B)
    (f := (IsScalarTower.toAlgHom R k T).toLinearMap)
    (h := (IsScalarTower.toAlgHom A T U).toLinearMap) h₁ ?_
  convert h₂ using 1
  ext x
  simp [IsScalarTower.algebraMap_apply k T U]

noncomputable abbrev fibreMap (R k A B : Type*) [CommRing R] [CommRing k] [CommRing A] [CommRing B]
    [Algebra R k] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    k ⊗[R] A →+* k ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R k) (IsScalarTower.toAlgHom R A B)).toRingHom

theorem fibreMap_isLocalization (R k A B : Type*) [CommRing R] [CommRing k] [CommRing A]
    [CommRing B] [Algebra R k] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B] :
    letI := (fibreMap R k A B).toAlgebra
    IsLocalization (M.map (Algebra.TensorProduct.includeRight : A →ₐ[R] k ⊗[R] A))
      (k ⊗[R] B) := by
  letI iTU : Algebra (k ⊗[R] A) (k ⊗[R] B) := (fibreMap R k A B).toAlgebra
  letI iAT : Algebra A (k ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  letI iBU : Algebra B (k ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  letI iAU : Algebra A (k ⊗[R] B) := ((algebraMap B (k ⊗[R] B)).comp (algebraMap A B)).toAlgebra
  haveI t1 : IsScalarTower A B (k ⊗[R] B) := .of_algebraMap_eq' rfl
  haveI t2 : IsScalarTower A (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by
    change (1 : k) ⊗ₜ[R] (algebraMap A B a) = fibreMap R k A B ((1 : k) ⊗ₜ[R] a)
    simp
  haveI t3 : IsScalarTower R A (k ⊗[R] B) := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B (k ⊗[R] B) r, IsScalarTower.algebraMap_apply R A B r]
    rfl
  haveI t4 : IsScalarTower k (k ⊗[R] A) (k ⊗[R] B) := .of_algebraMap_eq fun a => by
    change a ⊗ₜ[R] (1 : B) = fibreMap R k A B (a ⊗ₜ[R] (1 : A))
    simp
  have h := isPushout_cancel R k A B (k ⊗[R] A) (k ⊗[R] B)
    TensorProduct.isPushout' TensorProduct.isPushout'
  exact (Algebra.isLocalization_iff_isPushout M B).mpr h.symm

end GlobalTheory.CompanionTheory.FinAlgFlat

namespace GlobalTheory.CompanionTheory.FinAlgFlat

theorem fibreMap_flat_localize (R k P Q Bp An : Type*) [CommRing R] [CommRing k] [CommRing P]
    [CommRing Q] [CommRing Bp] [CommRing An] [Algebra R k] [Algebra R P] [Algebra R Q]
    [Algebra R Bp] [Algebra R An] [Algebra P Q] [Algebra P Bp] [Algebra P An] [Algebra Q An]
    [Algebra Bp An] [IsScalarTower R P Q] [IsScalarTower R P Bp] [IsScalarTower R Q An]
    [IsScalarTower R Bp An] [IsScalarTower P Q An] [IsScalarTower P Bp An]
    (M : Submonoid P) [IsLocalization M Bp] (N : Submonoid Q) [IsLocalization N An]
    (h : (fibreMap R k P Q).Flat) : (fibreMap R k Bp An).Flat := by
  have hQA : (fibreMap R k Q An).Flat := by
    have hl := fibreMap_isLocalization R k Q An N
    letI := (fibreMap R k Q An).toAlgebra
    exact IsLocalization.flat (k ⊗[R] An)
      (N.map (Algebra.TensorProduct.includeRight : Q →ₐ[R] k ⊗[R] Q))
  have e : (fibreMap R k Bp An).comp (fibreMap R k P Bp) =
      (fibreMap R k Q An).comp (fibreMap R k P Q) := by
    refine RingHom.ext fun x => ?_
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b =>
      simp [← IsScalarTower.algebraMap_apply]
  have hPA : ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).Flat := by
    rw [e]; exact h.comp hQA
  have hl := fibreMap_isLocalization R k P Bp M
  letI i1 := (fibreMap R k P Bp).toAlgebra
  letI i2 := (fibreMap R k Bp An).toAlgebra
  letI i3 := ((fibreMap R k Bp An).comp (fibreMap R k P Bp)).toAlgebra
  haveI : IsScalarTower (k ⊗[R] P) (k ⊗[R] Bp) (k ⊗[R] An) := .of_algebraMap_eq' rfl
  exact (Module.flat_iff_of_isLocalization (k ⊗[R] Bp)
    (M.map (Algebra.TensorProduct.includeRight : P →ₐ[R] k ⊗[R] P)) (k ⊗[R] An)).mpr hPA

theorem flat_localization_of_fibre (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Algebra P Q] [IsScalarTower R P Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q]
    (h : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat) (n : Ideal Q) [n.IsMaximal] :
    Module.Flat P (Localization.AtPrime n) := by
  haveI : Module.Finite P Q := .of_restrictScalars_finite R P Q
  haveI : Algebra.IsIntegral P Q := inferInstance
  haveI : Algebra.IsIntegral R P := inferInstance
  haveI : IsNoetherianRing P := IsNoetherianRing.of_finite R P
  haveI : IsNoetherianRing Q := IsNoetherianRing.of_finite R Q
  let p : Ideal P := n.comap (algebraMap P Q)
  haveI hp : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := P) n
  have hmR : p.comap (algebraMap R P) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) p)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime n) :=
    (Localization.localRingHom p n (algebraMap P Q) rfl).toAlgebra
  haveI tP : IsScalarTower P (Localization.AtPrime p) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n) x]
      exact (Localization.localRingHom_to_map p n (algebraMap P Q) rfl x).symm
  haveI tR : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R P (Localization.AtPrime p) x,
        ← IsScalarTower.algebraMap_apply P (Localization.AtPrime p) (Localization.AtPrime n),
        IsScalarTower.algebraMap_apply P Q (Localization.AtPrime n),
        ← IsScalarTower.algebraMap_apply R P Q,
        ← IsScalarTower.algebraMap_apply R Q (Localization.AtPrime n)]
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime n) :=
    IsLocalization.isNoetherianRing n.primeCompl _ inferInstance
  haveI : IsLocalHom (algebraMap R (Localization.AtPrime p)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hnu
    have ham : a ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr hnu
    rw [← hmR, Ideal.mem_comap] at ham
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p
      (algebraMap R P a)).mpr ham
    rw [← IsScalarTower.algebraMap_apply R P (Localization.AtPrime p)] at hm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime n)) :=
    Localization.isLocalHom_localRingHom p n (algebraMap P Q) rfl
  have hfl : Module.Flat R (Localization.AtPrime n) := inferInstance
  have hfib := fibreMap_flat_localize R (IsLocalRing.ResidueField R) P Q (Localization.AtPrime p)
    (Localization.AtPrime n) p.primeCompl n.primeCompl h
  have hBA : Module.Flat (Localization.AtPrime p) (Localization.AtPrime n) :=
    GlobalTheory.T.module_flat_of_flat_and_fibre_flat R (Localization.AtPrime p) (Localization.AtPrime n) hfl hfib
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
    (Localization.AtPrime n)).mp hBA

theorem flat_of_fibreMap_flat (R P Q : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q] [Algebra P Q] [IsScalarTower R P Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q]
    (h : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat) : Module.Flat P Q :=
  Module.flat_of_isLocalized_maximal Q Q (fun n _ => Localization.AtPrime n)
    (fun n _ => Algebra.linearMap Q _) (fun n _ => flat_localization_of_fibre R P Q h n)

theorem ringHom_flat_of_fibre_flat : ∀ (R P Q : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]
    [Module.Finite R P] [Module.Finite R Q] [Module.Flat R Q] (φ : P →ₐ[R] Q),
    (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom.Flat →
      φ.toRingHom.Flat := by
  intro R P Q _ _ _ _ _ _ _ _ _ _ φ h
  letI : Algebra P Q := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R P Q := .of_algebraMap_eq fun x => (φ.commutes x).symm
  have e : IsScalarTower.toAlgHom R P Q = φ := by ext; rfl
  have h' : (fibreMap R (IsLocalRing.ResidueField R) P Q).Flat := by
    rw [fibreMap, e]; exact h
  exact flat_of_fibreMap_flat R P Q h'

end GlobalTheory.CompanionTheory.FinAlgFlat
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.log_hermitian_sum_bounded : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) (A : HermLine ι) (B : J → HermLine ι) (T : Finset J), IsSmoothHerm A → (∀ j, IsSmoothHerm (B j)) → A.a = -∑ j ∈ T, (B j).a → ∃ C : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) → |Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z)| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded | exact GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded | (intros; apply GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.theta_multiplier_normal_form : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (Lr : RigLB A) (_ : CubicalStr A Lr) (g : ℕ) (u₀ : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g), ∃ (u : HolUnif A Lr.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.ex = u₀.ex ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Lr.L.U i → u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_appellHumbert_frame_of_cubical | exact GlobalTheory.CompanionTheory.Ar.exists_appellHumbert_frame_of_cubical | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_appellHumbert_frame_of_cubical <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.M0

theorem fieldPoint_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x :=
  @PositivityTheory.HtPt.Ml.lift_generic_point

end GlobalTheory.CompanionTheory.Ar.M0
end
