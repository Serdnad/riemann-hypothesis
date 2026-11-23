module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle053
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalChartCoords
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle152
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame

section Abstract

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {E : Type} [Field E] [NumberField E]
  {A : Subring K}

theorem mem_of_isFreeOn {ρ : 𝓞 E →+* Module.End K V} {L : Submodule A V} {N : ℕ} {t : Fin N → V}
    (h : HT.IsFreeOn ρ L t) (i : Fin N) : t i ∈ L := by
  have e : t i = ρ 1 (t i) := by simp

  rw [h.2.2, e, ← (RingOfIntegers.basis E).sum_repr 1, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_zsmul, LinearMap.smul_apply]
  exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _

theorem exists_lift_basis {R Y : Type} [CommRing R] [AddCommGroup Y] [Module R Y] (f : R →+* K)
    (hf : Function.Injective f) (hA : ∀ a, a ∈ A ↔ ∃ c, f c = a) (Φ : Y →+ V)
    (hsmul : ∀ (c : R) y, Φ (c • y) = f c • Φ y) (hinj : Function.Injective Φ)
    {ρ : 𝓞 E →+* Module.End K V} {L : Submodule A V} (hrange : ∀ v, v ∈ L ↔ ∃ y, Φ y = v)
    (rB : 𝓞 E → Y → Y) (hact : ∀ a y, Φ (rB a y) = ρ a (Φ y)) {N : ℕ} {t : Fin N → V}
    (h : HT.IsFreeOn ρ L t) :
    ∃ x : Fin N → Y, (∀ j, Φ (x j) = t j) ∧
      LinearIndependent R (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rB (RingOfIntegers.basis E q.2) (x q.1)) ∧
      Submodule.span R (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rB (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  choose x hx using fun i => (hrange (t i)).1 (mem_of_isFreeOn h i)
  have hΦ : ∀ c : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R,
      Φ (∑ q, c q • rB (RingOfIntegers.basis E q.2) (x q.1)) =
        ∑ q, f (c q) • ρ (RingOfIntegers.basis E q.2) (t q.1) := fun c => by

    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hsmul, hact, hx]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc q
    have h1 := Fintype.linearIndependent_iff.1 h.1 (fun q => f (c q)) (by rw [← hΦ, hc, map_zero])
    exact hf ((h1 q).trans (map_zero f).symm)
  · rw [eq_top_iff]
    rintro y -
    have hy : Φ y ∈ L := (hrange _).2 ⟨y, rfl⟩
    rw [h.2.2] at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
    choose c' hc' using fun q => (hA (c q : K)).1 (c q).2
    have e : y = ∑ q, c' q • rB (RingOfIntegers.basis E q.2) (x q.1) := hinj (by
      rw [hΦ, ← hc]
      exact Finset.sum_congr rfl fun q _ => by rw [hc']; rfl)
    rw [e]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

end Abstract

theorem exists_of_mem_stdLat {Ω : Type} [Field Ω] {A : Subring Ω} {d : ℕ}
    {T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)} {w : (Fin d → Ω) × (Fin d → Ω)}
    (h : w ∈ stdLat A T) : ∃ y₀ : (Fin d → Ω) × (Fin d → Ω), (∀ i, y₀.1 i ∈ A ∧ y₀.2 i ∈ A) ∧ w = T y₀ := by
  induction h using Submodule.span_induction with
  | mem w hw => exact hw
  | zero => exact ⟨0, fun i => ⟨A.zero_mem, A.zero_mem⟩, (map_zero T).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, rfl⟩ := ha
    obtain ⟨z, hz, rfl⟩ := hb
    exact ⟨y + z, fun i => ⟨A.add_mem (hy i).1 (hz i).1, A.add_mem (hy i).2 (hz i).2⟩, (map_add T y z).symm⟩
  | smul c a _ ha =>
    obtain ⟨y, hy, rfl⟩ := ha
    exact ⟨(c : Ω) • y, fun i => ⟨A.mul_mem c.2 (hy i).1, A.mul_mem c.2 (hy i).2⟩, (map_smul T (c : Ω) y).symm⟩

theorem toVec_injective (Ω : Type) [Field Ω] (d : ℕ) : Function.Injective (toVec Ω d) := by
  intro y y' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 ((dotProductEquiv Ω (Fin d)).injective h2)

theorem toVec_surjective (Ω : Type) [Field Ω] (d : ℕ) : Function.Surjective (toVec Ω d) := by
  rintro ⟨a, φ⟩
  obtain ⟨b, rfl⟩ := (dotProductEquiv Ω (Fin d)).surjective φ
  exact ⟨(a, b), rfl⟩

section Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω] {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d r : ℕ}
  {M : LieModel t.G ξ (Fin d → Ω)} {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)}

theorem vmap_injective {R S : Type} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (vmap (d := d) f) := fun _ _ h =>
  Prod.ext (funext fun i => hf (congrFun (congrArg Prod.fst h) i))
    (funext fun i => hf (congrFun (congrArg Prod.snd h) i))

theorem toH_injective (hξ : IsCptGen ξ) (S : GermSys t ξ M) (p : Cpt ξ) : Function.Injective (toH S p) :=
  fun _ _ h => vmap_injective (hξ.inj p)
    ((GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.1.1 (toVec_injective Ω d h))

theorem toH_mem_iff (S : GermSys t ξ M) {𝓗 : HodgeLat M.lat ρ H.bar r} (hG : S.Gives 𝓗) (p : Cpt ξ)
    (v : (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) : v ∈ 𝓗.HL p ↔ ∃ y, toH S p y = v := by
  constructor
  · intro hv
    obtain ⟨w, rfl⟩ := toVec_surjective Ω d v
    obtain ⟨y₀, hy₀, rfl⟩ := exists_of_mem_stdLat ((hG.2 p w).1 hv)
    choose a ha using fun i => (hy₀ i).1
    choose b hb using fun i => (hy₀ i).2
    refine ⟨(a, b), ?_⟩
    have e : vmap (genMap ξ p) (a, b) = y₀ := Prod.ext (funext ha) (funext hb)
    rw [toH, e]
  · rintro ⟨y, rfl⟩
    exact (hG.2 p _).2 (Submodule.subset_span ⟨vmap (genMap ξ p) y,
      fun i => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩)

theorem toH_rhoH (S : GermSys t ξ M) {𝓗 : HodgeLat M.lat ρ H.bar r} (hG : S.Gives 𝓗) (p : Cpt ξ) (a : 𝓞 E)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (rhoH (S.g p).B a y) = 𝓗.ρH a (toH S p y) := by
  have h1 := vmap_rhoH (S.mapK p) a y
  have h2 := LinearMap.congr_fun ((GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.2.2.1 a) (vmap (genMap ξ p) y)
  have h3 := hG.1 a (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))
  have e1 := congrArg (fun z => toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) z)) h1
  have e2 := congrArg (toVec Ω d) h2.symm
  exact (e1.trans e2).trans h3.symm

end Germ

theorem exists_basis_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (σ : E →+* Ω) (u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)), IsCptGen ξ → S.Gives 𝓗 → (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → ∀ p : Cpt ξ, ∃ (x : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) (A : Matrix (Fin r) (Fin r) Ω), IsHBasis (S.g p).B x ∧ (𝓗.quot σ).IsFrameAt (fun j => ∑ l, A j l • u l) p ∧ ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (x j)) = ∑ l, A j l • u l := by
  intro E _ _ _ H _ X t Ω _ _ ξ d r M S ρ 𝓗 σ u hξ hG hσ _ hu p
  obtain ⟨U, hU, x, hx⟩ := 𝓗.free p
  have hfree := hx p hU
  obtain ⟨x', h1, h2, h3⟩ := exists_lift_basis (genMap ξ p) (hξ.inj p) (A := regAt ξ p) (fun _ => Iff.rfl)
    (AddMonoidHom.mk' (toH S p) (toH_add S p)) (toH_smul S p) (toH_injective hξ S p)
    (toH_mem_iff S hG p) (fun a y => rhoH (S.g p).B a y) (toH_rhoH S hG p) hfree
  have hA : ∀ i, ∃ c : Fin r → Ω, ∑ l, c l • u l = HT.eigProj 𝓗.ρH σ (x i) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hu ▸ HT.LatBasic.eigProj_mem _ _ _)
  choose A hA using hA
  refine ⟨x', Matrix.of A, ⟨h2, h3⟩, ?_, fun j => ?_⟩
  · have e : (fun j => ∑ l, Matrix.of A j l • u l) = fun j => HT.eigProj 𝓗.ρH σ (x j) := funext hA
    rw [e]
    exact ⟨HodgeDeterminantLattice.linearIndependent_eigProj σ hfree,
      HodgeDeterminantLattice.eigQuot_eq_span σ hfree fun a => ⟨⟨_, hσ p a⟩, rfl⟩⟩
  · have := h1 j
    change toH S p (x' j) = x j at this
    rw [this]
    exact (hA j).symm

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

section Ring

variable {k : Type} [Field k] {d : ℕ}

theorem homAt_comp_homAt {X : Scheme.{0}} (x : Sp k ⟶ X) {A B C : Type} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] [CommRing C] [Algebra k C] (f : A →ₐ[k] B) (h : B →ₐ[k] C) :
    homAt x h ≫ homAt x f = homAt x (h.comp f) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem jetAug_comp_copy (n M : ℕ) (i : Fin n) :
    (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k).comp (jetCopy d M i) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro q
  have e : jetCopy (S := k) d M i (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, q.2)) :=
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.aeval_X _ q)
  have a₁ : (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X (i, q.2))) = 0 :=
    MvPolynomial.aeval_X _ _
  have a₂ : (jetAug : Jet k (Fin 1 × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 :=
    MvPolynomial.aeval_X _ _
  show (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k) (jetCopy (S := k) d M i (Ideal.Quotient.mk _ (MvPolynomial.X q))) =
    (jetAug : Jet k (Fin 1 × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X q))
  rw [e, a₁, a₂]

def sub₀ (M : ℕ) : Jet k (Fin 2 × Fin d) M →ₐ[k] Jet k (Fin 1 × Fin d) M :=
  jetSubstP M fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) p.1 p.2

def trJ (m M : ℕ) (h : m ≤ M) : Jet k (Fin 1 × Fin d) M →ₐ[k] Jet k (Fin 1 × Fin d) m :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

theorem aug_jq (w : Fin d → k) (p m : ℕ) :
    ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
        Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m).comp
      ((jq w p m : _ →ₐ[k] _) : Jet k (Fin 2 × Fin d) (p + m + 1) →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p) =
    ((trJ m (p + m + 1) (by omega)).comp (sub₀ (p + m + 1)) :
      Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] Jet k (Fin 1 × Fin d) m).toRingHom := by
  have key : ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m).restrictScalars k).comp
      (jq w p m) = (trJ m (p + m + 1) (by omega)).comp (sub₀ (p + m + 1)) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    have hq : jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) =
        if i = 0 then algebraMap k _ (w j) * dQ (Jet k (Fin 1 × Fin d) m) p
        else inR (k := k) (Jet k (Fin 1 × Fin d) m) p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) :=
      MvPolynomial.aeval_X _ _
    have hs : sub₀ (k := k) (d := d) (p + m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) =
        Ideal.Quotient.mk _ ((![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) i j - MvPolynomial.C (MvPolynomial.constantCoeff
            ((![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] :
              Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) i j))) :=
      congrArg (Ideal.Quotient.mk _) (MvPolynomial.aeval_X _ _)
    have hd : (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m)
        (dQ (Jet k (Fin 1 × Fin d) m) p) = 0 := MvPolynomial.aeval_X _ _
    show (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m)
        (jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X (i, j)))) =
      trJ m (p + m + 1) (by omega) (sub₀ (p + m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))))
    rw [hq, hs]
    fin_cases i
    · simp only [Fin.zero_eta, if_true, map_mul, hd, mul_zero]
      simp [trJ]
    · simp [trJ, inR]
  exact congrArg AlgHom.toRingHom key

end Ring

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem comp_psum_one {T T' : Over X0} (U : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ t.G)) (h : ∀ i, U ≫ xs i = 1)
    (I : Finset (Fin n)) : U ≫ psum t.G xs I = 1 := by
  have e := psum_hom (preHom (G := t.G) U) xs I
  have e' : (fun i => preHom (G := t.G) U (xs i)) = fun _ => (1 : T' ⟶ t.G) := funext h
  rw [e'] at e
  refine e.trans ?_
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons a l ih => exact (congrArg ((1 : T' ⟶ t.G) * ·) ih).trans (_root_.one_mul _)

end Pts



theorem frame_test_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (j₀ : t.PP.L.ι), ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ e₀ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ, (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) e₀ = 1 ∧ ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val (g.e (p + m + 1)) (homAt x (jq w p m)).left z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
  intro E _ _ _ H _ X0 t k _ p x d g w m j₀ hj₀
  have hpt : ∀ (I : ULift.{0} (Finset (Fin 2))) q, ((homAt x (jq w p m)).left ≫
      cφG t ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)] I) q ∈ t.PP.L.U j₀ := by
    intro I q
    have h0 : ∀ i : Fin 2, homAt x (jetAug : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] k) ≫
        jptG t x d g.x (p + m + 1) i = 1 := by
      intro i
      rw [jptG, ← Category.assoc, homAt_comp_homAt, jetAug_comp_copy]
      exact g.chart.zero _
    have hz := comp_psum_one t (homAt x (jetAug : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] k))
      ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)]
      (by intro i; fin_cases i; exacts [h0 0, h0 1]) I.down
    rw [Scheme.Hom.comp_apply]
    exact jet_left_mem t x j₀ hj₀ _ hz _
  have hred : ∀ (z' : Sp (Jet k (Fin 1 × Fin d) m)) (J' : (Sp (Jet k (Fin 1 × Fin d) m) ⟶ t.G.left) → t.PP.L.ι),
      Good t.PP.L z' J' → val (g.e (p + m + 1))
        (spMap ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
          Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (jq w p m)).left) z' J' = 1 := by
    intro z' J' hJ'
    have e : spMap ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
          Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (jq w p m)).left =
        spMap ((trJ m (p + m + 1) (by omega) : Jet k (Fin 1 × Fin d) (p + m + 1) →ₐ[k] _) :
          Jet k (Fin 1 × Fin d) (p + m + 1) →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (sub₀ (p + m + 1))).left := by
      have := aug_jq w p m
      simp only [homAt, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [this]
      rfl
    rw [e, ← val_pull hJ' (g.e (p + m + 1)) (homAt x (sub₀ (p + m + 1))).left]
    exact (val_corr hJ' (g.axes (p + m + 1)).1 _).trans (val_one _)
  have exists_unitΓ_eq {A : Type} [CommRing A] (u : Γ(Sp A, ⊤)ˣ) : ∃ e : Aˣ, unitΓ e = u := by
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom u, Units.ext ?_⟩
    exact congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id

  have val_eq_unit_of_red : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (B : Type) [CommRing B] (p : ℕ) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (Jet B Unit p) ⟶ Y) (j₀ : L.ι), (∀ κ q, (r ≫ φ κ) q ∈ L.U j₀) → (∀ (z' : Sp B) (J' : (Sp B ⟶ X) → L.ι), Good L z' J' → (∀ κ, J' (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) = j₀) → val t (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r) z' J' = 1) → ∃ e₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) e₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ X) → L.ι), Good L z J → (∀ κ, J (r ≫ φ κ) = j₀) → val t r z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
    intro X Y L hL B _ p K _ φ ε t r j₀ h₁ h₂
    have hW : (⊤ : (Sp (Jet B Unit p)).Opens) ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j₀) :=
      fun q _ => Set.mem_iInter.2 fun κ => h₁ κ q
    obtain ⟨e₀, he₀⟩ := exists_unitΓ_eq (res hW (pullU r _ (t.s fun _ => j₀)))
    have key : ∀ (Z : Scheme.{0}) (f : Z ⟶ Sp (Jet B Unit p)) (z : Z),
        gm f z ⊤ (unitΓ e₀) = gm (f ≫ r) z (LB.wchart L φ (fun _ => j₀)) (t.s fun _ => j₀) := by
      intro Z f z
      rw [he₀, gm_res f z hW (Set.mem_univ _)]
      exact gm_pull f r z _ (hW (Set.mem_univ _)) _
    refine ⟨e₀, ?_, ?_⟩
    · have hv : pullU (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) ⊤ (unitΓ e₀) = 1 := by
        apply unit_ext
        intro z' _
        obtain ⟨J', hJ', e⟩ := exists_good L hL z'
          (fun κ => spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) (fun _ => j₀)
          (fun _ _ _ => rfl) (fun κ => h₁ κ _)
        have hv := h₂ z' J' hJ' e
        rw [val_of t _ z' J' (fun _ => j₀) (fun κ => by rw [Category.assoc]; exact e κ), ← key] at hv
        have hp := gm_pull (𝟙 _) (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) z' ⊤ (Set.mem_univ _)
          (unitΓ e₀)
        rw [Category.id_comp] at hp
        rw [map_one]
        exact hp.trans hv
      apply toΓ_inj
      rw [map_one]
      exact (spMap_toΓ _ _).symm.trans (congrArg Units.val hv)
    · intro z J _ hc
      rw [val_of t r z J (fun _ => j₀) hc, key, Category.id_comp]
  obtain ⟨e₀, he, hv⟩ := val_eq_unit_of_red t.G.left (Sp (Jet k (Fin 2 × Fin d) (p + m + 1))) t.PP.L t.PP.isLB
    (Jet k (Fin 1 × Fin d) m) p (ULift (Finset (Fin 2)))
    (cφG t ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)]) (cε 2) (g.e (p + m + 1))
    (homAt x (jq w p m)).left j₀ hpt (fun z' J' hJ' _ => hred z' J' hJ')
  exact ⟨e₀, he, fun z J hJ hc => hv z J hJ fun I => hc _ (hpt I z)⟩

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

theorem _root_.GlobalTheory.T.regular_local_chart_coords : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (c : (k : K) → J k)
    (w : (Σ k, J k) → ℂ), w ∈ mcPts P → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    ∀ (a : ℕ) (r : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (h : MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      [IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)))],
    ringKrullDim (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) = n → a ≤ n →
    Ideal.span (Set.range fun i => algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) (r i)) =
      Ideal.map (algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))))
        (ReciprocityTheory.AnForm.R.ptIdeal (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) →
    (∀ i, eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) (r i) = 0) →
    eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) h ≠ 0 →
    (∀ v ∈ ReciprocityTheory.AnForm.R.zeroSet (Cmp.SncRes.ideal (pC P) c), eval v h ≠ 0 →
      ((fun q => v (Fintype.equivFin (Σ k, J k) q)) ∈ Bd ↔ ∃ i : Fin n, (i : ℕ) < a ∧ eval v (r i) = 0)) →
    ∃ (χ : SncChart P n Bd) (O : Set ((Σ k, J k) → ℂ)), IsOpen O ∧ w ∈ O ∧
      ∀ z ∈ O ∩ mcPts P, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c' : K → ℂ, (∀ k, c' k ≠ 0) ∧
        z = torusSmul c' (χ.γ t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartParams.sncChart_of_regular_parameters | exact GlobalTheory.CompanionTheory.Ar.ChartParams.sncChart_of_regular_parameters | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartParams.sncChart_of_regular_parameters <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.vertical_statement_holds : VerticalStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.vertical_holds | exact GlobalTheory.CompanionTheory.Ar.Flat.vertical_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.vertical_holds <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

theorem _root_.GlobalTheory.T.resolution_statement_holds : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds | exact GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.torus_extension_rank_bound : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MaxTorus.kernel_eq_of_rank_le | exact GlobalTheory.CompanionTheory.Ar.MaxTorus.kernel_eq_of_rank_le | (intros; apply GlobalTheory.CompanionTheory.Ar.MaxTorus.kernel_eq_of_rank_le <;> assumption)
end
