module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle025
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle052
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.AHWeil

theorem eq_top_of_add_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (W : Submodule ℂ (Fin g → ℂ)) (h : ∀ z : Fin g → ℂ, ∃ l : Λ, z - (l : Fin g → ℂ) ∈ W) : W = ⊤ := by
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hW : IsClosed (W : Set (Fin g → ℂ)) := W.closed_of_finiteDimensional
  obtain ⟨l, hl⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun l : Λ => (Homeomorph.subRight (l : Fin g → ℂ)) ⁻¹' (W : Set (Fin g → ℂ)))
    (fun l => hW.preimage (Homeomorph.continuous _))
    (Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 (h z))
  rw [← Homeomorph.preimage_interior] at hl
  obtain ⟨z, hz⟩ := hl
  exact W.eq_top_of_nonempty_interior' ⟨_, hz⟩

theorem dim_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g g' : ℕ} (u : HolUnif A L g) (u' : HolUnif A L g')
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z) : g = g' := by
  haveI := u.discrete
  haveI := u'.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := eq_top_of_add_discrete u'.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u'.ex w)
    refine ⟨⟨w - F z, (u'.ker _).1 ?_⟩, z, by simp⟩
    have h := u'.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

theorem tangent_and_weil_of_isAH : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ g = P.g ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
  ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin g → ℂ))) (unitOn c) := by
  intro hT P g u Hm χ hu
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u₀, H₀, χ₀, E₀, hu₀, -, hv, hw, -, -, hE, -, hW⟩ := hT P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  obtain rfl := dim_eq u u₀ F hF
  obtain ⟨⟨Ef, hEf, hB⟩, h1, h2⟩ := unimodular_and_tangent_of_isAH hT P rig hrig u Hm χ hu
  refine ⟨Ef, hEf, hB, rfl, h1, h2, fun k a b c hk hc => ?_⟩
  have ha := (UnifCompare.mem_iff u u₀ F hF a).2 a.2
  have hb := (UnifCompare.mem_iff u u₀ F hF b).2 b.2
  have e : Ef a b = E₀ ⟨F a, ha⟩ ⟨F b, hb⟩ := by
    have h := hE ⟨F a, ha⟩ ⟨F b, hb⟩
    rw [UnifCompare.hermForm_eq P.isLB u u₀ hu hu₀ F hF, ← hEf] at h
    exact_mod_cast h.symm
  have h := hW k ⟨F a, ha⟩ ⟨F b, hb⟩ c hk (e ▸ hc)
  rwa [← map_smul, ← map_smul, hF, hF] at h

end GlobalTheory.AHWeil
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM


open PureTypeVector in
theorem cmDatum_form_sqrtNegD_pure_period {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) {ρ : ℂ}
    (hty : ∀ i, ty i (H.rt : E) = ρ) {x : D.La} (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ((D.EF (H.w0 • x) x : ℤ) : ℝ) = ρ.im * r := by
  obtain ⟨hlin, hinj, -, -, Hm, hH, hpos, hEF⟩ := hP
  have hw0 : Pe (H.w0 • x) = ((1 + ρ) / 2) • Pe x := by
    funext i
    rw [hlin, Pi.smul_apply, smul_eq_mul]
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      simpa [map_ofNat] using this
    have h3 := congrArg (ty i) h2
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hty i] at h3
    rw [← h3]; ring
  set r : ℝ := (hermForm Hm (Pe x) (Pe x)).re with hr
  have hre : hermForm Hm (Pe x) (Pe x) = (r : ℂ) :=
    Complex.ext (by simp [hr]) (by simp [hermForm_self_im hH])
  have hr0 : 0 < r := hpos _ fun h => hx (hinj (by rw [h, map_zero]))
  refine ⟨r / 2, by positivity, ?_⟩
  rw [← hEF, hw0]
  have := hermForm_smul_smul Hm ((1 + ρ) / 2) 1 (Pe x) (Pe x)
  rw [one_smul] at this
  rw [this, hre]
  simp
  ring

theorem definite_datum_form_pos :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ),
      (D.q = 0 ∧ 0 < ((ε : ℤ) : ℝ) * H.rt0.im) ∨ (D.p = 0 ∧ ((ε : ℤ) : ℝ) * H.rt0.im < 0) →
      ∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x := by
  intro E _ _ _ H D ε h x hx
  obtain ⟨g, ty, hty⟩ : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let n : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ, Fin (n τ))).symm
    have key : ∀ τ, Nat.card {i // (e i).1 = τ} = n τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun s => s.1 = τ) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun h => (key τ).trans (if_pos h), fun h => (key τ).trans (if_neg h)⟩⟩
  obtain ⟨Pe, hP⟩ := datum_exists_period E H D g ty hty
  have hcard : ∀ i, Nat.card {j // ty j = ty i} ≠ 0 := fun i =>
    haveI : Nonempty {j // ty j = ty i} := ⟨⟨i, rfl⟩⟩
    Nat.card_pos.ne'
  have key : ∃ ρ : ℂ, (∀ i, ty i (H.rt : E) = ρ) ∧ 0 < ((ε : ℤ) : ℝ) * ρ.im := by
    rcases h with ⟨hq, hε⟩ | ⟨hp, hε⟩
    · refine ⟨H.rt0, fun i => ?_, hε⟩
      by_contra hne
      exact hcard i (((hty (ty i)).2 hne).trans hq)
    · refine ⟨-H.rt0, fun i => ?_, by simpa using hε⟩
      have hne : ty i (H.rt : E) ≠ H.rt0 := fun he => hcard i (((hty (ty i)).1 he).trans hp)
      have h2 : (H.rt : E) ^ 2 = -(H.d : E) := by
        have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
        simpa using this
      have h3 : ty i (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
        rw [← map_pow, h2, H.sqrt_neg_disc_sq]; simp
      exact (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left hne
  obtain ⟨ρ, hρ, hε⟩ := key
  obtain ⟨r, hr, hE⟩ := cmDatum_form_sqrtNegD_pure_period D hP hρ hx
  have : (0 : ℝ) < ((ε : ℤ) : ℝ) * ((D.EF (H.w0 • x) x : ℤ) : ℝ) := by
    rw [hE, ← _root_.mul_assoc]; exact mul_pos hε hr
  exact_mod_cast this

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem smoothOfRelativeDimension_of_fibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (β : R →+* K) (B : Over (Sp R)) [GrpObj B] (X' : Scheme.{0}) (π : X' ⟶ B.left) (p : X' ⟶ Sp K) (g : ℕ), IsAbelianScheme B → IsPullback π p B.hom (spMap β) → SmoothOfRelativeDimension g p → SmoothOfRelativeDimension g B.hom := by
  intro R K _ _ _ β B _ X' π p g hB hP hg
  have := hB.smooth
  have := hB.geomConnected
  have : ConnectedSpace (Sp R) := inferInstance
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace B.hom B.hom.isOpenMap
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected B.hom x
  have hn' : SmoothOfRelativeDimension n p :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback hP hn
  have hs : Surjective B.hom := inferInstance
  have : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hP hs
  obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary _)
  rw [← H1.dim_unique _ hn' hg y]
  exact hn

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_algClosure_lift {K k : Type} [Field K] [Field k] [IsAlgClosed k] (β : K →+* k) :
    ∃ j : AlgebraicClosure K →+* k, j.comp (algebraMap K (AlgebraicClosure K)) = β := by
  letI : Algebra K k := β.toAlgebra
  let f : AlgebraicClosure K →ₐ[K] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, RingHom.ext fun z => f.commutes z⟩

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}

def OnTors (e : ℕ → Q → Q → kˣ → Prop) (n : ℕ) (x y : Q) (c : kˣ) : Prop :=
  0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c

def tateIsoCongr {e e' : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    (h : ∀ n x y c, 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e' n x y c) : TateIso D k Q act e' :=
  { I with
    isom := fun n hn a b =>
      h n _ _ _ hn ((I.onto n hn _).2 ⟨a, rfl⟩) ((I.onto n hn _).2 ⟨b, rfl⟩) (I.isom n hn a b) }

theorem onTors_iff {Ω Q' : Type} [Field Ω] [Group Q'] (i : k →+* Ω) (r : Q →* Q') (hr : Function.Injective r)
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → Ωˣ → Prop}
    (h : ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 →
      (e n x y c ↔ e' n (r x) (r y) (Units.map i.toMonoidHom c))) (n : ℕ) (x y : Q) (c : kˣ) :
    OnTors e' n (r x) (r y) (Units.map i.toMonoidHom c) ↔ OnTors e n x y c := by
  unfold OnTors
  rw [← map_pow, ← map_pow, map_eq_one_iff r hr, map_eq_one_iff r hr]
  exact forall₃_congr fun hn hx hy => (h n x y c hn hx hy).symm

theorem onto_tors {Q' : Type} [Group Q'] (r : Q →* Q') (hr : Function.Injective r)
    (h : ∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) (n : ℕ) (hn : 0 < n) (z : Q') (hz : z ^ n = 1) :
    ∃ y : Q, y ^ n = 1 ∧ r y = z := by
  obtain ⟨x, rfl⟩ := h n z hn hz
  exact ⟨x, by rwa [← map_pow, map_eq_one_iff r hr] at hz, rfl⟩

end Abstract

theorem cmTorsionIsometry_transport_geometricPoint (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A))
    (hm : ∀ c, IsMonHom (act c))
    {F Ω k : Type} [Field F] [Field Ω] [Field k] [IsAlgClosed F] [IsAlgClosed Ω] [IsAlgClosed k] [CharZero F]
    (i : F →+* Ω) (j : F →+* k) (x : Sp F ⟶ S) (y : Sp Ω ⟶ S) (z : Sp k ⟶ S)
    (hy : spMap i ≫ x = y) (hz : spMap j ≫ x = z)
    (I : TateIso D Ω (Over.mk y ⟶ P.A) (fun c y => y ≫ act c)
      (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c))) :
    ∃ I' : TateIso D k (Over.mk z ⟶ P.A) (fun c y => y ≫ act c)
      (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)),
      (∀ (n : ℕ) (u : F), 0 < n → (I.ζ n : Ω) = i u → (I'.ζ n : k) = j u) ∧
      ∀ (n : ℕ) a (s : 𝟙_ (Over S) ⟶ P.A), 0 < n → toUnit _ ≫ s = I.ev n a → toUnit _ ≫ s = I'.ev n a := by
  subst hy hz
  have key : ∀ (k' : Type) [Field k'] (l : F →+* k') (r : (Over.mk x ⟶ P.A) →* (Over.mk (spMap l ≫ x) ⟶ P.A)),
      (∀ y, (r y).left = spMap l ≫ y.left) →
      (∀ c y, r (y ≫ act c) = r y ≫ act c) ∧ ∀ s : 𝟙_ (Over S) ⟶ P.A, r (toUnit _ ≫ s) = toUnit _ ≫ s := by
    intro k' _ l r hr
    have h : ∀ y, r y = (Over.homMk (spMap l) rfl : Over.mk (spMap l ≫ x) ⟶ Over.mk x) ≫ y :=
      fun y => Over.OverMorphism.ext (hr y)
    exact ⟨fun c y => by rw [h, h, Category.assoc], fun s => by rw [h, ← Category.assoc, comp_toUnit]⟩
  obtain ⟨r, hr, rinj, ronto, rw'⟩ := GlobalTheory.T.exists_torsion_injective_weil_compatible hL S P F Ω i x
  obtain ⟨q, hq, qinj, qonto, qw⟩ := GlobalTheory.T.exists_torsion_injective_weil_compatible hL S P F k j x
  obtain ⟨I₀, h₀⟩ := TateIsoFieldExt.down D i r (act := fun c y => y ≫ act c)
    (e := OnTors fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) rinj (onto_tors r rinj ronto)
    (key Ω i r hr).1 (fun c => by haveI := hm c; exact MonObj.one_comp (act c))
    (onTors_iff i r rinj rw') (tateIsoCongr I fun _ _ _ _ _ _ _ h _ _ _ => h)
  obtain ⟨I', h'⟩ := TateIsoFieldExt.up D j q (act' := fun c y => y ≫ act c)
    (e' := OnTors fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) qinj (onto_tors q qinj qonto)
    (key k j q hq).1 (onTors_iff j q qinj qw) I₀
  refine ⟨tateIsoCongr I' fun _ _ _ _ hn hx hy h => h hn hx hy, fun n u hn hu => ?_, fun n a s hn hs => ?_⟩
  · have h1 : i (I₀.ζ n) = i u := (h₀ n hn).1.symm.trans hu
    exact (h' n hn).1.trans (congrArg j (i.injective h1))
  · have h1 : toUnit _ ≫ s = I₀.ev n a :=
      rinj (((key Ω i r hr).2 s).trans (hs.trans ((h₀ n hn).2 a)))
    exact ((key k j q hq).2 s).symm.trans ((congrArg q h1).trans ((h' n hn).2 a).symm)

end GlobalTheory.CM
end
