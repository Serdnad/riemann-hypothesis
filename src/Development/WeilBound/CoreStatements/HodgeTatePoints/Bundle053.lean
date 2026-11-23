module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
import Development.WeilBound.CoreStatements.HodgeTatePoints.ActGeneratorZero
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle042
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle052
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle040
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle045
import Mathlib.Algebra.CharP.Subring
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle283
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle230
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle231
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle167
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle227
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle236

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cf

theorem fib_inj_of (htan : type_of% @GlobalTheory.T.geometric_to_tangent_power_free) (hbc : type_of% @GlobalTheory.T.formal_germ_base_change)
    (hinj : type_of% @GlobalTheory.T.tangent_power_free_conj_injective) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p := by
  intro E _ _ _ H _ hs X0 t hP k _ p _ _ x d g ⟨k', _, _, x', hx, h⟩
  obtain ⟨Ω, _, _, y, a, -, e⟩ := exists_common x (IsLocalRing.closedPoint k) x' hx
  obtain ⟨b, rfl⟩ : ∃ b : k →+* Ω, y = spMap b := ⟨(Spec.preimage y).hom, (Spec.map_preimage y).symm⟩
  have : CharP Ω p := charP_of_injective_ringHom b.injective p
  have h' : GeomPF t (spMap b ≫ x) := e ▸ (geompf_bc E H X0 t).1 k' Ω a x' h
  obtain ⟨g₂, hg, -⟩ := hbc E H hs X0 t k Ω b x d g
  exact (PositivityTheory.HtPt.Cc.conjInj_map hg p).1 (hinj E H hs X0 t Ω p _ d g₂ (htan E H hs X0 t hP Ω p _ h'))

theorem isMapOf_cancel {R R₂ R₃ O : Type} [CommRing R] [CommRing R₂] [CommRing R₃] [CommRing O] [StarRing O] {d : ℕ}
    {f : R →+* R₂} {g : R₂ →+* R₃} {B : Germ.FB R d O} {B₂ : Germ.FB R₂ d O} {B₃ : Germ.FB R₃ d O}
    (h : IsMapOf f B B₂) (h' : IsMapOf (g.comp f) B B₃) : IsMapOf g B₂ B₃ := by
  exact
    { F := fun i => by simp only [h'.F i, h.F i, MvPowerSeries.map_comp, RingHom.comp_apply]
      act := fun a i => by simp only [h'.act a i, h.act a i, MvPowerSeries.map_comp, RingHom.comp_apply]
      ph1 := by simp only [h'.ph1, h.ph1, MvPowerSeries.map_comp, RingHom.comp_apply]
      ph2 := by simp only [h'.ph2, h.ph2, MvPowerSeries.map_comp, RingHom.comp_apply]
      sy := by simp only [h'.sy, h.sy, MvPowerSeries.map_comp, RingHom.comp_apply]
      ad := fun a => by simp only [h'.ad a, h.ad a, MvPowerSeries.map_comp, RingHom.comp_apply] }

theorem spMap_comp' {R R₂ R₃ : Type} [CommRing R] [CommRing R₂] [CommRing R₃] (f : R →+* R₂) (g : R₂ →+* R₃) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem dualMap_comp' {R R₂ R₃ : Type} [CommRing R] [CommRing R₂] [CommRing R₃] (f : R →+* R₂) (g : R₂ →+* R₃) :
    (GlobalTheory.CompanionTheory.Ar.dualMap g).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) = GlobalTheory.CompanionTheory.Ar.dualMap (g.comp f) := by
  ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem exists_factor {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] {X : Scheme.{0}} (x : Sp R ⟶ X)
    (j : Sp A ⟶ X) [IsOpenImmersion j] (h : GlobalTheory.CompanionTheory.Ar.centre x ∈ Set.range j) : ∃ a : A →+* R, x = spMap a ≫ j := by
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint q).map x.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j x hr)).hom, ?_⟩
  show x = Spec.map (Spec.preimage (IsOpenImmersion.lift j x hr)) ≫ j
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem finite_nonint {K : Type} [Field K] (C : ACurve K) (x : K) : {i | ¬ C.v i x ≤ 1}.Finite := by
  by_cases h : x = 0
  · simp [h]
  · exact (C.fin x h).subset fun i hi e => hi e.le

theorem family_ex_of' (hfib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p)
    (hbc : type_of% @GlobalTheory.T.formal_germ_base_change) (huniv : type_of% @GlobalTheory.T.formal_germ_dimension_unique) (hiso : type_of% @GlobalTheory.T.formal_germs_isomorphic)
    (haff : type_of% @GlobalTheory.T.exists_formal_germ_open_affine) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
  intro E _ _ _ H _ hs X0 t hP K _ p _ _ C z Y hY
  have bc : ∀ {S S₂ : Type} [CommRing S] [CommRing S₂] (f : S →+* S₂) {x : Sp S ⟶ X0} {x₂ : Sp S₂ ⟶ X0}
      (_ : x₂ = spMap f ≫ x) {d : ℕ} (g : GermAt t x d), ∃ g₂ : GermAt t x₂ d, IsMapOf f g.B g₂.B ∧
        ∀ l, g₂.tg l = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l := by
    intro S S₂ _ _ f x x₂ e d g
    subst e
    exact hbc E H hs X0 t S S₂ f x d g
  obtain ⟨A, _, j, d, _, hj, ⟨gA⟩⟩ := haff E H hs X0 t hP (GlobalTheory.CompanionTheory.Ar.centre z)
  obtain ⟨a, ha⟩ := exists_factor z j hj
  obtain ⟨g, hg, hgt⟩ := bc a ha gA
  obtain ⟨φ₀, ψ₀, lam₀, h₀, h₀t⟩ := hiso E H hs X0 t hP K z d g g
  have loc : ∀ i : C.I, ∃ (gi : GermAt t (Y.x i) d) (BK : Germ.FB K d (𝓞 E)) (φ ψ : Germ.Pt K 1 d)
      (lam : Germ.PS K 2 d), IsMapOf (C.v i).valuationSubring.subtype gi.B BK ∧ GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B BK φ ψ lam ∧
      (GlobalTheory.CompanionTheory.Ar.centre (Y.x i) ∈ Set.range j → φ = φ₀ ∧ ψ = ψ₀ ∧ lam = lam₀) ∧
      ∀ l, IsCombAtG t z g.tg (fun j => lin φ 1 j l)
        (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
    intro i
    by_cases hi : GlobalTheory.CompanionTheory.Ar.centre (Y.x i) ∈ Set.range j
    · obtain ⟨b, hb⟩ := exists_factor (Y.x i) j hi
      obtain ⟨gi, hgi, hgit⟩ := bc b hb gA
      have e : spMap ((C.v i).valuationSubring.subtype.comp b) = spMap a := by
        rw [← cancel_mono j, ← ha, ← spMap_comp', Category.assoc, ← hb]
        exact Y.gen i
      obtain rfl : (C.v i).valuationSubring.subtype.comp b = a :=
        congrArg CommRingCat.Hom.hom (Spec.map_injective e)
      refine ⟨gi, g.B, φ₀, ψ₀, lam₀, isMapOf_cancel hgi hg, h₀, fun _ => ⟨rfl, rfl, rfl⟩, fun l => ?_⟩
      rw [hgit, ← Category.assoc, spMap_comp', dualMap_comp', ← hgt]
      exact h₀t l
    · obtain ⟨d', ⟨gi⟩⟩ := PositivityTheory.HtPt.Cd.germ_local E H hs X0 t hP _ (Y.x i)
      obtain ⟨g₂, hg₂, hg₂t⟩ := bc (C.v i).valuationSubring.subtype (Y.gen i).symm gi
      obtain rfl := (huniv E H hs X0 t K z d g).1 d' g₂
      obtain ⟨φ, ψ, lam, h, ht⟩ := hiso E H hs X0 t hP K z d g g₂
      exact ⟨gi, g₂.B, φ, ψ, lam, hg₂, h, fun h' => absurd h' hi, fun l => hg₂t l ▸ ht l⟩
  choose gi BK φ ψ lam hK hI hgood ht using loc
  have red : ∀ i : C.I, ∃ Bk : Germ.FB (IsLocalRing.ResidueField (C.v i).valuationSubring) d (𝓞 E),
      IsMapOf (IsLocalRing.residue _) (gi i).B Bk ∧ ConjInj Bk p := by
    intro i
    obtain ⟨gk, hk, -⟩ := bc (IsLocalRing.residue _) rfl (gi i)
    have h0 : (p : (C.v i).valuationSubring) = 0 := Subtype.ext (by simp)
    have : CharP (IsLocalRing.ResidueField (C.v i).valuationSubring) p :=
      (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
        rw [← map_natCast (IsLocalRing.residue (C.v i).valuationSubring), h0, map_zero])
    refine ⟨gk.B, hk, hfib E H hs X0 t hP _ p _ d gk ?_⟩
    have e : (spMap (IsLocalRing.residue (C.v i).valuationSubring) ≫ Y.x i) (IsLocalRing.closedPoint _) =
        GlobalTheory.CompanionTheory.Ar.centre (Y.x i) :=
      (Scheme.Hom.comp_apply _ _ _).trans (congrArg (Y.x i) (IsLocalRing.comap_closedPoint (IsLocalRing.residue _)))
    exact e ▸ hY i
  choose Bk hk hinj using red
  refine ⟨d, ⟨g.B, fun i => (gi i).B, BK, Bk, hK, hk, hinj, φ, ψ, lam, hI, ?_⟩, g, rfl, fun i => ⟨gi i, ht i⟩⟩
  refine ((Y.ae j.opensRange hj).union (Set.finite_iUnion fun a : Fin d => Set.finite_iUnion fun b : Fin d =>
    (finite_nonint C (lin φ₀ 1 a b)).union ((finite_nonint C (lin ψ₀ 1 a b)).union
      (finite_nonint C (bil lam₀ 1 1 a b))))).subset fun i hi => ?_
  by_cases hc : GlobalTheory.CompanionTheory.Ar.centre (Y.x i) ∈ Set.range j
  · obtain ⟨e₁, e₂, e₃⟩ := hgood i hc
    rw [Set.mem_ofPred_eq, e₁, e₂, e₃] at hi
    simp only [not_forall, not_and_or] at hi
    obtain ⟨a, b, h⟩ := hi
    exact Or.inr (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨b, h⟩⟩)
  · exact Or.inl hc

theorem family_ex_of (htan : type_of% @GlobalTheory.T.geometric_to_tangent_power_free)
    (hbc : type_of% @GlobalTheory.T.formal_germ_base_change) (hinj : type_of% @GlobalTheory.T.tangent_power_free_conj_injective)
    (haff : type_of% @GlobalTheory.T.exists_formal_germ_open_affine) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) :=
  family_ex_of' (fib_inj_of htan hbc hinj) hbc PositivityTheory.HtPt.Cd.germ_univ PositivityTheory.HtPt.Cd.germ_iso haff

end PositivityTheory.HtPt.Cf
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tors ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Mi

section Cat
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]


omit [BraidedCategory C] in
theorem isMonHom_of_mul {A B : C} [GrpObj A] [GrpObj B] (j : A ⟶ B)
    (h : ∀ (Y : C) (y z : Y ⟶ A), (y * z) ≫ j = (y ≫ j) * (z ≫ j)) : IsMonHom j := by
  constructor
  · have h1 := h (𝟙_ C) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ C ⟶ A) ≫ j = 1 := by
      have := h1
      exact (left_eq_mul.1 this)
    simpa [Hom.one_def] using h2
  · have h1 := h (A ⊗ A) (fst A A) (snd A A)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h1
    rw [h1]
    congr 1
    ext <;> simp

theorem isPullback_of_kernel {A B : C} [GrpObj B] [IsCommMonObj B] {N : ℕ} (j : A ⟶ B)
    (inj : ∀ (Y : C) (y z : Y ⟶ A), y ≫ j = z ≫ j → y = z)
    (ker : ∀ (Y : C) (g : Y ⟶ B), g ^ N = 1 ↔ ∃ y : Y ⟶ A, y ≫ j = g) :
    IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] := by
  have hw : j ≫ (𝟙 B) ^ N = toUnit A ≫ η[B] := by
    rw [comp_pow_id, (ker A j).2 ⟨𝟙 _, Category.id_comp _⟩, Hom.one_def]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => ((ker _ s.fst).1 ?_).choose) (fun s => ?_) (fun s => ?_)
    (fun s m h1 _ => ?_)⟩⟩
  · rw [← comp_pow_id s.fst, Hom.one_def, ← toUnit_unique s.snd (toUnit _)]
    exact s.condition
  · exact Exists.choose_spec (p := fun y => y ≫ j = s.fst) _
  · exact toUnit_unique _ _
  · apply inj
    rw [h1]
    exact (Exists.choose_spec (p := fun y => y ≫ j = s.fst) _).symm

omit [BraidedCategory C] in
theorem pow_comp {Y A B : C} [GrpObj A] [GrpObj B] (g : Y ⟶ A) (a : A ⟶ B) [IsMonHom a] (n : ℕ) :
    (g ^ n) ≫ a = (g ≫ a) ^ n := by
  induction n with
  | zero => simp [MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

end Cat

section Tors
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
  {G : Over S} [GrpObj G] [IsCommMonObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

theorem kernel_of_tors (h : Γ.IsTorsionAlong G x N i) :
    ∃ j : Γ.G ⟶ (Over.pullback x).obj G, j.left ≫ pullback.fst G.hom x = i ∧
      IsPullback j (toUnit Γ.G) ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G] := by
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hj : (toPull x G g).left ≫ pullback.fst G.hom x = i := toPull_fst x G g
  refine ⟨toPull x G g, hj, isPullback_of_kernel _ (fun Y y z e => h.inj Y y z ?_) (fun Y c => ?_)⟩
  · rw [← hj, ← Category.assoc, ← Category.assoc, ← Over.comp_left, e, Over.comp_left]
  · have h1 : c ^ N = 1 ↔ ofPull x G c ^ N = 1 := by
      have h2 := map_pow (toPullHom x G Y) (ofPull x G c) N
      have h3 : toPullHom x G Y (ofPull x G c) = c := toPull_ofPull x G c
      rw [h3] at h2
      rw [← h2]
      constructor
      · intro e
        rw [← map_one (toPullHom x G Y)] at e
        exact toPull_inj e
      · intro e
        rw [e, map_one]
    rw [h1, h.kernel]
    refine exists_congr fun y => ⟨fun e => hom_ext_pull ?_, fun e => ?_⟩
    · rw [Over.comp_left, Category.assoc, hj, e]; rfl
    · rw [← hj, ← Category.assoc, ← Over.comp_left, e]; rfl

end Tors

theorem kernel_isPullback {Z : Scheme.{0}} {A B D : Over Z} [GrpObj D] {j : A ⟶ B} {q : B ⟶ D}
    (hp : IsPullback j (toUnit A) q η[D]) : IsPullback j.left A.hom q.left (η[D]).left := by
  have hl := hp.map (Over.forget Z)
  have hA : (toUnit A).left = A.hom := by simpa using Over.w (toUnit A)
  rw [← hA]; exact hl

theorem isClosedImmersion_unit {Z : Scheme.{0}} (B : Over Z) [GrpObj B] [IsSeparated B.hom] :
    IsClosedImmersion (η[B]).left := by
  have : IsClosedImmersion ((η[B]).left ≫ B.hom) := by
    have : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w η[B]
    rw [this]; infer_instance
  exact IsClosedImmersion.of_comp _ B.hom

theorem torsion_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsProper (pullback.snd G.hom x) → IsFinite Γ.G.hom := by
  intro R _ _ T _ _ Γ S G _ _ x N i h hprop
  obtain ⟨j, -, hp⟩ := kernel_of_tors h
  have : IsProper ((Over.pullback x).obj G).hom := hprop
  have hj : IsClosedImmersion j.left :=
    MorphismProperty.of_isPullback (kernel_isPullback hp).flip (isClosedImmersion_unit _)
  have : IsProper Γ.G.hom := by rw [← Over.w j]; infer_instance
  have := Γ.quasiFinite
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

theorem torsion_etale : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  intro R _ _ T _ _ Γ S G _ _ x N i h _ hN
  obtain ⟨j, -, hp⟩ := kernel_of_tors h
  have hN' : IsUnit (N : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have e1 : FormallyUnramified ((𝟙 ((Over.pullback x).obj G)) ^ N).left :=
    GlobalTheory.formallyUnramified_mulA _ ((Over.pullback x).obj G) N hN'
  have : FormallyUnramified Γ.G.hom := MorphismProperty.of_isPullback (kernel_isPullback hp) e1
  have := Γ.flat
  have := Γ.finPres
  exact Etale.of_formallyUnramified_of_flat _

theorem torsion_end : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (a : G ⟶ G) [IsMonHom a], ∃ a' : Γ.G ⟶ Γ.G, IsMonHom a' ∧ a'.left ≫ i = i ≫ a.left := by
  intro R _ _ T _ _ Γ S G _ _ x N i h a _
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, Category.id_comp _⟩
  have hga : (g ≫ a) ^ N = 1 := by rw [← pow_comp, hg, MonObj.one_comp]
  obtain ⟨a', ha'⟩ := (h.kernel Γ.G (g ≫ a)).1 hga
  replace ha' : a'.left ≫ i = i ≫ a.left := ha'
  refine ⟨a', isMonHom_of_mul _ fun Y y z => h.inj Y _ _ ?_, ha'⟩
  let p : (Y ⟶ Γ.G) → (Over.mk (Y.hom ≫ x) ⟶ G) := fun y => Over.homMk (y.left ≫ i) (by
    simp only [Over.mk_hom, Category.assoc, h.isOver]; rw [← Category.assoc, Over.w])
  have hp : ∀ y, (p y).left = y.left ≫ i := fun _ => rfl
  have hpa : ∀ y, (p y ≫ a).left = (y ≫ a').left ≫ i := fun y => by
    rw [Over.comp_left, Over.comp_left, hp, Category.assoc, Category.assoc, ha']
  rw [← h.mul Y _ _ _ _ (hpa y) (hpa z), ← MonObj.mul_comp, Over.comp_left, Over.comp_left,
    h.mul Y _ _ _ _ (hp y) (hp z), Category.assoc, Category.assoc, ha']

end PositivityTheory.HtPt.Mi
end
end

section

noncomputable section

namespace PositivityTheory.HtPt.Twexists

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tors ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem exists_torsion' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (T : Type) [CommGroup T] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ), 1 ≤ N → ∀ τ : T →* (Over.mk ((genPt R).hom ≫ x) ⟶ G), Function.Injective τ → (∀ t, τ t ^ N = 1) → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (a : FractionRing R →+* Ω) (g : Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x) ⟶ G), g ^ N = 1 → ∃ t, g.left = Spec.map (CommRingCat.ofHom a) ≫ (τ t).left) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (Γ.pt t).left ≫ i = (τ t).left := by
  intro R _ _ _ _ T _ S G _ hG x N hN τ hτ htor hsurj
  haveI : IsCommMonObj G := hG.comm
  have hBs : IsSemiAbelian ((Over.pullback x).obj G) :=
    { comm := by have := hG.comm; infer_instance
      smooth := by have := hG.smooth; show Smooth (pullback.snd G.hom x); infer_instance
      separated := by have := hG.separated; show IsSeparated (pullback.snd G.hom x); infer_instance
      quasiCompact := by have := hG.quasiCompact; show QuasiCompact (pullback.snd G.hom x); infer_instance
      geomConnected := by have := hG.geomConnected; show GeometricallyConnected (pullback.snd G.hom x); infer_instance
      fibres := fun Ω _ _ q => by
        obtain ⟨E⟩ := hG.fibres Ω (q ≫ x)
        let eM := (Functor.mapMonNatIso (Over.pullbackComp q x) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
        let e : (Over.pullback (q ≫ x)).obj G ≅ (Over.pullback q).obj ((Over.pullback x).obj G) :=
          (Mon.forget _).mapIso eM
        haveI : IsMonHom e.hom := by
          show IsMonHom eM.hom.hom
          infer_instance
        letI := E.grpB
        haveI := E.q_hom
        haveI := E.i_hom
        refine ⟨{
          X := E.X
          addCommGroup := E.addCommGroup
          free := E.free
          finite := E.finite
          B := E.B
          grpB := E.grpB
          isAbelian := E.isAbelian
          q := e.inv ≫ E.q
          q_hom := inferInstance
          q_flat := ?_
          q_surjective := ?_
          q_quasiCompact := ?_
          i := E.i ≫ e.hom
          i_hom := inferInstance
          isKernel := ?_ }⟩
        · rw [Over.comp_left]
          have := E.q_flat
          have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
          infer_instance
        · rw [Over.comp_left]
          have := E.q_surjective
          have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
          infer_instance
        · rw [Over.comp_left]
          have := E.q_quasiCompact
          have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
          infer_instance
        · refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }
  haveI : IsCommMonObj ((Over.pullback x).obj G) := hBs.comm
  haveI : Smooth ((Over.pullback x).obj G).hom := hBs.smooth
  haveI : IsSeparated ((Over.pullback x).obj G).hom := hBs.separated
  haveI : QuasiCompact ((Over.pullback x).obj G).hom := hBs.quasiCompact
  obtain ⟨hfl, hqf⟩ :=
    GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ _ hBs N (by omega)
  haveI := hfl
  haveI := hqf
  have hP : IsPullback (pullback.fst (𝟙 ((Over.pullback x).obj G) ^ N) η)
      (toUnit (pullback (𝟙 ((Over.pullback x).obj G) ^ N) η))
      (𝟙 ((Over.pullback x).obj G) ^ N) η := by
    convert IsPullback.of_hasPullback (𝟙 ((Over.pullback x).obj G) ^ N) η using 1
    exact toUnit_unique _ _
  obtain ⟨hA, hAc, hj⟩ := GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_kernel_grp hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.CompanionTheory.Ar.BT.Tors.kernel_props hP
  haveI := h1
  haveI := h5
  have het := GlobalTheory.CompanionTheory.Ar.BT.Tors.kernel_base_etale (genPt R).hom hP
    (GlobalTheory.CompanionTheory.Ar.BT.Tors.isUnit_natCast_generic (R := R) hN)
  haveI : AlgebraicGeometry.IsReduced (genPt R).left :=
    (inferInstance : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have hred : AlgebraicGeometry.IsReduced
      (pullback (pullback (𝟙 ((Over.pullback x).obj G) ^ N) η).hom (genPt R).hom) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced
      (pullback.snd (pullback (𝟙 ((Over.pullback x).obj G) ^ N) η).hom (genPt R).hom)
  exact GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_of_kernel hP h1 h2 h3 h4 h5 hred τ hτ htor hsurj

end PositivityTheory.HtPt.Twexists
end
end
