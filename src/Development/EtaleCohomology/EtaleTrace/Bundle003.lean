module

public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.EtaleTrace

def PtCover : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (T : Sieve (S k)), T ∈ Scheme.etaleTopology (S k) → T.arrows (𝟙 _)

def TwZero : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
  GlobalTheory.EtC.twGen (U := U) 0 ζ = GlobalTheory.EtC.twGen (U := U) 0 ξ

def EvNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X U : Scheme.{0}) (α : CochainComplex.HomComplex.Cochain ((chains R).obj (sch.obj X)) (res R F) 0)
  (x : U ⟶ X), ev (R := R) α 0 0 (by simp) U x = Sec.res x (ev (R := R) α 0 0 (by simp) X (𝟙 X))

def CocEq : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
  (α β : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) (res R F) 0),
  (∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U),
    ev (R := R) α.1 0 0 (by simp) U x = ev (R := R) β.1 0 0 (by simp) U x) → α = β

theorem exists_prim (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0) (j : ℕ) :
    Nonempty (Prim (l ^ j) Γ(S k, ⊤)) := by
  have hq : 0 < l ^ j := pow_pos (Fact.out : l.Prime).pos j
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ j) k)
    (Polynomial.degree_cyclotomic_pos (l ^ j) k hq).ne'
  have hu : IsUnit ((l ^ j : ℕ) : k) := by
    rw [Nat.cast_pow]; exact (isUnit_iff_ne_zero.2 hl).pow j
  have hr' : Polynomial.aeval r (Polynomial.cyclotomic (l ^ j) ℤ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hr
  exact ⟨Prim.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom ⟨r, hu, hr'⟩⟩

end LateralTheory.EtaleTrace
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.LPdCut

def Dp (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) : (PN k N).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)

def LChart : Prop := ∀ (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)),
  ∃ j : Spec (CommRingCat.of (MvPolynomial (Fin N) k)) ⟶ PN k N, IsOpenImmersion j ∧
    j ≫ PNto k N = Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin N) k)) ∧
    Set.range j = (Dp k N i : Set (PN k N))

def LProper : Prop := ∀ (k : Type) [Field k] (N : ℕ), IsProper (PNto k N)

def LSmooth : Prop := ∀ (k : Type) [Field k] (N : ℕ), SmoothOfRelativeDimension N (PNto k N)

def LEmpty : Prop := A5 → A9 → ∀ (R : Type) [CommRing R] (X : Scheme.{0}), IsEmpty X → ∀ (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj X) F n)

theorem unit_of {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) {q : ℕ} (h : IsUnit (q : k)) : IsUnit (q : Γ(X, ⊤)) := by
  simpa using (h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom

end LateralTheory.EtaleTrace.LPdCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def LCompInt : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p →
  ConnectedSpace X → IsIntegral X

theorem noeth_components {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α] :
    Finite (_root_.ConnectedComponents α) ∧ ∀ x : α, IsOpen (connectedComponent x) := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hSu⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_univ (X := α))
  have hin : ∀ x : α, ∃ t ∈ S, x ∈ t := fun x => by
    have : x ∈ ⋃₀ S := hSu ▸ Set.mem_univ x
    simpa using this
  have hsub : ∀ t ∈ S, ∀ z ∈ t, t ⊆ connectedComponent z := fun t ht z hz =>
    (IsIrreducible.isConnected (hSi t ht)).isPreconnected.subset_connectedComponent hz
  refine ⟨?_, fun x => ?_⟩
  · have : Finite S := hSf.to_subtype
    refine Finite.of_surjective (fun t : S => (((IsIrreducible.nonempty (hSi t.1 t.2)).some : α) : _root_.ConnectedComponents α)) ?_
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨t, ht, hxt⟩ := hin x
    refine ⟨⟨t, ht⟩, ConnectedComponents.coe_eq_coe.mpr ?_⟩
    exact connectedComponent_eq (hsub t ht _ (IsIrreducible.nonempty (hSi t ht)).some_mem hxt)
  · have hc : (connectedComponent x)ᶜ = ⋃₀ {t ∈ S | Disjoint t (connectedComponent x)} := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_setOf_eq]
      constructor
      · intro hz
        obtain ⟨t, ht, hzt⟩ := hin z
        refine ⟨t, ⟨ht, Set.disjoint_left.mpr fun w hwt hwx => hz ?_⟩, hzt⟩
        rw [connectedComponent_eq hwx]; exact hsub t ht w hwt hzt
      · rintro ⟨t, ⟨_, hd⟩, hzt⟩ hzx
        exact Set.disjoint_left.mp hd hzt hzx
    rw [← isClosed_compl_iff, hc]
    have hfin : ({t ∈ S | Disjoint t (connectedComponent x)}).Finite := hSf.subset (Set.sep_subset _ _)
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun t ht => hSc t ht.1

theorem comp_fin {k : Type} [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) :
    Finite (_root_.ConnectedComponents X) ∧ ∀ x : X, IsOpen (connectedComponent x) := by
  have := hp.1; have := hp.2
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := {}
  exact noeth_components

theorem clopen_smoothProper_projective {k : Type} [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hX : IsProj p)
    (U : X.Opens) (hU : IsClosed (U : Set X)) : SP d (U.ι ≫ p) ∧ IsProj (U.ι ≫ p) := by
  have : IsClosedImmersion U.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)
  have := hp.1
  have := hp.2
  have hs := smoothOfRelativeDimension_comp (n := 0) (m := d) U.ι p
  rw [Nat.zero_add] at hs
  refine ⟨⟨inferInstance, hs⟩, ?_⟩
  obtain ⟨N, ι, hι, hιp⟩ := hX
  exact ⟨N, U.ι ≫ ι, inferInstance, by rw [Category.assoc, hιp]⟩

end LateralTheory.EtaleTrace
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def kHom {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) : k →+* X.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom

def loc (X : Scheme.{0}) [IsIntegral X] (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

def jet (k : Type) [Field k] {K : Type} [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K) (j : Fin n) : K × Ω[K⁄k] :=
  (v j, KaehlerDifferential.D k K (v j))

def Gen {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ} (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    (genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) v f ≠ 0) ∧
    ∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n))
      (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen _ f),
      (show X.functionField from X.presheaf.germ _ (genericPoint X) h (ι.app _
        (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg)))) * eval₂ (kHom p) v f ^ m =
        eval₂ (kHom p) v g

structure Coord {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ} (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) : Prop where
  opens : ∀ (n : ℕ), 0 < n → ∀ f : MvPolynomial (Fin (N + 1)) k, f.IsHomogeneous n → ∀ x : X,
    (x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) v f ≠ 0 ∧
      ∀ g : MvPolynomial (Fin (N + 1)) k, g.IsHomogeneous n → eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ loc X x)
  range : ∀ z : X.functionField, z ∈ (ι.stalkMap (genericPoint X)).hom.range ↔
    ∃ (n : ℕ) (f g : MvPolynomial (Fin (N + 1)) k), f.IsHomogeneous n ∧ g.IsHomogeneous n ∧
      eval₂ (kHom p) v f ≠ 0 ∧ z = eval₂ (kHom p) v g / eval₂ (kHom p) v f

def PNBasic : Prop := ∀ (k : Type) [Field k] (d : ℕ),
  IsIntegral (PN k d) ∧ IsSeparated (PNto k d) ∧ LocallyOfFiniteType (PNto k d)

def GenIn : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N),
  ι ≫ PNto k N = p → ∃ (v : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), v i = 1 ∧ Gen p ι v

def GenOut : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField), (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, w j / w i ∈ loc X x) →
  ∃ π : X ⟶ PN k N, π ≫ PNto k N = p ∧ Gen p π w

def GenUse : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → Coord p ι v

def JetSpan : Prop := ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (n : ℕ) (v : Fin n → K) (i : Fin n), v i = 1 →
  (∀ z : K, ∃ f g : MvPolynomial (Fin n) k, z = aeval v g / aeval v f) →
  Submodule.span K (Set.range (jet k v)) = ⊤ ∧ Algebra.EssFiniteType k K

def TrdegLe : Prop := ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
  Algebra.trdeg k K ≤ (Module.finrank K Ω[K⁄k] : ℕ)

def HomRel : Prop := ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (d : ℕ), Algebra.trdeg k K ≤ (d : ℕ) →
  ∀ (n : ℕ), d + 1 < n → ∀ v : Fin n → K, ∃ (m : ℕ) (F : MvPolynomial (Fin n) k), F ≠ 0 ∧ F.IsHomogeneous m ∧ aeval v F = 0

def Step : Prop := ∀ (k K : Type) [Field k] [Infinite k] [Field K] [Algebra k K] (n : ℕ) (v : Fin (n + 1) → K)
  (m : ℕ) (F : MvPolynomial (Fin (n + 1)) k), F ≠ 0 → F.IsHomogeneous m → aeval v F = 0 → ¬ LinearIndependent K (jet k v) →
  ∃ w : Fin n → K, (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
    Submodule.span K (Set.range (jet k w)) = Submodule.span K (Set.range (jet k v)) ∧
    ∀ O : Subring K, IsLocalRing O → (∀ c : k, algebraMap k K c ∈ O) → (∃ i, v i ≠ 0 ∧ ∀ j, v j / v i ∈ O) →
      ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ O

def Project : Prop := ∀ (k K : Type) [Field k] [Infinite k] [Field K] [Algebra k K] (d : ℕ), Module.finrank K Ω[K⁄k] = d →
  Algebra.trdeg k K ≤ (d : ℕ) → ∀ (n : ℕ) (v : Fin n → K), Submodule.span K (Set.range (jet k v)) = ⊤ →
  ∃ w : Fin (d + 1) → K, (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
    Submodule.span K (Set.range (jet k w)) = ⊤ ∧ LinearIndependent K (jet k w) ∧
    ∀ O : Subring K, IsLocalRing O → (∀ c : k, algebraMap k K c ∈ O) → (∃ i, v i ≠ 0 ∧ ∀ j, v j / v i ∈ O) →
      ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ O

def JetIndep : Prop := ∀ (k K : Type) [Field k] [PerfectField k] [Field K] [Algebra k K] (n : ℕ) (w : Fin n → K),
  LinearIndependent K (jet k w) → ∀ (m : ℕ) (F : MvPolynomial (Fin n) k), F.IsHomogeneous m → aeval w F = 0 → F = 0

def JetUnram : Prop := ∀ (k K O : Type) [Field k] [Field K] [Algebra k K] [CommRing O] (φ : O →+* K) (n : ℕ) (w : Fin n → K)
  (i : Fin n), w i ≠ 0 → Submodule.span K (Set.range (jet k w)) = ⊤ → (∀ c : k, algebraMap k K c ∈ φ.range) →
  (∀ j, w j / w i ∈ φ.range) → φ.FormallyUnramified

def FieldDim : Prop := ∀ (k : Type) [Field k] (d : ℕ) {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  SmoothOfRelativeDimension d p → letI := (kHom p).toAlgebra; Module.finrank X.functionField Ω[X.functionField⁄k] = d

def FinSurj : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k), IsProper p →
  ∀ (N d : ℕ) (ι : X ⟶ PN k N) (π : X ⟶ PN k d) (v : Fin (N + 1) → X.functionField) (w : Fin (d + 1) → X.functionField),
  IsClosedImmersion ι → π ≫ PNto k d = p → Coord p ι v → Coord p π w →
  (∀ i, ∃ c : Fin (N + 1) → k, w i = ∑ j, kHom p (c j) * v j) →
  (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ loc X x) →
  (∀ (m : ℕ) (F : MvPolynomial (Fin (d + 1)) k), F.IsHomogeneous m → eval₂ (kHom p) w F = 0 → F = 0) →
  IsFinite π ∧ Surjective π

def Fibre : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (p : X ⟶ S k)
  (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified → ∃ t : Pt r, Etale (equalizer.ι π (p ≫ t.1) ≫ p)

theorem kHom_mem_loc {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (x : X) (c : k) :
    kHom p c ∈ loc X x := by
  refine ⟨X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)), ?_⟩
  exact X.presheaf.germ_stalkSpecializes_apply _ _ _

theorem loc_local (X : Scheme.{0}) [IsIntegral X] (x : X) : IsLocalRing (loc X x) :=
  IsLocalRing.of_surjective' (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    (RingHom.rangeRestrict_surjective _)

theorem goal_of (h1 : PNBasic) (h2 : GenIn) (h3 : GenOut) (h4 : GenUse) (h5 : JetSpan) (h6 : TrdegLe) (h7 : Project)
    (h8 : JetIndep) (h9 : JetUnram) (h10 : FieldDim) (h11 : FinSurj) (h12 : Fibre) : LCover := by
  intro k _ _ d X p hsp ⟨N, ι, hι, hιp⟩ hX
  let _ : Algebra k X.functionField := (kHom p).toAlgebra
  obtain ⟨v, i₀, hv1, hv⟩ := h2 k p N ι hιp
  have cv := h4 k p N ι v hv
  have hgen : ∀ z : X.functionField, ∃ f g : MvPolynomial (Fin (N + 1)) k, z = aeval v g / aeval v f := by
    intro z
    obtain ⟨n, f, g, -, -, -, h⟩ := (cv.range z).1 (ι.stalkMap_surjective (genericPoint X) z)
    exact ⟨f, g, h⟩
  obtain ⟨hspan, hess⟩ := h5 k X.functionField _ v i₀ hv1 hgen
  have hd := h10 k d p hsp.2
  have htr := h6 k X.functionField
  rw [hd] at htr
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := h7 k X.functionField d hd htr _ v hspan
  have hfree : ∀ x : X, ∃ i, v i ≠ 0 ∧ ∀ j, v j / v i ∈ loc X x := by
    intro x
    have htop : ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) = ⊤ := by
      apply Proj.iSup_basicOpen_eq_top' _ _ (fun i => ⟨1, isHomogeneous_X k i⟩)
      rw [eq_top_iff]
      rintro f -
      induction f using MvPolynomial.induction_on with
      | C a => exact Subalgebra.algebraMap_mem _ (⟨C a, isHomogeneous_C _ a⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add f g hf hg => exact add_mem hf hg
      | mul_X f i hf => exact mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
    have hx : ι x ∈ ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := by
      rw [htop]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨a, b⟩ := (cv.opens 1 one_pos _ (isHomogeneous_X k i) x).1 hi
    exact ⟨i, by simpa using a, fun j => by simpa using b _ (isHomogeneous_X k j)⟩
  have hwx : ∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ loc X x := fun x =>
    hw4 _ (loc_local X x) (kHom_mem_loc p x) (hfree x)
  have hc : ∀ i, ∃ c : Fin (N + 1) → k, w i = ∑ j, kHom p (c j) * v j := by
    intro i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 (hw1 i)
    exact ⟨c, by rw [← hc]; exact Finset.sum_congr rfl fun j _ => Algebra.smul_def _ _⟩
  have hww : ∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, w j / w i ∈ loc X x := by
    intro x
    obtain ⟨i, hi, h⟩ := hwx x
    refine ⟨i, hi, fun j => ?_⟩
    obtain ⟨c, hc⟩ := hc j
    rw [hc, Finset.sum_div]
    exact sum_mem fun l _ => by rw [mul_div_assoc]; exact mul_mem (kHom_mem_loc p x _) (h l)
  obtain ⟨π, hπ, hg⟩ := h3 k p d w hww
  have cw := h4 k p d π w hg
  obtain ⟨hfin, hsurj⟩ := h11 k p hsp.1 N d ι π v w hι hπ cv cw hc hwx (h8 k X.functionField _ w hw3)
  obtain ⟨hint, -, hft⟩ := h1 k d
  obtain ⟨i, hi, -⟩ := hwx (genericPoint X)
  have hun := h9 k X.functionField _ (π.stalkMap (genericPoint X)).hom _ w i hi hw2
    (fun c => (cw.range _).2 ⟨0, 1, C c, isHomogeneous_one _ _, isHomogeneous_C _ c, by simp, by simp; rfl⟩)
    (fun j => (cw.range _).2 ⟨1, MvPolynomial.X i, MvPolynomial.X j, isHomogeneous_X k i, isHomogeneous_X k j,
      by simpa using hi, by simp⟩)
  obtain ⟨t, ht⟩ := h12 k p (PNto k d) π hπ hft hfin hsurj hun
  exact ⟨π, t, hπ, hfin, hsurj, ht⟩

end LateralTheory.EtaleTrace.Cov

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

theorem lefschetz_of (hB : Base) (hT : LTransfer) (hC : LCycle) (hF : LFix) (hTr : LTr) (hP : LPushPt) (hA : LAlg) :
    Lefschetz := by
  intro l _ k _ _ hl d Y X q p hq hp hpr c a hc ha hfin het hE
  classical
  obtain ⟨δ, hδ⟩ := hC hB l k hl
  obtain ⟨tr, htr⟩ := hTr hB l k hl δ hδ d p hp hpr
  have hproj := (hT hB l k hl p hp.1 a hfin het).2.1
  have h1 := hA hB l k hl δ hδ d q p hp tr htr c a hc ha (tr ∘ₗ push l a _) (fun n => push l a n ∘ₗ pb l c n)
    (fun n m h u v => by simp only [LinearMap.comp_apply]; rw [hproj])
  have hfx := hF k q p hq.1 hp.1 c a hc ha hE
  have hs : Set.Finite {y : Pt q | y.1 ≫ c = y.1 ≫ a} := hfx
  have h2 := hδ.trans d q p hq hp c a hc ha hE hs.toFinset (fun y => by simp)

  rw [← h1, h2, map_sum]
  have h3 : ∀ y : Pt q, (tr ∘ₗ push l a _) (δ.cl d y) = 1 := fun y => by
    rw [LinearMap.comp_apply, hP hB l k hl δ hδ d q p hq hp a ha hfin het y, htr]
  simp only [h3, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  exact (Nat.card_eq_card_finite_toFinset hs).symm

theorem pb_comp (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) :
    pb l (f ≫ g) n = pb l f n ∘ₗ pb l g n := by
  unfold pb pullHQ
  rw [Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]

theorem gal_eq (l : ℕ) [Fact l.Prime] {κ : Type} [Field κ] (Ω : Type) [Field Ω] [Algebra κ Ω] {X : Scheme.{0}} (p : X ⟶ S κ)
    (n : ℤ) (σ : Ω ≃ₐ[κ] Ω) : galHQ l Ω p n 0 σ = pb l (GlobalTheory.Et.galMap Ω p σ) n := rfl

theorem pb_frob (l : ℕ) [Fact l.Prime] {κ : Type} [Field κ] (Ω : Type) [Field Ω] [Algebra κ Ω] {X W : Scheme.{0}} (p : X ⟶ S κ)
    (n : ℤ) (σ : Ω ≃ₐ[κ] Ω) (c b : W ⟶ GlobalTheory.Et.geom Ω p) (F : GlobalTheory.Et.geom Ω p ⟶ GlobalTheory.Et.geom Ω p)
    (h : c ≫ GlobalTheory.Et.galMap Ω p σ = b ≫ F) (hid : pb l F n = LinearMap.id) :
    pb l b n ∘ₗ galHQ l Ω p n 0 σ⁻¹ = pb l c n := by
  have h1 : pb l b n = pb l c n ∘ₗ pb l (GlobalTheory.Et.galMap Ω p σ) n :=
    calc pb l b n = pb l b n ∘ₗ pb l F n := by rw [hid, LinearMap.comp_id]
      _ = pb l (c ≫ GlobalTheory.Et.galMap Ω p σ) n := by rw [h]; exact (pb_comp l b F n).symm
      _ = _ := pb_comp l c _ n
  have h2 : pb l (GlobalTheory.Et.galMap Ω p σ) n ∘ₗ pb l (GlobalTheory.Et.galMap Ω p σ⁻¹) n = LinearMap.id := by
    refine (pb_comp l _ _ n).symm.trans ?_
    rw [← galMap_mul, mul_inv_cancel, galMap_one]
    unfold pb pullHQ
    rw [CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id]
  rw [gal_eq, h1, LinearMap.comp_assoc, h2, LinearMap.comp_id]

theorem frobTrace_of (hB : Base) (hL : Lefschetz) (hI : LFrobId) (hG : LFrobGeom) : FrobTrace := by
  intro l _ κ Ω _ _ _ _ _ hl d Y X q p hq hp hpr a b ha hb hfin het r hr σ hσ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed κ
  have hlΩ : (l : Ω) ≠ 0 := fun h => hl ((algebraMap κ Ω).injective (by rw [map_natCast, h, map_zero]))
  obtain ⟨hq', hp', hpr', ha', hfin', het', c, F, hc, hF, hcF, hE, hcard⟩ :=
    hG κ Ω d q p hq hp hpr a b ha hb hfin het r hr σ hσ _ _ rfl rfl
  have key := hL l Ω hlΩ d _ _ hq' hp' hpr' c _ hc ha' hfin' het' hE
  refine Eq.trans ?_ (key.trans (congrArg _ hcard))
  have := Fintype.ofFinite κ
  obtain ⟨p₀, hp₀⟩ := CharP.exists κ
  obtain ⟨s, hs, hcd⟩ := FiniteField.card κ p₀
  have : Fact p₀.Prime := ⟨hs⟩
  have : CharP Ω p₀ := charP_of_injective_algebraMap (algebraMap κ Ω).injective p₀
  rw [Nat.card_eq_fintype_card, hcd, ← pow_mul] at hF
  have hid := hI hB l Ω p₀ hlΩ (pullback.snd _ _) _ F hF
  exact congrArg (altTr l _ d) (funext fun n => congrArg (push l _ n ∘ₗ ·) (pb_frob l Ω p n σ c _ F hcF (hid n)))

theorem goal_of (hFin : LFin) (_ : LRing) (hT : LTransfer) (_ : LadicH0LocallyConstant) (_ : LKunneth) (hC : LCycle) (_ : LPd) (_ : LCover)
    (_ : LInj) (_ : LConst) (hF : LFix) (hTr : LTr) (hP : LPushPt) (hA : LAlg) (hI : LFrobId) (hG : LFrobGeom) : Goal :=
  fun hB => ⟨hFin hB, hT hB, lefschetz_of hB hT hC hF hTr hP hA,
    frobTrace_of hB (lefschetz_of hB hT hC hF hTr hP hA) hI hG⟩

end LateralTheory.EtaleTrace

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def EtaleTateTwistSectionsDeterminedByPointsOfProper : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ s : Sec (tw (l ^ j) 0) X,
    ((∀ y : Pt p, Sec.res y.1 s = 0) → s = 0) ∧
    (ConnectedSpace X → ∀ y y' : Pt p, Sec.res y.1 s = Sec.res y'.1 s)

end LateralTheory.EtaleTrace
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LFinCut

theorem normal_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) [Smooth p] : GlobalTheory.IsNormalScheme X := by
  rw [GlobalTheory.isNormalScheme_iff]
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p fun y => ?_
  have hf : IsField ((S k).presheaf.stalk y) := isField_stalk_of_closure_mem_irreducibleComponents (S k) y (by
    have : closure ({y} : Set (S k)) = Set.univ := Set.eq_univ_of_forall fun z => subset_closure (Subsingleton.elim z y)
    rw [this, irreducibleComponents_eq_singleton]; rfl)
  let := hf.toField
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleTrace.LFinCut

end
end
