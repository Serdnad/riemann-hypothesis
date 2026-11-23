module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.AdLat

open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

section
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def adCoord (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n) : (Fin n → RA F E) →+ RA F E where
  toFun w := ∑ i, w i * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b)
  map_zero' := by simp
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.adCoord_tmul (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n)
    (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    _root_.GlobalTheory.AdLat.adCoord F e b (fun i => a ⊗ₜ x i) = a ⊗ₜ e.repr x b := by
  have hx : e.repr x b = ∑ i, x i * e.repr (Pi.single i 1) b := by
    conv_lhs => rw [← Finset.univ_sum_single x]

    simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Pi.single i (x i) = x i • (Pi.single i 1 : Fin n → E) by
        ext j; by_cases h : j = i <;> simp [Pi.single_apply, h],
      map_smul, Finsupp.smul_apply, smul_eq_mul]
  change ∑ i, (a ⊗ₜ x i) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hx, TensorProduct.tmul_sum]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.adCoord_smul (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n)
    (r : _root_.GlobalTheory.AdLat.RA F E) (w : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.adCoord F e b (r • w) = r * _root_.GlobalTheory.AdLat.adCoord F e b w := by
  change ∑ i, (r • w) i * _ = r * ∑ i, w i * _
  simp [Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.adCoord_sum (e : Module.Basis (Fin n) E (Fin n → E))
    (z : Fin n → _root_.GlobalTheory.AdLat.RA F E) (b : Fin n) :
    _root_.GlobalTheory.AdLat.adCoord F e b (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) = z b := by
  have h1 : ∀ a, _root_.GlobalTheory.AdLat.adCoord F e b (_root_.GlobalTheory.AdLat.fv F (e a)) =
      if a = b then 1 else 0 := by
    intro a
    have := _root_.GlobalTheory.AdLat.adCoord_tmul F e b 1 (e a)
    unfold _root_.GlobalTheory.AdLat.fv
    rw [this, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp [Algebra.TensorProduct.one_def]

  simp only [map_sum, _root_.GlobalTheory.AdLat.adCoord_smul, h1, mul_ite, mul_one, mul_zero,
  Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
theorem _root_.GlobalTheory.AdLat.mem_hat_pseudoBasis_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (e : Module.Basis (Fin n) E (Fin n → E)) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E), (∀ v, v ∈ L ↔ ∀ a, e.repr v a ∈ cI a) → ∀ z : Fin n → _root_.GlobalTheory.AdLat.RA F E, (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) ↔ ∀ a, z a ∈ _root_.GlobalTheory.AdLat.hat1 F (cI a : Set E) := by
  intro F E _ _ _ _ _ n L e cI hL z
  constructor
  · intro hz b
    rw [← _root_.GlobalTheory.AdLat.adCoord_sum F e z b]
    have key : _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) ≤
        (_root_.GlobalTheory.AdLat.hat1 F (cI b : Set E)).comap (_root_.GlobalTheory.AdLat.adCoord F e b) := by
      unfold _root_.GlobalTheory.AdLat.hat
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, x, hx, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe]
      rw [_root_.GlobalTheory.AdLat.adCoord_tmul]
      unfold _root_.GlobalTheory.AdLat.hat1
      exact AddSubgroup.subset_closure ⟨c, hc, _, (hL x).1 hx b, rfl⟩
    exact key hz
  · intro hz
    refine AddSubgroup.sum_mem _ fun a _ => ?_
    have key : _root_.GlobalTheory.AdLat.hat1 F (cI a : Set E) ≤
        (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))).comap
          ((smulAddHom (_root_.GlobalTheory.AdLat.RA F E)
            (Fin n → _root_.GlobalTheory.AdLat.RA F E)).flip (_root_.GlobalTheory.AdLat.fv F (e a))) := by
      unfold _root_.GlobalTheory.AdLat.hat1
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, y, hy, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        AddMonoidHom.flip_apply, smulAddHom_apply]
      have hmem : y • e a ∈ L := by
        rw [hL]
        intro a'
        rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; simpa using hy
        · simpa using (cI a').zero_mem
      unfold _root_.GlobalTheory.AdLat.hat
      refine AddSubgroup.subset_closure ⟨c, hc, _, hmem, ?_⟩
      funext i
      unfold _root_.GlobalTheory.AdLat.fv
      change (c ⊗ₜ[F] y) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] e a i) = c ⊗ₜ[F] (y • e a) i
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Pi.smul_apply, smul_eq_mul]
    exact key (hz a)

end GlobalTheory.AdLat
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace OpenSubgroupScheme

variable {K : Type} [Field K] {Ga G : Over (Spec (CommRingCat.of K))}

lemma mem_range_iff_factors (p : Ga ⟶ G) [IsOpenImmersion p.left] (x : 𝟙_ _ ⟶ G) :
    x.left (IsLocalRing.closedPoint K) ∈ Set.range p.left ↔ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = x := by
  constructor
  · intro h
    have hr : Set.range x.left ⊆ Set.range p.left := by
      rintro _ ⟨z, rfl⟩
      have : z = IsLocalRing.closedPoint K :=
        Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _
      rw [this]; exact h
    refine ⟨Over.homMk (IsOpenImmersion.lift p.left x.left hr) ?_, ?_⟩
    · rw [← Over.w p, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w x
    · ext1
      simp
  · rintro ⟨a, rfl⟩
    exact ⟨a.left (IsLocalRing.closedPoint K), rfl⟩

lemma exists_point [IsAlgClosed K] [LocallyOfFiniteType G.hom] (y : G.left) (hy : IsClosed {y}) :
    ∃ x : 𝟙_ _ ⟶ G, x.left (IsLocalRing.closedPoint K) = y :=
  ⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy),
    pointOfClosedPoint_apply G.hom y hy _⟩

lemma comp_mulRight [GrpObj G] (x g : 𝟙_ _ ⟶ G) : x ≫ (GrpObj.mulRight g).hom = x * g := by
  rw [GrpObj.mulRight_hom, Hom.mul_def, comp_lift_assoc, Category.comp_id, ← Category.assoc,
    Subsingleton.elim (x ≫ toUnit G) (𝟙 _), Category.id_comp]

lemma mulRight_apply [GrpObj G] (x g : 𝟙_ _ ⟶ G) :
    (GrpObj.mulRight g).hom.left (x.left (IsLocalRing.closedPoint K)) =
      (x * g).left (IsLocalRing.closedPoint K) := by
  rw [← comp_mulRight]; rfl

lemma range_eq_univ [IsAlgClosed K] [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G) [IsMonHom p]
    [IsOpenImmersion p.left] [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] :
    Set.range p.left = Set.univ := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  set U : Set G.left := Set.range p.left with hU
  have hUo : IsOpen U := p.left.isOpenEmbedding.isOpen_range
  let V : Set G.left := ⋃ g : {g : 𝟙_ _ ⟶ G // ¬ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = g},
    (GrpObj.mulRight g.1).hom.left ⁻¹' U
  have hVo : IsOpen V := isOpen_iUnion fun g => hUo.preimage (Scheme.Hom.continuous _)
  have hdisj : U ∩ V = ∅ := by
    by_contra hne
    obtain ⟨y, ⟨hyU, hyV⟩, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.mpr hne)
      (hUo.inter hVo).isLocallyClosed
    obtain ⟨x, rfl⟩ := exists_point y hyc
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hyV
    rw [Set.mem_preimage, mulRight_apply] at hg
    obtain ⟨a, ha⟩ := (mem_range_iff_factors p x).mp hyU
    obtain ⟨b, hb⟩ := (mem_range_iff_factors p _).mp hg
    refine g.2 ⟨a⁻¹ * b, ?_⟩
    rw [MonObj.mul_comp, GrpObj.inv_comp, ha, hb, inv_mul_cancel_left]
  have hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint K) ∈ U :=
    (mem_range_iff_factors p _).mpr ⟨1, MonObj.one_comp p⟩
  have hcov : U ∪ V = Set.univ := by
    by_contra hne
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
      (hUo.union hVo).isClosed_compl.isLocallyClosed
    obtain ⟨x, rfl⟩ := exists_point y hyc
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hy
    refine hy.2 (Set.mem_iUnion.mpr ⟨⟨x⁻¹, ?_⟩, ?_⟩)
    · rintro ⟨a, ha⟩
      refine hy.1 ((mem_range_iff_factors p x).mpr ⟨a⁻¹, ?_⟩)
      rw [GrpObj.inv_comp, ha, inv_inv]
    · rw [Set.mem_preimage, mulRight_apply, mul_inv_cancel]
      exact hone
  have hc : Uᶜ = V := by
    ext y
    constructor
    · intro hy
      exact ((hcov ▸ Set.mem_univ y : y ∈ U ∪ V)).resolve_left hy
    · intro hy hyU
      exact (hdisj ▸ ⟨hyU, hy⟩ : y ∈ (∅ : Set G.left))
  have hcl : IsClopen U := ⟨isOpen_compl_iff.mp (hc ▸ hVo), hUo⟩
  exact hcl.eq_univ ⟨_, hone⟩

end OpenSubgroupScheme

theorem isIso_of_isOpenImmersion_of_geometricallyConnected :
    ∀ (S : Scheme.{0}) (Ga G : Over S) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      IsOpenImmersion p.left → LocallyOfFiniteType G.hom → GeometricallyConnected G.hom → IsIso p := by
  intro S Ga G _ _ p _ _ _ _
  have hsurj : Set.range p.left = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    let s : S := G.hom y
    let Ω : Type := AlgebraicClosure (S.residueField s)
    let t : Spec (CommRingCat.of Ω) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)) ≫ S.fromSpecResidueField s
    have ht : G.hom y = t (IsLocalRing.closedPoint Ω) :=
      (Scheme.fromSpecResidueField_apply s _).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ ht
    have : IsOpenImmersion ((Over.pullback t).map p).left :=
      MorphismProperty.overPullbackMap _ _ ‹_›
    have : LocallyOfFiniteType ((Over.pullback t).obj G).hom := by
      show LocallyOfFiniteType (pullback.snd G.hom t); infer_instance
    have : ConnectedSpace ((Over.pullback t).obj G).left :=
      GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)
    have h := OpenSubgroupScheme.range_eq_univ ((Over.pullback t).map p)
    obtain ⟨w, hw⟩ : z ∈ Set.range ((Over.pullback t).map p).left := h ▸ Set.mem_univ _
    refine ⟨pullback.fst Ga.hom t w, ?_⟩
    have e : ((Over.pullback t).map p).left ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left :=
      pullback.lift_fst _ _ _
    rw [← hz, ← hw, ← Scheme.Hom.comp_apply, ← e]
    rfl
  have : IsIso p.left := isIso_of_isOpenImmersion_of_opensRange_eq_top p.left (by
    ext1
    exact hsurj)
  have : IsIso ((Over.forget S).map p) := this
  exact isIso_of_reflects_iso p (Over.forget S)

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal

namespace GlobalTheory.PeterssonUnfold

theorem unfold_lintegral :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ H Kf : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ 0 → μ 𝓕 ≠ ⊤ → MeasurableSet (H : Set G) → Kf ≤ H → ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ k, Group (R k)] [∀ k, TopologicalSpace (R k)] [∀ k, IsTopologicalGroup (R k)] [∀ k, T2Space (R k)] [∀ k, LocallyCompactSpace (R k)] [∀ k, SecondCountableTopology (R k)] [∀ k, MeasurableSpace (R k)] [∀ k, BorelSpace (R k)] (ν : ∀ k, Measure (R k)) [∀ k, (ν k).IsHaarMeasure] (ψ : ∀ k, G →* R k) (Λ : ∀ k, Subgroup (R k)) (s : ∀ k, R k) (g : ι → G) (P : Type) (Q : P → P → Prop) (dict : G → P) (pt : ∀ k, R k → P), (∀ k, Measurable (ψ k)) → (∀ k t, ∃ h ∈ H, ψ k h = t) → (∀ k, ∀ z ∈ Kf, ψ k z = 1) → (∀ k, ∀ γ ∈ Γ, ψ k γ = 1 → γ = 1) → (∀ k k', ∃ (e : R k ≃ᵐ R k') (α : R k → R k) (u : R k), MeasurePreserving e (ν k) (ν k') ∧ Measurable α ∧ (∀ x, ψ k' x = e (α (ψ k x))) ∧ ∀ t, α (α t) = u⁻¹ * t * u) → (∀ k, ∃ W ∈ 𝓝 (1 : R k), ∀ w ∈ Λ k, w ∈ W → w = 1) → Equivalence Q → (∀ x x', Q (dict x) (dict x') ↔ ∃ γ ∈ Γ, ∃ z ∈ Kf, x' = γ * x * z) → (∀ k, ∀ h ∈ H, Q (dict (g k * h)) (pt k (s k * ψ k h))) → (∀ x, ∃ k t, Q (dict x) (pt k t)) → (∀ k k' t t', Q (pt k t) (pt k' t') → k = k') → (∀ k t t', Q (pt k t) (pt k t') ↔ ∃ w ∈ Λ k, t' = w * t) → ∃ (κ : ℝ≥0∞) (D : ∀ k, Set (R k)), κ ≠ 0 ∧ κ ≠ ⊤ ∧ (∀ k, Countable (Λ k) ∧ IsFundamentalDomain (Λ k) (D k) (ν k)) ∧ ∀ Φ : P → ℝ≥0∞, (∀ x q, Q (dict x) q → Φ q = Φ (dict x)) → (∀ k, Measurable fun t => Φ (pt k t)) → Measurable (fun x => Φ (dict x)) ∧ ∫⁻ x in 𝓕, Φ (dict x) ∂μ = κ * ∑ k, ∫⁻ t in D k, Φ (pt k t) ∂(ν k) := by
  classical
  intro G _ _ _ μ _ _ Γ H Kf _ 𝓕 h𝓕 h0 htop hH hKH ι _ R _ _ _ _ _ _ _ _ ν _ ψ Λ s g P Q dict pt
    hψ hsurj hK hΓ hcomp hdisc hQ hdict hpt hcov hsep hΛ
  have hD := fun k => GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete (R k) (Λ k) (hdisc k)
  have hcount : ∀ k, Countable (Λ k) := fun k => (hD k).1
  choose D hDm hDu using fun k => (hD k).2
  have hpt' : ∀ k y, (g k)⁻¹ * y ∈ H → Q (dict y) (pt k (s k * ψ k ((g k)⁻¹ * y))) := by
    intro k y hy
    have := hpt k _ hy
    rwa [mul_inv_cancel_left] at this
  have hΓQ : ∀ δ ∈ Γ, ∀ y, Q (dict y) (dict (δ * y)) := fun δ hδ y =>
    (hdict _ _).2 ⟨δ, hδ, 1, Kf.one_mem, by rw [mul_one]⟩
  have inj1 : ∀ k k' y, ∀ δ ∈ Γ, (g k)⁻¹ * y ∈ H → (g k')⁻¹ * (δ * y) ∈ H →
      Q (pt k (s k * ψ k ((g k)⁻¹ * y))) (pt k' (s k' * ψ k' ((g k')⁻¹ * (δ * y)))) :=
    fun k k' y δ hδ hy hy' =>
      hQ.trans (hQ.symm (hpt' k y hy)) (hQ.trans (hΓQ δ hδ y) (hpt' k' _ hy'))
  have inj2 : ∀ k y, ∀ δ ∈ Γ, (g k)⁻¹ * y ∈ H → (g k)⁻¹ * (δ * y) ∈ H →
      ∃ w ∈ Λ k, s k * ψ k ((g k)⁻¹ * (δ * y)) = w * (s k * ψ k ((g k)⁻¹ * y)) ∧
        (w = 1 → δ = 1) := by
    intro k y δ hδ hy hy'
    obtain ⟨w, hw, he⟩ := (hΛ k _ _).1 (inj1 k k y δ hδ hy hy')
    refine ⟨w, hw, he, fun h1 => hΓ k δ hδ ?_⟩
    rw [h1, one_mul, mul_right_inj, map_mul, map_mul, map_mul, mul_right_inj] at he
    exact mul_eq_right.1 he
  let E : ι → Set G := fun k => {y | (g k)⁻¹ * y ∈ H ∧ s k * ψ k ((g k)⁻¹ * y) ∈ D k}
  have hms : ∀ k, Measurable fun y : G => s k * ψ k ((g k)⁻¹ * y) := fun k =>
    ((hψ k).comp (measurable_const_mul _)).const_mul _
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (measurable_const_mul (g k)⁻¹ hH).inter (hms k (hDm k))
  have cover : ∀ x, ∃ γ ∈ Γ, ∃ k, γ * x ∈ E k := by
    intro x
    obtain ⟨k, t, hq⟩ := hcov x
    obtain ⟨w, hw, -⟩ := hDu k t
    obtain ⟨h, hh, he⟩ := hsurj k ((s k)⁻¹ * (w * t))
    have h1 : Q (pt k t) (pt k (s k * ψ k h)) :=
      (hΛ k _ _).2 ⟨w, w.2, by rw [he, mul_inv_cancel_left]⟩
    obtain ⟨γ, hγ, z, hz, hx⟩ := (hdict x (g k * h)).1
      (hQ.trans hq (hQ.trans h1 (hQ.symm (hpt k h hh))))
    have h2 : (g k)⁻¹ * (γ * x) = h * z⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_inv_cancel_right]
    refine ⟨γ, hγ, k, ?_, ?_⟩
    · rw [h2]; exact H.mul_mem hh (H.inv_mem (hKH hz))
    · rw [h2, map_mul, map_inv, hK k z hz, inv_one, mul_one, he, mul_inv_cancel_left]
      exact hw
  have uniq : ∀ k k' y, ∀ δ ∈ Γ, y ∈ E k → δ * y ∈ E k' → k = k' ∧ δ = 1 := by
    intro k k' y δ hδ hy hy'
    obtain rfl : k = k' := hsep _ _ _ _ (inj1 k k' y δ hδ hy.1 hy'.1)
    refine ⟨rfl, ?_⟩
    obtain ⟨w, hw, he, h1⟩ := inj2 k y δ hδ hy.1 hy'.1
    refine h1 ?_
    have := (hDu k (s k * ψ k ((g k)⁻¹ * y))).unique (y₁ := ⟨w, hw⟩) (y₂ := 1)
      (by have := hy'.2; rwa [he] at this) (by simpa using hy.2)
    exact congrArg Subtype.val this
  have hE : IsFundamentalDomain Γ (⋃ k, E k) μ := by
    refine IsFundamentalDomain.mk' (MeasurableSet.iUnion hEm).nullMeasurableSet fun x => ?_
    obtain ⟨γ, hγ, k, hx⟩ := cover x
    refine ⟨⟨γ, hγ⟩, Set.mem_iUnion.2 ⟨k, hx⟩, fun γ' hγ' => ?_⟩
    obtain ⟨k', hx'⟩ := Set.mem_iUnion.1 hγ'
    have := (uniq k k' (γ * x) (γ' * γ⁻¹) (Γ.mul_mem γ'.2 (Γ.inv_mem hγ)) hx
      (by rw [mul_assoc, inv_mul_cancel_left]; exact hx')).2
    exact Subtype.ext (mul_inv_eq_one.1 this)
  have hH0 : μ H ≠ 0 := by
    intro hH0
    apply h0
    rw [h𝓕.measure_eq hE]
    refine measure_iUnion_null fun k => measure_mono_null (t := (fun y => (g k)⁻¹ * y) ⁻¹' H)
      (fun y hy => hy.1) ?_
    rw [measure_preimage_mul, hH0]
  have hloc : ∀ k t, ∃ W ∈ 𝓝 t, μ ((H : Set G) ∩ ψ k ⁻¹' W) ≠ ⊤ := by
    intro k t
    obtain ⟨U, hU, hΛU⟩ := hdisc k
    obtain ⟨V₀, hV₀, hVU⟩ := exists_nhds_split_inv hU
    obtain ⟨V, hVV, hVo, hV1⟩ := mem_nhds_iff.1 hV₀
    have ho : IsOpen {u : R k | s k * u * (s k * t)⁻¹ ∈ V} := hVo.preimage (by fun_prop)
    refine ⟨_, ho.mem_nhds (by simpa using hV1), fun hinf => ?_⟩
    rw [← measure_preimage_mul μ (g k)⁻¹] at hinf
    obtain ⟨x, hx, y, hy, δ, hδ, hxy⟩ := h𝓕.exists_ne_one_smul_eq
      (measurable_const_mul (g k)⁻¹ (hH.inter (hψ k ho.measurableSet))).nullMeasurableSet
      (by rw [hinf]; exact lt_top_iff_ne_top.2 htop)
    subst hxy
    obtain ⟨w, hw, he, h1⟩ := inj2 k x δ δ.2 hx.1 hy.1
    refine hδ (Subtype.ext (h1 (hΛU w hw ?_)))
    have h2 : s k * ψ k ((g k)⁻¹ * (δ * x)) * (s k * t)⁻¹ ∈ V := hy.2
    have h3 : s k * ψ k ((g k)⁻¹ * x) * (s k * t)⁻¹ ∈ V := hx.2
    rw [he, mul_assoc] at h2
    have := hVU _ (hVV h2) _ (hVV h3)
    rwa [mul_div_cancel_right] at this
  obtain ⟨κ, hκ0, hκt, hκ⟩ := GlobalTheory.map_restrict_subgroup_eq_common_smul_haar G μ H hH hH0 ι R ν ψ hψ hsurj hloc hcomp
  refine ⟨κ, D, hκ0, hκt, fun k => ⟨hcount k,
    IsFundamentalDomain.mk' (hDm k).nullMeasurableSet (hDu k)⟩, fun Φ hΦ hΦm => ?_⟩
  have hinv : ∀ δ ∈ Γ, ∀ y, Φ (dict (δ * y)) = Φ (dict y) := fun δ hδ y => hΦ _ _ (hΓQ δ hδ y)
  have hval : ∀ k y, (g k)⁻¹ * y ∈ H → Φ (dict y) = Φ (pt k (s k * ψ k ((g k)⁻¹ * y))) :=
    fun k y hy => (hΦ _ _ (hpt' k y hy)).symm
  refine ⟨fun B hB => ?_, ?_⟩
  · have : (fun x => Φ (dict x)) ⁻¹' B = ⋃ γ : Γ, ⋃ k, (fun x => (γ : G) * x) ⁻¹'
        (((fun y => (g k)⁻¹ * y) ⁻¹' H) ∩
          (fun y => Φ (pt k (s k * ψ k ((g k)⁻¹ * y)))) ⁻¹' B) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hx
        obtain ⟨γ, hγ, k, hk⟩ := cover x
        refine ⟨⟨γ, hγ⟩, k, hk.1, ?_⟩
        rw [← hval k _ hk.1, hinv γ hγ]; exact hx
      · rintro ⟨γ, k, hk, hx⟩
        rwa [← hval k _ hk, hinv γ γ.2] at hx
    rw [this]
    exact MeasurableSet.iUnion fun γ => MeasurableSet.iUnion fun k => measurable_const_mul _
      ((measurable_const_mul _ hH).inter (((hΦm k).comp (hms k)) hB))
  · rw [h𝓕.setLIntegral_eq hE _ fun γ x => hinv γ γ.2 x,
      lintegral_iUnion hEm (fun k k' hk => Set.disjoint_left.2 fun y hy hy' =>
        hk (uniq k k' y 1 Γ.one_mem hy (by rwa [one_mul])).1), tsum_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    let F : R k → ℝ≥0∞ := (D k).indicator fun t => Φ (pt k t)
    have hF : Measurable F := (hΦm k).indicator (hDm k)
    calc ∫⁻ x in E k, Φ (dict x) ∂μ
        = ∫⁻ x, (H : Set G).indicator (fun h => F (s k * ψ k h)) ((g k)⁻¹ * x) ∂μ := by
          rw [← lintegral_indicator (hEm k)]
          refine lintegral_congr fun x => ?_
          by_cases hx : (g k)⁻¹ * x ∈ H
          · rw [Set.indicator_of_mem (s := (H : Set G)) hx]
            by_cases hx' : s k * ψ k ((g k)⁻¹ * x) ∈ D k
            · rw [Set.indicator_of_mem (show x ∈ E k from ⟨hx, hx'⟩), hval k x hx]
              exact (Set.indicator_of_mem hx' fun t => Φ (pt k t)).symm
            · rw [Set.indicator_of_notMem (fun h : x ∈ E k => hx' h.2)]
              exact (Set.indicator_of_notMem hx' fun t => Φ (pt k t)).symm
          · rw [Set.indicator_of_notMem (fun h : x ∈ E k => hx h.1),
              Set.indicator_of_notMem (s := (H : Set G)) hx]
      _ = ∫⁻ h in (H : Set G), F (s k * ψ k h) ∂μ := by
          rw [lintegral_mul_left_eq_self
            ((H : Set G).indicator (fun h => F (s k * ψ k h))) (g k)⁻¹, lintegral_indicator hH]
      _ = ∫⁻ t, F (s k * t) ∂((μ.restrict H).map (ψ k)) :=
          (lintegral_map (f := fun t => F (s k * t)) (hF.comp (measurable_const_mul _)) (hψ k)).symm
      _ = κ * ∫⁻ t in D k, Φ (pt k t) ∂(ν k) := by
          rw [hκ, lintegral_smul_measure, lintegral_mul_left_eq_self F, lintegral_indicator (hDm k),
            smul_eq_mul]

end GlobalTheory.PeterssonUnfold
end
