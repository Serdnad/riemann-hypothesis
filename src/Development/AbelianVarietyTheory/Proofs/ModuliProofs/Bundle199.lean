module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle176
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle124
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEtaleLinearisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleHeckeKernelLists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle192
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle053

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem countable_addEquiv_of_free_finite (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] :
    Countable (La ≃+ La) := by
  let bas := Module.Free.chooseBasis ℤ La
  haveI : Countable La := bas.equivFun.injective.countable
  have hinj : Function.Injective (fun (gm : La ≃+ La) (i : Module.Free.ChooseBasisIndex ℤ La) => gm (bas i)) := by
    intro gm gm' h
    have h2 : gm.toAddMonoidHom.toIntLinearMap = gm'.toAddMonoidHom.toIntLinearMap :=
      bas.ext (fun i => congrFun h i)
    ext x
    exact LinearMap.congr_fun h2 x
  exact hinj.countable

theorem goodClass_of_lattice_families : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d r : ℕ) (La : Fin r → Type) [∀ i, AddCommGroup (La i)] (EF : ∀ i, LinearMap.BilinForm ℤ (La i)) (lam : ∀ i, Fin (2 * g) → La i) (ac : ∀ i, J → La i → La i) (B : Fin r → Set (Fin d → ℂ)) (Q : ∀ i, (Fin d → ℂ) → (La i →+ (Fin g → ℂ))) (Hm : Fin r → (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ t t', C t → TMap t' t (𝟙 _) → C t') → (∀ t, C t → t.Prim w w') → (∀ i, Function.Bijective (EF i) ∧ IsOpen (B i) ∧ IsPreconnected (B i) ∧ (∀ x, DifferentiableOn ℂ (fun bb => Q i bb x) (B i)) ∧ (∀ x, ac i w x + ac i w' x = x) ∧ (∀ x y, EF i (ac i w x) y = EF i x (ac i w' y)) ∧ (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF i (lam i i₁) (lam i i₂) : ℂ) / ((N' ^ 2 : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) ∧ (∀ j₁ i₁, ∃ y, ac i j₁ (lam i i₁) = ∑ i', Mat j₁ i' i₁ • lam i i' + (N' ^ 2) • y) ∧ (∀ bb ∈ B i, (Function.Injective (Q i bb) ∧ DiscreteTopology ((Q i bb)).range ∧ Submodule.span ℝ (Set.range (Q i bb)) = ⊤ ∧ ((Hm i bb)).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Hm i bb) z z).re) ∧ ∀ x y, (hermForm (Hm i bb) ((Q i bb) x) ((Q i bb) y)).im = EF i x y) ∧ ∀ j₁, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q i bb x) = Q i bb (ac i j₁ x)) ∧ ∀ y, y ≠ 0 → (hermForm (Hm i bb) (F y) (F y)).re < κ * (hermForm (Hm i bb) y y).re) ∧ (∀ bb ∈ B i, ∀ z' ∈ B i, (∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, Q i z' x = h (Q i bb x)) → bb = z') ∧ ∀ bb ∈ B i, ∀ t : TObj g (N' ^ 2) J b (spMap em), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm i bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q i bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q i bb) x → χ' l = (-1) ^ EF i x (ac i w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q i bb) (lam i i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q i bb) x) = (Q i bb) (ac i j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → C t) → (∀ t, C t → ∃ i, ∃ bb ∈ B i, (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm i bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q i bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q i bb) x → χ' l = (-1) ^ EF i x (ac i w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q i bb) (lam i i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q i bb) x) = (Q i bb) (ac i j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀)) → GoodClass em C Mat κ w w' d := by
  intro h1 h2 h3 h4 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hqt⟩ := GlobalTheory.T.thetaPoint_determines_shape_complex h1 h2 g J Mat κ n hn hodd
  refine ⟨max j₀ 1, ?_⟩
  intro j hj N' hN' o _ b em C d r La _ EF lam ac B Q Hm hiso hprim hfam hcov
  subst hN'
  have hj0 : j ≥ j₀ := le_trans (le_max_left _ _) hj
  have hj1 : j ≠ 0 := by have := le_trans (le_max_right _ _) hj; omega
  have hth := fun i => GlobalTheory.T.exists_holomorphic_thetaConstants_polarisedLattices h1 h2 h3 h4 o g (n ^ j) J b em w w' (La i) (EF i) (lam i) (ac i) d (B i) (Q i) (Hm i)
    hodd.pow (hfam i).1 (hfam i).2.1 (hfam i).2.2.2.1
    (fun bb hbb => ⟨((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).1,
      (((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2 w).imp fun F hF => hF.1⟩)
    (hfam i).2.2.2.2.1 (hfam i).2.2.2.2.2.1
  choose θ hθd hθ using hth
  have hsh := fun i bb (hbb : bb ∈ B i) t ht => GlobalTheory.T.shape_of_uniformised_theta_object h1 h2 h3 h4 o g ((n ^ j) ^ 2) J b em w w' t (La i) (EF i)
    (lam i) (ac i) (Q i bb) (Hm i bb) Mat κ ht (hfam i).2.2.2.2.2.2.2.1 ((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2
  have hbuild := fun i bb (hbb : bb ∈ B i) => GlobalTheory.T.exists_thetaObject_of_polarisedLattice h1 h2 h3 h4 o g ((n ^ j) ^ 2) J b em w w' (La i) (EF i)
    (lam i) (ac i) (Q i bb) (Hm i bb) (hfam i).1 ((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).1
    (fun j₁ => (((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2 j₁).imp fun F hF => hF.1)
    (hfam i).2.2.2.2.1 (hfam i).2.2.2.2.2.1 (hfam i).2.2.2.2.2.2.1
  refine ⟨hiso, fun t ht => ⟨?_, hprim t ht⟩, r, B, θ, fun i => ⟨(hfam i).2.1, (hfam i).2.2.1, hθd i, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · obtain ⟨i, bb, hbb, hu⟩ := hcov t ht
    exact hsh i bb hbb t hu
  · obtain ⟨t, htp, hu⟩ := hbuild i z hz
    exact ⟨t, (hfam i).2.2.2.2.2.2.2.2.2.2 z hz t hu htp, hθ i z hz t hu⟩
  · obtain ⟨hfree, hfin, -⟩ := unimodular_symplectic_coordinates_and_lattice_rank.2 (La i) (EF i) g (Q i z) (Hm i z)
      ((hfam i).2.2.2.2.2.2.2.2.1 z hz).1
    haveI := countable_addEquiv_of_free_finite (La i)
    have hc : (⋃ gm : La i ≃+ La i, {z' ∈ B i | ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
        ∀ x, h (Q i z' x) = Q i z (gm x)}).Countable := by
      refine Set.countable_iUnion fun gm => Set.Subsingleton.countable ?_
      rintro z₁ ⟨hz₁, k₁, hk₁⟩ z₂ ⟨hz₂, k₂, hk₂⟩
      refine (hfam i).2.2.2.2.2.2.2.2.2.1 z₁ hz₁ z₂ hz₂ ⟨k₁.trans k₂.symm, fun x => ?_⟩
      rw [LinearEquiv.trans_apply, hk₁, ← hk₂, LinearEquiv.symm_apply_apply]
    refine hc.mono ?_
    rintro z' ⟨hz', c, hcz⟩
    obtain ⟨t, -, hu⟩ := hbuild i z hz
    obtain ⟨t', -, hu'⟩ := hbuild i z' hz'
    have ht' := hθ i z' hz' t' hu'
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨a, ha⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh h1 h2 o g (n ^ j) J b _ _ t' n ℂ (𝟙 _) (θ i z') ⊥ hn.two_le
        (dvd_pow_self n hj1) ht' Ideal.isPrime_bot 0
      apply ha
      rw [hcz]
      simp
    rw [hcz] at ht'
    have hm := hqt j hj0 o b em t t' (θ i z) c hc0 (hsh i z hz t hu) (hsh i z' hz' t' hu') (hθ i z hz t hu) ht'
    obtain ⟨gm, h, hgm⟩ := GlobalTheory.T.exists_lattice_aut_of_isomorphic_theta_objects o g ((n ^ j) ^ 2) J b em w w' t t' (La i) (EF i) (lam i) (ac i) (Q i z) (Q i z')
      (Hm i z) (Hm i z') ((hfam i).2.2.2.2.2.2.2.2.1 z hz).1.1 ((hfam i).2.2.2.2.2.2.2.2.1 z' hz').1.1 hu hu' hm
    exact Set.mem_iUnion.2 ⟨gm, hz', h, hgm⟩
  · intro t ht
    obtain ⟨i, bb, hbb, hu⟩ := hcov t ht
    exact ⟨i, bb, hbb, hθ i bb hbb t hu⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkLoc

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsSeparated G.hom] {N n : ℕ}
    {σ : Fin n → (𝟙_ (Over S) ⟶ G)} {K : Set G.left} (h : Lists N σ K) {k : Type} [Field k] (x : Sp k ⟶ S)
    (z : Over.mk x ⟶ G) : Set.range z.left ⊆ K ↔ ∃ j, z = toUnit _ ≫ σ j := by
  obtain ⟨-, rfl, -⟩ := h
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  constructor
  · intro hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hz ⟨q, rfl⟩)
    have h1 := ListedSubgroup.eq_comp_section G.hom (σ j).left (Over.w (σ j)) _ q hj
    rw [Over.w z] at h1
    exact ⟨j, Over.OverMorphism.ext h1⟩
  · rintro ⟨j, rfl⟩ _ ⟨y, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, x y, (Scheme.Hom.comp_apply x (σ j).left y).symm⟩

theorem isUnit_natCast {F R : Type} [Field F] [CharZero F] [CommRing R] (s : Sp R ⟶ Sp F) (m : ℕ) (hm : 0 < m) :
    IsUnit (m : R) := by
  have h : IsUnit (m : F) := (Nat.cast_ne_zero.2 hm.ne').isUnit
  simpa using h.map (Spec.preimage s).hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

noncomputable abbrev pol {S : Scheme.{0}} {s : S ⟶ Sp (KA l)} (o : Ob D l s) : Out.PolAV S :=
  have h := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ S s o
  { A := o.t.G, isAb := h.1, g := Module.finrank ℚ E / 2 * (D.p + D.q), smoothDim := h.2.1, L := o.t.PP.L,
    isLB := o.t.PP.isLB, rigid := h.2.2.1, sym := h.2.2.2, ample := o.ample, ktriv := o.ktriv }

theorem weilIs_one {S : Scheme.{0}} [ConnectedSpace S] {s : S ⟶ Sp (KA l)} (o : Ob D l s) {𝔓 : Ideal (𝓞 E)}
    {p i n : ℕ} {σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)} {K : Set o.t.G.left} (hp : 0 < p)
    (hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤))) (hL : Lists (p ^ 2) σ K) (hH : HeckeSet D o.t 𝔓 p i K) (j j' : Fin n) :
    Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) (σ j) (σ j') 1 := by
  have := o.proper
  obtain ⟨U, hU, hW⟩ := GlobalTheory.exists_clopen_weilIs_iff GlobalTheory.firstFiveLaws.1 S (pol o) (p ^ 2) (𝟙_ (Over S)) (σ j) (σ j') 1
    (pow_pos hp 2) hu (hL.1 j) (hL.1 j') (one_pow _)
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  let k : Type := AlgebraicClosure (S.residueField s₀)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s₀) k)) ≫ S.fromSpecResidueField s₀
  obtain ⟨C, hC, hk⟩ := hH k x
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  have hmem : ∀ j, toUnit (Over.mk x) ≫ σ j ∈ C := fun j =>
    (hC _).2 ((range_subset_iff hL x _).2 ⟨j, rfl⟩)
  have h₁ := (hW (Over.mk x) (toUnit _)).1 (by
    rw [map_one, Nat.cast_pow]
    exact hk.2.2.2.1 _ (hmem j) _ (hmem j'))
  have : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  have hc : IsClopen (U : Set (𝟙_ (Over S)).left) := ⟨hU, U.isOpen⟩
  have h₂ : (U : Set (𝟙_ (Over S)).left) = Set.univ := hc.eq_univ ⟨_, h₁ ⟨q, rfl⟩⟩
  have h₃ := (hW (𝟙_ (Over S)) (𝟙 _)).2 (by rw [h₂]; exact Set.subset_univ _)
  rw [map_one, Category.id_comp, Category.id_comp] at h₃
  exact h₃

theorem hasQuot_of_linearisation {R : Type} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {s : Sp R ⟶ Sp (KA l)} (o : Ob D l s) {𝔓 : Ideal (𝓞 E)} {p i n : ℕ}
    {σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)} {K : Set o.t.G.left} (hD : 1 ≤ D.p + D.q) (hA : admitted l 𝔓 p)
    (hL : Lists (p ^ 2) σ K) (hH : HeckeSet D o.t 𝔓 p i K) (C : Type) [CommGroup C] [Finite C]
    (v : C →* (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (e : C → Fin n) (he : Function.Injective e) (hv : ∀ c, v c = σ (e c))
    (hσ : ∀ j, ∃ c, v c = σ j)
    (hu : ∃ u : ∀ c : C, LB.Gen (LB.LinComb (lbPow o.t.PP.L (p ^ 2)) (K := Fin 2)
        ![𝟙 o.t.G.left, ((toUnit o.t.G ≫ v c) * 𝟙 o.t.G).left] ![1, -1]), (∀ c, (u c).IsGen) ∧
      ∀ c c', LB.Gen.Corr (lbPow o.t.PP.L (p ^ 2)) _ _ _ _ (u (c * c')) (LB.mulGen (lbPow o.t.PP.L (p ^ 2)) _ _ _ _ (u c)
        (LB.pullGen (lbPow o.t.PP.L (p ^ 2)) _ _ (u c') ((toUnit o.t.G ≫ v c) * 𝟙 o.t.G).left))) :
    HasQuot o p K := by
  have := o.proper
  obtain ⟨u, hu₁, hu₂⟩ := hu
  have hinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (c : C),
      toUnit (Over.mk t) ≫ v c = 1 → c = 1 := fun k _ _ t c h => by
    have h₁ : toUnit (Over.mk t) ≫ v c = toUnit (Over.mk t) ≫ v 1 := by rw [h, map_one, MonObj.comp_one]
    rw [hv, hv] at h₁
    exact he (hL.2.2 k t (congrArg CommaMorphism.left h₁))
  obtain ⟨B, gB, ψ, hB, hψ, hf, het, hs, hk₁, hk₂⟩ : ∃ (B : Over (Sp R)) (_ : GrpObj B) (ψ : o.t.G ⟶ B),
      IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ c, v c ≫ ψ = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (x : Over.mk t ⟶ o.t.G),
        x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ v c :=
    GlobalTheory.exists_quotient_by_finite_group_of_sections R (pol o) C v hinj
  obtain ⟨M, hM, hiso⟩ := GlobalTheory.LinDescent.exists_descent (Sp R) o.t.G B ψ C v (lbPow o.t.PP.L (p ^ 2))
    (LB.isLB_linComb o.t.PP.isLB _ _) hψ hf het hs hk₁ (fun k _ _ t => ⟨hk₂ k t, hinj k t⟩) u hu₁ hu₂
  have hker : KerSet ψ K := fun k _ _ t z => by
    rw [hk₂, range_subset_iff hL]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨e c, by rw [hv]⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨c, hc⟩ := hσ j
      exact ⟨c, by rw [hc]⟩
  obtain ⟨t', ψ', h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_quotient_triple_family_reduced_noetherian E H R o.t _ p B ψ M (isUnit_natCast s) hA.2.2.1.pos o.proper
    (pol o).smoothDim o.ample o.ktriv hB hM hψ hf het hs (fun k _ _ x => by
      obtain ⟨C₀, hC₀, hk⟩ := hH k x
      have hm : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 ↔ z ∈ C₀ := fun z => (hker k x z).trans (hC₀ z).symm
      refine ⟨(Nat.card_congr (Equiv.subtypeEquivRight hm)).trans hk.2.2.2.2.1, fun z hz => ⟨?_, fun a => ?_⟩⟩
      · obtain ⟨c, rfl⟩ := (hk₂ k x z).1 hz
        rw [← MonObj.comp_pow, hv, hL.1, MonObj.comp_one]
      · exact (hm _).2 (hk.1 z ((hm z).1 hz) a)) hiso
  exact GlobalTheory.hasQuot_of_isIsogT E H D l 𝔓 p i (Sp R) s o t' ψ' K hD hA h₁ h₂ h₃ h₄
    (fun k _ _ x z => (h₅ _ z).trans (hker k x z)) hH

end GlobalTheory.HkLoc


open GlobalTheory.HkLoc in
theorem GlobalTheory.exists_etale_hasQuot_of_lists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] (s : Sp R ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (K : Set o.t.G.left) (q : Sp R), 1 ≤ D.p + D.q → admitted l 𝔓 p → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → ∃ (R' : Type) (_ : CommRing R') (π : Sp R' ⟶ Sp R) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π), Etale π ∧ q ∈ Set.range π ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l 𝔓 p i n R _ _ _ s o σ K q hD hA hL hH
  have hp : 0 < p := hA.2.2.1.pos
  have hΓ : ∀ m : ℕ, 0 < m → IsUnit (m : Γ(Sp R, ⊤)) := fun m hm => by
    simpa using (isUnit_natCast s m hm).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  obtain ⟨C, hC⟩ := GlobalTheory.HkFam.exists_subgroup_eq_range_of_lists E H D 𝔓 p i n (Sp R) o.t σ K o.proper (hΓ p hp) hL hH
  have hmem : ∀ c : C, ∃ j, σ j = c := fun c => by
    have : c.1 ∈ (C : Set (𝟙_ (Over (Sp R)) ⟶ o.t.G)) := c.2
    rwa [hC] at this
  choose e he using hmem
  have einj : Function.Injective e := fun c c' h => Subtype.ext (by rw [← he, h, he])
  have : Finite C := Finite.of_injective e einj
  obtain ⟨R', _, _, het, hq, hlin⟩ := GlobalTheory.exists_etale_linearisation R (pol o) (p ^ 2) C C.subtype q
    (isUnit_natCast s _ (pow_pos hp 2)) (pow_pos hp 2)
    (fun c => Subtype.ext (by
      have := hL.1 (e c)
      rw [he] at this
      exact this))
    (fun c c' => by
      have := weilIs_one o hp (hΓ _ (pow_pos hp 2)) hL hH (e c) (e c')
      rw [he, he] at this
      exact this)
  let π : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  have hπ : Etale π := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.2 het
  have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  have : AlgebraicGeometry.IsReduced (Sp R') := GlobalTheory.isReduced_of_smooth_of_isReduced π
  have : _root_.IsReduced R' := (affine_isReduced_iff (CommRingCat.of R')).1 this
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ s (π ≫ s) π rfl rfl
    (by simp [spMap]) o
  obtain ⟨h₁, -, h₂⟩ := (GlobalTheory.heckeSets_pull E H D 𝔓 p i _ _ o.t o'.t π m.toSABMap o.proper).2 K
  obtain ⟨σ', hσ', hL'⟩ := h₂ _ _ σ hL
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over (Sp R')))
  have tu : (toUnit (Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ π))).left = π := by simp
  let v : C →* (𝟙_ (Over (Sp R')) ⟶ o'.t.G) := MonoidHom.mk' (fun c => ρ.symm (toUnit _ ≫ c.1)) fun c c' => by
    rw [← map_mul, ← MonObj.comp_mul]
    rfl
  have hv : ∀ c, (v c).left ≫ m.toSABMap.φ = π ≫ c.1.left := fun c => by
    change (ρ.symm (toUnit _ ≫ c.1)).left ≫ _ = _
    rw [← e₀, ρ.apply_symm_apply, Over.comp_left, tu]
  have hv' : ∀ (c : C) j, σ j = c → v c = σ' j := fun c j h =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (by rw [hv, hσ', h]) ((Over.w _).trans (Over.w _).symm))
  refine ⟨R', inferInstance, π, o', m, hπ, hq, hasQuot_of_linearisation o' hD hA hL' (h₁ hH) C v e einj
    (fun c => hv' c _ (he c)) (fun j => ⟨⟨σ j, ?_⟩, hv' _ j rfl⟩) ?_⟩
  · change σ j ∈ (C : Set (𝟙_ (Over (Sp R)) ⟶ o.t.G))
    rw [hC]
    exact ⟨j, rfl⟩
  · exact hlin o'.t.G m.toSABMap.φ o'.t.PP.L v m.cart o'.t.PP.isLB (m.lin.imp fun _ h => h.1) hv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

theorem heckeQuot_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left) (f₁ f₂ : S ⟶ Xo.X) (n₁ : ObjMap o₁ Xo.univ f₁) (n₂ : ObjMap o₂ Xo.univ f₂), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → f₁ ≫ Xo.s = s → f₂ ≫ Xo.s = s → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → f₁ = f₂ ∧ ψ₁.left ≫ n₁.toSABMap.φ = ψ₂.left ≫ n₂.toSABMap.φ := by
  intro E _ _ _ H D l Xo P p i S hS s o o₁ o₂ ψ₁ ψ₂ K f₁ f₂ n₁ n₂ hA hK h₁ h₂ i₁ i₂ k₁ k₂
  obtain ⟨-, -, hp, hpP, hM⟩ := hA
  have hnat : ∀ {T : Over S} (x : T ⟶ o.t.G) (n : ℕ), x ≫ o.t.act.act (n : 𝓞 E) = x ^ n := by
    intro T x n
    induction n with
    | zero =>
      have h := o.t.act.add 0 0
      rw [add_zero] at h
      have h0 : o.t.act.act 0 = 1 := by simpa using h
      rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, o.t.act.add, MonObj.comp_mul, ih, o.t.act.one, Category.comp_id, pow_succ]
  have hkill : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G),
      Set.range z.left ⊆ K → z ^ p ^ 2 = 1 := by
    intro k _ _ x z hz
    obtain ⟨C, hC, hH⟩ := hK k x
    have hzC := hH.2.2.1 ((hC z).2 hz)
    have hbar : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
      rwa [map_natCast] at this
    have h := hzC ((p ^ 2 : ℕ) : 𝓞 E) (by
      rw [Nat.cast_pow, pow_two]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hbar)
    rwa [hnat] at h
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base E H D l p S s o o₁ o₂ ψ₁ ψ₂ K hp hM i₁ i₂ k₁ k₂ hkill
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2
    f₂ (𝟙 S) n₂).1 m
  have hf : f₁ = 𝟙 S ≫ f₂ :=
    (Xo.rep S s hS o₁).unique ⟨h₁, ⟨n₁⟩⟩ ⟨by rw [Category.id_comp, h₂], ⟨m'⟩⟩
  refine ⟨by rw [hf, Category.id_comp], ?_⟩
  subst hf
  have e := GlobalTheory.obj_rigid_closed GlobalTheory.firstFiveLaws.1 E H D l _ _ _ _ _ _ _ _ Xo.univ o₁ _ (Or.inl hS)
    n₁.toSABMap m'.toSABMap (fun a => ⟨_, n₁.eta a, m'.eta a⟩)
  rw [e, hm', ← Category.assoc, hm]

end GlobalTheory
end
