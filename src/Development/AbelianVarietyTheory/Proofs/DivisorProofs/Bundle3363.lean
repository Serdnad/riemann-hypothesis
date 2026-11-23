module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle586
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3287
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3355
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.NormDown

theorem dvd_of_map_dvd {V V' : Type} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {x y : V} (hxy : h x ∣ h y) : x ∣ y := by
  rcases ValuationRing.dvd_total x y with hd | ⟨c, rfl⟩
  · exact hd
  · by_cases hy : y = 0
    · simp [hy]
    obtain ⟨e, he⟩ := hxy
    have hy' : h y ≠ 0 := fun h0 => hy (hi (by rw [h0, map_zero]))
    have h1 : h y * 1 = h y * (h c * e) := by rw [mul_one, ← mul_assoc, ← map_mul, ← he]
    have hu : IsUnit (h c) := isUnit_iff_exists_inv.2 ⟨e, (mul_left_cancel₀ hy' h1).symm⟩
    have hc : IsUnit c := (isUnit_map_iff h c).1 hu
    exact ⟨↑hc.unit⁻¹, by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem map_injective {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {I I' : Ideal V} (e : I.map h = I'.map h) : I = I' := by
  obtain ⟨x, rfl⟩ : ∃ x, I = Ideal.span {x} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  obtain ⟨y, rfl⟩ : ∃ y, I' = Ideal.span {y} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I').symm⟩
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.span_singleton_eq_span_singleton] at e
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd (dvd_of_map_dvd h hi e.dvd) (dvd_of_map_dvd h hi e.symm.dvd)

theorem jK_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (fK : FractionRing R →+* FractionRing S)
    (hc : ∀ a, fK (algebraMap R _ a) = algebraMap S _ (f a)) : jK S ≫ spMap f = spMap fK ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (hc a).symm

theorem normDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  have idlAlong_eq_map_local {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X)
      (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
      idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
    have hx : χ (closedPoint R) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have idlAlong_comp_local {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
      [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [idlAlong_eq_map_local J χ ⟨U, hU⟩ hle, idlAlong_eq_map_local J _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z Z X₁.π X₁.fin inferInstance hLN X₁.normal hZ.2.1
    (by rw [hπ]; exact hWc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V T.complete (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = T₂.y ≫ i := by
    intro χ hχ
    rw [Category.assoc, hχ, ← Category.assoc, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'),
      jK_spMap f fK hfK, Category.assoc, hgen, hy₂]
    simp only [Category.assoc]
  obtain ⟨a₀, ha₀, h₀⟩ := hord T₂ _ (hover (spMap f ≫ ξ₁) (Category.assoc _ _ _))
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord T₂ _ (hover (ψ j) (hψ j))
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  apply map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← idlAlong_comp_local, hcomp, Category.assoc, h₀, hmp]
  simp only [← idlAlong_comp_local, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.NormDown
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GCTrait

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem map_cycAway_mem {n : ℕ} {L : Type} [Field L] (φ : cycAway n →+* L) (K : Subring L)
    (hz : φ (zetaAway n) ∈ K) (hi : φ ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ ∈ K) (c : cycAway n) : φ c ∈ K := by
  obtain ⟨c, hc⟩ := c
  induction hc using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hz
    · exact hi
  | zero => rw [show (⟨0, _⟩ : cycAway n) = 0 from rfl, map_zero]; exact K.zero_mem
  | one => rw [show (⟨1, _⟩ : cycAway n) = 1 from rfl, map_one]; exact K.one_mem
  | add x y hx hy ihx ihy =>
    rw [show (⟨x + y, _⟩ : cycAway n) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add (f := _)]; exact K.add_mem ihx ihy
  | neg x hx ih =>
    rw [show (⟨-x, _⟩ : cycAway n) = -⟨x, hx⟩ from rfl, map_neg]; exact K.neg_mem ih
  | mul x y hx hy ihx ihy =>
    rw [show (⟨x * y, _⟩ : cycAway n) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]; exact K.mul_mem ihx ihy

theorem exists_finite_point (n : ℕ) {X : Scheme.{0}} (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s]
    (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (x : Sp K ⟶ X),
      spMap (algebraMap K (PadicAlgCl p)) ≫ x = y := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum (PadicAlgCl p))) trivial
  have hr : Set.range y ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) q default]
    exact hy
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec y hr)
  obtain ⟨a, ha⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hft : a.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ha]
    infer_instance
  letI := a.hom.toAlgebra
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := cycAway n) (A := Γ(X, U)) (self := hft)
  let S : Set (PadicAlgCl p) := φ.hom '' (T : Set Γ(X, U)) ∪
    {φ.hom (a.hom (zetaAway n)), φ.hom (a.hom ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩)}
  have hSfin : S.Finite := (T.finite_toSet.image _).union (Set.toFinite _)
  haveI : Finite S := hSfin.to_subtype
  let K := IntermediateField.adjoin ℚ_[p] S
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hS : S ⊆ K := IntermediateField.subset_adjoin ℚ_[p] S
  have hc : ∀ c : cycAway n, φ.hom (a.hom c) ∈ K.toSubfield.toSubring :=
    map_cycAway_mem (φ.hom.comp a.hom) K.toSubfield.toSubring
      (hS (Or.inr (Or.inl rfl))) (hS (Or.inr (Or.inr rfl)))
  have hmem : ∀ b, φ.hom b ∈ K := fun b => by
    have hb : b ∈ Algebra.adjoin (cycAway n) (T : Set Γ(X, U)) := hT ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS (Or.inl ⟨x, hx, rfl⟩)
    | algebraMap c => exact hc c
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  let φK : Γ(X, U) →+* K := φ.hom.codRestrict K hmem
  refine ⟨K, hK, spMap φK ≫ hU.fromSpec, ?_⟩
  rw [← Category.assoc, spMap_comp'', ← IsOpenImmersion.lift_fac hU.fromSpec y hr, ← hφ]
  rfl

theorem exists_ext_emb (p : ℕ) [Fact p.Prime] (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W) (fK : FractionRing V →+* FractionRing W)
    (hinj : Function.Injective f) (hloc : IsLocalHom f) (hfin : f.Finite)
    (hc : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) (κ : FractionRing V →+* PadicAlgCl p)
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ ι : FractionRing W →+* PadicAlgCl p, ι.comp fK = κ ∧
      ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
  letI : Algebra V W := f.toAlgebra
  letI : Algebra (FractionRing V) (FractionRing W) := fK.toAlgebra
  letI : Algebra (FractionRing V) (PadicAlgCl p) := κ.toAlgebra
  haveI : Algebra.IsIntegral V W := ⟨fun w => hfin.to_isIntegral w⟩
  haveI : IsLocalHom (algebraMap V W) := hloc
  have hint : ∀ w : W, IsIntegral (FractionRing V) (algebraMap W (FractionRing W) w) := fun w =>
    IsIntegral.map_of_comp_eq (algebraMap V (FractionRing V)) (algebraMap W (FractionRing W))
      (RingHom.ext fun v => hc v) (Algebra.IsIntegral.isIntegral w)
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing W) := by
    constructor
    intro z
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) z
    rw [div_eq_mul_inv]
    exact ((hint a).mul (hint b).inv).isAlgebraic
  let ι : FractionRing W →ₐ[FractionRing V] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hι : ι.toRingHom.comp fK = κ := RingHom.ext fun x => ι.commutes x
  refine ⟨ι.toRingHom, hι, GlobalTheory.unitBall_eq_of_integral_dvr p V W hinj κ ι.toRingHom (fun v => ?_) hV⟩
  show ι (algebraMap W (FractionRing W) (f v)) = _
  rw [← hc]
  exact ι.commutes _

theorem exists_cTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X₁.M.Z), Set.range (gPt p ≫ y ≫ X₁.π) ⊆ Set.range i → ∃ c : CTrait X₁ p (y (cPt p)), c.y = y := by
  intro g n F W Z i X₁ hg hn hodd hi p _ y hr
  let y₁ : Sp (PadicAlgCl p) ⟶ F.X := IsOpenImmersion.lift i (gPt p ≫ y ≫ X₁.π) hr
  have hy₁ : y₁ ≫ i = gPt p ≫ y ≫ X₁.π := IsOpenImmersion.lift_fac _ _ _
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  obtain ⟨K, hK, x, hx⟩ := exists_finite_point n F.s p y₁
  obtain ⟨hdvr, hcomp, hunit⟩ := GlobalTheory.intRing_complete_dvr p K hK
  haveI := hdvr
  haveI : CharZero (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := inferInstance
  let e : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ≃ₐ[GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K] K := FractionRing.algEquiv _ K
  let es : K →+* FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := e.symm.toRingEquiv.toRingHom
  have hbase : GlobalTheory.Mum.Base (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  obtain ⟨T, f, fK, hinj, hloc, hfin, hc, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F _ hbase hdvr (spMap es ≫ x)
  obtain ⟨ι, hι, hint⟩ := exists_ext_emb p _ T.V f fK hinj hloc hfin hc _ hunit
  have h2 : algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p) =
      (algebraMap K (PadicAlgCl p)).comp e.toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (RingHom.ext fun v => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
    refine (IsFractionRing.lift_algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) v).trans ?_
    show _ = algebraMap K (PadicAlgCl p) (e (algebraMap _ _ v))
    rw [AlgEquiv.commutes]
    rfl
  have hκ : (algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p)).comp es = algebraMap K (PadicAlgCl p) := by
    ext k
    rw [h2]
    show algebraMap K (PadicAlgCl p) (e (e.symm k)) = _
    rw [AlgEquiv.apply_symm_apply]
  have key : spMap ι ≫ spMap fK ≫ spMap es = spMap (algebraMap K (PadicAlgCl p)) := by
    rw [spMap_comp'', spMap_comp'', ← RingHom.comp_assoc, hι, hκ]
  refine ⟨⟨y, rfl, T, ι, hint, ?_⟩, rfl⟩
  calc gPt p ≫ y ≫ X₁.π = y₁ ≫ i := hy₁.symm
    _ = (spMap (algebraMap K (PadicAlgCl p)) ≫ x) ≫ i := by rw [hx]
    _ = ((spMap ι ≫ spMap fK ≫ spMap es) ≫ x) ≫ i := by rw [key]
    _ = spMap ι ≫ T.y ≫ i := by rw [hTy]; simp only [Category.assoc]

end GlobalTheory.Poinc.GCTrait
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.Poinc.ideal_orders_of_proper_model : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ∀ (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a}) → (∀ (T : Trait F) (k : ℕ), 1 ≤ k → φ.evalZ ((k : ℤ) • T.β) = k * φ.evalZ T.β) → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  intro g n F W8 Z i φ X₁ Y πY hhom hprop ι J₁ hsupp hord hφ
  haveI := hprop

  have hsurj : Function.Surjective πY := by
    have hgen : genericPoint X₁.M.Z ∈ Set.range πY := by
      have w : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
      refine ⟨Y.pt w, ?_⟩
      have h := congrArg (fun h : Sp X₁.Ω₁ ⟶ X₁.M.Z => h w) (show Y.pt ≫ πY = _ from hhom)
      simp only [Scheme.Hom.comp_apply] at h
      rw [h]
      exact X₁.M.pt_apply _
    have hcl : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
    intro x
    have : x ∈ closure (Set.range πY) :=
      closure_mono (Set.singleton_subset_iff.2 hgen) (by rw [genericPoint_spec X₁.M.Z]; trivial)
    rwa [hcl.closure_eq] at this
  refine ⟨fun x hx => ?_, fun T ξ₁ hT => ?_⟩
  · obtain ⟨y, rfl⟩ := hsurj x
    exact hsupp y (by rw [Scheme.IdealSheafData.support_comap]; exact hx)
  ·
    obtain ⟨K', _, σ, yK, hσ, hy⟩ := GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType πY inferInstance hsurj (FractionRing T.V) (jK T.V ≫ ξ₁)
    obtain ⟨V', _, _, _, _, f, τ, hc', hfi, hfl, hff, hτ⟩ := GlobalTheory.T.exists_complete_dvr_integralClosure_finite_fractionRing T.V T.complete K' σ hσ
    have hfK : ∀ a, (τ.comp σ) (algebraMap T.V _ a) = algebraMap V' _ (f a) := hτ
    obtain ⟨ξ', hξπ, hξg⟩ := GlobalTheory.T.proper_lift_trait_of_generic_lift πY hprop T.V V' f (τ.comp σ) hfK ξ₁ (spMap τ ≫ yK) (by
      rw [Category.assoc, hy, spMap_comp, Category.assoc])
    have hB' : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
    obtain ⟨T₂, f₂, fK₂, hf₂i, hf₂l, -, hf₂K, hT₂y⟩ :=
      GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB' inferInstance (spMap (τ.comp σ) ≫ T.y)
    haveI := hfl
    haveI := hf₂l
    have hjK : ∀ {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (u : R →+* S)
        (uK : FractionRing R →+* FractionRing S), (∀ a, uK (algebraMap R _ a) = algebraMap S _ (u a)) →
        jK S ≫ spMap u = spMap uK ≫ jK R := by
      intro R S _ _ _ _ u uK hu
      change spMap (algebraMap S (FractionRing S)) ≫ spMap u = spMap uK ≫ spMap (algebraMap R (FractionRing R))
      rw [← spMap_comp, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun a => (hu a).symm)

    have hcomm : jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = T₂.y ≫ i := by
      have e1 := hjK f₂ fK₂ hf₂K
      calc jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ ξ' ≫ πY ≫ X₁.π := by
            simp only [Category.assoc]
        _ = spMap fK₂ ≫ (jK V' ≫ ξ') ≫ πY ≫ X₁.π := by rw [e1]; simp only [Category.assoc]
        _ = spMap fK₂ ≫ spMap τ ≫ (yK ≫ πY) ≫ X₁.π := by rw [hξg]; simp only [Category.assoc]
        _ = spMap fK₂ ≫ spMap τ ≫ spMap σ ≫ (jK T.V ≫ ξ₁ ≫ X₁.π) := by rw [hy]; simp only [Category.assoc]
        _ = T₂.y ≫ i := by rw [hT, hT₂y, spMap_comp]; simp only [Category.assoc]
    obtain ⟨a', ha', hid⟩ := hord T₂ (spMap f₂ ≫ ξ') hcomm
    rw [GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc, hξπ, ← Category.assoc, ← spMap_comp,
      GlobalTheory.TraitOrder.idlAlong_comp] at hid

    set h := f₂.comp f with hh
    have hinj : Function.Injective h := hf₂i.comp hfi
    have hloc : IsLocalHom h := inferInstance
    have hne : h T.ϖ ≠ 0 := (map_ne_zero_iff h hinj).2 T.irr.ne_zero
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T₂.irr
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · exact absurd ((isUnit_map_iff h T.ϖ).1 (he.isUnit_iff.2 (by simp))) T.irr.not_isUnit
      · exact hpos
    obtain ⟨b, hb, hI⟩ := GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr T.V T₂.V h hinj T.ϖ T₂.ϖ e a' _ T.irr T₂.irr he hid

    have hB₂ : GlobalTheory.Mum.Base T₂.V := ⟨⟨inferInstance, inferInstance, inferInstance, T₂.complete⟩, inferInstance⟩
    obtain ⟨eq, heq⟩ := GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n _ _ F T T₂ T₂.V h (RingHom.id _) (fK₂.comp (τ.comp σ)) (RingHom.id _)
      hB₂ inferInstance hinj Function.injective_id hloc inferInstance
      (fun a => by rw [RingHom.comp_apply, hfK, hf₂K]; rfl) (fun _ => rfl)
      (by
        rw [hT₂y, spMap_comp, Category.assoc]
        have hid1 : spMap (RingHom.id (FractionRing T₂.V)) = 𝟙 _ := by
          simp [spMap]
        rw [hid1, Category.id_comp]) T₂.ϖ e 1 T₂.irr he (by simp)
    have hval : φ.evalZ T₂.β = e * φ.evalZ T.β := by
      rw [← hφ T e he1]
      unfold InvFun.evalZ
      rw [← φ.eval_equiv eq.toIntLinearEquiv]
      congr 1
      ext a c
      have := heq a c
      simp only [Nat.cast_one, one_mul] at this
      simp [AddEquiv.coe_toIntLinearEquiv, ← this]
    refine ⟨b, ?_, hI⟩
    have h1 : (e : ℝ) * b = e * (ι * φ.evalZ T.β) := by
      rw [← Nat.cast_mul, hb, ha', hval]; ring
    have h2 : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
    exact mul_left_cancel₀ h2 h1
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem torsRat_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → GlobalTheory.TChart.TorsRat t.G l.M' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD
  haveI : CharZero R := hR.2
  have hadm : AdmBase R (maximalIdeal R) := hR.1
  have hn : 1 ≤ l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  haveI := P.U.gen_hom
  refine GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed t.G t.G P.A P.U.gen (𝟙 _) (𝟙 _) l.M' P.U.gen_hom
    inferInstance inferInstance (Category.comp_id _) hn ?_
  intro σ x hx
  letI : (Over.pullback (jK R)).Monoidal := (Over.instBraidedPullback (f := jK R)).toMonoidal
  letI : GrpObj ((Over.pullback (jK R)).obj t.G) := Functor.grpObjObj (F := Over.pullback (jK R))
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ t.G, y = x := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj t.G,
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ l.M' = 1 := by rw [hy0]; exact hx
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ l.M' = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A.A, a = h ≫ P.U.gen.hom := ⟨_, rfl⟩
  have ha : a ^ l.M' = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) l.M' hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨⟨p', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom l.M' hn p
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p' a a' hext ha').1 ((hT.1 p a).2 hp.symm)
  have heq := GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data L R hR t P iw s ε e hε hs hD σ p p' hext
  have haa : a' = a := ((hT.1 p' a').1 h2).trans (((hT.2.2.1 p p').2 heq).symm.trans hp)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app t.G).left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app t.G := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ P.U.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ P.U.gen.hom P.U.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  rw [hy0] at hyx
  simpa using hyx

end GlobalTheory.UCanon
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_thetaSetupTower_baseChange_member : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V'), IsCN V' → Function.Injective io → io.Finite → ∃ 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ, (∀ ev₂ h (zt : 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → (𝔪₂ ev₂ h).Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c))) ∧ ∀ ev₂ h ev₂' h' (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → ∀ a mu, (𝔪₂ ev₂' h').YY a mu ↔ (𝔪₂ ev₂ h).YY (𝔗.gl σ a) mu := by
  first | exact @GlobalTheory.exists_baseChange_member_of_tower | exact GlobalTheory.exists_baseChange_member_of_tower | (intros; apply GlobalTheory.exists_baseChange_member_of_tower <;> assumption)
end
