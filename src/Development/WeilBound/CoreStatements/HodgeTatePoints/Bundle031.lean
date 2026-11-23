module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle090
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle091
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle056
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle017
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle034
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle044
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle024
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle021
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfEquiv
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ReBase
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ReProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.DualLattices.PowMemCarrier
import ReciprocityTheory.DualLattices.Bundle018
import ReciprocityTheory.DualLattices.ProdDvdOfIso

@[expose] public section

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LCentre.Centre

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
    have hab : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hab
    refine ⟨h0, a.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hab]
    exact b.2
  · rintro ⟨h0, -, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨(a : Ω)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem exists_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ := by
  apply GlobalTheory.CompanionTheory.Ar.Centre.exists_centre <;> assumption

end PositivityTheory.HtPt.Mb.LCentre.Centre


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ :=
  @PositivityTheory.HtPt.Mb.LCentre.Centre.exists_centre
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LMorph.ChMorph

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem hom_eq_of_points {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) {i : Ω →+* Ω'} {f g : X' ⟶ X}
    (hf : Dominates ξ' ξ f i) (hg : Dominates ξ' ξ g i) (hb : ∀ q, f q = g q) : f = g := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.CompanionTheory.Ar.ChMorph.hom_eq_of_points <;> assumption

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  {o' : Type} [CommRing o'] [Algebra o' Ω'] {κ' : Type} {y : κ' → Ω'}

theorem specializes_of_dominates (M : PModel o x) (M' : PModel o' y) {i : Ω →+* Ω'} {f g : M'.X ⟶ M.X}
    (hf : Dominates M'.ξ M.ξ f i) (hg : Dominates M'.ξ M.ξ g i) (q : M'.X) : g q ⤳ f q := by
  apply GlobalTheory.CompanionTheory.Ar.ChMorph.specializes_of_dominates <;> assumption

theorem existsUnique_dominates :
    ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x)
      (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω')
      (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) →
      ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M o' _ Ω' _ _ κ' _ y M' i h
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.dominates_of_coords_regular M.X Ω M.ξ o κ x M'.X Ω' M'.ξ i M.tie M'.tie.gen M'.all
    (fun r p' => by
      obtain ⟨c, -, H⟩ := h p'
      exact H _ (Subalgebra.algebraMap_mem _ r))
    (fun p' => by
      obtain ⟨c, hc, H⟩ := h p'
      refine ⟨c, (map_ne_zero i).2 hc, fun c' => ?_⟩
      rw [← map_div₀]
      exact H _ (Algebra.subset_adjoin ⟨c', rfl⟩))
  refine ⟨f, hf, fun g hg => ?_⟩
  exact hom_eq_of_points M'.tie.gen M'.all hg hf fun q =>
    ((specializes_of_dominates M M' hf hg q).antisymm (specializes_of_dominates M M' hg hf q)).eq

end PositivityTheory.HtPt.Mb.LMorph.ChMorph


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.morph : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω') (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) → ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i :=
  @PositivityTheory.HtPt.Mb.LMorph.ChMorph.existsUnique_dominates
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Re

theorem tens_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  intro p _ C _ _ _ v R _ _ _ _ N₁ _ _ _ N₂ _ _ _ A₁ A₂
  refine ⟨PositivityTheory.HtPt.Re.hopfProd A₁ A₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; rfl
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_inl A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_inr A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_stab₁ A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_stab₂ A₁ A₂
  · intro c₁ c₂ h₁ h₂
    rw [PositivityTheory.HtPt.Re.hopfProd_carrier]
    exact PositivityTheory.HtPt.Re.hasColen_tn h₁ h₂

end PositivityTheory.HtPt.Re
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ch

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {C : ACurve K} {V : Type} [AddCommGroup V] [Module K V]

theorem basis_mem {i : C.I} {n : ℕ} {b : Module.Basis (Fin n) K V} {L : AddSubgroup V}
    (h : IsLatOf C i b L) (q : Fin n) : b q ∈ L := by
  refine (h _).2 fun r => ?_
  by_cases e : q = r <;> simp [e, Finsupp.single_apply]

theorem smul_mem_lat {i : C.I} {n : ℕ} {b : Module.Basis (Fin n) K V} {L : AddSubgroup V}
    (h : IsLatOf C i b L) {a : K} (ha : C.v i a ≤ 1) {x : V} (hx : x ∈ L) : a • x ∈ L := by
  refine (h _).2 fun r => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' ha ((h _).1 hx r)

theorem v_det_le {i : C.I} {n : ℕ} {b b' : Module.Basis (Fin n) K V} {L L' : AddSubgroup V}
    (h : IsLatOf C i b L) (h' : IsLatOf C i b' L') (hle : L ≤ L') : C.v i (b'.det b) ≤ 1 := by
  rw [Module.Basis.det_apply, Matrix.det_apply']
  refine (C.v i).map_sum_le fun σ _ => ?_
  rw [map_mul, map_prod]
  refine mul_le_one' ?_ (Finset.prod_le_one' fun q _ => (h' _).1 (hle (basis_mem h q)) _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]

theorem deg_triv [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    {L : C.I → AddSubgroup V} (h : ∀ i, IsLatOf C i b (L i)) : IsBun C L ∧ deg C L = 0 := by
  have hb : IsBun C L := Inhab.isBun_of_basis C b L h
  refine ⟨hb, ?_⟩
  rw [(GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L n b (fun _ => b) hb h).2]
  simp [Module.Basis.det_self]

end SlopeTestRemainingChoices

theorem deg_mono : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' := by
  intro K _ C V _ _ _ L L' hL hL' hle
  choose b hb using hL.1
  choose b' hb' using hL'.1
  obtain ⟨hf, e⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (Module.finBasis K V) b hL hb
  obtain ⟨hf', e'⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L' _ (Module.finBasis K V) b' hL' hb'
  rw [e, e']
  refine finsum_le_finsum' (hf.subset fun i hi h1 => hi (by simp [h1]))
    (hf'.subset fun i hi h1 => hi (by simp [h1])) fun i => ?_
  refine mul_le_mul_of_nonneg_left ?_ (Int.natCast_nonneg _)
  have n1 : C.v i ((Module.finBasis K V).det (b i)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((Module.finBasis K V).isUnit_det (b i)).ne_zero
  have n2 : C.v i ((Module.finBasis K V).det (b' i)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((Module.finBasis K V).isUnit_det (b' i)).ne_zero
  rw [WithZero.log_le_log n1 n2, ← Module.Basis.det_mul_det _ (b' i) (b i), map_mul]
  exact mul_le_of_le_one_right' (v_det_le (hb i) (hb' i) (hle i))

theorem deg_le_of_equiv {K : Type} [Field K] {C : ACurve K} {V V' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} (e : V ≃ₗ[K] V') (hL : IsBun C L)
    (hL' : IsBun C L') (h : ∀ i, ∀ x ∈ L i, e x ∈ L' i) : deg C L ≤ deg C L' := by
  obtain ⟨hM, hd⟩ := GlobalTheory.T.degree_invariant_linear_equiv K C V V' L
    (fun i => (L i).comap e.symm.toLinearMap.toAddMonoidHom) e hL (fun i x => by simp)
  rw [← hd]
  refine deg_mono K C V' _ _ hM hL' fun i y hy => ?_
  simpa using h i (e.symm y) hy

theorem deg_inj : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) := by
  intro K _ C V _ _ _ V' _ _ _ L L' f W hL hL' hf hh
  exact deg_le_of_equiv (Submodule.equivMapOfInjective f hf W) (GlobalTheory.T.sub_and_quotient_bundles K C V L W hL).1
    (GlobalTheory.T.sub_and_quotient_bundles K C V' L' _ hL').1 fun i x hx => hh i x hx

theorem subdeg_trivial : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 := by
  intro K _ C V _ _ _ n b L W h
  obtain ⟨hL, h0⟩ := deg_triv b h
  have hs := GlobalTheory.T.degree_additive_sub_quotient K C V L W hL
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K (fun q => W.mkQ (b q))
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have htop : ⊤ ≤ Submodule.span K (Set.range ((fun q => W.mkQ (b q)) ∘ a)) := by
    rw [hsp, show (Set.range fun q => W.mkQ (b q)) = W.mkQ '' Set.range b from
      Set.range_comp _ _, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
  let c := (Module.Basis.mk hli htop).reindex (Fintype.equivFin κ)
  have hc : ∀ q, c q = W.mkQ (b (a ((Fintype.equivFin κ).symm q))) := fun q => by simp [c]
  obtain ⟨hM, hM0⟩ := deg_triv (C := C) c (fun i => Inhab.isLatOf_latOf C i c)
  have := deg_mono K C _ _ _ hM (GlobalTheory.T.sub_and_quotient_bundles K C V L W hL).2 fun i y hy => by
    rw [← c.sum_repr y]
    refine sum_mem fun q _ => ⟨c.repr y q • b (a ((Fintype.equivFin κ).symm q)),
      smul_mem_lat (h i) (hy q) (basis_mem (h i) _), ?_⟩
    rw [hc]; simp
  omega

theorem ses_restrict {K : Type} [Field K] {C : ACurve K} {V V' V'' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    [AddCommGroup V''] [Module K V''] [FiniteDimensional K V'']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} {L'' : C.I → AddSubgroup V''}
    {f : V →ₗ[K] V'} {g : V' →ₗ[K] V''} (hL' : IsBun C L') (h : ShortExact C L L' L'' f g)
    (A : Submodule K V) (X : Submodule K V') (B : Submodule K V'')
    (hA : ∀ x, x ∈ A ↔ f x ∈ X) (hB : ∀ z, z ∈ B ↔ ∃ y ∈ X, g y = z) :
    ∃ I : C.I → AddSubgroup B, IsBun C I ∧ subDeg C L' X = subDeg C L A + deg C I ∧
      ∀ i z, z ∈ I i ↔ ∃ y ∈ L' i, y ∈ X ∧ g y = z := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  let f' : A →ₗ[K] X := f.restrict fun x hx => (hA x).1 hx
  let g' : X →ₗ[K] B := g.restrict fun y hy => (hB _).2 ⟨y, hy, rfl⟩
  have hse : ShortExact C (sub C L A) (sub C L' X)
      (fun i => (sub C L' X i).map g'.toAddMonoidHom) f' g' := by
    refine ⟨fun x y e => Subtype.ext (h1 (congrArg Subtype.val e)), fun y => ⟨fun hy => ?_, ?_⟩,
      fun z => ?_, fun i x => h4 i x, fun i z => Iff.rfl⟩
    · obtain ⟨x, hx⟩ := (h2 y).1 (congrArg Subtype.val hy)
      exact ⟨⟨x, (hA x).2 (hx ▸ y.2)⟩, Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (h2.apply_apply_eq_zero x)
    · obtain ⟨y, hy, e⟩ := (hB z).1 z.2
      exact ⟨⟨y, hy⟩, Subtype.ext e⟩
  obtain ⟨-, hI, hd⟩ := GlobalTheory.T.short_exact_first_term_bundle K C _ _ _ _ _ _ f' g' (GlobalTheory.T.sub_and_quotient_bundles K C V' L' X hL').1 hse
  refine ⟨_, hI, hd, fun i z => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, y.2, rfl⟩
  · rintro ⟨y, hy, hX, e⟩
    exact ⟨⟨y, hX⟩, hy, Subtype.ext e⟩

theorem subdeg_ses : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g X hL' h
  obtain ⟨I, hI, hd, hm⟩ := ses_restrict hL' h (X.comap f) X (X.map g) (fun _ => Iff.rfl)
    (fun _ => Iff.rfl)
  have hL'' := (GlobalTheory.T.short_exact_first_term_bundle K C _ _ _ _ _ _ f g hL' h).2.1
  have : deg C I ≤ subDeg C L'' (X.map g) :=
    deg_mono K C _ _ _ hI (GlobalTheory.T.sub_and_quotient_bundles K C V'' L'' _ hL'').1 fun i z hz => by
      obtain ⟨y, hy, -, e⟩ := (hm i z).1 hz
      exact (h.2.2.2.2 i z).2 ⟨y, hy, e⟩
  omega

theorem exists_dot {K : Type} [Field K] {d : ℕ} (ψ : Module.Dual K (Fin d → K)) :
    ∃ u : Fin d → K, ∀ x, u ⬝ᵥ x = ψ x := by
  refine ⟨fun j => ψ (Pi.single j 1), fun x => ?_⟩

  conv_rhs => rw [pi_eq_sum_univ' x, map_sum]
  simp [dotProduct, mul_comm]

theorem subdeg_orth : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W := by
  intro K _ C d L W X hL hW
  have hbij : Function.Bijective (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun u hu => funext fun j => ?_, fun ψ => ?_⟩
    · simpa using LinearMap.congr_fun hu (Pi.single j 1)
    · obtain ⟨u, hu⟩ := exists_dot ψ
      exact ⟨u, LinearMap.ext hu⟩
  obtain ⟨hD, -, hbi⟩ := GlobalTheory.T.dual_lattice_degree_neg K C _ _ L _ hL hbij
  let B₀ : (Fin d → K) →ₗ[K] W →ₗ[K] K := ((dotProductBilin K K).comp W.subtype).flip
  have hB₀ : ∀ φ (w : W), B₀ φ w = (w : Fin d → K) ⬝ᵥ φ := fun _ _ => rfl
  let B : ((Fin d → K) ⧸ X) →ₗ[K] W →ₗ[K] K :=
    X.liftQ B₀ fun φ hφ => LinearMap.ext fun w => (hW w).1 w.2 φ hφ
  have hB : ∀ φ (w : W), B (X.mkQ φ) w = (w : Fin d → K) ⬝ᵥ φ := fun _ _ => rfl
  have hBb : Function.Bijective B := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun ψ => ?_⟩
    · obtain ⟨φ, rfl⟩ := X.mkQ_surjective y
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        ← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
      intro ψ hψ
      obtain ⟨u, hu⟩ := exists_dot ψ
      have hu' : u ∈ W := (hW u).2 fun x hx => by
        rw [hu]; exact (Submodule.mem_dualAnnihilator ψ).1 hψ x hx
      rw [← hu, ← hB φ ⟨u, hu'⟩, hy]; rfl
    · obtain ⟨ψ', rfl⟩ := LinearMap.dualMap_surjective_of_injective W.injective_subtype ψ
      obtain ⟨u, hu⟩ := exists_dot ψ'
      refine ⟨X.mkQ u, LinearMap.ext fun w => ?_⟩
      rw [hB, dotProduct_comm, hu]; rfl
  obtain ⟨-, hq, -⟩ := GlobalTheory.T.dual_lattice_degree_neg K C _ _ _ B (GlobalTheory.T.sub_and_quotient_bundles K C _ _ X hD).2 hBb
  have he : dualLat C (quot C (dualLat C L (dotProductBilin K K)) X) B = sub C L W := by
    funext i; ext w
    have : (w : Fin d → K) ∈ L i ↔ (w : Fin d → K) ∈
        dualLat C (dualLat C L (dotProductBilin K K)) (dotProductBilin K K).flip i := by rw [hbi]
    refine Iff.trans ?_ this.symm
    constructor
    · intro H φ hφ
      exact H _ ⟨φ, hφ, rfl⟩
    · rintro H _ ⟨φ, hφ, rfl⟩
      exact H φ hφ
  have hs := GlobalTheory.T.degree_additive_sub_quotient K C _ _ X hD
  rw [he] at hq
  unfold dotDual
  unfold subDeg at hs ⊢
  omega

end PositivityTheory.HtPt.Ch
end

section

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Re

def splitEquiv {N N₁ N₂ : Type} [AddCommGroup N] [AddCommGroup N₁] [AddCommGroup N₂]
    (ι₁ : N₁ →+ N) (π₁ : N →+ N₁) (ι₂ : N₂ →+ N) (π₂ : N →+ N₂) (h11 : ∀ y, π₁ (ι₁ y) = y)
    (h22 : ∀ y, π₂ (ι₂ y) = y) (hsum : ∀ x, ι₁ (π₁ x) + ι₂ (π₂ x) = x) (h12 : ∀ y, π₁ (ι₂ y) = 0)
    (h21 : ∀ y, π₂ (ι₁ y) = 0) : N₁ × N₂ ≃+ N where
  toFun z := ι₁ z.1 + ι₂ z.2
  invFun x := (π₁ x, π₂ x)
  left_inv z := by simp [h11, h22, h12, h21]
  right_inv x := hsum x
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]; abel

theorem ret_colen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {N₁ : Type} [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁]
    {N₂ : Type} [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂]
    (ι₁ : N₁ →+ N) (π₁ : N →+ N₁) (ι₂ : N₂ →+ N) (π₂ : N →+ N₂) (h11 : ∀ y, π₁ (ι₁ y) = y)
    (h22 : ∀ y, π₂ (ι₂ y) = y) (hsum : ∀ x, ι₁ (π₁ x) + ι₂ (π₂ x) = x) (h12 : ∀ y, π₁ (ι₂ y) = 0)
    (h21 : ∀ y, π₂ (ι₁ y) = 0) (hs₁ : ∀ g ∈ AA.carrier, (fun x => g (ι₁ (π₁ x))) ∈ AA.carrier)
    (a b : NNReal)
    (ha : HasColen R v (AA.carrier.map (LinearMap.funLeft R C (ι₁ : N₁ → N))) a)
    (hb : HasColen R v (AA.carrier.map (LinearMap.funLeft R C (ι₂ : N₂ → N))) b) :
    HasColen R v AA.carrier (a ^ Fintype.card N₂ * b ^ Fintype.card N₁) := by
  let e := splitEquiv ι₁ π₁ ι₂ π₂ h11 h22 hsum h12 h21
  have e1 : (fun y : N₁ => e (y, 0)) = ι₁ := by
    funext y
    show ι₁ y + ι₂ 0 = ι₁ y
    simp
  have e2 : (fun y : N₂ => e (0, y)) = ι₂ := by
    funext y
    show ι₁ 0 + ι₂ y = ι₂ y
    simp
  have h := tn_char AA e (fun g hg => by
    convert hs₁ g hg using 3 with x
    exact congrFun e1 _)
  rw [e1, e2] at h
  have h2 := hasColen_tn ha hb
  rw [← h] at h2
  have h3 := hasColen_map v e.symm _ _ h2
  rwa [show AA.carrier.map (LinearMap.funLeft R C (e : N₁ × N₂ → N)) =
    AA.carrier.map (pbE (C := C) (R := R) e : (N → C) →ₗ[R] (N₁ × N₂ → C)) from rfl,
    map_pbE_symm] at h3

theorem eq_of_pow_mul {x₁ y₁ x₂ y₂ : NNReal} {m n : ℕ} (hm : m ≠ 0) (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂)
    (hy : y₂ ≠ 0) (h : x₁ ^ m * x₂ ^ n = y₁ ^ m * y₂ ^ n) : x₁ = y₁ := by
  refine le_antisymm h₁ (not_lt.1 fun hlt => ?_)
  have a : x₁ ^ m < y₁ ^ m := pow_lt_pow_left₀ hlt zero_le hm
  have b : x₂ ^ n ≤ y₂ ^ n := pow_le_pow_left₀ zero_le h₂ n
  have c : 0 < y₂ ^ n := pow_pos (pos_iff_ne_zero.2 hy) n
  exact absurd h (ne_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left b zero_le)
    (mul_lt_mul_of_pos_right a c)))

theorem ret_tight : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ hN AA N' _ _ _ ι π hπ hst hT
  classical
  have hcnt := @PositivityTheory.HtPt.Ra.cnt
  have hlens := @PositivityTheory.HtPt.Rc.lens
  let ι₂ : π.ker →+ N := π.ker.subtype
  let π₂ : N →+ π.ker := (AddMonoidHom.id N - ι.comp π).codRestrict π.ker (fun x => by
    simp [AddMonoidHom.mem_ker, hπ])
  have hπ₂ : ∀ x, ι₂ (π₂ x) = x - ι (π x) := fun _ => rfl
  have h12 : ∀ y, π (ι₂ y) = 0 := fun y => y.2
  have h22 : ∀ y, π₂ (ι₂ y) = y := fun y => Subtype.ext (by
    show ι₂ (π₂ (ι₂ y)) = ι₂ y
    rw [hπ₂, h12]; simp)
  have h21 : ∀ y, π₂ (ι y) = 0 := fun y => Subtype.ext (by
    show ι₂ (π₂ (ι y)) = 0
    rw [hπ₂, hπ]; simp)
  have hsum : ∀ x, ι (π x) + ι₂ (π₂ x) = x := fun x => by rw [hπ₂]; simp
  have hs₂ : ∀ g ∈ AA.carrier, (fun x => g (ι₂ (π₂ x))) ∈ AA.carrier :=
    (stabadd C R N N AA AA (AddMonoidHom.id N) (ι.comp π) (fun g hg => hg) hst).2
  obtain ⟨⟨A₁, hA₁⟩, -⟩ := ret_hopf p C v R hv hp N AA N' ι π hπ hst
  obtain ⟨⟨A₂, hA₂⟩, -⟩ := ret_hopf p C v R hv hp N AA π.ker ι₂ π₂ h22 hs₂
  have hN₁ : ∀ y : N', p • y = 0 := fun y => by rw [← hπ y, ← map_nsmul, hN, map_zero]
  have hN₂ : ∀ y : π.ker, p • y = 0 := fun y => by rw [← h22 y, ← map_nsmul, hN, map_zero]
  obtain ⟨a₁, c₁, o₁, -, hc₁0, -, ha₁, hc₁, ho₁⟩ := hlens p C v R hv hp N' hN₁ A₁
  obtain ⟨a₂, c₂, o₂, -, hc₂0, ho₂0, ha₂, hc₂, ho₂⟩ := hlens p C v R hv hp π.ker hN₂ A₂
  have l₁ := (hcnt p C v R hv hp N' hN₁ A₁ _ _ ha₁ hc₁).1
  have l₂ := (hcnt p C v R hv hp π.ker hN₂ A₂ _ _ ha₂ hc₂).1
  have m₁ := u4 p C v R hv hp N' hN₁ A₁ _ _ hc₁ ho₁
  have m₂ := u4 p C v R hv hp π.ker hN₂ A₂ _ _ hc₂ ho₂
  rw [hA₁] at ha₁ hc₁ ho₁
  rw [hA₂] at ha₂ hc₂ ho₂
  obtain ⟨a, c, o, ha, hc, ho, ea, eo⟩ := hT
  obtain rfl := hasLen_unique hv ha
    (ret_af p C v R hv hp N AA N' π.ker ι π ι₂ π₂ hπ h22 hsum h12 h21 hst hs₂ _ _ ha₁ ha₂)
  obtain rfl := hasLen_unique hv ho
    (ret_om hv AA ι π ι₂ π₂ hπ h22 hsum h12 h21 hst hs₂ _ _ ho₁ ho₂)
  obtain rfl := hasColen_unique hv AA.lat hc
    (ret_colen AA ι π ι₂ π₂ hπ h22 hsum h12 h21 hst _ _ hc₁ hc₂)
  have hcard : Fintype.card N = Fintype.card N' * Fintype.card π.ker := by
    rw [← Fintype.card_prod]
    exact (Fintype.card_congr (splitEquiv ι π ι₂ π₂ hπ h22 hsum h12 h21).toEquiv).symm
  rw [hcard] at ea eo
  refine ⟨a₁, c₁, o₁, ha₁, hc₁, ho₁, ?_, ?_⟩
  · refine eq_of_pow_mul (m := Fintype.card π.ker) (n := Fintype.card N') Fintype.card_ne_zero
      l₁ l₂ (pow_ne_zero _ hc₂0) ?_
    calc _ = (a₁ * a₂) ^ (Fintype.card N' * Fintype.card π.ker * (p - 1)) := by ring
      _ = _ := by rw [ea]; ring
  · refine (eq_of_pow_mul (m := Fintype.card π.ker) (n := Fintype.card N') Fintype.card_ne_zero
      m₁ m₂ (pow_ne_zero _ ho₂0) ?_).symm
    calc _ = (c₁ ^ Fintype.card π.ker * c₂ ^ Fintype.card N') ^ 2 := by ring
      _ = _ := by rw [← eo]; ring

end PositivityTheory.HtPt.Re
end
end
