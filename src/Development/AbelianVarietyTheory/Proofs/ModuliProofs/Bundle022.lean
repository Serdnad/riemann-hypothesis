module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → ∀ σ : LB.Sec (M.pull j), (∃ i, σ.f i ≠ 0) → ∃ (c : K) (s : LB.Sec M), c ≠ 0 ∧ (∀ i, (j.app (M.U i)).hom (s.f i) = cst fK (j ⁻¹ᵁ M.U i) c * rs XK (le_pull M j le_rfl) (σ.f (fun _ => i))) ∧ ∃ x ∈ Out.nonzeroLocus s, f x = IsLocalRing.closedPoint O := by
  first | exact @GlobalTheory.exists_smul_sec_nonzero_on_special_fibre | exact GlobalTheory.exists_smul_sec_nonzero_on_special_fibre | (intros; apply GlobalTheory.exists_smul_sec_nonzero_on_special_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS
section Basic
variable {Y Z : Scheme.{0}}

theorem rsT_of_le {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := dif_pos h

theorem pbT_of_le (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) :
    pbT f s O = (f.appLE O₀ O h).hom s := dif_pos h

theorem rsT_add {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sub {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_neg {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : rsT (-s) O = -rsT s O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mul {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s * t) O = rsT s O * rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_zero {O₀ : Y.Opens} (O : Y.Opens) : rsT (0 : Γ(Y, O₀)) O = 0 := by
  unfold rsT; split_ifs <;> simp

theorem rsT_one {O₀ O : Y.Opens} (h : O ≤ O₀) : rsT (1 : Γ(Y, O₀)) O = 1 := by
  rw [rsT_of_le h, map_one]

theorem rsT_sum {J : Type*} (S : Finset J) {O₀ : Y.Opens} (s : J → Γ(Y, O₀)) (O : Y.Opens) :
    rsT (∑ a ∈ S, s a) O = ∑ a ∈ S, rsT (s a) O := by
  unfold rsT; split_ifs <;> simp

theorem pbT_add (f : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (s + t) O = pbT f s O + pbT f t O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_sub (f : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (s - t) O = pbT f s O - pbT f t O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_neg (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens) : pbT f (-s) O = -pbT f s O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_mul (f : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (s * t) O = pbT f s O * pbT f t O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_zero (f : Z ⟶ Y) {O₀ : Y.Opens} (O : Z.Opens) : pbT f (0 : Γ(Y, O₀)) O = 0 := by
  unfold pbT; split_ifs <;> simp

theorem pbT_one (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) : pbT f (1 : Γ(Y, O₀)) O = 1 := by
  rw [pbT_of_le f h, map_one]

theorem pbT_sum {J : Type*} (S : Finset J) (f : Z ⟶ Y) {O₀ : Y.Opens} (s : J → Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (∑ a ∈ S, s a) O = ∑ a ∈ S, pbT f (s a) O := by
  unfold pbT; split_ifs <;> simp

theorem rsT_self {O : Y.Opens} (s : Γ(Y, O)) : rsT s O = s := by
  rw [rsT_of_le le_rfl]
  simp [resG]

theorem rsT_rsT {O₀ O₁ O₂ : Y.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ O₁) (s : Γ(Y, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le h₁, rsT_of_le h₂, rsT_of_le (h₂.trans h₁)]
  exact (congrArg (fun φ => φ.hom s)
    (Y.presheaf.map_comp (homOfLE h₁).op (homOfLE h₂).op)).symm

theorem rsT_pbT (f : Z ⟶ Y) {O₀ : Y.Opens} {O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ f ⁻¹ᵁ O₀) (h₂ : O₂ ≤ O₁)
    (s : Γ(Y, O₀)) : rsT (pbT f s O₁) O₂ = pbT f s O₂ := by
  rw [pbT_of_le f h₁, rsT_of_le h₂, pbT_of_le f (h₂.trans h₁)]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_map f h₁ (homOfLE h₂).op)

theorem pbT_rsT (f : Z ⟶ Y) {O₀ O₁ : Y.Opens} {O₂ : Z.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁)
    (s : Γ(Y, O₀)) : pbT f (rsT s O₁) O₂ = pbT f s O₂ := by
  rw [rsT_of_le h₁, pbT_of_le f h₂, pbT_of_le f (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.map_appLE f h₂ (homOfLE h₁).op)

theorem rsT_constFn {R : Type} [CommRing R] (q : Y ⟶ Sp R) {O₀ O : Y.Opens} (h : O ≤ O₀) (a : R) :
    rsT (constFn q O₀ a) O = constFn q O a := by
  rw [rsT_of_le h]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := O₀) (fun _ _ => trivial) (homOfLE h).op)

theorem pbT_constFn {R : Type} [CommRing R] (q : Y ⟶ Sp R) (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) (a : R) : pbT f (constFn q O₀ a) O = constFn (f ≫ q) O a := by
  rw [pbT_of_le f h]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ O₀ O (fun _ _ => trivial) h)

theorem eq_of_rsT_eq {J : Type} (V : J → Y.Opens) {O : Y.Opens} (hV : ∀ k, V k ≤ O) (hc : O ≤ iSup V)
    (s t : Γ(Y, O)) (h : ∀ k, rsT s (V k) = rsT t (V k)) : s = t := by
  refine Y.sheaf.eq_of_locally_eq' V O (fun k => homOfLE (hV k)) hc s t fun k => ?_
  have := h k
  rw [rsT_of_le (hV k), rsT_of_le (hV k)] at this
  exact this

theorem exists_rsT_eq {J : Type} (V : J → Y.Opens) {O : Y.Opens} (hV : ∀ k, V k ≤ O) (hc : O ≤ iSup V)
    (s : ∀ k, Γ(Y, V k)) (h : ∀ k l, rsT (s k) (V k ⊓ V l) = rsT (s l) (V k ⊓ V l)) :
    ∃ t : Γ(Y, O), ∀ k, rsT t (V k) = s k := by
  obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing' V O (fun k => homOfLE (hV k)) hc s (fun k l => by
    have := h k l
    rw [rsT_of_le inf_le_left, rsT_of_le inf_le_right] at this
    exact this)
  exact ⟨t, fun k => (rsT_of_le (hV k) _).trans (ht k)⟩

theorem le_iSup_inf_preimage (f : Z ⟶ Y) {I : Type} (U : I → Y.Opens) (hU : ⨆ i, U i = ⊤) (O : Z.Opens) :
    O ≤ ⨆ k, O ⊓ f ⁻¹ᵁ U k := by
  intro x hx
  have : f x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩

end Basic

variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens}

theorem IsCob.add {c c' : C1 U} (h : IsCob U c) (h' : IsCob U c') : IsCob U (c + c') := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨b', hb'⟩ := h'
  refine ⟨fun i => b i + b' i, fun i j => ?_⟩
  simp only [Pi.add_apply, rsT_add, hb, hb']
  ring

theorem IsCob.sub {c c' : C1 U} (h : IsCob U c) (h' : IsCob U c') : IsCob U (c - c') := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨b', hb'⟩ := h'
  refine ⟨fun i => b i - b' i, fun i j => ?_⟩
  simp only [Pi.sub_apply, rsT_sub, hb, hb']
  ring

theorem isCob_lc (q : Y ⟶ Sp K) {g : ℕ} (a : Fin g → K) (c : Fin g → C1 U) (h : ∀ x, IsCob U (c x)) :
    IsCob U (lc q a c) := by
  choose b hb using h
  refine ⟨fun i => ∑ x, constFn q (U i) (a x) * b x i, fun i j => ?_⟩
  simp only [lc, rsT_sum, rsT_mul, hb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rsT_constFn q inf_le_left, rsT_constFn q inf_le_right]
  ring

theorem cohom_lc (q : Y ⟶ Sp K) (f : Y ⟶ Y) (hf : f ≫ q = q) {g : ℕ} (a : Fin g → K) (c c' : Fin g → C1 U)
    (h : ∀ x, Cohom f U (c x) (c' x)) : Cohom f U (lc q a c) (lc q a c') := by
  choose b hb hb' using h
  refine ⟨fun i k => ∑ x, constFn q (U i ⊓ f ⁻¹ᵁ U k) (a x) * b x i k, fun i i' k => ?_, fun i k k' => ?_⟩
  · simp only [lc, rsT_sum, rsT_mul, ← hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [rsT_constFn q (inf_le_inf_right _ inf_le_left), rsT_constFn q (inf_le_inf_right _ inf_le_right),
      rsT_constFn q inf_le_left]
    ring
  · simp only [lc, rsT_sum, rsT_mul, pbT_sum, pbT_mul, ← hb', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k' ≤ f ⁻¹ᵁ (U k ⊓ U k') := fun y hy => ⟨hy.1.2, hy.2⟩
    have e' : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k' ≤ U i ⊓ f ⁻¹ᵁ U k' := fun y hy => ⟨hy.1.1, hy.2⟩
    rw [rsT_constFn q inf_le_left, rsT_constFn q e', pbT_constFn q f e, hf]
    ring

theorem Cohom.isCob_sub (f : Y ⟶ Y) (hU : ⨆ i, U i = ⊤) {c c₁ c' c₁' : C1 U} (h : Cohom f U c c')
    (h₁ : Cohom f U c₁ c₁') (hc : IsCob U (c' - c₁')) : IsCob U (c - c₁) := by
  obtain ⟨b, hb, hb'⟩ := h
  obtain ⟨b₁, hb₁, hb₁'⟩ := h₁
  obtain ⟨β, hβ⟩ := hc
  have glue : ∀ i, ∃ t : Γ(Y, U i), ∀ k, rsT t (U i ⊓ f ⁻¹ᵁ U k) =
      b i k - b₁ i k + pbT f (β k) (U i ⊓ f ⁻¹ᵁ U k) := by
    intro i
    refine exists_rsT_eq (fun k => U i ⊓ f ⁻¹ᵁ U k) (fun k => inf_le_left)
      (le_iSup_inf_preimage f U hU _) _ fun k l => ?_
    have e : (U i ⊓ f ⁻¹ᵁ U k) ⊓ (U i ⊓ f ⁻¹ᵁ U l) ≤ U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l :=
      fun y hy => ⟨hy.1, hy.2.2⟩
    have e₁ : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l ≤ f ⁻¹ᵁ (U k ⊓ U l) := fun y hy => ⟨hy.1.2, hy.2⟩
    have e₂ : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l ≤ U i ⊓ f ⁻¹ᵁ U l := fun y hy => ⟨hy.1.1, hy.2⟩
    rw [← rsT_rsT inf_le_left e, ← rsT_rsT e₂ e]
    congr 1
    have k₀ := congrArg (fun s => pbT f s (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l)) (hβ k l)
    simp only [Pi.sub_apply, pbT_sub] at k₀
    rw [pbT_rsT f inf_le_right e₁, pbT_rsT f inf_le_left e₁, ← hb', ← hb₁'] at k₀
    simp only [rsT_add, rsT_sub]
    rw [rsT_pbT f inf_le_right inf_le_left, rsT_pbT f inf_le_right e₂]
    linear_combination k₀
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun k => U i ⊓ U j ⊓ f ⁻¹ᵁ U k) (fun k => inf_le_left)
    (le_iSup_inf_preimage f U hU _) _ _ fun k => ?_
  have e₁ : U i ⊓ U j ⊓ f ⁻¹ᵁ U k ≤ U i ⊓ f ⁻¹ᵁ U k := inf_le_inf_right _ inf_le_left
  have e₂ : U i ⊓ U j ⊓ f ⁻¹ᵁ U k ≤ U j ⊓ f ⁻¹ᵁ U k := inf_le_inf_right _ inf_le_right
  simp only [Pi.sub_apply, rsT_sub]
  rw [rsT_rsT inf_le_right inf_le_left, rsT_rsT inf_le_left inf_le_left,
    ← rsT_rsT inf_le_left e₂ (t j), ← rsT_rsT inf_le_left e₁ (t i), ht, ht, ← hb, ← hb₁]
  simp only [rsT_add, rsT_sub]
  rw [rsT_pbT f inf_le_right e₁, rsT_pbT f inf_le_right e₂]
  ring

end GlobalTheory.KS
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem levelFactor_comp {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ}
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (c : Fin n → ℤ) (u : Fin m) : π u (∏ i, P i ^ c i) = L (bas c u) := by
  let φ : Λ →+ Additive H := AddMonoidHom.mk' (fun x => Additive.ofMul (L x)) hL
  have hφ : ∀ x, L x = Additive.toMul (φ x) := fun x => rfl
  have hc : bas c u = ∑ i, c i • bas (Pi.single i 1) u := by
    conv_lhs => rw [← Finset.univ_sum_single c]

    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : (Pi.single i (c i) : Fin n → ℤ) = c i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [hs, map_zsmul, Pi.smul_apply]

  rw [map_prod, hc, hφ, map_sum, toMul_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, hP, map_zsmul, toMul_zsmul]
  rfl

theorem levelFactor_torsion {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (ht : ∀ i, P i ^ k = 1) (x : Λ) : L x ^ k = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, bas c = Pi.single u x := ⟨bas.symm (Pi.single u x), bas.apply_symm_apply _⟩
  have h1 := levelFactor_comp bas P π L hL hP c u
  rw [hc, Pi.single_eq_same] at h1
  have hk : ∀ i, (P i ^ c i) ^ k = 1 := fun i => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  rw [← h1, ← map_pow, ← Finset.prod_pow, Finset.prod_eq_one (fun i _ => hk i), map_one]

theorem levelFactor_bij {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (hk : 0 < k) (ht : ∀ i, P i ^ k = 1)
    (hπ : ∀ y : Fin m → H, ∃! x : G, ∀ u, π u x = y u)
    (hb : ∀ y : G, y ^ k = 1 → ∃! c : Fin n → ZMod k, (List.ofFn fun i => P i ^ (c i).val).prod = y) :
    (∀ x, L x = 1 ↔ ∃ y, x = k • y) ∧ ∀ y : H, y ^ k = 1 → ∃ x, L x = y := by
  have : NeZero k := ⟨hk.ne'⟩
  have hcomp := levelFactor_comp bas P π L hL hP
  have htor := levelFactor_torsion u bas P π L hL hP k ht
  have L0 : L 0 = 1 := mul_left_cancel (a := L 0) (by rw [← hL, add_zero, _root_.mul_one])
  have hsm : ∀ (j : ℕ) (x : Λ), L (j • x) = L x ^ j := by
    intro j x
    induction j with
    | zero => rw [zero_smul, L0, pow_zero]
    | succ j ih => rw [succ_nsmul, hL, ih, pow_succ]
  have hone : ∀ a : G, (∀ v, π v a = 1) → a = 1 := by
    intro a ha
    obtain ⟨x, -, hx⟩ := hπ (fun _ => 1)
    exact (hx a ha).trans (hx 1 (fun v => map_one _)).symm
  have hred : ∀ w : Fin n → ℤ,
      ∏ i, P i ^ w i = (List.ofFn fun i => P i ^ ((w i : ZMod k).val)).prod := by
    intro w
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_eq_zpow_emod (w i) (n := (k : ℤ)) (by rw [zpow_natCast]; exact ht i),
      ← ZMod.val_intCast, zpow_natCast]
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ : ∃ w, bas w = Pi.single u x := ⟨_, bas.apply_symm_apply _⟩
    have hg : ∏ i, P i ^ w i = 1 := hone _ fun v => by
      rw [hcomp, hw]
      by_cases hv : v = u
      · subst hv; rw [Pi.single_eq_same, hx]
      · rw [Pi.single_eq_of_ne hv, L0]
    obtain ⟨c0, -, huniq⟩ := hb 1 (one_pow _)
    have e1 := huniq (fun i => (w i : ZMod k)) ((hred w).symm.trans hg)
    have e2 := huniq 0 (by simp)
    have hdvd : ∀ i, (k : ℤ) ∣ w i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun (e1.trans e2.symm) i)
    choose w' hw' using hdvd
    have hww : w = (k : ℤ) • w' := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, hw' i]
    refine ⟨bas w' u, ?_⟩
    calc x = bas w u := by rw [hw, Pi.single_eq_same]
      _ = ((k : ℤ) • bas w') u := by rw [hww, map_zsmul]
      _ = k • bas w' u := by rw [Pi.smul_apply, natCast_zsmul]
  · rintro ⟨y, rfl⟩
    rw [hsm, htor]
  · obtain ⟨a, ha, -⟩ := hπ (Pi.mulSingle u y)
    have hak : a ^ k = 1 := hone _ fun v => by
      rw [map_pow, ha]
      by_cases hv : v = u
      · subst hv; rw [Pi.mulSingle_eq_same, hy]
      · rw [Pi.mulSingle_eq_of_ne hv, one_pow]
    obtain ⟨c, hc, -⟩ := hb a hak
    refine ⟨bas (fun i => ((c i).val : ℤ)) u, ?_⟩
    have hprod : ∏ i, P i ^ ((c i).val : ℤ) = a := by
      rw [← hc, List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => zpow_natCast _ _
    rw [← hcomp, hprod, ha, Pi.mulSingle_eq_same]

theorem level_on_factor_of_eighth_power : ∀ (h g : ℕ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), 0 < k → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → (∀ x, lev x ^ k = 1) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ S), (∀ x, (toUnit (Over.mk p) ≫ lev x = 1 ↔ ∃ y, x = k • y)) ∧ ∀ y : Over.mk p ⟶ A, y ^ k = 1 → ∃ x, toUnit _ ≫ lev x = y := by
  intro h g J bas k o _ b S s t A _ _ pr lev hk hpr huniv hlev hpt
  have hcomp : ∀ i u, t.pt i ≫ pr u = lev (bas (Pi.single i 1) u) := fun i u =>
    Over.OverMorphism.ext (hpt i u)
  have hinj : ∀ (T : Over S) (x y : T ⟶ t.A), (∀ u, x ≫ pr u = y ≫ pr u) → x = y :=
    fun T x y hxy => (huniv T (fun u => y ≫ pr u)).unique hxy (fun u => rfl)
  let cg : ∀ T : Over S, CommGroup (T ⟶ t.A) := fun T =>
    { (inferInstance : Group (T ⟶ t.A)) with
      mul_comm := fun x y => hinj T _ _ fun u => by
        have := hpr u
        rw [MonObj.mul_comp, MonObj.mul_comp, _root_.mul_comm] }
  let π : ∀ T : Over S, Fin 8 → ((T ⟶ t.A) →* (T ⟶ A)) := fun T u =>
    MonoidHom.mk' (fun x => x ≫ pr u) (fun x y => by
      have := hpr u
      exact MonObj.mul_comp x y (pr u))
  refine ⟨?_, fun K _ _ p => ?_⟩
  · letI := cg (Out.baseOver S)
    exact levelFactor_torsion (G := Out.baseOver S ⟶ t.A) (H := Out.baseOver S ⟶ A)
      (0 : Fin 8) bas t.pt (π _) lev hlev hcomp k t.torsion
  let T := Over.mk p
  letI := cg T
  let q : T ⟶ Out.baseOver S := Over.homMk p (by simp [T])
  let ρ : (Out.baseOver S ⟶ t.A) →* (T ⟶ t.A) :=
    MonoidHom.mk' (fun x => q ≫ x) (fun x y => MonObj.comp_mul q x y)
  have hq : toUnit T = q := toUnit_unique _ _
  refine levelFactor_bij (G := T ⟶ t.A) (0 : Fin 8) bas (fun i => q ≫ t.pt i) (π T)
    (fun x => toUnit T ≫ lev x) (fun x y => by rw [hlev, MonObj.comp_mul]) (fun i u => ?_) k hk
    (fun i => by
      have h1 := map_pow ρ (t.pt i) k
      rw [t.torsion, map_one] at h1
      exact h1.symm)
    (fun y => huniv T y) (fun y hy => t.bij K p y hy)
  show (q ≫ t.pt i) ≫ pr u = toUnit T ≫ lev (bas (Pi.single i 1) u)
  rw [Category.assoc, hcomp, hq]

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem abelianScheme_id_pow_finite_etale_surjective :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (m : ℕ), IsAbelianScheme A → IsUnit (m : Γ(S, ⊤)) → IsMonHom ((𝟙 A) ^ m) ∧ IsFinite ((𝟙 A) ^ m).left ∧ Etale ((𝟙 A) ^ m).left ∧ Surjective ((𝟙 A) ^ m).left := by
  intro S A _ m hA hm
  obtain ⟨⟩ := hA
  have hmon : ∀ n : ℕ, IsMonHom ((𝟙 A) ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Hom.one_def]; infer_instance
    | succ n ih => rw [pow_succ, Hom.mul_def]; infer_instance
  have hfin : IsFinite ((𝟙 A) ^ m).left := GrpTangent.isFinite_id_pow A hm
  have het : Etale ((𝟙 A) ^ m).left := GrpTangent.etale_id_pow A hm
  refine ⟨hmon m, hfin, het, ⟨fun x => ?_⟩⟩
  set f := ((𝟙 A) ^ m).left with hf

  have hcl : IsClopen (Set.range f) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩

  have hw : A.hom (f x) = A.hom x := by
    rw [← Scheme.Hom.comp_apply, hf, Over.w]

  have hsub : A.hom ⁻¹' {A.hom x} ⊆ Set.range f :=
    (A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected.subset_isClopen hcl
      ⟨f x, by simp [hw], Set.mem_range_self x⟩
  exact hsub rfl

end GlobalTheory
end

section

open Complex Matrix
open scoped ContDiff BigOperators Real

theorem _root_.GlobalTheory.T.exists_periodic_dbar_solution : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ w : Fin g → (Fin g → ℂ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ ∀ (l : Λ) z, w a (z + l) = w a z) → (∀ a b z, (fderiv ℝ (w b) z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ (w b) z (I • (Pi.single a 1 : Fin g → ℂ))) = (fderiv ℝ (w a) z (Pi.single b 1 : Fin g → ℂ) + I * fderiv ℝ (w a) z (I • (Pi.single b 1 : Fin g → ℂ)))) → ∃ (t : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (l : Λ) z, f (z + l) = f z) ∧ ∀ a z, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = w a z - t a := by
  first | exact @GlobalTheory.dbar_solve_complexTorus | exact GlobalTheory.dbar_solve_complexTorus | (intros; apply GlobalTheory.dbar_solve_complexTorus <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem fibPt_injective {X : Scheme.{0}} (G : Over X) {k : Type} [Field k] {y : Sp k ⟶ X} :
    Function.Injective (fibPt G (y := y)) := fun a b h => Over.OverMorphism.ext (by
  have := congrArg (· ≫ pullback.fst G.hom y) h
  simpa only [fibPt, pullback.lift_fst] using this)

end GlobalTheory.HeckePoint

namespace GlobalTheory

open HeckePoint

end GlobalTheory
end
end
