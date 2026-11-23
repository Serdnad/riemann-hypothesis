module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenEmbeddingCompOfSumMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericEighthPowerUniformisedIsPolarised
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatVAlg
open GlobalTheory.KS GlobalTheory.HeatGlue

variable {Y X : Scheme.{0}}

theorem pbT_id {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : pbT (𝟙 Y) s O = rsT s O := by
  rw [pbT_of_le (𝟙 Y) h, rsT_of_le h]
  rfl

theorem cst_eq (π : Y ⟶ X) (V : X.Opens) {O : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (r : Γ(X, V)) :
    GlobalTheory.HeatV.cst π V h r = pbT π r O := (pbT_of_le π h r).symm

theorem rsT_unit {O₀ O : Y.Opens} (h : O ≤ O₀) (w : Γ(Y, O₀)ˣ) : rsT w.val O * rsT w⁻¹.val O = 1 := by
  rw [← rsT_mul, Units.mul_inv, rsT_one h]

theorem rsT_cocycle (L : LB Y) (hL : L.IsLB) (i j k : L.ι) {O : Y.Opens} (hO : O ≤ L.U i ⊓ L.U j ⊓ L.U k) :
    rsT (L.g i j).val O * rsT (L.g j k).val O = rsT (L.g i k).val O := by
  have e := congrArg (fun u : Γ(Y, L.U i ⊓ L.U j ⊓ L.U k)ˣ => rsT u.val O) (hL.cocycle i j k)
  simp only [Units.val_mul, rsT_mul] at e
  have r : ∀ {V V' : Y.Opens} (h : V' ≤ V) (u : Γ(Y, V)ˣ), O ≤ V' →
      rsT (ReciprocityTheory.ChartRestriction.G.Semi.res h u).val O = rsT u.val O := fun h u hO' => by
    show rsT (resG Y h u.val) O = _
    rw [← rsT_of_le h, rsT_rsT h hO']
  rw [r _ _ hO, r _ _ hO, r _ _ hO] at e
  exact e

theorem exists_heatV : ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) (V : X.Opens) (L : LB Y), L.IsLB → IsUnit (2 : Γ(X, V)) → ∀ (n : ℕ) (dd : Fin n → Fld Y), (∀ a, IsField ⊤ (dd a)) → (∀ a O (h : O ≤ π ⁻¹ᵁ V) (r : Γ(X, V)), dd a O (GlobalTheory.HeatV.cst π V h r) = 0) → ∀ (Θ : Matrix (Fin n) (Fin n) Γ(X, V)), Θᵀ = Θ → ∀ (J : Type) (W : J → Y.Opens) (j : J → L.ι) (d : J → Fld Y) (hW : ∀ i, W i ≤ π ⁻¹ᵁ V), (∀ i, W i ≤ L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i i' O (h : O ≤ W i ⊓ W i') (f : Γ(Y, O)), d i O f - d i' O f = ∑ a, ∑ b, GlobalTheory.HeatV.cst π V (h.trans (inf_le_left.trans (hW i))) (Θ a b) * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) * dd a O f) → (∀ z : C1 W, IsCoc W z → ∃ (cc : Fin n → Γ(X, V)) (y : ∀ i, Γ(Y, W i)), ∀ i i', z i i' = ∑ b, GlobalTheory.HeatV.cst π V (inf_le_left.trans (hW i)) (cc b) * (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) + (rsT (y i') (W i ⊓ W i') - rsT (y i) (W i ⊓ W i'))) → ∃ (e u : Fin n → Γ(X, V)) (pf pf' : ∀ i, Γ(Y, W i)), ∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(Y, O)), GlobalTheory.HeatV.opV π V dd Θ u (fun O' f' => d i O' f' + ∑ a, pbT π (e a) O' * dd a O' f') (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 Y) (L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 Y) (L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV π V dd Θ u (fun O' f' => d i' O' f' + ∑ a, pbT π (e a) O' * dd a O' f') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f := by
  intro Y X π V L hL h2 n dd hddF _hddC Θ hΘ J W j d hW hWL hdF hKS hH1
  simp only [cst_eq] at hKS hH1
  have hdd : ∀ a (O : Y.Opens), IsDer (dd a O) := fun a O => isDer_of_isField (hddF a) le_top
  obtain ⟨t, ht⟩ : ∃ t : Γ(X, V), 2 * t = 1 := ⟨_, h2.mul_val_inv⟩
  have hc2 : ∀ O : Y.Opens, O ≤ π ⁻¹ᵁ V → 2 * pbT π t O = 1 := fun O hO => by
    have e := congrArg (fun s => pbT π s O) ht
    simp only [pbT_mul, pbT_one π hO] at e
    rw [show (2 : Γ(X, V)) = 1 + 1 from one_add_one_eq_two.symm, pbT_add, pbT_one π hO, one_add_one_eq_two] at e
    exact e
  have hs : ∀ (O : Y.Opens) a b, pbT π (Θ a b) O = pbT π (Θ b a) O := fun O a b => by
    rw [show Θ a b = Θᵀ b a from rfl, hΘ]
  have hV2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → O ≤ π ⁻¹ᵁ V := fun i i' O h => h.trans (inf_le_left.trans (hW i))
  have hm2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → O ≤ L.U (j i) ⊓ L.U (j i') := fun i i' O h =>
    le_inf (h.trans (inf_le_left.trans (hWL i))) (h.trans (inf_le_right.trans (hWL i')))
  have hm3 : ∀ i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → O ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    fun i i' i'' O h => le_inf (le_inf (h.trans (inf_le_left.trans (inf_le_left.trans (hWL i))))
      (h.trans (inf_le_left.trans (inf_le_right.trans (hWL i'))))) (h.trans (inf_le_right.trans (hWL i'')))
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin n → J → J → ∀ O : Y.Opens, Γ(Y, O), ∀ b i i' O,
      φ b i i' O = dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O := ⟨_, fun _ _ _ _ => rfl⟩
  have rφ : ∀ b i i' (O₁ O : Y.Opens), O₁ ≤ W i ⊓ W i' → O ≤ O₁ → rsT (φ b i i' O₁) O = φ b i i' O := by
    intro b i i' O₁ O h1 h
    rw [hφ, hφ, rsT_mul, ← field_rsT (hddF b) le_top h, rsT_rsT (hm2 i i' O₁ h1) h, rsT_rsT (hm2 i i' O₁ h1) h]
  have dlc : ∀ i i' i'' (O : Y.Opens) (δ : Γ(Y, O) → Γ(Y, O)), IsDer δ → O ≤ W i ⊓ W i' ⊓ W i'' →
      δ (rsT (L.g (j i) (j i'')).val O) * rsT (L.g (j i) (j i''))⁻¹.val O =
        δ (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O +
        δ (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O := by
    intro i i' i'' O δ hδ hO
    have h3 := hm3 i i' i'' O hO
    exact hδ.dlog_mul (rsT_unit (h3.trans inf_le_left) _)
      (rsT_unit (le_inf (h3.trans (inf_le_left.trans inf_le_right)) (h3.trans inf_le_right)) _)
      (rsT_unit (le_inf (h3.trans (inf_le_left.trans inf_le_left)) (h3.trans inf_le_right)) _)
      (rsT_cocycle L hL _ _ _ h3)
  have cφ : ∀ b i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' ⊓ W i'' →
      φ b i i'' O = φ b i i' O + φ b i' i'' O := fun b i i' i'' O hO => by
    rw [hφ, hφ, hφ]; exact dlc i i' i'' O _ (hdd b O) hO
  have ks : ∀ i i' i'' (O : Y.Opens), O ≤ W i ⊓ W i' →
      d i O (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O =
        d i' O (rsT (L.g (j i') (j i'')).val O) * rsT (L.g (j i') (j i''))⁻¹.val O +
        ∑ a, ∑ b, pbT π (Θ a b) O * φ b i i' O * φ a i' i'' O := fun i i' i'' O hO => by
    rw [← sub_eq_iff_eq_add', ← sub_mul, hKS i i' O hO, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hφ, hφ]; ring

  obtain ⟨z₁, hz₁⟩ : ∃ z : C1 W, ∀ i i', z i i' =
      -(pbT π t (W i ⊓ W i') * ∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i') *
          dd a (W i ⊓ W i') (φ b i i' (W i ⊓ W i'))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z : C1 W, ∀ i i', z i i' =
      d i (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i') -
        pbT π t (W i ⊓ W i') * ∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i') *
          φ a i i' (W i ⊓ W i') * φ b i i' (W i ⊓ W i') := ⟨_, fun _ _ => rfl⟩
  have rz₁ : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → rsT (z₁ i i') O =
      -(pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * dd a O (φ b i i' O)) := by
    intro i i' O hO
    have e : ∀ a b, rsT (dd a (W i ⊓ W i') (φ b i i' (W i ⊓ W i'))) O = dd a O (φ b i i' O) := fun a b => by
      rw [← field_rsT (hddF a) le_top hO, rφ b i i' _ O le_rfl hO]
    rw [hz₁]
    simp only [rsT_neg, rsT_mul, rsT_sum, rsT_pbT π (hV2 i i' _ le_rfl) hO, e]
  have rz₂ : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' → rsT (z₂ i i') O =
      d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * φ a i i' O * φ b i i' O := by
    intro i i' O hO
    have e : ∀ b, rsT (φ b i i' (W i ⊓ W i')) O = φ b i i' O := fun b => rφ b i i' _ O le_rfl hO
    rw [hz₂]
    simp only [rsT_sub, rsT_mul, rsT_sum, rsT_pbT π (hV2 i i' _ le_rfl) hO, e]
    rw [← field_rsT (hdF i) inf_le_left hO, rsT_rsT (hm2 i i' _ le_rfl) hO, rsT_rsT (hm2 i i' _ le_rfl) hO]
  have tri : ∀ i i' i'', (W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ∧ (W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ∧
      (W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') :=
    fun _ _ _ => ⟨inf_le_left, le_inf (inf_le_left.trans inf_le_right) inf_le_right,
      le_inf (inf_le_left.trans inf_le_left) inf_le_right⟩
  have coc₁ : IsCoc W z₁ := by
    intro i i' i''
    obtain ⟨t1, t2, t3⟩ := tri i i' i''
    rw [rz₁ i i' _ t1, rz₁ i' i'' _ t2, rz₁ i i'' _ t3]
    have e := fun b => cφ b i i' i'' _ le_rfl
    simp only [e, (hdd _ _).1, mul_add, Finset.sum_add_distrib]
    ring
  have coc₂ : IsCoc W z₂ := by
    intro i i' i''
    obtain ⟨t1, t2, t3⟩ := tri i i' i''
    rw [rz₂ i i' _ t1, rz₂ i' i'' _ t2, rz₂ i i'' _ t3]
    have e := fun b => cφ b i i' i'' _ le_rfl
    simp only [e]
    rw [dlc i i' i'' _ _ (isDer_of_isField (hdF i) (t1.trans inf_le_left)) le_rfl, ks i i' i'' _ t1,
      quad_add (hs _) (fun a => φ a i i' _) (fun a => φ a i' i'' _)]
    linear_combination (∑ a, ∑ b, pbT π (Θ a b) (W i ⊓ W i' ⊓ W i'') * φ b i i' _ * φ a i' i'' _) *
      hc2 _ (hV2 i i' _ t1)
  obtain ⟨c, y₁, hy₁⟩ := hH1 z₁ coc₁
  obtain ⟨e, y₂, hy₂⟩ := hH1 z₂ coc₂
  have A1 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' →
      rsT (y₁ i') O - rsT (y₁ i) O = -(pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * dd a O (φ b i i' O)) -
        ∑ b, pbT π (c b) O * φ b i i' O := by
    intro i i' O hO
    have h := congrArg (fun s => rsT s O) (hy₁ i i')
    simp only [rz₁ i i' O hO, rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_pbT π (hV2 i i' _ le_rfl) hO,
      rsT_rsT inf_le_left hO, rsT_rsT inf_le_right hO] at h
    have e' : ∀ b, rsT (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
        rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) O = φ b i i' O := fun b => by
      rw [← hφ, rφ b i i' _ O le_rfl hO]
    simp only [← rsT_mul, e'] at h
    linear_combination -h
  have A2 : ∀ i i' (O : Y.Opens), O ≤ W i ⊓ W i' →
      rsT (y₂ i') O - rsT (y₂ i) O = d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        pbT π t O * ∑ a, ∑ b, pbT π (Θ a b) O * φ a i i' O * φ b i i' O - ∑ b, pbT π (e b) O * φ b i i' O := by
    intro i i' O hO
    have h := congrArg (fun s => rsT s O) (hy₂ i i')
    simp only [rz₂ i i' O hO, rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_pbT π (hV2 i i' _ le_rfl) hO,
      rsT_rsT inf_le_left hO, rsT_rsT inf_le_right hO] at h
    have e' : ∀ b, rsT (dd b (W i ⊓ W i') (rsT (L.g (j i) (j i')).val (W i ⊓ W i')) *
        rsT (L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) O = φ b i i' O := fun b => by
      rw [← hφ, rφ b i i' _ O le_rfl hO]
    simp only [← rsT_mul, e'] at h
    linear_combination -h
  refine ⟨fun a => -e a, fun a => -c a, y₂, y₁, ?_⟩
  intro k i i' O h f
  have hO : O ≤ π ⁻¹ᵁ V := hV2 i i' O h
  rw [pbT_id (hm2 i i' O h)]
  have hg := rsT_unit (hm2 i i' O h) (L.g (j i) (j i'))
  have hdi : IsDer (fun f : Γ(Y, O) => d i O f + ∑ a, pbT π (-e a) O * dd a O f) := by
    have h1 := isDer_of_isField (hdF i) (h.trans inf_le_left)
    refine ⟨fun x y => ?_, fun x y => ?_⟩
    · simp only [h1.1, (hdd _ O).1, mul_add, Finset.sum_add_distrib]
      ring
    · have s : ∑ a, pbT π (-e a) O * (x * dd a O y + y * dd a O x) =
          x * ∑ a, pbT π (-e a) O * dd a O y + y * ∑ a, pbT π (-e a) O * dd a O x := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      simp only [h1.2, (hdd _ O).2, s]
      ring
  have key := ringOp_conj hdi (fun a => hdd a O) (Θ := Θ.map (GlobalTheory.HeatV.cst π V hO))
    (fun a b => by show GlobalTheory.HeatV.cst π V hO (Θ a b) = GlobalTheory.HeatV.cst π V hO (Θ b a)
                   rw [show Θ a b = Θᵀ b a from rfl, hΘ])
    (fun a => GlobalTheory.HeatV.cst π V hO (-c a)) (rsT (y₂ i) O) (rsT (y₁ i) O) hg k f
  refine key.trans ?_
  congr 1
  have F1 := hKS i i' O h f
  have F2 := A2 i i' O h
  have F3 := A1 i i' O h
  simp only [hφ] at F2 F3
  simp only [ringOp, GlobalTheory.HeatV.opV, Matrix.map_apply, cst_eq]
  have E : (d i O (rsT (L.g (j i) (j i')).val O) + ∑ a, pbT π (-e a) O * dd a O (rsT (L.g (j i) (j i')).val O)) *
      rsT (L.g (j i) (j i'))⁻¹.val O = d i O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O -
        ∑ b, pbT π (e b) O * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) := by
    rw [add_mul, Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun b _ => by rw [pbT_neg]; ring
  have U1 : ∑ a, pbT π (-c a) O * (dd a O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) =
      -∑ b, pbT π (c b) O * (dd b O (rsT (L.g (j i) (j i')).val O) * rsT (L.g (j i) (j i'))⁻¹.val O) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [pbT_neg]; ring
  rw [E, U1]
  set g := rsT (L.g (j i) (j i')).val O
  set gi := rsT (L.g (j i) (j i'))⁻¹.val O
  linear_combination (2 * (k : Γ(Y, O))) * F1 +
    (k : Γ(Y, O)) ^ 2 * f * (-2 * F2 + (∑ a, ∑ b, pbT π (Θ a b) O * (dd a O g * gi) * (dd b O g * gi)) * hc2 O hO) +
    (k : Γ(Y, O)) * f * (-2 * F3 + (∑ a, ∑ b, pbT π (Θ a b) O * dd a O (dd b O g * gi)) * hc2 O hO)

end GlobalTheory.HeatVAlg
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.polarisation_value_spaces_generic_point_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (j₀ : P.A.L.ι) (q : FractionRing Ω), ⊤ ≤ ξ ⁻¹ᵁ P.A.L.U j₀ ∧ q ≠ 0 ∧ ∀ (k : ℕ) (s : FractionRing Ω), 1 ≤ k → (GlobalTheory.HeatSym.VS φ t.PP.L x' g k s ↔ ∃ σ : SecM (𝟙 P.A.A.left) P.A.L k, s = q ^ k * valR ξ _ (σ.f fun _ => j₀)) := by
  first | exact @GlobalTheory.HeatSym.vs_iff_generic | exact GlobalTheory.HeatSym.vs_iff_generic | (intros; apply GlobalTheory.HeatSym.vs_iff_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTQuotRigid

theorem objMap_comp_φ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem eq_one_of_fixes_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N h M : ℕ), 3 ≤ N → N.Coprime p → 0 < M →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
      (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
      IsSympLev u.P h M (zetaAway M) s₁ lev → ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : sympSimGrp h M), y ≫ ρ a = y → a = 1 := by
  intro p _ D R _ b N h M hN hNp hM X s s₁ u lev hlev ρ hρ k _ _ y a hya
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨-, -, m, hm⟩ := hρ a
  obtain ⟨o, ⟨n⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N X (Sp k) s y u
  obtain ⟨c, hc⟩ := objMap_comp_φ n m
  have key : ∀ (f : Sp k ⟶ X), f = y → ∀ mm : ObjMap o u f, mm.φ = n.φ := by
    intro f hf mm
    subst hf
    exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp _ _ _ _ _ _ _ mm n
  have hφ : n.φ ≫ m.φ = n.φ := by rw [← hc]; exact key _ hya c

  have hx : ∀ x, y ≫ (sympTwist a lev x).left = y ≫ (lev x).left := by
    intro x
    have ht : (y ≫ (sympTwist a lev x).left) ≫ u.A.hom = 𝟙 (Sp k) ≫ y := by
      rw [Category.assoc, Over.w]
      rfl
    have hσ := n.cart.1.lift_fst (y ≫ (sympTwist a lev x).left) (𝟙 _) ht
    have e1 : (y ≫ (sympTwist a lev x).left) ≫ m.φ = y ≫ (lev x).left := by
      rw [Category.assoc, hm x, ← Category.assoc, hya]
    rw [← e1, ← hσ, Category.assoc, hφ]

  let β : cycAway M →+* k := (Spec.preimage (y ≫ s₁)).hom
  have hβ : y ≫ s₁ = spMap β := by
    change y ≫ s₁ = Spec.map (CommRingCat.ofHom (Spec.preimage (y ≫ s₁)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hpow : β (zetaAway M) ^ M = 1 := by rw [← map_pow, zetaAway_pow_self hM.ne', map_one]
  let z : kˣ := Units.ofPowEqOne _ M hpow hM.ne'
  have hcl := (hlev.2.2 k y β z hβ rfl).1
  have hunit : ∀ x, (toUnit (Over.mk y) ≫ lev x).left = y ≫ (lev x).left := by
    intro x
    rw [Over.comp_left]
    congr 1
  have hfix : ∀ x, (a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x) =
      reduceMod M x := by
    intro x
    set c := liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x))
    have hsame : toUnit (Over.mk y) ≫ lev c = toUnit (Over.mk y) ≫ lev x := by
      ext1
      rw [hunit, hunit]
      exact hx x
    have hsplit : lev c = lev (c - x) * lev x := by rw [← hlev.1, sub_add_cancel]
    have h1 : toUnit (Over.mk y) ≫ lev (c - x) = 1 := by
      rw [hsplit, comp_mul] at hsame
      exact mul_eq_right.1 hsame
    obtain ⟨d, hd⟩ := (hcl (c - x)).1 h1
    have hr : reduceMod M c = reduceMod M x := by
      have : c = x + M • d := by rw [← hd]; abel
      rw [this]
      funext i
      simp [reduceMod]
    exact (reduceMod_liftMod _).symm.trans hr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have := hfix (liftMod v)
  rw [reduceMod_liftMod] at this
  exact this

end GlobalTheory.HTQuotRigid
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.smoothNeighbourhood_translates_cover_group : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u) → ∀ p : G'.left, ∃ j, p ∈ Set.range (N.chart x j) := by
  first | exact @GlobalTheory.Mum.chart_cover | exact GlobalTheory.Mum.chart_cover | (intros; apply GlobalTheory.Mum.chart_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nearOpenPullbackToSelfProduct_surjective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (N : Near π G'), Surjective (Desc.UT N).hom := by
  first | exact @GlobalTheory.Mum.Desc.surjective_UT_hom | exact GlobalTheory.Mum.Desc.surjective_UT_hom | (intros; apply GlobalTheory.Mum.Desc.surjective_UT_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isMonHom_of_sumMap_comp_fixing_nearOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' → IsMonHom φ := by
  first | exact @GlobalTheory.Mum.DescHom.isMonHom_of_sum_of_emb | exact GlobalTheory.Mum.DescHom.isMonHom_of_sum_of_emb | (intros; apply GlobalTheory.Mum.DescHom.isMonHom_of_sum_of_emb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.descentDatum_carries_translateChart : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, N.Pt (𝟙 S) (π ≫ a i) (x i).left) → ∀ φ, N.Datum φ → ∀ (j : Option (Fin n)) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback N.U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback G'.hom (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ N.chart x j → z ≫ pullback.snd _ _ = s → z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = y₂ ≫ N.chart x j := by
  first | exact @GlobalTheory.Mum.Near.datum_chart | exact GlobalTheory.Mum.Near.datum_chart | (intros; apply GlobalTheory.Mum.Near.datum_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nearOpenEmbedding_comp_of_sumMap_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' := by
  first | exact @GlobalTheory.Mum.DescFix.emb_comp_of_sum_comp | exact GlobalTheory.Mum.DescFix.emb_comp_of_sum_comp | (intros; apply GlobalTheory.Mum.DescFix.emb_comp_of_sum_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsionLabelings_eq_of_thetaPoint_pairings_order_n : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (n j m : ℕ), n.Prime → Odd n → m = n ^ j * (n ^ 2) ^ 2 → ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < m → ∀ (x₁ x₂ : QkPt D (Kb R) (m ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D A (m ^ 2) x₁ → LabTors D A (m ^ 2) x₂ → (∀ p, x₁ p ^ n = 1 → x₂ p = x₁ p) → ∀ v : QkPt D (Kb R) (m ^ 2) → Kb R, IsThetaPt A m x₁ (fun p => GlobalTheory.Ex.fnOf (v p)) → IsThetaPt A m x₂ (fun p => GlobalTheory.Ex.fnOf (v p)) → ∀ p, x₂ p = x₁ p := by
  first | exact @GlobalTheory.Mum.LabelRigid.labels_eq | exact GlobalTheory.Mum.LabelRigid.labels_eq | (intros; apply GlobalTheory.Mum.LabelRigid.labels_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_polAV_generic_fibre_e8LB : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ (A : PolAV (Sp (FractionRing V₁))) (gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  first | exact @GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen | exact GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen | (intros; apply GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.generic_eighth_power_uniformised_is_polarised : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ P.A, IsMonHom gen.hom ∧ LBIso (P.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  first | exact @GlobalTheory.SharpGen.gen_eighthPower | exact GlobalTheory.SharpGen.gen_eighthPower | (intros; apply GlobalTheory.SharpGen.gen_eighthPower <;> assumption)
end
