module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffMapDomainMul
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.UT.CancelHom

section
variable {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)}

theorem coeff_mapDomain_mul {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    (a : AddMonoidAlgebra F X') (c : AddMonoidAlgebra F X)
    (T : Finset X') (hT : a.coeff.support ⊆ T) (α : X) :
    (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α = ∑ χ ∈ T, a.coeff χ * c.coeff (α - h χ) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain, Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_mul]),
    Finsupp.sum_of_support_subset _ hT _ (by simp)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [neg_add_eq_sub]

theorem sumV_fibre {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X) (α : X)
    (f : X' → X → F) {s : F}
    (H : SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => f p.1.1 p.1.2) s) :
    SumV v (fun χ => f χ (α - h χ)) s := by
  classical
  let e : X' ≃ {p : X' × X // h p.1 + p.2 = α} :=
    { toFun := fun χ => ⟨(χ, α - h χ), by simp⟩
      invFun := fun p => p.1.1
      left_inv := fun χ => rfl
      right_inv := fun p => Subtype.ext (Prod.ext rfl (sub_eq_of_eq_add' p.2.symm)) }
  intro q
  obtain ⟨S, hS⟩ := H q
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.toEmbedding) (fun p hp => by
    rw [Finset.mem_map_equiv]
    exact hT (Finset.mem_map_of_mem _ hp))
  rw [Finset.sum_map] at this
  exact this

theorem val_sum_sub_coeff {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    {A : X' → F} {C : X → F}
    {a : AddMonoidAlgebra F X'} {c : AddMonoidAlgebra F X} {M N : ℚ}
    (hA : ∀ χ, (M : WithTop ℚ) ≤ v (A χ)) (hC : ∀ χ, (M : WithTop ℚ) ≤ v (C χ))
    (ha : ∀ χ, (N : WithTop ℚ) ≤ v (A χ - a.coeff χ)) (ha' : ∀ χ, v (A χ) ≤ v (a.coeff χ))
    (hc : ∀ χ, (N : WithTop ℚ) ≤ v (C χ - c.coeff χ))
    (T : Finset X') (hT : a.coeff.support ⊆ T) (α : X) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v (∑ χ ∈ T, A χ * C (α - h χ) -
      (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α) := by
  rw [coeff_mapDomain_mul h a c T hT, ← Finset.sum_sub_distrib]
  exact v.map_le_sum fun χ _ => val_mul_sub_mul (ha _) (hc _) (hC _) ((hA _).trans (ha' _))

theorem val_coeff_of_sumV {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    {A₁ A₂ : X' → F} {C₁ C₂ : X → F}
    {a₁ a₂ : AddMonoidAlgebra F X'} {c₁ c₂ : AddMonoidAlgebra F X} {M N : ℚ}
    (hA₁ : ∀ χ, (M : WithTop ℚ) ≤ v (A₁ χ)) (hA₂ : ∀ χ, (M : WithTop ℚ) ≤ v (A₂ χ))
    (hC₁ : ∀ χ, (M : WithTop ℚ) ≤ v (C₁ χ)) (hC₂ : ∀ χ, (M : WithTop ℚ) ≤ v (C₂ χ))
    (ha₁ : ∀ χ, (N : WithTop ℚ) ≤ v (A₁ χ - a₁.coeff χ)) (ha₁' : ∀ χ, v (A₁ χ) ≤ v (a₁.coeff χ))
    (ha₂ : ∀ χ, (N : WithTop ℚ) ≤ v (A₂ χ - a₂.coeff χ)) (ha₂' : ∀ χ, v (A₂ χ) ≤ v (a₂.coeff χ))
    (hc₁ : ∀ χ, (N : WithTop ℚ) ≤ v (C₁ χ - c₁.coeff χ))
    (hc₂ : ∀ χ, (N : WithTop ℚ) ≤ v (C₂ χ - c₂.coeff χ)) (α : X)
    (H : SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v ((AddMonoidAlgebra.mapDomainRingHom F h a₁ * c₂ -
      AddMonoidAlgebra.mapDomainRingHom F h a₂ * c₁).coeff α) := by
  classical
  obtain ⟨S, hS⟩ := sumV_fibre h α (fun x y => A₁ x * C₂ y - A₂ x * C₁ y) H (N + M)
  have h0 := hS (S ∪ (a₁.coeff.support ∪ a₂.coeff.support)) Finset.subset_union_left
  have h1 := val_sum_sub_coeff h hA₁ hC₂ ha₁ ha₁' hc₂ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_left.trans Finset.subset_union_right) α
  have h2 := val_sum_sub_coeff h hA₂ hC₁ ha₂ ha₂' hc₁ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_right.trans Finset.subset_union_right) α
  have h3 := v.map_le_sub (v.map_le_sub h2 h1) h0
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring
end

end GlobalTheory.UT.CancelHom

namespace GlobalTheory.UT

theorem sumV_cancel_hom : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (h : X' →+ X), Function.Injective h → ∀ (A₁ A₂ B₁ B₂ : X' → F) (C₁ C₂ : X → F), NullV v A₁ → NullV v A₂ → NullV v B₁ → NullV v B₂ → NullV v C₁ → NullV v C₂ → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0) → C₂ ≠ 0 → ∀ α, SumV v (fun χ : X' => B₁ χ * A₂ (α - χ) - B₂ χ * A₁ (α - χ)) 0 := by
  classical
  intro F _ v X X' _ _ _ _ _ _ h hinj A₁ A₂ B₁ B₂ C₁ C₂ nA₁ nA₂ nB₁ nB₂ nC₁ nC₂ HA HB hC α q
  obtain ⟨w, hw⟩ := exists_addGauss v X
  obtain ⟨χ₀, hχ₀⟩ := Function.ne_iff.mp hC
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (fun e => hχ₀ (v.top_iff.mp e) : v (C₂ χ₀) ≠ ⊤)
  obtain ⟨M₁, hM₁⟩ := nA₁.exists_lower
  obtain ⟨M₂, hM₂⟩ := nA₂.exists_lower
  obtain ⟨M₃, hM₃⟩ := nB₁.exists_lower
  obtain ⟨M₄, hM₄⟩ := nB₂.exists_lower
  obtain ⟨M₅, hM₅⟩ := nC₁.exists_lower
  obtain ⟨M₆, hM₆⟩ := nC₂.exists_lower
  obtain ⟨M, l1, l2, l3, l4, l5, l6⟩ : ∃ M : ℚ, M ≤ M₁ ∧ M ≤ M₂ ∧ M ≤ M₃ ∧ M ≤ M₄ ∧ M ≤ M₅ ∧ M ≤ M₆ :=
    ⟨min M₁ (min M₂ (min M₃ (min M₄ (min M₅ M₆)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  replace hM₁ := hM₁ M l1
  replace hM₂ := hM₂ M l2
  replace hM₃ := hM₃ M l3
  replace hM₄ := hM₄ M l4
  replace hM₅ := hM₅ M l5
  replace hM₆ := hM₆ M l6
  obtain ⟨N, n1, n2, n3⟩ : ∃ N : ℚ, m < N ∧ q + m ≤ M + (N + M) ∧ q ≤ N + M := by
    refine ⟨max (m + 1) (max (q + m - M - M) (q - M)), ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · have := (le_max_left (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
    · have := (le_max_right (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
  obtain ⟨a₁, ha₁, ha₁', -⟩ := nA₁.exists_trunc N
  obtain ⟨a₂, ha₂, ha₂', -⟩ := nA₂.exists_trunc N
  obtain ⟨b₁, hb₁, hb₁', -⟩ := nB₁.exists_trunc N
  obtain ⟨b₂, hb₂, hb₂', -⟩ := nB₂.exists_trunc N
  obtain ⟨c₁, hc₁, -, -⟩ := nC₁.exists_trunc N
  obtain ⟨c₂, hc₂, -, hc₂'⟩ := nC₂.exists_trunc N
  have EA := (hw _ _).mpr fun β =>
    CancelHom.val_coeff_of_sumV h hM₁ hM₂ hM₅ hM₆ ha₁ ha₁' ha₂ ha₂' hc₁ hc₂ β (HA β)
  have EB := (hw _ _).mpr fun β =>
    CancelHom.val_coeff_of_sumV h hM₃ hM₄ hM₅ hM₆ hb₁ hb₁' hb₂ hb₂' hc₁ hc₂ β (HB β)
  have push : ∀ (d : AddMonoidAlgebra F X') (g : WithTop ℚ),
      g ≤ w (AddMonoidAlgebra.mapDomainRingHom F h d) ↔ ∀ χ, g ≤ v (d.coeff χ) := by
    intro d g
    rw [hw, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
    refine ⟨fun H χ => ?_, fun H β => ?_⟩
    · have := H (h χ)
      rwa [Finsupp.mapDomain_apply_of_injective hinj] at this
    · by_cases hβ : β ∈ Set.range h
      · obtain ⟨χ, rfl⟩ := hβ
        rw [Finsupp.mapDomain_apply_of_injective hinj]
        exact H χ
      · rw [Finsupp.mapDomain_of_notMem_range _ _ hβ, v.map_zero]
        exact le_top
  set P := AddMonoidAlgebra.mapDomainRingHom F h with hP
  have key : ((q + m : ℚ) : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) + w c₂ := by
    have e : P (b₁ * a₂ - b₂ * a₁) * c₂ =
        P a₂ * (P b₁ * c₂ - P b₂ * c₁) - P b₂ * (P a₁ * c₂ - P a₂ * c₁) := by
      rw [map_sub, map_mul, map_mul]; ring
    rw [← w.map_mul, e]
    refine (WithTop.coe_le_coe.mpr n2).trans ?_
    rw [WithTop.coe_add]
    refine w.map_le_sub ?_ ?_ <;> rw [w.map_mul]
    · exact add_le_add ((push _ _).mpr fun χ => (hM₂ χ).trans (ha₂' χ)) EB
    · exact add_le_add ((push _ _).mpr fun χ => (hM₄ χ).trans (hb₂' χ)) EA
  have hc : w c₂ ≤ (m : WithTop ℚ) := by
    have := (hw c₂ _).mp le_rfl χ₀
    rwa [hc₂' χ₀ (by rw [← hm]; exact WithTop.coe_lt_coe.mpr n1), ← hm] at this
  have key2 : (q : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) := by
    have := key.trans (add_le_add le_rfl hc)
    rw [WithTop.coe_add] at this
    exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp this
  have key3 := (push _ _).mp key2 α
  refine ⟨b₁.coeff.support ∪ b₂.coeff.support, fun T hT => ?_⟩
  have h1 := CancelHom.val_sum_sub_coeff (AddMonoidHom.id X') hM₃ hM₂ hb₁ hb₁' ha₂ T
    (Finset.subset_union_left.trans hT) α
  have h2 := CancelHom.val_sum_sub_coeff (AddMonoidHom.id X') hM₄ hM₁ hb₂ hb₂' ha₁ T
    (Finset.subset_union_right.trans hT) α
  rw [AddMonoidAlgebra.mapDomainRingHom_id] at h1 h2
  simp only [RingHom.id_apply, AddMonoidHom.id_apply] at h1 h2
  have h3 := v.map_le_sub (v.map_le_sub ((WithTop.coe_le_coe.mpr n3).trans h2)
    ((WithTop.coe_le_coe.mpr n3).trans h1)) key3
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring

end GlobalTheory.UT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TorusCubTriv

open GlobalTheory GlobalTheory.UU GlobalTheory.EvenGenTorus TorusCube

theorem exists_cubTriv : ∀ (k : Type) [CommRing k], IsField k → ∀ (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (P₀ : GlobalTheory.UU.CP G₀) (i : splitTorus (Sp k) X ⟶ G₀), IsMonHom i → Nonempty (GlobalTheory.UU.CubTriv P₀.c i) := by
  intro k _ hk G₀ _ _ X _ _ _ P₀ i hi
  letI := hk.toField
  haveI := hi
  haveI : IsAffine (splitTorus (Sp k) X).left := isAffine_of_isAffineHom (splitTorus (Sp k) X).hom
  haveI := GlobalTheory.SS.LiftTorus.subsingleton_pic_torus k X
  obtain ⟨τ, hτ⟩ := GlobalTheory.LB.exists_isGen_of_subsingleton_pic_top
    (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb P₀.L.isLB (K := PUnit) (fun _ => i.left) (fun _ => 1))
  have e1 : (1 : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X).left ≫ i.left = (1 : splitTorus (Sp k) X ⟶ G₀).left := by
    rw [← Over.comp_left, MonObj.one_comp]
  obtain ⟨σ, hσ, vσ⟩ := exists_gen (φ' := ![i.left, (1 : splitTorus (Sp k) X ⟶ G₀).left]) (ε' := ![1, -1]) P₀.L.isLB
    (fun U _ h => (Fintype.prod_sum_type _).trans (by simp [Fin.prod_univ_two, e1]))
    (LB.mulGen _ _ _ _ _ τ (LB.invGen _ _ _ (LB.pullGen P₀.L.L (fun _ : PUnit => i.left) (fun _ => 1) τ
      (1 : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _)))
  have v : ∀ (T : Over (Sp k)) (x : T ⟶ splitTorus (Sp k) X) (z : T.left) (J), Good P₀.L.L z J →
      val σ x.left z J = val τ x.left z J * (val τ (1 : T ⟶ splitTorus (Sp k) X).left z J)⁻¹ := by
    intro T x z J hJ
    rw [vσ _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, MonObj.comp_one]
  refine ⟨⟨σ, hσ, fun T x y u z J hJ => ?_⟩⟩
  have a := cube k X G₀ i P₀.L P₀.c τ hτ T x y u z J hJ
  simp only [v T _ z J hJ]
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  simp only [ofMul_mul, ofMul_inv] at a' ⊢
  linear_combination (norm := abel) a'

end GlobalTheory.Mum.TorusCubTriv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PkgBaseChange
open GlobalTheory.UU

theorem surjective_of_cube {S' : Scheme.{0}} (G' : Over S') [GrpObj G']
    (h3 : Function.Surjective (G3 G').hom.appTop.hom) : Function.Surjective G'.hom.appTop.hom := by
  let s : G' ⟶ G3 G' := lift (𝟙 G') (lift 1 1)
  have hs : s.left ≫ (fst G' (G' ⊗ G')).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hw : s.left ≫ (G3 G').hom = G'.hom := Over.w s
  intro g
  obtain ⟨c, hc⟩ := h3 ((fst G' (G' ⊗ G')).left.appTop.hom g)
  refine ⟨c, ?_⟩
  have e1 : G'.hom.appTop.hom c = s.left.appTop.hom ((G3 G').hom.appTop.hom c) := by
    rw [← hw, Scheme.Hom.comp_appTop]; rfl
  have e2 : s.left.appTop.hom ((fst G' (G' ⊗ G')).left.appTop.hom g) = g := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]; rfl
  rw [e1, hc, e2]

theorem exists_isCPMap_of_lbIso : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f),
    (∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) →
    Function.Surjective (G3 G').hom.appTop.hom → ∀ (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G'),
    LBIso P'.L.L (P.L.L.pull F) → ∃ w, GlobalTheory.UU.IsCPMap P' P f F hw w := by
  intro S S' f G _ _ G' _ _ F hw mul h3 M M' ⟨w, hg⟩
  have h1 := surjective_of_cube G' h3
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP G' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio M'.L.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1)
    hr M'.L.rigGen
  let b : Γ(G'.left, ⊤)ˣ := pullU G'.hom ⊤ a
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB G'.hom (1 : 𝟙_ (Over S') ⟶ G').left (Over.w _) h1 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ G',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ G' (x3 G')) (ε := thε) (G3 G').hom
      (lift (1 : 𝟙_ (Over S') ⟶ G') (lift 1 1)).left (Over.w _) h3 c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨scaleGen b w, mul, scaleGen_isGen b hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
    ∀ x, W₀ x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : (T.left.presheaf.stalk z)ˣ, α = gm (Y := T.left) T.hom z ⊤ a := ⟨_, rfl⟩
  have e : ∀ x, W x = α * W₀ x := fun x => by
    have hm : x.left z ∈ (M.L.L.pull F).U (fun _ => J (x.left ≫ F)) ⊓ M'.L.L.U (J' x.left) :=
      ⟨mem_pull.2 (hJ (x.left ≫ F)), hJ' x.left⟩
    rw [hW, hW₀, hα, ← Over.w x]
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res x.left z le_top hm b).trans
      (gm_pull x.left G'.hom z ⊤ trivial a)) rfl)
  obtain ⟨a₁, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W₀ hW₀
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · refine a₁.trans ((congrArg (W₀ 1 * ·) (ha _ T.hom z J' hJ')).trans ?_)
    rw [e, hα, mul_comm _ (W₀ 1), _root_.mul_assoc]
  · have q : val M.sym (x.left ≫ F) z J * W₀ x = W₀ x⁻¹ * val M'.sym x.left z J' :=
      (a₂ x).trans (congrArg (W₀ x⁻¹ * ·) (es _ x.left z J' hJ'))
    rw [e, e, mul_left_comm, q, _root_.mul_assoc]
  · have q := (a₃ x y u).trans (congrArg (W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * ·) (ec T z J' hJ' x y u))
    simp only [e]
    apply Additive.ofMul.injective
    have q' := congrArg Additive.ofMul q
    simp only [ofMul_mul] at q' ⊢
    linear_combination (norm := abel) q'

end GlobalTheory.PkgBaseChange
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.Poinc.AdicTerm

theorem eq_zero_of_mem_pow_smul {V E : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    [AddCommGroup E] [Module V E] (N : Submodule V E) (hN : N.FG) (w : E)
    (h : ∀ n : ℕ, w ∈ maximalIdeal V ^ n • N) : w = 0 := by
  have hw : w ∈ N := Submodule.smul_le_right (h 0)
  haveI : Module.Finite V N := Module.Finite.iff_fg.mpr hN
  have hb := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  have hm : (⟨w, hw⟩ : N) ∈ (⨅ n : ℕ, maximalIdeal V ^ n • ⊤ : Submodule V N) := by
    rw [Submodule.mem_iInf]
    intro n
    exact (Submodule.mem_smul_top_iff _ N _).mpr (h n)
  rw [hb, Submodule.mem_bot] at hm
  exact congrArg Subtype.val hm

theorem sumI_smul {V E : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    [AddCommGroup E] [Module V E] {Ix : Type} (i₀ : Ix) (x : Ix → E) (y : Ix → V) (k v : E)
    (hx : ∀ i, x i = y i • k) (hy : ∀ i, i ≠ i₀ → y i ∈ maximalIdeal V)
    (hs : SumI (maximalIdeal V) x v) :
    ∃ S : V, v = S • k ∧ S - y i₀ ∈ maximalIdeal V := by
  classical
  obtain ⟨N, hN, -, -, hS⟩ := hs
  let P : Submodule V E := Submodule.map (LinearMap.toSpanSingleton V E k) (maximalIdeal V)
  have key : P.mkQ (v - y i₀ • k) = 0 := by
    refine eq_zero_of_mem_pow_smul (N.map P.mkQ) (hN.map _) _ fun n => ?_
    obtain ⟨S, hS⟩ := hS n
    have h1 := hS (insert i₀ S) (Finset.subset_insert _ _)
    have h2 : P.mkQ (v - ∑ i ∈ insert i₀ S, x i) ∈ maximalIdeal V ^ n • N.map P.mkQ := by
      rw [← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem h1
    have h3 : ∑ i ∈ (insert i₀ S).erase i₀, x i ∈ P := by
      refine Submodule.sum_mem _ fun i hi => ?_
      exact ⟨y i, hy i (Finset.ne_of_mem_erase hi), by simp [hx i]⟩
    have h4 : P.mkQ (∑ i ∈ (insert i₀ S).erase i₀, x i) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).mpr h3
    have h5 : v - y i₀ • k =
        (v - ∑ i ∈ insert i₀ S, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i := by
      rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S), hx i₀]
      abel
    rw [h5, map_add (f := _), h4, add_zero]
    exact h2
  obtain ⟨a, ha, hak⟩ := (Submodule.Quotient.mk_eq_zero P).mp key
  refine ⟨y i₀ + a, ?_, by simpa using ha⟩
  have hak' : a • k = v - y i₀ • k := by simpa using hak
  rw [add_smul, hak']
  abel

theorem sumF_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Ix : Type) (i₀ : Ix) (x : Ix → FractionRing V) (y : Ix → V) (κ v : FractionRing V), (∀ i, x i = κ * algebraMap V (FractionRing V) (y i)) → (∀ i, i ≠ i₀ → y i ∈ maximalIdeal V) → SumF (maximalIdeal V) (FractionRing V) x v → ∃ S : V, v = κ * algebraMap V (FractionRing V) S ∧ S - y i₀ ∈ maximalIdeal V := by
  intro V _ _ _ _ Ix i₀ x y κ v hx hy hs
  have h := @sumI_smul V (FractionRing V) _ _ _ _
    (Module.compHom (FractionRing V) (algebraMap V (FractionRing V))) Ix i₀ x y κ v
    (fun i => (hx i).trans (mul_comm _ _)) hy hs
  obtain ⟨S, h1, h2⟩ := h
  exact ⟨S, h1.trans (mul_comm _ _), h2⟩

end GlobalTheory.Poinc.AdicTerm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem exists_adic_sum_of_finsets {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {Ix : Type} (c : Ix → R) (S : ℕ → Finset Ix) (hmono : Monotone S)
    (hS : ∀ n i, i ∉ S n → c i ∈ I ^ n) :
    ∃ a : R, ∀ n, ∀ T : Finset Ix, S n ⊆ T → a - ∑ i ∈ T, c i ∈ I ^ n := by
  classical
  have key : ∀ n, ∀ T : Finset Ix, S n ⊆ T → ∑ i ∈ T, c i - ∑ i ∈ S n, c i ∈ I ^ n := by
    intro n T hT
    rw [← Finset.sum_sdiff hT, add_sub_cancel_right]
    exact Ideal.sum_mem _ fun i hi => hS n i (Finset.mem_sdiff.mp hi).2
  have hsm : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    simp
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance
    (f := fun n => ∑ i ∈ S n, c i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm, ← neg_mem_iff, neg_sub]
      exact key m _ (hmono hmn))
  refine ⟨a, fun n T hT => ?_⟩
  have h1 := ha n
  rw [SModEq.sub_mem, hsm] at h1
  have h2 := key n T hT
  have h3 := Ideal.add_mem _ h1 h2
  rw [← neg_mem_iff]
  convert h3 using 1
  ring

theorem exists_sumI_of_coeff {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {E : Type} [AddCommGroup E] [Module R E] {Jx : Type} [Fintype Jx] (g : Jx → E)
    {Ix : Type} (c : Ix → Jx → R) (h : ∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ I ^ n}.Finite) :
    ∃ s : E, GlobalTheory.UT.SumI I (fun i => ∑ k, c i k • g k) s := by
  classical
  have hmono : Monotone (fun n => (h n).toFinset) := by
    intro m n hmn i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun hk => hi fun k => Ideal.pow_le_pow_right hmn (hk k)
  have hS : ∀ k n i, i ∉ (h n).toFinset → c i k ∈ I ^ n := by
    intro k n i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    exact hi k
  choose a ha using fun k =>
    exists_adic_sum_of_finsets I (fun i => c i k) (fun n => (h n).toFinset) hmono (hS k)
  have hg : ∀ k, g k ∈ Submodule.span R (Set.range g) := fun k =>
    Submodule.subset_span ⟨k, rfl⟩
  refine ⟨∑ k, a k • g k, Submodule.span R (Set.range g),
    Submodule.fg_span (Set.finite_range g),
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k),
    fun i => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k),
    fun n => ⟨(h n).toFinset, fun T hT => ?_⟩⟩
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← Finset.sum_smul, ← sub_smul]
  exact Submodule.smul_mem_smul (ha k n T hT) (hg k)

theorem exists_sumF_of_coeff : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Jx : Type) [Fintype Jx] (g : Jx → F) (Ix : Type) (c : Ix → Jx → R), (∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ maximalIdeal R ^ n}.Finite) → ∃ s : F, GlobalTheory.UT.SumF (maximalIdeal R) F (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k) s := by
  intro R _ _ _ _ hc F _ _ Jx _ g Ix c h
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨s, hs⟩ := exists_sumI_of_coeff (maximalIdeal R) g c h
  refine ⟨s, ?_⟩
  have e : (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k)
      = fun i => ∑ k, c i k • g k := by
    funext i
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.smul_def]
    rfl
  rw [e]
  exact hs

end GlobalTheory.Mum
end
