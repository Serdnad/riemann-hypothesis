module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle171
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle172
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle161
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle169
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle166
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_action : GlobalTheory.CompanionTheory.GrForm.StAct := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stAct | exact GlobalTheory.CompanionTheory.GrForm.stAct | (intros; apply GlobalTheory.CompanionTheory.GrForm.stAct <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_exists_of_cocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle → GlobalTheory.CompanionTheory.GrForm.StExists := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.exists_of_cocycle | exact GlobalTheory.CompanionTheory.GrForm.exists_of_cocycle | (intros; apply GlobalTheory.CompanionTheory.GrForm.exists_of_cocycle <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_restrict : GlobalTheory.CompanionTheory.GrForm.StRes := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stRes | exact GlobalTheory.CompanionTheory.GrForm.stRes | (intros; apply GlobalTheory.CompanionTheory.GrForm.stRes <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_smul : GlobalTheory.CompanionTheory.GrForm.StSmul := by
  first | exact @GlobalTheory.CompanionTheory.GrFormSmul.stSmul | exact GlobalTheory.CompanionTheory.GrFormSmul.stSmul | (intros; apply GlobalTheory.CompanionTheory.GrFormSmul.stSmul <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_cocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stCocycle | exact GlobalTheory.CompanionTheory.GrForm.stCocycle | (intros; apply GlobalTheory.CompanionTheory.GrForm.stCocycle <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_vector_bundle : GlobalTheory.CompanionTheory.GrForm.StExists → GlobalTheory.CompanionTheory.GrForm.StAdd → GlobalTheory.CompanionTheory.GrForm.StSmul → GlobalTheory.CompanionTheory.GrForm.StRes → GlobalTheory.CompanionTheory.GrForm.StAct → GlobalTheory.CompanionTheory.GrForm.StLoc → GlobalTheory.CompanionTheory.GrForm.StVB := by
  first | exact @GlobalTheory.CompanionTheory.GrVB.main | exact GlobalTheory.CompanionTheory.GrVB.main | (intros; apply GlobalTheory.CompanionTheory.GrVB.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.smooth_pull_basis_filtration : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (a : A) (t u r : ℤ) (ht : t ≤ 0)
    (ha : (smO γ q l s 𝒱).LeC a (sFil _ t) (sFil _ 0)) (hb : (smO γ q l s 𝒱).LeC a (sFil _ u) (sFil _ r)) (j : ℕ)
    (x : HdR q j),
    ((smO γ q l s 𝒱).sqC a ha hb).pull j (GlobalTheory.CompanionTheory.BasisBase.zK q (TO q l s 𝒱) t u ht j x) =
      quoM (TS γ q l s 𝒱) r j (a • muB γ q l s 𝒱 j x) := by
  first | exact @GlobalTheory.CompanionTheory.BasisBase.sqC_zK | exact GlobalTheory.CompanionTheory.BasisBase.sqC_zK | (intros; apply GlobalTheory.CompanionTheory.BasisBase.sqC_zK <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem not_le_hyperplane {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) (r : ℕ)
    (t e : Fin r → R) (l : Fin r) (hI : Ideal.span (Set.range t) = I)
    (hz : ∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I →
      ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hl : IsUnit (e l)) :
    ¬ I ≤ IsLocalRing.maximalIdeal R * I ⊔
      Ideal.span (Set.range fun i => e l * t i - e i * t l) := by
  intro hle
  have htl : t l ∈ I := hI ▸ Ideal.subset_span ⟨l, rfl⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hle htl)
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hq
  simp only [smul_eq_mul] at hx
  let S : R := ∑ j, x j * e j
  let z : Fin r → R := fun i => -(x i * e l) + if i = l then 1 + S else 0
  have hsum : ∑ i, z i * t i = p := by
    have h1 : ∑ i, z i * t i = -(e l * ∑ i, x i * t i) + (1 + S) * t l := by
      simp only [z, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
      congr 1
      · congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : q = e l * ∑ i, x i * t i - S * t l := by
      rw [← hx]
      simp only [S, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    linear_combination h2 - hpq
  have hzm := hz z (hsum ▸ hp)
  have hxm : ∀ i, i ≠ l → x i ∈ IsLocalRing.maximalIdeal R := fun i hi => by
    have := hzm i
    simp only [z, if_neg hi, add_zero, neg_mem_iff] at this
    exact (Ideal.unit_mul_mem_iff_mem _ hl).1 (by rwa [mul_comm])
  have hS : S - x l * e l ∈ IsLocalRing.maximalIdeal R := by
    have : S - x l * e l = ∑ j ∈ Finset.univ.erase l, x j * e j := by
      have h5 : S = x l * e l + ∑ j ∈ Finset.univ.erase l, x j * e j :=
        (Finset.add_sum_erase _ (fun j => x j * e j) (Finset.mem_univ l)).symm
      rw [h5]
      ring
    rw [this]
    exact Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ (hxm j (Finset.ne_of_mem_erase hj))
  have h3 := hzm l
  simp only [z, if_true] at h3
  have h4 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    have : (1 : R) = (-(x l * e l) + (1 + S)) - (S - x l * e l) := by ring
    rw [this]
    exact Ideal.sub_mem _ h3 hS
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top h4

theorem corrected_compat {R B : Type} [CommRing R] [CommRing B] (c : R →+* B) (I m J : Ideal R)
    (hIm : I ≤ m) (hmI : m * I ≤ J) (r : ℕ) (t e : Fin r → R) (l : Fin r) (a' : R)
    (ha : a' * e l = 1) (ht : ∀ i, t i ∈ I) (hJ : ∀ i, e l * t i - e i * t l ∈ J)
    (ua uc g βa βc : B) (b : Fin r → B)
    (hD : ua - g * uc * (1 + ∑ i, c (t i) * b i) ∈ (m * I).map c)
    (hQ : ∑ i, c (e i) * b i - (βa - βc) ∈ m.map c) :
    ua * (1 - c (a' * t l) * βa) - g * (uc * (1 - c (a' * t l) * βc)) ∈ J.map c := by
  have hII : I * I ≤ J := (Ideal.mul_mono_left hIm).trans hmI
  have hIm' : I * m ≤ J := by rwa [mul_comm]
  have hE : c (a' * t l) ∈ I.map c := Ideal.mem_map_of_mem _ (I.mul_mem_left _ (ht l))
  have hT : ∑ i, c (t i) * b i ∈ I.map c :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ht i))
  have hTE : (∑ i, c (t i) * b i) * c (a' * t l) ∈ J.map c :=
    Ideal.map_mono hII (by rw [Ideal.map_mul]; exact Ideal.mul_mem_mul hT hE)
  have hEQ : c (a' * t l) * (∑ i, c (e i) * b i - (βa - βc)) ∈ J.map c :=
    Ideal.map_mono hIm' (by rw [Ideal.map_mul]; exact Ideal.mul_mem_mul hE hQ)
  have hP : ∑ i, c (a' * (e l * t i - e i * t l)) * b i ∈ J.map c :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ (J.mul_mem_left _ (hJ i)))
  have hDJ := Ideal.map_mono hmI hD
  have hT' : ∑ i, c (t i) * b i = ∑ i, c (a' * (e l * t i - e i * t l)) * b i +
      c (a' * t l) * ∑ i, c (e i) * b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : c a' * c (e l) = 1 := by rw [← map_mul, ha, map_one]
    simp only [map_mul, map_sub]
    linear_combination (-(c (t i) * b i)) * h1
  generalize hTd : ∑ i, c (t i) * b i = T at *
  generalize hPd : ∑ i, c (a' * (e l * t i - e i * t l)) * b i = P at *
  generalize hSd : ∑ i, c (e i) * b i = Sg at *
  generalize c (a' * t l) = E at *
  have key : ua * (1 - E * βa) - g * (uc * (1 - E * βc)) =
      (ua - g * uc * (1 + T)) * (1 - E * βa) +
        g * uc * (P + E * (Sg - (βa - βc)) - T * E * βa) := by
    rw [hT']; ring
  rw [key]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hDJ) (Ideal.mul_mem_left _ _
    (Ideal.sub_mem _ (Ideal.add_mem _ hP hEQ) (Ideal.mul_mem_right _ _ hTE)))

theorem exists_correction : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (I : Ideal R) (r : ℕ) (t : Fin r → R),
    Ideal.span (Set.range t) = I → I ≤ IsLocalRing.maximalIdeal R →
    (∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I → ∀ i, x i ∈ IsLocalRing.maximalIdeal R) →
    ∀ (M : LB X) (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u w : ∀ a, Γ(X, V a))
      (b : Fin r → ∀ a c, Γ(X, V a ⊓ V c)) (e : Fin r → R) (β : ∀ a, Γ(X, V a)) (l : Fin r),
      (∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a)) →
      (∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
        (1 + ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * b i a c) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a ⊓ V c)) →
      IsUnit (e l) →
      (∀ a c, ∑ i, GlobalTheory.SmallExtLift.cst s _ (e i) * b i a c - (rs X inf_le_left (β a) - rs X inf_le_right (β c)) ∈
        ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c)) →
      ∃ (J : Ideal R) (y z : ∀ a, Γ(X, V a)), ¬ I ≤ J ∧ (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
        ∀ a c, rs X inf_le_left (y a) - tr M V j hj a c * rs X inf_le_right (y c) ∈ ext s J (V a ⊓ V c) := by
  intro R _ _ X s I r t hI hIm hz M A V j hj u w b e β l huw hD hl hQ
  obtain ⟨a', ha'⟩ := hl.exists_left_inv
  have hrs : ∀ {U W : X.Opens} (h : W ≤ U) (x : R),
      rs X h (GlobalTheory.SmallExtLift.cst s U x) = GlobalTheory.SmallExtLift.cst s W x := fun {U W} h x =>
    GlobalTheory.SmallExtLift.gr_ext fun y hy => by
      rw [GlobalTheory.SmallExtLift.gr_res, GlobalTheory.SmallExtLift.gr_cst, GlobalTheory.SmallExtLift.gr_cst]
  have hmJ : IsLocalRing.maximalIdeal R * I ≤ IsLocalRing.maximalIdeal R * I ⊔
      Ideal.span (Set.range fun i => e l * t i - e i * t l) := le_sup_left
  refine ⟨IsLocalRing.maximalIdeal R * I ⊔ Ideal.span (Set.range fun i => e l * t i - e i * t l),
    fun a => u a * (1 - GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a),
    fun a => w a * (1 + GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a),
    not_le_hyperplane I r t e l hI hz hl, fun a => ?_, fun a c => ?_⟩
  · have htl : t l ∈ I := hI ▸ Ideal.subset_span ⟨l, rfl⟩
    have hE2 : GlobalTheory.SmallExtLift.cst s (V a) (a' * t l) * GlobalTheory.SmallExtLift.cst s (V a) (a' * t l) ∈
        ext s (IsLocalRing.maximalIdeal R * I ⊔
          Ideal.span (Set.range fun i => e l * t i - e i * t l)) (V a) := by
      rw [← map_mul]
      refine Ideal.mem_map_of_mem _ (hmJ ?_)
      exact Ideal.mul_mem_mul (hIm (I.mul_mem_left _ htl)) (I.mul_mem_left _ htl)
    have h1 := Ideal.map_mono hmJ (huw a)
    have key : u a * (1 - GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a) *
        (w a * (1 + GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a)) - 1 =
        (u a * w a - 1) - (u a * w a * β a * β a) * (GlobalTheory.SmallExtLift.cst s (V a) (a' * t l) *
          GlobalTheory.SmallExtLift.cst s (V a) (a' * t l)) := by ring
    rw [key]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ hE2)
  · have := corrected_compat (GlobalTheory.SmallExtLift.cst s (V a ⊓ V c)) I (IsLocalRing.maximalIdeal R) _
      hIm hmJ r t e l a' ha' (fun i => hI ▸ Ideal.subset_span ⟨i, rfl⟩)
      (fun i => Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
      (rs X inf_le_left (u a)) (rs X inf_le_right (u c)) (tr M V j hj a c)
      (rs X inf_le_left (β a)) (rs X inf_le_right (β c)) (fun i => b i a c) (hD a c) (hQ a c)
    simpa only [map_mul, map_sub, map_one, hrs] using this

end GlobalTheory.CompanionTheory.FewEq
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq.Cochain

theorem triple_mem {B : Type*} [CommRing B] {𝔞 𝔟 : Ideal B} (h𝔟 : 𝔟 * 𝔟 ≤ 𝔞) (h𝔞 : 𝔞 ≤ 𝔟)
    {ua uc ud wc wd g₁ g₂ g₃ h₁ h₂ h₃ : B} (hc : uc * wc - 1 ∈ 𝔞) (hd : ud * wd - 1 ∈ 𝔞)
    (e₁ : ua - g₁ * uc ∈ 𝔟) (e₂ : uc - g₂ * ud ∈ 𝔟) (hg : g₁ * g₂ = g₃)
    (i₁ : g₁ * h₁ = 1) (i₂ : g₂ * h₂ = 1) (i₃ : g₃ * h₃ = 1) :
    (ua - g₁ * uc) * h₁ * wc + (uc - g₂ * ud) * h₂ * wd - (ua - g₃ * ud) * h₃ * wd ∈ 𝔞 := by
  have hh : h₃ = h₁ * h₂ := by
    subst hg
    linear_combination (-(h₃ * g₂ * h₂)) * i₁ - h₃ * i₂ + (h₁ * h₂) * i₃
  have hm : wc - h₂ * wd ∈ 𝔟 := by
    have : wc - h₂ * wd = (wd * h₂) * (uc * wc - 1) - (wc * wd * h₂) * (uc - g₂ * ud)
        - wc * (ud * wd - 1) := by
      linear_combination (-(wc * wd * ud)) * i₂
    rw [this]
    exact 𝔟.sub_mem (𝔟.sub_mem (𝔟.mul_mem_left _ (h𝔞 hc)) (𝔟.mul_mem_left _ e₂))
      (𝔟.mul_mem_left _ (h𝔞 hd))
  have : (ua - g₁ * uc) * h₁ * wc + (uc - g₂ * ud) * h₂ * wd - (ua - g₃ * ud) * h₃ * wd =
      h₁ * ((ua - g₁ * uc) * (wc - h₂ * wd)) := by
    subst hg hh
    linear_combination ((uc - g₂ * ud) * h₂ * wd) * (-i₁)
  rw [this]
  exact 𝔞.mul_mem_left _ (h𝔟 (Ideal.mul_mem_mul e₁ hm))

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem rs_cst (s : X ⟶ Sp R) {U W : X.Opens} (h : W ≤ U) (x : R) :
    rs X h (GlobalTheory.SmallExtLift.cst s U x) = GlobalTheory.SmallExtLift.cst s W x := by
  refine GlobalTheory.SmallExtLift.gr_ext fun y hy => ?_
  have e := GlobalTheory.SmallExtLift.gr_res (𝟙 X) y h hy (GlobalTheory.SmallExtLift.cst s U x)
  exact e.trans (by rw [GlobalTheory.SmallExtLift.gr_cst, GlobalTheory.SmallExtLift.gr_cst])

theorem rs_mem_ext (s : X ⟶ Sp R) (J : Ideal R) {U W : X.Opens} (h : W ≤ U) {x : Γ(X, U)}
    (hx : x ∈ ext s J U) : rs X h x ∈ ext s J W := by
  have e : (ext s J U).map (rs X h) = ext s J W := by
    rw [ext, ext, Ideal.map_map]
    congr 1
    exact RingHom.ext fun r => rs_cst s h r
  exact e ▸ Ideal.mem_map_of_mem _ hx

theorem ext_eq_span (s : X ⟶ Sp R) {I : Ideal R} {r : ℕ} {t : Fin r → R}
    (ht : Ideal.span (Set.range t) = I) (U : X.Opens) :
    ext s I U = Ideal.span (Set.range fun i => GlobalTheory.SmallExtLift.cst s U (t i)) := by
  rw [ext, ← ht, Ideal.map_span, ← Set.range_comp]
  rfl

theorem sum_cst_rs (s : X ⟶ Sp R) {r : ℕ} (t : Fin r → R) {U W : X.Opens} (h : W ≤ U)
    (f : Fin r → Γ(X, U)) :
    ∑ i, GlobalTheory.SmallExtLift.cst s W (t i) * rs X h (f i) =
      rs X h (∑ i, GlobalTheory.SmallExtLift.cst s U (t i) * f i) := by

  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, rs_cst]

theorem exists_cochain : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (𝔪 I : Ideal R) (r : ℕ) (t : Fin r → R),
    Ideal.span (Set.range t) = I → I ≤ 𝔪 → ∀ (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u w : ∀ a, Γ(X, V a)),
      (∀ a, u a * w a - 1 ∈ ext s (𝔪 * I) (V a)) →
      (∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) ∈ ext s I (V a ⊓ V c)) →
      ∃ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
        (∀ a c d, ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * (rs X (le₁₂ V a c d) (b i a c) +
            rs X (le₂₃ V a c d) (b i c d) - rs X (le₁₃ V a c d) (b i a d)) ∈ ext s (𝔪 * I) (V a ⊓ V c ⊓ V d)) ∧
        ∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
          (1 + ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * b i a c) ∈ ext s (𝔪 * I) (V a ⊓ V c) := by
  intro R _ X s 𝔪 I r t ht hI M hM A V j hj u w huw he
  have key : ∀ a c, ∃ b0 : Fin r → Γ(X, V a ⊓ V c),
      ∑ i, b0 i * GlobalTheory.SmallExtLift.cst s _ (t i) =
        rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) := by
    intro a c
    have := he a c
    rw [ext_eq_span s ht] at this
    exact (Ideal.mem_span_range_iff_exists_fun).1 this
  choose b0 hb0 using key
  have hT : ∀ a c, ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) *
      (b0 a c i * trInv M V j hj a c * rs X inf_le_right (w c)) =
      (rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
        trInv M V j hj a c * rs X inf_le_right (w c) := by
    intro a c
    rw [← hb0, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨fun i a c => b0 a c i * trInv M V j hj a c * rs X inf_le_right (w c), ?_, ?_⟩
  · intro a c d
    have h𝔟 : ∀ U : X.Opens, ext s I U * ext s I U ≤ ext s (𝔪 * I) U := fun U => by
      rw [ext, ← Ideal.map_mul]
      exact Ideal.map_mono (Ideal.mul_mono_left hI)
    have h𝔞 : ∀ U : X.Opens, ext s (𝔪 * I) U ≤ ext s I U := fun U =>
      Ideal.map_mono Ideal.mul_le_right
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_cst_rs, hT]
    have i₁ := congrArg (rs X (le₁₂ V a c d)) (tr_mul_trInv M V j hj a c)
    have i₂ := congrArg (rs X (le₂₃ V a c d)) (tr_mul_trInv M V j hj c d)
    have i₃ := congrArg (rs X (le₁₃ V a c d)) (tr_mul_trInv M V j hj a d)
    rw [map_mul, map_one] at i₁ i₂ i₃
    have hU : ∀ x {W : X.Opens} (h : W ≤ V x),
        rs X h (u x) * rs X h (w x) - 1 ∈ ext s (𝔪 * I) W := fun x W h => by
      simpa only [map_sub, map_mul, map_one] using rs_mem_ext s (𝔪 * I) h (huw x)
    have := triple_mem (h𝔟 (V a ⊓ V c ⊓ V d)) (h𝔞 _)
      (hU c (inf_le_left.trans inf_le_right)) (hU d inf_le_right)
      (by simpa only [map_sub, map_mul, GlobalTheory.AbLaw.rs_rs] using rs_mem_ext s I (le₁₂ V a c d) (he a c))
      (by simpa only [map_sub, map_mul, GlobalTheory.AbLaw.rs_rs] using rs_mem_ext s I (le₂₃ V a c d) (he c d))
      (tr_cocycle hM V j hj a c d) i₁ i₂ i₃
    simpa only [map_sub, map_mul, map_add (f := _), map_one, GlobalTheory.AbLaw.rs_rs] using this
  · intro a c
    simp only [hT]
    have hx := rs_mem_ext s (𝔪 * I) (inf_le_right : V a ⊓ V c ≤ V c) (huw c)
    rw [map_sub, map_mul, map_one] at hx
    have e : rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
        (1 + (rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
          trInv M V j hj a c * rs X inf_le_right (w c)) =
        -(rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
          (rs X inf_le_right (u c) * rs X inf_le_right (w c) - 1) := by
      linear_combination (-(rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
        rs X inf_le_right (u c) * rs X inf_le_right (w c)) * tr_mul_trInv M V j hj a c
    rw [e]
    exact Ideal.mul_mem_left _ _ hx

end GlobalTheory.CompanionTheory.FewEq.Cochain
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq.FibreRed

open GlobalTheory.SmallExtLift

theorem app_eq_zero_of_mem_ext {R : Type} [CommRing R] [IsLocalRing R] {X Y : Scheme.{0}}
    {s : X ⟶ Sp R} {ι : Y ⟶ X} {f : Y ⟶ Sp (IsLocalRing.ResidueField R)}
    (w : ι ≫ s = f ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) (U : X.Opens)
    {z : Γ(X, U)} (hz : z ∈ ext s (IsLocalRing.maximalIdeal R) U) : (ι.app U).hom z = 0 := by
  have key : Ideal.map (GlobalTheory.SmallExtLift.cst s U) (IsLocalRing.maximalIdeal R) ≤
      RingHom.ker (ι.app U).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, GlobalTheory.SmallExtLift.app_cst w U r,
      (IsLocalRing.residue_eq_zero_iff r).mpr hr, map_zero]
  exact key hz

private theorem app_rs_eq_rs_app {X Y : Scheme.{0}} (φ : Y ⟶ X) {U W : X.Opens} (h : W ≤ U)
    (h' : φ ⁻¹ᵁ W ≤ φ ⁻¹ᵁ U) (x : Γ(X, U)) :
    (φ.app W).hom (rs X h x) = rs Y h' ((φ.app U).hom x) := by
  have := congrArg (fun q => q.hom x) (φ.naturality (homOfLE h).op)
  exact this

theorem dep_fibre : DepSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s →
    ∀ n r : ℕ, n < r →
    (∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ X),
      IsPullback φ s' s (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
      Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
        Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ n) →
    ∀ (A : Type) (V : A → X.Opens), ⨆ a, V a = ⊤ → (∀ a, IsAffineOpen (V a)) →
    ∀ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
      (∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d)) →
      ∃ (e : Fin r → R) (β : ∀ a, Γ(X, V a)), (∃ l, IsUnit (e l)) ∧ ∀ a c,
        ∑ i, GlobalTheory.SmallExtLift.cst s _ (e i) * b i a c - (rs X inf_le_left (β a) - rs X inf_le_right (β c)) ∈
          ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c) := by
  intro hD R _ _ X s hs n r hnr hfib A V hV hVa b hb
  let g := spMap (algebraMap R (IsLocalRing.ResidueField R))
  let φ := pullback.fst s g
  let s' := pullback.snd s g
  have hpb : IsPullback φ s' s g := IsPullback.of_hasPullback _ _
  have hpb' : IsPullback φ s' s (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) := hpb
  have hw : φ ≫ s = s' ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := hpb.w
  have hsurj : Function.Surjective (IsLocalRing.residue R) := Ideal.Quotient.mk_surjective
  obtain ⟨hfin, hrank⟩ := hfib _ s' φ hpb
  have hSp : ∀ (T : Type) [CommRing T], (Sp T).IsSeparated := fun T _ => by unfold Sp; infer_instance
  haveI hXsep : X.IsSeparated := ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  haveI hsep : (pullback s g).IsSeparated := ⟨by rw [← terminal.comp_from s']; infer_instance⟩
  haveI hg : IsAffineHom g := by
    show IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
    infer_instance
  haveI haff : IsAffineHom φ := MorphismProperty.pullback_fst (P := @IsAffineHom) s g hg
  let V' : A → (pullback s g).Opens := fun a => φ ⁻¹ᵁ V a
  have hV' : ⨆ a, V' a = ⊤ := by
    have h1 : ⨆ a, V' a = φ ⁻¹ᵁ (⨆ a, V a) := (TopologicalSpace.Opens.map_iSup φ.base V).symm
    rw [h1, hV]
    rfl
  have hV'a : ∀ a, IsAffineOpen (V' a) := fun a => (hVa a).preimage φ
  let α : Fin r → ∀ a c, Γ(pullback s g, V' a ⊓ V' c) := fun i a c => (φ.app (V a ⊓ V c)).hom (b i a c)
  have hα : ∀ i a c d, rs _ (le₁₂ V' a c d) (α i a c) + rs _ (le₂₃ V' a c d) (α i c d) =
      rs _ (le₁₃ V' a c d) (α i a d) := by
    intro i a c d
    have h0 := app_eq_zero_of_mem_ext hw (V a ⊓ V c ⊓ V d) (hb i a c d)
    rw [map_sub, map_add (f := _), app_rs_eq_rs_app φ (le₁₂ V a c d) (le₁₂ V' a c d),
      app_rs_eq_rs_app φ (le₂₃ V a c d) (le₂₃ V' a c d), app_rs_eq_rs_app φ (le₁₃ V a c d) (le₁₃ V' a c d)] at h0
    exact sub_eq_zero.mp h0
  obtain ⟨c, ψ, hc0, hcψ⟩ := hD (IsLocalRing.ResidueField R) (pullback s g) s' hsep n r hfin hrank hnr A V'
    hV' hV'a α hα
  choose e he using fun i => hsurj (c i)
  choose β hβ using fun a => app_surj hsurj hpb' (hVa a) (ψ a)
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hc0
  have hlu : IsUnit (e l) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [he l]; exact hl)
  refine ⟨e, β, ⟨l, hlu⟩, fun a c' => ?_⟩
  show _ ∈ Ideal.map (cst s (V a ⊓ V c')) (IsLocalRing.maximalIdeal R)
  rw [← IsLocalRing.ker_residue]
  apply mem_of_app_eq_zero hsurj hpb' ((hVa a).inf (hVa c'))

  rw [map_sub, map_sum, map_sub, app_rs_eq_rs_app φ inf_le_left (inf_le_left : V' a ⊓ V' c' ≤ V' a),
  app_rs_eq_rs_app φ inf_le_right (inf_le_right : V' a ⊓ V' c' ≤ V' c'), hβ, hβ]
  simp only [map_mul, app_cst hw, he]
  exact sub_eq_zero.mpr (hcψ a c')

end GlobalTheory.CompanionTheory.FewEq.FibreRed
end
end
