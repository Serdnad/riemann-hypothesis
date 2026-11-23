module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle004
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.MonPeriods

theorem exists_isMonomial_levelOne : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {W : Type}
    [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (t : SAB H (Sp W))
    (P : PELUnif (maximalIdeal W) t), ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] := by
  intro E _ _ _ H W _ _ _ hW ϖ hϖ t P
  obtain ⟨hdvr, hcomp, hchar⟩ := hW
  haveI := hdvr
  haveI := hcomp
  haveI := hchar
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W P.D inferInstance χ).1).imp fun _ h => h.1
  have hv : ∀ χ, HasVal ϖ (algebraMap W (FractionRing W) (hex χ).choose) (Q χ) := fun χ =>
    GlobalTheory.ValForm.hasVal_coord (hQ χ) (hex χ).choose_spec
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  have hbal : ∀ (x : 𝓞 E) a b, QForm.bOf P.D.toPre Q (x • a) b = QForm.bOf P.D.toPre Q a (H.bar x • b) := by
    intro x a b
    obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance P.D.toPre P.oD x a b (hex (x • a + b)).choose_spec
      (hex (x • a)).choose_spec (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec
      (hex (H.bar x • b)).choose_spec
    have h1 := hasVal_mul_unit (GlobalTheory.ValForm.hasVal_mul hϖ (GlobalTheory.ValForm.hasVal_mul hϖ (hv (x • a + b)) (hv a))
      (hv (H.bar x • b))) u
    have h2 := GlobalTheory.ValForm.hasVal_mul hϖ (GlobalTheory.ValForm.hasVal_mul hϖ (hv (a + H.bar x • b)) (hv (x • a))) (hv b)
    rw [← map_mul, _root_.mul_comm, hu] at h1
    have := hasVal_unique hϖ h1 h2
    simp only [QForm.bOf]
    linarith
  let be : LinearMap.BilinForm ℤ P.D.toPre.X :=
    LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D hQ' a b)
      (fun a a' b => by simp only [map_add (f := _), AddMonoidHom.add_apply])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul])
      (fun a b b' => by simp only [map_add (f := _)])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul])
  have hbe : ∀ a b, be a b = QForm.bOf P.D.toPre Q a b := fun _ _ => rfl
  refine ⟨be, ⟨fun y z => ?_, fun a y z => ?_, fun y z => by simp⟩, fun y => ?_⟩
  · rw [hbe, hbe, QForm.bOf_comm]
  · rw [hbe, hbe]
    exact hbal a y z
  · obtain ⟨u, hu⟩ := hv y
    set r := (hex y).choose with hr
    have hn : (((Q y).toNat : ℕ) : ℤ) = Q y := Int.toNat_of_nonneg (h0 y)
    have e : r = ↑u * ϖ ^ (Q y).toNat := by
      apply IsFractionRing.injective W (FractionRing W)
      rw [hu, map_mul, map_pow, _root_.mul_comm, ← zpow_natCast, hn]
    refine ⟨u, fun _ => (Q y).toNat, fun i => ?_, ?_⟩
    · fin_cases i
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ', hn]
    · have hc : PsiCoord P.D.toPre y r := (hex y).choose_spec
      rw [e] at hc
      simpa using hc

end GlobalTheory.MonPeriods
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem formallyUnramified_residue_comp_of_isEtaleCompletion :
    ∀ (k : Type) [Field k] (m e : ℕ) [CharZero (ChartRing k m e)] {A : Type} [CommRing A] [IsLocalRing A]
      (φ : A →+* ChartRing k m e), IsEtaleCompletion φ → ((residue (ChartRing k m e)).comp φ).FormallyUnramified := by
  intro k _ m e _ A _ _ φ hφ
  obtain ⟨-, hmax, hfin⟩ := hφ
  haveI : IsLocalHom φ := by
    constructor
    intro a ha
    by_contra hna
    have h1 : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hna
    have h2 : φ a ∈ maximalIdeal (ChartRing k m e) := hmax ▸ Ideal.mem_map_of_mem φ h1
    exact (mem_maximalIdeal _).1 h2 ha
  rw [← ResidueField.map_comp_residue]
  refine RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective) ?_
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  haveI : CharZero k := RingHom.charZero (algebraMap k (ChartRing k m e))
  haveI : CharZero (ResidueField (ChartRing k m e)) :=
    (RingHom.charZero_iff ((residue (ChartRing k m e)).comp (algebraMap k (ChartRing k m e))).injective).1 inferInstance
  haveI : CharZero (ResidueField A) := RingHom.charZero (ResidueField.map φ)
  letI := (ResidueField.map φ).toAlgebra
  haveI : Module.Finite (ResidueField A) (ResidueField (ChartRing k m e)) := hfin'
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField (ChartRing k m e)) := inferInstance
  exact Algebra.FormallyUnramified.of_isSeparable _ _

end GlobalTheory.GenFan
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.Member

theorem isEtaleCompletion_comp_bijective' {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion φ) : IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

theorem isEtaleCompletion_stalkClosedPointTo_comp_iso : ∀ {R : Type} [CommRing R] [IsLocalRing R] {X Y : Scheme.{0}} (ξ : Spec (CommRingCat.of R) ⟶ X) (g : X ⟶ Y) [IsIso g], IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → IsEtaleCompletion (Scheme.stalkClosedPointTo (ξ ≫ g)).hom := by
  intro R _ _ X Y ξ g _ h
  have hb : Function.Bijective (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp]
  exact isEtaleCompletion_comp_bijective' _ hb _ h

end GlobalTheory.Member
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.RedTh

def siegelGlueMat {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (s + m)) (Fin (s + m)) ℝ := fun i j =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun x => Fin.addCases (motive := fun _ => ℝ) (fun y => a x y) (fun _ => 0) j)
    (fun x => Fin.addCases (motive := fun _ => ℝ) (fun _ => 0) (fun y => b x y) j) i

@[simp] lemma siegelGlueMat_ll {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin s) : siegelGlueMat a b (Fin.castAdd m x) (Fin.castAdd m y) = a x y := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_lr {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin s) (y : Fin m) : siegelGlueMat a b (Fin.castAdd m x) (Fin.natAdd s y) = 0 := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_rl {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m) (y : Fin s) : siegelGlueMat a b (Fin.natAdd s x) (Fin.castAdd m y) = 0 := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_rr {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m) : siegelGlueMat a b (Fin.natAdd s x) (Fin.natAdd s y) = b x y := by
  simp [siegelGlueMat]

lemma gram_apply_glue {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    gram d u i j = ∑ k, u k i * d k * u k j := by
  simp only [gram]
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal]

lemma siegelGlue_scale {s m : ℕ} (d₁ : Fin s → ℝ) (d₂ : Fin m → ℝ) (h₁ : ∀ i, 0 < d₁ i)
    (h₂ : ∀ i, 0 < d₂ i) :
    ∃ t : ℝ, 0 < t ∧ ∀ (i : Fin s) (j : Fin m), (j : ℕ) = 0 → t * d₁ i ≤ 4 * d₂ j := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨1, one_pos, fun _ j => j.elim0⟩
  · set j0 : Fin m := ⟨0, hm⟩
    have hS : 0 ≤ ∑ i, d₁ i := Finset.sum_nonneg (fun i _ => (h₁ i).le)
    refine ⟨d₂ j0 / (1 + ∑ i, d₁ i), div_pos (h₂ j0) (by linarith), fun i j hj => ?_⟩
    have hj' : j = j0 := Fin.ext hj
    subst hj'
    have hi : d₁ i ≤ ∑ k, d₁ k := Finset.single_le_sum (fun k _ => (h₁ k).le) (Finset.mem_univ i)
    have hpos : 0 < 1 + ∑ k, d₁ k := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have := h₂ j0
    nlinarith

lemma isSiegel_glue {s m : ℕ} {e₁ : Fin s → ℝ} {u₁ : Matrix (Fin s) (Fin s) ℝ} {e₂ : Fin m → ℝ}
    {u₂ : Matrix (Fin m) (Fin m) ℝ} (h₁ : IsSiegel e₁ u₁) (h₂ : IsSiegel e₂ u₂)
    (hj : ∀ (i : Fin s) (j : Fin m), (j : ℕ) = 0 → e₁ i ≤ 4 * e₂ j) :
    IsSiegel (Fin.append e₁ e₂) (siegelGlueMat u₁ u₂) := by
  refine IsSiegel.mk ?_ ?_ ?_ ?_ ?_
  · intro i
    induction i using Fin.addCases with
    | left a => simpa using h₁.nonneg a
    | right a => simpa using h₂.nonneg a
  · intro p q h
    induction p using Fin.addCases with
    | left a =>
      induction q using Fin.addCases with
      | left b =>
        simp only [Fin.val_castAdd] at h
        simpa using h₁.step a b h
      | right b =>
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        have := a.isLt
        simpa using hj a b (by omega)
    | right a =>
      induction q using Fin.addCases with
      | left b =>
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        have := b.isLt
        omega
      | right b =>
        simp only [Fin.val_natAdd] at h
        simpa using h₂.step a b (by omega)
  · intro i
    induction i using Fin.addCases with
    | left a => simpa using h₁.diag a
    | right a => simpa using h₂.diag a
  · intro i j h
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [siegelGlueMat_ll]
        exact h₁.lower a b (by rw [Fin.lt_def] at h ⊢; simpa using h)
      | right b => simp
    | right a =>
      induction j using Fin.addCases with
      | left b => simp
      | right b =>
        rw [siegelGlueMat_rr]
        exact h₂.lower a b (by rw [Fin.lt_def] at h ⊢; simpa using h)
  · intro i j h
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [siegelGlueMat_ll]
        exact h₁.upper a b (by rw [Fin.lt_def] at h ⊢; simpa using h)
      | right b => simp
    | right a =>
      induction j using Fin.addCases with
      | left b => simp
      | right b =>
        rw [siegelGlueMat_rr]
        exact h₂.upper a b (by rw [Fin.lt_def] at h ⊢; simpa using h)

lemma isSiegel_zero_of {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : IsSiegel d u) :
    IsSiegel (0 : Fin n → ℝ) u :=
  IsSiegel.mk (fun _ => le_refl _) (by simp) h.diag h.lower h.upper

lemma isSiegel_smul_of {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : IsSiegel d u)
    {t : ℝ} (ht : 0 ≤ t) : IsSiegel (fun i => t * d i) u := by
  refine IsSiegel.mk (fun i => mul_nonneg ht (h.nonneg i)) ?_ h.diag h.lower h.upper
  intro p q hpq
  have := h.step p q hpq
  nlinarith

theorem siegelData_glue_scaled : ∀ (s m : ℕ) (d₁ : Fin s → ℝ) (u₁ : Matrix (Fin s) (Fin s) ℝ) (d₂ : Fin m → ℝ) (u₂ : Matrix (Fin m) (Fin m) ℝ), IsSiegel d₁ u₁ → IsSiegel d₂ u₂ → (∀ i, 0 < d₁ i) → (∀ i, 0 < d₂ i) → ∃ (t : ℝ) (d d' : Fin (s + m) → ℝ) (u : Matrix (Fin (s + m)) (Fin (s + m)) ℝ), 0 < t ∧ IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ (∀ i j : Fin s, gram d u (Fin.castAdd m i) (Fin.castAdd m j) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.castAdd m j) = t * gram d₁ u₁ i j) ∧ (∀ (i : Fin s) (j : Fin m), gram d u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d u (Fin.natAdd s j) (Fin.castAdd m i) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d' u (Fin.natAdd s j) (Fin.castAdd m i) = 0) ∧ ∀ i j : Fin m, gram d u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j ∧ gram d' u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j := by
  intro s m d₁ u₁ d₂ u₂ h₁ h₂ p₁ p₂
  obtain ⟨t, ht, hj⟩ := siegelGlue_scale d₁ d₂ p₁ p₂
  refine ⟨t, Fin.append (0 : Fin s → ℝ) d₂, Fin.append (fun i => t * d₁ i) d₂, siegelGlueMat u₁ u₂, ht,
    isSiegel_glue (isSiegel_zero_of h₁) h₂ (fun i j _ => by simpa using (h₂.nonneg j)),
    isSiegel_glue (isSiegel_smul_of h₁ ht.le) h₂ hj, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left a => simpa using mul_pos ht (p₁ a)
    | right a => simpa using p₂ a
  · intro i j
    refine ⟨?_, ?_⟩
    · rw [gram_apply_glue, Fin.sum_univ_add]
      simp
    · rw [gram_apply_glue, Fin.sum_univ_add, gram_apply_glue, Finset.mul_sum]
      simp only [siegelGlueMat_ll, siegelGlueMat_rl, Fin.append_left, Fin.append_right, zero_mul,
        mul_zero, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
  · intro i j
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [gram_apply_glue, Fin.sum_univ_add]
      simp
  · intro i j
    refine ⟨?_, ?_⟩ <;>
    · rw [gram_apply_glue, Fin.sum_univ_add, gram_apply_glue]
      simp

end GlobalTheory.RedTh
end
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SiegelGap

theorem chain {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hS : GlobalTheory.RedTh.IsSiegel d u) :
    ∀ m : ℕ, ∀ i j : Fin n, (j : ℕ) = i + m → d i ≤ 4 ^ m * d j := by
  first
  | exact @_root_.GlobalTheory.SiegelChain.siegel_chain
  | exact _root_.GlobalTheory.SiegelChain.siegel_chain
  | (apply _root_.GlobalTheory.SiegelChain.siegel_chain <;> assumption)
  | (intros; apply _root_.GlobalTheory.SiegelChain.siegel_chain <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SiegelChain.siegel_chain <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SiegelChain.siegel_chain ..)

theorem chain_le {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hS : GlobalTheory.RedTh.IsSiegel d u)
    (i j : Fin n) (h : i ≤ j) : d i ≤ 4 ^ n * d j := by
  have h1 := chain hS ((j : ℕ) - i) i j (by have : (i:ℕ) ≤ j := h; omega)
  have hm : (4:ℝ) ^ ((j : ℕ) - i) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  calc d i ≤ 4 ^ ((j : ℕ) - i) * d j := h1
    _ ≤ 4 ^ n * d j := by gcongr; exact hS.nonneg j

theorem lowerBlock_eq_zero_of_gap : ∀ (n : ℕ) (K c : ℝ), ∃ R : ℝ, 1 ≤ R ∧ ∀ (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), GlobalTheory.RedTh.IsSiegel d u → (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (∀ i j, j < i → v i j = 0) → (∀ i j, |v i j| ≤ c) → (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K) → ∀ k k' : Fin n, (k' : ℕ) = k + 1 → R * d k < d k' → ∀ p q, q ≤ k → k' ≤ p → (u * A.map (Int.cast : ℤ → ℝ) * v) p q = 0 := by
  intro n K c
  set C : ℝ := (n : ℝ) ^ 2 * (|c| + 1) with hC
  set X : ℝ := (|K| + 1) * C ^ 2 with hX
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ X := by positivity
  have h16 : (0:ℝ) ≤ 16 ^ n * X := by positivity
  refine ⟨16 ^ n * X + 1, by linarith, ?_⟩
  intro A d u v hS hd hvu huv hvl hvc hsum k k' hkk' hR p q hqk hkp
  set B : Matrix (Fin n) (Fin n) ℝ := A.map (Int.cast : ℤ → ℝ) with hB
  set Wm := u * B * v with hW

  have hratio : ∀ s t : Fin n, t ≤ k → k' ≤ s → X * d t < d s := by
    intro s t hts hks
    have h1 := chain_le hS t k hts
    have h2 := chain_le hS k' s hks
    have h4 : (0:ℝ) < 4 ^ n := by positivity
    have hdk := hd k
    have e16 : (16:ℝ) ^ n = 4 ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
    have : 4 ^ n * (X * d t) < 4 ^ n * d s := by
      calc 4 ^ n * (X * d t) ≤ 4 ^ n * (X * (4 ^ n * d k)) := by gcongr
        _ = 16 ^ n * X * d k := by rw [e16]; ring
        _ < (16 ^ n * X + 1) * d k := by nlinarith
        _ < d k' := hR
        _ ≤ 4 ^ n * d s := h2
    exact lt_of_mul_lt_mul_left this h4.le

  have hterm : ∀ s t : Fin n, d s / d t * Wm s t ^ 2 ≤ K := by
    intro s t
    have hnn : ∀ a b : Fin n, 0 ≤ d a / d b * Wm a b ^ 2 := fun a b =>
      mul_nonneg (div_nonneg (hd a).le (hd b).le) (sq_nonneg _)
    calc d s / d t * Wm s t ^ 2 ≤ ∑ q, d s / d q * Wm s q ^ 2 :=
          Finset.single_le_sum (f := fun q => d s / d q * Wm s q ^ 2) (fun q _ => hnn s q) (Finset.mem_univ t)
      _ ≤ ∑ p, ∑ q, d p / d q * Wm p q ^ 2 :=
          Finset.single_le_sum (f := fun p => ∑ q, d p / d q * Wm p q ^ 2)
            (fun p _ => Finset.sum_nonneg (fun q _ => hnn p q)) (Finset.mem_univ s)
      _ ≤ K := hsum
  have hWsmall : ∀ s t : Fin n, t ≤ k → k' ≤ s → C * |Wm s t| < 1 := by
    intro s t hts hks
    have hr := hratio s t hts hks
    have hdt := hd t
    have hXr : X < d s / d t := by rw [lt_div_iff₀ hdt]; exact hr
    have h1 : X * Wm s t ^ 2 ≤ K := le_trans (mul_le_mul_of_nonneg_right hXr.le (sq_nonneg _)) (hterm s t)
    have h2 : C ^ 2 * Wm s t ^ 2 < 1 := by
      have hK : K ≤ |K| := le_abs_self K
      by_contra hcon
      push_neg at hcon
      have : (|K| + 1) * 1 ≤ (|K| + 1) * (C ^ 2 * Wm s t ^ 2) := by gcongr
      nlinarith
    have h3 : (C * |Wm s t|) ^ 2 < 1 := by rw [mul_pow, sq_abs]; exact h2
    have h4 : 0 ≤ C * |Wm s t| := by positivity
    nlinarith
  have hrec : B = v * Wm * u := by
    rw [hW]; simp only [← Matrix.mul_assoc]
    rw [hvu, Matrix.one_mul, Matrix.mul_assoc, hvu, Matrix.mul_one]
  have hAzero : ∀ i j : Fin n, k' ≤ i → j ≤ k → A i j = 0 := by
    intro i j hi hj
    have hent : (A i j : ℝ) = ∑ t, (∑ s, v i s * Wm s t) * u t j := by
      have : B i j = (v * Wm * u) i j := by rw [← hrec]
      simpa [hB, Matrix.mul_apply] using this
    have hn : (0:ℝ) < (n:ℝ) ^ 2 := by have := Fin.pos i; positivity
    have key : ∀ s t : Fin n, |v i s * Wm s t * u t j| < 1 / (n:ℝ) ^ 2 := by
      intro s t
      by_cases hs : s < i
      · rw [hvl i s hs]; simp; positivity
      by_cases ht : j < t
      · rw [hS.lower t j ht]; simp; positivity
      push_neg at hs ht
      have hsm := hWsmall s t (le_trans ht hj) (le_trans hi hs)
      have hu1 : |u t j| ≤ 1 := by
        rcases eq_or_lt_of_le ht with h | h
        · rw [h, hS.diag]; simp
        · have := hS.upper t j h; linarith
      have hv1 : |v i s| ≤ |c| + 1 := by
        have := hvc i s; have := le_abs_self c; linarith
      rw [abs_mul, abs_mul]
      calc |v i s| * |Wm s t| * |u t j| ≤ (|c| + 1) * |Wm s t| * 1 := by gcongr
        _ < 1 / (n:ℝ) ^ 2 := by
          rw [lt_div_iff₀ hn]
          have : (|c| + 1) * |Wm s t| * 1 * (n:ℝ) ^ 2 = C * |Wm s t| := by rw [hC]; ring
          linarith
    have hbound : |(A i j : ℝ)| < 1 := by
      rw [hent]
      calc |∑ t, (∑ s, v i s * Wm s t) * u t j| = |∑ t, ∑ s, v i s * Wm s t * u t j| := by
            simp [Finset.sum_mul]
        _ ≤ ∑ t, ∑ s, |v i s * Wm s t * u t j| :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => Finset.abs_sum_le_sum_abs _ _)
        _ < ∑ t : Fin n, ∑ s : Fin n, 1 / (n:ℝ) ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨i, Finset.mem_univ _⟩ fun t _ =>
              Finset.sum_lt_sum_of_nonempty ⟨i, Finset.mem_univ _⟩ fun s _ => key s t
        _ = 1 := by
            have : (n:ℝ) ≠ 0 := by have := Fin.pos i; positivity
            simp; field_simp
    have : |A i j| < 1 := by exact_mod_cast hbound
    exact Int.abs_lt_one_iff.mp this
  rw [hW]
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : q < t
  · simp [hvl t q ht]
  push_neg at ht
  have hz : ∑ s, u p s * B s t = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s < p
    · simp [hS.lower p s hs]
    push_neg at hs
    simp [hB, hAzero s t (le_trans hkp hs) (le_trans ht hqk)]
  rw [hz, zero_mul]

end GlobalTheory.SiegelGap
end
