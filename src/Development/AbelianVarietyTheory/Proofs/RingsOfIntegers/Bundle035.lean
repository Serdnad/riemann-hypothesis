module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle044
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle017
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle013
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PushIntegral

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n : ℕ}

theorem push_letB (ga : Matrix (Fin n) (Fin n) E) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (v : Fin n → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga (letB c σ i v) = letB c σ i (ga.mulVec v) := by

  simp only [letB, map_sum, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, GlobalTheory.PushHarm.push_X,
  Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_range_of_isIntegral (T : CDVR) (io : c.F →+* T.Fr) {x : c.F} (hi : IsIntegral ℤ x) :
    ∃ y : T.V, algebraMap T.V T.Fr y = io x := by
  obtain ⟨p, hpm, hp⟩ := hi
  have hV : IsIntegral T.V (io x) := by
    refine ⟨p.map (Int.castRingHom T.V), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
      (io.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, hp, map_zero]
  exact IsIntegrallyClosed.isIntegral_iff.1 hV

theorem mem_range_of_smul (T : CDVR) (io : c.F →+* T.Fr) {k : ℕ} (hk : IsUnit (k : T.V)) (σ : E →+* ℂ) {x : E}
    (hx : (k : E) * x ∈ (1 : Submodule (𝓞 E) E)) : ∃ y : T.V, algebraMap T.V T.Fr y = io (embF c σ x) := by
  obtain ⟨s, hs⟩ := Submodule.mem_one.1 hx
  have hi : IsIntegral ℤ (embF c σ (algebraMap (𝓞 E) E s)) :=
    map_isIntegral_int (embF c σ) (NumberField.RingOfIntegers.isIntegral_coe s)
  obtain ⟨y, hy⟩ := mem_range_of_isIntegral c T io hi
  obtain ⟨u, hu⟩ := hk.exists_left_inv
  refine ⟨u * y, ?_⟩
  have h1 : algebraMap T.V T.Fr u * (k : T.Fr) = 1 := by
    rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hu, map_one]
  rw [map_mul, hy, hs, map_mul, map_mul, map_natCast, map_natCast, ← _root_.mul_assoc, h1, _root_.one_mul]

theorem coeff_mem (Λ : GenLat E n) (T : CDVR) (io : c.F →+* T.Fr) {k : ℕ} (hk : IsUnit (k : T.V))
    (ga : Matrix (Fin n) (Fin n) E) (hin : ∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) (m : LtN Dw n →₀ ℕ) :
    (MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga P)).coeff m ∈ (algebraMap T.V T.Fr).range := by
  have hle : symO (Dw := Dw) c Λ ≤
      (MvPolynomial.map (σ := LtN Dw n) (algebraMap T.V T.Fr)).range.comap
        ((MvPolynomial.map io).comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c ga).toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, v, hv, rfl⟩)
    · obtain ⟨y, hy⟩ := mem_range_of_isIntegral c T io o.2
      refine ⟨MvPolynomial.C y, ?_⟩
      simp [hy]
    · have h : ∀ j, ∃ y : T.V, algebraMap T.V T.Fr y = io (embF c σ (ga.mulVec v j)) := fun j =>
        mem_range_of_smul c T io hk σ (hin v hv j (Set.mem_univ j))
      choose y hy using h
      refine ⟨∑ j, MvPolynomial.C (y j) * MvPolynomial.X ⟨σ, i, j⟩, ?_⟩
      change _ = MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga (letB c σ i v))
      rw [push_letB]
      simp [letB, hy]
  obtain ⟨Q, hQ⟩ := hle hP
  change _ = MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga P) at hQ
  rw [← hQ, MvPolynomial.coeff_map]
  exact ⟨_, rfl⟩

theorem push_one (P : MvPolynomial (LtN Dw n) c.F) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c (1 : Matrix (Fin n) (Fin n) E) P = P := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c (1 : Matrix (Fin n) (Fin n) E) = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨σ, i, j⟩
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push, letB, Matrix.one_apply, apply_ite, ite_mul]
  rw [h]; rfl

theorem aeval_smul_of_degree {J K A : Type} [CommRing K] [CommRing A] [Algebra K A] (t : A) (f : J → A)
    (P : MvPolynomial J K) (d : ℕ) (hP : ∀ s ∈ P.support, (s.sum fun _ e => e) = d) :
    MvPolynomial.aeval (fun i => t * f i) P = t ^ d * MvPolynomial.aeval f P := by
  classical

  rw [P.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hP s hs]
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem degree_eq_totalDegree {a : (E →+* ℂ) → ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : RowDeg Dw.mult n c.F a P) : ∀ s ∈ P.support, (s.sum fun _ e => e) = P.totalDegree := by
  classical
  have h : ∀ s ∈ P.support, (s.sum fun _ e => e) = ∑ σ : E →+* ℂ, ∑ i : Fin (Dw.mult σ), a σ i := by
    intro s hs
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP s hs σ i
  intro s hs
  refine le_antisymm (MvPolynomial.le_totalDegree hs) ?_
  exact Finset.sup_le fun s' hs' => ((h s' hs').trans (h s hs).symm).le

end

theorem map_pushL_mem_FFV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → ∀ (T : CDVR) (io : c.F →+* T.Fr) (k : ℕ) (ga : Matrix (Fin n) (Fin n) E), IsUnit (k : T.V) → (∀ i j, ∑ b, IsCMField.complexConj E (ga b i) * ga b j = if i = j then 1 else 0) → (∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n) → MvPolynomial.map io (pushL c ga P) ∈ FFV (Dw := Dw) T w n ∧ pushL c 1 P = P ∧ ∀ m : ℕ, pushL c ((m : E) • ga) P = MvPolynomial.C ((m : c.F) ^ P.totalDegree) * pushL c ga P := by
  intro E _ _ _ H Dw l c n Λ w P hP T io k ga hk hu hin
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  have hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.IsUnitary ga := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply] using hu i j
  have hr := GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n ga P (fun τ i => w (τ, i))
  refine ⟨⟨⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map io (GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n ga P hU h1),
    ReciprocityTheory.ChartRestriction.G.PullbackSections.rowInv_map io (hr.1 h2), ReciprocityTheory.ChartRestriction.G.PullbackSections.rowDeg_map io (hr.2 h3)⟩,
    coeff_mem c Λ T io hk ga hin h4⟩, push_one c P, fun m => ?_⟩
  rw [map_pow, pushL, pushL, ← aeval_smul_of_degree _ _ P _ (degree_eq_totalDegree c h3)]
  congr 2
  funext ℓ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [_root_.mul_assoc]

end GlobalTheory.PushIntegral
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PullMove

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translT_mul {T : Over S} (x y : T ⟶ A) : translT A x ≫ translT A y = translT A (y * x) := by
  rw [translT, lift_transl, translPt_eq, translT, translPt_eq, MonObj.comp_mul, _root_.mul_assoc]

theorem translT_one {T : Over S} : translT A (1 : T ⟶ A) = 𝟙 _ := by
  rw [translT, translPt_eq, MonObj.comp_one, _root_.one_mul, lift_fst_snd]

theorem translT_endT (φ : A ⟶ A) [IsMonHom φ] {T : Over S} (x : T ⟶ A) :
    translT A x ≫ endT A T φ = endT A T φ ≫ translT A (x ≫ φ) := by
  rw [lift_transl, translT, comp_lift, lift_fst, lift_snd_assoc, translPt_eq, MonObj.mul_comp, Category.assoc]

theorem negT_endT (φ : A ⟶ A) [IsMonHom φ] (T : Over S) : negT A T ≫ endT A T φ = endT A T φ ≫ negT A T := by
  rw [negT, comp_lift, comp_lift, lift_fst, lift_fst, lift_snd_assoc, lift_snd_assoc]
  exact congrArg _ (GrpObj.inv_comp (snd T A) φ)

theorem negT_translT [IsCommMonObj A] {T : Over S} (x : T ⟶ A) :
    negT A T ≫ translT A x = translT A x⁻¹ ≫ negT A T := by
  rw [negT, lift_transl, translT, comp_lift, lift_fst, lift_snd_assoc, translPt_eq, GrpObj.comp_inv]
  refine congrArg _ ?_
  show fst T A ≫ x * (snd T A)⁻¹ = ((fst T A ≫ x)⁻¹ * snd T A)⁻¹
  rw [mul_inv, inv_inv]


omit [GrpObj A] in
theorem exists_conj {L : LB A.left} (hL : L.IsLB) (φ : A ⟶ A) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hα : α.IsGen) {T : Over S}
    (m' m : T ⊗ A ⟶ A) (e : m' ≫ φ = endT A T φ ≫ m)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![b, -b])) (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m'.left] ![a, -a]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val u' r z J = val α (r ≫ (snd T A).left) z J * val u (r ≫ (endT A T φ).left) z J *
          (val α (r ≫ m'.left) z J)⁻¹ := by
  have e₁ : (endT A T φ).left ≫ (snd T A).left = (snd T A).left ≫ φ.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have e₂ : (endT A T φ).left ≫ m.left = m'.left ≫ φ.left := by
    rw [← Over.comp_left, ← e, Over.comp_left]
  obtain ⟨u', hu', hv⟩ := exists_gen hL (φ' := ![(snd T A).left, m'.left]) (ε' := ![a, -a])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ α (snd T A).left)
      (LB.pullGen L _ _ u (endT A T φ).left)) (LB.invGen L _ _ (LB.pullGen L _ _ α m'.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)
      (DVR.pullGen_isGen _ _ _ _ hu _)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)))
  refine ⟨u', hu', fun Z r z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]

theorem prod_conj {U : Type} [CommGroup U] (f g : ℕ → U) (n N : ℕ)
    (hg : ∀ i, ∏ j ∈ Finset.range n, g (n * i + j) = 1) (hf : f (n * N) = f 0) :
    ∏ j ∈ Finset.range (n * N), (f j * g j * (f (j + 1))⁻¹) = 1 := by
  have t : ∀ k, ∏ j ∈ Finset.range k, (f j * g j * (f (j + 1))⁻¹) =
      f 0 * (∏ j ∈ Finset.range k, g j) * (f k)⁻¹ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
      group
  have p : ∀ M, ∏ j ∈ Finset.range (n * M), g j = 1 := fun M => by
    induction M with
    | zero => simp
    | succ M ih => rw [Nat.mul_succ, Finset.prod_range_add, ih, hg, _root_.mul_one]
  rw [t, p, hf, _root_.mul_one, mul_inv_cancel]

theorem exists_symLift_conj [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hα : α.IsGen) {T : Over S}
    (n N : ℕ) (x : T ⟶ A) (hx : x ^ (n * N) = 1) (U : ThetaGrp A L b T) (H : SymLift A L b n (x ≫ φ) U) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![a, -a]), ∃ hu : u.IsGen,
      SymLift A L a (n * N) x ⟨x, u, hu⟩ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val u r z J = val α (r ≫ (snd T A).left) z J *
          val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![b, -b]) U.φ
            (r ≫ (endT A T φ).left) z J * (val α (r ≫ (translPt A x).left) z J)⁻¹ := by
  have hp := H.pt_eq
  have ts : ∀ y : T ⟶ A, translT A y ≫ snd T A = translPt A y := fun y => lift_snd _ _
  have ns : negT A T ≫ snd T A = snd T A ≫ (GrpObj.inv : A ⟶ A) := lift_snd _ _
  obtain ⟨u, hu, vu⟩ := exists_conj hL φ a b α hα (translPt A x) (translPt A U.pt) (by
    rw [hp, ← ts (x ≫ φ), ← Category.assoc, ← translT_endT, Category.assoc, lift_snd, ← Category.assoc, ts])
    U.φ U.isGen
  obtain ⟨ν, hν, hs⟩ := H.sym
  obtain ⟨ν', hν', vν⟩ := exists_conj hL φ a b α hα (snd T A ≫ (GrpObj.inv : A ⟶ A))
    (snd T A ≫ (GrpObj.inv : A ⟶ A)) (by
      rw [lift_snd_assoc]
      exact GrpObj.inv_comp (snd T A) φ) ν hν
  refine ⟨u, hu, ⟨rfl, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩, vu⟩
  · refine (ThetaPullback.val_powGen ⟨x, u, hu⟩ (n * N) _ hJ).trans (Eq.trans ?_ (val_one _).symm)
    refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) ((Fin.prod_univ_eq_prod_range _ _).trans (prod_conj
      (fun j => val α (translPt A (x ^ j)).left y J)
      (fun j => val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![b, -b]) U.φ
        (endT A T φ ≫ translT A (U.pt ^ j)).left y J) n N (fun i => ?_) (by rw [hx, pow_zero])))
    · refine (vu _ _ y J hJ).trans ?_
      simp only [Category.id_comp, ← Over.comp_left]
      rw [ts, translT_endT, MonObj.pow_comp, ← hp, ← ts x, ← Category.assoc, translT_mul, ts, pow_succ']
    · have e := (ThetaPullback.val_powGen U n (endT A T φ ≫ translT A (U.pt ^ (n * i))).left hJ).symm.trans
        ((val_corr hJ H.pow_eq _).trans (val_one _))
      refine Eq.trans ?_ e
      rw [← Fin.prod_univ_eq_prod_range (fun j => val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left])
        (ε := ![b, -b]) U.φ (endT A T φ ≫ translT A (U.pt ^ (n * i + j))).left y J)]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← Over.comp_left, Category.assoc, translT_mul, ← pow_add, add_comm]
  · have e := (ThetaPullback.val_symGen U ν (endT A T φ).left hJ).symm.trans ((val_corr hJ hs _).trans (val_one _))
    refine (ThetaPullback.val_symGen ⟨x, u, hu⟩ ν' _ hJ).trans (Eq.trans ?_ (e.trans (val_one _).symm))
    refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (vu _ _ y J hJ) (vν _ _ y J hJ))
      (congrArg₂ (· * ·) (vu _ _ y J hJ) (congrArg (·⁻¹) (vν _ _ y J hJ)))).trans ?_
    simp only [Category.id_comp, ← Over.comp_left]
    have e₁ : translT A x⁻¹ ≫ translPt A x = snd T A := by
      rw [← ts x, ← Category.assoc, translT_mul, mul_inv_cancel, translT_one, Category.id_comp]
    have e₂ : negT A T ≫ translPt A x = translT A x⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) := by
      rw [← ts x, ← Category.assoc, negT_translT, Category.assoc, ns]
    rw [e₁, e₂, ns, negT_endT, translT_endT, GrpObj.inv_comp, ← hp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem isSymAct_of_isNormPull [IsCommMonObj A] (hA : IsAbelianScheme A) (L : RigLB A) (φ : A ⟶ A) [IsMonHom φ]
    (k N : ℕ) {T : Over S} (x : T ⟶ A) (hx : x ^ (k * N) = 1) {F G : LB.Sec (LPow A L.L (k : ℤ) T)}
    {F' G' : LB.Sec (LPow A L.L ((k * N : ℕ) : ℤ) T)} (h : IsSymAct A L k (x ≫ φ) F G)
    (hF : IsNormPull A L φ ((k * N : ℕ) : ℤ) (k : ℤ) F F') (hG : IsNormPull A L φ ((k * N : ℕ) : ℤ) (k : ℤ) G G') :
    IsSymAct A L (k * N) x F' G' := by
  have hL := L.isLB
  obtain ⟨-, U, H, ac⟩ := h
  obtain ⟨α₀, α, g₀, n₀, c, tw⟩ := hF
  obtain ⟨α₀', α', g₀', n₀', c', tw'⟩ := hG
  obtain ⟨u, hu, H', vu⟩ := exists_symLift_conj hL φ _ _ α₀ g₀ k N x hx U H
  refine ⟨hx, ⟨x, u, hu⟩, H', VVRank.isTwistPull_of_sv A hL hu fun y J hJ => ?_⟩
  have bb := fun r : (T ⊗ A).left ⟶ A.left =>
    gen_unique hL A.hom (eSec A) (Over.w η[A]) (SemiRigid.globalFns _ _ hA).2 g₀' g₀ (fun w I hI => by
      have a := val_corr hI n₀' (𝟙 _)
      have b := val_corr hI n₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm) _ r y J hJ
  rw [VVRank.sv_of_isTwistPull A tw' _ y hJ, VVRank.sv_of_isTwistPull A tw _ y hJ,
    VVRank.sv_of_isTwistPull A ac _ y hJ, vu _ _ y J hJ, val_corr hJ c, val_corr hJ c', val_pull hJ, val_pull hJ, bb]
  simp only [Category.id_comp, ← Over.comp_left]
  rw [translT_endT, ← H.pt_eq, show translT A x ≫ snd T A = translPt A x from lift_snd _ _,
    ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
    ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.PullMove

namespace GlobalTheory.PlaceInt

theorem moves_of_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (β : 𝓞 E) (N k k' : ℕ), β * H.bar β = (N : 𝓞 E) → k' = k * N → Odd k' → ∀ (b b' : (ptO Xo x ⟶ Xo.univ.t.G)), b' ≫ Xo.univ.t.act.act β = b → b' ^ k' = 1 → ∀ (F G : SecN Xo x k) (F' G' : SecN Xo x k'), Moves Xo b F G → Pulls Xo β F F' → Pulls Xo β G G' → Moves Xo b' F' G' := by
  intro E _ _ _ H Dw l Xo S _ x β N k k' _ hk _ b b' hb hb' F G F' G' h hF hG
  subst hk hb
  have := Xo.univ.t.act.hom β
  exact PullMove.isSymAct_of_isNormPull
    ⟨inferInstance, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩ _ _ k N b' hb' h hF hG

end GlobalTheory.PlaceInt
end
end

section

set_option autoImplicit false
open IsLocalRing

namespace GlobalTheory.PlaceInt

section
variable {V : Type} [CommRing V] [IsLocalRing V]

theorem mem_maximalIdeal_mvPowerSeries_iff {τ : Type} (f : MvPowerSeries τ V) :
    f ∈ maximalIdeal (MvPowerSeries τ V) ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal V := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

variable [IsNoetherianRing V] [IsAdicComplete (maximalIdeal V) V]

theorem isAdicComplete_mvPowerSeries_finite (τ : Type) [Finite τ] :
    IsAdicComplete (maximalIdeal (MvPowerSeries τ V)) (MvPowerSeries τ V) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin τ

  have ha : MvPowerSeries.HasSubst
      (fun i : Fin n => (MvPowerSeries.X (e.symm i) : MvPowerSeries τ V)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hb : MvPowerSeries.HasSubst
      (fun t : τ => (MvPowerSeries.X (e t) : MvPowerSeries (Fin n) V)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hba : ∀ f : MvPowerSeries (Fin n) V,
      MvPowerSeries.substAlgHom (R := V) hb (MvPowerSeries.substAlgHom (R := V) ha f) = f := by
    intro f
    rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
    have hX : (fun i : Fin n => MvPowerSeries.substAlgHom (R := V) hb
        (MvPowerSeries.X (e.symm i) : MvPowerSeries τ V)) = MvPowerSeries.X := by
      funext i
      rw [MvPowerSeries.substAlgHom_X, Equiv.apply_symm_apply]
    rw [MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]
  have hab : ∀ g : MvPowerSeries τ V,
      MvPowerSeries.substAlgHom (R := V) ha (MvPowerSeries.substAlgHom (R := V) hb g) = g := by
    intro g
    rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
    have hX : (fun t : τ => MvPowerSeries.substAlgHom (R := V) ha
        (MvPowerSeries.X (e t) : MvPowerSeries (Fin n) V)) = MvPowerSeries.X := by
      funext t
      rw [MvPowerSeries.substAlgHom_X, Equiv.symm_apply_apply]
    rw [MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]
  let E : MvPowerSeries (Fin n) V ≃+* MvPowerSeries τ V :=
    { toFun := MvPowerSeries.substAlgHom (R := V) ha
      invFun := MvPowerSeries.substAlgHom (R := V) hb
      left_inv := hba
      right_inv := hab
      map_mul' := map_mul _
      map_add' := map_add _ }
  have := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries V n
  exact GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv E

variable {σ τ : Type} [Finite σ] [Finite τ]

theorem exists_algHom_evC (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) :
    ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, ψ (MvPowerSeries.X j) = a j := by
  have := isAdicComplete_mvPowerSeries_finite (V := V) τ
  refine (GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a
    (fun j => ⟨1, ?_⟩)).1 inferInstance V
  rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]
  exact ha j

private theorem mvPowerSeries_algHom_ext_of_X_eq (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V)
    (ψ ψ' : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V) (h : ∀ j, ψ (MvPowerSeries.X j) = a j)
    (h' : ∀ j, ψ' (MvPowerSeries.X j) = a j) : ψ = ψ' := by
  have := isAdicComplete_mvPowerSeries_finite (V := V) τ
  have key := (GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a
    (fun j => ⟨1, by rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]; exact ha j⟩)).2
    inferInstance V ψ.toRingHom ψ'.toRingHom
    (fun t => by
      show ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)
      have hC : (MvPowerSeries.C t : MvPowerSeries σ V) = algebraMap V (MvPowerSeries σ V) t := by
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [hC, ψ.commutes, ψ'.commutes]) h h'
  exact AlgHom.ext fun f => RingHom.congr_fun key f

theorem evC_eq_algHom (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V)
    (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V) (hψ : ∀ j, ψ (MvPowerSeries.X j) = a j)
    (f : MvPowerSeries σ V) : evC a f = ψ f := by
  have h : ∃ φ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, φ (MvPowerSeries.X j) = a j :=
    ⟨ψ, hψ⟩
  rw [evC, dite_eq_left h, mvPowerSeries_algHom_ext_of_X_eq a ha h.choose ψ h.choose_spec hψ]

theorem constantCoeff_evC_mem (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) (f : MvPowerSeries σ V)
    (hf : MvPowerSeries.constantCoeff f ∈ maximalIdeal V) :
    MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V := by
  obtain ⟨ψ, hψ⟩ := exists_algHom_evC a ha
  rw [evC_eq_algHom a ha ψ hψ f]

  let χ₁ : MvPowerSeries σ V →+* ResidueField V :=
    (residue V).comp (MvPowerSeries.constantCoeff.comp ψ.toRingHom)
  let χ₂ : MvPowerSeries σ V →+* ResidueField V := (residue V).comp MvPowerSeries.constantCoeff
  have hC : ∀ t : V, ψ (MvPowerSeries.C t) = MvPowerSeries.C t := fun t => by
    have := ψ.commutes t
    rwa [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
  have key := (GlobalTheory.mvPowerSeries_eval_of_pow_mem (ResidueField V) ⊥ σ (fun _ => 0)
    (fun _ => ⟨1, by simp⟩)).2 inferInstance V χ₁ χ₂
    (fun t => by simp [χ₁, χ₂, hC])
    (fun j => by
      simp only [χ₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hψ]
      exact (residue_eq_zero_iff _).2 (ha j))
    (fun j => by simp [χ₂])
  have hf' := RingHom.congr_fun key f
  simp only [χ₁, χ₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf'
  rw [← residue_eq_zero_iff, hf']
  exact (residue_eq_zero_iff _).2 hf

end

theorem evC_spec : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ τ ρ : Type) [Finite σ] [Finite τ] [Finite ρ] (a : σ → MvPowerSeries τ V), (∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) → (∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (MvPowerSeries.X j) = a j) ∧ ∀ f, evC a f = ψ f) ∧ (∀ f, MvPowerSeries.constantCoeff f ∈ maximalIdeal V → MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V) ∧ ((∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f, evC a f = MvPowerSeries.subst a f) ∧ ∀ b : τ → MvPowerSeries ρ V, (∀ j, MvPowerSeries.constantCoeff (b j) ∈ maximalIdeal V) → ∀ f, evC b (evC a f) = evC (fun j => evC b (a j)) f := by
  intro V _ _ _ _ _ σ τ ρ _ _ _ a ha
  refine ⟨?_, fun f hf => constantCoeff_evC_mem a ha f hf, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_algHom_evC a ha
    exact ⟨ψ, hψ, fun f => evC_eq_algHom a ha ψ hψ f⟩
  · intro h0 f
    have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    rw [evC_eq_algHom a ha (MvPowerSeries.substAlgHom (R := V) hs)
      (fun j => MvPowerSeries.substAlgHom_X hs j) f]
    exact MvPowerSeries.substAlgHom_apply hs f
  · intro b hb f
    obtain ⟨ψa, hψa⟩ := exists_algHom_evC a ha
    obtain ⟨ψb, hψb⟩ := exists_algHom_evC b hb
    have hc : ∀ j, MvPowerSeries.constantCoeff (evC b (a j)) ∈ maximalIdeal V :=
      fun j => constantCoeff_evC_mem b hb (a j) (ha j)

    rw [evC_eq_algHom (fun j => evC b (a j)) hc (ψb.comp ψa)
      (fun j => by rw [AlgHom.comp_apply, hψa, evC_eq_algHom b hb ψb hψb]) f,
      evC_eq_algHom a ha ψa hψa, evC_eq_algHom b hb ψb hψb, AlgHom.comp_apply]

end GlobalTheory.PlaceInt
end
