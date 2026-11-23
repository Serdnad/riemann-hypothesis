module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerChainMatricesWithNormBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.PELU

theorem exists_isBC : ∀ (O : Type) [Ring O] (g : ℕ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g),
    ∃ F' : Fam ℂ O Λ g, IsBC F' F σ := by
  intro O _ g R _ σ Λ F
  let f : pullback F.s (spMap σ) ⟶ F.X := pullback.fst _ _
  let A' : Over (pullback F.s (spMap σ)) := (Over.pullback f).obj F.A
  letI : GrpObj A' := Functor.grpObjObj
  have hP : IsGrpPullback A' F.A f (pullback.fst F.A.hom f) := isGrpPullback_pullback F.A f
  haveI : IsCommMonObj A' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hP
  obtain ⟨act', ⟨hh, h1, hm, ha⟩, hc⟩ := GlobalTheory.ActPull.exists_act_pull _ _ f F.A A' _ hP Oᵐᵒᵖ
    (fun a => F.act a.unop) (fun a => F.hom _) F.act_one (fun a b => F.act_mul b.unop a.unop)
    (fun a b => F.act_add _ _)
  have hLB := LB.isLB_pull F.isLB (pullback.fst F.A.hom f)
  have hpol := GlobalTheory.pol_pull _ _ F.A A' f _ F.L (F.L.pull _) F.isLB hLB F.ab hP (GlobalTheory.PolBaseChange.lbIso_refl hLB)
  have hdim : SmoothOfRelativeDimension g A'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hP.1 F.dim
  let eta' : Λ → (𝟙_ (Over (pullback F.s (spMap σ))) ⟶ A') := fun a =>
    Over.homMk (hP.1.lift (f ≫ (F.eta a).left) (𝟙 _) (by
      rw [Category.assoc, Over.w]; simp)) (hP.1.lift_snd _ _ _)
  refine ⟨Fam.mk (pullback F.s (spMap σ)) (pullback.snd _ _) A' hpol.1 hdim (fun a => act' (MulOpposite.op a))
    (fun a => hh _) h1 (fun a b => by rw [MulOpposite.op_mul]; exact hm _ _)
    (fun a b => by rw [MulOpposite.op_add]; exact ha _ _)
    (F.L.pull (pullback.fst F.A.hom f)) hLB (hpol.2.1 F.ample) eta',
    f, pullback.fst F.A.hom f, IsPullback.of_hasPullback _ _, hP, fun a => hc _,
    GlobalTheory.PolBaseChange.lbIso_refl hLB, fun a => hP.1.lift_fst _ _ _⟩

end GlobalTheory.PELU
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

noncomputable section

namespace GlobalTheory.IwasawaGL

theorem diagPow_val {K : Type} [Field K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) :
    ((GlobalTheory.JSW.diagPow ϖ l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => ((ϖ ^ l i : Kˣ) : K)) := rfl

theorem exists_unit_part (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (x : w.adicCompletion E)
    (hx : x ≠ 0) :
    ∃ e : ℤ, Valued.v (x * ((ϖ ^ (-e) : (w.adicCompletion E)ˣ) : w.adicCompletion E)) = 1 := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨γ, hγ⟩ := WithZero.ne_zero_iff_exists.1 h0
  refine ⟨-Multiplicative.toAdd γ, ?_⟩
  rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← hγ, neg_neg,
    ← WithZero.coe_zpow, ← WithZero.coe_mul]
  rw [show (1 : WithZero (Multiplicative ℤ)) = ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

theorem iwasawa_diagPow : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ g : GL (Fin a) (w.adicCompletion E), ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w (n := a), g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k := by
  intro E _ _ a w ϖ hϖ g
  obtain ⟨b, k, hb, hk, rfl⟩ := Formalism.UG.P.spherical_iwasawa E w g
  have hd : ∀ i, (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i ≠ 0 :=
    Formalism.UG.P.spherical_diag_ne_zero b hb
  choose e he using fun i => exists_unit_part E w ϖ hϖ _ (hd i)
  let c : Fin a → w.adicCompletion E := fun i =>
    (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i * ((ϖ ^ (-e i) : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have hc0 : ∀ i, c i ≠ 0 := fun i => mul_ne_zero (hd i) (Units.ne_zero _)
  have hcO : ∀ i, c i ∈ Ov E w := fun i => (he i).le
  have hcO' : ∀ i, (c i)⁻¹ ∈ Ov E w := fun i => by
    show Valued.v (c i)⁻¹ ≤ 1
    rw [map_inv₀, he i, inv_one]
  let Dc : GL (Fin a) (w.adicCompletion E) :=
    ⟨Matrix.diagonal c, Matrix.diagonal (fun i => (c i)⁻¹),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hc0 i),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hc0 i)⟩
  have hDc : Dc ∈ KGL w (n := a) := by
    refine Formalism.UG.P.glint_mem_range_of_integral (Ov E w) Dc
      ⟨Matrix.diagonal (fun i => (⟨c i, hcO i⟩ : Ov E w)), ?_⟩
      ⟨Matrix.diagonal (fun i => (⟨(c i)⁻¹, hcO' i⟩ : Ov E w)), ?_⟩
    · ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Dc]
      split_ifs <;> simp
    · ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Dc, Units.inv_mk]
      split_ifs <;> simp
  let N : ℕ := ∑ i, (e i).natAbs
  let l : Fin a → ℕ := fun i => (e i + N).toNat
  have hexp : ∀ i, ((ϖ⁻¹) ^ N * ϖ ^ (l i) : (w.adicCompletion E)ˣ) = ϖ ^ (e i) := by
    intro i
    have hle : (e i).natAbs ≤ N :=
      Finset.single_le_sum (f := fun j => (e j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h1 : -((e i).natAbs : ℤ) ≤ e i := by rw [Int.natCast_natAbs]; exact neg_abs_le _
    have h2 : ((e i).natAbs : ℤ) ≤ N := by exact_mod_cast hle
    have hl : ((l i : ℕ) : ℤ) = e i + N := Int.toNat_of_nonneg (by omega)
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_add, hl]
    congr 1; ring
  have hT : ((GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc : GL (Fin a) (w.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (w.adicCompletion E)) =
      Matrix.diagonal (fun i => (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i) := by
    rw [Units.val_mul, Units.val_mul, diagPow_val, diagPow_val]
    change Matrix.diagonal _ * Matrix.diagonal _ * Matrix.diagonal c = _
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [← Units.val_mul, hexp i]
    simp only [c]
    rw [mul_left_comm, ← Units.val_mul, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one, mul_one]
  let u : GL (Fin a) (w.adicCompletion E) := b * (GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc)⁻¹
  have hu : u * (GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc) = b := by
    simp only [u]; group
  have hmat : (u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *
      Matrix.diagonal (fun i => (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i) = b := by
    rw [← hT, ← Units.val_mul, hu]
  have hent : ∀ i j, (u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j *
      (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) j j = (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
    intro i j
    have := congrFun (congrFun hmat i) j
    rwa [Matrix.mul_diagonal] at this
  have hmem : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · have h := hent i j
      rw [hb hij] at h
      exact (mul_eq_zero.1 h).resolve_right (hd j)
    · exact mul_right_cancel₀ (hd i) (by rw [one_mul]; exact hent i i)
  refine ⟨u, hmem, N, l, Dc * k, Subgroup.mul_mem _ hDc hk, ?_⟩
  simp only [u]
  group

end GlobalTheory.IwasawaGL
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.adelicGL_complementary_supports_commute : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (h t : GA E a), h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S → GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → h * t = t * h := by
  first | exact @GlobalTheory.JSW.MirSemi.supS_mul_comm | exact GlobalTheory.JSW.MirSemi.supS_mul_comm | (intros; apply GlobalTheory.JSW.MirSemi.supS_mul_comm <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.baseChangeBis : ∀ (S : Scheme.{0}) (A S' S'' : Over S) [GrpObj A] (g : ℕ) (_ : S'' ⟶ S'), HasRep A g S' → HasRep A g S'' := by
  first | exact @GlobalTheory.DualCon.HasRep.baseChange | exact GlobalTheory.DualCon.HasRep.baseChange | (intros; apply GlobalTheory.DualCon.HasRep.baseChange <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.additiveFamily_chart_affine_of_chart_finiteType : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → (∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N) → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  first | exact @GlobalTheory.DualApprox.chartAt_of_finiteType | exact GlobalTheory.DualApprox.chartAt_of_finiteType | (intros; apply GlobalTheory.DualApprox.chartAt_of_finiteType <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.additiveLineBundleFamily_of_disjoint_open_pieces : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Fam A (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → Fam A Pt := by
  first | exact @GlobalTheory.DualCon.ProdGlue.fam_of_pieces | exact GlobalTheory.DualCon.ProdGlue.fam_of_pieces | (intros; apply GlobalTheory.DualCon.ProdGlue.fam_of_pieces <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_lineBundleFamily_agreementLocus_of_affineOpens : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → (∀ V : T.left.affineOpens, ∃ (H : Over (Sp R)) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), Same A M N u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over (Sp R)) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), Same A M N u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  first | exact @GlobalTheory.DualCon.GlueKernel.exists_kernel_of_affine | exact GlobalTheory.DualCon.GlueKernel.exists_kernel_of_affine | (intros; apply GlobalTheory.DualCon.GlueKernel.exists_kernel_of_affine <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_point_disjointUnion_representingAdditiveFamily : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (t : T ⟶ X) (N : LB (A ⊗ T).left), Fam A N → ∃ x : T ⟶ Bt, x ≫ bt = t ∧ LBIso N (ev Pt (fst A T) (snd A T ≫ x)) := by
  first | exact @GlobalTheory.DualCon.ProdGlue.rep_exists | exact GlobalTheory.DualCon.ProdGlue.rep_exists | (intros; apply GlobalTheory.DualCon.ProdGlue.rep_exists <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem _root_.GlobalTheory.T.kerChain_matrices_with_norm_bounds : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms) (g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)) (Pl : Type) [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) (hn : HtNums R (InfinitePlace K)) (no : Bs.J → ℕ) (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ), (∀ v, IsUnit (Dc.Xc u v).det) → (∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) v x ^ 2 : ℝ) : ℂ) = famIpAt (Q.F 0) (Q.hF 0) v (f0 x) (f0 x)) → (∀ i, FamFramed (Q.F i) (Q.hF i)) → DatFramed Q.S₁ Q.hS₁ → (∀ φ F, Dc.Pt u Bs.μ0 φ F = g (Q.col (f0 φ)) F) → IsFrames Df X0 → FactorBounds Q no hn.sz → (∀ (v : InfinitePlace K) (ψ : Q.S₁.EqFun) F, v (g ψ F) ^ 2 ≤ Real.exp hn.hPn * (Q.S₁.ipAt Q.hS₁ v ψ ψ).re * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody Dc u Q f0 R := by
  first | exact @GlobalTheory.DefRowsChain.rowsBody_of_framed | exact GlobalTheory.DefRowsChain.rowsBody_of_framed | (intros; apply GlobalTheory.DefRowsChain.rowsBody_of_framed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitaryGroup_character_of_heckeChar : ∀ (D : D7) (ε : AE D), (ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧ (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧ ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0) → ∀ (V : HSp D) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∃ c : GA D V →* Circle, Continuous c ∧ (∀ g ∈ GinfC V, c g = 1) ∧ (∀ v η, NonSplitAt D v η → ∀ g, SuppPl η V g → c g = 1) ∧ ∀ e, IsSplitIdem D e → ∀ g x, SuppAt e V g → IsDetAt e V g x → c g = χ x := by
  first | exact @GlobalTheory.SplitDetCharacter.exists_character | exact GlobalTheory.SplitDetCharacter.exists_character | (intros; apply GlobalTheory.SplitDetCharacter.exists_character <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.liftsAlong_principal_small_extension : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → SmallLift A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  first | exact @GlobalTheory.DualOpen.liftsAlong_span_singleton | exact GlobalTheory.DualOpen.liftsAlong_span_singleton | (intros; apply GlobalTheory.DualOpen.liftsAlong_span_singleton <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen


open IsLocalRing in
theorem smallExt_fibre_ring : ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∃ (P : Type) (_ : CommRing P) (i : C →+* P) (p σ : P →+* C) (q : P →+* DualNumber (IsLocalRing.ResidueField C)), p.comp i = RingHom.id C ∧ σ.comp i = RingHom.id C ∧ q.comp i = (dnInl _).comp (IsLocalRing.residue C) ∧ IsClosedImmersion (spMap σ) ∧ Surjective (spMap σ) ∧ Milnor (spMap p) (spMap σ) (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e}))) ∧ Milnor (spMap p) (spMap q) (spMap (IsLocalRing.residue C)) (spMap (dnFst _)) := by
  intro C _ _ e he hm hne
  have hee : e * e = 0 := hm e he
  obtain ⟨φ, hφ⟩ : ∃ φ : ResidueField C →+ C, ∀ c, φ (residue C c) = c * e := by
    refine ⟨(Submodule.liftQ (maximalIdeal C) (LinearMap.toSpanSingleton C C e) ?_).toAddMonoidHom, fun c ↦ ?_⟩
    · intro a ha
      simpa using hm a ha
    · rfl
  have hφ0 : ∀ x, φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ] at hx
    rw [residue_eq_zero_iff]
    by_contra hc
    have hu : IsUnit c := by simpa using hc
    exact hne (hu.mul_right_eq_zero.mp hx)
  let P : Subring (C × DualNumber (ResidueField C)) :=
    RingHom.eqLocus ((residue C).comp (RingHom.fst _ _)) ((dnFst _).comp (RingHom.snd _ _))
  have hP : ∀ x : C × DualNumber (ResidueField C), x ∈ P ↔ residue C x.1 = x.2.fst := fun x ↦ Iff.rfl
  let p : P →+* C := (RingHom.fst _ _).comp P.subtype
  let q : P →+* DualNumber (ResidueField C) := (RingHom.snd _ _).comp P.subtype
  let i : C →+* P := RingHom.codRestrict ((RingHom.id C).prod ((dnInl _).comp (residue C))) P
    (fun c ↦ (hP _).2 rfl)
  let σ : P →+* C :=
    { toFun := fun x ↦ x.1.1 + φ x.1.2.snd
      map_one' := by simp
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Subring.coe_add, Prod.fst_add, Prod.snd_add, TrivSqZeroExt.snd_add, map_add (f := _)]
        ring
      map_mul' := by
        rintro ⟨⟨a, x⟩, hx⟩ ⟨⟨b, y⟩, hy⟩
        have hx' : residue C a = x.fst := hx
        have hy' : residue C b = y.fst := hy
        obtain ⟨c, hc⟩ := residue_surjective (R := C) x.snd
        obtain ⟨d, hd⟩ := residue_surjective (R := C) y.snd
        show a * b + φ (x * y).snd = (a + φ x.snd) * (b + φ y.snd)
        rw [DualNumber.snd_mul, ← hx', ← hy', ← hc, ← hd, ← map_mul, ← map_mul, ← map_add (f := _), hφ, hφ, hφ]
        linear_combination (-(c * d)) * hee }
  have hσ : ∀ x : P, σ x = x.1.1 + φ x.1.2.snd := fun _ ↦ rfl
  have hσi : σ.comp i = RingHom.id C := by
    ext c
    show c + φ (TrivSqZeroExt.inl (residue C c) : DualNumber _).snd = c
    simp
  have hsurj : Function.Surjective σ := fun c ↦ ⟨i c, RingHom.congr_fun hσi c⟩
  have hφmem : ∀ x, φ x ∈ Ideal.span {e} := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ]
    exact Ideal.mem_span_singleton'.2 ⟨c, rfl⟩
  have hker : RingHom.ker σ ≤ nilradical P := by
    rintro ⟨⟨a, x⟩, hx⟩ h
    have hx' : residue C a = x.fst := hx
    have h' : a + φ x.snd = 0 := h
    obtain ⟨c, hc⟩ := residue_surjective (R := C) x.snd
    rw [← hc, hφ] at h'
    have ha : a = -c * e := by linear_combination h'
    have h0 : x.fst = 0 := by
      rw [← hx', residue_eq_zero_iff, ha]
      exact Ideal.mul_mem_left _ _ he
    refine mem_nilradical.2 ⟨2, ?_⟩
    rw [pow_two]
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show a * a = 0
      rw [ha]
      linear_combination (c * c) * hee
    · show x * x = 0
      ext
      · simp [h0]
      · simp [DualNumber.snd_mul, h0]
  refine ⟨P, inferInstance, i, p, σ, q, rfl, hσi, rfl, ?_, ?_, ?_, ?_⟩
  · exact IsClosedImmersion.spec_of_surjective _ hsurj
  · refine ⟨fun x ↦ ?_⟩
    have := range_comap_of_surjective _ σ hsurj
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker σ : Set P) := fun a ha ↦
      @nilradical_le_prime _ _ x.asIdeal x.isPrime _ (hker ha)
    rw [← this] at hx
    exact hx
  · refine GlobalTheory.T.affineMilnorSquare_of_cartesian_ring_square _ _ _ _ _ _ _ _ ?_ ?_ ?_ Ideal.Quotient.mk_surjective
    · refine RingHom.ext fun x ↦ ?_
      refine (Ideal.Quotient.eq.2 ?_).symm
      show x.1.1 + φ x.1.2.snd - x.1.1 ∈ _
      simpa using hφmem _
    · rintro ⟨⟨a, x⟩, hx⟩ h1 h2
      have hx' : residue C a = x.fst := hx
      have h1' : a = 0 := h1
      have h2' : a + φ x.snd = 0 := h2
      subst h1'
      rw [zero_add] at h2'
      refine Subtype.ext (Prod.ext rfl ?_)
      show x = 0
      ext
      · simp [← hx']
      · simpa using hφ0 _ h2'
    · intro a b hab
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hab.symm)
      refine ⟨⟨(a, ⟨residue C a, residue C c⟩), rfl⟩, rfl, ?_⟩
      show a + φ (residue C c) = b
      rw [hφ, hc]
      ring
  · refine GlobalTheory.T.affineMilnorSquare_of_cartesian_ring_square _ _ _ _ _ _ _ _ ?_ ?_ ?_ (fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩)
    · exact RingHom.ext fun x ↦ x.2
    · intro x h1 h2
      exact Subtype.ext (Prod.ext h1 h2)
    · intro a b hab
      exact ⟨⟨(a, b), hab⟩, rfl, rfl⟩

end GlobalTheory.DualOpen
end
