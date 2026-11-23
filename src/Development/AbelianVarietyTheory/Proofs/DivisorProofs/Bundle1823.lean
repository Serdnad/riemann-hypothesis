module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle313
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.SelfSmoothing

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def smoothings (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a) : Submodule ℂ (GA E a → ℂ) where
  carrier := {f | ∃ β, IsTest (invSet E a) β ∧ smoothing ν β φ.1 = f}
  zero_mem' := ⟨0, isTest_zero, funext fun x => by simp [smoothing]⟩
  add_mem' := by
    rintro _ _ ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
    refine ⟨β + γ, hβ.add hγ, funext fun x => ?_⟩
    refine Eq.trans ?_ (integral_add (hβ.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn)
      (hγ.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn))
    simp only [smoothing, Pi.add_apply, add_mul]
  smul_mem' := by
    rintro c _ ⟨β, hβ, rfl⟩
    refine ⟨fun y => β y * c, hβ.mul contDiff_const, funext fun x => ?_⟩
    refine Eq.trans ?_ (integral_const_mul c _)
    simp only [smoothing]
    congr 1
    funext y
    ring

theorem exists_smoothing_eq_self : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ →
    ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧ smoothing ν α φ.1 = φ.1 := by
  intro hP E _ _ _ a ν _ φ hφ
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, -, hV⟩ := GlobalTheory.T.exists_finiteDimensional_space_automorphic_smoothings hP E a ν φ hφ
  let V₀ : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  let V' : Submodule ℂ (GA E a → ℂ) := smoothings ν φ ⊓ V₀
  have hf : FiniteDimensional ℂ V' := Submodule.finiteDimensional_of_le (S₂ := V₀) inf_le_right
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨⟨α n, (hα n).1, rfl⟩, ⟨_, hv, rfl⟩⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  exact hφ'.1

end GlobalTheory.AutGrowth.SelfSmoothing
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem GlobalTheory.AutGrowth.tame_of_autForm (hP : GlobalTheory.Published.AutomorphicFormsFiniteGL) (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hφ : IsAutForm φ) : φ ∈ tame E a := by
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, hVt, hV⟩ := GlobalTheory.T.exists_finiteDimensional_space_automorphic_smoothings hP E a ν φ hφ
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨_, hv, rfl⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  obtain ⟨ψ, hψ, e⟩ := hφ'
  have e' : ψ = φ := Subtype.ext e
  exact hVt (e' ▸ hψ)

theorem GlobalTheory.AutGrowth.lie_growth_of_finite : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ →
    ∀ g : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖(GlobalTheory.CuspRep.lie E a X φ).1 (g * GlobalTheory.CuspRep.infGL E a y)‖ ≤
      C * GlobalTheory.CuspRep.height y ^ N := by
  intro hP E _ _ _ a X φ hφ
  exact growth_of_tame (lie_mem_tame X (GlobalTheory.AutGrowth.tame_of_autForm hP E a φ hφ))
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section

namespace GlobalTheory.Poinc.Tors
open GlobalTheory.TorusExt

private theorem sumF_mul_left {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} {x y : Ix → F} {s t : F} (a : F) (h : SumF I F x s)
    (hy : ∀ i, y i = a * x i) (ht : t = a * s) : SumF I F y t := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, happ⟩ := h
  let f : F →ₗ[R] F :=
    { toFun := fun u => a * u
      map_add' := fun u v => mul_add a u v
      map_smul' := fun r u => by
        change a * ((algebraMap R (FractionRing R) r) • u) = (algebraMap R (FractionRing R) r) • (a * u)
        rw [Algebra.smul_def, Algebra.smul_def]
        ring }
  refine ⟨N.map f, hN.map f, ⟨s, hs, ht.symm⟩, fun i => ⟨x i, hx i, (hy i).symm⟩, fun n => ?_⟩
  obtain ⟨S, hS⟩ := happ n
  refine ⟨S, fun T hT => ?_⟩
  have hm := Submodule.mem_map_of_mem (f := f) (hS T hT)
  rw [Submodule.map_smul''] at hm
  have e : f (s - ∑ i ∈ T, x i) = t - ∑ i ∈ T, y i := by
    change a * (s - ∑ i ∈ T, x i) = t - ∑ i ∈ T, y i
    rw [mul_sub, Finset.mul_sum, ht]
    simp only [hy]
  rw [e] at hm
  exact hm


attribute [local instance] gtGroup in
theorem exhaust_of_labels : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ N : ℕ, 1 ≤ N → ∀ (C : Type) (g : C → GtPtF D.toPre (FractionRing R)) (x : C → (TFK (R := R) (FractionRing R) ⟶ A.A)), (∀ c, ∃ o, GtPtF.IsNsmul N (g c) o ∧ o.IsZero) → (∀ c c', g c = g c' → x c = x c') → (∀ (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) N) (y : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A), p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing R)) N p y → ∃ c, y.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (x c).left) → ∀ b : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ D.toPre.P.A, b ^ N = 1 → ∃ c, b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (g c).b.left := by
  intro hLL R _ _ _ I hI D A G _ _ hSA U N hN C g x htor hfun hcov b hb
  have hB : D.toPre.TauBimult := D.tau_bimult
  have hN0 : N ≠ 0 := by omega
  have hf : (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp (algebraMap (FractionRing R) (FractionRing R)) = (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) :=
    RingHom.ext fun _ => rfl
  obtain ⟨fT, hT⟩ := GlobalTheory.TorsionIso.torsion_eq hLL R I hI D A G hSA U (AlgebraicClosure (FractionRing R)) N hN
  obtain ⟨hT1, -, hT3, -⟩ := hT
  have hi : GtPtF.IsIota 0 (0 : GtPtF D.toPre (AlgebraicClosure (FractionRing R))) := by
    have hz : (0 : GtPtF D.toPre (AlgebraicClosure (FractionRing R))).IsZero := (isZero_iff_eq _).2 rfl
    obtain ⟨hb, hv⟩ := (isZero_iff_val _).1 hz
    refine (isIota_iff_val _ _).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have C : IsCub (th D.toPre (T := TF (R := R) (AlgebraicClosure (FractionRing R))) y J) := isCub_cubV D.toPre.cub hJ
    have t := tau_mul (𝟙 (TF (R := R) (AlgebraicClosure (FractionRing R)))) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm
  let P : {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} → QkPt D.toPre (AlgebraicClosure (FractionRing R)) N :=
    fun h => ⟨0, h.1, N • h.1, (isNsmul_iff_eq _ _ _).2 rfl,
      h.2.symm ▸ hi⟩
  have hPy : ∀ h, (P h).y = 0 := fun _ => rfl
  have hPg : ∀ h, (P h).g = h.1 := fun _ => rfl
  have hEq : ∀ h h', QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (P h) (P h') → h = h' := by
    intro h h' e
    obtain ⟨z, hy, t, ht, hg⟩ := e
    change 0 = 0 + N • z at hy
    simp only [zero_add] at hy
    have hz : z = 0 := by
      have h2 : (N : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hy.symm
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact absurd (by exact_mod_cast h3 : N = 0) hN0
      · exact h3
    have ht0 : t = 0 := isIota_unique (hz ▸ ht) hi
    have hg := (isAdd_iff_eq _ _ _).1 hg
    rw [hPg, hPg, ht0, add_zero] at hg
    exact Subtype.ext hg.symm
  haveI : Finite {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} := by
    have hc := GlobalTheory.UT.card_qk hLL R I hI D (AlgebraicClosure (FractionRing R)) N hN
    haveI : Finite (Quot (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N))) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hN0)
    refine Finite.of_injective (β := Quot (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N)))
      (fun h => Quot.mk (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N)) (P h)) fun h h' e => hEq h h' ?_
    exact (equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact e)
  have hcx : ∀ h, ∃ c, (fT (P h)).left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (x c).left :=
    fun h => hcov (P h) (fT (P h)) (hPy h) ((hT1 _ _).2 rfl)
  choose c hc using hcx
  have hgc : ∀ c, N • g c = 0 := by
    intro c
    obtain ⟨o, ho, hz⟩ := htor c
    rw [isNsmul_iff_eq] at ho
    rw [isZero_iff_eq] at hz
    rw [← ho, hz]
  let Φ : {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} → {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} :=
    fun h => ⟨gtExt D.toPre (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) hf (g (c h)), by rw [← map_nsmul, hgc, map_zero]⟩
  have hΦ : Function.Injective Φ := by
    intro h h' e
    have e1 : g (c h) = g (c h') := GlobalTheory.Balanced.gtExt_injective _ hf D.toPre (congrArg Subtype.val e)
    have e2 := hfun _ _ e1
    apply hEq
    apply (hT3 _ _).1
    apply Over.OverMorphism.ext
    rw [hc h, hc h', e2]
  obtain ⟨g', hg'b, hg'N⟩ :=
    exists_nsmul_eq_of_pow_eq (D := D.toPre) (F := (AlgebraicClosure (FractionRing R))) hN0 0 (hb.trans zero_b.symm)
  obtain ⟨h, hh⟩ := (Finite.injective_iff_surjective.1 hΦ) ⟨g', hg'N⟩
  refine ⟨c h, ?_⟩
  have e1 : g' = gtExt D.toPre (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) hf (g (c h)) := (congrArg Subtype.val hh).symm
  rw [← hg'b, e1, gtExt_b, Over.comp_left, extMap_left]

section Scale
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

omit [IsDomain R] in
theorem exists_scale {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := R) F).left ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) {c : F} (hc : c ≠ 0) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ z J, Good L z J →
      (val t' (𝟙 _) z J).val = CoefBasic.cstH (R := R) z c * (val t (𝟙 _) z J).val := by
  let u : Γ((TF (R := R) F).left, ⊤)ˣ :=
    Units.map ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom : F →* Γ(Spec (CommRingCat.of F), ⊤)) (Units.mk0 c hc)
  refine ⟨GlobalTheory.UU.scaleGen u t, GlobalTheory.UU.scaleGen_isGen u ht, fun z J hJ => ?_⟩
  rw [GlobalTheory.UU.val_scaleGen u t (𝟙 _) hJ, Units.val_mul, ← gs_unit (𝟙 _) z ⊤ trivial u, ← CoefBasic.cst_eq]
  rfl

theorem coef_scale {D : DegPre R} {k : ℕ} (g : GtPtF D F) {w w' : Frm D F k g.b} (hw : w.IsGen) {c : F}
    (h : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = CoefBasic.cstH (R := R) z c * (val w (𝟙 _) z J).val)
    (s : Fam D F k) (χ : D.X) : coef s g w' χ = c * coef s g w χ := by
  apply CoefBasic.coef_eq
  intro z J hJ
  have hx := CoefBasic.isCoef_coef g hw χ s z J hJ
  rw [h z J hJ]
  rw [CoefBasic.cst_eq] at hx ⊢
  rw [map_mul]
  linear_combination (CoefBasic.cstH (R := R) z c) * hx

end Scale

theorem liesOver_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U) (g : GtPtF D.toPre F) (w : Frm D.toPre F 1 g.b) (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x), w.IsGen → fr.IsGen → LiesOver U w₀ g w x fr → ∀ c : F, c ≠ 0 → ∃ (w' : Frm D.toPre F 1 g.b) (fr' : FrAt x), w'.IsGen ∧ fr'.IsGen ∧ LiesOver U w₀ g w' x fr' ∧ (∀ (s : Fam D.toPre F 1) χ, c * coef s g w' χ = coef s g w χ) ∧ ∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val fr (𝟙 _) z J).val := by
  intro R _ _ I _ D A G _ _ U F _ _ w₀ g w x fr hw hfr hL c hc
  obtain ⟨w', hw', hw'v⟩ := exists_scale (R := R) (F := F) w hw (inv_ne_zero hc)
  obtain ⟨fr', hfr', hfr'v⟩ := exists_scale (R := R) (F := F) fr hfr hc
  refine ⟨w', fr', hw', hfr', ?_, ?_, ?_⟩
  · intro k hk wk hwk hwkg s s' v hexp hval
    have hck : c ^ k ≠ 0 := pow_ne_zero k hc
    obtain ⟨wk0, hwk0g, hwk0v⟩ := exists_scale (R := R) (F := F) wk hwkg hck
    have h1 : SumF I F (coef s' g wk0) (c ^ k * v) := by
      refine hL k hk wk0 ?_ hwk0g s s' (c ^ k * v) hexp ?_
      · intro z J hJ
        apply Units.ext
        have e : CoefBasic.cstH (R := R) z (c ^ k) * (CoefBasic.cstH (R := R) z c⁻¹) ^ k = 1 := by
          rw [← map_pow, ← map_mul, ← mul_pow, mul_inv_cancel₀ hc, one_pow, map_one]
        rw [hwk0v z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hw'v z J hJ]
        linear_combination ((val w (𝟙 _) z J).val) ^ k * e
      · intro z J hJ
        have hv := hval z J hJ
        rw [hv, GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, zpow_natCast, zpow_natCast,
          Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
          show (val fr' (𝟙 (TFK (R := R) F).left) z J).val =
            @id ((TFK (R := R) F).left.presheaf.stalk z) (CoefBasic.cstH (R := R) z c) * (val fr (𝟙 (TFK (R := R) F).left) z J).val from hfr'v z J hJ]
        simp only [id, CoefBasic.cst_eq, map_mul, map_pow]
        ring
    have h2 : ∀ χ, coef s' g wk0 χ = c ^ k * coef s' g wk χ := fun χ => coef_scale g hwkg hwk0v s' χ
    exact sumF_mul_left (c ^ k)⁻¹ h1
      (fun χ => by rw [h2, ← _root_.mul_assoc, inv_mul_cancel₀ hck, _root_.one_mul])
      (by rw [← _root_.mul_assoc, inv_mul_cancel₀ hck, _root_.one_mul])
  · intro s χ
    rw [coef_scale g hw hw'v s χ, ← _root_.mul_assoc, mul_inv_cancel₀ hc, _root_.one_mul]
  · intro z J hJ
    rw [show (val fr' (𝟙 (TFK (R := R) F).left) z J).val =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (CoefBasic.cstH (R := R) z c) * (val fr (𝟙 (TFK (R := R) F).left) z J).val from hfr'v z J hJ]
    simp only [CoefBasic.cst_eq, id]

end GlobalTheory.Poinc.Tors
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

theorem _root_.GlobalTheory.T.compactPart_centralizer_iff_integralUnits_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := by
  first | exact @GlobalTheory.InertUnitOrb.cptPart_iff_intUnits_of_model | exact GlobalTheory.InertUnitOrb.cptPart_iff_intUnits_of_model | (intros; apply GlobalTheory.InertUnitOrb.cptPart_iff_intUnits_of_model <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRowAdel

theorem deltaNorm_all (D : D7) : DeltaNorm D := by
  intro i σ
  have h := GlobalTheory.T.fockForm_minorProduct_eq_prod_hookProducts D (Wc D i).rank (Vc D i).rank (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ)
    (fun ρ => (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).2.2.1.le)
    (fun ρ => by
      obtain ⟨-, -, hpq, hWV⟩ := GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ
      exact ⟨by omega, by omega⟩)
    (fun ρ => ⟨(GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).1, (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).2.1⟩)
  simpa [deltaAtEmb] using h

end GlobalTheory.LowRowAdel
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_parabolic_unfold_levi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk (Nat.add_sub_cancel' ha) w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, twOrb (MonoidHom.id (GlobalTheory.LeviDesc.parP a n w)) ((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ⟨_, hγ⟩ (fun p => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (p : GLw n w)) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f) := by
  first | exact @GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding | exact GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding | (intros; apply GlobalTheory.LeviDesc.twistedOrbitalIntegral_parabolic_unfolding <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Y : G.Cˣ), (minpoly G.F (Y : G.C)).Separable →
    (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      ∃ z m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (z : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ k⁻¹ = z * m := by
  first | (exact @GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep) | (exact GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep) | (intros; apply GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep  <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FrameBox
open Matrix

theorem riemLie_frameBox_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∀ t : ℝ, 0 < t → riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} ≤ ENNReal.ofReal ((3 * t) ^ (Ψ.card * (r ^ 2 - 1))) := by
  classical
  intro E _ _ _ r κ p q Ψ G x σ A e hr hI t ht
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  set z : Fin r := ⟨0, hr⟩ with hz
  set d := sgnR σ e with hd_def
  have hd : ∀ τ a, d τ a = 1 ∨ d τ a = -1 := fun τ a => by
    simp only [d, sgnR]; split_ifs <;> simp
  have hinv := det_ne_zero_of_isIdent hI
  have hvW : ∀ k, boxVec d z k ∈ W := fun k =>
    (GlobalTheory.T.mem_realLie_iff_traceFree_skew_signs E r κ p q Ψ G x σ A e hI _).2 (GlobalTheory.T.skewHermitianBasisVector_traceFreeSkewCond E r Ψ d z hd k)
  let K := Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}
  let w : K → W := fun k => ⟨boxVec d z k, hvW k⟩
  have hdual := GlobalTheory.T.skewHermitianCoordinate_dual_basisVector E r Ψ d z hd
  have hcoord : ∀ (g : K → ℝ) j, boxCoord z j ((∑ k, g k • w k : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = g j := by
    intro g j

    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, w, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_eq_single j (fun k hk => by rw [if_neg (Ne.symm hk)])]
    rw [if_pos rfl]
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := hcoord g j
    rw [hg] at this
    simpa using this.symm
  have hcardK : Fintype.card K = Ψ.card * (r ^ 2 - 1) := by
    simp [K, Fintype.card_prod, Fintype.card_coe, sq]
  have hfin : Fintype.card K = Module.finrank ℝ W := by
    refine le_antisymm hli.fintype_card_le_finrank ?_
    rw [hcardK]
    rcases Ψ.eq_empty_or_nonempty with h0 | ⟨τ0, hτ0⟩
    · have hs : Subsingleton W := ⟨fun a b => Subtype.ext (PiLp.ext fun m => by
        have := m.1.2; simp [h0] at this)⟩
      rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _
    · have hG : G.det ≠ 0 := by
        intro h
        apply (hinv ⟨τ0, hτ0⟩).2
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
      exact finrank_comap_realLie_le Ψ G x hr hG fun τ => (hinv τ).1
  have hspan : Submodule.span ℝ (Set.range w) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hfin
  have hrep : ∀ Y : W, Y = ∑ k, boxCoord z k (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) • w k := by
    intro Y
    have hYs : Y ∈ Submodule.span ℝ (Set.range w) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hYs
    have h2 : ∀ j, boxCoord z j (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = c j := by
      intro j
      rw [← hc]
      exact hcoord _ j
    simp_rw [h2]; exact hc.symm
  set S := {X : Ψ → Fin r → Fin r → ℂ | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} with hS_def
  have hSo : IsOpen S := by
    simp only [hS_def, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => isOpen_lt ?_ continuous_const
    have : Continuous fun X : Ψ → Fin r → Fin r → ℂ => Matrix.of (X τ) := continuous_apply τ
    exact (((continuous_const.matrix_mul this).matrix_mul continuous_const).matrix_elem a b).norm
  have hf : Measurable (fun Y : W => fromFrame x Y.1) :=
    ((fromFrame x).comp W.subtype).continuous_of_finiteDimensional.measurable
  unfold riemLie
  rw [Measure.map_apply hf hSo.measurableSet, OrthonormalBasis.addHaar_eq_volume]
  have key1 : ∀ τ (M : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * M * (mat x τ)⁻¹) * mat x τ = M := fun τ M => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hinv τ).1.isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hinv τ).1.isUnit]
  have hsub : (fun Y : W => fromFrame x Y.1) ⁻¹' S ⊆
      {y : W | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k} := by
    intro Y hY
    have hY' : ∀ τ a b, ‖(Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, b)‖ < t := by
      intro τ a b
      have := hY τ a b
      have e1 : Matrix.of (fromFrame x Y.1 τ) =
          mat x τ * Matrix.of (fun a b => (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, b)) * (mat x τ)⁻¹ := rfl
      rwa [e1, key1] at this
    refine ⟨fun k => boxCoord z k (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)), fun k => ?_, hrep Y⟩
    obtain ⟨τ, ⟨⟨a, b⟩, hab⟩⟩ := k
    simp only [boxCoord]
    split_ifs
    · exact (Complex.abs_re_le_norm _).trans (hY' _ _ _).le
    · exact (Complex.abs_im_le_norm _).trans (hY' _ _ _).le
    · exact (Complex.abs_im_le_norm _).trans (hY' _ _ _).le
  refine (measure_mono hsub).trans ((GlobalTheory.T.volume_coordinateBox_le_hadamard W K w t ht.le hfin).trans (ENNReal.ofReal_le_ofReal ?_))
  have hn : ∀ k, ‖w k‖ = √2 := fun k => GlobalTheory.T.norm_skewHermitianBasisVector_eq_sqrt_two E r Ψ d z hd k
  simp only [hn, Finset.prod_const, Finset.card_univ]
  rw [hcardK, ← mul_pow]
  have h2 : 2 * t * √2 ≤ 3 * t := by
    have hs : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith
  exact pow_le_pow_left₀ (by positivity) h2 _

end GlobalTheory.CovTop.VolUp.FrameBox
end
end
