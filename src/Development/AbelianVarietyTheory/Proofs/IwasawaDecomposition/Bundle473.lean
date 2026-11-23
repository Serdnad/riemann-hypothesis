module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle448
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle111
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle444
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle441
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle399
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle464
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

noncomputable section

namespace GlobalTheory.ToricTorsionSec

open ReciprocityTheory.ChartRestriction.G.DVR

theorem isPull_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}
    {a : T'.left ⟶ T.left} {b : T''.left ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPull b g' g'') : GtPt.IsPull (b ≫ a) g g'' := by
  refine ⟨by rw [h'.1, h.1, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  rw [val_corr hJ (h'.2 χ), val_pull hJ, val_corr hJ (h.2 χ), val_pull hJ, val_pull hJ, Category.assoc]

theorem isPullF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {a : T'.left ⟶ T.left} {b : Sp F ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPtF D F}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPullF F b g' g'') : GtPt.IsPullF F (b ≫ a) g g'' :=
  isPull_trans (T'' := TF (R := R) F) (g'' := ⟨g''.b, g''.s, g''.isGen, g''.s_zero, g''.mult⟩) h h'

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem appTop_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    (spMap f).appTop.hom (unitOn u).val = (unitOn (Units.map f.toMonoidHom u)).val := by
  have e := congrArg (fun φ => φ.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact e.symm

theorem isPullF_torusPt {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (τ : Multiplicative D.X →* Fˣ)
    (g : GtPt D (Over.mk (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))))
    (hg : ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ)))) (q : GtPtF D F) (hq : GlobalTheory.UT.IsTor τ q) :
    GtPt.IsPullF F (𝟙 _) g q := by
  refine ⟨?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · rw [hq.1, (hg 0).1, Category.id_comp, Hom.one_def, DegPre.zeroT, Over.comp_left, Over.comp_left]
    congr 1
    have e₁ := Over.w (toUnit (TF (R := R) F))
    have e₂ := Over.w (toUnit (Over.mk (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))))
    simp only [Over.mk_hom] at e₁ e₂
    rw [← Category.comp_id (toUnit (TF (R := R) F)).left, ← Category.comp_id (toUnit (Over.mk _)).left]
    exact e₁.trans ((spMap_comp _ _).symm.trans e₂.symm)
  · refine Units.ext ?_
    rw [hq.2 χ y J hJ, val_pull hJ, Category.id_comp, GlobalTheory.TorusTorsion.TorusVal.val_eq (hg χ) _ hJ]
    exact gs_unit (𝟙 _) y ⊤ trivial (unitOn (τ (Multiplicative.ofAdd χ)))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) → ∀ k : ℕ, 1 ≤ k →
    ∃ s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G),
      (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
        a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A') (f : A →+* A')
        (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
        a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
        (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a : R →+* F) τ h (q : QkPt P.D.toPre F k),
        a = (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
        GlobalTheory.FlatTors.IsImage P F k q (s F a τ h).left := by
  intro E _ _ _ H R _ _ _ t P _ hR k hk
  obtain ⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩ :=
    GlobalTheory.WholeBaseFinitePart.exists_torsion_toG E H R hR t P k hk
  let u : ∀ (A : Type) [CommRing A] (_ : Multiplicative P.D.toPre.X →* Aˣ),
      P.D.toPre.X →+ Additive Γ(Sp A, ⊤)ˣ := fun A _ τ =>
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  have hu : ∀ (A : Type) [CommRing A] (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → k • u A τ = 0 := by
    intro A _ τ hτ
    refine AddMonoidHom.ext fun χ => Additive.toMul.injective ?_
    have e : (τ (Multiplicative.ofAdd χ)) ^ k = 1 := by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    simp only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e,
      map_one, AddMonoidHom.zero_apply, toMul_zero]
  have ex : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ),
      ∃ g : GtPt P.D.toPre (Over.mk (spMap a)), ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ))) := by
    intro A _ a τ
    obtain ⟨g, hg⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := P.D.toPre) (T := Over.mk (spMap a)) (u A τ)
    exact ⟨g, hg⟩
  choose gT hgT using ex
  have ex₂ : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 →
      ∃! h : Over.mk (spMap a) ⟶ N, GtPt.IsPull h.left g₀ (gT A a τ) := by
    intro A _ a τ hτ
    obtain ⟨g', h₁, h₂⟩ := GlobalTheory.TorusTorsion.exists_nsmul_zero k (u A τ) (hu A τ hτ) (T := Over.mk (spMap a))
      (g := gT A a τ) (hgT A a τ)
    exact hU _ _ ⟨g', h₁, h₂⟩
  choose hT hhT hTu using ex₂
  refine ⟨fun A _ a τ hτ => hT A a τ hτ ≫ x₀, fun A _ a τ hτ => ?_,
    fun A A' _ _ a a' f τ hτ τ' hτ' ha hτf => ?_, fun A A' _ _ a ha a' f t₀ m₀ τ hτ z ha' hz => ?_,
    fun F _ _ _ a τ hτ q ha hq hqt => ?_⟩
  · show (hT A a τ hτ ≫ x₀) ^ k = 1
    rw [← MonObj.comp_pow, htors, MonObj.comp_one]
  · subst ha
    let ρ : Over.mk (spMap (f.comp a)) ⟶ Over.mk (spMap a) := Over.homMk (spMap f) (spMap_comp a f).symm
    have hρ : GtPt.IsPull ρ.left (gT A a τ) (gT A' (f.comp a) τ') :=
      GlobalTheory.TorusTorsion.isPull_of_units ρ (hgT A a τ) (hgT A' _ τ') fun χ => by
        refine (appTop_unitOn f _).trans ?_
        congr 2
        exact Units.ext (hτf _).symm
    have e := hTu A' _ τ' hτ' (ρ ≫ hT A a τ hτ) (isPull_trans (hhT A a τ hτ) hρ)
    show (hT A' (f.comp a) τ' hτ' ≫ x₀).left = spMap f ≫ (hT A a τ hτ ≫ x₀).left
    rw [← e]
    rfl
  · subst ha'
    exact GlobalTheory.T.classified_torusTorsionPoint_eq_uniformisationTorus E H R t P N g₀ x₀ hform A A' a ha f t₀ m₀ τ z hz (gT A' _ τ) (hgT A' _ τ) (hT A' _ τ hτ)
      (hhT A' _ τ hτ)
  · subst ha
    have hx : OverGen F N (hT F _ τ hτ).left := (Over.w (hT F _ τ hτ)).trans (spMap_comp _ _)
    have hp := isPullF_trans (hhT F _ τ hτ) (isPullF_torusPt τ (gT F _ τ) (hgT F _ τ) q.g hqt)
    rw [Category.id_comp] at hp
    exact GlobalTheory.WholeBaseFinitePart.generic E H R hR t P k hk N g₀ x₀ hfin htors hform F _ hx q hq hp

end GlobalTheory.ToricTorsionSec
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.liftDefiniteForms_eq_unitaryForms_classSumPairing : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m) (t : T) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 i t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] W), LinearIndependent ℂ (fun k => j (Pi.single k 1)) → Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) = ⊤ → (∀ x x', ⟪j x, j x'⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A3.A F.lv2.P0 F.lv2.ψ0 i t) x x')) → ∃ J : W →ₗ[ℂ] (GA D ((y.L F.lv2).V i) → (y.L F.lv2).TauV i), Function.Injective J ∧ LinearMap.range J = (y.L F.lv2).Amt (y.tup t) i ∧ (∀ x x', ⟪x, x'⟫_ℂ = (y.L F.lv2).ipA (y.tup t) i (J x) (J x')) ∧ ∀ x, J (j x) = R.toRealDat.extV i t (R.toRealDat.jV i t (liftForm A3.A F.lv2.P0 F.lv2.ψ0 i t x)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.LiftForms.lift_forms_embed | exact GlobalTheory.Mem.R3.Rw.LiftForms.lift_forms_embed | (intros; apply GlobalTheory.Mem.R3.Rw.LiftForms.lift_forms_embed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF.DDHw

theorem dd_hw_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu → mu = (lam τ₀).w := by
  intro L _ _ _ n ι _ K _ _ emb lam hd τ₀ mu h
  classical
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨w, hwV, hw0, hB⟩ := GlobalTheory.T.highestWeight_doubleDual_upperTriangular_eigenvector L n ι K emb lam hd τ₀ mu h
  obtain ⟨φ, hφ0, hφV, hφA⟩ := GlobalTheory.T.exists_specialisation_coefficientSpace_to_dualWeyl K n ι lam τ₀ w hwV hw0
  refine GlobalTheory.T.nablaSq_upperEigenvector_weight_eq_highest K n (lam τ₀) mu (φ w) (hφV w hwV) hφ0 fun B hBt => ?_
  have hc0 : detPow K n B (lam τ₀).detShift ≠ 0 := by
    rw [detPow]; exact Units.ne_zero _
  rw [sqAct, ← hφA, hB B hBt, map_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end GlobalTheory.AlgWtF.DDHw
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.OpenLev
open Classical
variable {D : D7} {n : ℕ}

theorem cong_entry {N : ℕ} {κ : Formalism.AUTREP.GAf D.host.E n} (hκ : NG.Cong D.host.E n N κ) (i j : Fin n) :
    ∃ w ∈ GlobalTheory.StdFrameExist.SI D, (km D n κ).val i j - (1 : Matrix (Fin n) (Fin n) (EAf D)) i j = (N : EAf D) * w := by
  obtain ⟨w, hw, e⟩ := hκ.2 i j
  refine ⟨w, (GlobalTheory.StdFrameExist.mem_ALint_iff w).1 hw, ?_⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) (EAf D)) i j = (1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) i j := by
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h2 : (N : EAf D) = (N : ReciprocityTheory.Aut.AL D.host.E) := by
    induction N with
    | zero => simp
    | succ k ih => simp
  rw [h1, h2]
  exact e


theorem redFn_eq_one_of_cong {N : ℕ} {PP : Pl D.host.E} (hN : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    {κ : Formalism.AUTREP.GAf D.host.E n} (hκ : NG.Cong D.host.E n N κ) :
    redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 := by
  obtain ⟨y, hy⟩ := ((GlobalTheory.T.stdMaximalCompact_reduction_properties D n).2.1 κ).2 hκ.1
  rw [← hy, redFn_frGL]
  apply Units.ext
  ext i j
  have hyij : ((y.val i j : Herm.intAf D.host.F D.host.E) : EAf D) = (km D n κ).val i j := by
    rw [← hy]
    simp [frGL, intGL, Formalism.UG.bc]
  obtain ⟨w, hw', e⟩ := cong_entry hκ i j
  have h1 : (((1 : Matrix (Fin n) (Fin n) (Herm.intAf D.host.F D.host.E)) i j : Herm.intAf D.host.F D.host.E) : EAf D) =
      (1 : Matrix (Fin n) (Fin n) (EAf D)) i j := by
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have key : y.val i j - (1 : Matrix (Fin n) (Fin n) (Herm.intAf D.host.F D.host.E)) i j =
      (N : Herm.intAf D.host.F D.host.E) * ⟨w, hw'⟩ := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [hyij, h1]
    exact e
  have hN' : (N : kP PP) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hN
    simpa using this
  have k2 := congrArg (resS D.host.F PP) key
  rw [map_sub, map_mul, map_natCast, hN', zero_mul, sub_eq_zero] at k2
  have h3 : resS D.host.F PP ((1 : Matrix (Fin n) (Fin n) (Herm.intAf D.host.F D.host.E)) i j) =
      (1 : Matrix (Fin n) (Fin n) (kP PP)) i j := by
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  simp only [Formalism.UG.bc]
  show resS D.host.F PP (y.val i j) = _
  rw [k2, h3]
  rfl

theorem mem_stdJ_of {Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n} {κ : Formalism.AUTREP.GAf D.host.E n}
    (hU : km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E))
    (hS : km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)))
    (hr : ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) : κ ∈ stdJ Ld := by
  show km D n κ ∈ Formalism.L2.DIV.lev D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld
  refine Kg_le_lev (T := Ld.Pg ∪ Ld.Q) Finset.subset_union_left Finset.subset_union_right ?_
  exact ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hS, hr PP hP⟩⟩

theorem stdX_eq_one_of {Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n} {κ : Formalism.AUTREP.GAf D.host.E n} (h : κ ∈ stdJ Ld)
    (hr : ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) : stdX Ld ⟨κ, h⟩ = 1 := by
  show levFn (1 : GL (Fin n) (EAf D)) Ld (km D n κ) = 1
  have hT : rTup (1 : GL (Fin n) (EAf D)) Ld (km D n κ) = 1 := by
    funext PP
    show upperLeftBlock Ld.hr (redFn (1 : GL (Fin n) (EAf D)) PP.1 (km D n κ)) = 1
    rw [hr PP.1 (Finset.mem_union_left _ PP.2)]
    exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [hT, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [hr PP (Finset.mem_union_right _ hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hr PP (Finset.mem_union_left _ hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

theorem exists_nat_mem (T : Finset (Pl D.host.E)) :
    ∃ N : ℕ, 0 < N ∧ ∀ PP ∈ T, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  refine ⟨∏ PP ∈ T, Ideal.absNorm PP.asIdeal, Finset.prod_pos fun PP _ => Nat.pos_of_ne_zero fun h0 =>
    PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0), fun PP hP => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) hP
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem PP.asIdeal)

theorem stdJ_open : ∀ (D : D7) (n : ℕ) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n), stdJ Ld ≤ ReciprocityTheory.Aut.Umax D.host.E n ∧
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E n N κ → ∃ h : κ ∈ stdJ Ld, stdX Ld ⟨κ, h⟩ = 1) ∧
    ∀ B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))),
      (∀ PP, PP ∈ Ld.Pg ∨ PP ∈ Ld.Q → ∀ v, NG.OverPl PP v → v ∈ B) → NG.HypOutside (stdJ Ld) (stdX Ld) B := by
  intro D n Ld
  have R := GlobalTheory.T.stdMaximalCompact_reduction_properties D n
  have hle : stdJ Ld ≤ ReciprocityTheory.Aut.Umax D.host.E n := fun κ hκ =>
    (R.2.1 κ).1 (parLev_St (lev_le_parLev (show km D n κ ∈ Formalism.L2.DIV.lev D.sp.cm
      (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld from hκ)))
  refine ⟨hle, ?_, ?_⟩
  · obtain ⟨N, hN, hmem⟩ := exists_nat_mem (D := D) (Ld.Pg ∪ Ld.Q)
    refine ⟨N, hN, fun κ hκ => ?_⟩
    have hr : ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 :=
      fun PP hP => redFn_eq_one_of_cong (hmem PP hP) hκ
    have h := mem_stdJ_of (R.1 κ) ((R.2.1 κ).2 hκ.1) hr
    exact ⟨h, stdX_eq_one_of h hr⟩
  · intro B hB κ hκ
    have hr : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n →
        ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 := by
      intro hU PP hP
      have hov : NG.OverPl PP (PP.under (𝓞 (maximalRealSubfield D.host.E))) := by
        simp [NG.OverPl, HeightOneSpectrum.under_asIdeal, Ideal.under_def]
      refine R.2.2.1 κ hU Bᶜ _ PP hκ hov ?_
      exact fun hc => hc <| hB PP (Finset.mem_union.1 hP) _ hov
    exact ⟨⟨fun h => hle h, fun hU => mem_stdJ_of (R.1 κ) ((R.2.1 κ).2 hU) (hr hU)⟩,
      fun h => stdX_eq_one_of h (hr (hle h))⟩

end GlobalTheory.MtIn.OpenLev

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.UniMem

open ReciprocityTheory.Aut

theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    g ∈ Formalism.UG.GLint (Fin n) O := by
  first
  | exact @_root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries
  | exact _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries
  | (apply _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> assumption)
  | (intros; apply _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries ..)

theorem blkOf_lt_iff {n r t : ℕ} (hn : n = r + t) (i j : Fin n) :
    blkOf r t j < blkOf r t i ↔ j.val < r ∧ r ≤ i.val := by
  have hi := i.2
  have hj := j.2
  unfold blkOf
  by_cases hj' : j.val < r <;> by_cases hi' : i.val < r
  · simp [hj', hi']
  · simp [hj', hi']; omega
  · simp [hj', hi']
  · have e1 : (j.val - r) / t = 0 := Nat.div_eq_of_lt (by omega)
    have e2 : (i.val - r) / t = 0 := Nat.div_eq_of_lt (by omega)
    simp [hj', hi', e1, e2]

theorem redFn_eq_one (D : D7) (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (hU : κ ∈ Umax D.host.E D.R.nV) (hκ : TrivOutside {s.v} κ) (PP : Pl D.host.E) (hP : ¬ NG.OverPl PP s.v) :
    redFn (1 : GL (Fin D.R.nV) (EAf D)) PP (km D D.R.nV κ) = 1 := by
  refine (GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV).2.2.1 κ hU {s.v} (PP.under (𝓞 (maximalRealSubfield D.host.E))) PP hκ rfl ?_
  intro h
  apply hP
  rw [Set.mem_singleton_iff] at h
  rw [← h]
  rfl

theorem mem_iff : ∀ (D : D7) (hr : D.R.r ≤ D.R.nV) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ∀ a b, ∃ h : (s.loc D.R.nV κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, h⟩) → s.w ∈ Pg → (∀ PP ∈ Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) → (∀ PP ∈ Q, ¬ NG.OverPl PP s.v) → ∀ κ, ReciprocityTheory.Aut.TrivOutside {s.v} κ → (κ ∈ stdJ (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi) ↔ NG.UniRT s D.R.r (s.loc D.R.nV κ)) := by
  intro D hr Pg Q ψ chi xi s φ hφ0 hred hsw hPg hQ κ hκ
  have hUA := (GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV).1
  have hSt := (GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV).2.1
  have hn : D.R.nV = D.R.r + D.R.t := rfl

  have hent : ∀ κ' ∈ Umax D.host.E D.R.nV, ∀ a b (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)),
      (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = (s.loc D.R.nV κ').val a b →
      (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ')).val a b = φ x := by
    intro κ' hU' a b x hx
    obtain ⟨h, e⟩ := hred κ' hU' a b
    rw [e]
    congr 1
    exact Subtype.ext hx.symm
  have hint : ∀ κ' ∈ Umax D.host.E D.R.nV, ∀ a b,
      (s.loc D.R.nV κ').val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    fun κ' hU' a b => (hred κ' hU' a b).1
  have hzero : ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1 := hφ0
  have hone : ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      φ x = 1 ↔ Valued.v ((x : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 := by
    intro x
    rw [← sub_eq_zero, ← map_one φ, ← map_sub, hφ0]
    rfl
  constructor
  · intro hJ
    rw [stdJ, Subgroup.mem_comap, mem_lev, mem_parLev] at hJ
    obtain ⟨⟨-, hS, hg, -⟩, hT⟩ := hJ
    have hU : κ ∈ Umax D.host.E D.R.nV := (hSt κ).1 hS
    have hgw : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blkOf D.R.r D.R.t) := hg s.w hsw
    have hT' : upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)) ∈ unip (kP s.w) D.R.r :=
      hT ⟨s.w, hsw⟩ (Set.mem_univ _)
    have hb2 : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) :=
      blockTri_blkOf_le _ _ hgw
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine mem_GLint_of_entries _ _ (fun a b => hint κ hU a b) (fun a b => ?_)
      rw [← map_inv]
      exact hint κ⁻¹ (inv_mem hU) a b
    · intro a b ha hb
      have e : (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, hint κ hU a b⟩ :=
        hent κ hU a b ⟨_, hint κ hU a b⟩ rfl
      have h0 : (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = 0 :=
        (mem_blockTri.1 hgw) a b ((blkOf_lt_iff hn a b).2 ⟨hb, ha⟩)
      rw [h0] at e
      exact (hzero ⟨_, hint κ hU a b⟩).1 e.symm
    · intro a b ha hb
      have hR := upper_block_val_submatrix hr hb2
      have key : ∀ i j : Fin D.R.r, ((upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)) : GL (Fin D.R.r) (kP s.w)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP s.w)) i j = (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val (Fin.castLE hr i) (Fin.castLE hr j) := by
        intro i j; rw [hR]; rfl
      have ea : Fin.castLE hr (⟨a.val, ha⟩ : Fin D.R.r) = a := Fin.ext rfl
      have eb : Fin.castLE hr (⟨b.val, hb⟩ : Fin D.R.r) = b := Fin.ext rfl
      refine ⟨fun hba => ?_, fun hab => ?_⟩
      · have h0 := unip_lower hT' (i := ⟨a.val, ha⟩) (j := ⟨b.val, hb⟩) hba
        rw [key, ea, eb, hent κ hU a b ⟨_, hint κ hU a b⟩ rfl] at h0
        exact (hzero ⟨_, hint κ hU a b⟩).1 h0
      · subst hab
        have h1 := unip_diag hT' ⟨a.val, ha⟩
        rw [key, ea, hent κ hU a a ⟨_, hint κ hU a a⟩ rfl] at h1
        exact (hone ⟨_, hint κ hU a a⟩).1 h1
  · intro hu
    have hgl := hu.1.1
    have hU : κ ∈ Umax D.host.E D.R.nV := GlobalTheory.SplitHeckeComm.mem_Umax_of_loc s κ hκ hgl
    have hw : ∀ a b, (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, hint κ hU a b⟩ :=
      fun a b => hent κ hU a b _ rfl
    have hgw : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blkOf D.R.r D.R.t) := by
      rw [mem_blockTri]
      intro i j hij
      obtain ⟨hj, hi⟩ := (blkOf_lt_iff hn i j).1 hij
      rw [hw]
      exact (hzero ⟨_, hint κ hU i j⟩).2 (hu.1.2 i j hi hj)
    rw [stdJ, Subgroup.mem_comap, mem_lev, mem_parLev]
    refine ⟨⟨hUA κ, (hSt κ).2 hU, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
    · by_cases hPw : PP = s.w
      · rw [hPw]; exact hgw
      · rw [redFn_eq_one D s κ hU hκ PP (hPg PP hP hPw)]; exact Subgroup.one_mem _
    · rw [redFn_eq_one D s κ hU hκ PP (hQ PP hP)]; exact Subgroup.one_mem _
    · intro PP _
      show upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) PP.1 (km D D.R.nV κ)) ∈ unip (kP PP.1) D.R.r
      by_cases hPw : PP.1 = s.w
      · obtain ⟨PP, hPP⟩ := PP
        simp only at hPw
        subst hPw
        have hR := upper_block_val_submatrix hr (blockTri_blkOf_le _ _ hgw)
        refine ⟨fun i j (hij : j.val < i.val) => ?_, fun i => ?_⟩
        · rw [hR, Matrix.submatrix_apply, hw]
          exact (hzero ⟨_, hint κ hU (Fin.castLE hr i) (Fin.castLE hr j)⟩).2 ((hu.2 (Fin.castLE hr i) (Fin.castLE hr j) i.2 j.2).1 hij)
        · rw [hR, Matrix.submatrix_apply, hw]
          exact (hone ⟨_, hint κ hU (Fin.castLE hr i) (Fin.castLE hr i)⟩).2 ((hu.2 (Fin.castLE hr i) (Fin.castLE hr i) i.2 i.2).2 rfl)
      · rw [redFn_eq_one D s κ hU hκ PP.1 (hPg PP.1 PP.2 hPw)]
        have e1 : upperLeftBlock hr (1 : GL (Fin D.R.nV) (kP PP.1)) = 1 := blockDiagonalExtendByOnePrimeField_one _ (blkR hr)
        rw [e1]
        exact Subgroup.one_mem _

end GlobalTheory.MtIn.UniMem

end
end
