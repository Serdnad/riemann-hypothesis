module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle001
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle082
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle122
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals


open GlobalTheory.TorsionFormCompare GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum in
theorem hasUnif_of_iso {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (hV : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (G G₀ : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀]
    [IsCommMonObj G₀] (ε : G ≅ G₀) (hε : IsMonHom ε.hom) (hsa : IsSemiAbelian G₀) (L₀ : LB G₀.left)
    (h : HasUnif G₀ L₀) : HasUnif G (L₀.pull ε.hom.left) := by
  obtain ⟨D, A₀, U₀, hL⟩ := h
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have he : eSec G ≫ ε.hom.left = 𝟙 _ ≫ eSec G₀ := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε.hom)
  let L' : RigLB G := ⟨U₀.LG.L.pull ε.hom.left, rigPullOf ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig,
    LB.isLB_pull U₀.LG.isLB _,
    GlobalTheory.CubePullLawChecks.rigPullIsGen ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig U₀.LG.isLB U₀.LG.rigGen⟩
  let w : LB.Iso L'.L (U₀.LG.L.pull ε.hom.left) := idIso L'.L
  have hw : RigAlong ε.hom U₀.LG L' w :=
    ⟨idIso_isGen L'.isLB, (maps_iff w _ (fun _ => eSec G₀) _ L'.rig U₀.LG.rig (𝟙 _) _
      (rigPull_le _ _ he U₀.LG.L) (fun _ => rfl)).1 (idIso_maps L')⟩
  obtain ⟨W, hW, hψ⟩ := psiOnExists V (IsLocalRing.maximalIdeal V) hR D
  obtain ⟨hD, -⟩ := exists_isIdPull V D.toPre W hW hψ
  obtain ⟨bc, U, -, -, hLG, -, -⟩ :=
    exists_unif_move V (IsLocalRing.maximalIdeal V) D A₀ G₀ G ε hR hsa hε U₀ L' w hw hD
  refine ⟨D, A₀, U, ?_⟩
  rw [hLG]
  exact LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hL

theorem unifAlong_bG {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) {R : Type} [CommRing R]
    (f : Sp R ⟶ S) (hG : IsSemiAbelian G) (h : UnifAlong G L.L) : UnifAlong (bG G f) (bL L f).L := by
  intro V _ _ _ _ hV hf ξ hξ _
  have hξ' : ((ξ ≫ f) ⁻¹' abLocus G).Nonempty := by
    obtain ⟨p, hp⟩ := hξ
    refine ⟨p, ?_⟩
    have := (abLocus_pullback (G' := bG G f) abLocusOne hG (isGrpPullback_pullback G f).1 (ξ p)).2 hp
    simpa using this
  obtain ⟨ε, hε, hφ⟩ := grpPullback_iso ((isGrpPullback_pullback (bG G f) ξ).comp (isGrpPullback_pullback G f))
    (isGrpPullback_pullback G (ξ ≫ f))
  obtain ⟨D, A, U, hU⟩ := hasUnif_of_iso hV _ _ ε hε (IsSemiAbelian.pullback (ξ ≫ f) G hG) _ (h V hV hf (ξ ≫ f) hξ')
  refine ⟨D, A, U, LBIso.trans U.LG.isLB (LB.isLB_pull (LB.isLB_pull L.isLB _) _)
    (LB.isLB_pull (bL L f).isLB _) hU ?_⟩
  exact LBIso.chartPull (h := ε.hom.left)
    (chartPullLinComb L.L _ (fun _ : PUnit => ε.hom.left) (fun _ => pullback.fst G.hom (ξ ≫ f)) (fun _ => 1) _ fun _ => rfl)
    (chartPullLinComb L.L _ (fun _ : PUnit => pullback.fst (bG G f).hom ξ) (fun _ => pullback.fst G.hom (ξ ≫ f))
      (fun _ => 1) _ fun _ => hφ.symm)
    (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _))

theorem unifAlong_affineOpen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsSemiAbelian G → UnifAlong G L.L → UnifAlong (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L :=
  fun _ G _ _ L _ hW hG h => unifAlong_bG G L hW.fromSpec hG h

end GlobalTheory.KeyVals

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

theorem formEq_psi {R : Type} [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) [IsMonHom f]
    (x x' : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (hx : x' = x ≫ f) :
    FormEq (Sum.elim (Sum.elim (PolDeg.lamPts x x') fun k => x.left ≫ w0φ D₀ f k) fun _ : PUnit => eSec D₀.P.A)
      (Sum.elim (Sum.elim PolDeg.negε w0ε) fun _ => (-1 : ℤ)) (fun _ : PUnit => x.left) (fun _ => (-1 : ℤ)) := by
  intro U _ h
  subst hx
  have m₁ : x ≫ padd D₀.P.A (𝟙 _) f = x * (x ≫ f) := (MonObj.comp_mul _ _ _).trans (by simp)
  have m₃ : x ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]) = 1 := by
    rw [← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit _), ← Hom.one_def]
  have m₄ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have e₁ : x.left ≫ (padd D₀.P.A (𝟙 _) f).left = (x * (x ≫ f)).left := by rw [← Over.comp_left, m₁]
  have e₂ : x.left ≫ f.left = (x ≫ f).left := (Over.comp_left _ _ _ _ _).symm
  have e₃ : x.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left := by
    rw [← Over.comp_left, m₃]
  have e₄ : eSec D₀.P.A = (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left := by rw [m₄]; rfl
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
    PolDeg.lamPts, PolDeg.negε, w0φ, w0ε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e₁, e₂, e₃, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

theorem exists_psi_rLaws : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ w0 : O, w0 + star w0 = 1 → ∀ uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ τ' : ∀ y z : D₀.X, LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.PolDeg.lamPts (D₀.c y) (D₀.c z)) GlobalTheory.PolDeg.negε),
    GlobalTheory.UTau0.BalTau ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub onB.toRingAct D₀.c τ' →
    (∀ y z p J, Good D₀.P.L p J → val (τ' y z) (𝟙 _) p J = val (τ' z y) (𝟙 _) p J) →
    ∃ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
      GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ := by
  intro R _ _ _ D₀ O _ _ _ onB hc w0 hw uw huw uw0 τ' hbal hsym
  haveI := onB.hom w0
  haveI := onB.hom (star w0)
  obtain ⟨u, hu, hu0⟩ := exists_ros GlobalTheory.globalFns_holds D₀.P.isAb D₀.P.isLB (onB.act w0) (onB.act (star w0))
    (onB.rosati w0)
  have hfg : padd D₀.P.A (onB.act w0) (onB.act (star w0)) = 𝟙 _ := by
    rw [← onB.map_add, hw, onB.map_one]
  have cadd : ∀ a b, D₀.c (a + b) = D₀.c a * D₀.c b := fun a b => D₀.c_add a b
  have c0 : D₀.c 0 = 1 := by
    have := cadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
  have cneg : ∀ a, D₀.c (-a) = (D₀.c a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_left (by rw [← cadd, neg_add_cancel, c0])
  let t := fun y : D₀.X => LB.mulGen D₀.P.L _ _ _ _
    (LB.mulGen D₀.P.L _ _ _ _ (τ' y (w0 • y)) (LB.pullGen D₀.P.L _ _ uw (D₀.c y).left))
    (LB.invGen D₀.P.L (fun _ : PUnit => eSec D₀.P.A) (fun _ => 1) D₀.rig)
  have ht : ∀ y, (t y).IsGen := fun y => DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hbal.1 y _) (DVR.pullGen_isGen _ _ _ _ huw _))
    (DVR.invGen_isGen _ _ _ _ D₀.rig_gen)
  choose ψ hψ hψv using fun y => exists_gen D₀.P.isLB (formEq_psi D₀ (onB.act w0) (D₀.c y) _ (hc w0 y)) (t y) (ht y)
  have Vψ : ∀ y p J, Good D₀.P.L p J → val (ψ y) (𝟙 _) p J =
      val (τ' y (w0 • y)) (𝟙 _) p J * val uw (D₀.c y).left p J * (rigV D₀ p J)⁻¹ := by
    intro y p J hJ
    rw [hψv y _ _ p J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, Category.id_comp]
    rfl
  have key : ∀ y z p J, Good D₀.P.L p J → tauV D₀ ψ p J y z = val (τ' y z) (𝟙 _) p J := by
    intro y z p J hJ
    have e1 := hbal.2.1 y z (w0 • y + w0 • z) p J hJ
    have e2 := hbal.2.2.1 y (w0 • y) (w0 • z) p J hJ
    have e3 := hbal.2.2.1 z (w0 • y) (w0 • z) p J hJ
    have e4 := hsym z (w0 • y) p J hJ
    have e5 := hbal.2.2.2 w0 u hu hu0 y z p J hJ
    have e6 := hbal.2.2.1 y (w0 • z) (star w0 • z) p J hJ
    rw [← add_smul, hw, one_smul] at e6
    have g := GlobalTheory.T.symmetricPullbackGenerator_second_difference R D₀ (onB.act w0) (onB.act (star w0)) hfg uw huw uw0 u hu hu0 _ (D₀.c y) (D₀.c z) p J hJ
    simp only [cadd, hc] at e1 e2 e3 e6
    unfold tauV
    rw [Vψ _ p J hJ, Vψ _ p J hJ, Vψ _ p J hJ, smul_add]
    simp only [cadd]
    apply Additive.ofMul.injective
    have E := fun {a b : ((𝟙_ (Over (Sp R))).left.presheaf.stalk p)ˣ} (e : a = b) => congrArg Additive.ofMul e
    have a1 := E e1; have a2 := E e2; have a3 := E e3; have a4 := E e4; have a5 := E e5; have a6 := E e6
    have b1 := E g
    simp only [ofMul_mul, ofMul_inv] at a1 a2 a3 a4 a5 a6 b1 ⊢
    linear_combination (norm := abel) a1 + a2 + a3 + b1 + a4 + a5 - a6
  refine ⟨ψ, hψ, ?_, ?_, ?_, ?_⟩
  · intro y y' z p J hJ
    rw [key _ _ p J hJ, key _ _ p J hJ, key _ _ p J hJ]
    exact hbal.2.1 y y' z p J hJ
  · intro y p J hJ
    have C := isCub_cubV D₀.cub hJ
    rw [Vψ _ p J hJ, Vψ _ p J hJ, smul_neg]
    have f1 := hbal.2.1 y (-y) (w0 • y) p J hJ
    have z1 := hbal.2.1 0 0 (w0 • y) p J hJ
    have f2 := hbal.2.2.1 (-y) (w0 • y) (-(w0 • y)) p J hJ
    have z2 := hbal.2.2.1 (-y) 0 0 p J hJ
    rw [add_neg_cancel] at f1 f2
    rw [add_zero] at z1 z2
    have g := GlobalTheory.T.symmetricPullbackGenerator_even_value R D₀ (onB.act w0) uw huw uw0 _ (D₀.c y) p J hJ
    simp only [cneg, hc, c0] at f1 z1 f2 z2 ⊢
    rw [C.face] at z1 z2
    apply Additive.ofMul.injective
    have E := fun {a b : ((𝟙_ (Over (Sp R))).left.presheaf.stalk p)ˣ} (e : a = b) => congrArg Additive.ofMul e
    have a1 := E f1; have a2 := E f2; have a3 := E z1; have a4 := E z2; have b1 := E g
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at a1 a2 a3 a4 b1 ⊢
    linear_combination (norm := abel) b1 + a1 - a2 + a3 - a4
  · intro a u' hu' hu0' y z p J hJ
    rw [key _ _ p J hJ, key _ _ p J hJ]
    exact hbal.2.2.2 a u' hu' hu0' y z p J hJ
  · intro y p J hJ
    rw [key _ _ p J hJ, Vψ _ p J hJ, inv_mul_cancel_right]

end GlobalTheory.UTau0
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatVal

theorem rsT_self {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) : rsT s O₀ = s := by
  simp [GlobalTheory.KS.rsT]

theorem valR_eq {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom) f := by
  unfold valR; rw [dite_eq_left h]; rfl

theorem value_opV_ringOp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* (FractionRing Ω)), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = (algebraMap Ω (FractionRing Ω)) (φ r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ σ' : SecM (𝟙 t.G.left) t.PP.L k) (r a : R) (ω : Ω), (∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i))) → IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ ω' : Ω, IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ (algebraMap Ω (FractionRing Ω)) ω' = (algebraMap Ω (FractionRing Ω)) (φ r) * ((algebraMap Ω (FractionRing Ω)) (φ a) * ringOp ⇑dt (fun b => ⇑(δL b)) (iota.mapMatrix Θ₁) u' p p' k ((algebraMap Ω (FractionRing Ω)) ω) - 2 * (k : (FractionRing Ω)) * (algebraMap Ω (FractionRing Ω)) (φ (D a)) * (algebraMap Ω (FractionRing Ω)) ω) := by
  intro E _ _ _ H R _ _ _ _ _ _ t c hc n v' D Ω _ _ _ φ x' δ dd' hadic hx' hinv hδφ hval hinj g hg δL hδL Θ₁ DV hDV iota hiota J W j d u pf pf' hW hcov hWU hfield hlift hglue
  have hφ : Function.Injective φ := GlobalTheory.T.injective_ringMap_of_pointValues_detect_functions R t.G Ω φ x' hx' hinj
  have hφc : φ c ≠ 0 := fun h => hc (hφ (by rw [h, map_zero]))
  haveI : CharZero Ω := charZero_of_injective_ringHom (φ.comp (algebraMap ℚ R)).injective
  haveI : CharZero (FractionRing Ω) :=
    charZero_of_injective_ringHom (IsFractionRing.injective Ω (FractionRing Ω))
  obtain ⟨i0, hi0⟩ := GlobalTheory.T.exists_cover_member_containing_fractionField_point R t.G Ω φ x' hx' c hφc J W hcov
  obtain ⟨dt0, hdt0⟩ := GlobalTheory.T.exists_derivation_fractionRing_of_vectorField t.G.left Ω x' hinj (W i0) (d i0) (hfield i0) hi0
  have hddv := fun a => GlobalTheory.T.pointValue_fractionField_comm_vectorField t.G.left Ω x' (dd' a) (δ a) (δL a) (hinv a).1 (hval a) (hδL a)
  have hcst := GlobalTheory.T.pointValue_fractionField_eq_basicOpen_extension R t.G Ω φ x' hx' c iota hiota (W i0) (hW i0) hi0
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.chartFunction_eq_value_mul_unit_pow_fractionField t.G.left t.PP.L t.PP.isLB Ω x' g (j i0) (W i0) (hWU i0) hi0
  set ψ : Γ(t.G.left, W i0) →+* FractionRing Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom.comp
      ((spMap (algebraMap Ω (FractionRing Ω)) ≫ x').appLE (W i0) ⊤ hi0).hom with hψ
  have hv : ∀ f, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') (W i0) f = ψ f :=
    fun f => valR_eq _ _ hi0 f
  have hd0 : ∀ F, ψ (d i0 (W i0) F) = dt0 (ψ F) := by
    intro F; rw [← hv, ← hv]; exact hdt0 _ _ le_rfl hi0
  have hdd : ∀ a F, ψ (dd' a (W i0) F) = δL a (ψ F) := by
    intro a F; rw [← hv, ← hv]; exact hddv a _ _ hi0
  have hc' : ∀ θ, ψ (GlobalTheory.HeatV.cst t.G.hom _ (hW i0) θ) = iota θ := by
    intro θ; rw [← hv]; exact hcst θ
  obtain ⟨dt, u', p, p', hdt, hgauge⟩ := GlobalTheory.T.heatRingOperator_conj_by_pow_nonzero Ω n dt0 δL (iota.mapMatrix Θ₁) two_ne_zero
    (fun a => iota (u a)) (ψ (pf i0)) (ψ (pf' i0)) (e₀ : FractionRing Ω) e₀.ne_zero
  have hdtR : ∀ r, dt (algebraMap Ω (FractionRing Ω) (φ r)) = algebraMap Ω (FractionRing Ω) (φ (D r)) := by
    intro r
    rw [hdt _ (fun a => by rw [hδL, hδφ, map_zero]), ← hiota, ← hiota, ← hc', ← hc', ← hd0]
    have := hlift i0 (W i0) le_rfl (GlobalTheory.HeatV.resV R c r)
    rw [this, hDV]
  refine ⟨dt, u', p, p', hdtR, ?_⟩
  intro k hk σ σ' r a ω hσ' hω
  have hop : ∀ F, ψ (GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i0) (pf i0) (pf' i0) k (W i0) (hW i0) F) =
      ringOp ⇑dt0 (fun b => ⇑(δL b)) (iota.mapMatrix Θ₁) (fun a => iota (u a)) (ψ (pf i0)) (ψ (pf' i0)) k (ψ F) := by
    intro F

    simp only [GlobalTheory.HeatV.opV, ringOp, map_add (f := _), map_sub, map_mul, map_sum, map_natCast, map_ofNat, map_pow, hd0, hdd,
    hc', rsT_self, RingHom.mapMatrix_apply, Matrix.map_apply]
  obtain ⟨ω', hω'⟩ := GlobalTheory.T.exists_sectionValue_in_frame_localRing_point t.G.left t.PP.L t.PP.isLB Ω x' g hg k σ'
  refine ⟨ω', hω', ?_⟩
  have h1 := he₀ k σ ω hω
  have h2 := he₀ k σ' ω' hω'
  rw [hv] at h1 h2
  have h3 := congrArg ψ (hσ' i0)
  simp only [map_mul, map_sub, map_natCast, map_ofNat, hop, hc', hiota] at h3
  rw [h1, h2, mul_comm (algebraMap Ω (FractionRing Ω) ω) ((e₀ : FractionRing Ω) ^ k), hgauge] at h3
  apply mul_left_cancel₀ (pow_ne_zero k e₀.ne_zero)
  linear_combination h3

end GlobalTheory.HeatVal
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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

theorem isKS_symm_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (DV : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) DV Θ₁ → Θ₁ᵀ = Θ₁ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab c hc n v' dd' hinv DV Θ₁ hKS

  have hc' : spMap (resV R c) ≫ 𝟙 (Sp R) = chart (bo R c) := by
    rw [Category.comp_id]; exact spMap_resV R c
  obtain ⟨hv, hb⟩ : (∀ i, IsTanAtG t (spMap (resV R c) ≫ 𝟙 (Sp R))
        (spMap (dualMap (resV R c)) ≫ (tv (v' i)).left)) ∧
      ∀ w, IsTanAtG t (spMap (resV R c) ≫ 𝟙 (Sp R)) w →
        ∃! a : Fin n → Γ(Sp R, (bo R c).1), IsCombAtG t (spMap (resV R c) ≫ 𝟙 (Sp R))
          (fun i => spMap (dualMap (resV R c)) ≫ (tv (v' i)).left) a w := by
    refine GlobalTheory.LocM.FrameBase.tanBasis_baseChange t (resV R c) (𝟙 (Sp R)) n _
      (fun i => GlobalTheory.LieMet.isTan_tv (v' i)) ?_
    intro w hw
    refine ⟨v'.repr (GlobalTheory.LieMet.tanOf hw), ?_, fun a ha => ?_⟩
    · show IsCombAtG t _ _ _ (tv (GlobalTheory.LieMet.tanOf hw)).left
      rw [GlobalTheory.LieMet.isComb_iff]
      exact (v'.sum_repr _).symm
    · have h := (GlobalTheory.LieMet.isComb_iff v' a (GlobalTheory.LieMet.tanOf hw)).1 ha
      rw [h]
      ext i
      simp [Finsupp.single_apply]
  rw [hc'] at hv hb

  have hc0 : c ≠ 0 := by
    rw [hc]; exact Finset.prod_ne_zero_iff.2 fun i _ => htt i
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  let gg : Γ(Sp R, ⊤) →+* FractionRing R :=
    (algebraMap R (FractionRing R)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have hs : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s = c := by simp [s]
  have hu : IsUnit (gg s) := by
    rw [isUnit_iff_ne_zero]
    simp only [gg, RingHom.comp_apply, hs]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc0))
  have gg_inj : Function.Injective gg := by
    intro x y h
    have h1 := IsFractionRing.injective R (FractionRing R) h
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h1
  let x₀ : Γ(Sp R, (bo R c).1) →+* FractionRing R :=
    IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu
  have hx₀ : ∀ y, x₀ (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) y) = gg y := by
    intro y
    show IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu _ = _
    rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hinj : Function.Injective x₀ := by
    show Function.Injective (IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu)
    rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      have := congrArg x₀ h
      rwa [hx₀, hx₀] at this
    · intro h
      rw [gg_inj h]
  have hres : x₀.comp (resV R c) = algebraMap R (FractionRing R) := by
    ext r
    show x₀ (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    rw [hx₀]
    simp [gg]
  have hsp : spMap x₀ ≫ chart (bo R c) = ReciprocityTheory.ChartRestriction.G.Out.jK R := by
    rw [← spMap_resV R c]
    show Spec.map (CommRingCat.ofHom x₀) ≫ Spec.map (CommRingCat.ofHom (resV R c)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    rw [← hres, ← Spec.map_comp]
    rfl

  have gpG := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left)
      (t.PP.L.pull (pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R)) _ P.U.gen.inv.left
          fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have key := GlobalTheory.T.kodairaSpencer_matrix_transpose_eq_at_polarized_point E H (Sp R) t (bo R c).1 (bo R c) n _ hv hb (FractionRing R) x₀ P.A
    (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R)) (gpG.congr hsp.symm rfl) hL le_rfl DV Θ₁ hKS
  ext a b
  apply hinj
  have := congrFun (congrFun key a) b
  simpa [Matrix.transpose_apply, Matrix.map_apply] using this

end GlobalTheory.HeatV
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem _root_.GlobalTheory.T.classifyingMap_symplecticLevel_equivariant : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
  (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)), HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
  ∀ (ρ : sympSimGrp h M → (X ⟶ X)), SympActs s s₁ u lev ρ →
  ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)), (∀ a, ρ a ≫ s₁ = s₁ ≫ spMap (σ a)) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M))
    (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)) (o' : Obj b N (Y.hom ≫ t)) (m : ObjMap o' o Y.hom)
    (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y.left) ⟶ o'.A)), (∀ a, (lv' a).left ≫ m.φ = (lu a).left) →
    (∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv')) →
    ∀ (y : Y.left ⟶ X) (my : ObjMap o' u y), (∀ a, (lv' a).left ≫ my.φ = y ≫ (lev a).left) →
    y ≫ s = Y.hom ≫ t → y ≫ s₁ = t₁ →
    ∀ (r : sympSimGrp h M → (Y ⟶ Y)), (∀ a, (r a).left ≫ t₁ = t₁ ≫ spMap (σ a)) →
    (∀ a c, r a ≫ lu c = sympTwist a lu c) → ∀ a, (r a).left ≫ y = y ≫ ρ a := by
  first | exact @GlobalTheory.HTSympCover.classify_equivariant | exact GlobalTheory.HTSympCover.classify_equivariant | (intros; apply GlobalTheory.HTSympCover.classify_equivariant <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.chart_isOpenImmersion_over_base : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')) (j : Option (Fin n)), IsOpenImmersion (N.chart x j) ∧ N.chart x j ≫ G'.hom = pullback.snd N.U.hom π := by
  first | exact @GlobalTheory.Mum.Near.chart_isOpenImmersion_over | exact GlobalTheory.Mum.Near.chart_isOpenImmersion_over | (intros; apply GlobalTheory.Mum.Near.chart_isOpenImmersion_over <;> assumption)
end
