module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Heat

theorem isWt_rsT_of_isTerm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y k α σ τ hT j V hVj S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  have hle : Y.q.left ⁻¹ᵁ V ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U fun _ => j :=
    fun z hz => Set.mem_iInter.2 fun _ => hVj hz
  have hql : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := by
    have := congrArg CommaMorphism.left hq
    simpa using this

  have key : ((x'.left.appLE (Y.q.left ⁻¹ᵁ V) ⊤ hV').hom (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V))) =
      (show Γ((Over.mk (spMap φ)).left, ⊤) from (unitOn (c α)).val) * (x.left.appLE (Y.q.left ⁻¹ᵁ V) ⊤ hV).hom (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
    refine fn_ext fun y _ => ?_
    have hy : x.left y ∈ Y.q.left ⁻¹ᵁ V := hV trivial
    have hy' : x'.left y ∈ Y.q.left ⁻¹ᵁ V := hV' trivial
    obtain ⟨J, hJ, eJ⟩ := exists_good Q.P.L Q.P.isLB y (fun _ : Unit => x.left ≫ Y.q.left) (fun _ => j)
      (fun _ _ _ => rfl) (fun _ => hVj hy)
    have e := hT _ x' y J hJ
    have e0 := hT _ x y J hJ
    rw [hq, hc α y J hJ] at e
    rw [gs_mul (𝟙 _) y ⊤ trivial, gs_unit (𝟙 _) y ⊤ trivial, gs_appLE _ _ ⊤ _ (𝟙 _) y trivial,
      gs_appLE _ _ ⊤ _ (𝟙 _) y trivial, Category.id_comp, Category.id_comp]
    simp only [rsT, dif_pos hle]
    erw [gs_res _ y hle hy, gs_res _ y hle hy']
    have e1 := sval_of τ x'.left y J (fun _ => j) (fun _ => (congrArg J hql).trans (eJ ()))
    have e2 := sval_of τ x.left y J (fun _ => j) (fun _ => eJ ())
    rw [e1] at e
    rw [e2] at e0
    refine e.trans ?_
    refine Eq.trans ?_ (congrArg (fun t => _ * t) e0.symm)
    simp only [Units.val_mul]
    ring
  unfold valR
  rw [dif_pos hV, dif_pos hV', key, map_mul]
  congr 1
  simp [unitOn]

end GlobalTheory.Heat
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.TermWt

theorem isWt_term : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Fin 1 → Q.P.L.ι) (V : Y.H.left.Opens), V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j → IsWt Y α V (rsT (τ.f j) V) := by
  intro R _ _ Q O _ _ _ oa Y k α σ τ hT j V hV
  intro S _ φ x x' c a a' ha ha' hV₁ hV₂ hq hc
  subst ha ha'
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hV' : V ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U j := hV
  have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ V → ∀ z,
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (valR b V (rsT (τ.f j) V))) =
        gs b z (LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j) (τ.f j) := by
    intro b hb z
    rw [valR, dite_eq_left hb, Iso.hom_inv_id_apply, rsT, dite_eq_left hV']
    refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z V (hb trivial) _).trans ?_)
    rw [Category.id_comp]
    exact gs_res b z hV (hb trivial) _
  have hqq : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg CommaMorphism.left hq
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  refine fn_ext fun z _ => ?_
  obtain ⟨J, hJ, hJj⟩ := exists_good Q.P.L hL z (fun _ : Fin 1 => x.left ≫ Y.q.left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b))
    (fun i => Set.mem_iInter.1 (hV (hV₁ (show z ∈ (⊤ : (Sp S).Opens) from trivial))) i)
  have e₁ : ∀ i, J (x.left ≫ (fun _ : Fin 1 => Y.q.left) i) = j i := hJj
  have e₂ : ∀ i, J (x'.left ≫ (fun _ : Fin 1 => Y.q.left) i) = j i := fun i => by rw [hqq]; exact hJj i
  have t₁ := hT (Over.mk (spMap φ)) x z J hJ
  have t₂ := hT (Over.mk (spMap φ)) x' z J hJ
  rw [sval_of τ _ z J j e₁] at t₁
  rw [sval_of τ _ z J j e₂, hq, hc α z J hJ, Units.val_mul] at t₂
  show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
  rw [germ _ hV₂ z, t₂, map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₁ z, t₁,
    show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c α : S) = (unitOn (c α)).val from rfl,
    gs_unit (𝟙 _) z ⊤ trivial]
  exact _root_.mul_left_comm _ _ _

end GlobalTheory.Heat.TermWt
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Heat.ShiftGauge

theorem toUnit_left {R : Type} [CommRing R] (T : Over (Sp R)) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem exists_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (mu : Q.X) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), (x ≫ Y.q) * Q.c mu = 1 → ∀ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1), ψ₀.IsGen → ∃ e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1]), e.IsGen ∧ (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y (-mu) (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J = 1 := by
  intro R _ _ Q O _ _ _ oa Y mu x hx ψ₀ hψ₀
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hq : IsMonHom Y.q := Y.q_linear.isMonHom
  set Tx : Y.H ⟶ Y.H := 𝟙 Y.H * (toUnit Y.H ≫ x) with hTx

  have hTq : Tx ≫ Y.q = Y.q * (toUnit Y.H ≫ x ≫ Y.q) := by
    rw [hTx, MonObj.mul_comp, Category.id_comp, Category.assoc]
  have hcq : cP Q Y.H mu * (Tx ≫ Y.q) = Y.q := by
    rw [hTq, cP, _root_.mul_comm, _root_.mul_assoc, ← MonObj.comp_mul (toUnit Y.H) (x ≫ Y.q) (Q.c mu), hx,
      MonObj.comp_one, _root_.mul_one]
  have e₁ : (cP Q Y.H mu).left = Y.H.hom ≫ (Q.c mu).left := by rw [cP, Over.comp_left, toUnit_left]
  have e₂ : (1 : Y.H ⟶ Q.P.A).left = Y.H.hom ≫ eSec Q.P.A := by rw [Hom.one_def, Over.comp_left, toUnit_left]; rfl
  let s := (Y.Φ Y.H Tx).s mu
  let w := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ ψ₀ Y.H.hom)
    (LB.pullGen Q.P.L _ _ Q.rig Y.H.hom)) s
  have hw : w.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hψ₀ _)
    (pullGen_isGen _ _ _ _ Q.rig_gen _)) ((Y.Φ Y.H Tx).isGen mu)
  have hF : FormEq (Sum.elim (Sum.elim (fun _ : PUnit => Y.H.hom ≫ (Q.c mu).left)
      (fun _ : PUnit => Y.H.hom ≫ eSec Q.P.A)) (DegPre.gtφT Q Y.H (Y.Φ Y.H Tx).b mu))
      (fun k => - Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => (1 : ℤ))) DegPre.gtε k)
      (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] := by
    intro U _ h
    simp only [zpow_neg, Finset.prod_inv_distrib, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.prod_unique, Fin.prod_univ_two]
    rw [GlobalTheory.TorusModel.prod_pt, Ray.Φ_b, hcq, e₁, e₂]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Over.comp_left]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  obtain ⟨e, he, hve⟩ := exists_gen hL hF (LB.invGen Q.P.L _ _ w) (invGen_isGen _ _ _ _ hw)
  have hval : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J →
      val e y.left z J = (val ψ₀ T.hom z J * val Q.rig T.hom z J *
        val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J)⁻¹ := by
    intro T y z J hJ
    have hy : y ≫ Tx = y * (toUnit T ≫ x) := by
      rw [hTx, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit Y.H) (toUnit T)]
    have hp := ((GlobalTheory.TorusModel.isPull_iff y (Y.Φ Y.H Tx) (Y.Φ T (y ≫ Tx))).1 (Y.rep.1 T Y.H y Tx)).2 mu z J hJ
    rw [hve _ _ z J hJ, val_inv, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Over.w y, ← hy]
    rw [show val ((Y.Φ T (y ≫ Tx)).s mu) (𝟙 _) z J = _ from hp]
  refine ⟨e, he, ?_, fun T y z J hJ => ?_⟩
  · intro j V hV S _ φ x₁ x₁' c a a' ha ha' hV₁ hV₂ hqq hc
    subst ha ha'
    have hV' : Y.q.left ⁻¹ᵁ V ≤
        (LB.LinComb Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1]).U j := hV
    have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V) → ∀ z,
        gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
          (valR b (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))) =
          gs b z (LB.wchart Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) j)
            (e.s j).val := by
      intro b hb z
      rw [valR, dite_eq_left hb, Iso.hom_inv_id_apply, rsT, dite_eq_left hV']
      refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z _ (hb trivial) _).trans ?_)
      rw [Category.id_comp]
      exact gs_res b z hV (hb trivial) _
    have hq' : x₁'.left ≫ Y.q.left = x₁.left ≫ Y.q.left := congrArg CommaMorphism.left hqq
    have hu : ∀ u : Over.mk (spMap φ) ⟶ Y.H, u ≫ Tx ≫ Y.q = (u ≫ Y.q) * (toUnit _ ≫ x ≫ Y.q) := fun u => by
      rw [hTq, MonObj.comp_mul, ← Category.assoc u (toUnit Y.H), toUnit_unique (u ≫ toUnit Y.H) (toUnit _)]
    have hT₀ : x₁' ≫ Tx ≫ Y.q = x₁ ≫ Tx ≫ Y.q := by rw [hu, hu, hqq]
    have hT : x₁'.left ≫ Tx.left ≫ Y.q.left = x₁.left ≫ Tx.left ≫ Y.q.left := congrArg CommaMorphism.left hT₀
    have hk : ∀ k, x₁'.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k =
        x₁.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k :=
      Fin.forall_fin_two.2 ⟨hq', hT⟩
    apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
    refine fn_ext fun z _ => ?_
    choose I hI using fun χ : (Over.mk (spMap φ)).left ⟶ Q.P.A.left => exists_chart hL (χ z)
    have hJ : Good Q.P.L z I := hI
    have hgv : ∀ (b : Sp S ⟶ Y.H.left) (hb : ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)),
        gs b z (LB.wchart Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) j)
          (e.s j).val = (trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] b z j
            (fun k => I (b ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) *
            val e b z I).val := fun b hb =>
      (gs_unit b z _ (hV (hb trivial)) _).trans (congrArg Units.val (gen_trans he b z (hV (hb trivial)) (hJ.mem _ b)))
    have htr : trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] x₁'.left z j
          (fun k => I (x₁'.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) =
        trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] x₁.left z j
          (fun k => I (x₁.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) := by
      unfold trF
      exact Finset.prod_congr rfl fun k _ => congrArg (fun ψ => gm ψ z (Q.P.L.U (j k) ⊓ Q.P.L.U (I ψ)) (Q.P.L.g (j k) (I ψ)) ^ (![1, -1] : Fin 2 → ℤ) k) (hk k)
    have ve : val e x₁'.left z I = gm (𝟙 (Over.mk (spMap φ)).left) z ⊤ (unitOn (c (-mu))) * val e x₁.left z I := by
      have hb : (Y.Φ _ x₁').b = (Y.Φ _ x₁).b := by rw [Ray.Φ_b, Ray.Φ_b, hqq]
      have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁ (toUnit _ ≫ x))).2 mu z I hJ
      have h2 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁' (toUnit _ ≫ x))).2 mu z I hJ
      rw [hb] at h2
      have h3 := hc mu z I hJ
      have h4 := GlobalTheory.TorusModel.cv_add (Y.Φ _ x₁) hJ mu (-mu)
      have h5 := GlobalTheory.TorusModel.cv_add (Y.Φ _ x₁') hJ mu (-mu)
      rw [add_neg_cancel, GlobalTheory.TorusModel.cv_zero _ hJ] at h4 h5
      rw [hb] at h5
      have h6 := hc (-mu) z I hJ
      rw [hval _ x₁ z I hJ, hval _ x₁' z I hJ]
      apply Additive.ofMul.injective
      have g1 := congrArg Additive.ofMul h1
      have g2 := congrArg Additive.ofMul h2
      have g3 := congrArg Additive.ofMul h3
      have g4 := congrArg Additive.ofMul h4
      have g5 := congrArg Additive.ofMul h5
      have g6 := congrArg Additive.ofMul h6
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at g1 g2 g3 g4 g5 g6 ⊢
      linear_combination (norm := abel) g1 - g2 - g4 + g5 + g6
    show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
    rw [germ _ hV₂ z, map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₁ z, hgv _ hV₂, hgv _ hV₁, htr, ve,
      show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c (-mu) : S) = (unitOn (c (-mu))).val from rfl,
      gs_unit (𝟙 _) z ⊤ trivial, ← Units.val_mul]
    exact congrArg Units.val (_root_.mul_left_comm _ _ _)
  · rw [hval T y z J hJ]
    simp only [_root_.mul_assoc, inv_mul_cancel]

end GlobalTheory.Heat.ShiftGauge
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HeatTermLin

theorem gs_sub_fn {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq r z U h, map_sub]

theorem sval_sub_smul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s t : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (s - c • t) r z J = sval s r z J - gs r z ⊤ c * sval t r z J := by
  have hm := hJ.mem φ r
  have h1 : sval (s - c • t) r z J = sval s r z J - sval (c • t) r z J :=
    gs_sub_fn r z _ hm _ _
  have h2 : sval (c • t) r z J = gs r z ⊤ c * sval t r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm c))
  rw [h1, h2]

theorem gs_constFn {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (e : R) :
    gs r z ⊤ (constFn p ⊤ e) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom e) := by
  rw [← gs_pull r p z ⊤ trivial]
  exact gs_res r z (U := p ⁻¹ᵁ ⊤) (V := ⊤) le_top trivial _

theorem isTerm_sub_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) (τ τ' : SecM Y.q.left Q.P.L k) (e : R), IsTerm Y k α σ τ → IsTerm Y k α σ' τ' → IsTerm Y k α (σ' - constFn Q.P.A.hom ⊤ e • σ) (τ' - constFn Y.H.hom ⊤ e • τ) := by
  intro R _ _ Q Ω _ _ _ oa Y k α σ σ' τ τ' e h h' T x y J hJ
  have a := sval_sub_smul (constFn Y.H.hom ⊤ e) τ' τ x.left y hJ
  have b := sval_sub_smul (constFn Q.P.A.hom ⊤ e) σ' σ (x ≫ Y.q).left y hJ
  rw [gs_constFn, Over.w] at a b
  refine a.trans ?_
  rw [h T x y J hJ, h' T x y J hJ]
  refine Eq.trans ?_ (congrArg (· * _) b).symm
  ring

end GlobalTheory.HeatTermLin
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtLocal

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open GlobalTheory.TorusModel (isPull_iff)

theorem gm_comp' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  refine Units.ext ?_
  rw [← gs_unit (r ≫ q) z U h, ← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h,
    Category.id_comp, gs_unit q (r z) U h]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem isWt_of_local (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V))
    (h : ∀ (S : Type) [CommRing S] [IsLocalRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ),
      ⊤ ≤ x.left ⁻¹ᵁ V → ⊤ ≤ x'.left ⁻¹ᵁ V → x' ≫ Y.q = x ≫ Y.q →
      (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) →
      valR (A := S) x'.left V f = c α * valR (A := S) x.left V f) : IsWt Y α V f := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun P hP => (map_sub _ _ _).trans (sub_eq_zero.2 ?_))
  let l := algebraMap S (Localization.AtPrime P)
  let k : Over.mk (spMap (l.comp φ)) ⟶ Over.mk (spMap φ) := Over.homMk (spMap l)
    (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom l)).symm
  obtain ⟨a₁, a₂⟩ := valR_spMap l x.left V hV
  obtain ⟨b₁, b₂⟩ := valR_spMap l x'.left V hV'
  have := h _ (l.comp φ) (k ≫ x) (k ≫ x') (fun χ => Units.map l.toMonoidHom (c χ)) a₁ b₁
    (by rw [Category.assoc, Category.assoc, hq]) fun χ y J hJ => by
      have hJ' : Good Q.P.L (k.left y) fun ψ => J (k.left ≫ ψ) := fun ψ => hJ (k.left ≫ ψ)
      have key : ∀ u : Over.mk (spMap φ) ⟶ Y.H, val ((Y.Φ _ (k ≫ u)).s χ) (𝟙 _) y J =
          Units.map (k.left.stalkMap y).hom.toMonoidHom
            (val ((Y.Φ _ u).s χ) (𝟙 _) (k.left y) fun ψ => J (k.left ≫ ψ)) := fun u => by
        refine (((isPull_iff _ _ _).1 (Y.rep.1 _ _ k u)).2 χ y J hJ).trans ?_
        rw [val_of _ (𝟙 _) _ _ (fun i => J (k.left ≫ DegPre.gtφT Q _ (Y.Φ _ u).b χ i)) (fun i => by rw [Category.id_comp])]
        refine Eq.trans ?_ (gm_comp' k.left (𝟙 _) y _ (hJ.mem _ k.left) _)
        rw [Category.comp_id]
        rfl
      rw [key, key, hc χ _ _ hJ', map_mul, ← gm_comp' k.left (𝟙 _) y ⊤ trivial]
      congr 1
      refine Units.ext ?_
      rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
      refine congrArg ((Sp (Localization.AtPrime P)).presheaf.germ ⊤ y trivial).hom ?_
      exact (congrArg (fun q => q.hom (c χ : S)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom l))).symm
  rw [map_mul]
  exact (b₂ f).symm.trans (this.trans (congrArg (_ * ·) (a₂ f)))

end GlobalTheory.Heat.WtLocal

namespace GlobalTheory.Heat.WtLocal

open GlobalTheory.ZH.CrdCalc (valR_res)

theorem isWt_of_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V')), (∀ (g : Γ(Q.P.A.left, V.1)) (h : Q.P.A.left.basicOpen g ≤ V'), IsWt Y α (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) (resG Y.H.left (Y.q.left.preimage_mono h) f)) → IsWt Y α (Y.q.left ⁻¹ᵁ V') f := by
  intro R _ _ Q O _ _ _ oa Y V V' hV α f hf
  refine isWt_of_local Y α _ _ fun S _ _ φ x x' c hx hx' hq hc => ?_
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg (fun q => q.left) hq
  have hp : Y.q.left (x'.left (closedPoint S)) ∈ V' := hx' trivial
  obtain ⟨g, hg, hpg⟩ := V.2.exists_basicOpen_le ⟨_, hp⟩ (hV hp)
  have m' : ⊤ ≤ x'.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of S) x'.left hpg).ge
  have m : ⊤ ≤ x.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) := by
    rw [← Scheme.Hom.comp_preimage, ← e]; exact m'
  have t := hf g hg S φ x x' c _ _ rfl rfl m m' hq hc
  exact (valR_res (R := S) x'.left _ m' f).symm.trans (t.trans (congrArg (_ * ·) (valR_res (R := S) x.left _ m f)))

end GlobalTheory.Heat.WtLocal
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.VertCoeffGlue

theorem affine_cover {X : Scheme.{0}} (O : X.Opens) :
    O ≤ ⨆ l : {V : X.Opens // IsAffineOpen V ∧ V ≤ O}, l.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (O : Set X) from hx) O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, fun y hy => hle hy⟩, hxU⟩

theorem exists_coeff : ∀ {X : Scheme.{0}} {n : ℕ} (W : X.Opens) (δ : Fld X) (dd : Fin n → Fld X), IsField W δ → (∀ a, IsField ⊤ (dd a)) →
    (∀ V V' : X.Opens, IsAffineOpen V → IsAffineOpen V' → V ≤ W → V' ≤ V →
      ∃! c : Fin n → Γ(X, V'), ∀ f : Γ(X, V), rsT (δ V f) V' = ∑ a, c a * rsT (dd a V f) V') →
    ∃ c : Fin n → Γ(X, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  intro X n W δ dd hδ hdd H
  let J : Type := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  choose c hc using fun j : J => (H j.1 j.1 j.2.1 j.2.1 j.2.2 le_rfl).exists
  have hl : ∀ (l : J) (O : X.Opens) (h : l.1 ≤ O), O ≤ W → ∀ f : Γ(X, O),
      rsT (δ O f) l.1 = ∑ a, c l a * rsT (dd a O f) l.1 := by
    intro l O h hO f
    have e1 := hδ.2.2 O l.1 h hO f
    have e2 := hc l (resG X h f)
    simp only [GlobalTheory.KS.rsT_self] at e2
    rw [GlobalTheory.KS.rsT_of_le h, ← e1, e2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hdd a).2.2 O l.1 h le_top f, GlobalTheory.KS.rsT_of_le h]
  have sub : ∀ j l : J, l.1 ≤ j.1 → ∀ a, rsT (c j a) l.1 = c l a := by
    intro j l h a
    refine congrFun ((H j.1 l.1 j.2.1 l.2.1 j.2.2 h).unique (y₁ := fun a => rsT (c j a) l.1) (y₂ := c l) ?_ ?_) a
    · intro f
      have := hc j f
      simp only [GlobalTheory.KS.rsT_self] at this
      rw [this, GlobalTheory.KS.rsT_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [GlobalTheory.KS.rsT_mul]
    · exact hl l j.1 h j.2.2
  have glue : ∀ a, ∃ s : Γ(X, W), ∀ j : J, rsT s j.1 = c j a := fun a => by
    refine GlobalTheory.KS.exists_rsT_eq (fun j : J => j.1) (fun j => j.2.2) (affine_cover W) (fun j => c j a)
      fun j k => ?_
    refine GlobalTheory.KS.eq_of_rsT_eq (fun l : {V : X.Opens // IsAffineOpen V ∧ V ≤ j.1 ⊓ k.1} => l.1)
      (fun l => l.2.2) (affine_cover _) _ _ fun l => ?_
    have hj : l.1 ≤ j.1 := l.2.2.trans inf_le_left
    have hk : l.1 ≤ k.1 := l.2.2.trans inf_le_right
    rw [GlobalTheory.KS.rsT_rsT inf_le_left l.2.2, GlobalTheory.KS.rsT_rsT inf_le_right l.2.2,
      sub j ⟨l.1, l.2.1, hj.trans j.2.2⟩ hj, sub k ⟨l.1, l.2.1, hk.trans k.2.2⟩ hk]
  choose s hs using glue
  refine ⟨s, fun O hO f => ?_⟩
  refine GlobalTheory.KS.eq_of_rsT_eq (fun l : {V : X.Opens // IsAffineOpen V ∧ V ≤ O} => l.1) (fun l => l.2.2)
    (affine_cover O) _ _ fun l => ?_
  rw [hl ⟨l.1, l.2.1, l.2.2.trans hO⟩ O l.2.2 hO f, GlobalTheory.KS.rsT_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_rsT hO l.2.2, hs a ⟨l.1, l.2.1, l.2.2.trans hO⟩]

end GlobalTheory.VertCoeffGlue
end
end
