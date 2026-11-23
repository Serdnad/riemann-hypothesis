module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2853
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

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
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

section T
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem trF_term (e : ℕ) (α : Q.X) (t : Fin 4 → Q.P.L.ι) (J : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι) (y : Y.H.left) :
    trF (fun _ : Fin 1 => Y.q.left) (fun _ => (e : ℤ)) (𝟙 _) y (fun _ => J Y.q.left) (fun _ => t 0) =
      trF (Q.famφB α) (DegPre.famε e) Y.q.left y (fun j => J (Y.q.left ≫ Q.famφB α j)) t *
        trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε (𝟙 _) y
          (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => t (![1, 2, 0, 3] k)) := by
  let G : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι → (Y.H.left.presheaf.stalk y)ˣ := fun ψ i =>
    gm ψ y (Q.P.L.U (J ψ) ⊓ Q.P.L.U i) (Q.P.L.g (J ψ) i)
  have e1 : trF (Q.famφB α) (DegPre.famε e) Y.q.left y (fun j => J (Y.q.left ≫ Q.famφB α j)) t =
      ∏ k, G (Y.q.left ≫ Q.famφB α k) (t k) ^ DegPre.famε e k := rfl
  have e2 : trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε (𝟙 _) y
      (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => t (![1, 2, 0, 3] k)) =
      ∏ k, G (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k)) (t (![1, 2, 0, 3] k)) ^ DegPre.gtε k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.id_comp, gtφT_eq]
  have e3 : trF (fun _ : Fin 1 => Y.q.left) (fun _ => (e : ℤ)) (𝟙 _) y (fun _ => J Y.q.left) (fun _ => t 0) =
      G Y.q.left (t 0) ^ (e : ℤ) := by
    rw [trF, Fin.prod_univ_one, Category.id_comp]
  have f0 : Q.famφB α 0 = 𝟙 _ := rfl
  rw [e1, e2, e3]
  simp only [Fin.prod_univ_four, DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, f0, Category.comp_id]
  rw [zpow_sub_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv, zpow_one, zpow_neg]
  abel

theorem term_germ {e : ℕ} {α : Q.X} {σ : Q.SecB e α} {τ : SecM Y.q.left Q.P.L e} (hτ : IsTerm Y e α σ τ)
    (t : Fin 4 → Q.P.L.ι) (y : Y.H.left) (h₁ : Y.q.left y ∈ LB.wchart Q.P.L (Q.famφB α) t) (h₂ : y ∈ xU Y α t) :
    gs (𝟙 _) y _ (τ.f fun _ => t 0) = gs Y.q.left y _ (σ.f t) * gs (𝟙 _) y _ (xc Y α t).val := by
  have hL : Q.P.L.IsLB := Q.P.isLB
  choose J hJ using fun χ : Y.H.left ⟶ Q.P.A.left => exists_chart hL (χ y)
  have hJ' : Good Q.P.L y J := hJ
  have e₀ := hτ Y.H (𝟙 _) y J hJ'
  have f0 : Q.famφB α 0 = 𝟙 _ := rfl
  have h₀ : y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) fun _ => t 0 := Set.mem_iInter.2 fun _ => by
    have := Set.mem_iInter.1 h₁ 0
    rw [f0] at this
    exact this
  rw [sval_of τ _ y J (fun _ => J Y.q.left) (fun _ => by simp),
    sval_of σ _ y J (fun j => J (Y.q.left ≫ Q.famφB α j)) (fun _ => by simp),
    val_of _ _ y J (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => by rw [Category.id_comp, gtφT_eq])] at e₀
  simp only [Over.id_left, Over.comp_left, Category.id_comp] at e₀
  have m₁ : (𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) fun _ => J Y.q.left :=
    Set.mem_iInter.2 fun _ => hJ _
  have m₂ : Y.q.left y ∈ LB.wchart Q.P.L (Q.famφB α) fun j => J (Y.q.left ≫ Q.famφB α j) :=
    Set.mem_iInter.2 fun j => hJ _
  have m₃ : (𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y ∈ LB.wchart Q.P.L (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α)
      fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k)) :=
    Set.mem_iInter.2 fun k => by
      show y ∈ (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) ⁻¹ᵁ _
      rw [gtφT_eq]; exact hJ _
  rw [sec_trans τ _ y m₁ h₀, sec_trans σ Y.q.left y m₂ h₁, gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) (𝟙 _) y m₃ h₂,
    Units.val_mul] at e₀
  rw [gs_unit (𝟙 _) y _ h₂]
  rw [trF_term Y e α t J y, Units.val_mul] at e₀
  exact ((Units.isUnit _).mul (Units.isUnit _)).mul_left_cancel (e₀.trans (mul_mul_mul_comm _ _ _ _))
end T

section T2
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem term_germ_at {e : ℕ} {α : Q.X} {σ : Q.SecB e α} {τ : SecM Y.q.left Q.P.L e} (hτ : IsTerm Y e α σ τ)
    (t : Fin 4 → Q.P.L.ι) {Z : Scheme.{0}} (r : Z ⟶ Y.H.left) (z : Z)
    (h₁ : Y.q.left (r z) ∈ LB.wchart Q.P.L (Q.famφB α) t) (h₂ : r z ∈ xU Y α t) :
    gs r z _ (τ.f fun _ => t 0) = gs (r ≫ Y.q.left) z _ (σ.f t) * gs r z _ (xc Y α t).val := by
  have h₀ : r z ∈ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (e : ℤ)).U fun _ => t 0 :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h₁ 0
  have h₁' : Y.q.left (r z) ∈ (LB.LinComb Q.P.L (Q.famφB α) (DegPre.famε e)).U t := h₁
  have e₁ : gs Y.q.left (r z) _ (σ.f t) = gs (𝟙 _) (r z) (Y.q.left ⁻¹ᵁ _) ((Y.q.left.app _).hom (σ.f t)) := by
    rw [gs_pull (𝟙 _) Y.q.left (r z) _ h₁', Category.id_comp]
  rw [gs_stalkMap r z _ h₀, term_germ Y hτ t (r z) h₁ h₂, map_mul, ← gs_stalkMap r z _ h₂, e₁,
    ← gs_stalkMap r z _ h₁', gs_pull r Y.q.left z _ h₁']
end T2

theorem heat_term_fibre : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ (α : Q.X) (c : K), CoordEq Y h ν m₀ V pb α c → ∀ (σ σ' : Q.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ U : A₀.left.Opens, U ≤ m₀ ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j)) → (∀ j, U ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) U = 2 * (e : Γ(A₀.left, U)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) U + pbT m₀ (σ.f (fun j => h.j (i j))) U * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, U)) * pbT (T j) (pb (i j)) U + constFn A₀.hom U c)) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hK hD α c hC σ σ' hA i T hT₁ hT₂ U hU hUT
  obtain ⟨τ, τ', hτ, hτ', hAc⟩ := hA
  refine ext_lift Y m₀ fun Z a b w z hz => ?_
  have hV : ∀ i, V i ≤ Q.P.L.U (h.j i) := hK.2.2.1
  have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => hUT j hz
  have ha := hF.mem_chart hD hV hT₁ w hi
  have T0 : T 0 = 𝟙 _ := hF.T_zero (hT₁ 0) (hT₂ 0)
  have wz : Y.q.left (a z) = m₀ (b z) := by
    have := congrArg (fun f => f z) w
    simpa using this
  set W := (LB.LinComb Q.P.L (Q.famφB α) (DegPre.famε e)).U fun j => h.j (i j) with hWdef
  have hU' : U ≤ m₀ ⁻¹ᵁ W := hU
  have hbW : m₀ (b z) ∈ W := hU hz
  have hqa : Y.q.left (a z) ∈ W := wz ▸ hbW
  have hb0 : (b ≫ m₀) z ∈ V (i 0) := by simpa [T0] using hi 0

  have P : ∀ j, gs b z U (pbT (T j) (pb (i j)) U) = gs (b ≫ T j) z _ (pb (i j)) := fun j =>
    gs_pbT b (T j) z (hUT j) hz _
  have Ed : gs b z U (rsT (ed W (σ.f fun j => h.j (i j))) U) = gs b z (m₀ ⁻¹ᵁ W) (ed W (σ.f fun j => h.j (i j))) :=
    gs_rsT b z hU' hz _
  have Sb : ∀ s : Q.SecB e α, gs b z U (pbT m₀ (s.f fun j => h.j (i j)) U) = gs (a ≫ Y.q.left) z W (s.f fun j => h.j (i j)) :=
    fun s => by rw [gs_pbT b m₀ z hU' hz, w]
  have Cc : gs b z U (constFn A₀.hom U c) = cst (b ≫ A₀.hom) z c := gs_constFn _ _ _ _ hz _

  have hΘ : ∀ a' b', gsH a z (h.W (i 0)) ha.1 (constFn Y.H.hom (h.W (i 0)) (h.Θ a' b')) = 0 := fun a' b' => by
    rw [← gs_eq_gsH, hF.gs_const w z (h.W (i 0)) ha.1, hF.symb, cst_eq_cstH, map_zero]
  have hop := congrArg (gsH a z (h.W (i 0)) ha.1) (hAc (i 0))
  rw [map_op h ν e hF.inv (i 0) (h.W (i 0)) le_rfl _ hΘ] at hop
  simp only [← gs_eq_gsH] at hop
  have hWc : h.W (i 0) ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (e : ℤ)).U fun _ => h.j (i 0) :=
    fun y hy => Set.mem_iInter.2 fun _ => h.le (i 0) hy
  rw [gs_rsT a z hWc ha.1, gs_rsT a z le_rfl ha.1,
    term_germ_at Y hτ' (fun j => h.j (i j)) a z hqa ha.2, ← hD.2.2 Z a b w z (i 0) hb0] at hop

  obtain ⟨δ, -, hδm, hδv⟩ := exists_stalkDer_field (isField_dE h ν hF.field (i 0)) a z ha.1
  set U' : Q.P.A.left.Opens := V (i 0) ⊓ W with hU'def
  have hqU : Y.q.left ⁻¹ᵁ U' ≤ h.W (i 0) := by
    rw [hD.1 (i 0)]; exact fun y (hy : Y.q.left y ∈ U') => hy.1
  have haV : Y.q.left (a z) ∈ V (i 0) := by
    have := ha.1; rw [hD.1 (i 0)] at this; exact this
  have haU : a z ∈ Y.q.left ⁻¹ᵁ U' := ⟨haV, hqa⟩
  have hbU : (b ≫ m₀) z ∈ U' := ⟨hb0, by simpa using hbW⟩
  have haU' : (a ≫ Y.q.left) z ∈ U' := by simpa using haU
  set f' : Γ(Q.P.A.left, U') := resG Q.P.A.left (inf_le_right : U' ≤ W) (σ.f fun j => h.j (i j)) with hf'
  have hAB : gs (𝟙 _) (a z) (h.W (i 0)) (rsT (τ.f fun _ => h.j (i 0)) (h.W (i 0))) =
      gs (𝟙 _) (a z) (Y.q.left ⁻¹ᵁ U') ((Y.q.left.app U').hom f') *
        gs (𝟙 _) (a z) (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))
          (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))) := by
    rw [gs_rsT (𝟙 _) (a z) hWc ha.1, term_germ Y hτ (fun j => h.j (i j)) (a z) hqa ha.2,
      gs_rsT (𝟙 _) (a z) inf_le_right ha, gs_pull (𝟙 _) Y.q.left (a z) U' haU, Category.id_comp, hf',
      gs_res Y.q.left (a z) inf_le_right haU]
  have hδ := hδv (h.W (i 0)) le_rfl ha.1 (rsT (τ.f fun _ => h.j (i 0)) (h.W (i 0)))
  rw [hAB, hδm, hδv _ hqU haU, hδv _ inf_le_left ha, ← hD.2.1 Z a b w z (i 0) U' inf_le_left hbU,
    hf', hK.1.res W U' inf_le_right le_top, gs_rsT b z (fun y (hy : m₀ y ∈ U') => hy.2) hbU,
    hC T hT₁ hT₂ Z a b w z i hi, ← gs_stalkMap a z _ haU, ← gs_stalkMap a z _ ha, gs_pull a Y.q.left z U' haU,
    gs_res _ z inf_le_right haU', gs_rsT a z inf_le_right ha] at hδ
  rw [gs_rsT a z hWc ha.1 (τ.f fun _ => h.j (i 0)), term_germ_at Y hτ (fun j => h.j (i j)) a z hqa ha.2, ← hδ] at hop
  have hX : IsUnit (gs a z (xU Y α fun j => h.j (i j)) (xc Y α fun j => h.j (i j)).val) := by
    rw [gs_unit a z _ ha.2]; exact Units.isUnit _
  rw [Sb σ', gs_eq_gsH b z U hz]

  simp only [map_mul, map_add (f := _), map_sum, map_natCast, map_ofNat, map_intCast]
  simp only [← gs_eq_gsH b z U hz]
  rw [Ed, Sb σ, Cc, Fin.sum_univ_four, P 0, P 1, P 2, P 3]
  rw [T0, Category.comp_id] at hop ⊢
  simp only [W] at hop ⊢
  have f0 : DegPre.famε e 0 = (e : ℤ) - 1 := rfl
  have f1 : DegPre.famε e 1 = 1 := rfl
  have f2 : DegPre.famε e 2 = -1 := rfl
  have f3 : DegPre.famε e 3 = 1 := rfl
  rw [f0, f1, f2, f3]
  push_cast
  apply hX.mul_left_cancel
  linear_combination hop
end GlobalTheory.HeatConn
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat.UnifLat

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_tau {o B X : Type} [CommRing o] [CommRing B] [AddCommGroup X] (b : o →+* B) (ζ : oˣ) {L : ℕ}
    (hL : 0 < L) (hζ : ζ ^ L = 1) (c : X →+ ZMod L) :
    ∃ τ : Multiplicative X →* Bˣ,
      (∀ χ, τ χ = Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ∧ τ ^ L = 1 := by
  haveI : NeZero L := ⟨hL.ne'⟩
  have hu : Units.map b.toMonoidHom ζ ^ L = 1 := by rw [← map_pow, hζ, map_one]
  refine ⟨{ toFun := fun χ => Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val
            map_one' := by simp
            map_mul' := fun χ χ' => by
              simp only [toAdd_mul, map_add (f := _), ZMod.val_add]
              rw [← pow_add, ← pow_eq_pow_mod _ hu] }, fun χ => rfl, ?_⟩
  refine MonoidHom.ext fun χ => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  show (Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ^ L = 1
  rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]

end GlobalTheory.Poinc.FibLat.UnifLat


open GlobalTheory.Poinc.FibLat.UnifLat in
theorem GlobalTheory.Poinc.FibLat.latAt_of_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (Gu : Over (Sp V)) [GrpObj Gu] [IsCommMonObj Gu], IsSemiAbelian Gu → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A Gu) (F : I → (Gu ⟶ Gu)) (m : I → D.toPre.X →+ D.toPre.X), (∀ e, EndChar U (F e) (m e)) → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (fV : V →+* V'), IsLocalHom fV → ∀ (ξ : Sp V' ⟶ M.Z) (a : o →+* V'), ξ ≫ M.s = spMap a → ∀ (G' : Over (Sp V')) [GrpObj G'] (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left), IsGrpPullback G' Gu (spMap fV) β → IsGrpPullback G' G ξ β' → (∀ e, ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ (F e).left ∧ F'.left ≫ β' = β' ≫ (f e).left) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (iK : V' →+* K), Function.Injective iK → iK.comp fV = (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V)) → ∀ c : T → D.toPre.X →+ ZMod L, (∀ t, ExtNear (gγ t) (ξ (closedPoint V')) ∧ ∃ (q : QkPt D.toPre K L) (τ : Multiplicative D.toPre.X →* Kˣ) (x : TFK (R := V) K ⟶ A.A) (x' : Sp K ⟶ G'.left), q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkToAkU U.toUnifPre K L q x ∧ (∀ χ, (τ (Multiplicative.ofAdd χ) : K) = iK (a ((ζ : o) ^ (c t χ).val))) ∧ x' ≫ G'.hom = spMap iK ∧ x' ≫ β = x.left ≫ genMap U ∧ ValAt (gγ t) (spMap iK ≫ ξ) (x' ≫ β')) → LatAt f gγ ζ L m c (ξ (closedPoint V')) := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ V _ _ _ hV Gu _ _ hGu D A U F m hF V' _ _ _ fV hfV ξ a hξ G' _ β β'
    hβ hβ' hF' K _ _ _ iK hiK hKf c hc
  haveI : IsSeparated G.hom := hG.separated
  haveI : IsSeparated Gu.hom := hGu.separated
  haveI : IsSeparated G'.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hβ.1 inferInstance
  obtain ⟨r, hrl, hr⟩ : ∃ r : V' →+* ResidueField V', IsLocalHom r ∧ ∀ x, r x = 0 ↔ x ∈ maximalIdeal V' :=
    ⟨residue V', inferInstance, fun x => residue_eq_zero_iff x⟩
  have hρ : ∀ x ∈ maximalIdeal V ^ (0 + 1), (r.comp fV) x = 0 := fun x hx => by
    rw [zero_add, pow_one] at hx
    exact (hr _).2 (map_nonunit fV x hx)
  obtain ⟨G₀, _, ψ, hψ⟩ : ∃ (G₀ : Over (Sp (ResidueField V'))) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G'.left),
      IsGrpPullback G₀ G' (spMap r) ψ := ⟨_, inferInstance, _, isGrpPullback_pullback G' (spMap r)⟩
  have h₀ : IsGrpPullback G₀ Gu (spMap (r.comp fV)) (ψ ≫ β) := (hψ.comp hβ).congr (spMap_comp_eq fV r).symm rfl
  have hφ : IsGrpPullback G₀ G (spMap r ≫ ξ) (ψ ≫ β') := hψ.comp hβ'
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := GlobalTheory.ToricTorsionUnif.main V hV Gu hGu D A U L hL
  refine ⟨ResidueField V', inferInstance, spMap r ≫ ξ, r.comp a, G₀, inferInstance, ψ ≫ β',
    GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀, ?_, ?_, hφ, isTorPart_gtTorus _ hρ h₀, ?_⟩
  · show ξ ((spMap r) (closedPoint (ResidueField V'))) = _
    rw [spMap, Spec_closedPoint]
  · rw [Category.assoc, hξ, spMap_comp_eq a r]
  refine ⟨fun e => ?_, fun t => ?_⟩
  · obtain ⟨F', hF1, hF2⟩ := hF' e
    have w : (ψ ≫ F'.left) ≫ G'.hom = G₀.hom ≫ spMap r := by
      rw [Category.assoc, Over.w F', hψ.1.w]
    obtain ⟨F₀, hF₀⟩ : ∃ F₀ : G₀ ⟶ G₀, F₀.left ≫ ψ = ψ ≫ F'.left :=
      ⟨Over.homMk (hψ.1.lift (ψ ≫ F'.left) G₀.hom w) (hψ.1.lift_snd _ _ _), hψ.1.lift_fst _ _ _⟩
    have hE := hF e (ResidueField V') (r.comp fV) hρ G₀ (ψ ≫ β) h₀ F₀
      (by rw [← Category.assoc, hF₀, Category.assoc, hF1, Category.assoc])
    have k : (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left =
        (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V')) (m e) ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left := by
      rw [← Over.comp_left, hE]
    calc (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ (ψ ≫ β') ≫ (f e).left
        = (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ ≫ F'.left ≫ β' := by rw [hF2]; simp only [Category.assoc]
      _ = ((GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left) ≫ ψ ≫ β' := by
          rw [Category.assoc, reassoc_of% hF₀]
      _ = _ := by rw [k]
  · obtain ⟨hext, q, τ, x, x', hq, hτq, hqx, hτ, hx'1, hx'2, hx'3⟩ := hc t
    obtain ⟨τV, hτVv, hτV⟩ := exists_tau a ζ hL hζ (c t)
    obtain ⟨τκ, hτκv, hτκ⟩ := exists_tau (r.comp a) ζ hL hζ (c t)
    have hchar : ∀ χ, (τ χ : K) = iK (τV χ : V') := fun χ => by
      rw [hτVv]
      refine (hτ (Multiplicative.toAdd χ)).trans ?_
      simp
    have hcharκ : ∀ χ, (τκ χ : ResidueField V') = r (τV χ : V') := fun χ => by
      rw [hτVv, hτκv]
      simp
    have hτL : τ ^ L = 1 := MonoidHom.ext fun χ => Units.ext (by
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hchar, ← map_pow, ← Units.val_pow_eq_pow_val,
        ← MonoidHom.pow_apply, hτV]
      simp)
    have hσ₀ : (s V' fV τV hτV).left ≫ Gu.hom = 𝟙 (Sp V') ≫ spMap fV :=
      (Over.w (s V' fV τV hτV)).trans (Category.id_comp _).symm
    obtain ⟨σ, hσβ, hσG⟩ : ∃ σ : Sp V' ⟶ G'.left, σ ≫ β = (s V' fV τV hτV).left ∧ σ ≫ G'.hom = 𝟙 _ :=
      ⟨hβ.1.lift _ _ hσ₀, hβ.1.lift_fst _ _ _, hβ.1.lift_snd _ _ _⟩
    obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ hext
    obtain ⟨σ', hσ'β, hσ'G⟩ : ∃ σ' : Sp V' ⟶ G'.left, σ' ≫ β' = v ∧ σ' ≫ G'.hom = 𝟙 _ :=
      ⟨hβ'.1.lift v (𝟙 _) (by rw [hv.over, Category.id_comp]), hβ'.1.lift_fst _ _ _, hβ'.1.lift_snd _ _ _⟩
    have eσK : spMap iK ≫ σ = x' := hβ.1.hom_ext (by
        rw [Category.assoc, hσβ, hx'2, hs4 K (iK.comp fV) τ hτL q x hKf hq hτq hqx,
          hs2 V' K fV (iK.comp fV) iK τV hτV τ hτL rfl hchar])
      (by rw [Category.assoc, hσG, hx'1, Category.comp_id])
    have eσ'K : spMap iK ≫ σ' = x' := hβ'.1.hom_ext (by
        rw [Category.assoc, hσ'β]; exact ValAt.unique (hv.comp (spMap iK)) hx'3)
      (by rw [Category.assoc, hσ'G, hx'1, Category.comp_id])
    haveI : IsDominant (spMap iK) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical iK).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hiK]; exact bot_le)⟩
    have eσ : σ = σ' := ext_of_isDominant_of_isSeparated G'.hom (by rw [hσG, hσ'G]) (spMap iK)
      (eσK.trans eσ'K.symm)
    let φκ : Multiplicative D.toPre.X →* Γ((Over.mk (𝟙 (Sp (ResidueField V')))).left, ⊤)ˣ :=
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField V'))).inv.hom.toMonoidHom).comp τκ
    obtain ⟨z, hz⟩ : ∃ z : Over.mk (𝟙 (Sp (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X,
        ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τκ (Multiplicative.ofAdd χ)) :=
      ⟨(GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ, fun χ => by
        show GlobalTheory.splitTorusPointsEquiv _ _ _ ((GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ) _ = _
        rw [MulEquiv.apply_symm_apply]; rfl⟩
    have hz1w : z.left ≫ (splitTorus (Sp (ResidueField V')) D.toPre.X).hom =
        (Over.mk (spMap (RingHom.id (ResidueField V')))).hom := by
      rw [Over.w z]
      show 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id (ResidueField V')))
      rw [CommRingCat.ofHom_id, Spec.map_id]
    let z₁ : Over.mk (spMap (RingHom.id (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X :=
      Over.homMk z.left hz1w
    have hz₁ : ∀ χ, GlobalTheory.UU.chV z₁ χ = unitOn (τκ (Multiplicative.ofAdd χ)) := fun χ =>
      (Units.ext (by rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val]; rfl)).trans (hz χ)
    have e3 := hs3 (ResidueField V') (ResidueField V') (r.comp fV) hρ (r.comp fV) (RingHom.id _) G₀ (ψ ≫ β) h₀ τκ hτκ
      z₁ (RingHom.id_comp _).symm hz₁
    have e2 := hs2 V' (ResidueField V') fV (r.comp fV) r τV hτV τκ hτκ rfl hcharκ
    have ez : (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ = spMap r ≫ σ := hβ.1.hom_ext
      (by
        rw [Category.assoc, Category.assoc, hσβ, ← e2, e3]
        rfl)
      (by
        rw [Category.assoc, Category.assoc, hσG, Category.comp_id, hψ.1.w, ← Category.assoc,
          Over.w (z ≫ _)]
        exact Category.id_comp _)
    refine ⟨z, fun χ => (hz χ).trans (by rw [hτκv]; rfl), ?_⟩
    rw [← Category.assoc, ez, eσ, Category.assoc, hσ'β]
    exact hv.comp (spMap r)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix


theorem _root_.GlobalTheory.T.isExponentialOfSemiAbelianFibre_linearChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (M : Matrix (Fin g) (Fin g) ℂ), IsUnit M.det → IsHolTo Set.univ (fun z => (e z).left) → GlobalTheory.ShFam.Hor.LogCh.IsExpAt t y e → GlobalTheory.ShFam.Hor.LogCh.IsExpAt t y (fun w => e (M *ᵥ w)) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.isExpAt_mulVec | exact GlobalTheory.ShFam.Hor.LogCh.isExpAt_mulVec | (intros; apply GlobalTheory.ShFam.Hor.LogCh.isExpAt_mulVec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HalfPt

theorem exists_spec_of_finite_surjective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (f : X ⟶ Sp R)
    [IsFinite f] [Surjective f] :
    ∃ (C : Type) (_ : CommRing C) (φ : R →+* C) (g : Sp C ⟶ X),
      Function.Injective φ ∧ φ.Finite ∧ g ≫ f = spMap φ := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of R ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f)
  have hψ : Spec.map ψ = X.isoSpec.inv ≫ f := Spec.map_preimage _
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, X.isoSpec.inv, ?_, ?_, ?_⟩
  · have hs : Surjective (Spec.map ψ) := by rw [hψ]; infer_instance
    have hd : DenseRange (PrimeSpectrum.comap ψ.hom) := hs.1.denseRange
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, nilradical_eq_zero] at hd
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    simpa using hd hx
  · have hf : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
    exact (IsFinite.SpecMap_iff ψ).1 hf
  · exact hψ.symm

end GlobalTheory.HalfPt

namespace GlobalTheory.HalfPt

theorem exists_half_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (a : 𝟙_ (Over (Sp R)) ⟶ B), IsCN R → IsAbelianScheme B → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (b : Over.mk (spMap ρ) ⟶ B), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ b ^ 2 = toUnit _ ≫ a := by
  intro R _ _ _ B _ _ a hCN hAb
  haveI : IsNoetherianRing R := hCN.1
  obtain ⟨hfin, -⟩ := GlobalTheory.T.isFinite_and_flat_mul_abelianScheme (Sp R) B hAb 2 (by norm_num)
  have hsurj := GlobalTheory.T.semiAbelian_mul_nat_surjective (Sp R) B (GlobalTheory.isSemiAbelian_of_isAbelianScheme B hAb) 2 two_ne_zero
  let m : B.left ⟶ B.left := ((𝟙 B) ^ 2 : B ⟶ B).left
  let s : Sp R ⟶ B.left := a.left
  haveI : IsFinite m := hfin
  haveI : Surjective m := hsurj
  haveI : IsFinite (pullback.snd m s) := inferInstance
  haveI : Surjective (pullback.snd m s) := inferInstance
  obtain ⟨C, _, φ, g, hinj, hφf, hg⟩ := exists_spec_of_finite_surjective (pullback.snd m s)
  obtain ⟨R', _, _, _, ρ, σ, hCN', hρi, hρf, hρl, hσ⟩ := GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom R C φ hCN hinj hφf
  have hsB : s ≫ B.hom = 𝟙 (Sp R) := Over.w a
  have hmB : m ≫ B.hom = B.hom := Over.w ((𝟙 B) ^ 2 : B ⟶ B)
  have hfst : pullback.fst m s ≫ B.hom = pullback.snd m s := by
    rw [← hmB, ← Category.assoc, pullback.condition, Category.assoc, hsB, Category.comp_id]
  have hρ : spMap σ ≫ spMap φ = spMap ρ := by
    rw [← hσ, spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let c : Over.mk (spMap ρ) ⟶ B :=
    Over.homMk (spMap σ ≫ g ≫ pullback.fst m s) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [hfst, hg, hρ])
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, c, hCN', hρi, hρf, hρl, ?_⟩
  have hc : c ^ 2 = c ≫ (𝟙 B) ^ 2 := by rw [comp_pow, Category.comp_id]
  rw [hc]
  ext
  simp only [c, Over.comp_left, Over.homMk_left, Category.assoc]
  show spMap σ ≫ g ≫ pullback.fst m s ≫ m = _
  rw [pullback.condition, ← Category.assoc g, hg, ← Category.assoc, hρ]
  rfl

end GlobalTheory.HalfPt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_completeDVR_local_embedding_normal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j := by
  first | exact @GlobalTheory.CompleteNormalDvr.exists_dvr_isCN | exact GlobalTheory.CompleteNormalDvr.exists_dvr_isCN | (intros; apply GlobalTheory.CompleteNormalDvr.exists_dvr_isCN <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_finite_local_extension_with_embedded_field_extension : ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀], IsCN V₀ → ∀ (L : Type) [Field L] [Algebra (FractionRing V₀) L] [FiniteDimensional (FractionRing V₀) L], ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V₀ →+* V₁) (σ : L →+* FractionRing V₁), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ x : V₀, σ (algebraMap (FractionRing V₀) L (algebraMap V₀ (FractionRing V₀) x)) = algebraMap V₁ (FractionRing V₁) (ρ x) := by
  first | exact @GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local | exact GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local | (intros; apply GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local <;> assumption)
end
