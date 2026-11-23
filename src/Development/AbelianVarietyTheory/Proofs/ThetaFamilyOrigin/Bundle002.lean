module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjMul
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.CrdDown

theorem val_of_rel {K : Type} [CommRing K] {X Y : Scheme.{0}} (x : Sp K ⟶ X) (ρ : X ⟶ Y) (p : Sp K ⟶ Y)
    (hp : x ≫ ρ = p) (U : X.Opens) (V : Y.Opens) (W : (Sp K).Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : U ≤ ρ ⁻¹ᵁ V)
    (hW : ⊤ ≤ W) (hWV : W ≤ p ⁻¹ᵁ V) (u : Γ(Sp K, W)ˣ) :
    ∃ c : Kˣ, ∀ (f : Γ(Y, V)) (w : Γ(Sp K, ⊤)),
      ((Sp K).presheaf.map (homOfLE hWV).op).hom ((p.app V).hom f) =
        ((Sp K).presheaf.map (homOfLE le_top).op).hom w * u.val →
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom w = (c : K) * valR x U ((ρ.appLE V U hV).hom f) := by
  subst hp
  obtain rfl : W = ⊤ := top_le_iff.1 hW
  let φ := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  refine ⟨(Units.map φ.toMonoidHom u)⁻¹, fun f w h => ?_⟩
  have e : ((Sp K).presheaf.map (homOfLE (le_top : (⊤ : (Sp K).Opens) ≤ ⊤)).op).hom w = w :=
    congrArg (fun φ => CommRingCat.Hom.hom φ w) ((Sp K).presheaf.map_id _)
  rw [e] at h
  have h1 : (x.appLE U ⊤ hU).hom ((ρ.appLE V U hV).hom f) = w * u.val :=
    (congrArg (fun φ => CommRingCat.Hom.hom φ f) (Scheme.Hom.appLE_comp_appLE x ρ V U ⊤ hV hU)).trans h
  rw [CrdCalc.valR_eq x U hU, Units.eq_inv_mul_iff_mul_eq]
  refine Eq.trans ?_ (congrArg φ h1).symm
  rw [map_mul, _root_.mul_comm]
  rfl

theorem crd_down_of_isValueAt : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (x : (Out.baseOver (Sp K)) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (Out.baseOver (Sp K)).left) (K := Fin 1) (fun _ => x.left) (fun _ => (N : ℤ)))) (w : J → Γ((Out.baseOver (Sp K)).left, ⊤)), (∀ a, Out.IsValueAt P.A P.L N (t a) x τ (w a)) → Crd (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) (x.left : Sp K ⟶ P.A.left) (fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w a)) := by
  intro K _ _ P N J t ρ e x τ w h
  have hx : (x.left : Sp K ⟶ P.A.left) (IsLocalRing.closedPoint K) ∈ ⨆ i, P.L.U i := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hi' := (CrdCalc.top_le_iff (x.left : Sp K ⟶ P.A.left) _).2 hi
  haveI : IsIso (snd (Out.baseOver (Sp K)) P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) P.A.hom))
  have hp : (x.left : Sp K ⟶ P.A.left) ≫ ρ = (Out.ptSecT P.A x).left := by
    rw [← cancel_mono (snd (Out.baseOver (Sp K)) P.A).left]
    refine (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) e).trans ((Category.comp_id _).trans ?_))
    exact (congrArg (fun q => q.left) (lift_snd (𝟙 (Out.baseOver (Sp K))) x)).symm
  have hU : ⊤ ≤ (x.left : Sp K ⟶ P.A.left) ⁻¹ᵁ LB.wchart P.L (fun _ : PUnit => 𝟙 P.A.left) (fun _ => i) :=
    fun y hy => Set.mem_iInter.2 fun _ => hi' hy
  have hW : ⊤ ≤ LB.wchart P.L (fun _ : Fin 1 => x.left) (fun _ => i) :=
    fun y hy => Set.mem_iInter.2 fun _ => hi' hy
  obtain ⟨c, hc⟩ := val_of_rel (x.left : Sp K ⟶ P.A.left) ρ _ hp _ _ _ hU
    (PowSec.chart_eq P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e (fun _ => i)).le hW
    (Out.val_le P.A P.L x (fun _ => i)) (τ.s (fun _ => i))
  exact ⟨fun _ => i, c, hU, fun a => hc _ _ (h a (fun _ => i))⟩

end GlobalTheory.ZH.CrdDown
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace IntAct

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem rosatiAdj_of_points (hL : L.IsLB) (f g : A ⟶ A)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∀ (T : Over S) (x y : T ⟶ A), (∀ p, T.hom p ∈ U) →
      ∃ (K : Type) (_ : Fintype K) (φ : K → (T.left ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
        t.IsGen ∧ ∀ (V : Type) [CommGroup V] (k : (T.left ⟶ A.left) → V), ∏ i, k (φ i) ^ ε i =
          k ((x ≫ f) * y).left * (k (x ≫ f).left)⁻¹ * (k y.left)⁻¹ * (k (x * (y ≫ g)).left)⁻¹ * k x.left *
            k (y ≫ g).left) : RosatiAdj A L f g := by
  intro s
  obtain ⟨U, hs, hU⟩ := h s
  refine ⟨U, hs, ?_⟩
  let W : (A ⊗ A).left.Opens := (A ⊗ A).hom ⁻¹ᵁ U
  let T : Over S := Over.mk (W.ι ≫ (A ⊗ A).hom)
  let ρ : T ⟶ A ⊗ A := Over.homMk W.ι rfl
  obtain ⟨x, y, hxy⟩ : ∃ x y : T ⟶ A, (lift x y).left = W.ι :=
    ⟨ρ ≫ fst A A, ρ ≫ snd A A, congrArg (fun q => q.left) (lift_comp_fst_snd ρ)⟩
  obtain ⟨K, _, φ, ε, t, ht, hf⟩ := hU T x y (fun p => p.2)
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := fun i => W.ι ≫ rosatiφ A f g i) (ε' := rosatiε)
    (fun V _ k => (hf V k).trans ((prod_ros f g x y k).symm.trans
      (Finset.prod_congr rfl fun i _ => by rw [hxy]))) t ht
  exact ⟨u, hu⟩

theorem isGen_oneGen {X Y : Scheme.{0}} (M : LB X) : (LB.oneGen M (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem rosatiAdj_one (hL : L.IsLB) : RosatiAdj A L 1 1 :=
  rosatiAdj_of_points hL _ _ fun _ => ⟨⊤, trivial, fun T x y _ =>
    ⟨PEmpty, inferInstance, _, _, LB.oneGen L, isGen_oneGen L, fun V _ k => by
      rw [MonObj.comp_one, MonObj.comp_one, _root_.one_mul, _root_.mul_one, Fintype.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel⟩⟩

theorem rosatiAdj_id (hL : L.IsLB) : RosatiAdj A L (𝟙 A) (𝟙 A) :=
  rosatiAdj_of_points hL _ _ fun _ => ⟨⊤, trivial, fun T x y _ =>
    ⟨PEmpty, inferInstance, _, _, LB.oneGen L, isGen_oneGen L, fun V _ k => by
      rw [Category.comp_id, Category.comp_id, Fintype.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel⟩⟩

theorem rosatiAdj_inv (hL : L.IsLB) (hs : Out.Sym A L) : RosatiAdj A L (𝟙 A)⁻¹ (𝟙 A)⁻¹ := by
  refine rosatiAdj_of_points hL _ _ fun s => ?_
  obtain ⟨U, hU, t, ht⟩ := hs s
  refine ⟨U, hU, fun T x y hT => ?_⟩
  have lf : ∀ w : T ⟶ A, ∃ m : T.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, m ≫ (A.hom ⁻¹ᵁ U).ι = w.left := fun w =>
    ⟨IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι w.left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      have e := congrArg (fun q => q p) (Over.w w)
      exact (congrArg (· ∈ U) e).mpr (hT p)), IsOpenImmersion.lift_fac _ _ _⟩
  choose m hm using lf
  have pr : ∀ (w : T ⟶ A) (V : Type) [CommGroup V] (k : (T.left ⟶ A.left) → V),
      ∏ i : Fin 2, k (m w ≫ (![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] :
        Fin 2 → ((A.hom ⁻¹ᵁ U).toScheme ⟶ A.left)) i) ^ (![1, -1] : Fin 2 → ℤ) i =
        k (w⁻¹).left * (k w.left)⁻¹ := fun w V _ k => by
    rw [Fin.prod_univ_two]
    show k (m w ≫ (A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) ^ (1 : ℤ) *
      k (m w ≫ (A.hom ⁻¹ᵁ U).ι) ^ (-1 : ℤ) = _
    rw [← Category.assoc, hm, zpow_one, zpow_neg_one]
    rfl
  refine ⟨(Fin 2 ⊕ Fin 2) ⊕ Fin 2, inferInstance, _, _,
    LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ t (m (x * y⁻¹))) (LB.pullGen L _ _ t (m y)))
      (LB.invGen L _ _ (LB.pullGen L _ _ t (m x))),
    DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)), fun V _ k => ?_⟩
  refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := V) _
    (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (pr (x * y⁻¹) V k) (pr y V k))
    (DVR.prod_neg _ _ (pr x V k))).trans ?_
  have e : ∀ w : T ⟶ A, w ≫ (𝟙 A)⁻¹ = w⁻¹ := fun w => by rw [GrpObj.comp_inv, Category.comp_id]
  rw [e, e, mul_inv, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, mul_inv, inv_inv]
  abel

theorem rosatiAdj_zpow (M : RigLB A) (c : CubicalStr A M) (hs : Out.Sym A M.L) (a : ℤ) :
    RosatiAdj A M.L ((𝟙 A) ^ a) ((𝟙 A) ^ a) := by
  induction a using Int.induction_on with
  | zero => rw [zpow_zero]; exact rosatiAdj_one M.isLB
  | succ n ih => rw [zpow_add_one]; exact rosatiAdj_mul S A M c _ _ _ _ ih (rosatiAdj_id M.isLB)
  | pred n ih => rw [zpow_sub_one]; exact rosatiAdj_mul S A M c _ _ _ _ ih (rosatiAdj_inv M.isLB hs)

theorem comp_id_zpow {T : Over S} (w : T ⟶ A) (a : ℤ) : w ≫ (𝟙 A) ^ a = w ^ a := by
  rw [GrpObj.comp_zpow, Category.comp_id]

theorem isMonHom_id_zpow (a : ℤ) : IsMonHom ((𝟙 A : A ⟶ A) ^ a) := by
  refine ⟨?_, ?_⟩
  · simp only [comp_id_zpow, MonObj.one_eq_one, one_zpow]
  · simp only [comp_id_zpow, MonObj.mul_eq_mul, mul_zpow, MonObj.comp_mul,
      tensorHom_fst, tensorHom_snd]


variable (A) in
def intRingAct : RingAct A ℤ where
  act a := (𝟙 A) ^ a
  hom := isMonHom_id_zpow
  map_one := zpow_one _
  map_mul a b := by rw [comp_id_zpow, ← zpow_mul, _root_.mul_comm]
  map_add a b := zpow_add _ a b

end IntAct

theorem exists_oAct_int : Out.CubeSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S),
    ∃ ρ : P.OAct ℤ, ∀ a : ℤ, ρ.act a = (𝟙 P.A : P.A ⟶ P.A) ^ a := by
  intro hC S _ P
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨c⟩ := (hC S P ⟨P.L, r, P.isLB, hr⟩ rfl).1
  exact ⟨⟨IntAct.intRingAct P.A, fun a => IntAct.rosatiAdj_zpow ⟨P.L, r, P.isLB, hr⟩ c P.sym a⟩, fun _ => rfl⟩

end GlobalTheory
end
end

end

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.homogeneousCoords_of_isValueAt_frame : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (x : (Out.baseOver (Sp K)) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (Out.baseOver (Sp K)).left) (K := Fin 1) (fun _ => x.left) (fun _ => (N : ℤ)))) (w : J → Γ((Out.baseOver (Sp K)).left, ⊤)), (∀ a, Out.IsValueAt P.A P.L N (t a) x τ (w a)) → Crd (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) (x.left : Sp K ⟶ P.A.left) (fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w a)) := by
  first | exact @GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt | exact GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt | (intros; apply GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt <;> assumption)

end
end
