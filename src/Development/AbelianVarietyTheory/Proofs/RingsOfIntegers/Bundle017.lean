module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ESecStruct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullExpLoc

theorem sum_match {Γ : Type} [CommRing Γ] {K : Type} (S S'' : Finset K) (g : K → K) (hg : Function.Injective g)
    (F T A T' ρ : K → Γ) (ξ : Γ) (hF : ∀ χ, F (g χ) = A χ * (ξ * ρ χ)) (hT : ∀ χ, T (g χ) * ρ χ = T' χ)
    (hoff : ∀ β, (∀ χ, β ≠ g χ) → F β = 0) (h'' : ∀ β ∉ S'', F β = 0) (h : ∀ χ ∉ S, A χ = 0) :
    ∑ β ∈ S'', F β * T β = ξ * ∑ χ ∈ S, A χ * T' χ := by
  classical
  have e₁ : ∑ β ∈ S'', F β * T β = ∑ β ∈ S'' ∪ S.image g, F β * T β :=
    Finset.sum_subset Finset.subset_union_left fun β _ hβ => by rw [h'' β hβ, zero_mul]
  have e₂ : ∑ β ∈ S.image g, F β * T β = ∑ β ∈ S'' ∪ S.image g, F β * T β :=
    Finset.sum_subset Finset.subset_union_right fun β _ hβ => by
      by_cases hx : ∃ χ, β = g χ
      · obtain ⟨χ, rfl⟩ := hx
        rw [hF, h χ fun hχ => hβ (Finset.mem_image_of_mem g hχ), zero_mul, zero_mul]
      · rw [hoff β fun χ e => hx ⟨χ, e⟩, zero_mul]
  rw [e₁, ← e₂, Finset.sum_image fun x _ y _ e => hg e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [hF, ← hT]
  ring

theorem tG_lin (hGF : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
    {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hlin : U.OLinear O ιD ιA ιG) (e : ℕ) (a : O)
    (u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
    (hu : u.IsGen)
    (hu0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (χ : D.toPre.X) {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J)
    (hJ : Geo.Tor.Good D.toPre.P.L z J) :
    Geo.Tor.val (tG U e (star a • χ)) r z J *
      Geo.Tor.val (LB.pullGen D.toPre.P.L _ _ u (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left)
        (r ≫ pGl U e) z J =
      Geo.Tor.val (tG U e χ) (r ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left) z J := by
  have H := Geo.Tor.val_corr hJ (TLinPf.tLin_of hGF R I O D A G U ιD ιA ιG hlin e a u hu hu0 χ) r
  have E : (U.gt e).pG ≫ lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A) =
      lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG := by
    rw [comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  have E' : (r ≫ pGl U e) ≫ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left =
      r ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left :=
    (Category.assoc _ _ _).trans (congrArg (fun q => r ≫ q.left) E)
  refine Eq.trans ?_ (H.trans (Geo.Tor.val_pull hJ _ _ r))
  refine Eq.trans ?_ (Geo.Tor.val_mul hJ _ _ r).symm
  refine congrArg _ ?_
  refine (Geo.Tor.val_pull hJ _ _ _).trans (Eq.trans ?_ (Geo.Tor.val_pull hJ _ _ r).symm)
  rw [E']

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), ∀ uR : LB.Gen (LB.LinComb P.D.toPre.P.L (rosatiφ P.D.toPre.P.A (P.oD.onB.act (star a)) (P.oD.onB.act a)) rosatiε), uR.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ uR (zero2 P.D.toPre.P.A)) (LB.oneGen P.D.toPre.P.L) → ∀ (e k : ℕ) (σ'' : H0 P.U.LG.L (k * N)) (τ : H0 P.U.LG.L k) (f'' : ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α) (f : ∀ α : P.D.toPre.X, P.D.toPre.SecB k α), P.U.ExpandsAt e (k * N) σ'' f'' → P.U.ExpandsAt e k τ f → ((∀ (χ : P.D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ P.D.toPre.P.A.left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → Geo.Tor.sval (f'' (star a • χ)) r z J = Geo.Tor.sval (f χ) (r ≫ (P.oD.onB.act a).left) z J * (Geo.Tor.val X r z J ^ k * Geo.Tor.val (LB.pullGen P.D.toPre.P.L _ _ uR (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left) r z J).val) ∧ ∀ β : P.D.toPre.X, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' β).f j = 0) → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k * N)).val * sv P.U.toUnifPre (k * N) σ'' (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k).val * sv P.U.toUnifPre k τ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL')) := by
  intro hGF V _ _ _ E _ _ _ H t P a N hN hN0 X uR huR huR0 e k σ'' τ f'' f h'' hf hrel Z r z J hJ jL jL' hL hL'
  letI := H.starRing
  obtain ⟨S'', hS''⟩ := expandsAt_val P.U.toUnifPre e (k * N) σ'' f'' h''
  obtain ⟨S, hS⟩ := expandsAt_val P.U.toUnifPre e k τ f hf
  obtain ⟨a₁, a₂⟩ := hS'' Z r z J hJ
  obtain ⟨b₁, b₂⟩ := hS Z (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z J hJ
  have hp : (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e =
      (r ≫ pGl P.U.toUnifPre e) ≫ (P.oD.onB.act a).left :=
    (Category.assoc _ _ _).trans ((congrArg (fun q => r ≫ q) (pG_act P.U.toUnifPre P.lin e a)).trans
      (Category.assoc _ _ _).symm)
  refine (a₂ jL hL).trans (Eq.trans ?_ (congrArg _ (b₂ jL' hL')).symm)
  refine sum_match S S'' (fun χ => star a • χ) (fun _ _ h => smul_star_inj a N hN hN0 h) _ _ _ _
    (fun χ => (Geo.Tor.val (LB.pullGen P.D.toPre.P.L _ _ uR
      (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c χ) (𝟙 P.D.toPre.P.A)).left) (r ≫ pGl P.U.toUnifPre e) z J).val) _
    (fun χ => ?_) (fun χ => ?_) (fun β hβ => ?_) a₁ b₁
  · rw [hp]
    exact (hrel.1 χ Z _ z J hJ).trans (congrArg _ (Units.val_mul _ _))
  · exact (Units.val_mul _ _).symm.trans
      (congrArg Units.val (tG_lin hGF P.U.toUnifPre P.lin e a uR huR huR0 χ r z J hJ))
  · exact (congrArg (Geo.Tor.gs _ z _) (hrel.2 β hβ _)).trans (gs_zero _ z _ (hJ.mem _ _))

end GlobalTheory.PullExpLoc
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.MixedCross

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cross_pow {Γ : Type} [CommRing Γ] (W W' X : Γˣ) {k₁ k₂ m₁ m₂ N : ℕ} (hm : m₁ * k₁ = m₂ * k₂)
    (s₁ t₁ s₂ t₂ : Γ)
    (h₁ : (W ^ (k₁ * N)).val * s₁ = (X ^ k₁).val * ((W' ^ k₁).val * t₁))
    (h₂ : (W ^ (k₂ * N)).val * s₂ = (X ^ k₂).val * ((W' ^ k₂).val * t₂)) :
    s₁ ^ m₁ * t₂ ^ m₂ = s₂ ^ m₂ * t₁ ^ m₁ := by
  push_cast at h₁ h₂
  have e₁ := congrArg (· ^ m₁) h₁
  have e₂ := congrArg (· ^ m₂) h₂
  simp only [mul_pow, ← pow_mul] at e₁ e₂
  have a₁ : k₁ * N * m₁ = m₁ * k₁ * N := by ring
  have a₂ : k₂ * N * m₂ = m₁ * k₁ * N := by rw [hm]; ring
  have b₁ : k₁ * m₁ = m₁ * k₁ := by ring
  have b₂ : k₂ * m₂ = m₁ * k₁ := by rw [hm]; ring
  rw [a₁, b₁] at e₁
  rw [a₂, b₂] at e₂
  have hu : IsUnit ((W : Γ) ^ (m₁ * k₁ * N)) := W.isUnit.pow _
  apply hu.mul_left_cancel
  calc (W : Γ) ^ (m₁ * k₁ * N) * (s₁ ^ m₁ * t₂ ^ m₂)
      = ((W : Γ) ^ (m₁ * k₁ * N) * s₁ ^ m₁) * t₂ ^ m₂ := by ring
    _ = (X : Γ) ^ (m₁ * k₁) * ((W' : Γ) ^ (m₁ * k₁) * t₁ ^ m₁) * t₂ ^ m₂ := by rw [e₁]
    _ = ((W : Γ) ^ (m₁ * k₁ * N) * s₂ ^ m₂) * t₁ ^ m₁ := by rw [e₂]; ring
    _ = (W : Γ) ^ (m₁ * k₁ * N) * (s₂ ^ m₂ * t₁ ^ m₁) := by ring

theorem gs_sub' {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by
  simp only [gs, dif_pos h, map_sub]

theorem sec_eq_of_thick (hB : lemmaBSt.{0}) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (G.left ⟶ Y)} {ε : K → ℤ}
    (s s' : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ (e : ℕ) (z : (thickObj V (maximalIdeal V) e G).left) (J), Good L z J →
      sval s (fGl (maximalIdeal V) G e) z J = sval s' (fGl (maximalIdeal V) G e) z J) (j : K → L.ι) :
    s.f j = s'.f j := by
  classical
  unfold sval fGl at h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hN : (LB.LinComb L φ ε).IsLB := linComb_isLB L hL φ ε
  refine sub_eq_zero.mp (hB V G (LB.LinComb L φ ε) hN (subSec s s') ϖ hϖ (fun i e => ?_) j)
  cases e with
  | zero => simp
  | succ e =>
    have hv : ∀ i', ((fstG (maximalIdeal V) e G).left.app ((LB.LinComb L φ ε).U i')).hom
        ((subSec s s').f i') = 0 := by
      intro i'
      apply fn_ext
      intro z hz
      have hz' : (fstG (maximalIdeal V) e G).left z ∈ LB.wchart L φ i' := hz
      obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
      have hm := hJ.mem φ (fstG (maximalIdeal V) e G).left
      have h1 := h e z J hJ
      rw [gs_eq (𝟙 _) z _ hz 0, map_zero, map_zero, gs_pull (𝟙 _) _ z ((LB.LinComb L φ ε).U i') hz', Category.id_comp]
      show gs (fstG (maximalIdeal V) e G).left z (LB.wchart L φ i') (s.f i' - s'.f i') = 0
      refine (gs_sub' _ z (LB.wchart L φ i') hz' (s.f i') (s'.f i')).trans (sub_eq_zero.mpr ?_)
      rw [sec_trans s _ z hz' hm, sec_trans s' _ z hz' hm, h1]
    obtain ⟨τ, hτ⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G (LB.LinComb L φ ε) (subSec s s') e).1 hv
    unfold SecIsMul at hτ
    rw [hτ i]
    refine Ideal.mul_mem_right _ _ ?_
    have hc : resTop ((LB.LinComb L φ ε).U i) (scal G.hom (ϖ ^ (e + 1))) =
        ((G.left.presheaf.map (homOfLE le_top).op).hom
          ((G.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ))) ^ (e + 1) := by
      simp only [resTop, scal, map_pow]
      rfl
    rw [hc]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _

theorem main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (k₁ k₂ m₁ m₂ : ℕ), m₁ * k₁ = m₂ * k₂ → ∀ (σ₁ : H0 P.U.LG.L (k₁ * N)) (τ₁ : H0 P.U.LG.L k₁) (σ₂ : H0 P.U.LG.L (k₂ * N)) (τ₂ : H0 P.U.LG.L k₂), (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k₁ * N)).val * sv P.U.toUnifPre (k₁ * N) σ₁ (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k₁).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k₁).val * sv P.U.toUnifPre k₁ τ₁ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k₂ * N)).val * sv P.U.toUnifPre (k₂ * N) σ₂ (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k₂).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k₂).val * sv P.U.toUnifPre k₂ τ₂ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval σ₁ r y J ^ m₁ * Geo.Tor.sval τ₂ (r ≫ (t.act.act a).left) y J ^ m₂ = Geo.Tor.sval σ₂ r y J ^ m₂ * Geo.Tor.sval τ₁ (r ≫ (t.act.act a).left) y J ^ m₁ := by
  intro hB V _ _ _ E _ _ _ H t P a N haN hN X k₁ k₂ m₁ m₂ hm σ₁ τ₁ σ₂ τ₂ h₁ h₂
  classical
  have : Smooth t.G.hom := t.semi.smooth
  have : IsSeparated t.G.hom := t.semi.separated
  have : QuasiCompact t.G.hom := t.semi.quasiCompact
  have : GeometricallyConnected t.G.hom := t.semi.geomConnected
  have hL : P.U.LG.L.IsLB := P.U.LG.isLB
  have hD : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  have eA : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L y J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)) r y J = sval σ₁ r y J ^ m₁ * sval τ₂ (r ≫ (t.act.act a).left) y J ^ m₂ := by
    intro Z r y J hJ
    rw [H1.SectionArithmetic.sval_mulSec _ _ r y hJ, H1.SectionArithmetic.sval_pullSec _ _ r y hJ, H1.SectionArithmetic.sval_powSec _ r y hJ,
      H1.SectionArithmetic.sval_powSec _ _ y hJ]
    simp [Finset.prod_const]
  have eB : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L y J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => σ₂)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => τ₁)) (t.act.act a).left)) r y J = sval σ₂ r y J ^ m₂ * sval τ₁ (r ≫ (t.act.act a).left) y J ^ m₁ := by
    intro Z r y J hJ
    rw [H1.SectionArithmetic.sval_mulSec _ _ r y hJ, H1.SectionArithmetic.sval_pullSec _ _ r y hJ, H1.SectionArithmetic.sval_powSec _ r y hJ,
      H1.SectionArithmetic.sval_powSec _ _ y hJ]
    simp [Finset.prod_const]
  obtain ⟨B', hB'⟩ : ∃ B' : type_of% (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L z J →
        sval B' r z J = sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => σ₂)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => τ₁)) (t.act.act a).left)) r z J := by
    refine exists_sec hL ?_ _
    intro U _ h
    simp only [Fintype.prod_sum_type, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Sum.elim_inl, Sum.elim_inr, Category.comp_id]
    have hz : (m₁ : ℤ) * k₁ = m₂ * k₂ := by exact_mod_cast hm
    simp only [← zpow_natCast, ← zpow_mul]
    congr 2
    · push_cast
      linear_combination (-(N : ℤ)) * hz
    · push_cast
      linear_combination hz
  have hthick : ∀ (e : ℕ) (z : (thickObj V (maximalIdeal V) e t.G).left)
      (J : ((thickObj V (maximalIdeal V) e t.G).left ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L z J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)) (fGl (maximalIdeal V) t.G e) z J = sval B' (fGl (maximalIdeal V) t.G e) z J := by
    intro e z J hJ
    rw [hB' _ _ z J hJ, eA _ _ z J hJ, eB _ _ z J hJ]
    obtain ⟨JD, hJD, -⟩ := exists_good P.D.toPre.P.L hD z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun a => a.elim)
    have m1 : (𝟙 _ ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U (J (fGl (maximalIdeal V) t.G e ≫ 𝟙 t.G.left)) := by
      simpa using hJ (fGl (maximalIdeal V) t.G e ≫ 𝟙 t.G.left)
    have m2 : ((𝟙 _ ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫
        fGl (maximalIdeal V) t.G e) z ∈
          P.U.LG.L.U (J ((fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left)) := by
      have hz := hJ ((fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left)
      have eq : (𝟙 _ ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫
          fGl (maximalIdeal V) t.G e = (fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left := by
        rw [Category.id_comp, Category.comp_id]
        exact fstG_act _ _ _
      rw [eq]
      exact hz
    have c := cross_pow _ _ _ hm _ _ _ _ (h₁ e _ (𝟙 _) z JD hJD _ _ m1 m2) (h₂ e _ (𝟙 _) z JD hJD _ _ m1 m2)
    unfold sv at c
    simp only [Category.id_comp, fGl, fstG_act] at c
    unfold sval
    simp only [fGl]
    exact c
  intro Z r y J hJ
  rw [← eA Z r y J hJ, ← eB Z r y J hJ, ← hB' Z r y J hJ]
  have hAB := sec_eq_of_thick hB t.G hL _ B' hthick
  unfold sval
  rw [hAB]

end GlobalTheory.MixedCross
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section BoxValues

variable {X Y Z : Scheme.{0}}

private theorem gm_inv' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)ˣ) :
    gm r z U a⁻¹ = (gm r z U a)⁻¹ := by
  unfold gm
  rw [dite_eq_left h]
  exact map_inv _ a

private theorem gm_res' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {U V : Y.Opens} (hle : V ≤ U) (h : r z ∈ V)
    (a : Γ(Y, U)ˣ) : gm r z V (res hle a) = gm r z U a := by
  ext
  rw [← gs_unit r z V h, ← gs_unit r z U (hle h)]
  exact gs_res r z hle h a.val

theorem gs_secOfIso_eq {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB)
    (a : A.ι) (b : B.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ A.U a ⊓ B.U b) :
    gs r z (A.U a) ((secOfIso t hu hA hB).f a) =
      ((gm r z ((LB.div B A).U (b, a)) (u.s (b, a)))⁻¹).val * gs r z (B.U b) (t.f b) := by
  have hD : r z ∈ (LB.div B A).U (b, a) := divLe a b hz
  rw [← gs_res r z (inf_le_left : A.U a ⊓ B.U b ≤ A.U a) hz]
  change gs r z _ (rs inf_le_left ((secOfIso t hu hA hB).f a)) = _
  rw [secOfIso_spec t hu hA hB a b, isoCand, gs_mul r z _ hz, gs_unit r z _ hz, gm_inv' r z _ hz,
    gm_res' r z (divLe a b) hz]
  congr 1
  exact gs_res r z inf_le_right hz (t.f b)

theorem gs_boxSecGen_eq {X' Y' : Scheme.{0}} (L : LB X) {j : ℕ} (pr : Fin j → (X' ⟶ X)) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (p : Fin j → (Y' ⟶ Y)) (φ : Fin j → K → (Y ⟶ X))
    (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a) (σ : ∀ i, LB.Sec (LB.LinComb L (φ i) ε))
    (jN : K → Fin j → L.ι) (r : Z ⟶ Y') (z : Z) (hz : r z ∈ LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN) :
    gs r z _ ((boxSecGen L pr φ' ε p φ hφ σ).f jN) =
      ∏ i, gs (r ≫ p i) z (LB.wchart L (φ i) (fun a => jN a i)) ((σ i).f (fun a => jN a i)) := by
  change gs r z _ (boxSecGenF L pr φ' ε p φ hφ σ jN) = _
  rw [boxSecGenF, gs_prod r z _ hz]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [gs_res r z _ hz]
  exact gs_pull r (p i) z _ (box_le_of_comp L pr φ' (φ i) (p i) i (hφ i) jN hz) _

theorem exists_boxSec_val {X' Y' : Scheme.{0}} {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB) {j : ℕ}
    {pr : Fin j → (X' ⟶ X)} (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (p : Fin j → (Y' ⟶ Y)) (φ : Fin j → K → (Y ⟶ X))
    (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a) (σ : ∀ i, LB.Sec (LB.LinComb M (φ i) ε)) :
    ∃ σ' : LB.Sec (LB.LinComb M' φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J J'), Good M z J → Good M' z J' →
      (∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a).val * sval σ' r z J' =
        ∏ i, sval (σ i) (r ≫ p i) z J := by
  refine ⟨secOfIso (u := LB.linCombIso w φ' ε) (boxSecGen M pr φ' ε p φ hφ σ) (linCombIso_isGen w hw φ' ε)
    (linComb_isLB M' hM' φ' ε) (linComb_isLB _ (linComb_isLB M hM pr _) φ' ε), ?_⟩
  intro Z r z J J' hJ hJ'
  have hA : r z ∈ LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) := Good.mem hJ' φ' r
  have hB : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) :=
    Set.mem_iInter.2 fun a => Good.mem hJ pr (r ≫ φ' a)
  have h1 := gs_secOfIso_eq (LB.linCombIso w φ' ε) (boxSecGen M pr φ' ε p φ hφ σ) (linCombIso_isGen w hw φ' ε)
    (linComb_isLB M' hM' φ' ε) (linComb_isLB _ (linComb_isLB M hM pr _) φ' ε) (fun a => J' (r ≫ φ' a))
    (fun a i => J ((r ≫ φ' a) ≫ pr i)) r z ⟨hA, hB⟩
  have h2 := gs_boxSecGen_eq M pr φ' ε p φ hφ σ (fun a i => J ((r ≫ φ' a) ≫ pr i)) r z hB
  have h3 := gm_linCombIso w φ' ε r z (fun a i => J ((r ≫ φ' a) ≫ pr i)) (fun a => J' (r ≫ φ' a)) ⟨hB, hA⟩
  rw [sval_of _ r z J' (fun a => J' (r ≫ φ' a)) (fun _ => rfl)]
  erw [h1, h3, h2, Units.mul_inv_cancel_left]
  refine Finset.prod_congr rfl (fun i _ => (sval_of (σ i) (r ≫ p i) z J _ (fun a => ?_)).symm)
  rw [Category.assoc, Category.assoc, hφ]

end BoxValues

theorem exists_boxSec_pow_ext : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (t : Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))), ∃ t' : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))), (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval t' r z J' = ∏ i, Geo.Tor.sval (t i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J) := by
  intro R _ _ j A A' pA F _ _ k t
  have hφ : ∀ (i : Fin j) (_ : Fin 1), (snd (TFK (R := R) F) A'.A).left ≫ (pA.pr i).left =
      ((TFK (R := R) F) ◁ pA.pr i).left ≫ (snd (TFK (R := R) F) A.A).left := fun i _ => by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  obtain ⟨t', ht'⟩ := exists_boxSec_val A.isLB A'.isLB pA.w pA.w_gen
    (fun _ : Fin 1 => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))
    (fun i => ((TFK (R := R) F) ◁ pA.pr i).left) (fun _ _ => (snd (TFK (R := R) F) A.A).left) hφ t
  refine ⟨t', fun Z r z J J' hJ hJ' => ?_⟩
  have h := ht' Z r z J J' hJ hJ'
  rw [Fin.prod_univ_one, zpow_natCast] at h
  exact h

end GlobalTheory
end
end
