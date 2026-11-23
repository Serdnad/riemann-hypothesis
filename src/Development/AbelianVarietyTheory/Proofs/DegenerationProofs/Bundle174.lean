module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle171
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle168
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle027
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MeetsOpensOfSeparatesSections
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.ParameterRoot

section Sections

variable {X Y : Scheme.{0}} {L : LB X} {f : Y ⟶ X}

def mulPow {k k' : ℕ} (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => (k : ℤ))))
    (t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => (k' : ℤ)))) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => ((k + k' : ℕ) : ℤ))) where
  f j := @id Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) (s.f j) * @id Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) (t.f j)
  compat i j := by
    let W : Y.Opens := LB.wchart L (fun _ : Fin 1 => f) i ⊓ LB.wchart L (fun _ : Fin 1 => f) j
    let gg : ℕ → Γ(Y, W)ˣ := fun d => (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => (d : ℤ))).g i j
    have e : gg (k + k') = gg k * gg k' := by
      simp only [gg, LB.LinComb, Fin.prod_univ_one, Nat.cast_add, zpow_add]
    let r₁ := (Y.presheaf.map (homOfLE (inf_le_left : W ≤ LB.wchart L (fun _ : Fin 1 => f) i)).op).hom
    let r₂ := (Y.presheaf.map (homOfLE (inf_le_right : W ≤ LB.wchart L (fun _ : Fin 1 => f) j)).op).hom
    have hs : r₁ (s.f i) = (gg k).val * r₂ (s.f j) := s.compat i j
    have ht : r₁ (t.f i) = (gg k').val * r₂ (t.f j) := t.compat i j
    have key : ∀ a a' b b', r₁ a = (gg k).val * r₂ b → r₁ a' = (gg k').val * r₂ b' →
        r₁ (a * a') = (gg (k + k')).val * r₂ (b * b') := by
      intro a a' b b' h h'
      rw [map_mul, map_mul, h, h', e, Units.val_mul]
      ring
    exact key _ _ _ _ hs ht

end Sections

section Algebra

theorem cancel {F T : Type} [Field F] (x v : T → F) (t₀ : T) (κ κ' : F) (m : ℕ) (hκ : κ ≠ 0) (hκ' : κ' ≠ 0)
    (h₀ : v t₀ ≠ 0) (h : ∀ t, κ * x t * x t₀ ^ m = κ' * (v t * v t₀ ^ m)) :
    ∃ c : F, c ≠ 0 ∧ ∀ t, x t = c * v t := by
  have hx : x t₀ ≠ 0 := by
    intro e
    have := h t₀
    rw [e, MulZeroClass.mul_zero, MulZeroClass.zero_mul] at this
    exact mul_ne_zero hκ' (mul_ne_zero h₀ (pow_ne_zero m h₀)) this.symm
  refine ⟨κ' * v t₀ ^ m / (κ * x t₀ ^ m), div_ne_zero (mul_ne_zero hκ' (pow_ne_zero m h₀))
    (mul_ne_zero hκ (pow_ne_zero m hx)), fun t => ?_⟩
  have := h t
  field_simp
  linear_combination this

end Algebra

section Point

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : UnifPre I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_val_ne_zero (hA : AmpleSt) {N : ℕ} (hN : 4 ≤ N) (x : Sp F ⟶ (UnifPre.GF (G := G) F).left)
    (l : U.LG.L.ι) (hl : ⊤ ≤ x ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => l)) :
    ∃ σ : U.SecGF F N, valF x _ (σ.f (fun _ => l)) ≠ 0 := by
  have hm := MatchCoord.mem_of_le hl
  obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB (MatchCoord.pt F)
    (fun _ : Fin 1 => x ≫ UnifPre.gFK (G := G) F) (fun _ => l) (fun _ _ _ => rfl)
    (fun k => Set.mem_iInter.1 hm k)
  obtain ⟨s, hs⟩ := GenericGenerated.exists_secK_isUnit hA R I D A G U N hN _
    (x ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) (MatchCoord.pt F) J hJ
  let σ : U.SecGF F N := H1.SectionArithmetic.pullSec s (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left
  have h₁ : sval σ x (MatchCoord.pt F) J = _ := H1.SectionArithmetic.sval_pullSec s _ x (MatchCoord.pt F) hJ
  have h₂ := sval_of σ x (MatchCoord.pt F) J (fun _ => l) e
  refine ⟨σ, fun h0 => ?_⟩
  have h₃ := MatchCoord.stk_valF hl (σ.f (fun _ => l))
  have h₄ : gs x (MatchCoord.pt F) _ (σ.f (fun _ => l)) = 0 :=
    h₃.symm.trans ((congrArg _ h0).trans (map_zero _))
  exact not_isUnit_zero ((congrArg IsUnit (h₁.symm.trans (h₂.trans h₄))).mp hs)

end Point

theorem parAt_of_parAt_mul : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N k : ℕ) (a : u.PtC) (g : GtPtF u.D.toPre (PadicAlgCl p)), 4 ≤ N → 1 ≤ k → u.ParAt (N * k) a g → u.ParAt N a g := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u lab N k a g hN hk H w hw l hl
  let x : Sp (PadicAlgCl p) ⟶ (UnifPre.GF (G := u.G) (PadicAlgCl p)).left :=
    (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left
  have hx : x ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = u.toG a := by
    have : x ≫ (snd (TFK (R := u.V) (PadicAlgCl p)) ((Over.pullback (jK u.V)).obj u.G)).left = a.left :=
      congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst u.G.hom (jK u.V)) this)
  have hl' : ⊤ ≤ x ⁻¹ᵁ LB.wchart u.U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => l) := by
    intro z _
    refine Set.mem_iInter.2 fun _ => ?_
    have : (x ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p)) z ∈ u.U.LG.L.U l := by
      rw [hx]; exact hl (Set.mem_univ z)
    exact this
  let v : ∀ d : ℕ, u.U.toUnifPre.SecGF (PadicAlgCl p) d → PadicAlgCl p := fun d σ =>
    valF x (LB.wchart u.U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => l))
      (σ.f (fun _ => l))
  have expd : ∀ d : ℕ, 1 ≤ d → ∀ σ : u.U.toUnifPre.SecGF (PadicAlgCl p) d,
      ∃ s, u.U.toUnifPre.ExpandsG (PadicAlgCl p) d σ s := fun d hd σ =>
    ((FieldBaseChange.expandsG_bijective u.U.toUnifPre (PadicAlgCl p) hL.1.globalFns hd (u.U.expand d hd)).1 σ).exists
  have summ : ∀ s : Fam u.D.toPre (PadicAlgCl p) N,
      HasSum (fun χ => GlobalTheory.UT.coef s g w χ) (∑' χ, GlobalTheory.UT.coef s g w χ) := fun s =>
    (GlobalTheory.T.summable_fourierCoefficients_family_finite_extension hL o Ω S ρ p y₀ u lab N (by omega) s g w hw).1.hasSum
  obtain ⟨σ₀, h₀⟩ : ∃ σ, v N σ ≠ 0 := exists_val_ne_zero u.U.toUnifPre hL.1.ample hN x l hl'
  obtain ⟨s₀, hs₀⟩ := expd N (by omega) σ₀
  have key : ∀ (m d : ℕ), d = N * (m + 1) → ∃ w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) d g.b, w'.IsGen ∧
      ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ σ s, u.U.toUnifPre.ExpandsG (PadicAlgCl p) N σ s →
        ∃ τ t, u.U.toUnifPre.ExpandsG (PadicAlgCl p) d τ t ∧ v d τ = v N σ * v N σ₀ ^ m ∧
          HasSum (fun χ => GlobalTheory.UT.coef t g w' χ)
            (κ * (∑' χ, GlobalTheory.UT.coef s g w χ) * (∑' χ, GlobalTheory.UT.coef s₀ g w χ) ^ m) := by
    intro m
    induction m with
    | zero =>
      intro d hd
      obtain rfl : N = d := by omega
      refine ⟨w, hw, 1, one_ne_zero, fun σ s hs => ⟨σ, s, hs, by simp, ?_⟩⟩
      simpa using summ s
    | succ m ih =>
      intro d hd
      obtain ⟨w', hw', κ, hκ, h⟩ := ih _ rfl
      obtain rfl : d = N * (m + 1) + N := hd
      have h1 : 1 ≤ N * (m + 1) := Nat.mul_pos (by omega) (by omega)
      obtain ⟨w'', hw''⟩ : ∃ w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (N * (m + 1) + N) g.b, w.IsGen :=
        DVR.exists_gen_of_local (V := PadicAlgCl p) u.D.toPre.P.L u.D.toPre.P.isLB _ _
      obtain ⟨c, hc, hp⟩ := GlobalTheory.T.fourierSeries_product_eq_product_series hL o Ω S ρ p y₀ u lab (N * (m + 1)) N g w' w w'' h1 (by omega) hw' hw hw''
      refine ⟨w'', hw'', c * κ, mul_ne_zero hc hκ, fun σ s hs => ?_⟩
      obtain ⟨τ, t, hτ, e, hsum⟩ := h σ s hs
      obtain ⟨t', ht'⟩ := expd (N * (m + 1) + N) (by omega) (mulPow τ σ₀)
      refine ⟨mulPow τ σ₀, t', ht', ?_, ?_⟩
      · have : v _ (mulPow τ σ₀) = v _ τ * v _ σ₀ := MatchCoord.valF_mul hl' _ _
        rw [this, e]; ring
      · convert hp τ σ₀ (mulPow τ σ₀) t s₀ t' hτ hs₀ ht' (fun _ => rfl) _ _ hsum (summ s₀) using 1
        ring
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨w', hw', κ, hκ, h⟩ := key m _ rfl
  obtain ⟨κ', hκ', h'⟩ := H w' hw' l hl
  obtain ⟨c, hc, e⟩ := cancel (T := {q : u.U.toUnifPre.SecGF (PadicAlgCl p) N × Fam u.D.toPre (PadicAlgCl p) N //
      u.U.toUnifPre.ExpandsG (PadicAlgCl p) N q.1 q.2}) (fun q => ∑' χ, GlobalTheory.UT.coef q.1.2 g w χ)
    (fun q => v N q.1.1) ⟨(σ₀, s₀), hs₀⟩ κ κ' m hκ hκ' h₀ (fun q => by
      obtain ⟨τ, t, hτ, e, hsum⟩ := h q.1.1 q.1.2 q.2
      exact (hsum.unique (h' τ t hτ)).trans (congrArg (κ' * ·) e))
  refine ⟨c, hc, fun σ s hs => ?_⟩
  have := summ s
  rw [e ⟨(σ, s), hs⟩] at this
  exact this

end GlobalTheory.ParameterRoot
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsionNonzero

section Pull
variable {X Y : Scheme.{0}}

abbrev one (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)

theorem chart_le (L : LB X) {V : X.Opens} (F : Y ⟶ X) (h : ⊤ ≤ F ⁻¹ᵁ V) (k : PUnit → L.ι) :
    (L.pull F).U k ≤ F ⁻¹ᵁ (V ⊓ (one L).U (fun _ => k PUnit.unit)) := fun x hx =>
  ⟨h (x := x) trivial, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx PUnit.unit⟩

theorem appLE_res (F : Y ⟶ X) {U V : X.Opens} {W : Y.Opens} (e : V ≤ U) (h : W ≤ F ⁻¹ᵁ V) (h' : W ≤ F ⁻¹ᵁ U)
    (a : Γ(X, U)) : (F.appLE V W h).hom (resG X e a) = (F.appLE U W h').hom a := by
  rw [← Scheme.Hom.map_appLE F h (homOfLE e).op]
  rfl

theorem res_appLE (F : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens} (e : W' ≤ W) (h : W ≤ F ⁻¹ᵁ U) (h' : W' ≤ F ⁻¹ᵁ U)
    (a : Γ(X, U)) : resG Y e ((F.appLE U W h).hom a) = (F.appLE U W' h').hom a := by
  rw [← Scheme.Hom.appLE_map F h (homOfLE e).op]
  rfl

theorem g_eq {K : Type} [Fintype K] [Unique K] (L : LB X) (F : Y ⟶ X) (i j : K → L.ι)
    (h : _ ≤ F ⁻¹ᵁ (L.U (i default) ⊓ L.U (j default))) :
    ((LB.LinComb L (K := K) (fun _ => F) (fun _ => 1)).g i j).val =
      (F.appLE _ _ h).hom (L.g (i default) (j default)).val := by
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

def pullSec (L : LB X) {V : X.Opens} (σ : ∀ j, Γ(X, V ⊓ (one L).U j)) (hσ : σ ∈ secOn (one L) V) (F : Y ⟶ X)
    (h : ⊤ ≤ F ⁻¹ᵁ V) : (L.pull F).Sec where
  f k := (F.appLE _ _ (chart_le L F h k)).hom (σ fun _ => k PUnit.unit)
  compat i j := by
    have hi := (inf_le_left : (L.pull F).U i ⊓ (L.pull F).U j ≤ _).trans (chart_le L F h i)
    have hj := (inf_le_right : (L.pull F).U i ⊓ (L.pull F).U j ≤ _).trans (chart_le L F h j)
    have hj' : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (one L).U (fun _ => j PUnit.unit) :=
      hj.trans (F.preimage_mono inf_le_right)
    have hi' : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (one L).U (fun _ => i PUnit.unit) :=
      hi.trans (F.preimage_mono inf_le_right)
    have hW : (L.pull F).U i ⊓ (L.pull F).U j ≤
        F ⁻¹ᵁ (V ⊓ (one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit)) := le_inf hi hj'
    have h₁ : (one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit) ≤
        𝟙 X ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.wchart_le L _ _ 0) (LB.wchart_le L _ _ 0)
    have h₂ : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.wchart_le L _ _ PUnit.unit) (LB.wchart_le L _ _ PUnit.unit)
    have hU : (L.pull F).U i ⊓ (L.pull F).U j ≤
        F ⁻¹ᵁ ((one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit)) := le_inf hi' hj'
    have e := congrArg (F.appLE _ _ hW).hom (hσ (fun _ => i PUnit.unit) (fun _ => j PUnit.unit))
    rw [map_mul, appLE_res F _ hW hi, appLE_res F _ hW hj, appLE_res F _ hW hU] at e
    refine (res_appLE F _ _ hi _).trans (e.trans (congrArg₂ (· * ·) ?_ (res_appLE F _ _ hj _).symm))
    refine (congrArg (F.appLE _ _ hU).hom (g_eq L (𝟙 X) _ _ h₁)).trans (Eq.trans ?_ (g_eq L F i j h₂).symm)
    exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val)
      (Scheme.Hom.appLE_comp_appLE F (𝟙 X) _ _ _ h₁ hU)

theorem le_nonzeroLocus_iff (L : LB X) {V : X.Opens} (σ : ∀ j, Γ(X, V ⊓ (one L).U j)) (hσ : σ ∈ secOn (one L) V)
    (F : Y ⟶ X) (h : ⊤ ≤ F ⁻¹ᵁ V) {K : Type} [Field K] (x : Sp K ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (pullSec L σ hσ F h) ↔ ∃ j, valF (x ≫ F) _ (σ j) ≠ 0 := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((Points.le_preimage_iff x _).1 hx)
    have h₁ := (Points.le_preimage_iff x _).2 hk
    have h₂ := Points.le_preimage_mono x (Y.basicOpen_le _) h₁
    have h₃ := (Points.le_preimage_basicOpen_iff x h₂ _).1 h₁
    refine ⟨fun _ => k PUnit.unit, ?_⟩
    rw [Points.valF_eq_valR, ← Points.valR_appLE x F (chart_le L F h k) h₂]
    exact h₃.ne_zero
  · rintro ⟨j, hj⟩
    obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩
    have h₁ : ⊤ ≤ (x ≫ F) ⁻¹ᵁ (V ⊓ (one L).U fun _ => a) := by
      by_contra hc
      exact hj (dif_neg hc)
    have h₂ : ⊤ ≤ x ⁻¹ᵁ (L.pull F).U (fun _ => a) := fun z hz =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (h₁ hz).2 0
    rw [Points.valF_eq_valR, ← Points.valR_appLE x F (chart_le L F h fun _ => a) h₂] at hj
    exact Points.le_preimage_mono x (le_iSup (fun k => Y.basicOpen ((pullSec L σ hσ F h).f k)) fun _ => a)
      ((Points.le_preimage_basicOpen_iff x h₂ _).2 hj.isUnit)

end Pull

theorem exists_torsion_valF_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L → ∀ (N : M.Z.Opens) (σ : Q.SecFam N), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.FibNe N σ → y (cPt p) ∈ N → ∃ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV) ⟶ u.G, t ^ (S.r * S.N) = 1 ∧ ∃ j, valF (X := Q.G.left) (t.left ≫ F) _ (σ j) ≠ 0 := by
  intro laws laws₂ o Ω _ _ _ _ S ρ M U₀ Q hbig p _ y y₀ u jV yV yK hfac F ψ hmap hiso N σ hσ hne hy
  obtain ⟨hj, hyV, -, -⟩ := hfac
  have hloc := ZHPre.isLocalHom_of_test u jV hj
  have hK : IsAlgClosed (IsLocalRing.ResidueField (OO p)) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hsq := hmap.1.1
  set r : Sp (IsLocalRing.ResidueField (OO p)) ⟶ Sp u.V :=
    spMap (IsLocalRing.residue (OO p)) ≫ spMap jV with hr
  have key : ∀ x, r x = IsLocalRing.closedPoint u.V := fun x => by
    have hx : x = IsLocalRing.closedPoint _ :=
      Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField (OO p))) _ _
    subst hx
    exact (congrArg (PrimeSpectrum.comap jV)
      (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans (IsLocalRing.comap_closedPoint jV)
  have hrange : Set.range r = {IsLocalRing.closedPoint u.V} := by
    ext x
    exact ⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint _, (key _).trans h.symm⟩⟩
  have hyN : ⊤ ≤ yV ⁻¹ᵁ N := by
    refine (Points.le_preimage_iff yV N).2 ?_
    rw [← hyV] at hy
    rw [← IsLocalRing.comap_closedPoint jV]
    exact hy
  have hF : ⊤ ≤ F ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N) := by
    rw [← Scheme.Hom.comp_preimage, hsq.w]
    exact fun z _ => hyN (x := u.G.hom z) trivial
  let θ := pullSec Q.L.L σ hσ F hF
  have hθ : ∃ x ∈ nonzeroLocus θ, u.G.hom x = IsLocalRing.closedPoint u.V := by
    obtain ⟨g, j, hg, hv⟩ := hne _ (r ≫ yV) (by
      rintro _ ⟨z, rfl⟩
      exact hyN (x := r z) trivial)
    have h₁ := (le_nonzeroLocus_iff Q.L.L σ hσ F hF (hsq.lift g r hg)).2 ⟨j, by rwa [hsq.lift_fst]⟩
    refine ⟨hsq.lift g r hg (IsLocalRing.closedPoint _), h₁ (x := IsLocalRing.closedPoint _) trivial, ?_⟩
    exact (congrArg (fun φ : Sp _ ⟶ Sp u.V => φ (IsLocalRing.closedPoint _)) (hsq.lift_snd g r hg)).trans (key _)
  have hg : u.A.g = S.g := (H1.dim_unique u.A.A.hom u.A.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 ρ.P.smoothDim)
    (eSec u.A.A (IsLocalRing.closedPoint (FractionRing u.V)))).trans ρ.g_eq
  have hN : 4 ≤ S.N := by
    rw [ρ.N_eq]
    have h₂ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (two_pos.trans_le ρ.two_le).ne' _)
    exact Nat.pow_le_pow_left h₂ 2
  have hn : ((S.r * S.N : ℕ) : IsLocalRing.ResidueField (OO p)) ≠ 0 := by
    have := S.unit.map (Spec.preimage (r ≫ yV ≫ M.s)).hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hlt : 6 * (S.N ^ u.A.g * u.A.g.factorial) < (S.r * S.N) ^ 2 := by
    rw [hg]
    exact hbig.2.2.trans_le (Nat.le_self_pow two_ne_zero _)
  have hc := GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ u.V u.complete u.D u.A u.G u.U (Q.L.L.pull F) θ
    (pull_isLB Q.L.isLB F) hiso hθ _ r S.N (S.r * S.N) hrange hN hn hlt 1
  by_contra hcon
  have heq : Nat.card {h : Over.mk r ⟶ u.G // h ^ (S.r * S.N) = 1 ∧ ¬ ⊤ ≤ (1 * h).left ⁻¹ᵁ nonzeroLocus θ} =
      Nat.card {h : Over.mk r ⟶ u.G // h ^ (S.r * S.N) = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun h => and_iff_left_of_imp fun hh hle => hcon ⟨h, hh, ?_⟩)
    rw [_root_.one_mul] at hle
    exact (le_nonzeroLocus_iff Q.L.L σ hσ F hF h.left).1 hle
  omega

end GlobalTheory.ZH.TorsionNonzero
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.psiCmp_of_secCmp' : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ (f : ∀ α, SecBT D (𝟙_ _) 1 α) (f' : ∀ α, SecBT D' (𝟙_ _) 1 α), SecCmp D D' β v xe f f' → PsiRel D (𝟙_ _) f → PsiRel D' (𝟙_ _) f' → (∃ j, (f' 0).f j ≠ 0) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam := by
  first | exact @GlobalTheory.psiCmp_of_secCmp | exact GlobalTheory.psiCmp_of_secCmp | (intros; apply GlobalTheory.psiCmp_of_secCmp <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.exists_thetaSection_nonzeroFibres_localRing : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ th : SecBT D (𝟙_ _) 1 0, FibNZ (𝟙_ _ ⊗ D.P.A).hom th ∧ ∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b := by
  first | exact @GlobalTheory.PsiRing.exists_basis_fibNZ | exact GlobalTheory.PsiRing.exists_basis_fibNZ | (intros; apply GlobalTheory.PsiRing.exists_basis_fibNZ <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

private theorem smConn_of_semiAbelian {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (hG : IsSemiAbelian G) : SmConn G := by
  obtain ⟨c, sm, se, qc, gc, -⟩ := hG
  exact ⟨c, sm, se, qc, gc⟩

theorem exists_semiAbelian_model_of_retract (W L : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L]
    (G : Over (Sp W)) [GrpObj G] (hG : IsSemiAbelian G) (C : Over (Sp L)) [GrpObj C]
    (a : C ⟶ (Over.pullback (spMap (algebraMap W L))).obj G)
    (b : (Over.pullback (spMap (algebraMap W L))).obj G ⟶ C) [IsMonHom a] [IsMonHom b]
    (hab : a ≫ b = 𝟙 C) :
    ∃ (G₁ : Over (Sp W)) (_ : GrpObj G₁), IsSemiAbelian G₁ ∧
      ∃ e : (Over.pullback (spMap (algebraMap W L))).obj G₁ ≅ C, IsMonHom e.hom := by

  obtain ⟨F, ⟨hF, hFe⟩, huniq⟩ :=
    GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W L G G hG hG (b ≫ a) inferInstance
  have hFF : F ≫ F = F := huniq (F ≫ F) ⟨inferInstance, by
    simp only [CategoryTheory.Functor.map_comp, hFe, Category.assoc, reassoc_of% hab]⟩

  obtain ⟨G₁, _, i, r, hSm₁, hi, hr, hir, hri⟩ :=
    GlobalTheory.T.exists_retract_of_smConn_idempotent (Sp W) G (smConn_of_semiAbelian G hG) F hF hFF
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.T.isSemiAbelian_of_retract' (Sp W) G G₁ hG hSm₁ i r hr hir
  subst hri

  refine ⟨G₁, inferInstance, hG₁,
    { hom := (Over.pullback (spMap (algebraMap W L))).map i ≫ b
      inv := a ≫ (Over.pullback (spMap (algebraMap W L))).map r
      hom_inv_id := ?_
      inv_hom_id := ?_ }, ?_⟩
  · calc ((Over.pullback (spMap (algebraMap W L))).map i ≫ b) ≫ a ≫ (Over.pullback (spMap (algebraMap W L))).map r = (Over.pullback (spMap (algebraMap W L))).map i ≫ (Over.pullback (spMap (algebraMap W L))).map (r ≫ i) ≫ (Over.pullback (spMap (algebraMap W L))).map r := by
          rw [hFe]; simp only [Category.assoc]
      _ = (Over.pullback (spMap (algebraMap W L))).map (i ≫ r ≫ i ≫ r) := by simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = 𝟙 _ := by rw [reassoc_of% hir, hir, CategoryTheory.Functor.map_id]
  · calc (a ≫ (Over.pullback (spMap (algebraMap W L))).map r) ≫ (Over.pullback (spMap (algebraMap W L))).map i ≫ b = a ≫ (Over.pullback (spMap (algebraMap W L))).map (r ≫ i) ≫ b := by
          simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = 𝟙 C := by rw [hFe, Category.assoc, reassoc_of% hab, hab]
  · show IsMonHom ((Over.pullback (spMap (algebraMap W L))).map i ≫ b)
    infer_instance

theorem potModel_semiAbelian_of_retract : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (B Q : Over (Sp K)) [GrpObj B] [GrpObj Q] (i : B ⟶ Q) (r : Q ⟶ B), IsMonHom i → IsMonHom r → i ≫ r = 𝟙 B → PotModel V K Q (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ B Q _ _ i r hi hr hir hQ
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hcomp, hfin, hloc, hcompl, G, _, ⟨e, he⟩, hG⟩ := hQ

  have hab : ((Over.pullback (spMap (algebraMap K L))).map i ≫ e.inv) ≫ e.hom ≫ (Over.pullback (spMap (algebraMap K L))).map r = 𝟙 ((Over.pullback (spMap (algebraMap K L))).obj B) := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]
  obtain ⟨G₁, _, hG₁, e₁, he₁⟩ :=
    exists_semiAbelian_model_of_retract W L G hG ((Over.pullback (spMap (algebraMap K L))).obj B) ((Over.pullback (spMap (algebraMap K L))).map i ≫ e.inv) (e.hom ≫ (Over.pullback (spMap (algebraMap K L))).map r) hab
  exact ⟨W, L, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, hcomp, hfin, hloc, hcompl, G₁, ‹_›, ⟨e₁, he₁⟩, hG₁⟩

end GlobalTheory.SS
end
