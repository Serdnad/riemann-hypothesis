module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreValueEqUnitMulLeadingFourierTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.LamBridge

section Charts

variable {X X' Y : Scheme.{0}}

def cpTrans {A'' A' A : LB Y} (c₁ : ChartPull A'' A' (𝟙 Y)) (c₂ : ChartPull A' A (𝟙 Y)) : ChartPull A'' A (𝟙 Y) where
  idx i := c₂.idx (c₁.idx i)
  le i _ hy := c₂.le _ (c₁.le i hy)
  g y i j hi hj := (c₁.g y i j hi hj).trans (c₂.g y _ _ (c₁.le i hi) (c₁.le j hj))

def cpDiv {A' A B' B : LB Y} (a : ChartPull A' A (𝟙 Y)) (b : ChartPull B' B (𝟙 Y)) :
    ChartPull (LB.div B' A') (LB.div B A) (𝟙 Y) where
  idx p := (b.idx p.1, a.idx p.2)
  le p _ hy := ⟨b.le _ hy.1, a.le _ hy.2⟩
  g y p q hp hq := (gm_div A' B' (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans (by rw [a.g y _ _ hp.2 hq.2, b.g y _ _ hp.1 hq.1])
    (gm_div A B (𝟙 Y) y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2)
      ⟨⟨b.le _ hp.1, a.le _ hp.2⟩, ⟨b.le _ hq.1, a.le _ hq.2⟩⟩).symm)

def cpEquiv (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (E : K' ≃ K) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (hφ : ∀ k, φ' k = φ (E k)) (hε : ∀ k, ε' k = ε (E k)) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) (𝟙 Y) :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ (𝟙 Y) ⁻¹ᵁ LB.wchart L φ (fun k => j (E.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have h := Set.mem_iInter.1 hy (E.symm k)
      rw [hφ, E.apply_symm_apply] at h
      exact h
  { idx := fun j k => j (E.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Fintype.prod_equiv E _ _ fun k => ?_
      rw [E.symm_apply_apply, hφ, hε] }

def cpFlat (L : LB X) {I K : Type} [Fintype I] [Fintype K] (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (σ : I → (Y ⟶ X'))
    (e : I → ℤ) : ChartPull (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb (LB.LinComb L ψ δ) σ e) (𝟙 Y) :=
  have le : ∀ j : I × K → L.ι, LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) j ≤
      (𝟙 Y) ⁻¹ᵁ LB.wchart (LB.LinComb L ψ δ) σ (fun i k => j (i, k)) :=
    fun _ _ hy => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  { idx := fun j i k => j (i, k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb (LB.LinComb L ψ δ) σ e (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => congrArg (· ^ e i)
        (gm_linComb L ψ δ (𝟙 Y ≫ σ i) y (fun k => j (i, k)) (fun k => j' (i, k))
          (Set.mem_iInter.1 (le j hj) i) (Set.mem_iInter.1 (le j' hj') i))).symm
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_mul, mul_comm (δ k), Category.assoc] }

end Charts

def e4 : Fin 4 ≃ ULift.{0} (Finset (Fin 2)) where
  toFun k := ⟨(![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k⟩
  invFun I := if I.down = {0, 1} then 0 else if I.down = {0} then 1 else if I.down = {1} then 2 else 3
  left_inv := by intro k; fin_cases k <;> rfl
  right_inv := by intro I; revert I; decide

theorem finFourEquivSubsetsFinTwo_down_eq (k : Fin 4) : (e4 k).down = (![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k := rfl

theorem mumfordSign_finFourEquivSubsetsFinTwo (k : Fin 4) : Oε k = (-1) ^ (2 - (e4 k).down.card) := by
  fin_cases k <;> decide

end GlobalTheory.Mum.LamBridge

namespace GlobalTheory.Mum.LamBridge

theorem lift_psum {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (u v : T ⟶ B) (I : Finset (Fin 2)) :
    (lift u v).left ≫ (psum B (x2 B) I).left = (psum B ![u, v] I).left := by
  rw [← Over.comp_left, comp_psum]
  congr 2
  funext k
  fin_cases k <;> simp [x2]

theorem mumfordBundleFourPoints_eq_lift_comp_partialSum {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (u v : T ⟶ B) (k : Fin 4) :
    lamPts u v k = (lift u v).left ≫ (psum B (x2 B) (e4 k).down).left := by
  rw [lift_psum]
  fin_cases k
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_01 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_0 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_1 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_e B u v).symm

end GlobalTheory.Mum.LamBridge

namespace GlobalTheory.Mum.LamBridge

theorem finFourEquivSubsetsFinTwo_symm_apply (I : ULift.{0} (Finset (Fin 2))) :
    (![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) (e4.symm I) = I.down := by
  rw [← finFourEquivSubsetsFinTwo_down_eq, Equiv.apply_symm_apply]

theorem exists_iso_tens : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (L₀ : LB B₀.left) (M : LB B.left), L₀.IsLB → M.IsLB → ∀ (β₂ : (G2 B₀).left ⟶ (G2 B).left) (wR : LB.Iso (abelian₂ B₀ L₀) ((abelian₂ B M).pull β₂)), wR.IsGen → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (Y : Over S₀) (x : Fin r → (Y ⟶ B₀)) (φ : (Fin r × Fin r) × Fin 4 → (Y.left ⟶ B.left)) (ε : (Fin r × Fin r) × Fin 4 → ℤ), (∀ k, φ k = (lift (x k.1.1) (x k.1.2)).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k.2)).left) → (∀ k, ε k = W k.1.1 k.1.2 * Oε k.2) → ∃ v : LB.Iso (LB.LinComb L₀ (tensφ x) (tensε W)) ((LB.LinComb M φ ε).pull (𝟙 Y.left)), v.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y.left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₀ : (Z ⟶ B₀.left) → L₀.ι), Good M z J → Good L₀ z J₀ → GlobalTheory.Mum.Two.isoVal v q z J J₀ = ∏ a, ∏ b, lamVal wR (q ≫ (lift (x a) (x b)).left) z J J₀ ^ W a b := by
  intro S₀ S B₀ _ _ B _ _ L₀ M hL₀ hM β₂ wR hw r W Y x φ ε hφ hε
  let σ : Fin r × Fin r → (Y.left ⟶ (G2 B₀).left) := fun ab => (lift (x ab.1) (x ab.2)).left
  let e : Fin r × Fin r → ℤ := fun ab => W ab.1 ab.2
  let v₁ := transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1) wR σ e
  have hv₁ : v₁.IsGen := isGen_transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1) hw σ e
  let cA : ChartPull (LB.LinComb L₀ (tensφ x) (tensε W)) (LB.LinComb (abelian₂ B₀ L₀) σ e) (𝟙 Y.left) :=
    cpTrans (cpEquiv L₀ (Equiv.prodCongr (Equiv.refl _) e4)
      (fun p : (Fin r × Fin r) × ULift.{0} (Finset (Fin 2)) => σ p.1 ≫ (psum B₀ (x2 B₀) p.2.down).left)
      (fun p => e p.1 * (-1) ^ (2 - p.2.down.card)) _ _
      (fun k => mumfordBundleFourPoints_eq_lift_comp_partialSum (x k.1.1) (x k.1.2) k.2)
      (fun k => by
        show W k.1.1 k.1.2 * Oε k.2 = W k.1.1 k.1.2 * (-1) ^ (2 - (e4 k.2).down.card)
        rw [mumfordSign_finFourEquivSubsetsFinTwo]))
      (cpFlat L₀ (fun I : ULift.{0} (Finset (Fin 2)) => (psum B₀ (x2 B₀) I.down).left)
        (fun I => (-1) ^ (2 - I.down.card)) σ e)
  let cB : ChartPull ((LB.LinComb M φ ε).pull (𝟙 Y.left))
      (LB.LinComb (abelian₂ B M) (fun p : (Fin r × Fin r) × PUnit => σ p.1 ≫ β₂) (fun p => e p.1 * 1)) (𝟙 Y.left) :=
    cpTrans (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (LB.LinComb M φ ε) (𝟙 Y.left) (𝟙 Y.left) rfl)
      (cpTrans (cpEquiv M (Equiv.prodCongr (Equiv.prodPUnit _).symm e4)
        (fun q : ((Fin r × Fin r) × PUnit) × ULift.{0} (Finset (Fin 2)) =>
          (σ q.1.1 ≫ β₂) ≫ (psum B (x2 B) q.2.down).left)
        (fun q => (e q.1.1 * 1) * (-1) ^ (2 - q.2.down.card)) φ ε
        (fun k => by rw [hφ k]; exact (Category.assoc _ _ _).symm)
        (fun k => by
          show ε k = (W k.1.1 k.1.2 * 1) * (-1) ^ (2 - (e4 k.2).down.card)
          rw [hε k, mumfordSign_finFourEquivSubsetsFinTwo, _root_.mul_one]))
        (cpFlat M (fun I : ULift.{0} (Finset (Fin 2)) => (psum B (x2 B) I.down).left)
          (fun I => (-1) ^ (2 - I.down.card)) (fun p : (Fin r × Fin r) × PUnit => σ p.1 ≫ β₂) (fun p => e p.1 * 1)))
  let c := cpDiv cA cB
  refine ⟨cGen c v₁, cGen_isGen c hv₁, fun Z q z J J₀ hJ hJ₀ => ?_⟩
  have hm : q z ∈ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y.left)) (LB.LinComb L₀ (tensφ x) (tensε W))).U
      (fun _ k => J (q ≫ 𝟙 Y.left ≫ φ k), fun k => J₀ (q ≫ tensφ x k)) :=
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (q ≫ 𝟙 Y.left ≫ φ k),
      Set.mem_iInter.2 fun k => hJ₀ (q ≫ tensφ x k)⟩
  refine (gm_res q z _ hm _).trans ((gm_transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1)
    wR σ e q z (c.idx _) (c.le _ hm)).trans ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => congrArg (· ^ W a b) ?_
  unfold GlobalTheory.PolDeg.lamVal
  have key : ∀ P P', P = P' → gm (q ≫ σ (a, b)) z _ (wR.s P) = gm (q ≫ σ (a, b)) z _ (wR.s P') := by
    rintro _ _ rfl; rfl
  refine key _ _ (Prod.ext (funext fun _ => funext fun I => ?_) (funext fun I => ?_))
  · show J _ = J _
    congr 1
    show q ≫ 𝟙 Y.left ≫ φ ((a, b), e4.symm I) = _
    rw [hφ]
    simp only [finFourEquivSubsetsFinTwo_symm_apply, Category.assoc, Category.id_comp]
  · show J₀ _ = J₀ _
    congr 1
    show q ≫ lamPts (x a) (x b) (e4.symm I) = _
    rw [mumfordBundleFourPoints_eq_lift_comp_partialSum, e4.apply_symm_apply, Category.assoc]

end GlobalTheory.Mum.LamBridge
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.SiegJoin.siegelToroidalPolCharts_of_steps5
    (hF : ∀ g n : ℕ, 1 ≤ g → 3 ≤ n → Odd n → Nonempty (SFam g n (zetaAway n))) (hMin : GlobalTheory.SiegJoin.MinSt5)
    (hPoin : GlobalTheory.Poinc.PoinSt) (hChart : GlobalTheory.SiegJoin.ChartSt5) (hDesc : GlobalTheory.SiegJoin.DescSt5) :
    GlobalTheory.Published.SiegelToroidalPolCharts := by
  intro g hg φ hφ hφ' n hn ho
  have hn0 : n ≠ 0 := by omega
  haveI : IsNoetherianRing (cycAway n) := by haveI := (GlobalTheory.SiegelTor.arBase_cycAway n hn0).1; infer_instance
  obtain ⟨F⟩ := hF g n hg hn ho
  obtain ⟨Z, z, i, OZ, hMA⟩ := hMin g hg n hn ho F
  have hMA' := hMA
  obtain ⟨o', _, β, S', s', U, c, π', G', _, e', _, N', ⟨hTh, hZp, hZn, hiz, hid, hOZ, hOZa⟩, -⟩ := hMA'
  obtain ⟨d, J, S, π, j, BD, hd, hJ, hV, hBl, hP, hj, hjd, hji, hjpre, hBD, hVj, k₀, hk₀⟩ :=
    hPoin g hg n hn ho F Z z i hTh OZ hOZ hOZa φ hφ
  haveI := hj
  have hBlow : BlowAt F z i φ d π j BD := ⟨J, hd, hJ, hV, hBl, hP, hjd, hji, hjpre, hBD, hVj⟩
  obtain ⟨hsm, hpre⟩ := hChart g hg φ hφ hφ' n hn ho F Z z i OZ d S π j BD hMA hBlow
  obtain ⟨G, _, e, hGs, hGd, hGe, hGab⟩ :=
    hDesc g hg φ n hn ho F Z z i d S π j BD hBlow hpre
  haveI := hsm
  haveI : Smooth (π ≫ z) := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) _
  haveI : QuasiSeparated G.hom := by haveI := hGs.separated; infer_instance
  obtain ⟨a, N, ha, hN, hiso⟩ := GlobalTheory.T.hodgeBundle_power_iso_minimalSiegelCompactification g n F Z z i OZ S π j G e hMA
    (fun x => ⟨hBl.1.isDomain_stalk x, hBl.1.isIntegrallyClosed_stalk x⟩) hP hjd hji hGs hGd hGe
  obtain ⟨N'', hN'', hgen, k, hk⟩ := GlobalTheory.T.exists_globallyGenerated_ample_power_toroidalPullback (cycAway n) Z S z π OZ (hodge G g) (GlobalTheory.CechPic.dual BD.lb) a N
    hZp hOZ hOZa (isLB_hodge G g) (GlobalTheory.CechPic.isLB_dual BD.isLB_lb) ha hN hiso ⟨k₀, hk₀⟩
  refine ⟨F, S, π ≫ z, j, hj, G, inferInstance, e, BD, d, N'', hP, hsm, by rw [← Category.assoc, hji, hiz], ?_,
    hGs, hGd, hGe, hGab, hd, ?_, hN'', hgen, k, hk⟩
  · intro x
    exact GlobalTheory.T.mem_closure_moduliFibre_of_monomialPeriodPreChart F (π ≫ z) j φ BD d x (hpre x)
  · intro x
    exact GlobalTheory.T.hasPolarisedChart_of_monomialPreChart_semiAbelianExt F (π ≫ z) j G e φ BD d x hn0 hGs hGd hGe hGab (hpre x)

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

theorem _root_.GlobalTheory.T.exists_uniformised_cover_pullback_semiAbelian_model : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → GlobalTheory.ZH.ZHOut ρS M U₀ EE → ∀ (b : o →+* R₁) (e : Ω →+* FractionRing R₁), (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ C : UCover R₁, C.A = A₁ := by
  first | exact @GlobalTheory.Mum.exists_uCover_of_zhOut | exact GlobalTheory.Mum.exists_uCover_of_zhOut | (intros; apply GlobalTheory.Mum.exists_uCover_of_zhOut <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum



theorem subring_eq_top_of_weight_units : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (i : splitTorus (Sp R) D.X ⟶ Y.H), IsMonHom i → IsPullback i (toUnit _) Y.q η[D.P.A] → ∀ {κ : Type} (bs : Module.Basis κ ℤ D.X) (V : D.P.A.left.Opens), IsAffineOpen V → ∀ (u : κ → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)ˣ), (∀ c, GlobalTheory.UU.IsWt i _ (u c).val (bs c)) → ∀ S : Subring Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ c, (Y.q.left.app V).hom c ∈ S) → (∀ c, (u c).val ∈ S ∧ ((u c)⁻¹).val ∈ S) → S = ⊤ := by
  intro R _ _ D Y i hi hk κ bs V hV u hu S hS hSu
  obtain ⟨hsm, haff, hsurj⟩ := Y.q_props
  have hmon : IsMonHom Y.q := Y.isMonHom_q
  let m : Multiplicative D.X →* Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)ˣ :=
    AddMonoidHom.toMultiplicativeLeft (bs.constr ℤ (fun k => Additive.ofMul (u k))).toAddMonoidHom
  have hm : ∀ k, m (Multiplicative.ofAdd (bs k)) = u k := fun k =>
    congrArg Additive.toMul (bs.constr_basis ℤ (fun k => Additive.ofMul (u k)) k)
  have key : ∀ χ : D.X, GlobalTheory.UU.IsWt i _ (m (Multiplicative.ofAdd χ)).val χ ∧
      (m (Multiplicative.ofAdd χ)).val ∈ S ∧ (m (Multiplicative.ofAdd χ))⁻¹.val ∈ S := by
    intro χ
    have hχ : χ ∈ AddSubgroup.closure (Set.range bs) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure, bs.span_eq]; trivial
    refine AddSubgroup.closure_induction (p := fun x _ => GlobalTheory.UU.IsWt i _ (m (Multiplicative.ofAdd x)).val x ∧
      (m (Multiplicative.ofAdd x)).val ∈ S ∧ (m (Multiplicative.ofAdd x))⁻¹.val ∈ S) ?_ ?_ ?_ ?_ hχ
    · rintro _ ⟨k, rfl⟩
      rw [hm]; exact ⟨hu k, hSu k⟩
    · rw [ofAdd_zero, map_one]; exact ⟨GlobalTheory.UU.isWt_one, S.one_mem, by simpa using S.one_mem⟩
    · intro x y _ _ hx hy
      rw [ofAdd_add, map_mul]
      refine ⟨hx.1.mul hy.1, ?_, ?_⟩
      · rw [Units.val_mul]; exact S.mul_mem hx.2.1 hy.2.1
      · rw [mul_inv, Units.val_mul]; exact S.mul_mem hx.2.2 hy.2.2
    · intro x _ hx
      rw [ofAdd_neg, map_inv]
      exact ⟨hx.1.inv, hx.2.2, by rw [inv_inv]; exact hx.2.1⟩
  have hbij := (isAffineOpen_and_bijective_of_weight_units (Sp R) D.X Y.H D.P.A Y.q i hmon hi inferInstance
    hsurj inferInstance hk V hV m (fun χ => (key χ).1)).2
  refine (Subring.eq_top_iff' S).2 fun f => ?_
  obtain ⟨x, rfl⟩ := hbij.2 f
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact S.zero_mem
  | add a b ha hb => rw [map_add (f := _)]; exact S.add_mem ha hb
  | single χ c =>
    change AddMonoidAlgebra.liftNC _ _ _ ∈ S
    rw [AddMonoidAlgebra.liftNC_single]
    exact S.mul_mem (hS c) (key χ).2.1

end GlobalTheory.Mum
end

section

open IsLocalRing GlobalTheory.Poinc GlobalTheory.UT

namespace GlobalTheory.Poinc

theorem isClassSum_of_sumI : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (y : Φ.Y) (N : ℕ), 1 ≤ N → ∀ (κ : Fin s → Φ.X y) (c : Φ.Q) (V' : Type) [CommRing V'] [IsLocalRing V'] (io : Φ.V y →+* V') (e : V'ˣ) (x : V'), SumI (maximalIdeal V') (fun nu : Fin s → Φ.X y => (e : V') * io (Φ.term y (κ + N • nu) c)) x → Φ.IsClassSum y N κ c io (((e⁻¹ : V'ˣ) : V') * x) := by
  intro O _ bar q s W A _ _ Φ y N hN κ c V' _ _ io e x hx j
  classical
  have hinj : Function.Injective (fun nu : Fin s → Φ.X y => κ + N • nu) := by
    intro a b h
    have h1 : N • a = N • b := add_left_cancel h
    funext v
    have h2 : (N : ℤ) • a v = (N : ℤ) • b v := by
      rw [natCast_zsmul, natCast_zsmul]; exact congrFun h1 v
    exact smul_right_injective (Φ.X y) (by omega : (N : ℤ) ≠ 0) h2
  obtain ⟨N', -, -, -, hx⟩ := hx
  obtain ⟨S₀, hS₀⟩ := hx j
  have hF : ((fun nu : Fin s → Φ.X y => κ + N • nu) ⁻¹'
      {mu | True ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ)}).Finite :=
    (PreModel.low_finite Φ y (fun _ => True) j).preimage hinj.injOn
  refine ⟨(S₀ ∪ hF.toFinset).image (fun nu => κ + N • nu), ?_, ?_, ?_⟩
  · intro mu hmu v
    obtain ⟨nu, -, rfl⟩ := Finset.mem_image.1 hmu
    exact ⟨nu v, rfl⟩
  · intro mu hmu hn
    choose nu hnu using hmu
    have e1 : mu = κ + N • nu := funext hnu
    by_contra hlt
    refine hn (Finset.mem_image.2 ⟨nu, Finset.mem_union_right _ ?_, e1.symm⟩)
    rw [Set.Finite.mem_toFinset]
    exact ⟨trivial, by show ∑ i, qW W (Φ.δ y i) (κ + N • nu) < _; rw [← e1]; omega⟩
  · have h := Submodule.smul_mono le_rfl (le_top : N' ≤ ⊤) (hS₀ (S₀ ∪ hF.toFinset) Finset.subset_union_left)
    rw [smul_eq_mul, Ideal.mul_top, ← Finset.mul_sum] at h

    rw [Finset.sum_image hinj.injOn, map_sum]
    have h' := Ideal.mul_mem_left _ ((e⁻¹ : V'ˣ) : V') h
    rwa [mul_sub, Units.inv_mul_cancel_left] at h'

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibre_value_eq_unit_mul_leadingFourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left) (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' → GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' → IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  first | exact @GlobalTheory.Mum.RedVal.closedFibre_val | exact GlobalTheory.Mum.RedVal.closedFibre_val | (intros; apply GlobalTheory.Mum.RedVal.closedFibre_val <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torusExtensionPoint_of_thickening_eq_transport : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → ∀ (Z : Scheme.{0}) (g : Z ⟶ (thickObj R' I e G').left), ∃ ξ' : GtPt E.toPre (Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)), GlobalTheory.TorusCoord.IsPointOf (U.gt e) g ξ' ∧ IsPullPt hE (𝟙 Z) (Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl)) ξ' := by
  first | exact @GlobalTheory.Mum.isPullPt_of_carries | exact GlobalTheory.Mum.isPullPt_of_carries | (intros; apply GlobalTheory.Mum.isPullPt_of_carries <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.value_unitSection_smul_genericFibre_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (s : SecK C.P.L.L C.α k), ∃ x y : R, y ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a : W) (σ : SecK C.P.L.L T.β k), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval s p' z J) → ∀ J, Good C.P.L.L (cpt W) J → stalkOf (cpt W) (T.φ y) * sval σ (unitW T.G) (cpt W) J = stalkOf (cpt W) (a * T.φ x) * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  first | exact @GlobalTheory.Mum.UnitGen.value_unit_generic | exact GlobalTheory.Mum.UnitGen.value_unit_generic | (intros; apply GlobalTheory.Mum.UnitGen.value_unit_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.carries_unitSection_rigidification_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W) (σ' : H0 T.U.LG.L k) (σ : SecK C.P.L.L T.β k), T.Carries u σ' σ → ∃ ε : Wˣ, ∀ J J', Good C.P.L.L (cpt W) J → Good T.U.LG.L (cpt W) J' → sval σ (unitW T.G) (cpt W) J * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k = stalkOf (cpt W) (u * ε) * sval σ' (unitW T.G) (cpt W) J' * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  first | exact @GlobalTheory.Mum.Trait.carries_unit | exact GlobalTheory.Mum.Trait.carries_unit | (intros; apply GlobalTheory.Mum.Trait.carries_unit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.rigidifiedValueAtOrigin_mem_idealPow_of_vanishes : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α) (v : R) (e : ℕ), OrigVal D b v → VanMod I b e → v ∈ I ^ (e + 1) := by
  first | exact @GlobalTheory.Mum.origVal_mem_of_vanMod | exact GlobalTheory.Mum.origVal_mem_of_vanMod | (intros; apply GlobalTheory.Mum.origVal_mem_of_vanMod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.rigidifiedValueAtOrigin_pullback_degeneration : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (k : ℕ) (x : D'.X) (b : D.SecB k (hD.xe x)) (b' : D'.SecB k x) (v : R), PullB hD x b b' → OrigVal D b v → OrigVal D' b' (φ v) := by
  first | exact @GlobalTheory.Mum.OrigValPull.origVal_pull | exact GlobalTheory.Mum.OrigValPull.origVal_pull | (intros; apply GlobalTheory.Mum.OrigValPull.origVal_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_torsionLabels_genericFibre_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∃ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ p', QkToAkU T.U.toUnifPre F (C.n ^ j) p' (lab' p')) ∧ ∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α := by
  first | exact @GlobalTheory.Mum.Trait.exists_lab_pull | exact GlobalTheory.Mum.Trait.exists_lab_pull | (intros; apply GlobalTheory.Mum.Trait.exists_lab_pull <;> assumption)
end
