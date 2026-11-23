module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.Base
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.CompId
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle003
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle002
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

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison.HT

open Pb Pb.Kap PAlg

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

theorem crisSurj : CrisSurj l := fun n => ((RL.base_acr (base l) isBase_base).2 n).1

def thP : period_ring_base.Plus l →+* ℂ_[l] where
  toFun x := period_ring_base.th l x.1
  map_one' := by
    have h := th_alg (l := l) 1
    rw [map_one, map_one] at h
    exact h
  map_mul' x y := (period_ring_base.base l).th_mul _ x.2 _ y.2
  map_zero' := by
    have h := th_alg (l := l) 0
    rw [map_zero, map_zero] at h
    exact h
  map_add' x y := (period_ring_base.base l).th_add _ x.2 _ y.2

theorem θD_algCl (x : PadicAlgCl l) : θD l (algClToBdR l x) = clToC l x := thetaAlgHom_algClToBdR l x

theorem br (ht : TFil l) (hs : CrisSurj l) : Br (per l K) (cb K ht hs) (RingHom.id (Acris l)) (thP l)
    (fun σ => ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ))
    (fun σ => galBase (IntermediateField.fixingSubgroupEquiv K σ))
    (fun σ => (period_ring_base.σC σ.1).toRingHom) (fun σ => qC l (period_ring_base.χ σ.1)) := by
  exact {
    et := rfl
    t_ne := DeRhamTwist.Twist.tQ_ne
    θ_i x := ⟨⟨_, ⟨ACris.iota ℂ_[l] l x, rfl⟩⟩, rfl, th_alg _⟩
    θ_o k := ⟨⟨_, ⟨algClToBdR l k.1, rfl⟩⟩, rfl, (th_alg _).trans (θD_algCl l k.1)⟩
    ker x := ((period_ring_base.base l).th_zero x.1 x.2).trans
      ⟨fun ⟨y, hy, e⟩ => ⟨⟨y, hy⟩, e⟩, fun ⟨y, e⟩ => ⟨y.1, y.2, e⟩⟩
    θ_σ g x :=
      ⟨⟨_, (period_ring_base.base l).plus_σ g.1 x.1 x.2⟩, rfl, (period_ring_base.base l).th_σ g.1 x.1 x.2⟩
    galois_t_transform g :=
      ⟨⟨_, ((period_ring_base.base l).th_q (period_ring_base.χ g.1)).1⟩, σD_tQ g.1, th_qQ _⟩
    eσ _ _ := rfl
    cris g n x := galBase_cris _ n x
  }

theorem red_ex {m : ℕ} (L : Lev (per l K) m) (hL : L.Good) (hC : L.CrisOK) (n : ℕ) :
    ∃ d : RedIn (B.DD false (base l) n) (B.κb (okToOC l K) false n) L.γ l n,
      ∀ c, d.ρ ((base l).cris n c) = Ideal.Quotient.mk _ (L.lam c) :=
  redIn_ex L.γ m L.lam (hL.lat m le_rfl).tf hC.1 hC.2 n

theorem lvEx_of (h : ∃ S : LevSys (per l K), S.Good ∧ ∀ m, (S.L m).CrisOK) : LvEx l K := fun ht hs =>
  h.elim fun S hS => (br l K ht hs).sys S hS.1 fun m n => red_ex l K (S.L m) (hS.1.lev m) (hS.2 m) n

end CrystallineSemistableComparison.HT
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.HT

open PAlg H2

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (ht : TFil l) (hs : CrisSurj l)
  {S : ∀ m, Lv (cb K ht hs) (m + 1)} (H : Hyp S)

theorem cY {M : Model l K} {r j : ℕ} {x : Fam M r j} (h : Comp x) : CB.Comp (toY ht hs x) := (toY_comp ht hs x).2 h

theorem toY_pull {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {r j : ℕ} (x : Fam N r j) (n : ℕ) :
    toY ht hs (pullS u hu x) n = (pdOm (c := (cb K ht hs).c n) (c' := (cb K ht hs).c n) (pullM (cb K ht hs) u hu n)
      (RingHom.id (cb K ht hs).Λ) (fun _ => rfl) r).pull j (toY ht hs x n) := rfl

def galY (M : Model l K) (σ : K.fixingSubgroup) (n : ℕ) : GlobalTheory.LogCris.Mor ((cb K ht hs).L M n) ((cb K ht hs).L M n)
    (galBase (IntermediateField.fixingSubgroupEquiv K σ) n) :=
  CrystallineSemistableComparison.SH.galM (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) false n

theorem galY_pt (M : Model l K) (σ : K.fixingSubgroup) (n : ℕ) (B₀ : CommRingCat.{0}) (y : ((cb K ht hs).L M n).Pt.obj B₀) :
    ((galY ht hs M σ n).pt.app B₀ y).1.2 = y.1.2 :=
  CrystallineSemistableComparison.SH.base_snd (B.schFn M.p) (B.gal_κb (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) false n) B₀ y

theorem toY_gal {M : Model l K} (σ : K.fixingSubgroup) {r j : ℕ} (x : Fam M r j) (n : ℕ) :
    toY ht hs (galS σ x) n = (pdOm (c := (cb K ht hs).c n) (c' := (cb K ht hs).c n) (galY ht hs M σ n)
      (ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (galBase_cris _ n) r).pull j (toY ht hs x n) := rfl

include H in
theorem half_galois_of_compatible (hg : ∀ (m : ℕ) (σ : K.fixingSubgroup), Nonempty (LHom (S m) (S m)
    (ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (galBase (IntermediateField.fixingSubgroupEquiv K σ))
    (period_ring_base.σC σ.1).toRingHom (qC l (period_ring_base.χ σ.1)))) :
    Half2 (K := K) ht (fun x => gam S (toY ht hs x)) := by
  exact {
    add hM _ _ x y hx hy a := H.add hM (cY ht hs hx) (cY ht hs hy) (cY ht hs (comp_add hx hy)) a
    lin hM _ _ c x hx a φ := H.lin hM c (cY ht hs hx) (cY ht hs (comp_smul c hx)) a φ
    lin' hM _ _ x hx a k φ := H.lin' hM (cY ht hs hx) a k φ
    sh hM _ _ _ k h x hx a := H.sh hM k h (cY ht hs hx) (cY ht hs (comp_sh ht k h hx)) a
    gal {M} hM r _ σ x hx a φ := H.gal hM (hg r σ).some (galY ht hs M σ) (galY_pt ht hs M σ) (cY ht hs hx) _
      (cY ht hs (comp_gal σ hx)) (fun n => galBase_cris _ n) (toY_gal ht hs σ x) a φ
    nat u hu hM hN _ _ x hx a φ := H.nat hM hN u hu (cY ht hs hx) _ (cY ht hs (comp_pull u hu hx)) (toY_pull ht hs u hu x) a φ
    cup hM _ _ _ _ _ h x y hx hy _ _ b b' c φ := H.cup hM h (cY ht hs hx) (cY ht hs hy) (cY ht hs (comp_cup h hx hy)) b b' c φ
    one {M} hM φ := H.one hM (cY ht hs (comp_one M)) φ
    c1 hM D hD x c hx h1 h2 := H.c1' hM D hD _ c (cY ht hs hx) ((toY_isFirstChern_iff ht hs D x).2 h1) h2
  }

variable (l K) in
theorem half2Of : Half2Of l K := fun ht hs hL h1 h2 h3 h4 h5 h6 h7 _ =>
  (hL ht hs).elim fun S => ⟨_, half_galois_of_compatible ht hs (S := S.L) ⟨h1, h2, h3, h4, h5, h6, h7, fun m => ⟨S.dn m⟩⟩ fun m σ => ⟨S.gal m σ⟩⟩

end CrystallineSemistableComparison.HT
end
end
