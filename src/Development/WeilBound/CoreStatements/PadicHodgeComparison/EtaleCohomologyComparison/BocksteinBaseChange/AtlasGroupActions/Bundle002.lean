module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.AtlasOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.TowerSmulZero
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueB'

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

theorem f_act (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (σ : K.fixingSubgroup) (x : ((dat Amp).H a).N j) :
    bβ Amp hC a j (((dat Amp).H a).act j σ x) = ((dat Amp).A a).act j σ (bβ Amp hC a j x) := by
  let g := IntermediateField.fixingSubgroupEquiv K σ
  refine Subtype.ext (funext fun n => ?_)
  exact hC.gal (B.schFn M.p) (okToOC l K) g (galOC_okToOC g) false n j
    ((show (M.HS false j).lim from x).1 n)

theorem f_act' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (σ : K.fixingSubgroup) (x : ((dat Amp).H' a).N j) :
    bβ' Amp hC a j (((dat Amp).H' a).act j σ x) = ((dat Amp).A a).act j σ (bβ' Amp hC a j x) := by
  let g := IntermediateField.fixingSubgroupEquiv K σ
  refine Subtype.ext (funext fun n => ?_)
  exact hC.gal (B.schFn M.p) (okToOC l K) g (galOC_okToOC g) true n j
    ((show (M.HS true j).lim from x).1 n)

theorem f_phi' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (x : ((dat Amp).H' a).N j) :
    bβ' Amp hC a j ((dat Amp).phi' a j x) = (dat Amp).phiA a j (bβ' Amp hC a j x) := by
  refine Subtype.ext (funext fun n => ?_)
  exact hC.phi (B.schFn M.p) (okToOC l K) n j ((show (M.HS true j).lim from x).1 n)

theorem f_nat (hC : B.Compat l) {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M}
    {b : (dat Amp).Ch N} (m : (dat Amp).Mo u hu a b) (j : ℕ) (x : ((dat Amp).H b).N j) :
    bβ Amp hC a j ((dat Amp).pullH m j x) = (dat Amp).pullA m j (bβ Amp hC b j x) := by
  refine Subtype.ext (funext fun n => ?_)
  exact hC.pull (okToOC l K) (B.schMap u hu) false n j ((show (N.HS false j).lim from x).1 n)

theorem f_nat' (hC : B.Compat l) {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M}
    {b : (dat Amp).Ch N} (m : (dat Amp).Mo u hu a b) (j : ℕ) (x : ((dat Amp).H' b).N j) :
    bβ' Amp hC a j (datPull Amp m j x) = (dat Amp).pullA m j (bβ' Amp hC b j x) := by
  refine Subtype.ext (funext fun n => ?_)
  exact hC.pull (okToOC l K) (B.schMap u hu) true n j ((show (N.HS true j).lim from x).1 n)

theorem f_cup (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (x : ((dat Amp).H a).N i)
    (y : ((dat Amp).H a).N j) (z : ((dat Amp).H a).N (i + j)) (hz : ((dat Amp).H a).cup x y z) :
    ((dat Amp).A a).cup (bβ Amp hC a i x) (bβ Amp hC a j y) (bβ Amp hC a (i + j) z) :=
  GlueBL.lim_cup (fun j => βS hC (B.schFn M.p) (okToOC l K) false j)
    (fun n _ _ x y => hC.cup (B.schFn M.p) (okToOC l K) false n rfl x y) x y z hz

theorem f_one (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (x : ((dat Amp).H a).N 0) (hx : ((dat Amp).H a).one x) :
    ((dat Amp).A a).one (bβ Amp hC a 0 x) := by
  intro n
  let F := B.schFn M.p
  let κ := okToOC l K
  exact (congrArg (fun v : M.Hc false n 0 => B.β F κ false n 0 v) (hx n)).trans
    (hC.one F κ false n)

theorem first_chern_compat_glue (hC : B.Compat l) (h1 : B.FirstChernCompatible l) {M : Model l K} (a : (dat Amp).Ch M) (x : ((dat Amp).H a).N 2)
    (hx : (dat Amp).c1H a x) : (dat Amp).c1A a (bβ Amp hC a 2 x) :=
  h1 M.p (okToOC l K) false a.1 _ hx

def bmap (hMain : B.Main l) (hC : B.Compat l) (h1 : B.FirstChernCompatible l) : BMap Model.Sm (dat Amp) where
  β a j := bβ Amp hC a j
  β' a j := bβ' Amp hC a j
  act a _ j σ x := f_act Amp hC a j σ x
  nat m _ _ j x := f_nat Amp hC m j x
  cup a _ _ _ x y z hz := f_cup Amp hC a x y z hz
  one a _ x hx := f_one Amp hC a x hx
  c1 a _ x hx := first_chern_compat_glue Amp hC h1 a x hx
  inj a hM j := f_inj Amp hMain hC a hM j
  surj a hM j := f_surj Amp hMain hC a hM j
  act' a _ j σ x := f_act' Amp hC a j σ x
  phi' a _ j x := f_phi' Amp hC a j x
  surj' a hM j := f_surj' Amp hMain hC a hM j

def bphi (hMain : B.Main l) (hC : B.Compat l) (h1 : B.FirstChernCompatible l) : BPhi (bmap Amp hMain hC h1) where
  pull m j := datPull Amp m j
  nat m _ _ j x := f_nat' Amp hC m j x
  inj a hM j := f_inj' Amp hMain hC a hM j

end GlueB'

theorem glueB : GlueB := fun _ _ _ Amp hMain hC h1 =>
  ⟨GlueB'.bmap Amp hMain hC h1, GlueB'.bphi Amp hMain hC h1, rfl⟩

end CrystallineSemistableComparison
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueE

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem kill_acr (P : PAlg l ⥤ Type) (n : ℕ) (T : El P) (x : (CH.modF (AcrEl P n)).obj T) :
    ((l : Acris l) ^ n) • x = 0 :=
  modF_smul (AcrEl P n) _ (fun T => show algebraMap (Acris l) (((elπ P).obj T).Acr n) ((l : Acris l) ^ n) = 0 by
    rw [map_pow, map_natCast]; exact ((elπ P).obj T).pow_l_acr n) T x

theorem kill_MS (P : PAlg l ⥤ Type) (n j : ℕ) (x : (MSys P j).M n) : ((l : Acris l) ^ n) • x = 0 :=
  tower_smul_zero (fun n => CH.modF (AcrEl P n)) (fun n => redEl P n.le_succ) j n _ (fun T y => kill_acr P n T y) x

variable (e : E.EtFam l K) (he : e.Red)

def eMap (M : Model l K) (j : ℕ) : M.T j →+ (M.MS j).lim where
  toFun v := ⟨fun n => e M n j (v.lev n), fun n => (he M n j _).trans (congrArg (e M n j) (v.2 n))⟩
  map_zero' := Subtype.ext (funext fun n => map_zero (e M n j))
  map_add' v w := Subtype.ext (funext fun n => map_add (e M n j) (v.lev n) (w.lev n))

theorem eMap_lin_lev (M : Model l K) (j : ℕ) (f : ℤ_[l] →+* Acris l) (z : ℤ_[l]) (v : M.T j) (n : ℕ) :
    (eMap e he M j (z • v)).1 n = f z • (eMap e he M j v).1 n :=
  ((congrArg (e M n j) (GlobalTheory.EtC.HtL.smul_eq l n n le_rfl M.spc j 0 z (v.1 n))).trans
    (map_nsmul (e M n j) _ _)).trans (padic_smul f n ((eMap e he M j v).1 n) (kill_MS M.P n j _) z).symm

theorem eMap_lin (M : Model l K) (j : ℕ) (f : ℤ_[l] →+* Acris l) (z : ℤ_[l]) (v : M.T j) :
    eMap e he M j (z • v) = f z • eMap e he M j v :=
  lim_ext fun n => (eMap_lin_lev e he M j f z v n).trans (lim_smul_val _ _ _ n).symm

theorem eMap_act (hq : e.Equi) (M : Model l K) (j : ℕ) (σ : Gal(PadicAlgCl l/K)) (v : M.T j) :
    eMap e he M j (GlobalTheory.EtC.galHl l (PadicAlgCl l) M.q j 0 σ v) = (M.galS j σ).lim (eMap e he M j v) :=
  lim_ext fun n => hq M n j σ (v.lev n)

theorem eMap_phi (hp : e.Phi) (M : Model l K) (j : ℕ) (v : M.T j) :
    (M.phiS j).lim (eMap e he M j v) = eMap e he M j v :=
  lim_ext fun n => hp M n j (v.lev n)

theorem eMap_nat (hn : e.Natu) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (j : ℕ) (v : N.T j) :
    eMap e he M j (Model.pullT u hu j v) = (Model.pullS u hu j).lim (eMap e he N j v) :=
  lim_ext fun n => hn M N u hu n j (v.lev n)

theorem eMap_cup (hc : e.Cup) (M : Model l K) {i j : ℕ} (x : M.T i) (y : M.T j) (z : M.T (i + j)) (h : M.CupT x y z)
    (n : ℕ) : (eMap e he M (i + j) z).1 n = (CH.mulP (AcrEl M.P n)).cup rfl ((eMap e he M i x).1 n) ((eMap e he M j y).1 n) :=
  (congrArg (e M n (i + j)) (h n)).trans (hc M n i j (x.lev n) (y.lev n))

theorem eMap_one (ho : e.One) (M : Model l K) : ∃ v : M.T 0, ∀ n, (eMap e he M 0 v).1 n = CH.oneH (AcrEl M.P n) :=
  (ho M).elim fun v hv => ⟨v, hv⟩

theorem etale_map_first_chern (h1 : e.C1) (M : Model l K) (D : E.LineData M.X) (c : Acris l)
    (hc : c = ACris.periodT (untilt_epsilon (p := l))) :
    ∃ v : M.T 2, E.IsFirstChernClassOfLineBundle M.p (okToOC l K) D (c • eMap e he M 2 v).1 := by
  subst hc
  exact (h1 M D).elim fun v hv => ⟨v, by rw [lim_smul_fun]; exact hv⟩

def emap (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (e : E.EtFam l K) (he : e.Good) : EMap Model.Sm (dat Amp) where
  e {M} _ j := eMap e he.red M j
  lin {M} _ _ j z v := eMap_lin e he.red M j (per l K).z z v
  act {M} _ _ j _ v := eMap_act e he.red he.equi M j _ v
  phi {M} _ _ j v := eMap_phi e he.red he.phi M j v
  nat {_ _ u hu _ _} _ _ _ j v := eMap_nat e he.red he.nat u hu j v
  cup {M} _ _ _ _ x y z h := eMap_cup e he.red he.cup M x y z h
  one {M} _ _ := eMap_one e he.red he.one M
  c1 {M} a _ := etale_map_first_chern e he.red he.c1 M a.1 (per l K).t rfl

end GlueE

theorem glueE : GlueE := fun _ _ _ Amp hE => hE.elim fun e he => ⟨GlueE.emap Amp e he⟩

end CrystallineSemistableComparison
end
end
