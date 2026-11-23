module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.IsCyclotomicExtensionFourSlopeModelField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle433
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.StdFrames
open scoped TensorProduct

namespace GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

def edgeOf : Arrow T → GlobalTheory.SplitFlip.Edge
  | .right i j => .ex i j
  | .down _ i j => .theta i j
  | _ => .ex 0 0

def IsGridArrow (m : ℕ) (t : T) (a : Arrow T) : Prop :=
  (∃ i j, i < m ∧ j ≤ m ∧ a = .right i j) ∨ ∃ i j, i ≤ m ∧ j < m ∧ a = .down t i j

variable {X Y : Node}

def OnGrid (m : ℕ) (t : T) (p : Path T X Y) : Prop := ∀ a ∈ p.arrows, IsGridArrow m t a

def edges (p : Path T X Y) : List GlobalTheory.SplitFlip.Edge := p.arrows.map edgeOf

section Grid

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def vacOf {W : G.Weil} (ρ : RealMatch W) : ∀ a : Arrow T, Sch G a
  | .right i j => ρ.vX i j
  | .down _ i j => ρ.vT i j
  | _ => 0

def locArg (B : Frames G) (t : T) (w : Pl D.host.E) : ∀ a : Arrow T, WO (G.pS a.pair) (G.pT a.pair) →
    Matrix (Fin ((locGrid G t w).rank (edgeOf a).tgt)) (Fin ((locGrid G t w).rank (edgeOf a).src)) (Kw w)
  | .right i j, x => if h : i < D.R.m ∧ j ≤ D.R.m then
      B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨h.1.le, h.2⟩ ⟨h.1, h.2⟩ (x.map fun c => cpt w (toEAf D c)) else 0
  | .down _ i j, x => if h : i ≤ D.R.m ∧ j < D.R.m then
      B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨h.1, h.2⟩ ⟨h.1, h.2.le⟩ (x.map fun c => cpt w (toEAf D c)) else 0
  | .coreUp _, _ => 0
  | .coreDown _, _ => 0
  | .col _ _, _ => 0

abbrev ArgT (G : GridData L sc) (p : Path T X Y) : Type := p.Fam fun a => WO (G.pS a.pair) (G.pT a.pair)

def castArg {t : T} {w : Pl D.host.E} {e₁ e₂ : GlobalTheory.SplitFlip.Edge} (h : e₁ = e₂)
    (y : Matrix (Fin ((locGrid G t w).rank e₁.tgt)) (Fin ((locGrid G t w).rank e₁.src)) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank e₂.tgt)) (Fin ((locGrid G t w).rank e₂.src)) (Kw w) := h ▸ y

def argAt (B : Frames G) (t : T) (w : Pl D.host.E) (a : Arrow T) (x : WO (G.pS a.pair) (G.pT a.pair)) (e : GlobalTheory.SplitFlip.Edge)
    (d : Matrix (Fin ((locGrid G t w).rank e.tgt)) (Fin ((locGrid G t w).rank e.src)) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank e.tgt)) (Fin ((locGrid G t w).rank e.src)) (Kw w) :=
  if h : edgeOf a = e then castArg h (locArg B t w a x) else d

noncomputable def pathArgs (B : Frames G) (t : T) (w : Pl D.host.E) : ∀ {Y : Node} (p : Path T X Y), ArgT G p → (locGrid G t w).Args
  | _, .nil, _ => 0
  | _, .snoc a p, x => fun e => argAt B t w a x.2 e (pathArgs B t w p x.1 e)

noncomputable def famProd : ∀ {Y : Node} (p : Path T X Y), PureT G p → ArgT G p → ℂ
  | _, .nil, _, _ => 1
  | _, .snoc _ p, d, x => famProd p d.1 x.1 * d.2 x.2

noncomputable def HalfAll (e : AE D) : ∀ {Y : Node} (p : Path T X Y), ArgT G p → Prop
  | _, .nil, _ => True
  | _, .snoc _ p, x => HalfAll e p x.1 ∧ IsHalf e x.2

noncomputable def VecAll {W : G.Weil} (ρ : RealMatch W) (e : AE D) : ∀ {Y : Node} (p : Path T X Y), PureT G p → PureT G p → Prop
  | _, .nil, _, _ => True
  | _, .snoc a p, φ, f => VecAll ρ e p φ.1 f.1 ∧ IsLocVec W a.pair e (vacOf ρ a) φ.2 f.2

def RepFin {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (p : Path T X Y) (τ : TotT G p)
    (Tl : ∀ w, (locGrid G t w).Args → ℂ) : Prop :=
  ∃ e, IsIdemSum e (locPl G t) ∧ ∃ φ : PureT G p → PureT G p, (∀ d ∈ τ.support, VecAll ρ e p (φ d) d) ∧
    ∀ x : ArgT G p, HalfAll e p x → (τ.sum fun d c => c * famProd p (φ d) x) = ∏ w ∈ locPl G t, Tl w (pathArgs B t w p x)


variable (G) in
abbrev PolE : Type := ∀ e : GlobalTheory.SplitFlip.Edge, PolF D (G.V (.grid e.src.1 e.src.2)).rank (G.V (.grid e.tgt.1 e.tgt.2)).rank

def polOf (P : PolE G) : ∀ a : Arrow T, PolF D (G.pT a.pair).rank (G.pS a.pair).rank
  | .right i j => P (.ex i j)
  | .down _ i j => P (.theta i j)
  | .coreUp _ => 0
  | .coreDown _ => 0
  | .col _ _ => 0

noncomputable def restrictPol (P : PolE G) : ∀ {Y : Node} (p : Path T X Y), PolT G p
  | _, .nil => ()
  | _, .snoc a p => (restrictPol P p, polOf P a)

def tensE (W : G.Weil) (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) : TotT G p :=
  tensT W (Q.mapDomain fun P => restrictPol P p) τ

def toOpp (P : PolE G) : GlobalTheory.RowClaim.PolRow G × GlobalTheory.RowClaim.PolDown G :=
  (fun i => P (.ex i D.R.m), fun j => P (.theta D.R.m j))

end Grid

end GlobalTheory.FlipRun

namespace GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.ChiGrid GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem range_snd_rel (ρ : RealMatch W) (i j : ℕ) :
    LinearMap.range ((LinearMap.snd ℂ _ _).comp (ρ.rel i j).subtype) = ⊤ := by
  refine LinearMap.range_eq_top.2 fun b => ?_
  obtain ⟨a, h⟩ := ρ.onto_small i j b
  exact ⟨⟨(a, b), h⟩, rfl⟩

def matchLin (ρ : RealMatch W) (i j : ℕ) : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j) →ₗ[ℂ]
    PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) :=
  (LinearMap.fst ℂ _ _).comp ((ρ.rel i j).subtype.comp
    (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose)

theorem matchLin_mem (ρ : RealMatch W) (i j : ℕ) (b : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) :
    (matchLin ρ i j b, b) ∈ ρ.rel i j := by
  have h := LinearMap.congr_fun (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose_spec b
  set g := (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose
  have e : ((g b : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j))) = (matchLin ρ i j b, b) :=
    Prod.ext rfl h
  exact e ▸ (g b).2

def flipPol (ρ : RealMatch W) (i j : ℕ) (P : PolE G) : PolE G →₀ ℂ :=
  (toTens_surjective (matchLin ρ i j (P (.theta i j) ⊗ₜ P (.ex i j)))).choose.sum fun q c =>
    Finsupp.single (Function.update (Function.update P (.ex i (j + 1)) q.1.2) (.theta (i + 1) j) q.2) c

def flipPolE (ρ : RealMatch W) (i j : ℕ) (Q : PolE G →₀ ℂ) : PolE G →₀ ℂ := Q.sum fun P c => c • flipPol ρ i j P

def flipsPolE (ρ : RealMatch W) (l : List (ℕ × ℕ)) (Q : PolE G →₀ ℂ) : PolE G →₀ ℂ :=
  l.foldl (fun Q x => flipPolE ρ x.1 x.2 Q) Q

def IsCuspListed (θ : InfFam D) (X : Node) (F : Fn G X) : Prop :=
  IsAutFunSm θ (G.V X) F ∧ IsCuspFun (G.V X) F ∧ G.IsListed θ X F

def CuspStep (W : G.Weil) (M : Vol G) (ρ : RealMatch W) (t : T) : Prop :=
  ∀ a : Arrow T, IsGridArrow D.R.m t a → ∀ e, IsIdemSum e (locPl G t) → ∀ φ f, IsLocVec W a.pair e (vacOf ρ a) φ f →
    ∀ (Q : PolF D (G.pT a.pair).rank (G.pS a.pair).rank) (F : Fn G a.src), IsCuspListed W.θ a.src F →
      LiftConv W M a (W.fock a.pair f Q) F ∧ IsCuspListed W.θ a.tgt (liftA W M a (W.fock a.pair f Q) F)

end GlobalTheory.FlipRun
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim.FormulaTwo

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem mem_xiVals {L : LevCh D T} {t : T} {n : ℕ} (hn : (L.xiH t).OrderDvd n) (hL : LocIn D.what₂.embLL (L.xiH t))
    {z : ℂˣ} (hz : z ∈ xiVals L t) : z ^ n = 1 ∧ (z : ℂ) ∈ Set.range D.what₂.embLL := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, x, rfl⟩ := hz
    refine ⟨?_, hL w x⟩
    have : ((L.xiH t) ^ n).loc w x = 1 := by rw [show (L.xiH t) ^ n = 1 from hn]; rfl
    exact this
  | one => exact ⟨one_pow _, 1, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx⟩ := ha.2
    obtain ⟨y, hy⟩ := hb.2
    exact ⟨by rw [mul_pow, ha.1, hb.1, one_mul], x * y, by simp [hx, hy]⟩
  | inv a _ ha =>
    obtain ⟨x, hx⟩ := ha.2
    exact ⟨by rw [inv_pow, ha.1, inv_one], x⁻¹, by simp [hx]⟩

theorem Bplus_smul_form {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (c : ℂ) (φ : Fn G (.top 0))
    (F : Fn G (.grid D.R.m 0)) : Bplus W M φ (c • F) = c * Bplus W M φ F := by
  simpa using Bplus_smul W M 1 c φ F

theorem scalar_calc {e z z' c p b s u κ v w : ℂ} (he : e = z * z') (hz : z ≠ 0) (hz' : z' ≠ 0) (hc : c ≠ 0)
    (h1 : p = (z * c)⁻¹ * b) (h2 : b = z'⁻¹ * s * u) (h3 : u = κ * v) (h4 : w = s * v) : e * c * p = κ * w := by
  subst he h1 h2 h3 h4
  field_simp

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}



theorem formulaAt_steps (hL : R.toLevCh.Is A.μ0) (hC : R.IsChain) (ch : Choice R) (hP : ProjAt ch) (hF : FlipAt ch)
    (hU : UnfoldAt ch) (hJ : JetsAt ch) (hc : ∀ i j t, ch.c i j t ≠ 0) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hK : ch.FieldOK) : ∃ κ ze, FormulaAt ch κ ze := by
  obtain ⟨τi, z, hF⟩ := hF
  obtain ⟨σ, z', hU⟩ := hU τi
  obtain ⟨hM, hJ⟩ := hJ
  obtain ⟨κ, hJ⟩ := hJ σ
  have key : ∀ t, ∃ e : D.what₂.LL, D.what₂.embLL e = (z t : ℂ) * z' t ∧ ∃ n : ℕ, 0 < n ∧ e ^ n = 1 := fun t => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    obtain ⟨h1, e, he⟩ := mem_xiVals ho (hK.chars.xi t) (mul_mem (hF t).1 (hU t).1)
    refine ⟨e, he, n, hn, D.what₂.embLL.injective ?_⟩
    rw [map_pow, he, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  choose ze hze hzn using key
  refine ⟨κ, ze, hzn, fun t x hx a => ?_⟩
  obtain ⟨τ, hτ, hfl⟩ := (hF t).2 (ch.Phi a)
  obtain ⟨M, hMt⟩ := exists_vol ch.G hL t
  choose Mβ hMβ using hM t (ch.Phi a)
  have hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ch.S.IsExpansion t (ch.Phi a) β
      (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) := fun β hβ => Classical.epsilon_spec ((hS t a).ex β hβ)
  have e1 : psiK ch a (R.Th t (R.jX t x)) =
      Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.cv.lift t (R.jX t x))) := by
    exact congrArg (fun u => Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) u))
      ((form_Th ch hC t _).trans (hP t x hx))
  have e2 := (hU t).2 a τ hτ M hMt Mβ (fun β => Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β))
    (fun β hβ => ⟨hMβ β, hex β hβ⟩) (R.jX t x)
  have e3 : (∑ᶠ β ∈ ch.S.supp t (ch.Phi a), (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
      defTot t ch.S.toGridChoice (Mβ β) σ (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) (colFn ch a)
        (formTop ch t (R.jX t x))) = κ * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := by
    rw [(hS t a).vCore_eq _ hex, finsum_mem_eq_finite_toFinset_sum _ (hS t a).fin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hβ' := (Set.Finite.mem_toFinset _).1 hβ
    exact (congrArg (HMul.hMul _) (hJ t a β hβ' (Mβ β) _ (hMβ β) (hex β hβ') (R.jX t x))).trans (mul_left_comm _ _ _)
  have e4 : vK ch t x a = ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := rfl
  have hct : cTot ch t ≠ 0 := (cTot_ne_zero_iff ch t).2 fun i j => hc i j t
  have e5 := congrArg (Bplus ch.W ch.M (colFn ch a)) (hfl M hMt (R.jX t x)).2
  exact scalar_calc (hze t) (z t).ne_zero (z' t).ne_zero hct (e1.trans (e5.trans (Bplus_smul_form _ _ _ _ _))) e2 e3 e4

theorem formula2K (hP : StepProj) (hF : StepFlip) (hU : StepUnfold) (hJ : StepJets) (hc : ConstK) (hS : SumOKK) :
    Formula2K := by
  obtain ⟨C0, H⟩ := ((((hP.and hF).and hU).and hJ).and hc).and hS
  refine ⟨C0, fun ε CF h => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF h
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j hK => ?_⟩
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  exact formulaAt_steps s.core.lev s.core.chain ch a b c d (fun i j t => (f i j t).2) g hK

end GlobalTheory.RowClaim.FormulaTwo

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def formGen (t : T) (y : (R.HX t).H) (η : Module.Dual ℂ R.cX.W) : Fn ch.G (.grid 0 D.R.m) := fun g =>
  η (R.cX.ext ((R.HX t).e y) (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) g))

def genPer (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H) (Q : PolCol ch.G × PolRow ch.G)
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) : ℂ :=
  defPer t ch.S.toGridChoice M Q d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (formGen ch t y η)

end Gen

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Gen2

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def GenConv (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H) (Q : PolCol ch.G × PolRow ch.G)
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) : Prop :=
  PathConv ch.W M (colPath t D.R.m)
      (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j))
      (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) ∧
    PathConv ch.W M (rowPath _ D.R.m D.R.m)
      (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) (formGen ch t y η) ∧
    IntegrableOn (fun h => liftP ch.W M (colPath t D.R.m)
        (colFam t D.R.m fun j => ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j))
          (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (stabilizerEmbedding ch.G.sp.topDec h) *
        liftP ch.W M (rowPath _ D.R.m D.R.m)
          (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) (formGen ch t y η) h)
      (M.fd (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m))

end Gen2

end GlobalTheory.RowReal
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowClaim.TermVolDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem isDefiniteSpace_of_isV {X : LSp D} {ν : ℕ} (h : X.IsV ν 0) : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace X.sp :=
  ⟨h.sigOK, fun τ => Or.inl (by rw [h.sig τ, h.rank, Nat.sub_zero])⟩

theorem isMeasDef_of_isTermVol {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U)
    {μ₀ : T} (hL : L.Is μ₀) (t : T) (Φ : G.Datum) (β : CosFam G t) (M : Vol G) (hM : IsTermVol t S Φ β M) :
    (∀ j (h : j < D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace (G.V (.top j)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel (G.V (.top j)) (S.levTop t Φ β j h) ∧
      IsMeasDef (G.V (.top j)) (S.levTop t Φ β j h) (M.ν (.top j)) (M.fd (.top j))) ∧
    ∀ i (h : i ≤ D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace (G.V (.grid i D.R.m)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel (G.V (.grid i D.R.m)) (S.levRow t i h) ∧
      IsMeasDef (G.V (.grid i D.R.m)) (S.levRow t i h) (M.ν (.grid i D.R.m)) (M.fd (.grid i D.R.m)) := by
  refine ⟨fun j h => ⟨?_, S.isCO_levTop W t Φ β h, ?_⟩, fun i h => ⟨?_, S.isCO_levRow W t h, ?_⟩⟩
  · exact isDefiniteSpace_of_isV (node_isV G hL (X := .top j) h.le)
  · have e := hM.1 j h
    unfold Vol.IsAt at e
    rw [if_pos (by simp [Node.neg])] at e
    exact e
  · have hV := node_isV G hL (X := .grid i D.R.m) ⟨h, le_rfl⟩
    have e : Node.neg D.R.m (.grid i D.R.m) = 0 := by simp [Node.neg]
    rw [e] at hV
    exact isDefiniteSpace_of_isV hV
  · have e := hM.2 i h
    unfold Vol.IsAt at e
    rw [if_pos (by simp [Node.neg])] at e
    exact e

end GlobalTheory.RowClaim.TermVolDef

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

namespace GlobalTheory.ChoiceSurjectivity

theorem choice_phi_surj : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (Φ : ch.G.Datum), ∃ a, ch.Phi a = Φ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F _ ch _ Φ
  obtain ⟨i⟩ := GlobalTheory.TestLat.SlopeModel.nonempty_idx (LaP ch.G)
  refine ⟨ch.e.symm ((Φ, Quotient.mk'' 1), i), ?_⟩
  simp [Choice.Phi, datumOf]

end GlobalTheory.ChoiceSurjectivity
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.MovedField Formalism.L2.Host in

theorem _root_.GlobalTheory.T.movedTensorFactor_mem_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) (S : (locGrid ch.G t w).Args → ℂ), (∀ z, S z ∈ Set.range D.what₂.embLL) → ∀ z, moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) S z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b _ _ _ hF t Φ _ β _ w S hS z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (w : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt w.1 (.inr ⟨t, w.2⟩))

  have hmu : ∀ j (x : (Kw w.1)ˣ), (((locGrid ch.G t w).mu j x : ℂˣ) : ℂ) ∈ K := fun j x => by
    change ((GlobalTheory.FunObj.muBase R.toLevCh j).loc w.1 x : ℂ) *
      ((R.xiH t).loc w.1 x : ℂ) ∈ K
    refine mul_mem ?_ ((hK _).1 (hF.chars.xi t _ x))
    rcases j with _ | j
    · exact one_mem K
    · rw [GlobalTheory.FunObj.muBase]
      split_ifs with hj
      · exact (hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x)
      · exact one_mem K
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).chi i x : ℂˣ) : ℂ) ∈ K :=
    fun i h1 h2 x => (hK _).1 (hF.chars.chi i h1 h2 _ x)
  have heta : ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).eta x : ℂˣ) : ℂ) ∈ K := fun x => by
    have hu := R.toLevCh.C.isEta.unr w.1
    obtain ⟨y, hy⟩ := hF.chars.eta w.1 hu
    exact loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x

  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw w.1)ˣ), (((locGrid ch.G t w).kappa e X x : ℂˣ) : ℂ) ∈ K := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    refine div_mem ?_ (pow_mem (heta x) _)
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw w.1)ˣ) (n : ℕ), apow x ((n : ℂ) / 2) ∈ K ∧ apow x (-(n : ℂ) / 2) ∈ K := fun x n =>
    ⟨by simpa using apow_half_mem hsq x n, by simpa using apow_half_mem hsq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, (locGrid ch.G t w).edgeFactor .one g e ∈ K := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact mul_mem (mul_mem (mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))) (hap _ _).1) (hap _ _).2
  have hchar : ∀ g, ((((charFactor (locGrid ch.G t w) g)⁻¹ : ℂˣ)) : ℂ) ∈ K := by
    intro g
    rw [Units.val_inv_eq_inv_val]
    refine inv_mem (units_prod_mem K _ _ fun e he => ?_)
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    exact mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))
  rw [hK]
  simp only [moved, Grid.pathAct]
  refine mul_mem ?_ (mul_mem (list_prod_mem' K _ _ (hedge _)) ((hK _).1 (hS _)))
  split
  · exact one_mem K
  · exact hchar _
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.branchingPairing_mem_coefficientField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ (U : VV ℂ (wt ch.G (.top D.R.m))) (V : VV ℂ (wt ch.G (.grid D.R.m D.R.m))), (∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range D.what₂.embLL) → (∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range D.what₂.embLL) → brPair (listedWt ch.G (.grid D.R.m D.R.m)) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) U V ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowClaim.brPair_mem_coefField | exact GlobalTheory.RowClaim.brPair_mem_coefField | (intros; apply GlobalTheory.RowClaim.brPair_mem_coefField <;> assumption)
end
