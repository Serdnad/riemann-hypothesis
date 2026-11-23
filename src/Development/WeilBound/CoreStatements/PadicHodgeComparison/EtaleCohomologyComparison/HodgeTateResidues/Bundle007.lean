module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.TowerSmulZero
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RedSubVal
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ResMIncl
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.OneTmul
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.TfBaseField
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.SplitField
import GroundTheory.PAdicHodge.NormalizedTraceTower
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg Pb

variable {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))


variable (l) in
def CrisSurj : Prop := ∀ n, Function.Surjective ((base l).cris n)

def cb (ht : TFil l) (hs : CrisSurj l) : CB l K where
  Λ := Acris l
  R n := (base l).Acr n
  I n := B.JJ false (base l) n
  γ n := B.DD false (base l) n
  κ n := B.κb (okToOC l K) false n
  c n := (base l).cris n
  c_surj := hs
  t := tA l
  ht := ht (base l)
  θ := θA l
  rd n := (base l).red n.le_succ
  rd_dp n := B.dd_red false _ n.le_succ
  rd_κ n := B.red_κb _ false n.le_succ
  rd_c n := B.red_cris _ n.le_succ

variable {K} (ht : TFil l) (hs : CrisSurj l) {M : Model l K}

def toY {r j : ℕ} (x : Fam M r j) : (cb K ht hs).Fam M r j := x

theorem toY_comp {r j : ℕ} (x : Fam M r j) : CB.Comp (toY ht hs x) ↔ Comp x := Iff.rfl

theorem toY_isFirstChern_iff (D : E.LineData M.X) (x : Fam M 1 2) : CB.IsFirstChernClassInFamily D (toY ht hs x) ↔ IsFirstChernClassInFamily D x := Iff.rfl

variable (l K)

def LvEx : Prop := ∀ (ht : TFil l) (hs : CrisSurj l), Nonempty (LvSys (cb K ht hs) (Γ := K.fixingSubgroup)
  (fun σ => ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (fun σ => galBase (IntermediateField.fixingSubgroupEquiv K σ))
  (fun σ => (period_ring_base.σC σ.1).toRingHom) fun σ => qC l (period_ring_base.χ σ.1))

def Half2Of : Prop := ∀ ht : TFil l, CrisSurj l → LvEx l K → RhoEx l K → CoEx l K → HomRho l K → HomMu l K → MulRho l K →
  FirstChernHodgeTateCompat l K → KForm → KFin → ∃ γ, Half2 (K := K) ht γ

end CrystallineSemistableComparison.HT
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Mul

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K)

namespace Mul

theorem rS_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (n : ℕ) (x : Y.Fam M r j) :
    (L.rS M r' n).pull j (CB.shS k h x n) = (shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j ((L.rS M r n).pull j (x n)) :=
  redSub_sh M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n) (Y.ht n) L.t_mem k h j (x n)

theorem rS_cup {r r' s i j : ℕ} (h : r + r' = s) (n : ℕ) (x : Y.Fam M r i) (y : Y.Fam M r' j) :
    (L.rS M s n).pull (i + j) (CB.cupS h x y n) =
      (okm (L.QA M) ((l : L.A) ^ n) h).pair.cup rfl ((L.rS M r n).pull i (x n)) ((L.rS M r' n).pull j (y n)) :=
  redSub_cup M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n) h (x n) (y n)

theorem rS_one (n : ℕ) : (L.rS M 0 n).pull 0 (Y.oneS M n) = redG' (L.QA M) ((l : L.A) ^ n) 0 0 (oneG (L.QA M)) :=
  redSub_one M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n)

theorem b_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (z : HG (L.QA M) r j) :
    L.bG M r' j (shG (L.QA M) L.t_mem k h j z) = shG (L.QB M) L.tB_mem k h j (L.bG M r j z) :=
  sq_sh ((L.nmB M).smor _ _ (L.nmB_mem M)) (L.lam Y.t ^ k) (L.tB ^ k) (map_pow _ _ _) _ _ _ _ _ _ _ _ j z

theorem b_cup {r r' s i j : ℕ} (h : r + r' = s) (z : HG (L.QA M) r i) (z' : HG (L.QA M) r' j) :
    L.bG M s (i + j) (cupG (L.QA M) h z z') = cupG (L.QB M) h (L.bG M r i z) (L.bG M r' j z') :=
  sq_cup ((L.nmB M).smor _ _ (L.nmB_mem M)) (grOkQ (L.QA M) h) (grOkQ (L.QB M) h) _ _ _ _ _ _ rfl z z'

theorem b_one : L.bG M 0 0 (oneG (L.QA M)) = L.μ M 0 0 0 (oneH M.q) := by
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)))
  change (1 : (s.obj (Fin.last 0)).obj.B) = (s.obj (Fin.last 0)).obj.i (L.tB ^ (0 - 0)) * 1
  rw [Nat.sub_self, pow_zero, map_one, mul_one]

theorem lifts_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) (e : ℕ) (z : HG (L.QA M) r j) (hz : L.Lifts e z x) :
    L.Lifts e (shG (L.QA M) L.t_mem k h j z) (CB.shS k h x) := fun n =>
  (red_sh (L.QA M) L.t_mem ((l : L.A) ^ n) k h j z).trans
    ((congrArg ((shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j) (hz n)).trans
      ((map_smul ((shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j) _ _).trans
        (congrArg (fun v => (l : L.A) ^ e • v) (rS_sh L M k h n x).symm)))

theorem lifts_cup {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) (e e' : ℕ) (z : HG (L.QA M) r i)
    (z' : HG (L.QA M) r' j) (hz : L.Lifts e z x) (hz' : L.Lifts e' z' y) :
    L.Lifts (e + e') (cupG (L.QA M) h z z') (CB.cupS h x y) := fun n =>
  (red_cup (L.QA M) ((l : L.A) ^ n) h z z').trans
    ((congrArg₂ ((okm (L.QA M) ((l : L.A) ^ n) h).pair.cup rfl) (hz n) (hz' n)).trans
      ((cup_smul _ _ _ _ _ _).trans
        (congrArg₂ (fun (a : L.A) (v : HGm (L.QA M) ((l : L.A) ^ n) s (i + j)) => a • v) (pow_add _ _ _).symm
          (rS_cup L M h n x y).symm)))

theorem rho_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) (w : HG (L.QB M) r j) (hr : L.Rho x w) :
    L.Rho (CB.shS k h x) (shG (L.QB M) L.tB_mem k h j w) :=
  hr.elim fun e he => he.elim fun z hz => ⟨e, shG (L.QA M) L.t_mem k h j z, lifts_sh L M k h x e z hz.1,
    (map_smul (shG (L.QB M) L.tB_mem k h j) _ _).symm.trans
      ((congrArg (shG (L.QB M) L.tB_mem k h j) hz.2).trans (b_sh L M k h z).symm)⟩

theorem cupG_smul {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) {r r' s i j : ℕ} (h : r + r' = s) (c : b.R) (e e' : ℕ)
    (w : HG Q r i) (w' : HG Q r' j) : c ^ (e + e') • cupG Q h w w' = cupG Q h (c ^ e • w) (c ^ e' • w') := by
  rw [pow_add]
  exact (cup_smul _ _ _ _ _ _).symm

theorem rho_cup {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) (w : HG (L.QB M) r i) (w' : HG (L.QB M) r' j)
    (hr : L.Rho x w) (hr' : L.Rho y w') : L.Rho (CB.cupS h x y) (cupG (L.QB M) h w w') :=
  hr.elim fun e he => he.elim fun z hz => hr'.elim fun e' he' => he'.elim fun z' hz' =>
    ⟨e + e', cupG (L.QA M) h z z', lifts_cup L M h x y e e' z z' hz.1 hz'.1,
      (cupG_smul (L.QB M) h (l : L.B) e e' w w').trans ((congrArg₂ (cupG (L.QB M) h) hz.2 hz'.2).trans (b_cup L M h z z').symm)⟩

theorem pow_zero_smul {R : Type} [CommRing R] {V : Type 1} [AddCommGroup V] [Module R V] (c : R) (v : V) : c ^ 0 • v = v := by
  rw [pow_zero, one_smul]

theorem rho_one : L.Rho (Y.oneS M) (L.μ M 0 0 0 (oneH M.q)) :=
  ⟨0, oneG (L.QA M), fun n => (rS_one L M n).symm.trans (pow_zero_smul _ _).symm, (pow_zero_smul _ _).trans (b_one L M).symm⟩

section Rat
variable {K B : Type} [CommRing K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of K)) (Q : ObjectProperty (Thick (nlFun γ 0 X q (κA K I)))) {t : B} (ht : t ∈ I)

theorem mu_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (a : ℕ) (ha : a ≤ r) (y : Hdg q a j) :
    shG Q ht k h j (muG γ q Q ht a r j y) = muG γ q Q ht a r' j y :=
  sqC_sh (kS γ q Q) (t ^ (r - a)) (t ^ k) (t ^ (r' - a)) (by rw [← pow_add]; congr 1; omega) _ _ _ _ _ _ j y

theorem mu_cup {r r' s i j a a' c : ℕ} (h : r + r' = s) (ha : a + a' = c) (h1 : a ≤ r) (h2 : a' ≤ r') (y : Hdg q a i) (y' : Hdg q a' j) :
    cupG Q h (muG γ q Q ht a r i y) (muG γ q Q ht a' r' j y') = muG γ q Q ht c s (i + j) (cupH q ha rfl y y') :=
  (sqC_cup (kS γ q Q) (grOk (smFun X q) ha) (grOkQ Q h) (t ^ (r - a)) (t ^ (r' - a')) (t ^ (s - c))
    (by rw [← pow_add]; congr 1; omega) _ _ _ _ _ _ rfl y y').symm

end Rat

end Mul

variable (l K) in
theorem mulRho : MulRho l K :=
  ⟨fun {_ _} L M {_ _ _} k h x w hr => rho_sh L M k h x w hr,
   fun {_ _} L M {_ _ _} k h a ha y => mu_sh L.γB M.q (L.QB M) L.tB_mem k h a ha y,
   fun {_ _} L M {_ _ _ _ _} h x y w w' hr hr' => rho_cup L M h x y w w' hr hr',
   fun {_ _} L M {_ _ _ _ _ _ _ _} h ha h1 h2 y y' =>
     mu_cup L.γB M.q (L.QB M) L.tB_mem h ha h1 h2 y y',
   fun {_ _} L M => rho_one L M⟩

end CrystallineSemistableComparison.HT
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers TensorProduct

namespace CrystallineSemistableComparison.HT

open Pb

namespace CoB

theorem sub_H {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    (h : ∀ T, Subsingleton (F.obj T)) (j : ℕ) : Subsingleton (CH.H F j) := by
  have : Subsingleton (CH.Cn F j) := ⟨fun _ _ => funext fun _ => (h _).elim _ _⟩
  exact Submodule.Quotient.mk_surjective _ |>.subsingleton

theorem hq_zero {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (ρ ρ' : ℤ) (h : ρ' ≤ 0) (j : ℕ) : Subsingleton (HQ Q ρ ρ' j) := by
  refine sub_H _ (fun T => ⟨fun x y => ?_⟩) j
  obtain ⟨x, hx, rfl⟩ := sq_surj _ _ x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
  refine (sq_eq _ _ _ _).2 ?_
  change _ ∈ T.obj.pdPow ρ'.toNat
  rw [Int.toNat_eq_zero.2 h, T.obj.pdPow_zero]; trivial

variable {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of K))

theorem mu_zero (Q : ObjectProperty (Thick (nlFun γ 0 X q (κA K I)))) {t : B} (ht : t ∈ I) {a r : ℕ} (h : r < a) (j : ℕ)
    (y : Hdg q a j) : muG γ q Q ht a r j y = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine (congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => ?_))).trans (Submodule.Quotient.mk_zero _)
  obtain ⟨x, hx, e⟩ := sq_surj _ _ (z.1 (s ⋙ (kS γ q Q).G))
  refine Subtype.ext ?_
  change (kS γ q Q).qC (t ^ (r - a)) (b := thFil _ ((a : ℤ) + 1)) (b' := sFil Q ((r : ℤ) + 1))
    (fun T _ hx => fil_mul_le (b := nlBase B I γ 0) ht (r := a + 1) (r' := r + 1) (by omega) T.obj hx) _
    (show sqM _ _ _ from z.1 (s ⋙ (kS γ q Q).G)).1 = 0
  rw [← e]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (fil_mul_le (b := nlBase B I γ 0) ht (r := a) (r' := r + 1) (by omega) _ hx)

theorem diff_mem {B T : Type} [CommRing B] [CommRing T] {I : Ideal B} {γ : DividedPowers I} {J : Ideal T} (δ : DividedPowers J)
    (i : B →+* T) (hi : IsDPMorphism γ δ i) {a r : ℕ} (har : a ≤ r) {c b t : B} (hc : c - b * t ^ (r - a) ∈ pdP γ (r - a + 1))
    (x : T) (hx : x ∈ pdP δ a) : i c * x - i b * (i (t ^ (r - a)) * x) ∈ pdP δ (r + 1) := by
  have h1 := dividedPowerFiltration_mul δ _ _ (dividedPowerFiltration_map hi _ hc) hx
  rw [show r - a + 1 + a = r + 1 by omega] at h1
  convert h1 using 1
  rw [map_sub, map_mul]; ring

theorem sqC_res (s : ℕ) {t : B} (ht : t ∈ I) {a r : ℕ} (har : a ≤ r) (j : ℕ) (c b : B) (hc : c - b * t ^ (r - a) ∈ pdP γ (r - a + 1))
    (ha : (smO γ q 1 s {⊤}).LeC c (sFil _ (a : ℤ)) (sFil _ (r : ℤ)))
    (hb : (smO γ q 1 s {⊤}).LeC c (sFil _ ((a : ℤ) + 1)) (sFil _ ((r : ℤ) + 1))) (y : Hdg q a j) :
    ((smO γ q 1 s {⊤}).sqC c ha hb).pull j (resH q (TO q 1 s {⊤}) a j y) = b • muG γ q (TS γ q 1 s {⊤}) ht a r j y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine (congrArg Submodule.Quotient.mk (Subtype.ext (funext fun σ => ?_))).trans (Submodule.Quotient.mk_smul _ _ _)
  obtain ⟨x, hx, e⟩ := sq_surj _ _ (z.1 (σ ⋙ (kS γ q (TS γ q 1 s {⊤})).G))
  refine Subtype.ext ?_
  change (smO γ q 1 s {⊤}).qC c hb _ (show sqM _ _ _ from z.1 (σ ⋙ (kS γ q (TS γ q 1 s {⊤})).G)).1 =
    b • (kS γ q (TS γ q 1 s {⊤})).qC (t ^ (r - a)) (b := thFil _ ((a : ℤ) + 1)) (b' := sFil _ ((r : ℤ) + 1))
    (fun T _ hx => fil_mul_le (b := nlBase B I γ 0) ht (r := a + 1) (r' := r + 1) (by omega) T.obj hx) _
    (show sqM _ _ _ from z.1 (σ ⋙ (kS γ q (TS γ q 1 s {⊤})).G)).1
  rw [← e]
  exact Ideal.Quotient.eq.2 (diff_mem (σ.obj (Fin.last j)).obj.δ (σ.obj (Fin.last j)).obj.i (σ.obj (Fin.last j)).obj.compat har hc x hx)

theorem e_ex (s : ℕ) {t : B} (ht : t ∈ I) {a r : ℕ} (har : a ≤ r) (has : a < s) (j : ℕ) (ρ ρ' : ℤ) (h : ρ = a) (h' : ρ' = (a : ℤ) + 1) :
    ∃ e : Hdg q a j ≃ₗ[K] HQ (TO q 1 s {⊤}) ρ ρ' j, ∀ (c b : B), c - b * t ^ (r - a) ∈ pdP γ (r - a + 1) →
      ∀ (ha : (smO γ q 1 s {⊤}).LeC c (sFil _ ρ) (sFil _ (r : ℤ))) (hb : (smO γ q 1 s {⊤}).LeC c (sFil _ ρ') (sFil _ ((r : ℤ) + 1)))
        (y : Hdg q a j), ((smO γ q 1 s {⊤}).sqC c ha hb).pull j (e y) = b • muG γ q (TS γ q 1 s {⊤}) ht a r j y := by
  subst h h'
  exact ⟨LinearEquiv.ofBijective _ (hdg_res q s {⊤} (by simp) a has j), fun c b hc ha hb y => sqC_res γ q s ht har j c b hc ha hb y⟩

variable {E : Type} [CommRing E] (θ : B →+* E)

theorem main [CharZero K] (U : Cov q) {t : B} (ht : t ∈ I) (m : ℕ) (hker : RingHom.ker θ = I) (hp : ∀ r, pdP γ r = Ideal.span {t ^ r})
    (hnil : t ^ m = 0) (hgr : ∀ i < m, ∀ x : B, x * t ^ i ∈ Ideal.span {t ^ (i + 1)} → x ∈ I) (r j : ℕ) (hr : r < m) :
    Spans γ q (TS γ q 1 m {⊤}) ht r j ∧ ∃ co, IsCo γ q (TS γ q 1 m {⊤}) θ ht r j co := by
  have hm : pdP γ m = ⊥ := by rw [hp, hnil]; simp
  obtain ⟨S⟩ := split_field (K := K) γ m hm
  have hB : TFBase γ 1 m := ⟨hm, fun r x hx => by simpa using hx, fun n hn => ⟨0, algebraMap K B (n : K)⁻¹, by
    rw [pow_zero, ← map_natCast (algebraMap K B), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn), map_one]⟩⟩
  have ha := fun (i : Fin m) n => leC_shift γ q 1 m {⊤} i (S.ν i n) (S.mem i n) (r : ℤ)
  have hb := fun (i : Fin m) n => leC_shift γ q 1 m {⊤} i (S.ν i n) (S.mem i n) ((r : ℤ) + 1)
  have hT := bcOn_false γ 1 m m (tfBase_field K (by omega)) hB S q {⊤} (Or.inr ⟨not_false, ⟨U⟩, by simp⟩) (r : ℤ) ((r : ℤ) + 1)
    (by omega) (by omega) ha hb j
  let R : ∀ i : Fin m, S.N i → B → Prop := fun i n b => S.ν i n - b * t ^ (i : ℕ) ∈ pdP γ (i + 1)
  have h1 : ∀ i n, ∃ b, R i n b := fun i n => by
    have := S.mem i n
    rw [hp] at this
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨b, by simp only [R]; rw [hb, sub_self]; exact zero_mem _⟩
  have h2 : ∀ i b, ∃ n, R i n b := fun i b => by
    obtain ⟨n, hn⟩ := S.surj i (b * t ^ (i : ℕ)) (by rw [hp]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    exact ⟨n, by simpa using neg_mem hn⟩
  have hu : ∀ i n b b', R i n b → R i n b' → θ b = θ b' := fun i n b b' hb hb' => by
    have := sub_mem hb' hb
    rw [hp, show S.ν i n - b' * t ^ (i : ℕ) - (S.ν i n - b * t ^ (i : ℕ)) = (b - b') * t ^ (i : ℕ) by ring] at this
    have h0 := hgr i i.2 _ this
    rw [← hker, RingHom.mem_ker, map_sub] at h0
    exact sub_eq_zero.1 h0
  choose β hβ using h1
  let lam : ∀ i, S.N i →+ E := fun i => AddMonoidHom.mk' (fun n => θ (β i n)) fun n n' => by
    rw [← map_add (f := _)]
    refine hu i _ _ _ (hβ i _) ?_
    have := add_mem (hβ i n) (hβ i n')
    simp only [R, map_add (f := _)]
    convert this using 1; ring
  have h3 : ∀ i n b, R i n b → lam i n = θ b := fun i n b hb => hu i n _ _ (hβ i n) hb
  have hl : ∀ i (k : K) n, lam i (k • n) = θ (algebraMap K B k) * lam i n := fun i k n => by
    rw [h3 i (k • n) (algebraMap K B k * β i n), map_mul]
    · rfl
    · have := Ideal.mul_mem_left _ (algebraMap K B k) (hβ i n)
      simp only [R, map_smul, Algebra.smul_def]
      convert this using 1; ring
  have hE := fun (a : ℕ) (h : a ≤ r) => e_ex γ q m ht h (by omega) j ((r : ℤ) - ((r - a : ℕ) : ℤ)) ((r : ℤ) + 1 - ((r - a : ℕ) : ℤ))
    (by omega) (by omega)
  choose e he using hE
  obtain ⟨ind, co, c1, c2, c3⟩ := CoA.co_abs θ hr S.N (fun i => HQ (TO q 1 m {⊤}) ((r : ℤ) - i) ((r : ℤ) + 1 - i) j)
    (fun a => Hdg q a j) (fun a y => muG γ q (TS γ q 1 m {⊤}) ht a r j y) _ hT R lam hl (fun i n => ⟨_, hβ i n⟩) h2 h3
    (fun i hi => hq_zero _ _ _ (by omega) j) e (fun a h n b y hn => he a h _ b hn _ _ y)
  refine ⟨eq_top_iff.2 fun w _ => ?_, co, ?_, ?_, ?_, ?_, c3⟩
  · exact ind (fun w => w ∈ Submodule.span B {w : HG (TS γ q 1 m {⊤}) r j | ∃ a ≤ r, ∃ y, w = muG γ q (TS γ q 1 m {⊤}) ht a r j y})
      (zero_mem _) (fun _ _ => add_mem) (fun a h b y => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, h, y, rfl⟩)) w
  · intro b w a φ
    refine ind (fun w => co (b • w) a φ = θ b * co w a φ) (by simp) (fun x y hx hy => ?_) (fun a' h b' y => ?_) w
    · simp only [smul_add, map_add (f := _), Pi.add_apply, AddMonoidHom.add_apply, hx, hy, mul_add]
    · beta_reduce
      rw [smul_smul]
      by_cases h0 : a = a'
      · subst h0; rw [c1 a h, c1 a h, map_mul, mul_assoc]
      · rw [c2 a' h a h0, c2 a' h a h0]; simp
  · intro w a k φ
    refine ind (fun w => co w a (k • φ) = θ (algebraMap K B k) * co w a φ) (by simp) (fun x y hx hy => ?_) (fun a' h b' y => ?_) w
    · simp only [map_add (f := _), Pi.add_apply, AddMonoidHom.add_apply, hx, hy, mul_add]
    · beta_reduce
      by_cases h0 : a = a'
      · subst h0; rw [c1 a h, c1 a h, LinearMap.smul_apply, smul_eq_mul, map_mul, map_mul]; ring
      · rw [c2 a' h a h0]; simp
  · intro a h y φ
    have := c1 a h 1 y φ
    rwa [one_smul, map_one, one_mul] at this
  · intro a a' h y
    by_cases h' : a' ≤ r
    · have := c2 a' h' a h 1 y
      rwa [one_smul] at this
    · rw [mu_zero γ q _ ht (not_le.1 h'), map_zero]; rfl

end CoB

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

theorem coEx : CoEx l K := by
  intro Y m L M hM r j hr
  haveI := AdicGeo.proper_p hM.1
  haveI := hM.2
  obtain ⟨U⟩ := (cov_ex M.q).1 inferInstance
  exact CoB.main L.γB M.q L.θ U L.tB_mem m L.ker_θ L.pdB L.nil L.gr r j hr

end CrystallineSemistableComparison.HT
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem lin_add {R : Type} [CommRing R] {A B C : Type 1} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B]
    [Module R C] (f : A →ₗ[R] C) (g : B →ₗ[R] C) {x x' : A} {y y' y'' : B} (h : f x = g y) (h' : f x' = g y') (e : y'' = y + y') :
    f (x + x') = g y'' := by rw [e, map_add (f := _), map_add (f := _), h, h']

theorem lin_smul {R : Type} [CommRing R] {A B C : Type 1} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B]
    [Module R C] (f : A →ₗ[R] C) (g : B →ₗ[R] C) (c : R) {x : A} {y y' : B} (h : f x = g y) (e : y' = c • y) :
    f (c • x) = g y' := by rw [e, map_smul, map_smul, h]

theorem kill_val (A : PAlg l) (n : ℕ) (x : A.Acr n) : A.cris n ((l : Acris l) ^ n) * x = 0 := by
  rw [map_pow, map_natCast, A.pow_l_acr n, zero_mul]

theorem kill_MH (P : PAlg l ⥤ Type) (n j : ℕ) (x : MH P n j) : ((l : Acris l) ^ n) • x = 0 :=
  GlueE.H_smul_eq_zero _ _ (fun T y => kill_val T.1.obj n y) j x

theorem e_smul (e : E.EtFam l K) (M : Model l K) (j n : ℕ) (z : ℤ_[l]) (v : M.T j) :
    e M n j ((z • v).lev n) = zA l z • e M n j (v.lev n) :=
  ((congrArg (e M n j) (GlobalTheory.EtC.HtL.smul_eq l n n le_rfl M.spc j 0 z (v.1 n))).trans (map_nsmul (e M n j) _ _)).trans
    (GlueE.padic_smul (zA l) n _ (kill_MH M.P n j _) z).symm

theorem zA_chi (σ : K.fixingSubgroup) (r : ℕ) :
    zA l ((DeRhamTwist.Twist.chi0 l σ.1 ^ r : ℤ_[l]ˣ) : ℤ_[l]) = χA (IntermediateField.fixingSubgroupEquiv K σ) ^ r := by
  rw [Units.val_pow_eq_pow_val, map_pow]
  rfl

variable (ht : TFil l) {e : E.EtFam l K} (he : EtP e)
include he

theorem h1_lift_add : ∀ {M : Model l K} {r j : ℕ} {v v' : M.T j} {x x' : Fam M r j},
    IsLift ht e r v x → IsLift ht e r v' x' → IsLift ht e r (v + v') (x + x') :=
  fun {M r j v v' x x'} h h' => ⟨comp_add h.1 h'.1, fun n =>
    lin_add ((βMorF (B.schFn M.p) (okToOC l K) r n).pull j) ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (h.2 n) (h'.2 n)
      (map_add (e M n j) (v.lev n) (v'.lev n))⟩

theorem h1_lift_smul : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j} (z : ℤ_[l]),
    IsLift ht e r v x → IsLift ht e r (z • v) (zA l z • x) :=
  fun {M r j v x} z h => ⟨comp_smul _ h.1, fun n =>
    lin_smul ((βMorF (B.schFn M.p) (okToOC l K) r n).pull j) ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (zA l z) (h.2 n)
      (e_smul e M j n z v)⟩

theorem h1_lift_shift : ∀ {M : Model l K} {r r' j : ℕ} {v : M.T j} {x : Fam M r j} (k : ℕ) (h : r + k = r'),
    IsLift ht e r v x → IsLift ht e r' v (shS ht k h x) :=
  fun {M r r' j v x} k h hx => ⟨comp_sh ht k h hx.1, fun n =>
    (β_sh (B.schFn M.p) (okToOC l K) ht k h n j (x n)).trans
      ((congrArg ((shT ht ((B.schFn M.p).pt (okToOC l K)) k h n).pull j) (hx.2 n)).trans (shT_tMor ht _ k h n j _))⟩

theorem h1_lift_galois : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j} (σ : K.fixingSubgroup), IsLift ht e r v x →
    IsLift ht e r (DeRhamTwist.Twist.chi0 l σ.1 ^ r • M.actT j σ v) (galS σ x) := by
  intro M r j v x σ hx
  refine ⟨comp_gal σ hx.1, fun n => ?_⟩
  let τ := IntermediateField.fixingSubgroupEquiv K σ
  let z : ℤ_[l] := ((DeRhamTwist.Twist.chi0 l σ.1 ^ r : ℤ_[l]ˣ) : ℤ_[l])
  have hz : zA l z = χA τ ^ r := zA_chi σ r
  have hequi : e M n j ((M.actT j σ v).lev n) =
      (galMor τ (B.ptTw (B.schFn M.p) (okToOC l K) τ (galOC_okToOC τ)) n).pull j (e M n j (v.lev n)) :=
    he.good.equi M n j τ (v.lev n)
  have hgal := galT_tMor ht τ (B.ptTw (B.schFn M.p) (okToOC l K) τ (galOC_okToOC τ))
    r n j (e M n j (v.lev n))
  change _ = (tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j
    (e M n j ((z • M.actT j σ v).lev n))
  simpa only [galS, hx.2 n, hgal, e_smul e M j n z (M.actT j σ v), hz, hequi, LinearMap.map_smul] using
    β_galF (B.schFn M.p) (okToOC l K) τ (galOC_okToOC τ) r n j (x n)

theorem h1_lift_naturality : ∀ {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {r j : ℕ} {v : N.T j} {x : Fam N r j},
    IsLift ht e r v x → IsLift ht e r (Model.pullT u hu j v) (pullS u hu x) := by
  intro M N u hu r j v x hx
  refine ⟨comp_pull u hu hx.1, fun n => ?_⟩
  have hnat : e M n j ((Model.pullT u hu j v).lev n) =
      (pullMor ((B.schMap u hu).pt (okToOC l K)) n).pull j (e N n j (v.lev n)) :=
    he.good.nat M N u hu n j (v.lev n)
  have hpull := pullT_tMor ht ((B.schMap u hu).pt (okToOC l K)) r n j (e N n j (v.lev n))
  simpa only [pullS, hx.2 n, hpull, hnat] using
    β_pullF (okToOC l K) (B.schMap u hu) r n j (x n)

end CrystallineSemistableComparison.HT
end
end
