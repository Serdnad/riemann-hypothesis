module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PrepairingEtaleValue
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftPOfBounds
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse
import GroundTheory.PAdicHodge.NormalizedTraceTower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct



namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {ht : TFil l}
  {Lf : ∀ {M : Model l K} (r : ℕ) {j : ℕ}, M.T j → Fam M r j → Prop} (h1 : Half1 ht @Lf)
  {γ : ∀ {M : Model l K} {r j : ℕ}, Fam M r j → ∀ a, Module.Dual K (Hdg M.q a j) →+ ℂ_[l]} (h2 : Half2 ht @γ)

include h1 h2 in
theorem indep {M : Model l K} (hM : M.Sm) {j r r' : ℕ} {v : M.T j} {x : Fam M r j} {x' : Fam M r' j} (hx : Lf r v x)
    (hx' : Lf r' v x') (a : ℕ) : γ x a = γ x' a := by
  obtain ⟨k, hk⟩ := h1.uniq M hM j
  have a1 := h1.sh r' (rfl : r + r' = r + r') hx
  have a2 := h1.sh r (Nat.add_comm r' r) hx'
  have e := hk (r + r') v _ _ a1 a2
  rw [← h2.sh hM r' rfl x (h1.comp hx) a, ← h2.sh hM r (Nat.add_comm r' r) x' (h1.comp hx') a,
    ← h2.sh hM k rfl _ (h1.comp a1) a, ← h2.sh hM k rfl _ (h1.comp a2) a, e]

def rr {M : Model l K} (hM : M.Sm) (j : ℕ) : ℕ := (h1.ex M hM j).choose

def xx {M : Model l K} (hM : M.Sm) {j : ℕ} (v : M.T j) : Fam M (rr h1 hM j) j := ((h1.ex M hM j).choose_spec v).choose

theorem xx_spec {M : Model l K} (hM : M.Sm) {j : ℕ} (v : M.T j) : Lf _ v (xx h1 hM v) := ((h1.ex M hM j).choose_spec v).choose_spec


variable (γ) in
def gT {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (v : M.T j) : Module.Dual K (Hdg M.q a j) →+ ℂ_[l] := γ (xx h1 hM v) a

include h2 in
theorem gT_eq {M : Model l K} (hM : M.Sm) (a : ℕ) {j r : ℕ} {v : M.T j} {x : Fam M r j} (hx : Lf r v x) :
    gT h1 (@γ) hM a v = γ x a := indep h1 h2 hM (xx_spec h1 hM v) hx a

include h2 in
theorem gT_add {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (v w : M.T j) :
    gT h1 (@γ) hM a (v + w) = gT h1 (@γ) hM a v + gT h1 (@γ) hM a w :=
  (gT_eq h1 h2 hM a (h1.add (xx_spec h1 hM v) (xx_spec h1 hM w))).trans
    (h2.add hM _ _ (h1.comp (xx_spec h1 hM v)) (h1.comp (xx_spec h1 hM w)) a)

include h2 in
theorem gT_smul {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (z : ℤ_[l]) (v : M.T j) (φ : Module.Dual K (Hdg M.q a j)) :
    gT h1 (@γ) hM a (z • v) φ = qC l (z : ℚ_[l]) * gT h1 (@γ) hM a v φ := by
  rw [gT_eq h1 h2 hM a (h1.smul z (xx_spec h1 hM v)), h2.lin hM _ _ (h1.comp (xx_spec h1 hM v)), θA_zA]
  rfl

include h2 in
theorem gT_act {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (σ : K.fixingSubgroup) (v : M.T j) (φ : Module.Dual K (Hdg M.q a j)) :
    qC l (period_ring_base.χ σ.1) ^ a * gT h1 (@γ) hM a (M.actT j σ v) φ = period_ring_base.σC σ.1 (gT h1 (@γ) hM a v φ) := by
  have e1 := gT_smul h1 h2 hM a ((DeRhamTwist.Twist.chi0 l σ.1 ^ rr h1 hM j : ℤ_[l]ˣ) : ℤ_[l]) (M.actT j σ v) φ
  replace e1 := (DFunLike.congr_fun (gT_eq h1 h2 hM a (h1.gal σ (xx_spec h1 hM v))) φ).symm.trans e1
  rw [Units.val_pow_eq_pow_val, PadicInt.coe_pow, map_pow] at e1
  have e2 := h2.gal hM σ _ (h1.comp (xx_spec h1 hM v)) a φ
  rw [e1] at e2
  have hc : qC l (period_ring_base.χ σ.1) ^ rr h1 hM j ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 (χ_ne _))
  refine mul_left_cancel₀ hc (Eq.trans ?_ e2)
  exact mul_left_comm _ _ _

def hV {M : Model l K} (hM : M.Sm) (a n : ℕ) : M.V n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]) :=
  (TensorProduct.liftAddHom (R := ℤ_[l]) (M := ℚ_[l]) (N := M.T n)
    (AddMonoidHom.mk' (fun z => AddMonoidHom.mk' (fun u =>
      AddMonoidHom.mk' (fun φ => qC l z * gT h1 (@γ) hM a u φ) (by intros; simp [mul_add]))
        (by intros; ext; simp [gT_add h1 h2, mul_add])) (by intros; ext; simp [add_mul]))
    (by
      intro r z u
      ext φ
      simp only [AddMonoidHom.mk'_apply]
      rw [gT_smul h1 h2, Algebra.smul_def, map_mul]
      simp only [PadicInt.algebraMap_apply]
      ring) :
    ℚ_[l] ⊗[ℤ_[l]] M.T n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]))


open Classical in
def hP (M : Model l K) (a n : ℕ) : M.V n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]) :=
  if hM : M.Sm then hV h1 h2 hM a n else 0

theorem hP_tmV {M : Model l K} (hM : M.Sm) (a n : ℕ) (z : ℚ_[l]) (u : M.T n) (φ : Module.Dual K (Hdg M.q a n)) :
    hP h1 h2 M a n (tmV M n z u) φ = qC l z * gT h1 (@γ) hM a u φ := by
  rw [hP, dite_eq_left hM]
  unfold hV tmV
  erw [TensorProduct.liftAddHom_tmul]
  rfl

theorem hP_toV {M : Model l K} (hM : M.Sm) (a : ℕ) {n r : ℕ} {u : M.T n} {x : Fam M r n} (hx : Lf r u x)
    (φ : Module.Dual K (Hdg M.q a n)) : hP h1 h2 M a n (M.toV n u) φ = γ x a φ := by
  rw [toV_eq, hP_tmV h1 h2 hM, map_one, one_mul, gT_eq h1 h2 hM a hx]

theorem hP_not {M : Model l K} (hM : ¬ M.Sm) (a n : ℕ) (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)) :
    hP h1 h2 M a n v φ = 0 := by
  rw [hP, dite_eq_right hM]; rfl

include h1 h2 in
theorem pre_of (hF : KFin) (hC : DlogClassExistsUnique) : Nonempty (HTPre l K) := ⟨{
  h := hP h1 h2
  lin := fun M a n z v φ => by
    by_cases hM : M.Sm
    · refine V_induction (p := fun v => hP h1 h2 M a n (z • v) φ = qC l z * hP h1 h2 M a n v φ) v ?_ ?_ ?_
      · simp only [smul_zero, map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z' u
        simp only [smul_tmV, hP_tmV h1 h2 hM, map_mul, mul_assoc]
      · intro x y hx hy
        simp only [smul_add, map_add (f := _), AddMonoidHom.add_apply, mul_add] at hx hy ⊢
        rw [hx, hy]
    · simp only [hP_not h1 h2 hM, mul_zero]
  lin' := fun M a n k v φ => by
    by_cases hM : M.Sm
    · refine V_induction (p := fun v => hP h1 h2 M a n v (k • φ) = kC K k * hP h1 h2 M a n v φ) v ?_ ?_ ?_
      · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z' u
        simp only [hP_tmV h1 h2 hM, gT]
        rw [h2.lin' hM _ (h1.comp (xx_spec h1 hM u)), mul_left_comm]
      · intro x y hx hy
        simp only [map_add (f := _), AddMonoidHom.add_apply, mul_add] at hx hy ⊢
        rw [hx, hy]
    · simp only [hP_not h1 h2 hM, mul_zero]
  fin := fun M hM a n => by
    have := proper_q hM
    have := smooth_q hM
    exact hF M.q a n
  equi := fun M hM a n σ v φ => by
    refine V_induction (p := fun v => qC l (period_ring_base.χ σ.1) ^ a * hP h1 h2 M a n (M.act n σ v) φ =
      period_ring_base.σC σ.1 (hP h1 h2 M a n v φ)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
    · intro z u
      simp only [act_tmV, hP_tmV h1 h2 hM]
      rw [map_mul, σC_qC, mul_left_comm, gT_act h1 h2 hM]
    · intro x y hx hy
      simp only [map_add (f := _), AddMonoidHom.add_apply, mul_add] at hx hy ⊢
      rw [hx, hy]
  nat := fun M N u hu hM hN a n v φ => by
    refine V_induction (p := fun v => hP h1 h2 M a n (Model.pullV u hu n v) φ =
      hP h1 h2 N a n v (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a n)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply]
    · intro z w
      simp only [pullV_tmV, hP_tmV h1 h2 hM, hP_tmV h1 h2 hN]
      rw [gT_eq h1 h2 hM a (h1.nat u hu (xx_spec h1 hN w)), h2.nat u hu hM hN _ (h1.comp (xx_spec h1 hN w))]
      rfl
    · intro x y hx hy
      simp only [map_add (f := _), AddMonoidHom.add_apply] at hx hy ⊢
      rw [hx, hy]
  cup := fun M hM i j x y z hz m m' b b' c φ => by
    have hx := xx_spec h1 hM x
    have hy := xx_spec h1 hM y
    rw [hP_toV h1 h2 hM c (h1.cup rfl hz hx hy), h2.cup hM rfl _ _ (h1.comp hx) (h1.comp hy) b b' c φ]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [hP_toV h1 h2 hM _ hx, hP_toV h1 h2 hM _ hy]
  one := fun M hM v hv φ => by rw [hP_toV h1 h2 hM 0 (h1.one M v hv), h2.one hM]
  first_chern_class_exists := fun M hM D _ hD => ⟨h1.first_chern_class_exists M D, hC M.q (genD D) (sSup_pb D _ hD)⟩
  c1 := fun M hM D hE hD r v c hv hc => by
    obtain ⟨x, hx, hl⟩ := h1.c1 M D hE hD r v hv
    have := h2.c1 hM D hD x c (h1.comp hl) hx hc
    exact ⟨fun φ => (hP_toV h1 h2 hM 1 hl φ).trans (this.1 φ),
      fun a ha φ => (hP_toV h1 h2 hM a hl φ).trans (by rw [this.2 a ha]; rfl)⟩ }⟩

end CrystallineSemistableComparison.HT
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.HomP

open Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
  {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ} {sn : ∀ n, Y.R n →+* Y.R n}
  {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)

def muEta (T : (L'.QB M).FullSubcategory) :
    (kS L.γB N.q (L.QB N)).G.obj (((h.nmW u hu).smor _ _ (h.nmW_mem u hu)).G.obj T) ⟶
      (smS (Model.genMap u hu) (Model.genMap_q u hu)).G.obj ((kS L'.γB M.q (L'.QB M)).G.obj T) :=
  nlHom (γ := dividedPowersBot K) (κ := Ideal.Quotient.mk ⊥) (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (h.oB r))
    (DPMorphism.id T.obj.δ).isDPMorphism fun e => (spec_id _ e _).trans (by
      change (pt T.obj ≫ Model.genMap u hu) ≫ 𝟙 _ = (pt T.obj ≫ 𝟙 _) ≫ Model.genMap u hu
      rw [Category.comp_id, Category.comp_id])

theorem mu_sq (a r j : ℕ) (y : Hdg N.q a j) :
    h.fW u hu r j (L.μ N a r j y) = h.cB ^ (r - a) • L'.μ M a r j (pullH (Model.genMap u hu) (Model.genMap_q u hu) a j y) :=
  genB (kS L.γB N.q (L.QB N)) ((h.nmW u hu).smor _ _ (h.nmW_mem u hu)) (smS (Model.genMap u hu) (Model.genMap_q u hu))
    (kS L'.γB M.q (L'.QB M)) (L.tB ^ (r - a)) (h.cB ^ (r - a)) (L'.tB ^ (r - a)) (fun k => (h.oB k).symm)
    (by rw [map_pow h.sB, h.t, mul_pow]) ⟨muEta h u hu, fun T T' f => hom_ext rfl⟩ (fun _ _ => rfl) _ _ _ _ _ _ _ _ j y

def nmA : NMor L.γ N.p (κA (OK l K) L.I) L'.γ M.p (κA (OK l K) L'.I) h.sA where
  hI := h.dpA
  u := u
  g := RingHom.id _
  hu := by simpa using hu
  hκ a r e := by
    have h1 := h.dpA.1 (Ideal.mem_map_of_mem h.sA (Ideal.Quotient.eq.1 e))
    rw [map_sub, h.oA] at h1
    exact Ideal.Quotient.eq.2 h1

theorem nmA_mem (T : Thick (nlFun L'.γ 0 M.X M.p (κA (OK l K) L'.I))) (hT : L'.QA M T) : L.QA N (((nmA h u hu).mor 0).obj T) :=
  ⟨⟨le_bot_iff.1 (le_trans (T.pdPow_anti h.le) hT.1.1.le), hT.1.2⟩, ⊤, rfl, le_rfl⟩

def smA : SMor (sP (L.QA N)) (sP (L'.QA M)) h.sA := (nmA h u hu).smor _ _ (nmA_mem h u hu)

def mZ (r : ℕ) : CH.Mor (sq (sFil (L.QA N) r) (sFil (L.QA N) ((r : ℤ) + 1))) (sq (sFil (L'.QA M) r) (sFil (L'.QA M) ((r : ℤ) + 1))) h.sA :=
  (smA h u hu).sq (fun _ _ hx => hx) fun _ _ hx => hx

def mZn (r n : ℕ) : CH.Mor (sq (stdI (L.QA N) (some (r : ℤ)) ((l : L.A) ^ n)) (stdI (L.QA N) (some ((r : ℤ) + 1)) ((l : L.A) ^ n)))
    (sq (stdI (L'.QA M) (some (r : ℤ)) ((l : L'.A) ^ n)) (stdI (L'.QA M) (some ((r : ℤ) + 1)) ((l : L'.A) ^ n))) h.sA :=
  (smA h u hu).sq (std_le (nmA h u hu) (nmA_mem h u hu) _) (std_le (nmA h u hu) (nmA_mem h u hu) _)

theorem red_sq (r n j : ℕ) (z : HG (L.QA N) r j) :
    redG' (L'.QA M) ((l : L'.A) ^ n) r j ((mZ h u hu r).pull j z) = (mZn h u hu r n).pull j (redG' (L.QA N) ((l : L.A) ^ n) r j z) :=
  genC (smA h u hu) _ _ _ _ _ _ _ _ j z

def bEta (T : (L'.QB M).FullSubcategory) :
    (smA h u hu).G.obj (((L'.nmB M).smor _ _ (L'.nmB_mem M)).G.obj T) ⟶
      ((L.nmB N).smor _ _ (L.nmB_mem N)).G.obj (((h.nmW u hu).smor _ _ (h.nmW_mem u hu)).G.obj T) :=
  ObjectProperty.homMk (nlHom (γ := L.γ) (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (h.ι r).symm)
    (DPMorphism.id T.obj.δ).isDPMorphism fun e => (spec_id _ e _).trans (by
      change (pt T.obj ≫ pullback.fst _ _) ≫ u = (pt T.obj ≫ Model.genMap u hu) ≫ pullback.fst _ _
      rw [Category.assoc, Category.assoc, Model.genMap, pullback.lift_fst]))

theorem b_sq (r j : ℕ) (z : HG (L.QA N) r j) :
    L'.bG M r j ((mZ h u hu r).pull j z) = h.fW u hu r j (L.bG N r j z) :=
  genA (smA h u hu) ((L'.nmB M).smor _ _ (L'.nmB_mem M)) ((L.nmB N).smor _ _ (L.nmB_mem N)) ((h.nmW u hu).smor _ _ (h.nmW_mem u hu))
    h.ι ⟨bEta h u hu, fun T T' f => ObjectProperty.hom_ext _ (hom_ext rfl)⟩ (fun _ _ => rfl) _ _ _ _ _ _ _ _ j z

variable {n : ℕ} (mm : GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (sn n))
  (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), (mm.pt.app B₀ y).1.2 = (show Spec B₀ ⟶ M.X from y.1.2) ≫ u)

theorem d_comm (x : Y.R n) (a : L.A) (e : (L.d n).ρ x = Ideal.Quotient.mk _ a) : (L'.d n).ρ (sn n x) = Ideal.Quotient.mk _ (h.sA a) := by
  obtain ⟨b, rfl⟩ := Y.c_surj n x
  rw [L.d_lam] at e
  rw [h.cris, L'.d_lam, ← h.lam]
  exact congrArg (lnMap h.sA l (le_refl n)) e

include hpt in
theorem r_sq (r j : ℕ) (x : CH.H (Y.SS N r n).fn j) :
    (mZn h u hu r n).pull j ((L.rS N r n).pull j x) = (L'.rS M r n).pull j ((pdOm mm sΛ (h.cris n) r).pull j x) :=
  genD (nmA h u hu) (nmA_mem h u hu) (L.d n) (L'.d n) (d_comm h) mm hpt (Y.c n) L.lam L'.lam (L.d_lam n) (L'.d_lam n) sΛ (h.cris n)
    (fun a => (h.lam a).symm) r j x

end CrystallineSemistableComparison.HT.HomP

namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem homMu : HomMu l K := fun h _ _ u hu a r j y => HomP.mu_sq h u hu a r j y

theorem HomP.step {A A' : Type} [CommRing A] [CommRing A'] {s : A →+* A'} {P P' : Type 1} [AddCommGroup P] [Module A P]
    [AddCommGroup P'] [Module A' P'] (f : P →ₛₗ[s] P') (l e : ℕ) {a b : P} {a' b' : P'} (h : a = (l : A) ^ e • b) (ha : a' = f a)
    (hb : f b = b') : a' = (l : A') ^ e • b' := by
  rw [ha, h, LinearMap.map_smulₛₗ, map_pow, map_natCast, hb]

theorem homRho : HomRho l K := fun h _ _ u hu mm hpt r j x w hw => hw.elim fun e he => he.elim fun z hz =>
  ⟨e, (HomP.mZ h u hu r).pull j z,
    fun n => HomP.step ((HomP.mZn h u hu r n).pull j) l e (hz.1 n) (HomP.red_sq h u hu r n j z)
      (HomP.r_sq h u hu (mm n) (hpt n) r j (x n)),
    (HomP.step (h.fW u hu r j) l e hz.2.symm (HomP.b_sq h u hu r j z) rfl).symm⟩

end CrystallineSemistableComparison.HT
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb

namespace RhoA

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem ok_dv (a : OK l K) (ha : a ≠ 0) : ∃ k : ℕ, a ∣ (l : OK l K) ^ k := by
  have ha' : (a : K) ≠ 0 := fun e => ha (Subtype.ext e)
  have h0 : 0 < ‖((a : K) : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast ha')
  have e : (((l : ℕ) : K) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  have h1 : ‖(((l : ℕ) : K) : PadicAlgCl l)‖ < 1 := by
    rw [e, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one h0 h1
  refine ⟨k, ⟨(a : K)⁻¹ * (l : K) ^ k, (mem_OK _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [IntermediateField.coe_mul, IntermediateField.coe_inv, IntermediateField.coe_pow, norm_mul, norm_inv, norm_pow]
    rw [inv_mul_le_iff₀ h0, mul_one]
    exact hk.le
  · change (((l : OK l K) ^ k : OK l K) : K) = (a : K) * ((a : K)⁻¹ * (l : K) ^ k)
    rw [mul_inv_cancel_left₀ ha']
    simp

theorem tf_dom {O : Type} [CommRing O] [IsDomain O] [CharZero O] {l : ℕ} (hl : l ≠ 0)
    (hdv : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot O) l s := by
  have hb : ∀ r, 1 ≤ r → pdP (dividedPowersBot O) r = ⊥ := fun r hr => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
    refine le_bot_iff.1 (le_trans ?_ (GlobalTheory.CompanionTheory.LiftLat.dividedPowerFiltration_one_eq (dividedPowersBot O)).le)
    refine Ideal.span_mono ?_
    rintro _ ⟨L, h1, h2, rfl⟩
    exact ⟨L, h1, by omega, rfl⟩
  refine ⟨hb s hs, fun r x hx => ?_, fun n hn => ?_⟩
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · have : (1 : O) ∈ pdP (dividedPowersBot O) 0 := Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
      simpa using Ideal.mul_mem_left _ x this
    · rw [hb r hr, Ideal.mem_bot] at hx ⊢
      exact (mul_eq_zero.1 hx).resolve_left (Nat.cast_ne_zero.2 hl)
  · obtain ⟨k, u, hu⟩ := hdv n (Nat.cast_ne_zero.2 hn)
    exact ⟨k, u, hu.symm⟩

section Abs
variable {A B Λ : Type} [CommRing A] [CommRing B] [CommRing Λ] {ι : A →+* B} {Z W : Type 1} [AddCommGroup Z] [Module A Z]
  [AddCommGroup W] [Module B W] (b : Z →ₛₗ[ι] W) {Zn : ℕ → Type 1} [∀ n, AddCommGroup (Zn n)] [∀ n, Module A (Zn n)]
  (red : ∀ n, Z →ₗ[A] Zn n) (l : ℕ)

theorem b_pow (e : ℕ) (z : Z) : b ((l : A) ^ e • z) = (l : B) ^ e • b z := by
  rw [LinearMap.map_smulₛₗ, map_pow, map_natCast]

theorem exu (hu : IsUnit (l : B)) (x : ∀ n, Zn n) (e₀ : ℕ) (z₀ : Z) (h₀ : ∀ n, red n z₀ = (l : A) ^ e₀ • x n) (k : ℕ)
    (hs : ∀ z, (∀ n, red n z = 0) → (l : A) ^ k • z = 0) :
    ∃! w : W, ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z := by
  have key : ∀ (w w' : W) e z e' z', (∀ n, red n z = (l : A) ^ e • x n) → (l : B) ^ e • w = b z →
      (∀ n, red n z' = (l : A) ^ e' • x n) → (l : B) ^ e' • w' = b z' → w = w' := by
    intro w w' e z e' z' h1 h2 h3 h4
    have h5 := hs ((l : A) ^ e' • z - (l : A) ^ e • z') fun n => by
      rw [map_sub, map_smul, map_smul, h1, h3, smul_comm, sub_self]
    have h6 := congrArg b h5
    rw [b_pow, map_sub, b_pow, b_pow, ← h2, ← h4, map_zero, smul_comm ((l : B) ^ e) ((l : B) ^ e') w', ← smul_sub, ← smul_sub,
      smul_smul, smul_smul] at h6
    exact sub_eq_zero.1 (((((hu.pow k).mul (hu.pow e')).mul (hu.pow e)).smul_eq_zero).1 h6)
  obtain ⟨u, hu'⟩ := (hu.pow e₀).exists_right_inv
  have hw : (l : B) ^ e₀ • (u • b z₀) = b z₀ := by rw [smul_smul, hu', one_smul]
  exact ⟨u • b z₀, ⟨e₀, z₀, h₀, hw⟩, fun w ⟨e, z, h1, h2⟩ => key _ _ _ _ _ _ h1 h2 h₀ hw⟩

theorem add_abs (x y : ∀ n, Zn n) (w w' : W) (h : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z)
    (h' : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • y n) ∧ (l : B) ^ e • w' = b z) :
    ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • (x n + y n)) ∧ (l : B) ^ e • (w + w') = b z := by
  obtain ⟨e, z, h1, h2⟩ := h
  obtain ⟨e', z', h3, h4⟩ := h'
  refine ⟨e + e', (l : A) ^ e' • z + (l : A) ^ e • z', fun n => ?_, ?_⟩
  · rw [map_add (f := _), map_smul, map_smul, h1, h3, smul_smul, smul_smul, smul_add, pow_add, mul_comm ((l : A) ^ e')]
  · rw [map_add (f := _), b_pow, b_pow, ← h2, ← h4, smul_smul, smul_smul, smul_add, pow_add, mul_comm ((l : B) ^ e')]

theorem smul_abs (x : ∀ n, Zn n) (w : W) (a : A)
    (h : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z) :
    ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • (a • x n)) ∧ (l : B) ^ e • (ι a • w) = b z := by
  obtain ⟨e, z, h1, h2⟩ := h
  refine ⟨e, a • z, fun n => ?_, ?_⟩
  · rw [map_smul, h1, smul_comm]
  · rw [LinearMap.map_smulₛₗ, ← h2, smul_comm]

end Abs

variable {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K)

theorem unit_B : IsUnit (l : L.B) := by
  have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) : IsUnit (l : K)).map (algebraMap K L.B)
  rwa [map_natCast] at this

theorem rS_tr (r j n : ℕ) (x : CH.H (Y.SS M r (n + 1)).fn j) :
    (L.rS M r n).pull j ((pdOm (Y.redM M n) (RingHom.id _) (Y.rd_c n) r).pull j x) =
      trG (L.QA M) (l : L.A) n r j ((L.rS M r (n + 1)).pull j x) :=
  sub_trans (L.d (n + 1)) (L.d n) m {⊤} (Y.redM M n) (Y.c (n + 1)) (Y.c n) L.lam (L.d_lam (n + 1)) (L.d_lam n) (Y.rd_c n)
    (fun _ _ => rfl) (Y.c_surj (n + 1)) r j x

theorem ex [FiniteDimensional ℚ_[l] K] (hM : M.Sm) (r j : ℕ) (hr : r < m) (x : Y.Fam M r j) (hx : CB.Comp x) : ∃! w, L.Rho x w := by
  haveI := AdicGeo.proper_p hM.1
  haveI : IsDiscreteValuationRing (OK l K) := OK_dvr
  obtain ⟨U⟩ := (cov_ex M.p).1 hM.2
  obtain ⟨k, h1, h2⟩ := lift_gr afgA L.γ l m ok_dv (tf_dom (Fact.out : l.Prime).ne_zero ok_dv (by omega)) L.lat M.p U r hr j
  obtain ⟨z, hz⟩ := h1 (fun n => (L.rS M r n).pull j (x n)) fun n =>
    (rS_tr L M r j n (x (n + 1))).symm.trans (congrArg ((L.rS M r n).pull j) (hx n))
  exact exu (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l (unit_B L) (fun n => (L.rS M r n).pull j (x n))
    (2 * k) z hz k h2

theorem add (r j : ℕ) (x y : Y.Fam M r j) (w w' : HG (L.QB M) r j) (h : L.Rho x w) (h' : L.Rho y w') : L.Rho (x + y) (w + w') := by
  obtain ⟨e, z, h1, h2⟩ := add_abs (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l
    (fun n => (L.rS M r n).pull j (x n)) (fun n => (L.rS M r n).pull j (y n)) w w' h h'
  exact ⟨e, z, fun n => (h1 n).trans (congrArg _ (map_add ((L.rS M r n).pull j) (x n) (y n)).symm), h2⟩

theorem smul (r j : ℕ) (c : Y.Λ) (x : Y.Fam M r j) (w : HG (L.QB M) r j) (h : L.Rho x w) : L.Rho (c • x) (L.ι (L.lam c) • w) := by
  obtain ⟨e, z, h1, h2⟩ := smul_abs (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l
    (fun n => (L.rS M r n).pull j (x n)) w (L.lam c) h
  exact ⟨e, z, fun n => (h1 n).trans (congrArg _ (LinearMap.map_smulₛₗ ((L.rS M r n).pull j) c (x n)).symm), h2⟩

end RhoA

theorem rhoEx {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] K] : RhoEx l K := by
  exact ⟨fun L M => RhoA.ex L M, fun L M => RhoA.add L M, fun L M => RhoA.smul L M⟩

end CrystallineSemistableComparison.HT
end
end
