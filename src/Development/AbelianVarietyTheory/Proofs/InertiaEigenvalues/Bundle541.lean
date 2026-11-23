module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle328
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle523
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle272
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle522
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.Prism.ModelChange

def Via {B C : Type} [CommRing B] [CommRing C] (_g : B →+* C) (Q : Type) : Type := Q

instance instAddCommGroupVia {B C : Type} [CommRing B] [CommRing C] (g : B →+* C) (Q : Type)
    [AddCommGroup Q] : AddCommGroup (Via g Q) := ‹AddCommGroup Q›

instance instModuleVia {B C : Type} [CommRing B] [CommRing C] (g : B →+* C) (Q : Type) [AddCommGroup Q]
    [Module C Q] : Module B (Via g Q) := Module.compHom Q g

theorem semiBC_comp {A B C M N P : Type} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P]
    {f : A →+* B} {g : B →+* C} {h : A →+* C} (hfg : ∀ a, g (f a) = h a)
    {u : M →ₛₗ[f] N} {v : N →ₛₗ[g] P} {w : M →ₛₗ[h] P} (hw : ∀ x, w x = v (u x))
    (hu : SemiBC u) (hv : SemiBC v) : SemiBC w := by
  intro Q _ _ q
  let q₁ : M →ₛₗ[f] Via g Q :=
    { toFun := fun x => (q x : Q)
      map_add' := fun x y => map_add q x y
      map_smul' := fun a x => by
        change q (a • x) = g (f a) • (q x : Q)
        rw [q.map_smulₛₗ, hfg] }
  obtain ⟨w₁, hw₁, hu₁⟩ := hu (Via g Q) q₁
  let w₂ : N →ₛₗ[g] Q :=
    { toFun := fun y => (w₁ y : Q)
      map_add' := fun y z => map_add w₁ y z
      map_smul' := fun b y => w₁.map_smul b y }
  obtain ⟨w₃, hw₃, hu₃⟩ := hv Q w₂
  refine ⟨w₃, fun x => ?_, fun w' hw' => ?_⟩
  · rw [hw, hw₃]; exact hw₁ x
  · let w'' : N →ₗ[B] Via g Q :=
      { toFun := fun y => (w' (v y) : Q)
        map_add' := fun y z => by
          change w' (v (y + z)) = w' (v y) + w' (v z)
          rw [map_add (f := _), map_add (f := _)]
        map_smul' := fun b y => by
          change w' (v (b • y)) = g b • w' (v y)
          rw [v.map_smulₛₗ, w'.map_smul] }
    have h1 : w'' = w₁ := hu₁ w'' fun x => by
      change w' (v (u x)) = q x
      rw [← hw x]; exact hw' x
    exact hu₃ w' fun y => by
      change w' (v y) = (w₁ y : Q)
      rw [← h1]; rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem torsionFree_of_equiv {P : Obj l ↥(OL K)} (e : P.A ≃+* Ainf l) (x : P.A) (h : (l : P.A) * x = 0) :
    x = 0 :=
  e.injective (by rw [map_zero]; apply ainf_torsionFree; rw [← map_natCast e, ← map_mul, h, map_zero])

def toAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) : Hom P (ainfObj K) where
  f := e.toRingHom
  f_δ := P.D.map_δ_of_map_φ (ainfObj K).D ainf_torsionFree _ fun a => H.e_φ a
  f_I a ha := ((isAinf_ainfObj K).e_I (e a)).2 ((H.e_I a).1 ha)
  f_str r a h := ((isAinf_ainfObj K).mk_eq_str_iff r (e a)).2 ((H.mk_eq_str_iff r a).1 h)

def ofAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) : Hom (ainfObj K) P where
  f := e.symm.toRingHom
  f_δ := (ainfObj K).D.map_δ_of_map_φ P.D (torsionFree_of_equiv e) _ fun a => e.injective
      ((e.apply_symm_apply _).trans ((congrArg WittVector.frobenius (e.apply_symm_apply (a : Ainf l))).symm.trans
        (H.e_φ _).symm))
  f_I a ha := (H.e_I _).2
      ((congrArg (Per.θ l) (e.apply_symm_apply (a : Ainf l))).trans (((isAinf_ainfObj K).e_I a).1 ha))
  f_str r a h := (H.mk_eq_str_iff r _).2
      ((congrArg (Per.θ l) (e.apply_symm_apply (a : Ainf l))).trans (((isAinf_ainfObj K).mk_eq_str_iff r a).1 h))

theorem ofAinf_comp_toAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) :
    (ofAinf H).comp (toAinf H) = Hom.id P :=
  Hom.ext' (RingHom.ext fun a => e.symm_apply_apply a)

theorem toAinf_comp_ofAinf {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) :
    (toAinf H).comp (ofAinf H) = Hom.id (ainfObj K) :=
  Hom.ext' (RingHom.ext fun a => e.apply_symm_apply a)

variable {T : Type} [AddCommGroup T] [Module ℤ_[l] T]

def jOfModel {M : FCrys l ↥(OL K)} {P P' : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} {e' : P'.A ≃+* Ainf l}
    (c : Hom P P') (hc : ∀ a, e' (c.f a) = e a)
    (j' : M.M P' →ₛₗ[(inclW l).comp e'.toRingHom] (WCb l ⊗[ℤ_[l]] T)) :
    M.M P →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T) where
  toFun x := j' (M.tr c x)
  map_add' x y := by rw [map_add (f := _), map_add (f := _)]
  map_smul' a x := by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    change inclW l (e' (c.f a)) • _ = inclW l (e a) • _
    rw [hc]

theorem realises_of {M : FCrys l ↥(OL K)} {P P' : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l}
    {e' : P'.A ≃+* Ainf l} {ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)} (H : IsAinf K P e) (c : Hom P P')
    (hc : ∀ a, e' (c.f a) = e a) {j' : M.M P' →ₛₗ[(inclW l).comp e'.toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (hj : Realises K M P' e' T ρ j') : Realises K M P e T ρ (jOfModel c hc j') := by
  have H' := hj.ainf
  obtain ⟨d₀, hd, hd0⟩ := H.exists_generator
  refine Realises.of_generator H ?_ d₀ hd ?_ ?_
  · exact semiBC_comp (f := c.f) (g := (inclW l).comp e'.toRingHom) (h := (inclW l).comp e.toRingHom)
      (u := M.tr c) (v := j') (w := jOfModel c hc j') (fun a => congrArg (inclW l) (hc a)) (fun _ => rfl)
      (M.tr_bc c) hj.bc
  · intro x m k h
    have : IsDomain P'.A := e'.toMulEquiv.isDomain
    have := M.proj P'
    let d' : ↥P'.I := ⟨c.f d₀, c.f_I _ d₀.2⟩
    have hd'e : e' (d' : P'.A) = e d₀ := hc _
    have hd'0 : (d' : P'.A) ≠ 0 := fun h0 => hd0 (e.injective (by rw [← hd'e, h0, map_zero, map_zero]))
    obtain ⟨n, i, hn⟩ := exists_isFrac (d' : P'.A) (M.Φ P' d' (M.tr c x))
    obtain ⟨r, hr⟩ := M.Φ_nat c d₀ d' x m k n i h hn
    have heq : (d' : P'.A) ^ i • M.tr c m = (d' : P'.A) ^ k • n :=
      sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero hd'0 hd'0)))
    have hu : IsUnit (((inclW l).comp e'.toRingHom) (d' : P'.A)) := by
      change IsUnit (inclW l (e' (d' : P'.A))); rw [hd'e]; exact H.isUnit_inclW hd
    have key := smul_eq_of_isUnit j' hu heq (hj.j_φ d' hd'0 (M.tr c x) n i hn)
    change inclW l (e d₀) ^ k • _ = j' (M.tr c m)
    rw [← hd'e]; exact key
  · intro g x
    have hcg : c.comp (H.galHom g) = (H'.galHom g).comp c := Hom.ext' (RingHom.ext fun a => e'.injective (by
      change e' (c.f ((H.galHom g).f a)) = e' ((H'.galHom g).f (c.f a))
      rw [hc, H.e_galHom, H'.e_galHom, hc]))
    have e0 : M.tr c (M.tr (H.galHom g) x) = M.tr (H'.galHom g) (M.tr c x) :=
      (M.tr_comp _ _ x).symm.trans ((congrArg (fun f => M.tr f x) hcg).trans (M.tr_comp _ _ x))
    exact (congrArg j' e0).trans (hj.j_act g (M.tr c x))

end GlobalTheory.Prism.ModelChange


open GlobalTheory.Prism.ModelChange in
theorem GlobalTheory.Prism.realisation_indep_model : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e₀ : P₀.A ≃+* Ainf l), IsAinf K P₀ e₀ → ∃ a : Hom P₀ (ainfObj K), ∀ (M : FCrys l ↥(OL K)), Function.Bijective (M.tr a) ∧ ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)), (∀ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ → ∃ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j) ∧ (∀ j : M.M P₀ →ₛₗ[(inclW l).comp e₀.toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M P₀ e₀ T ρ j → ∃ j₀ : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j₀ ∧ ∀ x, j₀ (M.tr a x) = j x) := by
  intro l _ K P₀ e₀ H
  refine ⟨toAinf H, fun M => ⟨?_, fun T _ _ ρ => ⟨fun j₀ hj₀ => ⟨_, realises_of H (toAinf H) (fun _ => rfl) hj₀⟩,
    fun j hj => ⟨_, realises_of (isAinf_ainfObj K) (ofAinf H) (fun a => by exact e₀.apply_symm_apply a) hj,
      fun x => ?_⟩⟩⟩⟩
  · refine Function.bijective_iff_has_inverse.2 ⟨M.tr (ofAinf H), fun x => ?_, fun y => ?_⟩
    · rw [← M.tr_comp, ofAinf_comp_toAinf, M.tr_id]
    · rw [← M.tr_comp, toAinf_comp_ofAinf, M.tr_id]
  · change j (M.tr (ofAinf H) (M.tr (toAinf H) x)) = j x
    rw [← M.tr_comp, ofAinf_comp_toAinf, M.tr_id]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.MirAvg

theorem bc_ringEquiv_eq_one_iff {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K) :
    Formalism.UG.bc (e : K →+* K') h = 1 ↔ h = 1 := by
  refine ⟨fun H => ?_, fun H => by rw [H, map_one]⟩
  ext i j
  have := congrArg (fun u : GL (Fin r) K' => (u : Matrix (Fin r) (Fin r) K') i j) H
  apply e.injective
  have h1 : ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K') i j
      = e ((h : Matrix (Fin r) (Fin r) K) i j) := rfl
  simp only [h1] at this
  rw [this]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem bc_ringEquiv_mulVec {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K)
    (x : Fin r → K) :
    ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K').mulVec (fun j => e (x j)) =
      fun j => e ((h : Matrix (Fin r) (Fin r) K).mulVec x j) := by
  funext j
  have h1 : ∀ i j, ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K') i j
      = e ((h : Matrix (Fin r) (Fin r) K) i j) := fun _ _ => rfl

  simp only [Matrix.mulVec, dotProduct, h1, map_sum, map_mul]

theorem det_bc_ringEquiv {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K) :
    Matrix.GeneralLinearGroup.det (Formalism.UG.bc (e : K →+* K') h) =
      Units.map (e : K →* K') (Matrix.GeneralLinearGroup.det h) := by
  ext
  exact ((e : K →+* K').map_det (h : Matrix (Fin r) (Fin r) K)).symm

theorem mirSet_iff_bc {g : ℕ} [Fact g.Prime] {r : ℕ} {K' : Type} [CommRing K'] (e : ZMod g ≃+* K')
    (h : GL (Fin r) (ZMod g)) (a : Fin r → K') (b : Bool) :
    (if b then ∀ x, ∃ c : K', ((Formalism.UG.bc (e : ZMod g →+* K') h : GL (Fin r) K') :
        Matrix (Fin r) (Fin r) K').mulVec x - x = c • a
      else ∀ x, a ⬝ᵥ x = 0 → ((Formalism.UG.bc (e : ZMod g →+* K') h : GL (Fin r) K') :
        Matrix (Fin r) (Fin r) K').mulVec x = x) ↔ mirSet (fun j => e.symm (a j)) b h := by
  have hs : Function.Surjective (fun (x : Fin r → ZMod g) j => e (x j)) :=
    fun x => ⟨fun j => e.symm (x j), by funext j; simp⟩
  cases b with
  | true =>
    simp only [mirSet, if_true]
    rw [hs.forall]
    refine forall_congr' fun x => ?_
    rw [bc_ringEquiv_mulVec, e.surjective.exists]
    refine exists_congr fun c => ?_
    simp only [funext_iff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun j => ?_
    rw [← e.injective.eq_iff (a := _ - _), map_sub, map_mul, e.apply_symm_apply]
  | false =>
    simp only [mirSet, Bool.false_eq_true, if_false]
    rw [hs.forall]
    refine forall_congr' fun x => ?_
    rw [bc_ringEquiv_mulVec]
    refine imp_congr ?_ ?_
    · rw [← e.injective.eq_iff (b := 0), map_zero]

      simp only [dotProduct, map_sum, map_mul, e.apply_symm_apply]
    · simp only [funext_iff, e.injective.eq_iff]

theorem mirC_eq_coeff_mirEl : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eR : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) →
    ∀ (i : Fin D.R.m) (kv0 : Σ k : Fin 2, D.nd.PlG k) (a : Fin D.R.r → kP (plg kv0).1) (b : Bool) (ε : ℤ) (y : G),
    haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
    GlobalTheory.DownLift.mirC R i (plg kv0) a b ε y = (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then
      (GlobalTheory.MirAvg.mirEl ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) (plg kv0).1).comp
        (Units.map (iso kv0 : ZMod (D.host.g kv0.1) →* kP (plg kv0).1))))
        (fun j => (iso kv0).symm (a j)) b).coeff (eR y kv0) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R eR plg iso hrec i kv0 a b ε y
  haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
  have h1 : (∀ PP', PP' ≠ plg kv0 → R.eG y PP' = 1) ↔ ∀ kv, kv ≠ kv0 → eR y kv = 1 := by
    rw [plg.surjective.forall]
    refine forall_congr' fun kv => imp_congr plg.injective.ne_iff ?_
    rw [hrec]
    exact bc_ringEquiv_eq_one_iff _ _
  have h2 := mirSet_iff_bc (iso kv0) (eR y kv0) a b
  have h3 := det_bc_ringEquiv (iso kv0) (eR y kv0)
  rw [← hrec] at h2 h3
  rw [mirEl_coeff]
  unfold GlobalTheory.DownLift.mirC
  by_cases hA : ∀ kv, kv ≠ kv0 → eR y kv = 1
  · rw [if_pos hA]
    by_cases hB : mirSet (fun j => (iso kv0).symm (a j)) b (eR y kv0)
    · rw [if_pos hB, if_pos ⟨h1.2 hA, h2.2 hB⟩, h3]
      rfl
    · rw [if_neg hB, if_neg fun H => hB (h2.1 H.2)]
  · rw [if_neg hA, if_neg fun H => hA (h1.1 H.1)]

end GlobalTheory.MirAvg

end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

noncomputable section

namespace GlobalTheory.RSConj

theorem conj_tprod {β : Type} (f : β → ℂ) :
    starRingEnd ℂ (∏' i, f i) = ∏' i, starRingEnd ℂ (f i) := by
  by_cases hf : Multipliable f
  · exact hf.map_tprod (starRingEnd ℂ) Complex.continuous_conj
  · have hg : ¬ Multipliable fun i => starRingEnd ℂ (f i) := by
      intro hg
      apply hf
      have := hg.map (starRingEnd ℂ) Complex.continuous_conj
      convert this using 1
      funext i
      simp
    rw [tprod_eq_one_of_not_multipliable hf, tprod_eq_one_of_not_multipliable hg, map_one]

theorem conj_natCast_cpow_neg (q : ℕ) (x : ℝ) :
    starRingEnd ℂ ((q : ℂ) ^ (-(x : ℂ))) = (q : ℂ) ^ (-(x : ℂ)) := by
  have h : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
    push_cast
    rfl
  rw [h, Complex.conj_ofReal]

theorem conj_locL (q : ℕ) (A B : Multiset ℂˣ) (x : ℝ) :
    starRingEnd ℂ (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) =
      locL q B (A.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  unfold locL
  rw [map_multiset_prod]
  simp only [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.prod_bind, Multiset.map_map, Function.comp_def]
  rw [Multiset.prod_map_prod_map]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [map_inv₀, map_sub, map_one, map_mul, conj_natCast_cpow_neg, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Complex.conj_conj]
  ring

theorem partial_conj : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b),
    σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' →
    ∀ x : ℝ, 1 < x → ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 =
      starRingEnd ℂ (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) := by
  intro E _ _ _ a b σ σ' _ _ T _ _ x _
  rw [conj_tprod]
  congr 1
  funext w
  exact (conj_locL _ _ _ x).symm

end GlobalTheory.RSConj
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

def yInf (g : GA E (m + 1)) : Fin (m + 1) → Cinf E := fun i => pInf E (GlobalTheory.ZEul.lastRow g i)

def yFin (g : GA E (m + 1)) : Fin (m + 1) → Af E := fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)

def sqrtC (Φ : (Fin (m + 1) → Cinf E) → ℂ) (u : Fin (m + 1) → Cinf E) : ℂ := (Real.sqrt (Φ u).re : ℂ)

def fT (φ : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (g : GA E (m + 1)) : ℂ :=
  φ (g * infGL E (m + 1) (secInv (yInf g))) * sqrtC Φ (yInf g)

def wt (N : ℕ) (x : ℝ) (g : GA E (m + 1)) : ℝ≥0 := Real.toNNReal ((indN N (yFin g)).re * detPow E (m + 1) x g)

theorem yInf_of_lastRow {g g' : GA E (m + 1)} (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g) : yInf g' = yInf g := by
  funext i; exact congrArg (fun r => pInf E (r i)) h

theorem yFin_of_lastRow {g g' : GA E (m + 1)} (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g) : yFin g' = yFin g := by
  funext i; exact congrArg (fun r => GlobalTheory.RSJ.pFin E (r i)) h

theorem fT_of_lastRow {φ : GA E (m + 1) → ℂ} {Φ : (Fin (m + 1) → Cinf E) → ℂ} {g g' : GA E (m + 1)}
    (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g) :
    fT φ Φ g' = φ (g' * infGL E (m + 1) (secInv (yInf g))) * sqrtC Φ (yInf g) := by
  rw [fT, yInf_of_lastRow h]

theorem wt_of_lastRow_of_detPow {N : ℕ} {x : ℝ} {g g' : GA E (m + 1)} (h : GlobalTheory.ZEul.lastRow g' = GlobalTheory.ZEul.lastRow g)
    (hd : detPow E (m + 1) x g' = detPow E (m + 1) x g) : wt N x g' = wt N x g := by
  rw [wt, wt, yFin_of_lastRow h, hd]

end GlobalTheory.ZUnf
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.HerrCocycleCriterion

theorem herr_of_tie {O D M : Type} [CommRing O] [AddCommGroup D] [Module O D] [AddCommGroup M]
    [Module O M] (γ φ : D →ₗ[O] D) (g Φ : M →ₗ[O] M) (j : D →ₗ[O] M) (hj : Function.Injective j)
    (y z : D) (b t : M) (hγ : j (γ y) = g (j y)) (hφ : j (φ z) = Φ (j z))
    (hc : Φ (g b) = g (Φ b)) (ht : Φ t = t) (hy : Φ b - b = j y) (hz : t + (g b - b) = j z) :
    (y, z) ∈ herrCocycles γ φ := by
  simp only [herrCocycles, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply]
  apply hj
  rw [map_zero, map_add (f := _), map_neg, map_sub, map_sub, hγ, hφ, ← hy, ← hz, map_add (f := _), map_sub, map_sub,
    hc, ht]
  abel

theorem TWmap_one {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R]
    [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (t : ↥T.L.T) :
    TWmap f T ((1 : R) ⊗ₜ[O] t) = (1 : R) ⊗ₜ[O] t := by
  simp [TWmap]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cocyc : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T := by
  intro D HW F l _ K s LL h T c b y z g₀ hg hy hz
  have h1 := ((F l).E K s LL h).tie.jD_act T (g₀ : ↥(GK K)) y
  rw [hg] at h1
  exact herr_of_tie _ _ _ _ _ (((F l).E K s LL h).tie.jD_inj T) y z b _ h1
    (((F l).E K s LL h).tie.jD_φ T z)
    (GlobalTheory.HerrClassMaps.TWmap_act _ _ (GlobalTheory.HerrClassMaps.phi_gRW (D.locA l) LL _) T _ b)
    (TWmap_one _ T _) hy hz

end GlobalTheory.NL.HerrCocycleCriterion
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_top_of_vanishing_blockAverages : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E (m + 1) → ℂ),
    Continuous f → (∀ γ g, f (ratGL E (m + 1) γ * g) = f g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => f (blkU x * g)) = 0) → Good ψ m f := by
  first | (exact @GlobalTheory.CuspGeneric.good_top) | (exact GlobalTheory.CuspGeneric.good_top) | (intros; apply GlobalTheory.CuspGeneric.good_top  <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.exists_finset_definiteUnitary_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y := by
  first | exact @GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets | exact GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets | (intros; apply GlobalTheory.UnitaryBC.ClassTransport.exists_finset_double_cosets <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_ainf_unit_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (ω : (Ainf l)ˣ), ∃ η : (Ainf l)ˣ, WittVector.frobenius (η : Ainf l) = ω * η := by
  first | exact @GlobalTheory.Per.frobenius_eq_mul_solvable | exact GlobalTheory.Per.frobenius_eq_mul_solvable | (intros; apply GlobalTheory.Per.frobenius_eq_mul_solvable <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

theorem _root_.GlobalTheory.T.maxUnramified_acts_on_letterIdempotent_image : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)), ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i)) := by
  first | exact @GlobalTheory.HWL.Letter.letter | exact GlobalTheory.HWL.Letter.letter | (intros; apply GlobalTheory.HWL.Letter.letter <;> assumption)
end
