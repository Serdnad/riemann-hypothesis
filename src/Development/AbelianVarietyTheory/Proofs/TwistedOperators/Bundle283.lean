module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle058
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle269
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocHat

open GlobalTheory.StdFrames (cpt cpt_ext toAd_spec)

variable {D : D7} {n : ℕ}

theorem mem_hat_iff_locL {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) (y : Fin n → EAf D) :
    y ∈ hat Λ ↔ ∀ v : HeightOneSpectrum (𝓞 D.host.F),
      (fun i => Formalism.UG.prV (E := D.host.E) v (y i)) ∈ Formalism.L2.Herm.locL v Λ := by
  haveI : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.mpr h
  rw [mem_hat]
  exact GlobalTheory.LatticeStabLocal.mem_latS_adele_iff Λ y

theorem prV_eq_zero_iff_cpt (v : HeightOneSpectrum (𝓞 D.host.F)) (z : EAf D) :
    Formalism.UG.prV (E := D.host.E) v z = 0 ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → cpt Q z = 0 := by
  refine (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (toAd_spec D) v z).trans ?_
  exact Iff.rfl

theorem mem_hat_iff_of_supp {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    (v : HeightOneSpectrum (𝓞 D.host.F)) {y : Fin n → EAf D}
    (hy : ∀ w, w ≠ v → ∀ i, Formalism.UG.prV (E := D.host.E) w (y i) = 0) :
    y ∈ hat Λ ↔ (fun i => Formalism.UG.prV (E := D.host.E) v (y i)) ∈ Formalism.L2.Herm.locL v Λ := by
  rw [mem_hat_iff_locL h]
  refine ⟨fun H => H v, fun H w => ?_⟩
  by_cases hwv : w = v
  · subst hwv
    exact H
  · have hz : (fun i => Formalism.UG.prV (E := D.host.E) w (y i)) = 0 := by
      ext i
      exact hy w hwv i
    rw [hz]
    exact Submodule.zero_mem _


theorem locL_le {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) (h' : Λ'.FG)
    (v : HeightOneSpectrum (𝓞 D.host.F))
    (H : ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ → idem Q • y ∈ hat Λ') :
    Formalism.L2.Herm.locL v Λ ≤ Formalism.L2.Herm.locL v Λ' := by
  obtain ⟨e, -, -, he1, he0⟩ :=
    GlobalTheory.StdFrames.exists_idem (D := D) {Q : Pl D.host.E | Q.under (𝓞 D.host.F) = v}

  have hpe : Formalism.UG.prV (E := D.host.E) v e = 1 := by
    have h0 : Formalism.UG.prV (E := D.host.E) v (e - 1) = 0 := by
      rw [prV_eq_zero_iff_cpt]
      intro Q hQ
      rw [map_sub, map_one, he1 Q hQ, sub_self]
    rwa [map_sub, map_one, sub_eq_zero] at h0

  have key : ∀ x ∈ Λ, (e • fun i => inc D (x i)) ∈ hat Λ' := by
    intro x hx
    refine mem_hat_of_idem h' fun w => ?_
    rw [smul_smul]
    by_cases hw : w.under (𝓞 D.host.F) = v
    · have hwe : idem w * e = idem w := by
        refine cpt_ext fun Q => ?_
        rw [map_mul]
        by_cases hQ : Q = w
        · subst hQ
          rw [cpt_idem_self, he1 Q hw, one_mul]
        · rw [cpt_idem_ne hQ, zero_mul]
      rw [hwe]
      exact H w hw _ (smul_mem_hat (idem_mem w) (inc_mem_hat hx))
    · have hwe : idem w * e = 0 := by
        refine cpt_ext fun Q => ?_
        rw [map_mul, map_zero]
        by_cases hQ : Q = w
        · subst hQ
          rw [he0 Q hw, mul_zero]
        · rw [cpt_idem_ne hQ, zero_mul]
      rw [hwe, zero_smul]
      exact zero_mem_hat

  unfold Formalism.L2.Herm.locL Formalism.UG.latS
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have hm := (mem_hat_iff_locL h' _).mp (key x hx) v
  have hxe : (fun i => Formalism.UG.prV (E := D.host.E) v ((e • fun i => inc D (x i)) i)) =
      fun i => Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) (x i) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hpe, one_mul]
    rw [Formalism.UG.P.afsplit_prV_inclE]
  rw [hxe] at hm
  exact hm

theorem prV_idem_smul {v : HeightOneSpectrum (𝓞 D.host.F)} {Q : Pl D.host.E} (hQ : Q.under (𝓞 D.host.F) = v)
    (y : Fin n → EAf D) : ∀ w, w ≠ v → ∀ i, Formalism.UG.prV (E := D.host.E) w ((idem Q • y) i) = 0 := by
  intro w hw i
  have hQw : Formalism.UG.prV (E := D.host.E) w (idem Q) = 0 := by
    rw [prV_eq_zero_iff_cpt]
    intro Q' hQ'
    apply cpt_idem_ne
    intro hEq
    subst hEq
    exact hw (hQ'.symm.trans hQ)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, hQw, zero_mul]

theorem locL_eq_iff_idem : ∀ (D : D7) (n : ℕ) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Λ.FG → Λ'.FG → ∀ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ' ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ ↔ idem Q • y ∈ hat Λ' := by
  intro D n Λ Λ' h h' v
  constructor
  · intro heq Q hQ y
    rw [mem_hat_iff_of_supp h v (prV_idem_smul hQ y), mem_hat_iff_of_supp h' v (prV_idem_smul hQ y), heq]
  · intro H
    exact le_antisymm (locL_le h h' v fun Q hQ y => (H Q hQ y).mp)
      (locL_le h' h v fun Q hQ y => (H Q hQ y).mpr)

end GlobalTheory.LocHat
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.Unglue

theorem ideal_eq_top {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (h : ∀ a : E, (∀ i ∈ I, a * (i : E) ∈ (algebraMap (𝓞 E) E).range) → a ∈ (algebraMap (𝓞 E) E).range) :
    I = ⊤ := by
  have h0 : (I : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI
  have h1 : (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ≤ 1 := by
    intro a ha
    have ha' := (FractionalIdeal.mem_inv_iff h0).1 ha
    refine (FractionalIdeal.mem_one_iff _).2 (h a fun i hi => ?_)
    exact (FractionalIdeal.mem_one_iff _).1 (ha' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hi))
  have h2 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 E)⁰ E) = I * (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ I * 1 := by gcongr
      _ = I := mul_one _
  rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact top_le_iff.1 h2

theorem star_mem {E : Type} [Field E] [NumberField E] [StarRing E] {a : E}
    (h : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨RingOfIntegers.mapRingEquiv starRingAut b, rfl⟩

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V) {y : V}
    (hy : y ∈ Submodule.span E (L : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | (apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target ..)

theorem isLattice_capX_and_exists_glue (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V)
    (hl : IsLine Y X ι z u) (L : Submodule (𝓞 D.host.E) Y.V) (hL : IsSDIn Y (flatSp Y X ι z) L) (hp : IsPrim Y z L) :
    Submodule.IsFullLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  obtain ⟨hi, ho, hz⟩ := hl
  obtain ⟨hfg, hsp, hsd⟩ := hL
  have hT := Tu_ne_zero u
  have hinj : Function.Injective ι := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    refine X.nondeg.1 x fun y => ?_
    rw [← hi, hx, map_zero, LinearMap.zero_apply]
  have hzU : ∀ a : D.host.E, a • z ∈ flatSp Y X ι z := fun a =>
    Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))
  have hzL : z ∈ L := by simpa using (hp 1).2 (one_mem _)
  have hLU : ∀ y ∈ L, y ∈ flatSp Y X ι z := fun y hy => hsp ▸ Submodule.subset_span hy
  have hint : ∀ y ∈ L, Y.hD y z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := fun y hy =>
    (hsd z (hLU z hzL)).1 hzL y hy
  have hdec : ∀ y ∈ L, ∃ x : X.V, y = ι x + (-(Y.hD y z) * (Tu D u)⁻¹) • z := by
    intro y hy
    obtain ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 (hLU y hy)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hb
    refine ⟨x, ?_⟩
    have : Y.hD (ι x + s • z) z = -(s * Tu D u) := by
      have h1 := ho x
      simp only [HSpace.hD] at h1 hz ⊢
      rw [map_add (f := _), map_smul, h1, hz, smul_eq_mul]; ring
    rw [this]
    congr 2
    field_simp
  have hlat : Submodule.IsLattice D.host.E (capX Y X ι L) := by
    refine GlobalTheory.StdFrames.isLattice_crdLat X ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective (ι.restrictScalars (𝓞 D.host.E)) hinj (hfg.of_le ?_)
      exact Submodule.map_comap_le _ _
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
  refine ⟨{ toIsLattice := hlat, span_eq_top := ?_ }, ?_⟩
  · apply Submodule.eq_top_iff'.2
    intro y
    let x := (Formalism.L2.Herm.crd X).symm y
    have hx : ι x ∈ Submodule.span D.host.E (L : Set Y.V) := by
      rw [hsp]
      exact Submodule.mem_sup_left (LinearMap.mem_range_self ι x)
    obtain ⟨c, hc, hcx⟩ := exists_smul_mem L hx
    have hcy : c • y ∈ capX Y X ι L := by
      change c • y ∈ Formalism.L2.Herm.crdLat X (L.comap (ι.restrictScalars (𝓞 D.host.E)))
      refine ⟨c • x, ?_, ?_⟩
      · change ι (c • x) ∈ L
        simpa using hcx
      · simp [x]
    have hcy' : c • y ∈ Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E)) :=
      Submodule.subset_span hcy
    rw [← algebraMap_smul D.host.E c] at hcy'
    have := (Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E))).smul_mem
      (c : D.host.E)⁻¹ hcy'
    simpa only [smul_smul, inv_mul_cancel₀ (RingOfIntegers.coe_ne_zero_iff.2 hc), one_smul] using this
  · let I : Ideal (𝓞 D.host.E) :=
      (L.map ((Y.hT z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hI : ∀ i : 𝓞 D.host.E, i ∈ I ↔ ∃ y ∈ L, Y.hD y z = (i : D.host.E) := fun i => Iff.rfl
    have hI0 : I ≠ ⊥ := by
      obtain ⟨i, hi'⟩ := hint z hzL
      intro h
      have : i ∈ I := (hI i).2 ⟨z, hzL, hi'.symm⟩
      rw [h, Ideal.mem_bot] at this
      rw [this, map_zero, hz] at hi'
      exact hT (neg_eq_zero.1 hi'.symm)
    have hItop : I = ⊤ := by
      refine ideal_eq_top I hI0 fun a ha => ?_
      have : star a • z ∈ L := by
        refine (hsd _ (hzU _)).2 fun x hx => ?_
        obtain ⟨i, hi'⟩ := hint x hx
        have := ha i ((hI i).2 ⟨x, hx, hi'.symm⟩)
        have e : Y.hD x (star a • z) = a * Y.hD x z := by
          simp only [HSpace.hD]
          rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
          congr 1
          exact star_star a
        rw [e, ← hi']
        exact this
      simpa using star_mem ((hp _).1 this)
    obtain ⟨l, hlL, hl1⟩ := (hI (-1)).1 (hItop ▸ Submodule.mem_top)
    obtain ⟨x₀, hx₀⟩ := hdec l hlL
    have hl2 : l = (Tu D u)⁻¹ • z + ι x₀ := by
      rw [hx₀, hl1, add_comm]
      simp
    have hc : (capX Y X ι L).comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
        L.comap (ι.restrictScalars (𝓞 D.host.E)) :=
      Submodule.comap_map_eq_of_injective (f := (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E))
        (Formalism.L2.Herm.crd X).injective _
    refine ⟨x₀, ?_⟩
    rw [glueLat, hc, ← hl2]
    refine le_antisymm (fun y hy => ?_)
      (sup_le (Submodule.map_comap_le _ _) ((Submodule.span_singleton_le_iff_mem _ _).2 hlL))
    obtain ⟨x, hx⟩ := hdec y hy
    obtain ⟨b, hb⟩ := hint y hy
    have e : y + b • l = ι (x + b • x₀) := by
      rw [← algebraMap_smul D.host.E b, ← algebraMap_smul D.host.E b x₀, hb, map_add (f := _), map_smul, hl2]
      generalize Y.hD y z = t at hx ⊢
      rw [hx]
      module
    have hm : y + b • l ∈ L := L.add_mem hy (L.smul_mem _ hlL)
    have e2 : y = ι (x + b • x₀) - b • l := by rw [← e, add_sub_cancel_right]
    rw [e2]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x + b • x₀, ?_, rfl⟩)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self l)))
    change ι (x + b • x₀) ∈ L
    rw [← e]
    exact hm

end GlobalTheory.AdIsom.Unglue
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.GLTwist

open Formalism.UG (Tj Ov)

section Twist

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ordV_mul {x y : w.adicCompletion E} (hx : x ≠ 0) (hy : y ≠ 0) :
    Formalism.UG.ordV E w (x * y) = Formalism.UG.ordV E w x + Formalism.UG.ordV E w y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, GlobalTheory.LGrp.BorelCompletion.ordV_eq, GlobalTheory.LGrp.BorelCompletion.ordV_eq, map_mul,
    WithZero.log_mul hx' hy']
  ring

theorem ordV_zpow {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℤ) : Formalism.UG.ordV E w (ϖ ^ k) = k := by
  rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, map_zpow₀, show Valued.v ϖ = _ from hϖ, WithZero.log_zpow,
    show WithZero.log (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ)) : WithZero (Multiplicative ℤ)) = -1 from rfl]
  simp

def ordDet (g : GL (Fin r) (w.adicCompletion E)) : ℤ := Formalism.UG.ordV E w g.val.det

theorem det_ne_zero (g : GL (Fin r) (w.adicCompletion E)) : g.val.det ≠ 0 :=
  (Matrix.GeneralLinearGroup.det g).ne_zero

theorem ordDet_mul (g h : GL (Fin r) (w.adicCompletion E)) : ordDet (g * h) = ordDet g + ordDet h := by
  rw [ordDet, Units.val_mul, Matrix.det_mul, ordV_mul (det_ne_zero g) (det_ne_zero h)]
  rfl

theorem ordDet_of_mem {k : GL (Fin r) (w.adicCompletion E)} (hk : k ∈ KGL w (n := r)) : ordDet k = 0 := by
  have h : Valued.v k.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hk
  rw [ordDet, GlobalTheory.LGrp.BorelCompletion.ordV_eq, h]
  simp

theorem ordDet_one : ordDet (1 : GL (Fin r) (w.adicCompletion E)) = 0 := ordDet_of_mem (one_mem _)

theorem prod_zpow_eq {ι : Type} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (d : ι → ℤ) (s : Finset ι) :
    ∏ i ∈ s, ϖ ^ d i = ϖ ^ ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ h0]

theorem ordDet_of_diagonal {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {t : GL (Fin r) (w.adicCompletion E)}
    {d : Fin r → ℤ} (ht : t.1 = Matrix.diagonal fun i => ϖ ^ d i) : ordDet t = ∑ i, d i := by
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  rw [ordDet, ht, Matrix.det_diagonal, prod_zpow_eq h0, ordV_zpow hϖ]

def twistRep (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ) :
    Representation ℂ (GL (Fin r) (w.adicCompletion E)) V where
  toFun g := ((z : ℂ) ^ ordDet g) • ρ g
  map_one' := by simp [ordDet_one]
  map_mul' g h := by
    rw [ordDet_mul, zpow_add₀ z.ne_zero, map_mul]
    refine LinearMap.ext fun y => ?_
    simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, mul_smul]
    exact smul_comm _ _ _

theorem twistRep_apply (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ)
    (g : GL (Fin r) (w.adicCompletion E)) (y : V) : twistRep ρ z g y = ((z : ℂ) ^ ordDet g) • ρ g y := rfl

theorem heckeVec_twistRep (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (z : ℂˣ)
    (t : GL (Fin r) (w.adicCompletion E)) (x : V) :
    heckeVec (twistRep ρ z) (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) t) x =
      ((z : ℂ) ^ ordDet t) • heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) t) x := by
  rw [heckeVec, heckeVec, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : ∃ a ∈ KGL w (n := r), ∃ b ∈ KGL w (n := r), c.out = a * t * b
  · obtain ⟨a, ha, b, hb, e⟩ := id hc
    have h : ordDet c.out = ordDet t := by
      rw [e, ordDet_mul, ordDet_mul, ordDet_of_mem ha, ordDet_of_mem hb]
      simp
    rw [twistRep_apply, h, smul_comm]
  · rw [GlobalTheory.WeylGL.dosetInd_of_not hc]
    simp

theorem isSatVecGL_twistRep {ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (z : ℂˣ) : IsSatVecGL w (twistRep ρ z) x (B.map (z * ·)) := by
  refine ⟨hx.1, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
  · rw [twistRep_apply, ordDet_of_mem hk, zpow_zero, one_smul]
    exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk
  · have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
    have em : B.map (z * ·) = B.map (· * z) := Multiset.map_congr rfl fun b _ => mul_comm _ _
    have ho : ordDet (GlobalTheory.WeylGL.tor h0 fun i : Fin r => if (i : ℕ) < j then 1 else 0) = j := by
      rw [ordDet_of_diagonal hϖ (GlobalTheory.WeylGL.tor_val h0 _)]
      simp [Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right hj]
    rw [GlobalTheory.WeylGL.Tj_eq h0, heckeVec_twistRep, ← GlobalTheory.WeylGL.Tj_eq h0, hx.2.2.2 ϖ hϖ j hj, em,
      GlobalTheory.SphGal.satEig_map_mul, ho, zpow_natCast, smul_smul]

end Twist

theorem hasSum_twisted_hecke_eigenvalues : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ (z : ℂˣ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∀ c : (Fin r → ℤ) → ℂ, (∀ d, heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) x = c d • x) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac (B.map (z * ·)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B.map fun β => (z * β)⁻¹) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  intro hP E _ _ w r V _ _ ρ x B hx z ϖ hϖ T hT c hc
  have hc' : ∀ d, heckeVec (twistRep ρ z) (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) x =
      ((z : ℂ) ^ (∑ i, d i) * c d) • x := fun d => by
    rw [heckeVec_twistRep, hc d, ordDet_of_diagonal hϖ (hT d), smul_smul]
  obtain ⟨δ, h0, h⟩ := GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL hP E w r V (twistRep ρ z) x _ (isSatVecGL_twistRep hx z) ϖ hϖ T hT _ hc'
  refine ⟨δ, h0, fun X h1 h2 => ?_⟩
  have := h X h1 h2
  rw [Multiset.map_map] at this
  exact this

end GlobalTheory.FinZeta.GLTwist

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

variable {D : D7}

def chiS (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (c : EAf D) : ℂ :=
  X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g
    (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h).symm c))

theorem chiS_rfl (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (c : EAf D) :
    chiS X h c = X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g
      (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h).symm c)) := rfl

end GlobalTheory.SeeConjChar
end
end
