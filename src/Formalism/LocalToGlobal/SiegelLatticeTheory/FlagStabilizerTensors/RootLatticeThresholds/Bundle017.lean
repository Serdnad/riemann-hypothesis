module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle012
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem dcrel_of_heq {Λ₁ Λ₂ : Submodule (𝓞 E) S.V} (h : Λ₁ = Λ₂) {T T' : E} (F : LFlag S r T)
    (P : Submodule (𝓞 E) S.V → LFlag S r T' → Prop) (x : TermDef.Carrier (P Λ₁)) (y : TermDef.Carrier (P Λ₂))
    (he : HEq (TermDef.mk Λ₁ F (P Λ₁) x) (TermDef.mk Λ₂ F (P Λ₂) y)) : TermDef.DCRel Λ₂ F x.1 y.1 := by
  subst h
  have h2 : Quot.mk _ x = Quot.mk _ y := eq_of_heq he
  have h3 := Quot.eqvGen_exact h2
  clear he h2
  induction h3 with
  | rel a b hab => exact hab
  | refl a => apply Formalism.L2.SG.TermDef.dcrel_refl
  | symm a b _ ih => exact Formalism.L2.SG.Pf.dcrel_symm (h := ih)
  | trans a b c _ _ ih1 ih2 => exact Formalism.L2.SG.Pf.dcrel_trans (h := ih1) (h' := ih2)

theorem nlam_isom {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    n ∈ Formalism.HermitianLatticesTheory.isom S.hT := hn.1.1

theorem nlam_gmap {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    Formalism.HermitianLatticesTheory.gmap n Λ = Λ := hn.1.2

theorem gmap_inv_of {Λ : Submodule (𝓞 E) S.V} {g : S.V ≃ₗ[E] S.V} (h : Formalism.HermitianLatticesTheory.gmap g Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ = Λ := by
  have hinv : ∀ y : S.V, g⁻¹ (g y) = y := fun y => g.symm_apply_apply y
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.HermitianLatticesTheory.gmap g Λ := by rw [h]; exact hy
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    rw [hinv]
    exact hz
  · intro hx
    refine ⟨g x, ?_, hinv x⟩
    rw [← h]
    exact Submodule.mem_map_of_mem hx

end Gen

section Fib

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem frame_lf {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) :
    frame (lf D F0) a = F0.fvec a := rfl

theorem lin_isom (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1

theorem lin_gmap (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1

theorem frame_eq (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') : s.frame = Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u')) := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dite_eq_left (lin_isom s)]
  rfl

theorem frame_apply (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') (a : Fin (D.R.rS + 1)) : frame s.frame a = s.lin ((X.Fu u').fvec a) := by
  rw [frame_eq]
  show (Formalism.L2.SG.Saturated.mapFlag s.lin (lin_isom s) (lf D (X.Fu u')).fl).fvec a =
    s.lin ((lf D (X.Fu u')).fl.fvec a)
  generalize (lf D (X.Fu u')).fl = F
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, Formalism.L2.SG.Saturated.mapFlag]
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Formalism.L2.SG.Saturated.mapFlag]

theorem stabF_of_fix {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {c : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) : c ∈ stabF D F0 := by
  have he : ∀ i, c (F0.e i) = F0.e i := fun i => by
    have h1 := hfix i.castSucc
    simpa only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1
  refine ⟨hc, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    simp only [LinearEquiv.coe_coe, he]
  · have h1 := hfix (Fin.last _)
    simpa only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last] using h1

theorem fib_dec {s s' : _root_.Formalism.L2.SG.PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm) :
    s.lam = s'.lam ∧ ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s.lam' (lf D (X.Fu u')),
      ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V, c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
        Formalism.HermitianLatticesTheory.gmap c s'.lam' = s.lam' ∧ (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
        s'.lin = n * s.lin * ν * c := by

  have hmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), (f * g) x = f (g x) :=
    fun _ _ _ => rfl
  have hinv : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f⁻¹ (f x) = x :=
    fun f x => f.symm_apply_apply x
  have hinv' : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f (f⁻¹ x) = x :=
    fun f x => f.apply_symm_apply x
  have gmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V),
      Formalism.HermitianLatticesTheory.gmap (f * g) L = Formalism.HermitianLatticesTheory.gmap f (Formalism.HermitianLatticesTheory.gmap g L) := by
    intro f g L
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have gone : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
    intro L
    unfold Formalism.HermitianLatticesTheory.gmap
    exact Submodule.map_id L

  have h' := h
  unfold Formalism.L2.SG.TermOp.GTerm.toTerm at h'
  injection h' with h1 h3
  have hd : TermDef.DCRel s'.lam (lf D (X.Fu u)) s.frame s'.frame :=
    dcrel_of_heq h1 (lf D (X.Fu u)) (fun Λ => TermDef.PD D Λ (lf D (X.Fu u)) u')
      ⟨s.frame, s.rep.2.2.2.2⟩ ⟨s'.frame, s'.rep.2.2.2.2⟩ h3
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hd
  have hnL : n ∈ NLam s.lam (lf D (X.Fu u)) := by rw [h1]; exact hn

  have hm' : m ∈ NLam (Formalism.HermitianLatticesTheory.gmap s.lin s.lam')
      (Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u'))) := by
    rw [lin_gmap, h1, ← frame_eq]
    exact hm
  have hν : s.lin⁻¹ * m * s.lin ∈ NLam s.lam' (lf D (X.Fu u')) :=
    (Formalism.L2.SG.Pf.mem_NLam_map _ _ _ _ _).1 hm'
  have hback : Formalism.HermitianLatticesTheory.gmap s.lin⁻¹ s.lam = s.lam' := by
    rw [← lin_gmap s, ← gmul, inv_mul_cancel, gone]
  generalize hνdef : s.lin⁻¹ * m * s.lin = ν at hν
  refine ⟨h1, n, hnL, ν, hν, (n * s.lin * ν)⁻¹ * s'.lin,
    ?_, ?_, ?_, (mul_inv_cancel_left _ _).symm⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (nlam_isom hn) (lin_isom s)) (nlam_isom hν))) (lin_isom s')
  · rw [gmul, lin_gmap s', ← h1, mul_inv_rev (n * s.lin) ν, mul_inv_rev n s.lin, gmul, gmul, gmap_inv_of (nlam_gmap hnL),
      hback, gmap_inv_of (nlam_gmap hν)]
  · intro a
    have e1 := hfr a
    rw [frame_apply, frame_apply] at e1
    rw [hmul, e1]
    have e2 : n (m (s.lin ((X.Fu u').fvec a))) = (n * s.lin * ν) ((X.Fu u').fvec a) := by
      rw [← hνdef]
      simp only [hmul, hinv']
    rw [e2, hinv]

theorem lam'_eq {s s' : _root_.Formalism.L2.SG.PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm) : s.lam' = s'.lam' := by
  obtain ⟨-, n, -, ν, -, c, hc, hgc, hfix, -⟩ := fib_dec h
  have hstab : c ∈ stabF D (X.Fu u') := stabF_of_fix (X.Fu u') hc hfix
  have hone : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D (X.Fu u') :=
    stabF_of_fix (X.Fu u') (Subgroup.one_mem _) (fun _ => rfl)
  have hg1 : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) s.lam' = s.lam' := by
    unfold Formalism.HermitianLatticesTheory.gmap
    exact Submodule.map_id _
  have hR := Y.rowsOK u'
  obtain ⟨Λ0, -, huniq⟩ := hR.2 s.lam' (hR.1 _ s.mem')
  have e1 := huniq s.lam' ⟨s.mem', 1, hone, hg1⟩
  have e2 := huniq s'.lam' ⟨s'.mem', c, hstab, hgc⟩
  exact e1.trans e2.symm

theorem gterm_eq {s s' : _root_.Formalism.L2.SG.PackageTie2.TT Y u u'} (hl : s.lam = s'.lam) (hl' : s.lam' = s'.lam')
    (h : ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ n' ∈ NLam s.lam' (lf D (X.Fu u')), s'.lin = n * s.lin * n') : s = s' := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  rcases s with ⟨l, hm, l', hm', c⟩
  rcases s' with ⟨k, km, k', km', c'⟩
  simp only at hl hl'
  subst hl
  subst hl'
  have hc : c = c' :=
    (Quot.out_eq c).symm.trans ((Quot.sound ⟨n, hn, n', hn', hq⟩).trans (Quot.out_eq c'))
  subst hc
  rfl

end Fib

end Formalism.L2.SG.Pf.FibreCounting
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPf

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def IntNX (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : ℝ :=
  (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ /
            (((Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p) *
              (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP) *
    ((Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP * (IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D))

def LocRep (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) : Prop :=
  (∀ v, Measurable (L v) ∧ ∀ cv, 0 ≤ L v cv) ∧
    ∀ c ∈ Good X u u', ∀ v, hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = L v (c v)

def PlaceEnergy (P : Parts X u u') (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  ∀ v, Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v)) ≠ ⊤ ∧
    ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) =
      ENNReal.ofReal (K v * (Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))).toReal)

def ConstPin (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  (∀ v, 0 ≤ K v) ∧
    (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ /
              (((Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p) *
                (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP) *
      ((Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP * ((∏ v, K v) / Formalism.L2.SG.MassDataConc.kapN D)) =
      (P.Gam0 ^ P.S.f)⁻¹

end Formalism.L2.SG.Pf.Carrier.EnergyPf
end
end

section

noncomputable section
open scoped Classical InnerProductSpace ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf

section FinXN

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D} (Y : Full X)

theorem sharp_bij_of_neat (u : D.what₂.Word) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) :
    Function.Bijective (sharp Y.hK (Y.cs u)) := by
  have hst : Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u Y.hK) := hN
  let cls : (Y.cs u).Cl → Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) :=
    fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)
  have hcls : Function.Bijective cls := by
    refine ⟨fun ρ ρ' h => ?_, fun c => ?_⟩
    · obtain ⟨a, ⟨γ, rfl⟩, κ, hκ, hab⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
      obtain ⟨ρ0, _, huniq⟩ := Y.colReps u ((Y.cs u).h ρ')
      have h1 := huniq ρ ⟨γ, ⟨κ, hκ⟩, hab⟩
      have h2 := huniq ρ' ⟨1, 1, by simp⟩
      exact h1.trans h2.symm
    · induction c using Quotient.inductionOn' with
      | h g =>
        obtain ⟨ρ, ⟨γ, κ, hg⟩, _⟩ := Y.colReps u g
        refine ⟨ρ, ?_⟩
        show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ g
        rw [DoubleCoset.eq]
        exact ⟨iotaF X u γ, ⟨γ, rfl⟩, κ, κ.2, hg⟩
  let ec := Equiv.ofBijective cls hcls
  let s : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) → Hfin X u := fun c => (Y.cs u).h (ec.symm c)
  have hs : ∀ c, DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (s c) = c := fun c => ec.apply_symm_apply c
  obtain ⟨e, he⟩ := Formalism.L2.SG.ColsDim.columns_decomposition (Gam X u) (Hinf X u) (Hfin X u) ℂ (X.Vpi u) (iotaI X u)
    (iotaF X u) (Ku X u Y.hK) (psiK X u Y.hK) (piRep X u) s hs hst
  have key : ∀ T ρ, (sharp Y.hK (Y.cs u) T) ρ =
      (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap (e T (cls ρ))) := by
    intro T ρ
    have hsρ : s (cls ρ) = (Y.cs u).h ρ := by
      show (Y.cs u).h (ec.symm (ec ρ)) = _
      rw [ec.symm_apply_apply]
    show (InnerProductSpace.toDual ℂ (X.Vpi u)).symm
      (LinearMap.toContinuousLinearMap ((LinearMap.proj ((1 : Hinf X u), (Y.cs u).h ρ)).comp T.1)) = _
    congr 2
    refine LinearMap.ext fun ξ => ?_
    refine Eq.trans ?_ (he T (cls ρ) ξ).symm
    rw [hsρ]
    rfl
  refine ⟨fun T T' h => ?_, fun x => ?_⟩
  · apply e.injective
    funext c
    obtain ⟨ρ, rfl⟩ := hcls.2 c
    have h1 : (sharp Y.hK (Y.cs u) T) ρ = (sharp Y.hK (Y.cs u) T') ρ := by rw [h]
    rw [key T ρ, key T' ρ] at h1
    exact LinearMap.toContinuousLinearMap.injective ((InnerProductSpace.toDual ℂ (X.Vpi u)).symm.injective h1)
  · let d : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) → Module.Dual ℂ (X.Vpi u) :=
      fun c => LinearMap.toContinuousLinearMap.symm (InnerProductSpace.toDual ℂ (X.Vpi u) (x (ec.symm c)))
    refine ⟨e.symm d, ?_⟩
    ext ρ
    refine (key (e.symm d) ρ).trans ?_
    rw [e.apply_symm_apply]
    show (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.symm (InnerProductSpace.toDual ℂ (X.Vpi u) (x (ec.symm (ec ρ)))))) = x ρ
    rw [LinearEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply, ec.symm_apply_apply]

theorem finX_of_neat (hN : ∀ u, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) (hin : ∀ u, InHH X u Y.hK) (hfin : FiniteDimensional ℂ (HHX X))
    (hfib : ∀ u u' (t : RT Y u u'), Finite (fib Y t))
    (hpi : ∀ u u' (s₁ s₂ s₁' s₂' : _root_.Formalism.L2.SG.PackageTie2.TT Y u u'), s₁.toTerm = s₁'.toTerm → s₂.toTerm = s₂'.toTerm →
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ →
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁' = rowOf Y.TR (Y.cs u) (Y.cs u') s₂' →
      s0T s₁ s₂ = s0T s₁' s₂' ∧ (liftScalar s₁ s₂ ↔ liftScalar s₁' s₂')) (hG : ∀ u u' (t : RT Y u u'), t.G ∈ D.host.F)
    (hvol : VolPosC) : FinX Y :=
  { shInj := fun u => (sharp_bij_of_neat Y u (hN u)).1
    shSurj := fun u => (sharp_bij_of_neat Y u (hN u)).2
    inHH := hin
    puLin := fun u => Formalism.L2.SG.PoincareInHH.Cut.puLinear_holds X u Y.hK (Y.Dt u)
    finHH := hfin
    fibFin := hfib
    pairIndep := hpi
    Greal := hG
    cdEx := fun n ε => cd_haar_scaling D.cd n ε
    volPos := fun u => hvol D X Y u (Formalism.L2.SG.Closed.level_subgroup_properties X) }

end FinXN

end Formalism.L2.SG.Pf
end
end
