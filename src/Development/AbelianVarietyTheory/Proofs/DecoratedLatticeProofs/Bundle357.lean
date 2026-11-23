module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle242
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSlice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section
namespace GlobalTheory.FinPl.SplitPhi
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  have h := p.sec_pr 1
  rw [mul_one] at h
  rw [← h, p.pr_sec, map_one]

theorem prV_toEAf_e_ne (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.F)} (hw : w ≠ p.v) :
    Formalism.UG.prV (E := D.host.E) w (toEAf D p.e) = 0 := by
  obtain ⟨ε, hε, he⟩ := p.above
  obtain ⟨h1, h2, -⟩ := p.split
  have : p.e = algebraMap (AF D.host.F) (AE D) ε * p.e := by
    rw [← he, add_mul, h1, mul_comm (cA D p.e), h2, add_zero]
  rw [this]
  exact GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw _

theorem prV_toEAf_eps (p : SplitPt D k) {ε : AF D.host.F} (hε : IsPlaceIdem D p.v ε) :
    Formalism.UG.prV (E := D.host.E) p.v (toEAf D (algebraMap (AF D.host.F) (AE D) ε)) = 1 := by
  obtain ⟨α, rfl, h1, -⟩ := hε
  have h1' : (Formalism.UG.evalV D.host.F p.v) ((sndA D.host.F) (pairA D.host.F 0 α)) = 1 := h1
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [Formalism.IndefR.Datum.toEAf, finPart, Formalism.UG.prV]
  rw [h1']
  rfl

theorem prF_eq_zero (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (y : EAf D) (hy : Formalism.UG.prV (E := D.host.E) p.v y = 0) : p.prF he y = 0 := by
  have h0 : toEAf D p.e * y = 0 := by
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [hy, mul_zero]
    · rw [prV_toEAf_e_ne p hw, zero_mul]
  have : p.prF he y = p.prF he (toEAf D p.e * y) := by
    rw [map_mul, p.prF_toEAf he, pr_e, one_mul]
  rw [this, h0, map_zero]

theorem prF_IE_prV (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (y : EAf D) : p.prF he (Formalism.UG.P.afsplitIE p.v (Formalism.UG.prV (E := D.host.E) p.v y)) = p.prF he y := by
  rw [← sub_eq_zero, ← map_sub]
  apply prF_eq_zero p he
  rw [map_sub, Formalism.UG.P.afsplit_prV_IE, sub_self]

def phi (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) :
    D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k where
  toFun x := p.prF he (Formalism.UG.P.afsplitIE p.v x)
  map_one' := by
    have := prF_IE_prV p he 1
    rw [map_one (Formalism.UG.prV (E := D.host.E) p.v), map_one (p.prF he)] at this
    exact this
  map_mul' x y := by simp only [map_mul]
  map_zero' := by simp only [map_zero]
  map_add' x y := by simp only [map_add (f := _)]

theorem phi_apply (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (x : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F) :
    phi p he x = p.prF he (Formalism.UG.P.afsplitIE p.v x) := rfl

theorem phi_prV (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (a : AE D) : phi p he (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a := by
  rw [phi_apply, prF_IE_prV, p.prF_toEAf he]

theorem phi_inclE (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (c : D.host.E) : phi p he (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c) := by
  rw [← phi_prV p he]
  rfl

theorem tensInt_iff (v : HeightOneSpectrum (𝓞 D.host.F)) (z : D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    z ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
        (v.adicCompletionIntegers D.host.F).toSubring ↔
      Formalism.UG.P.afsplitIE v z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  refine ⟨Formalism.UG.P.afsplit_IE_int v z, fun h => ?_⟩
  have := Formalism.UG.P.afsplit_prV_int v _ h
  rwa [Formalism.UG.P.afsplit_prV_IE] at this

theorem sigR_sigR (z : EAf D) : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
    (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (· ⊗ₜ[D.host.F] x) (star_star a)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem toEAf_cA (a : AE D) : toEAf D (cA D a) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul y e => rfl

theorem sigR_mem_iff (s : EAf D) : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈
    Formalism.L2.Herm.intAf D.host.F D.host.E ↔ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  refine ⟨fun h => ?_, GlobalTheory.LevSplit.sigR_int⟩
  have := GlobalTheory.LevSplit.sigR_int h
  rwa [sigR_sigR] at this

theorem one_sub_e_mul (p : SplitPt D k) (y : EAf D)
    (hy : ∀ w, w ≠ p.v → Formalism.UG.prV (E := D.host.E) w y = 0) :
    (1 - toEAf D p.e) * y = toEAf D (cA D p.e) * y := by
  obtain ⟨ε, hε, he⟩ := p.above
  rw [← sub_eq_zero, ← sub_mul, sub_sub, ← RingHom.map_add (f := _), he]
  refine Formalism.UG.P.afsplit_inj _ fun w => ?_
  rw [map_mul]
  by_cases hw : w = p.v
  · subst hw; rw [map_sub, map_one, prV_toEAf_eps p hε, sub_self, zero_mul]
  · rw [hy w hw, mul_zero]

theorem sigR_inclE (v : HeightOneSpectrum (𝓞 D.host.F)) (c : D.host.E) :
    Formalism.UG.sigR (sigD D) (v.adicCompletion D.host.F) (Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) c) =
      Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) (sigD D c) := by
  simp only [Formalism.UG.sigR, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

theorem exists_ringHom_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∃ φ : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k,
      (∀ a : AE D, φ (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a) ∧
      (∀ c : D.host.E, φ (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c)) ∧
      (∀ c : D.host.E, φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F)
          (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c)) = p.pr (incA D (sigD D c))) ∧
      ∀ z, z ∈ Formalism.UG.tensInt (F := D.host.F) (p.v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
          (p.v.adicCompletionIntegers D.host.F).toSubring ↔
        φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) ∈ 𝒪[k] := by
  intro D k _ _ _ _ p PP he
  refine ⟨phi p he, phi_prV p he, phi_inclE p he, fun c => by rw [sigR_inclE]; exact phi_inclE p he (sigD D c), fun z => ?_⟩
  set y := Formalism.UG.P.afsplitIE p.v z with hy
  have hsup : ∀ w, w ≠ p.v → Formalism.UG.prV (E := D.host.E) w y = 0 := fun w hw =>
    Formalism.UG.P.afsplit_prV_IE_ne p.v w hw z
  have hsig : Formalism.UG.P.afsplitIE p.v (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y := by
    rw [hy]; exact (Formalism.UG.P.afsplit_sigR_IE (sigD D) p.v z).symm
  have h1 := tensInt_iff p.v z
  have h2 := p.mem_intAf_iff he y
  have h3 := one_sub_e_mul p y hsup
  have h4 := p.prF_mem_iff he (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y)
  have h5 : toEAf D (cA D p.e) * y = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
      (toEAf D p.e * Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y) := by
    rw [RingHom.map_mul, sigR_sigR, toEAf_cA]
  refine h1.trans (h2.trans ?_)
  rw [h3, h5, sigR_mem_iff, ← h4]
  have e1 : phi p he z = p.prF he y := phi_apply p he z
  have e2 : phi p he (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) =
      p.prF he (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y) := (phi_apply p he _).trans (congrArg _ hsig)
  rw [e1, e2]
  exact and_comm

end GlobalTheory.FinPl.SplitPhi
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def boxL (c : SB (Matrix n Unit k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := box Ξ c
  map_add' Ξ Ξ' := Subtype.ext (funext fun x => by simp [box, splitCols, add_mul])
  map_smul' a Ξ := Subtype.ext (funext fun x => by simp [box, splitCols]; ring)

theorem heis_slice_left {S A L T : HSp D} (d : OrthDec S A L) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (u u' : WO A T) (w : WO L T) :
    heisO ψ S T ((d.resS T).symm (u', 0)) f ((d.resS T).symm (u, w)) =
      heisO ψ A T u' (fun u => f ((d.resS T).symm (u, w))) u := by
  simp only [heisO]
  rw [d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem isHalf_slice_left {S A L T : HSp D} (d : OrthDec S A L) {a : AE D} {y : WO A T} (hy : IsHalf a y) :
    IsHalf a ((d.resS T).symm (y, 0)) := by
  intro i j
  rw [resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hy i l]

end GlobalTheory.SliceLeft

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem up_fromCols_left (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (x : Matrix n n' k) :
    p.up F₀ FS (fromCols x 0) = (B.o.resS S).symm (p.up FA FS x, 0) := by
  have k1 : x * FA.γ * B.o.qA.map (p.π.comp (incA D)) * F₀.β = fromCols x (0 : Matrix n Unit k) := by
    rw [beta_eq p h hL, Matrix.mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.o.qA.map _) (B.o.iA.map _), ← Matrix.map_mul, B.o.qA_iA,
      ← Matrix.mul_assoc (B.o.qA.map _) (B.o.iB.map _), ← Matrix.map_mul, B.o.qA_iB]
    simp [FA.γβ]
  have k2 : fromCols x (0 : Matrix n Unit k) * F₀.γ = x * FA.γ * B.o.qA.map (p.π.comp (incA D)) := by
    rw [← k1, Matrix.mul_assoc (x * FA.γ * B.o.qA.map (p.π.comp (incA D))) F₀.β F₀.γ, F₀.βγ, Matrix.mul_one]
  rw [resS_symm_apply, Matrix.zero_mul, add_zero]
  unfold Place.up
  rw [pA, map_ι_mul, rat_map_π]
  congr 1
  rw [Matrix.mul_assoc FS.β (fromCols x 0) F₀.γ, k2]
  simp only [Matrix.mul_assoc]

theorem resS_up_fst (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (t : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS t)).1 = p.up FA FS t.toCols₁ := by
  have k1 : t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) * FA.β = t.toCols₁ := by
    calc t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) * FA.β
        = ((t * F₀.γ) * fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β)
            (B.o.iB.map (p.π.comp (incA D)) * FL.β)).toCols₁ := by
          rw [Matrix.mul_fromCols, toCols₁_fromCols, Matrix.mul_assoc (t * F₀.γ)]
      _ = ((t * F₀.γ) * F₀.β).toCols₁ := by rw [← beta_eq p h hL]
      _ = t.toCols₁ := by rw [Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
  have k2 : t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) = t.toCols₁ * FA.γ := by
    rw [← k1, Matrix.mul_assoc (t * F₀.γ * B.o.iA.map (p.π.comp (incA D))) FA.β FA.γ, FA.βγ, Matrix.mul_one]
  rw [resS_apply]
  dsimp only
  unfold Place.up
  rw [jA, map_ι_mul, rat_map_π]
  simp only [Matrix.mul_assoc] at k2 ⊢
  rw [k2]

end GlobalTheory.SliceLeft

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

theorem toCols_add_left {k n n' : Type} [Field k] (t : Matrix n (n' ⊕ Unit) k) (x : Matrix n n' k) :
    (t + fromCols x (0 : Matrix n Unit k)).toCols₁ = t.toCols₁ + x ∧
      (t + fromCols x (0 : Matrix n Unit k)).toCols₂ = t.toCols₂ :=
  ⟨by ext i j; simp, by ext i j; simp⟩

theorem slice_left : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (c : SB (Matrix n Unit k)) (w₀ : WO B.L S), ∃ T', p.IsModel ψ FA FS T' ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ u, T' Ξ u = T₀ Ψ ((B.o.resS S).symm (u, w₀)) := by
  intro D k _ _ _ _ p ψ ρ B S s n n' _ _ _ _ FA F₀ FS h T₀ hT c w₀
  obtain ⟨FL, hFL, -⟩ := slice_line D k p ψ ρ B S s n n' FA F₀ FS h T₀ hT
  let T' : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun u : WO B.A S => (B.o.resS S).symm (u, w₀))).comp (T₀.comp (boxL c))
  have hT' : ∀ Ξ u, T' Ξ u = T₀ (box Ξ c) ((B.o.resS S).symm (u, w₀)) := fun _ _ => rfl
  refine ⟨T', ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_left B.o (hT.theta (box Φ c)) w₀
  · have e := hT.trans (fromCols x 0) (box Φ c) (box Φ' c) (fun t => by
      rw [box_apply, box_apply, hΦ, (toCols_add_left t x).1, (toCols_add_left t x).2])
    funext u
    rw [hT', e, up_fromCols_left p h hFL, heis_slice_left]
    rfl
  · have e := hT.modul ((B.o.resS S).symm (y, 0)) (isHalf_slice_left B.o hy) (box Φ c) (box Φ' c) (fun t => by
      simp only [box_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, resS_up_fst p h hFL, symplO_zero_right',
        add_zero]
      ring)
    funext u
    rw [hT', e, heis_slice_left]
    rfl
  · have e : Ψ = box Ξ c := Subtype.ext (funext fun x => by rw [hΨ, box_apply]; rfl)
    rw [hT', e]

end GlobalTheory.SliceLeft
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAtPlaceSrc

open GlobalTheory.WeilAtPlace GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {lam : ℕ →* ℂ} {w₀ : 𝓞 D.host.E} {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}

theorem weilDatum_source_eq_scalar_smul_latticeIntertwiner (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hlam : GoodNorm (sgO D) lam) {g : GA D S} (hg : g ∈ GfC S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f (hf : IsThetaFunO ψ S T f), om (g, 1) f = c • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ) := by
  obtain ⟨o, ho⟩ := exists_extend (thetaSub ψ S T) Om
  have ho' : ∀ p f (hf : IsThetaFunO ψ S T f), o p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => ho p ⟨f, hf⟩
  have hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (o p f) := fun p f hf => by
    rw [ho' p f hf]
    exact (Om p ⟨f, hf⟩).2
  have hheis : ∀ (g' : GA D S) (k' : GA D T), g' ∈ GfC S → k' ∈ GfC T → ∀ u f, IsThetaFunO ψ S T f →
      o (g', k') (heisO ψ S T u f) = heisO ψ S T (actO S T g' k' u) (o (g', k') f) := by
    intro g' k' hg' hk' u f hf
    obtain ⟨f', h1, h2⟩ := hL.Heisenberg₂ hψ hg' hk' u ⟨f, hf⟩
    rw [ho' _ f hf, ← h2, ← h1]
    exact ho _ f'
  obtain ⟨c, hc, h⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ S T (om (g, 1) * o (g⁻¹, 1⁻¹))
    (fun f hf => hW.om_pres _ _ (hpres _ _ hf))
    (fun u f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hheis _ _ (inv_mem hg) (inv_mem (one_mem _)) u f hf,
        hW.om_heis _ _ _ _ (hpres _ _ hf), GlobalTheory.FinWeilForm.actO_actO_inv])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hpres _ _ hf), ho' _ f hf,
        hL.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, hf⟩])
  refine ⟨c, hc, fun f hf => ?_⟩
  have h1 := h _ (hpres (g, 1) f hf)
  rw [Module.End.mul_apply, ← Module.End.mul_apply (o _), ← map_mul,
    show ((g⁻¹, 1⁻¹) * (g, 1) : GA D S × GA D T) = 1 from inv_mul_cancel (g, (1 : GA D T)), map_one,
    Module.End.one_apply] at h1
  rw [h1, ho' _ f hf]

theorem exists_weilScalarCharacter_sourceFinitePart (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hlam : GoodNorm (sgO D) lam) :
    ∃ ν : GA D S →* Circle, ∀ g ∈ GfC S, ∀ f (hf : IsThetaFunO ψ S T f),
      om (g, 1) f = (ν g : ℂ) • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ) := by
  have hs := fun g : GA D S => weilDatum_source_eq_scalar_smul_latticeIntertwiner hψ hW hL hlam (pFin_mem S g)
  choose c hc h using hs
  obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hne : ∀ p, (Om p ⟨f, hf⟩ : WO S T → ℂ) ≠ 0 := fun p h0 => f0 (by
    have h1 : Om p ⟨f, hf⟩ = 0 := Subtype.ext h0
    have h2 := congrArg (Om p⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at h2
    exact congrArg Subtype.val h2)
  refine ⟨MonoidHom.mk' (fun g => ⟨c g, mem_sphere_zero_iff_norm.2 (hc g)⟩) fun p q => Circle.ext ?_,
    fun g hg f hf => ?_⟩
  · show c (p * q) = c p * c q
    have e1 : (pFin S (p * q), (1 : GA D T)) = (pFin S p, 1) * (pFin S q, 1) :=
      Prod.ext (map_mul _ _ _) (one_mul _).symm
    have e2 := h (p * q) f hf
    rw [e1, map_mul, Module.End.mul_apply, h q f hf, map_smul, h p _ (Om (pFin S q, 1) ⟨f, hf⟩).2, smul_smul, map_mul,
      Module.End.mul_apply] at e2
    have e3 := smul_left_injective ℂ (hne ((pFin S p, 1) * (pFin S q, 1))) (a₁ := c q * c p) (a₂ := c (p * q)) (by
      simpa only [map_mul, Module.End.mul_apply] using e2)
    rw [← e3, mul_comm]
  · have e := h g f hf
    rwa [pFin_of_mem hg] at e

theorem weilScalar_source_eq_one_nonsplit_unramified (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om) {ν : GA D S →* Circle}
    (hν : ∀ g ∈ GfC S, ∀ f (hf : IsThetaFunO ψ S T f), om (g, 1) f = (ν g : ℂ) • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ))
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hv : NonSplitAt D v ε) (uS : UnramAt ε χS)
    (uT : UnramAt ε χT) {g : GA D S} (hg : SuppPl ε S g) : ν g = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  refine GlobalTheory.T.adelic_unitary_character_trivial_at_nonsplit_place D S ΛS hS v ε hv ν (fun k hk hst => ?_) g hg
  have hvac' : ∃ f, f ≠ 0 ∧ IsThetaFunO ψ S T f ∧ ∀ v η, NonSplitAt D v η →
      ∀ u ∈ (latO S T ΛS ΛT fun w => w = v), heisO ψ S T u f = f := by
    obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
    obtain ⟨e, he, e0⟩ : ∃ e, Fixes (opF hψ.1 S T w₀) (latF S T ΛS ΛT) e ∧ e ≠ 0 := by
      by_contra hn
      push_neg at hn
      have : (⊤ : Submodule ℂ (thetaSub ψ S T)) ≤ ⊥ := by
        rw [← hL.span, Submodule.span_le]
        rintro _ ⟨x, e, he, rfl⟩
        rw [hn e he, map_zero]
        exact zero_mem _
      exact f0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 (this (Submodule.mem_top (x := ⟨f, hf⟩)))))
    refine ⟨e, fun h0 => e0 (Subtype.ext h0), e.2, fun v η hv u hu => ?_⟩
    obtain ⟨b, hb, hb'⟩ := exists_half_of_nonSplit hv
    have hu' := GlobalTheory.PlaceModel.latO_le_top _ hu
    let a : XF S T := XF.mk u (GlobalTheory.SplitScalar.latO_fin hu')
    have ha : a ∈ latF S T ΛS ΛT := hu'
    have e0 : algebraMap (AF D.host.F) (AE D) η • u = u :=
      GlobalTheory.FinWeilForm.placeIdem_smul_self hv.1 hu
    have e1 : a = 2 • (b • a) := by
      rw [two_nsmul, ← add_smul, ← two_mul, hb']
      exact XF.ext e0.symm
    have e2 : b • a ∈ latF S T ΛS ΛT := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b hb _ ha
    have h1 := congrArg Subtype.val (he a ha)
    rw [coe_opF] at h1
    have h2 : phase ψ w₀ a = 1 := by rw [e1]; exact phase_two hL.sd w₀ e2
    rwa [h2, one_smul] at h1
  obtain ⟨f₀, f0, hf₀, hvac⟩ := hvac'
  have hfix := hvac v ε hv
  have hst' := GlobalTheory.T.mem_localHomLattice_of_keeps_completedLattices D S T ΛS ΛT hS hT v ε hv.1 k 1 hst
    (fun y => by rw [GlobalTheory.FinWeilForm.finMat_one, Matrix.one_mulVec])
  have s1 : SuppPl ε T (1 : GA D T) := fun i j => by
    rw [GlobalTheory.FinWeilO.mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have a := GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hψ S T ΛS ΛT hS hT χS χT om
    ((GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩) hW v ε hv uS uT k 1 hk s1 hst'
    f₀ hf₀ hfix
  have b := hL.inert hv hk s1 (fun u hu => (hst' u).1 hu) ⟨f₀, hf₀⟩ hfix
  have hkf : k ∈ GfC S := GlobalTheory.IdemSupport.mem_GfC_of_suppF S (GlobalTheory.IdemSupport.place_comp hΦ hv.1).1 hk
  have c := hν k hkf f₀ hf₀
  rw [a, b] at c
  exact Circle.ext (smul_left_injective ℂ f0 (c.symm.trans (one_smul ℂ f₀).symm))

end GlobalTheory.WeilAtPlaceSrc

end

theorem GlobalTheory.WeilAtPlaceSrc.weilDatum_src_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ (a : Gv S v) (f : GlobalTheory.FinWeilO.thetaSub ψ S T), om (embV S v a, 1) f = (Om (embV S v a, 1) f : WO S T → ℂ) := by
  intro D ψ S T χS χT om hW hψ lam w₀ Om hL hlam v w h hi uS uT a f
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨ν, hν⟩ := GlobalTheory.WeilAtPlaceSrc.exists_weilScalarCharacter_sourceFinitePart hψ hW hL hlam
  obtain ⟨ε, hns, hp⟩ := GlobalTheory.WeilAtPlace.exists_nonSplit_of_inert hi h
  have hsu : GlobalTheory.WeilParts.SuppPl ε S (embV S v a) := (Supp.suppF_iff_of_isPrimeIdem S hp h _).2 ⟨a, rfl⟩
  have hk : embV S v a ∈ GfC S :=
    GlobalTheory.IdemSupport.mem_GfC_of_suppF S (GlobalTheory.IdemSupport.place_comp hΦ hns.1).1 hsu
  have e1 := GlobalTheory.WeilAtPlaceSrc.weilScalar_source_eq_one_nonsplit_unramified hψ hW (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat S)
    (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat T) hL hν hns
    (GlobalTheory.WeilAtPlace.unramAt_of_unrAt hp uS) (GlobalTheory.WeilAtPlace.unramAt_of_unrAt hp uT) hsu
  have e2 := hν _ hk f.1 f.2
  rw [e1, Circle.coe_one, one_smul] at e2
  exact e2
end
