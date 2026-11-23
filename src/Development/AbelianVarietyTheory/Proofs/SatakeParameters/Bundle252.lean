module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle247
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle199
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle170
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle219
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperator
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle238
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

namespace GlobalTheory.FinTypSpanLoc

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS π.S s τ → ∀ (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → π.S ≤ ⨆ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  intro L _ _ _ n π s τ hloc c hc hcL
  obtain ⟨i, T0, hi, hiL, hT0inj, hT0S, hT0eq⟩ := hloc

  have hci : c = i := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (c : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i := by
      refine hd.equalizer hc hi (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hcL, hiL]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hrt : ∀ (h h' : GAf L n) (f : GAf L n → ℂ), NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
    intro h h' f; funext g; simp [NG.rt, mul_assoc]
  have hnt : Nontrivial τ.V := by
    haveI := τ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation τ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  let Good : (τ.V →ₗ[ℂ] (GAf L n → ℂ)) → Prop := fun T =>
    (∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) ∧
      ∀ u, T u ∈ π.S
  let Wd : Submodule ℂ (GAf L n → ℂ) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS : Wd ≤ π.S := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
    refine iSup_le fun T => ?_
    exact le_iSup₂_of_le (f := fun (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)) => LinearMap.range T)
      T.1 ⟨T.2.2, T.2.1⟩ le_rfl

  have htr : ∀ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => π.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, hrt, hrt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, hrt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add (f := _)]; exact Submodule.add_mem _ h₁ h₂
  have hT0 : Good T0 := ⟨hT0eq, hT0S⟩
  rcases π.irr Wd hWdS hstab with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : τ.V)
    have hmem : T0 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T0, hT0⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hu (hT0inj (hmem.trans (map_zero T0).symm))
  · intro f hf
    rw [← h0] at hf
    exact hWdle hf

end GlobalTheory.FinTypSpanLoc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

namespace GlobalTheory.ThetaRiesz

theorem thetaPair_of_invariant_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsAdmissible σ → IsUnitarisable σ → IsOpen (μ.ker : Set kˣ) → ∀ (b : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), b ≠ 0 → (∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)), (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ a c, b Φ' (π h a) (σ g c) = b Φ a c) → ThetaPair μ σ π := by
  intro k _ _ _ _ r n V W _ _ _ _ μ σ π hadm hunit hμ b hb hb_inv
  obtain ⟨Bf, hsym, hpos, hinv⟩ := hunit
  obtain ⟨hone, hmul, -, -, hop⟩ := om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ

  have huniq : ∀ u u' : V, (∀ w, Bf u w = Bf u' w) → u = u' := by
    intro u u' h
    by_contra hne
    have hne' : u - u' ≠ 0 := sub_ne_zero.2 hne
    have hfun : Bf (u - u') = 0 := by rw [map_sub, LinearMap.ext h, sub_self]
    have h0 : Bf (u - u') (u - u') = 0 := by rw [hfun, LinearMap.zero_apply]
    have := hpos _ hne'
    rw [h0] at this
    simp at this

  let S : SB (Matrix (Fin n) (Fin r) k) → Subgroup (GL (Fin r) k) := fun Φ =>
    { carrier := {g | om μ g 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ}
      one_mem' := hone _
      mul_mem' := by
        intro x y hx hy
        show om μ (x * y) 1 _ = _
        have := hmul x y 1 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ)
        rw [mul_one] at this
        rw [this]
        have hy' : om μ y 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hy
        have hx' : om μ x 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hx
        rw [hy', hx']
      inv_mem' := by
        intro x hx
        have hx' : om μ x 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hx
        show om μ x⁻¹ 1 _ = _
        have := hmul x⁻¹ x 1 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ)
        rw [inv_mul_cancel, mul_one, hx', hone] at this
        exact this.symm }
  have hSo : ∀ Φ, IsOpen ((S Φ : Subgroup _) : Set (GL (Fin r) k)) := by
    intro Φ
    have h1 := hop _ Φ.2
    have hc : Continuous (fun g : GL (Fin r) k => (g, (1 : GL (Fin n) k))) :=
      continuous_id.prodMk continuous_const
    exact h1.preimage hc
  have hL : ∀ Φ a, ∀ s ∈ S Φ, ∀ w, b Φ a (σ s w) = b Φ a w := by
    intro Φ a s hs w
    have hs' : om μ s 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hs
    have := hb_inv s 1 Φ Φ hs'.symm a w
    simpa using this
  have hex : ∀ Φ a, ∃ u : V, ∀ w, b Φ a w = Bf u w := fun Φ a =>
    exists_vector_of_smooth_antilinear k r V σ Bf hadm hsym hpos hinv (b Φ a) (S Φ) (hSo Φ) (hL Φ a)
  choose f hf using hex
  have hadd1 : ∀ Φ Ψ a, f (Φ + Ψ) a = f Φ a + f Ψ a := fun Φ Ψ a =>
    huniq _ _ fun w => by rw [← hf, map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hf, hf, map_add (f := _), LinearMap.add_apply]
  have hsmul1 : ∀ (z : ℂ) Φ a, f (z • Φ) a = z • f Φ a := fun z Φ a =>
    huniq _ _ fun w => by rw [← hf, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hf, map_smul, LinearMap.smul_apply]
  have hadd2 : ∀ Φ a a', f Φ (a + a') = f Φ a + f Φ a' := fun Φ a a' =>
    huniq _ _ fun w => by rw [← hf, map_add (f := _), LinearMap.add_apply, hf, hf, map_add (f := _), LinearMap.add_apply]
  have hsmul2 : ∀ (z : ℂ) Φ a, f Φ (z • a) = z • f Φ a := fun z Φ a =>
    huniq _ _ fun w => by rw [← hf, map_smul, LinearMap.smul_apply, hf, map_smul, LinearMap.smul_apply]
  let B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V :=
    LinearMap.mk₂ ℂ f hadd1 hsmul1 hadd2 hsmul2
  have hB : ∀ Φ a, B Φ a = f Φ a := fun _ _ => rfl
  refine ⟨B, ?_, ?_⟩
  · intro h0
    apply hb
    ext Φ a w
    rw [hf, ← hB, h0]
    simp
  · intro g h Φ Φ' hΦ F
    rw [hB, hB]
    apply huniq
    intro c
    have hc : σ g (σ g⁻¹ c) = c := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [← hf, ← hc, hb_inv g h Φ Φ' hΦ F, hf, ← hinv g (f Φ F) (σ g⁻¹ c)]

end GlobalTheory.ThetaRiesz
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.IneUnrTwist

open Formalism.MainNotions Formalism.ConjugateSelfDual GlobalTheory.WeilDeligne ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct

theorem wd_inePol_twist {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w} (a χ : WD h) (h1 : χ.lpDim = 1)
    (hu : χ.unr) {s : G E Ω} (hs : s ∈ Ine (F := E) B) : (a.lpChar χ).inePol s = a.inePol s := by
  induction a using WD.ind with | hP n a => ?_
  induction χ using WD.ind with | hP m c => ?_
  rw [WD.lpDim_mk] at h1
  rw [WD.unr_mk] at hu
  rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hs, WD.inePol_of_mem_Ine _ hs, WD.charPol_mk, WD.charPol_mk,
    WDRep.tensor_ρ, hu.2]
  let e : (Fin m → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by simpa using h1)
  let E' := (TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) e).trans (TensorProduct.rid ℂ _)
  rw [← LinearEquiv.charpoly_conj E']
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [E', LinearEquiv.conj_apply]

theorem main : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → IneUnr D := fun D T w a χ h1 hu s hs => by
  rw [T.inePol w _ s hs, T.inePol w _ s hs, T.char w a χ h1]
  exact wd_inePol_twist _ _ ((T.dim w χ).trans h1) ((T.unr w χ).1 hu) hs

end GlobalTheory.IneUnrTwist
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.frobeniusConjugation_conditions_adaptedKernelDatum : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  first | exact @GlobalTheory.Ggeo.frobeniusConjugation_conditions_adaptedKernelDatum_alt | exact GlobalTheory.Ggeo.frobeniusConjugation_conditions_adaptedKernelDatum_alt | (intros; apply GlobalTheory.Ggeo.frobeniusConjugation_conditions_adaptedKernelDatum_alt <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.AdmEntInt

theorem mod_three_eq_two_of_jacobiSym_neg_eq_one (d : ℕ) (h : jacobiSym (-(d : ℤ)) 3 = 1) : d % 3 = 2 := by
  rw [jacobiSym.mod_left] at h
  simp only [Nat.cast_ofNat] at h
  have : (-(d : ℤ)) % 3 = 0 ∨ (-(d : ℤ)) % 3 = 1 ∨ (-(d : ℤ)) % 3 = 2 := by omega
  rcases this with h0 | h0 | h0 <;> rw [h0] at h
  · norm_num at h
  · omega
  · norm_num at h

end GlobalTheory.Ggeo.AdmEntInt

theorem GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hHyp h3 ep be sg
  intro u μ w hlf hd i hi _heven c c'
  have hlf' : LevFree Y u μ w := hlf
  obtain ⟨hAdm, hComb⟩ := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hHyp u μ w hlf' i hi c c'
  have hd3 : D.what₂.places.resChar w = 3 → D.host.d % 3 = 2 := fun _ =>
    GlobalTheory.Ggeo.AdmEntInt.mod_three_eq_two_of_jacobiSym_neg_eq_one _ (D.host.split_small 3 Nat.prime_three (by norm_num) h3)
  have hJ := GlobalTheory.T.integralJets_normalisedThetaCombinations_away_d hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hAdm
    (D.what₂.places.resChar w) (t.ent.lam w) hd hd3 _ hComb
  let T := t.kf u μ w hlf'
  have hB := T.B_bas i hi.le c
  have hB' := T.B_bas (i + 1) hi c'
  have hK := GlobalTheory.T.integral_jets_realPlace_local_bases D (t.O u μ).dgen (t.O u μ).dgen_gen _ _ _ _ hAdm (D.what₂.places.resChar w) (t.ent.lam w)
    (T.B i c) (T.B (i + 1) c') (fun τ => T.c0 i c c' τ * TaylorLogMetric.lamC (t.ent.lam w) ((t.O u μ).dgen τ)) hB hB'
    (fun τ => by rw [norm_mul, T.unitAbs_eq_one, one_mul]) _ hJ
  rw [← T.th i hi c c'] at hK
  exact GlobalTheory.T.kvalGe_zero_of_integral_jets _ _ _ _ _ _ hK
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.ChainE

variable {D : D7}

theorem mult_level {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (U : MMap M) (hU : U ∈ Mult θ M J χ) (v : M.Vec) : ∀ k ∈ J, ∀ g, U v (g * k) = χ k * U v g := by
  intro k hk g
  induction hU using Submodule.span_induction with
  | mem x hx => exact hx.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy => simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy, mul_add]
  | smul a x _ hx => simp only [MultilinearMap.smul_apply, Pi.smul_apply, hx, smul_eq_mul, mul_left_comm]

theorem natCast_pow_notMem (P : Pl D.host.E) {n : ℕ} (h : ((n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (c : ℕ) :
    ((n ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h' =>
  h (P.isPrime.mem_of_pow_mem c (by rwa [Nat.cast_pow] at h'))

theorem gaL_comm {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (H : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (Φ : GA D V → ℂ)
    (h : ∀ g0 : G0 L.Pg L.r, actG0 V β L g0 (H Φ) = H (actG0 V β L g0 Φ)) :
    gaL V β L eG c (H Φ) = H (gaL V β L eG c Φ) := by
  unfold gaL

  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  exact congrArg (c g • ·) (h (eG g))

section Chain

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem dnFrom_hk (t : T) (P : Pl D.host.E) (cs : ℕ → List ℤ →₀ ℂ)
    (hs : ∀ k, k + 1 < D.R.m → ∀ U U' : R.CC t (k + 1), (∀ v, U'.1 v = hk _ P (cs (k + 1)) (U.1 v)) →
      ∀ v, (R.ioY t k U').1 v = hk _ P (cs k) ((R.ioY t k U).1 v))
    (n : ℕ) (hn : n < D.R.m) (U U' : R.CC t n) (hU : ∀ v, U'.1 v = hk _ P (cs n) (U.1 v)) :
    ∀ v, (Lift.dnFrom (R.CC t) (R.ioY t) n U').1 v = hk _ P (cs 0) ((Lift.dnFrom (R.CC t) (R.ioY t) n U).1 v) := by
  induction n with
  | zero => exact hU
  | succ k ih => exact ih (by omega) (R.ioY t k U) (R.ioY t k U') (hs k hn U U' hU)

noncomputable def liftCC (t : T) (y : (R.HX t).H) : R.CC t 0 :=
  Lift.dnFrom (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y))

theorem thDn_eq (t : T) (y : (R.HX t).H) : R.thDn t y = (liftCC t y).1 := rfl

theorem e_Th (hT : R.chain_Th) (t : T) (x : (R.HX t).H) (v : (R.MY 0).Vec) : R.HE.e (R.Th t x) v =
    R.e0 ((liftCC t x).1 (PiTensorProduct.tprod ℂ v)) := by
  rw [hT t x, postOn_apply, thDn_eq t x]
  rfl

theorem compositeLift_relation_passes_to_rows (F : Face D A) (hl : R.toLevCh.Is A.μ0) (t : T) (P : Pl D.host.E) (hP : Good R t P) (c : List ℤ →₀ ℂ) (U : R.CC t 0)
    (v : (R.MY 0).Vec) :
    R.e0 (hk _ P c (U.1 (PiTensorProduct.tprod ℂ v))) = hk _ P c (R.e0 (U.1 (PiTensorProduct.tprod ℂ v))) := by
  obtain ⟨n, hn⟩ := hl.βY 0 (by have := D.R.two_le_m; omega)
  have hN := natCast_pow_notMem P ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hl).2.1 t P hP).1 n
  have h1 := (GlobalTheory.T.level_operators_at_prime_off_level_datum _ _ _ _ (R.datYt t 0 R.triv) hn P hN hP).1
  have h2 := (GlobalTheory.T.level_operators_at_prime_off_level_datum _ _ _ _ (R.dat0 R.triv) hn P hN fun PP h =>
    hP PP (Or.inl (h.resolve_right (Finset.notMem_empty PP)))).2.2.2.1
  have h3 := mult_level _ _ _ _ _ ((mem_multT R.θ (R.MY 0) _ _ _).1 U.2) v
  refine gaL_comm _ _ _ _ _ _ _ fun g0 => h2 c g0 _ fun k hk h => ?_
  have h4 := h3 k (h1 k hk).1 h
  rw [(h1 k hk).2, one_mul] at h4
  exact h4

theorem e_Th_hk (F : Face D A) (hl : R.toLevCh.Is A.μ0) (hT : R.chain_Th) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (c : List ℤ →₀ ℂ) (y y' : (R.HX t).H) (h : ∀ v, (liftCC t y').1 v = hk _ P c ((liftCC t y).1 v)) :
    R.HE.e (R.Th t y') = postOn (R.MY 0) (hk (Yc D 0) P c) (R.HE.e (R.Th t y)) := by
  refine MultilinearMap.ext fun v => ?_
  exact ((e_Th hT t y' v).trans ((congrArg R.e0 (h _)).trans (compositeLift_relation_passes_to_rows F hl t P hP c (liftCC t y) v))).trans
    ((postOn_apply _ _ _ v).trans (congrArg (hk (Yc D 0) P c) (e_Th hT t y v))).symm

end Chain

theorem matchE_of_chain : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P, Good R t P → FixAll R t P → ∀ (cX : List ℤ →₀ ℂ) (cs : ℕ → List ℤ →₀ ℂ), Match R.ψ (R.ωX t) P (cs (D.R.m - 1)) (dualC cX) → (∀ k, k + 1 < D.R.m → Match R.ψ (R.ωY t k) P (cs k) (dualC (cs (k + 1)))) → MatchE R t P cX (cs 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hI hC hS t P hP hF cX cs hX hY y y' hy
  refine e_Th_hk F hC.lev hC.chain.Th t P hP (cs 0) y y' ?_
  exact dnFrom_hk t P cs (fun k hk => GlobalTheory.T.chainInnerStep_intertwines_matchedHecke R F hI hC hS t P k hP hk (hF.1 k hk) _ _ (hY k hk))
    (D.R.m - 1) (by have := D.R.two_le_m; omega) _ _ (GlobalTheory.T.theta_chain_last_step_intertwines_matched_hecke R F hC hS t P hP hF.2.1 _ _ hX y y' hy)

end GlobalTheory.Hk3.ChainE
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SysW



theorem matched_operators_theta_intertwine : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i t P, Good R t P → ∀ cV cW, MatchW R i t P cV cW → ∀ hV, IsOpsV R i t hV → (∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y)) ∧ ∀ c, ∀ w ∈ Wcc R SF i c, hV P cV (LinearMap.adjoint (R.thG i t) w) = evC (Wc D i) P (c P) cW • LinearMap.adjoint (R.thG i t) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hX SF hSF i t P hP cV cW hM hV hhV
  have hP0 : Good R A.μ0 P := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).2.2
  have hWinj : Function.Injective (R.HW i (sg0 D A)).e := (hC.models.HW i (sg0 D A)).1
  have key : ∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y) := by
    intro h hh y
    have h1 := hM y (hV P cV y) (hhV P hP cV y)
    have h2 := hh P hP0 cW (R.thG i t y)
    exact hWinj (h1.trans h2.symm)
  refine ⟨key, ?_⟩
  intro c w hw
  have XW := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R F hC hS hX SF hSF i
  obtain ⟨hW, hWo, hWn, -, -, -, hWe, -⟩ := XW
  have XV := (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).2 i t
  obtain ⟨hV', hV'o, hV'n⟩ := XV
  have hVinj : Function.Injective (R.HV i t).e := (hC.models.HV i t).1
  have heq : ∀ c, hV P c = hV' P c := fun c => LinearMap.ext fun x => hVinj (by rw [hhV P hP, hV'o P hP])
  have nV' : Commute (hV' P cV) (LinearMap.adjoint (hV' P cV)) :=
    Eq.mpr (congrArg (Commute (hV' P cV)) (hV'n.2 P hP cV)) (hV'n.1 P P hP hP _ _)
  have nV : Commute (hV P cV) (LinearMap.adjoint (hV P cV)) :=
    Eq.mpr (congrArg (fun L => Commute L (LinearMap.adjoint L)) (heq cV)) nV'
  have nW : Commute (hW P cW) (LinearMap.adjoint (hW P cW)) :=
    Eq.mpr (congrArg (Commute (hW P cW)) (hWn.2 P hP0 cW)) (hWn.1 P P hP0 hP0 _ _)
  exact GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.thG i t) (fun _ : Unit => hV P cV) (fun _ : Unit => hW P cW) (fun _ u => key hW hWo u)
    (fun _ => nV) (fun _ => nW) () _ w (hWe c P hP0 cW w hw)

end GlobalTheory.SysW
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.matched_spherical_pairs_commute_composite_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ t P, Good R t P → ∀ cX c0, MatchE R t P cX c0 → ∀ hX, IsOpsX R t hX → (∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y)) ∧ ∀ c, ∀ w ∈ EEc R SF c, hX P cX (LinearMap.adjoint (R.Th t) w) = evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • LinearMap.adjoint (R.Th t) w := by
  first | exact @GlobalTheory.Hk3.SysE.matched_commute | exact GlobalTheory.Hk3.SysE.matched_commute | (intros; apply GlobalTheory.Hk3.SysE.matched_commute <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dualSplitLabel_operator_mul_scalar_operator : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), _root_.Formalism.DivisionValues.conjPl P ≠ P → ∀ j, j ≤ V.rank → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (dualLab (splitLab V.rank j)) 1) (opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) u) = opOf π P (Finsupp.single (splitLab V.rank (V.rank - j)) 1) u := by
  first | exact @GlobalTheory.DualSplitRel.dual_rel | exact GlobalTheory.DualSplitRel.dual_rel | (intros; apply GlobalTheory.DualSplitRel.dual_rel <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.modelPolynomial_oddDegree_of_realisesFramePoly : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G := by
  first | exact @GlobalTheory.TwV.DelA.oddDeg_of_realises | exact GlobalTheory.TwV.DelA.oddDeg_of_realises | (intros; apply GlobalTheory.TwV.DelA.oddDeg_of_realises <;> assumption)
end
