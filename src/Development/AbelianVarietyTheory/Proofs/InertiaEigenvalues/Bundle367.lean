module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle344
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle348
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle195
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.continuous_and_residualTriv_complexConj : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N), Continuous (GlobalTheory.TwistDet.cConj X) ∧ ∀ (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g : GE N, ResTriv i s g → ResTriv i s (GlobalTheory.TwistDet.cConj X g) := by
  first | exact @GlobalTheory.ResConjTriv.continuous_cConj_and_resTriv | exact GlobalTheory.ResConjTriv.continuous_cConj_and_resTriv | (intros; apply GlobalTheory.ResConjTriv.continuous_cConj_and_resTriv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.relaxedResidualSelmer_mem_unrelaxed : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), FirstHalf i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q → ∀ x : Z1 (red i K (Tgl i s)), cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → (∀ a, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))), x.1 σ = 0 ∧ x.1 (GlobalTheory.TwistDet.cConj X σ) = 0) → cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅ := by
  first | exact @GlobalTheory.ResUnr.unrelax | exact GlobalTheory.ResUnr.unrelax | (intros; apply GlobalTheory.ResUnr.unrelax <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.actsTriviallyResidual_of_complexConjugate : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g g' : GE N, IsCj X g g' → ResTriv i s g → ResTriv i s g' := by
  first | exact @GlobalTheory.ResTrivConj.resTriv_conj | exact GlobalTheory.ResTrivConj.resTriv_conj | (intros; apply GlobalTheory.ResTrivConj.resTriv_conj <;> assumption)
end

section

namespace GlobalTheory.BKCup

section Bridge

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.BKDimNoInv
open ReciprocityTheory.Gal (cycZ)

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycLL_eq (g : ↥(GK Bw.Kw)) :
    ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 g : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (Bw.e.symm g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l])) := by
  change algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
  rw [P.PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi Bw P g]
  exact (congrArg Subtype.val (Bw.eO_alg _)).symm

theorem dot_dual {O L : Type} [CommRing O] [CommRing L] (φ : O →+* L) {m : ℕ} (A : GL (Fin m) O) (ε : O)
    (x y : Fin m → L) :
    ((A : Matrix (Fin m) (Fin m) O).map φ).mulVec x ⬝ᵥ
      ((ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ).mulVec y = φ ε * (x ⬝ᵥ y) := by
  have h1 : (ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ =
      φ ε • (((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ).transpose := by
    ext a b
    simp
  have h2 : ((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ * (A : Matrix (Fin m) (Fin m) O).map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.coe_units_inv, Units.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]
  rw [h1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem cup_cob {m : ℕ} (r r' : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hr' : Continuous fun g => ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hd : ∀ g, ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O) =
      algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]) •
        ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)⁻¹.transpose)
    (hBK : bkACore (P.PD Bw.Kw)) (hdR : Bw.IsdRW P r)
    (c c' : ↥(GK Bw.Kw) → Fin m → ↥Bw.LL.1) (y y' : ↥Gw → Fin m → O)
    (hc : c ∈ finiteCocycles (P.PD Bw.Kw) (Bw.rep r)) (hc' : c' ∈ finiteCocycles (P.PD Bw.Kw) (Bw.rep r'))
    (hy : ∀ g a, c (Bw.e g) a = Bw.toLL (y g a)) (hy' : ∀ g a, c' (Bw.e g) a = Bw.toLL (y' g a)) :
    ∃ f : ↥Gw → ↥Bw.LL.1, Continuous f ∧ ∀ g h : ↥Gw,
      Bw.toLL (y g ⬝ᵥ ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).mulVec (y' h)) =
        Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l])) * f h - f (g * h) + f g := by
  have hG := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1
  have rep_apply {s : ↥Gw →* GL (Fin m) O} (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
      Bw.rep s g x = (((s (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl
  let mkRep (s : ↥Gw →* GL (Fin m) O)
      (hs : Continuous fun g => ((s g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)) :
      GRep ↥(GK Bw.Kw) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) := by
    haveI : IsTopologicalRing ↥Bw.LL.1 := hG.2.2.2.1
    exact { V := Fin m → ↥Bw.LL.1
            acg := inferInstance
            modLL := inferInstance
            modQp := inferInstance
            towQp := inferInstance
            modO := inferInstance
            towO := inferInstance
            fd := inferInstance
            top := inferInstance
            mtop := inferInstance
            cadd := inferInstance
            csmul := inferInstance
            ρ := Bw.rep s
            cont := by
              intro x
              simp only [rep_apply]
              exact ((hs.comp Bw.e_symm_cont).matrix_map
                (continuous_subtype_val.comp Bw.eO_cont)).matrix_mulVec continuous_const }
  let A := mkRep r hr
  let A' := mkRep r' hr'
  have hA : IsDR (P.PD Bw.Kw) A.ρ := by
    change Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) =
      Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin m → ↥Bw.LL.1)
    rw [Module.finrank_fin_fun]
    exact hdR
  let Q : (Fin m → ↥Bw.LL.1) →ₗ[↥Bw.LL.1] (Fin m → ↥Bw.LL.1) →ₗ[↥Bw.LL.1] ↥Bw.LL.1 :=
    dotProductBilin ↥Bw.LL.1 ↥Bw.LL.1
  have hD : IsDual1 (P.PD Bw.Kw) (Bw.rep r) (Bw.rep r') Q := by
    refine ⟨fun g x z => ?_, fun x hx => ?_, fun z hz => ?_, rfl⟩
    · change Bw.rep r g x ⬝ᵥ Bw.rep r' g z = _ * (x ⬝ᵥ z)
      rw [rep_apply, rep_apply, hd, dot_dual, cycLL_eq]
    · exact dotProduct_eq_zero x hx
    · exact dotProduct_eq_zero z fun x => (dotProduct_comm _ _).trans (hz x)
  obtain ⟨f, hf, hf'⟩ := (((hBK _ _ hG A A' Q hA hD).1 c hc.1).1 hc) c' hc'
  refine ⟨f ∘ Bw.e, hf.comp Bw.e_cont, fun g h => ?_⟩
  have h1 : ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 (Bw.e g) : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) * f (Bw.e h) - f (Bw.e g * Bw.e h) +
      f (Bw.e g) = c (Bw.e g) ⬝ᵥ Bw.rep r' (Bw.e g) (c' (Bw.e h)) := congrFun hf' (Bw.e g, Bw.e h)
  rw [cycLL_eq, rep_apply, MulEquiv.symm_apply_apply, ← map_mul] at h1
  refine Eq.trans ?_ h1.symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, hy, hy']

end Bridge

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

theorem cup_coboundary : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ ρ, IsDual i s ρ → ∀ (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (c c' : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin D.R.r → ↥(bkP.br i v hv).LL.1) (y y' : ↥(DecV N v) → Fin D.R.r → X.O0 i), c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) → c' ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ) → (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) → (∀ g a, c' ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y' g a)) → ∃ f : ↥(DecV N v) → ↥(bkP.br i v hv).LL.1, Continuous f ∧ ∀ g h : ↥(DecV N v), (bkP.br i v hv).toLL (y g ⬝ᵥ ((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).mulVec (y' h)) = (bkP.br i v hv).toLL (algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i])) * f h - f (g * h) + f g := by
  intro D N X bkP i s h ρ hρ v hv c c' y y' hc hc' hy hy'
  haveI : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed D.host.E
  refine cup_cob (bkP.br i v hv) (D.loc (X.l i)) ((Tgl i s).comp (DecV N v).subtype) (ρ.comp (DecV N v).subtype)
    ?_ ?_ (fun g => ?_) (h.2.2.2.2.2.1 _ _).1 (h.1.2.1 v hv (Tgl i s) (Or.inr rfl)).1 c c' y y' hc hc' hy hy'
  · exact ((GlobalTheory.PrimeToInertia.continuous_Tmat i s).comp continuous_subtype_val).congr fun g => (Tgl_coe i s g).symm
  · exact ((GlobalTheory.PrimeToInertia.continuous_Tdual i s).comp continuous_subtype_val).congr fun g => (hρ g).symm
  · refine (hρ g).trans ?_
    rw [Tdual, ← Tgl_coe]
    rfl

end GlobalTheory.BKCup
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.TwistLabel

theorem teich_zero' {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  by_contra h0
  have h1 : t 0 * t x = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact hx.2 (ht x 1 hx.1 one_ne_zero (mul_left_cancel₀ h0 h1))

theorem teich_injective' {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : Function.Injective t := by
  have h0 := teich_zero' t ht
  have hne : ∀ x, x ≠ 0 → t x ≠ 0 := fun x hx => ((IsUnit.mk0 x hx).map t).ne_zero
  intro x y h
  by_cases hx : x = 0
  · by_contra hxy
    exact hne y (fun hy => hxy (hx.trans hy.symm)) (by rw [← h, hx, h0])
  · by_cases hy : y = 0
    · exact absurd (by rw [h, hy, h0]) (hne x hx)
    · exact ht x y hx hy h

theorem prod_scaleRoots {α : Type*} (s : Multiset α) (f : α → ℂ) (c : ℂ) :
    ((s.map fun x => X - C (f x)).prod).scaleRoots c = (s.map fun x => X - C (f x * c)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s IH =>
    rw [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots', X_sub_C_scaleRoots, IH,
      Multiset.map_cons, Multiset.prod_cons]
    rw [leadingCoeff_X_sub_C, one_mul, ne_eq, leadingCoeff_eq_zero]
    exact (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C _).ne_zero

theorem roots_prod_map {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ((s.map fun x => X - C (f x)).prod).roots = s.map f := by
  rw [show (s.map fun x => X - C (f x)) = (s.map f).map (fun a => X - C a) by rw [Multiset.map_map]; rfl]
  exact roots_multiset_prod_X_sub_C _

end GlobalTheory.TwistLabel

open GlobalTheory.TwistLabel in
theorem main : ∀ D : D7, SumRepresentations.tie0 D → IneRep D → LabDepth D → LabGen D → LabChar D := by
  intro D hT _ hDep hGen k w hw L χ u hL hχ hχl
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ, hG⟩ := hGen
  have hLP := hT.1
  have hγI : γ k w ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := (hγ.2 k w hw).1
  have hdim : D.naut.lpDim (D.naut.lpChar L χ) = D.naut.lpDim L := D.naut.lpDim_char L χ hχ
  have hχdeg : (D.naut.items₂ k w χ).natDegree = D.naut.lpDim χ := by rw [hχl, natDegree_X_sub_C, hχ]
  have hχtame : TameLP D χ := ((hDep k w hw χ).2).1 hχdeg
  have hLtame : TameLP D L := ((hDep k w hw L).2).1 hL
  have hLχtame : TameLP D (D.naut.lpChar L χ) := by
    intro σ hσ hwσ
    have h1 := hχtame σ hσ hwσ
    rw [hχ, pow_one] at h1
    have h2 := ((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 σ hσ).2 1 (by rw [h1, map_one])
    rw [h2, hLtame σ hσ hwσ, scaleRoots_one, hdim]
  have hfull : (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L := by
    rw [← hdim]; exact ((hDep k w hw _).2).2 hLχtame
  refine ⟨hfull, ?_⟩
  set u' := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) with hu'
  have hrχ : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w χ) = {u'} := by
    rw [hχl, Formalism.CyclotomicNorms.rootsBar, Polynomial.map_sub, map_X, map_C, roots_X_sub_C]
  have hχγ : D.naut.inePol χ (γ k w) = X - C (D.ntypes.teichC k u') := by
    rw [hG k w hw χ hχdeg, hrχ]; simp
  have hsc := ((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 (γ k w) hγI).2 _ hχγ
  rw [hG k w hw L hL, prod_scaleRoots, hG k w hw _ (hfull.trans hdim.symm)] at hsc
  have hr := congrArg Polynomial.roots hsc
  rw [roots_prod_map, roots_prod_map] at hr
  have hinj := teich_injective' (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
  apply Multiset.map_injective hinj
  rw [hr, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro x _
  simp [Function.comp, map_mul]
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

namespace GlobalTheory.PendOf.CenLat

theorem prMt_mem_range (D : D7) (i : D.nd.Loc)
    (hO : ∀ a : 𝓞 D.what₂.LL, D.nd.embK i (a : D.what₂.LL) ∈
      (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range)
    (y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)) (hy : y ∈ GlobalTheory.EtaJoin.lat D (D.nd.mu i) (D.nd.j i)) :
    D.nd.prMt i y ∈ LinearMap.range
      (TensorProduct.mk (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) 1) := by
  unfold GlobalTheory.EtaJoin.lat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    rw [← D.nd.prMt_lat i]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hO a
    have h1 : a • x = (a : D.what₂.LL) • x := rfl
    rw [h1, LinearMap.map_smulₛₗ, ← hb, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

theorem cenInt_lat : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), (∀ a : 𝓞 D.what₂.LL, D.nd.embK i (a : D.what₂.LL) ∈ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range) → (∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)), D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) → S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x))) → CenInt D → ∀ (c : MonoidAlgebra ℤ (G0g D.nd)), (∀ a, c * a = a * c) → ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i, S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m') = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (Int.castRingHom ℂ) c) (S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m)) := by
  intro D i S hO hΦ hC c hc m
  have hm : (1 : KK D.nd i) ⊗ₜ[D.nd.O i] m ∈ LinearMap.range
      (TensorProduct.mk (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i) 1) := ⟨m, rfl⟩
  rw [← D.nd.prMt_lat i] at hm
  generalize (1 : KK D.nd i) ⊗ₜ[D.nd.O i] m = v at hm
  induction hm using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨y, hy, hxy⟩ := hC i c hc x hx
    obtain ⟨m', hm'⟩ := prMt_mem_range D i hO y hy
    refine ⟨m', ?_⟩
    rw [← hΦ _ x y hxy, ← hm']
    rfl
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨a • b, ?_⟩
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (KK D.nd i) a, ← algebraMap_smul (KK D.nd i) a x,
      S.semi, S.semi, map_smul, hb]

end GlobalTheory.PendOf.CenLat
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

namespace GlobalTheory.NewPrime

section General

def rect {Λ B : Type} [CommRing Λ] [AddCommGroup B] [Module Λ B] {r a : ℕ} (Z : Matrix (Fin r) (Fin a) Λ) (x : Fin a → B) :
    Fin r → B := fun c => ∑ j, Z c j • x j

abbrev what₂ {Λ μ ν : Type} [CommRing Λ] (Z : μ → ν → Λ) : Submodule Λ (ν → Λ) := Submodule.span Λ (Set.range Z)

def Cob {Γ Λ M : Type} [Group Γ] [CommRing Λ] [AddCommGroup M] [Module Λ M] (ρ : Representation Λ Γ M) (f : Γ → M) : Prop :=
  ∃ m, ∀ g, f g = ρ g m - m

variable (Λ : Type) [CommRing Λ] {Y Y' : Type} [AddCommGroup Y] [Module Λ Y] [AddCommGroup Y'] [Module Λ Y'] {n : ℕ}

def Bal (β : Y →+ Y' →+ ZMod n) : Prop := ∀ (a : Λ) y y', β (a • y) y' = β y (a • y')

def Perf (β : Y →+ Y' →+ ZMod n) : Prop :=
  Bal Λ β ∧ (∀ y, (∀ y', β y y' = 0) → y = 0) ∧ ∀ y', (∀ y, β y y' = 0) → y' = 0

def vecPair (r : ℕ) (β : Y →+ Y' →+ ZMod n) : (Fin r → Y) →+ (Fin r → Y') →+ ZMod n :=
  ∑ c : Fin r, ((β.comp (Pi.evalAddMonoidHom (fun _ => Y) c)).flip.comp (Pi.evalAddMonoidHom (fun _ => Y') c)).flip

theorem vecPair_apply (r : ℕ) (β : Y →+ Y' →+ ZMod n) (x : Fin r → Y) (y : Fin r → Y') :
    vecPair r β x y = ∑ c, β (x c) (y c) := by
  simp [vecPair]

def CupB {Γ M M' : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [AddCommGroup M'] (χ : Γ → ZMod n)
    (act : Γ → M' → M') (P : M →+ M' →+ ZMod n) (x : Γ → M) (y : Γ → M') : Prop :=
  ∃ f : Γ → ZMod n, IsLocallyConstant f ∧ ∀ g h, P (x g) (act g (y h)) = χ g * f h - f (g * h) + f g

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

def Kills (A : Type) [CommRing A] [Algebra (X.O0 i) A] : Prop := ∀ x ∈ idl i, algebraMap (X.O0 i) A x = 0

section Coef

variable {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)

def SelC (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] (Q : Finset (PlE D.host))
    (f : GE N → Fin D.R.r → Y) : Prop :=
  ∃ z : Z1 (repOn (Tgl i s) κ Y), z.1 = f ∧ Submodule.Quotient.mk z ∈ selOn bkP i (Tgl i s) κ Y Q

def Univ (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) Λ) (Z : GE N → Matrix (Fin D.R.r) (Fin a) Λ) : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y],
    (∀ x : Fin a → Y, matAct Φ x = 0 → SelC bkP i s κ Y Q fun g => rect (Z g) x) ∧
    (∀ x : Fin a → Y, matAct Φ x = 0 → Cob (repOn (Tgl i s) κ Y) (fun g => rect (Z g) x) → x = 0) ∧
    ∀ f, SelC bkP i s κ Y Q f → ∃ x : Fin a → Y, matAct Φ x = 0 ∧
      Cob (repOn (Tgl i s) κ Y) fun g => f g - rect (Z g) x

variable (ρ : GE N →* GL (Fin D.R.r) (X.O0 i))

section Dual

variable {Y Y' : Type} [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y]
  [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1)))
  (Q : Finset (PlE D.host))

def DualSel (y : Z1 (repOn ρ κ⁻¹ Y')) : Prop :=
  (∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 v), y.1 τ = 0) ∧
  (∀ v, v ∈ Spl i ∨ v ∈ Q → ∃ m, ∀ g ∈ DecV N v, y.1 g = repOn ρ κ⁻¹ Y' g m - m) ∧
  ∀ v ∈ placesOver D.host.E (X.l i), ∀ x : Z1 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype),
    Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) κ Y v →
    CupB (fun g : DecV N v => ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g.1 : (ZMod (X.l i ^ (nu X i + 1)))ˣ) :
        ZMod (X.l i ^ (nu X i + 1))))
      (fun g m => repOn ρ κ⁻¹ Y' g.1 m) (vecPair D.R.r β) x.1 (fun g => y.1 g.1)

def DualCl : Set (H1 (repOn ρ κ⁻¹ Y')) := {c | ∃ y, DualSel bkP i s κ ρ β Q y ∧ c = Submodule.Quotient.mk y}

end Dual

def OrderFormula (Q : Finset (PlE D.host)) : Prop :=
  ∀ (Y Y' : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] [Finite Y']
    (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Perf Λ β →
    Finite (DualCl bkP i s κ ρ β Q) ∧ Nat.card (selOn bkP i (Tgl i s) κ Y Q) =
      Nat.card (DualCl bkP i s κ ρ β Q) * ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ Y').comp (DecV N v).subtype))

def NoInvDual : Prop := ∀ (Y' : Type) [AddCommGroup Y'] [Module Λ Y'] (m : Fin D.R.r → Y'),
  (∀ g, repOn ρ κ⁻¹ Y' g m = m) → m = 0

def LocCountFin : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y],
    ∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (bkOn bkP i (Tgl i s) κ Y v) =
      (∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype))) *
        Nat.card Y ^ (D.R.f * D.R.r)


omit [Algebra (X.O0 i) Λ] in
def IsChar {M : ℕ} {ι : Type} [Fintype ι] (ξ : ι → Λ) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  ∀ g, ((κ g : Λˣ) : Λ) * ∏ q, (1 + ξ q) ^ (Multiplicative.toAdd (d q g)).val = 1

def bform (x y : GE N → Fin D.R.r → Λ) (h : GE N) : Λ := x h ⬝ᵥ y h - x (cConj X h) ⬝ᵥ y (cConj X h)

end Coef

def NewPl (M : ℕ) (L : Subgroup (GE N)) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N) : Prop :=
  (∀ v, Over p v → v ∉ X.S0 i) ∧ IsSplitPl D.host p ∧ normV p % (2 * X.l i ^ M) = 1 ∧ DecV N p ≤ L ∧
    IsOpen (d.ker : Set (GE N)) ∧ IsFrob (N.plOm.1 p) (normV p) σ ∧ γ ∈ Ine (F := D.host.E) (N.plOm.1 p) ∧
    d γ = Multiplicative.ofAdd 1


variable (X) in
def two (g : GE N) : Bool → GE N := fun b => if b then cConj X g else g

end GlobalTheory.NewPrime
end
end

section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.admInt_of_sup_laws : ∀ (D : D7) (E : IntegralHeckeForms.XD D), SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D → IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := by
  first | exact @GlobalTheory.IntSup.admInt_of_sup | exact GlobalTheory.IntSup.admInt_of_sup | (intros; apply GlobalTheory.IntSup.admInt_of_sup <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.stableQuadraticGauss_neg_one_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → IsStableGauss A ψ x μ (-1) G₁ := by
  first | exact @GlobalTheory.JR.WeilQuad.stableGauss_neg_one | exact GlobalTheory.JR.WeilQuad.stableGauss_neg_one | (intros; apply GlobalTheory.JR.WeilQuad.stableGauss_neg_one <;> assumption)
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralTensorTorsion_cocycle_of_torsion_localCocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ)
      (f : Br.G D.nbr i w hw → (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k),
    f ∈ divisibleCocycles (latC C N) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latC C (twistM N θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧ ∀ g, iotaW ↥C.LL.1 lam a k (z' g) = f g := by
  first | exact @GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle | exact GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle | (intros; apply GlobalTheory.UseLoc.Cases.LiftW.lift_cocycle <;> assumption)
end
