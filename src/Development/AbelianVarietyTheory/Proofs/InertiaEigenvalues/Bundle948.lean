module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle701
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle943
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle250
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle238
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle211
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle107
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle537
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle890
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle942
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle908
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle944
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergCellIntegralMatchedVectors
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle945
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle707
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle880
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GenRealFock

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem pureTensor_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (P Q : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ptP i t (P + Q) = R.ptP i t P + R.ptP i t Q := by
  unfold RealDat.ptP; exact map_add _ _ _

theorem pureTensor_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (c : ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ptP i t (c • P) = c • R.ptP i t P := by
  unfold RealDat.ptP; exact map_smul _ _ _

theorem downInt_add_f (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f f' : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f' * l (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y (f + f') l g = downInt R i t y f l g + downInt R i t y f' l g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp [thetaKO, add_mul]

theorem downInt_smul_f (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y (c • f) l g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp [thetaKO, mul_assoc]

theorem downInt_add_l (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l l' : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l' (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y f (l + l') g = downInt R i t y f l g + downInt R i t y f l' g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp [mul_add]

theorem downInt_smul_l (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y f (c • l) g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

theorem exists_bilin (R : RealDat D A Ks) (F : Face D A) (hG : GlobalTheory.LiftRows.Given R F) (hP : R.FullP)
    (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ∃ B : GA D (Wc D i) → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ,
      ∀ g P l, B g P l = downInt R i t y (R.ptP i t P) l g := by
  have hth := hG.core.thP.pt_theta i t
  have hint := fun f l g hf => GlobalTheory.T.integrableOn_downwardThetaLift_integrand D G Pl0 T A Ks R F hG hP i t y f l g hf
  refine ⟨fun g => LinearMap.mk₂ ℂ (fun P l => downInt R i t y (R.ptP i t P) l g) ?_ ?_ ?_ ?_, fun g P l => rfl⟩
  · intro P Q l
    rw [pureTensor_add, downInt_add_f _ _ _ _ _ _ _ _ (hint _ l g (hth P)) (hint _ l g (hth Q))]
  · intro c P l
    rw [pureTensor_smul, downInt_smul_f, smul_eq_mul]
  · intro P l l'
    exact downInt_add_l _ _ _ _ _ _ _ _ (hint _ l g (hth P)) (hint _ l' g (hth P))
  · intro c P l
    rw [downInt_smul_l, smul_eq_mul]

theorem gen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t (R.ioP i x w)) l g = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t P) l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hio P l g
  obtain ⟨B, hB⟩ := exists_bilin R F hG hP i t y
  have hth := hG.core.thP.pt_theta i t
  have key := (GlobalTheory.T.equivariant_bilinearForms_vanish_of_io_generation_real) D G Pl0 T A Ks R F hG hP i t (GA D (Wc D i)) B ?_ ?_ ?_ P g
  · rw [← hB, key, LinearMap.zero_apply]
  · intro j u hu P P' e l
    rw [hB, hB, e]
    exact (GlobalTheory.T.downwardThetaLift_real_points_equivariant) D G Pl0 T A Ks R F hG hP i t y u hu _ (hth P) l j
  · intro τ Y hY P P' hd h0 j
    refine LinearMap.ext fun l => ?_
    rw [LinearMap.zero_apply, hB]
    refine (GlobalTheory.T.thetaLift_vanishing_preserved_by_realLieDerivative) D G Pl0 T A Ks R F hG hP i t y τ Y hY P P' hd l (fun g' => ?_) j
    rw [← hB, h0 g', LinearMap.zero_apply]
  · intro x w j
    refine LinearMap.ext fun l => ?_
    rw [LinearMap.zero_apply, hB]
    exact hio x w l j

end GlobalTheory.GenRealFock
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.PinsNormal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levJ_eq (R : RealDat D A Ks) (i : Fin D.R.m) {t t' : T0} (e : R.Q t' = R.Q t) : levJ R i t' = levJ R i t := by
  have key : ∀ (Q Q' : Finset (Pl D.host.E)) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), Q = Q' →
      lev D.sp.cm (Vc D i).gram (R.βV i) (Lev.flag1L (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q (LevelP.triv _ _ _)
        (fun _ => R.chi ((i : ℕ) + 1)) ξ Lev.Frm.A)) =
      lev D.sp.cm (Vc D i).gram (R.βV i) (Lev.flag1L (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q' (LevelP.triv _ _ _)
        (fun _ => R.chi ((i : ℕ) + 1)) ξ' Lev.Frm.A)) := by
    rintro Q _ ξ ξ' rfl
    exact Subgroup.ext fun x => Iff.rfl
  have h := key _ _ (R.xiR t') (R.xiR t) e
  unfold levJ levEnv
  exact congrArg (fun K => (Lev.toAfE (Vc D i) K).comap (finHom (Vc D i)).range.subtype) h

theorem repsR_of_eq (R : RealDat D A Ks) (i : Fin D.R.m) {t t' : T0} (e : R.Q t' = R.Q t) {K' : Type} [Field K'] {Cl : Type} [Fintype Cl]
    {h : Cl → GA D (Vc D i)} {bad : ℕ} {J' : Subgroup (Bridge.Gf (Vc D i))}
    {Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} {gam : Cl → ℕ} {vol : K'}
    (H : RepsR R i t' h bad J' Lh gam vol) : RepsR R i t h bad J' Lh gam vol := by
  unfold RepsR at H ⊢
  rwa [levJ_eq R i e, e] at H

theorem extC_down (R : RealDat D A Ks) (i : Fin D.R.m) {K₁ K₂ : Type} [Field K₁] [Field K₂] (j₁ : D.what₂.LL →+* K₁) (j₂ : D.what₂.LL →+* K₂)
    (σ₁ : K₁ →+* ℂ) (σ₂ : K₂ →+* ℂ) (h₁ : σ₁.comp j₁ = D.what₂.embLL) (h₂ : σ₂.comp j₂ = D.what₂.embLL)
    (hs : Function.Surjective j₁) (c0 : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (a₁ : VsV D i K₁ →ₛₗ[σ₁] (R.cV i).W) (a₂ : VsV D i K₂ →ₛₗ[σ₂] (R.cV i).W)
    (H₁ : CoefficientBaseChange R i j₁ σ₁ c0 a₁) (H₂ : CoefficientBaseChange R i j₂ σ₂ c0 a₂) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W)
    (hc : ExtC R i σ₂ a₂ c) : ExtC R i σ₁ a₁ c := by
  intro v v' e
  let ε : K₁ ≃+* D.what₂.LL := (RingEquiv.ofBijective j₁ ⟨j₁.injective, hs⟩).symm
  have hε : j₁.comp (ε : K₁ →+* D.what₂.LL) = RingHom.id K₁ := RingHom.ext fun x => (RingEquiv.ofBijective j₁ ⟨j₁.injective, hs⟩).apply_symm_apply x
  let u : VsV D i D.what₂.LL := ⟨MvPolynomial.map (ε : K₁ →+* D.what₂.LL) (v : Pol K₁ D.what₂.Tau (Vc D i).rank),
    Formalism.L2.Ker.map_mem_VV _ _ _ v.2⟩
  obtain ⟨w₁, e₁, f₁⟩ := H₁ u
  obtain ⟨w₂, e₂, f₂⟩ := H₂ u
  have hw : w₁ = v := Subtype.ext (by
    rw [e₁]
    change MvPolynomial.map j₁ (MvPolynomial.map (ε : K₁ →+* D.what₂.LL) (v : Pol K₁ D.what₂.Tau (Vc D i).rank)) = _
    rw [MvPolynomial.map_map, hε, MvPolynomial.map_id])
  rw [← hw, f₁, ← f₂]
  refine hc w₂ v' ?_
  rw [e, e₂, MvPolynomial.map_map, h₂, ← hw, e₁, MvPolynomial.map_map, h₁]

theorem exists_normal_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    ∃ c' : Coeff l, c.F ≤ c'.F ∧ Normal ℚ c'.F := by
  have := c.fin
  have hle : c.F ≤ IntermediateField.normalClosure ℚ c.F ℂ := IntermediateField.le_normalClosure c.F
  have : IsNormalClosure ℚ c.F (IntermediateField.normalClosure ℚ c.F ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure fun x => IsAlgClosed.splits _
  exact ⟨⟨IntermediateField.normalClosure ℚ c.F ℂ, inferInstance, fun τ a => hle (c.conj τ a), hle c.zeta_mem,
    c.le.trans hle⟩, hle, IsNormalClosure.normal (F := ℚ) (K := c.F) (L := IntermediateField.normalClosure ℚ c.F ℂ)⟩



theorem exists_pins_normal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → ∃ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) ∧ M.lev = (O i).lev ∧ (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) ∧ Normal ℚ M.c'.F ∧ GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 ∧ (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) ∧ ∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O hC hfin hfw hG i hO
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  have hL : R.toLevCh.Is A.μ0 := hC.lev
  have hchi : R.grp_chiW := hC.grp.chiW
  have hfam := hC.fam
  have hmodels := hC.models
  have hvP : R.thP_vP := hC.thP.vP
  obtain ⟨hpb, hV, hlev⟩ := GlobalTheory.T.baseTuple_pins_orientation_standardFrame_levelMap D G Pl0 T0 A T R κ v₀ O hL hT i hO
  obtain ⟨gramR, c0R, c0L, htie, hc0O⟩ := hO.2.lift.c0
  haveI : Nonempty T0 := ⟨A.μ0⟩
  let rep : T0 → T0 := fun t => Function.invFun R.Q (R.Q t)
  have hrepQ : ∀ t, R.Q (rep t) = R.Q t := fun t => Function.invFun_eq (f := R.Q) ⟨t, rfl⟩
  have hrepE : ∀ t t' : T0, R.Q t' = R.Q t → rep t' = rep t := fun t t' e => congrArg (Function.invFun R.Q) e
  choose pd l₂ h1 h2 using fun t => GlobalTheory.CoverHalf.exists_half_of_laws T.toCore R hT.toLawsM hL hpb hG t
  obtain ⟨c₁, hc1a, hc1b, hc1xi, hc⟩ := GlobalTheory.OneCover.exists_covers_rep T R hT hL i (Vc D i).rank pd
    (fun t => GlobalTheory.CoverHalf.coverHalf D (R.Q t)) l₂ h1 h2 rep hrepQ
  choose Mφ hMφ hφ using fun t => GlobalTheory.T.exists_level_place_datum_over_number_field D G Pl0 T0 A _ R hL hvP i hV t _ (iotaW T i)
    (GlobalTheory.PinnedDataGiven.latEmb_iotaW T hT i)
  choose MB hMB hB using fun t => GlobalTheory.T.exists_numberField_heckeCharacter_sqrtNorm_values D G Pl0 T0 A _ R hL i t
  have := c₁.fin
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.TupleCover.exists_coeff_ge T.Q.l (c₁.F ⊔ ⨆ t, (Mφ t ⊔ MB t))
  obtain ⟨c₃, hc₃, hcurve⟩ := GlobalTheory.CurveField.exists_coeff_curveOver _ T.Q.H T.Q.l c₂ 1 one_pos
  obtain ⟨c', hc', hnorm⟩ := exists_normal_coeff c₃
  have h23 : c₂.F ≤ c'.F := hc₃.trans hc'
  have h3 : c₁.F ≤ c'.F := (le_sup_left.trans hc₂).trans h23
  have h4 : ∀ t, Mφ t ⊔ MB t ≤ c'.F := fun t =>
    (((le_iSup (fun t => Mφ t ⊔ MB t) t).trans le_sup_right).trans hc₂).trans h23
  have hle : T.Q.c.F ≤ c'.F := hc1a.trans h3
  have hLL := hc1b.trans h3
  obtain ⟨d, U, dict, f, xi, -, hcov, hhalf, hxi, hcxi, hmod⟩ := hc c' hle h3
  let dδ : T0 → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank := fun t => { d (rep t) with cδ := f t }
  let jL : D.what₂.LL →+* c'.F := D.what₂.embLL.codRestrict c'.F fun x => hLL ⟨x, rfl⟩
  have hjL : (inC c').comp jL = D.what₂.embLL := RingHom.ext fun _ => rfl
  obtain ⟨c0', hc0, hplace⟩ := GlobalTheory.T.exists_coefficientMap_extension_rational_values D G Pl0 T0 A _ R hL hchi hfam hmodels gramR c0R c0L htie i c'.F jL (inC c') hjL
  obtain ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, hrep, hbad, hcl⟩ :=
    GlobalTheory.SplitReps.exists_repsR_repsCov R i (hL.βV i) hV c'.F (T.Q.Xo ((i : ℕ) + 1)) c' id d
  have hrepR : ∀ t, RepsR R i t (h (rep t)) (bad (rep t)) (J' (rep t)) (Lh (rep t)) (gam (rep t)) (vol (rep t)) :=
    fun t => repsR_of_eq R i (hrepQ t) (hrep (rep t)).1
  choose B hBis using fun t => hB t c'.F (le_sup_right.trans (h4 t)) (bad (rep t)) (hbad (rep t)).2.2.2.2
    fun PP hPP => (hrepR t).2.1 PP (Or.inr hPP)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad (rep t)) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  obtain ⟨io, hw, hio⟩ := GlobalTheory.T.exists_harmonicCoefficientMap_at_weights D T.Q hT.pins κ fw.kap i c'
  choose φ hφis using fun t => hφ t c'.F (le_sup_left.trans (h4 t)) (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => GlobalTheory.T.exists_adelicSide_of_models D G Pl0 T0 A _ R hmodels i t _ _ c0' _ (h (rep t)) _ (hrepR t).2.2.1
    (hrepR t).2.2.2.2.2.1 (v₀ i (sg0 D A))
  have hact := fun c => GlobalTheory.T.levelAction_framedPoints_isAction D G Pl0 T0 A T R hL hT hpb i c (O i).lev hlev
  let M : OMDat T.toCore R i T0 id :=
    { c' := c', hle := hle, jL := jL, hV := hT.spaceW _ (inR i) _ rfl, c0' := c0', lev := (O i).lev, dδ := dδ,
      Cl' := fun t => Cl (rep t), fCl := fun t => fCl (rep t),
      bad := fun t => bad (rep t), Lh := fun t => Lh (rep t), La := fun t => La (rep t), Nc := fun t => Nc (rep t),
      gam := fun t => gam (rep t), vol := fun t => vol (rep t), ep := fun t k => epF t (Lh (rep t) k), B := B,
      epF := epF, io := io, hw := hw, φ := φ,
      w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
      U₂ := fun t => U (rep t), dict₂ := fun t => dict (rep t), xi := xi, thAd := thAd,
      Plc := fun t x => ∃ x₀, Place R i t (h (rep t)) c0' (jVx R i t x₀) x }
  have hMP : M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) :=
    ⟨⟨hjL, hV, fw.hv₀ i _, ⟨gramR, c0R, c0L, htie, hc0⟩, hlev⟩,
      fun t => ⟨⟨h (rep t), J' (rep t), hrepR t, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
      ⟨hact _, hact _⟩, fun t => hbad (rep t), fun t => hcl (rep t), fun t => ⟨fun _ => rfl, hepF t⟩, hio,
      fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩
  refine ⟨M, hMP, rfl, ?_, hnorm, hcurve c' hc', fun t x => h3 (hc1xi t x), fun t t' e => ?_⟩
  · obtain ⟨cM, hcM, -, huM⟩ := GlobalTheory.T.coefficientMap_unique_bijective_complex_extension D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP
    obtain ⟨cO, -, -, huO⟩ := GlobalTheory.T.coefficientMap_unique_bijective_complex_extension D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i Unit (fun _ => A.μ0) (O i) hO.2
    have hsurj : Function.Surjective (O i).jL := by
      intro x
      have hx : (x : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hO.1 ▸ x.2
      obtain ⟨y, hy⟩ := hx
      refine ⟨y, Subtype.ext ?_⟩
      have := RingHom.congr_fun hO.2.lift.field y
      exact this.trans hy
    have hsame : ExtC R i (inC (O i).c') (O i).c0' cM :=
      extC_down R i (O i).jL jL (inC (O i).c') (inC c') hO.2.lift.field hjL hsurj (c0L i) (O i).c0' c0' hc0O hc0 cM hcM
    have e0 : cM = _ := huO cM hsame
    intro c
    constructor
    · intro hc'
      rw [huO c hc', ← e0]
      exact hcM
    · intro hc'
      rw [huM c hc']
      exact hsame
  · have er : rep t' = rep t := hrepE t t' e
    have key : ∀ a b : T0, a = b → ∀ (fa : Rul (d a).Xo₂ (d a).c₂) (fb : Rul (d b).Xo₂ (d b).c₂),
        ∃ cx : Rul (d b).Xo₂ (d b).c₂, ({ d a with cδ := fa } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) =
          { ({ d b with cδ := fb } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) with cδ := cx } := by
      rintro a _ rfl fa fb
      exact ⟨fa, rfl⟩
    have keyK : ∀ {β : Type} (g : ∀ a, Cl a → β) (a b : T0) (hab : a = b) (k : Cl a), g b (cast (congrArg Cl hab) k) = g a k := by
      rintro β g a _ rfl k
      rfl
    refine ⟨Equiv.cast (congrArg Cl er.symm), key _ _ er (f t') (f t), congr_arg_heq U er, congr_arg_heq dict er,
      congrArg bad er, congrArg vol er, fun k => ⟨keyK Lh _ _ er.symm k, keyK La _ _ er.symm k, keyK Nc _ _ er.symm k,
      keyK gam _ _ er.symm k⟩⟩

end GlobalTheory.PinsNormal
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.RSEulerId

theorem thetaZ_eq_mul_eulD : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
                       (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ ∧
          GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x =
            ((H x * (GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) := by
  intro E _ _ _ a π ha hu T hT
  obtain ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hℓ, hα, hπ₀, hω, hc, hφ, hφ0, hΦs, hΦc, hΦr, hΦp, hΦ0, hcore⟩ :=
    GlobalTheory.T.unfoldedWhittakerIntegral_eq_eulerProduct_schurSums E a π ha hu T hT
  have hF : φ.1 ∈ GlobalTheory.JSW.mspanR π₀ := hφ.elim (fun h => Submodule.mem_sInf.2 fun _ hS => hS.1 φ h) id
  have hπu : π₀.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  have hFc : Continuous φ.1 := by
    obtain ⟨ψ, hψ, hw⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπu φ.1 hF
    have h0 := (hw []).2
    rw [GlobalTheory.JSW.word_nil, hψ] at h0
    exact h0.cont
  refine ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hα, hπ₀, hω, hc, hφ, hφ0, hΦs, hΦc, hΦr, hΦp, hΦ0, fun μ _ 𝓕 h𝓕 => ?_⟩
  obtain ⟨𝓕₀, h𝓕₀⟩ := GlobalTheory.T.exists_isFundamentalDomain_rationalUpperUnitriangular E a μ
  obtain ⟨H, hHc, hH1, hH⟩ := hcore μ 𝓕₀ h𝓕₀
  refine ⟨H, hHc, hH1, fun x hx => ?_⟩
  obtain ⟨hHx, heq⟩ := hH x hx
  have hU := GlobalTheory.T.lintegral_rankinSelbergTheta_eq_whittakerUnfolding E a ℓ hℓ π₀ hπu φ.1 hF Φ hΦs.continuous hΦc hΦr J η μ 𝓕 𝓕₀ h𝓕 h𝓕₀ x
  have hfin := GlobalTheory.T.lintegral_theta_self_cusp_rapid_span_ne_top E a ℓ π₀ ω hω hc φ.1 hF Φ hΦs hΦc hΦr hΦp J η μ 𝓕 h𝓕 x hx
  have hZ := GlobalTheory.T.rankinSelbergThetaIntegral_smoothSpan_eq_toReal_lintegral E a ℓ π₀ φ.1 hF hFc Φ hΦs.continuous hΦr hΦp J η μ 𝓕 h𝓕 x hfin
  rw [hU, heq] at hfin hZ
  refine ⟨hHx, fun h => hfin (by rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hHx).ne']), ?_⟩
  rw [hZ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hHx.le]

end GlobalTheory.RSEulerId
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.unfolded_rankinSelberg_cellIntegral_matchedVectors : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
      Continuous κ → (∀ h, 0 ≤ κ h) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) →
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) →
      (∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        ∀ x : ℝ, 1 < x →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (β w.1 i : ℂ)) x ≠ ⊤ →
          (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤) ∧ (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤) ∧
          ∫ g in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g ∂μ =
            (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) *
              ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ),
                l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ))
                  (fun i => (β w.1 i : ℂ)) x v := by
  first | (exact @GlobalTheory.RSnmCells.unfolded_cells_eq) | (exact GlobalTheory.RSnmCells.unfolded_cells_eq) | (intros; apply GlobalTheory.RSnmCells.unfolded_cells_eq  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.typePlaces_twistPlaces_goodPosition : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (μ0 : T), Rl.toLevCh.Is μ0 → (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧ (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E → D.host.pde ≠ D.host.q ∧ D.host.pde' ≠ D.host.q → ∀ (i : D.ntw.Tw) (ch : Set (Pl D.host.E)), IsChoice ch → PlacesOK Rl.Pg (half ch (D.ntw.pD i)) := by
  first | exact @GlobalTheory.SeriesTie.PlacesGood.placesOK | exact GlobalTheory.SeriesTie.PlacesGood.placesOK | (intros; apply GlobalTheory.SeriesTie.PlacesGood.placesOK <;> assumption)
end
