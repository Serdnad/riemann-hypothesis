module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle209
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle198
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle196
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle193
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle226
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle220
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle228
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle227
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK Formalism.MainNotions.G.GAtP.algOK

theorem blk_frame_eq {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hT : PosTie X D pos Kc ι ρ) (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n)
    (M : GL (Fin n) D.host.E) (hU : StdU D M) (hF : FrIs fd ρ j La h M) :
    (fun v s => Matrix.GeneralLinearGroup.map (algebraMap X.G.Kf Kc)
        (gPosGL (X.Pj j) v s ((SecondKernelHermitian.glInv X j (SecondKernelHermitian.BOf fd j La) v)⁻¹))) =
      (fun v s => Matrix.GeneralLinearGroup.map ι (hAt (X.Pj j) h (posJ X D pos j) (fun _ => 1) (atR D M) v s)) := by
  have hblk := GlobalTheory.T.unitaryBlockMatrices_read_in_placeField X D pos Kc ι ρ hT M hU
  cases j with
  | zero =>
    funext (v : X.Pl) (s : Fin (X.G.P.n' v))
    have hA : (SecondKernelHermitian.glInv X 0 (SecondKernelHermitian.BOf fd 0 La) v)⁻¹ = SecondKernelHermitian.frGL fd 0 La v := inv_inv _
    have hdet : IsUnit (fd.frM 0 La v).det := by
      rw [hF v, Matrix.det_submatrix_equiv_self]
      have hu := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map (ρ v)
      rw [RingHom.map_det] at hu
      exact hu
    have hv : (SecondKernelHermitian.frGL fd 0 La v : Matrix _ _ _) = fd.frM 0 La v := by
      unfold SecondKernelHermitian.frGL
      rw [dite_eq_left hdet]
      rfl
    apply Units.ext
    ext a b
    have e1 := congrFun (congrFun (hblk v s).1 (finCongr h a)) (finCongr h b)
    simp only [Matrix.map_apply] at e1
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, hA]
    show algebraMap X.G.Kf Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) ((SecondKernelHermitian.frGL fd 0 La v : Matrix _ _ _) a b))) = _
    rw [hv, hF v]
    by_cases hs : Even s.val
    · have ho : ¬ IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact not_not.2 hs
      rw [if_neg ho] at e1
      simp only [hAt, hs, if_true]
      rw [one_mul, inv_one, mul_one]
      exact e1.symm
    · have ho : IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact hs
      rw [if_pos ho] at e1
      simp only [hAt, hs, if_false, invT]
      rw [one_mul, inv_one, mul_one, ← map_inv]
      exact e1.symm
  | succ j =>
    funext (v : X.Pl) (s : Fin (X.G.P.n' v))
    have hA : (SecondKernelHermitian.glInv X (j + 1) (SecondKernelHermitian.BOf fd (j + 1) La) v)⁻¹ = SecondKernelHermitian.frGL fd (j + 1) La v := inv_inv _
    have hdet : IsUnit (fd.frM (j + 1) La v).det := by
      rw [hF v, Matrix.det_submatrix_equiv_self]
      have hu := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map (ρ v)
      rw [RingHom.map_det] at hu
      exact hu
    have hv : (SecondKernelHermitian.frGL fd (j + 1) La v : Matrix _ _ _) = fd.frM (j + 1) La v := by
      unfold SecondKernelHermitian.frGL
      rw [dite_eq_left hdet]
      rfl
    apply Units.ext
    ext a b
    have e1 := congrFun (congrFun (hblk v s).1 (finCongr h a)) (finCongr h b)
    simp only [Matrix.map_apply] at e1
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, hA]
    show algebraMap X.G.Kf Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) ((SecondKernelHermitian.frGL fd (j + 1) La v : Matrix _ _ _) a b))) = _
    rw [hv, hF v]
    by_cases hs : Even s.val
    · have ho : ¬ IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact not_not.2 hs
      rw [if_neg ho] at e1
      simp only [hAt, hs, if_true]
      rw [one_mul, inv_one, mul_one]
      exact e1.symm
    · have ho : IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact hs
      rw [if_pos ho] at e1
      simp only [hAt, hs, if_false, invT]
      rw [one_mul, inv_one, mul_one, ← map_inv]
      exact e1.symm

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK Formalism.MainNotions.G.GAtP.algOK

theorem gmOf_map_eq_actC : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n) (M : GL (Fin n) D.host.E), StdU D M → FrIs fd ρ j La h M → ∀ (G : (X.Pj j).Xsp) (V : XR (X.Pj j) ℂ), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι V → MvPolynomial.map (algebraMap X.G.Kf Kc) (gmOf fd j La G) = MvPolynomial.map ι (actC X D pos j h M V) := by
  intro p _ X D pos Kc _ _ ι ρ hT fd j La n h M hU hF G V hGV
  unfold gmOf actC
  rw [natAct_eq, map_natActR, map_natActR, ← hGV, blk_frame_eq X D pos Kc ι ρ hT fd j La h M hU hF]

end GlobalTheory.TwV.DelA
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL.LimAtLU

variable {a : ℕ}

theorem int_of_mem_inf {lam : DomWeight a} {x : ℂ} (hx : x ∈ infOfWeight lam) :
    ∃ j : ℤ, ((a : ℂ) - 1) / 2 - x = j := by
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  exact ⟨(k : ℤ) - lam.w k, by push_cast; ring⟩


open Classical in
noncomputable def jumpsOf (lam : DomWeight a) : Multiset ℤ :=
  (infOfWeight lam).map fun z => if h : ∃ n : ℤ, ((a : ℂ) - 1) / 2 - z = n then h.choose else 0

theorem jumpsOf_map (lam : DomWeight a) :
    (jumpsOf lam).map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [jumpsOf, Multiset.map_map]
  refine Multiset.map_congr rfl fun z hz => ?_
  have h := int_of_mem_inf hz
  simp only [Function.comp_apply, dif_pos h]
  exact h.choose_spec.symm

theorem eq_jumpsOf {lam : DomWeight a} {J : Multiset ℤ}
    (hJ : J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z)) : J = jumpsOf lam :=
  Multiset.map_injective Int.cast_injective (hJ.trans (jumpsOf_map lam).symm)

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

theorem overPl_of_induced {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O}
    (hj : GlobalTheory.Pst.Induces Bw) {τ : E →+* Qbar l} {LL' : FinExt l} {τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1}
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') : OverPl ι (ι.toRingHom.comp τ) w := by
  intro x hx
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    RingEquiv.symm_apply_apply]
  rw [hτ]
  have h1 := norm_algHom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩
  have h2 : ‖Bw.j (algebraMap E Ω x)‖ < 1 := (hj.valuation_lt_one_iff _).1 ((h x).2 hx)
  exact h1 ▸ h2

end GlobalTheory.CongL.LimAtLU


open Classical GlobalTheory.CongL.LimAtLU in
theorem GlobalTheory.CongL.crysDRU_of_linApprox : ClosedAtL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → (∀ τ : E →+* ℂ, ∃ lam, HasWeightAt U τ lam) → ∀ (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Continuous r → IsSSRep r → ∀ C : Set (_root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), LinApprox r C → (∀ ρ ∈ C, Continuous ρ ∧ ∃ U' : Submodule ℂ (UA E a → ℂ), SameWtAt ι w U U' ∧ CrysDRU U' ι ρ w) → CrysDRU U ι r w := by
  intro hC E Ω _ _ _ _ _ _ l _ ι a ha U _ hW r w hwl hr hss C hlin hCC
  intro P AI hT A hA O _ _ _ Bw hBw
  choose lamF hlamF using hW
  have key : ∀ lamG : (E →+* ℂ) → DomWeight a, (∀ σ, HasWeightAt U σ (lamG σ)) →
      (IsdRAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ (jumpsOf (lamG (ι.toRingHom.comp τ)))) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)) → IsCrysAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    intro lamG hG
    refine hC E Ω l a ha P AI hT w A hA O Bw hBw (fun τ => jumpsOf (lamG (ι.toRingHom.comp τ))) r hr hss C hlin
      (fun ρ hρ => ?_)
    obtain ⟨hcont, U', hWW, hcd⟩ := hCC ρ hρ
    have h := hcd P AI hT A hA O Bw hBw
    exact ⟨hcont, GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT E Ω _ O Bw a _ h.1,
      fun τ LL' τ' hi => h.2.2 τ LL' τ' hi _ _ ((hWW _ (overPl_of_induced ι hA hBw hi) _).1 (hG _)) (jumpsOf_map _)⟩
  refine ⟨(key lamF hlamF).2 fun ρ hρ => ?_, (key lamF hlamF).1.1, fun τ LL' τ' hi lam J hl hJ => ?_⟩
  · obtain ⟨-, U', -, hcd⟩ := hCC ρ hρ
    exact (hcd P AI hT A hA O Bw hBw).1
  · let lamG := Function.update lamF (ι.toRingHom.comp τ) lam
    have hG : ∀ σ, HasWeightAt U σ (lamG σ) := by
      intro σ
      rcases eq_or_ne σ (ι.toRingHom.comp τ) with h | h
      · rw [h]
        simpa [lamG] using hl
      · show HasWeightAt U σ (Function.update lamF (ι.toRingHom.comp τ) lam σ)
        rw [Function.update_of_ne h]
        exact hlamF σ
    have e := (key lamG hG).1.2 τ LL' τ' hi
    rw [eq_jumpsOf hJ]
    simpa [lamG] using e
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

namespace GlobalTheory.PolarizedWeight

theorem exists_isWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∃ wt : ℤ, IsWeight π wt := by
  intro E _ _ _ l a ha π χ h
  obtain ⟨hreg, hpol, -⟩ := h
  have hcomm : ∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o) := fun τ u o => by
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X
  have hm : ∀ σ, π.HasInfChar σ ((CG.mk π).infChar σ) := fun σ =>
    GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E a hcomm (CG.mk π) σ
  set ψ := GlobalTheory.GalOfCusp.compNorm E χ with hψ
  have key : ∀ τ : E →+* ℂ, (CG.mk π).infChar (ComplexEmbedding.conjugate τ) =
      ((CG.mk π).infChar τ).map fun z => -(z + expo ψ⁻¹ τ) := fun τ => by
    have h1 := (hm τ).twist ψ⁻¹
    rw [GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing E a (π.twist ψ⁻¹) π hpol.dual τ _ _ h1 (hm (ComplexEmbedding.conjugate τ)), Multiset.map_map]
    rfl

  have hint : ∀ τ : E →+* ℂ, ∃ k : ℤ, expo ψ τ = k := fun τ => by
    obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ :=
      Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ).1]; omega)
    obtain ⟨n, hn⟩ := (hreg τ).2 z hz
    have hz' : -(z + expo ψ⁻¹ τ) ∈ (CG.mk π).infChar (ComplexEmbedding.conjugate τ) := by
      rw [key]
      exact Multiset.mem_map.2 ⟨z, hz, rfl⟩
    obtain ⟨n', hn'⟩ := (hreg _).2 _ hz'
    refine ⟨n + n' + ((a : ℤ) - 1), ?_⟩
    rw [GlobalTheory.RegAlgCharAlg.expo_inv'] at hn'
    push_cast
    linear_combination hn' + hn
  choose k hk using hint
  have hkc : ∀ τ, k (ComplexEmbedding.conjugate τ) = k τ := fun τ => by
    have := (hk _).symm.trans ((GlobalTheory.T.exponent_heckeChar_compNorm_conjEmbedding E χ τ).trans (hk τ))
    exact_mod_cast this
  let n : (maximalRealSubfield E →+* ℂ) → ℤ := fun φ => k (ComplexEmbedding.lift E φ)
  have hkn : ∀ τ : E →+* ℂ, k τ = n (τ.comp (algebraMap (maximalRealSubfield E) E)) := fun τ => by
    rcases GlobalTheory.cm_eq_or_conj_of_comp_eq E (ComplexEmbedding.lift E (τ.comp (algebraMap (maximalRealSubfield E) E))) τ
      (ComplexEmbedding.lift_comp_algebraMap E _).symm with h | h
    · exact congrArg k h
    · exact (congrArg k h).trans (hkc _)

  have hn : ∀ g : (maximalRealSubfield E →+* ℂ) → ℂ,
      ∏ τ : E →+* ℂ, g (τ.comp (algebraMap (maximalRealSubfield E) E)) ^ k τ = ∏ φ, g φ ^ (2 * n φ) := by
    classical
    intro g
    rw [← Finset.prod_fiberwise Finset.univ
      (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E))]
    refine Finset.prod_congr rfl fun φ _ => ?_
    set τ₀ := ComplexEmbedding.lift E φ with hτ₀
    have h0 : τ₀.comp (algebraMap (maximalRealSubfield E) E) = φ :=
      ComplexEmbedding.lift_comp_algebraMap E φ
    have h1 : (ComplexEmbedding.conjugate τ₀).comp (algebraMap (maximalRealSubfield E) E) = φ := by
      rw [GlobalTheory.cm_conj_comp_eq, h0]
    have hne : τ₀ ≠ ComplexEmbedding.conjugate τ₀ := fun h =>
      IsTotallyComplex.complexEmbedding_not_isReal τ₀ (ComplexEmbedding.isReal_iff.2 h.symm)
    have hfib : Finset.univ.filter
        (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E) = φ) =
        {τ₀, ComplexEmbedding.conjugate τ₀} := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        exact GlobalTheory.cm_eq_or_conj_of_comp_eq E τ₀ τ (h.trans h0.symm)
      · rintro (rfl | rfl)
        · exact h0
        · exact h1
    rw [hfib, Finset.prod_pair hne, h0, h1, hkc, mul_comm (2 : ℤ), zpow_mul, zpow_two]
  have hAlg : IsAlgPos χ n := fun x hx => by
    have hpos : ∀ φ : maximalRealSubfield E →+* ℂ,
        ((‖φ (x : maximalRealSubfield E)‖ : ℝ) : ℂ) = φ x ∧ 0 < ‖φ (x : maximalRealSubfield E)‖ := by
      intro φ
      have hr : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
      have h0 := hx hr.embedding
      rw [← hr.coe_embedding_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
      exact ⟨rfl, h0⟩
    let z : Cinf E := fun w => ((Real.log (w ((x : maximalRealSubfield E) : E)) / 2 : ℝ) : ℂ)
    let u : (Cinf E)ˣ := expU z
    have hu : u * Units.map (starRingEnd (Cinf E)).toMonoidHom u =
        Units.map (diagInf E).toMonoidHom (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) := by
      apply Units.ext
      funext w
      have e1 := hpos (w.embedding.comp (algebraMap _ E))
      have e2 : ‖w.embedding ((x : maximalRealSubfield E) : E)‖ = w ((x : maximalRealSubfield E) : E) :=
        InfinitePlace.norm_embedding_eq w _
      change Complex.exp (z w) * starRingEnd ℂ (Complex.exp (z w)) = pInf E (algebraMap E (Ad E) ((x : maximalRealSubfield E) : E)) w
      rw [pInf_algebraMap, ← Complex.exp_conj, Complex.conj_ofReal, ← Complex.exp_add, ← Complex.ofReal_add,
        ← Complex.ofReal_exp, show Real.log (w ((x : maximalRealSubfield E) : E)) / 2 + Real.log (w ((x : maximalRealSubfield E) : E)) / 2 =
          Real.log (w ((x : maximalRealSubfield E) : E)) by ring, Real.exp_log (e2 ▸ e1.2), ← e2]
      exact e1.1
    have hN : ideleNorm E (infId E u) = infDiag x := GlobalTheory.T.ideleMapOfAlgebra_maximalRealSubfield_injective E (by rw [GlobalTheory.T.ideleMap_normToMaxReal_infiniteIdele, hu, ← InfType.infDiag_eq, GlobalTheory.T.ideleMap_infDiag_maxRealSubfield_cm])
    have e1 : ((χ.inf x : ℂˣ) : ℂ) = ((chiInf (compNorm E χ) u : ℂˣ) : ℂ) := by
      rw [HChar.inf, MonoidHom.comp_apply, ← hN]; rfl
    rw [e1, chiInf_eq_prod _ k hk]
    let g : (maximalRealSubfield E →+* ℂ) → ℂ := fun φ =>
      Complex.exp ((Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 : ℝ) : ℂ)
    have hc : ∀ τ : E →+* ℂ, coord τ (u : Cinf E) = g (τ.comp (algebraMap _ E)) := by
      intro τ
      rw [coord_expU]
      congr 1
      have e3 : z (InfinitePlace.mk τ) = ((Real.log ‖(τ.comp (algebraMap (maximalRealSubfield E) E)) (x : maximalRealSubfield E)‖ / 2 : ℝ) : ℂ) := by
        simp only [z, InfinitePlace.apply]; rfl
      unfold coord
      split_ifs
      · exact e3
      · change starRingEnd ℂ (z (InfinitePlace.mk τ)) = _
        rw [e3, Complex.conj_ofReal]
    simp only [hc]
    rw [hn g]
    refine Finset.prod_congr rfl fun φ _ => ?_
    rw [zpow_mul, zpow_two, ← Complex.exp_add, ← Complex.ofReal_add, ← Complex.ofReal_exp,
      show Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 + Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 =
        Real.log ‖φ (x : maximalRealSubfield E)‖ by ring, Real.exp_log (hpos φ).2, (hpos φ).1]
  have hpar := UpperTheory.heckeChar_parallel_weight (maximalRealSubfield E) χ n hAlg
  obtain ⟨φ₀⟩ : Nonempty (maximalRealSubfield E →+* ℂ) := inferInstance
  refine ⟨(a : ℤ) - 1 - n φ₀, fun τ => ?_⟩
  have hconj : τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom = ComplexEmbedding.conjugate τ := by
    ext x
    exact IsCMField.complexEmbedding_complexConj E τ x
  have hb : expo ψ⁻¹ τ = -(n φ₀ : ℂ) := by
    rw [GlobalTheory.RegAlgCharAlg.expo_inv', hk, hkn, hpar _ φ₀]
  rw [hconj, key]
  refine Multiset.map_congr rfl fun z _ => ?_
  rw [hb]
  push_cast
  ring

end GlobalTheory.PolarizedWeight
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem _root_.GlobalTheory.T.kernelFunctions_common_linearOperator_off_splitPrime : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.LatAll → B.VecP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ T : (TaylorLogMetric.VC D a b → ℂ) →ₗ[ℂ] (TaylorLogMetric.VC D a b → ℂ), ∀ i, kerTh B χ SS cl (N i) (N' i) Ξ = T (B.eNat χ a b (N i) (N' i)) := by
  first | exact @GlobalTheory.KerCommon.kerTh_common_op | exact GlobalTheory.KerCommon.kerTh_common_op | (intros; apply GlobalTheory.KerCommon.kerTh_common_op <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem _root_.GlobalTheory.T.kernel_theta_unitary_lattice_equivariant : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N N' → DatLoc D cc SS cl N N' Ξ → ∀ (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → kerTh B χ SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) = TaylorLogMetric.pull D B.tor e e' (kerTh B χ SS cl N N' Ξ) := by
  first | exact @GlobalTheory.TwU.KerMove.kerTh_move | exact GlobalTheory.TwU.KerMove.kerTh_move | (intros; apply GlobalTheory.TwU.KerMove.kerTh_move <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem datLoc_of_move : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : HomE D.host.E a b → ℂ) (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → DatLoc D cc SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) → DatLoc D cc SS cl N N' Ξ := by
  intro D cc a b SS cl N N' Ξ e e' he he' h x x' hx
  have hs : star e * e = 1 := mul_eq_one_comm.1 he
  have hs' : star e' * e' = 1 := mul_eq_one_comm.1 he'
  have hRR : ∀ y : HomE D.host.E a b, Matrix.toLin' (star e') ∘ₗ (KerMove.RR (star e) (star e') y) ∘ₗ Matrix.toLin' e = y := by
    intro y
    refine LinearMap.ext fun v => ?_
    simp only [KerMove.RR_apply, LinearMap.comp_apply, star_star]
    rw [← LinearMap.comp_apply (Matrix.toLin' (star e')) (Matrix.toLin' e'), ← Matrix.toLin'_mul, hs', Matrix.toLin'_one,
      LinearMap.id_apply, ← LinearMap.comp_apply (Matrix.toLin' (star e)) (Matrix.toLin' e), ← Matrix.toLin'_mul, hs,
      Matrix.toLin'_one, LinearMap.id_apply]
  have key := h (KerMove.RR (star e) (star e') x) (KerMove.RR (star e) (star e') x') (fun P hP => by
    have h1 := KerMove.localization_map₂ (D := D) (KerMove.RR (star e) (star e')) _ _
      (fun z hz => KerMove.perO_map (aaOf D cc) N (SDLat.smulLat e N) N' (SDLat.smulLat e' N') (KerMove.RR (star e) (star e'))
        (fun w hw => KerMove.homO_RR_inv e e' he N N' w hw) z hz) P _ (hx P hP)
    rwa [map_smul, map_sub] at h1)
  simpa only [hRR] using key

end GlobalTheory.TwV

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut

theorem _root_.GlobalTheory.T.sphericalDoubleCosetSum_scalar_irreducible_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  first | exact @GlobalTheory.HeckeScalarDC.dc_scalar | exact GlobalTheory.HeckeScalarDC.dc_scalar | (intros; apply GlobalTheory.HeckeScalarDC.dc_scalar <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.orthonormalLocalBasis_coordinates_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ w z a b₀ a₁ b₁, ∑ i, hK D lam P P' b w a b₀ i * gK D lam P P' b z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b₀ = b₁ then 1 else 0 := by
  first | exact @GlobalTheory.KerStd.HypCoord.hK_gK_dual | exact GlobalTheory.KerStd.HypCoord.hK_gK_dual | (intros; apply GlobalTheory.KerStd.HypCoord.hK_gK_dual <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

theorem _root_.GlobalTheory.T.fixed_of_fixed_by_local_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → ∀ φ : UA E a → ℂ, IsAutFormU φ → (∀ w, Apart w w₀ → ∀ x ∈ H w, RU E a x φ = φ) → ∀ x ∈ GlobalTheory.Cong.AdaptLev.levelOf a w₀ H, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.AdaptLev.fixed_of_levelOf) | (exact GlobalTheory.Cong.AdaptLev.fixed_of_levelOf) | (intros; apply GlobalTheory.Cong.AdaptLev.fixed_of_levelOf  <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

theorem _root_.GlobalTheory.T.autForm_fixed_by_integralPoints_almostAllPlaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ : UA E a → ℂ), IsAutFormU φ → ∀ᶠ w in Filter.cofinite, ∀ x ∈ GlobalTheory.Cong.AdaptLev.intU a w, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.AutFormFix.fixed_intU_eventually) | (exact GlobalTheory.Cong.AutFormFix.fixed_intU_eventually) | (intros; apply GlobalTheory.Cong.AutFormFix.fixed_intU_eventually  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.inverse_series_formalGroup_iso_integral : ∀ (l : ℕ) [Fact l.Prime] (g : Formalism.MainNotions.GL3Theta.G1 l), g.Ok → ∀ (hLT : Formalism.L2.G.Pend.LTIso g) (n : ℕ), ‖PowerSeries.coeff n (Formalism.L2.KerInert.BeCob.vLT hLT)‖ ≤ 1 := by
  first | exact @GlobalTheory.InverseSeriesIntegral.v_integral | exact GlobalTheory.InverseSeriesIntegral.v_integral | (intros; apply GlobalTheory.InverseSeriesIntegral.v_integral <;> assumption)
end
