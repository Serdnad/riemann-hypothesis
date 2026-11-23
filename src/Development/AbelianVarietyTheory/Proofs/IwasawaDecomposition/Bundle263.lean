module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThOrth

open Formalism.IndefR.CxPass.LevelOperators

theorem theta_eq_zero_of_orth {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {F : Type} [AddCommGroup F] [Module K F]
    {σ : K →+* ℂ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {j : F →ₛₗ[σ] V} {r : Representation K G F} {ρ : G → V →ₗ[ℂ] V} {gE : Representation ℂ G E} {Θ : V →ₗ[ℂ] E}
    (H : Hyp σ j r ρ gE Θ)
    (hRZ : Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint Θ)).comap j : Set F)) =
      LinearMap.range (LinearMap.adjoint Θ))
    (e a : MonoidAlgebra K G) (he : opF r e ∘ₗ opF r e = opF r e)
    (hfix : ∀ y ∈ LinearMap.range Θ, opV σ (fun g => gE g) a y = y) (f : F) (hea : opF r e f = opF r a f)
    (horth : ∀ z ∈ ((LinearMap.range (LinearMap.adjoint Θ)).comap j ⊓ LinearMap.range (opF r e) : Submodule K F),
      ⟪j z, j f⟫_ℂ = 0) : Θ (j f) = 0 := by
  have h1 : Θ (j (opF r e f)) = Θ (j f) := by
    rw [hea, j_opF H.jr, theta_opV H.sp H.jr H.eq, hfix _ ⟨_, rfl⟩]
  have h2 : j (opF r e f) ∈ LinearMap.range (opV σ ρ e) := ⟨j f, (j_opF H.jr e f).symm⟩
  obtain ⟨u', hu', hθ⟩ := H.dn e he h2
  have hu'' : u' ∈ Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓
      LinearMap.range (opF r e) : Submodule K F) : Set F)) := by
    rw [H.ratLev hRZ e he]
    exact hu'
  have h3 : ⟪u', j f⟫_ℂ = 0 := by
    have hle : Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓
        LinearMap.range (opF r e) : Submodule K F) : Set F)) ≤ (Submodule.span ℂ {j f})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact horth z hz
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu'')
  obtain ⟨⟨w, rfl⟩, -⟩ := hu'
  have h4 : Θ (LinearMap.adjoint Θ w - j f) = 0 := by
    rw [map_sub, hθ, h1, sub_self]
  have h5 : ⟪LinearMap.adjoint Θ w, LinearMap.adjoint Θ w - j f⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left, h4, inner_zero_right]
  rw [inner_sub_right, h3, sub_zero, inner_self_eq_zero] at h5
  rw [← h1, ← hθ, h5, map_zero]

theorem opF_lvlIdem_fix {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (H : Subgroup G) (ψ : H →* Kˣ) (v : V)
    (hv : ∀ a : H, ρ a.1 v = ((ψ a : Kˣ) : K) • v) : opF ρ (lvlIdem H ψ) v = v := by
  classical
  rw [opF_eq_lift]
  unfold lvlIdem

  rw [map_sum, LinearMap.sum_apply]
  have : ∀ h : H, MonoidAlgebra.lift K (V →ₗ[K] V) G ρ
      (MonoidAlgebra.single (h : G) ((Nat.card H : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K))) v = (Nat.card H : K)⁻¹ • v := by
    intro h
    rw [MonoidAlgebra.lift_single, LinearMap.smul_apply, hv, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, mul_one]
  rw [Finset.sum_congr rfl fun h _ => this h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), one_smul]

end GlobalTheory.Mem.ThOrth

namespace GlobalTheory.Mem.ThOrth

open Formalism.IndefR.CxPass.LevelOperators



theorem thG_eq_zero_of_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y _Z hP hH i t x hx
  have hok := hH.ok
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak hP.char hH.aux.ex
  have hM := hc.models
  have hCore : GlobalTheory.Hk3.Core R.toRealDat F.lv2 := ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
  have hL := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hok.ok2.irr i
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hM
  have hJ : (R.toCx3 F).JIsoL F.cv := Formalism.IndefR.Links.RealDat3.jIsoL_of (F := F) hM
  have hRZ : (R.toCx3 F).RatZ := (complex_data_conditions_base_level_of_primitive_links hok hH.sep hP.char hH.prim).ratZ
  have hjr (g : G) (v : A3.fam3.amb3.FL i t) :
      (R.toCx3 F).jL i t ((A3.A.fam.L i t).r g v) =
        (R.toCx3 F).opLC i t (Sum.inr g) ((R.toCx3 F).jL i t v) := by
    have hb := hK i t
    have key : ∀ k : Module.Basis.ofVectorSpaceIndex D.what₂.LL (A3.fam3.amb3.FL i t),
        (R.toCx3 F).opLC i t (Sum.inr g) ((R.toCx3 F).jL i t (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t) k)) =
        (R.toCx3 F).jL i t ((A3.A.fam.L i t).r g (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t) k)) := by
      intro k
      unfold Formalism.IndefR.Cx.CxData.opLC
      rw [dite_eq_left hb]
      have e : (R.toCx3 F).jL i t (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t) k) = Module.Basis.mk hb.1 hb.2.ge k :=
        (Module.Basis.mk_apply hb.1 hb.2.ge k).symm
      rw [e, Module.Basis.constr_basis]
      rfl
    have hh := Module.Basis.ext (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t))
      (f₁ := ((R.toCx3 F).jL i t).comp ((A3.A.fam.L i t).r g))
      (f₂ := ((R.toCx3 F).opLC i t (Sum.inr g)).comp ((R.toCx3 F).jL i t))
      (fun k => (key k).symm)
    exact LinearMap.congr_fun hh v
  have H : Hyp A3.fam3.base3.v0.embedding ((R.toCx3 F).jL i t) (A3.A.fam.L i t).r
      (fun g => (R.toCx3 F).opLC i t (Sum.inr g)) (R.gWx F i) ((R.toCx3 F).θ' i t) := by
    refine ⟨Formalism.IndefR.CxPass.lift_embeddings_span hK i t, hjr, ?_, hH.prim.gEquiv.2 i t, hH.prim.gUnit.2 i⟩
    intro g a b
    rw [hJ i t, hJ i t]
    change A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _) =
      A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _)
    set_option backward.isDefEq.respectTransparency false in
      rw [CSDForm.csumForm_apply, CSDForm.csumForm_apply]
    exact congrArg A3.fam3.base3.v0.embedding ((hok.ok2.lifts i t).act.unitary g a b)
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 := ⟨hok.ok2.conj, hok.ok2.irr, hok.ok2.lifts i t⟩

  have hopE : opV A3.fam3.base3.v0.embedding (fun g => R.gWx F i g) (idemOf A3.A.X) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i) := by
    let mA : ((R.HW i (sg0 D A3.A)).H →ₗ[ℂ] (R.HW i (sg0 D A3.A)).H) →+
        (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H →ₗ[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H) :=
      { toFun := Tw.map (twAt D.what₂.embLL A3.A.v0), map_zero' := LinearMap.ext fun _ => rfl,
        map_add' := fun _ _ => LinearMap.ext fun _ => rfl }
    rw [show Tw.map (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i) = mA (GlobalTheory.Hk3.eH R.toRealDat i) from rfl]
    unfold opV GlobalTheory.Hk3.eH

    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => LinearMap.ext fun y => ?_
    show cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((idemOf A3.A.X).coeff g)) •
        R.gW i (sg0 D A3.A) g (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) y) =
      RealDat.eC (A := A3.A) (sg0 D A3.A) g •
        R.gW i (sg0 D A3.A) g (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) y)
    rw [Formalism.IndefR.Links.emb_eq D.what₂.embLL A3.A.v0, Formalism.IndefR.Links.cj_cj]
    rfl
  have hθ : ∀ (u : (R.toCx3 F).FLC i t),
      Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) =
        cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u) :=
    fun u => rfl
  have hfix : ∀ y ∈ LinearMap.range ((R.toCx3 F).θ' i t),
      opV A3.fam3.base3.v0.embedding (fun g => R.gWx F i g) (idemOf A3.A.X) y = y := by
    rintro _ ⟨u, rfl⟩
    rw [hopE]
    change Tw.mk (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i
      (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u))) =
      (R.toCx3 F).θ' i t u
    rw [hθ, map_smul, hL.2.2.2, ← hθ]
    rfl

  set ℓ := A3.A.fam.lvlA F.P0 F.ψ0 with hℓ
  set f0 := liftForm A3.A F.P0 F.ψ0 i t x with hf0
  have hf0l : f0 = GlobalTheory.Mem.LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r ℓ.P ℓ.ψ x := rfl
  have hlev : f0 ∈ lvlForms (A3.A.fam.L i t).S (A3.A.fam.L i t).r ℓ.P ℓ.ψ := by
    rw [← GlobalTheory.Mem.LiftForms.range_lvlForm]
    exact ⟨x, hf0l.symm⟩
  have hfix0 : opF (A3.A.fam.L i t).r (lvlIdem ℓ.P ℓ.ψ) f0 = f0 := by
    exact opF_lvlIdem_fix (A3.A.fam.L i t).r ℓ.P ℓ.ψ f0 hlev
  have hea : opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ) f0 = opF (A3.A.fam.L i t).r (idemOf A3.A.X) f0 := by
    rw [goodAt, opF_mul, LinearMap.comp_apply, hfix0]
    rfl
  have horth : ∀ z ∈ ((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) ⊓
      LinearMap.range (opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) : Submodule _ _),
      ⟪(R.toCx3 F).jL i t z, (R.toCx3 F).jL i t f0⟫_ℂ = 0 := by
    intro z hz
    have hZeq : (((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t)) ⊓
        LinearMap.range (opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) : Submodule _ _) =
        LinearMap.range ((A3.A.fam.L i t).toF ℓ ((R.toCx3 F).Zl i t)) := by
      refine Eq.trans ?_ (Formalism.IndefR.CxPass.LevelOperators.range_toF (A3.A.fam.L i t) ℓ _).symm
      rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq]
      rfl
    have hz' : z ∈ LinearMap.range ((A3.A.fam.L i t).toF ℓ ((R.toCx3 F).Zl i t)) := hZeq ▸ hz
    obtain ⟨c, rfl⟩ := hz'
    rw [← GlobalTheory.Mem.LiftForms.lvlForm_lE hB c]
    refine (hJ i t _ _).trans ?_
    have h0 : Formalism.DivisionValues.hform ((A3.A.fam.L i t).S.lvlH (A3.A.fam.L i t).r ℓ.P ℓ.ψ)
        ((A3.A.fam.L i t).lE ℓ ((R.toCx3 F).Zl i t) *ᵥ c) x = 0 := hx c
    show A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _) = 0
    rw [CSDForm.csumForm_apply, hf0l, GlobalTheory.Mem.LiftForms.csum_lvlForm, h0, mul_zero, map_zero]
  have key := theta_eq_zero_of_orth H (hRZ.2 i t) (goodAt ℓ.X ℓ.P ℓ.ψ) (idemOf A3.A.X)
    (opF_goodAt_idem _ _ hok.ok2.irr _ _) hfix f0 hea horth
  have h2 := congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) key
  rw [hθ, hP.phs i, map_one, one_smul] at h2
  exact h2

end GlobalTheory.Mem.ThOrth

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta.StepLevFock

theorem om_ptY_of_finite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ GfC (Yc D k), ∀ κ' ∈ GfC (Yc D (k + 1)), ∀ c : ℂ, R.ωY t k (κ, κ') (R.vY t k) = c • R.vY t k → ∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH t k hk κ hκ κ' hκ' c hc φ
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hP.char.base.chain hH.aux.ex
  exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ (R.ωY t k) hP.char.base.models.inf (hch.ωY t k hk)
    _ _ _ _ (R.vY t k) (hch.ptY t k hk) κ hκ κ' hκ' c hc φ

end GlobalTheory.Mem.R3.DTheta.StepLevFock
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def reFaceErr (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : type_of% R.err0 :=
  fun w _ => errOf ((R.toCx3 F).data (reFace F Dc Sp Zsc).cr false) ((reFace F Dc Sp Zsc).fc (R.toCx3 F).zs).Z.F0 w



private theorem toCx3_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    R.toCx3 (reFace F Dc Sp Zsc) = R.toCx3 F := by
  dsimp only [RealDat3.toCx3, reFace, Face3.lv2]
  rfl

private theorem toCx3_withErr (R : RealDat3 D A3 Ks) (F : Face3 D A3) (e : type_of% R.err0) :
    (R.withErr e).toCx3 F = reErr (R.toCx3 F) e := by
  dsimp only [RealDat3.toCx3, RealDat3.withErr, reErr]
  rfl

private theorem errOf_data_reErr {K : Type} [Field K] [NumberField K] [StarRing K]
    {Bs : DefBase K} {Am : DefAmb Bs} (X : CxData Am) (e : type_of% X.err0)
    {fc : DefSub Am → DefFace Bs} (cr : Crd Am fc) (w : HeightOneSpectrum (𝓞 K)) :
    errOf ((reErr X e).data cr false) (fc (reErr X e).zs).Z.F0 w =
      errOf (X.data cr false) (fc X.zs).Z.F0 w := by
  dsimp only [errOf, IndefData.Iw, CxData.data, CxData.liftMat, CxData.liftMatC, CxData.tC,
    CxData.w0C, CxData.wC, CxData.zs, CxData.Z, CxData.Zl, reErr]
  rfl


theorem reFace_errEq (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    ErrEq (R.withErr (reFaceErr R F Dc Sp Zsc)) (reFace F Dc Sp Zsc) := by
  intro w j
  let F' := reFace F Dc Sp Zsc
  let e := reFaceErr R F Dc Sp Zsc
  change e w j = errOf (((R.withErr e).toCx3 F').data F'.cr false)
    (F'.fc ((R.withErr e).toCx3 F').zs).Z.F0 w
  rw [toCx3_withErr, toCx3_reFace, errOf_data_reErr]
  rfl



theorem reFace_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : Keep (A3 := A3) R.toRealDat F.lv2 cG) :
    Keep (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 cG :=
  ⟨h.std, h.signs, h.frames, h.beta, h.prX, h.grp, h.psi, h.guard, h.valKs, h.frameKs, h.levKs⟩



theorem reFace_keep_back (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0)
    (h : Keep (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 cG) : Keep (A3 := A3) R.toRealDat F.lv2 cG :=
  ⟨h.std, h.signs, h.frames, h.beta, h.prX, h.grp, h.psi, h.guard, h.valKs, h.frameKs, h.levKs⟩



theorem reFace_scal (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hl6 : ∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨
      ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v))
    (hs : R.IsScal F) : R.IsScal (reFace F Dc Sp Zsc) := by
  refine ⟨hs.lam0, hs.kap, hs.off, fun i t p hp => ?_, fun i p v hv hp => ?_, hs.tup⟩
  · refine (hs.abs0 i t p hp).trans ?_
    rcases hl6 i with h | h
    · exact congrArg Real.exp h.symm
    · exact absurd hp (h.1 p)
  · refine (hs.abs i p v hv hp).trans ?_
    rcases hl6 i with h | h
    · exact congrArg Real.exp h.symm
    · exact absurd (h.2 p v hv) hp



theorem reFace_pins (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0)
    (hl6 : ∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨
      ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v))
    (hP : Pins R F cG) : Pins (R.withErr e) (reFace F Dc Sp Zsc) cG := by
  have h := RealDat3.weak_characterisation_with_error hP.char e
  have hl6' : ∀ i, (Zsc ((R.withErr e).toCx3 F).zs).l6m i = (F.Zsc ((R.withErr e).toCx3 F).zs).l6m i ∨
      ((∀ p, (R.withErr e).Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → (R.withErr e).PartAt F i p v) := fun i => by
    rw [RealDat3.zs_withErr]
    exact (hl6 i).imp id fun h => ⟨h.1, fun p v hv => (RealDat3.partAt_withErr e i p v).2 (h.2 p v hv)⟩
  exact ⟨⟨h.base, h.inert, h.fullY, h.fullX, h.fullP, reFace_scal (R.withErr e) F Dc Sp Zsc hl6' h.scal, h.tup, h.phase, h.allPl⟩,
    reFace_keep R F cG Dc Sp Zsc e hP.keep, hP.phs, hP.trSem⟩



theorem further_face_statements_independent_of_error (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : UnusedChoiceStatements R F) :
    UnusedChoiceStatements (R.withErr e) (reFace F Dc Sp Zsc) :=
  ⟨⟨h.ex.ItY, h.ex.ItX, h.ex.ioY, h.ex.ioX, h.ex.Th, h.ex.ioP, h.ex.thF, h.ex.thG⟩, h.conj, h.levelW, h.integral⟩



def reFaceRead (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) : Read (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 X0 :=
  { Y with
    mj := ⟨Y.mj.eW, Y.mj.eW_range, Y.mj.eW_norm, Y.mj.eW_lat⟩
    cen0 := fun cG hK => Y.cen0 cG (reFace_keep_back R F cG Dc Sp Zsc e hK)
    cen1 := fun cG hK => Y.cen1 cG (reFace_keep_back R F cG Dc Sp Zsc e hK) }



def reFaceReadL (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ReadL (R.withErr e) (reFace F Dc Sp Zsc) X0 (reFaceRead R F Dc Sp Zsc e X0 Y) :=
  { Z with }

end GlobalTheory.Mem.R3

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem reFace_prim (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : PrimRows3 R F) :
    PrimRows3 (R.withErr e) (reFace F Dc Sp Zsc) := by
  -- Expose the constructors so Lean can reduce projections of the updated records directly.
  obtain ⟨R₂, _, _, _, _⟩ := R
  cases R₂
  cases F
  dsimp only [RealDat3.withErr, reFace]
  obtain ⟨⟨hE, hR⟩, ⟨hW, hL⟩⟩ := h.hecke
  exact
  { heckeR := h.heckeR
    heckeL := h.heckeL
    hecke := ⟨⟨hE, ⟨hR.intw, hR.comm, hR.parts⟩⟩, ⟨hW, ⟨hL.intw, hL.comm, hL.parts⟩⟩⟩
    gUnit := h.gUnit
    gEquiv := h.gEquiv
    block := h.block
    rowTest := h.rowTest
    liftTest := h.liftTest
    liftTestB := h.liftTestB
    liftOnto := fun hW' hh => h.liftOnto hW' ⟨hh.intw, hh.comm, hh.parts⟩
    pos := h.pos
    posScal := h.posScal
    levE := h.levE
    h2P := h.h2P
    thmB := h.thmB
    sumE := h.sumE
    unif := h.unif
    mLat := h.mLat
    levW := h.levW
    thmA := h.thmA
    sumW := h.sumW
    scalConj := h.scalConj
    dimParts := h.dimParts }

end GlobalTheory.Mem.R3

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

open scoped ComplexOrder

namespace GlobalTheory.Mem.FramePos

open Formalism.L2.DIV

theorem majAt_XQ_ne_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 : Type} {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ}
    (h : BlockHyp B ℓ v0 s) (Z : Submodule K B.S.Forms) (v : InfinitePlace K)
    (x : Fin (B.dZ ℓ Z) → K) (hx : x ≠ 0) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x x ≠ 0 := by
  have hP : Function.Surjective (B.Pq ℓ Z).mulVec := fun y =>
    ⟨(B.zE ℓ Z).mulVec y, by rw [Matrix.mulVec_mulVec, (BlockDat.lf_z_proj (Z := Z) h).1, Matrix.one_mulVec]⟩
  have hpos : (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)).PosDef :=
    (quotRestrPosDef _ _ _ (BlockDat.lf_HV_pos h v)).1 _ (map_surj _ _ hP)
  have hf := frameOfSpec _ _ hpos
  rw [majAt_eq]
  have e : B.XQ ℓ Z v = frameOf (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)) := rfl
  rw [e, hf.2]
  have hne : (fun i => v.embedding (x i)) ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := congrFun h0 i
    simpa using this
  exact (hpos.dotProduct_mulVec_pos hne).ne'

end GlobalTheory.Mem.FramePos


open GlobalTheory.Mem.FramePos in
theorem GlobalTheory.Mem.R3.framesBase_majAt_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL), v ≠ A3.A.v0 → ∀ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, x ≠ 0 → Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT i A3.A.μ0) v x x ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hH _ _ i v _ x hx
  have hok := hH.ok.ok2
  have hB : Formalism.L2.DIV.BlockHyp (A3.A.fam.L i A3.A.fam.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.fam.v0 1 :=
    ⟨hok.conj, hok.irr, hok.lifts i _⟩
  exact majAt_XQ_ne_zero hB _ v x hx
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.fullFlagLift_genericPoint_specializes_residue : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ q : Sp Y₁.Fn ⟶ Y₂.X, q ≫ f₂ = (ratOf Y₁).pt ≫ f₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt q → ∀ y : Y₁.X, (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = y → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X) → q (IsLocalRing.closedPoint Y₁.Fn) ⤳ genericPoint Y₂.X := by
  first | exact @GlobalTheory.FlagBundle.lift_specializes_genericPoint | exact GlobalTheory.FlagBundle.lift_specializes_genericPoint | (intros; apply GlobalTheory.FlagBundle.lift_specializes_genericPoint <;> assumption)
end
