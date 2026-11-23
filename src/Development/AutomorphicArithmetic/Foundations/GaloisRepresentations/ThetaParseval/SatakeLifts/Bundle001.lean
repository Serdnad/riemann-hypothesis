module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle036
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc

theorem UpperTheory.Gal.TP.Loc.contraUnit :
    UpperTheory.Gal.TP.Loc.ContraIrr → UpperTheory.Gal.TP.Loc.ContraUnit := by
  intro hci k _ _ _ _ n V _ _ ρ hsm hirr hu
  obtain ⟨B, hherm, hpos, hinv⟩ := hu
  have hnd : ∀ w : V, (∀ v : V, B v w = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := hpos w hne
    rw [hw w] at h1
    simp at h1
  obtain ⟨w0, hw0⟩ : ∃ w : V, w ≠ 0 := by
    by_contra hne
    push_neg at hne
    haveI : IsSimpleOrder (Subrepresentation ρ) := hirr
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    generalize (⊥ : Subrepresentation ρ) = a
    generalize (⊤ : Subrepresentation ρ) = b
    obtain ⟨A, hA⟩ := a
    obtain ⟨A', hA'⟩ := b
    congr 1
    ext x
    rw [hne x]
    simp only [Submodule.zero_mem]
  have hcirr : (contra ρ).IsIrreducible := (hci k n V ρ hsm hirr).1
  let S : V →ₗ⋆[ℂ] smoothPart ρ.dual :=
    LinearMap.codRestrict (smoothPart ρ.dual) B.flip fun w =>
      mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm w).mem_nhds (by simp)) fun g hg => by
        have hg' : ρ g w = w := hg
        ext a
        show B (ρ g⁻¹ a) w = B a w
        have h := hinv g (ρ g⁻¹ a) w
        rw [hg'] at h
        rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
  have hSapply (w a : V) : ((S w : smoothPart ρ.dual) : Module.Dual ℂ V) a = B a w := rfl
  have hcomm (g : GL (Fin n) k) (w : V) : S (ρ g w) = contra ρ g (S w) := by
    refine Subtype.ext (LinearMap.ext fun a => ?_)
    rw [contra_apply, hSapply, hSapply]
    have h := hinv g (ρ g⁻¹ a) w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    exact h
  have hbij : Function.Bijective S := by
    have hi : Function.Injective S := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      refine hnd w fun v => ?_
      have h := congrArg (fun l : smoothPart ρ.dual => (l : Module.Dual ℂ V) v) hw
      simpa [hSapply] using h
    refine ⟨hi, ?_⟩
    let R : Subrepresentation (contra ρ) :=
      { toSubmodule := LinearMap.range S
        apply_mem_toSubmodule := fun g l hl => by
          obtain ⟨w, rfl⟩ := hl
          exact ⟨ρ g w, hcomm g w⟩ }
    rcases hcirr.eq_bot_or_eq_top R with hR | hR
    · exfalso
      have h : S w0 ∈ R.toSubmodule := ⟨w0, rfl⟩
      rw [hR] at h
      exact hw0 (hi (by rw [(Submodule.mem_bot ℂ).1 h, map_zero]))
    · intro l
      have h : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨w, hw⟩ := h
      exact ⟨w, hw⟩
  let e := LinearEquiv.ofBijective S hbij
  let T : ↥(GlobalTheory.PRep.smoothPart ρ.dual) →ₗ⋆[ℂ] V := e.symm.toLinearMap
  have hST : ∀ f, S (T f) = f := fun f => e.apply_symm_apply f
  have hTS : ∀ w, T (S w) = w := fun w => e.symm_apply_apply w
  have hTg : ∀ g f, T (contra ρ g f) = ρ g (T f) := by
    intro g f
    rw [← hST f, ← hcomm, hTS, hTS]
  refine ⟨⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun f f' => B (T f') (T f))
    ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩, ⟨e, fun g x => hcomm g x⟩⟩
  · intro f₁ f₂ f'
    simp [map_add (f := _)]
  · intro c f f'
    simp [LinearMap.map_smulₛₗ]
  · intro f f₁ f₂
    simp [map_add (f := _)]
  · intro c f f'
    simp [LinearMap.map_smulₛₗ]
  · intro f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hherm (T f') (T f)
  · intro f hf
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hpos _ (fun h => hf (by rw [← hST f, h, map_zero]))
  · intro g f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [hTg, hTg]
    exact hinv g _ _
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lift_key (hK : UpperTheory.Gal.TP.Loc.KeepsSB) (hD : UpperTheory.Gal.TP.Loc.ModelDict)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    {ν b : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin n) k) V} {π : Representation ℂ (GL (Fin d) k) W}
    {β : SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] V →ₗ[ℂ] W}
    (hβ : ∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (Φ Φ' : SB (Matrix (Fin n) (Fin d) k)),
      (Φ' : Matrix (Fin n) (Fin d) k → ℂ) = GlobalTheory.SplitFlip.omA ν b g h Φ → ∀ v : V, β Φ' (σ g v) = π h (β Φ v))
    (g : GL (Fin n) k) (h : GL (Fin d) k) (Φ Φ' : SB (Matrix (Fin n) (Fin d) k))
    (Ψ Ψ' : Matrix (Fin d) (Fin n) k → ℂ)
    (hΦ : ∀ X, (Φ : Matrix (Fin n) (Fin d) k → ℂ) X = Ψ X.transpose)
    (hΦ' : ∀ X, (Φ' : Matrix (Fin n) (Fin d) k → ℂ) X = Ψ' X.transpose)
    (hΨ' : Ψ' = om b⁻¹ g h Ψ) (v : V) :
    β Φ' (src (ν * b) σ g v) = π h (β Φ v) := by
  have hmem : GlobalTheory.SplitFlip.omA ν b (GlobalTheory.SplitFlip.invT g) h (Φ : Matrix (Fin n) (Fin d) k → ℂ)
      ∈ SB (Matrix (Fin n) (Fin d) k) := (hK k n d).1 ν b _ h _ Φ.2
  have hfun : GlobalTheory.SplitFlip.omA ν b (GlobalTheory.SplitFlip.invT g) h (Φ : Matrix (Fin n) (Fin d) k → ℂ)
      = ((ν * b) (Matrix.GeneralLinearGroup.det g) : ℂ) • (Φ' : Matrix (Fin n) (Fin d) k → ℂ) := by
    have hΦf : (Φ : Matrix (Fin n) (Fin d) k → ℂ) = fun Y => Ψ Y.transpose := funext hΦ
    funext X
    rw [hΦf, hD k n d ν b g h Ψ X, Pi.smul_apply, smul_eq_mul, hΦ' X, hΨ']
  have hsub : (⟨_, hmem⟩ : SB (Matrix (Fin n) (Fin d) k))
      = ((ν * b) (Matrix.GeneralLinearGroup.det g) : ℂ) • Φ' := Subtype.ext hfun
  have key := hβ (GlobalTheory.SplitFlip.invT g) h Φ ⟨_, hmem⟩ rfl v
  rw [src_apply, map_smul, ← LinearMap.smul_apply, ← map_smul, ← hsub, key]

private theorem continuous_invT' {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} :
    Continuous (GlobalTheory.SplitFlip.invT : GL (Fin n) k →* GL (Fin n) k) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem UpperTheory.Gal.TP.Loc.pairOfLift :
    UpperTheory.Gal.TP.Loc.LeftSmooth → UpperTheory.Gal.TP.Loc.KeepsSB → UpperTheory.Gal.TP.Loc.ModelDict → UpperTheory.Gal.TP.Loc.Separates → UpperTheory.Gal.TP.Loc.PairOfLift := by
  intro hL hK hD hS k _ _ _ _ n d ν b V _ _ W _ _ σ π hν hb hπ ⟨β, hβ0, hβ⟩
  let tr : SB (Matrix (Fin d) (Fin n) k) → SB (Matrix (Fin n) (Fin d) k) :=
    fun Ψ => ⟨fun X => (Ψ : Matrix (Fin d) (Fin n) k → ℂ) X.transpose, (hK k n d).2 _ Ψ.2⟩
  have tr_add : ∀ Ψ₁ Ψ₂, tr (Ψ₁ + Ψ₂) = tr Ψ₁ + tr Ψ₂ := fun _ _ => rfl
  have tr_smul : ∀ (c : ℂ) Ψ, tr (c • Ψ) = c • tr Ψ := fun _ _ => rfl
  have hsm : ∀ (Ψ : SB (Matrix (Fin d) (Fin n) k)) (F : smoothPart π.dual),
      (F : Module.Dual ℂ W) ∘ₗ β (tr Ψ) ∈ smoothPart (src (ν * b) σ).dual := by
    intro Ψ F
    apply mem_smoothPart_of_nhds
    have hT : {g : GL (Fin n) k | ∀ Y : Matrix (Fin d) (Fin n) k,
        (Ψ : Matrix (Fin d) (Fin n) k → ℂ) (Y * (g : Matrix (Fin n) (Fin n) k))
          = (Ψ : Matrix (Fin d) (Fin n) k → ℂ) Y} ∈ nhds 1 := by
      have hc : Continuous (fun g : GL (Fin n) k => GlobalTheory.SplitFlip.invT g⁻¹) :=
        continuous_invT'.comp continuous_inv
      have h1 : (fun g : GL (Fin n) k => GlobalTheory.SplitFlip.invT g⁻¹) 1 = 1 := by simp
      have hpre := hc.tendsto' 1 1 h1 (hL k n d (tr Ψ))
      filter_upwards [hpre] with g hg Y
      have hval : ((GlobalTheory.SplitFlip.invT g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
          = (g : Matrix (Fin n) (Fin n) k).transpose := by
        rw [GlobalTheory.SplitFlip.invT_val, inv_inv]
      have hY := hg Y.transpose
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hY
      simp only [tr, hval, Matrix.transpose_mul, Matrix.transpose_transpose] at hY
      exact hY
    have hK0 : (KO k (Fin n) : Set (GL (Fin n) k)) ∈ nhds 1 :=
      GlobalTheory.SplitFlip.isOpen_KO.mem_nhds (one_mem _)
    have hker : ((detChar (Fin n) b).ker : Set (GL (Fin n) k)) ∈ nhds 1 :=
      (IsSmoothChar.detChar hb).mem_nhds (one_mem _)
    have hab1 : nabs k (1 : kˣ) = 1 := GlobalTheory.SplitFlip.nabs_of_valuation_eq_one (by simp)
    have hfix : {g : GL (Fin n) k | om b⁻¹ g 1 (Ψ : Matrix (Fin d) (Fin n) k → ℂ) = Ψ} ∈ nhds 1 := by
      filter_upwards [hT, hK0, hker] with g hgT hgK hgk
      have hdet : b (Matrix.GeneralLinearGroup.det g) = 1 := hgk
      have hab : nabs k (Matrix.GeneralLinearGroup.det g) = 1 :=
        GlobalTheory.SplitFlip.nabs_of_valuation_eq_one (GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hgK)
      funext x
      simp [om, hdet, hab, hab1, hgT]
    have hfix' := (continuous_inv.tendsto' (1 : GL (Fin n) k) 1 inv_one) hfix
    filter_upwards [hfix'] with g hg
    apply LinearMap.ext
    intro v
    rw [Representation.dual_apply]
    simp only [Module.Dual.transpose_apply, LinearMap.coe_comp, Function.comp_apply]
    congr 1
    have hk := lift_key hK hD hβ g⁻¹ 1 (tr Ψ) (tr Ψ) Ψ Ψ (fun _ => rfl) (fun _ => rfl) hg.symm v
    simpa using hk
  let B : SB (Matrix (Fin d) (Fin n) k) →ₗ[ℂ] smoothPart π.dual →ₗ[ℂ] smoothPart (src (ν * b) σ).dual :=
    LinearMap.mk₂ ℂ (fun Ψ F => ⟨(F : Module.Dual ℂ W) ∘ₗ β (tr Ψ), hsm Ψ F⟩)
      (fun Ψ₁ Ψ₂ F => by ext v; simp [tr_add])
      (fun c Ψ F => by ext v; simp [tr_smul])
      (fun Ψ F₁ F₂ => by ext v; simp)
      (fun c Ψ F => by ext v; simp)
  refine ⟨B, ?_, ?_⟩
  · intro hB
    obtain ⟨Φ0, hΦ0⟩ : ∃ Φ0, β Φ0 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hβ0 (LinearMap.ext hc)
    obtain ⟨v, hv⟩ : ∃ v, β Φ0 v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hΦ0 (LinearMap.ext hc)
    obtain ⟨l, hl⟩ := hS k d W π hπ _ hv
    let Ψ0 : SB (Matrix (Fin d) (Fin n) k) :=
      ⟨fun Y => (Φ0 : Matrix (Fin n) (Fin d) k → ℂ) Y.transpose, (hK k d n).2 _ Φ0.2⟩
    have htr : tr Ψ0 = Φ0 := Subtype.ext (funext fun X => by simp [tr, Ψ0])
    apply hl
    have := congrArg (fun B' : SB (Matrix (Fin d) (Fin n) k) →ₗ[ℂ] smoothPart π.dual →ₗ[ℂ]
      smoothPart (src (ν * b) σ).dual => ((B' Ψ0 l : smoothPart _) : Module.Dual ℂ V) v) hB
    simpa [B, htr] using this
  · intro g h Ψ Ψ' hΨ' F
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have key := lift_key hK hD hβ g h (tr Ψ) (tr Ψ') Ψ Ψ' (fun _ => rfl) (fun _ => rfl) hΨ'
      ((src (ν * b) σ) g⁻¹ v)
    have hv : (src (ν * b) σ) g ((src (ν * b) σ) g⁻¹ v) = v := by
      show ((src (ν * b) σ) g * (src (ν * b) σ) g⁻¹) v = v
      rw [← map_mul]
      simp
    rw [hv] at key
    simp only [B, LinearMap.mk₂_apply, contra_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [key]
    congr 1
    show (π h⁻¹ * π h) _ = _
    rw [← map_mul]
    simp
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def mulHomeo {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n d : ℕ}
    (a : (Matrix (Fin n) (Fin n) k)ˣ) (c : (Matrix (Fin d) (Fin d) k)ˣ) :
    Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun X := a.val * X * c.val
  invFun Y := (a⁻¹).val * Y * (c⁻¹).val
  left_inv X := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv Y := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private def transHomeo {k : Type} [TopologicalSpace k] {n d : ℕ} :
    Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin d) (Fin n) k where
  toFun X := X.transpose
  invFun Y := Y.transpose
  left_inv X := Matrix.transpose_transpose X
  right_inv Y := Matrix.transpose_transpose Y
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

private theorem comp_homeo_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {f : Y → ℂ} (hf : f ∈ SB Y) : (fun x => f (e x)) ∈ SB X :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

theorem UpperTheory.Gal.TP.Loc.keepsSB :
    UpperTheory.Gal.TP.Loc.KeepsSB := by
  intro k _ _ _ _ n d
  refine ⟨fun ν b g h Φ hΦ => ?_, fun Ψ hΨ => comp_homeo_mem_SB transHomeo hΨ⟩
  have hc := comp_homeo_mem_SB (mulHomeo g⁻¹ (GlobalTheory.SplitFlip.invT h)) hΦ
  have key : GlobalTheory.SplitFlip.omA ν b g h Φ =
      ((↑(ν (GlobalTheory.SplitFlip.gdet g))⁻¹ * ↑(b (GlobalTheory.SplitFlip.gdet h)) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (-↑(Fintype.card (Fin d)) / 2) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (-↑(Fintype.card (Fin n)) / 2) : ℂ) •
        fun X => Φ (mulHomeo g⁻¹ (GlobalTheory.SplitFlip.invT h) X)) := by
    funext X
    rfl
  rw [key]
  exact (SB _).smul_mem _ hc
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.leftSmooth :
    UpperTheory.Gal.TP.Loc.LeftSmooth := by
  intro k _ _ _ _ n d Φ
  obtain ⟨hlc, hcs⟩ := Φ.2
  have key : ∀ f : GL (Fin n) k → Matrix (Fin n) (Fin d) k → Matrix (Fin n) (Fin d) k,
      Continuous (fun p : GL (Fin n) k × Matrix (Fin n) (Fin d) k => f p.1 p.2) → (∀ X, f 1 X = X) →
      ∀ᶠ g in nhds (1 : GL (Fin n) k), ∀ X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ),
        (Φ : Matrix (Fin n) (Fin d) k → ℂ) (f g X) = (Φ : Matrix (Fin n) (Fin d) k → ℂ) X := by
    intro f hf h1
    apply hcs.isCompact.eventually_forall_of_forall_eventually
    intro X₀ _
    have e1 := (hlc.comp_continuous hf).eventually_eq (1, X₀)
    have e2 := (hlc.comp_continuous
      (continuous_snd : Continuous (Prod.snd : GL (Fin n) k × Matrix (Fin n) (Fin d) k → _))).eventually_eq (1, X₀)
    filter_upwards [e1, e2] with p hp1 hp2
    simp only [Function.comp] at hp1 hp2
    rw [hp1, hp2, h1]
  have hU1 := key (fun g X => (g : Matrix (Fin n) (Fin n) k) * X)
    ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd) (fun X => by simp)
  have hU2 := key (fun g X => ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X)
    ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul continuous_snd) (fun X => by simp)
  filter_upwards [hU1, hU2] with g hg1 hg2
  intro X
  by_cases hX : X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ)
  · exact hg1 X hX
  by_cases hgX : (g : Matrix (Fin n) (Fin n) k) * X ∈ tsupport (Φ : Matrix (Fin n) (Fin d) k → ℂ)
  · have := hg2 _ hgX
    rw [← Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hgX]
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem range_val_map_rev (t : ℕ) :
    (Finset.range t).val.map (fun i : ℕ => t - 1 - i) = (Finset.range t).val := by
  have hinj : ∀ i ∈ (Finset.range t).val, ∀ j ∈ (Finset.range t).val, t - 1 - i = t - 1 - j → i = j := by
    intro i hi j hj h
    simp only [Finset.mem_val, Finset.mem_range] at hi hj
    omega
  rw [Multiset.Nodup.ext (Multiset.Nodup.map_on hinj (Finset.range t).nodup) (Finset.range t).nodup]
  intro y
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hy
    exact ⟨t - 1 - y, by omega, by omega⟩

private theorem npowU_neg {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) :
    GlobalTheory.LFun.npowU w (-z) = (GlobalTheory.LFun.npowU w z)⁻¹ := by
  ext
  rw [Units.val_inv_eq_inv_val, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.coe_npowU]
  unfold GlobalTheory.LFun.npow
  exact Complex.cpow_neg _ _

theorem UpperTheory.Gal.TP.Loc.segInv :
    UpperTheory.Gal.TP.Loc.SegInv := by
  intro K _ _ w x t
  unfold GlobalTheory.LFun.seg
  rw [Multiset.map_map]
  conv_rhs => rw [← range_val_map_rev t, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i hi
  simp only [Finset.mem_val, Finset.mem_range] at hi
  simp only [Function.comp_apply, mul_inv, ← npowU_neg]
  congr 2
  rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + i ≤ t)]
  push_cast
  ring
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.srcGood :
    UpperTheory.Gal.TP.Loc.SrcGood := by
  intro k _ _ _ _ n c V _ _ σ hc hu hs hirr hun
  have hcont : Continuous (GlobalTheory.SplitFlip.invT : GL (Fin n) k →* GL (Fin n) k) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun h : GL (Fin n) k => ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose
      exact Units.continuous_coe_inv.matrix_transpose
    · show Continuous fun h : GL (Fin n) k => (h : Matrix (Fin n) (Fin n) k).transpose
      exact Units.continuous_val.matrix_transpose
  refine ⟨?_, ?_, ?_⟩
  · exact isSmooth_twist (isSmooth_comp hs _ hcont) hc.detChar
  · have ht {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
        {ρ : Representation ℂ G W} (hρ : ρ.IsIrreducible) (χ : G →* ℂˣ) :
        (twist ρ χ).IsIrreducible := by
      let e : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          have h := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          simpa [twist_apply, smul_smul] using h⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
      exact e.isSimpleOrder_iff.2 hρ
    exact ht (GlobalTheory.InvTransposeEnds.isIrreducible_comp hirr _
      fun h => ⟨GlobalTheory.SplitFlip.invT h, GlobalTheory.SplitFlip.invT_invT h⟩) _
  · obtain ⟨B, h1, h2, h3⟩ := hun
    refine ⟨B, h1, h2, fun g v w => ?_⟩
    rw [src_apply, src_apply, LinearMap.map_smul B, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h3,
      smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have hn := hu (Matrix.GeneralLinearGroup.det g)
    rw [show ((c (Matrix.GeneralLinearGroup.det g) : ℂ) * (starRingEnd ℂ) (c (Matrix.GeneralLinearGroup.det g) : ℂ)) = 1 by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_num, one_mul]
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.modelDict :
    UpperTheory.Gal.TP.Loc.ModelDict := by
  intro k _ _ _ _ n d ν b g h Ψ X
  have hM : ((((GlobalTheory.SplitFlip.invT g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
      ((GlobalTheory.SplitFlip.invT h : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)).transpose =
      ((h⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) * X.transpose * (g : Matrix (Fin n) (Fin n) k) := by
    rw [GlobalTheory.SplitFlip.invT_inv_val, GlobalTheory.SplitFlip.invT_val, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hg := nabs_pos k (Matrix.GeneralLinearGroup.det g)
  have hh := nabs_pos k (Matrix.GeneralLinearGroup.det h)
  unfold GlobalTheory.SplitFlip.omA om
  rw [GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.apow_inv]
  beta_reduce
  rw [hM]
  simp only [GlobalTheory.SplitFlip.apow, GlobalTheory.SplitFlip.gdet, Fintype.card_fin]
  rw [Complex.ofReal_cpow hg.le, Complex.ofReal_cpow hh.le]
  simp only [map_inv, inv_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    neg_div, neg_neg, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have hb : ((b (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.separates :
    UpperTheory.Gal.TP.Loc.Separates := by
  intro k _ _ _ _ n V _ _ ρ hρ v hv
  exact GlobalTheory.ContraRefl.exists_smooth_form_ne hρ (GlobalTheory.ThetaLiftGL.compactOpen_basis k n) hv
end
