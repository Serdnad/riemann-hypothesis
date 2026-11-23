module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle347
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle351
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle345
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle346
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

namespace GlobalTheory.LocMod.GSuppTwo

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hz_link (p : Place D k) {σ : ℕ} {B : BesLev D (σ + 1)} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) :
    p.hz B = -p.xi ^ 2 * p.hz B' := by
  unfold Place.hz Place.xi Place.pr
  rw [l.norm, map_mul, map_mul, map_mul, map_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, map_neg]
  ring

theorem isComp_inv (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) :
    p.IsComp χ μ⁻¹ := by
  intro x a ha
  have h1 := h x a ha
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at h1 ⊢
  rw [h1, inv_inv]

theorem isLoc_one (p : Place D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) :
    p.IsLoc F 1 1 := by
  refine ⟨fun i j => by simp [Formalism.L2.Theta.mt], ?_⟩
  have : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
  simp [F.βγ]

theorem gsupp2_std : ∀ (D : D7), OmLoc D → FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s) (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (GlobalTheory.StepData.XIx (Fin κ) t j) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1)) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank),
    p.IsComp s₂.χV⁻¹ (S.μ (j + 1 + 1)) →
  ∀ T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂, Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) →
    Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) →
  ∀ h, SuppAt p.e B'.V h → GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ Φ₁)) (flatFB s₂ (s₂.om (1, h) (T₂ Φ₂))) ≠ 0 →
    ∃ r ∈ besGrp B'.d B'.o, SuppAt p.e B'.V r ∧
      ∃ u uk, p.IsLoc F.G₂ u uk ∧ uk ∈ ((S.T t).lev (j + 1 + 1) (c + 1) (by omega)).J ∧ h = r * u := by
  intro D hOm hBF hFB hCo hSym k _ _ _ _ p s κ S t _ _ ψ hstd hψ j c H σ B J B' F s₁ s₂ l vL hμ T₁ T₂ hT₁ hT₂
    Φ₁ Φ₂ hΦ₁ hΦ₂ h hh hne
  let _ : MeasurableSpace k := borel k
  have _ : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol k
  have _ := hν.1
  have hc : c = 2 * σ := by have := F.bes'.1; omega
  obtain ⟨-, hchar, hxi, -, hcomp⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hstd
  have hcont : Continuous S.ψ := (hchar S.ψ hψ).1
  obtain ⟨μT, hμT⟩ := hcomp s₂.χW
  have hμS := isComp_inv p hμ
  obtain ⟨hL1, hL2, hL3⟩ := (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).1 B'.V _ F.G₂
  obtain ⟨hk, hhk⟩ := hL2 h hh

  let Φ₂' : SB (Matrix (GlobalTheory.StepData.XIx (Fin κ) t (j + 1 + 1) ⊕ Fin (c + 1)) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k) :=
    ⟨om (S.μ (j + 1 + 1)) 1 hk Φ₂.1, GlobalTheory.SplitWeil.Model.om_mem_SB _ _ _ Φ₂.2⟩
  have hom : s₂.om (1, h) (T₂ Φ₂) = T₂ Φ₂' :=
    hOm k p ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil _ μT hμS hμT _ _ F.G₁ F.G₂ T₂ hT₂ 1 1 h hk
      (isLoc_one p F.G₁) hhk Φ₂ Φ₂' (by simp [Φ₂'])

  obtain ⟨C₀, hC₀⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D k p _ (σ + 1) F.s F.s_ne).1 B F.F₀).1
  obtain ⟨C₂, hC₂⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D k p _ σ (F.s * p.xi) (mul_ne_zero F.s_ne hxi)).1 B' F.F₂).1

  obtain ⟨U₁, hU₁, hflat₁⟩ := hBF k p ν hν.1 ψ S.ψ hψ (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C₀ F.G₀ F.F₁ F.G₁
    hC₀ F.bes F.jac T₁ hT₁
  have hjac' : p.IsJacFrame J F.s (-p.xi ^ 2 * p.hz B') F.F₁ F.G₁ := hz_link p l ▸ F.jac
  obtain ⟨U₂, hU₂, hflat₂⟩ := hFB k p ν hν.1 ψ S.ψ hψ σ J B' s₂ F.s F.s_ne _ _ (c + 1) F.F₁ F.G₁ F.F₂ C₂ F.G₂
    hjac' hC₂ F.bes' T₂ hT₂
  have hsb := GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k S.ψ ν hcont hν.1
  let Ψ₁ : SB (Matrix (GlobalTheory.StepData.XIx (Fin κ) t (j + 1)) (GlobalTheory.StepData.XIx (Fin κ) t j ⊕ Unit) k) :=
    ⟨GlobalTheory.LocFlat.flCol S.ψ ν (σ + 1 + 1) Φ₁.1, ((hsb _ _ (c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 _ Φ₁.2⟩
  let Ψ₂ : SB (Matrix (GlobalTheory.StepData.XIx (Fin κ) t (j + 1 + 1) ⊕ Unit) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1)) k) :=
    ⟨GlobalTheory.LocFlat.flRow S.ψ ν (σ + 1) Φ₂'.1, ((hsb _ _ (c + 1) (σ + 1) (by omega)).2 (by omega)).1 _ Φ₂'.2⟩
  obtain ⟨Λ, -, hΛ⟩ := hCo k p ν hν.1 ψ hstd S.ψ hψ (σ + 1) σ B B' l J.W₀ vL F.s F.s_ne _ _ _ F.F₀ C₀ F.F₁ F.F₂ C₂
    hC₀ hC₂ U₁ U₂ hU₁ hU₂
  obtain ⟨Ξ, hΞ, hΞΛ⟩ := hΛ Ψ₁ Ψ₂
  rw [hom, hflat₁ Φ₁ Ψ₁ rfl, hflat₂ Φ₂' Ψ₂ rfl, hΞΛ] at hne
  have hΞ0 : Ξ.1 ≠ 0 := by
    intro h0
    apply hne
    have : Ξ = 0 := Subtype.ext h0
    rw [this, map_zero]

  have hds := ((hSym k ν hν s κ S t).2.2.2 j c H σ hc).1 hk (by
    rw [hΞ] at hΞ0
    simpa [Ψ₁, Ψ₂, Φ₂', hΦ₁, hΦ₂] using hΞ0)
  obtain ⟨q, hq, u, hu, hkqu⟩ := hds
  obtain ⟨r, hr⟩ := (hL1 q).exists
  obtain ⟨u', hu'⟩ := (hL1 u).exists
  have hrB := (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).2.2 _ (c + 1) σ B' (F.s * p.xi) F.F₂ F.G₂ F.bes' r q hq hr
  refine ⟨r, hrB, hr.1, u', u, hu', hu, ?_⟩
  have h1 := hL3 r q u' u hr hu'
  rw [← hkqu] at h1
  exact (hL1 hk).unique hhk h1

end GlobalTheory.LocMod.GSuppTwo
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
namespace GlobalTheory.BiComb

variable {D : D7}

theorem heisO_resS_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (F : WO V S → ℂ)
    (w u : WO A S) (v : WO L S) :
    heisO ψ V S ((o.resS S).symm (w, 0)) F ((o.resS S).symm (u, v)) =
      heisO ψ A S w (fun u' => F ((o.resS S).symm (u', v))) u := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem heisO_resT_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (F : WO S V → ℂ)
    (w u : WO S A) (v : WO S L) :
    heisO ψ S V ((o.resT S).symm (w, 0)) F ((o.resT S).symm (u, v)) =
      heisO ψ S A w (fun u' => F ((o.resT S).symm (u', v))) u := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem comb_resS_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (c : WO A S →₀ ℂ)
    (F : WO V S → ℂ) (u : WO A S) (v : WO L S) :
    comb ψ V S (c.mapDomain fun w => (o.resS S).symm (w, 0)) F ((o.resS S).symm (u, v)) =
      comb ψ A S c (fun u' => F ((o.resS S).symm (u', v))) u := by
  classical
  have hinj : Function.Injective fun w : WO A S => (o.resS S).symm (w, 0) := fun a b h => by
    have := congrArg (o.resS S) h
    simp only [AddEquiv.apply_symm_apply, Prod.mk.injEq, and_true] at this
    exact this
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hinj, heisO_resS_slice]

theorem comb_resT_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (c : WO S A →₀ ℂ)
    (F : WO S V → ℂ) (u : WO S A) (v : WO S L) :
    comb ψ S V (c.mapDomain fun w => (o.resT S).symm (w, 0)) F ((o.resT S).symm (u, v)) =
      comb ψ S A c (fun u' => F ((o.resT S).symm (u', v))) u := by
  classical
  have hinj : Function.Injective fun w : WO S A => (o.resT S).symm (w, 0) := fun a b h => by
    have := congrArg (o.resT S) h
    simp only [AddEquiv.apply_symm_apply, Prod.mk.injEq, and_true] at this
    exact this
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hinj, heisO_resT_slice]

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isOne (Y Y' : Type) [Fintype Y] [Fintype Y'] : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} := GlobalTheory.SplitFlip.isCompact_intMatrix
  exact ⟨⟨_, GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB hc ⟨hc.isClosed, GlobalTheory.SplitFlip.isOpen_intMatrix⟩⟩, rfl⟩

end Loc

theorem source_slice_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := GlobalTheory.T.exists_local_model_slice_source_line

theorem target_slice_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := GlobalTheory.T.exists_local_model_slice_target_line

theorem comb_bimodel_and_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''], (∀ (A S A' : HSp D) (FA : Frame k A.rank n') (FS : Frame k S.rank n) (FA' : Frame k A'.rank n'') Λ c c' (Ξ₁ O₁ : SB (Matrix n n' k)) (Ξ₂ O₂ : SB (Matrix n'' n k)) (Ξ O : SB (Matrix n n' k × Matrix n'' n k)), p.IsBiModel ψ FA FS FA' Λ → p.IsCombAt ψ FA FS c Ξ₁.1 → p.IsCombAt ψ FS FA' c' Ξ₂.1 → IsOne O₁ → IsOne O₂ → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → (∀ q, O.1 q = O₁.1 q.1 * O₂.1 q.2) → Λ Ξ = biComb ψ A S A' c c' (Λ O)) ∧ ∀ (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), IsStdChar D ψ (-1) → p.IsCoreFrame B s FA F₀ → (∀ T₀ c (Ξ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ F₀ FS T₀ → p.IsCombAt ψ FA FS c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toCols₁ * a fun r => x r (Sum.inr ())) → (∀ x, O.1 x = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ * a fun r => x r (Sum.inr ())) → T₀ Ψ = comb ψ B.V₀ S (c.mapDomain fun w => (B.o.resS S).symm (w, 0)) (T₀ O)) ∧ ∀ T₀ c (Ξ : Matrix n' n k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ FS F₀ T₀ → p.IsCombAt ψ FS FA c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toRows₁ * a (x (Sum.inr ()))) → (∀ x, O.1 x = Set.indicator {x : Matrix n' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toRows₁ * a (x (Sum.inr ()))) → T₀ Ψ = comb ψ S B.V₀ (c.mapDomain fun w => (B.o.resT S).symm (w, 0)) (T₀ O) := by
  intro D k _ _ _ _ p ψ n n' n'' _ _ _ _ _ _
  refine ⟨?_, ?_⟩
  · intro A S A' FA FS FA' Λ c c' Ξ₁ O₁ Ξ₂ O₂ Ξ O hΛ hc hc' hO₁ hO₂ hΞ hO
    funext u v
    obtain ⟨T₁, hT₁, e₁⟩ := hΛ.1 Ξ₂ v
    let P : SB (Matrix n n' k × Matrix n'' n k) := ⟨_, GlobalTheory.LocFlat.CFac.prodFn_mem_SB O₁.2 Ξ₂.2⟩
    rw [e₁ Ξ₁ Ξ hΞ u, hc.2 T₁ hT₁ O₁ Ξ₁ hO₁ rfl]
    have hf : T₁ O₁ = fun u' => comb ψ S A' c' (Λ O u') v := by
      funext u'
      rw [← e₁ O₁ P (fun q => rfl) u']
      obtain ⟨T₂, hT₂, e₂⟩ := hΛ.2 O₁ u'
      rw [e₂ Ξ₂ P (fun q => rfl) v, hc'.2 T₂ hT₂ O₂ Ξ₂ hO₂ rfl]
      have hg : T₂ O₂ = Λ O u' := funext fun v' => (e₂ O₂ O hO v').symm
      rw [hg]
    rw [hf]
    rfl
  · intro ρ B S s FA F₀ FS _ hF
    refine ⟨?_, ?_⟩
    · intro T₀ c Ξ a Ψ O hT hc hΞ ha hΨ hO
      funext x
      obtain ⟨T₁, hT₁, e⟩ := source_slice_model D k p ψ n n' ρ B S s FA F₀ FS hF T₀ hT a ha (B.o.resS S x).2
      obtain ⟨O₁, hO₁⟩ := exists_isOne (k := k) n n'
      have h1 := hc.2 T₁ hT₁ O₁ ⟨Ξ, hΞ⟩ hO₁ rfl
      have hx : x = (B.o.resS S).symm ((B.o.resS S x).1, (B.o.resS S x).2) := by simp
      rw [hx, e ⟨Ξ, hΞ⟩ Ψ hΨ, h1, comb_resS_slice]
      have hg : T₁ O₁ = fun u' => T₀ O ((B.o.resS S).symm (u', (B.o.resS S x).2)) :=
        funext fun u' => (e O₁ O (fun y => by rw [hO₁]; exact hO y) u').symm
      rw [hg]
    · intro T₀ c Ξ a Ψ O hT hc hΞ ha hΨ hO
      funext x
      obtain ⟨T₁, hT₁, e⟩ := target_slice_model D k p ψ n n' ρ B S s FA F₀ FS hF T₀ hT a ha (B.o.resT S x).2
      obtain ⟨O₁, hO₁⟩ := exists_isOne (k := k) n' n
      have h1 := hc.2 T₁ hT₁ O₁ ⟨Ξ, hΞ⟩ hO₁ rfl
      have hx : x = (B.o.resT S).symm ((B.o.resT S x).1, (B.o.resT S x).2) := by simp
      rw [hx, e ⟨Ξ, hΞ⟩ Ψ hΨ, h1, comb_resT_slice]
      have hg : T₁ O₁ = fun u' => T₀ O ((B.o.resT S).symm (u', (B.o.resT S x).2)) :=
        funext fun u' => (e O₁ O (fun y => by rw [hO₁]; exact hO y) u').symm
      rw [hg]

end GlobalTheory.BiComb
end
end

section

noncomputable section
open scoped TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_mul_gaMat (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one_gaMat (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem Place.pi_idem (p : Place D k) : p.π p.e = 1 := by
  have h1 := p.ι_π 1
  rw [mul_one, map_one] at h1
  rw [← h1, p.π_ι]

theorem Place.pi_eq_of_toEAf (p : Place D k) {a b : AE D} (h : toEAf D a = toEAf D b) : p.π a = p.π b := by
  have hf : finPart D a = finPart D b :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).injective h
  have key : p.e * a = p.e * b := GlobalTheory.SplitScalar.adele_ext
    (by rw [map_mul, map_mul, GlobalTheory.SplitScalar.infPart_splitIdem p.split, zero_mul, zero_mul])
    (by rw [map_mul, map_mul, hf])
  calc p.π a = p.π (p.e * a) := by rw [map_mul, p.pi_idem, one_mul]
    _ = p.π (p.e * b) := by rw [key]
    _ = p.π b := by rw [map_mul, p.pi_idem, one_mul]

theorem Place.map_pi_eq_of_toEAf (p : Place D k) {m n : ℕ} {a b : Matrix (Fin m) (Fin n) (AE D)}
    (h : a.map (toEAf D) = b.map (toEAf D)) : a.map p.π = b.map p.π := by
  ext i j
  exact p.pi_eq_of_toEAf (congrFun (congrFun h i) j)

theorem exists_toEAf_lift (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

def liftM {m n : ℕ} (x : Matrix (Fin m) (Fin n) (EAf D)) : Matrix (Fin m) (Fin n) (AE D) :=
  x.map fun z => (exists_toEAf_lift z).choose

theorem liftM_map {m n : ℕ} (x : Matrix (Fin m) (Fin n) (EAf D)) : (liftM x).map (toEAf D) = x := by
  ext i j
  exact (exists_toEAf_lift (x i j)).choose_spec

def stdFrame (k : Type) [Field k] (N : ℕ) : Frame k N (Fin N) := ⟨1, 1, by simp, by simp⟩

theorem exists_GL_mul_of_mul_eq_one {n : ℕ} (M : GL (Fin n) k) (N Ni : Matrix (Fin n) (Fin n) k) (h : N * Ni = 1) :
    ∃ gk : GL (Fin n) k, gk.val = M.val * Ni := by
  have h' : Ni * N = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 h
  exact ⟨M * ⟨Ni, N, h', h⟩, rfl⟩

theorem Place.exists_movedTo (p : Place D k) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (M : GL (Fin V.rank) k) (g₀ : GA D V) : ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Matrix (Fin V.rank) (Fin V.rank) (AE D), b₀.map (toEAf D) = β.val :=
    ⟨liftM β.val, liftM_map _⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Matrix (Fin V.rank) (Fin V.rank) (AE D), c₀.map (toEAf D) = (β⁻¹).val :=
    ⟨liftM (β⁻¹).val, liftM_map _⟩
  have hbc : b₀.map p.π * c₀.map p.π = 1 := by
    rw [← Matrix.map_mul]
    have h1 : (b₀ * c₀).map (toEAf D) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (toEAf D) := by
      rw [Matrix.map_mul, hb₀, hc₀, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, mul_inv_cancel,
        Units.val_one]
    rw [p.map_pi_eq_of_toEAf h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN : ((mt V g₀).map p.π * b₀.map p.π) * (c₀.map p.π * (mt V g₀⁻¹).map p.π) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (b₀.map p.π), hbc, Matrix.one_mul, ← Matrix.map_mul, ← mt_mul_gaMat,
      mul_inv_cancel, mt_one_gaMat, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN' : (c₀.map p.π * (mt V g₀⁻¹).map p.π) * ((mt V g₀).map p.π * b₀.map p.π) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 hN
  obtain ⟨gk, hgk⟩ := exists_GL_mul_of_mul_eq_one M _ _ hN
  obtain ⟨g, hg, -⟩ := ((GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).1 V (Fin V.rank) (stdFrame k V.rank)).1 gk
  refine ⟨g, hg.1, fun b hb => ?_⟩
  have h2 : (mt V g).map p.π = gk.val := by
    rw [hg.2]
    change (1 : Matrix (Fin V.rank) (Fin V.rank) k) * gk.val * 1 = gk.val
    rw [Matrix.one_mul, Matrix.mul_one]
  have hbb : b.map p.π = b₀.map p.π := p.map_pi_eq_of_toEAf (by rw [hb, hb₀])
  rw [mt_mul_gaMat, Matrix.map_mul, Matrix.map_mul, h2, hbb, hgk, Matrix.mul_assoc (M.val * _), Matrix.mul_assoc M.val,
    hN', Matrix.mul_one]

theorem normalFrames_and_basePoint_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), p.xi ≠ 0 → (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n), s ≠ 0 → (∃ F : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F) ∧ ∃ F : Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n), s ≠ 0 → hh ≠ 0 → ∃ F : Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (M : GL (Fin V.rank) k) (g₀ : GA D V), ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val :=
  fun _ _ _ _ _ _ p _ =>
    ⟨fun _ _ _ _ B _ FA hs => ⟨p.exists_isCoreFrame hs B FA, p.exists_isBesFrame hs B FA⟩,
      fun _ _ _ _ J _ _ F₀ hs hh0 => p.exists_isJacFrame hs J hh0 F₀,
      fun V β M g₀ => p.exists_movedTo V β M g₀⟩

end GlobalTheory.LocMod
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdHomAt
open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latO_mono (S T : HSp D) (LS LT) {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) :
    latO S T LS LT P ≤ latO S T LS LT Q :=
  AddSubgroup.closure_mono fun _ ⟨α, h1, h2, h3⟩ => ⟨α, h1, fun v hv => h2 v fun hp => hv (h v hp), h3⟩

theorem mem_latO_at (q : SplitPt D k) {S T : HSp D} {LS LT} {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True)
    (hh : IsHalf q.e u) : u ∈ latO S T LS LT (· = q.v) := by
  obtain ⟨ε, ⟨β, rfl, h1, h0⟩, hsum⟩ := q.above
  have hβ : β ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have main : (latO S T LS LT fun _ => True) ≤ (latO S T LS LT (· = q.v)).comap
      (DistribSMul.toAddMonoidHom (WO S T) (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨β * α, fun v => by rw [map_mul]; exact mul_mem (hβ v) (hα v), fun v hv => ?_,
      a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul, h0 v hv, zero_mul]
    · ext i j
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Matrix.of_apply]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  have h := main hu
  rw [AddSubgroup.mem_comap] at h
  convert h using 1
  ext i j
  change _ = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) * u i j
  rw [← hsum, ← hh i j, ← mul_assoc, add_mul, q.split.1, mul_comm (cA D q.e), q.split.2.1, add_zero]

theorem int_iff_up_mem_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) → (∀ z, z ∈ LT ↔ z ∈ intVec D T.rank) → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) ↔ (GlobalTheory.LocMod.ofSplit q).up FS FT x ∈ stdHom S T := by
  intro D k _ _ _ _ q hq Y Y' _ _ _ _ S T FS FT LS LT hS hT eS eT hFS hFT x
  have eS' : (LS : Set (Fin S.rank → D.host.E)) = intVec D S.rank := Set.ext eS
  have eT' : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank := Set.ext eT
  rw [stdHom, ← eS', ← eT']
  refine ⟨fun hx => latO_mono S T _ _ (fun _ _ => trivial)
    (GlobalTheory.UpMem.up_mem_latO D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT x hx), fun hx => ?_⟩
  have hh := Witness.up_half (ofSplit q) FS FT x
  obtain ⟨x', hx', e⟩ := GlobalTheory.HalfIntUp.exists_int_up D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT _ (mem_latO_at q hx hh) hh
  have := congrArg ((ofSplit q).down FS FT) e
  rw [Witness.down_up, Witness.down_up] at this
  rwa [this]

end GlobalTheory.StdHomAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MidDat

theorem exists_o {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ o : WO S T →₀ ℂ, (∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x) ∧
      ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
        Tm Φ₁ = comb ψ S T o (Tm Φ₀) := by
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := GlobalTheory.SeeSaw.LocPlInhab.exists_latInd q FS FT hS hT
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨o, o1, fun Tm hTm a b hb ha => ?_⟩
  obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
  obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
  exact o2 Tm hTm

theorem idem_eq {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n : ℕ} (a : Fin n → AE D)
    (pl : Fin n ≃ P) (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i).1) : e = ∑ i, a i := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P, ← Equiv.sum_comp pl]
  exact Finset.sum_congr rfl fun i _ => GlobalTheory.LocMod.PinInhab.idem_unique (hes _ (pl i).2) (ha i)

theorem isThetaAt_smul {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ} {f₀ Φ f : Mx D m n → ℂ}
    {κ : ℂ} (hκ : κ ≠ 0) (h : IsThetaAt ψ B hs e Λ c f₀ (κ • Φ) f) : IsThetaAt ψ B hs e Λ c f₀ Φ (κ⁻¹ • f) := by
  obtain ⟨hex, hall⟩ := h
  refine ⟨hex, fun Tm hTm => ?_⟩
  rw [hall Tm hTm, map_smul, smul_smul, inv_mul_cancel₀ hκ, one_smul]

end GlobalTheory.MidDat

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → (ofSplit q).up FS FT x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  first | exact @GlobalTheory.UpMem.up_mem_latO | exact GlobalTheory.UpMem.up_mem_latO | (intros; apply GlobalTheory.UpMem.up_mem_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel


theorem _root_.GlobalTheory.T.exists_splitPoint_weilChar_conductor_one_of_units : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → q.UnitAA → ∃ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  first | exact @GlobalTheory.SplitWeilChar.weil_char_conductor_one | exact GlobalTheory.SplitWeilChar.weil_char_conductor_one | (intros; apply GlobalTheory.SplitWeilChar.weil_char_conductor_one <;> assumption)
end
