module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle226
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLocalRows

open Formalism.IndefR.principalLevelFrame

theorem fixed_fd_of_isotIn {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A)
    (hadm : ∀ N : ℕ, 0 < N →
      FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, NG.Cong D.host.E n N κ → ρ κ x = x}))
    (π : NG.FinTyp D.host.E n) (hne : isotIn (D := D) ρ C π ≠ ⊥) (N : ℕ) (hN : 0 < N) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E n N κ → NG.rt D.host.E n κ f = f}) := by
  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : π.S →ₗ[ℂ] A,
      (IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold isotIn
    exact iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ (GAf D.host.E n → ℂ) := (LinearMap.ker Φ).map π.S.subtype
    have hS'le : S' ≤ π.S := by
      rintro f ⟨k, _, rfl⟩
      exact k.2
    have hS'st : ∀ h, ∀ f ∈ S', NG.rt D.host.E n h f ∈ S' := by
      rintro h f ⟨k, hk, rfl⟩
      refine ⟨⟨NG.rt D.host.E n h k, π.stable h k k.2⟩, ?_, rfl⟩
      show Φ _ = 0
      rw [hΦe h k, LinearMap.mem_ker.1 hk, map_zero]
    rcases π.irr S' hS'le hS'st with h0 | hall
    · rw [eq_bot_iff]
      intro k hk
      have : (k : GAf D.host.E n → ℂ) ∈ S' := ⟨k, hk, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E n → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      rw [show y = k from Subtype.ext hky.symm]
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 hk)
  set F := Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E n N κ → NG.rt D.host.E n κ f = f} with hF
  set T := Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, NG.Cong D.host.E n N κ → ρ κ x = x} with hT
  have := hadm N hN
  have hFS : F ≤ π.S := Submodule.span_le.2 fun f hf => hf.1
  have hFT : ∀ f (hf : f ∈ F), Φ ⟨f, hFS hf⟩ ∈ T := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨hΦC ⟨_, rfl⟩, fun κ hκ => ?_⟩
      rw [← hΦe κ]
      congr 1
      exact Subtype.ext (hx.2 κ hκ)
    | zero =>
      have : (⟨0, hFS F.zero_mem⟩ : π.S) = 0 := rfl
      rw [this, map_zero]
      exact T.zero_mem
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hFS (F.add_mem hx hy)⟩ : π.S) = ⟨x, hFS hx⟩ + ⟨y, hFS hy⟩ := rfl
      rw [this, map_add (f := _)]
      exact T.add_mem ihx ihy
    | smul a x hx ih =>
      have : (⟨a • x, hFS (F.smul_mem a hx)⟩ : π.S) = a • ⟨x, hFS hx⟩ := rfl
      rw [this, map_smul]
      exact T.smul_mem a ih
  let g : F →ₗ[ℂ] T := LinearMap.codRestrict T (Φ ∘ₗ Submodule.inclusion hFS) (fun f => hFT f f.2)
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : Φ (Submodule.inclusion hFS a) = Φ (Submodule.inclusion hFS b) := congrArg Subtype.val hab
    exact Submodule.inclusion_injective hFS (hinj h1)
  exact Module.Finite.of_injective g hg

section Conj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem fixed_fd_of_conjT (π : NG.FinTyp L n) (N : ℕ)
    (h : FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ (FinTyp.conjT π).S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f})) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f}) := by
  set S1 := Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f} with hS1
  set S2 := Submodule.span ℂ {f | f ∈ (FinTyp.conjT π).S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f} with hS2
  have hmap : ∀ f ∈ S1, (fun g => star (f g)) ∈ S2 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨?_, fun κ hκ => ?_⟩
      · rw [conjT_S, mem_conjSub]
        simpa using hx.1
      · rw [← conj_rt, hx.2 κ hκ]
    | zero =>
      have : (fun g => star ((0 : GAf L n → ℂ) g)) = 0 := by
        funext g
        simp
      rw [this]
      exact S2.zero_mem
    | add x y _ _ hx hy =>
      have : (fun g => star ((x + y) g)) = (fun g => star (x g)) + (fun g => star (y g)) := by
        funext g
        simp
      rw [this]
      exact S2.add_mem hx hy
    | smul a x _ hx =>
      have : (fun g => star ((a • x) g)) = star a • (fun g => star (x g)) := by
        funext g
        simp [mul_comm]
      rw [this]
      exact S2.smul_mem _ hx
  let c : S1 →ₗ[ℝ] S2 :=
    { toFun := fun f => ⟨fun g => star ((f : GAf L n → ℂ) g), hmap f f.2⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by simp)
      map_smul' := fun r a => Subtype.ext (funext fun g => by simp) }
  have hc : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    funext g
    have := congrFun (congrArg Subtype.val hab) g
    exact star_injective this
  haveI : FiniteDimensional ℝ S2 := Module.Finite.trans ℂ S2
  haveI : FiniteDimensional ℝ S1 := Module.Finite.of_injective c hc
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ S1

theorem form_of_conjT (π : NG.FinTyp L n) (B' : (FinTyp.conjT π).S → (FinTyp.conjT π).S → ℂ)
    (hlin : ∀ x y z (c : ℂ), B' x (y + c • z) = B' x y + c * B' x z)
    (hherm : ∀ x y, B' x y = starRingEnd ℂ (B' y x))
    (hpos : ∀ x, x ≠ 0 → 0 < (B' x x).re)
    (hinv : ∀ h (x y x' y' : (FinTyp.conjT π).S), (x' : GAf L n → ℂ) = NG.rt L n h x →
      (y' : GAf L n → ℂ) = NG.rt L n h y → B' x' y' = B' x y) :
    ∃ B : π.S → π.S → ℂ, (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) ∧
      (∀ x y, B x y = starRingEnd ℂ (B y x)) ∧ (∀ x, x ≠ 0 → 0 < (B x x).re) ∧
      ∀ h (x y x' y' : π.S), (x' : GAf L n → ℂ) = NG.rt L n h x →
        (y' : GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y := by
  let c : π.S → (FinTyp.conjT π).S := fun f =>
    ⟨fun g => star ((f : GAf L n → ℂ) g), by rw [conjT_S, mem_conjSub]; simpa using f.2⟩
  have hc : ∀ f : π.S, ((c f : (FinTyp.conjT π).S) : GAf L n → ℂ) = fun g => star ((f : GAf L n → ℂ) g) := fun _ => rfl
  refine ⟨fun x y => starRingEnd ℂ (B' (c x) (c y)), ?_, ?_, ?_, ?_⟩
  · intro x y z a
    have e : c (y + a • z) = c y + (starRingEnd ℂ a) • c z := by
      apply Subtype.ext
      funext g
      simp [hc, mul_comm]
    simp only
    rw [e, hlin, map_add (f := _), map_mul, Complex.conj_conj]
  · intro x y
    simp only
    rw [hherm (c x) (c y)]
  · intro x hx
    simp only
    rw [Complex.conj_re]
    apply hpos
    intro h0
    apply hx
    apply Subtype.ext
    funext g
    have := congrFun (congrArg Subtype.val h0) g
    rw [hc] at this
    simpa using this
  · intro h x y x' y' hx hy
    simp only
    congr 1
    apply hinv h
    · rw [hc, hc, hx]
      rfl
    · rw [hc, hc, hy]
      rfl

end Conj

end GlobalTheory.RowLocalRows

namespace GlobalTheory.RowLocalRows

open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult


end GlobalTheory.RowLocalRows

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelAction

theorem conj_mulVec_mem {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (y : GL (Fin n) S)
    (z : Fin n → R) (hz : ∀ j, ((β⁻¹).1 *ᵥ z) j ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 *ᵥ z)) i ∈ S := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec]
  generalize (β⁻¹).1 *ᵥ z = w at hz
  exact Subring.sum_mem S (t := Finset.univ) (f := fun j => (y.1 i j : R) * w j) fun j _ => mul_mem (y.1 i j).2 (hz j)

variable {D : D7}

theorem finCong_of_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {k : GA D V}
    (hk : Lev.finE V k ∈ St β) : GlobalTheory.Member.FinCong V 1 k := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨y, hy⟩ := hk
  have hy' : β * intGL D.host.F D.host.E V.rank y * β⁻¹ = Formalism.UG.bc (Lev.swapAE D) (finHom V k) := hy
  intro z hz
  refine ⟨(finHom V k).1 *ᵥ z - z, sub_mem ?_ hz, (one_nsmul _).symm⟩
  rw [hl] at hz ⊢
  have h2 := (hfr _).1 (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)
  have h3 : (Formalism.UG.bc (Lev.swapAE D) (finHom V k)).1 *ᵥ
      (fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← hy']
    exact (hfr _).2 (conj_mulVec_mem _ β y _ h2)
  have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h3
  convert h4 using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  exact RingHom.map_mulVec (Lev.swapAE D) (finHom V k).1 z i

theorem exists_endo {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {k : GA D V}
    (hk : GlobalTheory.Member.FinCong V 1 k) : ∃ f : La →ₗ[𝓞 D.host.E] La, ∀ a, ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - (finHom V k).1.mulVec (finVec V (ι a)) = M • w := by
  have hh := GlobalTheory.Member.LatMove.hat_eq_of_finCong V hk
  have hL := GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V hh
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V k
  rw [hL] at h3
  obtain ⟨f, hf, -⟩ := GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1) (finHom V k)
    (latG V 1) h1 h2 h3
  let e : La ≃ₗ[𝓞 D.host.E] latG V 1 := (LinearEquiv.ofInjective ι hι.1).trans (LinearEquiv.ofEq _ _ hι.2)
  have he : ∀ a, (e a : Fin V.rank → D.host.E) = ι a := fun a => rfl
  refine ⟨e.symm.toLinearMap ∘ₗ f M ∘ₗ e.toLinearMap, fun a => ?_⟩
  obtain ⟨w, hw, ew⟩ := hf M hM (e a)
  refine ⟨(finHom V k).1 *ᵥ w, ?_, ?_⟩
  · rw [← hh]
    exact (GlobalTheory.Member.LatMove.mem_hat_iff V k _).2 ⟨w, h5 ▸ hw, rfl⟩
  · have e1 : ι ((e.symm.toLinearMap ∘ₗ f M ∘ₗ e.toLinearMap) a) = (f M (e a) : Fin V.rank → D.host.E) := by
      rw [← he]
      exact congrArg Subtype.val (e.apply_symm_apply _)
    rw [e1]
    have e2 : finVec V (f M (e a) : Fin V.rank → D.host.E) = (finHom V k).1 *ᵥ (finVec V (ι a) + M • w) := ew
    rw [e2, Matrix.mulVec_add, add_sub_cancel_left]
    exact map_nsmul (finHom V k).1.mulVecLin M w

theorem not_isConjPl {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    {PP PP' : Pl D.host.E} (h : l.Mb ≤ PP.asIdeal) (h' : l.Mb ≤ PP'.asIdeal) : ¬ Lev.IsConjPl PP PP' := by
  intro hc
  apply PP'.isPrime.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le h' (Ideal.map_le_iff_le_comap.2 fun c hc' => ?_)
  obtain ⟨c', h1, h2⟩ := hc c (h hc')
  have e : H.bar c = c' := RingOfIntegers.ext ((H.bar_eq c).trans h2.symm)
  change H.bar c ∈ PP'.asIdeal
  rwa [e]

theorem latEmb_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, g, e, F, ik, φ, th, h, -⟩ := hT.adPin _ hj _ T.toCore.good_σ₀
  have hV := hT.spaceW _ hj _ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i →
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatEmb (Wc D i) (iotaW T i) := by
    rintro V hr rfl h
    exact h
  exact key _ hr hV h

theorem exists_levIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ i : Fin D.R.m, ∃ lev, LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ hpb i
  have hT := tie.laws
  have hβ := hR.lev.βW i
  have hle : ∀ PP ∈ R.Pg, T.Q.l.Mb ≤ PP.asIdeal := by
    intro PP hP
    obtain ⟨k, hk⟩ := (hR.lev.Pg PP).1 hP
    rw [hT.half.2]
    refine (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_
    rw [hpb, ← show PP.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact Ideal.map_comap_le
  have hlift : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := hβ
    refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)
    rcases h' with h' | h'
    · exact not_isConjPl T.Q.l (hle PP h) (hle PP' h')
    · exact absurd h' (Finset.notMem_empty _)
  have hM : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  choose k hk using fun g => hlift (R.eG g)
  choose f hf using fun g => exists_endo (iotaW T i) (latEmb_iotaW T hT i) hM
    (finCong_of_mem_St hβ (parLev_St (hk g).2.1))
  exact ⟨f, fun g => ⟨k g, hk g, fun a _ => hf g a⟩⟩

end GlobalTheory.LevelAction
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PtId.OneScalar

theorem map_pG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c c' : Coeff l) (φ : c.F →+* ℂ) (φ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    MvPolynomial.map φ (pG (Dw := Dw) c a n) = MvPolynomial.map φ' (pG (Dw := Dw) c' a n) := by
  have h : ∀ s i hi col, MvPolynomial.map φ (minorPolynomial (Dw := Dw) (n := n) c s i hi col) =
      MvPolynomial.map φ' (minorPolynomial c' s i hi col) := by
    intro s i hi col
    unfold minorPolynomial
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p q : 2
    simp
  unfold pG
  simp only [map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
  congr 1
  split_ifs
  · exact h _ _ _ _
  · exact h _ _ _ _
  · rw [map_zero, map_zero]

theorem ten_extremal_mem (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    (Formalism.L2.DIV.ten fun τ => extremal K n (lam τ)) ∈ Formalism.L2.DIV.VV K lam :=
  GlobalTheory.Proof.TensorMapDescent.ten_mem lam _ fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (Formalism.L2.DIV.natW_antitone (lam τ))

theorem lt_injective {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (hH : ∀ ρ, tauE D ρ (H.rt : D.host.E) = H.rt0)
    {m n : ℕ} (lt : LtN Dw n → FVar D m n)
    (hlt : ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
      (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1))) : Function.Injective lt := by
  have hp : ∀ ℓ : LtN Dw n, ∀ ρ, ℓ.1 = tauE D ρ → (ℓ.2.1 : ℕ) < Dw.p := by
    rintro ⟨σ, s, b⟩ ρ h
    have hs := s.2
    have : Dw.mult σ = Dw.p := by
      rw [show σ = tauE D ρ from h]
      exact if_pos (hH ρ)
    exact this ▸ hs
  intro x y hxy
  obtain ⟨a1, a2⟩ := hlt x
  obtain ⟨b1, b2⟩ := hlt y
  have hpx := hp x (lt x).1
  have hpy := hp y (lt y).1
  rw [hxy] at a1 a2 hpx
  have key : x.1 = y.1 ∧ (x.2.1 : ℕ) = y.2.1 := by
    rcases a2 with ⟨a2, a3⟩ | ⟨a2, a3⟩ <;> rcases b2 with ⟨b2, b3⟩ | ⟨b2, b3⟩
    · exact ⟨a2.trans b2.symm, by omega⟩
    · have := hpx a2; omega
    · have := hpy b2; omega
    · exact ⟨a2.trans b2.symm, by omega⟩
  obtain ⟨σ, s, b⟩ := x
  obtain ⟨σ', s', b'⟩ := y
  obtain ⟨k1, k2⟩ := key
  dsimp only at k1 k2 a1 b1
  subst k1
  obtain rfl : s = s' := Fin.ext k2
  obtain rfl : b = b' := a1.symm.trans b1
  rfl

section Hw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

theorem coefficientMap_extremalTensor_baseChange {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (hO : hwOK O.c' (lamV D i) O.hw)
    {c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W} (hc : CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0') :
    O.c0' O.hw = c0L ⟨_, ten_extremal_mem D.what₂.LL (lamV D i)⟩ := by
  obtain ⟨v', h1, h2⟩ := hc ⟨_, ten_extremal_mem D.what₂.LL (lamV D i)⟩
  rw [← h2]
  congr 1
  apply Subtype.ext
  rw [h1, show (O.hw : Formalism.L2.DIV.Pol O.c'.F D.what₂.Tau (Vc D i).rank) = _ from hO]
  dsimp only
  rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
  simp only [Formalism.L2.DIV.map_extremal]

end Hw

end GlobalTheory.PtId.OneScalar
end
