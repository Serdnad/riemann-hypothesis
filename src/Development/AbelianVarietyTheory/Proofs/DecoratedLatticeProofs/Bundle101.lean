module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle099
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle100
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle064
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.SplitValuePow

theorem val_pow {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (N : ℕ) (w : HeightOneSpectrum (𝓞 L)) :
    (χ ^ N).val w = χ.val w ^ N := by
  unfold Formalism.L2.Host.HChar.val Formalism.L2.Host.HChar.locK Formalism.L2.Host.HChar.loc
  simp only [MonoidHom.comp_apply, SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem inf_pow {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (N : ℕ) (k : Lˣ) :
    (χ ^ N).inf k = χ.inf k ^ N := by
  unfold Formalism.L2.Host.HChar.inf
  simp only [MonoidHom.comp_apply, SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ) (p : ℕ), χ.HasInfQ (Formalism.L2.Host.embTau D) a → (∀ τ, a τ ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  intro D χ a p ha ha0 hp w hw hfin
  obtain ⟨N, hN, hunr⟩ := GlobalTheory.T.exists_pow_heckeChar_unramified_everywhere D.host.E χ
  obtain ⟨n, hn2, hinf⟩ := ha
  have hn0 : ∀ τ, n τ ≠ 0 := fun τ h => ha0 τ (by have := hn2 τ; rw [h] at this; push_cast at this; linarith)
  have ht : ∀ v, (χ ^ N).TameAt v := fun v x hx _ => hunr v x hx
  have hinf' : (χ ^ N).HasInf (Formalism.L2.Host.embPsi D.host) (fun g => (N : ℤ) * n (D.eTau.symm g)) := by
    intro k
    rw [inf_pow, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Fintype.prod_equiv D.eTau _ _ fun τ => ?_
    show _ = _ ^ ((N : ℤ) * n (D.eTau.symm (D.eTau τ)))
    rw [Equiv.symm_apply_apply, ← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  refine GlobalTheory.SplitValue.not_isOfFinOrder_val D (χ ^ N) _ p ht hinf'
    (fun g => mul_ne_zero (by exact_mod_cast hN.ne') (hn0 _)) hp w hw ?_
  rw [val_pow]
  exact hfin.pow

end GlobalTheory.SplitValuePow
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_mul_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) * (locChar χ w' (Units.map (toCompl h').toMonoidHom x) : ℂˣ) := by
  first | exact @GlobalTheory.LFun.charAt_eq_locChar_mul_locChar | exact GlobalTheory.LFun.charAt_eq_locChar_mul_locChar | (intros; apply GlobalTheory.LFun.charAt_eq_locChar_mul_locChar <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) := by
  first | exact @GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt | exact GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt | (intros; apply GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LFun.EigLoc

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
open Formalism.MainNotions.SchurIrreducible (IsSplit)

section General

variable {G H : Type} [Group G] [Group H]

theorem comp_symm_mem_hecke (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {φ : G → ℂ} (hφ : φ ∈ Hecke ℂ K) : φ ∘ e.symm ∈ Hecke ℂ K' := by
  classical
  have hφ' : IsBiInv K φ ∧ FinDosetSupp K φ := hφ
  obtain ⟨hb, S, hS⟩ := hφ'
  have hsymm : ∀ y : H, y ∈ K' → e.symm y ∈ K := fun y hy => by
    rw [hK, MulEquiv.apply_symm_apply]; exact hy
  show IsBiInv K' (φ ∘ e.symm) ∧ FinDosetSupp K' (φ ∘ e.symm)
  refine ⟨fun a b g => ?_, ⟨S.image e, fun g hg => ?_⟩⟩
  · have := hb ⟨_, hsymm a a.2⟩ ⟨_, hsymm b b.2⟩ (e.symm g)
    simpa only [Function.comp_apply, map_mul] using this
  · obtain ⟨s, hs, a, b, hab⟩ := hS (e.symm g) hg
    refine ⟨e s, ?_, ⟨e a, (hK _).1 a.2⟩, ⟨e b, (hK _).1 b.2⟩, ?_⟩
    · exact Finset.mem_image_of_mem _ hs
    · have := congrArg e hab
      simpa only [MulEquiv.apply_symm_apply, map_mul] using this

theorem heckeVec_eq_comp_symm {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {φ : G → ℂ} (hφ : φ ∈ Hecke ℂ K) {x : V} (hx : x ∈ fixed ρ K) :
    heckeVec ρ K φ x = heckeVec (ρ.comp e.symm.toMonoidHom) K' (φ ∘ e.symm) x := by
  classical
  have hfix : ∀ k, k ∈ K → ρ k x = x := fun k hk => by
    have hx' : ∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x := hx
    simpa using hx' ⟨k, hk⟩
  have hT : ∀ g k, k ∈ K → φ (g * k) • ρ (g * k) x = φ g • ρ g x := by
    intro g k hk
    have hb : IsBiInv K φ := hφ.1
    have h1 : φ (g * k) = φ g := by simpa using hb 1 ⟨k, hk⟩ g
    rw [h1, map_mul, mul_apply_eq_comp, hfix k hk]
  let Q : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, map_mul, map_inv])
  have hQ : ∀ g : G, Q (g : G ⧸ K) = ((e g : H) : H ⧸ K') := fun g => rfl
  unfold heckeVec
  rw [← finsum_comp_equiv Q]
  refine finsum_congr fun c => ?_
  have h1 : (((Q c).out : H) : H ⧸ K') = ((e c.out : H) : H ⧸ K') := by
    rw [QuotientGroup.out_eq', ← hQ, QuotientGroup.out_eq']
  have h2 : (e c.out)⁻¹ * (Q c).out ∈ K' := QuotientGroup.eq.1 h1.symm
  have h3 : c.out⁻¹ * e.symm (Q c).out ∈ K := by
    rw [hK]
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h2
  have h4 := hT c.out _ h3
  rw [mul_inv_cancel_left] at h4
  exact h4.symm

private theorem cell_unif_lemma {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
    {n q m : ℕ} {ϖ ϖ' : L} (hU : IsUnramInv ϖ c q) (hU' : IsUnramInv ϖ' c q) (hm : 2 * m ≤ n)
    (a : Fin m → ℤ) (y : GU c n)
    (H : ∃ u : GU c n, IsUnipU u ∧ ∃ k ∈ KU c n,
      (((y : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        tMat ϖ n m a * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((k : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) :
    ∃ u : GU c n, IsUnipU u ∧ ∃ k ∈ KU c n,
      (((y : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        tMat ϖ' n m a * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((k : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  obtain ⟨u, hu, k, hk, hy⟩ := H
  have hne : ∀ t : L, IsUnramInv t c q → t ≠ 0 := fun t ht h0 => by
    have h := ht.2.2.2.1
    simp [h0] at h
  have hg0 : ∀ t : L, t ≠ 0 → ∀ i, tMat t n m a i i ≠ 0 := by
    intro t ht i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> first | exact zpow_ne_zero _ ht | exact one_ne_zero
  have hvv : Valued.v ϖ = Valued.v ϖ' := hU.2.2.2.1.trans hU'.2.2.2.1.symm
  have hgv : ∀ i, Valued.v (tMat ϖ n m a i i) = Valued.v (tMat ϖ' n m a i i) := by
    intro i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> simp only [map_zpow₀, hvv]
  have htm : ∀ t : L, tMat t n m a = Matrix.diagonal (fun i => tMat t n m a i i) := by
    intro t
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp only [tMat, Matrix.diagonal_apply_ne _ hij]
  set e : Fin n → L := fun i => tMat ϖ n m a i i / tMat ϖ' n m a i i with he_def
  have he0 : ∀ i, e i ≠ 0 := fun i => div_ne_zero (hg0 ϖ (hne ϖ hU) i) (hg0 ϖ' (hne ϖ' hU') i)
  obtain ⟨t, ht⟩ := Formalism.UG.P.fSatake_tMat_exists hU hm a
  obtain ⟨t', ht'⟩ := Formalism.UG.P.fSatake_tMat_exists hU' hm a
  have hb : ∀ i, c (tMat ϖ n m a i i) * tMat ϖ n m a i.rev i.rev = 1 := fun i => by
    have := Formalism.UG.P.fSatake_unit_diag (Formalism.UG.P.fSatake_borel_tMat ht) i
    rwa [ht] at this
  have hb' : ∀ i, c (tMat ϖ' n m a i i) * tMat ϖ' n m a i.rev i.rev = 1 := fun i => by
    have := Formalism.UG.P.fSatake_unit_diag (Formalism.UG.P.fSatake_borel_tMat ht') i
    rwa [ht'] at this
  have hce : ∀ i, c (e i) * e i.rev = 1 := fun i => by
    simp only [he_def, map_div₀]
    rw [div_mul_div_comm, hb i, hb' i, div_one]
  obtain ⟨D, hD, hD'⟩ := Formalism.UG.P.fSatake_diag_exists e hce
  have hev : ∀ i, Valued.v (e i) = 1 := fun i => by
    simp only [he_def]
    rw [map_div₀, hgv i, div_self]
    exact (Valuation.ne_zero_iff _).2 (hg0 ϖ' (hne ϖ' hU') i)
  have hDK : D ∈ KU c n := Formalism.UG.P.fSatake_diag_mem_K hD hD' hev
  have hDD : (((D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((D : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hsplit : tMat ϖ n m a = tMat ϖ' n m a * (((D : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hD, htm ϖ, htm ϖ', Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_div_cancel₀ _ (hg0 ϖ' (hne ϖ' hU') i)]
  obtain ⟨hub, hud⟩ := hu
  refine ⟨D * u * D⁻¹, ?_, D * k, Subgroup.mul_mem _ hDK hk, ?_⟩
  · have hmat : ∀ i j, (((D * u * D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
        e i * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹ := by
      intro i j
      simp only [Subgroup.coe_mul, Units.val_mul, hD, hD', Matrix.mul_diagonal, Matrix.diagonal_mul]
    unfold IsUnipU IsBorelU
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hmat, hub i j hij, mul_zero, zero_mul]
    · rw [hmat, hud i, mul_one, mul_inv_cancel₀ (he0 i)]
  · rw [hy, hsplit]
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), hDD, Matrix.one_mul]

private theorem satU_eq_of_isUnramInv {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
    {n q m : ℕ} {ϖ ϖ' : L} (hU : IsUnramInv ϖ c q) (hU' : IsUnramInv ϖ' c q) (hm : 2 * m ≤ n)
    (f : GU c n → ℂ) (α : Fin m → ℂ) : SatU ϖ q f α = SatU ϖ' q f α := by
  unfold SatU
  refine finsum_congr fun a => ?_
  congr 1
  refine finsum_congr fun x => ?_
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (cell_unif_lemma hU hU' hm a _ h1) h2
  · exact absurd (cell_unif_lemma hU' hU hm a _ h2) h1
  · rfl

end General

theorem heckeVec_eq_smul_of_isParamVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v) (B : Multiset ℂˣ), ∀ φ ∈ Hecke ℂ (stabLoc σ J L v), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLoc σ J v) V) (x : V), IsParamVec σ J L h ρ x B → heckeVec ρ (stabLoc σ J L v) φ x = z • x := by
  intro F E _ _ _ _ _ σ n J L v w h B φ hφ
  classical
  by_cases hsp : IsSplit (E := E) v ∧
      ∃ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e
  · obtain ⟨hv, e0, he0⟩ := hsp
    obtain ⟨z, hz⟩ := GlobalTheory.T.satake_determines_sphericalHeckeCharacter_GL E w n B (φ ∘ e0.symm) (comp_symm_mem_hecke e0 he0.2 hφ)
    refine ⟨z, fun V _ _ ρ x hx => ?_⟩
    rw [heckeVec_eq_comp_symm e0 he0.2 hφ hx.mem_fixed]
    exact hz V (ρ.comp e0.symm.toMonoidHom) x (hx.isSatVecGL hv he0)
  by_cases hin : ∃ (c : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E)
      (e : GLoc σ J v ≃* GU c n) (α : Fin (n / 2) → ℂˣ),
      IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧ B = GlobalTheory.LGrp.bcParam n α
  · obtain ⟨c0, ϖ0, e0, α0, hU0, hC0, hB0⟩ := hin
    have hmem := comp_symm_mem_hecke e0 hC0.2.2 hφ
    refine ⟨SatU ϖ0 (qV F v) (φ ∘ e0.symm) (fun i => (α0 i : ℂ)), fun V _ _ ρ x hx => ?_⟩
    have hfx := hx.mem_fixed
    rcases hx with ⟨hv, e, he, -⟩ | ⟨-, c, ϖ, e, α, hU, hC, hS, hB⟩
    · exact (hsp ⟨hv, e, he⟩).elim
    · obtain rfl : c = c0 := IsConjAt.unique hC.1 hC0.1
      have hS0 := IsSatVecU.of_chart hC hC0 hS
      rw [heckeVec_eq_comp_symm e0 hC0.2.2 hφ hfx, hS0.2.2 _ hmem]
      congr 1
      rw [satU_eq_of_isUnramInv hU hU0 (Nat.mul_div_le n 2)]
      exact GlobalTheory.T.unitarySatakeTransform_eq_of_baseChangeSatakeParameter_eq _ ϖ0 c (qV F v) n hU0 α α0 (hB.symm.trans hB0) _ hmem
  · refine ⟨0, fun V _ _ ρ x hx => ?_⟩
    rcases hx with ⟨hv, e, he, -⟩ | ⟨-, c, ϖ, e, α, hU, hC, -, hB⟩
    · exact (hsp ⟨hv, e, he⟩).elim
    · exact (hin ⟨c, ϖ, e, α, hU, hC, hB⟩).elim

end GlobalTheory.LFun.EigLoc
end
end

section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.quantitativeMahlerCriterion_unitaryGroup : ∀ I : AutInst, HtMin I := by
  first | exact @GlobalTheory.htMin_of_reduced | exact GlobalTheory.htMin_of_reduced | (intros; apply GlobalTheory.htMin_of_reduced <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.positionOne_of_symmetricDoubleIntegral_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (ρ₀ : Representation ℂ (GL (n₀ ⊕ Fin (c + 1 + 1)) k) (SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k))) (_ : IsSrc μ₁ ρ₀) (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (e : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ) (_ : SrcComb ψ ν (ρ + 1) ρ₀ Φ₁ e) (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ), (∀ g ∈ e.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F (om μ₁ g 1 Φ₁.1) Φ₂.1 (z g)) → OneDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁.1 Φ₂.1 (comb e z) := by
  first | exact @GlobalTheory.PosOne.oneDbl_of_symDbl | exact GlobalTheory.PosOne.oneDbl_of_symDbl | (intros; apply GlobalTheory.PosOne.oneDbl_of_symDbl <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.symmetricPositions_doubleIntegral_existsUnique : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), ∃! z, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁.1 Φ₂.1 z := by
  first | exact @GlobalTheory.PosOne.symDbl_existsUnique | exact GlobalTheory.PosOne.symDbl_existsUnique | (intros; apply GlobalTheory.PosOne.symDbl_existsUnique <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverDS

theorem gelf_one_eq_sum {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.Dec.gelf ε 1 f g = ∑ a, ∑ b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a f) g := by
  unfold GlobalTheory.Dec.gelf
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) _ _ (fun a => ?_)
  simp [GlobalTheory.Dec.cycWord, Formalism.REAL.Eword, List.ofFn_succ]

theorem casimir_eq_gelfVal_of_hasInfChar : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ χ : Fin n → ℂ, GlobalTheory.Dec.HasInfChar ε χ σ → ∀ v, casimir R.HK.act v = GlobalTheory.Dec.gelfVal χ 2 • v := by
  intro p q n e ε T R σ hb hf χ hχ v
  obtain ⟨hU, -, hK, -⟩ := GlobalTheory.T.coverFactoringRepresentation_unitaryGroup_dictionary p q n e ε T R.U σ hb hf
  have hkf : ∀ u : R.HK.V, IsKFin ε σ (R.ι u) := fun u =>
    (hK _).1 ((R.ι_range _).1 ⟨u, rfl⟩)
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    simp [UJset, Formalism.REAL.inUJ]
  have hσ1 : σ 1 = 1 := hU.1.1
  have key : ∀ u : R.HK.V,
      inner ℂ (R.ι u) (R.ι (casimir R.HK.act v - GlobalTheory.Dec.gelfVal χ 2 • v)) = 0 := by
    intro u
    have h := (hχ (R.ι v) (R.ι u) (hkf v) (hkf u)).2 1 1 h1
    rw [gelf_one_eq_sum, ← e.sum_comp] at h
    have h2 : ∀ a b : Ix p q,
        Formalism.REAL.Eab ε (e a) (e b) (Formalism.REAL.Eab ε (e b) (e a)
          (fun g => inner ℂ (R.ι u) (σ g (R.ι v)))) 1 =
        inner ℂ (R.ι u) (R.ι (R.HK.act (Eab a b) (R.HK.act (Eab b a) v))) := by
      intro a b
      rw [Formalism.REAL.lie_derivative_congr (e a) (e b)
        (fun x hx => GlobalTheory.T.matrixUnitDerivative_discreteSeriesMatrixCoeff p q n e ε T R σ hb hf b a v (R.ι u) x hx) h1,
        GlobalTheory.T.matrixUnitDerivative_discreteSeriesMatrixCoeff p q n e ε T R σ hb hf a b _ (R.ι u) 1 h1, hσ1]
      rfl
    have h3 : ∀ a : Ix p q, (∑ b : Fin n, Formalism.REAL.Eab ε (e a) b (Formalism.REAL.Eab ε b (e a)
          (fun g => inner ℂ (R.ι u) (σ g (R.ι v)))) 1) =
        ∑ b : Ix p q, inner ℂ (R.ι u) (R.ι (R.HK.act (Eab a b) (R.HK.act (Eab b a) v))) := by
      intro a
      rw [← e.sum_comp]
      exact Finset.sum_congr rfl (fun b _ => h2 a b)
    simp only [h3, hσ1] at h
    rw [map_sub, map_smul, inner_sub_right, inner_smul_right, sub_eq_zero]
    refine Eq.trans ?_ h

    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, inner_sum]
  have h0 := key (casimir R.HK.act v - GlobalTheory.Dec.gelfVal χ 2 • v)
  rw [inner_self_eq_zero] at h0
  exact sub_eq_zero.1 (R.ι_inj (h0.trans (map_zero _).symm))

end GlobalTheory.CoverDS
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitary_group_conjugate_transpose_matrix : ∀ (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsFrame β I.L → ∃ G : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), ((Formalism.UG.bc (Formalism.L2.Herm.intAf I.F I.E).subtype G : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  first | exact @GlobalTheory.GramFrame.gram_frame_int | exact GlobalTheory.GramFrame.gram_frame_int | (intros; apply GlobalTheory.GramFrame.gram_frame_int <;> assumption)
end

section


theorem _root_.GlobalTheory.T.chebotarev_degreeOne_valuationSubrings : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  first | exact @GlobalTheory.chebOmSt_holds | exact GlobalTheory.chebOmSt_holds | (intros; apply GlobalTheory.chebOmSt_holds <;> assumption)
end
