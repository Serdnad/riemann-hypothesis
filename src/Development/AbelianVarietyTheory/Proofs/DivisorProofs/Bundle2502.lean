module

public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.Bundle032
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairBDual
import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
public import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle588
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle550
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisDual

open Formalism.HermitianLatticesTheory Formalism.UG Formalism.L2.Forms
open scoped Matrix

theorem natCast_notMem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {l s : ℕ}
    (hl : l.Prime) (hlw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) (hs : ¬ l ∣ s) : (s : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hcop : Nat.Coprime l s := (hl.coprime_iff_not_dvd).2 hs
  obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hlw
  · simpa using h

theorem isBasisAt_tauLat {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ}
    (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) {l : ℕ} (hl : l.Prime)
    (hlw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) (M : Submodule (𝓞 E) (Fin n → E)) (B : GL (Fin n) E)
    (hB : IsLocBasis l (M : Set (Fin n → E)) B) : IsBasisAt w (tauLat emb τ M) (bc (emb τ) B) := by
  have h1 : ¬ l ∣ 1 := fun h => hl.one_lt.ne' (Nat.dvd_one.1 h)
  unfold IsBasisAt
  apply le_antisymm
  · rw [← localized_localized w (colLat _)]
    refine localization_mono _ ?_
    unfold tauLat
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s', hs', hint⟩ := (hB x).1 ⟨1, h1, by simpa using hx⟩
    refine ⟨(s' : 𝓞 K), natCast_notMem w hl hlw hs', ?_⟩
    rw [lc_mem_colLat]
    intro a
    have e : ((s' : 𝓞 K) • fun b => emb τ (x b)) = fun b => emb τ (((s' : E) • x) b) := by
      funext b
      simp [Algebra.smul_def]
    rw [e, Formalism.L2.Col.vl_bc_inv_mulVec, Matrix.mulVec_smul]
    obtain ⟨r, hr⟩ := hint a
    exact du_map_mem_one (emb τ) (Submodule.mem_one.2 ⟨r, by rw [hr]; rfl⟩)
  · rw [← localized_localized w (tauLat emb τ M)]
    refine localization_mono _ ?_
    unfold colLat
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s', hs', hmem⟩ := (hB (fun a => (B : Matrix (Fin n) (Fin n) E) a j)).2 ⟨1, h1, fun a => by
      have e : (((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ fun a => (B : Matrix (Fin n) (Fin n) E) a j) a =
          (1 : Matrix (Fin n) (Fin n) E) a j := by
        have h2 : ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (B : Matrix (Fin n) (Fin n) E) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [← h2]
        rfl
      rw [e, Matrix.one_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩⟩
    refine ⟨(s' : 𝓞 K), natCast_notMem w hl hlw hs', ?_⟩
    refine Submodule.subset_span ⟨_, hmem, ?_⟩
    funext b
    simp [Algebra.smul_def, bc_coe]

end GlobalTheory.LocBasisDual

namespace GlobalTheory.LocBasisDual

theorem basisAt_dualFr_tauLat : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E M → (∃ B, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B) ∧ Submodule.IsLattice K (dualFr (tauLat emb τ M)) ∧ ∀ B : GL (Fin n) E, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B → IsBasisAt w (dualFr (tauLat emb τ M)) (inside₂ K n (Matrix.GeneralLinearGroup.map (emb τ) B)) := by
  intro E K _ _ _ _ ι _ n emb τ w l hl hlw M hM
  have : Fact l.Prime := ⟨hl⟩
  refine ⟨Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis l E M hM.fg (Submodule.IsFullLattice.span_eq_top (self := hM)),
    (Formalism.L2.DIV.dualFr_tauLat_isLattice emb τ M hM).toIsLattice, fun B hB => ?_⟩
  exact pb_isBasisAt_dualFr w _ (tauLatticeLattice_holds E K ι n emb τ M hM).fg _
    (isBasisAt_tauLat emb τ w hl hlw M B hB)

end GlobalTheory.LocBasisDual
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.HeisTranslSum

theorem isHalf_add' {D : D7} {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u + v) := fun i j => by
  rw [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_sub' {D : D7} {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u - v) := fun i j => by
  rw [Matrix.sub_apply, mul_sub, hu i j, hv i j]

theorem half_duality {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {Q : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e Q)
    (x : WO S T) (hx : IsHalf e x) :
    (∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT := by
  obtain ⟨hd, -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  have hmul : ∀ P ∈ Q, e * es P = es P := by
    intro P hP
    rw [hsum, Finset.sum_mul, Finset.sum_eq_single_of_mem P hP]
    · exact (hes P hP).1.1
    · intro R hR hne
      exact GlobalTheory.Tow.idemAt_orth (hes R hR) (hes P hP) hne
  have he1 : e * e = e := by
    conv_lhs => rhs; rw [hsum]
    rw [Finset.mul_sum, Finset.sum_congr rfl hmul, ← hsum]
  have hc1 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he1]
  have hinf : infPart D e = 0 := by

    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun P hP => GlobalTheory.SplitScalar.infPart_splitIdem (hes P hP).1
  have hfin : x.map (infPart D) = 0 := by
    ext i j
    show infPart D (x i j) = 0
    rw [← hx i j, RingHom.map_mul, hinf, zero_mul]
  refine ⟨fun h => (hd x hfin).2 fun u hu => ?_, fun h y hy _ => (hd x hfin).1 h y hy⟩
  have hst : cA D e • u ∈ latAll S T ΛS ΛT :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc1])) u hu
  have := h _ hst (GlobalTheory.SplitScalar.isHalf_smul hc1 u)
  rwa [← GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx] at this

theorem sum_heisO_base_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ z : GA D S, (∀ t : WO S T, IsHalf e t → actO S T z⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT) → ∀ Rr : Finset (WO S T), (∀ u ∈ Rr, actO S T z⁻¹ 1 u ∈ latAll S T ΛS ΛT ∧ IsHalf (cA D e) u) → (∀ w, actO S T z⁻¹ 1 w ∈ latAll S T ΛS ΛT → IsHalf (cA D e) w → ∃! v, v ∈ Rr ∧ w - v ∈ latAll S T ΛS ΛT) → (∀ w ∈ latAll S T ΛS ΛT, IsHalf (cA D e) w → actO S T z⁻¹ 1 w ∈ latAll S T ΛS ΛT) → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm → ∑ u ∈ Rr, heisO ψ S T u f₀ = (Rr.card : ℂ) • Tm (actPull (z, (1 : GA D T)) (halfInd e (latAll S T ΛS ΛT))) := by
  intro D ψ hψ S T ΛS ΛT hS hT Q e he z hz Rr hRr huniq hlat f₀ Tm hM
  have hB := half_duality hψ hS hT he
  have hSB := GlobalTheory.isSBHalf_halfInd e (latAll S T ΛS ΛT)
  have hvac : Tm (halfInd e (latAll S T ΛS ΛT)) = f₀ := by simpa using hM.vac
  have h1 : ∀ u ∈ Rr, heisO ψ S T u f₀ =
      Tm (fun t => ψ (symplO S T t u) * halfInd e (latAll S T ΛS ΛT) t) := by
    intro u hu
    rw [← hvac, hM.modul _ hSB u (hRr u hu).2]

  rw [Finset.sum_congr rfl h1, ← map_sum, ← map_smul]
  congr 1
  funext t
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_mul]
  simp only [actPull, inv_one]
  set Λ := latAll S T ΛS ΛT with hΛ
  set x := actO S T z⁻¹ 1 t with hx
  by_cases hte : IsHalf e t
  · have hxe : IsHalf e x := (Formalism.IndefR.Fin.LevelGroupLemmas.isHalf_actO z⁻¹ 1 t).2 hte
    by_cases hxΛ : x ∈ Λ
    · have htΛ : t ∈ Λ := hz t hte hxΛ
      have ht1 : halfInd e Λ t = 1 := by simp only [halfInd]; rw [if_pos ⟨htΛ, hte⟩]
      have hx1 : halfInd e Λ x = 1 := by simp only [halfInd]; rw [if_pos ⟨hxΛ, hxe⟩]
      rw [ht1, hx1, mul_one, mul_one]
      have : ∀ u ∈ Rr, ψ (symplO S T t u) = 1 := by
        intro u hu
        rw [← GlobalTheory.SplitHecke.symplO_actO S T z⁻¹ 1 t u]
        exact (hB x hxe).2 hxΛ _ (hRr u hu).1
          ((Formalism.IndefR.Fin.LevelGroupLemmas.isHalf_actO z⁻¹ 1 u).2 (hRr u hu).2)
      rw [Finset.sum_congr rfl this]
      simp
    · have hx0 : halfInd e Λ x = 0 := by
        simp only [halfInd]; rw [if_neg fun h => hxΛ h.1]
      rw [hx0, mul_zero]
      by_cases htΛ : t ∈ Λ
      · have ht1 : halfInd e Λ t = 1 := by simp only [halfInd]; rw [if_pos ⟨htΛ, hte⟩]
        rw [ht1, mul_one]
        have hchar : ∀ w ∈ Λ, IsHalf (cA D e) w → ψ (symplO S T t w) = 1 := (hB t hte).2 htΛ
        have hnot : ¬ ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1 := fun h => hxΛ ((hB x hxe).1 h)
        push Not at hnot
        obtain ⟨y, hyΛ, hyH, hyψ⟩ := hnot
        set u₀ := actO S T z 1 y with hu₀
        have hy0 : actO S T z⁻¹ 1 u₀ = y := by
          have := GlobalTheory.SplitHecke.actO_inv_actO (S := S) (T := T) z 1 y
          rwa [inv_one] at this
        have hu₀H : IsHalf (cA D e) u₀ := (Formalism.IndefR.Fin.LevelGroupLemmas.isHalf_actO z 1 y).2 hyH
        have hψu₀ : ψ (symplO S T t u₀) ≠ 1 := by
          rw [← GlobalTheory.SplitHecke.symplO_actO S T z⁻¹ 1 t u₀, hy0]; exact hyψ
        have hact_add : ∀ a b : WO S T, actO S T z⁻¹ 1 (a + b) = actO S T z⁻¹ 1 a + actO S T z⁻¹ 1 b :=
          fun a b => map_add (GlobalTheory.SplitHecke.actAdd S T z⁻¹ 1) a b
        have hact_sub : ∀ a b : WO S T, actO S T z⁻¹ 1 (a - b) = actO S T z⁻¹ 1 a - actO S T z⁻¹ 1 b :=
          fun a b => map_sub (GlobalTheory.SplitHecke.actAdd S T z⁻¹ 1) a b
        have hshift : ∀ u ∈ Rr, actO S T z⁻¹ 1 (u + u₀) ∈ Λ ∧ IsHalf (cA D e) (u + u₀) := fun u hu =>
          ⟨by rw [hact_add, hy0]; exact Λ.add_mem (hRr u hu).1 hyΛ, isHalf_add' (hRr u hu).2 hu₀H⟩
        let rep : ∀ u ∈ Rr, WO S T := fun u hu =>
          ((huniq (u + u₀) (hshift u hu).1 (hshift u hu).2).exists).choose
        have hrep : ∀ u (hu : u ∈ Rr), rep u hu ∈ Rr ∧ (u + u₀) - rep u hu ∈ Λ := fun u hu =>
          ((huniq (u + u₀) (hshift u hu).1 (hshift u hu).2).exists).choose_spec
        have hsum : (∑ u ∈ Rr, ψ (symplO S T t u)) * ψ (symplO S T t u₀) = ∑ u ∈ Rr, ψ (symplO S T t u) := by
          rw [Finset.sum_mul]
          refine Finset.sum_bij rep (fun u hu => (hrep u hu).1) ?_ ?_ ?_
          · intro a₁ ha₁ a₂ ha₂ heq
            have hd : a₁ - a₂ ∈ Λ := by
              have := Λ.sub_mem (hrep a₁ ha₁).2 (hrep a₂ ha₂).2
              rw [heq] at this
              convert this using 1; abel
            exact (huniq a₁ (hRr a₁ ha₁).1 (hRr a₁ ha₁).2).unique ⟨ha₁, by simp⟩ ⟨ha₂, hd⟩
          · intro b hb
            have hw1 : actO S T z⁻¹ 1 (b - u₀) ∈ Λ := by
              rw [hact_sub, hy0]; exact Λ.sub_mem (hRr b hb).1 hyΛ
            have hw2 : IsHalf (cA D e) (b - u₀) := isHalf_sub' (hRr b hb).2 hu₀H
            obtain ⟨a, ha, hwa⟩ := (huniq (b - u₀) hw1 hw2).exists
            refine ⟨a, ha, ?_⟩
            refine (huniq (a + u₀) (hshift a ha).1 (hshift a ha).2).unique (hrep a ha) ⟨hb, ?_⟩
            have := Λ.neg_mem hwa
            convert this using 1; abel
          · intro u hu
            have hdiff := (hrep u hu).2
            have hH : IsHalf (cA D e) ((u + u₀) - rep u hu) :=
              isHalf_sub' (isHalf_add' (hRr u hu).2 hu₀H) (hRr _ (hrep u hu).1).2
            rw [← AddChar.map_add_eq_mul, ← GlobalTheory.LatVac.symplO_add_right]
            have hsplit : u + u₀ = rep u hu + ((u + u₀) - rep u hu) := by abel
            rw [hsplit, GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul, hchar _ hdiff hH, mul_one]
        have hzero : (∑ u ∈ Rr, ψ (symplO S T t u)) * (ψ (symplO S T t u₀) - 1) = 0 := by
          rw [mul_sub, hsum, mul_one, sub_self]
        rcases mul_eq_zero.1 hzero with h | h
        · exact h
        · exact absurd (sub_eq_zero.1 h) hψu₀
      · have ht0 : halfInd e Λ t = 0 := by simp only [halfInd]; rw [if_neg fun h => htΛ h.1]
        rw [ht0, mul_zero]
  · have hxe : ¬ IsHalf e x := fun h => hte ((Formalism.IndefR.Fin.LevelGroupLemmas.isHalf_actO z⁻¹ 1 t).1 h)
    have ht0 : halfInd e Λ t = 0 := by simp only [halfInd]; rw [if_neg fun h => hte h.2]
    have hx0 : halfInd e Λ x = 0 := by simp only [halfInd]; rw [if_neg fun h => hxe h.2]
    rw [ht0, hx0, mul_zero, mul_zero]

end GlobalTheory.HeisTranslSum
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PullModelLaw

theorem om_apply_eq_smul_pull : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm → ∀ (p : GA D S × GA D T) (κ : ℂ), (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull p Φ)) → om p f₀ = κ • Tm (actPull p (halfInd e (latAll S T ΛS ΛT))) → ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → om p (Tm Φ) = κ • Tm (actPull p Φ) := by
  intro D ψ S T χS χT om hW ΛS ΛT hsS hsT Q e he f₀ hf₀ _ Tm hTm p κ hsb hκ Φ hΦ
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hthm : ∀ Ψ, IsSBHalf e (latAll S T ΛS ΛT) Ψ → IsThetaFunO ψ S T (Tm Ψ) :=
    GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T ΛS ΛT hsS hsT e hee hinf f₀ hf₀ Tm hTm
  have hqp : ((p.1⁻¹, p.2⁻¹) : GA D S × GA D T) * p = 1 := Prod.ext (by simp) (by simp)
  have hpq : p * ((p.1⁻¹, p.2⁻¹) : GA D S × GA D T) = 1 := Prod.ext (by simp) (by simp)
  have hback : ∀ x : WO S T, actO S T p.1⁻¹ p.2⁻¹ (actO S T p.1 p.2 x) = x := fun x => by
    rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
  have hsmul : ∀ (w : WO S T) (c : ℂ) (F : WO S T → ℂ), c • heisO ψ S T w F = heisO ψ S T w (c • F) :=
    fun w c F => by
      funext t
      simp only [heisO, Pi.smul_apply, smul_eq_mul]
      ring
  let L : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := actPull p, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := κ • ((om (p.1⁻¹, p.2⁻¹)).comp (Tm.comp L))
  have hTm'ap : ∀ Ψ, Tm' Ψ = κ • om (p.1⁻¹, p.2⁻¹) (Tm (actPull p Ψ)) := fun Ψ => rfl
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm' := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hx' : IsHalf e (actO S T p.1 p.2 x) := (isHalf_actO p.1 p.2 x).2 hx
      have e1 : actPull p (fun t => Ψ (t + x)) = fun t => actPull p Ψ (t + actO S T p.1 p.2 x) := by
        funext t
        show Ψ (actO S T p.1⁻¹ p.2⁻¹ t + x) = Ψ (actO S T p.1⁻¹ p.2⁻¹ (t + actO S T p.1 p.2 x))
        rw [actO_add, hback]
      rw [hTm'ap, hTm'ap, e1, hTm.trans _ (hsb Ψ hΨ) _ hx',
        hW.om_heis p.1⁻¹ p.2⁻¹ _ _ (hthm _ (hsb Ψ hΨ)), hback, hsmul]
    · have hy' : IsHalf (cA D e) (actO S T p.1 p.2 y) := (isHalf_actO p.1 p.2 y).2 hy
      have e1 : actPull p (fun t => ψ (symplO S T t y) * Ψ t) =
          fun t => ψ (symplO S T t (actO S T p.1 p.2 y)) * actPull p Ψ t := by
        funext t
        show ψ (symplO S T (actO S T p.1⁻¹ p.2⁻¹ t) y) * Ψ (actO S T p.1⁻¹ p.2⁻¹ t) =
          ψ (symplO S T t (actO S T p.1 p.2 y)) * Ψ (actO S T p.1⁻¹ p.2⁻¹ t)
        conv_lhs => rw [← hback y]
        rw [Formalism.IndefR.Eqv.symplO_actO]
      rw [hTm'ap, hTm'ap, e1, hTm.modul _ (hsb Ψ hΨ) _ hy',
        hW.om_heis p.1⁻¹ p.2⁻¹ _ _ (hthm _ (hsb Ψ hΨ)), hback, hsmul]
    · rw [one_smul, hTm'ap, ← map_smul, ← hκ, ← Module.End.mul_apply, ← map_mul, hqp, map_one,
        Module.End.one_apply]
  have e3 : Tm Φ = Tm' Φ := GlobalTheory.PlaceVec.placeModel_unique hW.std hsS hsT hee hinf hTm hTm' hΦ
  rw [e3, hTm'ap, map_smul, ← Module.End.mul_apply, ← map_mul, hpq, map_one, Module.End.one_apply]

end GlobalTheory.PullModelLaw

end
end
