module

public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle004
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle172
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle186
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle081
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.LbB

section Inst

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}

theorem locInt_locAt (B : GL (Fin D.R.k) D.host.E) : LocInt (locAt X u w hg B) := by
  intro v x
  exact (X.g u w hg).completion_integers_iff v _ rfl x

theorem splAlg_locAt (B : GL (Fin D.R.k) D.host.E) : GlobalTheory.TwV.SplAlg (locAt X u w hg B) := by
  intro v a
  exact (X.g u w hg).spl_alg _ _ a

theorem reL_eq_map {a b : ℕ} (h : a = b) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) :
    reL h L = L.map (((Formalism.L2.PairingIndexBounds.F.reE (E := D.host.E) h : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) :
      (Fin a → D.host.E) →ₗ[D.host.E] (Fin b → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  subst h
  rfl



theorem lbAtB_locAt (B : GL (Fin D.R.k) D.host.E) (hrat : FrRat X u w hg B) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E))
    (hL : L = reL (rank_eq_first_level D.R) (X.lev0 u).Lb) : GlobalTheory.TwV.LbAtB (locAt X u w hg B) L := by
  rw [hL, reL_eq_map]
  exact lbAtB_of _ (locInt_locAt B) (splAlg_locAt B) _
    (frAtB_re (rank_eq_first_level D.R) (locAt X u w hg B) (X.lev0 u).Lb B rfl (fun v => (X.g u w hg).fr _ ((X.g u w hg).pl v).2)
      (fun v tt => (X.g u w hg).fr_lat _ _ tt) (fun v => hrat _ _))

end Inst

theorem lbAtB_lev0At : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Joint0 g.herm.lev0 u (g.forms u) → GlobalTheory.TwV.LbAtB (lev0At g u w hg).A (lev0At g u w hg).Lb := by
  intro D Gt c g u w hg hJ
  exact lbAtB_locAt g.cmp.B (g.cmp.fr_B u w hg) _ hJ.Lb_eq

end GlobalTheory.TwV.LbB

end
end

section

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.BasicNotions NumberField GlobalTheory.ThStr GlobalTheory.ThBe0 Classical

namespace GlobalTheory.ClassSumEquiv

open MvPolynomial

theorem polD_subst (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ)
    (y' γ' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (γ : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ τ, (γ' τ).det ≠ 0) :
    aeval (fun l : Idx D N N' => ∑ k, C ((γ' l.1)⁻¹ k l.2.1) * (X (l.1, k, l.2.2) : MvPolynomial (Idx D N N') ℂ))
      (aeval (fun l : Idx D N N' => ∑ k, C (γ l.1 l.2.2 k) * (X (l.1, l.2.1, k) : MvPolynomial (Idx D N N') ℂ))
        (polD D s Q (fun τ => γ' τ * y' τ))) =
      polD D s (aeval (fun k : FrV D N => ∑ a : Fin N, C (γ k.1 k.2.1 a) *
        (X (k.1, a, k.2.2) : MvPolynomial (FrV D N) ℂ)) Q) y' := by
  unfold polD
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun ⟨τ, a, k⟩ => ?_

  simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  split_ifs with hk
  · have e : y' τ b' ⟨k, hk⟩ = ∑ b, (γ' τ)⁻¹ b' b * (γ' τ * y' τ) b ⟨k, hk⟩ := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul_cancel_left _ _ (h τ).isUnit]

    rw [e, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  · simp

theorem applyAt0_polD_equivariant : ∀ (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ) (y' γ' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (γ : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (G : VC D N N' → ℂ), (∀ τ, (γ' τ).det ≠ 0) → Differentiable ℂ G → applyAt0 D (polD D s Q (fun τ => γ' τ * y' τ)) (fun z => G (fun τ => ((γ' τ)⁻¹ * Matrix.of (z τ) * γ τ : Matrix (Fin N') (Fin N) ℂ))) = applyAt0 D (polD D s (MvPolynomial.aeval (fun k : FrV D N => ∑ a : Fin N, MvPolynomial.C (γ k.1 k.2.1 a) * (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (FrV D N) ℂ)) Q) y') G := by
  intro D N N' s Q y' γ' γ G h hG
  have hd : Differentiable ℂ (fun z => G (GlobalTheory.NormSum.Minor.mulL (fun τ => (γ' τ)⁻¹) z)) :=
    hG.comp (LinearMap.toContinuousLinearMap (GlobalTheory.NormSum.Minor.mulL (a := N) (fun τ => (γ' τ)⁻¹))).differentiable
  have h1 := GlobalTheory.NormSum.Minor.applyAt0_comp hd (GlobalTheory.NormSum.Minor.mulR γ) (fun l k => γ l.1 l.2.2 k)
    (fun l k => (l.1, l.2.1, k)) (GlobalTheory.NormSum.Minor.mulR_coordV γ) (polD D s Q (fun τ => γ' τ * y' τ))
  rw [GlobalTheory.NormSum.Minor.applyAt0_comp hG (GlobalTheory.NormSum.Minor.mulL (fun τ => (γ' τ)⁻¹))
    (fun l k => (γ' l.1)⁻¹ k l.2.1) (fun l k => (l.1, k, l.2.2)) (GlobalTheory.NormSum.Minor.mulL_coordV _),
    polD_subst D N N' s Q y' γ' γ h] at h1
  rw [← h1]
  simp only [Matrix.mul_assoc]
  rfl

end GlobalTheory.ClassSumEquiv
end

section

noncomputable section

namespace GlobalTheory.TameEig

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology

theorem val_apply_eq {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (y : Ω) :
    A.valuation (σ y) = A.valuation y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h1 : A.valuation (σ y / y) = 1 := by
      have h2 := Valuation.map_add_eq_of_lt_left A.valuation (x := (1 : Ω)) (y := σ y / y - 1)
        (by rw [map_one]; exact hσ y hy)
      have e : (1 : Ω) + (σ y / y - 1) = σ y / y := by ring
      rwa [e, map_one] at h2
    have hv : A.valuation y ≠ 0 := by simpa using hy
    rw [map_div₀, div_eq_one_iff_eq hv] at h1
    exact h1

theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (σ : G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv := val_apply_eq A σ hσ
  have hD : σ ∈ Dec (F := E) A := by
    rw [mem_Dec]
    ext x
    have e : x = σ • ((σ⁻¹ : G E Ω) • x) := (smul_inv_smul σ x).symm
    rw [e, ValuationSubring.smul_mem_pointwise_smul_iff, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, AlgEquiv.smul_def σ, hv]
  refine ⟨hD, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have e : σ x - x = x * (σ x / x - 1) := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) (hσ x h0)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem residue_eq_one (N : NData R H what₂) (i : N.Loc) {x : N.O i}
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal (N.O i)) : IsLocalRing.residue (N.O i) x = 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue (N.O i)), ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hx

def chiBar (N : NData R H what₂) (i : N.Loc) : G H.E N.Om →* (IsLocalRing.ResidueField (N.O i))ˣ :=
  (Units.map (IsLocalRing.residue (N.O i)).toMonoidHom).comp (N.chi i 1)

theorem chiBar_val (N : NData R H what₂) (i : N.Loc) (g : G H.E N.Om) :
    ((chiBar N i g : (IsLocalRing.ResidueField (N.O i))ˣ) : IsLocalRing.ResidueField (N.O i)) =
      IsLocalRing.residue (N.O i) (chi1 N i g) := rfl

theorem chiBar_open (N : NData R H what₂) (i : N.Loc) : IsOpen ((chiBar N i).ker : Set (G H.E N.Om)) := by
  have hm : IsOpen (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i)) := by
    have := (isAdic_iff.1 (N.O_adic i)).1 1
    rwa [pow_one] at this
  let U1 : Set (G H.E N.Om) :=
    (fun g => ((N.chi i 1 g : (N.O i)ˣ) : N.O i) - 1) ⁻¹' (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i))
  have hU1 : IsOpen U1 := hm.preimage ((N.chi_cont i 1).sub continuous_const)
  have h1 : (1 : G H.E N.Om) ∈ U1 := by
    show ((N.chi i 1 1 : (N.O i)ˣ) : N.O i) - 1 ∈ IsLocalRing.maximalIdeal (N.O i)
    rw [map_one, Units.val_one, sub_self]; exact Ideal.zero_mem _
  have hsub : U1 ⊆ ((chiBar N i).ker : Set (G H.E N.Om)) := by
    intro g hg
    show Units.map (IsLocalRing.residue (N.O i)).toMonoidHom (N.chi i 1 g) = 1
    ext
    exact residue_eq_one N i hg
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU1.mem_nhds h1) hsub)

theorem not_isPrimePow_15 : ¬ IsPrimePow 15 := by
  intro h
  obtain ⟨p, k, hp, -, he⟩ := (isPrimePow_nat_iff 15).1 h
  have h3 : (3:ℕ) ∣ p ^ k := by rw [he]; norm_num
  have h5 : (5:ℕ) ∣ p ^ k := by rw [he]; norm_num
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h3)
  have e5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5)
  omega

theorem residue_ne_one (N : NData R H what₂) (i : N.Loc)
    (w : PlE H) (hS : w ∈ N.S i) (q : ℕ) (hq : q.Prime) (hq15 : q % 15 = 1) (hw : w ∈ placesOver H.E q)
    (hDel : Nat.card ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) = 15) :
    IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)) ≠ 1 := by
  intro h1
  haveI : Fact q.Prime := ⟨hq⟩
  have hval : (N.plOm.1 w).valuation (q : N.Om) < 1 := by
    have := ((N.plOm.2 w) ((q : ℕ) : 𝓞 H.E)).2 hw
    simpa using this
  have hcop : Nat.Coprime 15 q :=
    (Nat.gcd_rec 15 q).trans (by simp only [hq15, Nat.gcd_one_left])
  have hpow : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), N.chi i 1 σ ^ 15 = 1 := by
    intro σ hσ
    have h := pow_card_eq_one' (G := (Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1))
      (x := ⟨N.chi i 1 σ, Subgroup.mem_map_of_mem _ hσ⟩)
    rw [hDel] at h
    exact congrArg Subtype.val h
  have hwild : ∀ σ : G H.E N.Om, (∀ y : N.Om, y ≠ 0 → (N.plOm.1 w).valuation (σ y / y - 1) < 1) →
      σ ∈ (chiBar N i).ker := by
    intro σ hσ
    have hI := wild_mem_Ine (N.plOm.1 w) σ hσ
    have h15 : chiBar N i σ ^ 15 = 1 := by
      show (Units.map (IsLocalRing.residue (N.O i)).toMonoidHom) (N.chi i 1 σ) ^ 15 = 1
      rw [← map_pow, hpow σ hI, map_one]
    exact GlobalTheory.T.character_trivial_at_wild_of_coprime_pow H.E N.Om q (N.plOm.1 w) hval _ (chiBar N i) (chiBar_open N i) σ
      (fun a ha => hσ a ha) 15 (by norm_num) hcop h15
  have hg : N.gam0 i w ∈ (chiBar N i).ker :=
    MonoidHom.mem_ker.2 (Units.ext (by simp only [chiBar_val, h1, Units.val_one]))
  have hTG := N.restN_tameGenerator_generates i w (Or.inl hS)
  have hle : ((Subgroup.closure (insert (N.gam0 i w) {σ : G H.E N.Om | ∀ y : N.Om, y ≠ 0 →
      (N.plOm.1 w).valuation (σ y / y - 1) < 1}) : Subgroup (G H.E N.Om)) : Set (G H.E N.Om)) ⊆
      ((chiBar N i).ker : Set (G H.E N.Om)) :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hg, fun σ hσ => hwild σ hσ⟩)
  have hcl := Subgroup.isClosed_of_isOpen _ (chiBar_open N i)
  have hIne : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), IsLocalRing.residue (N.O i) (chi1 N i σ) = 1 := by
    intro σ hσ
    have h2 : σ ∈ (chiBar N i).ker := closure_minimal hle hcl (hTG.2 hσ)
    rw [← chiBar_val, MonoidHom.mem_ker.1 h2, Units.val_one]
  have : Finite ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hDel]; norm_num)
  obtain ⟨g, hgen⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1))
  obtain ⟨σ, hσ, hσg⟩ := Subgroup.mem_map.1 g.2
  have hord : orderOf (g : (N.O i)ˣ) = 15 := by rw [Subgroup.orderOf_coe, hgen, hDel]
  have hprim : IsPrimitiveRoot ((g : (N.O i)ˣ) : N.O i) 15 := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hord]
    exact IsPrimitiveRoot.orderOf _
  apply GlobalTheory.T.primitiveRoot_notPrimePow_map_ne_one' _ (N.O i) (IsLocalRing.residue (N.O i)) _ 15 (by norm_num) hprim not_isPrimePow_15
  rw [← hσg]
  exact hIne σ hσ

theorem charpoly_red (N : NData R H what₂) {i : N.Loc} (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))
    {w : PlE H} {x : N.X i} (hs : Formalism.MainNotions.SumRepresentations.SplitI N r w x) (γ : G H.E N.Om) (hγ : γ ∈ Ine (F := H.E) (N.plOm.1 w)) :
    ((redRep N i (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly =
      (X - 1) ^ R.r * (X - C (IsLocalRing.residue (N.O i) (chi1 N i γ))) ^ R.t := by
  have hK : (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).charpoly).map
      (algebraMap (N.O i) (Kf N i)) =
      ((X - 1) ^ R.r * (X - C (chi1 N i γ)) ^ R.t).map (algebraMap (N.O i) (Kf N i)) := by
    obtain ⟨Pm, hP⟩ := hs
    have h := hP γ hγ
    rw [← Matrix.charpoly_map]
    have e1 : ((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (algebraMap (N.O i) (Kf N i)) =
        ((mapRep (algebraMap (N.O i) (Kf N i)) (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Kf N i)) := rfl
    have h2 := Matrix.charpoly_units_conj' Pm
      ((mapRep (algebraMap (N.O i) (Kf N i)) (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Kf N i))
    rw [← Matrix.coe_units_inv, ← Units.val_mul, ← Units.val_mul, h] at h2
    rw [e1, ← h2]
    have h3 := Formalism.MainNotions.SumRepresentations.diagHom_charpoly (k := Kf N i) R.r R.t
      (Units.map (algebraMap (N.O i) (Kf N i)).toMonoidHom (N.chi i 1 γ))
    rw [Formalism.MainNotions.SumRepresentations.diagHom_coe] at h3
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_C]
    exact h3
  have hO := Polynomial.map_injective _ (IsFractionRing.injective (N.O i) (Kf N i)) hK
  have e2 : ((redRep N i (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) =
      ((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (IsLocalRing.residue (N.O i)) := rfl
  rw [e2, Matrix.charpoly_map, hO]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one, Polynomial.map_C]

end GlobalTheory.TameEig
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.RealNormChar

theorem conj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : E) :
    IsCMField.complexConj M (algebraMap E M x) = algebraMap E M (IsCMField.complexConj E x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E M)) x).symm

theorem algebraMap_mem_real {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : maximalRealSubfield E) : algebraMap E M x ∈ maximalRealSubfield M := by
  refine (IsCMField.complexConj_eq_self_iff M _).1 ?_
  rw [conj_algebraMap, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def realHom (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] : maximalRealSubfield E →+* maximalRealSubfield M :=
  ((algebraMap E M).comp (maximalRealSubfield E).subtype).codRestrict _ algebraMap_mem_real

def normChar {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) :
    HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩

theorem infIdele_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K w x = GroundTheory.Global.IdeleGroup.infiniteEmbedding w x := by
  classical
  refine Units.ext (Prod.ext (funext fun u => ?_) rfl)
  change Pi.mulSingle w (x : w.Completion) u = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (x : w.Completion) u
  rw [GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply]

theorem normChar_locInf {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (u : InfinitePlace L) (hu : u.IsReal) :
    (normChar L χ).locInf u (-1) = χ.locInf (u.comap (algebraMap K L)) (-1) := by
  have hv := hu.comap (algebraMap K L)
  show χ.1 (GroundTheory.Global.ideleNorm K L (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L u (-1))) =
    χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K (u.comap (algebraMap K L)) (-1))
  rw [infIdele_eq, infIdele_eq, GroundTheory.Global.ideleNorm_infiniteEmbedding]
  congr 2
  apply Units.ext
  apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective
  have := GroundTheory.Global.extensionEmbeddingOfIsReal_normUnits (K := K) u hu (-1)
  rw [this]
  simp


open scoped GroundTheory.Global.AdeleBaseChange in
open GlobalTheory.UnitaryHeckeBaseChange in
theorem ideleNorm_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.GalOfCusp.ideleNorm E x = GroundTheory.Global.ideleNorm (maximalRealSubfield E) E x := by
  apply Units.ext
  obtain ⟨z, hz⟩ := (adeleEquiv (isCMExt_real E)).surjective (x : AdeleRing (𝓞 E) E)
  have h : adeleNorm E (adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  have h2 : ∀ z, toAdele (maximalRealSubfield E) E z =
      GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft (maximalRealSubfield E) E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a l =>
      rw [toAdele_tmul, GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft_tmul]
      have hmap : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap
          (maximalRealSubfield E) E = GroundTheory.Global.AdeleBaseChange.adeleMap (maximalRealSubfield E) E := by
        ext a : 1
        apply Prod.ext
        · funext w
          open scoped NumberField.LiesOver in
          change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
          rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
        · apply FiniteAdeleRing.ext
          intro w
          change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap _ _ w _ =
            GroundTheory.Global.SemiLocal.completionMap _ w _
          rfl
      rw [hmap, mul_comm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  change adeleNorm E (x : AdeleRing (𝓞 E) E) = _
  rw [GroundTheory.Global.coe_ideleNorm, ← hz, h]
  have h3 : adeleEquiv (isCMExt_real E) z = _ := h2 z
  rw [h3]
  exact (Algebra.norm_eq_of_algEquiv _ _).symm

theorem main : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (a : ℕ) (χ : HChar (maximalRealSubfield K)), (∀ v : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  intro K M _ _ _ _ _ _ _ a χ hsign
  letI : Algebra (maximalRealSubfield K) (maximalRealSubfield M) := (realHom K M).toAlgebra
  haveI : IsScalarTower (maximalRealSubfield K) (maximalRealSubfield M) M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (maximalRealSubfield K) K M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨normChar (maximalRealSubfield M) χ,
    fun u => (normChar_locInf χ u (IsTotallyReal.isReal u)).trans (hsign _), fun x => ?_⟩
  show χ.1 (GroundTheory.Global.ideleNorm _ _ (GlobalTheory.GalOfCusp.ideleNorm M x)) =
    χ.1 (GlobalTheory.GalOfCusp.ideleNorm K (GroundTheory.Global.ideleNorm K M x))
  rw [ideleNorm_eq, ideleNorm_eq, GroundTheory.Global.ideleNorm_ideleNorm, GroundTheory.Global.ideleNorm_ideleNorm]

end GlobalTheory.RealNormChar

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.DecCover

theorem main : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (N : Subgroup (_root_.Formalism.ConjugateSelfDual.G F Ω)), IsOpen (N : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T ∧ ∀ g : _root_.Formalism.ConjugateSelfDual.G F Ω, ∃ u ∈ T, ∃ A' : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A' u ∧ ∃ x ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A', ∃ n ∈ N, g = x * n := by
  intro Ω _ F _ _ _ _ v N hN
  classical
  have : IsGalois F Ω := {}
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hN N.one_mem
  have hcheb := fun g : _root_.Formalism.ConjugateSelfDual.G F Ω =>
    GlobalTheory.Published.cheb_holds F Ω U.toSubgroup U.isOpen U.isNormal' g {v}
  choose u hu _ _ B hB _ σ hσ hσU using hcheb
  have hmem : ∀ g : _root_.Formalism.ConjugateSelfDual.G F Ω, (σ g)⁻¹ * g ∈ N := by
    intro g
    apply hU
    have h1 := U.isNormal'.conj_mem _ (hσU g) (σ g)⁻¹
    have h2 : (σ g)⁻¹ * (σ g * g⁻¹) * (σ g)⁻¹⁻¹ = ((σ g)⁻¹ * g)⁻¹ := by group
    rw [h2] at h1
    have h3 := U.toSubgroup.inv_mem h1
    rw [inv_inv] at h3
    exact h3
  have hopen : ∀ g : _root_.Formalism.ConjugateSelfDual.G F Ω, IsOpen {h : _root_.Formalism.ConjugateSelfDual.G F Ω | (σ g)⁻¹ * h ∈ N} := fun g =>
    hN.preimage (continuous_const_mul _)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun g : _root_.Formalism.ConjugateSelfDual.G F Ω => {h : _root_.Formalism.ConjugateSelfDual.G F Ω | (σ g)⁻¹ * h ∈ N}) hopen
    (fun g _ => Set.mem_iUnion.2 ⟨g, hmem g⟩)
  refine ⟨t.image u, ?_, fun g => ?_⟩
  · intro hv
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hv
    exact hu i (by simp [hi])
  · obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ g))
    refine ⟨u i, Finset.mem_image_of_mem u hi, B i, hB i, σ i, (hσ i).1, (σ i)⁻¹ * g, hgi, ?_⟩
    group

end GlobalTheory.DecCover

end
end
