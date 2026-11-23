module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle058
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.LevMod

open GlobalTheory.CongLevel

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))

def RedTo (g : Sp E n ≃ₗ[E] Sp E n) (hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : Prop :=
  ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)

variable {P}

theorem RedTo.one : RedTo P (1 : Sp E n ≃ₗ[E] Sp E n) 1 := fun x _ => by
  rw [Units.val_one, Matrix.one_mulVec]; rfl

theorem RedTo.mul {g g' : Sp E n ≃ₗ[E] Sp E n} {a b : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hg' : g' ∈ GLint E n P)
    (h : RedTo P g a) (h' : RedTo P g' b) : RedTo P (g * g') (a * b) := fun x hx => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h' x hx]
  exact h _ ((hg' x).2 hx)

theorem RedTo.inv {g : Sp E n ≃ₗ[E] Sp E n} {a : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hg : g ∈ GLint E n P)
    (h : RedTo P g a) : RedTo P g⁻¹ a⁻¹ := fun x hx => by
  have h1 := h _ (((inv_mem hg : g⁻¹ ∈ GLint E n P) x).2 hx)
  rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at h1
  rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]


variable (P) in
def redSub (G : Subgroup (Sp E n ≃ₗ[E] Sp E n)) (hG : G ≤ GLint E n P) : Subgroup (GL (Fin n) (𝓞 E ⧸ P.asIdeal)) where
  carrier := {a | ∃ g ∈ G, RedTo P g a}
  one_mem' := ⟨1, one_mem _, RedTo.one⟩
  mul_mem' := fun ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g * g', mul_mem hg hg', RedTo.mul (hG hg') h h'⟩
  inv_mem' := fun ⟨g, hg, h⟩ => ⟨g⁻¹, inv_mem hg, h.inv (hG hg)⟩

end Red

theorem unipotentArg_extendByIdOnLastCoords {E : Type} [Field E] {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    Loc.n1Arg (extE c κ) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [add_assoc, extE_apply, resX_eN]
  simp only [map_zero, sub_self, add_zero]
  unfold Loc.atN Loc.eN
  split_ifs with h1 h2
  · exact absurd h2 (by simp)
  · rfl
  · rfl

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem extE_mem_Cbe (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E))) (h : AutY X R j)
    (hh : h ∈ stabL X.E _ (lamYat (Pr := Pr) j w)) (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j))
    (hκ : κ ∈ GLint X.E (R.N j) w) (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    extE (cOf R j) κ ∈ Loc.Cbe (Jat (Pr := Pr) sharp j w) h := by
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero w
  unfold lamYat at hh
  rw [if_pos hw] at hh
  refine ⟨extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ κ, ?_⟩
  have e : (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) = h⁻¹ * extE (cOf R j) κ * h := by simp
  show (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) ∈ Jat (Pr := Pr) sharp j w
  rw [e]
  have hs := mul_mem (mul_mem (inv_mem hh) (extE_stab w (qOf w) (cOf R j) (fun i => i + 1) κ hκ)) hh
  have hc := conj_cong (qOf w) _ _ h hh (extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr)
  unfold Jat
  rw [if_pos hw]
  split_ifs
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact CongLevel.sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact CongLevel.sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _

theorem exists_levG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j), cst.Ok → P.1 ∈ Pr.vGs → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → (∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, y x ∈ lamYat (Pr := Pr) (R := R) j P.1) → lamRow Ch mu cst.sharp j P.1 (LinearMap.id + (qOf P.1 : X.E) • y) = 1) → ChiMul Ch sel mu cst j P h → ChiTriv Ch sel mu cst j P h → ∃ lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j), GrpG sel mu cst j P h lev ∧ ChrG Ch sel mu cst j P h lev := by
  intro X Pr R Ch sel S mu cst j P h hc hP hdu hh hle hlam hmul htriv
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) := fun a ha h0 => by
    have := GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq P.1 _ (Ideal.absNorm_mem _) hdu.2 a ha h0
    rwa [map_natCast] at this
  have hone : ∀ κ ∈ GLint X.E (R.N j) P.1, (∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (κ x) = redV P.1 x) →
      chiInv Ch sel mu cst j P h (extE (cOf R j) κ) = 1 := by
    intro κ hκ hr
    unfold lamYat at hh hlam
    rw [if_pos hP] at hh hlam
    have hcong := conj_cong (qOf P.1) _ _ h hh
      (extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd κ hκ hr)
    have h1 := hlam ((qOf P.1 : X.E)⁻¹ • ((h⁻¹ * extE (cOf R j) κ * h : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have h2 := hcong x hx
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, unipotentArg_extendByIdOnLastCoords, hc.psi_int P 0 (by simpa using CongLevel.intAt_nat P.1 0), inv_one, one_mul]
  obtain ⟨lam, hl⟩ := exists_char (H := ↥(redSub P.1 _ hle)) (CAt sel mu cst j P h) (chiInv Ch sel mu cst j P h)
    (fun r a => ∃ g ∈ GLint X.E (R.N j) P.1,
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) ∧ RedTo P.1 g a.1)
    hmul.1 hmul.2
    (fun ⟨a, g, hg, hga⟩ => by
      obtain ⟨r, hr, hrg⟩ := id hg
      exact ⟨r, hr, g, hle hg, hrg, hga⟩)
    (by
      rintro r a r' a' ⟨g, hg, h1, h2⟩ ⟨g', hg', h1', h2'⟩
      refine ⟨g * g', mul_mem hg hg', fun x => ?_, RedTo.mul hg' h2 h2'⟩
      show r (r' _) = _
      rw [h1', h1]
      rfl)
    (by
      rintro a r hr r' hr' ⟨g, hg, h1, h2⟩ ⟨g', hg', h1', h2'⟩
      have hκ : g⁻¹ * g' ∈ GLint X.E (R.N j) P.1 := mul_mem (inv_mem hg) hg'
      have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 ((g⁻¹ * g') x) = redV P.1 x := fun x hx => by
        rw [RedTo.mul hg' (h2.inv hg) h2' x hx, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      have hs : extE (cOf R j) (g⁻¹ * g') ∈ CAt sel mu cst j P h := extE_mem_Cbe _ j P.1 hP hd h hh _ hκ hred
      have ht : (extE (cOf R j) (g⁻¹ * g'))⁻¹ * (r⁻¹ * r') ∈ CAt sel mu cst j P h :=
        mul_mem (inv_mem hs) (mul_mem (inv_mem hr) hr')
      have ht1 := htriv _ ht fun x => by
        show (extE (cOf R j) (g⁻¹ * g')).symm (r.symm (r' _)) = _
        rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, extE_inX, h1, h1']
        exact congrArg _ (g.apply_symm_apply _).symm
      have e : r' = r * (extE (cOf R j) (g⁻¹ * g') * ((extE (cOf R j) (g⁻¹ * g'))⁻¹ * (r⁻¹ * r'))) := by
        rw [mul_inv_cancel_left, mul_inv_cancel_left]
      have h3 := hmul.2 r hr _ (mul_mem hs ht)
      rw [← e, hmul.2 _ hs _ ht, ht1, hone _ hκ hred, mul_one, mul_one] at h3
      exact h3.symm)
  exact ⟨⟨redSub P.1 _ hle, lam⟩, fun _ => Iff.rfl,
    fun a g r hr h1 h2 => hl a r hr ⟨g, hle ⟨r, hr, h1⟩, h1, h2⟩⟩

end GlobalTheory.Mem.Col2.LevMod

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem GlobalTheory.TameRecip.exists_ine_of_unit : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) → ∀ (x : (v.adicCompletion E)ˣ) (u : 𝓞 E), IsUnitAt v x → Valued.v ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) < 1 → ∃ σ ∈ Ine (F := E) A, toAb E Ω σ = art (localIdele E v x) ∧ A.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 := by
  intro H E Ω _ _ _ _ _ _ art ha v A hA ϖ hϖ1 hϖ2 π hπ x u hx hxu
  have hq : 1 < normV v := by
    unfold normV
    have : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    exact Finite.one_lt_card
  have hn : 0 < normV v - 1 := by omega
  have hvE : ∀ a : 𝓞 E, Valued.v (algebraMap E (v.adicCompletion E) (a : E)) = v.valuation E (a : E) :=
    fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have hu1 : Valued.v (algebraMap E (v.adicCompletion E) (u : E)) = 1 := by
    rw [hvE]
    refine le_antisymm (v.valuation_le_one u) (not_lt.mp fun h => ?_)
    have hm : u ∈ v.asIdeal := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mp h
    have hlt : Valued.v (x : v.adicCompletion E) < 1 := by
      have e : (x : v.adicCompletion E) = ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) +
          algebraMap E (v.adicCompletion E) (u : E) := by ring
      rw [e]
      refine Valuation.map_add_lt _ hxu ?_
      rw [hvE]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mpr hm
    have hx' : Valued.v (x : v.adicCompletion E) = 1 := hx
    rw [hx'] at hlt
    exact lt_irrefl _ hlt
  have hu : u ∉ v.asIdeal := by
    intro hm
    have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mpr hm
    rw [← hvE, hu1] at h
    exact lt_irrefl _ h
  have hu0 : algebraMap E (v.adicCompletion E) (u : E) ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  let uc : (v.adicCompletion E)ˣ := Units.mk0 _ hu0
  have hy : Valued.v (((x * uc⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) < 1 := by
    have e : ((x * uc⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1 =
        ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) *
          (algebraMap E (v.adicCompletion E) (u : E))⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, uc, Units.val_mk0]
      field_simp
    rw [e, map_mul, map_inv₀, hu1, inv_one, mul_one]
    exact hxu
  obtain ⟨z, hz1, hz⟩ := GlobalTheory.T.exists_unit_pow_normV_sub_one' E v (x * uc⁻¹) hy
  obtain ⟨ρ, hρ, hρz⟩ := (ha.ine v A hA _).mp ⟨z, hz1, rfl⟩
  obtain ⟨τ, hτF, hτπ, hτc⟩ := GlobalTheory.T.exists_frob_of_eisenstein_root H E Ω art ha v A hA ϖ hϖ1 hϖ2 π hπ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (u : E)) hn
  have h1' : u * ϖ ∈ v.asIdeal := Ideal.mul_mem_left _ _ hϖ1
  have h2' : u * ϖ ∉ v.asIdeal ^ 2 := by
    intro h
    rcases Ideal.IsPrime.mul_mem_pow v.asIdeal h with h3 | h3
    · exact hu h3
    · exact hϖ2 h3
  have hπ' : (π * t) ^ (normV v - 1) = algebraMap E Ω ((u * ϖ : 𝓞 E) : E) := by
    rw [mul_pow, hπ, ht, ← map_mul]
    push_cast
    ring_nf
  obtain ⟨τ', hτ'F, hτ'π, hτ'c⟩ := GlobalTheory.T.exists_frob_of_eisenstein_root H E Ω art ha v A hA (u * ϖ) h1' h2' (π * t) hπ'
  have hσ0 : τ'⁻¹ * τ ∈ Ine (F := E) A := GlobalTheory.T.frobenius_inv_mul_mem_inertia E Ω v A hA τ τ' hτF hτ'F
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    have : ϖ = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 hπ
  have hval := GlobalTheory.T.frobenius_ratio_pi_congr_tame_unit E Ω v A hA u hu π t hπ0 ht τ τ' hτF hτ'F hτπ hτ'π
  have hc0 : (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ((map_ne_zero _).mpr hϖ0)
  have huE : (u : E) ≠ 0 := by
    intro h
    apply hu
    have : u = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  have hcast : ((u * ϖ : 𝓞 E) : E) = (u : E) * (ϖ : E) := by push_cast; ring
  have hs0 : ((-1) ^ normV v : v.adicCompletion E) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hϖc : algebraMap E (v.adicCompletion E) (ϖ : E) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hc0' : (-1) ^ normV v * algebraMap E (v.adicCompletion E) (((u * ϖ : 𝓞 E)) : E) ≠ 0 := by
    rw [hcast, map_mul]
    exact mul_ne_zero hs0 (mul_ne_zero hu0 hϖc)
  have ec := hτc (Units.mk0 _ hc0) rfl
  have ec' := hτ'c (Units.mk0 _ hc0') rfl
  have hmain : toAb E Ω (τ'⁻¹ * τ) = art (localIdele E v uc) := by
    have e1 : toAb E Ω τ = (art (localIdele E v (Units.mk0 _ hc0)))⁻¹ := by
      rw [← ec, map_inv, inv_inv]
    rw [map_mul, ec', e1, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 2
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, uc]
    rw [hcast, map_mul]
    field_simp
  refine ⟨τ'⁻¹ * τ * ρ ^ (normV v - 1), mul_mem hσ0 (pow_mem hρ _), ?_, ?_⟩
  · rw [map_mul, map_pow, hmain, hρz, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hz]
    congr 1
    rw [mul_comm x, mul_inv_cancel_left]
  · have e : (τ'⁻¹ * τ * ρ ^ (normV v - 1)) π = (τ'⁻¹ * τ) π := by
      rw [AlgEquiv.mul_apply, GlobalTheory.T.inertia_pow_residueCard_sub_one_apply_of_pow_mem E Ω v A hA (ϖ : E) π hπ ρ hρ]
    rw [e]
    exact hval

end
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LatticeDescent

theorem exists_rational_solution {F K V : Type} [Field F] [Field K] [Algebra F K]
    [TopologicalSpace K] [IsTopologicalRing K] (hd : DenseRange (algebraMap F K))
    [AddCommGroup V] [Module F V] {k : ℕ} (s : Fin k → V) (z : V) (a : Fin k → K)
    (U : Set K) (hU : IsOpen U) (ha : ∀ j, a j ∈ U)
    (h : ∀ l : V →ₗ[F] F, algebraMap F K (l z) = ∑ j, algebraMap F K (l (s j)) * a j) :
    ∃ c : Fin k → F, (∀ j, algebraMap F K (c j) ∈ U) ∧ ∑ j, c j • s j = z := by
  classical
  let S : (Fin k → F) →ₗ[F] V := Fintype.linearCombination F s
  have hS : ∀ c, S c = ∑ j, c j • s j := fun c => Fintype.linearCombination_apply F s c
  have hs : ∀ j, s j ∈ LinearMap.range S := fun j => ⟨Pi.single j 1, by
    simp [S]⟩
  have hz : z ∈ LinearMap.range S := by
    by_contra hz
    obtain ⟨f, hf, hm⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
    have h0 : ∀ j, f (s j) = 0 := fun j => by
      have : f (s j) ∈ Submodule.map f (LinearMap.range S) := Submodule.mem_map_of_mem (hs j)
      rwa [hm] at this
    have := h f
    simp only [h0, map_zero, zero_mul, Finset.sum_const_zero] at this
    exact hf ((algebraMap F K).injective (by rw [this, map_zero]))
  obtain ⟨T0, hT0⟩ := S.rangeRestrict.exists_rightInverse_of_surjective S.range_rangeRestrict
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T0
  have hST : ∀ y ∈ LinearMap.range S, S (T y) = y := fun y hy => by
    have e1 : T y = T0 ⟨y, hy⟩ := LinearMap.congr_fun hT ⟨y, hy⟩
    have e2 := congrArg Subtype.val (LinearMap.congr_fun hT0 ⟨y, hy⟩)
    rw [e1]
    exact e2
  let φ : (Fin k → K) → (Fin k → K) := fun x i =>
    x i - ∑ j, algebraMap F K (T (s j) i) * x j + algebraMap F K (T z i)
  have hφ : Continuous φ := by
    refine continuous_pi fun i => ?_
    simp only [φ]
    fun_prop
  have hφa : φ a = a := by
    funext i
    have := h ((LinearMap.proj i).comp T)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply] at this
    simp only [φ, this]
    ring
  have hopen : IsOpen (φ ⁻¹' Set.pi Set.univ fun _ => U) :=
    (isOpen_set_pi Set.finite_univ fun _ _ => hU).preimage hφ
  obtain ⟨b, hb⟩ := (DenseRange.piMap (fun _ : Fin k => hd)).exists_mem_open hopen
    ⟨a, by rw [Set.mem_preimage, hφa]; exact fun j _ => ha j⟩
  refine ⟨b - T (S b) + T z, fun i => ?_, ?_⟩
  · have := hb i trivial
    convert this using 1

    simp only [φ, Pi.map_apply, hS, map_sum, map_smul, Pi.add_apply, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_mul, mul_comm]
  · rw [← hS, map_add (f := _), map_sub, hST _ ⟨b, rfl⟩, hST _ hz, sub_self, zero_add]

theorem functional_of_tmul {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    {n k : ℕ} (s : Fin k → Fin n → E) (z : Fin n → E) (a : Fin k → K)
    (h : ∀ i, z i ⊗ₜ[F] (1 : K) = ∑ j, s j i ⊗ₜ[F] a j) (l : (Fin n → E) →ₗ[F] F) :
    algebraMap F K (l z) = ∑ j, algebraMap F K (l (s j)) * a j := by
  classical
  have hl : ∀ y : Fin n → E, l y = ∑ i, l (Pi.single i (y i)) := fun y => by

    rw [← map_sum, Finset.univ_sum_single]
  have hi : ∀ i, l (Pi.single i (z i)) • (1 : K) = ∑ j, l (Pi.single i (s j i)) • a j := fun i => by
    have := congrArg (fun t => TensorProduct.lid F K
      (LinearMap.rTensor K (l.comp (LinearMap.single F (fun _ : Fin n => E) i)) t)) (h i)

    simpa only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.comp_apply,
    LinearMap.single_apply] using this
  rw [hl z, Algebra.algebraMap_eq_smul_one, Finset.sum_smul]
  simp only [hi]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← hl, Algebra.smul_def]

theorem exists_smul_mem_of_mem_latS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → ∀ z : Fin n → E, (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ latS (F := F) (v.adicCompletion F) (intV E v) M → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • z ∈ M := by
  intro F E _ _ _ _ _ v n M hM z hz
  classical
  have : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.2 hM.fg
  have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := M)
  obtain ⟨a, ha, ea⟩ := (GlobalTheory.LatticeStabLocal.mem_latS_iff_isComb hs _).1 hz
  obtain ⟨c, hc, ec⟩ := exists_rational_solution (HeightOneSpectrum.denseRange_algebraMap F v)
    (fun j => (s j : Fin n → E)) z a (v.adicCompletionIntegers F)
    (Valued.isOpen_valuationSubring _) ha
    (functional_of_tmul (fun j => (s j : Fin n → E)) z a ea)
  have hv : ∀ j, v.valuation F (c j) ≤ 1 := fun j => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c j)]
    exact hc j
  choose m d hmd using fun j => v.exists_primeCompl_mul_eq_of_integer (c j) (hv j)
  refine ⟨∏ j, (d j : 𝓞 F), (prod_mem fun j _ => (d j).2 : _ ∈ v.asIdeal.primeCompl), ?_⟩
  rw [← ec, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  have e : algebraMap (𝓞 F) (𝓞 E) (∏ j, (d j : 𝓞 F)) • c j • (s j : Fin n → E) =
      algebraMap (𝓞 F) (𝓞 E) ((∏ i ∈ Finset.univ.erase j, (d i : 𝓞 F)) * m j) •
        (s j : Fin n → E) := by
    have key : ∀ (x : 𝓞 F) (y : Fin n → E),
        algebraMap (𝓞 F) (𝓞 E) x • y = algebraMap (𝓞 F) F x • y := fun x y => by
      funext i
      simp only [Pi.smul_apply, Algebra.smul_def]
      rfl
    rw [key, key, smul_smul, map_mul, ← hmd j, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j),
      map_mul]
    congr 1
    ring
  rw [e]
  exact M.smul_mem _ (s j).2

end GlobalTheory.LatticeDescent
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem exists_nhds_one_rational_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ U ∈ nhds (1 : HA (AF F) σ J), ∀ g ∈ U, (∃ γ : HFinIn (AF F) σ J, γ • (1 : HA (AF F) σ J) = g) → g = 1 := by
  intro F E _ _ _ _ _ σ M J
  have hd := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  have h1 : ({1} : Set (HFinIn (AF F) σ J)) ∈ nhds (1 : HFinIn (AF F) σ J) :=
    (isOpen_discrete _).mem_nhds rfl
  obtain ⟨U, hU, hsub⟩ := (mem_nhds_subtype _ _ _).1 h1
  refine ⟨U, hU, ?_⟩
  rintro g hg ⟨γ, rfl⟩
  have hγ : γ • (1 : HA (AF F) σ J) = (γ.1 : HR (AF F) σ J) := mul_one (γ.1 : HR (AF F) σ J)
  rw [hγ] at hg ⊢
  have h2 : γ = 1 := hsub hg
  rw [h2]
  rfl

end GlobalTheory.Mem.Vol
end

section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem mainProof : WeylLatticeDuality.Stmt := by
  intro p _ Lt T _ _ e he N nu ν hrow hzero φ
  classical
  have hY : ∀ s, (nu s).colLen 0 ≤ N := fun s => colLen_le_of_rowLen (hzero s N le_rfl)
  have hν : ∀ s, ν (e s) = fun r : Fin N => (nu s).rowLen r := fun s => funext fun r => (hrow s r).symm
  choose ι hι hdec b g c d Nc hNc h1 h2 h3 h4 h5 using fun s => GlobalTheory.T.dual_bases_colProd_alt GlobalTheory.T.columnMinorProducts_fock_reproducing_identity N (nu s) (hY s)
  rw [GlobalTheory.T.integral_minors_iff_basis_alt p Lt N nu hY ι b c d h1 h2 φ]
  have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] =>
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s)))) = fun y =>
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) :=
    funext fun y => GlobalTheory.T.phi_DeX_expand_alt p Lt T e N nu hY ι b g c h1 h3 φ y
  rw [hfun, GlobalTheory.T.comb_mem_iff_alt p Lt T e he N ν ι b g Nc hNc h4 (fun s => by rw [hν s]; exact h5 s)]

end GlobalTheory.WeylLatDualProof
end
end
