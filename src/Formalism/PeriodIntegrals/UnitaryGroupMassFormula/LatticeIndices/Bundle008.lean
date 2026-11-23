module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CardNuGZmod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocIdxLift
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.Automorphisms.Bundle001
public import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LeviEmbeddingBlock32

@[expose] public section

section

noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_natCast_of (g : ℕ) (hg1 : (g : 𝓞 F) ∈ v.asIdeal) (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) :
    Valued.v (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) = WithZero.exp (-1 : ℤ) := by
  have h0 : (g : 𝓞 F) ≠ 0 := fun h => hg2 (by rw [h]; exact zero_mem _)
  have key := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (g : 𝓞 F)
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at key
  have e : (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) =
      algebraMap (𝓞 F) (v.adicCompletion F) (g : 𝓞 F) := by
    rw [map_natCast]
    simp
  rw [e, show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (g : 𝓞 F)) = v.intValuation (g : 𝓞 F) from key]
  have h1 : v.intValuation (g : 𝓞 F) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hg1)
  have h2 : ¬ v.intValuation (g : 𝓞 F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => hg2 ((v.intValuation_le_pow_iff_mem _ 2).1 h)
  have hne : v.intValuation (g : 𝓞 F) ≠ 0 := by
    exact v.intValuation_ne_zero _ h0
  rw [← WithZero.exp_log hne] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

theorem resZ_of (g : ℕ) [hgp : Fact g.Prime] (hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = g)
    (hg1 : (g : 𝓞 F) ∈ v.asIdeal) (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) :
    ∃ π : v.adicCompletionIntegers F →+* ZMod g, Function.Surjective π ∧
      RingHom.ker π = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} := by
  have hv := val_natCast_of v g hg1 hg2
  have hmax := ReciprocityTheory.Aut.maxIdeal_eq_span (F := F) (v := v)
    (π := ((g : ℕ) : v.adicCompletionIntegers F)) hv
  have hc : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = g := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, hcard]
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact hgp.out.ne_zero)
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
  let e := ZMod.ringEquivOfPrime (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) hgp.out
    (by rw [← Nat.card_eq_fintype_card]; exact hc)
  refine ⟨(e.symm : IsLocalRing.ResidueField (v.adicCompletionIntegers F) →+* ZMod g).comp
    (IsLocalRing.residue _), e.symm.surjective.comp IsLocalRing.residue_surjective, ?_⟩
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.coe_toRingHom, EmbeddingLike.map_eq_zero_iff,
    IsLocalRing.residue_eq_zero_iff, hmax]

end MassDataIdxRes

namespace MassDataIdxSteps

open NumberField Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

def ResArith {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : Prop :=
  Nat.card (𝓞 X.B.I.F ⧸ p.1.asIdeal) = gOf p ∧ ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal ∧
    ((gOf p : ℕ) : 𝓞 X.B.I.F) ∉ p.1.asIdeal ^ 2

theorem stResZ_of {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) (h : ResArith X p) : StResZ X p := by
  obtain ⟨hc, h1, h2⟩ := h
  have hg0 : gOf p ≠ 0 := by
    intro h0
    apply h2
    rw [h0, Nat.cast_zero]
    exact zero_mem _
  haveI := p.1.isMaximal
  haveI : Finite (𝓞 X.B.I.F ⧸ p.1.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hg0)
  letI : Fintype (𝓞 X.B.I.F ⧸ p.1.asIdeal) := Fintype.ofFinite _
  letI : Field (𝓞 X.B.I.F ⧸ p.1.asIdeal) := Ideal.Quotient.field _
  obtain ⟨n, hl, hcard⟩ := FiniteField.card (𝓞 X.B.I.F ⧸ p.1.asIdeal) (ringChar (𝓞 X.B.I.F ⧸ p.1.asIdeal))
  rw [← Nat.card_eq_fintype_card, hc] at hcard
  have hlP : ((ringChar (𝓞 X.B.I.F ⧸ p.1.asIdeal) : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hn : (n : ℕ) = 1 := by
    by_contra hne
    have h2n : 2 ≤ (n : ℕ) := by
      have := n.pos
      omega
    apply h2
    rw [hcard, Nat.cast_pow]
    exact Ideal.pow_le_pow_right h2n (Ideal.pow_mem_pow hlP n)
  haveI : Fact (gOf p).Prime := ⟨by rw [hcard, hn, pow_one]; exact hl⟩
  exact MassDataIdxRes.resZ_of p.1 (gOf p) hc h1 h2

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

abbrev FpX : Type := Fv X.B.I.F p.1

abbrev TpX : Type := FpX X p ⊗[X.B.I.F] X.B.I.E

theorem card_idx : Fintype.card (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) = X.B.I.n := by
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

  rw [X.n_eq]
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]
  omega

def idxEquiv : Fin X.B.I.n ≃ Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k :=
  Fintype.equivOfCardEq (by rw [card_idx X, Fintype.card_fin])

def IsSplitEquiv (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : Prop :=
  ∀ t, θ (sigR (FpX X p) X.B.I.cm.sig t) = (θ t).swap

def th1 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : TpX X p →+* FpX X p :=
  (RingHom.fst (FpX X p) (FpX X p)).comp θ.toAlgHom.toRingHom

def th2 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : TpX X p →+* FpX X p :=
  (RingHom.snd (FpX X p) (FpX X p)).comp θ.toAlgHom.toRingHom

def J1 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p) :=
  X.B.I.J.map (fun e => th1 X p θ (inclR (FpX X p) e))

def LatBasis (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P : GL (Fin X.B.I.n) (FpX X p)) : Prop :=
  ∀ x : Fin X.B.I.n → TpX X p, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    (∀ i, (Matrix.mulVec ((P⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))
        fun j => th1 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F) ∧
    (∀ i, (Matrix.mulVec (Matrix.transpose ((P : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *
        Matrix.transpose (J1 X p θ))
        fun j => th2 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F)

def StSplitLat : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧ ∃ P, LatBasis X p θ P

end Loc

def LatCore : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p),
    IsSplitEquiv X p θ → ∀ P, LatBasis X p θ P → StLatGL X p

theorem stRed_of_parts {D : D7} (X : HidaSetting D) (p : TypX X) (hR : StResZ X p) (hS : StSplitLat X p)
    (hC : LatCore) : StRed X p := by
  obtain ⟨θ, hθ, P, hP⟩ := hS
  have hL : StLatGL X p := hC X p θ hθ P hP
  obtain ⟨π, hπ, hker⟩ := hR
  intro K hK
  obtain ⟨ψ, hψ, hψk⟩ := hL K hK
  refine ⟨(Matrix.GeneralLinearGroup.map π).comp ψ, ?_, ?_⟩
  · intro M
    classical
    rcases subsingleton_or_nontrivial (ZMod (gOf p)) with hs | hs
    · refine ⟨1, ?_⟩
      apply Units.ext
      ext i j
      exact @Subsingleton.elim _ hs _ _

    let A : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p) :=
      fun i j => Function.surjInv hπ ((M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j)
    have hA : ∀ i j, π (A i j) = (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j :=
      fun i j => Function.surjInv_eq hπ _
    have hdetM : IsUnit (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det :=
      by
        first
          | exact Matrix.isUnits_det_units M
          | exact (Matrix.isUnit_iff_isUnit_det (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)))).mp M.isUnit
    have hmap : π A.det = (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      exact hA i j
    have hle : RingHom.ker π ≤ IsLocalRing.maximalIdeal (Op X p) :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
    have hdet : IsUnit A.det := by
      by_contra hnu
      have hm : A.det ∈ IsLocalRing.maximalIdeal (Op X p) :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
      obtain ⟨v, hv⟩ := IsUnit.exists_right_inv (show IsUnit (π A.det) by rw [hmap]; exact hdetM)
      obtain ⟨b, rfl⟩ := hπ v
      have h1 : A.det * b - 1 ∈ RingHom.ker π := by
        rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hv, map_one, sub_self]
      have h2 : A.det * b ∈ IsLocalRing.maximalIdeal (Op X p) := by
        first
          | exact Ideal.mul_mem_right _ _ hm
          | exact Ideal.mul_mem_right _ hm
      have h3 : (1 : Op X p) ∈ IsLocalRing.maximalIdeal (Op X p) := by
        have h4 := Ideal.sub_mem _ h2 (hle h1)
        rwa [sub_sub_cancel] at h4
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h3)) isUnit_one
    obtain ⟨x, hx⟩ := hψ ((Matrix.isUnit_iff_isUnit_det A).mpr hdet).unit
    refine ⟨x, ?_⟩
    apply Units.ext
    ext i j
    rw [MonoidHom.comp_apply, hx]
    exact hA i j
  · intro x

    have key : ∀ i j, π (((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) - 1) i j) =
        ((Matrix.GeneralLinearGroup.map π (ψ x) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) - 1) i j := by
      intro i j
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp only [map_one, map_zero] <;> rfl
    rw [← hψk x, ← hker]
    constructor
    · intro h i j
      rw [RingHom.mem_ker, key]
      have h' : (Matrix.GeneralLinearGroup.map π (ψ x) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) = 1 := by
        rw [MonoidHom.comp_apply] at h
        rw [h]
        rfl
      rw [h', sub_self]
      rfl
    · intro h
      apply Units.ext
      ext i j
      have h0 := h i j
      rw [RingHom.mem_ker, key, Matrix.sub_apply, sub_eq_zero] at h0
      exact h0

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem imA_vecV_smul (p : TypX X) (t : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (t • w) = PI.FinKW.psiV X.B.I p.1 t • PI.FinKW.vecV X.B.I p.1 w := by
  funext i; simp [PI.FinKW.vecV, map_mul]

theorem imA_vecV_add (p : TypX X) (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (a + b) = PI.FinKW.vecV X.B.I p.1 a + PI.FinKW.vecV X.B.I p.1 b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_zero (p : TypX X) :
    PI.FinKW.vecV X.B.I p.1 (0 : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) = 0 := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_OEp_mul (p : TypX X) {s t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (hs : s ∈ OEp X p)
    (ht : t ∈ OEp X p) : s * t ∈ OEp X p := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb', rfl⟩ := ht
  exact ⟨a * b, Subring.mul_mem _ ha hb', map_mul _ _ _⟩

theorem smul_mem_spanAt (p : TypX X) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {w : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hw : w ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s}) :
    t • w ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s} := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t', ht', s, hs, rfl⟩ := hx
    exact Submodule.subset_span ⟨t * t', imA_OEp_mul X p ht ht', s, hs, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem imA_inMod_loc (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (h : InMod X.B.I m S w) :
    InModP X p m (PI.FinKW.vecV X.B.I p.1 '' S) (PI.FinKW.vecV X.B.I p.1 w) := by
  obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp h
  clear h
  rw [imA_vecV_add]
  refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, rfl⟩
  · induction ha using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span ⟨1, ⟨1, one_mem _, map_one _⟩, _, ⟨x, hx, rfl⟩, (one_smul _ _).symm⟩
    | zero => rw [imA_vecV_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [imA_vecV_add]; exact add_mem hx hy
    | smul c x _ hx =>
      show PI.FinKW.vecV X.B.I p.1 ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x) ∈ _
      rw [imA_vecV_smul]
      exact smul_mem_spanAt X p _ ⟨c, c.2, rfl⟩ hx
  · have key : ∃ x ∈ X.B.I.Lf, b = (m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x := by
      induction hb' using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
      | add y z _ _ hy hz =>
        obtain ⟨y', hy', rfl⟩ := hy
        obtain ⟨z', hz', rfl⟩ := hz
        exact ⟨y' + z', add_mem hy' hz', (smul_add _ _ _).symm⟩
      | smul c y _ hy =>
        obtain ⟨y', hy', rfl⟩ := hy
        refine ⟨c • y', Submodule.smul_mem _ c hy', ?_⟩
        show (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • _ = _ • ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • y')
        rw [smul_smul, smul_smul, mul_comm]
    obtain ⟨x, hx, rfl⟩ := key
    rw [imA_vecV_smul, map_natCast, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (p.1.adicCompletionIntegers X.B.I.F)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I x hx p.1)

theorem imA_vecV_mulVec (p : TypX X) (x : X.B.I.Gf)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 ((X.B.I.fmat x - 1) *ᵥ w) =
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (piV X.B.I p.1 (tf X.B.I hb x)) :
        GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 w := by
  rw [LocIdxLift_vecV_mulVec, Matrix.map_sub _ (map_sub _), LocIdxLift_psiV_fmat X.B.I hb,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem imA_kpp_sub (p : TypX X) : KppX X hb p ⊆ {y | y ∈ KvX X p ∧ LocCong X p y} := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hx' : x ∈ X.B.I.Kset ∧ K2cong X.B.I X.B.g X.e0 X.z0 X.bw x := hx
  obtain ⟨hxK, h1, h2, h3⟩ := hx'
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hK := (Bridge_mem_Kf_iff X.B.I hb x).mpr hxK
    rw [Kf, Subgroup.mem_iInf] at hK
    exact hK p.1
  · intro a
    have h := imA_inMod_loc X p _ _ _ (h1 a)
    rw [imA_vecV_mulVec X hb, Set.image_image] at h
    exact h
  · have h := imA_inMod_loc X p _ _ _ h2
    rw [imA_vecV_mulVec X hb, ← Set.range_comp] at h
    exact h
  · intro i
    have h := imA_inMod_loc X p _ _ _ (h3 i)
    rw [imA_vecV_mulVec X hb, Set.image_union, Set.image_image, ← Set.range_comp] at h
    exact h

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 MassDataIdxRed
open Formalism.DoubleCosetMeasures (IsUpUni)

variable {A B : Type} [CommRing A] [CommRing B] {r k : ℕ}

theorem mem_sG_iff_map (f : A →+* B) (hf : Function.Injective f) (g : GL (Idx r k) A) :
    g ∈ sG A r k ↔ glRed f g ∈ sG B r k := by
  change Par _ (g : Matrix (Idx r k) (Idx r k) A) ↔ Par _ ((glRed f g : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)
  rw [glRed_coe]
  set x : Matrix (Idx r k) (Idx r k) A := (g : Matrix (Idx r k) (Idx r k) A) with hx
  have z0 : ∀ {a : A}, f a = 0 → a = 0 := fun h => hf (by rw [h, map_zero])
  have z1 : ∀ {a : A}, f a = 1 → a = 1 := fun h => hf (by rw [h, map_one])
  constructor
  · intro h
    refine MassDataIdxStImB.par_map f (map_zero f) (map_one f) (fun h hh => ?_) h
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hh.map f
  · rintro ⟨h11, h33, h21, h31, h32, h, _, h22⟩
    have u11 : IsUpUni (b11 x) :=
      ⟨fun i j hij => z0 (h11.1 hij), fun a => z1 (h11.2 a)⟩
    have u33 : IsUpUni (b33 x) :=
      ⟨fun i j hij => z0 (h33.1 hij), fun a => z1 (h33.2 a)⟩
    have v21 : b21 x = 0 := by ext i j; exact z0 (congrFun (congrFun h21 i) j)
    have v31 : b31 x = 0 := by ext i j; exact z0 (congrFun (congrFun h31 i) j)
    have v32 : b32 x = 0 := by ext i j; exact z0 (congrFun (congrFun h32 i) j)
    have v22 : b22 x = midEmb (Matrix.of fun i j => x (wI i) (wI j)) := by
      ext i j
      have e := congrFun (congrFun h22 i) j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z1 (by simpa [b22, midEmb] using e)
    refine ⟨u11, u33, v21, v31, v32, Matrix.of fun i j => x (wI i) (wI j), ?_, v22⟩
    show IsUnit (Matrix.det _)
    rw [← det_shape u11 u33 v21 v31 v32 _ v22, hx]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

end MassDataIdxStIm
end
end
