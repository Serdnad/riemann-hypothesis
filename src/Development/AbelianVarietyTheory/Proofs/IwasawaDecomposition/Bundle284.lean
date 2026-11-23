module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle006
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle007
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle272
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle273
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lamN_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (kap : ℝ)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) {p} (hp : R.EEp3 p ≠ ⊥) (t j) :
    (R.updS kap (zeroLam R F c)).lamN t j p = R.lamN t j p := by
  unfold RealDat3.lamN
  split_ifs with h
  · exact scalarsZeroPartConvention_fixedPlace R F c ((hZ p hp _).1)
  · rfl

theorem isKap_congr {N Tup Sig : Type} [AddCommGroup N] [Module ℂ N] {m : ℕ} {dnup : Tup → N →ₗ[ℂ] N} {partE : Sig → Submodule ℂ N}
    {lam lam' : Tup → ℕ → Sig → ℝ} {κ : ℝ} (h : Lift.IsKap m dnup partE lam κ)
    (hl : ∀ μ j σ, partE σ ≠ ⊥ → lam' μ j σ = lam μ j σ) : Lift.IsKap m dnup partE lam' κ := by
  intro μ σ x hx
  by_cases hσ : partE σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp only [map_zero, smul_zero]
  · rw [Finset.prod_congr rfl fun j _ => hl μ j σ hσ]
    exact h μ σ x hx

theorem isLamP_congr {A Amb Sig : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb] {thW : A →ₗ[ℂ] Amb}
    {adj : Amb →ₗ[ℂ] A} {part : Sig → Submodule ℂ Amb} {lam lam' : Sig → ℝ} (h : Lift.IsLamP thW adj part lam)
    (hl : ∀ σ, part σ ≠ ⊥ → lam' σ = lam σ) : Lift.IsLamP thW adj part lam' := by
  intro σ x hx
  by_cases hσ : part σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp only [map_zero, smul_zero]
  · rw [hl σ hσ]
    exact h σ x hx



theorem thmB_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hB : R.PThmB) : (R.updS R.kap (zeroLam R F c)).PThmB := by
  let S := R.updS R.kap (zeroLam R F c)
  change Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 S.lamN R.kap
  exact isKap_congr (lam := R.lamN) hB fun μ j _ hσ => lamN_zeroLam R F c R.kap hZ hσ μ j



theorem thmA_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hA : R.PThmA) : (R.updS R.kap (zeroLam R F c)).PThmA := by
  intro i t
  change Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (R.Wp3 i)
    (fun p => zeroLam R F c i t p A3.A.v0)
  exact isLamP_congr (lam := fun p => R.lam3 i t p A3.A.v0) (hA i t)
    fun p hp => scalarsZeroPartConvention_fixedPlace R F c (i := i) (t := t) (p := p) hp



private theorem toCx3_updS_eq_reScal (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam) :
    (R.updS kap lam).toCx3 F = reScal (R.toCx3 F) (fun _ => kap) lam := by
  rfl

theorem galD_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hG : (R.toCx3 F).GalD F.cr false) : ((R.updS R.kap (zeroLam R F c)).toCx3 F).GalD F.cr false := by
  rw [toCx3_updS_eq_reScal]
  exact cx_galD_scal (R.toCx3 F) F.cr (fun _ => R.kap) (zeroLam R F c)
    (fun j p v hv hp => zeroLam_off R F c (i := j) (t := A3.A.μ0) (p := p) (v := v) hv hp) hG

theorem partAt_updS_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (i p v) :
    (R.updS kap lam).PartAt (reFace F Dc Sp Zsc) i p v ↔ R.PartAt F i p v :=
  (RealDat3.partAt_updS kap lam i p v).trans Iff.rfl

private theorem toCx3_reFace_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    R.toCx3 (reFace F Dc Sp Zsc) = R.toCx3 F := by
  rfl

private theorem simX_reFace_iff (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (X : CxData A3.fam3.amb3) (i p v l) :
    SimX (reFace F Dc Sp Zsc).cr X false i p v l ↔ SimX F.cr X false i p v l := by
  dsimp only [SimX, CxData.liftMat, CxData.liftMatC, CxData.tC,
    Face3.cr, Face3.fc, reFace, faceOf3, crdOf3, lv]
  rfl

theorem scal_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hs : R.IsScal F) :
    (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)).IsScal (reFace F Dc Sp Zsc) := by
  let c := (Zsc (R.toCx3 F).zs).l6m
  let lam := zeroLam R F c
  let S := R.updS R.kap lam
  let F' := reFace F Dc Sp Zsc
  change S.IsScal F'
  have hpart (i p v) : S.PartAt F' i p v ↔ R.PartAt F i p v :=
    partAt_updS_reFace R F R.kap lam Dc Sp Zsc i p v
  have hlam (t j p) (hp : R.EEp3 p ≠ ⊥) : S.lamN t j p = R.lamN t j p :=
    lamN_zeroLam R F c R.kap hZ hp t j
  have hface : S.toCx3 F' = S.toCx3 F := toCx3_reFace_eq S F Dc Sp Zsc
  have hzs : (S.toCx3 F').zs = (R.toCx3 F).zs :=
    (congrArg CxData.zs hface).trans (RealDat3.zs_updS (R := R) (F := F) R.kap lam)
  have hscale : (F'.Zsc (S.toCx3 F').zs).l6m = c := congrArg (fun zs => (Zsc zs).l6m) hzs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i t p l hp hl
    change lam i t p A3.A.v0 = l
    exact (scalarsZeroPartConvention_fixedPlace R F c (i := i) (t := t) (p := p) hp).trans
      (hs.lam0 i t p l hp hl)
  · intro κ hk hne
    have hk' : Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 S.lamN κ := hk
    refine hs.kap κ (isKap_congr (lam' := R.lamN) hk' fun t j p hp => (hlam t j p hp).symm) ?_
    obtain ⟨t, p, hp, hne⟩ := hne
    change R.EEp3 p ≠ ⊥ at hp
    have hprod : (∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p) =
        ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p :=
      Finset.prod_congr rfl fun j _ => hlam t j p hp
    exact ⟨t, p, hp, hprod ▸ hne⟩
  · intro i p v l hv hp he
    change lam i A3.A.μ0 p v = l
    have hp' := (hpart i p v).mp hp
    have hsim : SimX F'.cr (S.toCx3 F') false i p v l := he
    rw [hface] at hsim
    have hsim' : SimX F.cr (R.toCx3 F) false i p v l :=
      (RealDat3.sim_updS (R := R) (F := F) R.kap lam i p v l).mp
        ((simX_reFace_iff F Dc Sp Zsc (S.toCx3 F) i p v l).mp hsim)
    exact (zeroLam_off R F c (i := i) (t := A3.A.μ0) (p := p) (v := v) hv hp').trans
      (hs.off i p v l hv hp' hsim')
  · intro i t p hp
    change lam i t p A3.A.v0 = Real.exp ((F'.Zsc (S.toCx3 F').zs).l6m i)
    rw [hscale]
    exact zeroLam_of_zero R F c (i := i) (t := t) (p := p) (v := A3.A.v0) (Or.inl ⟨rfl, hp⟩)
  · intro i p v hv hp
    change lam i A3.A.μ0 p v = Real.exp ((F'.Zsc (S.toCx3 F').zs).l6m i)
    rw [hscale]
    exact zeroLam_of_zero R F c (i := i) (t := A3.A.μ0) (p := p) (v := v)
      (Or.inr ⟨hv, fun h => hp ((hpart i p v).mpr h)⟩)
  · intro i t p v hv
    change zeroLam R F c i t p v = zeroLam R F c i A3.A.μ0 p v
    unfold zeroLam
    split_ifs
    · rfl
    · exact hs.tup i t p v hv

end GlobalTheory.Mem.R3

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TiePlace

theorem iota_sigma_mem_range {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (S : HidaSetting p n' W Qq O Kf ι σ j w) (s : ℕ) (y : Qq) :
    ι ((σ ^ s) y) ∈ Set.range (algebraMap O Kf) ↔ y ∈ Set.range (algebraMap W Qq) := by
  haveI := S.frac_alt
  haveI := S.frac_O

  have h1 : ∀ z : Qq, z ∈ Set.range (algebraMap W Qq) → σ z ∈ Set.range (algebraMap W Qq) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t', ht'⟩ := S.frob t
    exact ⟨_, ht'.symm⟩
  have hk : ∀ (k : ℕ) (z : Qq), z ∈ Set.range (algebraMap W Qq) → (σ ^ k) z ∈ Set.range (algebraMap W Qq) := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
      intro z hz
      rw [pow_succ]
      exact ih _ (h1 z hz)
  have hs : ∀ z : Qq, (σ ^ s) z ∈ Set.range (algebraMap W Qq) ↔ z ∈ Set.range (algebraMap W Qq) := by
    intro z
    refine ⟨fun h => ?_, hk s z⟩
    have hn : 1 ≤ n' := le_trans (by norm_num) S.two_le
    have e : (σ ^ (s * (n' - 1))) ((σ ^ s) z) = z := by
      have em : (σ ^ (s * (n' - 1))) ((σ ^ s) z) = (σ ^ (s * (n' - 1)) * σ ^ s) z := rfl
      rw [em, ← pow_add]
      have : s * (n' - 1) + s = n' * s := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [this, pow_mul, S.period, one_pow]
      rfl
    rw [← e]
    exact hk _ _ h

  have hj : Function.Injective j := by
    intro a b h
    apply IsFractionRing.injective W Qq
    apply ι.injective
    rw [S.ι_comp, S.ι_comp, h]
  have hnu : ¬ IsUnit (p : O) := by
    letI := j.toAlgebra
    haveI : Module.Finite W O := S.finite
    haveI : FaithfulSMul W O := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
    intro h
    exact S.p_unif.not_isUnit ((isUnit_map_iff (algebraMap W O) _).1 (by simpa using h))
  have hι : ∀ z : Qq, ι z ∈ Set.range (algebraMap O Kf) ↔ z ∈ Set.range (algebraMap W Qq) := by
    intro z
    refine ⟨fun h => ?_, ?_⟩
    · by_contra hz
      obtain ⟨o, ho⟩ := h
      have hz0 : z ≠ 0 := fun h0 => hz ⟨0, by rw [h0, map_zero]⟩
      obtain ⟨t, ht⟩ := (ValuationRing.isInteger_or_isInteger W z).resolve_left hz
      have htu : ¬ IsUnit t := by
        rintro ⟨u, rfl⟩
        apply hz
        refine ⟨(u⁻¹ : Wˣ), ?_⟩
        rw [← inv_inv z, ← ht]
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, Units.inv_mul, map_one]
      have htm : t ∈ Ideal.span {(p : W)} := by
        rw [← S.p_unif.maximalIdeal_eq]
        exact htu
      obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 htm
      have e1 : algebraMap O Kf (o * j (t' * p)) = 1 := by
        rw [map_mul, ho, ← S.ι_comp, ht, ← map_mul, mul_inv_cancel₀ hz0, map_one]
      have e2 : o * j (t' * p) = 1 := by
        apply IsFractionRing.injective O Kf
        rw [e1, map_one]
      apply hnu
      have : IsUnit (j (t' * p)) := IsUnit.of_mul_eq_one o (by rw [mul_comm]; exact e2)
      rw [map_mul, map_natCast] at this
      exact isUnit_of_mul_isUnit_right this
    · rintro ⟨t, rfl⟩
      exact ⟨j t, (S.ι_comp t).symm⟩
  rw [hι, hs]

theorem val_pos_iff {K : Type} [Field K] (val : AddValuation K (WithTop ℤ)) (z : K) :
    (0 : WithTop ℤ) < val z ↔ z = 0 ∨ ¬ (0 : WithTop ℤ) ≤ val z⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, false_or, AddValuation.map_inv, not_le]
    obtain ⟨n, hn⟩ : ∃ n : ℤ, val z = n := WithTop.ne_top_iff_exists.1 (fun h => hz ((AddValuation.top_iff val).1 h)) |>.imp fun _ h => h.symm
    rw [hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    norm_cast
    omega

theorem mem_asIdeal_iff_inv {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (x : R) :
    x ∈ v.asIdeal ↔ x = 0 ∨ (algebraMap K (v.adicCompletion K) (algebraMap R K x))⁻¹ ∉ v.adicCompletionIntegers K := by
  by_cases hx : x = 0
  · subst hx
    simp
  · simp only [hx, false_or, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, not_le]
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
    have h1 : (algebraMap K (v.adicCompletion K) (algebraMap R K x)) = ((algebraMap R K x : K) : v.adicCompletion K) := rfl
    rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have h0 : v.valuation K (algebraMap R K x) ≠ 0 := by
      simpa using hx
    rw [one_lt_inv₀ (zero_lt_iff.2 h0)]

theorem inv_int_iff {p : ℕ} {G : GAtP p} (v : Fin G.P.nV) (s : ℕ) {LL : Type} [Field LL]
    (val : AddValuation LL (WithTop ℤ)) (emb : LL →+* G.Kf)
    (hint : ∀ z, (0 : WithTop ℤ) ≤ val z ↔ emb z ∈ Set.range (algebraMap G.O G.Kf)) (z : LL) (y : G.P.Qq v)
    (hk : emb z = G.P.ι v ((G.P.σ v ^ s) y)) :
    y⁻¹ ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔ (0 : WithTop ℤ) ≤ val z⁻¹ := by
  rw [hint, map_inv₀, hk, ← map_inv₀, ← map_inv₀]
  exact (iota_sigma_mem_range (G.P.setting v) s y⁻¹).symm

section Comparison₂

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

theorem tie_mem_iff {L : ColLevel R F E sp gp C A clsLat} (t : Formalism.L2.Herm.GLevTie L G) (v : Fin G.P.nV) (x : 𝓞 F) :
    x ∈ (t.pl v).1.asIdeal ↔ x = 0 ∨
      ((t.eQ v _ rfl).symm ((t.spl _ (t.pl v).2 (inclE (F := F) ((t.pl v).1.adicCompletion F) (algebraMap F E (x : F)))).1))⁻¹ ∉
        Set.range (algebraMap (G.P.W v) (G.P.Qq v)) := by
  rw [t.spl_F, mem_asIdeal_iff_inv (K := F), t.completion_integers_iff v _ rfl, map_inv₀, RingEquiv.apply_symm_apply]

end Comparison₂

theorem int_map_eq_zero_iff {F E L : Type} [Field F] [Field E] [Field L] (g : F →+* E) (f : E →+* L)
    (x : 𝓞 F) : f (g (x : F)) = 0 ↔ x = 0 := by
  rw [map_eq_zero_iff f f.injective, map_eq_zero_iff g g.injective]
  exact RingOfIntegers.coe_eq_zero_iff



theorem place_of_tie : ∀ (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w)))
    (x : 𝓞 D.host.F),
    x ∈ (((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  intro D sc Ce Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x
  have hpos := pos_C D sc Ce Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s
    (algebraMap D.host.F D.host.E (x : D.host.F))
  have hsig : sigD (recC D sc Ce Lc I ψ hd) (algebraMap D.host.F D.host.E (x : D.host.F)) =
      algebraMap D.host.F D.host.E (x : D.host.F) := AlgHom.commutes _ _
  have key : (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
      (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) =
      ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v
        ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((Cmp.locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v (algebraMap D.host.F D.host.E (x : D.host.F)))) := by
    have e : tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F)) = Cmp.tEL (recC D sc Ce Lc I ψ hd)
          ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩) (if Even s.val then algebraMap D.host.F D.host.E (x : D.host.F)
            else sigD (recC D sc Ce Lc I ψ hd) (algebraMap D.host.F D.host.E (x : D.host.F))) := by
      by_cases he : Even s.val
      · simp only [he, if_true, ite_true, ↓reduceIte]; rfl
      · simp only [he, if_false, ite_false, ↓reduceIte, hsig]; rfl
    rw [e]
    exact hpos
  refine (tie_mem_iff ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg) v x).trans ?_
  have hz : x = 0 ↔ tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
      (algebraMap D.host.F D.host.E (x : D.host.F)) = 0 := by
    exact (int_map_eq_zero_iff (algebraMap D.host.F D.host.E) (Cmp.tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)) x).symm
  refine Iff.trans ?_ (val_pos_iff (D.what₂.places.val w) (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
      (algebraMap D.host.F D.host.E (x : D.host.F)))).symm
  exact or_congr hz (not_congr (inv_int_iff v s.val (D.what₂.places.val w) ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg)
    ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW_int u w hg) _ _ key))

end GlobalTheory.TiePlace
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_level_at_each_index : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ i : Fin D.R.m, ∃ lev, LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev := by
  first | exact @GlobalTheory.LevelAction.exists_levIs | exact GlobalTheory.LevelAction.exists_levIs | (intros; apply GlobalTheory.LevelAction.exists_levIs <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainModels

theorem models_seed : GlobalTheory.Published.DiscreteSeriesExists → ∀ D : D7, HostHyp D → Formalism.IndefR.Seed.ModY D ∧
    ∀ (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x : D.host.E, ∃ y : Ks, algebraMap Ks D.what₂.LL y = D.embE x) →
      ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ),
        Formalism.IndefR.Seed.ModWAt D.what₂.embLL MW ∧ GlobalTheory.RealGeo.FrameKs Ks MW := by
  intro h D _
  exact exists_models h D

end GlobalTheory.ChainModels
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

variable {D : D7}

def FixRed (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd)
    (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) : Prop :=
  ∀ kv : (Σ k : Fin 2, D.nd.PlG k), IsRedBasis X (D.naut.plGw kv.1 kv.2) (b kv) ∧ ∀ k ∈ X.B.I.Kset, ∀ i,
    X.B.I.fmat k *ᵥ incl X.B.I (b kv i) -
      ∑ j, (((((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) •
        incl X.B.I (b kv j) ∈ wLf X (D.naut.plGw kv.1 kv.2)

theorem goodAt_of_fixRed {X : HidaSetting D} {red : X.B.I.Gf → G0g D.nd}
    {b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E} (hf : FixRed X red b) :
    ∀ k ∈ X.B.I.Kset, GoodAt X k (red k) :=
  fun k hk kv => ⟨b kv, (hf kv).1, (hf kv).2 k hk⟩

end GlobalTheory.Mem.SRe

end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.tameHeckeCharacter_value_via_power_generator : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∉ S → χ.UnrAt w) → (∀ w ∈ S, χ.TameAt w) → ∀ (v : HeightOneSpectrum (𝓞 L)), v ∉ S → ∀ (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → (∀ w ∈ S, w.valuation L ((k : L) - 1) < 1) → χ.inf k * χ.val v ^ h = 1 := by
  first | exact @GlobalTheory.Mem.ValPow.inf_mul_val_pow | exact GlobalTheory.Mem.ValPow.inf_mul_val_pow | (intros; apply GlobalTheory.Mem.ValPow.inf_mul_val_pow <;> assumption)
end
