module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle110
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle225
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section
open IsNilpotent

namespace GlobalTheory.AboveL.ResWD

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
  {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem exists_tval_resI (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v') (hl' : ((l : ℕ) : 𝓞 L) ∉ v'.asIdeal)
    {t : Ine (F := K) A →* Multiplicative ℤ_[l]} {t' : Ine (F := L) A →* Multiplicative ℤ_[l]}
    (ht : IsTameChar t) (ht' : IsTameChar t') :
    ∃ c : Qbar l, c ≠ 0 ∧ ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ := by
  obtain ⟨c, hc⟩ := GlobalTheory.TameCharUnique.exists_eq_mul L Ω A v' h' l hl' (t.comp ResEx.resI) t'
    (ht.1.comp ResEx.continuous_resI) ht'.1 ht'.2
  refine ⟨algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]), ?_, fun σ => ?_⟩
  swap
  · have := hc σ
    simp only [MonoidHom.comp_apply] at this
    simp [tval, this]
  intro h0
  rw [map_eq_zero, PadicInt.coe_eq_zero] at h0
  have hc0 : ∀ σ, (t (ResEx.resI (K := K) σ)).toAdd = 0 := fun σ => by
    have := hc σ
    simpa [h0] using this
  obtain ⟨σ, hσ⟩ := ht.2 (Multiplicative.ofAdd 1)
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let f : ℕ → (L →ₐ[K] Ω) := fun n => (((σ : _root_.Formalism.ConjugateSelfDual.G K Ω) ^ n : _root_.Formalism.ConjugateSelfDual.G K Ω) : Ω →ₐ[K] Ω).comp (IsScalarTower.toAlgHom K L Ω)
  have main : ∀ i j : ℕ, i < j → f i = f j → False := fun i j hij e => by
    set k := j - i with hk
    have hk0 : 0 < k := Nat.sub_pos_of_lt hij
    have hfix : ∀ x : L, ((σ : _root_.Formalism.ConjugateSelfDual.G K Ω) ^ k).toRingEquiv (algebraMap L Ω x) = algebraMap L Ω x := fun x => by
      have e1 := congrArg (fun g : L →ₐ[K] Ω => g x) e
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_algHom] at e1
      have e2 : (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) ^ j = (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) ^ i * (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) ^ k := by
        rw [← pow_add, hk, Nat.add_sub_cancel' hij.le]
      rw [e2, AlgEquiv.mul_apply] at e1
      exact (((σ : _root_.Formalism.ConjugateSelfDual.G K Ω) ^ i).injective e1).symm
    let σ'' : _root_.Formalism.ConjugateSelfDual.G L Ω := AlgEquiv.ofRingEquiv (f := ((σ : _root_.Formalism.ConjugateSelfDual.G K Ω) ^ k).toRingEquiv) hfix
    have hres : AlgEquiv.restrictScalarsHom K σ'' = (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) ^ k := AlgEquiv.ext fun _ => rfl
    have hmem : σ'' ∈ Ine (F := L) A := by
      show AlgEquiv.restrictScalarsHom K σ'' ∈ Ine (F := K) A
      rw [hres]
      exact pow_mem σ.2 k
    have e3 : ResEx.resI (K := K) ⟨σ'', hmem⟩ = σ ^ k := Subtype.ext (by rw [SubgroupClass.coe_pow, ← hres]; rfl)
    have := hc0 ⟨σ'', hmem⟩
    rw [e3, map_pow, hσ, ← ofAdd_nsmul, toAdd_ofAdd, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at this
    omega
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact main i j hlt e
  · exact main j i hlt e.symm

theorem isMonodromy_res {t : Ine (F := K) A →* Multiplicative ℤ_[l]}
    {t' : Ine (F := L) A →* Multiplicative ℤ_[l]} {r : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {c : Qbar l} (hN : IsMonodromy t r N)
    (hc : ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ) :
    IsMonodromy t' (resTo L r) (c • N) := by
  obtain ⟨h1, U, hU, H⟩ := hN
  refine ⟨h1.smul c, U.comap ResEx.resI, hU.preimage ResEx.continuous_resI, fun σ hσ => ?_⟩
  have := H _ hσ
  rw [smul_smul, mul_comm, ← hc]
  exact this

theorem exists_conj (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v') (hl : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal)
    {t : Ine (F := K) A →* Multiplicative ℤ_[l]}
    {t' : Ine (F := L) A →* Multiplicative ℤ_[l]} {r : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {c : Qbar l} (ht : IsTameChar t) (hN : IsMonodromy t r N)
    (hc : ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ) :
    ∃ β : Qbar l, ∀ g : Weil h', exp (β • N) * wdMat t' (deg_frob (h := h')) (resTo L r) (c • N) g =
      wdMat t (deg_frob (h := h)) r N (ResEx.resW h h' g) * exp (β • N) := by
  have hq0 : ((normV v : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV v).ne_bot
  have hf : deg (ResEx.resW h h' (frob h')) ≠ 0 := by
    intro h0
    have h1 : ((frob h' : Weil h') : _root_.Formalism.ConjugateSelfDual.G L Ω) ∈ Ine (F := L) A :=
      (deg_eq_zero_iff (σ := ResEx.resW h h' (frob h'))).1 h0
    have h2 := (deg_eq_zero_iff (σ := frob h')).2 h1
    rw [deg_frob] at h2
    exact one_ne_zero h2
  have hq1 : 1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, inv_eq_one]
    intro h1
    have h3 : (((normV v : ℕ) : ℚ) ^ deg (ResEx.resW h h' (frob h')) : ℚ) = 1 := by
      rw [← Rat.cast_inj (α := Qbar l)]; push_cast; exact h1
    exact hf ((zpow_eq_one_iff_right₀ (Nat.cast_nonneg _)
      (Nat.cast_ne_one.mpr (one_lt_normV v).ne')).mp h3)
  have key : ∀ m : ℤ,
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ m)) *
        (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹) =
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) *
        (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h') ^ m))⁻¹) := fun m => by
    have h1 := ht.tval_inePart_mul hl (deg_frob (h := h)) (ResEx.resW h h' (frob h'))
      (ResEx.resW h h' (frob h') ^ m)
    have h2 := ht.tval_inePart_mul hl (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ m)
      (ResEx.resW h h' (frob h'))
    rw [(Commute.self_zpow (ResEx.resW h h' (frob h')) m).eq] at h1
    linear_combination h2 - h1
  refine ⟨tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) /
    (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹), fun g => ?_⟩
  have hg : g = frob h' ^ deg g * ineIncl h' (inePart (deg_frob (h := h')) g) := by
    rw [ineIncl_inePart, mul_inv_cancel_left]
  have hRg : ResEx.resW h h' g =
      ResEx.resW h h' (frob h') ^ deg g * ineIncl h (ResEx.resI (inePart (deg_frob (h := h')) g)) := by
    conv_lhs => rw [hg]
    rw [map_mul, map_zpow, ResEx.resW_ineIncl]
  have hT : tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' g)) =
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ deg g)) +
        tval t (ResEx.resI (inePart (deg_frob (h := h')) g)) := by
    rw [hRg, ht.tval_inePart_mul hl, deg_ineIncl, zpow_zero, inv_one, one_mul, inePart_ineIncl]
  have hd : deg (ResEx.resW h h' g) = deg (ResEx.resW h h' (frob h') ^ deg g) := by
    rw [hRg, deg_mul, deg_ineIncl, add_zero]
  have hs := key (deg g)
  have hqd : ((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' g) ≠ 0 := zpow_ne_zero _ hq0
  rw [wdMat, wdMat, hT]
  have e1 : (-tval t' (inePart (deg_frob (h := h')) g)) • (c • N) =
      (-tval t (ResEx.resI (inePart (deg_frob (h := h')) g))) • N := by
    rw [smul_smul, hc]
    congr 1
    ring
  have e2 : ((resTo L r g : Matrix (Fin a) (Fin a) (Qbar l))) = r (ResEx.resW h h' g) := rfl
  rw [e1, e2]
  set β := tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) /
    (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹) with hβ
  have h2 := hN.mul_exp hl ht (ResEx.resW h h' g) ((((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' g))⁻¹ * β)
  rw [mul_inv_cancel_left₀ hqd] at h2
  rw [← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1, ← exp_add_smul hN.1]
  congr 3
  have hsm : tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ deg g)) =
      β * (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h') ^ deg g))⁻¹) := by
    rw [hβ, div_mul_eq_mul_div, eq_div_iff hq1]
    linear_combination hs
  rw [hd]
  linear_combination hsm

end GlobalTheory.AboveL.ResWD

namespace GlobalTheory.AboveL

theorem wdOf_restricts : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v') (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Qbar l)) (hl : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal) (hl' : ((l : ℕ) : 𝓞 L) ∉ v'.asIdeal), Continuous r → Restricts (wdOf h hl ι r) (wdOf h' hl' ι (resTo L r)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ ι a r hl hl' hr
  have hr' : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp hr
  have ht := isTameChar_tameL h hl
  have ht' := isTameChar_tameL h' hl'
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hr'
  obtain ⟨c, hc0, hc⟩ := ResWD.exists_tval_resI h' hl' ht ht'
  have hN' := ResWD.isMonodromy_res hN hc
  obtain ⟨β, hβ⟩ := ResWD.exists_conj h h' hl ht hN hc
  obtain ⟨aK, haK⟩ := hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  have ex : wdOf h hl ι r = WD.mk aK := IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N, aK, hN, haK, rfl⟩
  have hb : IsFrobSS (fun g => toEndC ι (wdMat (tameL h hl) (deg_frob (h := h)) r N (ResEx.resW h h' g)))
      (toEndC ι N) (ResEx.resRep h h' aK) := ⟨haK.1, fun g => haK.2 _⟩
  obtain ⟨aL2, haL2⟩ := hN'.exists_isFrobSS hl' ht' (deg_frob (h := h')) ι
  have hcomm : ∀ g, hN'.rep hl' ht' (deg_frob (h := h')) ι g * toEndC ι N =
      ((normV v' : ℕ) : ℂ) ^ deg g • (toEndC ι N * hN'.rep hl' ht' (deg_frob (h := h')) ι g) := fun g => by
    have := hN'.rep_comm hl' ht' (deg_frob (h := h')) ι g
    rw [toEndC_smul, mul_smul_comm, smul_mul_assoc, smul_comm] at this
    exact smul_right_injective _ ((map_ne_zero ι).mpr hc0) this
  obtain ⟨aL1, haL1⟩ := WeilDeligne.exists_isFrobSS (hN'.rep hl' ht' (deg_frob (h := h')) ι) (toEndC ι N)
    (hN'.isSmooth_rep hl' ht' _ ι) (hN.1.map _) hcomm
  obtain ⟨u, hu⟩ := (isUnit_exp (hN.1.smul β)).map (toEndC ι (n := Fin a))
  have i1 : aL1.Iso (ResEx.resRep h h' aK) := haL1.iso hb (LinearMap.GeneralLinearGroup.toLinearEquiv u)
    (fun g w => by
      show ((u : Module.End ℂ (Fin a → ℂ)) * toEndC ι (wdMat (tameL h' hl') (deg_frob (h := h')) (resTo L r) (c • N) g)) w =
        (toEndC ι (wdMat (tameL h hl) (deg_frob (h := h)) r N (ResEx.resW h h' g)) * (u : Module.End ℂ (Fin a → ℂ))) w
      rw [hu, ← map_mul, hβ, map_mul])
    (fun w => by
      show ((u : Module.End ℂ (Fin a → ℂ)) * toEndC ι N) w = (toEndC ι N * (u : Module.End ℂ (Fin a → ℂ))) w
      rw [hu, ← map_mul, exp_smul_mul hN.1, map_mul])
  have i2 : aL1.Iso aL2 := haL1.iso_of_smul ((map_ne_zero ι).mpr hc0) (by
    have := haL2
    rw [toEndC_smul] at this
    exact this)
  have ex' : wdOf h' hl' ι (resTo L r) = WD.mk (ResEx.resRep h h' aK) :=
    (IsWDOf.wdOf_eq hl' ⟨_, ht', _, deg_frob, c • N, aL2, hN', haL2, rfl⟩).trans (WD.sound (i2.symm.trans i1))
  refine ⟨a, aK, ResEx.resRep h h' aK, ex.symm, ex'.symm, rfl, fun σ σ' hs => ?_⟩
  show aK.ρ (ResEx.resW h h' σ') = aK.ρ σ
  congr 1
  exact Subtype.ext (AlgEquiv.ext fun z => (hs z).symm)

end GlobalTheory.AboveL

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem sameOff_symm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) {N : ℕ} {x y : GL (Fin N) (AfE F E)} (h : SameOff w x y) : SameOff w y x :=
  fun w' hw => (h w' hw).symm



theorem normConj_mem_pow : ∀ (D : D7) (n p : ℕ) (G : GAtP p) (A : LocAt D.host.F D.host.E n G), LocInt A → SplAlg A → ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf p (G.P.W v) (A.iw v) P → ∀ (m : ℕ) (a b : 𝓞 D.host.E), (b : D.host.E) = D.host.conj (a : D.host.E) → a ∈ P.asIdeal ^ m → ∃ c : 𝓞 D.host.F, c ∈ (A.pl v).1.asIdeal ^ m ∧ algebraMap D.host.F D.host.E (c : D.host.F) = ((a * b : 𝓞 D.host.E) : D.host.E) := by
  intro D n p G A hInt hSpl v P hP m a b hb ha

  let T : ℕ → Ideal (𝓞 D.host.E) := fun k =>
    { carrier := {x | ∃ y : G.P.W v, A.iw v (x : D.host.E) = algebraMap _ _ y ∧ (p : G.P.W v) ^ k ∣ y}
      add_mem' := by
        rintro x x' ⟨y, hy, hdy⟩ ⟨y', hy', hdy'⟩
        exact ⟨y + y', by simp [hy, hy'], dvd_add hdy hdy'⟩
      zero_mem' := ⟨0, by simp, dvd_zero _⟩
      smul_mem' := by
        rintro r x ⟨y, hy, hdy⟩
        obtain ⟨yr, hyr, -⟩ := hP r
        exact ⟨yr * y, by simp [hy, hyr], dvd_mul_of_dvd_right hdy _⟩ }
  have hT : ∀ k, P.asIdeal ^ k ≤ T k := by
    intro k
    induction k with
    | zero =>
      intro x _
      obtain ⟨y, hy, -⟩ := hP x
      exact ⟨y, hy, by simp⟩
    | succ k ih =>
      rw [pow_succ]
      refine Ideal.mul_le.2 fun x hx z hz => ?_
      obtain ⟨y, hy, hdy⟩ := ih hx
      obtain ⟨yz, hyz, hdz⟩ := hP z
      exact ⟨y * yz, by simp [hy, hyz], by rw [pow_succ]; exact mul_dvd_mul hdy (hdz.1 hz)⟩
  obtain ⟨ya, hya, hda⟩ := hT m ha
  obtain ⟨yb, hyb, -⟩ := hP b
  have hcc : ∀ x : D.host.E, D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) :=
    fun x => D.host.conjE_apply D.host.φ₀ x
  have hcc2 : ∀ x : D.host.E, D.host.conj (D.host.conj x) = x := fun x =>
    D.host.φ₀.injective (by rw [hcc, hcc, Complex.conj_conj])
  have hfix : D.host.conj (((a * b : 𝓞 D.host.E) : D.host.E)) = ((a * b : 𝓞 D.host.E) : D.host.E) := by
    show D.host.conj ((a : D.host.E) * (b : D.host.E)) = (a : D.host.E) * (b : D.host.E)
    rw [map_mul, hb, hcc2, mul_comm]
  have hF : ((a * b : 𝓞 D.host.E) : D.host.E) ∈ D.host.F :=
    (D.host.conjE_mem_hostF_iff _).2 hfix
  have hint : IsIntegral ℤ (⟨_, hF⟩ : D.host.F) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.F D.host.E) (algebraMap D.host.F D.host.E).injective).1
      (a * b).isIntegral_coe
  let c : 𝓞 D.host.F := ⟨⟨_, hF⟩, hint⟩
  refine ⟨c, ?_, rfl⟩
  obtain ⟨t, ht⟩ := hda
  have hiw : A.iw v ((a * b : 𝓞 D.host.E) : D.host.E) = (p : G.P.Qq v) ^ m * algebraMap _ _ (t * yb) := by
    show A.iw v ((a : D.host.E) * (b : D.host.E)) = _
    rw [map_mul, hya, hyb, ht]
    simp only [map_mul, map_pow, map_natCast]
    ring
  have hph : A.phE v ((a * b : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) (c : D.host.F) := by
    have h1 : (inclE (F := D.host.F) ((A.pl v).1.adicCompletion D.host.F)) ((a * b : 𝓞 D.host.E) : D.host.E) =
        (1 : D.host.E) ⊗ₜ[D.host.F] algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) (c : D.host.F) := by
      show (algebraMap D.host.F D.host.E (c : D.host.F)) ⊗ₜ[D.host.F] (1 : (A.pl v).1.adicCompletion D.host.F) = _
      rw [← Algebra.TensorProduct.algebraMap_apply (R := D.host.F) (S := D.host.F), Algebra.TensorProduct.algebraMap_apply']
    show ((A.spl v) ((inclE (F := D.host.F) ((A.pl v).1.adicCompletion D.host.F)) ((a * b : 𝓞 D.host.E) : D.host.E))).1 = _
    refine (congrArg (fun z => ((A.spl v) z).1) h1).trans ?_
    simp only [hSpl v]
  have heQ : A.eQ v (A.iw v ((a * b : 𝓞 D.host.E) : D.host.E)) = A.phE v ((a * b : 𝓞 D.host.E) : D.host.E) := by
    simp [LocAt.iw]
  have hu : A.eQ v (algebraMap _ _ (t * yb)) ∈ (A.pl v).1.adicCompletionIntegers D.host.F :=
    (hInt v _).1 ⟨_, rfl⟩
  rw [hiw, map_mul, map_pow, map_natCast, hph] at heQ
  have hval : ∀ k : D.host.F, Valued.v (algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) k) =
      (A.pl v).1.valuation D.host.F k := by
    intro k
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (A.pl v).1 k
  have hp1 : Valued.v ((p : ℕ) : (A.pl v).1.adicCompletion D.host.F) ≤ WithZero.exp (-1 : ℤ) := by
    have h := (HeightOneSpectrum.intValuation_le_pow_iff_mem (A.pl v).1 ((p : ℕ) : 𝓞 D.host.F) 1).2
      (by simpa using (A.pl v).2)
    rw [← map_natCast (algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F)), hval,
      ← map_natCast (algebraMap (𝓞 D.host.F) D.host.F), HeightOneSpectrum.valuation_of_algebraMap]
    simpa using h
  have hu' : Valued.v (A.eQ v (algebraMap _ _ (t * yb))) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hu
  have hv : Valued.v (algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) (c : D.host.F)) ≤
      WithZero.exp (-(m : ℤ)) := by
    rw [← heQ, map_mul, map_pow]
    calc _ ≤ WithZero.exp (-1 : ℤ) ^ m * 1 := mul_le_mul' (pow_le_pow_left' hp1 m) hu'
      _ = WithZero.exp (-(m : ℤ)) := by
        rw [mul_one, ← WithZero.exp_nsmul]
        congr 1
        simp
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F),
    ← hval]
  exact hv

theorem smul_latK_of_smul_latAd : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (x x' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) (c : 𝓞 E), (c : E) ∈ (algebraMap F E).range → (∀ y ∈ latAd x Lb, c • y ∈ latAd x' Lb) → (∀ y ∈ latAd x' Lb, c • y ∈ latAd x Lb) → ∀ z ∈ latK sp J a x Lb, c • z ∈ latK sp J a x' Lb := by
  intro R F E _ _ _ _ _ _ sp N J a x x' Lb c hc h1 h2
  obtain ⟨c0, hc0⟩ := hc
  have hsig : (sp.cm.sig : E →+* E) (c : E) = c := by
    rw [← hc0]; exact (sp.cm.sig).commutes c0
  have hsm : ∀ y : Fin N → E, c • y = (c : E) • y := fun y => rfl
  have hd : ∀ y ∈ dualSet (sp.cm.sig : E →+* E) J (latAd x Lb),
      c • y ∈ dualSet (sp.cm.sig : E →+* E) J (latAd x' Lb) := by
    intro y hy z hz
    have key := hy _ (h2 z hz)
    have e1 : hform (sp.cm.sig : E →+* E) J z (c • y) = hform (sp.cm.sig : E →+* E) J (c • z) y := by
      rw [hsm, hsm]
      simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, hsig]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1]; exact key
  have hc' : compan (sp := sp) J a (latAd x Lb) ≤
      (compan (sp := sp) J a (latAd x' Lb)).comap (LinearMap.lsmul (𝓞 E) (Fin N → E) c) := by
    unfold compan
    refine sup_le (fun y hy => ?_) (Submodule.smul_le.2 fun r hr n hn => ?_)
    · exact Submodule.mem_sup_left (h1 y hy)
    · have hn' : c • n ∈ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J (latAd x' Lb)) := by
        have : Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J (latAd x Lb)) ≤
            (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J (latAd x' Lb))).comap
              (LinearMap.lsmul (𝓞 E) (Fin N → E) c) :=
          Submodule.span_le.2 fun y hy => Submodule.subset_span (hd y hy)
        exact this hn
      rw [Submodule.mem_comap]
      show c • (r • n) ∈ _
      rw [smul_comm]
      exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hn')
  intro z hz
  unfold latK toStd at hz ⊢
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
  refine Submodule.mem_map.2 ⟨c • w, hc' hw, ?_⟩
  rw [LinearMap.map_smul]

theorem eqOff_latK_of_sameOff : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (n p : ℕ) [Fact p.Prime] (G : GAtP p) (A : LocAt D.host.F D.host.E n G), LocInt A → SplAlg A → ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf p (G.P.W v) (A.iw v) P → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (a : 𝓞 D.host.E) (Lb : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin N → D.host.E)) = ⊤ → ∀ x x' : GL (Fin N) (AfE D.host.F D.host.E), SameOff (A.pl v).1 x x' → GL3Theta.EqOff D P (latK D.sp J a x Lb) (latK D.sp J a x' Lb) := by
  intro D n p _ G A hInt hSpl v P hP N J a Lb hfin hspan x x' hoff
  obtain ⟨m1, h1⟩ := GlobalTheory.T.adelicLattice_smul_mem_of_agree_away_from_place D.host.F D.host.E N Lb hfin hspan (A.pl v).1 x x' hoff
  obtain ⟨m2, h2⟩ := GlobalTheory.T.adelicLattice_smul_mem_of_agree_away_from_place D.host.F D.host.E N Lb hfin hspan (A.pl v).1 x' x (sameOff_symm _ hoff)
  refine ⟨max m1 m2, fun a' b hb ha => ?_⟩
  obtain ⟨c, hc, hcab⟩ := normConj_mem_pow D n p G A hInt hSpl v P hP (max m1 m2) a' b hb ha
  have hr : ((a' * b : 𝓞 D.host.E) : D.host.E) ∈ (algebraMap D.host.F D.host.E).range := ⟨_, hcab⟩
  have e1 : ∀ y ∈ latAd x Lb, (a' * b) • y ∈ latAd x' Lb := by
    intro y hy
    have := h1 c (Ideal.pow_le_pow_right (le_max_left _ _) hc) y hy
    rw [hcab] at this
    exact this
  have e2 : ∀ y ∈ latAd x' Lb, (a' * b) • y ∈ latAd x Lb := by
    intro y hy
    have := h2 c (Ideal.pow_le_pow_right (le_max_right _ _) hc) y hy
    rw [hcab] at this
    exact this
  exact ⟨smul_latK_of_smul_latAd D.sp J a x x' Lb _ hr e1 e2, smul_latK_of_smul_latAd D.sp J a x' x Lb _ hr e2 e1⟩

end GlobalTheory.TwV.Xc

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.modelPartition_size_extension_firstLast_rows : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → NuIs X D pos j (extNu (D.R.N (j + 1)) ν) ∧ (∀ τ, szT X D pos j τ = ∑ r, (ν τ r : ℤ)) ∧ (∀ τ, szT X D pos j τ = ∑ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ)) ∧ (∀ τ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ) ≤ cT1 X D pos j τ) ∧ ∀ τ, 0 ≤ X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) := by
  first | exact @GlobalTheory.TwV.DelA.size_first_last_rows | exact GlobalTheory.TwV.DelA.size_first_last_rows | (intros; apply GlobalTheory.TwV.DelA.size_first_last_rows <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symbolFramePolynomial_eq_zero_of_generic_vanish : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (P : DA X Kc j), (∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' P = 0) → P = 0 := by
  first | exact @GlobalTheory.TwV.DelA.eq_zero_of_evD_generic | exact GlobalTheory.TwV.DelA.eq_zero_of_evD_generic | (intros; apply GlobalTheory.TwV.DelA.eq_zero_of_evD_generic <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL

theorem overPl_unique {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (τ : E →+* ℂ)
    {w u : HeightOneSpectrum (𝓞 E)} (hw : OverPl ι τ w) (hu : OverPl ι τ u) : u = w := by
  by_contra hne
  have hI : u.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have htop : u.asIdeal ⊔ w.asIdeal = ⊤ := Ideal.IsMaximal.coprime_of_ne u.isMaximal w.isMaximal hI
  have h1 : (1 : 𝓞 E) ∈ u.asIdeal ⊔ w.asIdeal := htop ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  have hx' := hu x hx
  have hy' := hw y hy
  have hsum : ι.symm (τ ((x : E))) + ι.symm (τ ((y : E))) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _)]
    have : ((x : E) + (y : E)) = 1 := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hxy
    rw [this, map_one, map_one]
  have hle := IsUltrametricDist.norm_add_le_max (ι.symm (τ ((x : E)))) (ι.symm (τ ((y : E))))
  rw [hsum, norm_one] at hle
  exact absurd hle (not_le.mpr (max_lt hx' hy'))

end GlobalTheory.CongL
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut

theorem weak_repIso : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (r r' : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak π ι r' → UpperTheory.V.Af.RepIso r r' := by
  intro E Ω _ _ _ _ _ _ l _ ι a π r r' h h'
  obtain ⟨hc, hss, hev⟩ := h
  obtain ⟨hc', hss', hev'⟩ := h'
  refine GlobalTheory.IsoOfFrobFree.main E Ω l ι a r r' hc hc' hss hss' ?_
  filter_upwards [hev, hev'] with w ⟨B, hB, hF⟩ ⟨B', hB', hF'⟩
  obtain rfl := CG.HasSat.unique hB hB'
  exact ⟨_, hF, hF'⟩

end GlobalTheory.GalCut
end
