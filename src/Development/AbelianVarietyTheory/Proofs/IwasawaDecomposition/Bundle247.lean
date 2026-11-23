module

public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.OhatCompact
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle239
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelMeasure

theorem isMinf_unique {p q : ℕ} {m m' : Measure (UpqT p q)} (h : Lev.IsMinf m) (h' : Lev.IsMinf m') : m' = m := by
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.1
  haveI := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.2.1
  haveI := h.1
  haveI := h'.1
  have e : m' = ((Measure.haarScalarFactor m' m : NNReal) : ENNReal) • m := Measure.isMulLeftInvariant_eq_smul m' m
  have h1 := GlobalTheory.OmegaDensityScale.omegaDensity_smul h.2 (Measure.haarScalarFactor m' m)
  rw [← e] at h1
  have h2 := GlobalTheory.OmegaDensityScale.omegaDensity_unique h'.2 h1
  have h0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have ht : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hc : ((Measure.haarScalarFactor m' m : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (h2.trans (one_mul _).symm)
  rw [e, hc, one_smul]

theorem exists_isMeasLevW (D : D7) (V : HSp D) (hV : V.SigOK) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hKo : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))
    (hKc : IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (m : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))
    (hm : ∀ ρ, (m ρ).IsHaarMeasure) (hg : ∀ ρ, good ρ (m ρ)) (hu : ∀ ρ m', good ρ m' → m' = m ρ) :
    ∃ μ, Lev.IsMeasLevW V K good μ := by
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb D.host.F D.host.E D.sp.cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (tauE D i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig V.rank V.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) A hcm hτ hθ1 (fun i => hV (tauE D i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  let j : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* GA D V :=
    (e0.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : Continuous j := e0.symm.continuous.comp (Continuous.prodMk_right 1)
  have hj0 : ∀ k, e0 (j k) = (1, k) := fun k => e0.apply_symm_apply _
  have hfin : ∀ h : GA D V, Lev.finE V (j (e0 h).2) = Lev.finE V h := by
    intro h
    have h1 : finHom V (j (e0 h).2) = finHom V h := by
      refine Units.ext ?_
      have a1 := (he0 (j (e0 h).2)).1
      have a2 := (he0 h).1
      rw [hj0] at a1
      exact a1.symm.trans a2
    rw [Lev.finE_eq, Lev.finE_eq, h1]
  have hinf : ∀ k, j k ∈ GfC V := by
    intro k
    have a1 := (he0 (j k)).2
    rw [hj0] at a1
    exact Units.ext a1.symm
  let K' := (K.comap (Lev.finE V)).comap j
  have hK : ∀ h : GA D V, (e0 h).2 ∈ K' ↔ Lev.finE V h ∈ K := fun h => by
    rw [← hfin h]; rfl
  have hK'o : IsOpen (K' : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := hKo.preimage hj
  have hK'c : IsCompact (K' : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := by
    have h1 := hKc.image (continuous_snd.comp e0.continuous)
    convert h1 using 1
    ext k
    constructor
    · intro hk
      exact ⟨j k, ⟨hinf k, hk⟩, congrArg Prod.snd (hj0 k)⟩
    · rintro ⟨h, hh, rfl⟩
      exact (hK h).2 hh.2
  let e : GA D V ≃ₜ* (∀ i, UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2) ×
      HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := GlobalTheory.Mem.VolExists.exists_haar_prod m e K' hK'o hK'c
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' => ⟨⟨m, hg⟩, fun m' hm' B hB => ?_⟩⟩
  obtain rfl : m' = m := funext fun i => hu i _ (hm' i)
  have hv : ∀ i, ∃ u : UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact GlobalTheory.Mem.VolExists.exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hv using hv
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, m' i ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) = m' i (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (hm i)
    rw [measure_preimage_mul, measure_preimage_mul_right]
  rw [Finset.prod_congr rfl (fun i _ => hcj i)] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat D.sp.cm.sig V.gram (θ' i) h := by
    rw [he1, (he0 h).2]; rfl
  have h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat D.sp.cm.sig V.gram (θ' i) h := by
    have h3 : UpqT.mat (u i)⁻¹ * A' i = A i := by
      rw [← hv i, ← Matrix.mul_assoc, ← GlobalTheory.Mem.VolExists.mat_mul, inv_mul_cancel, GlobalTheory.Mem.VolExists.mat_one,
        Matrix.one_mul]
    rw [GlobalTheory.Mem.VolExists.mat_mul, GlobalTheory.Mem.VolExists.mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1,
      ← Matrix.mul_assoc, hv i]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨C', h3, -⟩ := (hA i).2.2 _ (hA' i)
    have : b = u i * e1 (e0 h).1 i * (u i)⁻¹ := by
      apply hinj
      have h5 := congrArg (· * C') (hbe.trans h2.symm)
      simpa only [Matrix.mul_assoc, h3, Matrix.mul_one] using h5
    exact this ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

end GlobalTheory.LevelMeasure
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker Complex Classical
open Formalism.L2.Th1.H (matH alphaQ qOf opU slice pow4)
open scoped BigOperators ComplexConjugate Real

namespace WeilVac

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem kappa_ne_zero {γ₀ : IsoK D} (k : KapChoice γ₀) : k.kappa ≠ 0 := by
  refine finprod_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun p => zpow_ne_zero _ ?_
  intro h0
  have h1 := k.rt_pow p p.2.1 p.2.2
  have hpi : k.pi p ≠ 0 := by
    intro h
    have h2 := k.pi_gen p p.2.1 p.2.2
    rw [h, Ideal.span_singleton_zero] at h2
    exact pow_ne_zero _ (k.pp p).ne_bot h2
  have hE : (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) ≠ 0 := by
    set_option synthInstance.maxHeartbeats 200000 in
      simpa using hpi
  rw [h0, zero_pow (mul_ne_zero two_ne_zero (classNumber_ne_zero _))] at h1
  exact div_ne_zero ((map_ne_zero _).2 hE) ((map_ne_zero _).2 ((map_ne_zero _).2 hE)) h1.symm

theorem thMM_spec (B : Base D cc δ) (h : B.StdOK) : B.IsThMM B.thMM ∧ B.thMM ≠ 0 := by
  obtain ⟨e, u⟩ := ThetaVec.thetaVector _ _ _ _ _ _ _ _ h _ (kappa_ne_zero B.kc)
  have h1 : B.IsThMM B.thMM := Classical.epsilon_spec (p := IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa) e
  exact ⟨h1, (u _ h1.1 h1.2).1⟩

theorem areaOK (B : Base D cc δ) : B.AreaOK := by
  rw [Base.AreaOK, ThetaVec.area_eq]
  exact GlobalTheory.OddTheta.area_eq B.L _ fun z => by rw [← B.lat]; rfl

theorem q_int (B : Base D cc δ) (h : B.StdOK) {x : D.what₂.Tau → ℂ} (hx : x ∈ B.lamM) :
    ∃ m : ℤ, qOf B.cq (matH (hOne B.L D.what₂.Tau)) x = m := by
  have hs : ∀ a, slice a (0 : Fin 4 × D.what₂.Tau → ℂ) = 0 := fun _ => rfl
  have h1 := h.betaSemi.1 (B.gC (ThetaVec.ins 0 x)) ⟨ThetaVec.ins 0 x, fun a => by
    rw [ThetaVec.slice_ins]; split_ifs; exacts [hx, B.lamM.zero_mem], rfl⟩
  rw [h.betaAlpha, ← mul_self_eq_one_iff] at h1
  simp only [ThetaVec.slice_ins, Fin.prod_univ_four, hs, h.alpha0, Fin.isValue, if_true, Fin.reduceEq, if_false,
    mul_one] at h1
  rw [alphaQ, ← Complex.exp_add, Complex.exp_eq_one_iff] at h1
  obtain ⟨m, hm⟩ := h1
  refine ⟨m, ?_⟩
  have : (qOf B.cq (matH (hOne B.L D.what₂.Tau)) x : ℂ) = m := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    linear_combination hm
  exact_mod_cast this

theorem entry_mem (B : Base D cc δ) {N N' : ℕ} {x : VC D N N'}
    (hx : x ∈ La D (tor0 D cc δ) (stdL D N) (stdL D N')) : x ∈ powLat B.lamM N N' := by
  refine (AddSubgroup.closure_le _).2 ?_ hx
  rintro _ ⟨w, hw, A, hA, rfl⟩ i j
  exact AddSubgroup.subset_closure ⟨w, hw, A i j, (GlobalTheory.OddGenus.mem_iff_entries D N N' A).1 hA i j, rfl⟩

theorem Hf_eq (B : Base D cc δ) {N N' : ℕ} (z w : VC D N N') :
    Hf D (tor0 D cc δ) z w =
      ∑ i, ∑ j, matH (hOne B.L D.what₂.Tau) (fun τ => z τ i j) (fun τ => w τ i j) := by
  have hA : area (tor0 D cc δ).abelian₂ = latticeArea B.L := (areaOK B).trans (ThetaVec.area_eq _)
  have e : ∀ u v : D.what₂.Tau → ℂ, matH (hOne B.L D.what₂.Tau) u v =
      ∑ τ, u τ * conj (v τ) / (latticeArea B.L : ℂ) := fun u v => ThetaVec.stdH_apply B.L u v
  simp only [e, Hf, hA, Finset.sum_div]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem thZero_mem (B : Base D cc δ) (h : B.StdOK) (N N' : ℕ) :
    B.thZero N N' ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N') := by
  have hθ := (thMM_spec B h).1.1
  refine ⟨?_, fun x hx z => ?_⟩
  · have hd : Differentiable ℂ B.thMM := differentiableOn_univ.1 hθ.1.differentiableOn
    unfold Base.thZero tensPow
    fun_prop
  · have hx' := entry_mem B hx
    choose m hm using fun i j => q_int B h (hx' i j)
    have h1 : Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = ((∑ i, ∑ j, m i j : ℤ) : ℝ) := by
      rw [Hf_eq B]
      push_cast
      simp only [Complex.re_sum, Finset.mul_sum, ← hm]
      rfl
    have h2 : al D (tor0 D cc δ) x = ∏ i, ∏ j, alphaQ B.cq (matH (hOne B.L D.what₂.Tau)) fun τ => x τ i j := by
      rw [al, h1, round_intCast, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      simp only [alphaQ, hm, ← Complex.exp_sum, ← Finset.mul_sum]
      congr 1
      push_cast
      ring
    rw [h2, U, Hf_eq B, Hf_eq B]
    simp only [Base.thZero, tensPow, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, Complex.exp_sum,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hθ.2 _ (hx' i j) fun τ => z τ i j

end WeilVac

open WeilVac

end GlobalTheory.Mem.Col2
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL


theorem _root_.GlobalTheory.T.isCompact_integralGL_finiteAdeles : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), IsCompact (PIW.ClassFinD.KGL F n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) := by
  first | exact @GlobalTheory.isCompact_KGL | exact GlobalTheory.isCompact_KGL | (intros; apply GlobalTheory.isCompact_KGL <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open Formalism.UG (cT cT_mul cT_one bc UJ)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeRef

section Cong

variable {A : Type} [CommRing A] {M : ℕ} (s : A →+* A)

def act (J : Matrix (Fin M) (Fin M) A) (P : GL (Fin M) A) : Matrix (Fin M) (Fin M) A :=
  cT s (P : Matrix (Fin M) (Fin M) A) * J * (P : Matrix (Fin M) (Fin M) A)

theorem act_one (J : Matrix (Fin M) (Fin M) A) : act s J 1 = J := by
  simp [act, cT_one]

theorem act_mul (J : Matrix (Fin M) (Fin M) A) (P Q : GL (Fin M) A) :
    act s J (P * Q) = act s (act s J P) Q := by
  simp only [act, Units.val_mul, cT_mul, Matrix.mul_assoc]

def cong (M : ℕ) : Setoid (Matrix (Fin M) (Fin M) A) where
  r J J' := ∃ P : GL (Fin M) A, J' = act s J P
  iseqv := ⟨fun J => ⟨1, (act_one s J).symm⟩,
    fun ⟨P, h⟩ => ⟨P⁻¹, by rw [h, ← act_mul, mul_inv_cancel, act_one]⟩,
    fun ⟨P, h⟩ ⟨Q, h'⟩ => ⟨P * Q, by rw [h', h, act_mul]⟩⟩

end Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}

omit [NumberField E] in
theorem frameRel_iff (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (g : HA (AF F) σ J)
    (g' : HA (AF F) σ J') : FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g g' ↔
      HA.mat (AF F) σ J' g' = (bc (inclR (AF F)) P)⁻¹ * HA.mat (AF F) σ J g * bc (inclR (AF F)) P := by
  rw [mul_assoc, eq_inv_mul_iff_mul_eq, eq_comm, ← Units.val_inj]
  rfl

omit [NumberField E] in
theorem bc_mem {J : Matrix (Fin M) (Fin M) E} {u : GL (Fin M) E} (hu : act (σ : E →+* E) J u = J) :
    bc (inclR (AF F)) u ∈ HR (AF F) σ J := by
  show cT (sigR (AF F) σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) * J.map (inclR (AF F)) *
    (u : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) = J.map (inclR (AF F))
  have h : cT (sigR (AF F) σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) =
      (cT (σ : E →+* E) (u : Matrix (Fin M) (Fin M) E)).map (inclR (AF F)) := by
    ext i j
    simp [cT, sigR, inclR]
  rw [h, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun X : Matrix (Fin M) (Fin M) E => X.map (inclR (F := F) (AF F))) hu

def IsTransport (σ : E →ₐ[F] E) (J₀ J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)) : Prop :=
  ∃ (P : GL (Fin M) E) (e : HA (AF F) σ J₀ ≃* HA (AF F) σ J), J = act (σ : E →+* E) J₀ P ∧
    (∀ g, FrameRel J₀ J (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ μ = Measure.haar.map e

theorem frame (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (h : J' = act (σ : E →+* E) J P) :
    (∃ e : HA (AF F) σ J ≃* HA (AF F) σ J', ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧
    ∀ e : HA (AF F) σ J ≃* HA (AF F) σ J', (∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) →
      Continuous e ∧ Continuous e.symm :=
  ⟨(GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) M J J' P h).1.exists, (GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) M J J' P h).2⟩

theorem IsTransport.isHaar {J₀ J : Matrix (Fin M) (Fin M) E} {μ : Measure (HA (AF F) σ J)}
    (h : IsTransport σ J₀ J μ) : μ.IsHaarMeasure := by
  obtain ⟨P, e, hJ, he, rfl⟩ := h
  obtain ⟨h1, h2⟩ := (frame J₀ J P hJ).2 e he
  exact e.isHaarMeasure_map _ h1 h2

theorem IsTransport.map_eq (hσ : IsCMExt F E σ) {J₀ J J' : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (HA (AF F) σ J')}
    (h : IsTransport σ J₀ J μ) (h' : IsTransport σ J₀ J' μ') {P : GL (Fin M) E} (hP : J' = act (σ : E →+* E) J P)
    (e : HA (AF F) σ J ≃* HA (AF F) σ J') (he : ∀ g, FrameRel J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) :
    μ.map e = μ' := by
  haveI := h.isHaar
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hσ
  haveI : μ.IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ (GlobalTheory.HermLineZeros.conj_invol hσ) (δ := σ d - d)
      (sub_ne_zero.2 hd) (by rw [map_sub, GlobalTheory.HermLineZeros.conj_invol hσ, neg_sub]) hJ μ
  obtain ⟨P₁, e₁, hJ₁, he₁, hμ⟩ := h
  obtain ⟨P₂, e₂, hJ₂, he₂, rfl⟩ := h'
  have hu : act (σ : E →+* E) J (P₁⁻¹ * P₂ * P⁻¹) = J := by
    conv_lhs => rw [hJ₁, ← act_mul, ← mul_assoc, mul_inv_cancel_left, act_mul, ← hJ₂, hP, ← act_mul,
      mul_inv_cancel, act_one]
  let u : HA (AF F) σ J := (⟨_, bc_mem hu⟩ : HR (AF F) σ J)
  have hc := ((frame J J' P hP).2 e he).1.measurable
  have hc₁ := ((frame J₀ J P₁ hJ₁).2 e₁ he₁).1.measurable
  have key : (e₂ : _ → _) = e ∘ ((fun x => x * u) ∘ (fun x => u⁻¹ * x)) ∘ e₁ := by
    funext g
    apply Subtype.ext
    have a := (frameRel_iff _ _ _ _ _).1 (he₂ g)
    have b := (frameRel_iff _ _ _ _ _).1 (he (u⁻¹ * e₁ g * u))
    have c := (frameRel_iff _ _ _ _ _).1 (he₁ g)
    refine a.trans (Eq.trans ?_ b.symm)
    show _ = _ * ((bc (inclR (AF F)) (P₁⁻¹ * P₂ * P⁻¹))⁻¹ * HA.mat (AF F) σ J (e₁ g) *
      bc (inclR (AF F)) (P₁⁻¹ * P₂ * P⁻¹)) * _
    rw [c]
    simp only [map_mul, map_inv]
    group
  have hl := measurable_const_mul u⁻¹
  have hr := measurable_mul_const u
  rw [key, ← Measure.map_map hc ((hr.comp hl).comp hc₁), ← Measure.map_map (hr.comp hl) hc₁, ← hμ,
    ← Measure.map_map hr hl, map_mul_left_eq_self, map_mul_right_eq_self]

theorem exists_isTransport (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    ∃ μ, IsTransport σ (Quotient.mk (cong (σ : E →+* E) M) J).out J μ := by
  obtain ⟨P, hP⟩ := Quotient.mk_out (s := cong (σ : E →+* E) M) J
  obtain ⟨e, he⟩ := (frame (σ := σ) _ J P hP).1
  exact ⟨_, P, e, hP, he, rfl⟩

theorem exists_isHaar_basisInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ G : GaugeFam F E σ, G.IsHaar ∧ G.BasisInv := by
  intro F E _ _ _ _ _ σ hσ
  choose μ hμ using fun (M : ℕ) (J : Matrix (Fin M) (Fin M) E) => exists_isTransport σ J
  refine ⟨⟨μ⟩, fun M J _ => (hμ M J).isHaar, fun M J J' P hJ hP => ⟨(frame J J' P hP).1, fun e he => ?_⟩⟩
  have h' := hμ M J'
  rw [← Quotient.sound (s := cong (σ : E →+* E) M) (a := J) (b := J') ⟨P, hP⟩] at h'
  exact (hμ M J).map_eq hσ hJ h' hP e he

end GlobalTheory.GaugeRef
end
end
