module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.LatCpt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TraceEqAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.SelfDualMeasureSFinite
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BHRSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BasIntSmulMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.QSplitHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle012

@[expose] public section

section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

def CondAllF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    IsStdChar ψ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x : Fv F v),
      (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔ dV v * x ∈ v.adicCompletionIntegers F

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem condV_of_all (h : CondAllF) : CondV σ J ψ v := by
  intro hs t
  rw [← h F hs.1.1 ψ hs.2.2.1 hs.2.2.2 v t]
  exact forall₂_congr fun s _ => by rw [mul_comm]

attribute [local instance] LocMassOrdSF.isModTop_tens in
private theorem fullLattice_of_isSDLoc (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (hSD : IsSDLoc σ J v (L : Set (Fin n → E))) :
    Submodule.IsFullLattice E L := by
  classical
  refine { toIsLattice := hL, span_eq_top := ?_ }
  rw [eq_top_iff]
  intro x _
  by_contra hx
  obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_le_ker_of_notMem hx
  let A := Fv F v ⊗[F] E
  let ι : E →+* A := inclR (F := F) (Fv F v)
  let f : (Fin n → A) →ₗ[A] A :=
    ∑ i : Fin n, ι (φ (Pi.single i 1)) • LinearMap.proj i
  have hf (y : Fin n → E) : f (ratV (F := F) (Fv F v) y) = ι (φ y) := by
    simp only [f, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, ratV,
      smul_eq_mul]
    change (∑ i : Fin n, ι (φ (Pi.single i 1)) * ι (y i)) = _
    simp_rw [← map_mul, ← map_sum]
    congr 1
    conv_rhs => rw [← Finset.univ_sum_single y, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  let fF := f.restrictScalars (Fv F v)
  let fO := fF.restrictScalars (v.adicCompletionIntegers F)
  have hfL : latLoc (E := E) v (L : Set (Fin n → E)) ≤ LinearMap.ker fO := by
    rw [latLoc, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    change f (ratV (F := F) (Fv F v) y) = 0
    rw [hf, LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy)), map_zero]
  have hOpen := LocMassOrdLat.isOpen_latLoc σ J v (L : Set (Fin n → E)) hSD (basLat_fg v L hL)
  obtain ⟨t, ht, htx⟩ := LocMassOrdLat.exists_scale v (hOpen.mem_nhds (Submodule.zero_mem _))
    (fun _ : Unit => ratV (F := F) (Fv F v) x)
  have hz := LinearMap.mem_ker.mp (hfL (htx ()))
  change fF (t • ratV (F := F) (Fv F v) x) = 0 at hz
  rw [map_smul] at hz
  change t • f (ratV (F := F) (Fv F v) x) = 0 at hz
  rw [hf] at hz
  exact ((map_ne_zero ι).2 hφx) ((smul_eq_zero.mp hz).resolve_left ht)

theorem sdVolW_of_cond (a : ℕ) (hC : CondAllF) (hP : TrPerf σ J ψ v) : SdVolW σ J ψ v Λ a := by
  intro hS hLat hSD hU hμ
  have hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ := by
    obtain ⟨L, hL, rfl⟩ := hLat
    exact ⟨L, fullLattice_of_isSDLoc σ J v L hL hSD, rfl⟩
  have hVol := sdVolW_of_pi σ J ψ v Λ a (condV_of_all σ J ψ v hC) (dualW_of_perf σ J ψ v Λ a hP)
    (idxPiW_std σ J ψ v Λ a hS hFull) hFull
  exact hVol hS hLat hSD hU hμ

theorem sdVolH_of_cond (a : ℕ) (hC : CondAllF) (hP : TrPerf σ J ψ v) :
    SdVolH σ J ψ v a := by
  intro hS
  exact sdVolH_of_pi σ J ψ v a (condV_of_all σ J ψ v hC) (dualH_of_perf σ J ψ v a hP)
    (idxPiH_std σ J ψ v a hS) hS

end PI.OmLocU.SdB
end
end

section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem sigQ_ne (hstd : StdHyp σ J ψ) (hun : UnramAt (E := E) v) : sigQ σ v ≠ RingHom.id _ := by
  by_cases hp : (IE (E := E) v).IsPrime
  · exact qInert_holds σ J ψ v hstd hun hp
  · haveI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    obtain ⟨e, he⟩ := qSplit_holds σ J ψ v hstd hun hp
    intro hid
    have h := he (e.symm (1, 0))
    rw [hid, RingHom.id_apply, RingEquiv.apply_symm_apply] at h
    exact one_ne_zero (congrArg Prod.fst h)

theorem trOnto_holds (hstd : StdHyp σ J ψ) : TrOnto σ v := by
  intro hun s hs hfix
  obtain ⟨θ, h3, h4⟩ := theta_exists σ v hstd.1
  have hsp := thetaSpan_holds σ J ψ v hstd hun θ h4
  have hind := theta_indep σ v hstd.1 θ h3
  set iθ : Fv F v ⊗[F] E := inclR (F := F) (Fv F v) (θ : E) with hiθ
  have hss : sigO σ (sigO σ θ) = θ := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ hstd.1 _)
  obtain ⟨t, ht⟩ := fix_int σ hstd.1 (θ + sigO σ θ) (by rw [map_add (f := _), hss, add_comm])
  have hσθ : sigO σ θ = algebraMap (𝓞 F) (𝓞 E) t - θ := by rw [ht]; ring
  have hinc : ∀ a : 𝓞 F, inclR (F := F) (Fv F v) ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) =
      sc (E := E) v (iO v a) := fun a => inclR_alg' v (a : F)
  have hsiθ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ iθ = sc (E := E) v (iO v t) - iθ := by
    have e1 := congrArg (fun y : 𝓞 E => inclR (F := F) (Fv F v) (y : E)) hσθ
    simp only [AddSubgroupClass.coe_sub, map_sub, hinc, sigO_coe] at e1
    rw [hiθ, sigR_incl]
    exact e1
  have htr : ∀ a b : Fv F v, (sc (E := E) v a + sc (E := E) v b * iθ) +
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (sc (E := E) v a + sc (E := E) v b * iθ) = sc (E := E) v (2 * a + b * iO v t) := by
    intro a b
    rw [map_add (f := _), map_mul, sigR_sc, sigR_sc, hsiθ]
    simp only [sc_eq', map_add (f := _), map_mul, map_ofNat]
    ring
  obtain ⟨s0, s1, hs01⟩ := hsp s hs
  have hs1 : (s1 : Fv F v) = 0 := by
    have h := htr s0 s1
    rw [← hs01, hfix] at h
    have h' := hind (2 * s0 + s1 * iO v t - 2 * s0) (0 - 2 * s1) (by
      rw [hs01] at h
      simp only [sc_eq', map_add (f := _), map_mul, map_sub, map_ofNat, map_zero] at h ⊢
      linear_combination (-1 : Fv F v ⊗[F] E) * h)
    have h2 : (2 : Fv F v) ≠ 0 := by
      have : (2 : Fv F v) = algebraMap F (Fv F v) 2 := by rw [map_ofNat]
      rw [this]; exact (map_ne_zero _).2 two_ne_zero
    have := h'.2
    rw [zero_sub, neg_eq_zero, mul_eq_zero] at this
    exact this.resolve_left h2
  have hmemO : ∀ a b : Fv F v, Valued.v a ≤ 1 → Valued.v b ≤ 1 →
      sc (E := E) v a + sc (E := E) v b * iθ ∈ OEv (E := E) v := fun a b ha hb =>
    Orb.oev_add v (by simpa using sc_mul_mem_oEv v ha (Orb.oSub (E := E) v).1)
      (sc_mul_mem_oEv v hb (Orb.gen_mem v θ))
  have hs' : s = sc (E := E) v (s0 : Fv F v) := by rw [hs01, hs1]; simp [sc_eq']
  have hs0 : Valued.v (s0 : Fv F v) ≤ 1 := s0.2
  by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
  ·
    have htv : ¬ t ∈ v.asIdeal := by
      intro htin
      apply sigQ_ne σ J ψ v hstd hun
      have h2Q : (2 : QE (E := E) v) = 0 := by
        have : (2 : QE (E := E) v) = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) 2) := by
          rw [map_ofNat, map_ofNat]
        rw [this, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ h2
      have htQ : Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) t) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ htin)
      have hθf : sigQ σ v (Ideal.Quotient.mk (IE (E := E) v) θ) = Ideal.Quotient.mk (IE (E := E) v) θ := by
        rw [sigQ_mk, hσθ, map_sub, htQ, zero_sub]
        linear_combination (-(Ideal.Quotient.mk (IE (E := E) v) θ)) * h2Q
      refine RingHom.ext fun q => ?_
      obtain ⟨a0, a1, rfl⟩ := h4 q
      rw [map_add (f := _), map_mul, sigQ_alg, sigQ_alg, hθf]
      rfl
    have hvt : Valued.v (iO v t) = 1 := le_antisymm (v_iO_le v t)
      (not_lt.1 fun hlt => htv ((v_iO_lt_iff v t).1 hlt))
    have ht0 : iO v t ≠ 0 := fun h0 => by rw [h0, map_zero] at hvt; exact zero_ne_one hvt
    refine ⟨sc (E := E) v 0 + sc (E := E) v ((s0 : Fv F v) * (iO v t)⁻¹) * iθ,
      hmemO _ _ (by simp) (by rw [map_mul, map_inv₀, hvt, inv_one, mul_one]; exact hs0), ?_⟩
    rw [htr, hs']
    congr 1
    field_simp
    ring
  · have hv2 : Valued.v (iO v 2) = 1 := le_antisymm (v_iO_le v 2)
      (not_lt.1 fun hlt => h2 ((v_iO_lt_iff v 2).1 hlt))
    have hi2 : iO v 2 = (2 : Fv F v) := by
      show algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 2
      rw [map_ofNat, map_ofNat]
    rw [hi2] at hv2
    have h20 : (2 : Fv F v) ≠ 0 := fun h0 => by rw [h0, map_zero] at hv2; exact zero_ne_one hv2
    refine ⟨sc (E := E) v ((s0 : Fv F v) * 2⁻¹) + sc (E := E) v 0 * iθ,
      hmemO _ _ (by rw [map_mul, map_inv₀, hv2, inv_one, mul_one]; exact hs0) (by simp), ?_⟩
    rw [htr, hs']
    congr 1
    field_simp
    ring

end PI.OmLocU.Red
end
end

section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def EtaIn : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (IE (E := E) v).IsPrime →
    ∀ x : Fv F v ⊗[F] E, x * x = x → x = 0 ∨ x = 1

def EtaSp : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1

theorem etaLink_of (hI : EtaIn σ J ψ v) (hS : EtaSp σ J ψ v) : EtaLink σ J ψ v := by
  intro hstd hun
  unfold etaV
  constructor
  · intro h hp
    split_ifs at h with hx
    · obtain ⟨x, h1, h2, h3⟩ := hx
      rcases hI hstd hun hp x h1 with h0 | h0
      · exact h2 h0
      · exact h3 h0
  · intro hp
    rw [if_pos (hS hstd hun hp)]

theorem resAlg_of_etaSp (hI : EtaIn σ J ψ v) (hS : EtaSp σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of_eta σ J ψ v (etaLink_of σ J ψ v hI hS)

end PI.OmLocU.Red
end
end
