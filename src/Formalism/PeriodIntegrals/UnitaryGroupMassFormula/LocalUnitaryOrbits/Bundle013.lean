module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUniformizerHermitianIdeal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.RelIndexSmulSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BHRSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle011
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

@[expose] public section

section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem ov_smul (a : v.adicCompletionIntegers F) (y : Fv F v ⊗[F] E) :
    a • y = sc (E := E) v (a : Fv F v) * y := by
  rw [← smul_eq_sc]; rfl

theorem iO_max (p : 𝓞 F) (hp : p ∈ v.asIdeal) :
    (⟨iO v p, mem_O_iO v p⟩ : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v p).mpr hp
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at h1
  exact (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))).mpr h1

theorem thetaSpan_holds : ThetaSpan σ J ψ v := by
  intro _ _ θ hsp x hx
  classical
  let ι : 𝓞 E →+* Fv F v ⊗[F] E := (inclR (F := F) (Fv F v)).comp (algebraMap (𝓞 E) E)
  let Nt : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Submodule.span _ (ι '' Set.range (RingOfIntegers.basis E))
  let M : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Submodule.span _ {(1 : Fv F v ⊗[F] E), inclR (F := F) (Fv F v) (θ : E)}
  have halg : ∀ b : 𝓞 F, ι (algebraMap (𝓞 F) (𝓞 E) b) = sc (E := E) v (iO v b) := by
    intro b
    show inclR (F := F) (Fv F v) (algebraMap F E (b : F)) = _
    rw [inclR_alg']
  have hN : ∀ y : 𝓞 E, ι y ∈ Nt := by
    intro y
    have hy : y ∈ Submodule.span ℤ (Set.range (RingOfIntegers.basis E)) := by
      rw [(RingOfIntegers.basis E).span_eq]
      trivial
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => rw [map_zero]; exact Nt.zero_mem
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact Nt.add_mem ha hb
    | smul n a _ ha => rw [map_zsmul]; exact zsmul_mem ha n
  have hI : ∀ w ∈ IE (E := E) v, ∀ c : 𝓞 E,
      ι (c * w) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • Nt := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, hp, rfl⟩ := hz
      intro c
      have hs := (ov_smul (E := E) v (⟨iO v p, mem_O_iO v p⟩ : v.adicCompletionIntegers F) (ι c)).symm
      rw [map_mul, halg, mul_comm]
      rw [hs]
      exact Submodule.smul_mem_smul (iO_max v p hp) (hN c)
    | zero => intro c; rw [mul_zero, map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => intro c; rw [mul_add, map_add (f := _)]; exact Submodule.add_mem _ (ha c) (hb c)
    | smul d a _ ha =>
      intro c
      rw [smul_eq_mul, ← mul_assoc]
      exact ha (c * d)
  have hNM : Nt ≤ M ⊔ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • Nt := by
    rw [Submodule.span_le]
    rintro _ ⟨y, _, rfl⟩
    obtain ⟨a0, a1, hq⟩ := hsp (Ideal.Quotient.mk (IE (E := E) v) y)
    obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective a0
    obtain ⟨b1, rfl⟩ := Ideal.Quotient.mk_surjective a1
    have e0 : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk _ b0) =
        Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) b0) := rfl
    have e1 : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) (Ideal.Quotient.mk _ b1) =
        Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) b1) := rfl
    have hw : y - algebraMap (𝓞 F) (𝓞 E) b0 - algebraMap (𝓞 F) (𝓞 E) b1 * θ ∈ IE (E := E) v := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, map_mul, hq, e0, e1]
      ring
    have hy : ι y = ((⟨iO v b0, mem_O_iO v b0⟩ : v.adicCompletionIntegers F) • (1 : Fv F v ⊗[F] E) +
        (⟨iO v b1, mem_O_iO v b1⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (θ : E)) +
        ι (1 * (y - algebraMap (𝓞 F) (𝓞 E) b0 - algebraMap (𝓞 F) (𝓞 E) b1 * θ)) := by
      rw [ov_smul, ov_smul, mul_one]
      show _ = sc (E := E) v (iO v b0) + sc (E := E) v (iO v b1) * ι θ + _
      rw [← halg, ← halg, ← map_mul, ← map_add (f := _), ← map_add (f := _)]
      congr 1
      ring
    rw [hy]
    exact Submodule.add_mem_sup (Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩) (hI _ hw 1)
  have hle : Nt ≤ M := Submodule.le_of_le_smul_of_le_jacobson_bot
    (Submodule.fg_span ((Set.finite_range _).image _)) (IsLocalRing.maximalIdeal_le_jacobson ⊥) hNM
  have hx' : x ∈ Submodule.span (v.adicCompletionIntegers F) (ι '' Set.univ) := hx
  have hxM : x ∈ M := by
    apply hle
    refine (Submodule.span_le.mpr ?_) hx'
    rintro _ ⟨y, _, rfl⟩
    exact hN y
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hxM
  refine ⟨a, b, ?_⟩
  rw [← hab, ov_smul, ov_smul, mul_one]

theorem resAlg_of_eta (hE : EtaLink σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of_span σ J ψ v (thetaSpan_holds σ J ψ v) hE

end PI.OmLocU.Red
end
end

section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem oEv_basis2 (hfin : Module.finrank F E = 2) : ∃ β : Fin 2 → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin 2 → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • β i := by
  have h := oEv_basis (E := E) v
  rw [hfin] at h
  exact h

theorem sigR_smulF (c : Fv F v) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a b => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem hb_li {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (hβ : LinearIndependent (Fv F v) β) :
    LinearIndependent (Fv F v) (hb σ v hinv β (a := a)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hent : ∀ i j, ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
    intro i j
    rw [hc]
    rfl
  have hβ2 := Fintype.linearIndependent_iff.1 hβ
  obtain ⟨i, j⟩ := p
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 := hent i j
    rw [sum_lt σ v hinv β c h] at h1
    have h0 := hβ2 ![c (i, j), c (j, i)] (by simpa [Fin.sum_univ_two] using h1)
    simpa using h0 0
  · have h1 := hent i i
    rw [sum_diag σ v hinv β c i, b_sc_eq] at h1
    exact (map_eq_zero_iff _ (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).1 h1
  · have h1 := hent j i
    rw [sum_lt σ v hinv β c h] at h1
    have h0 := hβ2 ![c (j, i), c (i, j)] (by simpa [Fin.sum_univ_two] using h1)
    simpa using h0 1

theorem fix_int' (hcm : IsCMExt F E σ) {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v)
    (hf : sigR (Fv F v) σ t = t) : ∃ r ∈ v.adicCompletionIntegers F, t = sc (E := E) v r := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin := hcm.2.2.1
  set r : Fv F v := algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) t with hr
  have hsc : sc (E := E) v r = t := by
    calc sc (E := E) v r
        = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2)) * (t + t) := by
          rw [b_sc_eq, hr, map_mul, trace_v v σ hinv hnt hfin, hf]
      _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2) * 2) * t := by
          rw [map_mul, map_ofNat, mul_assoc, two_mul]
      _ = t := by rw [half_two, map_one, one_mul]
  refine ⟨r, b_int_of_sc v (hsc ▸ ht), hsc.symm⟩

theorem hb_mem {a : ℕ} (hcm : IsCMExt F E σ) (β : Fin 2 → Fv F v ⊗[F] E)
    (hβ : ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin 2 → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • β i)
    (T : HermR (Fv F v) σ a) :
    T ∈ HO σ v a ↔ ∃ c : Fin a × Fin a → v.adicCompletionIntegers F,
      T = ∑ p, (c p : Fv F v) • hb σ v (b_sig_sig σ hcm) β p := by
  have hinv := b_sig_sig σ hcm
  constructor
  · intro hT
    have hT' : ∀ i j, (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v := hT
    have hH : ∀ i j, sigR (Fv F v) σ ((T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i) =
        (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := fun i j => T.2 i j
    choose d hd using fun i j => (hβ _).1 (hT' i j)
    choose r hr hrT using fun i => fix_int' σ v hcm (hT' i i) (hH i i)
    refine ⟨fun p => if p.1 < p.2 then d p.1 p.2 0 else if p.2 < p.1 then d p.2 p.1 1 else ⟨r p.1, hr p.1⟩, ?_⟩
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [sum_lt σ v hinv β _ h, hd i j, Fin.sum_univ_two]
      simp [h, not_lt.2 h.le]
    · rw [sum_diag σ v hinv β _ i, hrT i]
      simp
    · rw [sum_gt σ v hinv β _ h, ← hH i j, hd j i, Fin.sum_univ_two, map_add (f := _), sigR_smulF, sigR_smulF, add_comm]
      simp [h, not_lt.2 h.le]
  · rintro ⟨c, rfl⟩
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [sum_lt σ v hinv β _ h]
      exact (hβ _).2 ⟨![c (i, j), c (j, i)], by simp [Fin.sum_univ_two]⟩
    · rw [sum_diag σ v hinv β _ i]
      exact b_sc_mem v (c (i, i)).2
    · rw [sum_gt σ v hinv β _ h]
      have hm := b_sigR_mem v σ ((hβ ((c (j, i) : Fv F v) • β 0 + (c (i, j) : Fv F v) • β 1)).2
        ⟨![c (j, i), c (i, j)], by simp [Fin.sum_univ_two]⟩)
      rwa [map_add, sigR_smulF, sigR_smulF, add_comm] at hm

theorem idxPiH_std (a : ℕ) (hS : StdHyp σ J ψ) : IdxPiH σ v a := by
  intro _ ϖ hϖ
  have hcm := hS.1
  obtain ⟨β, hli, hβ⟩ := oEv_basis2 v hcm.2.2.1
  rw [genIdx v (HO σ v a) (hb σ v (b_sig_sig σ hcm) β) (hb_li σ v (b_sig_sig σ hcm) β hli)
    (hb_mem σ v hcm β hβ) ϖ hϖ, qv, Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring

end PI.OmLocU.SdB
end
end
