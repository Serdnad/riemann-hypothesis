module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.coefUb :
    UpperTheory.V.Z.Kato.Joint.CoefUb := by
  intro l _ c c' F hF
  obtain ⟨d, h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c c'
  obtain ⟨d', h3, h4⟩ := (UpperTheory.V.Th.Nm.inOf d).1 {x // x ∈ F} (fun x => x.1) (fun x => hF x.1 x.2)
  exact ⟨d', h1.trans h3, h2.trans h3, fun x hx => h4 ⟨x, hx⟩⟩
end

section

open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

private theorem norm_l_lt (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends (p := l) ((l : ℕ) : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

private theorem sq_ne {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (α c : ℂ) (hα : ‖ι.symm α‖ = 1) (hc : c = 1 ∨ c = -1)
    (n : ℕ) (hn : n ≠ 0) : α ^ 2 ≠ c * (l : ℂ) ^ n := by
  intro h
  have h1 := congrArg (fun z => ‖ι.symm z‖) h
  have h2 : ‖ι.symm c‖ = 1 := by rcases hc with rfl | rfl <;> simp
  simp only [map_pow, map_mul, map_natCast, norm_pow, norm_mul, hα, h2, one_pow, one_mul] at h1
  have h3 := pow_lt_one₀ (norm_nonneg _) (norm_l_lt l) hn
  rw [← h1] at h3
  exact lt_irrefl _ h3

private theorem alg_eq {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) :
    algebraMap ℤ_[l] (Qbar l) z = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) :=
  IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) z

private theorem norm_alg {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) z‖ = ‖z‖ := by
  rw [alg_eq]
  exact PadicAlgCl.norm_extends (p := l) (z : ℚ_[l])

private theorem tmul_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) : ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) ∈ X.VB N l w (Qbar l) :=
  ⟨(1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : X.B N l w), by simp⟩

theorem UpperTheory.V.Z.Kato.Joint.admissibleFunctional_of_projection :
    UpperTheory.V.Z.Kato.Joint.AdmOf2 := by
  classical
  intro hAdm hK3 hRho _ hFrob hUnif hForm hFin hUb hLin hOp hStab hThP hEig hQuad hInt
  intro l _ Ω _ _ _ ι e S A W g hNf χg ψ₀ hlM hal hK hAtt hIne hψ j hj ε X N _ χ α B cc c₀ hN hMN hlN hχ hα hαe hE
  have hp : l.Prime := Fact.out
  have he := hNf.e_pos
  have hl2 := hNf.l_odd
  obtain ⟨ρ, hρ, hρc, hρ10, hρ11, F, hρ00⟩ := hRho l Ω ι e S A W g ψ₀ hNf ⟨hlM, hal, χg, hK, hAtt, hIne⟩ ⟨χg, hK, hIne, hψ⟩
  have hρ' : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = (eps l s ^ e * (χg s : Qbar l)⁻¹) • mat W s := by
    intro s
    rw [hρ, hψ s, rhoK, thK, mul_inv, inv_inv]
    rfl
  obtain ⟨⟨S0, hS0⟩, hirr⟩ := hFrob l Ω ι e S A W g χg hNf hK hAtt ρ hρ'
  have hq := hQuad l Ω ι e S A W g χg hNf hK hlM hAtt
  have hcop : ∀ d : ℕ, d.Coprime N → d.Coprime g.M := fun d hd => Nat.Coprime.coprime_dvd_right hMN hd
  have hlcN : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 hlN
  have hjl : (l : Ω) ∈ A.nonunits := (‹JEx› l Ω A hNf.atL).1
  have hjA : ∀ x ∈ A, ‖j x‖ ≤ 1 := fun x hx => (hj x).1 hx
  obtain ⟨φ, hφ1, hφ2⟩ := X.j_hol
  let lamC : Letter → ℂ := fun T => match T with
    | Letter.T q => g.a q
    | Letter.U => α
    | Letter.D d => g.χ (d : ZMod g.M)
  have hcm : Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := Units.continuous_val.comp hρc
  have hw : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hw1 : 2 * e - 1 + 1 = 2 * e := by omega
  have hw2 : 2 * e - 1 + 2 = 2 * e + 1 := by omega
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have h3 := hK3 ε X ε.injective ⟨φ, hφ2, hφ1⟩ (2 * e + 1) g N l hl2 hMN hN hlcN.symm ⟨e, rfl⟩ (by omega) α
    (by rw [← hχ l hlcN]; exact hαe) (sq_ne ι α _ hα (hq l (hcop l hlcN)) _ (by omega))
    (sq_ne ι α _ hα (hq l (hcop l hlcN)) _ (by omega)) lamC (fun _ _ _ => rfl) rfl (fun _ _ => rfl) (E := Qbar l) norm_alg ι
  simp only [hw] at h3
  obtain ⟨m, π, σ, P, hP, hP1, -, hσ, hπg, hσg, hσT, hπT, hπσ, hPx⟩ := h3 ρ S0
    (hUnif l Ω _ hcm.matrix_trace) (hUnif l Ω _ hcm.matrix_det)
    (fun q hq hS s hs => by rw [hw1]; exact hS0 q hq hS s hs) hirr
  let χd : ℕ → ℤ_[l] := fun d => if g.χ (d : ZMod g.M) = 1 then 1 else -1
  have hχd : ∀ d : ℕ, d.Coprime N → ι.symm (g.χ (d : ZMod g.M)) = ((χd d : ℤ_[l]) : Qbar l) := by
    intro d hd
    by_cases h : g.χ (d : ZMod g.M) = 1
    · simp [χd, h]
    · have h' := (hq d (hcop d hd)).resolve_left h
      simp only [χd, if_neg h]
      rw [h']
      simp
  have hχd' : ∀ d : ℕ, d.Coprime N → ι ((χd d : ℤ_[l]) : Qbar l) = χ d := by
    intro d hd
    rw [← hχd d hd, RingEquiv.apply_symm_apply, hχ d hd]
  obtain ⟨lam₀, lam, c, hc, hf0, hf, hfix, hl0, hl⟩ := hFin hUb l ι (2 * e + 1) N B cc (fun d => ((χd d : ℤ_[l]) : Qbar l)) c₀ P hP
  have hev : ∃ k : ℕ, ∀ T, GlobalTheory.KZ.admitted N l T → ‖ι.symm (lamC T)‖ ≤ (l : ℝ) ^ k := by
    obtain ⟨k, hk⟩ := hInt l Ω ι e S A W g χg hNf hK hAtt
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
    refine ⟨k, ?_⟩
    rintro (q | _ | d) hT
    · exact hk q hT.1
    · exact hα.le.trans h1
    · rcases hq d (hcop d hT) with h | h <;> simpa [lamC, h] using h1
  have heig := hEig hLin hOp hStab hThP l Ω ε X A N (2 * e - 1) j χd (fun T => ι.symm (lamC T))
    ⟨hjl, hl2, hlN, hN, hodd, hjA⟩ hev P hP
    (fun T hT b hb => by
      have hb' := GlobalTheory.T.hecke_letter_preserves_basis_set ε X ε.injective ⟨φ, hφ2, hφ1⟩ N l (2 * e - 1) hl2 hN hlcN.symm hodd T hT b hb
      rw [hPx _ (tmul_mem X N l _ _ hb'), hPx _ (tmul_mem X N l _ _ hb), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_smul, ← hπT i T hT _ (tmul_mem X N l _ _ hb)]
      rfl)
    lam₀ lam hf0 (by rw [hw2]; exact hl)
  obtain ⟨pr, a, cf, hcf, -, hadd, hsm, hint, hgal, hT, hD, hU, hlam⟩ :=
    hAdm ε X A N l e S W ψ₀ ι g j hNf he ⟨φ, hφ1, hφ2⟩ hjl hl2 hlN hN hjA (fun T => ι.symm (lamC T)) ρ F hρ hρ10 hρ11
      (by rw [hw1]; exact hρ00) (fun _ _ _ => rfl) χd hχd m π σ P hP hP1 hσ hπg hσg hσT hπT hπσ hPx c lam hf hfix heig
  refine ⟨pr, cf, χd, (((l : ℕ) : Qbar l) ^ a) • lam, ((l : ℕ) : Qbar l) ^ a, hc.trans hcf,
    pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero), hadd, hsm, hint, hgal,
    ⟨fun q => ((χd q : ℤ_[l]) : Qbar l), fun q hq hql b hb => ⟨hT q hq hql b hb,
      hD q ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hql (h.mul_left l)) b hb⟩⟩, hU, hχd',
    fun b hb d hd => hD d hd b hb, hlam, fun s hs => ?_⟩
  have hF := hForm l ι (2 * e + 1) N χ (fun q => g.a q) α B cc (fun d => ((χd d : ℤ_[l]) : Qbar l)) (fun T => ι.symm (lamC T))
    (by omega) hE hχd' (fun _ _ _ => ι.apply_symm_apply _) (ι.apply_symm_apply _) hχd P hP s hs
  rw [LinearMap.smul_apply, smul_eq_mul, hl, hl0, hF, hP1, map_one, one_mul]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open UpperTheory.V.Z.Kato.Joint
open scoped Pointwise

private theorem aqBd_place {q : ℕ} (hq : q.Prime) : ∃ w : Pl, ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  have hn : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) = q := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hne : Ideal.span {((q : ℕ) : 𝓞 ℚ)} ≠ ⊤ := fun h => by
    rw [h, Ideal.absNorm_top] at hn
    exact hq.one_lt.ne hn
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((q : ℕ) : 𝓞 ℚ) ∈ M := (Ideal.span_singleton_le_iff_mem M).1 hle
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hq.ne_zero (Nat.cast_eq_zero.1 hmem)

private theorem aqBd_frob (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {q : ℕ} (hq : q.Prime) :
    ∃ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s := by
  obtain ⟨w, hw⟩ := aqBd_place hq
  obtain ⟨V, hV⟩ := exists_isPlaceOver (F := ℚ) Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hV
  rw [GlobalTheory.RhoAdm.normV_ratPrime hq w hw] at hσ
  refine ⟨σ, V, ?_, fun x hx => ⟨?_, hσ.2 x ((V.valuation_le_one_iff x).2 hx)⟩⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    simpa using (hV _).2 hw
  · have h : σ • V = V := MulAction.mem_stabilizer_iff.1 hσ.1
    rw [← h]
    exact ValuationSubring.smul_mem_pointwise_smul σ x V hx

theorem UpperTheory.V.Z.Kato.Joint.aqBd :
    UpperTheory.V.Z.Kato.Joint.AqBd := by
  intro l _ Ω _ _ _ ι e S A W g χ hN hχ hatt
  obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
  have hc := (Continuous.matrix_trace
    (Units.continuous_val.comp (GlobalTheory.RhoAdm.untw_cont e W χ hN.cont hχ))).norm
  haveI : CompactSpace (Ω ≃ₐ[ℚ] Ω) := inferInstance
  obtain ⟨C, hC⟩ := (isCompact_range hc).bddAbove
  obtain ⟨k, hk⟩ := GlobalTheory.KummerEisensteinGalois.exists_le_l_pow l (max C (∑ q ∈ S0, ‖ι.symm (g.a q)‖))
  refine ⟨k, fun q hq => le_trans ?_ hk⟩
  by_cases hqS : q ∈ S0
  · exact le_max_of_le_right
      (Finset.single_le_sum (f := fun q => ‖ι.symm (g.a q)‖) (fun _ _ => norm_nonneg _) hqS)
  · obtain ⟨s, hs⟩ := aqBd_frob Ω hq
    rw [← (hS0 q hq hqS s hs).1]
    exact le_max_of_le_left (hC ⟨s, rfl⟩)
end
