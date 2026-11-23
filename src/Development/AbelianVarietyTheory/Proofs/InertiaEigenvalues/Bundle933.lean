module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle879
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle750
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubgroupIsUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle003
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut

@[expose] public section

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.RamShift

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem eq_finGL_of_pInf {q : GA E n} (hq : GeneralLinearGroup.map (pInf E) q = 1) :
    q = finGL E n (GeneralLinearGroup.map (pFin E) q) := by
  have h := infGL_mul_finGL q
  rw [hq, map_one, one_mul] at h
  exact h.symm

theorem pInf_tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  unfold GlobalTheory.CellDec.tl
  exact pInf_finGL _

theorem compV_tl_of_eq_zero (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {v : HeightOneSpectrum (𝓞 E)} (hv : l v = 0) :
    GlobalTheory.CellDec.compV E n v (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  rw [GlobalTheory.CellDec.compV_tl, hv, GlobalTheory.IwaCell.tD_zero]

theorem one_mem_mirS (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : (1 : GA E (m + 1)) ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) := by
  refine ⟨fun w _ => map_one _, fun j => ?_⟩
  rw [Units.val_one, Matrix.one_apply]
  by_cases h : j = Fin.last m
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem mem_NA_of_mem {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := n)) : u ∈ GlobalTheory.CellDec.NA E n :=
  (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => hu.1 i j hij, hu.2⟩

end GlobalTheory.RamShift


open GlobalTheory.RamShift in
theorem GlobalTheory.RamShift.exists_shifted_bump_shintani : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)), π.IsUnitary → ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ F ∈ GlobalTheory.JSW.mspanR π, ∃ l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, l₀.1 w (Fin.last m) = 0) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧
      (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
        (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, F (g * k) = F g) ∧
      GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) ∧
      ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
        GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  intro E _ _ _ m T π _ α hα ϖ hϖ
  set l₀ := shift m T ϖ with hl₀
  set t₀ := GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 with ht₀def
  have ht₀inf : GeneralLinearGroup.map (pInf E) t₀ = 1 := pInf_tl ϖ l₀.1
  set D := GeneralLinearGroup.map (pFin E) t₀ with hD
  have ht₀ : t₀ = finGL E (m + 1) D := eq_finGL_of_pInf ht₀inf
  obtain ⟨b, hb1, hbN, hbC, hbU, hbS⟩ := GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic E m T
  obtain ⟨φ, hφV, hφK, x₀, hx₀, hW₀⟩ := GlobalTheory.T.exists_spherical_whittaker_torusElement_ne_zero E m T π α hα ϖ hϖ
  set φ' := act (.fin D) φ with hφ'def
  have hφ'V : φ' ∈ π.V := π.stable _ φ hφV
  have hφ' : ∀ g, φ'.1 g = φ.1 (g * t₀) := fun g => by rw [ht₀]; rfl
  have hWφ' : ∀ y, whit φ'.1 y = whit φ.1 (y * t₀) := fun y => by
    rw [whit_mul_right]
    congr 1
    funext z
    exact hφ' z
  obtain ⟨F₀, hF₀V, hF₀b, hF₀U, hF₀inv, hF₀rel⟩ :=
    GlobalTheory.T.kirillov_semilocal_smooth_bump E m T b hbN hbC hbU hbS π φ' hφ'V ⟨x₀, hx₀, by rw [hWφ']; exact hW₀⟩
  have hWF : ∀ y, whit (fun g => F₀ (g * t₀⁻¹)) y = whit F₀ (y * t₀⁻¹) := fun y =>
    (whit_mul_right F₀ y t₀⁻¹).symm
  refine ⟨fun g => F₀ (g * t₀⁻¹), mspanR_rt hF₀V _, l₀, fun w => shift_last m T ϖ w, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨U, hUo, hU⟩ := hF₀U
    refine ⟨U.comap (MulAut.conj D).toMonoidHom, ?_, fun u hu g => ?_⟩
    · exact hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have e : g * finGL E (m + 1) u * t₀⁻¹ = g * t₀⁻¹ * finGL E (m + 1) (D * u * D⁻¹) := by
        rw [ht₀, map_mul, map_mul, map_inv]; group
      show F₀ (g * finGL E (m + 1) u * t₀⁻¹) = F₀ (g * t₀⁻¹)
      rw [e]
      exact hU _ hu _
  ·
    intro k hk hkinf hkT g
    have hkf := eq_finGL_of_pInf hkinf
    set kf := GeneralLinearGroup.map (pFin E) k with hkfdef
    have hφk : act (.fin kf) φ = φ := GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed E (m + 1) φ (π.cusp φ hφV).1 T hφK kf
      (fun w hw => by
        have := GlobalTheory.CellDec.mem_US.1 hk w hw
        exact this)
      (fun w hw => hkT w hw)
    have e : g * k * t₀⁻¹ = g * t₀⁻¹ * (t₀ * k * t₀⁻¹) := by group
    show F₀ (g * k * t₀⁻¹) = F₀ (g * t₀⁻¹)
    rw [e]
    refine hF₀inv _ ?_ ?_ ?_ _
    · rw [map_mul, map_mul, map_inv, ht₀inf, hkinf]; simp
    · intro w hw
      change GlobalTheory.CellDec.compV E (m + 1) w (t₀ * k * t₀⁻¹) = 1
      rw [map_mul, map_mul, map_inv, compV_tl_of_eq_zero ϖ l₀.1 (l₀.2 w hw), hkT w hw]; simp
    · intro y
      rw [hφ', hφ']
      have e2 : y * (t₀ * k * t₀⁻¹) * t₀ = y * t₀ * finGL E (m + 1) kf := by rw [← hkf]; group
      rw [e2]
      exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 (y * t₀)) hφk
  ·
    rw [hWF, mul_inv_cancel, hF₀b 1 (one_mem_mirS T m), hb1]
    exact one_ne_zero
  ·
    obtain ⟨C, hC, hCp⟩ := hbC
    refine ⟨C, hC, fun p hp hne => ?_⟩
    rw [hWF, mul_inv_cancel_right, hF₀b p hp] at hne
    obtain ⟨u, hu, hup⟩ := hCp p hp hne
    exact ⟨u⁻¹, inv_mem (mem_NA_of_mem hu), hup⟩
  ·
    intro p hp l hl
    have hcomm : GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1) = GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * t₀ := by
      rw [add_comm l₀.1 l.1, GlobalTheory.CellDec.tl_add]
    rw [hWF, hWF, hcomm, ← mul_assoc, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [hF₀rel (GlobalTheory.CellDec.tl (m + 1) ϖ l.1) _ (pInf_tl ϖ l.1)
      (fun w hw => compV_tl_of_eq_zero ϖ l.1 (l.2 w hw)) (fun x hx => ?_) p hp.1, mul_comm]
    rw [hWφ', hWφ', mul_assoc, ← GlobalTheory.CellDec.tl_add, add_comm l.1 l₀.1, GlobalTheory.T.whittaker_mul_torusShift_add_eq_sphericalProduct E m T π α hα φ hφV hφK ϖ hϖ x hx l hl, mul_comm]
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section

namespace GlobalTheory.PlaceRead.TupAt

section General

open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.SeriesTie Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {D : D7}

theorem splitK_of_prime (P : PlE D.host) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hn : ¬ Ideal.absNorm P.asIdeal ∣ 30 * D.host.condN) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal) := by
  have := P.isPrime
  have h2 : Ideal.absNorm P.asIdeal = normV P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have h1 : P.asIdeal.inertiaDeg ℤ = 1 :=
    Nat.Prime.eq_one_of_pow (Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal ▸ hp)
  have key : ∀ r : ℕ, r.Prime → ((r : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = r := fun r hr hm => by
    by_contra hne
    have hc : IsCoprime ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) (r : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hp hr).2 hne)
    obtain ⟨a, b, e⟩ := hc
    exact this.ne_top ((Ideal.eq_top_iff_one _).2
      (e ▸ add_mem (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _)) (Ideal.mul_mem_left _ _ hm)))
  have hN : ¬ Ideal.absNorm P.asIdeal ∣ D.host.condN := fun h => hn (h.mul_left _)
  have hF : Fact (Ideal.absNorm P.asIdeal).Prime := ⟨hp⟩
  have hsp := Formalism.L2.Host.span_isPrime (Ideal.absNorm P.asIdeal)
  have hmax : (Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : ℤ)}).IsMaximal :=
    hsp.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero)
  have hlo : P.asIdeal.LiesOver (Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  refine GlobalTheory.TwistDet.exists_splitK h1 (Formalism.L2.Host.ramificationIdx_eq_one D.host _ hN P.asIdeal) ?_
    (fun h => Formalism.HC.HostRaw.ne_q_of_not_dvd hN (key _ D.host.hyp.1 h))
    (fun h => Formalism.HC.HostRaw.ne_d_of_not_dvd hN (key _ D.host.hyp.2.1 h))
  rw [← h2]
  exact hp.eq_two_or_odd'.resolve_left (Formalism.HC.HostRaw.ne_two_of_not_dvd hN)

theorem isDelta_delAt (cf : CharFrame D) (i : D.ntw.Tw) : ∃ q : ℕ, IsDelta q (cf.delAt (D.ntw.l i)) ∧
    (∀ P : Pl D.host.E, P ∈ D.ntw.pD i ↔ (q : 𝓞 D.host.E) ∈ P.asIdeal) ∧ (q = D.host.pde ∨ q = D.host.pde') := by
  refine ⟨if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, fun P => ?_, ?_⟩
  · unfold CharFrame.delAt
    split_ifs
    exacts [cf.isDel', cf.isDel]
  · rw [← Finset.mem_coe, D.ntw.pD_eq]
    rfl
  · split_ifs
    exacts [Or.inr rfl, Or.inl rfl]

theorem ram_mul (cf : CharFrame D) (i : D.ntw.Tw) {Q : Finset (Pl D.host.E)} {ψ : HChar D.host.E} (hψ : IsPsi (D.ntw.l i) Q ψ)
    (P : Pl D.host.E) : ¬ (cf.delAt (D.ntw.l i) * ψ).UnrAt P ↔ P ∈ D.ntw.pD i ∨ P ∈ Q := by
  obtain ⟨q, hδ, hq, -⟩ := isDelta_delAt cf i
  have hm : ∀ x, (cf.delAt (D.ntw.l i) * ψ).loc P x = (cf.delAt (D.ntw.l i)).loc P x * ψ.loc P x := fun _ => rfl
  by_cases hP : P ∈ D.ntw.pD i
  · refine iff_of_true (fun hu => ?_) (Or.inl hP)
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 := (hδ.ine P ((hq P).1 hP) (D.ntw.l i ^ a)).1 fun x hx => by
      have h3 : ψ.loc P x ^ (D.ntw.l i ^ a) = 1 :=
        (MonoidHom.pow_apply ..).symm.trans (congrArg (fun χ : HChar D.host.E => χ.loc P x) ha)
      rw [eq_inv_of_mul_eq_one_left ((hm x).symm.trans (hu x hx)), inv_pow, h3, inv_one]
    have hl : (D.ntw.l i).Prime := (D.ntw.lPrime _).out
    have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1 (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hl).1 (Nat.prime_five.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    omega
  · have hd := hδ.unr P fun h => hP ((hq P).2 h)
    rw [or_iff_right hP, ← not_iff_not, not_not, ← hψ.ram]
    exact forall₂_congr fun x hx => by rw [hm, hd x hx, one_mul]

theorem chrEq_twVia {cf : CharFrame D} {c : NChoice D} {tp : TupTied D cf c} (h : PsiChoiceCompatible D cf c tp) {w : D.what₂.places.Pl}
    (hw : D.what₂.muAt w ≠ D.what₂.mu0) (hψ : IntegralHeckeForms.TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w)) {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hv : ∀ P, P ∉ c.Q w → P ∉ D.ntw.pD (c.twI w) → ∃ y, D.what₂.embLL y = (((tp.psi w).val P : ℂˣ) : ℂ))
    (ι : KE c w →+* ℂ) (hι : ∀ y, ι (c.embW w y) = D.what₂.embLL y) : ChrEq (twVia ρ ι).chi (tp.psi w) := by
  classical
  obtain ⟨-, -, hopen, -, hzk, -, -⟩ := hψ
  have hl : D.ntw.l (c.twI w) ≠ 0 := (D.ntw.lPrime _).out.ne_zero
  have hz : D.ntw.zk (c.twI w) (c.k' w) ^ (D.ntw.l (c.twI w) ^ c.k' w) = 1 :=
    Units.ext (by simpa using (D.ntw.zk_prim (c.twI w) (c.k' w)).pow_eq_one)
  have hfin := GlobalTheory.TwistChr.finite_placesOver D.host.E (l := D.what₂.places.resChar w) (c.twI_l w ▸ hl)
  refine GlobalTheory.TwistChr.chrEq_charOf hρ.rc _ _ hopen (pow_ne_zero (c.k' w) hl) (fun σ => ?_) _
    ((c.Q w ∪ D.ntw.pD (c.twI w)) ∪ hfin.toFinset)
    (fun v hv => ((tp.psi_is w hw).ram v).2 fun hQ => hv (Finset.mem_union_left _ (Finset.mem_union_left _ hQ)))
    fun v hv' A hA σ hσ => ?_
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · have h1 : v ∉ c.Q w := fun hQ => hv' (Finset.mem_union_left _ (Finset.mem_union_left _ hQ))
    obtain ⟨y, hy⟩ := hv v h1 fun hQ => hv' (Finset.mem_union_left _ (Finset.mem_union_right _ hQ))
    have hy' : D.what₂.embLL y⁻¹ = (((tp.psi w).val v)⁻¹ : ℂˣ).1 := by rw [map_inv₀, hy, Units.val_inv_eq_inv_val]
    have e := h w hw v h1 (fun hQ => hv' (Finset.mem_union_right _ (hfin.mem_toFinset.2 hQ))) A σ hA hσ _ hy'
    rw [← hy', ← hι, e, ← IsScalarTower.algebraMap_apply]
    rfl

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}

theorem isTupOf {μ0 : T0} (hL : Rl.toRealDat.toLevCh.Is μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) {Q : Finset (Pl D.host.E)} {ψ : HChar D.host.E} (hψ : IsPsi (D.ntw.l i) Q ψ) {t : T0}
    (ht : Rl.xiH t = Rl.C.delAt (D.ntw.l i) * ψ) (hch : ∀ P ∈ Rl.Q t, P ∈ ρ.ch i) (τ : GlobalTheory.ExportSeries.Twist D Circle)
    (hc : ChrEq τ.chi ψ) (hQ : τ.Q = half (ρ.ch i) Q) : GlobalTheory.ConjTwist.IsTupOf Rl.toRealDat (ρ.B i j b) τ t := by
  classical
  refine ⟨GlobalTheory.ChrEqUnique.idc_unique D _ _ _ (hL.xi t) (ht ▸ GlobalTheory.TwistChr.chrEq_mul (hp.delta i j b) hc), ?_⟩
  have key : ∀ P, (P ∈ Rl.Q t ∨ ∃ P' ∈ Rl.Q t, Lev.IsConjPl P' P) ↔ P ∈ D.ntw.pD i ∨ P ∈ Q := fun P =>
    (hL.Q_ram t P).symm.trans (ht ▸ ram_mul Rl.C i hψ P)
  ext P
  rw [Finset.mem_union, hρ.delta, hQ]
  refine Iff.trans ?_ (or_congr mem_half mem_half).symm
  rw [← or_and_right, ← key]
  refine ⟨fun h => ⟨Or.inl h, hch P h⟩, fun ⟨h1, h2⟩ => h1.elim id fun ⟨P', h3, h4⟩ => ?_⟩
  by_cases e : P' = P
  · exact e ▸ h3
  · exact absurd h2 (((hρ.ch i).pair _ _ (GlobalTheory.BigOn.Exp.isConjPl_of_lev h4) e).1 (hch P' h3))

end General

theorem val_delAt {D : D7} {cf : CharFrame D} (h : ValLL0 D cf) (i : D.ntw.Tw) (P : PlE D.host) (hP : P ∉ D.ntw.pD i) :
    ∃ y, D.what₂.embLL y = (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) := by
  obtain ⟨q, hδ, hq, -⟩ := isDelta_delAt cf i
  have hu := hδ.unr P fun e => hP ((hq P).2 e)
  have hv : (cf.delAt (D.ntw.l i)).ValuesIn 0 D.what₂.embLL := by
    unfold CharFrame.delAt
    split_ifs
    exacts [h.toLL.del', h.toLL.del]
  obtain ⟨y, hy⟩ := hv P hu
  exact ⟨y, by simpa [HChar.valTw] using hy⟩

section State

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  (x : St P)

theorem mem_Wt {v : B.places.Pl} (hv : TwistedAt (Dof x) v) : v ∈ P.Wt := by_contra fun h => hv (P.q.mu.off v h)

theorem tupT_muTw {v : B.places.Pl} (hv : TwistedAt (Dof x) v) :
    x.r.Y.tupT ((Dof x).what₂.muTw v) = x.m.z.R.mu ((Dof x).plEq v) := by
  rw [← ((Dof x).what₂.muAt_or v).resolve_left hv, x.r.Y.muAt v, x.r.Y.tupT_tup]

theorem xi_mu (ch : NChoice (Dof x)) {v : B.places.Pl} (hv : TwistedAt (Dof x) v) {ψ : HChar (Dof x).host.E} (e : ψ = T.psi v) :
    x.m.z.R.xiH (x.m.z.R.mu ((Dof x).plEq v)) = x.m.z.R.C.delAt ((Dof x).ntw.l (ch.twI v)) * ψ := by
  have h1 := (x.m.z.mu v).2
  rw [if_pos (mem_Wt x hv)] at h1
  refine ((x.m.z.lev.xiH _).trans h1).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ CharFrame.delAt x.m.z.lev.C (ch.twI_l v)) e).symm
  rfl

end State

end GlobalTheory.PlaceRead.TupAt

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix

namespace GlobalTheory.FirstBlocksReduction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ExportSeries GlobalTheory.FlatVecSum

variable {D : D7} {S T : HSp D}



theorem exists_reps {G X : Type} [Group G] (J J' : Subgroup G) (φ : G → X) (A : Set X) (hA : A.Finite)
    (hφ : ∀ κ ∈ J, φ κ ∈ A) (h : ∀ u ∈ J, ∀ κ ∈ J, u⁻¹ * κ ∈ J' ↔ φ u = φ κ) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ J) ∧ ∀ κ ∈ J, ∃! u : G, u ∈ F ∧ u⁻¹ * κ ∈ J' := by
  classical
  have hfin : (φ '' (J : Set G)).Finite := hA.subset (by rintro _ ⟨κ, hκ, rfl⟩; exact hφ κ hκ)
  have hs : ∀ x : ↥(φ '' (J : Set G)), ∃ u, u ∈ J ∧ φ u = x.1 := fun x => x.2
  choose s hsJ hsφ using hs
  haveI := hfin.fintype
  refine ⟨Finset.univ.image s, fun u hu => ?_, fun κ hκ => ⟨s ⟨φ κ, κ, hκ, rfl⟩, ⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
    exact hsJ x
  · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · exact (h _ (hsJ _) _ hκ).2 (hsφ _)
  · rintro u ⟨hu, hu'⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
    congr 1
    exact Subtype.ext ((hsφ x).symm.trans ((h _ (hsJ x) _ hκ).1 hu'))

theorem extension_by_one_mul {G H : Type} [Group G] [Monoid H] (K : Subgroup G) (f : K →* H) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    ext1 K f (a * b) = ext1 K f a * ext1 K f b := by
  unfold ext1
  rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left (mul_mem ha hb), ← map_mul]
  rfl

theorem lowerRightBlock_mul_blockTriangular {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) {a b : GL (Fin n) κ} (ha : a ∈ blockTri (blk2 r))
    (hb : b ∈ blockTri (blk2 r)) : upperLeftBlock hr (a * b) = upperLeftBlock hr a * upperLeftBlock hr b :=
  extension_by_one_mul _ _ ha hb

def firstBlocks (B : Base S T) (ψ : Twist D Circle) (k : Bridge.Gf S) : G0 B.G.Pg T.rank :=
  rTup B.F.βS (B.levS ψ) (Formalism.UG.bc (Lev.swapAE D) k.1)

theorem firstBlocks_mul (B : Base S T) (ψ : Twist D Circle) {a b : Bridge.Gf S} (ha : a ∈ B.levJ ψ) (hb : b ∈ B.levJ ψ) :
    firstBlocks B ψ (a * b) = firstBlocks B ψ a * firstBlocks B ψ b := by
  have pa := lev_le_parLev ha
  have pb := lev_le_parLev hb
  funext PP
  show upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) (a.1 * b.1))) =
    upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1)) * upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) b.1))
  have e : redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1 * Formalism.UG.bc (Lev.swapAE D) b.1) =
      redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1) * redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) b.1) :=
    extension_by_one_mul (St B.F.βS) (redAt B.F.βS PP.1) (Base.mem_St_of_mem_levJ ha) (Base.mem_St_of_mem_levJ hb)
  rw [map_mul, e]
  exact lowerRightBlock_mul_blockTriangular _ (blockTri_blkOf_le _ _ (parLev_g pa PP.2)) (blockTri_blkOf_le _ _ (parLev_g pb PP.2))

theorem mem_princ_iff (B : Base S T) (ψ : Twist D Circle) {k : Bridge.Gf S} (hk : k ∈ B.levJ ψ) :
    k ∈ (princ B).levJ ψ ↔ firstBlocks B ψ k = 1 :=
  ⟨fun h => Subgroup.mem_bot.1 h.2, fun h => ⟨mem_parLev.2 (by exact mem_parLev.1 hk.1), Subgroup.mem_bot.2 h⟩⟩

theorem exists_reps_levJ : ∀ {D : Formalism.BasicNotions.D7} {S T : Formalism.BasicNotions.TH.HSp D} (B : GlobalTheory.ExportSeries.Base S T), GlobalTheory.ExportSeries.Base.Good B → ∀ (ψ : GlobalTheory.ExportSeries.Twist D Circle), GlobalTheory.ExportSeries.Base.admitted B (GlobalTheory.ExportSeries.Twist.Q ψ) → ∃ (F : Finset ↥(Formalism.IndefR.Bridge.Gf S)), (∀ u ∈ F, u ∈ GlobalTheory.ExportSeries.Base.levJ B ψ) ∧ ∀ κ ∈ GlobalTheory.ExportSeries.Base.levJ B ψ, ∃! u : ↥(Formalism.IndefR.Bridge.Gf S), u ∈ F ∧ u⁻¹ * κ ∈ GlobalTheory.ExportSeries.Base.levJ (GlobalTheory.FlatVecSum.princ B) ψ := by
  intro D S T B _ ψ _
  refine exists_reps _ _ (firstBlocks B ψ) (B.G.P.H : Set _) (Set.finite_coe_iff.1 (finite_H B.G.P)) (fun κ hκ => hκ.2)
    fun u hu κ hκ => ?_
  have hm := mul_mem (inv_mem hu) hκ
  have e := firstBlocks_mul B ψ hu hm
  rw [mul_inv_cancel_left] at e
  rw [mem_princ_iff B ψ hm, e]
  exact left_eq_mul.symm

end GlobalTheory.FirstBlocksReduction

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.FlatVecSum

theorem princ_levJ_le_levLam_eq : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ hle : (GlobalTheory.FlatVecSum.princ B).levJ ψ ≤ B.levJ ψ, ∀ (k : Bridge.Gf S) (hk : k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ),
      (((GlobalTheory.FlatVecSum.princ B).levLam ψ ⟨k, hk⟩ : ℂˣ) : ℂ) = ((B.levLam ψ ⟨k, hle hk⟩ : ℂˣ) : ℂ) := by
  intro D S T B _ ψ _
  have hle : (GlobalTheory.FlatVecSum.princ B).levJ ψ ≤ B.levJ ψ := by
    intro k hk
    obtain ⟨h1, h2⟩ := hk
    refine ⟨h1, ?_⟩
    have h2' : Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _ ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) := h2
    rw [Subgroup.mem_bot.1 h2']
    exact Subgroup.one_mem _
  refine ⟨hle, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hk
  have h2' : Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _ ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) := h2
  have e := Subgroup.mem_bot.1 h2'
  show ((Formalism.L2.DIV.levFn B.F.βS ((GlobalTheory.FlatVecSum.princ B).levS ψ) _ : ℂˣ) : ℂ) =
    ((Formalism.L2.DIV.levFn B.F.βS (B.levS ψ) _ : ℂˣ) : ℂ)
  unfold Formalism.L2.DIV.levFn
  congr 2
  · congr 1
    · show Formalism.L2.DIV.ext1 (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) (⇑(1 : _ →* ℂˣ))
          (Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _) = Formalism.L2.DIV.ext1 B.G.P.H B.G.P.chi (Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) _)
      have key : ∀ y, y = Formalism.L2.DIV.rTup B.F.βS (B.levS ψ) ((Formalism.UG.bc (Lev.swapAE D)) ((finHom S).range.subtype k)) →
          Formalism.L2.DIV.ext1 (⊥ : Subgroup (Formalism.L2.DIV.G0 B.G.Pg T.rank)) (⇑(1 : _ →* ℂˣ)) y =
            Formalism.L2.DIV.ext1 B.G.P.H B.G.P.chi y := by
        rintro y rfl
        rw [e]
        exact (Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ (1 : _ →* ℂˣ)).trans (Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one B.G.P.H B.G.P.chi).symm
      exact key _ rfl

end GlobalTheory.FlatVecSum
end
