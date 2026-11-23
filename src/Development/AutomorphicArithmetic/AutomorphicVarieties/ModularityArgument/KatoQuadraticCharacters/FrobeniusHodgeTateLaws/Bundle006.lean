module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle253
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004

@[expose] public section

section

open UpperTheory.V.Z.Kato.Joint

section

open Formalism.ConjugateSelfDual GlobalTheory.KZ GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers UpperTheory.V.HV

variable {l : ℕ} [Fact l.Prime]

private theorem finSupp_comp_fop (k : ℕ) (χ : ℕ → Qbar l) (T : Letter)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (h : FinSupp lam) : FinSupp (lam ∘ₗ fop k l χ T) := by
  obtain ⟨S, hS⟩ := h
  cases T with
  | T q =>
    refine ⟨S.image (q * ·) ∪ S.image (· / q), fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show GlobalTheory.EisM.To k (χ q) q f n = 0
    have h1 : f (q * n) = 0 := hf _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
    have h2 : f (n / q) = 0 := hf _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
    simp [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, h1, h2]
  | U =>
    refine ⟨S.image (l * ·), fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show GlobalTheory.EisM.Uo l f n = 0
    exact hf _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  | D d =>
    refine ⟨S, fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show (χ d • f) n = 0
    simp [hf n hn]

private theorem finSupp_comp_lift (k : ℕ) (χ : ℕ → Qbar l) (P : FreeAlgebra (Qbar l) Letter) :
    ∀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l, FinSupp lam →
      FinSupp (lam ∘ₗ FreeAlgebra.lift (Qbar l) (fop k l χ) P) := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    intro lam h
    rw [AlgHom.commutes]
    have hr : lam ∘ₗ algebraMap (Qbar l) (Module.End (Qbar l) (ℕ → Qbar l)) r = r • lam := by
      ext f
      simp [Module.algebraMap_end_apply]
    rw [hr]
    exact FinSupp.smul h r
  | grade1 x =>
    intro lam h
    rw [FreeAlgebra.lift_ι_apply]
    exact finSupp_comp_fop k χ x lam h
  | mul a b ha hb =>
    intro lam h
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    exact hb _ (ha lam h)
  | add a b ha hb =>
    intro lam h
    rw [map_add (f := _), LinearMap.comp_add]
    exact FinSupp.add (ha lam h) (hb lam h)

private theorem exists_pow_mul_le (x : Qbar l) : ∃ k : ℕ, ‖((l : ℕ) : Qbar l) ^ k * x‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_le_l_pow l ‖x‖
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_l_pow]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  calc ((l : ℝ))⁻¹ ^ k * ‖x‖ ≤ ((l : ℝ))⁻¹ ^ k * (l : ℝ) ^ k := by gcongr
    _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl.ne', one_pow]

end

open Formalism.ConjugateSelfDual GlobalTheory.KZ GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers UpperTheory.V.HV in
theorem UpperTheory.V.Z.Kato.Joint.finP :
    UpperTheory.V.Z.Kato.Joint.FinP := by
  classical
  intro hub l _ ι k N B cc χE c₀ P _
  let lam₀ : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l :=
    ∑ n ∈ Finset.range B, ι.symm (cc n) • LinearMap.proj n
  have hlam₀ : ∀ a : ℕ → Qbar l, lam₀ a = ι.symm (GlobalTheory.EisM.lam B cc fun i => ι (a i)) := by
    intro a

    simp [lam₀, GlobalTheory.EisM.lam, map_sum, map_mul, LinearMap.sum_apply]
  have hfs₀ : FinSupp lam₀ := by
    refine ⟨Finset.range B, fun f hf => ?_⟩
    rw [hlam₀, GlobalTheory.EisM.lam, Finset.sum_eq_zero, map_zero]
    intro n hn
    simp [hf n hn]
  let lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l := lam₀ ∘ₗ FreeAlgebra.lift (Qbar l) (fop k l χE) P
  have hfs : FinSupp lam := finSupp_comp_lift k χE P lam₀ hfs₀
  obtain ⟨S, hS⟩ := hfs
  choose e he using exists_pow_mul_le (l := l)
  let g : ℕ → Qbar l := fun i => ((l : ℕ) : Qbar l) ^ e (lam (Pi.single i 1)) * lam (Pi.single i 1)
  obtain ⟨c, hc₀, -, hcF⟩ := hub l c₀ c₀ (S.image g) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact he _)
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨lam₀, lam, c, hc₀, hfs₀, ⟨S, hS⟩, ?_, hlam₀, fun a => rfl⟩
  intro i σ hσ _
  by_cases hi : i ∈ S
  · have hy := hσ _ (hcF _ (Finset.mem_image_of_mem g hi))
    have hne : ((l : ℕ) : Qbar l) ^ e (lam (Pi.single i 1)) ≠ 0 := by
      intro h0
      have h1 := congrArg norm h0
      rw [norm_l_pow, norm_zero] at h1
      exact pow_ne_zero _ (inv_ne_zero hl.ne') h1
    simp only [g, map_mul, map_pow, map_natCast] at hy
    exact mul_left_cancel₀ hne hy
  · have h0 : lam (Pi.single i 1) = 0 :=
      hS _ (fun s hs => Pi.single_eq_of_ne (by rintro rfl; exact hi hs) 1)
    rw [h0, map_zero]
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

variable {l : ℕ} [Fact l.Prime]

private theorem cgp_refl (n : ℕ) (x : Qbar l) : Cg n x x := by simp [Cg]

private theorem cgp_symm {n : ℕ} {x y : Qbar l} (h : Cg n x y) : Cg n y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

private theorem cgp_add {n : ℕ} {x y x' y' : Qbar l} (h : Cg n x y) (h' : Cg n x' y') : Cg n (x + x') (y + y') := by
  unfold Cg at *
  rw [add_sub_add_comm]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cgp_trans {n : ℕ} {x y z : Qbar l} (h : Cg n x y) (h' : Cg n y z) : Cg n x z := by
  unfold Cg at *
  rw [← sub_add_sub_cancel x y z]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cgp_mul {n : ℕ} {a x y : Qbar l} (ha : ‖a‖ ≤ 1) (h : Cg n x y) : Cg n (a * x) (a * y) := by
  simpa using cg_mul_left (k := 0) (Nat.zero_le _) (by simpa using ha) h

private theorem fop_cg {k n : ℕ} {χ : ℕ → Qbar l} (hχ : ∀ d, ‖χ d‖ ≤ 1) (T : Letter) {f g : ℕ → Qbar l}
    (h : ∀ i, Cg n (f i) (g i)) (i : ℕ) : Cg n (fop k l χ T f i) (fop k l χ T g i) := by
  cases T with
  | T q =>
    show Cg n (GlobalTheory.EisM.To k (χ q) q f i) (GlobalTheory.EisM.To k (χ q) q g i)
    unfold GlobalTheory.EisM.To GlobalTheory.EisM.Vo
    refine cgp_add (h _) (cgp_mul ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ (hχ q) (by positivity)
        (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))
    · split_ifs
      · exact h _
      · exact cgp_refl _ _
  | U => exact h _
  | D d => exact cgp_mul (hχ d) (h i)

theorem thP : ThP := by
  intro hOp hStab l _ Ω _ _ _ ε X A N w j χ hS P hP
  set F := FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) with hF
  set G := FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) with hG
  have hχ : ∀ d, ‖((χ d : ℤ_[l]) : Qbar l)‖ ≤ 1 := fun d => by
    rw [norm_algebraMap']
    exact (χ d).2
  have hw : ∀ x ∈ Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}), ∀ n : ℕ,
      (∀ f g : ℕ → Qbar l, (∀ i, Cg n (f i) (g i)) → ∀ i, Cg n (F x f i) (F x g i)) ∧
      ∀ b, InChi X N w χ b → ∃ b', InChi X N w χ b' ∧
        G x ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) = (1 : Qbar l) ⊗ₜ[ℤ_[l]] b' ∧
        ∀ i, Cg n (F x (th X A N j n b) i) (th X A N j n b' i) := by
    intro x hx n
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨T, hT, rfl⟩ := hx
      rw [hF, hG, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
      refine ⟨fun f g h i => fop_cg hχ T h i, fun b hb => ⟨X.op N l T b,
        hStab l Ω ε X N w χ hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 T b hT hb, ?_,
        fun i => cgp_symm (hOp l Ω ε X A N w j χ hS n T b hT hb i)⟩⟩
      rw [Tower.opV, LinearMap.baseChange_tmul]
    | one =>
      rw [map_one, map_one]
      exact ⟨fun f g h i => h i, fun b hb => ⟨b, hb, rfl, fun i => cgp_refl _ _⟩⟩
    | mul x y _ _ hx hy =>
      rw [map_mul, map_mul]
      refine ⟨fun f g h i => hx.1 _ _ (hy.1 f g h) i, fun b hb => ?_⟩
      obtain ⟨b', hb', e', c'⟩ := hy.2 b hb
      obtain ⟨b'', hb'', e'', c''⟩ := hx.2 b' hb'
      refine ⟨b'', hb'', ?_, fun i => cgp_trans (hx.1 _ _ c' i) (c'' i)⟩
      rw [Module.End.mul_apply, e', e'']
  have hP' : P ∈ Submodule.span (Qbar l)
      (Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}) : Set (FreeAlgebra (Qbar l) Letter)) := by
    rw [← Algebra.adjoin_eq_span]
    exact hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun n _ Θ hΘ b hb i => ?_⟩
    obtain ⟨b', hb', e', c'⟩ := (hw x hx n).2 b hb
    rw [e', Nat.sub_zero]
    exact cgp_trans (c' i) (cgp_symm (hΘ b' hb'.1 i))
  | zero =>
    refine ⟨0, fun n _ Θ hΘ b hb i => ?_⟩
    simp only [map_zero, LinearMap.zero_apply]
    exact cgp_refl _ _
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, fun n hn Θ hΘ b hb i => ?_⟩
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
    exact cgp_add (cg_mono (by omega) (hc n (by omega) Θ hΘ b hb i))
      (cg_mono (by omega) (hd n (by omega) Θ hΘ b hb i))
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨k, hk⟩ := exists_le_l_pow l ‖a‖
    refine ⟨c + k, fun n hn Θ hΘ b hb i => ?_⟩
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Nat.sub_sub]
    exact cg_mul_left (by omega) hk (hc n (by omega) Θ hΘ b hb i)

end UpperTheory.V.Z.Kato.Joint

end
end

section

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.chiStab :
    UpperTheory.V.Z.Kato.Joint.ChiStab := by
  intro l hp Ω _ _ _ ε X N w χ hl hlN hN hw T b hT hb
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hlN).symm
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  refine ⟨GlobalTheory.T.hecke_letter_preserves_basis_set ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T hT b hb.1, fun d hd => ?_⟩
  have h := GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T (GlobalTheory.KZ.Letter.D d) hT hd b hb.1
  change X.op N l T (X.diam N l d b) = X.diam N l d (X.op N l T b) at h
  rw [← h, hb.2 d hd, map_smul]
end

section

open UpperTheory.V.Z.Kato.Joint

private theorem formP_lam_add (B : ℕ) (cc a b : ℕ → ℂ) :
    GlobalTheory.EisM.lam B cc (a + b) = GlobalTheory.EisM.lam B cc a + GlobalTheory.EisM.lam B cc b := by
  unfold GlobalTheory.EisM.lam
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem formP_lam_smul (B : ℕ) (cc a : ℕ → ℂ) (r : ℂ) :
    GlobalTheory.EisM.lam B cc (r • a) = r * GlobalTheory.EisM.lam B cc a := by
  unfold GlobalTheory.EisM.lam
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem UpperTheory.V.Z.Kato.Joint.LocFacts₂ :
    UpperTheory.V.Z.Kato.Joint.FormP := by
  unfold UpperTheory.V.Z.Kato.Joint.FormP
  intro l _ ι k N χ t α B cc χE ev hk hE hχE hT hU hD P hP
  have hℓ : Nat.Prime l := Fact.out
  suffices key : ∀ a : ℕ → Formalism.ConjugateSelfDual.Qbar l,
      GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) →
      GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ)
                   (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) ∧
        (GlobalTheory.EisM.lam B cc fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) =
          ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) ev) P) * GlobalTheory.EisM.lam B cc fun i => ι (a i) from
    fun a ha => (key a ha).2
  unfold GlobalTheory.KZ.admissibleLettersSubalgebra at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    intro a ha
    simp only [FreeAlgebra.lift_ι_apply]
    cases x with
    | T q =>
      obtain ⟨hq, hqn⟩ : Nat.Prime q ∧ ¬q ∣ N * l := hx
      have hcop : q.Coprime N :=
        Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn)
      have hχq : ι (χE q) = GlobalTheory.EisM.ch χ (q : ℤ) := by
        rw [hχE q hcop]
        simp [GlobalTheory.EisM.ch]
      have hf : (fop k l χE (GlobalTheory.KZ.Letter.T q)) a = GlobalTheory.EisM.To k (χE q) q a := rfl
      have hcomm : (fun i => ι (GlobalTheory.EisM.To k (χE q) q a i)) =
          GlobalTheory.EisM.To k (GlobalTheory.EisM.ch χ (q : ℤ)) q (fun i => ι (a i)) := by
        funext m
        simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, map_add (f := _), map_mul, map_pow, map_natCast, hχq]
        split_ifs <;> simp
      rw [hf, hcomm]
      refine ⟨GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ _ hk (dvd_mul_right N l) hq hqn ha, ?_⟩
      rw [hE.T _ ha q hq hqn, hT q hq hqn]
    | U =>
      have hf : (fop k l χE GlobalTheory.KZ.Letter.U) a = GlobalTheory.EisM.Uo l a := rfl
      have hcomm : (fun i => ι (GlobalTheory.EisM.Uo l a i)) = GlobalTheory.EisM.Uo l (fun i => ι (a i)) := rfl
      rw [hf, hcomm]
      refine ⟨(GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l _ (fun i => ι (a i)) hk hℓ (dvd_mul_left l N) ?_ ha).1, ?_⟩
      · intro d
        simp [GlobalTheory.EisM.ch]
      · rw [hE.U _ ha, hU]
    | D d =>
      have hd : d.Coprime N := hx
      have hf : (fop k l χE (GlobalTheory.KZ.Letter.D d)) a = χE d • a := rfl
      have hcomm : (fun i => ι ((χE d • a) i)) = ι (χE d) • fun i => ι (a i) := by
        funext i
        simp
      rw [hf, hcomm, formP_lam_smul, hD d hd]
      exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.2.1 _ _ ha).1, rfl⟩
  | algebraMap r =>
    intro a ha
    have hf : (FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) (algebraMap (Formalism.ConjugateSelfDual.Qbar l) _ r) a = r • a := by
      simp [Algebra.algebraMap_eq_smul_one]
    have hcomm : (fun i => ι ((r • a) i)) = ι r • fun i => ι (a i) := by
      funext i
      simp
    rw [hf, hcomm, formP_lam_smul, AlgHom.commutes]
    exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.2.1 _ _ ha).1, rfl⟩
  | add x y _ _ hx hy =>
    intro a ha
    obtain ⟨h1, h2⟩ := hx a ha
    obtain ⟨h3, h4⟩ := hy a ha
    have hcomm : (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE) (x + y)) a i)) =
        (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) x) a i)) +
          (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) y) a i)) := by
      funext i
      simp
    rw [hcomm, formP_lam_add, h2, h4, map_add (f := _), map_add (f := _), add_mul]
    exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.1 _ _ h1 h3).1, rfl⟩
  | mul x y _ _ hx hy =>
    intro a ha
    obtain ⟨h3, h4⟩ := hy a ha
    obtain ⟨h1, h2⟩ := hx _ h3
    simp only [map_mul, Module.End.mul_apply]
    refine ⟨h1, ?_⟩
    rw [h2, h4, mul_assoc]
end

section

open UpperTheory.V.Z.Kato.Joint

private noncomputable def avg {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (δ : ℕ → PadicAlgCl l) (a b : ℤ) : ℕ → PadicAlgCl l :=
  fun i => ∑ u : (ZMod N)ˣ, δ (u : ZMod N).val * ser ι N θ m k ψ (((u : ZMod N).val : ℤ) * a) (((u : ZMod N).val : ℤ) * b) i

private theorem expand {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (δ : ℕ → PadicAlgCl l) (c d : ℤ) :
    (GlobalTheory.KummerEisensteinGalois.up (l ^ m) fun i => ∑ x : ZMod N, ι.symm (GlobalTheory.EisM.hat θ (x.val : ℤ) / 2) *
                 GlobalTheory.LambdaValuationPowers.chiProj N l m k ψ δ c d (x.val : ℤ) i) =
      ((c : PadicAlgCl l) ^ 2 * (d : PadicAlgCl l) ^ 2) • avg ι N θ m k ψ δ 1 1
      - ((c : PadicAlgCl l) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (l ^ m)) * (d : PadicAlgCl l) ^ 2) • avg ι N θ m k ψ δ c 1
      - ((c : PadicAlgCl l) ^ 2 * (d : PadicAlgCl l) * ψ⁻¹ (d : ZMod (l ^ m))) • avg ι N θ m k ψ δ 1 d
      + ((c : PadicAlgCl l) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (l ^ m)) * (d : PadicAlgCl l) * ψ⁻¹ (d : ZMod (l ^ m))) •
          avg ι N θ m k ψ δ c d := by
  funext i
  simp only [GlobalTheory.KummerEisensteinGalois.up, avg, ser, GlobalTheory.LambdaValuationPowers.chiProj, GlobalTheory.LambdaValuationPowers.coPtSb, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_one]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => ?_
  rw [show c * ((x.val : ℤ) * ((u : ZMod N).val : ℤ)) = (x.val : ℤ) * (((u : ZMod N).val : ℤ) * c) by ring,
    mul_comm d ((u : ZMod N).val : ℤ)]
  ring

private theorem sum_units {K : Type} [Field K] (n : ℕ) [NeZero n] (ψ : DirichletCharacter K n) (f : ZMod n → K) :
    ∑ a : ZMod n, ψ a * f a = ∑ b : (ZMod n)ˣ, ψ b * f b := by
  classical
  symm
  refine Finset.sum_bij_ne_zero (fun b _ _ => (b : ZMod n)) (fun _ _ _ => Finset.mem_univ _)
    (fun a _ _ b _ _ h => Units.ext h) (fun a _ h => ?_) (fun _ _ _ => rfl)
  have ha : IsUnit a := by
    by_contra hn
    exact h (by rw [MulChar.map_nonunit _ hn, zero_mul])
  obtain ⟨b, rfl⟩ := ha
  exact ⟨b, Finset.mem_univ _, h, rfl⟩

private theorem cop_unit (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a : ℤ) (ha : IsCoprime a N) :
    IsCoprime (((u : ZMod N).val : ℤ) * a) N :=
  (Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)).mul_left ha

theorem UpperTheory.V.Z.Kato.Joint.rhsEq :
    UpperTheory.V.Z.Kato.Joint.RhsEq := by
  intro hE hM l _ ι e N _ θ χ t α B cc c d δ lam κ' κ v hl he hlN hχ hα hc hd hEig hδ hlam m hm ψ z
  have hk3 : 3 ≤ 2 * e + 1 := by omega
  have hodd : Odd (2 * e + 1) := ⟨e, rfl⟩
  have hc' : IsCoprime (c : ℤ) N := Nat.isCoprime_iff_coprime.2 hc
  have hd' : IsCoprime (d : ℤ) N := Nat.isCoprime_iff_coprime.2 hd
  have h1 : IsCoprime (1 : ℤ) N := isCoprime_one_left
  unfold rhs5
  rw [expand ι N θ m (2 * e + 1) ψ δ c d]
  split_ifs with hpar
  · have hpar' : ι (ψ (-1)) = θ (-1) := by rw [hpar, RingEquiv.apply_symm_apply]
    have hf : ∀ y : ZMod (l ^ m), ι (ψ (-y)) = θ (-1) * ι (ψ y) := fun y => by
      rw [← hpar', ← map_mul, ← map_mul, neg_one_mul]
    obtain ⟨hMF, hval⟩ := hM (2 * e + 1) l N m θ χ (fun y => ι (ψ y)) t α B cc Fact.out hk3 hodd (NeZero.pos N) hlN hm hχ hf hα hEig
    set F := frm l N m (2 * e + 1) θ (θ * χ) (fun y => ι (ψ y)) with hF
    set μ := GlobalTheory.EisM.mesMu (2 * e + 1) l (GlobalTheory.EisM.hat θ) (GlobalTheory.EisM.tw2 N (θ (-1))) α B cc m (fun y => ι (ψ y)) with hμ
    have hG : (fun i => ι ((fun i => ι.symm (F i)) i)) = F := by
      funext i; simp
    have hlG : 2 * lam (fun i => ι.symm (F i)) = κ' * (N.totient : PadicAlgCl l) * ι.symm α ^ m * ι.symm μ := by
      have h2 := congrArg ι.symm hval
      rw [map_mul, map_mul, map_mul, map_pow, map_natCast, map_ofNat] at h2
      rw [hlam _ (by rw [hG]; exact hMF), hG]
      linear_combination κ' * h2
    have hav : ∀ a b : ℤ, IsCoprime a N → IsCoprime b N → lam (avg ι N θ m (2 * e + 1) ψ δ a b) =
        ι.symm (θ (a : ZMod N)) * ι.symm ((θ * χ)⁻¹ (b : ZMod N)) *
          (κ' * (N.totient : PadicAlgCl l) * ι.symm α ^ m * ι.symm μ) := by
      intro a b ha hb
      have h3 := (hE l ι N θ χ m (2 * e + 1) ψ a b hl hm hk3 hodd hχ ha hb).2.2 hpar'
      have : avg ι N θ m (2 * e + 1) ψ δ a b =
          (2 * ι.symm (θ (a : ZMod N)) * ι.symm ((θ * χ)⁻¹ (b : ZMod N))) • fun i => ι.symm (F i) := by
        funext i
        apply ι.injective

        simp only [avg, Pi.smul_apply, smul_eq_mul, map_mul, map_sum, RingEquiv.apply_symm_apply, map_ofNat]
        rw [← h3 i]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hδ _ (ZMod.val_coe_unit_coprime u), ZMod.natCast_zmod_val]
      rw [this, map_smul, smul_eq_mul, ← hlG]
      ring
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [sum_units (l ^ m) ψ (fun a => z ^ a.val)]
    simp only [map_add (f := _), map_sub, map_smul, smul_eq_mul, hav _ _ h1 h1, hav _ _ hc' h1, hav _ _ h1 hd', hav _ _ hc' hd',
      Fin.sum_univ_four, smB, smT, Int.cast_natCast, Int.cast_one, map_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Nat.cast_mul, map_mul]
    ring
  · have hpar' : ι (ψ (-1)) ≠ θ (-1) := fun h => hpar (by rw [← h, RingEquiv.symm_apply_apply])
    have hav : ∀ a b : ℤ, IsCoprime a N → IsCoprime b N → avg ι N θ m (2 * e + 1) ψ δ a b = 0 := by
      intro a b ha hb
      funext i
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [(hE l ι N θ χ m (2 * e + 1) ψ _ _ hl hm hk3 hodd hχ (cop_unit N u a ha) (cop_unit N u b hb)).1 hpar']
      simp
    rw [hav _ _ h1 h1, hav _ _ hc' h1, hav _ _ h1 hd', hav _ _ hc' hd']
    simp
end
