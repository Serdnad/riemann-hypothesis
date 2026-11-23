module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle001
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.EvalSmulCong
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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

@[expose] public section

section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem term {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n N : ℕ) (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (f : X.Kˣ) (c : ℕ) (k k' : ℤ_[l]) (h : (l : ℤ_[l]) ^ n ∣ k * c - k') :
    AdicCompletion.eval (idl l) (X.Kl l) n (k • clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
      X.kmap l (X.gal s) (k' • clsK X l n (slD X N (f : X.K)))) = 0 := by
  obtain ⟨hRep, -, hPow, hUniq, hMap, -, -⟩ := sCls Ω ε X l n
  obtain ⟨hGalSl, -⟩ := sSlD Ω ε X N hN
  have hApi := (sApi Ω ε X l n).2.2.2.2.1
  have hmul : ∀ a b : X.K, slD X N (a * b) = slD X N a * slD X N b := by
    intro a b
    simp [slD]
  have h1 : slD X N 1 = 1 := by simp [slD]
  have hpow : ∀ (a : X.K) (m : ℕ), slD X N (a ^ m) = slD X N a ^ m := by
    intro a m
    simp [slD]
  let U : X.Kˣ → X.Kˣ := fun u =>
    ⟨slD X N u, slD X N ↑u⁻¹, by rw [← hmul]; simp [h1], by rw [← hmul]; simp [h1]⟩
  have hA := hRep (U (galU X s f ^ c))
  have hB := hPow _ _ c (hMap (X.gal s) _ _ (hRep (U f)))
  have heq : (Units.map (X.gal s : X.K →* X.K) (U f)) ^ c = U (galU X s f ^ c) := by
    ext
    simp only [U, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [hpow, hGalSl]
    rfl
  rw [heq] at hB
  have hc : Cgr (l ^ n) (U (galU X s f ^ c)) (U (galU X s f ^ c)) := by
    first | rfl | exact ⟨1, by simp⟩ | simp [Cgr]
  have hz := hUniq _ _ _ _ hA hB hc
  rw [map_smul]
  have hsplit : k • clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
      k' • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K))) =
      k • (clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
        (c : ℤ_[l]) • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K)))) +
      ((k * c) • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K))) -
        k' • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K)))) := by
    rw [smul_sub, smul_smul]
    abel
  rw [hsplit, map_add (f := _), map_smul, hApi (k * c) k' _ h, add_zero]
  convert smul_zero k using 2

private theorem dvd_iff (l : ℕ) [Fact l.Prime] (n : ℕ) (k k' : ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣ k - k' ↔ PadicInt.toZModPow n k = PadicInt.toZModPow n k' := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

private theorem val_cast {M M' : ℕ} [NeZero M] (h : M' ∣ M) (z : ZMod M) :
    ((z.val : ℕ) : ZMod M') = ZMod.castHom h (ZMod M') z := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private noncomputable def dg {M : ℕ} (d : (ZMod M)ˣ) : GL (Fin 2) (ZMod M) :=
  ⟨!![1, 0; 0, (d : ZMod M)], !![1, 0; 0, ((d⁻¹ : (ZMod M)ˣ) : ZMod M)],
    by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

theorem UpperTheory.V.Z.Kato.Nb.sXiTw :
    UpperTheory.V.Z.Kato.Nb.SXiTw := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y P a s
  have hM0 : M₀ ∣ M := hL.eq ▸ Dvd.intro_left N rfl
  have hlM : l ^ n ∣ M := hL.dl.trans hM0
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨-, -, -, -, -, -, -, hcyc⟩ := sSlD Ω ε X N hN
  have hone : ∀ (K : ℕ) [NeZero K], cycM K (1 : Gal(Ω/ℚ)) = 1 := by
    intro K _
    have h := (hcyc K 1).2.1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hinv : ∀ (K : ℕ) [NeZero K], cycM K s⁻¹ = (cycM K s)⁻¹ := by
    intro K _
    rw [eq_inv_iff_mul_eq_one, ← (hcyc K s⁻¹).2.1 s, inv_mul_cancel, hone]
  set d := cycM M s with hd
  have hcd : ZMod.castHom hM0 (ZMod M₀) ((d⁻¹ : (ZMod M)ˣ) : ZMod M) = cyc M₀ s⁻¹ := by
    rw [(hcyc M₀ s⁻¹).1, ← ((hcyc M s⁻¹).2.2.2.2 M₀ hM0), hinv M]
    rfl
  have hgr : ∀ (z : Row M₀) (m : GL (Fin 2) (ZMod M)),
      gr M₀ s⁻¹ (z ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) =
        z ᵥ* cD N M₀ ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    intro z m
    ext i
    fin_cases i
    · simp [gr, cD, dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    · simp [gr, cD, dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, val_cast hM0, ← hcd]
      rw [ZMod.cast_mul hM0, ZMod.cast_mul hM0]
      ring
  unfold Xi UpperTheory.Kd.K4.CgF
  intro u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]

  rw [Finset.sum_filter, Finset.sum_filter, map_sum, map_sub, sub_eq_zero]
  conv_rhs => rw [← Fintype.sum_equiv (Equiv.mulRight (dg d⁻¹)) _ _ (fun _ => rfl)]

  rw [← sub_eq_zero, ← map_sub, ← Finset.sum_sub_distrib, map_sum]
  apply Finset.sum_eq_zero
  intro m _
  simp only [Equiv.coe_mulRight]
  have hdet : Matrix.GeneralLinearGroup.det (m * dg d⁻¹) = Matrix.GeneralLinearGroup.det m * d⁻¹ := by
    rw [map_mul]
    congr 1
    ext
    simp [dg, Matrix.det_fin_two, Matrix.GeneralLinearGroup.val_det_apply]
  have hent : ∀ i, ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) i 0 =
      (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 0 ∧
      ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) i 1 =
      (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 1 * ((d⁻¹ : (ZMod M)ˣ) : ZMod M) := by
    intro i
    simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  have hC : Cnd l N g ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) ↔
      Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    unfold Cnd
    rw [(hent 1).1, (hent 0).1]
  have hP : Matrix.GeneralLinearGroup.det m * d⁻¹ * d = Matrix.GeneralLinearGroup.det m := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  simp only [hdet, hP]
  by_cases h : Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧ P (Matrix.GeneralLinearGroup.det m)
  · rw [if_pos h, if_pos ⟨hC.2 h.1, h.2⟩]
    unfold tw
    rw [hgr x m, hgr y m]
    refine term X l n N hN s _ _ _ _ ?_
    rw [dvd_iff]
    simp only [map_sub, map_mul, map_pow, map_add (f := _), map_natCast, (hent 0).1, (hent 0).2]
    have hdl : Units.map (ZMod.castHom hlM (ZMod (l ^ n)) : ZMod M →* ZMod (l ^ n)) d = cycM (l ^ n) s :=
      (hcyc M s).2.2.2.2 (l ^ n) hlM
    have hχ : PadicInt.toZModPow n (((cyclotomicCharacter Ω l) s.toRingEquiv : ℤ_[l]ˣ) : ℤ_[l]) =
        ZMod.castHom hlM (ZMod (l ^ n)) (d : ZMod M) := by
      rw [(dvd_iff l n _ _).1 (sCycZ Ω l n s).2, map_natCast, ZMod.natCast_zmod_val, ← hdl]
      rfl
    have hc : (((cyc (l ^ n) s).val : ℕ) : ZMod (l ^ n)) = ZMod.castHom hlM (ZMod (l ^ n)) (d : ZMod M) := by
      rw [ZMod.natCast_zmod_val, (hcyc (l ^ n) s).1, ← hdl]
      rfl
    simp only [hc, hχ, val_cast hlM, Units.val_mul, mul_inv_rev, inv_inv, map_mul]
    clear hcyc hgr hcd hC hP hdl hone hinv hent hdet h
    set φ := ZMod.castHom hlM (ZMod (l ^ n))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, map_mul, hχ]
    have hdd : φ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) * φ (d : ZMod M) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have key : φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * φ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) *
        (φ (d : ZMod M) * PadicInt.toZModPow n (u 1)) =
        φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1) := by
      linear_combination (φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1)) * hdd
    rw [key]
    ring
  · rw [if_neg h, if_neg (fun h' => h ⟨hC.1 h'.1, h'.2⟩), map_zero, sub_zero, map_zero]
end

section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem gam_mono {M M' : ℕ} (h : M ∣ M') : CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨a, b, c, d⟩ := hγ
  have e := fun (x : ℤ) (y : ZMod M') (hh : (x : ZMod M') = y) => congrArg (ZMod.castHom h (ZMod M)) hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_intCast, map_one] using e _ _ a
  · simpa only [map_intCast, map_zero] using e _ _ b
  · simpa only [map_intCast, map_zero] using e _ _ c
  · simpa only [map_intCast, map_one] using e _ _ d

private theorem gam_le {M N l : ℕ} (hN : N ∣ M) (hl : l ∣ M) : CongruenceSubgroup.Gamma M ≤ Gam N l := by
  intro γ hγ
  have h1 := gam_mono hN hγ
  have h2 := gam_mono hl hγ
  rw [CongruenceSubgroup.Gamma_mem] at h1 h2
  refine ⟨?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma1_mem _ _).2 ⟨h1.1, h1.2.2.2, h1.2.2.1⟩
  · exact CongruenceSubgroup.Gamma0_mem.2 h2.2.2.1

private theorem mem_gam_iff (M : ℕ) (a b : SL(2, ℤ)) : a * b⁻¹ ∈ CongruenceSubgroup.Gamma M ↔
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) a = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) b := by
  rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, mul_inv_eq_one]

private theorem map_liftSL (M : ℕ) (γ : SL(2, ZMod M)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M γ) = γ :=
  Classical.epsilon_spec (GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) M γ)

private theorem isTr_img {M N l : ℕ} [NeZero M] (hN : N ∣ M) (hl : l ∣ M) :
    IsTr (CongruenceSubgroup.Gamma M) (Gam N l) (fun γ : {γ // γ ∈ img (Gam N l) M} => liftSL M γ.1) := by
  refine ⟨fun γ => ?_, fun δ hδ => ?_⟩
  · obtain ⟨δ, hδ, e⟩ := (Finset.mem_filter.1 γ.2).2
    have h1 : liftSL M γ.1 * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [mem_gam_iff, map_liftSL, e]
    have h2 := mul_mem (gam_le hN hl h1) hδ
    simpa using h2
  · refine ⟨⟨Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, δ, hδ, rfl⟩⟩, ?_, fun γ hγ => ?_⟩
    · show _ ∈ _
      rw [mem_gam_iff, map_liftSL]
    · have h1 : δ * (liftSL M γ.1)⁻¹ ∈ CongruenceSubgroup.Gamma M := hγ
      rw [mem_gam_iff, map_liftSL] at h1
      exact Subtype.ext h1.symm

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem recip_mod [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {σ : Ω ≃ₐ[ℚ] Ω} (hσ : σ ∈ fixMu Ω M)
    (f : X.K) (h : SL(2, ℤ)) : ∃ δ ∈ CongruenceSubgroup.Gamma M,
      X.gal σ (X.sl (ofSL (δ * h)) f) = X.sl (ofSL h) (X.gal σ f) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨M0, hM0, hf⟩ := X.level f
  have hM' : M0 * M ≠ 0 := mul_ne_zero hM0.ne' hM
  haveI : NeZero (M0 * M) := ⟨hM'⟩
  have hζ := isPrimitiveRoot_eOm ε hM'
  set ζ := eOm ε (1 / ((M0 * M : ℕ) : ℚ)) with hζd
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ⁻¹ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hmod : ∀ a b : ℕ, ζ ^ a = ζ ^ b → a ≡ b [MOD M0 * M] := fun a b hab => by
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder hM').pow_eq_pow_iff_modEq.1 hab
  have hij : (i : ZMod (M0 * M)) * j = 1 := by
    have : ζ ^ (i * j) = ζ ^ 1 := by
      rw [pow_mul, hi, ← map_pow, hj, pow_one, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hmod _ _ this)
    simpa using h2
  have hi1 : (i : ZMod M) = 1 := by
    have h1 : σ (ζ ^ M0) = ζ ^ M0 := (mem_fixMu_iff σ).1 hσ _ (by rw [← pow_mul, hζ.pow_eq_one])
    have : ζ ^ (M0 * i) = ζ ^ (M0 * 1) := by
      rw [mul_one, mul_comm, pow_mul, hi, ← map_pow, h1]
    have h2 := Nat.ModEq.mul_left_cancel' hM0.ne' (hmod _ _ this)
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
  let φ := ZMod.castHom (dvd_mul_left M M0) (ZMod M)
  have hj1 : (j : ZMod M) = 1 := by
    have := congrArg φ hij
    rwa [map_mul, map_natCast, map_natCast, map_one, hi1, one_mul] at this
  have hdet : en h 0 0 * en h 1 1 - en h 0 1 * en h 1 0 = 1 := by
    have := h.2
    rwa [Matrix.det_fin_two] at this
  have hdet' : (en h 0 0 : ZMod (M0 * M)) * en h 1 1 - en h 0 1 * en h 1 0 = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod (M0 * M)) hdet
  obtain ⟨γ, hγ⟩ := GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) (M0 * M)
    ⟨!![(en h 0 0 : ZMod (M0 * M)), j * en h 0 1; i * en h 1 0, en h 1 1], by
      rw [Matrix.det_fin_two_of]; linear_combination hdet' - (en h 0 1 : ZMod (M0 * M)) * (en h 1 0) * hij⟩
  have e : ∀ a b, (en γ a b : ZMod (M0 * M)) =
      !![(en h 0 0 : ZMod (M0 * M)), j * en h 0 1; i * en h 1 0, en h 1 1] a b := fun a b =>
    congrArg (fun m : SL(2, ZMod (M0 * M)) => m.1 a b) hγ
  have e00 : (en γ 0 0 : ZMod (M0 * M)) = en h 0 0 := e 0 0
  have e01 : (en γ 0 1 : ZMod (M0 * M)) = j * en h 0 1 := e 0 1
  have e10 : (en γ 1 0 : ZMod (M0 * M)) = i * en h 1 0 := e 1 0
  have e11 : (en γ 1 1 : ZMod (M0 * M)) = en h 1 1 := e 1 1
  refine ⟨γ * h⁻¹, ?_, ?_⟩
  · rw [mem_gam_iff]
    have f00 := congrArg φ e00
    have f01 := congrArg φ e01
    have f10 := congrArg φ e10
    have f11 := congrArg φ e11
    simp only [map_mul, map_intCast, map_natCast, hi1, hj1, one_mul] at f00 f01 f10 f11
    ext a b
    fin_cases a <;> fin_cases b
    exacts [f00, f01, f10, f11]
  · rw [inv_mul_cancel_right]
    refine X.recip (M0 * M) f (Nat.pos_of_ne_zero hM') (fun δ hδ => hf δ (gam_mono (dvd_mul_right _ _) hδ)) ζ hζ σ i
      (by rw [zpow_natCast, hi]) γ h ⟨e00.symm, ?_, ?_, e11.symm⟩
    · rw [e01, Int.cast_natCast, ← mul_assoc, hij, one_mul]
    · rw [e10, Int.cast_natCast]

private theorem trM_eq [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (x : X.Khat l) :
    trM X l N M w g x = trH X l w (fun γ : {γ // γ ∈ img (Gam N l) M} => liftSL M γ.1) ![en g 0 0, en g 0 1]
      (X.kmap l (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv x) := by
  unfold trM trH
  rw [← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Tower.act_act Ω ε X l _ _ (by simp) (by simp)]
  congr 1
  funext u
  simp [Tower.act, sec, mZl, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sTrM :
    UpperTheory.V.Z.Kato.Nb.STrM := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW a ha hI
  have hlp : l.Prime := Fact.out
  have hNM : N ∣ M := hL.eq ▸ dvd_mul_right _ _
  have hnM : l ^ n ∣ M := hL.eq ▸ hL.dl.mul_left _
  have hlM : l ∣ M := (dvd_pow_self l (by have := hL.pos; omega)).trans hnM
  obtain ⟨hE, hAdd, -, hSum, hDv, -⟩ := sApi Ω ε X l n
  obtain ⟨hR, -, -, hCg, hMap, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, hTo, -, hUn, -, -, hCy⟩ := sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))
  refine ⟨?_, fun σ hσ => ?_⟩
  · have hle : CongruenceSubgroup.Gamma M ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) :=
      le_inf (gam_le hNM hlM) (gam_mono hnM)
    have hT := isTr_img (l := l) hNM hlM
    have hRep : Rep X l n (slU X (ofSL g) a)
        (X.kmap l (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (a : X.K))) := by
      rw [hTo]; exact hMap _ _ _ (hR a)
    have hU := hUn _ (ofSL g) a ha
    have hH : InvH X (CongruenceSubgroup.Gamma M) (l ^ n) (slU X (ofSL g) a) := by
      intro γ hγ
      obtain ⟨k, hk⟩ := hI _ ((CongruenceSubgroup.Gamma_normal M).conj_mem γ hγ g)
      refine ⟨slU X (ofSL g) k, ?_⟩
      show X.sl (ofSL γ) (X.sl (ofSL g) a) = X.sl (ofSL g) a * (X.sl (ofSL g) k) ^ l ^ n
      rw [← map_pow, ← map_mul, ← hk, ← X.sl_mul, ← X.sl_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]
    obtain ⟨h1, h2, -⟩ := trc ε X l N w n _ hle _ _ hT ![en g 0 0, en g 0 1] _ _ hRep
    rw [trM_eq]
    exact ⟨⟨_, h1 hU, hE.refl _⟩, h2 hH, hW n _ M (Nat.pos_of_ne_zero (NeZero.ne M)) le_rfl hle _ _ hT _ _ _ hU hH hRep⟩
  · haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow (by have := hL.pos; omega) hlp.one_lt⟩
    have hσ' : σ ∈ fixMu Ω (l ^ n) := by
      rw [mem_fixMu_iff] at hσ ⊢
      intro z hz
      obtain ⟨c, hc⟩ := hnM
      exact hσ z (by rw [hc, pow_mul, hz, one_pow])
    have hχ := (sCycZ Ω l n σ).2
    rw [(hCy (l ^ n) σ).2.2.2.1.1 hσ', Units.val_one, ZMod.val_one, Nat.cast_one] at hχ
    unfold trM

    rw [map_sum]
    refine hSum _ _ _ _ fun γ _ u => ?_
    generalize g * liftSL M γ = h
    obtain ⟨δ, hδ, e⟩ := recip_mod X (NeZero.ne M) hσ (a : X.K) h
    obtain ⟨k, hk⟩ := hI δ hδ
    set A := X.kmap l (X.gal σ) (X.kmap l (X.sl (ofSL h)).toRingEquiv (clsK X l n (a : X.K))) with hA
    set B := X.kmap l (X.sl (ofSL h)).toRingEquiv (clsK X l n (X.gal σ a)) with hB
    have rA : Rep X l n (galU X σ (slU X (ofSL h) a)) A := hMap _ _ _ (hMap _ _ _ (hR a))
    have rB : Rep X l n (slU X (ofSL h) (galU X σ a)) B := hMap _ _ _ (hR (galU X σ a))
    have hBA := hCg _ _ _ _ rB rA ⟨galU X σ (slU X (ofSL h) k), Units.ext (by
      show X.sl (ofSL h) (X.gal σ a) = X.gal σ (X.sl (ofSL h) a) * (X.gal σ (X.sl (ofSL h) k)) ^ l ^ n
      rw [← e, map_mul, X.sl_mul, hk, map_mul, map_pow, map_mul, map_pow])⟩
    set c := (mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) * u 1]) 0 with hc
    set c' := (mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 with hc'
    have hcc : (l : ℤ_[l]) ^ n ∣ c ^ w - c' ^ w := by
      refine Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow c c' w)
      obtain ⟨t, ht⟩ := hχ
      refine ⟨mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * t * u 1, ?_⟩
      simp only [hc, hc', Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * u 1) * ht
    have h3 := hDv _ _ A hcc
    show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal σ) (X.kmap l (X.sl (toGQ (h : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (c ^ w • clsK X l n (a : X.K))) - X.kmap l (X.sl (toGQ (h : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (c' ^ w • clsK X l n (X.gal σ a))) = 0
    rw [hTo, map_smul, map_smul, map_smul, ← hA, ← hB]
    have : c ^ w • A - c' ^ w • B = (c ^ w • A - c' ^ w • A) - c' ^ w • (B - A) := by
      rw [smul_sub]; abel
    rw [this, map_sub, h3, map_smul, hBA, smul_zero, sub_zero]
end
