module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KmapSubMemOfASet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle009
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OrbitSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle007
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.HG

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem ent_toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (i j : Fin 2) : ent (toGQ m) i j = (m i j : ℚ) := by
  simp [ent, toGQ, h]

private theorem gal_diag (X : Tower Ω ε) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal s (X.sl (toGQ !![a, 0; 0, b]) f) = X.sl (toGQ !![a, 0; 0, b]) (X.gal s f) := by
  have hd : 0 < (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.det_fin_two_of]; simpa using mul_pos ha hb
  have h1 : eOm ε 0 = 1 := by
    have := Function.leftInverse_invFun ε.injective 1
    simpa [eOm] using this
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have key : ∀ (f : X.K) (r : ℚ), (X.exp (X.sl (toGQ !![a, 0; 0, b]) f)).coeff r = (X.exp f).coeff (r * b / a) := by
    intro f r
    have := X.exp_upper (toGQ !![a, 0; 0, b]) (by rw [ent_toGQ _ hd]; simp) f (r * b / a)
    rw [ent_toGQ _ hd, ent_toGQ _ hd, ent_toGQ _ hd] at this
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Int.cast_zero, mul_zero, zero_div, h1, one_mul] at this
    rw [← this]; congr 1; field_simp
  apply X.exp.toRingHom.injective
  ext r
  show (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, key, key, X.gal_exp]

private theorem galB_diag (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (p : ℤ) (hp : 0 < p) (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) :
    X.galB l s (X.act l !![p, 0; 0, 1] b) = X.act l !![p, 0; 0, 1] (X.galB l s b) := by
  funext u
  show X.kmap l _ (X.kmap l _ (b _)) = X.kmap l _ (X.kmap l _ (b _))
  rw [X.kmap_kmap, X.kmap_kmap]
  congr 2
  · ext f; exact gal_diag X p 1 hp one_pos s f
  · funext i
    fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private def tr (t : ℤ) : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem sl_up (X : Tower Ω ε) (p : ℤ) (hp : 0 < p) (j : ℤ) (f : X.K) :
    X.sl (toGQ !![1, j; 0, p]) f = X.sl (ofSL (tr j)) (X.sl (toGQ !![1, 0; 0, p]) f) := by
  rw [← X.sl_mul, ← Betti.toGQ_sl, ← toGQ_mul_of_pos _ _ (by simpa [Matrix.det_fin_two_of] using hp)
    (by rw [(tr j).det_coe]; exact one_pos)]
  congr 3
  simp [tr]

private theorem recip_up (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (p : ℤ) (hp : 0 < p) (s : Ω ≃ₐ[ℚ] Ω) (x : X.Khat l) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ (M : ℕ) (ζ : Ω) (e : ℕ), 0 < M → M₀ ∣ M → IsPrimitiveRoot ζ M → s ζ = ζ ^ e → ∀ j : ℤ,
      AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal s) (X.kmap l (X.sl (toGQ !![1, j; 0, p])).toRingEquiv x)) =
      AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.sl (toGQ !![1, j * e; 0, p])).toRingEquiv (X.kmap l (X.gal s) x)) := by
  have hc := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  obtain ⟨f, hf⟩ := hc.1 (AdicCompletion.eval (idl l) (X.Kl l) n x)
  obtain ⟨M₀, h0, hl⟩ := X.level (X.sl (toGQ !![1, 0; 0, p]) (f : X.K))
  refine ⟨M₀, h0, fun M ζ e hM hd hζ hs j => ?_⟩
  have hF := hc.2.2.2.2.2.1
  rw [hF _ _ _ (hF _ _ _ hf.symm), hF _ _ _ (hF _ _ _ hf.symm)]
  congr 1
  apply Units.ext
  show X.gal s (X.sl _ (f : X.K)) = X.sl _ (X.gal s (f : X.K))
  rw [sl_up X p hp j, sl_up X p hp (j * e), ← gal_diag X 1 p one_pos hp]
  obtain ⟨k, hk⟩ := hd
  have hk0 : 0 < k := Nat.pos_of_mul_pos_left (hk ▸ hM)
  have hζ' : IsPrimitiveRoot (ζ ^ k) M₀ := hζ.pow hM (by rw [hk, mul_comm])
  refine X.recip M₀ _ h0 hl (ζ ^ k) hζ' s e ?_ _ _ ?_
  · rw [map_pow, hs, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
  · simp [en, tr, mul_comm]

private theorem expo [IsAlgClosure ℚ Ω] (l n M : ℕ) [Fact l.Prime] (hM : 0 < M) (hd : l ^ n ∣ M) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ (ζ : Ω) (e : ℕ), IsPrimitiveRoot ζ M ∧ s ζ = ζ ^ e ∧ Nat.Coprime e M ∧
      (l : ℤ_[l]) ^ n ∣ (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) - e := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hs : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one hs.pow_eq_one
  refine ⟨ζ, e, hζ, he.symm, (hζ.pow_iff_coprime hM e).1 (he ▸ hs), ?_⟩
  obtain ⟨k, hk⟩ := hd
  have ht : IsPrimitiveRoot (ζ ^ k) (l ^ n) := hζ.pow hM (by rw [hk, mul_comm])
  have h1 := cyclotomicCharacter.spec l (n := n) s.toRingEquiv (ζ ^ k) ht.pow_eq_one
  have h2 : s.toRingEquiv (ζ ^ k) = (ζ ^ k) ^ e := by
    show s (ζ ^ k) = _
    rw [map_pow, ← he, ← pow_mul, ← pow_mul, mul_comm]
  rw [h2] at h1
  have h3 := (ht.isOfFinOrder (pow_pos (Fact.out : l.Prime).pos n).ne').pow_eq_pow_iff_modEq.1 h1
  rw [← ht.eq_orderOf] at h3
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    (ZMod.natCast_eq_natCast_iff _ _ _).2 h3, ZMod.natCast_zmod_val, sub_self]

private theorem sum_perm {Q : Type} [AddCommMonoid Q] (p e : ℕ) (hp : 0 < p) (he : Nat.Coprime e p) (F : ℤ → Q)
    (hF : ∀ k t : ℤ, F (k + t * p) = F k) : ∑ j ∈ Finset.range p, F (j * e) = ∑ j ∈ Finset.range p, F j := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have h1 : ∀ k : ℤ, F k = F ((k : ZMod p).val) := by
    intro k
    rw [ZMod.val_intCast, ← hF (k % p) (k / p)]
    congr 1
    rw [mul_comm]; exact (Int.emod_add_mul_ediv k p).symm
  have h2 : ∀ G : ZMod p → Q, ∑ j ∈ Finset.range p, G j = ∑ x, G x := fun G =>
    Finset.sum_nbij' (fun j => (j : ZMod p)) ZMod.val (by simp) (by simp [ZMod.val_lt])
      (fun j hj => ZMod.val_cast_of_lt (by simpa using hj)) (by simp) (by simp)
  have h3 := h2 fun x => F (x * e).val
  have h4 := h2 fun x => F x.val
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => h1 (j * e), Finset.sum_congr rfl fun (j : ℕ) _ => h1 j]
  push_cast
  rw [h3, h4]
  exact Equiv.sum_comp (ZMod.unitOfCoprime e he).mulRight fun x => F x.val

private theorem eval_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K) {x y : X.Khat l}
    (h : AdicCompletion.eval (idl l) (X.Kl l) n x = AdicCompletion.eval (idl l) (X.Kl l) n y) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y) := by
  have hc := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  obtain ⟨f, hf⟩ := hc.1 (AdicCompletion.eval (idl l) (X.Kl l) n y)
  rw [hc.2.2.2.2.2.1 φ x f (h.trans hf.symm), hc.2.2.2.2.2.1 φ y f hf.symm]

private theorem poly_cg (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (a t : X.Fn l)
    (ht : PolMod X l w n t) (h : CgF X l n a t) (u v : Fin 2 → ℤ_[l]) (h0 : (l : ℤ_[l]) ^ n ∣ u 0 - v 0) (h1 : u 1 = v 1) :
    AdicCompletion.eval (idl l) (X.Kl l) n (a u) = AdicCompletion.eval (idl l) (X.Kl l) n (a v) := by
  obtain ⟨c, -, hc⟩ := ht
  have hu := h u
  have hv := h v
  rw [map_sub, sub_eq_zero] at hu hv

  rw [hu, hv, hc, hc, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  rw [map_smul, map_smul, ← hx, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    ← sub_smul]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, h1, ← sub_mul]
  exact (h0.trans (sub_dvd_pow_sub_pow _ _ _)).mul_right _

private theorem cg_act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) {a b : X.Fn l}
    (h : CgF X l n a b) : CgF X l n (X.act l m a) (X.act l m b) := by
  intro u
  have := h (mZl l m *ᵥ u)
  rw [map_sub, sub_eq_zero] at this ⊢
  exact eval_kmap X l n _ this

private theorem cg_add (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {a b a' b' : X.Fn l}
    (h : CgF X l n a b) (h' : CgF X l n a' b') : CgF X l n (a + a') (b + b') := by
  intro u
  rw [Pi.add_apply, Pi.add_apply, add_sub_add_comm, map_add (f := _), h u, h' u, add_zero]

end UpperTheory.V.Z.Kato.Nb.HG

open UpperTheory.V.Z.Kato.Nb.HG in
theorem UpperTheory.V.Z.Kato.Nb.sHeckeGal :
    UpperTheory.V.Z.Kato.Nb.SHeckeGal := by
  intro Ω _ _ _ ε X l hl N w n p hN hp hc s a ha
  obtain ⟨ha', hG⟩ := sGalAct Ω ε X l N w n hN s a ha
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hσ := (Betti.isDiam_sgD hN.ne' hl.out.ne_zero (Nat.Coprime.coprime_mul_left_right hc)).1
  have hD : 0 < (!![(p : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simpa [Matrix.det_fin_two_of] using hp.pos
  have hS : ∀ γ : SL(2, ℤ), 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := fun γ => by rw [γ.det_coe]; exact one_pos
  unfold Tower.heckeT
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add (f := _)]
  refine cg_add X l n ?_ ?_
  · intro u
    set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
    choose M₀ hM₀ hR using fun j : ℕ => recip_up X l n p hp' s (a (mZl l !![1, (j : ℤ); 0, (p : ℤ)] *ᵥ ![u 0, χ * u 1]))
    have hM : 0 < (∏ j ∈ Finset.range p, M₀ j) * (l ^ n * p) :=
      Nat.mul_pos (Finset.prod_pos fun j _ => hM₀ j) (Nat.mul_pos (pow_pos hl.out.pos n) hp.pos)
    obtain ⟨ζ, e, hζ, hs, he, hχe⟩ := expo l n _ hM ((Dvd.intro _ rfl : l ^ n ∣ _).mul_left _) s
    obtain ⟨t, ht, hat⟩ := ha.1
    have hper : ∀ k t : ℤ,
        AdicCompletion.eval (idl l) (X.Kl l) n (X.act l !![1, k + t * p; 0, (p : ℤ)] (X.galB l s a) u) =
        AdicCompletion.eval (idl l) (X.Kl l) n (X.act l !![1, k; 0, (p : ℤ)] (X.galB l s a) u) := by
      intro k t
      have hg : tr t ∈ Gam N l := ⟨(CongruenceSubgroup.Gamma1_mem N _).2 (by simp [tr]),
        CongruenceSubgroup.Gamma0_mem.2 (by simp [tr])⟩
      have := cg_act X l n !![1, k; 0, (p : ℤ)] (ha'.2.1 _ hg) u
      rw [Tower.act_act Ω ε X l _ _ (hS _) (by simpa [Matrix.det_fin_two_of] using hp.pos), map_sub, sub_eq_zero] at this
      rw [← this]
      congr 3
      simp [tr]
    have hsum := sum_perm p e hp.pos (he.coprime_dvd_right ((Dvd.intro_left _ rfl : p ∣ _).mul_left _))
      (fun k => AdicCompletion.eval (idl l) (X.Kl l) n (X.act l !![1, k; 0, (p : ℤ)] (X.galB l s a) u)) hper

    rw [map_sub, sub_eq_zero, LinearMap.sum_apply, LinearMap.sum_apply, map_sum, Finset.sum_apply, Finset.sum_apply,
    map_sum, map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j hj => ?_
    refine (hR j _ ζ e hM ((Finset.dvd_prod_of_mem _ hj).mul_right _) hζ hs j).trans ?_
    refine eval_kmap X l n _ (eval_kmap X l n _ (poly_cg X l w n a t ht hat _ _ ?_ ?_))
    · have : (l : ℤ_[l]) ^ n ∣ j * u 1 * (χ - e) := hχe.mul_left _
      convert this using 1
      simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hχ]
      ring
  · rw [← Tower.act_act Ω ε X l _ _ (hS _) hD, ← Tower.act_act Ω ε X l _ _ (hS _) hD, galB_diag X l p hp']
    exact cg_act X l n _ (hG _ hσ).2
end

section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem pol_cont {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (w n : ℕ) (t : X.Fn l) (ht : PolMod X l w n t) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) → CgF X l n (X.galB l s t) t := by
  obtain ⟨c, hc, htc⟩ := ht
  choose f _ hf using hc
  choose Ec hEc using fun i => GlobalTheory.KZ.GalCont.fix_fin X (f i : X.K)
  obtain ⟨Ez, hEz⟩ := GlobalTheory.KZ.GalCont.cyc_sub_one_mem (Ω := Ω) l n
  obtain ⟨-, -, -, -, hmap, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, hsm, -⟩ := sApi Ω ε X l n
  refine ⟨Ez ∪ Finset.univ.biUnion Ec, fun s hs u => ?_⟩
  have hχ := hEz s fun x hx => hs x (Finset.mem_union_left _ hx)
  rw [idl, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hχ
  have hk : ∀ i, AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal s) (c i)) =
      AdicCompletion.eval (idl l) (X.Kl l) n (c i) := by
    intro i
    have h1 := hmap (X.gal s) _ _ (hf i)
    have h2 : Units.map (X.gal s : X.K →* X.K) (f i) = f i :=
      Units.ext (hEc i s fun x hx => hs x (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩)))
    rw [h2] at h1
    exact (show _ = _ from h1).trans (show _ = _ from hf i).symm
  have hgal : X.galB l s t u =
      X.kmap l (X.gal s) (t ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) := rfl

  rw [hgal, htc, htc, map_sum, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [map_smul, map_sub, map_smul, hk, ← map_smul, ← map_sub]
  refine hsm _ _ _ ?_
  rw [← mul_sub]
  refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow _ _ _)) _
  rw [← sub_one_mul]
  exact hχ.mul_right _

theorem UpperTheory.V.Z.Kato.Nb.sTopCocG :
    UpperTheory.V.Z.Kato.Nb.STopCocG := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy u hu z β hβ hz
  obtain ⟨hE, hadd, -, -, -, -, hgal, -, -, hmul, -⟩ := sApi Ω ε X l n
  obtain ⟨-, iadd, -, icg, -⟩ := sInvApi Ω ε X l N w n
  obtain ⟨m1, m2, -⟩ := sXiMul Ω ε X l n N M₀ M w g hL x y hxy (fun z => z = 1)
  obtain ⟨-, -, -, -, -, -, -, hcy⟩ := sSlD Ω ε X N (NeZero.pos N)
  refine ⟨fun σ hσ => ?_, fun σ hσ τ hτ => ?_, ?_⟩
  · exact icg _ _ (hz σ hσ) (iadd _ _ (sXiInv Ω ε X l n N M₀ M w g hL hW x y hxy _ _ (hu.eqv σ))
      (iadd _ _ (sGalAct Ω ε X l N w n (NeZero.pos N) σ β hβ).1 hβ).2).1
  · have h0 := m2 (u σ) 0
    rw [Nat.cast_zero, zero_smul] at h0
    have h1 := m1 (u (σ * τ)) (u σ) (tw X (l ^ n) M₀ σ (u τ)) (fun x y => u σ x y ^ 0) fun x y h => by
      simpa using hu.coc σ τ x y h
    have h2 := sXiTw Ω ε X l n N M₀ M w g hL x y (fun z => z = 1) (u τ) σ
    rw [(hcy M σ).2.2.2.1.1 hσ] at h2
    simp only [mul_one] at h2
    have h3 := hE.trans h1 (hadd _ _ _ _ (hE.refl _) (hadd _ _ _ _ h2 h0).2).1
    have h4 := hE.trans (hz _ (mul_mem hσ hτ)) (hadd _ _ _ _ h3 (hE.refl _)).1
    have h5 := (hadd _ _ _ _ (hz σ hσ) (hgal σ _ _ (hz τ hτ))).1
    refine hE.trans h4 (hE.symm ?_)
    convert h5 using 1
    rw [hmul, map_add (f := _), map_sub]
    abel
  · obtain ⟨T, hT⟩ := hu.loc
    obtain ⟨⟨t, ht, hβt⟩, -⟩ := hβ
    obtain ⟨E, hEt⟩ := pol_cont X l w n t ht
    refine ⟨T ∪ E, fun σ hσ τ hτ h => ?_⟩
    have h1 := m1 (u σ) (u τ) (u τ) (u τ) fun x y hh => by
      simpa using hT σ τ (fun a ha => h a (Finset.mem_union_left _ ha)) x y hh
    rw [sub_self, add_zero] at h1
    have h2 := hEt (τ⁻¹ * σ) fun a ha => by
      rw [AlgEquiv.mul_apply, h a (Finset.mem_union_right _ ha), ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have h3 := hgal τ _ _ (hE.trans (hgal _ _ _ hβt) (hE.trans h2 (hE.symm hβt)))
    rw [← hmul, mul_inv_cancel_left] at h3
    exact hE.trans (hz σ hσ) (hE.trans (hadd _ _ _ _ h1 (hadd _ _ _ _ h3 (hE.refl β)).2).1 (hE.symm (hz τ hτ)))
end

section

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

private theorem cgr_solve {K : Type} [Field K] {m : ℕ} {f a b c d : Kˣ} (h : Cgr m f (a * b)) (h' : Cgr m f (c * d)) :
    Cgr m b (c * d / a) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  refine ⟨k' / k, ?_⟩
  rw [div_pow, div_mul_div_comm, ← hk', hk, eq_div_iff_mul_eq', mul_assoc, mul_left_comm]

theorem sBridge : SBridge := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy u hu z β hβ hz A _ _ π
  obtain ⟨eqv, hadd, -, hsum, -, -, hgal, -, -, hmul, -⟩ := sApi Ω ε X l n
  obtain ⟨-, iadd, -, -, isum, -⟩ := sInvApi Ω ε X l N w n
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcyc := (sSlD Ω ε X N hN).2.2.2.2.2.2.2 M
  have cmul : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM M (s * t) = cycM M s * cycM M t := fun s t => (hcyc s).2.1 t
  have crep : ∀ t, cycM M (repM M t : Ω ≃ₐ[ℚ] Ω) = t := (hcyc 1).2.2.1
  have cfix : ∀ s : Ω ≃ₐ[ℚ] Ω, s ∈ fixMu Ω M ↔ cycM M s = 1 := fun s => (hcyc s).2.2.2.1
  have hM := sXiMul Ω ε X l n N M₀ M w g hL x y hxy
  have hT := sXiTw Ω ε X l n N M₀ M w g hL x y
  have hI := sXiInv Ω ε X l n N M₀ M w g hL hW x y hxy
  let B : (ZMod M)ˣ → X.Fn l := fun t =>
    Xi X l n N M₀ M w g x y (fun z => z = t) (u (repM M t)) + X.galB l (repM M t) β
  have hB : ∀ t, InvM X l N w n (B t) := fun t =>
    (iadd _ _ (hI _ _ (hu.eqv _)) (sGalAct Ω ε X l N w n hN _ β hβ).1).1
  have key : ∀ (s : Ω ≃ₐ[ℚ] Ω) (t : (ZMod M)ˣ), CgF X l n (shB X l M z s t)
      (Xi X l n N M₀ M w g x y (fun z => z = t) (u s) + (X.galB l s (B (t * (cycM M s)⁻¹)) - B t)) := by
    intro s t
    unfold shB
    simp only [B]
    generalize hτ : (repM M t : Ω ≃ₐ[ℚ] Ω) = τ
    generalize hτ' : (repM M (t * (cycM M s)⁻¹) : Ω ≃ₐ[ℚ] Ω) = τ'
    have c1 : cycM M τ = t := hτ ▸ crep _
    have c2 : cycM M τ' = t * (cycM M s)⁻¹ := hτ' ▸ crep _
    generalize hσ : τ⁻¹ * s * τ' = σ
    have e : τ * σ = s * τ' := by rw [← hσ]; group
    have hfix : σ ∈ fixMu Ω M := by
      rw [cfix]
      have h := congrArg (cycM M) e
      rw [cmul, cmul, c1, c2, mul_comm (cycM M s), inv_mul_cancel_right] at h
      exact mul_eq_left.1 h
    have h1 := hgal τ _ _ (hz σ hfix)
    rw [map_add (f := _), map_sub, ← hmul, e, hmul] at h1
    have h2 := hT (fun z => z = t) (u σ) τ
    have p2 : (fun z : (ZMod M)ˣ => z * cycM M τ = t) = fun z => z = 1 := by
      funext z
      rw [c1, mul_eq_right]
    rw [p2] at h2
    have h3 := (hM (fun z => z = t)).1 (tw X (l ^ n) M₀ τ (u σ)) (u s) (tw X (l ^ n) M₀ s (u τ')) (u τ)
      fun x y h => cgr_solve (hu.coc τ σ x y h) (e ▸ hu.coc s τ' x y h)
    have h4 := hT (fun z => z = t) (u τ') s
    have p4 : (fun z : (ZMod M)ˣ => z * cycM M s = t) = fun z => z = t * (cycM M s)⁻¹ := by
      funext z
      rw [eq_mul_inv_iff_mul_eq]
    rw [p4] at h4
    have h5 := eqv.trans (eqv.symm h2) (eqv.trans h3 (hadd _ _ _ _ (eqv.refl _) (hadd _ _ _ _ h4 (eqv.refl _)).2).1)
    have h6 := eqv.trans h1 (hadd _ _ _ _ h5 (eqv.refl _)).1
    convert h6 using 1
    rw [map_add (f := _)]
    abel
  refine ⟨fun t => ∑ v ∈ Finset.univ.filter (fun v => π v = t), B v, fun t => isum _ _ _ fun v _ => hB v, fun s t => ?_⟩
  have h := hsum _ (Finset.univ.filter (fun v => π v = t)) _ _ fun v _ => key s v
  have r : ∑ v ∈ Finset.univ.filter (fun v => π v = t * (π (cycM M s))⁻¹), B v =
      ∑ v ∈ Finset.univ.filter (fun v => π v = t), B (v * (cycM M s)⁻¹) := by
    symm
    refine Finset.sum_equiv (Equiv.mulRight (cycM M s)⁻¹) (fun v => ?_) fun v _ => rfl
    simp
  beta_reduce

  rw [r, (hM (fun _ => True)).2.2.2 (u s) A π t, map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact h

end UpperTheory.V.Z.Kato.Nb

end
end
