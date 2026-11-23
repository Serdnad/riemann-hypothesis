module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.Rigdesc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Formalism.LocalRingCardinality.SpanPowerMembership.Places
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCutoffCoordinateHyperplanesPoincareBoun
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotDesc

def idq {S : Scheme.{0}} {A B : Over S} (q : A ⟶ B) : A ⊗ A ⟶ A ⊗ B := lift (fst A A) (snd A A ≫ q)

theorem evc_lam {S : Scheme.{0}} {A Y : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hΛ : (abelian₂ A L).IsLB)
    (a b : Y ⟶ A) : evc hΛ a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hΛ = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hΛ, pull_lam, lift_fst,
    lift_snd]

theorem lam_mul_right_sub {S : Scheme.{0}} {A Y : Over S} [GrpObj A] [IsCommMonObj A] (c : Pic A.left)
    (a k y : Y ⟶ A) : lam c a (k * y) - lam c a y = lam c (a * y) k - lam c y k := by
  simp only [lam]
  rw [show a * y * k = a * (k * y) by rw [_root_.mul_assoc, _root_.mul_comm y k],
    show y * k = k * y from _root_.mul_comm y k]
  abel

theorem exists_descent_lam : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsMonHom i →
    Mono i → IsFinite H.hom → Flat H.hom →
    (∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x) →
    ∀ (B : Over (Sp R)) [GrpObj B] (q : A ⟶ B), IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left →
    Surjective q.left → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q →
    ∃ (P : LB (A ⊗ B).left) (hP : P.IsLB), ∀ (Y : Over (Sp R)) (a x : Y ⟶ A),
      evc hP a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) -
        GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL) := by
  intro R _ _ A _ hA L hL H _ i _ _ _ _ hK B _ q hB _ hqf hqfl hqs hpb
  have := hA.comm
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hku : lam (cls L hL) (fst A H) (snd A H ≫ i) = 0 := by
    rw [← evc_lam hL hΛ, ← triv_ev_iff hΛ]
    exact lam_triv_of_memKL _ A hA L hL H i ((hK H i).2 ⟨𝟙 H, Category.id_comp i⟩)
  have := hB.smooth
  have := hqf
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have hlfp : LocallyOfFinitePresentation q.left := inferInstance
  obtain ⟨-, h2⟩ := CompanionTheory.PfDual.rigDescent_holds (Sp R) A A B hA q hqfl hlfp hqs
  have hrig : Triv (ev (abelian₂ A L) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hΛ, evc_lam hL hΛ, lam_one_left]
  have hinv : ∀ (T : Over (Sp R)) (x x' : T ⟶ A), x ≫ q = x' ≫ q →
      LBIso (ev (abelian₂ A L) (fst A T) (snd A T ≫ x)) (ev (abelian₂ A L) (fst A T) (snd A T ≫ x')) := by
    intro T x x' hxx
    refine (cls_eq_iff (pull_isLB hΛ _) (pull_isLB hΛ _)).1 ?_
    rw [cls_ev hΛ, cls_ev hΛ, evc_lam hL hΛ, evc_lam hL hΛ]
    obtain ⟨z, hz1, hz2⟩ : ∃ z : T ⟶ H ⊗ A, z ≫ ((fst H A ≫ i) * snd H A) = x ∧ z ≫ snd H A = x' :=
      ⟨_, hpb.lift_fst x x' hxx, hpb.lift_snd x x' hxx⟩
    subst hz1 hz2
    have ex : snd A T ≫ z ≫ ((fst H A ≫ i) * snd H A) =
        (snd A T ≫ z ≫ fst H A ≫ i) * (snd A T ≫ z ≫ snd H A) := by
      rw [MonObj.comp_mul, MonObj.comp_mul]
    rw [ex, ← sub_eq_zero, lam_mul_right_sub]
    have k : ∀ u : A ⊗ T ⟶ A, lam (cls L hL) u (snd A T ≫ z ≫ fst H A ≫ i) = 0 := fun u => by
      have e := congrArg (GlobalTheory.CechPic.pull (lift u (snd A T ≫ z ≫ fst H A)).left) hku
      rwa [map_zero, pull_lam, lift_fst, lift_snd_assoc, Category.assoc, Category.assoc] at e
    rw [k, k, sub_zero]
  obtain ⟨N, hN, -, hiso⟩ := h2 (abelian₂ A L) hΛ hrig hinv
  refine ⟨N, hN, fun Y a x => ?_⟩
  have hPc : GlobalTheory.CechPic.pull (idq q).left (cls N hN) = cls (abelian₂ A L) hΛ :=
    ((cls_eq_iff hΛ (pull_isLB hN _)).2 hiso).symm
  have e : lift a (x ≫ q) = lift a x ≫ idq q := by
    simp [idq]
  rw [evc, e, Over.comp_left, pull_comp, hPc, show cls _ hΛ = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hΛ, pull_lam, lift_fst,
    lift_snd]
  rfl

end GlobalTheory.QuotDesc
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVal

open GlobalTheory.IdemSupport

theorem valuation_cP {D : D7} (Q : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.E) :
    (cP Q).valuation D.host.E (star x) = Q.valuation D.host.E x := by
  have : cP Q = Formalism.BasicNotions.Examples₂.PlacesToy.conjW Q := by
    ext r
    have := Formalism.BasicNotions.Examples₂.PlacesToy.mem_conjW_pow Q r 1
    rw [pow_one, pow_one] at this
    rw [this, mem_cP]
    rfl
  rw [this, Formalism.BasicNotions.Examples₂.PlacesToy.valuation_conjW, star_star]

theorem eq_of_le_iff {a b : WithZero (Multiplicative ℤ)}
    (h : ∀ c, c ≠ 0 → (a ≤ c ↔ b ≤ c)) : a = b := by
  have key : ∀ {a b : WithZero (Multiplicative ℤ)}, (∀ c, c ≠ 0 → a ≤ c → b ≤ c) → b ≤ a := by
    intro a b h
    by_cases ha : a = 0
    · by_contra hb
      have hb0 : b ≠ 0 := fun e => hb (by rw [e]; exact zero_le)
      have h1 := h (WithZero.exp (WithZero.log b - 1)) WithZero.exp_ne_zero (by rw [ha]; exact zero_le)
      rw [← WithZero.exp_log hb0, WithZero.exp_le_exp, WithZero.log_exp] at h1
      omega
    · exact h a ha le_rfl
  exact le_antisymm (key fun c hc => (h c hc).2) (key fun c hc => (h c hc).1)

theorem int_iff {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {e : FiniteAdeleRing (𝓞 E) E}
    (h1 : e P = 1) (h0 : ∀ R, R ≠ P → e R = 0) (y : FiniteAdeleRing (𝓞 E) E) {k : E} (hk : k ≠ 0) :
    (∀ R : HeightOneSpectrum (𝓞 E), Valued.v ((e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) R) ≤ 1) ↔
      Valued.v (y P) ≤ P.valuation E k := by
  have e1 : ∀ R, (e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) R =
      e R * (y R * algebraMap E (R.adicCompletion E) k⁻¹) := fun R => rfl
  have hv : 0 < P.valuation E k := zero_lt_iff.2 (by simpa using hk)
  have e2 : Valued.v ((e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) P) ≤ 1 ↔
      Valued.v (y P) ≤ P.valuation E k := by
    rw [e1, h1, one_mul, map_mul, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀, mul_inv_le_iff₀ hv, one_mul]
  rw [← e2]
  refine ⟨fun h => h P, fun h R => ?_⟩
  by_cases hR : R = P
  · rw [hR]; exact h
  · rw [e1, h0 R hR, zero_mul, map_zero]
    exact zero_le

theorem map_three {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B ≃+* C) (a b c : A) :
    g (f (a * (b * c))) = g (f a) * (g (f b) * g (f c)) := by
  simp only [map_mul]

theorem conj_mem_iff {D : D7} (e z : AE D) (k : D.host.E) :
    finPart D (cA D e * (cA D z * incA D (star k)⁻¹)) ∈ intAE D ↔ finPart D (e * (z * incA D k⁻¹)) ∈ intAE D := by
  rw [← star_inv₀, ← cA_incA, ← RingHom.map_mul, ← RingHom.map_mul]
  refine ⟨fun h => ?_, finPart_cA_mem⟩
  have := finPart_cA_mem h
  rwa [cA_cA] at this



theorem components_and_conj_valuation : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) ∧ ∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q) := by
  intro D ι hinc hint hid
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  choose ε hε using hid
  have hd : ∀ P, IsDelta Φ P (ε P) := fun P => (tie_iff hΦ (hε P).1.1 (hε P).2.1 P).1 (hε P).1.2.2
  refine ⟨fun e P h => ?_, fun z Q => ?_⟩
  · rw [delta_unique hΦ (delta_of_isIdemAt hΦ h) (hd P)]
    exact (hε P).2
  have hc : cA D (ε Q) = ε (cP Q) := delta_unique hΦ (delta_conj hΦ (hd Q)) (hd _)
  have key : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (y : AE D) (k : D.host.E), k ≠ 0 →
      (finPart D (ε P * (y * incA D k⁻¹)) ∈ intAE D ↔ Valued.v (ι (finPart D y) P) ≤ P.valuation D.host.E k) := by
    intro P y k hk
    have : ι (finPart D (incA D k⁻¹)) = algebraMap D.host.E _ k⁻¹ := hinc k⁻¹
    rw [hint, map_three, this]
    exact int_iff (hε P).2.2.1 (hε P).2.2.2 _ hk
  refine eq_of_le_iff fun c hc0 => ?_
  obtain ⟨k, rfl⟩ := Q.valuation_surjective D.host.E c
  have hk : k ≠ 0 := fun e => hc0 (by rw [e, Valuation.map_zero])
  have h1 := key (cP Q) (cA D z) (star k) (star_ne_zero.2 hk)
  rw [valuation_cP, ← hc, conj_mem_iff] at h1
  exact h1.symm.trans (key Q z k hk)

end GlobalTheory.ConjVal
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem det_dbar_eq_sum_dbar : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, ContDiffAt ℝ 2 (f i) v) → (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) := by
  intro n f j v hf
  have hP := GlobalTheory.T.piola_identity_wirtingerAntiholomorphic f j v (fun i _ => hf i)
  have hd : ∀ w : Equiv.Perm (Fin n), DifferentiableAt ℝ
      (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v := fun w =>
    (HasFDerivAt.finsetProd (u := Finset.univ.erase j) (g := fun i x => dbar (f i) x (coordVec (w i)))
      (fun i _ => (differentiableAt_dbar_apply (hf i) _).hasFDerivAt)).differentiableAt
  have hj : DifferentiableAt ℝ (f j) v := (hf j).differentiableAt (by norm_num)
  have key : ∀ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
      dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) =
      ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, dbar (f i) v (coordVec (w i)) +
      f j v * (((Equiv.Perm.sign w : ℤ) : ℂ) *
        dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j))) := by
    intro w
    rw [dbar_mul hj (hd w), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    ring
  rw [Finset.sum_congr rfl (fun w _ => key w), Finset.sum_add_distrib, ← Finset.mul_sum, hP, mul_zero, add_zero,
    ← Matrix.det_transpose, Matrix.det_apply']
  rfl

end GlobalTheory.GoodTop
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem linForm_eq_of_antisymm_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  intro ι _ m L hL Q Q' h
  have sq : ∀ u : ℤˣ, ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
    intro u
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have key : ∀ P : MvPolynomial (Root m) ℝ,
      L (antisymm P) = (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) * L P := by
    intro P

    simp only [GlobalTheory.GoodMetric.antisymm, map_sum, map_zsmul]
    rw [Finset.sum_congr rfl (fun w _ => by
      rw [GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks ι m L hL w P, zsmul_eq_mul, ← mul_assoc, sq, one_mul])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ∀ τ, Equiv.Perm (Fin (m τ)))).ne'
  have e := congrArg L h
  rw [key, key] at e
  exact mul_left_cancel₀ hc e

end GlobalTheory.FlagPush
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem isEqn_diag_of_frame : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) (m : ι → ℕ) (E' : Fr (ratOf Y) m m) (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ (y : Y.X), ∀ A ∈ E'.S y, Par m ⊤ (B * A⁻¹) ∧ ∀ x : Root m, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t := by
  intro F _ Y ι m E' gr B hB H y A hA
  have par : ∀ {z : Y.X} {A : Mat m Y.Fn}, A ∈ E'.S z → Par m ⊤ (B * A⁻¹) := fun {z A} h =>
    ((Fr.mem_iff (Fr.mem_genericPoint h)).1 hB).mono le_rfl le_top
  refine ⟨par hA, fun x => ?_⟩
  obtain ⟨A', hA', t', ht', heq⟩ := H y x
  have hP : Par m ((ratOf Y).O y).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have e : B * A⁻¹ = (B * A'⁻¹) * (A' * A⁻¹) := by
    rw [← mul_assoc, mul_assoc B, Mat.inv_mul (Fr.det_ne hA'), mul_one]
  obtain ⟨hu0, hui, -, -⟩ := GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m Y.Fn _ (A' * A⁻¹) hP x
  obtain ⟨-, -, -, hmul⟩ := GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m Y.Fn ⊤ (B * A'⁻¹) (par hA') x
  obtain ⟨ht0, -⟩ := GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m Y.Fn ⊤ (B * A⁻¹) (par hA) x
  have hd : (B * A⁻¹) x.1 x.2 x.2 = t' * (A' * A⁻¹) x.1 x.2 x.2 := by
    rw [e, hmul _ (hP.mono le_rfl le_top), ht']
  refine ⟨Units.mk0 _ ht0, rfl, heq.iff_unitAt.2 ?_⟩
  have hu : UnitAt y ((A' * A⁻¹) x.1 x.2 x.2) := (unitAt_iff hu0).2
    ⟨mem_O_ratOf.1 ((hP x.1).1 x.2 x.2), mem_O_ratOf.1 hui⟩
  convert hu using 1
  rw [Units.val_mk0, hd]
  exact mul_div_cancel_left₀ _ t'.ne_zero

end GlobalTheory.FlagPush
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → MContDiffAt ∞ (fun v => H A (e.symm v) ()) (e y) ∧ IsUnit (H A (e.symm (e y)) ()).det := by
  first | exact @GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart | exact GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart | (intros; apply GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.exists_logCutoff_coordinateHyperplanes_poincareBound : ∀ {n : ℕ} (S : Finset (Fin n)), ∃ (C : ℝ) (χ : ℕ → V n → ℝ), (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k v, 0 ≤ χ k v ∧ χ k v ≤ 1) ∧ (∀ k v, (∃ a ∈ S, v a = 0) → χ k =ᶠ[𝓝 v] fun _ => 0) ∧ (∀ v : V n, (∀ a ∈ S, v a ≠ 0) → ∀ᶠ k in atTop, χ k =ᶠ[𝓝 v] fun _ => 1) ∧ ∀ k v b, ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b ≤ C := by
  first | exact @GlobalTheory.GoodTop.exists_logCutoff_hyperplanes | exact GlobalTheory.GoodTop.exists_logCutoff_hyperplanes | (intros; apply GlobalTheory.GoodTop.exists_logCutoff_hyperplanes <;> assumption)
end

section

namespace GlobalTheory.Proof.CoeffSpan

theorem finiteDimensional_coeffSpan (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun φ k => φ (ρ k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    refine ⟨{ toFun := fun A => ℓ (A w), map_add' := fun A B => by simp, map_smul' := fun c A => by simp }, ?_⟩
    rfl
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.Proof.CoeffSpan
end

section


theorem _root_.GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case : GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernDegree := by
  first | exact @GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | exact GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | (intros; apply GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex <;> assumption)
end

section


theorem _root_.GlobalTheory.T.arithInterChangeOfMetric_of_mixedInductive : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.ArMetric := by
  first | exact @GlobalTheory.Published.arMetric_of_arMix | exact GlobalTheory.Published.arMetric_of_arMix | (intros; apply GlobalTheory.Published.arMetric_of_arMix <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.height_add_mul_geometricDegree_nonneg_of_smallSection : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → ∀ (C : HermLB p) (h : X → ℝ), C.SemiPos D → C.IsArithHeight h → (∀ z, z ≠ genericPoint X → 0 ≤ h z) → ∀ (m : ℕ) (u : ℝ), 0 < m → 0 ≤ u → (∃ s ∈ ((C.shift (fun _ => u) fun _ => rfl).pow m).smallSec, s ≠ 0) → 0 ≤ h (genericPoint X) + u * gdeg C D := by
  first | exact @GlobalTheory.HSNef.height_add_mul_gdeg_nonneg_of_smallSec | exact GlobalTheory.HSNef.height_add_mul_gdeg_nonneg_of_smallSec | (intros; apply GlobalTheory.HSNef.height_add_mul_gdeg_nonneg_of_smallSec <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.isNef_of_semiPos_generated_by_smallSections : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ) (s : Fin n → M.B.Sec), M.SemiPos D → (∀ i, s i ∈ M.smallSec) → (∀ x : X, ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.IsNef D := by
  first | exact @GlobalTheory.GenNef.isNef_of_gen_small | exact GlobalTheory.GenNef.isNef_of_gen_small | (intros; apply GlobalTheory.GenNef.isNef_of_gen_small <;> assumption)
end
