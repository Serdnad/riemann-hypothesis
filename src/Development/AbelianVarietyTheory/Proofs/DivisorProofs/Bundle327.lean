module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle255
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle161
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SliceAn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle247
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaTotallyRealAtMostSimplePole
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150

@[expose] public section

section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory.UCls
open scoped TensorProduct
open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem isKM_mul {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  obtain ⟨⟨hd', hh'⟩, h2', h3'⟩ := hk'
  refine ⟨⟨by rw [det_mul]; exact hd.mul hd', fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hh, hh']
  · obtain ⟨y2, hy2, e2⟩ := h2' x hx
    have hx' : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y2 := by rw [← e2]; abel
      rw [this]; exact add_mem hx (nsmul_mem hy2 _)
    obtain ⟨y1, hy1, e1⟩ := h2 _ hx'
    refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e1, ← e2]; abel
  · obtain ⟨y1, hy1, e1⟩ := h3 x hx
    obtain ⟨y2, hy2, e2⟩ := h3' y1 hy1
    exact ⟨y2, hy2, by rw [← mulVec_mulVec, e2, e1]⟩

theorem isKM_inv {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) :
    IsKM c G L M k⁻¹ := by
  apply GlobalTheory.UCls.KGrp.isKM_inv <;> assumption

theorem tEquiv_refl (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t : RA F E) :
    TEquiv c G L M t t :=
  ⟨1, by simp, 1, isKM_one c G L M, by simp [Algebra.TensorProduct.one_def.symm]⟩

theorem tEquiv_symm {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' : RA F E}
    (h : TEquiv c G L M t t') : TEquiv c G L M t' t := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  refine ⟨u⁻¹, by rw [map_inv₀, ← mul_inv, hu, inv_one], k⁻¹, isKM_inv hk, ?_⟩
  have hd : IsUnit k.det := hk.1.1
  have e1 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hu0, Algebra.TensorProduct.one_def]
  have e2 : k.det * k⁻¹.det = 1 := by rw [det_nonsing_inv, Ring.mul_inverse_cancel _ hd]
  calc t = (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u)) * t * (k.det * k⁻¹.det) := by
        rw [e1, e2, one_mul, mul_one]
    _ = _ := by ring

theorem tEquiv_trans {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' t'' : RA F E}
    (h : TEquiv c G L M t t') (h' : TEquiv c G L M t' t'') : TEquiv c G L M t t'' := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  obtain ⟨u', hu', k', hk', rfl⟩ := h'
  refine ⟨u' * u, ?_, k * k', isKM_mul hk hk', ?_⟩
  · rw [map_mul]
    calc u' * u * (c u' * c u) = (u' * c u') * (u * c u) := by ring
      _ = 1 := by rw [hu, hu', one_mul]
  · have e : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (u' * u)) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u') * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [det_mul, e]; ring

theorem tEquiv_of_eqvGen {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    (a b : {t : RA F E // IsTA c t})
    (h : Relation.EqvGen (fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1) a b) :
    TEquiv c G L M a.1 b.1 :=
  (Equivalence.eqvGen_iff (r := fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1)
    ⟨fun a => tEquiv_refl c G L M a.1, fun h => tEquiv_symm h, fun h h' => tEquiv_trans h h'⟩).1 h

end GlobalTheory.UCls
end

theorem GlobalTheory.UCls.torus_eqvGen_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t}), Relation.EqvGen (fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1) a b → TEquiv (IsCMField.complexConj E) G L M a.1 b.1 :=
  by intro E _ _ _ r M G L a b h; exact GlobalTheory.UCls.tEquiv_of_eqvGen a b h
end

section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem theta_comm {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (a : A) :
    ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((pullback.snd (str A B) g).app U).hom (secAlg A g U a) := by
  apply GlobalTheory.HilbAff.IdealDet.comm_fst <;> assumption

def theta {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra;
    Γ(T, U) ⊗[A] B →+* Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((pullback.snd (str A B) g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((pullback.fst (str A B) g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => theta_comm A B g U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem theta_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens)
    (c : Γ(T, U)) (b : B) :
    letI := (secAlg A g U).toAlgebra;
    theta A B g U (c ⊗ₜ[A] b) = ((pullback.snd (str A B) g).app U).hom c *
      ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U)
        (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem kappa_apply_eq {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) (x : letI := (secAlg A g U).toAlgebra; Γ(T, U) ⊗[A] B) :
    kappa A B g I U x =
      (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom (theta A B g U x) := by
  letI := (secAlg A g U).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    have hk : kappa A B g I U (c ⊗ₜ[A] b) =
        ((I.subschemeι ≫ pullback.snd (str A B) g).app U).hom c *
          ((I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤
            ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
      letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) :=
        (((I.subschemeι ≫ pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    rw [hk, theta_tmul, map_mul]
    congr 1
    have e : (pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) ≫
        I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U) =
        (I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤
          ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    rw [← e]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; rfl

theorem ker_kappa_eq {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    RingHom.ker (kappa A B g I U) =
      Ideal.comap (theta A B g U) (RingHom.ker (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom) := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, kappa_apply_eq]; exact Iff.rfl

def psi (C : Type) [CommRing C] [Algebra A C] :
    C ⊗[A] B →+* Γ(pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C))), ⊤) :=
  (pullbackSpecIso A B C).hom.appTop.hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv.hom.comp
      (Algebra.TensorProduct.comm A C B).toRingHom)

end GlobalTheory.HilbAff
end
end

section

open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

noncomputable section

namespace GlobalTheory.DiffDecay

section Weak

variable {E : Type} [AddCommGroup E] [Module ℂ E]

def WithSemi (_p : Seminorm ℂ E) : Type := E

instance (p : Seminorm ℂ E) : AddCommGroup (WithSemi p) := inferInstanceAs (AddCommGroup E)
instance (p : Seminorm ℂ E) : Module ℂ (WithSemi p) := inferInstanceAs (Module ℂ E)
instance (p : Seminorm ℂ E) : SeminormedAddCommGroup (WithSemi p) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := WithSemi p) p.toAddGroupSeminorm
instance (p : Seminorm ℂ E) : NormedSpace ℂ (WithSemi p) where
  norm_smul_le a x := (map_smul_eq_mul p a x).le

theorem bounded_of_weak [TopologicalSpace E] [IsTopologicalAddGroup E] {T : Type} (f : T → E)
    (h : ∀ l : E →L[ℂ] ℂ, ∃ C : ℝ, ∀ t, ‖l (f t)‖ ≤ C) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ C : ℝ, ∀ t, p (f t) ≤ C := by
  apply PositivityTheory.ThKG.Loc.Bump.weak_bounded <;> assumption

end Weak

section Tame

variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {W : Type} [SeminormedAddCommGroup W]

def Tame (R : W → E →ₗ[ℂ] E) : Prop :=
  ∀ p : Seminorm ℂ E, Continuous p → ∃ (q : Seminorm ℂ E) (M : ℕ), Continuous q ∧
    ∀ w f, p (R w f - f) ≤ ‖w‖ * (1 + ‖w‖) ^ M * q f

theorem continuous_smul_semi (c : ℝ) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ f, q' f = |c| * q f :=
  ⟨(‖c‖₊ : NNReal) • q, (continuous_const.mul hq : Continuous fun f => |c| * q f), fun _ => rfl⟩

theorem Tame.growth {R : W → E →ₗ[ℂ] E} (h : Tame R) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ (q : Seminorm ℂ E) (M : ℕ), Continuous q ∧ ∀ w f, p (R w f) ≤ (1 + ‖w‖) ^ M * q f := by
  obtain ⟨q, M, hq, hb⟩ := h p hp
  refine ⟨p + q, M + 1, (hp.add hq : Continuous fun f => p f + q f), fun w f => ?_⟩
  have h1 : p (R w f) ≤ p (R w f - f) + p f := by
    simpa using map_add_le_add p (R w f - f) f
  have h2 := hb w f
  have h3 : 1 ≤ (1 + ‖w‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg w])
  have hp0 := apply_nonneg p f
  have hq0 := apply_nonneg q f
  have hw := norm_nonneg w
  rw [Seminorm.add_apply, pow_succ]
  nlinarith [mul_nonneg hw hp0, mul_nonneg (mul_nonneg hw hp0) (sub_nonneg.2 h3), mul_nonneg hp0 (sub_nonneg.2 h3),
    mul_nonneg hq0 (sub_nonneg.2 h3)]

theorem Tame.iter {R : W → E →ₗ[ℂ] E} (h : Tame R) (j : ℕ) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ u, ‖u‖ ≤ 1 → ∀ f, p (((R u - 1) ^ j) f) ≤ ‖u‖ ^ j * q f := by
  induction j with
  | zero => exact ⟨p, hp, fun u _ f => by simp⟩
  | succ j ih =>
    obtain ⟨q, hq, hb⟩ := ih
    obtain ⟨q₁, M, hq₁, hb₁⟩ := h q hq
    obtain ⟨q₂, hq₂, e₂⟩ := continuous_smul_semi (2 ^ M) q₁ hq₁
    refine ⟨q₂, hq₂, fun u hu f => ?_⟩
    rw [pow_succ, Module.End.mul_apply]
    refine (hb u hu _).trans ?_
    rw [pow_succ, mul_assoc, e₂, abs_of_nonneg (by positivity)]
    gcongr
    rw [LinearMap.sub_apply, Module.End.one_apply, ← mul_assoc]
    refine (hb₁ u f).trans ?_
    gcongr
    linarith

theorem Tame.decay {R : W → E →ₗ[ℂ] E} (h : Tame R) (p : Seminorm ℂ E) (hp : Continuous p) (A C : ℝ) (N : ℕ) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ (s : W) (r : ℝ), 0 ≤ r → ‖s‖ ≤ A * r →
      (0 < r → ∃ u, ‖u‖ * r ≤ C ∧ ∀ f, p (R s (R u f + f)) = 0) → ∀ f, p (R s f) ≤ q f * (1 + r) ^ (-(N : ℝ)) := by
  obtain ⟨q₁, M, hq₁, hb₁⟩ := h.growth p hp
  obtain ⟨q₂, hq₂, hb₂⟩ := h.iter (M + N) q₁ hq₁
  set r₀ := max C 1 with hr₀
  obtain ⟨q₃, hq₃, e₃⟩ := continuous_smul_semi ((1 + |A|) ^ M * (1 + r₀) ^ (M + N)) q₁ hq₁
  obtain ⟨q₄, hq₄, e₄⟩ := continuous_smul_semi ((1 + |A|) ^ M * (2 * r₀) ^ (M + N)) q₂ hq₂
  have hr1 : 1 ≤ r₀ := le_max_right _ _
  refine ⟨q₃ + q₄, (hq₃.add hq₄ : Continuous fun f => q₃ f + q₄ f), fun s r hr hs hu f => ?_⟩
  have hs' : 1 + ‖s‖ ≤ (1 + |A|) * (1 + r) := by
    nlinarith [le_abs_self A, abs_nonneg A, mul_le_mul_of_nonneg_right (le_abs_self A) hr]
  have hpow : (1 + ‖s‖) ^ M ≤ (1 + |A|) ^ M * (1 + r) ^ M := by
    rw [← mul_pow]; gcongr
  rw [Real.rpow_neg (by linarith), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity), Seminorm.add_apply]
  have h3 := apply_nonneg q₃ f
  have h4 := apply_nonneg q₄ f
  rcases le_or_gt r r₀ with hrr | hrr
  · refine le_trans ?_ (le_add_of_nonneg_right h4)
    rw [e₃, abs_of_nonneg (by positivity)]
    calc p (R s f) * (1 + r) ^ N ≤ ((1 + |A|) ^ M * (1 + r) ^ M * q₁ f) * (1 + r) ^ N := by
          gcongr; exact (hb₁ s f).trans (by gcongr)
      _ = (1 + |A|) ^ M * (1 + r) ^ (M + N) * q₁ f := by ring
      _ ≤ _ := by gcongr
  · refine le_trans ?_ (le_add_of_nonneg_left h3)
    obtain ⟨u, huC, hu0⟩ := hu (by linarith)
    have hC : C ≤ r₀ := le_max_left _ _
    have hu1 : ‖u‖ ≤ 1 := by
      by_contra hcon
      nlinarith [not_le.1 hcon]
    have hstep : ∀ g, p (R s g) ≤ p (R s ((R u - 1) g)) := fun g => by
      have e1 : (2 : ℂ) • R s g = R s (R u g + g) - R s ((R u - 1) g) := by
        rw [← map_sub, ← map_smul, LinearMap.sub_apply, Module.End.one_apply, two_smul]; congr 1; abel
      have e2 := map_sub_le_add p (R s (R u g + g)) (R s ((R u - 1) g))
      rw [← e1, map_smul_eq_mul, hu0] at e2
      have := apply_nonneg p (R s g)
      simp only [Complex.norm_ofNat] at e2
      linarith
    have hit : ∀ j : ℕ, p (R s f) ≤ p (R s (((R u - 1) ^ j) f)) := fun j => by
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact ih.trans (hstep _)
    have hur : ‖u‖ * (1 + r) ≤ 2 * r₀ := by nlinarith
    rw [e₄, abs_of_nonneg (by positivity)]
    calc p (R s f) * (1 + r) ^ N ≤ ((1 + |A|) ^ M * (1 + r) ^ M * (‖u‖ ^ (M + N) * q₂ f)) * (1 + r) ^ N := by
          gcongr
          refine (hit (M + N)).trans ((hb₁ s _).trans ?_)
          gcongr
          exact hb₂ u hu1 f
      _ = (1 + |A|) ^ M * (‖u‖ * (1 + r)) ^ (M + N) * q₂ f := by rw [mul_pow ‖u‖]; ring
      _ ≤ _ := by gcongr

end Tame

section Heis

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : Type} [SeminormedAddCommGroup W]

def heisOp (L : V →L[ℝ] ℝ) (k : ℝ) (a : V) : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k))).comp (SchwartzMap.compSubConstCLM ℂ (-a))

theorem tame_heisOp
    (hT : ∀ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p →
      ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (a : V) (f : SchwartzMap V ℂ),
        p (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ M * q f)
    (hP : ∀ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p →
      ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (L : V →L[ℝ] ℝ) (k : ℝ) (f : SchwartzMap V ℂ),
        p (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ M * q f)
    (L : W → V →L[ℝ] ℝ) (k : W → ℝ) (a : W → V) (c : ℝ) (hc : 1 ≤ c) (hL : ∀ w, ‖L w‖ ≤ c * ‖w‖)
    (hk : ∀ w, |k w| ≤ c * ‖w‖ ^ 2) (ha : ∀ w, ‖a w‖ ≤ ‖w‖) :
    Tame fun w => (heisOp (L w) (k w) (a w)).toLinearMap := by
  intro p hp
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := hP p hp
  obtain ⟨q₂, M₂, hq₂, hb₂⟩ := hT p hp
  have hTt : Tame fun a : V => (SchwartzMap.compSubConstCLM ℂ (-a) : SchwartzMap V ℂ →L[ℂ] _).toLinearMap := hT
  obtain ⟨q₃, M₃, hq₃, hb₃⟩ := hTt.growth q₁ hq₁
  obtain ⟨q₄, hq₄, e₄⟩ := continuous_smul_semi (c ^ (M₁ + 1)) q₃ hq₃
  refine ⟨q₂ + q₄, M₁ + M₂ + M₃ + 1, (hq₂.add hq₄ : Continuous fun f => q₂ f + q₄ f), fun w f => ?_⟩
  set g := SchwartzMap.compSubConstCLM ℂ (-(a w)) f with hg
  have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L w y + k w)) g - g) (g - f)
  rw [sub_add_sub_cancel] at h1
  refine le_trans h1 ?_
  have hw := norm_nonneg w
  have h1w : 1 ≤ 1 + ‖w‖ := by linarith
  have hc0 : 0 < c := by linarith
  rw [Seminorm.add_apply, mul_add, add_comm]
  refine add_le_add ((hb₂ _ f).trans ?_) ((hb₁ _ _ g).trans ?_)
  · have := ha w
    calc _ ≤ ‖w‖ * (1 + ‖w‖) ^ M₂ * q₂ f := by gcongr
      _ ≤ _ := by gcongr; omega
  · have h2 : q₁ g ≤ (1 + ‖w‖) ^ M₃ * q₃ f := (hb₃ (a w) f).trans (by have := ha w; gcongr)
    have h3 : ‖L w‖ + |k w| ≤ c * (‖w‖ * (1 + ‖w‖)) := by nlinarith [hL w, hk w]
    have h4 : 1 + ‖L w‖ ≤ c * (1 + ‖w‖) := by nlinarith [hL w]
    rw [e₄, abs_of_nonneg (pow_nonneg hc0.le _)]
    have h5 := apply_nonneg q₃ f
    have h6 := apply_nonneg q₁ g
    calc _ ≤ c * (‖w‖ * (1 + ‖w‖)) * (c * (1 + ‖w‖)) ^ M₁ * ((1 + ‖w‖) ^ M₃ * q₃ f) := by gcongr
      _ = ‖w‖ * (1 + ‖w‖) ^ (M₁ + M₃ + 1) * (c ^ (M₁ + 1) * q₃ f) := by rw [mul_pow c]; ring
      _ ≤ _ := by gcongr; omega

end Heis

end GlobalTheory.DiffDecay

end
end

section

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

theorem _root_.GlobalTheory.T.mem_filtration_of_components_mem_eigenSpan : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F := by
  first | exact @GlobalTheory.Div.KerFil.mem_of_components | exact GlobalTheory.Div.KerFil.mem_of_components | (intros; apply GlobalTheory.Div.KerFil.mem_of_components <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.exists_balanced_unit_multiple_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ C : ℝ, 1 ≤ C ∧
    ∀ b : F, b ≠ 0 → ∃ ε : (𝓞 F)ˣ, ∀ τ τ' : Emb F, |τ (((ε : 𝓞 F) : F) * b)| ≤ C * |τ' (((ε : 𝓞 F) : F) * b)| := by
  first | exact @GlobalTheory.BalancedUnits.balanced_unit_multiple | exact GlobalTheory.BalancedUnits.balanced_unit_multiple | (intros; apply GlobalTheory.BalancedUnits.balanced_unit_multiple <;> assumption)
end

section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  first | exact @GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound | exact GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound | (intros; apply GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.upperHalfPlaneProduct_prod_im_rpow_contDiffOn : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), ContDiffOn ℝ ∞ (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  first | exact @GlobalTheory.upperHalf_prodImPow_contDiffOn | exact GlobalTheory.upperHalf_prodImPow_contDiffOn | (intros; apply GlobalTheory.upperHalf_prodImPow_contDiffOn <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.partialZeta_totallyReal_at_most_simple_pole : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (C C' : ClassGroup (NumberField.RingOfIntegers F)) (Z Z' : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C' Z' → (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)) → ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ ∀ s : ℂ, s ≠ 1 → Z s = R s / (s - 1) := by
  first | exact @GlobalTheory.ZetaPole.zeta_simple_pole | exact GlobalTheory.ZetaPole.zeta_simple_pole | (intros; apply GlobalTheory.ZetaPole.zeta_simple_pole <;> assumption)
end

section

namespace GlobalTheory.NormBoundSumSquares

theorem norm_le_one_of_sum_sq_lt_one :
    (let d1 : {E : Type} → [inst : Field E] → [NumberField E] → {a : ℕ} → GlobalTheory.CuspRep.Lie E a → ℝ := @(fun {E : Type} [Field E] [NumberField E] {a : ℕ} (x : GlobalTheory.CuspRep.Lie E a) ↦ ∑ w : NumberField.InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a, ‖x i j w‖ ^ (2 : ℕ)); ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ} (x : GlobalTheory.CuspRep.Lie E a), d1 x < (1 : ℝ) → ‖x‖ ≤ (1 : ℝ)) := by
  intro d1 E _ _ _ a x hx
  have hsum : ∑ w : NumberField.InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a, ‖x i j w‖ ^ (2 : ℕ) < 1 := hx
  have entry : ∀ (i j : Fin a) (w : NumberField.InfinitePlace E), ‖x i j w‖ ≤ 1 := by
    intro i j w
    by_contra hcon
    have hgt : 1 < ‖x i j w‖ := lt_of_not_ge hcon
    have hsq : 1 < ‖x i j w‖ ^ (2 : ℕ) := one_lt_pow₀ hgt (by norm_num)
    have h₃ : ‖x i j w‖ ^ (2 : ℕ) ≤ ∑ j' : Fin a, ‖x i j' w‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun j' => ‖x i j' w‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ j)
    have h₂ : ∑ j' : Fin a, ‖x i j' w‖ ^ (2 : ℕ)
        ≤ ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun i' => ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have h₁ : ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ)
        ≤ ∑ w' : NumberField.InfinitePlace E, ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w'‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun w' => ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w'‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ w)
    linarith
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => entry i j w

end GlobalTheory.NormBoundSumSquares
end
