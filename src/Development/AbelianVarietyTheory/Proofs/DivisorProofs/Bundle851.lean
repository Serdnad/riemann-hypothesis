module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle757
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle592
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle845
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle823
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle826
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle819
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle004
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.LieVal

open GlobalTheory.CatCoh

private theorem thickHomExt {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
    {pd : DividedPowers I} {s : X ⟶ Sp R} {T T' : Thick pd s} {f g : T ⟶ T'}
    (h : ∀ b, f.φ b = g.φ b) : f = g := by
  have hφ : f.φ = g.φ := AlgHom.ext h
  rcases f with ⟨φ, φ₀, comm, dp, pt⟩
  rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
  obtain rfl : φ = ψ := hφ
  obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := T.surj c
    rw [comm, comm']
  rfl

theorem main : ∀ {A : Over (Sp ℂ)} {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol F.V))) (k : K.K) (p : Tot I g), p ∈ K.W k → ∀ (w : Fin g → ℂ) (ρ : Hol (K.W k) →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p (0, w)) → ∀ (v : epsR ℂ ⟶ A), v.left = spMap ρ.toRingHom ≫ r.x k → ∀ (f : Form (A.hom ≫ 𝟙 _)) (per : Λ →+ Hol F.V) (q : GlobalTheory.CatCoh.C0 K.Oc), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 → tanVal v f = fderiv ℂ (Hol.fn (W := K.W k) (q (K.triv k))) p (0, w) := by
  intro A I _ g Λ _ F K r k p hp w ρ hρ v hv f per q hq
  let e : Hol (K.W k) →+* DualNumber ℂ := (TrivSqZeroExt.inlHom ℂ ℂ).comp (Hol.ev p hp).toRingHom
  let T : K.Obj :=
    { k := k, C := DualNumber ℂ, alg := (e.comp (K.cst k)).toAlgebra
      J := RingHom.ker ((SqExt.dual ℂ).π : DualNumber ℂ →+* ℂ)
      nil := ⟨2, (SqExt.dual ℂ).sq⟩, ρ := e, ρ_cst := fun _ ↦ rfl }
  have hder : ∀ h : Hol (K.W k), fderiv ℂ h.fn p (0, w) = ∑ a, (dw a h).fn p * w a := fun h ↦ by
    have : ((0, w) : Tot I g) = ∑ a, w a • ((0, Pi.single a 1) : Tot I g) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp only [Prod.snd_sum, Prod.smul_snd]
        exact pi_eq_sum_univ' w

    rw [this, map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    exact congrArg (· * w a) (Hol.fn_der _ h hp).symm
  have hexp : ∀ h : Hol (K.W k), ρ h = e h + ∑ a, e (dw a h) * TrivSqZeroExt.inr (w a) := fun h ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [(hρ h).1]
      simp [e, TrivSqZeroExt.fst_sum, Hol.ev_apply]
    · rw [(hρ h).2, hder]
      simp [e, TrivSqZeroExt.snd_sum, Hol.ev_apply, mul_comm]
  let a : K.triv k ⟶ T := Charts.ptHom T (K.le_refl k)
  let b : K.triv k ⟶ T := Charts.fromTriv T (K.le_refl k) ρ.toRingHom
    (fun c ↦ by
      change ρ (K.cst k c) = e (K.cst k c)
      rw [hexp]; simp [Charts.dw_cst])
    (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (w a), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, Charts.sh_refl]
        exact hexp h⟩)
  have ea := congrFun (congrFun (congrFun hq _) _) a
  have eb := congrFun (congrFun (congrFun hq _) _) b
  change ((show DualNumber ℂ from q T) - e (Charts.sh (K.le_refl k) (q (K.triv k))) : DualNumber ℂ) =
    (show DualNumber ℂ from ev f.1 (r.functor.map a)) - e (K.cst k (per 0)) at ea
  change ((show DualNumber ℂ from q T) - ρ (q (K.triv k)) : DualNumber ℂ) =
    (show DualNumber ℂ from ev f.1 (r.functor.map b)) - e (K.cst k (per 0)) at eb
  rw [Charts.sh_refl] at ea
  let E := SqExt.dual ℂ
  have hfst : (E.π : E.C →+* E.B).comp ρ.toRingHom = (Hol.ev p hp).toRingHom :=
    RingHom.ext fun h ↦ (hρ h).1.trans (Hol.ev_apply p hp h).symm
  have halg : ∀ c : ℂ, e (K.cst k (algebraMap ℂ (Hol F.V) c)) = algebraMap ℂ (DualNumber ℂ) c := fun c ↦ by
    have : K.cst k (algebraMap ℂ (Hol F.V) c) = algebraMap ℂ (Hol (K.W k)) c := rfl
    rw [this]
    change TrivSqZeroExt.inl (Hol.ev p hp (algebraMap ℂ _ c)) = _
    rw [AlgHom.commutes]; rfl
  let Φ : E.thick _ (E.red_w (pt_w v)) ⟶ r.obj T :=
    { φ := { RingHom.id (DualNumber ℂ) with commutes' := fun c ↦ (halg c).symm }
      φ₀ := (Ideal.Quotient.mk T.J).comp (TrivSqZeroExt.inlHom ℂ ℂ)
      comm := fun c ↦ Ideal.Quotient.eq.2 (by
        change (TrivSqZeroExt.inl (TrivSqZeroExt.fst (R := ℂ) (M := ℂ) c) - (show TrivSqZeroExt ℂ ℂ from c)).fst = 0
        rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, sub_self])
      dp := isDPMorphism_of_rat (C' := DualNumber ℂ) _ _ _ fun c hc ↦ hc
      pt := by
        have h0 : spMap ((Ideal.Quotient.mk T.J).comp (TrivSqZeroExt.inlHom ℂ ℂ)) ≫
            spMap (E.π : E.C →+* E.B) ≫ v.left = spMap ((Ideal.Quotient.mk T.J).comp e) ≫ r.x k := by
          rw [hv, ← Category.assoc (spMap (E.π : E.C →+* E.B)), ← Cris.spMap_comp, hfst, ← Category.assoc,
            ← Cris.spMap_comp]
        exact h0 }
  have mkHom : ∀ (C : Type) [CommRing C] [Algebra ℂ C] (ψ : Hol (K.W k) →ₐ[ℂ] C) (y : Sp C ⟶ A.left)
      (hy : y ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap ℂ C)), y = spMap ψ.toRingHom ≫ r.x k →
      ∃ m : r.obj (K.triv k) ⟶ Thick.triv C y hy, ∀ c, m.φ c = ψ c := fun C _ _ ψ y hy e' ↦
    ⟨{ φ := { ψ.toRingHom with commutes' := fun c ↦ ψ.commutes c }
       φ₀ := Ideal.Quotient.lift ⊥ ψ.toRingHom fun c hc ↦ by rw [Ideal.mem_bot.1 hc, map_zero]
       comm := fun _ ↦ rfl
       dp := isDPMorphism_of_eq_bot _ rfl _ _
       pt := by
        refine Eq.trans ?_ e'.symm
        refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ r.x k) ?_)
        exact (Cris.spMap_comp _ _).symm }, fun _ ↦ rfl⟩
  obtain ⟨a', ha'⟩ := mkHom ℂ (Hol.ev p hp) _ (E.red_w (pt_w v)) (by
    rw [hv, ← Category.assoc, ← Cris.spMap_comp, hfst])
  obtain ⟨b', hb'⟩ := mkHom (DualNumber ℂ) ρ v.left (pt_w v) hv
  have e1 : r.functor.map a = a' ≫ E.secHom (E.red_w (pt_w v)) E.i E.π_i ≫ Φ := thickHomExt fun c ↦ by
    change e (Charts.sh (K.le_refl k) c) = TrivSqZeroExt.inl (a'.φ c)
    exact (congrArg e (Charts.sh_refl _ c)).trans (congrArg TrivSqZeroExt.inl (ha' c).symm)
  have e2 : r.functor.map b = b' ≫ E.idHom (pt_w v) ≫ Φ := thickHomExt fun c ↦ (hb' c).symm
  have z1 : ev f.1 a' = 0 := f.2 a' rfl rfl
  have z2 : ev f.1 b' = 0 := f.2 b' rfl rfl
  have g1 : ev f.1 (r.functor.map a) = Φ.φ (ev f.1 (E.secHom (E.red_w (pt_w v)) E.i E.π_i)) + ev f.1 Φ := by
    rw [e1]
    refine (ev_comp f.1 a' _).trans ?_
    rw [z1, map_zero, zero_add]
    exact ev_comp f.1 _ Φ
  have g2 : ev f.1 (r.functor.map b) = Φ.φ (ev f.1 (E.idHom (pt_w v))) + ev f.1 Φ := by
    rw [e2]
    refine (ev_comp f.1 b' _).trans ?_
    rw [z2, map_zero, zero_add]
    exact ev_comp f.1 _ Φ
  rw [g1] at ea
  rw [g2] at eb
  have key : (E.val v.left (pt_w v) f.1 : DualNumber ℂ) = ρ (q (K.triv k)) - e (q (K.triv k)) := by
    rw [SqExt.val_apply]
    have aux : ∀ x y z u s t c : DualNumber ℂ, x - y = s + u - c → x - z = t + u - c → s - t = z - y :=
      fun x y z u s t c h1 h2 ↦ by linear_combination h2 - h1
    exact aux _ _ _ _ _ _ _ ea eb
  rw [tanVal_apply, key, TrivSqZeroExt.snd_sub, (hρ _).2]
  exact sub_zero _

end GlobalTheory.AnPer.LieVal
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem exists_torsion_matrix : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), ∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k' := by
  intro K _ _ ι g t Λ₀ Λ₁ Ω₀ Ω₁ h c₀ c₁ τ₀ τ₁ h₀ h₁ N _
  obtain ⟨a, b, c⟩ := GlobalTheory.T.latticeCorrespondence_torsion_relation_properties K ι Λ₀ Λ₁ (Tr t) c₀ c₁ τ₀ τ₁
    (GlobalTheory.T.isLatticeQuotientCorrespondence_of_torsionTransport K ι g t Λ₀ Λ₁ Ω₀ Ω₁ h) h₀ h₁ N
    (fun x y => ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ y ∧ Tr t k k')
    (fun _ _ => Iff.rfl)
  exact GlobalTheory.T.additive_bijective_relation_rowVec_eq_matrix N _ a b c

end GlobalTheory.WpFam
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.every_element_is_norm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F'), ∃ γ : GL (Fin n) F, IsNorm s δ γ := by
  first | (exact @GlobalTheory.Shin.exists_isNorm) | (exact GlobalTheory.Shin.exists_isNorm) | (intros; apply GlobalTheory.Shin.exists_isNorm  <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.WpFam

namespace GlobalTheory.WpFamGL

theorem transport_GL : ∀ (g : ℂ ≃+* ℂ) (N N' w : ℕ) [NeZero N] (a : (ZMod N)ˣ) (A : GL (Fin 2) (ZMod N)) (F F' : GL (Fin 2) (ZMod N) → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N' → N ∣ N' → ZetaAct g N a → IsFam (gact N 1) w F → (∀ α, QConj g N' (F α) (F' (α * dg a))) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → (∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3) → ∀ α, g (F α τ₀ / ω₀ ^ w) = F' (α * A) τ₁ / ω₁ ^ w := by
  classical
  intro g N N' w _ a A F F' τ₀ τ₁ ω₀ ω₁ hN' hdiv hζ hF hFF' hω₀ h4 h6 hwp α
  let e : Fin 2 → Fin 2 → ZMod N := fun i => Pi.single i 1
  let m : Fin 2 × Bool → ℕ := fun s => if s.2 then 3 else 2
  let u : Fin 2 × Bool → GL (Fin 2) (ZMod N) → ℍ → ℂ := fun s β =>
    if s.2 then wpd N (vmul (e s.1) (β * 1)) else wp N (vmul (e s.1) (β * 1))
  let u' : Fin 2 × Bool → GL (Fin 2) (ZMod N) → ℍ → ℂ := fun s β => u s (β * dg a)
  have hact : ActBij (gact N 1) := (GlobalTheory.WpFam.Act.isRAct_gact N 1).actBij
  have hu : ∀ s, IsFam (gact N 1) (m s) (u s) := by
    rintro ⟨i, _ | _⟩
    · simpa [m, u] using (GlobalTheory.WpFamGL.main N 1 (e i)).1
    · simpa [m, u] using (GlobalTheory.WpFamGL.main N 1 (e i)).2
  have huu' : ∀ s β, QConj g N' (u s β) (u' s β) := by
    rintro ⟨i, _ | _⟩ β
    · have h := (GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hζ (vmul (e i) β)).1
      rw [GlobalTheory.WpFam.Act.vmul_vmul] at h
      simpa [u, u'] using h.of_dvd hN' hdiv
    · have h := (GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hζ (vmul (e i) β)).2.1
      rw [GlobalTheory.WpFam.Act.vmul_vmul] at h
      simpa [u, u'] using h.of_dvd hN' hdiv
  have hsep : ∀ β, (∀ s, u s β τ₀ = u s α τ₀) → F β τ₀ = F α τ₀ := by
    intro β hβ
    have : β = α := GlobalTheory.WpFam.SepGL.main N τ₀ β α fun i =>
      ⟨by simpa [u] using hβ (i, false), by simpa [u] using hβ (i, true)⟩
    rw [this]
  have hα : α * A * (dg a)⁻¹ * dg a = α * A := by group
  have hval : ∀ s, g (u s α τ₀ / ω₀ ^ m s) = u' s (α * A * (dg a)⁻¹) τ₁ / ω₁ ^ m s := by
    rintro ⟨i, _ | _⟩
    · simpa [u, u', m, hα, GlobalTheory.WpFam.Act.vmul_vmul] using (hwp (vmul (e i) α)).1
    · simpa [u, u', m, hα, GlobalTheory.WpFam.Act.vmul_vmul] using (hwp (vmul (e i) α)).2
  have key := GlobalTheory.QFam.transport_of_separating g (GL (Fin 2) (ZMod N)) (Fin 2 × Bool) (gact N 1) N' w
    m F (fun β => F' (β * dg a)) u u' τ₀ τ₁ ω₀ ω₁ hN' hact hF hu hFF' huu' hω₀ h4 h6 α
    (α * A * (dg a)⁻¹) hsep hval
  simpa [hα] using key

end GlobalTheory.WpFamGL
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem peak_isSecOn {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (la : La) (i : ι) (W : Set Y) (hW : W ⊆ (A.chart i).source)
    (u : V n → ℂ) (hu : Differentiable ℂ u) :
    A.IsSecOn la W (fun j y => A.g la j i y * u (A.chart i y)) := by
  refine ⟨fun j => ?_, fun j l y hy hj hl => ?_⟩
  · have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' W ⊆ ovl A.chart j i :=
      fun v hv => ⟨hv.1, hW hv.2⟩
    have h1 := (A.holo_g la j i).mono hsub
    have h2 := hu.comp_differentiableOn ((A.holo_trans j i).mono hsub)
    exact h1.mul h2
  · show A.g la j i y * _ = A.g la j l y * (A.g la l i y * _)
    rw [A.g_cocycle la j l i y hj hl (hW hy)]; ring

theorem peak_section : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La) (i : ι) (p : V n) (ρ c : ℝ) (q f : V n → ℂ), 0 < ρ → 0 < c → closedBall p ρ ⊆ (A.chart i).target → Differentiable ℂ q → Differentiable ℂ f → (∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ A.ph H i ((A.chart i).symm v) - 2 * (q v).re) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ v ∈ ball p (ρ / 2), F0 i ((A.chart i).symm v) = f v * Complex.exp (k * q v)) ∧ (∀ j y, y ∉ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ → F0 j y = 0) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
  intro n Y _ _ _ _ _ ι La _ A C H G i p ρ c q f hρ hc hball hq hf hpeak
  obtain ⟨χ, hχs, hχsupp, hχ1⟩ := GlobalTheory.T.smooth_bump_chart_ball_halfOne n Y ι La A i p ρ hρ hball
  obtain ⟨K0, hK0, hcut⟩ := GlobalTheory.T.n1_cutoff_mul_section_le_lintegral n Y ι La A C χ hχs
  set W : Set Y := (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ with hWdef
  set Wi : Set Y := (A.chart i).source ∩ A.chart i ⁻¹' ball p (ρ / 2) with hWidef
  have hWo : IsOpen W := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hWio : IsOpen Wi := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hWs : W ⊆ (A.chart i).source := Set.inter_subset_left
  set Z : Set Y := W \ Wi with hZdef
  have hZm : MeasurableSet Z := hWo.measurableSet.diff hWio.measurableSet
  have hZloc : ∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hyi : y ∈ Wi := by
        by_contra h
        exact hy ⟨hyW, h⟩
      filter_upwards [hWio.mem_nhds hyi] with x hx
      rw [hχ1 x hx.1 hx.2, hχ1 y hyi.1 hyi.2]
    · have hns : y ∉ tsupport χ := fun h => hyW (hχsupp h)
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hns] with x hx
      rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hns]
  have hKc : IsCompact ((A.chart i).symm '' closedBall p ρ) :=
    (isCompact_closedBall p ρ).image_of_continuousOn ((A.chart i).continuousOn_symm.mono hball)
  have hWK : Z ∩ W ⊆ (A.chart i).symm '' closedBall p ρ := fun y hy =>
    ⟨A.chart i y, ball_subset_closedBall hy.2.2, (A.chart i).left_inv hy.2.1⟩
  have hfin : A.mu (Z ∩ W) ≠ ⊤ :=
    ((measure_mono hWK).trans_lt (ap_mu_compact A _ hKc)).ne
  have hcont : ContinuousOn (fun v => ‖f v‖ ^ 2 *
      Real.exp (-A.ph (A.kap + G) i ((A.chart i).symm v))) (closedBall p ρ) :=
    (hf.continuous.continuousOn.norm.pow 2).mul
      (((A.smooth_ph (A.kap + G) i).continuousOn.mono hball).neg.rexp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall p ρ).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p (mem_closedBall_self hρ.le))
  refine ⟨K0 * (M * (A.mu (Z ∩ W)).toReal), by positivity, fun k => ?_⟩
  have hu : Differentiable ℂ (fun v => f v * Complex.exp (k * q v)) :=
    hf.mul ((hq.const_mul _).cexp)
  have hsec := peak_isSecOn A (A.kap + (G + k • H)) i W hWs _ hu
  refine ⟨_, GlobalTheory.T.smoothSection_cutoff_mul_holomorphic n Y ι La A _ W χ _ hWo hχs hχsupp hsec, ?_, ?_, ?_⟩
  · intro v hv
    have hvt : v ∈ (A.chart i).target :=
      hball (ball_subset_closedBall (ball_subset_ball (by linarith) hv))
    have hs := (A.chart i).map_target hvt
    have hr := (A.chart i).right_inv hvt
    have h1 : χ ((A.chart i).symm v) = 1 := hχ1 _ hs (by rw [hr]; exact hv)
    simp only [h1, A.g_self _ i hs, hr]
    simp
  · intro j y hy
    have hns : y ∉ tsupport χ := fun h => hy (hχsupp h)
    simp [image_eq_zero_of_notMem_tsupport hns]
  · refine (hcut (G + k • H) W Z _ hWo hχsupp hsec hZm hZloc).trans ?_
    have hbd : ∀ y ∈ Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + (G + k • H))
        (fun j y => A.g (A.kap + (G + k • H)) j i y *
          (f (A.chart i y) * Complex.exp (k * q (A.chart i y)))) y) ≤
        ENNReal.ofReal (M * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      have hs : y ∈ (A.chart i).source := hy.2.1
      have hcb : A.chart i y ∈ closedBall p ρ := ball_subset_closedBall hy.2.2
      have hout : ρ / 2 ≤ ‖A.chart i y - p‖ := by
        by_contra h
        exact hy.1.2 ⟨hs, by simpa [mem_ball, dist_eq_norm] using not_le.1 h⟩
      rw [A.nsq_chart _ _ i hs (hsec.2 _ i y hy.2 (A.mem_pick y) hs)]
      have h1 := hM _ hcb
      have h2 := hpeak _ hcb
      rw [(A.chart i).left_inv hs] at h1 h2
      rw [Real.norm_of_nonneg (by positivity)] at h1
      have h3 : c * ρ ^ 2 / 4 ≤ c * ‖A.chart i y - p‖ ^ 2 := by
        have : (ρ / 2) ^ 2 ≤ ‖A.chart i y - p‖ ^ 2 := by gcongr
        nlinarith
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have e : ‖A.g (A.kap + (G + k • H)) i i y *
          (f (A.chart i y) * Complex.exp (k * q (A.chart i y)))‖ ^ 2 *
          Real.exp (-A.ph (A.kap + (G + k • H)) i y) =
          (‖f (A.chart i y)‖ ^ 2 * Real.exp (-A.ph (A.kap + G) i y)) *
          Real.exp (-(A.ph H i y - 2 * (q (A.chart i y)).re) * k) := by
        rw [A.g_self _ i hs, one_mul, norm_mul, Complex.norm_exp, ← add_assoc,
          A.ph_add _ (k • H) i y hs, A.aap_ph_nsmul H k i hs, mul_pow, ← Real.exp_nat_mul,
          mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        simp
        ring
      refine e.le.trans ?_
      refine mul_le_mul h1 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hM0
      nlinarith
    have hint := setLIntegral_mono' (μ := A.mu) (hZm.inter hWo.measurableSet) hbd
    rw [setLIntegral_const] at hint
    refine (mul_le_mul_right hint _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hK0, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    ring

end GlobalTheory.OTY
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.subsingleton_invariantDifferentials_of_etale : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  first | exact @GlobalTheory.PDivGroup.subsingleton_omega_of_isEt | exact GlobalTheory.PDivGroup.subsingleton_omega_of_isEt | (intros; apply GlobalTheory.PDivGroup.subsingleton_omega_of_isEt <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), G.IsConn → Function.Surjective (omegaMap G H q) → ∀ n, Function.Surjective (q.app n) := by
  first | exact @GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective | exact GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective | (intros; apply GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.weil_representation_preserves_L2_space : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure] (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)), ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' := by
  first | exact @GlobalTheory.KSp.weil_representation_preserves_L2 | exact GlobalTheory.KSp.weil_representation_preserves_L2 | (intros; apply GlobalTheory.KSp.weil_representation_preserves_L2 <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.splitUnitaryWeilRepresentation_isSmooth : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → GlobalTheory.SplitWeil.IsSmoothRep ω := by
  first | exact @GlobalTheory.KSp.isKW_isSmoothRep | exact GlobalTheory.KSp.isKW_isSmoothRep | (intros; apply GlobalTheory.KSp.isKW_isSmoothRep <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → ∀ x : E, x ≠ 0 → x ∈ orderC c → x⁻¹ ∈ orderC c → ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by
  first | exact @GlobalTheory.CMVal.OrderUnits.orderC_units | exact GlobalTheory.CMVal.OrderUnits.orderC_units | (intros; apply GlobalTheory.CMVal.OrderUnits.orderC_units <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R}

def crysAct (o₀ : GlobalTheory.UPel.HT.Obj b N t) : D.O →+* Module.End k (HdR o₀.A) :=
  RingHom.mk'
    { toFun x := haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)
      map_one' := by
        haveI := o₀.act.hom 1
        exact (push_congr (dp0 k) (𝟙 _) o₀.act.one).trans (push_id (dp0 k) (𝟙 _))
      map_mul' x y := by
        haveI := o₀.act.hom
        exact (push_congr (dp0 k) (𝟙 _) (o₀.act.mul x y)).trans (push_comp (dp0 k) (𝟙 _) _ _) }
    fun x y ↦ by
      haveI := o₀.act.hom
      haveI : IsMonHom (o₀.act.act x * o₀.act.act y) := o₀.act.add x y ▸ o₀.act.hom _
      exact (push_congr (dp0 k) (𝟙 _) (o₀.act.add x y)).trans (push_mul (dp0 k) (𝟙 _) _ _)

theorem crysAct_apply (o₀ : GlobalTheory.UPel.HT.Obj b N t) (x : D.O) :
    crysAct o₀ x = (haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)) := rfl

def rhoPart (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1)

def lieZ (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  Submodule.span k {z | ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → 𝓞 D.F) (y : HdR o₀.A), y ∈ rhoPart o₀ β ∧
    (∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) ∧ z = ∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y}

end GlobalTheory.HTCount
end
end
