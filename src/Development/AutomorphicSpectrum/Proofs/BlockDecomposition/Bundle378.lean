module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupH0NormalCoboundary
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticUniformization
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionLattice
public import GroundTheory.GlobalFields.ComplexMultiplication.IdeleAction
public import GroundTheory.GlobalFields.ComplexMultiplication.IdeleActionQuotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle369
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle368
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle370
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFil

theorem isFil_thFil : ∀ {b : Base} (L : b.Fun), IsFil (thP L) (thFil L) := by
  apply GlobalTheory.CompanionTheory.OmCls.isFil_thFil <;> assumption

end GlobalTheory.CompanionTheory.DPFil
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.compact_fixed_vector_projection : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∃ E : V →ₗ[ℂ] V, (∀ v, E v ∈ fixed π J) ∧ (∀ v ∈ fixed π J, E v = v) ∧ (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l ∘ₗ E = l) ∧ (∀ x ∈ J, E ∘ₗ π x = E) ∧ ∀ (u : V) (H : Subgroup G), H ≤ J → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) → E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  first | exact @GlobalTheory.CompanionTheory.CompactAvg.exists_average | exact GlobalTheory.CompanionTheory.CompactAvg.exists_average | (intros; apply GlobalTheory.CompanionTheory.CompactAvg.exists_average <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd.ProdSingle

theorem prodIrr_single : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (Y : Fin h → IrrGL (k := k)) (hd : ∑ a, (Y a).1 = N) (i₀ : Fin h), (∀ i, i ≠ i₀ → (Y i).1 = 0) → ∃ z : IrrCl (GL (Fin N) k), (⟨N, z⟩ : IrrGL (k := k)) = Y i₀ ∧ Nonempty ((prodIrr Y hd).Equiv z.rep.ρ) := by
  intro k _ _ _ _ h N Y hd i₀ h0
  have hN : (Y i₀).1 = N := by
    rw [← hd]
    exact (Finset.sum_eq_single i₀ (fun i _ hi => h0 i hi) (fun hi => absurd (Finset.mem_univ _) hi)).symm
  subst hN
  refine ⟨(Y i₀).2, Sigma.eta _, ?_⟩
  have hd' : ∑ a : Fin 1, (Y ((fun _ : Fin 1 => i₀) a)).1 = (Y i₀).1 := by simp
  obtain ⟨e₁⟩ := GlobalTheory.T.induced_product_drop_zero_factors Y hd (fun _ : Fin 1 => i₀) (Subsingleton.strictMono _)
    (fun j hj => ⟨0, by
      by_contra hne
      exact hj (h0 j (fun e => hne e.symm))⟩) hd'
  obtain ⟨e₂⟩ := nonempty_equiv_prodIrr_one (Y i₀) hd'
  exact ⟨e₁.trans e₂.symm⟩

end GlobalTheory.CompanionTheory.FineProd.ProdSingle
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

theorem _root_.GlobalTheory.T.product_irreducible_append_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t), Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)) := by
  first | exact @GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append | exact GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append | (intros; apply GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append <;> assumption)
end

section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticUniformization

theorem exists_analyticIso_of_isAnalyticUniformization (Λ : Submodule ℤ ℂ)
    (E : WeierstrassCurve ℂ) (f : ℂ →+ E.toAffine.Point)
    (hf : GroundTheory.Global.Elliptic.IsAnalyticUniformization Λ f) :
    ∃ ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point,
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z := by
  let φ : (ℂ ⧸ Λ.toAddSubgroup) →+ E.toAffine.Point :=
    QuotientAddGroup.lift Λ.toAddSubgroup f fun z hz => (hf.map_eq_zero_iff z).2 hz
  have hφ : ∀ z : ℂ, φ (QuotientAddGroup.mk z) = f z := fun z => rfl
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hφ] at hx
    exact (QuotientAddGroup.eq_zero_iff z).2 ((hf.map_eq_zero_iff z).1 hx)
  have hsurj : Function.Surjective φ := fun P => by
    obtain ⟨z, rfl⟩ := hf.surjective P
    exact ⟨QuotientAddGroup.mk z, hφ z⟩
  let ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point :=
    AddEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hξ : ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z := fun z => rfl
  refine ⟨ξ, fun z hz => ?_, hξ⟩
  have hz0 : f z ≠ 0 := fun h => hz ((hf.map_eq_zero_iff z).1 h)
  obtain ⟨X, Y, hX, hY, hev⟩ := hf.analyticAt_affine z hz0
  refine ⟨X, Y, hX, hY, hev.mono fun w hw => ?_⟩
  obtain ⟨h, hw⟩ := hw
  exact ⟨h, (hξ w).trans hw⟩

end GlobalTheory.CompanionTheory.EllipticUniformization
end
end

section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.EllipticDict

theorem idealLattice_toAddSubgroup_eq_idealSub :
    ∀ {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (I : FractionalIdeal (𝓞 K)⁰ K),
      (GroundTheory.Global.Elliptic.idealLattice (algebraMap K ℂ) I).toAddSubgroup =
        GlobalTheory.EllipticCM.idealSub I := by
  intro K _ _ _ I
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end GlobalTheory.CompanionTheory.EllipticDict
end

section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.EllipticCM

theorem ord_eq_ord_vw_finitePart {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    GroundTheory.Global.IdeleGroup.ord v s =
      GlobalTheory.Idele.ord_vw (GlobalTheory.EllipticCM.finitePart (K := K) s) v :=
  rfl

theorem coe_smul_eq_finitePart_smul {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s) • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
  refine GlobalTheory.Idele.eq_of_count_eq (Units.ne_zero _)
    (GlobalTheory.Idele.smul_ne_zero _ (Units.ne_zero _)) fun v => ?_
  rw [GroundTheory.Global.IdeleGroup.count_smul, GlobalTheory.Idele.count_smul _ (Units.ne_zero _),
    ord_eq_ord_vw_finitePart]

theorem inv_smul_eq_finitePart_inv_smul {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s⁻¹ • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  coe_smul_eq_finitePart_smul s⁻¹ 𝔞

end GlobalTheory.CompanionTheory.EllipticCM
end

section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.IdeleQuot

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K : Type} [Field K] [NumberField K]

theorem finitePart_apply (s : GroundTheory.Global.IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    ((GlobalTheory.EllipticCM.finitePart (K := K) s : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v =
      (GroundTheory.Global.IdeleGroup.finiteProj v s : v.adicCompletion K) := by
  rw [GroundTheory.Global.IdeleGroup.coe_finiteProj]
  rfl

theorem finitePart_inv (s : GroundTheory.Global.IdeleGroup K) :
    GlobalTheory.EllipticCM.finitePart (K := K) s⁻¹ = (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ :=
  map_inv (Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) s

theorem ord_vw_finitePart (s : GroundTheory.Global.IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    GlobalTheory.Idele.ord_vw (GlobalTheory.EllipticCM.finitePart (K := K) s) v =
      GroundTheory.Global.IdeleGroup.ord v s :=
  rfl

theorem coe_smul_eq_finitePart_smul (s : GroundTheory.Global.IdeleGroup K)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      GlobalTheory.EllipticCM.finitePart (K := K) s • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  GlobalTheory.Idele.eq_of_count_eq (Units.ne_zero _) (GlobalTheory.Idele.smul_ne_zero _ 𝔞.ne_zero) fun v => by
    rw [GroundTheory.Global.IdeleGroup.count_smul, GlobalTheory.Idele.count_smul _ 𝔞.ne_zero, ord_vw_finitePart]

theorem smulQuotient_inv_mk_eq_mk_iff_mulEquiv :
    ∀ {K : Type} [Field K] [NumberField K] (s : GroundTheory.Global.IdeleGroup K)
      (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : K),
      GroundTheory.Global.IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk y ↔
        GlobalTheory.Idele.mulEquiv (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ 𝔞.ne_zero rfl
          (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  intro K _ _ s 𝔞 x y
  rw [GroundTheory.Global.IdeleGroup.smulQuotient_mk_eq_mk_iff, GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff]
  refine forall_congr' fun v => ?_
  rw [← finitePart_inv, finitePart_apply s⁻¹ v, coe_smul_eq_finitePart_smul]
  rfl

end GlobalTheory.CompanionTheory.IdeleQuot
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.torsion_sum_zeta_bound_delta : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (r : ℝ), 1 < r → Summable (fun U : (Fin m → E) ⧸ intVec E m => (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' U : (Fin m → E) ⧸ intVec E m, (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) ≤ delta c * zetaR E r := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.delta_block_series_zeta_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

theorem idx_self_eq {d : ℕ} (I : Idx d d) : I.1 = id := by
  have hs : Function.Surjective I.1 := Finite.injective_iff_surjective.1 I.2.injective
  exact (StrictMono.range_inj I.2 strictMono_id).1 (by rw [hs.range_eq, Set.range_id])

theorem sum_idx_self {M : Type*} [AddCommMonoid M] {d : ℕ} [Fintype (Idx d d)] (g : Idx d d → M) :
    ∑ I, g I = g ⟨id, strictMono_id⟩ := by
  letI : Unique (Idx d d) :=
    { default := ⟨id, strictMono_id⟩, uniq := fun I => Subtype.ext (idx_self_eq I) }
  exact Fintype.sum_unique g

section Form
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d j : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (I : Fin j → Fin d) (u : ComposableArrows C j)

theorem form_add_fun (x x' : Φ.A.obj E.D) : E.form σ I (x + x') u = E.form σ I x u + E.form σ I x' u := by
  simp only [Frame.form, map_add (f := _), mul_add]

theorem form_sub_fun (x x' : Φ.A.obj E.D) : E.form σ I (x - x') u = E.form σ I x u - E.form σ I x' u := by
  simp only [Frame.form, map_sub, mul_sub]

theorem form_alg_mul (a : R) (x : Φ.A.obj E.D) :
    E.form σ I (algebraMap R _ a * x) u = a • E.form σ I x u := by
  simp only [Frame.form, map_mul, AlgHom.commutes, Algebra.smul_def]
  ring

end Form

theorem coef_map : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (r : ℤ), r = d → d + 1 ≤ s →
    letI := (strV q W).toAlgebra
    ∃ φ : HQ (KS q s {W}) r (r + 1) d →ₗ[K] Γ(X, W), Function.Injective φ ∧ ∀ (y : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c → φ c = y := by
  intro K _ _ X q W d t s E ε hL σ r hr hs
  letI := (strV q W).toAlgebra
  obtain ⟨hE, hU⟩ := GlobalTheory.T.local_graded_class_representative q t s E ε hL σ d r hr hs
  have ex : ∀ c : HQ (KS q s {W}) r (r + 1) d, ∃ y : Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c := by
    intro c
    obtain ⟨y, hy⟩ := hE c
    refine ⟨y ⟨id, strictMono_id⟩, ?_⟩
    have e : (fun u => ∑ I : Idx d d, E.form σ I.1 (ε (y I)) u) = E.form σ id (ε (y ⟨id, strictMono_id⟩)) :=
      funext fun u => sum_idx_self (fun I : Idx d d => E.form σ I.1 (ε (y I)) u)
    rwa [e] at hy
  have z0 : ∀ y : Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) 0 → y = 0 := by
    intro y h
    have e : (fun u => ∑ I : Idx d d, E.form σ I.1 (ε ((fun _ => y : Idx d d → Γ(X, W)) I)) u) = E.form σ id (ε y) :=
      funext fun u => sum_idx_self (fun I : Idx d d => E.form σ I.1 (ε y) u)
    exact congrFun (hU (fun _ => y) (by rwa [e])) ⟨id, strictMono_id⟩
  have uniq : ∀ (y y' : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c →
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y')) c → y = y' := by
    intro y y' c h h'
    have h2 := rep_add h (rep_smul (-1 : K) h')
    have e : (fun u => E.form σ id (ε y) u + (-1 : K) • E.form σ id (ε y') u) = E.form σ id (ε (y - y')) := by
      funext u
      rw [map_sub, form_sub_fun, neg_one_smul, sub_eq_add_neg]
    rw [e, neg_one_smul, add_neg_cancel] at h2
    exact sub_eq_zero.1 (z0 _ h2)
  choose φ hφ using ex
  refine ⟨{ toFun := φ, map_add' := ?_, map_smul' := ?_ }, ?_, fun y c h => uniq _ _ c (hφ c) h⟩
  · intro c c'
    refine uniq _ _ (c + c') (hφ _) ?_
    have h2 := rep_add (hφ c) (hφ c')
    have e : (fun u => E.form σ id (ε (φ c)) u + E.form σ id (ε (φ c')) u) = E.form σ id (ε (φ c + φ c')) := by
      funext u
      rw [map_add (f := _), form_add_fun]
    rwa [e] at h2
  · intro a c
    refine uniq _ _ (a • c) (hφ _) ?_
    have h2 := rep_smul a (hφ c)
    have e : (fun u => a • E.form σ id (ε (φ c)) u) = E.form σ id (ε (a • φ c)) := by
      funext u
      have e1 : a • φ c = strV q W a * φ c := Algebra.smul_def a (φ c)
      rw [e1, map_mul, hL.2.2.1 a, form_alg_mul]
    rwa [e] at h2
  · intro c c' h
    have h' : φ c = φ c' := h
    have h2 := hφ c'
    rw [← h'] at h2
    exact rep_unique (hφ c) h2

end GlobalTheory.CompanionTheory.ConeLocal
end
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_pairing_depth_induction : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (y : Fin (n + 1) → k) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (uM (n + 1) y) v) v' (((ψ (y (Fin.last n)) : Circle) : ℂ) * A) ∧ EvVal ν ψ T B v (T' (uM (n + 1) y) v') (((ψ (-y (Fin.last n)) : Circle) : ℂ) * A) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.EvVal_translate | exact GlobalTheory.CompanionTheory.MirPair.EvVal_translate | (intros; apply GlobalTheory.CompanionTheory.MirPair.EvVal_translate <;> assumption)
end
