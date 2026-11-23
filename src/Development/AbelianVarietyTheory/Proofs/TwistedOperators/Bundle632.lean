module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaIntegrandIsUnfoldingTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle537
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle622
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionHomMulEmbeddedAnisotropic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle623
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle618
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle449
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
open GlobalTheory.Unf.FB

noncomputable section


open GlobalTheory.ThLaws in
theorem GlobalTheory.th_isTh_lev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) := by
  intro D ψ hψ σ J B y hy x₀ hx₀
  obtain ⟨hcont, -, hleft, hcen, -, -⟩ := GlobalTheory.T.jacobiActionUnipotent_laws D ψ hψ σ J B y hy
  beta_reduce at hcen hleft
  obtain ⟨x₁, hx₁, -, -, hlast, hq⟩ := GlobalTheory.T.besselBasePoint_isUnfoldingBasePoint_spec D σ B
  have e : x₁ = x₀ := rat_injective (hx₁.trans hx₀.symm)
  refine ⟨hcont.comp continuous_subtype_val, fun γ hγQ hγN n hn => hleft γ hγN hγQ n hn, fun c n hn => ?_, ?_⟩
  · rw [hcen c n hn, hx₀, hq]
  intro j a ha1 ha0 hg
  have hl : a (Fin.last σ) = 0 := hlast a (by rw [e]; exact hg)
  have hj : j.1 < σ := by
    by_contra hc
    have : j = Fin.last σ := Fin.ext (by have := j.2; simp only [Fin.val_last]; omega)
    rw [this, hl] at ha1
    exact zero_ne_one ha1
  let j' : Fin (σ + 1) := ⟨j.1 + 1, by omega⟩
  have hjj : j < j' := by rw [Fin.lt_def]; simp [j']
  obtain ⟨t, ht⟩ := exists_psiE_ne_one hψ
  let A : Fin (σ + 1) → AE D := GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a
  let Bv : Fin (σ + 1) → AE D := fun k => if k = j' then cA D t else 0
  have hB0 : ∀ k, k ≠ j' → Bv k = 0 := fun k hk => if_neg hk
  have hA0 : ∀ i, j < i → A i = 0 := fun i hi => by
    show incA D (a i) = 0
    rw [ha0 i hi, map_zero]
  have hN : ∀ i k, ¬(i ≤ j ∧ k = j') → A i * cA D (Bv k) = 0 := by
    intro i k hik
    by_cases hk : k = j'
    · rw [hA0 i (not_le.1 fun hi => hik ⟨hi, hk⟩), zero_mul]
    · rw [hB0 k hk, map_zero, mul_zero]
  have hAB : (fun k => cA D (Bv k)) ⬝ᵥ A = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_comm]
    exact hN k k fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj)
  have hupper : tvGL A Bv hAB ∈ upperUni (σ + 1) (AE D) := fun i k => by
    refine ⟨fun hki => ?_, ?_⟩
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hki), tvN_apply,
        hN i k fun h => absurd (h.2 ▸ hki) (not_lt.2 (le_of_lt (lt_of_le_of_lt h.1 hjj))), zero_add]
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_eq, tvN_apply,
        hN i i fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj), add_zero]
  have hUX : tvGL A Bv hAB ∈ UX D (σ + 1) := mem_UX.2 hupper
  have hu : J.d.levi (tvGL A Bv hAB) ∈ flagN J.d := J.d.levi_mem_NFlag hupper
  have hup : upSum (tvN A Bv) = t := by
    unfold upSum
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j']
    · rw [if_pos (by simp [j']), tvN_apply, show Bv j' = cA D t from if_pos rfl, cA_cA']
      show incA D (a j) * t = t
      rw [ha1, map_one, one_mul]
    · intro k _ hk
      rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = j'
      · rw [if_neg]
        intro h
        apply hi
        rw [hk] at h
        exact Fin.ext (by simp [j'] at h; omega)
      · rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨J.d.jY *ᵥ Bv, J.d.levi (tvGL A Bv hAB), star (psiE ψ t), ?_, levi_isTransv J.d A Bv hAB,
    Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_iInf.2 fun i => ?_⟩, ?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form J.W (J.d.jX *ᵥ A) (J.d.jY *ᵥ Bv) = 0
    rw [form_mulVec, ← J.d.pX_eq, Matrix.mulVec_mulVec, J.d.pX_jX, Matrix.one_mulVec, hAB]
  · rw [mem_fixer]
    have hcol : ∀ m, (tvGL A Bv hAB).1 m i.1 = (1 : Mx D (σ + 1) (σ + 1)) m i.1 := fun m => by
      rw [tvGL_val, Matrix.add_apply, tvN_apply,
        hN m i.1 fun h => absurd (h.2 ▸ i.2) (not_le.2 hjj), add_zero]
    ext k l
    have h1 := congrFun (congrFun (J.d.levi_jX (tvGL A Bv hAB)) k) i.1
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id] at h1 ⊢
    rw [h1]
    simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro h1
    apply ht
    rw [← star_star (psiE ψ t), h1, star_one]
  · intro n hn n' hn'
    have hx : ∀ u ∈ UX D (σ + 1), zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := fun u hu => zEll_mul B.L B.ζ hu
    have hJu : jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.levi (tvGL A Bv hAB)) = id := by
      have := jacS_levi_mul ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (hx _ hUX) 1
      rwa [mul_one, jacS_one] at this
    have hpu : psiFlag ψ J.d (J.d.levi (tvGL A Bv hAB)) = psiE ψ t := by
      rw [psiFlag, blockX_levi, tvGL_val, upSum_add, upSum_one, zero_add, hup]
    beta_reduce
    rw [GlobalTheory.JacHom.jacS_mul J.d hx ψ (mul_mem hn hu) hn', GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hu, hJu,
      GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hn', psiFlag_mul J.d ψ (mul_mem hn hu) hn', psiFlag_mul J.d ψ hn hu,
      psiFlag_mul J.d ψ hn hn', hpu]
    simp only [id, star_mul']
    ring
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjXCols

theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem exists_nat_smul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ) (A : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ s ∈ Λ, (N : E) • (A *ᵥ s) ∈ Λ := by
  classical
  obtain ⟨gens, hg⟩ := hΛ.fg
  have key : ∀ g : Fin n → E, ∃ z : ℤ, z ≠ 0 ∧ (z : E) • (A *ᵥ g) ∈ Λ := fun g =>
    GlobalTheory.OrthDual.exists_int_smul_mem Λ (by rw [hΛ.span_eq_top]; trivial)
  choose z hz0 hz using key
  have hnat : ∀ g, ((z g).natAbs : E) • (A *ᵥ g) ∈ Λ := by
    intro g
    rcases Int.natAbs_eq (z g) with h | h
    · have h1 := hz g
      rw [h, Int.cast_natCast] at h1
      exact h1
    · have h1 := hz g
      rw [h, Int.cast_neg, Int.cast_natCast, neg_smul, Submodule.neg_mem_iff] at h1
      exact h1
  refine ⟨∏ g ∈ gens, (z g).natAbs, Finset.prod_pos fun g _ => Int.natAbs_pos.2 (hz0 g), ?_⟩
  let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
    (((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • Matrix.mulVecLin A).restrictScalars (𝓞 E)
  have hle : Submodule.span (𝓞 E) (gens : Set (Fin n → E)) ≤ Λ.comap f := by
    rw [Submodule.span_le]
    intro g hgm
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun g => (z g).natAbs) hgm
    have hk' : (∏ g ∈ gens, (z g).natAbs) = (z g).natAbs * k := hk
    show ((∏ g ∈ gens, (z g).natAbs : ℕ) : E) • (A *ᵥ g) ∈ Λ
    rw [hk', Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (hnat g) k
  rw [hg] at hle
  intro s hs
  exact hle hs

variable {D : D7}

theorem sum_mul_eq (S : HSp D) (N : ℕ) (Q M : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (hQM : S.gram * Q = M * S.gram)
    (s : Fin S.rank → D.host.E) (j : Fin S.rank) :
    ∑ l, (∑ k, star (s k) * S.gram k l) * ((N : D.host.E) • Q) l j =
      ∑ k, star (((N : D.host.E) • (Mᴴ *ᵥ s)) k) * S.gram k j := by
  have h : Matrix.vecMul (Matrix.vecMul (star s) S.gram) ((N : D.host.E) • Q) =
      Matrix.vecMul (star ((N : D.host.E) • (Mᴴ *ᵥ s))) S.gram := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_smul, hQM, star_smul, star_natCast, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.vecMul_vecMul]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

theorem rat_natCast_smul {m n : ℕ} (N : ℕ) (X : Matrix (Fin m) (Fin n) D.host.E) :
    (rat ((N : D.host.E) • X) : Mx D m n) = N • (rat X : Mx D m n) := by
  ext i j
  simp [rat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul]

end GlobalTheory.ProjXCols

namespace GlobalTheory.ProjXCols




theorem nsmul_projX_mem_latBig : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G (2 * ρ + 1), N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) ∈ latBig G (2 * ρ + 1) := by
  intro D hQ T L μ0 hL sc G W M hM F hF ρ h
  have hi : 2 * ρ + 1 < D.R.m := by omega
  have h0 : ∀ j, (Node.grid (2 * ρ + 1 + 1) 0 : Node) ≠ .grid 0 j := fun j hh => by
    injection hh with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.isV (show (Node.grid (2 * ρ + 1 + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  obtain ⟨N, hN, hNs⟩ := exists_nat_smul_mulVec_mem _ (selfDual_isFullLattice _ _ hsd)
    ((G.V (.grid (2 * ρ + 1 + 1) 0)).gram * (F.dB ρ h).e * (F.dB ρ h).e'ᴴ)ᴴ
  refine ⟨N, hN, fun u hu => ?_⟩
  have e1 : N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) =
      u ⬝ (rat ((N : D.host.E) • ((F.dB ρ h).e * (F.dB ρ h).qX)) :
        Mx D (G.V (.grid (2 * ρ + 1 + 1) 0)).rank (G.V (.grid (2 * ρ + 1 + 1) 0)).rank) := by
    rw [rat_natCast_smul, rat_mul, Matrix.mul_smul, Matrix.mul_assoc]
    rfl
  rw [e1]
  refine GlobalTheory.CoreRowLat.latO_mul_right _ (fun s hs => ⟨_, hNs s hs, fun j => ?_⟩) hu
  refine sum_mul_eq _ N _ _ ?_ s j
  simp only [HypDec.qX, Matrix.mul_assoc]

end GlobalTheory.ProjXCols
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.orthAt_oB_lat0_of_std : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : GlobalTheory.Asc.Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v := by
  first | exact @GlobalTheory.AscFin.CoreSum.besselCoreVertexLattice_splitsAlongOrthDecomposition | exact GlobalTheory.AscFin.CoreSum.besselCoreVertexLattice_splitsAlongOrthDecomposition | (intros; apply GlobalTheory.AscFin.CoreSum.besselCoreVertexLattice_splitsAlongOrthDecomposition <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.depthLatticeGridCore_iff_firstRow_extByZero : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (a : WO (G.V (.core 1)) (Yc D 0)), F.oz.jA ⬝ a ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) a ∈ latRow G 0 := by
  first | exact @GlobalTheory.CoreRowLat.jA_mem_latCore_iff | exact GlobalTheory.CoreRowLat.jA_mem_latCore_iff | (intros; apply GlobalTheory.CoreRowLat.jA_mem_latCore_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.MovedAlg

variable {D : D7}

def IsAlgComb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f₀ F : WO S T → ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO S T), (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, (w p).map (infPart D) = 0) ∧
    F = ∑ p, c p • heisO ψ S T (w p) f₀

theorem isAlg_mul {a b : ℂ} (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) : IsAlgebraic ℚ (a * b) := by
  rw [← mem_algebraicClosure_iff] at ha hb ⊢
  exact mul_mem ha hb

section Comb

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem IsAlgComb.zero : IsAlgComb ψ S T f₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, by simp⟩

theorem IsAlgComb.smul {a : ℂ} (ha : IsAlgebraic ℚ a) {F : WO S T → ℂ} (h : IsAlgComb ψ S T f₀ F) :
    IsAlgComb ψ S T f₀ (a • F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := h
  refine ⟨n, fun p => a * c p, w, fun p => isAlg_mul ha (hc p), hw, ?_⟩
  rw [Finset.smul_sum]
  simp only [smul_smul]

theorem IsAlgComb.add {F F' : WO S T → ℂ} (hF : IsAlgComb ψ S T f₀ F) (hF' : IsAlgComb ψ S T f₀ F') :
    IsAlgComb ψ S T f₀ (F + F') := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨m, c', w', hc', hw', rfl⟩ := hF'
  refine ⟨n + m, Fin.append c c', Fin.append w w', fun p => ?_, fun p => ?_, ?_⟩
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simpa using hc q
    · simpa using hc' q
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simpa using hw q
    · simpa using hw' q
  · rw [Fin.sum_univ_add]
    simp

theorem IsAlgComb.finsum : ∀ {n : ℕ} (c : Fin n → ℂ) (F : Fin n → WO S T → ℂ), (∀ p, IsAlgebraic ℚ (c p)) →
    (∀ p, IsAlgComb ψ S T f₀ (F p)) → IsAlgComb ψ S T f₀ (∑ p, c p • F p)
  | 0, _, _, _, _ => by simpa using (IsAlgComb.zero : IsAlgComb ψ S T f₀ 0)
  | n + 1, c, F, hc, hF => by
    rw [Fin.sum_univ_succ]
    exact (IsAlgComb.smul (hc 0) (hF 0)).add (IsAlgComb.finsum _ _ (fun p => hc _) fun p => hF _)

theorem heisO_sum_smul (u : WO S T) {n : ℕ} (c : Fin n → ℂ) (F : Fin n → WO S T → ℂ) :
    heisO ψ S T u (∑ p, c p • F p) = ∑ p, c p • heisO ψ S T u (F p) := by
  funext z
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem IsAlgComb.Heisenberg₂
    (hψ : ∀ u v : WO S T, u.map (infPart D) = 0 → v.map (infPart D) = 0 → IsAlgebraic ℚ (ψ (symplOH S T u v)))
    {u : WO S T} (hu : u.map (infPart D) = 0) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T f₀ F) :
    IsAlgComb ψ S T f₀ (heisO ψ S T u F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  refine ⟨n, fun p => c p * ψ (symplOH S T u (w p)), fun p => u + w p,
    fun p => isAlg_mul (hc p) (hψ _ _ hu (hw p)), fun p => ?_, ?_⟩
  · rw [Matrix.map_add _ (map_add (infPart D)), hu, hw p, add_zero]
  · rw [heisO_sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [GlobalTheory.LinkCompare.heisO_heisO, smul_smul]

end Comb

theorem om_algComb {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X)
    (hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)))
    (t : T) (x : GA D A) (h : GA D WW)
    (h0 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) X.vac)) {F : WO (GlobalTheory.Grid.neg A) WW → ℂ}
    (hF : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F) : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  have e : ∀ p, X.ω t (x, h) (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) =
      heisO W.ψ (GlobalTheory.Grid.neg A) WW (actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm x) h (w p))
        (X.ω t (x, h) X.vac) := fun p =>
    (hX.is.weil t).om_heis ((GlobalTheory.Grid.ofSgn true A).symm x) h (w p) X.vac hv

  rw [map_sum]
  simp only [map_smul, e]
  exact IsAlgComb.finsum _ _ hc fun p => IsAlgComb.Heisenberg₂ hψ (GlobalTheory.FinApprox.actO_fin _ _ (hw p)) h0

end GlobalTheory.MovedAlg

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.OrthOff

theorem orthOff : All fun {D} _ _ _ {G} _ _ => ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT (fun v => v ∉ G.pl.S0), ∀ y : WO S T, IsHalf e y → symplO S T u y = 0 := by
  intro D _ T L μ0 _ sc G W M _ e he S T' LS LT u hu y hy
  classical
  have hx : FinPl.MxAt (fun p => ∃ PP ∈ G.pl.W0, p = HeightOneSpectrum.under (𝓞 D.host.F) PP) (y.map (cA D)) :=
    GlobalTheory.PlaceModelComb.mxAt_of_idemSum he (Or.inr fun i j => by
      rw [Matrix.map_apply, ← map_mul, hy i j])
  have hu' := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have hoff : ∀ i j, u i j ∈ FinPl.idOff D (fun p => ∃ PP ∈ G.pl.W0, p = HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
    intro i j
    rw [FinPl.idOff, Ideal.mem_iInf]
    rintro ⟨w, PP, hPP, rfl⟩
    have hin : HeightOneSpectrum.under (𝓞 D.host.F) PP ∈ G.pl.S0 := by
      unfold Places.W0 at hPP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP
      rw [G.pl.under_w hv]
      exact hv
    have h := hu' i j
    rw [FinPl.idAt, Ideal.mem_inf, Ideal.mem_iInf] at h
    exact h.2 ⟨_, fun h' => h' hin⟩
  have hh : hO S T' u y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * u d a = 0 :=
      GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hx c b) (hoff d a)
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T'.gram c d) * u d a
        = incA D (S.gram⁻¹ a b) * incA D (T'.gram c d) * (cA D (y c b) * u d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

end GlobalTheory.OrthOff
end
end
