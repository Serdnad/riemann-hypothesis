module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp


theorem _root_.GlobalTheory.T.runSizes_quotientGaps_large : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 ∧
    (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1 ≤
      ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ ∧
    ∀ G T : ℕ, G = ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) →
      T = ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ →
      ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 4 ≤
          min (LevelStarExponents.gapS (Fm.D x ι) (Fm.params x hx ι).Cgap) (LevelStarExponents.h0 (Fm.L x ι)) ∧
        ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4 +
          2 * (Fm.D x ι).R.r + 1 ≤ LevelStarExponents.h0 (Fm.L x ι) := by
  first | exact @GlobalTheory.RunSizes.gaps_large | exact GlobalTheory.RunSizes.gaps_large | (intros; apply GlobalTheory.RunSizes.gaps_large <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX

theorem _root_.GlobalTheory.T.familyHypotheses_of_workingClass_sevenDuties : ∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), GlobalTheory.Fc.W3 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm → GlobalTheory.BigTop.FamHyp Fm := by
  first | exact @GlobalTheory.BigTop.famHyp_of_working_duty | exact GlobalTheory.BigTop.famHyp_of_working_duty | (intros; apply GlobalTheory.BigTop.famHyp_of_working_duty <;> assumption)
end

section

open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DblTargetRestrictCore

open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF in
theorem restrict_core : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h hd hhd f₁ f₂ hf₁ hf₂
  obtain ⟨ι, hιc, hιm, hιq, hιs, hιd⟩ := GlobalTheory.T.exists_continuous_unitaryDiagonalEmbedding_doubled F E σ nT JT
  have ext : ∀ a b : GAF σ (dblG JT), mtF σ (dblG JT) a = mtF σ (dblG JT) b → a = b := fun a b hab =>
    (HR (AF F) σ (dblG JT)).subtype_injective (Units.ext hab)
  have hdι : hd = ι h := ext _ _ (by rw [hhd, hιm])
  subst hdι
  have hsc := fun h' => GlobalTheory.T.weilDatum_doubleSpace_acts_unitScalar_seesaw_CM F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h' (ι h') (hιm h')
  choose c hc1 hc using hsc
  have hth := GlobalTheory.T.isThetaFunction_doublingThetaTensor_CM F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  by_cases h0 : ∃ f₀, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0
  swap
  · push_neg at h0
    rw [h0 f₁ hf₁]
    have hz : ∀ g : WOF F E nS nT → ℂ, deltaT (0 : WOF F E nS nT → ℂ) g = 0 := fun g => by
      funext x; simp [deltaT]
    simp only [map_zero, hz]
  obtain ⟨f₀, hf₀, hf₀0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hf₀0
  set fs := heisOF σ JS JT ξ₀ B.ψ y f₀ with hfs
  have hfsθ : IsThetaFunOF σ JS JT ξ₀ B.ψ fs := GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS nT JS JT ξ₀ y f₀ hf₀
  have hfs0 : fs 0 ≠ 0 := by
    have : symplOHF σ JS JT ξ₀ 0 y = 0 := by simp [symplOHF, symplOF, hOF]
    simp only [hfs, heisOF, this, AddChar.map_zero_eq_one, one_mul, zero_add]
    exact hy
  have top0 : topR (0 : WOF F E nS (nT + nT)) = 0 := by ext i j; rfl
  have bot0 : botR (0 : WOF F E nS (nT + nT)) = 0 := by ext i j; rfl
  have dl0 : ∀ a b : WOF F E nS nT → ℂ, deltaT a b 0 = a 0 * conj (b 0) := fun a b => by
    rw [deltaT_apply, top0, bot0, neg_zero]
  have hfsn : fs 0 * conj (fs 0) ≠ 0 := mul_ne_zero hfs0 ((map_ne_zero _).2 hfs0)

  have omi : ∀ h' : GAF σ JT, ω (1, h') (ω (1, h')⁻¹ fs) = fs := fun h' => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have pres := hω.om_pres

  have key : ∀ h' (a : ℂ), ωd (1, ι h') (deltaT (ω (1, h')⁻¹ fs) fs) 0 = a * (fs 0 * conj (fs 0)) → c h' = a := by
    intro h' a ha
    have e := congrFun (hc h' (ω (1, h')⁻¹ fs) fs (pres _ _ hfsθ) hfsθ) 0
    rw [Pi.smul_apply, smul_eq_mul, omi, dl0, ha] at e
    exact (mul_right_cancel₀ hfsn e).symm

  have hone : c 1 = 1 := by
    refine key 1 1 ?_
    have p1 : ((1 : GAF σ JS), (1 : GAF σ JT)) = 1 := rfl
    have p2 : ((1 : GAF σ JS), (1 : GAF σ (dblG JT))) = 1 := rfl
    rw [map_one, p1, p2, inv_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply, dl0, one_mul]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    refine key (a * b) _ ?_
    have e1 : ((1 : GAF σ JS), ι (a * b)) = (1, ι a) * (1, ι b) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    set g := ω ((1 : GAF σ JS), a * b)⁻¹ fs with hg
    have hgθ : IsThetaFunOF σ JS JT ξ₀ B.ψ g := pres _ _ hfsθ
    have comb : ω (1, a) (ω (1, b) g) = fs := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, hg, omi]
    rw [e1, map_mul, Module.End.mul_apply, hc b g fs hgθ hfsθ, map_smul,
      hc a (ω (1, b) g) fs (pres _ _ hgθ) hfsθ, comb]
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, dl0]
    ring
  let cc : GAF σ JT →* Circle :=
    { toFun := fun h' => ⟨c h', mem_sphere_zero_iff_norm.2 (hc1 h')⟩
      map_one' := Circle.ext hone
      map_mul' := fun a b => Circle.ext (hmul a b) }
  have hcc : ∀ h', (cc h' : ℂ) = c h' := fun _ => rfl

  have hcont : Continuous cc := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun h₀ => ?_)
    set g₁ := ω (1, h₀)⁻¹ fs
    have hg₁ : IsThetaFunOF σ JS JT ξ₀ B.ψ g₁ := pres _ _ hfsθ
    have hN : Continuous fun h' : GAF σ JT => ωd (1, ι h') (deltaT g₁ fs) 0 :=
      (hωd.om_cont _ (hth _ _ hg₁ hfsθ) 0).comp (continuous_const.prodMk hιc)
    have hD : Continuous fun h' : GAF σ JT => ω (1, h') g₁ 0 * conj (fs 0) :=
      ((hω.om_cont _ hg₁ 0).comp (continuous_const.prodMk continuous_id)).mul continuous_const
    have hD0 : ω (1, h₀) g₁ 0 * conj (fs 0) ≠ 0 := by rw [omi]; exact hfsn
    have hev : ∀ᶠ h' in nhds h₀, ω (1, h') g₁ 0 * conj (fs 0) ≠ 0 := hD.continuousAt.eventually_ne hD0
    refine ((hN.continuousAt).div hD.continuousAt hD0).congr (hev.mono fun h' hh' => ?_)
    show ωd (1, ι h') (deltaT g₁ fs) 0 / (ω (1, h') g₁ 0 * conj (fs 0)) = c h'
    rw [hc h' g₁ fs hg₁ hfsθ, Pi.smul_apply, smul_eq_mul, dl0, mul_div_assoc, div_self hh', mul_one]

  have hrat : ∀ γ ∈ GQF σ JT, cc γ = 1 := by
    intro γ hγ
    apply Circle.ext
    rw [hcc, Circle.coe_one]
    have e1 := hωd.om_aut 1 (Subgroup.one_mem _) (ι γ) (hιq γ hγ) _ (hth _ _ hfsθ hfsθ)
    have e2 := hω.om_aut 1 (Subgroup.one_mem _) γ hγ fs hfsθ
    rw [hc γ fs fs hfsθ hfsθ, Pi.smul_apply, smul_eq_mul, dl0, dl0, e2] at e1
    have := mul_right_cancel₀ hfsn (e1.trans (one_mul _).symm)
    exact this

  have hsplit : ∀ e, IsSplitIdemF σ e → ∀ g, SuppAtF σ e JT g → cc g = 1 := by
    intro e he g hg
    have hee : e * e = e := he.1
    obtain ⟨y, hy⟩ : ∃ y : (AEF F E)ˣ, IsDetAtF σ e JT g y := by
      have hd1 : (mtF σ JT g).det * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) = 1 :=
        (Matrix.GeneralLinearGroup.det (matHomF σ JT g)).mul_inv
      have hd2 : ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) * (mtF σ JT g).det = 1 :=
        (Matrix.GeneralLinearGroup.det (matHomF σ JT g)).inv_mul
      refine ⟨⟨e * (mtF σ JT g).det + (1 - e),
        e * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) + (1 - e), ?_, ?_⟩, rfl⟩
      · linear_combination ((mtF σ JT g).det * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ)
          - (mtF σ JT g).det - ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) + 1) * hee + e * hd1
      · linear_combination ((mtF σ JT g).det * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ)
          - (mtF σ JT g).det - ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) + 1) * hee + e * hd2
    have m1 : mtF σ JS (1 : GAF σ JS) = 1 := by unfold mtF; rw [map_one]; rfl
    have hx1 : IsDetAtF σ e JS 1 1 := by
      show ((1 : (AEF F E)ˣ) : AEF F E) = e * (mtF σ JS 1).det + (1 - e)
      rw [m1, Matrix.det_one, Units.val_one]; ring
    have hS1 : SuppAtF σ e JS 1 := fun i j => by rw [m1, sub_self]; simp
    obtain ⟨rd, hrd, hrd'⟩ := hωd.om_split e he 1 (ι g) hS1 (hιs e g hg) 1 y hx1 (hιd e g y hy)
    obtain ⟨r, hr, hr'⟩ := hω.om_split e he 1 g hS1 hg 1 y hx1 hy
    obtain ⟨ℓ, hℓ, a, b, ha, hb, hℓab⟩ := GlobalTheory.T.exists_invariant_form_doubled_space_split_place F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
    have hheis := GlobalTheory.T.heisenbergOp_doubledGram_doublingThetaTensor F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
    have dadd : ∀ f f' : WOF F E nS nT → ℂ, deltaT (f + f') b = deltaT f b + deltaT f' b := fun f f' => by
      funext x; simp only [deltaT_apply, Pi.add_apply, add_mul]
    have dsmul : ∀ (s : ℂ) (f : WOF F E nS nT → ℂ), deltaT (s • f) b = s • deltaT f b := fun s f => by
      funext x; simp only [deltaT_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    let ℓ₁ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => ℓ (deltaT f b)
        map_add' := fun f f' => by simp only [dadd, map_add (f := _)]
        map_smul' := fun s f => by simp only [dsmul, map_smul, RingHom.id_apply] }
    have hℓ₁ : ∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        ℓ₁ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ₁ f := by
      intro u hu f hf
      let ũ : WOF F E nS (nT + nT) := (Matrix.fromRows u 0).submatrix finSumFinEquiv.symm id
      have ht : topR ũ = u := by
        ext i j
        simp only [ũ, topR, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
          Matrix.fromRows_apply_inl, id]
      have hb0 : botR ũ = 0 := by
        ext i j
        simp only [ũ, botR, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
          Matrix.fromRows_apply_inr, Matrix.zero_apply, id]
      have hu' : ∀ i j, cAF σ e * ũ i j = ũ i j := by
        intro i j
        obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
        rcases i with i | i <;>
          simp only [ũ, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
            Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero, id, hu]
      have h0b : heisOF σ JS JT ξ₀ B.ψ 0 b = b := by
        funext x; simp [heisOF, symplOHF, symplOF, hOF]
      show ℓ (deltaT (heisOF σ JS JT ξ₀ B.ψ u f) b) = ℓ (deltaT f b)
      have e3 := hheis ũ f b
      rw [ht, hb0, neg_zero, h0b] at e3
      rw [← e3, hℓ ũ hu' _ (hth f b hf hb)]
    have E1 := hrd' ℓ hℓ _ (hth a b ha hb)
    rw [hc g a b ha hb, map_smul, smul_eq_mul] at E1
    have E2 : ℓ (deltaT (ω (1, g) a) b) = (r : ℂ) * (splitFacOF χS χT 1 y : ℂ) * ℓ (deltaT a b) := hr' ℓ₁ hℓ₁ a ha
    have s1 : (splitFacOF χS χT 1 y : ℂ) = χS y := by simp [splitFacOF]
    have s2 : (splitFacOF χS 1 1 y : ℂ) = χS y := by simp [splitFacOF]
    rw [E2, s1] at E1
    rw [s2] at E1
    have hs : (χS y : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hcr : c g * r = rd :=
      mul_right_cancel₀ (mul_ne_zero hs hℓab) (by linear_combination E1)
    have hcg : c g = ((rd / r : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hr.ne'), hcr]
    have hn := hc1 g
    rw [hcg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hrd hr)] at hn
    apply Circle.ext
    rw [hcc, Circle.coe_one, hcg, hn, Complex.ofReal_one]
  have hall := GlobalTheory.T.unitaryChar_eq_one_of_trivial_rational_splitPlace F E σ B hB nT JT hT cc hcont hrat hsplit h
  rw [hc h f₁ f₂ hf₁ hf₂, ← hcc, hall, Circle.coe_one, one_smul]

end GlobalTheory.DblTargetRestrictCore
end
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem pbA_comp (M : TwoLevels E r U C) (u v : U) (f : HA M) :
    pbA M v (pbA M u f) = pbA M (u * v) f := by
  apply Subtype.ext
  funext c x
  show f.1 (u • v • c) ⟨lact (M.tr u (v • c)) (lact (M.tr v c) x.1), _⟩ =
    f.1 ((u * v) • c) ⟨lact (M.tr (u * v) c) x.1, _⟩
  rw [show u • v • c = (u * v) • c from (mul_smul u v c).symm]
  have hγ := M.tr_mul u v c
  have hy : lact (M.tr u (v • c) * M.tr v c) x.1 ∈ M.dom := by
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul]
    exact lact_tr_mem M u _ (lact_tr_mem M v c x.2)
  have e : lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹) (lact (M.tr u (v • c) * M.tr v c) x.1) =
      lact (M.tr (u * v) c) x.1 := by
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel_right]
  have hz : lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹)
      (⟨lact (M.tr u (v • c) * M.tr v c) x.1, hy⟩ : M.dom).1 ∈ M.dom := by
    show lact _ (lact _ x.1) ∈ M.dom
    rw [e]; exact lact_tr_mem M (u * v) c x.2
  have key := f.2.2 ((u * v) • c) _ hγ ⟨lact (M.tr u (v • c) * M.tr v c) x.1, hy⟩ hz
  rw [show (⟨lact (M.tr (u * v) c) x.1, lact_tr_mem M (u * v) c x.2⟩ : M.dom) =
      ⟨lact (M.tr (u * v) c * (M.tr u (v • c) * M.tr v c)⁻¹) (lact (M.tr u (v • c) * M.tr v c) x.1), hz⟩
      from Subtype.ext e.symm, key]
  exact congrArg (f.1 _) (Subtype.ext (ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul _ _ _).symm)

theorem pbA_one (M : TwoLevels E r U C) (f : HA M) : pbA M 1 f = f := by
  apply Subtype.ext
  funext c x
  show f.1 ((1 : U) • c) ⟨lact (M.tr 1 c) x.1, _⟩ = f.1 c x
  have hγ := M.tr_mul 1 1 c
  simp only [mul_one, one_smul] at hγ
  rw [mul_inv_rev, mul_inv_cancel_left] at hγ
  have hz : lact (M.tr 1 c)⁻¹ (lact (M.tr 1 c) x.1) ∈ M.dom := by
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]
    exact x.2
  have key := f.2.2 c _ hγ ⟨lact (M.tr 1 c) x.1, lact_tr_mem M 1 c x.2⟩ hz
  simp only [one_smul]
  rw [← key]
  refine congrArg (f.1 c) (Subtype.ext ?_)
  show lact (M.tr 1 c)⁻¹ (lact (M.tr 1 c) x.1) = x.1
  rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]

theorem tw_law (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (a : U → C → ℂˣ) (ha : ∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) :
    tw M (fun c => (a 1 c : ℂ)) 1 = AlgHom.id ℂ _ ∧
      ∀ u v : U, (tw M (fun c => (a v c : ℂ)) v).comp (tw M (fun c => (a u c : ℂ)) u) =
        tw M (fun c => (a (u * v) c : ℂ)) (u * v) := by
  refine ⟨?_, fun u v => ?_⟩
  · apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro f
      show tw M _ 1 (Polynomial.C f) = Polynomial.C f
      rw [tw_C, pbA_one]
    · show tw M _ 1 Polynomial.X = Polynomial.X
      rw [tw_X]
      have h1 : cst M (fun c => (a 1 c : ℂ)) = 1 := by
        apply Subtype.ext
        funext c x
        show (a 1 c : ℂ) = 1
        have h := ha 1 1 c
        rw [one_mul, one_smul] at h
        have h' : a 1 c = 1 := by
          have := congrArg (fun t => (a 1 c)⁻¹ * t) h
          simpa using this.symm
        rw [h', Units.val_one]
      rw [h1, map_one, one_mul]
  · apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro f
      show tw M _ v (tw M _ u (Polynomial.C f)) = tw M _ (u * v) (Polynomial.C f)
      rw [tw_C, tw_C, tw_C, pbA_comp]
    · show tw M _ v (tw M _ u Polynomial.X) = tw M _ (u * v) Polynomial.X
      rw [tw_X, map_mul, tw_C, tw_X, tw_X, ← mul_assoc, ← Polynomial.C_mul]
      congr 2
      apply Subtype.ext
      funext c x
      show (a u (v • c) : ℂ) * (a v c : ℂ) = (a (u * v) c : ℂ)
      rw [ha v u c, Units.val_mul, mul_comm]

end GlobalTheory.CuspEmb

end
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

theorem isOpen_isPreconnected_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (c : C) : IsOpen M.dom ∧ IsPreconnected M.dom := by
  have key : ∀ (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ),
      X.Ψ = Ψ → X.Gm = Gm → X.p0 = p0 → IsOpen (GG Ψ Gm p0) ∧ IsPreconnected (GG Ψ Gm p0) := by
    intro X Ψ Gm p0 h1 h2 h3
    subst h1 h2 h3
    exact ⟨FourierCoefficientDomain.isOpen_dom X, (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected⟩
  exact key (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c)

theorem C_mem_nonZeroDivisors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U]
    [MulAction U C] (M : TwoLevels E r U C) (D : HA M), (∀ c, ∃ x : M.dom, (D : C → M.dom → ℂ) c x ≠ 0) →
    Polynomial.C D ∈ nonZeroDivisors (Polynomial (HA M)) := by
  intro E _ _ _ r U C _ _ M D hD
  have key : ∀ p : Polynomial (HA M), p * Polynomial.C D = 0 → p = 0 := by
    intro p hp
    apply Polynomial.ext
    intro i
    have hq : p.coeff i * D = 0 := by
      have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q i) hp
      simp only [Polynomial.coeff_mul_C, Polynomial.coeff_zero] at this
      exact this
    have hq' : ((p.coeff i : HA M) : C → M.dom → ℂ) * (D : C → M.dom → ℂ) = 0 := by
      have := congrArg (fun f : HA M => (f : C → M.dom → ℂ)) hq
      exact this
    rw [Polynomial.coeff_zero]
    apply Subtype.ext
    funext c x
    obtain ⟨x0, hx0⟩ := hD c
    obtain ⟨GD, hGD, hGD'⟩ := D.2.1 c
    obtain ⟨Gq, hGq, hGq'⟩ := (p.coeff i).2.1 c
    obtain ⟨hO, hC⟩ := isOpen_isPreconnected_dom M c
    have h0 : GD x0.1 ≠ 0 := by rw [← hGD']; exact hx0
    have hz := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hO hC hGD hGq
      (fun y hy => by
        have := congrFun (congrFun hq' c) ⟨y, hy⟩
        simp only [Pi.mul_apply, Pi.zero_apply] at this
        rw [← hGD' ⟨y, hy⟩, ← hGq' ⟨y, hy⟩, mul_comm]
        exact this) x0.2 h0 x.1 x.2
    show ((p.coeff i : HA M) : C → M.dom → ℂ) c x = ((0 : HA M) : C → M.dom → ℂ) c x
    rw [hGq' x, hz]
    rfl
  refine mem_nonZeroDivisors_iff.2 ⟨fun x hx => key x ?_, key⟩
  rwa [mul_comm] at hx

end GlobalTheory.CuspEmb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seesawTriple_secondFiniteDatum_standard_isVacuumDatum : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (hA' : X.rA'.IsStd) (hW : X.rW.IsStd), X.Is ψ θ α β νH S → ∀ t, IsFinF ψ θ false (GlobalTheory.BotDict.stdFr A' hA'.1) (GlobalTheory.BotDict.stdFr WW hW.1) (X.f' t) := by
  first | exact @GlobalTheory.BotDict.isFinF_snd_std | exact GlobalTheory.BotDict.isFinF_snd_std | (intros; apply GlobalTheory.BotDict.isFinF_snd_std <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.integrableOn_thetaKernel_definiteSeesawStage : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (p : ℕ)
    (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
    ∀ (t : T) (P' : PolF D WW.rank A'.rank) (h : GA D WW), MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m' := by
  first | exact @GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero | exact GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero | (intros; apply GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero <;> assumption)
end
