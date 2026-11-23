module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryBlockLevelUnitBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueFlow

open Matrix GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem row_of_stab {X Y : Matrix (Fin n) (Fin r) E} (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {g : GAd σ J} {B C : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (hX : (matHom _ σ J g).1 * adMat F X = adMat F X * B) (hY : (matHom _ σ J g⁻¹).1 * adMat F Y = adMat F Y * C) :
    adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 = B * adMat F (cT (σ : E →+* E) Y * J) := by
  set S := sigR (AF F) σ with hS
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 with hMdef
  set Mi : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g⁻¹).1 with hMidef
  have hinv : matHom (AF F) σ J g⁻¹ = (matHom (AF F) σ J g)⁻¹ := map_inv _ g
  have hMMi : M * Mi = 1 := by
    rw [hMdef, hMidef, hinv]; exact Units.mul_inv _
  have hU : cT S M * adMat F J * M = adMat F J := g.2
  have hadY : adMat F (cT (σ : E →+* E) Y * J) = cT S (adMat F Y) * adMat F J := by
    rw [adMat, Matrix.map_mul]
    congr 1
  have hJM : adMat F J * M = cT S Mi * adMat F J := by
    calc adMat F J * M = (cT S Mi * cT S M) * adMat F J * M := by
          rw [← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
      _ = cT S Mi * (cT S M * adMat F J * M) := by simp only [Matrix.mul_assoc]
      _ = cT S Mi * adMat F J := by rw [hU]
  have h1 : adMat F (cT (σ : E →+* E) Y * J) * M = cT S C * adMat F (cT (σ : E →+* E) Y * J) := by
    rw [hadY, Matrix.mul_assoc, hJM, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hY, Formalism.UG.cT_mul, Matrix.mul_assoc]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, GlobalTheory.StdPar.yx hCM hJ hW]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : cT S C = B := by
    calc cT S C = cT S C * (adMat F (cT (σ : E →+* E) Y * J) * adMat F X) := by rw [hyx, Matrix.mul_one]
      _ = adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X := by rw [h1, Matrix.mul_assoc]
      _ = B := by rw [Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  rw [h1, h2]

theorem const_centre {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {c : (AF F ⊗[F] E)ˣ} {a : GAd σ J} (ha : IsIdTorusElt σ J X Y (fun _ => c) a) :
    a ∈ levi σ J X Y {Fin.last r} ∧ ∀ m ∈ levi σ J X Y {Fin.last r}, a * m = m * a := by
  have ext : ∀ {m : GAd σ J}, m ∈ levi σ J X Y {Fin.last r} →
      (∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F X = adMat F X * B) ∧
      ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F Y = adMat F Y * C := by
    intro m hm
    simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hm
    obtain ⟨⟨B, -, hB⟩, ⟨C, -, hC⟩⟩ := hm (Fin.last r) (Finset.mem_singleton_self _)
    exact ⟨⟨B.1, hB⟩, ⟨C.1, hC⟩⟩
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf]
    intro k hk
    refine ⟨⟨⟨diagonal fun i => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => (((c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩,
      ⟨⟨diagonal fun i => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => ((conjUnit σ c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun ha.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
    · ext i j
      have := congrFun (congrFun ha.2.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
  · obtain ⟨⟨B, hB⟩, ⟨C, hC⟩⟩ := ext hm
    obtain ⟨⟨B', hB'⟩, ⟨C', hC'⟩⟩ := ext (inv_mem hm)
    have rY := row_of_stab hCM hJ hW hB hC'
    have rX := row_of_stab hCM hJ (GlobalTheory.IdTorusCent.swap hCM hJ hW) hC hB'
    have dc : ∀ (d : AF F ⊗[F] E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)),
        diagonal (fun _ : Fin (r + 1) => d) * Z = Z * diagonal (fun _ => d) := fun d Z => by
      ext i j; simp [diagonal_mul, mul_diagonal, mul_comm]
    have c1 : (matHom _ σ J m).1 * (adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) Y * J)) = adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J m).1 := by
      rw [Matrix.mul_assoc (adMat F X * _), rY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB,
        Matrix.mul_assoc (adMat F X) B, ← dc, ← Matrix.mul_assoc]
    have c2 : (matHom _ σ J m).1 * (adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) X * J)) = adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) X * J) * (matHom _ σ J m).1 := by
      rw [Matrix.mul_assoc (adMat F Y * _), rX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hC,
        Matrix.mul_assoc (adMat F Y) C, ← dc, ← Matrix.mul_assoc]
    apply matHom_injective
    apply Units.ext
    simp only [map_mul, Units.val_mul, GlobalTheory.T.idelicFrameTorusElement_matrix_eq hCM hJ hW ha, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, c1, c2]

end GlobalTheory.ResidueFlow


open GlobalTheory.IdTorus in
theorem GlobalTheory.ResidueEisenstein.exists_isFlowJ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ b : ℝ → GAd σ J, IsFlowJ σ J X Y b := by
  intro F E _ _ _ _ _ σ n J r X Y hc hJ hW
  obtain ⟨t, htc, ht⟩ := exists_continuous_isIdTorusElt hc hJ hW
  obtain ⟨l, lc, ladd, -, labs⟩ := exists_real_idele_flow F E σ hc
  have hd : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have cl := fun s : ℝ => GlobalTheory.ResidueFlow.const_centre hc hJ hW (ht fun _ => l (s / ((r + 1 : ℕ) : ℝ)))
  refine ⟨fun s => t fun _ => l (s / ((r + 1 : ℕ) : ℝ)),
    htc.comp (continuous_pi fun _ => lc.comp (continuous_id.div_const _)), fun s s' => ?_, fun s => ?_,
    fun s => (cl s).1, fun s => (cl s).2⟩
  · refine isIdTorusElt_uniq hc hJ hW (ht _) ?_
    have : (fun _ : Fin (r + 1) => l ((s + s') / ((r + 1 : ℕ) : ℝ))) =
        (fun _ => l (s / ((r + 1 : ℕ) : ℝ))) * fun _ => l (s' / ((r + 1 : ℕ) : ℝ)) := by
      funext k; rw [add_div, ladd]; rfl
    rw [this]; exact isIdTorusElt_mul (ht _) (ht _)
  · refine ⟨Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ))), (ht _).1, ?_⟩
    have : Matrix.GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ)))) =
        l (s / ((r + 1 : ℕ) : ℝ)) ^ (r + 1) := by
      apply Units.ext
      change Matrix.det (Matrix.diagonal fun _ : Fin (r + 1) => (l (s / ((r + 1 : ℕ) : ℝ))).1) = _
      rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]
    rw [this, map_pow, NNReal.coe_pow, labs, ← Real.exp_nat_mul, mul_div_cancel₀ _ hd]

end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviDecompositionFrame

theorem levi_dec_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ p β, ScalesBy σ J X p β → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, p = u * m ∧ ScalesBy σ J X m β ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) ∧ (absE F E (Matrix.GeneralLinearGroup.det β) = 1 → m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW p β hp
  have yx' : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx h hJ hW
  have hinv : ScalesBy σ J X p⁻¹ β⁻¹ := by
    unfold ScalesBy at *
    have := congrArg (fun Z => (matHom _ σ J p⁻¹).1 * Z * (β⁻¹).1) hp
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
    exact this.symm
  have hpF : p ∈ GlobalTheory.UAut.parFlag σ J X fun _ => 0 :=
    ⟨⟨_, fun _ _ hlt => absurd hlt (lt_irrefl _), hp⟩, _, fun _ _ hlt => absurd hlt (lt_irrefl _), hinv⟩
  obtain ⟨u, hu, m, hmF, hpm, hr⟩ := (GlobalTheory.LeviFlag.levi_decomposition F E σ h n J hJ (r + 1) X Y (fun _ => 0)
    hW.xx hW.yy hW.xy).1 p hpF
  rw [GlobalTheory.UAut.unipFlag_const] at hu
  have hm : m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} := by
    simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf, Finset.mem_singleton]
    rintro k rfl
    exact Subgroup.mem_inf.2 ⟨GlobalTheory.ResLineLevi.mem_frameStab_of_parFlag yx' hmF.1,
      GlobalTheory.ResLineLevi.mem_frameStab_of_parFlag hW.xy hmF.2⟩
  have hmb : ScalesBy σ J X m β := by
    have e : m = u⁻¹ * p := by rw [hpm, inv_mul_cancel_left]
    unfold ScalesBy at *
    rw [e, map_mul, Units.val_mul, Matrix.mul_assoc, hp, ← Matrix.mul_assoc,
      GlobalTheory.ResLineLevi.unipRad_fix (inv_mem hu)]
  refine ⟨u, hu, m, hm, hpm, hmb, hr, fun hl => Subgroup.mem_inf.2 ⟨hm, ?_⟩⟩
  simp only [Subgroup.mem_iInf, Finset.mem_singleton]
  rintro k rfl
  exact ⟨β, by simpa [MonoidHom.mem_ker] using hl, hmb⟩

end GlobalTheory.LeviDecompositionFrame
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagTan

theorem le_preimage_of_trivSqZeroExt {L M : Type} [Field L] [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M]
    [IsCentralScalar L M] {T : Scheme.{0}} (φ : TrivSqZeroExt L M →+* L) (hφ : ∀ a, φ a = a.fst)
    (x : Sp (TrivSqZeroExt L M) ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  let q : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : (spMap φ) q = s := by
    refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
    change φ a ∈ (⊥ : Ideal L) ↔ a ∈ s.asIdeal
    rw [Ideal.mem_bot, hφ]
    constructor
    · intro ha
      refine s.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by
        rw [pow_two, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha rfl, TrivSqZeroExt.inr_mul_inr]]
      exact s.asIdeal.zero_mem
    · intro ha
      by_contra h0
      exact s.2.ne_top (s.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
  have h₁ : (spMap φ ≫ x) q ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem IsKS.sum_of_der : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K} (hy : KSIso (psiSet H) y)
    {ι : Type} [Fintype ι] {x : ι → (Sp (DualNumber K) ⟶ Xo.X)} (hx : ∀ a, GlobalTheory.FlagTan.IsTanX y (x a))
    {Mx : ι → HIx Dw (psiSet H) → K} (hM : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) y (x a) (Mx a))
    {x' : Sp (DualNumber K) ⟶ Xo.X} (hx' : GlobalTheory.FlagTan.IsTanX y x') (m : ι → K)
    (h : ∀ (O : Xo.X.Opens) (f : Γ(Xo.X, O)) (h' : ⊤ ≤ x' ⁻¹ᵁ O) (hc : ∀ a, ⊤ ≤ x a ⁻¹ᵁ O),
      (evalPt x' O h' f).snd = ∑ a, m a * (evalPt (x a) O (hc a) f).snd), GlobalTheory.FlagTan.IsKS (psiSet H) y x' (∑ a, m a • Mx a) := by
  intro E _ _ _ H Dw l Xo c K _ _ y hy ι _ x hx Mx hM x' hx' m h
  obtain ⟨X, -, hXy, hX⟩ := hy
  have ex : ∀ a, x a = spMap (dir c (Mx a)).toRingHom ≫ X := fun a => ((hX _ (hx a)).2 _).1 (hM a)
  refine ((hX x' hx').2 _).2 ?_
  obtain ⟨U, hU, hpU, -⟩ := Opens.isBasis_iff_nbhd.1 Xo.X.isBasis_affineOpens
    (Opens.mem_top (y.x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)))
  have hyU : ⊤ ≤ y.x ⁻¹ᵁ U := fun s _ => by
    have : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) := Subsingleton.elim _ _
    subst this
    exact hpU
  have hXU : ⊤ ≤ X ⁻¹ᵁ U :=
    le_preimage_of_trivSqZeroExt (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom (fun _ => rfl) X U
      (by rw [hXy]; exact hyU)
  have htan : ∀ z : Sp (DualNumber K) ⟶ Xo.X, IsTanX y z → ⊤ ≤ z ⁻¹ᵁ U := fun z hz =>
    le_preimage_of_trivSqZeroExt (red c K).toRingHom (fun _ => rfl) z U (by rw [hz.2]; exact hyU)
  have hev : ∀ (N : HIx Dw (psiSet H) → K) (z : Sp (DualNumber K) ⟶ Xo.X)
      (hz : z = spMap (dir c N).toRingHom ≫ X) (hzU : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(Xo.X, U)),
      evalPt z U hzU f = dir c N (evalPt X U hXU f) := by
    intro N z hz hzU f
    subst hz
    exact evalPt_spMap_comp _ X U hXU hzU f
  have hx'U := htan x' hx'
  have hcU : ∀ a, ⊤ ≤ x a ⁻¹ᵁ U := fun a => htan _ (hx a)
  set M'' : HIx Dw (psiSet H) → K := ∑ a, m a • Mx a
  have hzU : ⊤ ≤ (spMap (dir c M'').toRingHom ≫ X) ⁻¹ᵁ U := by
    intro s hs
    exact hXU (Set.mem_univ _)
  refine ext_evalPt hU hx'U hzU (RingHom.ext fun f => ?_)
  rw [hev M'' _ rfl hzU f]
  refine TrivSqZeroExt.ext ?_ ?_
  · have e1 := evalPt_spMap_comp (red c K).toRingHom x' U hx'U (by rw [hx'.2]; exact hyU) f
    have e2 := evalPt_spMap_comp (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom X U hXU
      (by rw [hXy]; exact hyU) f
    simp only [hx'.2, hXy] at e1 e2
    rw [fst_dir]
    exact e1.symm.trans e2
  · rw [h U f hx'U hcU, snd_dir]
    simp only [fun a => hev (Mx a) (x a) (ex a) (hcU a) f, snd_dir, M'', Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.FlagTan
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem ksRow_exists_lieComb : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm K (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR K ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 K) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* K) (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → K, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  intro K _ A _ _ A' _ i h O _ a cO ψ hiso hlag hperf hadj hK hEq ι m χ ub hb hspan hind heig hbasis τ τb hconj j
  classical

  have hsp : ⊤ ≤ Submodule.span K (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
    have e : (Fil A).mkQ '' Set.range hb =
        Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A) := by
      rw [← Set.range_comp]; rfl
    rw [← e, ← Submodule.map_span]
    intro q _
    obtain ⟨x, rfl⟩ := (Fil A).mkQ_surjective q
    have hx : x ∈ Submodule.span K (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
    obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨y, hy, ?_⟩
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [map_add (f := _), hg0, add_zero]
  let B := Module.Basis.mk hind hsp
  let k₀ : (Σ σ, Fin (m σ)) := ⟨τb, j⟩
  obtain ⟨f, hl⟩ := hperf.bijective_left.2 (B.coord k₀ ∘ₗ (Fil A).mkQ)
  have hval : ∀ x, ψ f x = B.coord k₀ ((Fil A).mkQ x) := fun x => by rw [hl]; rfl
  have hf : f ∈ Fil A := hlag f fun g hg => by
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [hval, hg0, map_zero]
  have hδ : ∀ k, ψ f (hb k) = if k = k₀ then 1 else 0 := fun k => by
    have e : (Fil A).mkQ (hb k) = B k := by simp [B]
    rw [hval, e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

  have hact : ∀ z, act (dp0 K) (𝟙 _) a z f = χ τ z • f := fun z => by
    haveI := a.hom z
    have hz : act (dp0 K) (𝟙 _) a z f ∈ Fil A := by
      rw [act_apply]; exact push_mem_Fil _ hf
    have hf' : act (dp0 K) (𝟙 _) a z f - χ τ z • f ∈ Fil A :=
      sub_mem hz (Submodule.smul_mem _ _ hf)
    have hker : (Submodule.span K (Set.range hb) ⊔ Fil A) ≤
        LinearMap.ker (ψ (act (dp0 K) (𝟙 _) a z f - χ τ z • f)) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso _ hf' g hg
      rintro _ ⟨k, rfl⟩
      have e := hiso f hf _ (heig k (cO z))
      rw [map_sub, map_smul, sub_eq_zero] at e
      have e2 := hadj z f (hb k)
      change ψ (act (dp0 K) (𝟙 _) a z f - χ τ z • f) (hb k) = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, e2, e, hδ]
      by_cases hk : k = k₀
      · subst hk
        simp [k₀, hconj z]
      · simp [hk]
    have h0 : ψ (act (dp0 K) (𝟙 _) a z f - χ τ z • f) = 0 := by
      refine LinearMap.ext fun x => ?_
      have : x ∈ Submodule.span K (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
      exact hker this
    exact sub_eq_zero.1 (hperf.bijective_left.1 (h0.trans (map_zero ψ).symm))

  obtain ⟨w, hw, hu⟩ := hK f hf
  have htan : IsTangent w := by
    obtain ⟨k, -, l⟩ := hw
    exact l.1
  have heq : ∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ τ z) ≫ w := fun z => by
    have e1 := hEq z f w hw
    rw [hact z] at e1
    exact (hK _ (Submodule.smul_mem _ _ hf)).unique e1 (hw.smul _)
  obtain ⟨cf, hcf⟩ := hbasis τ w htan heq
  exact ⟨cf, w, hcf, f, hf, fun k => by convert hδ k, hw⟩

end GlobalTheory.KSExist
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSRing

theorem ksRow_exists_lieComb_ring : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm R (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR R ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* R) (ub : ∀ σ, Fin (m σ) → (epsR R ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span R (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent R (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 R) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR R ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → R, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  intro R _ A _ _ A' _ i h O _ a cO ψ hiso hlag hperf hadj hK hEq ι m χ ub hb hspan hind heig hbasis τ τb hconj j
  classical

  have hsp : ⊤ ≤ Submodule.span R (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
    have e : (Fil A).mkQ '' Set.range hb =
        Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A) := by
      rw [← Set.range_comp]; rfl
    rw [← e, ← Submodule.map_span]
    intro q _
    obtain ⟨x, rfl⟩ := (Fil A).mkQ_surjective q
    have hx : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
    obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨y, hy, ?_⟩
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [map_add (f := _), hg0, add_zero]
  let B := Module.Basis.mk hind hsp
  let k₀ : (Σ σ, Fin (m σ)) := ⟨τb, j⟩
  obtain ⟨f, hl⟩ := hperf.bijective_left.2 (B.coord k₀ ∘ₗ (Fil A).mkQ)
  have hval : ∀ x, ψ f x = B.coord k₀ ((Fil A).mkQ x) := fun x => by rw [hl]; rfl
  have hf : f ∈ Fil A := hlag f fun g hg => by
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [hval, hg0, map_zero]
  have hδ : ∀ k, ψ f (hb k) = if k = k₀ then 1 else 0 := fun k => by
    have e : (Fil A).mkQ (hb k) = B k := by simp [B]
    rw [hval, e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

  have hact : ∀ z, act (dp0 R) (𝟙 _) a z f = χ τ z • f := fun z => by
    haveI := a.hom z
    have hz : act (dp0 R) (𝟙 _) a z f ∈ Fil A := by
      rw [act_apply]; exact push_mem_Fil _ hf
    have hf' : act (dp0 R) (𝟙 _) a z f - χ τ z • f ∈ Fil A :=
      sub_mem hz (Submodule.smul_mem _ _ hf)
    have hker : (Submodule.span R (Set.range hb) ⊔ Fil A) ≤
        LinearMap.ker (ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f)) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso _ hf' g hg
      rintro _ ⟨k, rfl⟩
      have e := hiso f hf _ (heig k (cO z))
      rw [map_sub, map_smul, sub_eq_zero] at e
      have e2 := hadj z f (hb k)
      change ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) (hb k) = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, e2, e, hδ]
      by_cases hk : k = k₀
      · subst hk
        simp [k₀, hconj z]
      · simp [hk]
    have h0 : ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) = 0 := by
      refine LinearMap.ext fun x => ?_
      have : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
      exact hker this
    exact sub_eq_zero.1 (hperf.bijective_left.1 (h0.trans (map_zero ψ).symm))

  obtain ⟨w, hw, hu⟩ := hK f hf
  have htan : IsTangent w := by
    obtain ⟨k, -, l⟩ := hw
    exact l.1
  have heq : ∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ τ z) ≫ w := fun z => by
    have e1 := hEq z f w hw
    rw [hact z] at e1
    exact (hK _ (Submodule.smul_mem _ _ hf)).unique e1 (hw.smul _)
  obtain ⟨cf, hcf⟩ := hbasis τ w htan heq
  exact ⟨cf, w, hcf, f, hf, fun k => by convert hδ k, hw⟩

end GlobalTheory.KSRing
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.exists_integralUnitary_blockLevel_unitBlock : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ {a d : ℕ}, a ≤ d →
    ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 →
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) →
    ∃ k ∈ intG D a, ∀ i j, (((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D 0 a d).map (inc D) -
      (unitBlock D 0 a d).map (inc D) * (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
        hatId D 𝔪 := by
  first | exact @GlobalTheory.FunObj.StdDatum.BlockPoint.exists_intG_unitBlock | exact GlobalTheory.FunObj.StdDatum.BlockPoint.exists_intG_unitBlock | (intros; apply GlobalTheory.FunObj.StdDatum.BlockPoint.exists_intG_unitBlock <;> assumption)
end

section

open GlobalTheory.HTLat

theorem _root_.GlobalTheory.T.prod_endomorphism_pow_levelComponent_eq_one_of_relation : ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : Fin n → (M →* M)) (c : Fin n → ℤ_[l]), ∑ i, c i • Tate.map l (φ i) = 0 → ∀ (N : ℕ) (m : Fin n → ℤ), (∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N))) → ∀ t : Tate l M, ∏ i, φ i (t.lev N) ^ m i = 1 := by
  first | exact @GlobalTheory.TateRel.prod_pow_eq_one | exact GlobalTheory.TateRel.prod_pow_eq_one | (intros; apply GlobalTheory.TateRel.prod_pow_eq_one <;> assumption)
end
