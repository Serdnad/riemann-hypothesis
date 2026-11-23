module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResLine.LeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem dual_eq {k : ℕ} (C : Matrix (Fin n) (Fin k) E) (g : GAd σ J) (B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))
    (e : (matHom _ σ J g).1 * adMat F C = adMat F C * B) :
    cT (sigR (AF F) σ) B * adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have hu : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have h1 : adMat F (cT (σ : E →+* E) C * J) = cT (sigR (AF F) σ) (adMat F C) * adMat F J := by
    rw [c1]; exact Matrix.map_mul
  rw [h1, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, ← e, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (adMat F J), hu]

omit [NumberField E] in
theorem unipRad_fix {k : ℕ} {C : Matrix (Fin n) (Fin k) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h1 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    rw [h1]; simp⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [Subgroup.mem_bot.1 hB] at e
  simpa using e

variable {X Y : Matrix (Fin n) (Fin r) E}

theorem mem_unipRad_iff (hW : IsWittFrame σ J X Y) (k : Fin r) (g : GAd σ J) :
    g ∈ unipRad σ J (initCols X k) ↔ (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) ∧
      ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 →
        ∃ a, adMat F (initCols X k) *ᵥ a = (matHom _ σ J g).1 *ᵥ y - y := by
  have e1 : {i | ∃ k' ∈ ({k} : Finset (Fin r)), i ≤ k'} = {i | i ≤ k} := by simp
  refine ⟨fun hg => ⟨unipRad_fix hg, fun y hy => ?_⟩, fun ⟨h1, h2⟩ => Subgroup.subset_closure ⟨?_, ?_, fun x hx => ?_⟩⟩
  · rw [← unip_singleton hW] at hg
    have := hg.2.2 y (by rw [e1, mem_colPerp_iff]; exact hy)
    rwa [e1, mem_colSpan_iff] at this
  · rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  · have := dual_eq (initCols X k) g 1 (by rw [h1, Matrix.mul_one])
    rw [Formalism.UG.cT_one, Matrix.one_mul] at this
    rw [Matrix.mul_sub, Matrix.mul_one, this, sub_self]
  · have := h2 (fun i => inclR (F := F) (AF F) (x i)) (by
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

theorem conj_mem (hW : IsWittFrame σ J X Y) (k : Fin r) {m u : GAd σ J} (hm : m ∈ frameStab σ J (initCols X k) ⊤)
    (hu : u ∈ unipRad σ J (initCols X k)) : m * u * m⁻¹ ∈ unipRad σ J (initCols X k) := by
  rw [mem_unipRad_iff hW] at hu ⊢
  obtain ⟨B', -, e'⟩ := inv_mem hm
  obtain ⟨B, -, e⟩ := hm
  have hmm : (matHom _ σ J m).1 * (matHom _ σ J m⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, e', ← Matrix.mul_assoc (Units.val _) _ B'.1,
      hu.1, ← e', ← Matrix.mul_assoc, hmm, Matrix.one_mul]
  · have hd := dual_eq (initCols X k) m B.1 e
    obtain ⟨a, ha⟩ := hu.2 ((matHom _ σ J m⁻¹).1 *ᵥ y) (by
      rw [← hd, mulVec_mulVec, Matrix.mul_assoc, hmm, Matrix.mul_one, ← mulVec_mulVec, hy, mulVec_zero])
    refine ⟨B.1 *ᵥ a, ?_⟩
    rw [mulVec_mulVec, ← e, ← mulVec_mulVec, ha, mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hmm, one_mulVec,
      map_mul, map_mul, Units.val_mul, Units.val_mul]

theorem eq_one (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (k : Fin r) {g : GAd σ J}
    (hg : g ∈ unipRad σ J (initCols X k)) (hm : g ∈ frameStab σ J (initCols Y k) ⊤) : g = 1 := by
  rw [mem_unipRad_iff hW] at hg
  obtain ⟨B, -, e⟩ := hm
  have hT : cT (σ : E →+* E) (initCols X k) * J * initCols Y k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun hW.xy (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have hT' : cT (σ : E →+* E) (initCols Y k) * J * initCols X k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have aT : adMat F (cT (σ : E →+* E) (initCols X k) * J) * adMat F (initCols Y k) = 1 := by
    rw [← Matrix.map_mul, hT, Matrix.map_one _ (map_zero _) (map_one _)]
  have aT' : adMat F (cT (σ : E →+* E) (initCols Y k) * J) * adMat F (initCols X k) = 1 := by
    rw [← Matrix.map_mul, hT', Matrix.map_one _ (map_zero _) (map_one _)]
  have d1 := dual_eq (initCols X k) g 1 (by rw [hg.1, Matrix.mul_one])
  rw [Formalism.UG.cT_one, Matrix.one_mul] at d1
  have hB : B.1 = 1 := by
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols X k) * J) * ·) e
    simp only [← Matrix.mul_assoc] at this
    rw [d1, aT, Matrix.one_mul] at this
    exact this.symm
  have d2 := dual_eq (initCols Y k) g _ e
  rw [hB, Formalism.UG.cT_one, Matrix.one_mul] at d2
  rw [hB, Matrix.mul_one] at e
  have h0 : ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 → (matHom _ σ J g).1 *ᵥ y = y := fun y hy => by
    obtain ⟨a, ha⟩ := hg.2 y hy
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols Y k) * J) *ᵥ ·) ha
    simp only [mulVec_mulVec, mulVec_sub] at this
    rw [aT', d2, sub_self, one_mulVec] at this
    rw [this, mulVec_zero] at ha
    exact sub_eq_zero.1 ha.symm
  have h1 : ∀ y, (matHom _ σ J g).1 *ᵥ y = y := fun y => by
    have := h0 (y - adMat F (initCols Y k) *ᵥ adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y) (by
      rw [mulVec_sub, mulVec_mulVec (M := adMat F (cT (σ : E →+* E) (initCols X k) * J)), aT, one_mulVec, sub_self])
    rw [mulVec_sub, mulVec_mulVec (M := (matHom _ σ J g).1), e] at this
    exact sub_left_injective this
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have := h1 (Pi.single j 1)
  rw [mulVec_single_one] at this
  exact (congrFun this i).trans (Pi.single_apply _ _ _)

theorem mul_one_by_one {R : Type} [CommRing R] (C : Matrix (Fin n) (Fin 1) R) (B : Matrix (Fin 1) (Fin 1) R) :
    C * B = B.det • C := by
  ext i j
  rw [Subsingleton.elim j 0]
  simp [Matrix.mul_apply, mul_comm]

theorem absE_of_scales {x : Matrix (Fin n) (Fin 1) E} {L : Matrix (Fin 1) (Fin n) E} (hL : L * x = 1) {γ : GAd σ J}
    (hγ : γ ∈ ratPts σ J) {l : (AF F ⊗[F] E)ˣ} (e : Scales σ J x γ l) : absE F E l = 1 := by
  rw [← range_ratEmb] at hγ
  obtain ⟨γ0, rfl⟩ := hγ
  have hmat : (matHom _ σ J (ratEmb σ J γ0)).1 = (γ0.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    ext s t; rfl
  have hL' : adMat F L * adMat F x = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  set c : E := (L * γ0.1.1 * x) 0 0 with hc
  have hl : l.1 = inclR (F := F) (AF F) c := by
    have := congrArg (adMat F L * ·) e
    simp only [Matrix.mul_smul] at this
    rw [hL', hmat, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul] at this
    have := congrFun (congrFun this 0) 0
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    exact this.symm
  by_cases hc0 : c = 0
  · have : Subsingleton (AF F ⊗[F] E) := by
      have h01 := l.mul_inv
      rw [hl, hc0, map_zero, zero_mul] at h01
      exact subsingleton_of_zero_eq_one h01
    rw [Subsingleton.elim l 1, map_one]
  · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 c hc0)
    rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 c hc0)) = l from
      Units.ext (by simp [hl])] at this

theorem levi_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J →
    IsWittFrame σ J X Y →
    (∀ m ∈ levi σ J X Y {0}, ∀ u ∈ unipRad σ J (ResLine.col X), m * u * m⁻¹ ∈ unipRad σ J (ResLine.col X)) ∧
    (∀ g ∈ unipRad σ J (ResLine.col X), g ∈ levi σ J X Y {0} → g = 1) ∧
    (∀ γ ∈ ratPts σ J, γ ∈ levi σ J X Y {0} → γ ∈ leviOne σ J X Y {0}) ∧
    (∀ u ∈ unipRad σ J (ResLine.col X), Scales σ J (ResLine.col X) u 1) ∧
    (∀ m ∈ leviOne σ J X Y {0}, ∃ l, Scales σ J (ResLine.col X) m l ∧ absE F E l = 1) ∧
    ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (ResLine.col X) γ l → absE F E l = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hc : ResLine.col X = initCols X 0 := by
    ext i j
    rw [Subsingleton.elim j 0]
    rfl
  have hlev : ∀ m ∈ levi σ J X Y {0}, m ∈ frameStab σ J (initCols X 0) ⊤ ∧ m ∈ frameStab σ J (initCols Y 0) ⊤ :=
    fun m hm => by
      simp only [levi, Subgroup.mem_iInf] at hm
      exact hm 0 (Finset.mem_singleton_self _)
  have hT' : cT (σ : E →+* E) (initCols Y 0) * J * initCols X 0 = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE (0 : Fin (r + 1)).2)) (j.castLE (0 : Fin (r + 1)).2)).trans
      (by simp only [Matrix.one_apply, Fin.castLE_inj])
  have h6 : ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (initCols X 0) γ l → absE F E l = 1 := fun γ hγ l e =>
    absE_of_scales hT' hγ e
  rw [hc]
  refine ⟨fun m hm u hu => conj_mem hW 0 (hlev m hm).1 hu, fun g hg hm => eq_one h hJ hW 0 hg (hlev g hm).2,
    fun γ hγ hm => ⟨hm, ?_⟩, fun u hu => ?_, fun m hm => ?_, h6⟩
  · show γ ∈ ⨅ k ∈ ({0} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker
    simp only [Subgroup.mem_iInf]
    intro k hk
    obtain rfl := Finset.mem_singleton.1 hk
    obtain ⟨B, -, e⟩ := (hlev γ hm).1
    exact ⟨B, h6 γ hγ (Matrix.GeneralLinearGroup.det B) (e.trans (mul_one_by_one _ _)), e⟩
  · exact (unipRad_fix hu).trans (one_smul _ _).symm
  · have h2 : m ∈ ⨅ k ∈ ({0} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker := hm.2
    simp only [Subgroup.mem_iInf] at h2
    obtain ⟨B, hB, e⟩ := h2 0 (Finset.mem_singleton_self _)
    exact ⟨Matrix.GeneralLinearGroup.det B, e.trans (mul_one_by_one _ _), hB⟩

end GlobalTheory.ResLine.LeviFacts
end
end

section

set_option autoImplicit false

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.AllWt GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FlagTan GlobalTheory.FlatLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

private theorem evR_eq_zero_of_genVal_eq_zero {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (h0 : ∀ Z : Comp Xo c, genVal Z g = 0) {L : Type} [Field L] [Algebra c.F L] (z : FrPt Xo c L) :
    evR Xo c g z = 0 := by
  set_option synthInstance.maxHeartbeats 400000 in
    obtain ⟨hL, -, hG, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
    obtain ⟨C, ψ, z0, t', hψ, hb⟩ := hA hG L z
    rw [evR_frBor hg hb]
    have hnat := (mem_secZ.mp hg).1
    obtain ⟨p, φ0, u, hu⟩ := hL.test C.R C.y
    have e1 : evR Xo c g z0 = (ψ.comp φ0) (g p u) :=
      evR_eq hnat (frMap_comp (χ := ψ.comp φ0) hu hψ (fun _ => rfl))
    have e2 : evR Xo c g C.yg = (C.R.val.comp φ0) (g p u) :=
      evR_eq hnat (frMap_comp (χ := C.R.val.comp φ0) hu C.gen (fun _ => rfl))
    have e3 := evR_frBor hg C.bor
    have e4 : evR Xo c g (genFr hG C.Z) = 0 := by
      have h1 := h0 C.Z
      rw [genVal_apply hG] at h1
      exact h1
    rw [e4, mul_zero, e2, AlgHom.comp_apply, Subalgebra.coe_val] at e3
    have e5 : φ0 (g p u) = 0 := Subtype.ext e3
    rw [e1, AlgHom.comp_apply, e5, map_zero, mul_zero]

theorem secZ_eq_zero_of_genVal {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (h0 : ∀ Z : Comp Xo c, genVal Z g = 0) : g = 0 :=by
  funext p u
  obtain ⟨a, ha⟩ : ∃ a, Ideal.Quotient.mk p.I a = g p u := Ideal.Quotient.mk_surjective _
  show g p u = 0
  rw [← ha, Ideal.Quotient.eq_zero_iff_mem]
  have hJ : p.I.jacobson = p.I := by
    first
    | exact IsJacobsonRing.out' _ p.rad
    | exact IsJacobsonRing.out inferInstance p.rad
    | exact Ideal.IsJacobson.out' _ p.rad
  rw [← hJ, Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨hIm, hm⟩
  letI : Field (MvPolynomial _ c.F ⧸ m) := Ideal.Quotient.field m
  let φ : p.R →ₐ[c.F] MvPolynomial _ c.F ⧸ m := Ideal.Quotient.factorₐ c.F hIm
  obtain ⟨z, hz⟩ := exists_frMap φ u
  have h1 := evR_eq (mem_secZ.mp hg).1 hz
  rw [evR_eq_zero_of_genVal_eq_zero hg h0 z, ← ha] at h1
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h1.symm

theorem genVal_eq_zero_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Z : Comp Xo c) (e : Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, genVal Z f = 0 ↔ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c f y = 0 :=by
  intro E _ _ _ H Dw l Xo c Z e f hf
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  constructor
  · intro h0 S _ _ y hy
    by_cases ht : Tested y
    · have hz : idem Z * f = 0 := by
        refine secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hf) (fun Z' => ?_)
        by_cases hZ : Z' = Z
        · subst hZ
          rw [map_mul, h0, mul_zero]
        · rw [genVal_apply hG]
          exact evC_eq_zero hG hZ (mul_comm f (idem Z) ▸ mul_mem_suppOn f (idem_mem_suppOn Z))
      have h1 : evR Xo c (idem Z * f) y = evR Xo c (idem Z) y * evR Xo c f y := evalAt_mul _ _ _ _ y
      rw [hz, evR_idem hy ht, one_mul] at h1
      rw [← h1]
      exact evalAt_zero _ _ y
    · unfold evR evalAt
      rw [dite_eq_right ht]
  · intro hall
    rw [genVal_apply hG]
    exact hall _ _ (liesOn_genFr hG Z)

end GlobalTheory.CompHt
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TanBasis

open TensorProduct

theorem exists_tan_basis {R A K ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Field K] [Fintype ι] {n : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (xr : A →+* K) (hι : Fintype.card ι = n) :
    ∃ Φ : A →+* TrivSqZeroExt K (ι → K), (∀ a, (Φ a).fst = xr a) ∧ (∀ r, (Φ (algebraMap R A r)).snd = 0) ∧
      ∀ M M' : ι → K, (∀ a, ∑ k, (Φ a).snd k * M k = ∑ k, (Φ a).snd k * M' k) → M = M' := by
  classical
  haveI := GlobalTheory.AugCot.smooth_of_locally h
  letI : Algebra A K := xr.toAlgebra
  have hrank : Module.finrank K (K ⊗[A] Ω[A⁄R]) = n := by
    have h1 := Module.rankAtStalk_baseChange (R := A) (M := Ω[A⁄R]) (S := K) (IsLocalRing.closedPoint K)
    rw [Module.rankAtStalk_eq_finrank_of_free, GlobalTheory.AugCot.rankAtStalk_kaehler_of_locally h] at h1
    exact_mod_cast h1
  let b : Module.Basis ι K (K ⊗[A] Ω[A⁄R]) :=
    (Module.finBasisOfFinrankEq K _ hrank).reindex (Fintype.equivFinOfCardEq hι).symm
  let δ : A → (ι → K) := fun a => b.equivFun (1 ⊗ₜ KaehlerDifferential.D R A a)
  have hsm : ∀ (a : A) (m : Ω[A⁄R]), (1 : K) ⊗ₜ[A] (a • m) = xr a • ((1 : K) ⊗ₜ[A] m) := by
    intro a m
    rw [TensorProduct.tmul_smul, ← algebraMap_smul K a]
    rfl
  have hδmul : ∀ a a', δ (a * a') = xr a • δ a' + xr a' • δ a := by
    intro a a'
    simp only [δ, Derivation.leibniz, TensorProduct.tmul_add, hsm, map_add (f := _), map_smul]
  have hδadd : ∀ a a', δ (a + a') = δ a + δ a' := by
    intro a a'; simp only [δ, map_add (f := _), TensorProduct.tmul_add]
  have hδalg : ∀ r, δ (algebraMap R A r) = 0 := by
    intro r; simp only [δ, Derivation.map_algebraMap, TensorProduct.tmul_zero, map_zero]
  have hδ1 : δ 1 = 0 := by simpa using hδalg 1
  have hδ0 : δ 0 = 0 := by simp only [δ, map_zero, TensorProduct.tmul_zero]
  let Φ : A →+* TrivSqZeroExt K (ι → K) :=
    { toFun := fun a => TrivSqZeroExt.inl (xr a) + TrivSqZeroExt.inr (δ a)
      map_one' := by ext <;> simp [hδ1]
      map_mul' := fun a a' => by
        ext k
        · simp
        · simp [hδmul, TrivSqZeroExt.snd_mul, add_comm]
      map_zero' := by ext <;> simp [hδ0]
      map_add' := fun a a' => by ext <;> simp [hδadd] }
  refine ⟨Φ, fun a => by simp [Φ], fun r => by simp [Φ, hδalg], fun M M' hM => ?_⟩
  let L : (ι → K) → (K ⊗[A] Ω[A⁄R] →ₗ[K] K) := fun M => Fintype.linearCombination K M ∘ₗ b.equivFun.toLinearMap
  have hL : ∀ M : ι → K, ∀ a, L M (1 ⊗ₜ KaehlerDifferential.D R A a) = ∑ k, (Φ a).snd k * M k := by
    intro M a
    simp [L, Φ, δ, Fintype.linearCombination_apply, smul_eq_mul]
  have hLL : L M = L M' := by
    apply (LinearMap.liftBaseChangeEquiv K).symm.injective
    refine LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A) fun a => ?_
    rw [LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.liftBaseChangeEquiv_symm_apply, hL, hL, hM]
  funext j
  have := LinearMap.congr_fun hLL (b j)
  simpa [L, Finsupp.single_eq_pi_single, Fintype.linearCombination_apply_single] using this

end GlobalTheory.TanBasis

namespace GlobalTheory.TanBasis

theorem exists_point_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι], Fintype.card ι = Dw.dim → ∃ X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x ∧ Function.Injective (fun M : ι → K => spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  intro E _ _ _ H Dw l Xo c K _ _ y ι _ hι
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y.x (IsLocalRing.closedPoint K)) (U := ⊤) trivial
  have hrange : Set.range y.x ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    rwa [Subsingleton.elim p (IsLocalRing.closedPoint K)]
  let y' := IsOpenImmersion.lift hU.fromSpec y.x hrange
  have hy' : y' ≫ hU.fromSpec = y.x := IsOpenImmersion.lift_fac _ _ _
  let g := Spec.preimage (hU.fromSpec ≫ Xo.s)
  have hg : Spec.map g = hU.fromSpec ≫ Xo.s := Spec.map_preimage _
  let xr := Spec.preimage y'
  have hxr : Spec.map xr = y' := Spec.map_preimage _
  haveI := Xo.smooth
  have hsm : SmoothOfRelativeDimension Dw.dim (Spec.map g) := by
    rw [hg]
    have := (inferInstance : SmoothOfRelativeDimension (0 + Dw.dim) (hU.fromSpec ≫ Xo.s))
    rwa [zero_add] at this
  have hloc := HasRingHomProperty.Spec_iff.1 hsm
  letI : Algebra (KA l) Γ(Xo.X, U) := g.hom.toAlgebra
  obtain ⟨Φ, h1, h2, h3⟩ := exists_tan_basis (R := KA l) (A := Γ(Xo.X, U)) hloc xr.hom hι
  have hbase : ∀ r, xr.hom (g.hom r) = algebraMap c.F K (IntermediateField.inclusion c.le r) := by
    have : Spec.map (g ≫ xr) = sOf c K := by
      rw [Spec.map_comp, hxr, hg, ← Category.assoc, hy', y.x_over]
    intro r
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective this)) r
  have hfst : (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom.comp Φ = xr.hom := by
    ext a; exact h1 a
  refine ⟨spMap Φ ≫ hU.fromSpec, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hg, spMap, ← Spec.map_comp, sOf]
    have hΦg : Φ.comp g.hom =
        (algebraMap c.F (TrivSqZeroExt K (ι → K))).comp (IntermediateField.inclusion c.le).toRingHom := by
      refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
      · rw [RingHom.comp_apply, h1, hbase]
        simp [TrivSqZeroExt.algebraMap_eq_inl']
      · rw [RingHom.comp_apply, show g.hom r = algebraMap (KA l) Γ(Xo.X, U) r from rfl, h2]
        simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [← hΦg]
    rfl
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom.comp Φ)) ≫ _ = _
    rw [hfst]
    change Spec.map xr ≫ _ = _
    rw [hxr, hy']
  · intro M M' hMM
    simp only at hMM
    rw [← Category.assoc, ← Category.assoc, cancel_mono, spMap, spMap, spMap, ← Spec.map_comp,
      ← Spec.map_comp] at hMM
    have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hMM)
    apply h3
    intro a
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hr a)
    simpa using this

end GlobalTheory.TanBasis
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerConjTransport

theorem kkMap_top_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    {N : Std G U} (Z : Normal W N) (t : T) (j : ℕ) (d : FinDatum G t (.top t j)) (x : FinPt G (Pair.top t j).small)
    (y : FinPt G (Pair.top t j).big) (Hf : VC D (G.pS (Pair.top t j)).rank (G.pT (Pair.top t j)).rank → ℂ)
    (hJ : Formalism.L2.Ker.JetInVV ℂ (wt G (Pair.top t j).small) (wt G (Pair.top t j).big) (nuEnd G (.top t j)))
    (hper : ∀ τ : D.what₂.Tau, period Z.δ τ ≠ 0)
    (hjet : ∀ mon, jetTab W N.frC (.top t j) (Z.vec d) (x * N.u _) (y * N.u _) mon = Z.c0 (.top t j) * opp (.top t j : Pair T)
       (((mon.mapDomain (fvar G (.top t j))).prod fun v e => period Z.δ v.1 ^ e) *
         GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar G (.top t j))) 1) Hf)) :
    Z.kkMap 1 d x y = Formalism.L2.Ker.jetOp (wt G (Pair.top t j).small) (wt G (Pair.top t j).big)
      (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) Hf) (nuEnd G (.top t j)) := by
  have e1 : jetTab W N.frC (.top t j) (Z.vec d) (x * N.u _) (y * N.u _) = fun mon => (Z.c0 (.top t j) : ℂ) *
      ((mon.prod fun v e => period Z.δ v.1 ^ e) * GL3Theta.applyAt0 D (MvPolynomial.monomial mon 1) Hf) := by
    funext mon
    rw [hjet mon, show fvar G (Pair.top t j) = id from rfl, Finsupp.mapDomain_id]
    rfl
  unfold Normal.kkMap fockComp
  rw [e1, GlobalTheory.T.jetOperator_characterScaledTable _ _ _ _ _ _ hJ, smul_smul]
  have hs : Z.scal 1 (Pair.top t j) * ((Z.c0 (Pair.top t j) : ℂ) *
      ∏ τ, period Z.δ τ ^ ∑ i, (wt G (Pair.top t j).big τ).natW i) = 1 := by
    unfold Normal.scal GlobalTheory.FunObj.fockDeg
    simp only [opp, RingHom.id_apply, Pi.one_apply, one_div]
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    simp only [← mul_pow, inv_mul_cancel₀ (hper _), one_pow, Finset.prod_const_one, mul_one]
    simp
  rw [hs, one_smul]

end GlobalTheory.KerConjTransport

end
end
