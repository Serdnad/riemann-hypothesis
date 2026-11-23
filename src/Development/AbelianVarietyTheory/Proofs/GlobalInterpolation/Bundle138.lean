module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle136
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle001
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle107
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle135
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicIsogenyConstantOfIsogenyFormula
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle040
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.TorsValsFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.IdxHom

open GlobalTheory.CharValCompare Matrix Kronecker

variable {E : Type} [Field E] {a b : ℕ}

def crd (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b →+ (Fin a × Fin b → E) where
  toFun x := (LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a))).vec
  map_zero' := by simp
  map_add' x y := by
    rw [LinearMap.add_comp, LinearMap.comp_add, map_add (f := _), Matrix.vec_add]

theorem crd_apply (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    crd g g' x = (LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a))).vec := rfl

theorem crd_injective (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : Function.Injective (crd g g') := by
  intro x y h
  rw [crd_apply, crd_apply, Matrix.vec_inj] at h
  have h1 := LinearMap.toMatrix'.injective h
  refine LinearMap.ext fun v => ?_
  have := LinearMap.congr_fun h1 (g.symm v)
  simpa using this

theorem crd_surjective (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : Function.Surjective (crd g g') := by
  intro v
  obtain ⟨A, rfl⟩ := Matrix.vec_bijective.2 v
  refine ⟨(g' : Sp E b →ₗ[E] Sp E b) ∘ₗ Matrix.toLin' A ∘ₗ (g.symm : Sp E a →ₗ[E] Sp E a), ?_⟩
  rw [crd_apply]
  congr 1
  rw [← LinearMap.toMatrix'_toLin' A]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp

def chg (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) : Matrix (Fin a × Fin b) (Fin a × Fin b) E :=
  (LinearMap.toMatrix' ((g₂.symm : Sp E a →ₗ[E] Sp E a) ∘ₗ (g₁ : Sp E a →ₗ[E] Sp E a)))ᵀ ⊗ₖ
    LinearMap.toMatrix' ((g₁'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ (g₂' : Sp E b →ₗ[E] Sp E b))

theorem chg_mulVec (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    chg g₁ g₂ g₁' g₂' *ᵥ crd g₂ g₂' x = crd g₁ g₁' x := by
  rw [chg, crd_apply, crd_apply, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose,
    ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  congr 2
  refine LinearMap.ext fun v => ?_
  simp

theorem det_chg (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) :
    (chg g₁ g₂ g₁' g₂').det = ((dt g₂)⁻¹ * dt g₁) ^ b * ((dt g₁')⁻¹ * dt g₂') ^ a := by
  rw [chg, Matrix.det_kronecker, Matrix.det_transpose, LinearMap.det_toMatrix', LinearMap.det_toMatrix',
    LinearMap.det_comp, LinearMap.det_comp, LinearEquiv.det_coe_symm, LinearEquiv.det_coe_symm, Fintype.card_fin,
    Fintype.card_fin, dt_eq, dt_eq, dt_eq, dt_eq]

variable [NumberField E]

theorem ordE_chg (P : HeightOneSpectrum (𝓞 E)) (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) :
    ordE P (chg g₁ g₂ g₁' g₂').det =
      (b * ordE P (dt g₁) - a * ordE P (dt g₁')) - (b * ordE P (dt g₂) - a * ordE P (dt g₂')) := by
  have h : ∀ {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n), P.valuation E (dt f) = WithZero.exp (-ordE P (dt f)) := by
    intro n f
    rw [ordE, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 (dt_ne f))]
  rw [det_chg, ordE, map_mul, map_pow, map_pow, map_mul, map_mul, map_inv₀, map_inv₀, h g₁, h g₂, h g₁', h g₂',
    ← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.log_exp, nsmul_eq_mul, nsmul_eq_mul]
  ring

variable [StarRing E]

theorem mem_homAt_iff {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {g : Sp E a ≃ₗ[E] Sp E a} {g' : Sp E b ≃ₗ[E] Sp E b} (hg : IsFr P N g) (hg' : IsFr P N' g') (x : HomE E a b) :
    x ∈ homAt {P} N N' ↔ ∀ i, IntAt P (crd g g' x i) := by
  change (∀ Q ∈ ({P} : Finset _), ∀ y ∈ localization₂ Q.asIdeal N, x y ∈ localization₂ Q.asIdeal N') ↔ _
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro h ⟨j, i⟩
    have h1 := h _ ((hg _).2 (single_mem_stdAt P j))
    rw [← g'.apply_symm_apply (x _), hg', stdAt, mem_localization_standardLattice] at h1
    have h2 := h1 i
    simpa [crd_apply, LinearMap.toMatrix'_apply] using h2
  · intro h y hy
    obtain ⟨z, rfl⟩ := g.surjective y
    rw [hg, stdAt, mem_localization_standardLattice] at hy
    rw [← g'.apply_symm_apply (x _), hg', stdAt, mem_localization_standardLattice]
    intro i
    have : g'.symm (x (g z)) =
        LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a)) *ᵥ z := by
      rw [LinearMap.toMatrix'_mulVec]
      rfl
    rw [this, Matrix.mulVec, dotProduct]
    exact intAt_sum _ _ fun j _ => (h (j, i)).mul (hy j)

theorem relIndex_homAt : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (P : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Sp E b)), IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' → homAt {P} N₂ N₂' ≤ homAt {P} N₁ N₁' → (((homAt {P} N₂ N₂').toAddSubgroup.relIndex (homAt {P} N₁ N₁').toAddSubgroup : ℕ) : ℚ) = ((Ideal.absNorm P.asIdeal : ℕ) : ℚ) ^ (volExp P N₁ N₁' - volExp P N₂ N₂') := by
  intro E _ _ _ a b P N₁ N₂ N₁' N₂' h₁ h₂ h₁' h₂' hle
  obtain ⟨g₁, hg₁⟩ := exists_isFr P h₁
  obtain ⟨g₂, hg₂⟩ := exists_isFr P h₂
  obtain ⟨g₁', hg₁'⟩ := exists_isFr P h₁'
  obtain ⟨g₂', hg₂'⟩ := exists_isFr P h₂'
  have h0 : ∀ x, x ∈ (homAt {P} N₁ N₁').toAddSubgroup.map (crd g₁ g₁') ↔ ∀ i, IntAt P (x i) := by
    intro x
    obtain ⟨y, rfl⟩ := crd_surjective g₁ g₁' x
    rw [AddSubgroup.mem_map_iff_mem (crd_injective _ _), Submodule.mem_toAddSubgroup, mem_homAt_iff hg₁ hg₁']
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (crd_injective g₁ g₁'),
    GlobalTheory.IdxDet.relIndex_mulVec E (Fin a × Fin b) P (chg g₁ g₂ g₁' g₂') _ _ ?_ h0 ?_ (AddSubgroup.map_mono hle),
    ordE_chg, volExp, volExp, ordDet_eq hg₁, ordDet_eq hg₂, ordDet_eq hg₁', ordDet_eq hg₂']
  · rw [det_chg]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (dt_ne _)) (dt_ne _)))
      (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (dt_ne _)) (dt_ne _)))
  · intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, (h0 _).2 ((mem_homAt_iff hg₂ hg₂' y).1 hy), (chg_mulVec _ _ _ _ y).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨y, rfl⟩ := crd_surjective g₂ g₂' v
      exact ⟨y, (mem_homAt_iff hg₂ hg₂' y).2 ((h0 _).1 hv), (chg_mulVec _ _ _ _ y).symm⟩

end GlobalTheory.IdxHom
end
end

section

noncomputable section

namespace GlobalTheory.KerT

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker

theorem spread_lt_of_two_mul_lt {n p : ℕ} (hp : p.Prime) (lam : DomWeight n)
    (h : ∀ a b : Fin n, 2 * (lam.w a - lam.w b + (n : ℤ)) < (p : ℤ)) : lam.spread < p := by
  have hp0 := hp.pos
  unfold DomWeight.spread
  split_ifs with hn
  · have := h ⟨0, hn⟩ ⟨n - 1, by omega⟩
    omega
  · omega

theorem localization_delAtr_eq_localization_nabAtr : GlobalTheory.Published.InducedSimpleLowestAlcove →
    ∀ (X : Fields) (n p : ℕ) (lam : X.Tau → DomWeight n), p.Prime →
      (∀ τ (a b : Fin n), 2 * ((lam τ).w a - (lam τ).w b + (n : ℤ)) < (p : ℤ)) →
      ∀ w : HeightOneSpectrum (𝓞 X.K), ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
        ∀ L : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsFullLattice X.E L →
          localization₂ w.asIdeal (delAtr X.emb lam L) = localization₂ w.asIdeal (nabAtr X.emb lam L) := by
  intro h X n p lam hp hl w hw L hL
  refine le_antisymm ?_ ?_
  · rintro x ⟨s, hs, hx⟩
    exact ⟨s, hs, delLeNab X.K X.Tau n lam _ hx⟩
  · exact GlobalTheory.ColPeriod.WeylLoc.nabLeDel_of_local (GlobalTheory.Published.weylDualWeylLatticesAgree_of_lowest_alcove h) X.K X.Tau n lam _
      (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau n X.emb τ L hL)) p w hp hw
      fun τ => spread_lt_of_two_mul_lt hp (lam τ) (hl τ)

end GlobalTheory.KerT
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.Moved

theorem sd_stdL (D : D7) (N : ℕ) : StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D N) := by
  letI := D.host.cmStar
  have hr : ∀ x : D.host.E, x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ x := fun x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hm : ∀ x : Fin N → D.host.E, x ∈ StandardLatticesGL3.stdL D N ↔ ∀ k, IsIntegral ℤ (x k) := fun x => by
    simp only [StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun k => hr (x k)
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → D.host.E) ∈ StandardLatticesGL3.stdL D N := fun k => by
    rw [hm]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [hr]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd D.host.E).toIntAlgHom).mul (hy i)
  · rw [hm]
    intro k
    have := h _ (hs k)
    rw [hr] at this
    simpa [Formalism.BasicNotions.stdH, Pi.single_apply, apply_ite] using this

theorem isHerm_formV (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (formV A n N N') := by
  intro x y

  simp [formV, map_sum, mul_comm]

theorem inter_mem_Th {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {H : Sesq V} {α : V → ℂ}
    (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} (hf : relIdx A₁ A₂ ≠ 0)
    (hs₁ : IsSemiChar H A₁ α) (hd₂ : IsSelfDual H A₂) (hs₂ : IsSemiChar H A₂ α)
    {F : V → ℂ} (hF : F ∈ Th H α A₁) : inter H α A₁ A₂ F ∈ Th H α A₂ := by
  have : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := Nat.finite_of_card_ne_zero hf
  refine ⟨?_, GlobalTheory.ThetaInter.inter_mem_fixedBy hH hs₁ hd₂ hs₂ hF.2⟩
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  have hU : ∀ x z, AnalyticAt ℂ (opU H x F) z := fun x z => by
    have h : AnalyticAt ℂ (fun z => H z x) z := (LinearMap.toContinuousLinearMap (H.flip x)).analyticAt z
    have h2 : AnalyticAt ℂ (fun z => F (z + x)) z :=
      AnalyticAt.comp (f := fun z => z + x) (hF.1 _ (Set.mem_univ _)) (analyticAt_id.add analyticAt_const)
    exact h2.mul ((analyticAt_const.mul h).sub analyticAt_const).cexp
  rw [GlobalTheory.ThetaInter.inter_eq]
  intro z _
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.mul (hU _ z))

theorem iop_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (A₁ A₂ : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) A₁ A₂ G =
      inter (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) A₁ A₂ G := rfl

theorem iop_mul (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (A B : AddSubgroup (TaylorLogMetric.VC D N N')) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (z : TaylorLogMetric.VC D N N') : TaylorLogMetric.Iop D T A B (fun w => c * G w) z = c * TaylorLogMetric.Iop D T A B G z := by
  unfold TaylorLogMetric.Iop
  rw [mul_left_comm, mul_finsum _ c]
  congr 1
  refine finsum_congr fun q => ?_
  simp only [TaylorLogMetric.U]; ring

variable {D : D7} {χ : TaylorLogMetric.IdE D → ℂ} {n : ℕ} {L L' L'' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}

theorem chi_detId_mul (hχ : TaylorLogMetric.IsChi D χ) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') (h'' : StandardLatticesGL3.SD D L'') :
    χ (TaylorLogMetric.detId D L L'') = χ (TaylorLogMetric.detId D L L') * χ (TaylorLogMetric.detId D L' L'') := by
  rw [(GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L' L'' h h' h'').2]
  exact hχ.1 _ _ (GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L' L'' h h' h'').1 (GlobalTheory.RelDetIdeal.detId_normOne_mul D n L' L'' L'' h' h'' h'').1

theorem chi_detId_ne_zero (hχ : TaylorLogMetric.IsChi D χ) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') : χ (TaylorLogMetric.detId D L L') ≠ 0 := by
  obtain ⟨⟨𝔟, -, hb⟩, h2⟩ := GlobalTheory.RelDetIdeal.detId_normOne_mul D n L L L h h h
  have h1 : TaylorLogMetric.detId D L L = 1 := by
    rw [← mul_one (TaylorLogMetric.detId D L L), ← hb, ← mul_assoc, ← h2]
  have h3 := chi_detId_mul hχ h h' h
  have h4 : χ 1 = 1 := by simpa [Submodule.one_eq_span] using hχ.2 1
  rw [h1, h4] at h3
  exact left_ne_zero_of_mul_eq_one h3.symm

theorem thMoved_mem_and_moves : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ), TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → (∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 ∧ B.thMoved a b L L' ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L L')) ∧ (∀ L L' L'', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L'' → B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L')) ∧ ∀ L L₁ L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L' → B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  intro D cc δ B χ a b hχ hE hL h0 ha hb
  have sa := sd_stdL D a
  have sb := sd_stdL D b
  have hne : ∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 := fun L L' h h' =>
    mul_ne_zero (zpow_ne_zero _ (chi_detId_ne_zero hχ sa h)) (zpow_ne_zero _ (chi_detId_ne_zero hχ sb h'))
  have step : ∀ L₁ L₁' L₂ L₂', StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L₁' → StandardLatticesGL3.SD D L₂ → StandardLatticesGL3.SD D L₂' → ∀ F,
      F ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L₁ L₁') →
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') F ∈
        Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L₂ L₂') := by
    intro L₁ L₁' L₂ L₂' h₁ h₁' h₂ h₂' F hF
    have A₁ : TaylorLogMetric.admitted D a b L₁ L₁' := ⟨ha, hb, h₁, h₁'⟩
    have A₂ : TaylorLogMetric.admitted D a b L₂ L₂' := ⟨ha, hb, h₂, h₂'⟩
    rw [iop_eq]
    exact inter_mem_Th (isHerm_formV _ _ _ _) (hL.2 a b _ _ _ _ A₁ A₂).1 (hL.1 a b _ _ A₁).2 (hL.1 a b _ _ A₂).1
      (hL.1 a b _ _ A₂).2 hF
  refine ⟨fun L L' h h' => ⟨hne L L' h h', step _ _ _ _ h sb h h' _ (step _ _ _ _ sa sb h sb _ h0)⟩, ?_, ?_⟩
  · intro L L' L'' h h' h''
    funext z
    have e : Base.chiFac χ a b L L'' * B.thMoved a b L L'' z = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'')
          (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
      congrFun (hE.2.1 a b ⟨L, h⟩ ⟨L', h'⟩ ⟨L'', h''⟩ ha hb) z
    have f : Base.chiFac χ a b L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
      unfold Base.chiFac
      rw [chi_detId_mul hχ sb h' h'', mul_zpow]
      ring
    rw [iop_mul, ← mul_assoc, ← f] at e
    exact mul_left_cancel₀ (hne _ _ h h'') e
  · intro L L₁ L' h h₁ h'
    funext z
    have e : Base.chiFac χ a b L₁ L' * B.thMoved a b L₁ L' z = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) *
        TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L')
          (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
      congrFun (hE.2.2 a b ⟨L, h⟩ ⟨L₁, h₁⟩ ⟨L', h'⟩ ha hb) z
    have f : Base.chiFac χ a b L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
      unfold Base.chiFac
      rw [chi_detId_mul hχ sa h h₁, mul_zpow]
      ring
    rw [iop_mul, ← mul_assoc, ← f] at e
    exact mul_left_cancel₀ (hne _ _ h₁ h') e

end GlobalTheory.ThetaMove.Moved
end

section

noncomputable section

namespace GlobalTheory.ThetaZeroAlg

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
open GlobalTheory.IsogConst

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem omegaK_eq (d : ℕ) : Formalism.L2.Th1.CM.omegaK d = Formalism.L2.Th1.F.cmTheta 1 d := by
  unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring

theorem hasCMBy (B : Base D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d B.L := by
  intro ω hω
  rw [omegaK_eq]
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B ω hω

theorem disc_one (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.g₂ ^ 3 - 27 * B.L.g₃ ^ 2 = 1 := by
  have hL' : (B.L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← B.lat]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ B.L hL'
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

theorem d_sq (D : D7) : Squarefree D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).squarefree

theorem host_imagQuadratic_discriminant_mod_four (D : D7) : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega

theorem g₂_g₃_mem_Qbar (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.g₂ ∈ TaylorLogMetric.Qbar ∧ B.L.g₃ ∈ TaylorLogMetric.Qbar := by
  have hdisc := disc_one B hcc hδ
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv B.L) := GlobalTheory.ThLoc.cm1 D.host.d B.L (d_sq D) (host_imagQuadratic_discriminant_mod_four D) (hasCMBy B)
  have hjQ : Formalism.L2.Th1.CM.jInv B.L ∈ TaylorLogMetric.Qbar :=
    (qbar_iff _).2 (hj.tower_top (A := ℚ)).isAlgebraic
  have hg2c : B.L.g₂ ^ 3 = Formalism.L2.Th1.CM.jInv B.L / 1728 := by
    unfold Formalism.L2.Th1.CM.jInv; rw [hdisc]; ring
  have h2 : B.L.g₂ ∈ TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 3) (by norm_num) ?_
    rw [hg2c]; exact div_mem hjQ (nat_mem 1728)
  have h3sq : B.L.g₃ ^ 2 = (B.L.g₂ ^ 3 - 1) / 27 := by rw [← hdisc]; ring
  have h3 : B.L.g₃ ∈ TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 2) (by norm_num) ?_
    rw [h3sq]
    exact div_mem (sub_mem (pow_mem h2 3) (one_mem _)) (nat_mem 27)
  exact ⟨h2, h3⟩

theorem kernelBase_periodLattice_sigmaTwo_algebraic (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    Formalism.L2.Th1.F.s2 B.L ∈ TaylorLogMetric.Qbar := by
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  have hd0 : 0 < D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).pos
  obtain ⟨S, -, -, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny D.host.d B.L (hasCMBy B) (-1) 2 (by simp) hd0
  have hαsq := alpha_sq D.host.d
  have hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ TaylorLogMetric.Qbar :=
    qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))
  have hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0 := by
    intro h0
    rw [h0] at hαsq
    have : (D.host.d : ℂ) = 0 := by linear_combination hαsq
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have he : InQ (Formalism.L2.Th1.F.pSeries B.L) := by
    intro k
    rw [Formalism.L2.KerInert.AlgP.pSeries_eq_map TaylorLogMetric.Qbar B.L h2 h3, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  have hc := algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso
  rw [hαsq] at hc
  have hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) := by
    push_cast; ring
  rw [hN] at hc
  have hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card S + 1 + D.host.d ≠ 0)
  have e : Formalism.L2.Th1.F.s2 B.L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ *
      (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 B.L) := by
    rw [← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [e]
  exact mul_mem (inv_mem (natCast_mem _ _)) hc

theorem weierstrassP_halfPeriod_algebraic (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.weierstrassP (B.ω₀ / 2) ∈ TaylorLogMetric.Qbar := by
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  haveI : Algebra.IsAlgebraic ℚ TaylorLogMetric.Qbar :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 x.2)⟩
  have hN : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) ∈ B.L.lattice := by
    have e : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) = B.ω₀ := by push_cast; ring
    rw [e]; exact B.omega_mem
  have hx : IsAlgebraic ℚ (B.L.weierstrassP (B.ω₀ / 2)) :=
    (PI.GalTorsConj.W.wp_isAlgebraic B.L TaylorLogMetric.Qbar h2 h3 2 (B.ω₀ / 2) (by norm_num) hN
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)).restrictScalars ℚ
  exact mem_algebraicClosure_iff.2 hx

theorem evenTheta_iteratedDeriv_zero_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ k : ℕ, iteratedDeriv k B.th0 0 ∈ TaylorLogMetric.Qbar := by
  intro D cc δ B hcc hδ k
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  have hc := Formalism.L2.KerInert.AlgP.theta_null_coefficients B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B) TaylorLogMetric.Qbar h2 h3
    (kernelBase_periodLattice_sigmaTwo_algebraic B hcc hδ) (weierstrassP_halfPeriod_algebraic B hcc hδ) k
  unfold Formalism.L2.Th1.F.taylor0 at hc
  rw [PowerSeries.coeff_mk] at hc
  have hf : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have e : iteratedDeriv k B.th0 0 = ((k.factorial : ℕ) : ℂ) *
      (iteratedDeriv k (Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2)) 0 / ((k.factorial : ℕ) : ℂ)) := by
    rw [mul_div_cancel₀ _ hf]; rfl
  rw [e]
  exact mul_mem (natCast_mem _ _) hc

end GlobalTheory.ThetaZeroAlg
end
end
