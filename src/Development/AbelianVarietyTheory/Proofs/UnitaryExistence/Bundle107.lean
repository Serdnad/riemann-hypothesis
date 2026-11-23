module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle146
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle128
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle097
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle071
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveField

open GlobalTheory.Ex.UnifModel GlobalTheory.Ex.TorsionField

theorem exists_finset_fixed (hM : Out.MulNSt) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (P : Out.PolAV (Sp M)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset ℂ, (∀ z ∈ s, IsIntegral ℚ z) ∧ ∀ τ : ℂ →+* ℂ, (∀ x ∈ M, τ x = x) → (∀ z ∈ s, τ z = z) →
      ∀ x : Over.mk (spMap (algebraMap M ℂ)) ⟶ P.A, x ^ n = 1 → spMap τ ≫ x.left = x.left := by
  classical
  let F := algebraicClosure M ℂ
  have : IsAlgClosed F := (algebraicClosure.isAlgClosure M ℂ).isAlgClosed
  obtain ⟨s, hs⟩ := exists_finset (F := F) hM P hn
  refine ⟨s.image Subtype.val, fun z hz => ?_, fun τ h₁ h₂ x hx => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact isIntegral_trans (A := M) _ (mem_algebraicClosure_iff'.1 y.2)
  · let k : Subfield F := RingHom.eqLocusField (τ.comp (algebraMap F ℂ)) (algebraMap F ℂ)
    obtain ⟨y, hy, hy'⟩ := exists_descend_algClosed hM P (algebraMap M F) (algebraMap F ℂ) (algebraMap M ℂ)
      (fun _ => rfl) hn x hx
    obtain ⟨z, hz⟩ := hs k k.subtype (fun c => ⟨⟨algebraMap M F c, h₁ c c.2⟩, rfl⟩)
      (fun c hc => ⟨⟨c, h₂ c (Finset.mem_image_of_mem _ hc)⟩, rfl⟩) y hy
    have e₁ : spMap (algebraMap F ℂ) ≫ spMap k.subtype = spMap ((algebraMap F ℂ).comp k.subtype) :=
      spMap_comp fun _ => rfl
    have e₂ : spMap τ ≫ spMap ((algebraMap F ℂ).comp k.subtype) = spMap ((algebraMap F ℂ).comp k.subtype) :=
      spMap_comp fun c => c.2
    rw [← hy', ← hz, reassoc_of% e₁, reassoc_of% e₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_wC_eq (H : Host E) (a : ℤ × ℤ) :
    ∃ m k : ℤ, wC H a = (m : ℂ) + k * ((1 + Complex.I * Real.sqrt H.d) / 2) := by
  have h : H.rt0 ^ 2 = (Complex.I * Real.sqrt H.d) ^ 2 := by
    rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨a.1, a.2, by rw [wC, h]⟩
  · exact ⟨a.1 + a.2, -a.2, by rw [wC, h]; push_cast; ring⟩

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) :
    u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_pow_eq_one (C : Curve H) {n : ℕ} (hn : 0 < n) (a : ℤ × ℤ) :
    (C.u.ex fun _ => C.c * (wC H a / n)) ^ n = 1 := by
  obtain ⟨m, k, h⟩ := exists_wC_eq H a
  rw [← ex_nsmul, C.u.ker]
  refine (C.lat _).2 ⟨m, k, funext fun _ => ?_⟩
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [← h, Pi.smul_apply, nsmul_eq_mul]
  field_simp

theorem exists_model (H : Host E) : ∃ (M : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ M)
    (P : Out.PolAV (Sp M)) (C : Curve H) (ψ : C.P.A.left ⟶ P.A.left),
    IsGrpPullback C.P.A P.A (spMap (algebraMap M ℂ)) ψ := by
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, -, ⟨P₀, π, -, -, ⟨hg₀, hπ, hL₀⟩, -⟩, hcm, -⟩ :=
    cmCurve_closed H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := exists_baseChange firstFiveLaws.1.polBaseChange (spMap (algebraMap M ℂ)) P₀
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all PC
  have hL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (pull_isLB P₀.isLB ψ) (pull_isLB P.isLB _) hLC
      (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (Geo.Tor.chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀.symm)
  obtain ⟨c, hc, hΛ⟩ := hcm PC (ψ ≫ π)
    ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp fun _ => rfl) rfl, hL.symm⟩ u
  rw [hw] at hΛ
  exact ⟨M, inferInstance, P₀, ⟨PC, hgC.trans (hg₀.trans hg), u, hu, c, hc, hΛ⟩, ψ, hψ⟩

theorem exists_curveOver (H : Host E) {n : ℕ} (hn : 0 < n) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ CurveOver H F n := by
  obtain ⟨M, _, P, C, ψ, hψ⟩ := exists_model H
  obtain ⟨s, hs, hfix⟩ := exists_finset_fixed firstFiveLaws.1.mulN M P hn
  have := IntermediateField.finiteDimensional_adjoin (K := ℚ) (S := (s : Set ℂ)) hs
  refine ⟨M ⊔ IntermediateField.adjoin ℚ (s : Set ℂ), inferInstance, fun τ hτ => ?_⟩
  have h₁ : ∀ x ∈ M, (τ : ℂ →+* ℂ) x = x := fun x hx => hτ x (le_sup_left (a := M) hx)
  have h₂ : ∀ z ∈ s, (τ : ℂ →+* ℂ) z = z := fun z hz =>
    hτ z (le_sup_right (a := M) (IntermediateField.subset_adjoin ℚ _ hz))
  have e : spMap (τ : ℂ →+* ℂ) ≫ spMap (algebraMap M ℂ) = spMap (algebraMap M ℂ) :=
    spMap_comp fun c => h₁ c c.2
  have w : ψ ≫ P.A.hom = (C.P.A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap (algebraMap M ℂ) := by
    rw [Category.assoc, e, hψ.1.w]
  refine ⟨C, hψ.1.lift _ _ w, hψ.cancel (hψ.congr e.symm (hψ.1.lift_fst _ _ w).symm) (hψ.1.lift_snd _ _ w),
    fun a => ?_⟩
  have h1 : wC H (1, 0) = 1 := by simp [wC]
  rw [h1, _root_.one_mul]
  obtain ⟨ε, hε⟩ := exists_mulEquiv_of_isGrpPullback hψ (𝟙 (Sp ℂ)) (spMap (algebraMap M ℂ)) (Category.id_comp _).symm
  have hx := hfix τ h₁ h₂ (ε (C.u.ex fun _ => C.c * (wC H a / n))) (by
    rw [← map_pow]
    exact (congrArg ε (ex_pow_eq_one C hn a)).trans (map_one ε))
  rw [hε] at hx
  have ho : C.pt (wC H a / n) ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex fun _ => C.c * (wC H a / n))
  refine hψ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hψ.1.lift_fst, Category.assoc]
    exact hx.symm
  · rw [Category.assoc, hψ.1.lift_snd, Category.assoc, ho, reassoc_of% ho, Category.comp_id]

theorem exists_coeff_curveOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (n : ℕ), 0 < n → ∃ c' : Coeff l, c.F ≤ c'.F ∧ ∀ c'' : Coeff l, c'.F ≤ c''.F → CurveOver H c''.F n := by
  intro E _ _ _ H l c n hn
  obtain ⟨F, _, hF⟩ := exists_curveOver H hn
  have := c.fin
  exact ⟨⟨c.F ⊔ F, inferInstance, fun τ a => le_sup_left (b := F) (c.conj τ a), le_sup_left (b := F) c.zeta_mem,
    c.le.trans le_sup_left⟩, le_sup_left, fun c'' h τ hτ => hF τ fun x hx => hτ x (h (le_sup_right (a := c.F) hx))⟩

end GlobalTheory.CurveField
end

section

noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GeometricValues

theorem eq_zero_of_forall_algClosed {K R : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] (x : R)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (φ : R →ₐ[K] Ω), φ x = 0) : x = 0 := by
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  let φ : R →ₐ[K] AlgebraicClosure (FractionRing (R ⧸ J)) :=
    (IsScalarTower.toAlgHom K (FractionRing (R ⧸ J)) (AlgebraicClosure (FractionRing (R ⧸ J)))).comp
      ((IsScalarTower.toAlgHom K (R ⧸ J) (FractionRing (R ⧸ J))).comp (Ideal.Quotient.mkₐ K J))
  have h0 := h _ φ
  have h1 : algebraMap (R ⧸ J) (FractionRing (R ⧸ J)) (Ideal.Quotient.mk J x) = 0 := by
    apply (algebraMap (FractionRing (R ⧸ J)) (AlgebraicClosure (FractionRing (R ⧸ J)))).injective
    rw [map_zero]
    exact h0
  have h2 : Ideal.Quotient.mk J x = 0 := by
    apply IsFractionRing.injective (R ⧸ J) (FractionRing (R ⧸ J))
    rw [map_zero]
    exact h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem ptsDetect_of {K : Type} [Field K] {ι : Type} [Fintype ι]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
    (hW : EvalWD pts mapR)
    (hB : ∀ (S : Type) [CommRing S] [Algebra K S] (T : Type) [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
      (y : pts S), ∃ z : pts T, mapR φ y z)
    (e : ι → ℕ) : PtsDetect pts mapR borR e := by
  intro g hg h
  funext p y
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  refine eq_zero_of_forall_algClosed (K := K) (g p y) ?_
  intro Ω _ _ _ φ
  obtain ⟨z, hz⟩ := hB p.R Ω φ y
  have hT : FromTest pts mapR z := ⟨p, φ, y, hz⟩
  have h0 := h Ω z
  unfold evalAt at h0
  rw [dite_eq_left hT] at h0
  rw [← h0]
  exact hW g hg.1 Ω p _ φ _ y _ z hz hT.choose_spec.choose_spec.choose_spec

end GeometricValues

theorem ptsDetect_framed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), PtsDetect (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (ex Dw a n) := by
  intro E _ _ _ H Dw l Xo c a n
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  exact GeometricValues.ptsDetect_of (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (fun t y y' => FrBor t y y') (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c S T φ y) (ex Dw a n)

end GlobalTheory.Frames
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory


open Moduli.LevelAction in
theorem levMove_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (_c : Coeff l), ∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') (gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La), 1 ≤ Dw.p + Dw.q → (∀ a, gM a - gM' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA a - gA' a)) → IsIso ρ → IsIso ρ' → IsLevMove ρ ν gM gA → IsLevMove ρ' ν' gM' gA' → (∃ g : Sim Dw, (∀ a, g.f l.M a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ a, Dw.ModN l.A (g.f l.A a - gA a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) → ρ = ρ' ∧ ν.φ = ν'.φ := by
  intro E _ _ _ H Dw l Xo _ ρ ρ' ν ν' gM gM' gA gA' hpq hM hA _ _ ⟨hs, e, eA⟩ ⟨hs', e', eA'⟩ ⟨g, hgM, hgA, hν⟩
  have hred : IsReduced Xo.X := by
    have := Xo.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
      (SmoothOfRelativeDimension.smooth Dw.dim _)).1
  obtain ⟨o, m, a₁, b₁⟩ := exists_obj_twist_by_similitude SimAlg.sim_group E H Dw l _ _ _ _ Xo.univ g hpq hν
  obtain ⟨n, hn⟩ := Moduli.LevelAction.exists_comp_sabMap m ν (Category.id_comp ρ)
  obtain ⟨n', hn'⟩ := Moduli.LevelAction.exists_comp_sabMap m ν' (Category.id_comp ρ')
  have c₁ : ∀ a, (o.eta a).left ≫ n.φ = ρ ≫ (Xo.univ.eta a).left := fun a => by
    rw [hn, ← Category.assoc, a₁, Moduli.LevelAction.eta_congr Xo.univ (hgM a), e]
  have c₂ : ∀ a, (o.etaA a).left ≫ n.φ = ρ ≫ (Xo.univ.etaA a).left := fun a => by
    rw [hn, ← Category.assoc, b₁, Moduli.LevelAction.etaA_congr Xo.univ (hgA a), eA]
  have d₁ : ∀ a, (o.eta a).left ≫ n'.φ = ρ' ≫ (Xo.univ.eta a).left := fun a => by
    rw [hn', ← Category.assoc, a₁, Moduli.LevelAction.eta_congr Xo.univ (hgM a), Moduli.LevelAction.eta_congr Xo.univ (hM a), e']
  have d₂ : ∀ a, (o.etaA a).left ≫ n'.φ = ρ' ≫ (Xo.univ.etaA a).left := fun a => by
    rw [hn', ← Category.assoc, b₁, Moduli.LevelAction.etaA_congr Xo.univ (hgA a), Moduli.LevelAction.etaA_congr Xo.univ (hA a), eA']
  obtain rfl : ρ = ρ' := (Xo.rep _ Xo.s hred o).unique ⟨hs, ⟨⟨n, c₁, c₂⟩⟩⟩ ⟨hs', ⟨⟨n', d₁, d₂⟩⟩⟩
  refine ⟨rfl, ?_⟩
  have h := obj_rigid_closed firstFiveLaws.1 E H Dw l _ _ _ _ _ _ _ _ Xo.univ o ρ (Or.inl hred) n n'
    fun a => ⟨_, c₁ a, d₁ a⟩
  have : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  rw [hn, hn'] at h
  exact (cancel_epi m.φ).1 h

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

namespace DefiniteData

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_std (x y : Fin r → E) :
    herm (1 : Matrix (Fin r) (Fin r) E) x y = ∑ a, x a * cc (y a) := by
  simp [herm, Matrix.one_apply]

theorem emb_herm_self (φ : E →+* ℂ) (x : Fin r → E) :
    φ (herm (1 : Matrix (Fin r) (Fin r) E) x x) = ((∑ a, ‖φ (x a)‖ ^ 2 : ℝ) : ℂ) := by

  rw [herm_std, map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, emb_cc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

def stdLat (E : Type) [Field E] [NumberField E] (r : ℕ) : Submodule (𝓞 E) (Fin r → E) :=
  LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin r))

omit [IsCMField E] in
theorem mem_stdLat (x : Fin r → E) : x ∈ stdLat E r ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · rintro ⟨y, rfl⟩ a
    exact (y a).isIntegral_coe
  · intro h
    exact ⟨fun a => ⟨x a, h a⟩, rfl⟩

omit [IsCMField E] in
theorem single_mem_stdLat (b : Fin r) : (Pi.single b 1 : Fin r → E) ∈ stdLat E r := by
  rw [mem_stdLat]
  intro a
  by_cases h : a = b
  · subst h; simpa using isIntegral_one
  · simpa [h] using isIntegral_zero

theorem stab_finite :
    {γ : GL (Fin r) E | IsUStab (1 : Matrix (Fin r) (Fin r) E) (stdLat E r) γ}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le (K := E) (A := ℂ) 1
  have hpi := Set.Finite.pi' (fun _ : Fin r => Set.Finite.pi' (fun _ : Fin r => hfin))
  refine Set.Finite.of_finite_image (hpi.subset ?_) ?_
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
  · rintro _ ⟨γ, ⟨hh, hl⟩, rfl⟩ a b
    have hv : ∀ i, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single b 1) i =
        (γ : Matrix (Fin r) (Fin r) E) i b := by
      intro i; simp
    refine ⟨?_, fun φ => ?_⟩
    · have := (mem_stdLat _).1 ((hl _).1 (single_mem_stdLat b)) a
      rwa [hv] at this
    · have h1 := congrArg φ (hh (Pi.single b 1) (Pi.single b 1))
      rw [emb_herm_self, emb_herm_self] at h1
      have h2 := Complex.ofReal_injective h1
      have h3 : ∑ i, ‖φ ((Pi.single b 1 : Fin r → E) i)‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro i _ hi; simp [hi]
        · simp
      rw [h3] at h2
      simp only [hv] at h2
      have h4 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2 ≤ 1 := by
        rw [← h2]
        exact Finset.single_le_sum (f := fun i => ‖φ ((γ : Matrix (Fin r) (Fin r) E) i b)‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ a)
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
  · intro γ _ δ _ h
    apply Units.ext
    ext a b
    exact congrFun (congrFun h a) b

theorem eq_zero_of_herm_self {x : Fin r → E}
    (h : herm (1 : Matrix (Fin r) (Fin r) E) x x = 0) : x = 0 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := emb_herm_self φ x
  rw [h, map_zero] at h1
  have h2 : ∑ a, ‖φ (x a)‖ ^ 2 = 0 := by exact_mod_cast h1.symm
  funext a
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 h2 a (Finset.mem_univ a)
  have h4 : φ (x a) = 0 := by simpa using h3
  exact (map_eq_zero_iff φ φ.injective).1 h4

theorem nonempty_data (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) :
    Nonempty (FD.Data E r) := by
  classical
  let X : FD.Data E 1 := inhab
  exact ⟨
  { Ψ := X.Ψ
    cmType := X.cmType
    Gm := 1
    Gm_herm := by
      intro a b
      by_cases h : a = b
      · subst h; simp [cc_one]
      · simp [h, Ne.symm h, cc_zero]
    Gm_det := by simp
    p0 := r
    p0_le := le_rfl
    signature := by
      intro τ
      refine ⟨1, by simp, ?_⟩
      ext a b
      by_cases h : a = b
      · subst h
        simp [gram, hermC, col, sgn, Matrix.one_apply, apply_ite]
      · simp [gram, hermC, col, sgn, Matrix.one_apply, apply_ite, h, Ne.symm h]
    Λ := stdLat E r
    Λ_fg := by
      unfold stdLat
      rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map _
    Λ_span := by
      rw [eq_top_iff]
      intro x _
      rw [pi_eq_sum_univ' x]
      exact Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdLat b))
    den := 1
    den_ne := one_ne_zero
    Λ_int := by
      intro x hx y hy
      rw [herm_std, show ((1 : 𝓞 E) : E) = 1 by simp, one_mul]
      exact IsIntegral.sum _ fun a _ =>
        ((mem_stdLat x).1 hx a).mul (isIntegral_cc ((mem_stdLat y).1 hy a))
    Γ := ⊥
    Γ_stab := by
      intro γ hγ
      rw [Subgroup.mem_bot] at hγ
      subst hγ
      simp [IsUStab]
    Γ_index := ⟨(stab_finite (E := E) (r := r)).toFinset, fun γ hγ =>
      ⟨γ, (Set.Finite.mem_toFinset _).2 hγ, by simp⟩⟩
    Γ_free := fun γ hγ _ _ _ _ _ => Subgroup.mem_bot.mp hγ
    χ := fun _ _ => 1
    χ_mul := by intros; simp
    χ_add := by intros; simp
    χ_fin := fun _ => ⟨1, one_pos, by intros; simp⟩
    ξ0 := X.ξ0
    ξ0_im := X.ξ0_im
    ξ0_ne := X.ξ0_ne
    κ0 := X.κ0
    κ0_xi := X.κ0_xi
    κ0_sign := X.κ0_sign
    m := 1
    m_pos := one_pos
    transv := by
      intro ξ _ hiso s _ _
      have hξ := eq_zero_of_herm_self hiso
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      ext a b
      simp [transvMat, hξ, Matrix.one_apply] }⟩

end DefiniteData

theorem exists_unf_nonempty_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), Nonempty U.Comp := by
  intro E _ _ _ H Dw l Xo c h σ
  obtain ⟨X⟩ := DefiniteData.nonempty_data E (Dw.p + Dw.q)
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws
    GlobalTheory.firstFiveLaws.2.1.secTwist E H Dw l Xo c h σ
  exact ⟨{ Comp := Unit, X := fun _ => X, un := fun _ _ => y }, ⟨()⟩⟩

end GlobalTheory
end
