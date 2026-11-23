module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle121
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle134
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle122
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle137
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle125
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle120
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle005
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle133
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle127
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle048
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle016
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle126
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isBlockDiag_one_add_single {N j : ℕ} {ca cb : Fin N} (hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s hrs
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
  have h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hrs hs.symm
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem not_sameOrbit_of_ptData : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t → ¬ SameOrbit (fstPt k₀ (RW.lift x x)) (sndPt k₀ (RW.lift x x)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hW x z₀ z₁ F h t hP hOrb
  obtain ⟨hF, hG, h0, h1, hbd, hdet, ht, hE0, hE1⟩ := hP
  obtain ⟨hb0, -, -, -⟩ := GlobalTheory.T.twisted_atlas_compatibility K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW x z₀ z₁ h0 h1
  obtain ⟨c, hc, hcz⟩ : SameOrbit z₁ z₀ := orbit_trans (orbit_trans h1 (orbit_symm hOrb)) (orbit_symm h0)
  have hz : ∀ q, z₁ q = c q.1 * z₀ q := fun q => congrFun hcz q

  have hbase : basePart M.blk z₁ = basePart M.blk z₀ := by
    funext q
    have e₀ : z₀ ⟨q.1.1, F.c q.1⟩ = 1 := (hE0 a).1 q.1
    have e₁ : z₁ ⟨q.1.1, F.c q.1⟩ = 1 := (hE1 a).1 q.1
    have hc1 : c q.1.1 = 1 := by
      have := hz ⟨q.1.1, F.c q.1⟩
      rw [e₀, e₁, mul_one] at this
      exact this.symm
    show z₁ ⟨q.1.1, q.2⟩ = z₀ ⟨q.1.1, q.2⟩
    rw [hz, show c (Sigma.fst (⟨q.1.1, q.2⟩ : Σ k, ι k)) = 1 from hc1, one_mul]
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    have hN := M.j_le
    have ha := a.2
    have hb' := b.2
    unfold lastCol at hca
    split_ifs at hca with hl <;> omega
  have hbd₁ : IsBlockDiag j (h * (1 + Matrix.single cb ca t)) := hbd.mul (isBlockDiag_one_add_single hs t)
  have hplk : ∀ m : ι k₀, plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ (h * (1 + Matrix.single cb ca t)) =
      c k₀ * plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ h := fun m => by
    have e₀ := (hE0 a).2 k₀ hk m
    have e₁ := (hE1 a).2 k₀ hk m
    rw [hbase] at e₁
    have e₂ := hz ⟨k₀, m⟩
    rw [e₁, e₀] at e₂
    exact e₂
  have hmin := Ind.minor_eq_of_plk M hb0 hF hG hk hbd₁ hbd hplk
  have hpl := GlobalTheory.T.elementary_twist_minor_scalar N j a b ca cb M.j_le hb hab hca hcb h 1 0 t (c k₀) hdet isBlockDiag_one
    Matrix.blockTriangular_one (fun I => by
      have e : (1 + Matrix.single cb ca (0 : ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by simp
      rw [e, Matrix.mul_one]
      exact hmin I)
  have h2 := hpl.2
  simp only [mul_zero, Matrix.one_apply_eq, mul_one, Finset.prod_const_one, one_mul] at h2
  exact ht h2.symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = pPhi M F keep v bl h ε w ∧ basePart M.blk z = bl (pB ε w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hctx w hw
  have hT := GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hctx w hw
  have hc2 := hctx
  unfold GlobalTheory.CompanionTheory.Ar.PB.PFl.IsPCtx at hc2
  obtain ⟨-, -, hframe, hchart, -⟩ := hc2
  unfold GlobalTheory.CompanionTheory.Ar.PB.WMan.IsBaseChart at hchart
  have hwV : pB ε w ∈ V := hw
  obtain ⟨hmem, hnorm, hgood, -⟩ := hchart.2.2.2.2 (pB ε w) hwV
  have hbase : basePart M.blk (GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w)) =
      bl (pB ε w) := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    unfold GlobalTheory.CompanionTheory.Ar.PB.basePart GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ
    split
    next hex => exact absurd hex (fun ⟨p, hp⟩ => hk p hp)
    next hex => rfl
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w), ?_, rfl, hbase⟩
  have hmain := (GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M).2.2 F hframe
    (GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w))
    (by rw [hbase]; exact hmem) (by rw [hbase]; exact hgood) (by rw [hbase]; exact hnorm)
  refine hmain.2 ⟨fun τ => pH keep h ε τ w, ?_⟩
  refine ⟨fun k => by rw [hbase]; exact hnorm k, fun τ => hT.1 τ, ?_⟩
  intro p k hp
  refine ⟨1, one_ne_zero, fun m => ?_⟩
  rw [one_mul, hbase]
  unfold GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ
  split
  next hex =>
    have hc : hex.choose = p := M.blk_inj _ _ k hex.choose_spec hp
    rw [hc]
  next hex => exact absurd ⟨p, hp⟩ hex

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial

theorem step_monomial : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (Φ : Type) [Field Φ] (y : K₀ ⊕ StepIx Ψ p q → Φ), (∀ k, y k ≠ 0) → ∀ (τ : Ψ) (i : Fin (p + q)), (∀ h1 : (i : ℕ) < p, ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (((i : ℕ) + 1) * m (.inl τ)) / y (.inr ⟨.inl τ, ⟨i, h1⟩⟩)) ∧ (∀ h1 : p ≤ (i : ℕ), ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (p * m (.inl τ) + ((i : ℕ) - p + 1) * m (.inr τ)) / ((if h0 : 0 < p then y (.inr ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩) else 1) * y (.inr ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩))) := by
  classical
  intro Ψ _ p q Ω _ _ n A K₀ _ J₀ _ x₀ m h Φ _ y hy τ i
  obtain ⟨hbase, hstep⟩ := GlobalTheory.T.model_dy_weights Ψ p q Ω n A K₀ J₀ x₀ m h τ i
  have hsplit : ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) =
      (∏ k, y (.inl k)) ^ (rkW i * m (.inl τ) + rkO i * m (.inr τ)) *
        ∏ t, y (.inr t) ^ (-((model A x₀ m h).dy (τ, i) (.inr t))) := by
    rw [Fintype.prod_sum_type, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hbase k, neg_neg, zpow_natCast]
  have hval : ∀ t : StepIx Ψ p q, y (.inr t) ^ (-((model A x₀ m h).dy (τ, i) (.inr t))) =
      if (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) then (y (.inr t))⁻¹
      else 1 := by
    intro t
    split_ifs with hc
    · rw [(hstep t).1 hc, _root_.zpow_neg, zpow_one]
    · rw [(hstep t).2 hc, neg_zero, zpow_zero]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hso : stepOf Ψ p q (τ, i) = ⟨.inl τ, ⟨i, h1⟩⟩ := by
      unfold stepOf
      exact dif_pos h1
    have hW : rkW i = (i : ℕ) + 1 := by unfold rkW; omega
    have hO : rkO i = 0 := by unfold rkO; omega
    rw [hsplit, hW, hO, zero_mul, add_zero, Fintype.prod_eq_single (stepOf Ψ p q (τ, i)), hval,
      if_pos (Or.inl rfl), hso, div_eq_mul_inv]
    intro t ht
    rw [hval, if_neg]
    rintro (h' | ⟨-, -, hp⟩)
    · exact ht h'
    · omega
  · have hso : stepOf Ψ p q (τ, i) = ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩ := by
      unfold stepOf
      exact dif_neg (not_lt.2 h1)
    have hW : rkW i = p := by unfold rkW; omega
    have hO : rkO i = (i : ℕ) - p + 1 := by unfold rkO; omega
    rw [hsplit, hW, hO]
    by_cases hp0 : 0 < p
    · rw [dif_pos hp0]
      have hne : stepOf Ψ p q (τ, i) ≠ ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩ := by
        rw [hso]
        intro he
        exact Sum.inr_ne_inl (congrArg Sigma.fst he)
      rw [Fintype.prod_eq_mul _ _ hne, hval, hval, if_pos (Or.inl rfl),
        if_pos (Or.inr ⟨rfl, show p - 1 + 1 = p by omega, h1⟩), hso]
      · rw [div_eq_mul_inv, mul_inv]
        ring
      · rintro x ⟨hx1, hx2⟩
        rw [hval, if_neg]
        rintro (h' | ⟨hs, hj, -⟩)
        · exact hx1 h'
        · apply hx2
          obtain ⟨s, j⟩ := x
          dsimp only at hs hj
          subst hs
          exact Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp; omega)))
    · rw [dif_neg hp0, one_mul, Fintype.prod_eq_single (stepOf Ψ p q (τ, i)), hval, if_pos (Or.inl rfl), hso,
        div_eq_mul_inv]
      intro t ht
      rw [hval, if_neg]
      rintro (h' | ⟨-, hj, -⟩)
      · exact ht h'
      · omega

end GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

theorem _root_.GlobalTheory.T.exists_component_in_chart_regular : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (tie : CoordTie ℤ ξ (seg y)) (Q : Ideal (MRing J))
    (hQ : Q.IsPrime) (hle : mCoordIdeal y ≤ Q) (c : ∀ k, J k)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ Q),
    ∃ P : Cpt ξ, InChart ξ (seg y) c P ∧ ∀ a ∈ regAt ξ P, RegAt y Q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

section Pure

theorem values_adapted {Ω Φ : Type} [Field Ω] [Field Φ] (i : Ω →+* Φ) (R : Subring Φ) {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) Ω) (T : Matrix (Fin r) (Fin r) Ω) (C₀ : Matrix (Fin r) (Fin n) Ω) (z : Ω)
    (u U Rm Rm' : Matrix (Fin r) (Fin r) Φ) (F : Matrix (Fin n) (Fin r) Φ)
    (hF : F = A.map i * u) (hu : u * U = T.map i * Rm) (hRm : ∀ a b, Rm a b ∈ R) (hRm' : ∀ a b, Rm' a b ∈ R)
    (hR : Rm * Rm' = 1) (hB : ∀ a b, i ((A * T) a b / z) ∈ R) (hC₀ : ∀ a b, i (C₀ a b) ∈ R)
    (hinv : ∀ a b, ∑ k, C₀ a k * ((A * T) k b / z) = if a = b then 1 else 0) :
    ∃ C : Matrix (Fin r) (Fin n) Φ, (∀ a b, (F * U) a b / i z ∈ R) ∧ (∀ a b, C a b ∈ R) ∧
      ∀ a b, ∑ k, C a k * ((F * U) k b / i z) = if a = b then 1 else 0 := by
  set B : Matrix (Fin n) (Fin r) Ω := Matrix.of fun a b => (A * T) a b / z with hBdef
  have hFU : F * U = (A * T).map i * Rm := by
    rw [hF, Matrix.mul_assoc, hu, ← Matrix.mul_assoc, Matrix.map_mul]
  have hval : ∀ a b, (F * U) a b / i z = (B.map i * Rm) a b := by
    intro a b
    rw [hFU, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.map_apply, hBdef, Matrix.of_apply, map_div₀]
    ring
  have hCB : C₀ * B = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hinv a b
  have hRm2 : Rm' * Rm = 1 := mul_eq_one_comm.1 hR
  refine ⟨Rm' * C₀.map i, fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [hval, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hB a k) (hRm k b)
  · rw [Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hRm' a k) (hC₀ k b)
  · have h1 : (Rm' * C₀.map i) * (B.map i * Rm) = 1 := by
      have h2 : C₀.map i * B.map i = 1 := by
        rw [← Matrix.map_mul, hCB]
        exact Matrix.map_one _ (map_zero i) (map_one i)
      calc (Rm' * C₀.map i) * (B.map i * Rm) = Rm' * (C₀.map i * B.map i) * Rm := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, hRm2]
    have h3 := congrFun (congrFun h1 a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h3
    simpa only [hval] using h3

theorem colFrame_semi {Ω Φ E F : Type} [Field Ω] [Field Φ] [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Φ F]
    {i : Ω →+* Φ} {j : E →+ F} (hj : ∀ (a : Ω) (e : E), j (a • e) = i a • j e) {r : ℕ} (e : Fin r → E)
    (T : Matrix (Fin r) (Fin r) Ω) :
    (fun k => j (colFrame e T k)) = colFrame (fun a => j (e a)) (T.map i) := by
  funext k

  simp only [colFrame, map_sum, hj, Matrix.map_apply]

theorem isFrameAt_of_map {X : Scheme.{0}} {Ω E E' : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup E']
    [Module Ω E'] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (f : E →ₗ[Ω] E') (hf : Function.Injective f) {r : ℕ}
    (b : Fin r → E) (p : Cpt ξ) (h : (L.map f).IsFrameAt (fun k => f (b k)) p) : L.IsFrameAt b p := by
  refine ⟨LinearIndependent.of_comp f h.1, ?_⟩
  have h2 : (L p).map (f.restrictScalars (regAt ξ p)) =
      (Submodule.span (regAt ξ p) (Set.range b)).map (f.restrictScalars (regAt ξ p)) := by
    have : (Set.range fun k => f (b k)) = (f.restrictScalars (regAt ξ p)) '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [Submodule.map_span, ← this]
    exact h.2
  exact Submodule.map_injective_of_injective (f := f.restrictScalars (regAt ξ p)) hf h2

end Pure

section Main

theorem adapted_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (rk (CMType H) D.p D.q (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (n (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ))) = if a = b then 1 else 0) ∧ ∀ l, ((𝔐'.V (.inl τ)).gr (Fl.b (.inl τ)) l).IsGenAt p' (U l l) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF 𝔐' pr j Fl hO hV hC τ p' hp c₁ hch
  obtain ⟨T, C₀, -, hfr, hreg, hC₀r, hinv⟩ := GlobalTheory.T.exists_local_twist_trivialization 𝔐.X Ω 𝔐.ξ (EE 𝔐) ((k : K₀) → J₀ k) (seg x₀)
    (LL 𝔐 (.inl τ)) (m (.inl τ)) (rk (CMType H) D.p D.q (.inl τ)) (n (.inl τ)) (VV 𝔐 (.inl τ)) (φ (.inl τ))
    (cc 𝔐 bW bO (.inl τ)) (hF.2.2.1 _) (hF.1 _) (hF.2.1 _).1 (hF.2.1 _).2 ⟨pr p'.1, hp⟩ c₁ hch
  let e : Fin (rk (CMType H) D.p D.q (.inl τ)) → 𝔐.Li := fun a => (bW τ a : 𝔐.Li)
  have hfrV : (𝔐.V (.inl τ)).IsFrameAt (colFrame e T) ⟨pr p'.1, hp⟩ := by
    refine isFrameAt_of_map _ (inW 𝔐) (GenBases.inW_injective 𝔐) _ _ ?_
    have h : (fun k => inW 𝔐 (colFrame e T k)) = colFrame (cc 𝔐 bW bO (.inl τ)) T := by
      funext k

      simp only [colFrame, map_sum, map_smul]
      rfl
    rw [h]
    exact hfr
  have hE := hO.2.2.2.1
  have hpull := FlagPull.pull_isFrameAt hO.1 hE p' hp hfrV
  rw [← hV (.inl τ), colFrame_semi hE.1] at hpull
  have he : LinearIndependent Ω e :=
    (bW τ).linearIndependent.map' (𝔐.Vgen (.inl τ)).subtype (Submodule.ker_subtype _)
  have hw := hE.2 _ e he
  have hb : Fl.b (.inl τ) = colFrame (fun a => j (e a)) (genU Ω (rk (CMType H) D.p D.q) (.inl τ)) := by
    funext k
    rw [hC.1 τ k, DetG.wBlock_gMat]
    rfl
  have hflag := Fl.sub (.inl τ)
  rw [hb] at hflag
  obtain ⟨U, Rm, Rm', hU, hRm, hRm', hR, hu, hgen⟩ := GlobalTheory.T.exists_triangular_regular_frame_change 𝔐'.X _ 𝔐'.ξ 𝔐'.Li (𝔐'.V (.inl τ))
    (rk (CMType H) D.p D.q (.inl τ)) (fun a => j (e a)) _ (genU Ω (rk (CMType H) D.p D.q) (.inl τ)) p' hw
    (by rw [DetG.det_genU]; exact isUnit_one) hpull hflag
  obtain ⟨C, h1, h2, h3⟩ := values_adapted (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) (regAt 𝔐'.ξ p')
    (aOf 𝔐 bW bO φ (.inl τ)) T C₀ (seg x₀ c₁ ^ m (.inl τ)) _ U Rm Rm' (fMat (aOf 𝔐 bW bO φ) (.inl τ)) rfl hu hRm hRm' hR
    (fun a b => LatModel.dominates_regAt hO.1 p' hp (hreg a b))
    (fun a b => LatModel.dominates_regAt hO.1 p' hp (hC₀r a b)) hinv
  refine ⟨U, C, hU, h1, h2, h3, fun l => ?_⟩
  rw [hb]
  exact hgen l

end Main

end GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

def agreeRate (t : ℝ) : ℝ := Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t)

theorem agree_exp_le_sq {s : ℝ} (hs : 0 < s) : Real.exp (-(s ^ 2)⁻¹) ≤ s ^ 2 := by
  have hx : 0 < (s ^ 2)⁻¹ := by positivity
  have h1 : (s ^ 2)⁻¹ ≤ Real.exp ((s ^ 2)⁻¹) := by linarith [Real.add_one_le_exp ((s ^ 2)⁻¹)]
  rw [Real.exp_neg]
  calc (Real.exp (s ^ 2)⁻¹)⁻¹ ≤ ((s ^ 2)⁻¹)⁻¹ := inv_anti₀ hx h1
    _ = s ^ 2 := inv_inv _

theorem agreeRate_nonneg (s : ℝ) (hs : 0 < s) : 0 ≤ agreeRate (Real.exp (-(s ^ 2)⁻¹)) := by
  unfold agreeRate
  rw [limRate_log_inv_exp]
  have : 0 < (s ^ 2)⁻¹ := by positivity
  positivity

theorem agree_cauchy (hI : Inputs) (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (h0 : 0 < S.t₀) :
    ∃ C' t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ S.t₀ ∧
    ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P)
      (w : Fin (D + 1) → σ) (t t' : ℝ), 0 < t' → t' ≤ t → t ≤ t₁ →
      |Re.num II t w - Re.num II t' w| ≤ ((D : ℝ) + 1) * (|C'| * |agreeRate t|) := by
  obtain ⟨C', t₁, ht₁, ht₁0, hb⟩ := GlobalTheory.T.monge_ampere_regularization_log_log_bound hI.convergenceRate D σ S h0
  refine ⟨C', t₁, ht₁, ht₁0, ?_⟩
  intro II hII K _ ι _ P Re w t t' ht' htt ht
  have ht0 : 0 < t := lt_of_lt_of_le ht' htt
  rw [GlobalTheory.T.intersection_difference_telescoping_integral hI II hII K ι D σ S P Re t t' w ht0 (ht.trans ht₁0) ht' ((htt.trans ht).trans ht₁0)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hr : ∀ r : Fin (D + 1), |mInt S.A (fun i => S.potT (w (r.succAbove i)) (if r.succAbove i < r then t else t'))
      (fun x => S.phT (w r) t x - S.phT (w r) t' x)| ≤ |C'| * |agreeRate t| := by
    intro r
    have := hb t t' ht' htt ht (w r) (fun i => w (r.succAbove i)) (fun i => decide (r.succAbove i < r))
    simp only [decide_eq_true_eq] at this
    refine this.trans ?_
    rw [mul_div_assoc]
    exact (le_abs_self _).trans (by rw [abs_mul]; rfl)
  refine (Finset.sum_le_sum fun r _ => hr r).trans ?_
  simp

theorem agreementPos : AgreementPos := by
  intro hI D σ _ S abelian₂ h0
  obtain ⟨C', t₁, ht₁, ht₁0, hc⟩ := agree_cauchy hI D σ S h0
  obtain ⟨hlim, hrate, -, -⟩ := limRate
  refine ⟨|abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * 4)), min 1 t₁, lt_min one_pos ht₁, ?_⟩
  intro II hII K _ ι _ P Re
  have hδ : Tendsto (fun t => ((D : ℝ) + 1) * (|C'| * |agreeRate t|)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t => |agreeRate t|) (𝓝[>] 0) (𝓝 0) := by
      have h2 := hlim.abs
      rw [abs_zero] at h2
      exact h2
    simpa using (this.const_mul |C'|).const_mul ((D : ℝ) + 1)
  have hL := fun w => tendsto_limUnder_of_cauchy_rate (fun t => Re.num II t w)
    (fun t => ((D : ℝ) + 1) * (|C'| * |agreeRate t|)) t₁ ht₁ hδ (hc II hII K ι P Re w)
  refine ⟨fun w => (hL w).1, fun s hs hss => ?_⟩
  have hs1 : s ≤ 1 := hss.trans (min_le_left _ _)
  have hst : s ≤ t₁ := hss.trans (min_le_right _ _)
  have hT : Real.exp (-(s ^ 2)⁻¹) ≤ t₁ := by
    refine (agree_exp_le_sq hs).trans ?_
    nlinarith
  refine ⟨hT.trans ht₁0, fun c hcL => ?_⟩
  set t := Real.exp (-(s ^ 2)⁻¹)
  have hM : ∀ w, |Re.num II t w - Re.limNum II w| ≤ ((D : ℝ) + 1) * (|C'| * |agreeRate t|) :=
    fun w => (hL w).2 t (Real.exp_pos _) hT
  have hb := (formPoly_sub_bound σ (D + 1) (Re.num II t) (Re.limNum II) _ hM).2 c
  have hr : |agreeRate t| ≤ 4 * s := by
    rw [abs_of_nonneg (agreeRate_nonneg s hs)]
    exact hrate s hs hs1
  have hsum : (∑ a, |c a|) ^ (D + 1) ≤ |abelian₂| ^ (D + 1) :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hcL.trans (le_abs_self _)) _
  have hD : (0 : ℝ) ≤ (D : ℝ) + 1 := by positivity
  calc |eval c (Re.FT II t) - eval c (Re.PB II)|
      ≤ (∑ a, |c a|) ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * |agreeRate t|)) := hb
    _ ≤ |abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * (4 * s))) := by
      gcongr
    _ = |abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * 4)) * s := by ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flagHeight_holds : FlagHeight := PositivityTheory.Xgp.t_top_flh

end GlobalTheory.CompanionTheory.Ar.PB
end
