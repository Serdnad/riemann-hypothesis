module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle062
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle006
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle095
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.Divisibility.Numbers

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharValue

def ballIdeal {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) (t : NNReal) (ht : 0 < t) : Ideal O where
  carrier := {y | v (algebraMap O C y) < t}
  zero_mem' := by simpa using ht
  add_mem' := by
    intro a b ha hb
    show v (algebraMap O C (a + b)) < t
    rw [map_add (f := _)]
    exact v.map_add_lt ha hb
  smul_mem' := by
    intro c a ha
    show v (algebraMap O C (c * a)) < t
    rw [map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one c)) ha

def letterEquiv (Ty : Type) (r : Ty → ℕ) (n : ℕ) : (Σ τ : Ty, Fin (r τ)) × Fin n ≃ Letter Ty r n where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun l := (⟨l.1, l.2.1⟩, l.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem dAct_mulVec {R : Type} [CommRing R] {d : ℕ} {OE : Type} [CommRing OE] [StarRing OE] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d OE) (a : OE) (u : Fin d → R) (s : R)
    (hu : (_root_.ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (B.A.act a)).mulVec u = s • u) :
    (TB.dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k s • (fun i => algebraMap R k (u i)) := by
  funext i
  have h := congrArg (algebraMap R k) (congrFun hu i)

  simp only [Matrix.mulVec, dotProduct, _root_.ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart, Matrix.of_apply, map_sum, map_mul, Pi.smul_apply,
  smul_eq_mul] at h
  simp only [Matrix.mulVec, dotProduct, TB.dAct, FB.actK, MvPowerSeries.coeff_map, Pi.smul_apply, smul_eq_mul]
  exact h

theorem map_boxSer {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {n d : ℕ} (g : Fin n → PS R 1 d) :
    MvPowerSeries.map φ (PowGerm.boxSer g) = PowGerm.boxSer (fun b => MvPowerSeries.map φ (g b)) := by
  unfold PowGerm.boxSer
  rw [map_prod]
  exact Finset.prod_congr rfl fun b _ => (MvPowerSeries.rename_map _ φ (g b)).symm

theorem exists_germ_valuation_eq : ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (B : FB O d OE) (h : PS C 2 d), B.IsCanonGauge C h → ∀ (w0 : OE) (k n : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) [Fintype (Letter Ty r n)] (σ : Ty → (OE →+* O)) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → O), (∀ ℓ a, (_root_.ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (B.A.act a)).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ τ, ∃ a0, IsUnit (σ τ a0 - σ τ (star a0))) → (∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧ ∀ τ, ∃ a : OE, star a * a = (N : OE) ∧ v (algebraMap O C (σ τ a - 1)) < v (algebraMap O C x)) → ∀ (ty : Fin n → Ty) (P : MvPolynomial (Letter Ty r n) O), (∀ mo ∈ P.support, ∀ ℓ, mo ℓ ≠ 0 → ℓ.1 = ty ℓ.2.2) → ∀ χ : Fin n → PS O 1 d, (∀ b, IsCh B.G.F (χ b)) → MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P ≠ 0 → ∃ f : PS O n d, v (nabValN B C h w0 k (MvPowerSeries.map (algebraMap O C) f) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun (ℓ : Letter Ty r n) i => algebraMap O C (u ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map (algebraMap O C) P)) = v (algebraMap O C (MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P)) := by
  intro C _ _ v O _ _ hv d OE _ _ B h hg w0 k n Ty _ r _ σ u hu h0 hN ty P hP χ hχ hx
  classical
  obtain ⟨P', rfl⟩ : ∃ P', P = MvPolynomial.rename (letterEquiv Ty r n) P' :=
    ⟨MvPolynomial.rename (letterEquiv Ty r n).symm P, by simp [MvPolynomial.rename_rename]⟩
  rw [MvPolynomial.eval_rename] at hx ⊢
  set y : (Σ τ : Ty, Fin (r τ)) × Fin n → O :=
    (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) ∘ (letterEquiv Ty r n) with hy
  set x : O := MvPolynomial.eval y P' with hxdef
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hx0 : 0 < v (algebraMap O C x) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact fun e => hx (hinj (by rw [e, map_zero]))
  obtain ⟨N, hNlt, ha⟩ := hN x hx
  choose a ha1 ha2 using ha
  have hh : MvPowerSeries.constantCoeff h = 0 := by
    have := congrArg MvPowerSeries.constantCoeff hg.ax0
    rwa [TB.WickVanishing.gt_const_ev_eq _ (TB.WickVanishing.pair_points_zero_constant TB.WickVanishing.gp_zero₂ (TB.WickVanishing.gp_pt 0)), map_zero] at this
  obtain ⟨g, ρ, hρ, hsum⟩ := GlobalTheory.T.covariantDerivative_value_character_germs O d OE C B h hg hinj w0 N k n (ballIdeal hv _ hx0)
    (by show v (algebraMap O C (N : O)) < _; rwa [map_natCast]) (fun b => a (ty b)) (fun _ => 1)
    (fun b => by rw [ha1, mul_one]) (Σ τ : Ty, Fin (r τ)) u (fun b => {l | l.1 = ty b})
    (fun b l => σ l.1 (a (ty b)))
    (fun b l hl => by
      have hl' : l.1 = ty b := hl
      have h2 : v (algebraMap O C (σ l.1 (a (ty b)) - 1)) < v (algebraMap O C x) := by
        rw [hl']; exact ha2 _
      refine ⟨h2, ?_, dAct_mulVec C B _ _ _ (hu l _)⟩
      apply hv.isUnit_of_one'
      have h3 := v.map_one_add_of_lt (lt_of_lt_of_le h2 (hv.map_le_one x))
      rwa [map_sub, map_one, add_sub_cancel] at h3)
    (fun b l hl l' hl' => by
      have e1 : l.1 = ty b := hl
      have e2 : l'.1 = ty b := hl'
      obtain ⟨a0, ha0⟩ := h0 (ty b)
      exact GlobalTheory.T.canonicalGauge_eigenvector_pairing_integral O d OE C B h hg (σ (ty b)) a0 ha0 (u l) (u l') (fun c => e1 ▸ hu l c)
        (fun c => e2 ▸ hu l' c) _)
    χ y (fun b => (hχ b).1)
    (fun b l _ => GlobalTheory.MultiplicativeSeries.main O d B.G (χ b) (hχ b).2 (u l))
    P' (fun mo hmo l b hne => by
      have hmem : Finsupp.mapDomain (letterEquiv Ty r n) mo ∈
          (MvPolynomial.rename (letterEquiv Ty r n) P').support := by
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_rename_mapDomain _ (letterEquiv Ty r n).injective]
        exact MvPolynomial.mem_support_iff.1 hmo
      exact hP _ hmem (letterEquiv Ty r n (l, b))
        (by rwa [Finsupp.mapDomain_apply_of_injective (letterEquiv Ty r n).injective]))
  refine ⟨PowGerm.boxSer g, ?_⟩
  rw [map_boxSer, MvPolynomial.map_rename,
    GlobalTheory.nabValN_boxSer O d OE B C h w0 hh k n _ (Σ τ : Ty, Fin (r τ)) (Letter Ty r n) (letterEquiv Ty r n) _
      (fun l i => algebraMap O C (u l i)) _ (fun _ => rfl) (fun _ => rfl),
    MvPolynomial.support_map_of_injective _ hinj]
  simp only [MvPolynomial.coeff_map]
  rw [hsum, map_add (f := _)]
  exact v.map_add_eq_of_lt_left hρ

end GlobalTheory.CharValue
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_cayley_side_bound : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (Q : Mx k r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ g ∈ GG k r, ∀ (a : Fin r) (w : R.smSub), (lenA k r z g a.succ / lenA k r z g a.castSucc) ^ 2 * ‖l (R.σ g w)‖ ^ 2 ≤ ∑ c, ∑ e, ‖l (R.σ g (E c e w))‖ ^ 2 := by
  first | exact @GlobalTheory.MomentPointwise.pointwise | exact GlobalTheory.MomentPointwise.pointwise | (intros; apply GlobalTheory.MomentPointwise.pointwise <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace OverSquare

open FrameLift OverMove

theorem rel_square {A A₂ Y Y' Y₂ Y₂' : Scheme.{0}} {L : LB A} {L₂ : LB A₂} (hL : L.IsLB) (hL₂ : L₂.IsLB)
    {φ φ' : A₂ ⟶ A} {ν : A ⟶ A} {ν₂ : A₂ ⟶ A₂} (hφ : ν₂ ≫ φ' = φ ≫ ν)
    {w₀ : LB.Iso L₂ (L.pull φ)} {w' : LB.Iso L₂ (L.pull φ')} {w : LB.Iso L (L.pull ν)} {w₂ : LB.Iso L₂ (L₂.pull ν₂)}
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ A₂) (z : Z) i k j l, ν (φ (f z)) ∈ L.U i → φ (f z) ∈ L.U k →
      ν₂ (f z) ∈ L₂.U j → f z ∈ L₂.U l →
      gw w (f ≫ φ) z i k * gw w₀ f z k l = gw w' (f ≫ ν₂) z i j * gw w₂ f z j l)
    {q : Y ⟶ A} {q' : Y' ⟶ A} {q₂ : Y₂ ⟶ A₂} {q₂' : Y₂' ⟶ A₂} {p : Y₂ ⟶ Y} {p' : Y₂' ⟶ Y'} {pm : Y ⟶ Y'}
    {pm₂ : Y₂ ⟶ Y₂'} {σ : Y₂' ⟶ Y₂} (hσ : σ ≫ pm₂ = 𝟙 _) (hp : p ≫ q = q₂ ≫ φ) (h₂ : pm₂ ≫ q₂' = q₂ ≫ ν₂)
    (sq : pm₂ ≫ p' = p ≫ pm) {s : LB.Sec (LOne L q)} {s' : LB.Sec (LOne L q')} {s₂ : LB.Sec (LOne L₂ q₂)}
    {s₂' : LB.Sec (LOne L₂ q₂')} (H₀ : Rel w₀ p s₂ s) (H : Rel w pm s s') (H₂ : Rel w₂ pm₂ s₂ s₂') :
    Rel w' p' s₂' s' := by
  intro Z r z i j hi hj
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : Z ⟶ Y₂, r = r₀ ≫ pm₂ := ⟨r ≫ σ, by rw [Category.assoc, hσ, Category.comp_id]⟩
  obtain ⟨k, hk⟩ := exists_chart hL (φ (q₂ (r₀ z)))
  obtain ⟨l, hl⟩ := exists_chart hL₂ (q₂ (r₀ z))
  have e₂ : q₂' (pm₂ (r₀ z)) = ν₂ (q₂ (r₀ z)) := pt_eq h₂ (r₀ z)
  have e₁ : q (p (r₀ z)) = φ (q₂ (r₀ z)) := pt_eq hp (r₀ z)
  have e₀ : φ' (ν₂ (q₂ (r₀ z))) = ν (φ (q₂ (r₀ z))) := pt_eq hφ (q₂ (r₀ z))
  have hj' : ν₂ (q₂ (r₀ z)) ∈ L₂.U j := e₂ ▸ (show q₂' (pm₂ (r₀ z)) ∈ L₂.U j from hj)
  have hi' : ν (φ (q₂ (r₀ z))) ∈ L.U i := by
    have : φ' (q₂' (pm₂ (r₀ z))) ∈ L.U i := hi
    rwa [e₂, e₀] at this
  have a := H Z (r₀ ≫ p) z i k (by show ν (q (p (r₀ z))) ∈ _; rw [e₁]; exact hi')
    (by show q (p (r₀ z)) ∈ _; rw [e₁]; exact hk)
  have b := H₀ Z r₀ z k l hk hl
  have c := H₂ Z r₀ z j l hj' hl
  have e := hw Z (r₀ ≫ q₂) z i k j l hi' hk hj' hl
  rw [Category.assoc r₀ pm₂ p', sq, ← Category.assoc r₀ p pm, a, b, c, ← _root_.mul_assoc, ← _root_.mul_assoc,
    ← Units.val_mul, ← Units.val_mul, Category.assoc r₀ p q, hp, ← Category.assoc r₀ q₂ φ, e,
    Category.assoc r₀ pm₂ q₂', h₂, Category.assoc r₀ q₂ ν₂]

theorem gw_square {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S S₂ : Scheme.{0}} {t : SAB H S} {t₂ : SAB H S₂} {r r' : S₂ ⟶ S} {ρ : S ⟶ S} {ρ₂ : S₂ ⟶ S₂}
    (hu : Function.Surjective t₂.G.hom.appTop.hom)
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t t ρ) (ν₂ : SABMap t₂ t₂ ρ₂)
    (hr : ρ₂ ≫ r' = r ≫ ρ) (hφ : ν₂.φ ≫ m'.φ = m.φ ≫ ν.φ)
    {w₀ : LB.Iso t₂.PP.L (t.PP.L.pull m.φ)} {w' : LB.Iso t₂.PP.L (t.PP.L.pull m'.φ)}
    {w : LB.Iso t.PP.L (t.PP.L.pull ν.φ)} {w₂ : LB.Iso t₂.PP.L (t₂.PP.L.pull ν₂.φ)}
    (h₀ : OverMove.RigIso m w₀) (h' : OverMove.RigIso m' w') (h : OverMove.RigIso ν w) (h₂ : OverMove.RigIso ν₂ w₂)
    (Z : Scheme.{0}) (f : Z ⟶ t₂.G.left) (z : Z) (i k : t.PP.L.ι) (j l : t₂.PP.L.ι)
    (hi : ν.φ (m.φ (f z)) ∈ t.PP.L.U i) (hk : m.φ (f z) ∈ t.PP.L.U k) (hj : ν₂.φ (f z) ∈ t₂.PP.L.U j)
    (hl : f z ∈ t₂.PP.L.U l) :
    gw w (f ≫ m.φ) z i k * gw w₀ f z k l = gw w' (f ≫ ν₂.φ) z i j * gw w₂ f z j l := by
  obtain ⟨a, Ta⟩ := exists_comp t.PP.isLB w w₀ h.1 h₀.1 t.PP.isLB t₂.PP.isLB
  obtain ⟨b, Tb⟩ := exists_comp t₂.PP.isLB w' w₂ h'.1 h₂.1 t.PP.isLB t₂.PP.isLB
  have ga := Ta.pgen_comp t.PP.isLB h.1 h₀.1
  have ra := Ta.pmaps_comp t.PP.isLB (fun _ => m.cm.e_comm) h.2 h₀.2
  have gb := Tb.pgen_comp t₂.PP.isLB h'.1 h₂.1
  have rb := Tb.pmaps_comp t₂.PP.isLB (fun _ => ν₂.cm.e_comm) h'.2 h₂.2
  have e := gw_eq_of_pmaps (S := S₂) (S₀ := S) t.PP.isLB t₂.PP.isLB t₂.G.hom (eSec t₂.G) (Over.w η[t₂.G]) hu
    hφ.symm ga gb (h₁ := m.cm.e ≫ ν.cm.e) (h₂ := ν₂.cm.e ≫ m'.cm.e)
    (by rw [m.base, m'.base, ν.base, ν₂.base]; exact hr.symm) ra rb f z i l
  have hi' : m'.φ (ν₂.φ (f z)) ∈ t.PP.L.U i :=
    (congrArg (· ∈ t.PP.L.U i) (pt_eq hφ (f z))).mpr hi
  exact (Ta Z f z i k l hi hk hl).symm.trans (e.trans (Tb Z f z i j l hi' hj hl))

end OverSquare


open FrameLift OverMove OverSquare in
theorem frOver_of_square_of_frMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂ ≫ r' = d.r ≫ ρ → ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrMove ρ ν y y' → FrMove ρ₂ ν₂ y₂ y₂' → FrOver { d with r := r', m := m' } y₂' y' := by
  intro E _ _ _ H Dw l Xo c n d ρ ν ρ₂ ν₂ r' m' hr hφ S _ _ _ y y' y₂ y₂' h hy hy₂
  obtain ⟨e, hu, w₀, p, hw₀, p₁, p₂, H₀⟩ := (frOver_iff d _ _).1 h
  obtain ⟨ex, eu, pm, w, a₁, a₂, hw, H₁⟩ := MoveCalc.frMove_iff_carry.1 hy
  obtain ⟨ex₂, eu₂, pm₂, w₂, b₁, b₂, hw₂, H₂⟩ := MoveCalc.frMove_iff_carry.1 hy₂
  obtain ⟨w', g', r₁', -⟩ := m'.lin
  have e' : y₂'.x ≫ r' = y'.x := by rw [ex₂, ex, Category.assoc, hr, ← Category.assoc, e]
  obtain ⟨p', -, p₁', p₂', -⟩ := exists_pm_iso m' e'
  obtain ⟨σ, hσ⟩ := MoveCalc.exists_section ν₂ ex₂ b₁ b₂
  have sq : pm₂ ≫ p' = p ≫ pm := by
    refine pm_ext ?_ ?_
    · rw [Category.assoc, p₁', ← Category.assoc, b₂, Category.assoc, hφ, Category.assoc, a₂, ← Category.assoc p, p₁,
        Category.assoc]
    · rw [Category.assoc, p₂', b₁, Category.assoc, a₁, p₂]
  have hs : Function.Surjective d.Xo₂.univ.t.G.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _
    ⟨d.Xo₂.univ.t.semi.comm, d.Xo₂.univ.t.semi.smooth, d.Xo₂.univ.proper, d.Xo₂.univ.t.semi.geomConnected⟩).2
  refine (frOver_iff { d with r := r', m := m' } y₂' y').2 ⟨e', fun τ i => ?_, w', p', ⟨g', r₁'⟩, p₁', p₂', ?_⟩
  · show y₂'.u τ i ≫ m'.φ = y'.u τ i
    rw [eu₂, eu, Category.assoc, hφ, ← Category.assoc, hu]
  · exact rel_square Xo.univ.t.PP.isLB d.Xo₂.univ.t.PP.isLB hφ
      (gw_square hs d.m m' ν ν₂ hr hφ (rigIso_of d.m hw₀.1 hw₀.2) (rigIso_of m' g' r₁') (rigIso_of ν hw.1 hw.2.1)
        (rigIso_of ν₂ hw₂.1 hw₂.2.1)) hσ p₁ b₂ sq H₀ H₁ H₂

end GlobalTheory
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselSubgroup_parameter_measurePreserving : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → (∀ h₀ ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n₀ ∈ Formalism.QuantumDeterminants.Nset k r, MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 * h₀ : Mx k r) i j), (fun i j => (h₀⁻¹ * Matrix.of p.2 * h₀ * n₀ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (h₀ * Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * n₀ * Matrix.of p.1 * Matrix.of p.2 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN)) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => (Matrix.of p.1 : Mx k r) i j), (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ MeasurePreserving (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (μW.prod μN) (μW.prod μN) ∧ ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  first | exact @GlobalTheory.sParam_measurePreserving | exact GlobalTheory.sParam_measurePreserving | (intros; apply GlobalTheory.sParam_measurePreserving <;> assumption)
end

section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem _root_.GlobalTheory.T.reducedWignerCoefficient_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + (n : ℂ))).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wM L M l : ℂ) • v := by
  first | exact @GlobalTheory.reducedWigner_lowering | exact GlobalTheory.reducedWigner_lowering | (intros; apply GlobalTheory.reducedWigner_lowering <;> assumption)
end

section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem exists_linearEquiv_of_irreducible_capelli :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [AddCommGroup V₂]
      [Module ℂ V₂] [FiniteDimensional ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
      (E₂ : Fin n → Fin n → Module.End ℂ V₂) (m : Fin n → ℂ), GlRel E₁ → GlRel E₂ → Irr E₁ → Irr E₂ →
      (∀ w v, qdet E₁ w v = cpol m w • v) → (∀ w v, qdet E₂ w v = cpol m w • v) →
      ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ _ V₂ _ _ _ n E₁ E₂ m g₁ g₂ i₁ i₂ c₁ c₂
  haveI := i₁.1
  haveI := i₂.1
  obtain ⟨ν₁, v₁, -, hv₁, hw₁, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V₁ n E₁ g₁ ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  obtain ⟨ν₂, v₂, -, hv₂, hw₂, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V₂ n E₂ g₂ ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have p₁ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) g₁ (mem_CapSp.2 fun w => c₁ w v₁) hv₁ hw₁
  have p₂ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) g₂ (mem_CapSp.2 fun w => c₂ w v₂) hv₂ hw₂
  have s₁ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift (Formalism.FourierDecayAlt.P.singular_dominant V₁ n E₁ ν₁ v₁ g₁ hw₁ hv₁)
  have s₂ := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift (Formalism.FourierDecayAlt.P.singular_dominant V₂ n E₂ ν₂ v₂ g₂ hw₂ hv₂)
  have h := (Formalism.FourierDecayAlt.P.separating_polynomials n _ _ (fun w => (p₁ w).symm.trans (p₂ w)) s₂).2 s₁
  have hν : ν₁ = ν₂ := by
    funext j
    exact sub_left_injective (congrFun h j)
  subst hν
  exact exists_linearEquiv_of_irreducible_isHW V₁ V₂ n E₁ E₂ ν₁ v₁ v₂ g₁ g₂ i₁.2 i₂.2 hw₁ hw₂ hv₁ hv₂

end GlobalTheory
end

section

open Matrix

noncomputable section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section aux

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma deriv_smul_const_vec (φ : ℝ → ℂ) (v : E) (t : ℝ) :
    deriv (fun s => φ s • v) t = deriv φ t • v := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases hφ : DifferentiableAt ℝ φ t
  · exact deriv_smul_const hφ v
  · have hn : ¬ DifferentiableAt ℝ (fun s => φ s • v) t := by
      intro h
      obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)
      apply hφ
      have hv' : ℓ v ≠ 0 := by rw [hℓ]; simpa using hv
      have h2 := (((ℓ.restrictScalars ℝ).differentiableAt).comp t h).const_mul (ℓ v)⁻¹
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show φ s = (ℓ v)⁻¹ * ℓ (φ s • v)
      rw [map_smul, smul_eq_mul, mul_comm (φ s), ← mul_assoc, inv_mul_cancel₀ hv', one_mul]
    rw [deriv_zero_of_not_differentiableAt hφ, deriv_zero_of_not_differentiableAt hn, zero_smul]

private lemma Dx_smul_const (x : Bool × B.Mat k r) (f : B.Mat k r → ℂ) (v : E) :
    Dx x (fun g => f g • v) = fun g => Dx x f g • v := by
  funext g
  unfold Dx
  split_ifs
  · exact deriv_smul_const_vec _ v 0
  · exact deriv_smul_const_vec _ v 0

private lemma Dw_smul_const (w : List (Bool × B.Mat k r)) (f : B.Mat k r → ℂ) (v : E) :
    Dw w (fun g => f g • v) = fun g => Dw w f g • v := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w (fun g => f g • v)) = fun g => Dx x (Dw w f) g • v
    rw [ih]
    exact Dx_smul_const x _ v

theorem polyOK_star {N a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : IsPolyDeg a P) :
    IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hPq⟩ := h

  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_rename_le _ _).trans (le_trans ?_ hq)
    exact MvPolynomial.totalDegree_le_of_support_subset (MvPolynomial.support_map_subset (f := starRingEnd ℂ) q)
  · intro g

    have key : ∀ (p : MvPolynomial ((Fin N × Fin N) ⊕ (Fin N × Fin N)) ℂ) (y : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℂ),
        star (MvPolynomial.eval y p) = MvPolynomial.eval₂ (starRingEnd ℂ) (fun i => star (y i)) p := by
      intro p y
      induction p using MvPolynomial.induction_on with
      | C c => rw [MvPolynomial.eval_C, MvPolynomial.eval₂_C, Complex.star_def]
      | add p p' hp hp' => rw [map_add (f := _), star_add, hp, hp', MvPolynomial.eval₂_add]
      | mul_X p i hp =>
        rw [map_mul, star_mul', hp, MvPolynomial.eval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    show star (P g) = _
    rw [MvPolynomial.eval_rename, MvPolynomial.eval_map, hPq g, key]
    congr 1
    funext i
    rcases i with ⟨a, b⟩ | ⟨a, b⟩ <;> simp

theorem polyOK_ck {κ : ℕ} {P : B.Mat k r → ℂ} (hP : IsPolyDeg κ P) (v : E) (UU : Set (B.Mat k r)) :
    B.CkOn ⊤ UU (fun g => P g • v) := by
  obtain ⟨hs, -⟩ := polynomial_bound k r κ P hP
  intro g₀ _
  exact ⟨Set.univ, fun g => P g • v, isOpen_univ, Set.mem_univ _,
    (hs.smul contDiff_const).contDiffOn, fun _ _ _ => rfl⟩

theorem polyOK_bound {κ : ℕ} {P : B.Mat k r → ℂ} (hP : IsPolyDeg κ P) (v : E) {d : ℝ} (hd : (κ : ℝ) ≤ d) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r, ‖B.dLR u w (fun g => P g • v) g‖ ≤ C * B.gN g ^ d := by
  obtain ⟨-, hB⟩ := polynomial_bound k r κ P hP
  obtain ⟨C₀, hC₀⟩ := hB m
  refine ⟨max C₀ 0 * ‖v‖, mul_nonneg (le_max_right _ _) (norm_nonneg _), ?_⟩
  intro u w hu hw hl g hg
  have h1 := hC₀ u w hu hw hl g hg
  have hs : ((u ++ w).map (fun _ : B.Mat k r => (0 : ℕ))).sum = 0 := by simp
  rw [hs, Nat.cast_zero, add_zero, dLR_eq] at h1

  have hg1 : 1 ≤ B.gN g := gN_ge_one hg
  have e0 : 0 ≤ B.gN g ^ (κ : ℝ) := Real.rpow_nonneg (zero_le_one.trans hg1) _
  have hpow : B.gN g ^ (κ : ℝ) ≤ B.gN g ^ d := Real.rpow_le_rpow_of_exponent_le hg1 hd
  have hC : ‖Dw (wL u ++ wR w) P g‖ ≤ max C₀ 0 * B.gN g ^ d :=
    h1.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) e0).trans
      (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
  rw [dLR_eq, Dw_smul_const, norm_smul]
  calc ‖Dw (wL u ++ wR w) P g‖ * ‖v‖ ≤ max C₀ 0 * B.gN g ^ d * ‖v‖ :=
        mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    _ = max C₀ 0 * ‖v‖ * B.gN g ^ d := by ring

end aux

private lemma foldr_max_zero_le_of_forall_le {o : ℕ} (l : List ℕ) (h : ∀ a ∈ l, a ≤ o) : l.foldr max 0 ≤ o := by

  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih => exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem polyOp_ok : Formalism.FourierDecayAlt.P.CutMP.JDPolyOK := by
  intro k r Wp Wq _ _ _ _ _ o κ Θ hΘ
  refine ⟨fun UU T hT => ?_, fun d hd T hT => ?_, ?_⟩
  · obtain ⟨-, P, hP, hc, hca⟩ := hΘ T hT
    rw [show T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hc,
      show T.coefAdj = fun g => star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hca]
    exact ⟨polyOK_ck hP _ UU, polyOK_ck (polyOK_star hP) _ UU⟩
  · obtain ⟨-, P, hP, hc, hca⟩ := hΘ T hT
    rw [show T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hc,
      show T.coefAdj = fun g => star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hca]
    refine ⟨polyOK_ck hP _ _, polyOK_ck (polyOK_star hP) _ _, fun m => ?_⟩
    obtain ⟨C₁, -, h₁⟩ := polyOK_bound hP (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) hd m
    obtain ⟨C₂, -, h₂⟩ := polyOK_bound (polyOK_star hP) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) hd m
    refine ⟨max C₁ C₂, fun u w hu hw hl g hg => ?_⟩
    have hx : 0 ≤ B.gN g ^ d := Real.rpow_nonneg (zero_le_one.trans (gN_ge_one hg)) d
    exact ⟨(h₁ u w hu hw hl g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx),
      (h₂ u w hu hw hl g hg).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)⟩
  · show (Θ.map fun T => T.word.length).foldr max 0 ≤ o
    refine foldr_max_zero_le_of_forall_le _ fun a ha => ?_
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp ha
    exact (hΘ T hT).1

end GlobalTheory.HatNF
end
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.cmEmbeddings_integral_and_distinct_mod_maximal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → (∀ τ x, V.Ge 0 (emA3 io ι τ x)) ∧ ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a : 𝓞 E, V.v (emA3 io ι τ a - emA3 io ι τ' a) = 0 := by
  first | exact @GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' | exact GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' | (intros; apply GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' <;> assumption)
end
