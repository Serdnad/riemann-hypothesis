module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsUniqueSecIsFnAt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertTrivialOfNowhereVanishing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExAtMemPairChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle785
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle013
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicClassicalVacuumFactorEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.MulFrame

open GlobalTheory.ThetaFn GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter

theorem exists_two_mul_dot {g : ℕ} {a : Fin g → ℂ} (ha : Half a) (M : Fin g → ℤ) :
    ∃ n : ℤ, 2 * (a ⬝ᵥ cv M) = n := by
  have h : ∀ i, ∃ n : ℤ, 2 * a i = n := fun i => by
    rcases ha i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using h
  refine ⟨∑ i, n i * M i, ?_⟩
  simp only [dotProduct, cv, Finset.mul_sum, ← _root_.mul_assoc, hn]
  push_cast
  rfl

theorem cv_nsmul {g : ℕ} (m : ℕ) (M : Fin g → ℤ) : cv (m • M) = (m : ℂ) • cv M := by
  funext i
  simp [cv]

theorem perV_nsmul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (m : ℕ) (M N : Fin g → ℤ) :
    perV τ (m • M) (m • N) = (m : ℂ) • perV τ M N := by
  rw [perV, perV, cv_nsmul, cv_nsmul, Matrix.mulVec_smul, smul_add]

theorem autV_nsmul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) {a b : Fin g → ℂ} (ha : Half a) (hb : Half b) (m : ℕ)
    (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    autV τ a b (m • M) (m • N) ((m : ℂ) • z) = autV τ a b M N z ^ (m ^ 2) := by
  obtain ⟨p, hp⟩ := exists_two_mul_dot ha M
  obtain ⟨q, hq⟩ := exists_two_mul_dot hb N
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self (m : ℤ)
  have hk' : (m : ℂ) * (m - 1) = k + k := by exact_mod_cast hk
  rw [autV, autV, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(k * (p - q)), ?_⟩
  simp only [cv_nsmul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  push_cast
  rw [← hp, ← hq]
  linear_combination (-(2 * Real.pi * Complex.I * (a ⬝ᵥ cv M - b ⬝ᵥ cv N))) * hk'

section Origin

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T}

theorem val_origin {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig) {m : T ⊗ A ⟶ A} {ε : Fin 2 → ℤ} {c : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ε)}
    (hn : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L rig T c)) (i : L.ι)
    (hi : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] (fun _ => i)) :
    valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] (fun _ => i)) (α.s fun _ => i).val = u.fr i 0 ^ c := by
  have he := comp_ptSecT u p (comp_one_eq_ex_zero u p)
  have h1 : ⊤ ≤ p.left ⁻¹ᵁ LB.wchart L (fun k => (ptSecT A (1 : T ⟶ A)).left ≫ ![(snd T A).left, m.left] k)
      (fun _ => i) := by
    rw [← he] at hj
    exact fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hj hy) k
  have h2 := (mem_ptChart_iff (comp_one_eq_ex_zero u p) (fun _ => i)).2 hi
  have h12 := (le_preimage_inf p.left _ _).2 ⟨h1, h2⟩
  have e := congrArg (fun t => valAt' p.left _ (Units.val t))
    (hn (fun _ => i) (fun _ => i) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl))
  refine Eq.trans ?_ (((ThetaFn.valAt'_res p.left inf_le_left h12 _).symm.trans
    (e.trans (ThetaFn.valAt'_res p.left inf_le_right h12 _))).trans (valAt'_rigT p hrig c (fun _ => i) hi))
  rw [← he]
  exact (valAt'_appLE' p.left (ptSecT A (1 : T ⟶ A)).left _ h1 _).symm

end Origin

theorem fnT_iff {g : ℕ} {P : PolAV (Sp ℂ)} (u : HolUnif P.A P.L g) (k : ℕ)
    (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ) :
    FnT u k t f ↔ IsFnAt u basePt (k : ℤ) t f := by
  constructor
  · intro h j z hj
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    rw [zpow_natCast]
    exact h i z ((exAt_mem_chart_iff u basePt _ _ z).1 hj)
  · intro h i z hi
    rw [← zpow_natCast]
    exact h (fun _ => i) z ((exAt_mem_chart_iff u basePt _ _ z).2 hi)

end GlobalTheory.MBLow.Cl.MulFrame

namespace GlobalTheory.MBLow.Cl


open GlobalTheory.ThetaFn GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter MulFrame in
theorem exists_normalised_mulPull_fnT : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ), FnT u 1 th f → ∃ (α : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![(snd (baseOver (Sp ℂ)) x.P.A).left, (snd (baseOver (Sp ℂ)) x.P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (s₁ : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp ℂ)))), α.IsGen ∧ LB.Gen.Corr x.P.L _ _ _ _ (LB.pullGen x.P.L _ _ α (ptSecT x.P.A 1).left) (rigT x.P.A x.P.L x.rig (baseOver (Sp ℂ)) (((m ^ 2 : ℕ) : ℤ) - 1)) ∧ IsTwistPull x.P.A x.P.L (mulT x.P.A (baseOver (Sp ℂ)) m) (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧ FnT u (m ^ 2) s₁ fun z => f ((m : ℂ) • z) := by
  intro g x hg u τ a b c W hNF m th f hf
  have hfr := frame_eq_autV_mul g x hg u τ a b c W hNF
  obtain ⟨-, -, ha, hb, -, hΛ, hrig, -⟩ := hNF
  have hL := x.P.isLB
  have H := GlobalTheory.exists_mulPull_gen_over GlobalTheory.abelianSchemeLaws_all.1.mulPull x.P (baseOver (Sp ℂ)) m
  rw [← Nat.cast_pow] at H
  obtain ⟨α₀, hα₀⟩ := H
  obtain ⟨α, hα, hn⟩ := NormTheta.exists_normalised hL x.rig_gen m ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
    (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₀ hα₀
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT x.P.A (baseOver (Sp ℂ)) m)
    (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  refine ⟨α, s₁, hα, hn, hs₁, ?_⟩
  have hψ := exAt_mulT u basePt m
  have hΦ : ∀ z, exAt u basePt z ≫ (snd (baseOver (Sp ℂ)) x.P.A ^ m).left = (u.ex ((m : ℂ) • z)).left := fun z => by
    rw [← lift_snd (fst (baseOver (Sp ℂ)) x.P.A) (snd (baseOver (Sp ℂ)) x.P.A ^ m), Over.comp_left, ← Category.assoc]
    exact (congrArg (· ≫ _) (hψ z)).trans (exAt_snd _ _ _)
  obtain ⟨r, hr, hne, hrj⟩ := exists_fn_of_isGen (Φ := fun z => (m : ℂ) • z) hL (by fun_prop) hΦ hα
  haveI := u.discrete
  obtain ⟨-, -, k3⟩ := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 (fun _ => 1) r
    Matrix.isHermitian_zero (fun _ => norm_one) hr hne (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
      obtain ⟨i', hi'⟩ := exists_chart u valueRules hL ((m : ℂ) • z)
      have hj := (exAt_mem_pairChart_iff (hΦ z) ![i, i']).2 ⟨hi, hi'⟩
      have hj' := hj
      rw [← exAt_add_period u basePt z l l.2] at hj'
      rw [hrj _ _ hj', hrj _ _ hj, exAt_add_period u basePt z l l.2]
      obtain ⟨M, N, hl⟩ := (hΛ l).1 l.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hermForm, Matrix.zero_mulVec, dotProduct_zero]
      rw [hfr M N i z hi, hfr (m • M) (m • N) i' _ hi', autV_nsmul τ ha hb, perV_nsmul, hl, smul_add]
      have n1 : autV τ a b M N z ≠ 0 := Complex.exp_ne_zero _
      simp only [_root_.zpow_neg, zpow_natCast, mul_pow, pow_one, mul_zero, add_zero, Complex.exp_zero]
      field_simp)
  have h0 : r 0 = 1 := by
    obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
    have hj := (exAt_mem_pairChart_iff (hΦ 0) (fun _ => i)).2 ⟨hi, by rw [smul_zero]; exact hi⟩
    have n := u.fr_ne i 0 hi
    rw [hrj _ _ hj, val_origin hrig hn i hi hj, smul_zero, ← zpow_add₀ n, ← zpow_add₀ n]
    simp
  have hc : IsPullConst u basePt (fun z => (m : ℂ) • z) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α 1 := fun j z hj => by
    have n := zpow_ne_zero ((m ^ 2 : ℕ) : ℤ) (u.fr_ne _ _ ((exAt_mem_pairChart_iff (hΦ z) j).1 hj).1)
    rw [← h0, ← k3 z, hrj j z hj, _root_.zpow_neg, inv_mul_cancel_right₀ n]
  have h2 := isFnAt_fnAt u basePt hL _ s₁
  have e := funext (hc.fn_eq hL hψ hs₁ ((fnT_iff u 1 th f).1 hf) h2)
  rw [fnT_iff]
  simpa only [e, _root_.one_mul] using h2

end GlobalTheory.MBLow.Cl

end
end

section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexConjugate
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.WeylModel

variable {F : Type} [Field F] [NumberField F]

theorem act_weyl {κ : Type} [Fintype κ] [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = (w.2, -w.1) := by
  simp [AdelicSvN.act, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : AF F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (GlobalTheory.StdCharFromIsStd.norm_psi hψ t)]

end GlobalTheory.TowU.WeylModel


open GlobalTheory.TowU.WeylModel in
theorem GlobalTheory.TowU.realised_weyl2 : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  intro F _ _ ψ hψ κ _ _
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ ⊕ κ → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ → AF F) := ⟨rfl⟩
  let μ : Measure (κ → AF F) := Measure.addHaar
  let E : (κ → AF F) × (κ → AF F) ≃+ (κ ⊕ κ → AF F) :=
    { toFun := fun p => Sum.elim p.1 p.2
      invFun := fun x => (x ∘ Sum.inl, x ∘ Sum.inr)
      left_inv := fun p => by simp
      right_inv := fun x => by simp
      map_add' := fun p q => by funext i; cases i <;> rfl }
  have hc : Continuous E := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).symm.continuous
  have hc' : Continuous E.symm := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).continuous
  let H : (κ → AF F) × (κ → AF F) ≃ₜ (κ ⊕ κ → AF F) :=
    { toEquiv := E.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  let ν : Measure (κ ⊕ κ → AF F) := Measure.map E (μ.prod μ)
  haveI : ν.IsAddHaarMeasure := E.isAddHaarMeasure_map _ hc hc'
  let ε₁ : κ → ℤˣ := fun _ => 1
  let ε₂ : κ ⊕ κ → ℤˣ := Sum.elim (fun _ => 1) (fun _ => -1)
  obtain ⟨S, S', hS, hSf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ κ μ inferInstance ε₁
  obtain ⟨Sd, Sd', hSd, hSdf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ (κ ⊕ κ) ν inferInstance ε₂
  refine ⟨S, S', ?_, Sd, Sd', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · convert hS using 1
    funext w
    rw [act_weyl]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [ε₁]
  · convert hSd using 1
    funext w
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>
      simp [dblAct, act_weyl, ε₂]
  · funext y
    have hν : ν = Measure.map H.toMeasurableEquiv (μ.prod μ) := rfl
    have e₂ : star (S (star φ₂)) (y ∘ Sum.inr) =
        ∫ x, φ₂ x * ψ (-(∑ i, ((ε₁ i : ℤ) : AF F) * x i * (y ∘ Sum.inr) i)) ∂μ := by
      rw [Pi.star_apply, hSf (star φ₂) (GlobalTheory.ConjSch.star_mem_schA κ φ₂ h₂), Complex.star_def, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_mul, conj_psi hψ, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [hSdf _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ h₁ φ₂ h₂), hν, integral_map_equiv]
    change _ = S φ₁ (y ∘ Sum.inl) * star (S (star φ₂)) (y ∘ Sum.inr)
    rw [e₂, hSf φ₁ h₁, ← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change φ₁ p.1 * φ₂ p.2 * ψ (∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i) = _
    have es : ∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i =
        ∑ i, ((ε₁ i : ℤ) : AF F) * p.1 i * (y ∘ Sum.inl) i +
          -(∑ i, ((ε₁ i : ℤ) : AF F) * p.2 i * (y ∘ Sum.inr) i) := by
      simp [Fintype.sum_sum_type, ε₁, ε₂]
    rw [es, AddChar.map_add_eq_mul]
    ring

end
end

section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.UnipOp

open GlobalTheory.AdelicSvNQuad GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem star_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : AF F) : star (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [show star (ψ t) = starRingEnd ℂ (ψ t) from rfl, Complex.conj_mul', GlobalTheory.StdCharFromIsStd.norm_psi hψ t]
  simp

theorem invOf_two_eq : (⅟(2 : AF F)) = algebraMap F (AF F) (2⁻¹) := by
  refine invOf_eq_right_inv ?_
  rw [show (2 : AF F) = algebraMap F (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
    mul_inv_cancel₀ (two_ne_zero), map_one]

theorem quad_rat {κ : Type} [Fintype κ] (B : Matrix κ κ F) (ξ : κ → F) :
    quad (⅟(2 : AF F)) (B.map (algebraMap F (AF F))) (fun i => algebraMap F (AF F) (ξ i)) =
      algebraMap F (AF F) (quad (2⁻¹ : F) B ξ) := by
  rw [map_quad, invOf_two_eq]

theorem isOp_unip (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (C : Matrix κ κ F) (hC : Cᵀ = C) :
    IsOp ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1))
      (mulQ (F := F) ψ (⅟2) (C.map (algebraMap F (AF F)))) (mulQ (F := F) ψ (⅟2) (-(C.map (algebraMap F (AF F))))) := by
  set A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F)) with hAdef
  have hA : Aᵀ = A := by rw [hAdef, ← Matrix.transpose_map, hC]
  have inv : ∀ (B : Matrix κ κ (AF F)) φ, mulQ ψ (⅟2) (-B) (mulQ ψ (⅟2) B φ) = φ := fun B φ => by
    funext x
    rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  have inv' : ∀ (B : Matrix κ κ (AF F)) φ, mulQ ψ (⅟2) B (mulQ ψ (⅟2) (-B) φ) = φ := fun B φ => by
    have := inv (-B) φ
    rwa [neg_neg] at this
  have adm : ∀ B : Matrix κ κ (AF F), ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ mulQ ψ (⅟2) B ∈ (adeleClass F).adm κ := by
    intro B l hl g hg
    obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ (⅟2) B hg
    obtain ⟨T, hT⟩ := hl g' hg'
    exact ⟨T.comp M, fun f => by rw [LinearMap.comp_apply, hM f, hT]; rfl⟩
  have nrm : ∀ (B : Matrix κ κ (AF F)) (φ : (κ → AF F) → ℂ) x, ‖mulQ ψ (⅟2) B φ x‖ₑ = ‖φ x‖ₑ := by
    intro B φ x
    rw [mulQ_apply, enorm_mul, ← ofReal_norm (ψ _), GlobalTheory.StdCharFromIsStd.norm_psi hψ, ENNReal.ofReal_one, one_mul]
  refine ⟨mulQ_mem ψ hψ _ A, mulQ_mem ψ hψ _ (-A), fun φ _ => inv A φ, fun φ _ => inv' A φ, adm A, adm (-A),
    fun w φ _ => funext fun x => ?_, ⟨1, one_ne_zero, fun φ _ => ?_⟩, ?_⟩
  · rw [act_unip, mulQ_apply]
    simp only [schr]
    rw [mulQ_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add A hA]
  · rw [one_mul]
    unfold thetaSum
    congr 1
    funext ξ
    rw [mulQ_apply, hAdef, quad_rat, hψ.2.1, one_mul]
  · intro μ μ' hμ hμ'
    letI : MeasurableSpace (κ → AF F) := borel _
    haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
    haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : SecondCountableTopology (κ → AF F) := inferInstance
    haveI := hμ
    haveI := hμ'
    have e := Measure.isAddLeftInvariant_eq_smul μ' μ
    have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ
    refine ⟨(μ'.addHaarScalarFactor μ : ℝ≥0∞), by exact_mod_cast hpos.ne', ENNReal.coe_ne_top, fun φ _ => ?_⟩
    simp_rw [nrm]
    conv_lhs => rw [e]
    rw [lintegral_smul_measure]
    rfl

end GlobalTheory.TowU.UnipOp

namespace GlobalTheory.TowU.UnipOp

open GlobalTheory.AdelicSvNQuad GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem dblAct_unip {κ : Type} [Fintype κ] [DecidableEq κ] (C : Matrix κ κ F) :
    dblAct (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1) :
        (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F)) =
      GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-(Matrix.fromBlocks C 0 0 (-C))) 1) := by
  funext w
  rw [act_unip]
  simp only [dblAct, act_unip]
  refine Prod.ext ?_ ?_
  · funext a
    rcases a with a | a <;> rfl
  · funext a
    rcases a with a | a <;>
      simp [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec] <;> ring

theorem quad_dbl {κ : Type} [Fintype κ] (h : AF F) (A : Matrix κ κ (AF F)) (x : κ ⊕ κ → AF F) :
    quad h (Matrix.fromBlocks A 0 0 (-A)) x = quad h A (x ∘ Sum.inl) + -quad h A (x ∘ Sum.inr) := by
  simp only [quad, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add, Matrix.neg_mulVec, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], ∀ C : Matrix κ κ F, Cᵀ = C → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1)) S S' := by
  intro F _ _ ψ hψ κ _ _ C hC
  set A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F)) with hAdef
  let Cd : Matrix (κ ⊕ κ) (κ ⊕ κ) F := Matrix.fromBlocks C 0 0 (-C)
  have hCd : Cdᵀ = Cd := by
    simp only [Cd, Matrix.fromBlocks_transpose, hC, Matrix.transpose_zero, Matrix.transpose_neg]
  have hn : (-C).map (algebraMap F (AF F)) = -C.map (algebraMap F (AF F)) := Matrix.map_neg _ (map_neg _) _
  have hCdA : Cd.map (algebraMap F (AF F)) = Matrix.fromBlocks A 0 0 (-A) := by
    simp only [Cd, Matrix.fromBlocks_map, hAdef, Matrix.map_zero _ (map_zero _), hn]
  refine ⟨_, _, isOp_unip ψ hψ C hC, mulQ ψ (⅟2) (Cd.map (algebraMap F (AF F))),
    mulQ ψ (⅟2) (-(Cd.map (algebraMap F (AF F)))), ?_, fun φ₁ _ φ₂ _ => funext fun x => ?_⟩
  · rw [dblAct_unip]
    exact isOp_unip ψ hψ Cd hCd
  · rw [mulQ_apply, hCdA, quad_dbl]
    simp only [boxFun, Pi.star_apply, mulQ_apply, star_mul', star_star, star_psi hψ]
    rw [AddChar.map_add_eq_mul, ← hAdef]
    ring

end GlobalTheory.TowU.UnipOp
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem rexp_eq_zero_iff_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Letter E), 1 ≤ x.1 → (rexp x = 0 ↔ x.2.IsUnitary) ∧ (x.2.IsUnitary ↔ (CG.mk x.2).IsUnitary) := by
  intro E _ _ _ x ha
  refine ⟨?_, (CG.isUnitary_mk _).symm⟩
  have hc : ∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ :=
    Classical.epsilon_spec (p := fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ)
      (by rw [zc_eq_scL]; exact Central.lie_scalar x.2 (1 : Cinf E))
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hpos : (0 : ℝ) < x.1 * Module.finrank ℚ E := by positivity
  have hz := (zc_comm_mem_eigen E x.1).2.2
  rw [rexp, div_eq_zero_iff, or_iff_left hpos.ne']
  constructor
  · intro h0
    have hne : (x.1 * (Module.finrank ℚ E : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
    obtain ⟨χ, h1, -, h2, -⟩ := exists_abs_cpow E (-cex x / (x.1 * (Module.finrank ℚ E : ℂ)))
    have hre : (-cex x / (x.1 * (Module.finrank ℚ E : ℂ))).re = 0 := by
      rw [← Nat.cast_mul, Complex.div_natCast_re, Complex.neg_re, h0]; simp
    have hχ : χ.IsUnitary := fun y => by
      rw [h2, hre, nu, Model.eq_one_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E 0)]
      exact isUnitary_one y
    have hn : IsNormalised (x.2.twist χ) := by
      rintro _ ⟨φ, hφ, rfl⟩ t g
      have h3 : zc E x.1 (mulChi x.1 χ φ) = (0 : ℂ) • mulChi x.1 χ φ := by
        rw [h1, hc φ hφ, mul_div_cancel₀ _ hne, ← add_smul, add_neg_cancel, map_smul]
      simpa using (hz _ 0).1 h3 t g
    obtain ⟨ω, hω⟩ := Central.exists_hasCentral E x.1 x.2
    have h4 := ((hω.twist χ).isUnitary_iff.1 (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn)).mul
      (isUnitary_pow hχ x.1).inv
    rw [mul_inv_cancel_right] at h4
    exact hω.isUnitary_iff.2 h4
  · intro hu
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 x.2.ne_bot
    obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
    have h1 := congrArg norm ((hz φ _).1 (hc φ hφ) 1 g)
    rw [splitCentre_eq_scalar, hu.norm_eq hφ, norm_mul, Complex.norm_exp] at h1
    have h2 := (mul_eq_right₀ (norm_ne_zero_iff.2 hg)).1 h1.symm
    simpa using h2

end GlobalTheory.ResW
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_adelicClassicalVacuumFactor_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → X.Λ = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) X.Λ) v → ∀ κ : ℂ, Reads θ V W hr X bas idx f (κ • v) x → (∀ x' ∈ X.dom, IsUnitFr X x' → ∀ (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ), IsTheta1 X bas idx (H.w0 : D.host.E) x' X.Λ ϑ → MeanOne X bas idx x' X.Λ ϑ → (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X bas idx v x' z) → ‖κ'‖ = ‖κ‖) := by
  first | exact @GlobalTheory.AdTh.norm_factor_eq_of_reads | exact GlobalTheory.AdTh.norm_factor_eq_of_reads | (intros; apply GlobalTheory.AdTh.norm_factor_eq_of_reads <;> assumption)
end
