module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle037
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle009
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle040
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSecondPartialLawTrivial
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Harm
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ}

def invTranspose {K : Type} [Field K] (g : GL (Fin n) K) : GL (Fin n) K :=
  ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose, (g : Matrix (Fin n) (Fin n) K).transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem rename_letAct_invTranspose_eq_colAct {Ix : Type} [Fintype Ix] {pl : Ix → (E →+* ℂ)} (hpl : IsEnum H pl) (K : Type) [Field K]
    (g : {τ : E →+* ℂ // InPsi H τ} → GL (Fin n) K) (P : MvPolynomial (LtN Dw n) K) :
    rename (thetaLetterEquiv Dw n) (letAct Dw pl K (fun t => invTranspose (g ⟨pl t, (hpl.2 _).2 ⟨t, rfl⟩⟩)) P) =
      colAct K _ Dw.p Dw.q (Fin n) g (rename (thetaLetterEquiv Dw n) P) := by
  rw [colAct_apply]
  refine DFunLike.congr_fun (?_ : (rename (thetaLetterEquiv Dw n)).comp
    (letAct Dw pl K (fun t => invTranspose (g ⟨pl t, (hpl.2 _).2 ⟨t, rfl⟩⟩))) =
    (colSubst (fun t => (((g t)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (fun t => g t)).comp
      (rename (thetaLetterEquiv Dw n))) P
  refine MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, letAct, aeval_X]
  rcases half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) τ with h | ⟨τ, h, rfl⟩
  · have h₁ : ∃ t, pl t = τ := (hpl.2 τ).1 h

    rw [dite_eq_left h₁, thetaLetterEquiv_of_mem Dw h, colSubst_X_xVar, xForm_apply, map_sum]
    have e : (⟨pl h₁.choose, (hpl.2 _).2 ⟨_, rfl⟩⟩ : {τ : E →+* ℂ // InPsi H τ}) = ⟨τ, h⟩ :=
      Subtype.ext h₁.choose_spec
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw h]
    simp only [e]
    rfl
  · have h₀ : ¬ ∃ t, pl t = ComplexEmbedding.conjugate τ := fun hh => by
      have h₂ : InPsi H (ComplexEmbedding.conjugate τ) := (hpl.2 _).2 hh
      exact (not_mem_hostType_iff H τ).2 h₂ h
    have h₁ : ∃ t, ComplexEmbedding.conjugate (pl t) = ComplexEmbedding.conjugate τ := by
      obtain ⟨t, ht⟩ := (hpl.2 τ).1 h
      exact ⟨t, by rw [ht]⟩

    rw [dite_eq_right h₀, dite_eq_left h₁, thetaLetterEquiv_conjugate Dw h, colSubst_X_yVar, yForm_apply, map_sum]
    have e : (⟨pl h₁.choose, (hpl.2 _).2 ⟨_, rfl⟩⟩ : {τ : E →+* ℂ // InPsi H τ}) = ⟨τ, h⟩ :=
      Subtype.ext ((ComplexEmbedding.involutive_conjugate E).injective h₁.choose_spec)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw h]
    simp only [e]
    rfl

variable {l : Level H} (c : Coeff l)

theorem rename_minorP_of_mem (hn : Dw.p + Dw.q ≤ n) {τ : E →+* ℂ} (h : InPsi H τ) (i : Fin Dw.p)
    (hi : i.val < Dw.mult τ) (hi' : i.val + 1 ≤ n) :
    rename (thetaLetterEquiv Dw n) (minorPolynomial (Dw := Dw) c τ i.val hi (Fin.castLE hi')) =
      xMinor ⟨τ, h⟩ i (baseCovec c.F hn) := by
  rw [minorPolynomial, xMinor, AlgHom.map_det]
  congr 1
  ext1 s b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, baseCovec, xForm_single]
  rw [thetaLetterEquiv_of_mem Dw h]
  rfl

theorem rename_minorP_conjugate (hn : Dw.p + Dw.q ≤ n) {τ : E →+* ℂ} (h : InPsi H τ) (i : Fin Dw.q)
    (hi : i.val < Dw.mult (ComplexEmbedding.conjugate τ)) (hi' : n - (i.val + 1) + (i.val + 1) = n) :
    rename (thetaLetterEquiv Dw n) (minorPolynomial (Dw := Dw) c (ComplexEmbedding.conjugate τ) i.val hi
      (fun b => Fin.cast hi' (Fin.natAdd (n - (i.val + 1)) b))) =
      ((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : Poly c.F _ Dw.p Dw.q (Fin n)) *
        yMinor ⟨τ, h⟩ i (baseVec c.F hn) := by
  rw [minorPolynomial, yMinor, AlgHom.map_det, ← Matrix.det_permute']
  congr 1
  ext1 s b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, baseVec, yForm_single,
    Matrix.submatrix_apply, id]
  rw [thetaLetterEquiv_conjugate Dw h]
  refine congrArg X (Prod.ext rfl (Prod.ext rfl (Fin.ext ?_)))
  have := b.isLt
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_rev, Fin.val_castLE, Fin.revPerm_apply]
  omega

theorem rename_pG [Fintype {τ : E →+* ℂ // InPsi H τ}] (hn : Dw.p + Dw.q ≤ n) (a : (E →+* ℂ) × ℕ → ℕ) :
    ∃ u : ℤˣ, rename (thetaLetterEquiv Dw n) (pG (Dw := Dw) c a n) =
      ((u : ℤ) : Poly c.F _ Dw.p Dw.q (Fin n)) *
        basePoly c.F hn (fun t : {τ : E →+* ℂ // InPsi H τ} => diffOf fun i : Fin Dw.p => a (t.1, i))
          (fun t => diffOf fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i)) := by
  refine ⟨∏ t : {τ : E →+* ℂ // InPsi H τ}, ∏ i : Fin Dw.q, Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) ^
    diffOf (fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i)) i, ?_⟩
  rw [pG, ← Fintype.prod_sigma', ← (halfRowEquiv (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw)).symm.prod_comp,
    Fintype.prod_prod_type, basePoly, minorProd, map_prod]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Fintype.prod_sum_type, map_mul, mul_left_comm, ← Finset.prod_mul_distrib, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi' : i.val + 1 ≤ n := by have := i.isLt; omega
    have hi : i.val < Dw.mult t.1 := by rw [mult_of_mem Dw t.2]; exact i.isLt
    change rename _ ((if h : i.val + 1 ≤ n then
      (if InPsi H t.1 then minorPolynomial c t.1 i.val hi (Fin.castLE h)
        else minorPolynomial c t.1 i.val hi (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a t.1 i.val) = _
    rw [dite_eq_left hi', if_pos t.2, map_pow, rename_minorP_of_mem Dw c hn t.2]
    congr 1
    rw [aStep, diffOf, mult_of_mem Dw t.2]
    split_ifs <;> rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi' : i.val + 1 ≤ n := by have := i.isLt; omega
    have hi : i.val < Dw.mult (ComplexEmbedding.conjugate t.1) :=
      i.isLt.trans_eq (mult_conjEmb_of_mem Dw t.2).symm
    have h₀ : ¬ InPsi H (ComplexEmbedding.conjugate t.1) := fun h₂ => (not_mem_hostType_iff H t.1).2 h₂ t.2
    change rename _ ((if h : i.val + 1 ≤ n then
      (if InPsi H (ComplexEmbedding.conjugate t.1) then
        minorPolynomial c (ComplexEmbedding.conjugate t.1) i.val hi (Fin.castLE h)
        else minorPolynomial c (ComplexEmbedding.conjugate t.1) i.val hi
          (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a (ComplexEmbedding.conjugate t.1) i.val) = _
    rw [dite_eq_left hi', if_neg h₀, map_pow, rename_minorP_conjugate Dw c hn t.2, ← mul_pow]
    congr 1
    have hq : Dw.mult (ComplexEmbedding.conjugate t.1) = Dw.q := mult_conjEmb_of_mem Dw t.2
    rw [aStep, diffOf, hq]
    split_ifs <;> rfl

theorem pG_mem_ne_zero_generates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → pG (Dw := Dw) c a n ∈ harmA (Dw := Dw) c a n ∧ pG (Dw := Dw) c a n ≠ 0 ∧ ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (Set.range fun g : Ix → GL (Fin n) c.F => letAct Dw pl c.F g (pG (Dw := Dw) c a n)) := by
  intro E _ _ _ H Dw n Ix _ pl hpl hn l c a ha
  obtain ⟨u, hu⟩ := rename_pG Dw c hn a
  set k := fun t : {τ : E →+* ℂ // InPsi H τ} => diffOf fun i : Fin Dw.p => a (t.1, i) with hk
  set k' := fun t : {τ : E →+* ℂ // InPsi H τ} =>
    diffOf fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i) with hk'
  have hx (t : {τ : E →+* ℂ // InPsi H τ}) : partOf (k t) = fun i : Fin Dw.p => a (t.1, i) :=
    partOf_diffOf fun i j hij => ha t.1 hij
  have hy (t : {τ : E →+* ℂ // InPsi H τ}) :
      partOf (k' t) = fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i) :=
    partOf_diffOf fun i j hij => ha _ hij
  have hmem (P : MvPolynomial (LtN Dw n) c.F) :
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ↔
        rename (thetaLetterEquiv Dw n) P ∈ orbitSpan c.F hn k k' := by
    rw [← (rowHighest_orbitSpan_main hn k k' c.F).2.1, mem_rowHighest_iff_rowAdd]
    simp only [hx, hy]
    exact mem_HHa_iff_rename (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
      (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) _ P
  rw [← zsmul_eq_mul] at hu
  have hu' : basePoly c.F hn k k' = (u : ℤ) • rename (thetaLetterEquiv Dw n) (pG (Dw := Dw) c a n) := by
    rw [hu, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  have hinj := (thetaLetterEquiv Dw n).injective
  refine ⟨⟨(hmem _).2 ?_, fun m => ?_⟩, fun h0 => ?_, fun P hP => ?_⟩
  · rw [hu]
    exact zsmul_mem (basePoly_mem hn k k') _
  · rw [← coeff_rename_mapDomain _ hinj, hu, ← map_basePoly hn k k' (Int.castRingHom c.F), ← map_zsmul, coeff_map]
    exact intCast_mem _ _
  · rw [h0, map_zero, smul_zero] at hu'
    exact basePoly_ne_zero hn k k' hu'
  · have key : orbitSpan c.F hn k k' ≤ (Submodule.span c.F (Set.range fun g : Ix → GL (Fin n) c.F =>
        letAct Dw pl c.F g (pG (Dw := Dw) c a n))).map (rename (thetaLetterEquiv Dw n)).toLinearMap := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      simp only [hu', map_zsmul, ← rename_letAct_invTranspose_eq_colAct Dw hpl]
      exact zsmul_mem (Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self _))) _
    obtain ⟨Q, hQ, e⟩ := key ((hmem P).1 hP)
    rwa [← rename_injective _ hinj e]

end GlobalTheory.FrameRead
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem rd_fock_of_symLift : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x δ : Fin g → ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Odd n → δ ∈ Φ.lat → (n : ℂ) • x = (2 : ℂ) • δ → SymLift A L.L k n (Φ.e x) U → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fock Φ.Hm k x θ) := by
  intro S A _ _ L x0 g Φ hχ k n U x δ s s' θ hn hδ hnx hU hact hrd

  obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_thetaConstant_of_thetaGroup S A L x0 g Φ k U x hU.1
  have hread := GlobalTheory.T.reading_of_thetaGroup_action S A L x0 g Φ k U x c s s' θ hc hact hrd

  have hsq : c ^ 2 = 1 := GlobalTheory.T.thetaConst_symmetric_square_eq_one S A L x0 g Φ k U x c hc hU.3

  have hmem : (n : ℂ) • x ∈ Φ.lat := by
    rw [hnx, two_smul]
    exact add_mem hδ hδ
  have hχδ : Φ.χ ((2 : ℂ) • δ) = 1 := (GlobalTheory.T.appellHumbert_frame_semicharacter S A L x0 g Φ).2.2 hχ δ hδ
  have hpow := GlobalTheory.T.thetaConstant_pow_eq_one_of_power_trivial S A L x0 g Φ k n U x c hc hmem hU.2
  rw [hnx, hχδ, one_zpow, _root_.mul_one] at hpow

  have hc1 : c = 1 := by
    obtain ⟨m, rfl⟩ := hn
    rw [pow_succ, pow_mul, hsq, one_pow, _root_.one_mul] at hpow
    exact hpow
  subst hc1
  simpa only [_root_.one_mul] using hread

end GlobalTheory.AnVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.normalisedPullbackMulN_reads_theta : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (N : ℕ) (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ^ N).left] ![(N : ℤ) ^ 2, -1])) (s : LB.Sec (LPow A L.L 1 (Over.mk x0))) (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), α₀.IsGen → IsNormMul A L.L L.rig N α₀ → LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd (Over.mk x0) A).left) → IsTwistPull A L.L (mulT A (Over.mk x0) N) (snd (Over.mk x0) A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ → Φ.Rd 1 s θ → Φ.Rd ((N : ℤ) ^ 2) s₁ (fun z => θ ((N : ℂ) • z)) := by
  first | exact @GlobalTheory.AnVal.rd_mulN | exact GlobalTheory.AnVal.rd_mulN | (intros; apply GlobalTheory.AnVal.rd_mulN <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_normalisedIso_reading_one_analyticFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∃ wP : PrimTy H Xo, IsPrim wP) ∧ ∀ wP : PrimTy H Xo, IsPrim wP → ∀ z : Fin g → ℂ, Φ.toAnFr.GenRd _ _ wP (Φ.e z).left (Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z])) 1 := by
  first | exact @GlobalTheory.AnVal.PrimRd.prim_reading | exact GlobalTheory.AnVal.PrimRd.prim_reading | (intros; apply GlobalTheory.AnVal.PrimRd.prim_reading <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_analytic_frame_of_unit_uniformisation_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W), letI : Algebra c.F ℂ := σ.toAlgebra; ∃ Φ : AnPt (Xo := Xo) (c := c) (U.un k x) W.g (fun j => relab c σ (W.e j).1) W.e, Φ.OfFam W.F (W.ik k) W.Pm ∧ Φ.Hm = Wu.Hm ∧ Φ.χ = Wu.χl ∧ Φ.fr = Wu.fr ∧ Φ.toAnFr.Rd 1 (U.un k x).s Wu.θ ∧ (∀ kk F θ, Φ.toAnFr.Rd kk F θ ↔ IsFrRd W Wu kk F θ) ∧ (∀ (α : 𝓞 E) a, W.Pm (W.F.t (W.ik k) (α • a)) = tyAct (fun j => relab c σ (W.e j).1) α (W.Pm (W.F.t (W.ik k) a))) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo (U.un k x).x a = Φ.e ((l.M : ℂ)⁻¹ • W.Pm (W.F.t (W.ik k) a)) := by
  first | exact @GlobalTheory.AnVal.exists_anPt_of_unitAt | exact GlobalTheory.AnVal.exists_anPt_of_unitAt | (intros; apply GlobalTheory.AnVal.exists_anPt_of_unitAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.analyticFrame_second_partial_law_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 3 × Fin g) m)ˣ, (u : Jet ℂ (Fin 3 × Fin g) m) = psJet m (anFB ty).ph2 ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift (jpt y g Φ.jx m (1 : Fin 3)) (lift (jpt y g Φ.jx m (2 : Fin 3)) (jpt y g Φ.jx m (0 : Fin 3)))).left) (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn g m ![1, 2] ((anFB ty).G.F j)]) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)])) (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))) := by
  first | exact @GlobalTheory.AnValSecondLaw.second_law | exact GlobalTheory.AnValSecondLaw.second_law | (intros; apply GlobalTheory.AnValSecondLaw.second_law <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.analyticFrame_symmetry_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m (anFB ty).sy ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m) (scaleGen _ _ (unitΓ u⁻¹) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  first | exact @GlobalTheory.AnVal.Sym.sy_trivial | exact GlobalTheory.AnVal.Sym.sy_trivial | (intros; apply GlobalTheory.AnVal.Sym.sy_trivial <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_familyUnif_isTypeFn_card_comp_le : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty ∧ Fintype.card U.Comp ≤ F.n := by
  first | exact @GlobalTheory.card_comp_le_periodSpaces | exact GlobalTheory.card_comp_le_periodSpaces | (intros; apply GlobalTheory.card_comp_le_periodSpaces <;> assumption)
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

section

open GlobalTheory.LevelPairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_zetaM_pow (c : Coeff l) (ta : c.F ≃+* c.F) :
    ∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M] := by
  have h3 := l.three_le
  haveI : NeZero l.M := ⟨by omega⟩
  have hp := zetaM_prim c
  have hp' : IsPrimitiveRoot (ta (zetaM c)) l.M := hp.map_of_injective ta.injective
  obtain ⟨a, -, ha⟩ := hp.eq_pow_of_pow_eq_one hp'.pow_eq_one
  have hco : a.Coprime l.M := (hp.pow_iff_coprime (by omega) a).1 (ha ▸ hp')
  obtain ⟨a', -, h⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco (by omega)
  refine ⟨a, a', ha.symm, ?_⟩
  unfold Nat.ModEq
  rw [h, Nat.mod_eq_of_lt (by omega)]

theorem mk_qRep {K : Submodule (𝓞 E) Dw.La} (x : Dw.La ⧸ K) : (Submodule.Quotient.mk (qRep x) : Dw.La ⧸ K) = x :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ x)

theorem level_nsmul (x : LevQc Dw l) : l.M • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : (l.M : 𝓞 E) ∈ l.Mb * Mfr l := by
    rw [Mfr, l.prod]; exact Ideal.mem_span_singleton_self _
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (Submodule.mem_inf.1 (Ideal.mul_le_inf h)).2 Submodule.mem_top

theorem nsmul_nsmul_of_modEq {n a a' : ℕ} (h : a * a' ≡ 1 [MOD l.M]) (x : Fin n → LevQc Dw l) :
    a • a' • x = x := by
  have h3 := l.three_le
  have hM : l.M • x = 0 := funext fun b => level_nsmul (x b)
  have e : a * a' = l.M * (a * a' / l.M) + 1 := by
    have := Nat.div_add_mod (a * a') l.M
    rw [h, Nat.mod_eq_of_lt (show 1 < l.M by omega)] at this
    exact this.symm
  rw [← mul_smul, e, add_smul, one_smul, mul_comm, mul_smul, hM, smul_zero, zero_add]

theorem pairL_nsmul {n : ℕ} (a : ℕ) (x : Fin n → LevQc Dw l) (y : Fin n → Dw.La) :
    (l.M : ℤ) ∣ (a : ℤ) * pairL (l := l) (fun b => qRep (x b)) y -
      pairL (l := l) (fun b => qRep ((a • x) b)) y := by
  have e : (a : ℤ) * pairL (l := l) (fun b => qRep (x b)) y = pairL (l := l) (fun b => a • qRep (x b)) y := by
    unfold pairL
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  rw [e]
  refine pairL_congr _ _ _ _ (fun b => ?_) (fun b => by simp)
  rw [← Submodule.Quotient.eq, mk_qRep, ← Nat.cast_smul_eq_nsmul (𝓞 E), Submodule.Quotient.mk_smul, mk_qRep,
    Nat.cast_smul_eq_nsmul]
  rfl

theorem map_phiHat (c : Coeff l) {n : ℕ} (ta : c.F ≃+* c.F) {a a' : ℕ} (ha : ta (zetaM c) = zetaM c ^ a)
    (h : a * a' ≡ 1 [MOD l.M]) (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q := by
  have h' : a' * a ≡ 1 [MOD l.M] := mul_comm a a' ▸ h
  let e : (Fin n → LevQc Dw l) ≃ (Fin n → LevQc Dw l) :=
    ⟨fun x => a • x, fun x => a' • x, nsmul_nsmul_of_modEq h', nsmul_nsmul_of_modEq h⟩
  unfold phiHat
  refine (ta.toAddEquiv.map_finsum _).trans (Eq.trans (finsum_congr fun x => ?_) (finsum_comp_equiv e))
  change ta _ = ta (φ (a' • a • x)) * zetaM c ^ pairL (l := l) (fun b => qRep ((a • x) b)) _
  rw [nsmul_nsmul_of_modEq h', map_mul, map_zpow₀, ha, ← zpow_natCast, ← zpow_mul,
    zpow_congr c (pairL_nsmul a x _)]

theorem phiHat_mul (c : Coeff l) {n : ℕ} (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    phiHat c (fun x => u * φ x) q = u * phiHat c φ q := by
  unfold phiHat
  rw [← smul_eq_mul u, smul_finsum]
  refine finsum_congr fun x => ?_
  rw [smul_eq_mul, mul_assoc]

theorem shortValAt_mul {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (nab : NabV Xo c)
    (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (h : ShortValAt Xo c nab w Λ b N P y v) :
    ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, ?_⟩
  rw [map_mul, h7, AlgHom.commutes, mul_left_comm]
  congr 1
  rw [← Algebra.smul_def, smul_finsum]
  refine finsum_congr fun q => ?_
  rw [Algebra.smul_def, map_mul, mul_assoc]

end

theorem phiHat_aut_and_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ), (∀ ta : c.F ≃+* c.F, (∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M]) ∧ ∀ a a' : ℕ, ta (zetaM c) = zetaM c ^ a → a * a' ≡ 1 [MOD l.M] → ∀ (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l), ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q) ∧ (∀ (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) q, phiHat c (fun x => u * φ x) q = u * phiHat c φ q) ∧ ∀ (nab : NabV Xo c) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S), ShortValAt Xo c nab w Λ b N P y v → ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  intro E _ _ _ H Dw l Xo c n
  exact ⟨fun ta => ⟨exists_zetaM_pow c ta, fun _ _ ha h φ q => map_phiHat c ta ha h φ q⟩,
    fun u φ q => phiHat_mul c u φ q,
    fun nab w Λ b u N P S _ _ y v h => shortValAt_mul nab w Λ b u N P S y v h⟩

end GlobalTheory.GalTw
end
