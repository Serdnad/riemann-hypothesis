module

import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CubicalReadingOneAnalyticFrame
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaConstSymmetricSquareEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle009
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle035
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle036
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle030
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal.Sym

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

theorem tay_coord {g : ℕ} (k : Fin g) :
    tay (fun v : Fin g → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  apply GlobalTheory.JetLinSub.tay_coord <;> assumption


theorem psJet_X {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (s : κ) :
    psJet m (MvPowerSeries.X s : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X s) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem jetN_coord {n g : ℕ} (m : ℕ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j) = Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  unfold jetN jetOf
  show renN n g m (psJet m (tay (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) 0)) = _
  rw [tay_coord, psJet_X]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply]

def swapL (g : ℕ) : (Fin 2 → Fin g → ℂ) →ₗ[ℂ] (Fin 2 → Fin g → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Equiv.swap (0 : Fin 2) 1 i)

def swapI : ULift.{0} (Finset (Fin 2)) ≃ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.finsetCongr (Equiv.swap (0 : Fin 2) 1)).trans Equiv.ulift.symm)

theorem psumL_swap (g : ℕ) (I : ULift.{0} (Finset (Fin 2))) :
    psumL 2 g I ∘ₗ swapL g = psumL 2 g (swapI I) := by
  refine LinearMap.ext fun w => ?_
  simp [psumL, swapL, swapI, Equiv.finsetCongr_apply]

theorem cε_swap (I : ULift.{0} (Finset (Fin 2))) : cε 2 (swapI I) = cε 2 I := by
  simp [cε, swapI, Equiv.finsetCongr_apply]

theorem jetMap_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n m : ℕ} {ψ ψ' : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) (h' : Φ.JetMap m ψ' Λ) : ψ = ψ' := by
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, rfl⟩ := h'
  rfl

theorem sy_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m (anFB ty).sy ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m) (scaleGen _ _ (unitΓ u⁻¹) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hI e he m
  refine ⟨1, ?_, ?_⟩
  · show (1 : Jet ℂ (Fin 2 × Fin g) m) = psJet m 1
    rw [← MvPolynomial.coe_one, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, map_one]
  have hR := (he m).2
  have hS := GlobalTheory.T.jetReading_linearSubstitution_points _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr 2 2 m (swapL g)
    (fun p : Fin 2 × Fin g => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] :
      Fin 2 → Fin g → MvPolynomial (Fin 2 × Fin g) ℂ) p.1 p.2) (by
      rintro ⟨i, j⟩
      rw [psJet_X]
      refine Eq.trans ?_ (jetN_coord m (Equiv.swap (0 : Fin 2) 1 i) j).symm
      show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
      fin_cases i <;> simp) _ _ _ _ _ hR
  have hC := GlobalTheory.T.corr_of_jets_of_analytic_frame_products _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hI 2 m _ _ _ _ _ _ _ _ _ _ hR hS (by
    intro ψ
    refine (Fintype.sum_equiv swapI _ _ fun I => ?_).symm
    have h1 := hS.1 I
    beta_reduce at h1 ⊢
    rw [psumL_swap] at h1
    rw [jetMap_unique _ h1 (hR.1 (swapI I)), cε_swap])
  intro j j' h1 h2 h3
  refine (hC j j' h1 h2 h3).trans ?_
  congr 1
  show _ = res le_top (unitΓ (1 : (Jet ℂ (Fin 2 × Fin g) m)ˣ)⁻¹) * _
  rw [inv_one, unitΓ, map_one]
  have : ∀ (X : Scheme.{0}) (U : X.Opens), res (le_top : U ≤ ⊤) (1 : Γ(X, ⊤)ˣ) = 1 := fun X U => map_one _
  rw [this]
  exact (_root_.one_mul _).symm

end GlobalTheory.AnVal.Sym
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_analyticFrame_jetPair_isAnE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∃ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e := by
  first | exact @GlobalTheory.AnVal.exists_isAnE | exact GlobalTheory.AnVal.exists_isAnE | (intros; apply GlobalTheory.AnVal.exists_isAnE <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section MulN

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
  (Φ : AnFr A L x0 g)

theorem mulN_e_zero : Φ.e 0 = 1 := by
  have h := Φ.e_add 0 0
  rw [add_zero] at h
  simpa using h

theorem mulN_e_nsmul (N : ℕ) (z : Fin g → ℂ) : Φ.e ((N : ℂ) • z) = Φ.e z ^ N := by
  induction N with
  | zero => simp [mulN_e_zero Φ]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

omit [IsCommMonObj A] in
theorem mulN_comp {Z : Over S} (y : Z ⟶ A) (N : ℕ) : y ≫ mulA A N = y ^ N := by
  unfold mulA
  induction N with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

omit [IsCommMonObj A] in
theorem mulN_eSec (N : ℕ) : eSec A ≫ (mulA A N).left = eSec A := by
  have h1 : (η : 𝟙_ (Over S) ⟶ A) = 1 := by
    have h0 : (1 : 𝟙_ (Over S) ⟶ A) = toUnit _ ≫ η := rfl
    simpa using h0.symm
  have h := mulN_comp (η : 𝟙_ (Over S) ⟶ A) N
  rw [h1, one_pow] at h
  unfold eSec
  rw [← Over.comp_left, h1, h]

theorem mulN_genRd (N : ℕ)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (hg : α₀.IsGen) (hn : IsNormMul A L.L L.rig N α₀) (z : Fin g → ℂ) :
    Φ.GenRd ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1] α₀ (Φ.e z).left ![z, (N : ℂ) • z] 1 := by
  have hφ : ∀ (z : Fin g → ℂ) (k : Fin 2), (Φ.e z).left ≫ (![𝟙 A.left, (mulA A N).left] : Fin 2 → (A.left ⟶ A.left)) k
      = (Φ.e ((![LinearMap.id, (N : ℂ) • LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k z)).left := by
    intro z k
    fin_cases k
    · simp
    · simp [← Over.comp_left, mulN_comp, mulN_e_nsmul]
  have hper : ∀ gm ∈ Φ.lat, (∀ z, (Φ.e (z + gm)).left = (Φ.e z).left) ∧
      ∀ k, (![LinearMap.id, (N : ℂ) • LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k gm ∈ Φ.lat := by
    intro gm hgm
    refine ⟨fun z => by rw [Φ.genMove_e_per z gm hgm], fun k => ?_⟩
    fin_cases k
    · simpa using hgm
    · simpa [Nat.cast_smul_eq_nsmul] using Φ.lat.nsmul_mem hgm N
  have hherm : ∀ z w, ∑ k, (((![(N : ℤ) ^ 2, -1] : Fin 2 → ℤ) k : ℤ) : ℂ) *
      hermForm Φ.Hm ((![LinearMap.id, (N : ℂ) • LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k z)
        ((![LinearMap.id, (N : ℂ) • LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k w) = 0 := by
    intro z w
    simp [Fin.sum_univ_two, hermForm]
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    ring
  obtain ⟨⟨v, -, hv⟩, -⟩ := GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel S A L x0 g Φ A.left (Fin 2) ![𝟙 A.left, (mulA A N).left]
    ![(N : ℤ) ^ 2, -1] α₀ hg g (fun z => (Φ.e z).left) ![LinearMap.id, (N : ℂ) • LinearMap.id] Φ.lat Φ.hol hφ
    Φ.span hper hherm
  have hrig : Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => 1) L.rig x0 (fun _ => 0) 1 := by
    refine ⟨fun _ => (Φ.genMove_e_zero_left).symm, fun j hj => ?_⟩
    have hj' := (GlobalTheory.AnValGenCorr.chart_iff _ _ _ _).mp hj PUnit.unit
    rw [← Φ.genMove_e_zero_left] at hj'
    simp
    exact (Φ.fr_0 (j PUnit.unit) hj').symm
  have h0 := hv 0
  rw [Φ.genMove_e_zero_left] at h0
  have h0' := (Φ.genRd_pullGen_iff _ _ α₀ (eSec A) x0 _ v).mpr h0
  have hinv := (GlobalTheory.AnValGenCorr.genRd_corr_mul_inv S A L x0 g Φ S PUnit PUnit _ _ _ _ L.rig L.rig x0 _ _ 1 1
    hrig hrig).2.2.2
  have hpow := Φ.genRd_rigPow ((N : ℤ) ^ 2)
  have hmul := (GlobalTheory.AnValGenCorr.genRd_corr_mul_inv S A L x0 g Φ _ PUnit PUnit _ _ _ _ _ _ x0 _ _ 1 _
    hpow hinv).2.2.1
  have hv1 := (GlobalTheory.AnValGenCorr.genRd_corr_mul_inv S A L x0 g Φ _ (Fin 2) (PUnit ⊕ PUnit) _ _ _ _ _ _ x0 _ _ v _
    h0' hmul).2.1 hn ?ss ⟨fun _ => 0, ?pa, ?pb⟩
  · simp at hv1
    subst hv1
    have hz := hv z
    have hp : (fun k => (![LinearMap.id, (N : ℂ) • LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k z)
        = ![z, (N : ℂ) • z] := by
      funext k
      fin_cases k <;> simp
    rw [hp] at hz
    exact hz
  · unfold LB.SameSum
    intro ψ
    have e0 : eSec A ≫ 𝟙 A.left = eSec A := Category.comp_id _
    have e1 : eSec A ≫ (mulA A N).left = eSec A := mulN_eSec N
    simp [Fin.sum_univ_two, Fintype.sum_sum_type]
    split_ifs <;> simp_all
  · intro k
    fin_cases k <;> simp
  · rintro (_ | _) <;> rfl

end MulN

theorem rd_mulN : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (N : ℕ) (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ^ N).left] ![(N : ℤ) ^ 2, -1])) (s : LB.Sec (LPow A L.L 1 (Over.mk x0))) (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), α₀.IsGen → IsNormMul A L.L L.rig N α₀ → LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd (Over.mk x0) A).left) → IsTwistPull A L.L (mulT A (Over.mk x0) N) (snd (Over.mk x0) A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ → Φ.Rd 1 s θ → Φ.Rd ((N : ℤ) ^ 2) s₁ (fun z => θ ((N : ℂ) • z)) := by
  intro S A _ _ L x0 g Φ N α₀ α s s₁ θ h1 h2 h3 h4 h5
  have hψ : mulT A (Over.mk x0) N ≫ fst (Over.mk x0) A = fst (Over.mk x0) A := by
    unfold mulT
    simp
  have hsnd : ∀ z, (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A).left = (Φ.e z).left := by
    intro z
    unfold ptSecT
    rw [← Over.comp_left]
    simp
  have hsN : (snd (Over.mk x0) A).left ≫ (mulA A N).left = (snd (Over.mk x0) A ^ N).left := by
    rw [← Over.comp_left, mulN_comp]
  have hpt : ∀ z, (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A ^ N).left = (Φ.e ((N : ℂ) • z)).left ∧
      ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ
          LB.wchart L.L ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ^ N).left] j ∧
        valAt' (ptSecT A (Φ.e z)).left
            (LB.wchart L.L ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ^ N).left] j) (α.s j).val =
          (fun _ => (1 : ℂ)) z * (Φ.fr (j 0) z ^ ((N : ℤ) ^ 2) * Φ.fr (j 1) ((N : ℂ) • z) ^ (-(1 : ℤ))) := by
    intro z
    have hqm : (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A ^ N).left = (Φ.e ((N : ℂ) • z)).left := by
      rw [← hsN, ← Category.assoc, hsnd, ← Over.comp_left, mulN_comp, mulN_e_nsmul]
    refine ⟨hqm, ?_⟩
    have hg := mulN_genRd Φ N α₀ h1 h2 z
    rw [← hsnd z] at hg
    have hpull := (Φ.genRd_pullGen_iff _ _ α₀ (snd (Over.mk x0) A).left (ptSecT A (Φ.e z)).left _ 1).mpr hg
    obtain ⟨J, hJ⟩ : ∃ J : ((Over.mk x0 ⊗ A).left ⟶ A.left) → L.L.ι,
        ∀ ψ, ⊤ ≤ ((ptSecT A (Φ.e z)).left ≫ ψ) ⁻¹ᵁ L.L.U (J ψ) :=
      ⟨fun ψ => (GlobalTheory.AnValGenCorr.exists_chart L.L L.3 ((ptSecT A (Φ.e z)).left ≫ ψ)).choose,
        fun ψ => (GlobalTheory.AnValGenCorr.exists_chart L.L L.3 ((ptSecT A (Φ.e z)).left ≫ ψ)).choose_spec⟩
    have hcv := GlobalTheory.AnValGenCorr.corr_val L.L _ _ _ _ α _ h3 J (ptSecT A (Φ.e z)).left hJ
    refine ⟨fun k => J (![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ^ N).left] k),
      (GlobalTheory.AnValGenCorr.chart_iff _ _ _ _).mpr (fun k => hJ _), ?_⟩
    rw [hcv, hpull.2 _ ((GlobalTheory.AnValGenCorr.chart_iff _ _ _ _).mpr (fun k => hJ _))]
    have hs0 : (snd (Over.mk x0) A).left ≫ (![𝟙 A.left, (mulA A N).left] : Fin 2 → (A.left ⟶ A.left)) 0 =
        (snd (Over.mk x0) A).left := Category.comp_id _
    have hs1 : (snd (Over.mk x0) A).left ≫ (![𝟙 A.left, (mulA A N).left] : Fin 2 → (A.left ⟶ A.left)) 1 =
        (snd (Over.mk x0) A ^ N).left := hsN
    simp only [Fin.prod_univ_two, hs0, hs1]
    simp
  have res := AnFr.rd_twistPull S A L x0 g Φ (mulT A (Over.mk x0) N) (snd (Over.mk x0) A ^ N) (lift_snd _ _)
    ((N : ℤ) ^ 2) 1 α s s₁ θ (fun z => (N : ℂ) • z) (fun _ => 1) hψ h4 h5 hpt
  simpa using res

end GlobalTheory.AnVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cubical_reading_one_analyticFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ a b d : Fin g → ℂ, Φ.toAnFr.GenRd (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift (Φ.e a) (lift (Φ.e b) (Φ.e d))).left (fun I => psumL 3 g I ![a, b, d]) 1 := by
  first | exact @GlobalTheory.cubical_reading_one | exact GlobalTheory.cubical_reading_one | (intros; apply GlobalTheory.cubical_reading_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConst_symmetric_square_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ), Φ.ThConst k U x c → (∃ nu : LB.Gen (negLB A L.L k (Over.mk x0)), nu.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (symGen A L.L k U nu) (LB.oneGen L.L)) → c ^ 2 = 1 := by
  first | exact @GlobalTheory.AnValSym.sq_const_eq_one | exact GlobalTheory.AnValSym.sq_const_eq_one | (intros; apply GlobalTheory.AnValSym.sq_const_eq_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem exists_anPt_of_unitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W), letI : Algebra c.F ℂ := σ.toAlgebra; ∃ Φ : AnPt (Xo := Xo) (c := c) (U.un k x) W.g (fun j => relab c σ (W.e j).1) W.e, Φ.OfFam W.F (W.ik k) W.Pm ∧ Φ.Hm = Wu.Hm ∧ Φ.χ = Wu.χl ∧ Φ.fr = Wu.fr ∧ Φ.toAnFr.Rd 1 (U.un k x).s Wu.θ ∧ (∀ kk F θ, Φ.toAnFr.Rd kk F θ ↔ IsFrRd W Wu kk F θ) ∧ (∀ (α : 𝓞 E) a, W.Pm (W.F.t (W.ik k) (α • a)) = tyAct (fun j => relab c σ (W.e j).1) α (W.Pm (W.F.t (W.ik k) a))) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo (U.un k x).x a = Φ.e ((l.M : ℂ)⁻¹ • W.Pm (W.F.t (W.ik k) a)) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W Wu
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have hAH : AHFrame W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr := by
    refine ⟨Wu.herm, Wu.pos, Wu.c1, Wu.c2, Wu.c3, Wu.c4, ?_, Wu.c6⟩
    intro j hj
    rw [← W.pt]
    exact Wu.c5 j hj
  obtain ⟨Φ, hO, hH, hχ, hfr, hlin, hlev⟩ := GlobalTheory.T.analyticFrame_of_appellHumbertFramePeriodFamily E H Dw l Xo c (U.un k x) W.g
    (fun j => relab c σ (W.e j).1) W.e _ W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr W.per W.pt hAH
    (fun ℓ => W.der ℓ.1 ℓ.2)
  have hRd : ∀ kk F θ, Φ.toAnFr.Rd kk F θ ↔ IsFrRd W Wu kk F θ := by
    intro kk F θ
    unfold AnFr.Rd IsFrRd
    constructor
    · intro h j z pt h1 h2 h3
      rw [← hO.1 z] at h1 h3
      rw [← hfr]
      exact h j z pt h1 h2 h3
    · intro h j z pt h1 h2 h3
      rw [hO.1 z] at h1 h3
      rw [hfr]
      exact h j z pt h1 h2 h3
  refine ⟨Φ, hO, hH, hχ, hfr, ?_, hRd, hlin, hlev⟩
  refine (hRd _ _ _).2 ?_
  intro j z pt h1 h2 h3
  rw [zpow_one]
  exact Wu.c7 j z pt h1 h2 h3

end GlobalTheory.AnVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.harmonicValue_baseChange_alt : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S'), FrMap ψ y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = spMap ψ.toRingHom → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b)) = ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) := by
  first | exact @GlobalTheory.harmonicValue_baseChange | exact GlobalTheory.harmonicValue_baseChange | (intros; apply GlobalTheory.harmonicValue_baseChange <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.NetNorms

theorem _root_.GlobalTheory.T.exists_netData_from_half_conjugate_embeddings : ∀ (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (good : (B.KO →+* ℂ) → Prop), (∀ σ, good σ ↔ ¬ good (ComplexEmbedding.conjugate σ)) → (∀ σ F, B.supN j ka (ComplexEmbedding.conjugate σ) F = B.supN j ka σ F) → ∀ (n : (B.KO →+* ℂ) → ℕ) (ev : ∀ σ, Fin (n σ) → (B.Cusp j ka →ₛₗ[σ] ℂ)) (C : ℝ), (∀ σ, good σ → (∀ F, ∃ y, B.supN j ka σ F / 4 ≤ ‖ev σ y F‖) ∧ (∀ y F, ‖ev σ y F‖ ≤ B.supN j ka σ F) ∧ Real.log (16 * (n σ : ℝ)) ≤ C ∧ ∀ (m : ℕ) (F : Fin m → B.Cusp j ka), LinearIndependent B.KO F → LinearIndependent ℂ (fun i => fun y => ev σ y (F i))) → ∃ Nt : NetData B j ka, NetMax Nt ∧ NetLeSup Nt ∧ NetSize Nt C ∧ ∀ σ, NetInj Nt σ := by
  first | exact @GlobalTheory.exists_netData_of_readings_on_half | exact GlobalTheory.exists_netData_of_readings_on_half | (intros; apply GlobalTheory.exists_netData_of_readings_on_half <;> assumption)
end
