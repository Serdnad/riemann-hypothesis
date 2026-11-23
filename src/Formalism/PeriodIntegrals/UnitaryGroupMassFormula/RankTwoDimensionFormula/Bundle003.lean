module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DimFormCOfSteps
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem tr_repr_eq (y : (VS D).V) (i : Fin X.B.I.n) : X.bas.repr y i = X.ιE (X.crd y i) := by
  exact (X.ιE.apply_symm_apply (X.bas.repr y i)).symm

theorem tr_crd_injective : Function.Injective X.crd := by
  intro a b h
  apply X.bas.repr.injective
  ext i
  rw [tr_repr_eq X a i, tr_repr_eq X b i, h]

def trLin (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  Matrix.toLin X.bas X.bas (M.map X.ιE)

theorem tr_crd_lin (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (trLin X M y) = M *ᵥ X.crd y := by
  have h := LinearMap.toMatrix_mulVec_repr X.bas X.bas (Matrix.toLin X.bas X.bas (M.map X.ιE)) y
  rw [LinearMap.toMatrix_toLin] at h
  funext i
  apply X.ιE.injective
  rw [← tr_repr_eq]
  show X.bas.repr (Matrix.toLin X.bas X.bas (M.map X.ιE) y) i = _
  rw [← h]

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, tr_repr_eq]

theorem tr_lin_mul (M N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    (trLin X M).comp (trLin X N) = trLin X (M * N) := by
  have hm : (M * N).map X.ιE = M.map X.ιE * N.map X.ιE := by
    ext i j

    simp [Matrix.mul_apply, map_sum, map_mul]
  unfold trLin
  rw [hm, Matrix.toLin_mul X.bas X.bas X.bas]

theorem tr_lin_one : trLin X 1 = LinearMap.id := by
  unfold trLin
  rw [Matrix.map_one _ (map_zero X.ιE) (map_one X.ιE), Matrix.toLin_one]

def trEquiv (M : GL (Fin X.B.I.n) X.B.I.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (trLin X (M : Matrix _ _ _)) (trLin X ((M⁻¹ : GL _ _) : Matrix _ _ _))
    (by rw [tr_lin_mul, Units.mul_inv, tr_lin_one])
    (by rw [tr_lin_mul, Units.inv_mul, tr_lin_one])

theorem tr_crd (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (trEquiv X M y) = (M : Matrix _ _ _) *ᵥ X.crd y := tr_crd_lin X _ y

theorem tr_af_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
  haveI : Nonempty (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := ⟨v⟩
  first
    | infer_instance
    | exact (RestrictedProduct.evalRingHom _ v).domain_nontrivial
    | exact ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x => x.1 v) h)⟩⟩

attribute [local instance] tr_af_nontrivial

theorem tr_star (a : X.B.I.E) : star (X.ιE a) = X.ιE (star a) :=
  (Formalism.BasicNotions.bridge_star_holds D.R D.host _).trans (X.ιE_conj a).symm

theorem tr_hT (x y : (VS D).V) :
    (VS D).hT x y = X.ιE (star (X.crd x) ⬝ᵥ (X.B.I.J *ᵥ X.crd y)) := by
  conv_lhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
  smul_eq_mul, starRingEnd_apply, tr_repr_eq, tr_star, ← X.J_eq, dotProduct, Matrix.mulVec,
  Pi.star_apply, map_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem tr_isom (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    trEquiv X M ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  have hM' : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hM
  have hH : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ =
      Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) := by
    ext i j
    rfl
  show ∀ a b, (VS D).hT (trEquiv X M a) (trEquiv X M b) = (VS D).hT a b
  intro a b
  rw [tr_hT, tr_hT, tr_crd, tr_crd]
  congr 1
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hH, hM']

theorem transport_holds : Transport := by
  intro D X u γ
  have hG : (γ : X.B.I.GA) ∈ X.B.I.GFset := (Subgroup.mem_inf.1 γ.2).1
  obtain ⟨M, hM, -, hf⟩ := hG
  have hH : ∀ y ∈ fixSet X u, X.B.I.fmat (iotaF X u γ : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y :=
    (iotaF X u γ).2
  have hcoe : ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl
  have hinc : ∀ v, X.B.I.fmat (γ : X.B.I.GA).2 *ᵥ incl X.B.I v =
      incl X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ v) := by
    intro v
    rw [hf]
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm
  have hfixc : ∀ y ∈ fixSet X u, (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y = y := by
    intro y hy
    have h1 := hH y hy
    rw [hcoe, hinc] at h1
    funext i
    exact Formalism.UG.P.inclE_injective _ _ _ (congrFun h1 i)
  have hfix : ∀ y, X.crd y ∈ fixSet X u → trEquiv X M y = y := by
    intro y hy
    apply tr_crd_injective X
    rw [tr_crd, hfixc _ hy]
  refine ⟨trEquiv X M, ⟨tr_isom X M hM, fun j => ?_, ?_⟩, fun h => ?_⟩
  · show Submodule.map _ (Submodule.span _ _) = Submodule.span _ _
    rw [Submodule.map_span, Set.image_image, X.Fu_e]
    congr 1
    apply Set.image_congr
    intro a _
    exact hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
  · rw [X.flagZVector]
    exact hfix _ (Or.inr rfl)
  · ext y
    have key : X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ *ᵥ incl X.B.I (X.crd y) =
        incl X.B.I (X.crd ((trEquiv X M).symm y)) := by
      have e1 : incl X.B.I (X.crd y) =
          X.B.I.fmat (iotaF X u γ : X.B.I.Gf) *ᵥ incl X.B.I (X.crd ((trEquiv X M).symm y)) := by
        rw [hcoe, hinc, ← tr_crd, LinearEquiv.apply_symm_apply]
      rw [e1, Matrix.mulVec_mulVec]
      have e2 : X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ * X.B.I.fmat (iotaF X u γ : X.B.I.Gf) =
          X.B.I.fmat (((iotaF X u γ : X.B.I.Gf))⁻¹ * (iotaF X u γ : X.B.I.Gf)) := rfl
      rw [e2, inv_mul_cancel]
      exact Matrix.one_mulVec _
    have e : ((iotaF X u γ : X.B.I.Gf) * h * X.xu u)⁻¹ = (h * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf)⁻¹ := by
      group
    rw [LinearEquiv.image_eq_preimage_symm]
    simp only [latS, Set.mem_ofPred_eq, Set.mem_preimage]
    rw [e]
    have ef : X.B.I.fmat ((h * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf)⁻¹) =
        X.B.I.fmat (h * X.xu u)⁻¹ * X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ := rfl
    rw [ef, ← Matrix.mulVec_mulVec, key]

end PI.UnitaryDimensionFormula
end
end

section

noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def cj {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : Hfin X u) : X.B.I.Gf :=
  (X.xu u)⁻¹ * (s : X.B.I.Gf) * X.xu u

def UniSub : Prop :=
  ∀ (F : Type) [Field F] (k : ℕ) (x y : GL (Fin k) F), Formalism.L2.SG.GGMirabolic.IsUni k x →
    Formalism.L2.SG.GGMirabolic.IsUni k y →
      Formalism.L2.SG.GGMirabolic.IsUni k (x * y) ∧ Formalism.L2.SG.GGMirabolic.IsUni k x⁻¹

def IdxHom : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    levi Y.TR (1 : X.B.I.Gf) = 1 ∧
    (∀ s t : Hfin X u, cj X u s ∈ X.B.I.Kset → cj X u t ∈ X.B.I.Kset →
      levi Y.TR (cj X u (s * t)) = levi Y.TR (cj X u s) * levi Y.TR (cj X u t)) ∧
    ∀ s : Hfin X u, cj X u s ∈ X.B.I.Kset → s ∈ Ku X u Y.hK →
      ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi Y.TR (cj X u s) v)

def IdxSurj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ A : Iof Y.TR, ∃ s : Hfin X u, cj X u s ∈ X.B.I.Kset ∧ levi Y.TR (cj X u s) = A

variable {D : D7} {X : HidaSetting D}

theorem kset_inv {m : X.B.I.Gf} (hm : m ∈ X.B.I.Kset) : m⁻¹ ∈ X.B.I.Kset := by
  simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hm ⊢
  simpa using (Formalism.UG.stabGL X.B.I.Lf).inv_mem hm

theorem cj_inv (u : D.what₂.Word) (s : Hfin X u) : cj X u s⁻¹ = (cj X u s)⁻¹ := by
  simp [cj, mul_assoc]

theorem cj_one (u : D.what₂.Word) : cj X u 1 = 1 := by
  simp [cj]

theorem latS_mul_K {u : D.what₂.Word} (h : X.B.I.Gf) (s : Hfin X u) (hs : cj X u s ∈ X.B.I.Kset) :
    latS X u (h * (s : X.B.I.Gf)) = latS X u h := by
  ext y
  simp only [latS, Set.mem_setOf_eq]
  have e : (h * (s : X.B.I.Gf) * X.xu u)⁻¹ = (cj X u s)⁻¹ * (h * X.xu u)⁻¹ := by
    simp only [cj]; group
  have hm := kset_inv hs
  simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hm
  have e2 : X.B.I.fmat ((cj X u s)⁻¹ * (h * X.xu u)⁻¹) =
      X.B.I.fmat (cj X u s)⁻¹ * X.B.I.fmat (h * X.xu u)⁻¹ := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  rw [e, e2, ← Matrix.mulVec_mulVec]
  exact (hm _).symm

def Uprod (hU : UniSub) (TR : TypedRed X) : Subgroup (Iof TR) where
  carrier := {x | ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (x v)}
  one_mem' := fun _ => Formalism.L2.SG.GGMirabolic.isUni_one
  mul_mem' := fun {a b} ha hb v => (hU _ _ _ _ (ha v) (hb v)).1
  inv_mem' := fun {a} ha v => (hU _ _ _ _ (ha v) (ha v)).2

theorem card_Uprod (hU : UniSub) (TR : TypedRed X) :
    Nat.card (Uprod hU TR) = ∏ v, Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k := by
  have e : ↥(Uprod hU TR) ≃ ∀ v, {x : GL (Fin D.R.k) (TR.Fq v) // Formalism.L2.SG.GGMirabolic.IsUni D.R.k x} :=
    Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi]
  rfl

theorem card_Iof (TR : TypedRed X) :
    Nat.card (Iof TR) = ∏ v, Fintype.card (GL (Fin D.R.k) (TR.Fq v)) := by
  rw [Nat.card_pi]
  simp [Nat.card_eq_fintype_card]

theorem gamma_one_eq_card (hU : UniSub) (TR : TypedRed X) :
    Gam1 TR = (Nat.card (Iof TR ⧸ Uprod hU TR) : ℝ) := by
  have hU0 : ∀ v, (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) ≠ 0 := by
    intro v
    have : Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k ≠ 0 := by
      unfold Formalism.L2.SG.GGMirabolic.cardU
      exact Nat.card_ne_zero.mpr ⟨⟨⟨1, Formalism.L2.SG.GGMirabolic.isUni_one⟩⟩, inferInstance⟩
    exact_mod_cast this
  have h1 : ∀ v, Formalism.L2.SG.GGMirabolic.gam (TR.psi0 v) (1 : GL (Fin D.R.k) (TR.Fq v)) =
      (((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) : ℝ) : ℂ) := by
    intro v
    have hp : Formalism.L2.SG.GGMirabolic.psiNat (TR.psi0 v) (1 : GL (Fin D.R.k) (TR.Fq v)) = 1 := by
      rw [Formalism.L2.SG.GGMirabolic.psiNat, if_pos Formalism.L2.SG.GGMirabolic.isUni_one, Formalism.L2.SG.GGMirabolic.psiU]
      convert AddChar.map_zero_eq_one (TR.psi0 v)
      unfold Formalism.L2.SG.GGMirabolic.superdiag
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      split_ifs with hj
      · show (1 : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j = 0
        exact Matrix.one_apply_ne (fun hij => by subst hij; omega)
      · rfl
    rw [Formalism.L2.SG.GGMirabolic.gam]
    simp only [mul_one, mul_inv_cancel, hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast
    rw [div_eq_inv_mul]
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Uprod hU TR)
  rw [card_Iof, card_Uprod] at hq
  have hq' : (Nat.card (Iof TR ⧸ Uprod hU TR) : ℝ) =
      (∏ v, (Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ)) /
        ∏ v, (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) := by
    rw [eq_div_iff (Finset.prod_ne_zero_iff.mpr fun v _ => hU0 v)]
    exact_mod_cast hq.symm
  rw [hq', ← Finset.prod_div_distrib]
  simp only [Formalism.L2.SG.TermOp.Gam1, Formalism.L2.SG.GGMirabolic.gamProd, Pi.one_apply, h1]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]

theorem indexGe_of (hU : UniSub) (hH : IdxHom) (hS : IdxSurj) : IndexGe := by
  intro D X Y u hT Λ hΛ
  classical
  have hlat0 : latS X u (((Y.cs u).h ((Y.cs u).base Λ) : Hfin X u) : X.B.I.Gf) = (Λ : Set (VS D).V) := by
    rw [← lamOf_eq_latS (Y.cs u) ((Y.cs u).base Λ), (Y.cs u).base_lam Λ hΛ]
  have hKmul : ∀ m m' : X.B.I.Gf, m ∈ X.B.I.Kset → m' ∈ X.B.I.Kset → m * m' ∈ X.B.I.Kset := by
    intro m m' hm hm'
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hm hm' ⊢
    simpa using (Formalism.UG.stabGL X.B.I.Lf).mul_mem hm hm'
  have cj_mul : ∀ a b : Hfin X u, cj X u (a * b) = cj X u a * cj X u b := by
    intro a b
    simp only [cj, Subgroup.coe_mul]
    group
  obtain ⟨hl1, hlmul, hluni⟩ := hH D X Y u hT
  choose s hsK hsA using hS D X Y u hT
  let e : Fin (Nat.card (Iof Y.TR ⧸ Uprod hU Y.TR)) ≃ (Iof Y.TR ⧸ Uprod hU Y.TR) :=
    (Finite.equivFin _).symm
  refine ⟨Nat.card (Iof Y.TR ⧸ Uprod hU Y.TR),
    fun i => (Y.cs u).h ((Y.cs u).base Λ) * s (Quotient.out (e i)), ?_, ?_, ?_⟩
  · exact le_of_eq (gamma_one_eq_card hU Y.TR)
  · intro i
    rw [Subgroup.coe_mul, latS_mul_K _ _ (hsK _), hlat0]
  · intro i j hij
    have hAi := hsA (Quotient.out (e i))
    have hAj := hsA (Quotient.out (e j))
    have hKa := hsK (Quotient.out (e i))
    have hKb := hsK (Quotient.out (e j))
    set a := s (Quotient.out (e i)) with ha
    set b := s (Quotient.out (e j)) with hb
    have hab : a⁻¹ * b ∈ Ku X u Y.hK := by
      have : ((Y.cs u).h ((Y.cs u).base Λ) * a)⁻¹ * ((Y.cs u).h ((Y.cs u).base Λ) * b) = a⁻¹ * b := by
        group
      rwa [this] at hij
    have hKai : cj X u a⁻¹ ∈ X.B.I.Kset := by
      rw [cj_inv]
      exact kset_inv hKa
    have hKab : cj X u (a⁻¹ * b) ∈ X.B.I.Kset := by
      rw [cj_mul]
      exact hKmul _ _ hKai hKb
    have hinv : levi Y.TR (cj X u a⁻¹) = (levi Y.TR (cj X u a))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← hlmul _ _ hKai hKa, inv_mul_cancel, cj_one, hl1]
    have hmem : (Quotient.out (e i))⁻¹ * Quotient.out (e j) ∈ Uprod hU Y.TR := by
      have h2 := hluni _ hKab hab
      rw [hlmul _ _ hKai hKb, hinv, hAi, hAj] at h2
      exact h2
    apply e.injective
    rw [← QuotientGroup.out_eq' (e i), ← QuotientGroup.out_eq' (e j)]
    exact QuotientGroup.eq.mpr hmem

end PI.UnitaryDimensionFormula
end
end
