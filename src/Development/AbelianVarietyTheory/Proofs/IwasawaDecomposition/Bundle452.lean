module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle111
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle444
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle442
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle446
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle414
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Bare



theorem rows_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {y : Hd R.toRealDat}
    {mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G} {p : PkD D G} (t : PkT F y mA p) : (p.ch true).n ≤ p.Dall := by
  rcases Nat.eq_zero_or_pos p.Dall with h0 | hpos
  · have h := p.D_eq
    rw [h0, Nat.cast_zero, mul_zero] at h
    have h' : (p.ch true).n = 0 := by exact_mod_cast h
    omega
  · rw [t.dall] at hpos ⊢
    have hF := Module.finite_of_finrank_pos hpos
    have h1 := LinearMap.finrank_range_of_inj (t.ch true).jE_inj
    have h2 := Module.finrank_eq_card_basis (p.ch true).bs.toBasis
    rw [Fintype.card_fin] at h2
    rw [← h2, ← h1, (t.ch true).jE_range]
    have hle := Mult.goodPart_le R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0
    have hf := Submodule.finiteDimensional_of_le hle
    refine le_trans ?_ (Submodule.finrank_mono hle)
    exact Submodule.finrank_map_le (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
      (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0)



theorem frames_unit {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {y : Hd R.toRealDat}
    {mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G} {p : PkD D G} (t : PkT F y mA p) (v) : IsUnit (p.Xo v).det := by
  obtain ⟨_, -, h⟩ := t.rr
  exact (h v).2

end GlobalTheory.Mem.R3.Rw.Bare
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.RepCls

theorem reps_classes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F rep → ∃ e : Φ ≃ principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b))) (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0), ∀ π, (principalLevelFrame.rowRepR R.θ (e π)).Iso (rep π) ∧ (∀ b, y.prtE F b (principalLevelFrame.rowRepR R.θ (e π)) = y.prtE F b (rep π)) ∧ (∀ i, y.prtW F i (principalLevelFrame.rowRepR R.θ (e π)) = y.prtW F i (rep π)) ∧ ∃ b, y.prtE F b (rep π) ≠ ⊥ ∧ y.prtE F b (rep π) ≤ (y.C F).EEc b := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y Φ rep hR
  let f : Φ → principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0) :=
    fun π => Quotient.mk _ ⟨rep π, hR.mem π⟩
  have hinj : Function.Injective f := by
    intro π π' h
    exact hR.inj π π' (Quotient.exact h)
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨π, hπ⟩ := hR.all (Formalism.L2.Col.finTypRep _ c) (Formalism.L2.Col.finTypRep_mem _ c)
    refine ⟨π, ?_⟩
    rw [← Quotient.out_eq c]
    exact Quotient.sound hπ
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun π => ?_⟩
  have hiso : (principalLevelFrame.rowRepR R.θ (Equiv.ofBijective f ⟨hinj, hsurj⟩ π)).Iso (rep π) :=
    Formalism.L2.Col.finTypRep_mk_iso ⟨rep π, hR.mem π⟩
  refine ⟨hiso, fun b => ?_, fun i => ?_, ?_⟩
  · unfold Hd.prtE principalLevelFrame.isotE
    rw [principalLevelFrame.isotL_iso _ _ _ _ _ _ (principalLevelFrame.conjT_iso hiso)]
  · unfold Hd.prtW
    rw [principalLevelFrame.isotL_iso _ _ _ _ _ _ hiso]
  · obtain ⟨b, hb⟩ := hR.mem π
    refine ⟨b, ?_, ?_⟩
    · intro h
      apply hb
      unfold Hd.prtE at h
      rw [eq_bot_iff] at h ⊢
      intro x hx
      have h0 := h (Submodule.mem_map_of_mem hx)
      rw [Submodule.mem_bot] at h0 ⊢
      exact (LinearEquiv.map_eq_zero_iff _).1 h0
    · exact Submodule.map_mono inf_le_left

end GlobalTheory.Mem.R3.Rw.RepCls
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.GoodDual

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare Formalism.L2.DIV GlobalTheory.BI

theorem isChar_inv {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) :
    IsChar ℂ ℂ fun g => χ g⁻¹ := by
  obtain ⟨n, ρ, hρ⟩ := h
  let e : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun
  let σ : Representation ℂ G (Fin n → ℂ) :=
    { toFun := fun g => e.conj (ρ.dual g)
      map_one' := by rw [map_one]; exact LinearEquiv.conj_id e
      map_mul' := fun a b => by rw [map_mul]; exact LinearEquiv.conj_comp e _ _ }
  refine ⟨n, σ, fun g => ?_⟩
  have : σ.character g = ρ.dual.character g := LinearMap.trace_conj' _ e
  show χ g⁻¹ = _
  rw [Algebra.algebraMap_self, RingHom.id_apply, this, Representation.char_dual, hρ, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem goodIdempotent_coeff_inv_eq_coeff {D : D7} {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hI : IdemTie D om) (h : G0g D.nd) :
    D.ntypes.e0.coeff h⁻¹ = D.ntypes.e0.coeff h := by
  obtain ⟨x, rfl⟩ := pull_bijective.2 h
  have e : (pull x)⁻¹ = pull x⁻¹ := rfl
  rw [e, hI, hI]
  exact GlobalTheory.GoodIdemFlip.coeff_goodIdem_flip _ D.host om Set.univ x x⁻¹
    (fun v _ => by rw [Pi.inv_apply]) (fun v hv => absurd (Set.mem_univ v) hv)

theorem goodStable_of_coeff {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (emb : K →+* ℂ)
    (X : Finset (G → K)) (hirr : ∀ χ ∈ X, IsAbsIrrChar χ)
    (hsym : ∀ g, (idemOf X).coeff g⁻¹ = (idemOf X).coeff g) : GoodStable X := by
  classical
  intro χ hχ
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf emb X hirr X
    (fun ψ g => emb (ψ g⁻¹)) (fun ψ hψ => by
      obtain ⟨n, ρ, -, hρ⟩ := GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar emb (hirr ψ hψ)
      exact isChar_inv ⟨n, ρ, hρ⟩) (fun g => by
      rw [← hsym g]

      simp only [idemOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_chiIdem, map_sum, map_mul, map_div₀,
      map_natCast, inv_one, inv_inv, Nat.card_eq_fintype_card]) hχ
  convert hψ using 1
  funext g
  apply emb.injective
  simpa using hψe g⁻¹

end GlobalTheory.Mem.R3.GoodDual

end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem GlobalTheory.AlgWtF.tenRepF_isIrreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → (GlobalTheory.AlgWtF.tenRepF emb lam).IsIrreducible := by
  intro L _ _ _ n ι _ K _ _ emb lam hCM
  have hstab : ∀ W : Submodule K (Formalism.L2.DIV.VV K lam),
      (∀ γ : GQ L n, ∀ w ∈ W, GlobalTheory.AlgWtF.tenRepF emb lam γ w ∈ W) →
      ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W := by
    intro W hW g w hw
    have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ w ∈ W,
        Formalism.L2.DIV.rhoK lam (GlobalTheory.AlgWtF.embGLF emb γ₀) w ∈ W := by
      intro γ₀ hγ₀ w hw
      obtain ⟨γ, rfl⟩ := GlobalTheory.T.unitaryRationalPointMatrixHom_surjective_onto L n γ₀ hγ₀
      exact hW γ w hw
    by_contra hnot
    have hx : ((Formalism.L2.DIV.rhoK lam g w : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K ι n) ∉
        W.map (Formalism.L2.DIV.VV K lam).subtype := by
      rintro ⟨y, hy, hyx⟩
      exact hnot (by rw [show Formalism.L2.DIV.rhoK lam g w = y from Subtype.ext hyx.symm]; exact hy)
    obtain ⟨ψ, hψx, hψW⟩ := Submodule.exists_le_ker_of_notMem hx
    obtain ⟨P, hP⟩ := GlobalTheory.T.weightAction_matrixCoeff_polynomial_in_entries K ι n lam (w : Formalism.L2.DIV.Pol K ι n) ψ
    let f : (ι ⊕ ι) × Fin n × Fin n → (L →+* K) × Fin n × Fin n :=
      fun v => (Sum.elim emb (fun τ => (emb τ).comp (IsCMField.complexConj L : L →+* L)) v.1, v.2)
    have hzero := GlobalTheory.T.zariskiDense_rationalPoints_definiteUnitary_charZero L n K (MvPolynomial.rename f P) ?_
    · obtain ⟨B, hBc, hBe⟩ := GlobalTheory.T.exists_unitary_extension_of_cmType_family L n ι K emb hCM g
      have h0 := hzero B hBc
      rw [MvPolynomial.eval_rename] at h0
      apply hψx
      have h1 : ((Formalism.L2.DIV.rhoK lam g w : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K ι n) =
          Formalism.L2.DIV.actP lam g w := rfl
      rw [h1, hP g, ← h0]
      refine congrArg (fun y => MvPolynomial.eval y P) ?_
      funext v
      rcases v with ⟨τ | τ, a, b⟩
      · simp [f, hBe]
      · simp only [f, Function.comp_apply, Sum.elim_inr]
        rw [hBc (emb τ), hBe τ]
        rfl
    · intro γ₀ hγ₀
      rw [MvPolynomial.eval_rename]
      have h2 := hrat γ₀ hγ₀ w hw
      have h3 : ψ (Formalism.L2.DIV.actP lam (GlobalTheory.AlgWtF.embGLF emb γ₀) w) = 0 :=
        hψW ⟨_, h2, rfl⟩
      rw [hP] at h3
      rw [← h3]
      refine congrArg (fun y => MvPolynomial.eval y P) ?_
      funext v
      rcases v with ⟨τ | τ, a, b⟩
      · simp [f, GlobalTheory.AlgWtF.embGLF]
      · have hinv : (((γ₀⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) =
            ReciprocityTheory.Aut.conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
          Units.inv_eq_of_mul_eq_one_right hγ₀
        simp only [f, Function.comp_apply, Sum.elim_inr, GlobalTheory.AlgWtF.embGLF, MonoidHom.pi_apply, ← map_inv,
          Matrix.GeneralLinearGroup.map_apply, hinv, ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply,
          RingHom.comp_apply]
  have hsimple : ∀ W : Submodule K (Formalism.L2.DIV.VV K lam),
      (∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    GlobalTheory.T.coefficientSpace_stable_eq_bot_or_top K ι n lam (fun τ => GlobalTheory.T.nablaSq_endomorphism_eq_sum_GL_operators K n (lam τ) (GlobalTheory.T.dualWeylModule_simple_charZero K n (lam τ)))
  haveI hnt : Nontrivial (Formalism.L2.DIV.VV K lam) := GlobalTheory.T.nontrivial_weylCoefficientSpace K ι n lam
  haveI : Nontrivial (Subrepresentation (GlobalTheory.AlgWtF.tenRepF emb lam)) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    obtain ⟨x, hx⟩ := exists_ne (0 : Formalism.L2.DIV.VV K lam)
    have hxt : x ∈ (⊤ : Subrepresentation (GlobalTheory.AlgWtF.tenRepF emb lam)).toSubmodule := trivial
    rw [← h'] at hxt
    exact hx hxt
  refine { eq_bot_or_eq_top := fun W => ?_ }
  rcases hsimple W.toSubmodule (hstab W.toSubmodule (fun γ w hw => W.apply_mem_toSubmodule γ hw)) with h | h
  · left; exact Subrepresentation.ext h
  · right; exact Subrepresentation.ext h
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem mem_HHa_span {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    {P : MvPolynomial (Letter T r n) k} (h : P ∈ Submodule.span k (HHa r n k cc isX a)) : P ∈ HHa r n k cc isX a := by
  classical
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩
  | add x y _ _ hx hy =>
    refine ⟨add_mem hx.1 hy.1, fun σ i i' hi t => by rw [map_add (f := _), hx.2.1 σ i i' hi t, hy.2.1 σ i i' hi t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx.2.2 m h
    · exact hy.2.2 m h
  | smul c x _ hx =>
    exact ⟨Submodule.smul_mem _ c hx.1, fun σ i i' hi t => by rw [map_smul, hx.2.1 σ i i' hi t],
      fun m hm => hx.2.2 m (MvPolynomial.support_smul hm)⟩

section Marks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {r : ℕ} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)}

theorem isMark_sign (h : IsMark l L mk) (ε : ℤˣ) : IsMark l L ((ε : ℤ) • mk) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using h
  · have e : ∀ a, (((-1 : ℤˣ) : ℤ) • mk) a = -mk a := fun a => by simp
    refine ⟨fun a => by rw [e]; exact neg_mem (h.mem a), fun a ha ⟨u, hu, hu'⟩ => h.inj a ha ⟨-u, neg_mem hu, ?_⟩,
      fun v hv => ?_⟩
    · rw [smul_neg, ← hu', e, neg_neg]
    · obtain ⟨a, ha, u, hu, hu'⟩ := h.surj v hv
      exact ⟨-a, neg_mem ha, u, hu, by rw [e, map_neg, neg_neg, hu']⟩


open CategoryTheory MonObj in
theorem marked_of_congr {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

end Marks

theorem kernel_value {D : D7} {S T : HSp D} {r g : ℕ} {hr : T.rank = r} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {X : Data D.host.E r} {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    (hS : IsSet ψ θ S T hr X eT bas) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {q : ℕ} (hp : X.p0 = q) {Z : Fam T} (hZ : IsONeg T q Z) {h : GA D S} (hh : h ∈ GfC S)
    {γ : GA D T} (hγ : γ ∈ GQ T) (k : GA D T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) {φ : TF S.rank g} (hφ : GlobalTheory.SW.IsSB φ)
    (hz : Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ (γ * k) Z)) φ (om (h, γ * k) f)) {q0 : ℕ} (hq : X.p0 + q0 = r) :
    thetaKO om h k (fv ψ θ S T q Z f Q) = thP X hq bas idx φ (toP S hr eT hq Q) (frOf hr eT (mvZ θ (γ * k) Z)) := by
  subst hp
  obtain ⟨hZ', hc, -⟩ := (GlobalTheory.T.orthonormalNegFirstFamily_frame_cartan_move D S T r g hr ψ θ X eT bas idx hS Z hZ).2.2.2.2 (γ * k)
  have h1 := GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hh
  obtain ⟨h2, h3⟩ := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hS.2.1 (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (cartZ T X.p0 Z) (cartZ T X.p0 (mvZ θ (γ * k) Z)) Z (mvZ θ (γ * k) Z) h (γ * k)
    (fun τ => by rw [h1]) hc (fun τ => by rw [h1, Matrix.mul_one]) (fun _ => rfl) f hf Q
  have h4 := (((GlobalTheory.T.adelicTheta_of_testFunction_exists_laws_fockVectors D S T r g hr ψ θ X eT bas idx hS _ hZ').1 φ hφ).2 _ hz).2.2.2.2.2.2 q0 hq Q
  rw [← h4]
  have h5 := hom.om_aut 1 (one_mem _) γ hγ _ (hom.om_pres (h, k) _ h2)
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, _root_.one_mul, h3] at h5
  exact h5.symm

theorem isThetaFunO_of_isVacO {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {sS : Fam S} {sT : Fam T}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : IsThetaFunO ψ S T f := h.2.2

theorem thR_smul_of_prod {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {x : Frame X.Ψ r} {v : TF n g}
    {th : (Fin g → ℂ) → ℂ} {κ : ℂ} (h : ∀ z : Fin n → Fin g → ℂ, ∏ b, th (z b) = κ * thA X bas idx v x z) (a : ℂ)
    (w : Ker.WR X n) :
    a * (Ker.gaussR X bas idx x (Ker.zR X idx x w) * ∏ b, th (Ker.zR X idx x w b)) = Ker.thR X bas idx ((a * κ) • v) x w := by
  rw [h]
  simp only [Ker.thR, thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, tsum_mul_left]
  ring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}

def TermAt (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (ε : ℤˣ) : Prop :=
  ∀ (t : Unit) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i A.μ0 h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) → ∀ (k : O.Cl' t) (g' : GA D (Wc D i)) (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r), IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT bas → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → ∀ L : Lt D.host.E D.R.r, SelfD X L → latW (rank_Wc i) L = latG (Wc D i) g' → ∀ v : TF (Vc D i).rank g, IsVac X bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) L) v → ∀ a : ℂ, Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (baseZ R i))) (a • v) (R.ωP i A.μ0 (1, g') (R.vacP i)) → ∀ mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), (∀ b, mk₂ b ∈ L) → MarkAd (rank_Wc i) (O.dδ t).l₂ (iotaW T i) g' mk₂ → ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots (O.dδ t).l₂ L ((ε : ℤ) • mk₂) (O.Nc t k) Y → GlobalTheory.SW.IsSB (gphi X bas (T.Q.H.w0 : D.host.E) (O.La t k).La L v (fun q => inC O.c' (O.w t k q)) Y) ∧ Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (baseZ R i))) ((a * inC O.c' (O.ep t k * ((((O.La t k).mIdx (O.Nc t k) D.R.r : O.c'.F))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ t).l₂) : O.c'.F))⁻¹ * ((O.La t k).zCard (O.Nc t k) D.R.r : O.c'.F)))) • gphi X bas (T.Q.H.w0 : D.host.E) (O.La t k).La L v (fun q => inC O.c' (O.w t k q)) Y) (R.ωP i A.μ0 (h k, g') (R.vP i A.μ0))

def IoAt (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ)
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : Prop :=
  ∀ x : VsV D i O.c'.F, ∃ Q : PolF D (Wc D i).rank (Vc D i).rank, (∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' x)) = fv R.ψ R.θ (Vc D i) (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (baseZ R i) f Q) ∧ ∀ (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ) (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))), (∀ ρ, (eT ρ).1 = tauE D ρ) → MvPolynomial.C ph * toP (Vc D i) (rank_Wc i) eT Dc.hr Q = MvPolynomial.C ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * MvPolynomial.rename Dc.eL (MvPolynomial.map (inC O.c') (O.io x))

def CovAt (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (c0 : ℂ) : Prop :=
  ∀ (ε : ℤˣ) (t : Unit) (g' : GA D (Wc D i)) (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))), IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT bas → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → Matched T.Q.c O.s0 X idx e → ∀ L : Lt D.host.E D.R.r, SelfD X L → latW (rank_Wc i) L = latG (Wc D i) g' → ∀ mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), (∀ b, mk₂ b ∈ L) → MarkAd (rank_Wc i) (O.dδ t).l₂ (iotaW T i) g' mk₂ → letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra; ∀ (y₂ : FrPt (O.dδ t).Xo₂ (O.dδ t).c₂ ℂ) (A₂ : AnFib X bas idx e (frOf (rank_Wc i) eT (mvZ R.θ g' (baseZ R i))) L y₂), A₂.Marked ((ε : ℤ) • mk₂) → evR (O.dδ t).Xo₂ (O.dδ t).c₂ (O.dδ t).cδ y₂ = c0 * ((O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g')) : ℂˣ) : ℂ)

theorem io_mem (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (x : VsV D i O.c'.F) :
    O.io x ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank O.c'.F ComplexEmbedding.conjugate (InPsi T.Q.H)
      (fun τ j => wtA (κ i) (τ, j)) :=
  hP.io.2.elim fun _ h => mem_HHa_span _ _ _ _ _ _ (h.2.2.1 ▸ LinearMap.mem_range_self _ _)

end GlobalTheory.OneMapRef

end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe.IsoRe

variable {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (h' : FinX (reY Z Y))

def eP (u u' : D.what₂.Word) : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u') :=
  (rp_iso_pair D Z X Y h h' u u').choose



def sIsoRe : SIso (sOf h) ((@sOf (reD D Z) (@reX D Z X) (@reY D Z X Y) h')) where
  cd := (by with_unfolding_all exact ((Eq.refl (Formalism.L2.SG.PairVal.cdScaleOf D)) :))
  del := (by with_unfolding_all exact ((Eq.refl D.s.Del) :))
  letter := (by with_unfolding_all exact ((Eq.refl D.s.letter) :))
  eHH := (by with_unfolding_all exact ((eHHre Z X) :))
  eCu := (by with_unfolding_all exact ((eCure Z h h') :))
  Pu_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D Z X Y h h').1 :))
  volN := (by with_unfolding_all exact ((Eq.refl Y.volN) :))
  volH := (by with_unfolding_all exact ((Eq.refl Y.volH) :))
  eT := (by with_unfolding_all exact ((eRT Z Y) :))
  aTerm_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D Z X Y h h').2.2 :))
  isId := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).1 :))
  inS := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.1 :))
  relevant := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.1 :))
  FeqF := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.1 :))
  Gterm := fun {u u'} t => Subtype.ext (a1 := (sOf h).Gterm t) (a2 := (by with_unfolding_all exact (((sOf h').Gterm (eRT Z Y u u' t)) :))) ((by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.1 :)))
  atP := fun p => (by with_unfolding_all exact ((Formalism.L2.S.LocIso.refl (Formalism.L2.S.locC D p)) :))
  ePl := (by with_unfolding_all exact ((Equiv.refl (Formalism.MainNotions.S.LocalSplitGroups.PlF D)) :))
  BBne := fun {u u'} t q => (by with_unfolding_all exact ((((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.1 q) :))
  generic := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.1 :))
  eP := (by with_unfolding_all exact ((eP Z h h') :))
  pfst := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).1) :))
  psnd := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.1) :))
  s0 := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.1) :))
  scalarPair := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.2.1) :))
  pval := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.2.2) :))
  ptOf := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.2.1 :))
  cTerm := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.2.2.2 :))
  massPair := fun {u u'} p => (by with_unfolding_all exact (((((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 ((p.1.1) : RT Y u u')).2.2.2.2.2.2.2.2.1).trans
      (congrArg Formalism.L2.SG.PairVal.massTerm ((rp_iso_pair D Z X Y h h' u u').choose_spec ((p) : RP Y u u')).1)) : _))
  meanCount := (by with_unfolding_all exact ((funext fun u => funext fun u' => funext fun w => (GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').2 w :
      (fun (u u' : D.what₂.Word) w => Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w) =
        fun (u u' : D.what₂.Word) w => Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w) :))

end GlobalTheory.Mem.SRe.IsoRe

namespace GlobalTheory.Mem.SRe



theorem sIso_reD : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y)),
    ∃ e : SIso (sOf h) ((@sOf (reD D Z) (@reX D Z X) (@reY D Z X Y) h')), HEq e.eHH (eHHre Z X) ∧ ∀ u, HEq (e.eCu u) (eCure Z h h' u) :=
  fun _ Z X _ h h' => ⟨IsoRe.sIsoRe Z h h', (by with_unfolding_all exact ((HEq.refl (eHHre Z X)) :)),
    fun u => (by with_unfolding_all exact ((HEq.refl (eCure Z h h' u)) :))⟩

end GlobalTheory.Mem.SRe
end
end
