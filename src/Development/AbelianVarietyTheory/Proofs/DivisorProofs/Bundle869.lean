module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSimpleRingOfIsSemisimpleRing
public import GroundTheory.Brauer.BaseChangeCSA
import GroundTheory.Brauer.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle836
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle838
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UPel.HT.MoritaChar0

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

theorem actF_mem_algO (x : D.F) : ((D.actF x : D.endO) : Module.End ℚ D.VQ) ∈ D.algO := by

  rw [← (integralBasis D.F).sum_repr x, map_sum]
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [map_smul, Subalgebra.coe_smul, integralBasis_apply, D.actF_coe, D.coe_actInt]
  exact Subalgebra.smul_mem _ (D.actQ_mem_algO _) _

def toAlgO : D.F →+* D.algO :=
  (D.endO.val.toRingHom.comp D.actF.toRingHom).codRestrict D.algO (actF_mem_algO D)

theorem toAlgO_comm (x : D.F) (a : D.algO) : toAlgO D x * a = a * toAlgO D x := by
  have h : ((D.actF x : D.endO) : Module.End ℚ D.VQ) ∈ Subalgebra.centralizer ℚ (D.algO : Set (Module.End ℚ D.VQ)) := by
    rw [D.centralizer_algO]; exact (D.actF x).2
  rw [Subalgebra.mem_centralizer_iff] at h
  exact Subtype.ext (h a a.2).symm

def algebraFAlgO : Algebra D.F D.algO := (toAlgO D).toAlgebra' (toAlgO_comm D)

attribute [local instance] algebraFAlgO

instance towerQFAlgO : IsScalarTower ℚ D.F D.algO :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

instance finFAlgO : FiniteDimensional D.F D.algO := Module.Finite.of_restrictScalars_finite ℚ D.F D.algO

instance centralFAlgO : Algebra.IsCentral D.F D.algO := by
  refine ⟨fun z hz => ?_⟩
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨c, hc⟩ := D.center_algO z z.2 fun h hh => congrArg Subtype.val (hz ⟨h, hh⟩)
  exact Algebra.mem_bot.2 ⟨c, Subtype.ext hc.symm⟩

theorem finrank_F_algO : Module.finrank D.F D.algO = D.m ^ 2 := by
  have h := Module.finrank_mul_finrank ℚ D.F D.algO
  rw [D.finrank_algO, mul_comm (D.m ^ 2)] at h
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h

theorem algebraMap_injective_of_charZero (K : Type) [Field K] [NumberField K] (k : Type) [Field k]
    [CharZero k] [Algebra (𝓞 K) k] : Function.Injective (algebraMap (𝓞 K) k) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker (algebraMap (𝓞 K) k)) h0
    (RingHom.mem_ker.2 hc) (Algebra.IsIntegral.isIntegral c)
  apply hne
  rw [Ideal.under_def, RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)

end GlobalTheory.UPel.HT.MoritaChar0

namespace GlobalTheory.UPel.HT.MoritaChar0

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

attribute [local instance] algebraFAlgO

def algebraOFAlgO : Algebra (𝓞 D.F) D.algO :=
  ((algebraMap D.F D.algO).comp (algebraMap (𝓞 D.F) D.F)).toAlgebra' fun _ _ => Algebra.commutes _ _

attribute [local instance] algebraOFAlgO

instance towerOFAlgO : IsScalarTower (𝓞 D.F) D.F D.algO := IsScalarTower.of_algebraMap_eq fun _ => rfl

def ordToAlgO : D.O →ₐ[𝓞 D.F] D.algO where
  toRingHom := D.actQ.codRestrict D.algO D.actQ_mem_algO
  commutes' c := by
    apply Subtype.ext
    show D.actQ (algebraMap (𝓞 D.F) D.O c) = ((D.actF (c : D.F) : D.endO) : Module.End ℚ D.VQ)
    rw [D.actF_coe, D.coe_actInt]

instance isLocalizedModule_ordToAlgO :
    IsLocalizedModule (nonZeroDivisors (𝓞 D.F)) (ordToAlgO D).toLinearMap where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hs : ((s : 𝓞 D.F) : D.F) ≠ 0 := by
      intro h
      exact nonZeroDivisors.coe_ne_zero s (RingOfIntegers.coe_eq_zero_iff.1 h)
    have key : ∀ a : D.algO, algebraMap (𝓞 D.F) (Module.End (𝓞 D.F) D.algO) s a = ((s : 𝓞 D.F) : D.F) • a := by
      intro a
      rw [Module.algebraMap_end_apply, ← algebraMap_smul D.F (s : 𝓞 D.F) a]
    refine ⟨fun a b h => ?_, fun a => ⟨((s : 𝓞 D.F) : D.F)⁻¹ • a, ?_⟩⟩
    · rw [key, key] at h
      exact smul_right_injective _ hs h
    · rw [key, smul_inv_smul₀ hs]
  surj y := by
    obtain ⟨q, x, hx⟩ := D.exists_of_mem_algO y.2
    refine ⟨(q.num • x, ⟨(q.den : 𝓞 D.F), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast q.den_ne_zero)⟩), ?_⟩
    apply Subtype.ext
    show (((q.den : 𝓞 D.F) • y : D.algO) : Module.End ℚ D.VQ) = D.actQ (q.num • x)
    rw [Nat.cast_smul_eq_nsmul, AddSubmonoidClass.coe_nsmul, hx, map_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
      ← Int.cast_smul_eq_zsmul ℚ, Rat.den_mul_eq_num]
  exists_of_eq h := ⟨1, by rw [one_smul, one_smul]; exact D.actQ_injective (congrArg Subtype.val h)⟩

end GlobalTheory.UPel.HT.MoritaChar0

namespace GlobalTheory.UPel.HT.MoritaChar0
attribute [local instance] algebraFAlgO algebraOFAlgO

theorem tensor_order_algEquiv_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k]
    [IsAlgClosed k] [CharZero k] [Algebra (𝓞 D.F) k],
    Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  intro p _ D k _ _ _ _
  have hinj := algebraMap_injective_of_charZero D.F k
  letI : Algebra D.F k := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower (𝓞 D.F) D.F k :=
    IsScalarTower.of_algebraMap_eq fun c => (IsFractionRing.lift_algebraMap hinj c).symm
  haveI : SMulCommClass D.F (𝓞 D.F) k := ⟨fun a b x => by simp only [Algebra.smul_def]; ring⟩
  have hF : IsBaseChange D.F (ordToAlgO D).toLinearMap :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 D.F)) D.F _
  have hk : IsBaseChange k (TensorProduct.mk D.F k D.algO 1) := TensorProduct.isBaseChange D.F D.algO k
  have hc := hF.comp hk
  let φ : (k ⊗[𝓞 D.F] D.O) ≃ₐ[k] (k ⊗[D.F] D.algO) :=
    AlgEquiv.ofLinearEquiv hc.equiv (by
      rw [Algebra.TensorProduct.one_def, IsBaseChange.equiv_tmul]
      simp [Algebra.TensorProduct.one_def])
      (LinearMap.map_mul_of_map_mul_tmul fun a₁ a₂ b₁ b₂ => by
        simp [IsBaseChange.equiv_tmul, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul'])
  haveI : IsSimpleRing D.algO := D.algO_simple
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k (k ⊗[D.F] D.algO)
  have hn : n = D.m := by
    have h1 := GroundTheory.Brauer.finrank_baseChange_eq D.F k D.algO
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix, Module.finrank_self, finrank_F_algO,
      Fintype.card_fin] at h1
    exact Nat.mul_self_inj.mp (by simpa [pow_two] using h1)
  subst hn
  exact ⟨φ.trans e⟩

end GlobalTheory.UPel.HT.MoritaChar0
end
end

section

open GlobalTheory.LogDerProj

theorem _root_.GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R), ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_res | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_res | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_res <;> assumption)
end

section

open GlobalTheory.LogDerProj

theorem _root_.GlobalTheory.T.exists_pow_smul_eq_of_logDerivation_extend_eq : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (D₁ D₂ : logSub φ J), res (S := S) f φ J D₁ = res (S := S) f φ J D₂ → ∃ c : Submonoid.powers f, c • D₁ = c • D₂ := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq <;> assumption)
end

section

open Classical MvPolynomial

theorem _root_.GlobalTheory.T.cauchyBinet_columnFrame_prodDetPow_eq_sum : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (x₀ : GlobalTheory.MinorFrame.Var ι d a → ℂ), GlobalTheory.MinorFrame.rsub (GlobalTheory.MinorFrame.frameMat x₀).conjTranspose (GlobalTheory.MinorFrame.detG a n) = ∑ T : GlobalTheory.MinorFrame.Tup ι a d n, star (MvPolynomial.eval x₀ (GlobalTheory.MinorFrame.prodMinors T)) • GlobalTheory.MinorFrame.prodMinors T := by
  first | exact @GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum | exact GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum | (intros; apply GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum <;> assumption)
end

section

open Classical MvPolynomial

theorem _root_.GlobalTheory.T.fockPairing_linearSubstitution_adjoint : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ) (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' = Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by
  first | exact @GlobalTheory.MinorFrame.fockS_rsub_adj | exact GlobalTheory.MinorFrame.fockS_rsub_adj | (intros; apply GlobalTheory.MinorFrame.fockS_rsub_adj <;> assumption)
end

section


theorem _root_.GlobalTheory.T.fockColumnSubstitution_exp_of_columnDerivation : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (c : ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Q),
    (∀ (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a) (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
      HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R) m)
        (AddMonoidAlgebra.coeff (GlobalTheory.ColLie.colDer τ S R) m) 0) →
    (∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P, q (GlobalTheory.ColLie.colDer τ S P) = ((c : ℂ) * S.trace) • q P) →
    ∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P,
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp S)) P) = ((NormedSpace.exp S).det ^ c) • q P := by
  first | exact @GlobalTheory.ColLie.colSub_exp_of_colDer | exact GlobalTheory.ColLie.colSub_exp_of_colDer | (intros; apply GlobalTheory.ColLie.colSub_exp_of_colDer <;> assumption)
end

section


theorem _root_.GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a)
    (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
    HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R) m)
      (AddMonoidAlgebra.coeff (GlobalTheory.ColLie.colDer τ S R) m) 0 := by
  first | exact @GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp | exact GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp | (intros; apply GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp <;> assumption)
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.complexHermitianForm_unitaryChartSection : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ (τ : X.Ψ) (u v : Fin r → ℂ), hermC τ.1 X.Gm (secM X x w τ *ᵥ u) (secM X x w τ *ᵥ v) = hermC τ.1 X.Gm u v := by
  first | exact @GlobalTheory.SUChartSection.hermC_secM | exact GlobalTheory.SUChartSection.hermC_secM | (intros; apply GlobalTheory.SUChartSection.hermC_secM <;> assumption)
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ τ : X.Ψ, (secM X x w τ).det = 1 := by
  first | exact @GlobalTheory.SUChartSection.det_secM_eq_one | exact GlobalTheory.SUChartSection.det_secM_eq_one | (intros; apply GlobalTheory.SUChartSection.det_secM_eq_one <;> assumption)
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (τ : X.Ψ) (a b : Fin r), ContDiffOn ℝ ∞ (fun w => gsB X w τ a b) {w | cpt X x w ∈ X.dom} := by
  first | exact @GlobalTheory.SUChartSection.GSSmooth.gsB_contDiffOn | exact GlobalTheory.SUChartSection.GSSmooth.gsB_contDiffOn | (intros; apply GlobalTheory.SUChartSection.GSSmooth.gsB_contDiffOn <;> assumption)
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_diag_im : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (z : V (nd X)) (τ : X.Ψ) (a : Fin r), (dY X z τ a a).im = 0 := by
  first | exact @GlobalTheory.SUChartSection.diagreal | exact GlobalTheory.SUChartSection.diagreal | (intros; apply GlobalTheory.SUChartSection.diagreal <;> assumption)
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (z : V (nd X)) (τ : X.Ψ) (a b : Fin r), dY X z τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (dY X z τ a b) = 0 := by
  first | exact @GlobalTheory.SUChartSection.dY_skew | exact GlobalTheory.SUChartSection.dY_skew | (intros; apply GlobalTheory.SUChartSection.dY_skew <;> assumption)
end
