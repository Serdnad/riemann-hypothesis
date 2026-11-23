module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle033
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle094
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameZero

theorem exists_complex_point {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (I : Ideal A) (hI : I ≠ ⊤) : ∃ ψ : A →ₐ[K] CAt σ, ∀ x ∈ I, ψ x = 0 := by
  classical
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  haveI := hM
  letI : Field (A ⧸ M) := Ideal.Quotient.field M
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let g : (A ⧸ M) →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let f : A →ₐ[K] ℂ := g.comp (Ideal.Quotient.mkₐ K M)
  refine ⟨⟨(f : A →+* ℂ), fun r => f.commutes r⟩, fun x hx => ?_⟩
  show g (Ideal.Quotient.mk M x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hx), map_zero]


set_option synthInstance.maxHeartbeats 400000 in
theorem noCommonZero_of_readings : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → T.R j), (∀ i, ws i ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, ∃ i, rdU (T.U j T.σ₀) (ws i) k x ≠ 0) → NoCommonZero (T.Q.Xo j) T.Q.c ws := by
  intro D T h j hj a n m ws hws hz
  obtain ⟨hL, -, hG, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  have hu := (h.toLawsCore.unf j hj T.σ₀ T.good_σ₀).2.2.1
  intro k _ _ _ y
  by_contra hne
  simp only [not_exists, not_not] at hne
  obtain ⟨C, ψ, z, t', hψ, hbor⟩ := hA hG k y
  have hz0 : ∀ i, evR (T.Q.Xo j) T.Q.c (ws i) z = 0 := by
    intro i
    have e1 := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hws i) t' z y hbor
    rw [hne i] at e1
    have hw : wchar (ex (T.Q.Dw j) a n) t' ≠ 0 := by
      unfold wchar
      exact Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Units.ne_zero _)
    exact (mul_eq_zero.mp e1.symm).resolve_left hw
  have hsm := C.sm
  have hI : Ideal.span (Set.range fun i => evR (T.Q.Xo j) T.Q.c (ws i) C.y) ≠ ⊤ := by
    intro htop
    have hker : Ideal.span (Set.range fun i => evR (T.Q.Xo j) T.Q.c (ws i) C.y) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker,
        ← GlobalTheory.Reg.evR_baseChange_of_isReduced _ _ _ _ (T.Q.Xo j) T.Q.c hL a n (ws i) (hws i) _ k ψ C.y z hψ]
      exact hz0 i
    have h1 := hker (htop ▸ Submodule.mem_top : (1 : C.R) ∈ _)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨ψ', hψ'⟩ := exists_complex_point T.σ₀ _ hI
  obtain ⟨z', hz'⟩ := hL.bc _ _ ψ' C.y
  obtain ⟨kk, x, t, hb⟩ := hu z'
  obtain ⟨i, hi⟩ := hz kk x.1 x.2
  apply hi
  haveI : IsDomain (CAt T.σ₀) := inferInstanceAs (IsDomain ℂ)
  have e2 := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hws i) t _ _ hb
  have e3 := GlobalTheory.Reg.evR_baseChange_of_isReduced _ _ _ _ (T.Q.Xo j) T.Q.c hL a n (ws i) (hws i) _ _ ψ' C.y z' hz'
  have e4 : ψ' (evR (T.Q.Xo j) T.Q.c (ws i) C.y) = 0 := hψ' _ (Ideal.subset_span ⟨i, rfl⟩)
  have hw2 : wchar (ex (T.Q.Dw j) a n) t ≠ 0 := by
    unfold wchar
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Units.ne_zero _)
  have e6 : wchar (ex (T.Q.Dw j) a n) t * evR (T.Q.Xo j) T.Q.c (ws i) ((T.U j T.σ₀).un kk x) = 0 := by
    rw [← e2, e3, e4]
  have e5 := (mul_eq_zero.mp e6).resolve_left hw2
  unfold rdU
  simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2, e5]
  unfold toC
  rfl

end GlobalTheory.FrameZero
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory.ShortValueLinear

theorem isHomogeneous_of_rowDeg {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) :
    P.IsHomogeneous (∑ σ : T, ∑ i : Fin (r σ), a σ i) := by
  classical
  intro m hm
  have hmS : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hm
  have key : ∀ (σ : T) (i : Fin (r σ)), a σ (i : ℕ) = ∑ b, m ⟨σ, (i, b)⟩ :=
    fun σ i => (hP m hmS σ i).symm
  simp only [key]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun σ _ => Fintype.sum_prod_type _

theorem sum_support_eq_constr {ι F S : Type} [Field F] [CommRing S] [Algebra F S]
    (G : (ι →₀ ℕ) → S) (P : MvPolynomial ι F) :
    ∑ m ∈ P.support, algebraMap F S (P.coeff m) * G m =
      (MvPolynomial.basisMonomials ι F).constr F G P := by
  classical
  rw [Module.Basis.constr_apply, Finsupp.sum]
  refine Finset.sum_congr ?_ fun μ _ => ?_
  · ext μ
    simp [MvPolynomial.basisMonomials]
  · simp [MvPolynomial.basisMonomials, Algebra.smul_def]

theorem formula_linear {ι F S Qt J : Type} [Field F] [CommRing S] [Algebra F S] [Finite Qt] [Fintype J]
    (k N : F) (w : Qt → F) (G : Qt → J → (ι →₀ ℕ) → S) (d m : ℕ) (cf : Fin m → F)
    (Q : Fin m → MvPolynomial ι F) (hQ : ∀ i, (Q i).IsHomogeneous d) :
    algebraMap F S (k * (N ^ (∑ i, cf i • Q i).totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap F S (w q) * ∑ j, ∑ μ ∈ (∑ i, cf i • Q i).support,
          algebraMap F S ((∑ i, cf i • Q i).coeff μ) * G q j μ =
      ∑ i, algebraMap F S (cf i) * (algebraMap F S (k * (N ^ (Q i).totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap F S (w q) * ∑ j, ∑ μ ∈ (Q i).support,
          algebraMap F S ((Q i).coeff μ) * G q j μ) := by
  classical
  have := Fintype.ofFinite Qt
  set B := MvPolynomial.basisMonomials ι F
  have hsum : ∀ (P : MvPolynomial ι F) (q : Qt) (j : J),
      ∑ μ ∈ P.support, algebraMap F S (P.coeff μ) * G q j μ = B.constr F (G q j) P :=
    fun P q j => sum_support_eq_constr (G q j) P
  simp only [hsum, finsum_eq_sum_of_fintype]
  have hpre : ∀ P : MvPolynomial ι F, P.IsHomogeneous d →
      algebraMap F S (k * (N ^ P.totalDegree)⁻¹) *
          ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) P =
        algebraMap F S (k * (N ^ d)⁻¹) * ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) P := by
    intro P hP
    by_cases hP0 : P = 0
    · simp [hP0]
    · rw [hP.totalDegree hP0]
  have hQs : (∑ i, cf i • Q i).IsHomogeneous d := by
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hQ i))
  have hR : ∀ i, algebraMap F S (cf i) * (algebraMap F S (k * (N ^ (Q i).totalDegree)⁻¹) *
        ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) (Q i)) =
      algebraMap F S (cf i) * (algebraMap F S (k * (N ^ d)⁻¹) *
        ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) (Q i)) :=
    fun i => by rw [hpre _ (hQ i)]
  have hlin : ∀ (q : Qt) (j : J), B.constr F (G q j) (∑ i, cf i • Q i) =
      ∑ i, algebraMap F S (cf i) * B.constr F (G q j) (Q i) := by
    intro q j

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
  rw [hpre _ hQs]
  simp only [hR]
  simp only [hlin, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.ShortValueLinear

namespace GlobalTheory

theorem shortThetaValue_linear : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, Q i ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (u : Fin m → S), ShortValAt Xo c nab w Λ β N (∑ i, cf i • Q i) y v → (∀ i, ShortValAt Xo c nab w Λ β N (Q i) y (u i)) → v = ∑ i, algebraMap c.F S (cf i) * u i := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hL a w β m cf Q hQ S _ _ y v u hv hu
  classical
  have : Finite (LevQ Dw l) := GlobalTheory.ShortValue.finite_levelQuotient Dw l
  have hEU := fun i => GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l
    Xo c nab hnab n Λ N hU hT hL a (Q i) (hQ i) w β
  have hRow : ∀ i, RowDeg Dw.mult n c.F (fun τ j => a (τ, j)) (Q i) := by
    intro i
    have h := hQ i
    unfold HHa at h
    simp only [Set.mem_setOf_eq] at h
    exact h.2.2
  have hQd := fun i => GlobalTheory.ShortValueLinear.isHomogeneous_of_rowDeg (hRow i)
  unfold ShortValAt at hv
  obtain ⟨S', _i1, _i2, φ, y', z, tp, F, hff, hfr, hz, hgeo, htp, huu, hφv⟩ := hv
  have hnat : ∀ i, φ (u i) = algebraMap c.F S' (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ (Q i).totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S' (w q) *
        ∑ j, ∑ μ ∈ (Q i).support, algebraMap c.F S' ((Q i).coeff μ) *
          ∏ b, nab y' ((N : ℤ) ^ 2) (F q j b) (colOf μ b) := by
    intro i
    refine (hEU i).2 S S' φ y y' hfr (u i) _ (hu i) ?_
    unfold ShortValAt
    exact ⟨S', _i1, _i2, AlgHom.id c.F S', y', z, tp, F,
      RingHom.FaithfullyFlat.of_bijective ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩,
      GlobalTheory.Frames.frMapUniq_refl y', hz, hgeo, htp, huu, rfl⟩
  have hlin := GlobalTheory.ShortValueLinear.formula_linear (S := S')
    (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹) (N : c.F) w
    (fun q j μ => ∏ b, nab y' ((N : ℤ) ^ 2) (F q j b) (colOf μ b)) _ m cf Q hQd
  apply RingHom.FaithfullyFlat.injective hff
  change φ v = φ (∑ i, algebraMap c.F S (cf i) * u i)
  rw [hφv]
  refine hlin.trans ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul φ, AlgHom.commutes, hnat i]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.ClassSumUnique

theorem eq_of_forall_algClosed {K R : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] (u v : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k), φ u = φ v) : u = v := by
  rw [← sub_eq_zero]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
  let ψ : R →+* AlgebraicClosure J.ResidueField :=
    (algebraMap J.ResidueField (AlgebraicClosure J.ResidueField)).comp (algebraMap R J.ResidueField)
  letI : Algebra K (AlgebraicClosure J.ResidueField) := (ψ.comp (algebraMap K R)).toAlgebra
  have e : ψ u = ψ v := h (AlgebraicClosure J.ResidueField) { ψ with commutes' := fun _ => rfl }
  have e' : algebraMap R J.ResidueField u = algebraMap R J.ResidueField v :=
    (algebraMap J.ResidueField (AlgebraicClosure J.ResidueField)).injective e
  rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, e', sub_self]

theorem sec_eq_of_geometric {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f f' : Rul Xo c} (hf : f ∈ sec Xo c a m)
    (hf' : f' ∈ sec Xo c a m)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), evR Xo c f y = evR Xo c f' y) :
    f = f' := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : GlobalTheory.CoefChangeCompare.ValueWD Xo c :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hBC : GlobalTheory.CoefChangeCompare.HasBC Xo c := GlobalTheory.CoefChangeCompare.hasBC_of hS
  funext p y
  haveI := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 p).2
  refine eq_of_forall_algClosed (K := c.F) _ _ fun k _ _ _ φ => ?_
  obtain ⟨z, hz⟩ := hBC p.R k φ y
  rw [← GlobalTheory.CoefChangeCompare.evR_of_map hWD hf.1 hz, ← GlobalTheory.CoefChangeCompare.evR_of_map hWD hf'.1 hz]
  exact h k z

theorem isThClsD_unique : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F), d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∀ k, (La k).Unimod ∧ (La k).TrivAt d.l₂.M ∧ (La k).LevOK (Nc k) d.l₂.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), (∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (x : Cl → Vs) (a' : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), ∀ f ∈ sec Xo c a' m, ∀ f' ∈ sec Xo c a' m, IsThClsD Xo c d w La Nc gam vol ep io x f → IsThClsD Xo c d w La Nc gam vol ep io x f' → f = f' := by
  intro hC E _ _ _ H Dw l Xo c n d Cl _ w La Nc gam vol ep Vs _ _ io hd hnab hLa a hio x a' m f hf f' hf' h h'
  obtain ⟨_, hnab⟩ := hnab
  refine sec_eq_of_geometric hf hf' fun k _ _ _ y => ?_
  letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a => by
    show algebraMap c.F k (d.eF.symm (d.eF a)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := h k hk y y₂ hy
  obtain ⟨v', hv', e'⟩ := h' k hk y y₂ hy
  have hvv : v = v' := funext fun cl =>
    ((GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n
      (La cl) (Nc cl) (hLa cl).1 (hLa cl).2.1 (hLa cl).2.2 a _
      ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hio (x cl))) (fun q => d.eF (w cl q)) 1).1 k y₂).unique
      (hv cl) (hv' cl)
  rw [e, e', hvv]

end GlobalTheory.ClassSumUnique
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaRule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem monomial_degree_of_mem_harm {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ harmA (Dw := Dw) c a n) {m : LtN Dw n →₀ ℕ} (hm : m ∈ P.support) :
    (m.sum fun _ e => e) = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  have hrow := hP.1.2.2 m hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hrow τ i

theorem totalDegree_of_mem_harm {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ harmA (Dw := Dw) c a n) (h0 : P ≠ 0) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  obtain ⟨m0, hm0⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  unfold MvPolynomial.totalDegree
  refine le_antisymm (Finset.sup_le fun m hm => (monomial_degree_of_mem_harm hP hm).le) ?_
  rw [← monomial_degree_of_mem_harm hP hm0]
  exact Finset.le_sup (f := fun s : LtN Dw n →₀ ℕ => s.sum fun _ e => e) hm0

theorem thExpr_eq_sum_superset (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (U : Finset (LtN Dw n →₀ ℕ))
    (hU : P.support ⊆ U) :
    thExpr Xo c nab y P F = algebraMap c.F S (((l.M : c.F) ^ (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)))⁻¹) *
      ∑ m ∈ U, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((l.M : ℤ) ^ 2) (F b) (colOf m b) := by
  unfold thExpr
  rw [Finset.sum_subset hU (fun m _ hm => by rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul])]
  by_cases h0 : P = 0
  · subst h0; simp
  · rw [totalDegree_of_mem_harm hP h0]

theorem thExpr_linear (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    {N : ℕ} (cf : Fin N → c.F) (Q : Fin N → MvPolynomial (LtN Dw n) c.F) (hQ : ∀ i, Q i ∈ harmA (Dw := Dw) c a n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (hsum : ∑ i, cf i • Q i = P) :
    thExpr Xo c nab y P F = ∑ i, algebraMap c.F S (cf i) * thExpr Xo c nab y (Q i) F := by
  classical
  set U := P.support ∪ Finset.univ.biUnion fun i => (Q i).support
  have hQU : ∀ i, (Q i).support ⊆ U := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => (Q i).support) (Finset.mem_univ i)).trans Finset.subset_union_right
  rw [thExpr_eq_sum_superset nab y F hP U Finset.subset_union_left]
  simp only [fun i => thExpr_eq_sum_superset nab y F (hQ i) U (hQU i)]
  subst hsum

  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
  Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem thValAt_linear (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (x : Fin n → Dw.La)
    {N : ℕ} (cf : Fin N → c.F) (Q : Fin N → MvPolynomial (LtN Dw n) c.F) (hQ : ∀ i, Q i ∈ harmA (Dw := Dw) c a n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (hsum : ∑ i, cf i • Q i = P)
    {S : Type} [CommRing S] [Algebra c.F S] (y0 : FrPt Xo c S) {v : S} (hv : ThValAt Xo c nab y0 x P v)
    (vi : Fin N → S) (hvi : ∀ i, ThValAt Xo c nab y0 x (Q i) (vi i)) :
    v = ∑ i, algebraMap c.F S (cf i) * vi i := by
  obtain ⟨S', _, _, φ, y', F, hff, hmap, hV, he⟩ := hv
  have hrefl : FrMap (AlgHom.id c.F S') y' y' :=
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S' S' (AlgHom.id c.F S') y').2.1
  have e1 : ∀ i, φ (vi i) = thExpr Xo c nab y' (Q i) F := fun i =>
    GlobalTheory.thetaValue_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l Xo c nab hnab S S' φ y0 y' hmap a n x (Q i) (hQ i)
      _ _ (hvi i) ⟨S', inferInstance, inferInstance, AlgHom.id c.F S', y', F,
        RingHom.FaithfullyFlat.of_bijective Function.bijective_id, hrefl, hV, rfl⟩
  apply hff.injective
  show φ v = φ (∑ i, algebraMap c.F S (cf i) * vi i)

  rw [he, thExpr_linear nab y' F cf Q hQ hP hsum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, AlgHom.commutes, e1 i]

theorem levPt_eq_of_sub_mem {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {u u' : Dw.La}
    (h : u - u' ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) : levPt Xo x0 u = levPt Xo x0 u' := by
  have e : Xo.univ.eta u = Xo.univ.eta u' := by
    have h1 := Xo.univ.eta_add (u - u') u'
    rw [sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul] at h1
    exact h1
  unfold levPt
  rw [e]

end Lin

theorem isThRule_linear_and_congr : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (x : Fin n → Dw.La) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) (g : Fin m → Rul Xo c), (∀ i, Q i ∈ harmA c a n) → (∑ i, cf i • Q i) ∈ harmA c a n → IsThRule Xo c nab x (∑ i, cf i • Q i) f → (∀ i, IsThRule Xo c nab x (Q i) (g i)) → f = ∑ i, cf i • g i) ∧ ∀ (x x' : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), (∀ b, x b - x' b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → IsThRule Xo c nab x P f → IsThRule Xo c nab x' P f := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab a n
  refine ⟨fun x m cf Q f g hQ hP hf hg => ?_, fun x x' P f hx hf p y => ?_⟩
  · funext p y
    rw [thValAt_linear hC nab hnab x cf Q hQ hP rfl y (hf p y) (fun i => g i p y) (fun i => hg i p y)]
    rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def (cf i) (g i p y)).symm
  · obtain ⟨S', _, _, φ, y', F, hff, hmap, hV, he⟩ := hf p y
    exact ⟨S', inferInstance, inferInstance, φ, y', F, hff, hmap,
      fun b => levPt_eq_of_sub_mem (Xo := Xo) y'.x (hx b) ▸ hV b, he⟩

end GlobalTheory.ThetaRule
end
end
