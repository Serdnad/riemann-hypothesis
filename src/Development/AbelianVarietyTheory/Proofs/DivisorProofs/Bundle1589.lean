module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle135
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle047
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.lieDerivative_realLieSmoothing_eq_density : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a, ∀ (X : Lie E a) (g : GA E a), lieD X (smoothing ν α ψ) g = smoothing ν (dens X α) ψ g := by
  first | exact @GlobalTheory.AutGrowth.lieD_smoothing_eq_dens | exact GlobalTheory.AutGrowth.lieD_smoothing_eq_dens | (intros; apply GlobalTheory.AutGrowth.lieD_smoothing_eq_dens <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.centre_comp_mem_kinfEquivariantAutomorphicMaps : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) (T : W →ₗ[ℂ] Sm E a), T ∈ maps L W hW → ∀ z ∈ Zalg E a, z ∘ₗ T ∈ maps L W hW := by
  first | exact @GlobalTheory.AutGrowth.comp_mem_maps | exact GlobalTheory.AutGrowth.comp_mem_maps | (intros; apply GlobalTheory.AutGrowth.comp_mem_maps <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.realLieSmoothing_mem_slowlyIncreasing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ f ∈ growth E a, smoothing ν α f ∈ growth E a := by
  first | exact @GlobalTheory.AutGrowth.smoothing_mem_growth | exact GlobalTheory.AutGrowth.smoothing_mem_growth | (intros; apply GlobalTheory.AutGrowth.smoothing_mem_growth <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.smoothing_right_translate_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), KInv α → ∀ (ψ : GA E a → ℂ) (k : Kinf E a) (g : GA E a), smoothing ν α (fun x => ψ (x * infGL E a (Unitary.toUnits k))) g = smoothing ν α ψ (g * infGL E a (Unitary.toUnits k)) := by
  first | exact @GlobalTheory.AutGrowth.smoothing_rt_Kinf | exact GlobalTheory.AutGrowth.smoothing_rt_Kinf | (intros; apply GlobalTheory.AutGrowth.smoothing_rt_Kinf <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure], ∃ α : ℕ → Lie E a → ℂ, (∀ n, IsTest (invSet E a) (α n) ∧ KInv (α n)) ∧ ∀ ψ ∈ Sm E a, ∀ g, Tendsto (fun n => smoothing ν (α n) ψ g) atTop (𝓝 (ψ g)) := by
  first | exact @GlobalTheory.AutGrowth.ApproxId.exists_approx_identity | exact GlobalTheory.AutGrowth.ApproxId.exists_approx_identity | (intros; apply GlobalTheory.AutGrowth.ApproxId.exists_approx_identity <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isContRep_sub_cptRep (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W)
    [FiniteDimensional ℂ W] : GlobalTheory.Published.AutFin.IsContRep (GlobalTheory.PRep.sub (cptRep E a) W hW) := by
  first
  | exact @_root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub
  | exact _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub
  | (apply _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub ..)

theorem finiteDimensional_capEigen_maps : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W), FiniteDimensional ℂ W → ∀ (c : (E →+* ℂ) → ℂ → ℂ) (N : Submodule ℂ (W →ₗ[ℂ] Sm E a)), N ≤ maps L W hW → (∀ T ∈ N, ∀ τ u, cap τ u ∘ₗ T = c τ u • T) → FiniteDimensional ℂ N := by
  intro hHC E _ _ _ a L hL W hW hWf c N hN hcap
  haveI := hWf
  have hF := hHC E a L hL W (GlobalTheory.PRep.sub (cptRep E a) W hW) (isContRep_sub_cptRep W hW) c
  haveI := hF
  have hmem : ∀ T ∈ N, ∀ w, T w ∈ GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c := by
    intro T hT w
    have hm : (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
        ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧
          ∀ k ∈ L, finRep E a k (T w) = T w := hN hT
    obtain ⟨heq, hall⟩ := hm
    obtain ⟨htame, hleft, hfix⟩ := hall w
    have hZ : ∀ z ∈ Zalg E a, ∃ s : ℂ, z ∘ₗ T = s • T := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact ⟨c τ u, hcap T hT τ u⟩
      | algebraMap r => exact ⟨r, LinearMap.ext fun v => by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨s + t, by rw [LinearMap.add_comp, hs, ht, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨t * s, by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ht, LinearMap.comp_smul, hs, smul_smul]⟩
    refine ⟨⟨hleft, ?_, ?_, ?_, ?_⟩, hfix, GlobalTheory.Published.AutFinGL.type_of_map _ T heq w, fun τ u => ?_⟩
    · exact isOpen_stab_of_mem_nhds (finRep E a) (T w)
        (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
    · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, heq k w⟩
    · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {T w}) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs⟩ := hZ z hz
      have e : z (T w) = s • T w := LinearMap.congr_fun hs w
      show z (T w) ∈ _
      rw [e]
      exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
    · exact growth_of_tame htame
    · exact LinearMap.congr_fun (hcap T hT τ u) w
  let Φ : N →ₗ[ℂ] (W →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c)) :=
    { toFun := fun T => LinearMap.codRestrict _ T.1 fun w => Submodule.subset_span (hmem T.1 T.2 w)
      map_add' := fun T T' => LinearMap.ext fun w => rfl
      map_smul' := fun r T => LinearMap.ext fun w => rfl }
  have hinj : Function.Injective Φ := fun T T' h =>
    Subtype.ext (LinearMap.ext fun w => congrArg Subtype.val (LinearMap.congr_fun h w))
  exact Module.Finite.of_injective Φ hinj

end GlobalTheory.AutGrowth

end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

theorem rho_jM_common_eigvec : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (i : Fin G.m)
    (τ : FM P →+* PadicAlgCl p), τ.comp (algebraMap G.F (FM P)) = G.emb i →
    ∃ v : Fin G.n → PadicAlgCl p, v ≠ 0 ∧
      ∀ a : FM P, (G.rho i (jM P a)).map (fun x => (x : PadicAlgCl p)) *ᵥ v = τ a • v := by
  intro p _ G P i τ hτ
  let f : G.Fw i →+* PadicAlgCl p := algebraMap (G.Fw i) (PadicAlgCl p)
  have hf : (fun x : G.Fw i => (x : PadicAlgCl p)) = ⇑f := rfl
  have hfe : f.comp (G.embW i) = G.emb i := by
    ext x; rfl
  let ψ : G.C →+* Matrix (Fin G.n) (Fin G.n) (PadicAlgCl p) := f.mapMatrix.comp (G.rho i)
  have hψ : ∀ x, ψ x = (G.rho i x).map (fun x => (x : PadicAlgCl p)) := fun x => rfl
  set M := ψ (P.γ : G.C) with hM
  set lam := τ (AdjoinRoot.root P.pol) with hlam
  have hchar : M.charpoly = P.pol.map (G.emb i) := by
    rw [hM, hψ, hf, Matrix.charpoly_map, charpoly_rho_eq_map_pol, Polynomial.map_map, hfe]
  have heval : Polynomial.eval lam M.charpoly = 0 := by
    rw [hchar, Polynomial.eval_map, ← hτ, ← Polynomial.hom_eval₂, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.eval₂_root, map_zero]
  rw [Matrix.eval_charpoly] at heval
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 heval
  have hMv : M *ᵥ v = lam • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  refine ⟨v, hv0, fun a => ?_⟩
  rw [← hψ]
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [jM_mk]
  have key : ∀ g : Polynomial G.F, ψ (Polynomial.aeval (P.γ : G.C) g) *ᵥ v =
      τ (AdjoinRoot.mk P.pol g) • v := by
    intro g
    induction g using Polynomial.induction_on with
    | C c =>
      rw [Polynomial.aeval_C, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, ← RingHom.comp_apply τ, hτ]
      show (f.mapMatrix (G.rho i (algebraMap G.F G.C c))) *ᵥ v = _
      rw [G.rho_F]
      ext j
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, RingHom.mapMatrix_apply, Matrix.diagonal_map]
      exact Or.inl rfl
    | add g h hg hh =>
      rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hg, hh, map_add (f := _), map_add (f := _), add_smul]
    | monomial k c hk =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, ← Matrix.mulVec_mulVec, Polynomial.aeval_X, ← hM, hMv,
        Matrix.mulVec_smul, hk, smul_smul]
      congr 1
      rw [map_mul (AdjoinRoot.mk P.pol) _ Polynomial.X, map_mul τ, AdjoinRoot.mk_X, mul_comm]
  exact key g

end GlobalTheory.StabFin
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section
namespace GlobalTheory.Poinc.Tors.OneOver

theorem exists_frm_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F 1 b) (hw : w.IsGen) (k : ℕ) :
    ∃ wk : Frm D F k b, wk.IsGen ∧ ∀ z J, Good D.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k := by
  obtain ⟨z₀⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' D.P.isLB z₀
  obtain ⟨wk, hwk, hv⟩ := GlobalTheory.TorusExt.exists_gen_val D.P.isLB (DegPre.lineφ D F b) (DegPre.lineε k) hJ₀
    (val w (𝟙 _) z₀ J₀ ^ k)
  refine ⟨wk, hwk, fun z J hJ => ?_⟩
  obtain rfl := CoefBasic.pt_eq z₀ z
  have a₁ := CoefBasic.val_tr hwk (𝟙 _) hJ hJ₀
  have a₂ := CoefBasic.val_tr hw (𝟙 _) hJ hJ₀
  simp only [Category.id_comp] at a₁ a₂
  rw [CoefBasic.prod_line k b (CoefBasic.trU D.P.L z₀ J J₀)] at a₁
  rw [CoefBasic.prod_line 1 b (CoefBasic.trU D.P.L z₀ J J₀)] at a₂
  refine a₁.trans ?_
  rw [hv, a₂]
  simp only [pow_one, mul_pow, inv_pow]

theorem sumF_scale {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hI : AdmBase R I) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} {x : Ix → F} {v v' c : F} (h : SumF I F x v)
    (h' : SumF I F (fun i => c * x i) v') : v' = c * v := by
  have hl := (GlobalTheory.AdicSum.sumF_calculus R I hI F Ix x x v v).2.1 h h (c - 1)
  have e : (fun i => (c - 1) * x i + x i) = fun i => c * x i := funext fun i => by ring
  rw [e, show (c - 1) * v + v = c * v by ring] at hl
  exact (GlobalTheory.AdicSum.sumF_calculus R I hI F Ix (fun i => c * x i) x v' (c * v)).1 h' hl

theorem eq_of_liesOver : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre F) (w w' : Frm D.toPre F 1 g.b) (x x' : TFK (R := R) F ⟶ A.A) (fr : FrAt x) (fr' : FrAt x'), w.IsGen → w'.IsGen → fr.IsGen → fr'.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g w' x' fr' → x = x' := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ w₀ hw₀ g w w' x x' fr fr' hw hw' hfr hfr' H H'
  obtain ⟨wk, hwk, hvk⟩ := exists_frm_pow w hw 4
  obtain ⟨wk', hwk', hvk'⟩ := exists_frm_pow w' hw' 4
  obtain ⟨c, hc, -, hcoef⟩ := ((CoefBasic.coef_basic R D.toPre F 4 g).2.2 wk hwk).2.2.1 wk' hwk'
  have key : ∀ (t : SecA A F 4) (v v' : F), ValAt t x fr v → ValAt t x' fr' v' → v' = c * v := by
    intro t v v' hv hv'
    obtain ⟨s, hs⟩ : ∃ s, U.toUnifPre.ExpandsF F 4 w₀ t s := by
      obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F (k := 4) (by norm_num) w₀ hw₀
      exact ⟨e t, (he t _).2 rfl⟩
    have h1 := H 4 (by norm_num) wk hvk hwk t s v hs hv
    have h2 := H' 4 (by norm_num) wk' hvk' hwk' t s v' hs hv'
    rw [show coef s g wk' = fun χ => c * coef s g wk χ from funext (hcoef s)] at h2
    exact sumF_scale hI h1 h2
  obtain ⟨M, s, hcov, haff⟩ := (hL.1.ample _ A 4 le_rfl).2 ⊤ (isAffineOpen_top _)
  choose r hr hsurj using fun i => (haff i).2
  obtain ⟨i', hi⟩ : ∃ i' : A.A.left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.A.left.topIso.inv, A.A.left.topIso.inv_hom_id⟩
  have sec : ∀ j, ∃ v : SecA A F 4, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J),
      Good A.L z J → sA v r z J =
        sval (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
          (r ≫ (snd (TFK (R := R) F) A.A).left ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec A.isLB (φ := fun _ : Fin 4 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => ((4 : ℕ) : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd (TFK (R := R) F) A.A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (VVRank.sval_pullTo _ _ _ r z hJ)⟩
  choose v hv using sec
  choose a ha using fun j => GlobalTheory.OneBasis.exists_valAt A F hL.1 (v j) x hfr
  choose a' ha' using fun j => GlobalTheory.OneBasis.exists_valAt A F hL.1 (v j) x' hfr'
  have hrel : ∀ j, a' j = c * a j := fun j => key (v j) (a j) (a' j) (ha j) (ha' j)
  have hf : (x.left ≫ i') ≫ (A.A.hom ∣_ ⊤) = (x'.left ≫ i') ≫ (A.A.hom ∣_ ⊤) := by
    rw [← cancel_mono (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens).ι]
    simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hi, Over.w]
  have e : ∀ y : TFK (R := R) F ⟶ A.A,
      (ptSecT A.A y).left ≫ (snd (TFK (R := R) F) A.A).left ≫ i' = y.left ≫ i' := fun y => by
    rw [← Category.assoc, ← Over.comp_left, ptSecT, lift_snd]
  have key2 : x.left ≫ i' = x'.left ≫ i' := by
    refine AutUniq.hom_eq_of_sval (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s
      (A.A.hom ∣_ ⊤) _ _ hf hcov (fun i => (haff i).1) r hr hsurj fun z => ?_
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' A.isLB z
    obtain ⟨κ, hκ⟩ : ∃ κ : F →+* (TFK (R := R) F).left.presheaf.stalk z, ∀ b, cst (R := R) F z b = κ b :=
      ⟨CoefBasic.cstH (R := R) z, CoefBasic.cst_eq z⟩
    refine ⟨J, hJ, Units.map κ.toMonoidHom (Units.mk0 c hc) *
      val (powFrame A.A A.L x' fr' 4) (𝟙 _) z J * (val (powFrame A.A A.L x fr 4) (𝟙 _) z J)⁻¹, fun j => ?_⟩
    have p := (hv j _ (ptSecT A.A x).left z J hJ).symm.trans (ha j z J hJ)
    have q := (hv j _ (ptSecT A.A x').left z J hJ).symm.trans (ha' j z J hJ)
    rw [e] at p q
    rw [p, q, hrel j]
    have hinv := Units.inv_mul (val (powFrame A.A A.L x fr 4) (𝟙 _) z J)
    simp only [Units.val_mul, Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      hκ, map_mul, id] at hinv ⊢
    linear_combination (-(κ c * (val (powFrame A.A A.L x' fr' 4) (𝟙 _) z J).val * κ (a j))) * hinv
  have := congrArg (fun q => q ≫ (A.A.hom ⁻¹ᵁ ⊤).ι) key2
  simp only [Category.assoc, hi, Category.comp_id] at this
  exact Over.OverMorphism.ext this

end GlobalTheory.Poinc.Tors.OneOver
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ConsEta
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

theorem under_under_of_compat {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra F K] [Algebra F L] [alg : Algebra K L]
    (hc : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_under]
  have : algebraMap (𝓞 K) (𝓞 L) (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 L) x := by
    apply RingOfIntegers.ext
    exact hc (x : F)
  rw [this]

theorem finEval_ideleMap_localIdele {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra F K] [Algebra F L] [alg : Algebra K L]
    (hc : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.under (𝓞 F) ≠ w.under (𝓞 F)) (a : (v.adicCompletion K)ˣ) :
    Units.map (GlobalTheory.IdeleNormChar.finEval w) (ideleMap K L (Neutral.B1.localIdele K v a)) = 1 := by
  have hne : w.under (𝓞 K) ≠ v := fun h => hv (h ▸ under_under_of_compat hc w)
  apply Units.ext
  show finiteCompletionMap K L w ((Neutral.B1.localIdele K v a : AdeleRing (𝓞 K) K).2 (w.under (𝓞 K))) = 1
  rw [(Neutral.B1.localIdele_isSupportedAt K v a).2 _ hne, map_one]

theorem isSplitAt_of_under_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {v w : HeightOneSpectrum (𝓞 E)}
    (hw : GlobalTheory.UnitaryBC.IsSplitAt w)
    (h : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) :
    GlobalTheory.UnitaryBC.IsSplitAt v := by
  obtain ⟨u, hu, hu'⟩ := hw
  by_cases hvw : v = w
  · subst hvw; exact ⟨u, hu, hu'⟩
  · exact ⟨w, Ne.symm hvw, h.symm⟩

theorem conjQuot_nsUnits_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.UnitaryBC.IsSplitAt w → ∀ u ∈ GlobalTheory.MuExist.nsUnits E, GlobalTheory.ConsEta.conjQuot E w u = 1 := by
  intro E _ _ _ w hw u hu
  have key : GlobalTheory.MuExist.nsUnits E ≤ (conjQuot E w).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w', a, hw', -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have hne : w' ≠ w := fun h => hw' (h ▸ hw)
    have hunder : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
      fun h => hw' (isSplitAt_of_under_eq hw h)
    have h1 : Units.map (GlobalTheory.IdeleNormChar.finEval w) (Neutral.B1.localIdele E w' a) = 1 :=
      Units.ext ((Neutral.B1.localIdele_isSupportedAt E w' a).2 w hne.symm)
    have h2 : Units.map (GlobalTheory.IdeleNormChar.finEval w)
        (ideleConj (maximalRealSubfield E) E (Neutral.B1.localIdele E w' a)) = 1 :=
      finEval_ideleMap_localIdele (F := maximalRealSubfield E)
        (alg := (conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra)
        (fun x => (conj (maximalRealSubfield E) E).commutes x) w w' hunder a
    simp only [conjQuot, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.id_apply, _root_.map_div, h1, h2, div_one]
  exact key hu

end GlobalTheory.ConsEta
end
end

section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.FockKFinStep
open GlobalTheory.ThK.EvAt0.PolD LineDeriv

theorem lin_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (b x : κ → mixedEmbedding.mixedSpace F) :
    lin b x = ∑ j, (B.repr b j : ℂ) * lin (B j) x := by
  conv_lhs => rw [← B.sum_repr b]
  simp only [lin, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm]

  simp [map_sum, map_smul, Finset.mul_sum]

theorem fderiv_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (a : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) (x) :
    fderiv ℝ f x a = ∑ j, (B.repr a j : ℂ) * fderiv ℝ f x (B j) := by
  conv_lhs => rw [← B.sum_repr a]

  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Complex.real_smul]

theorem sumAt {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} (s : Finset ι) (g : ι → SInf F κ) (x) :
    (∑ j ∈ s, g j) x = ∑ j ∈ s, g j x := by simp

theorem dOp_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) :
    dOp a b f = ∑ j, (B.repr a j : ℂ) • ∂_{B j} f -
      (2 * Real.pi * Complex.I : ℂ) • ∑ j, (B.repr b j : ℂ) • mulOp (B j) f := by
  refine DFunLike.ext _ _ fun x => ?_
  rw [dOp_apply, fderiv_expand B a f x, lin_expand B b x]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, sumAt, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, mulOp_apply, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

theorem dStep_finiteDimensional : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (P : Submodule ℂ (SInf F κ)),
    FiniteDimensional ℂ P → FiniteDimensional ℂ (GlobalTheory.FockKFin.dStep P) := by
  intro F _ _ κ _ P hP
  let B := Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)
  let T : Submodule ℂ (SInf F κ) :=
    (⨆ j, P.map (lineDerivOpCLM ℂ (SInf F κ) (B j)).toLinearMap) ⊔ ⨆ j, P.map (mulOp (B j)).toLinearMap
  haveI : FiniteDimensional ℂ T := by
    haveI := Submodule.finiteDimensional_iSup (fun j => P.map (lineDerivOpCLM ℂ (SInf F κ) (B j)).toLinearMap)
    haveI := Submodule.finiteDimensional_iSup (fun j => P.map (mulOp (B j)).toLinearMap)
    exact Submodule.finiteDimensional_sup _ _
  refine Submodule.finiteDimensional_of_le (S₂ := T) ?_
  rw [GlobalTheory.FockKFin.dStep, Submodule.span_le]
  rintro _ ⟨a, b, f, hf, rfl⟩
  rw [dOp_expand B]
  refine Submodule.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem j ⟨f, hf, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem (p := fun j => P.map (mulOp (B j)).toLinearMap) j ⟨f, hf, rfl⟩))

end GlobalTheory.FockKFinStep
end
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.continuous_unitaryAdelicComponentAtPlace_explicit : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Continuous (piV G v) := by
  first | (exact @GlobalTheory.OrbFinAf.continuous_piV) | (exact GlobalTheory.OrbFinAf.continuous_piV) | (intros; apply GlobalTheory.OrbFinAf.continuous_piV  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_integralUnitaryPointsAtPlace_mul_mem : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v := by
  first | (exact @GlobalTheory.OrbFinAf.mul_mem_IntV_eventually) | (exact GlobalTheory.OrbFinAf.mul_mem_IntV_eventually) | (intros; apply GlobalTheory.OrbFinAf.mul_mem_IntV_eventually  <;> assumption)
end
