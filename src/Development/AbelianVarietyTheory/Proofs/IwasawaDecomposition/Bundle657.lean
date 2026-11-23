module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle645
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDisc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle291
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

noncomputable section

namespace GlobalTheory.FlagEmb.PlkSpan

theorem indep_of_plk_ne_zero (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : plk u id ≠ 0) : LinearIndependent K u := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h
  set r := GlobalTheory.FlagEmb.plE N k q
  have hdet : (Matrix.of fun l l' => u l (r l')).det ≠ 0 := hq
  have hA := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  refine LinearIndependent.of_comp (LinearMap.funLeft K K r) ?_
  exact hA

theorem plk_ne_zero_of_indep (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : LinearIndependent K u) : plk u id ≠ 0 := by
  let Q : Matrix (Fin (N + 1)) (Fin k) K := (Matrix.of u).transpose
  have hinj : Function.Injective Q.mulVec := by
    intro x y hxy
    have h0 : Q.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 : ∑ l, (x - y) l • u l = 0 := by
      funext r
      have := congrFun h0 r
      simp only [Q, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have h2 := (Fintype.linearIndependent_iff.1 h) _ h1
    funext l
    exact sub_eq_zero.1 (h2 l)
  obtain ⟨Q', hQ'⟩ := GlobalTheory.matrix_exists_left_inverse_of_field Q hinj
  have hCB := GlobalTheory.FlagEmb.CauchyBinet.lform_plk K N k (Fin k) (Fin k) (fun l => Q' l) u id id
  have hM : (Matrix.of fun l l' => ∑ r, (fun l => Q' l) (id l') r * u (id l) r) = (Q' * Q).transpose := by
    ext l l'
    simp [Q, Matrix.mul_apply, mul_comm]
  rw [hM, hQ', Matrix.transpose_one, Matrix.det_one] at hCB
  intro h0
  rw [h0] at hCB
  simp at hCB

theorem plk_comb (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K) (T : Matrix (Fin k) (Fin k) K) :
    plk (fun l => ∑ j, T l j • u j) id = T.det • plk u id := by
  funext q
  simp only [plk, id, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.det_mul]
  congr 1
  ext l l'
  simp [Matrix.mul_apply, Finset.sum_apply]

theorem main : ∀ (K : Type) [Field K] (N k : ℕ) (u u' : Fin k → Fin (N + 1) → K), (plk u id ≠ 0 ↔ LinearIndependent K u) ∧ (LinearIndependent K u → ((LinearIndependent K u' ∧ Submodule.span K (Set.range u') = Submodule.span K (Set.range u)) ↔ ∃ r : Kˣ, plk u' id = (r : K) • plk u id)) := by
  intro K _ N k u u'
  refine ⟨⟨indep_of_plk_ne_zero K N k u, plk_ne_zero_of_indep K N k u⟩, fun hu => ⟨?_, ?_⟩⟩
  · rintro ⟨hu', hs⟩
    choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun K).1
      (hs ▸ Submodule.subset_span ⟨l, rfl⟩ : u' l ∈ Submodule.span K (Set.range u))
    have h1 := plk_comb K N k u (Matrix.of c)
    have h2 : (fun l => ∑ j, (Matrix.of c) l j • u j) = u' := funext hc
    rw [h2] at h1
    have hd : (Matrix.of c).det ≠ 0 := by
      intro h0
      exact plk_ne_zero_of_indep K N k u' hu' (by rw [h1, h0, zero_smul])
    exact ⟨Units.mk0 _ hd, h1⟩
  · rintro ⟨r, hr⟩
    have h0 := plk_ne_zero_of_indep K N k u hu
    have h0' : plk u' id ≠ 0 := by
      rw [hr]
      exact smul_ne_zero r.ne_zero h0
    have hr' : plk u id = (r : K)⁻¹ • plk u' id := by
      rw [hr, smul_smul, inv_mul_cancel₀ r.ne_zero, one_smul]
    refine ⟨indep_of_plk_ne_zero K N k u' h0', le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u u' _ h0' hr l
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u' u _ h0 hr' l

end GlobalTheory.FlagEmb.PlkSpan
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.exists_integral_flagCell_of_valuedField : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (A : ValuationSubring K) (M : ℕ) (c u : Let m → Fin (M + 1) → K), InBlock c u → (∀ τ, LinearIndependent K fun j : Fin (m τ) => u ⟨τ, j⟩) → ∃ (w : Pm m) (x : CellVar m → K) (d : Let m → K), (∀ v, x v ∈ A) ∧ (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  first | exact @GlobalTheory.FlagEmb.exists_integral_cell | exact GlobalTheory.FlagEmb.exists_integral_cell | (intros; apply GlobalTheory.FlagEmb.exists_integral_cell <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.pluckerVector_blockTriangular_frame_change : ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (c c' : Let m → Fin (M + 1) → S) (d : Let m → S) (k : ℕ) (e : Fin k → Let m), Tri c c' d → Down e → plk c' e = (∏ l, d (e l)) • plk c e := by
  first | exact @GlobalTheory.FlagEmb.plk_tri | exact GlobalTheory.FlagEmb.plk_tri | (intros; apply GlobalTheory.FlagEmb.plk_tri <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

section Lin

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem det_fromRows_mul (A : Matrix m m ℂ) (B : Matrix n n ℂ) (R : Matrix m (m ⊕ n) ℂ) (C : Matrix n (m ⊕ n) ℂ) :
    (Matrix.fromRows (A * R) (B * C)).det = A.det * B.det * (Matrix.fromRows R C).det := by
  rw [← Matrix.det_fromBlocks_zero₂₁ A 0 B, ← Matrix.det_mul, Matrix.fromBlocks_mul_fromRows]
  simp

theorem horVal_change {K : Matrix (m ⊕ n) m ℂ} {C : Matrix n (m ⊕ n) ℂ} {R : Matrix m (m ⊕ n) ℂ}
    {S S' : Matrix (m ⊕ n) n ℂ} (N : Matrix m m ℂ) (M : Matrix n n ℂ) (h : C * K = 0) (hS : C * S = 1)
    (hR : R * (K * N) = 1) (hS' : Mᵀ * C * S' = 1) :
    horVal K C * M.det = horVal (K * N) (Mᵀ * C) * N.det := by
  have h1 : N * R * K = 1 := by
    rw [Matrix.mul_assoc, mul_eq_one_comm, Matrix.mul_assoc]; exact hR
  have h2 : Mᵀ * C * (K * N) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, h]; simp
  have e1 := det_fromRows_mul N 1 R C
  have e2 := det_fromRows_mul 1 Mᵀ R C
  rw [Matrix.one_mul] at e1 e2
  rw [horVal_eq h h1 hS, horVal_eq h2 hR hS', e1, e2]
  simp only [Matrix.det_one, Matrix.det_transpose]
  ring

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem differentiableAt_det {A : V → Matrix m m ℂ} {b : V} (h : ∀ i j, DifferentiableAt ℂ (fun b => A b i j) b) :
    DifferentiableAt ℂ (fun b => (A b).det) b := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun s _ => (differentiableAt_const _).mul ?_
  exact (HasFDerivAt.finsetProd fun i _ => (h _ _).hasFDerivAt).differentiableAt

theorem differentiableAt_horVal {K : V → Matrix (m ⊕ n) m ℂ} {C : V → Matrix n (m ⊕ n) ℂ} {b₀ : V}
    (hK : ∀ i j, DifferentiableAt ℂ (fun b => K b i j) b₀) (hC : ∀ i j, DifferentiableAt ℂ (fun b => C b i j) b₀)
    {R : Matrix m (m ⊕ n) ℂ} (hR : R * K b₀ = 1)
    (h : ∀ᶠ b in 𝓝 b₀, C b * K b = 0 ∧ ∃ S : Matrix (m ⊕ n) n ℂ, C b * S = 1) :
    DifferentiableAt ℂ (fun b => horVal (K b) (C b)) b₀ := by
  have d1 : DifferentiableAt ℂ (fun b => (R * K b).det) b₀ := differentiableAt_det fun i j => by
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hK _ _)
  have d2 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det) b₀ := differentiableAt_det fun i j => by
    rcases i with i | i
    · exact differentiableAt_const _
    · exact hC i j
  have n1 : (R * K b₀).det ≠ 0 := by rw [hR]; simp
  have d3 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det * ((R * K b).det)⁻¹) b₀ :=
    d2.fun_mul (d1.fun_inv n1)
  refine d3.congr_of_eventuallyEq ?_
  filter_upwards [h, d1.continuousAt.eventually_ne n1] with b ⟨h0, S, hS⟩ hb
  have hu : IsUnit (R * K b).det := hb.isUnit
  have e := det_fromRows_mul (R * K b)⁻¹ 1 R (C b)
  rw [Matrix.one_mul] at e
  rw [horVal_eq h0 (R := (R * K b)⁻¹ * R) (by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]) hS, e,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_one]
  ring

end Lin

theorem exists_generates {F : Type} [Field F] (Y : GlobalTheory.ProjVar.Var F) (D : Y.Dv) (h : Y.H0 D ≠ ⊥)
    (h' : Y.H0 (-D) ≠ ⊥) : ∃ s, ∀ y, D.GeneratesAt y s := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h'
  have hst : s * t ∈ Y.H0 0 := add_neg_cancel D ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hs ht
  let L : Y.H0 0 →ₗ[F] Y.H0 0 := (LinearMap.mulLeft F (s * t)).restrict fun g hg =>
    add_zero (0 : Y.Dv) ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hst hg
  have hinj : Function.Injective L := fun a b e =>
    Subtype.ext (mul_left_cancel₀ (mul_ne_zero hs0 ht0) (congrArg Subtype.val e))
  letI : FiniteDimensional F (Y.H0 0) := by
    have := finite_coh_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver 0
    haveI : Module.Finite F Γ(Y.X, ⊤) := .equiv ((coh.zeroUnitEquiv Y.X).restrictScalars F)
    let f : Γ(Y.X, ⊤) →ₗ[F] Y.Fn := (IsScalarTower.toAlgHom F Γ(Y.X, ⊤) Y.Fn).toLinearMap
    have hf : ∀ a, f a ∈ Y.H0 0 := fun a =>
      GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 fun x =>
        CartierDiv.regularAt_zero_iff.2 (regAt_fnOf trivial trivial a)
    apply Module.Finite.of_surjective (f.codRestrict _ hf)
    intro a
    obtain ⟨b, hb⟩ := exists_fnOf_eq (X := Y.X) (U := ⊤) trivial fun x _ =>
      CartierDiv.regularAt_zero_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 a.2 x)
    exact ⟨b, Subtype.ext hb⟩
  obtain ⟨u, hu⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨1, GlobalTheory.ProjVar.Var.eff_iff_one_mem.1 Y.eff_zero⟩
  have hu' : s * t * u = 1 := congrArg Subtype.val hu
  refine ⟨s, fun y => ?_⟩
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have r1 := hg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hs y)
  have r2 := hg.neg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 ht y)
  have r3 := CartierDiv.regularAt_zero_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 u.2 y)
  refine hg.generatesAt_iff.2 ((unitAt_iff (mul_ne_zero hs0 g.ne_zero)).2 ⟨r1, ?_⟩)
  have e : (s * (g : Y.Fn))⁻¹ = t * ((g⁻¹ : Y.Fnˣ) : Y.Fn) * u := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hu', Units.val_inv_eq_inv_val]
    have := g.ne_zero
    field_simp
  exact e ▸ r2.mul r3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {σ : c.F →+* ℂ}
  {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {τ : E →+* ℂ} {x : ∀ i, Idx Dw τ → (Fu.Di i).La}
  {hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E}

end GlobalTheory.ShFam.Hor

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem valAt'_eq_ev {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {U : Y.Opens}
    {x : CxPts p σ} (h : x ∈ CxPts.ptsIn p σ U) (f : Γ(Y, U)) : valAt' x.1 U f = CxPts.ev p σ U f x := by
  rw [CxPts.ev_eq h, CxPts.evHom_eq_evalPt h, TangentOrigin.valAt'_eq_evalPt _ _ h]

theorem chart_change : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ)), DifferentiableOn ℂ ψ ψ.source → DifferentiableOn ℂ ψ.symm ψ.target → (∀ j, HolAlong (c.e.trans ψ).source fun x => (c.e.trans ψ) x j) ∧ IsHolTo (c.e.trans ψ).target (fun z => ((c.e.trans ψ).symm z).1) := by
  intro k _ Y p n σ c ψ hψ hψs
  refine ⟨fun j V _ _ _ B x hB hx hm => ?_, fun U' f => ⟨?_, ?_⟩⟩
  · have hs : ∀ b ∈ B, x b ∈ c.e.source ∧ c.e (x b) ∈ ψ.source := fun b hb => by
      simpa [OpenPartialHomeomorph.trans_source] using hm hb
    have hco : ∀ a, DifferentiableOn ℂ (fun b => c.e (x b) a) B := fun a => by
      refine ((hx c.U (c.x a)).2.mono fun b hb => ⟨hb, c.source_subset (hs b hb).1⟩).congr fun b hb => ?_
      rw [c.apply_eq _ (hs b hb).1, valAt'_eq_ev (c.source_subset (hs b hb).1)]
    have hce : DifferentiableOn ℂ (fun b => c.e (x b)) B := differentiableOn_euclidean.2 hco
    have h2 : DifferentiableOn ℂ (fun b => ψ (c.e (x b))) B := hψ.comp hce fun b hb => (hs b hb).2
    exact differentiableOn_pi.1 h2 j
  · exact (c.e.trans ψ).continuousOn_symm.isOpen_inter_preimage (c.e.trans ψ).open_target
      (CxPts.isOpen_ptsIn U')
  · have hm : ∀ z ∈ {z ∈ (c.e.trans ψ).target | ⊤ ≤ ((c.e.trans ψ).symm z).1 ⁻¹ᵁ U'},
        z ∈ ψ.target ∧ ψ.symm z ∈ c.e.target ∧ c.e.symm (ψ.symm z) ∈ CxPts.ptsIn p σ U' := fun z hz => by
      have h1 := hz.1
      simp only [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at h1
      exact ⟨h1.1, h1.2, hz.2⟩
    have h2 : DifferentiableOn ℂ (CxPts.ev p σ U' f ∘ c.e.symm ∘ ψ.symm)
        {z ∈ (c.e.trans ψ).target | ⊤ ≤ ((c.e.trans ψ).symm z).1 ⁻¹ᵁ U'} :=
      (c.holo U' f).comp (hψs.mono fun z hz => (hm z hz).1) fun z hz => ⟨(hm z hz).2.1, (hm z hz).2.2⟩
    refine h2.congr fun z hz => ?_
    exact valAt'_eq_ev (hm z hz).2.2 f

end GlobalTheory.ShFam.Hor.LogCh
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

theorem exists_log_lift {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (hz : ‖z‖ < 1 / 2) (h0 : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) :
    ∃ s ∈ logDom n a, logExp a s = z ∧ (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) ∧
      1 + ‖s‖ ≤ 5 * (1 + |Real.log ‖∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k‖|) := by
  classical
  set s : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.log (z k) else z k with hs
  have hzk : ∀ k, ‖z k‖ < 1 / 2 := fun k => lt_of_le_of_lt (norm_le_pi_norm z k) hz
  have hpos : ∀ k : Fin n, (k : ℕ) < a → 0 < ‖z k‖ := fun k hk => norm_pos_iff.mpr (h0 k hk)
  have hlogneg : ∀ k : Fin n, (k : ℕ) < a → Real.log ‖z k‖ < 0 := fun k hk =>
    Real.log_neg (hpos k hk) (by linarith [hzk k])
  set ℓ := |Real.log ‖∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k‖| with hℓ
  have hℓk : ∀ k : Fin n, (k : ℕ) < a → -Real.log ‖z k‖ ≤ ℓ := by
    intro k hk
    rw [hℓ, norm_prod, Real.log_prod]
    · calc -Real.log ‖z k‖ ≤ ∑ j ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), -Real.log ‖z j‖ := by
            apply Finset.single_le_sum (f := fun j => -Real.log ‖z j‖)
            · intro j hj
              have := hlogneg j (Finset.mem_filter.mp hj).2
              linarith
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
        _ = -∑ j ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), Real.log ‖z j‖ := by
            rw [Finset.sum_neg_distrib]
        _ ≤ _ := neg_le_abs _
    · intro j hj
      exact (hpos j (Finset.mem_filter.mp hj).2).ne'
  have hℓ0 : 0 ≤ ℓ := abs_nonneg _
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : (k : ℕ) < a
    · simp only [hk, if_true, hs]
      rw [Complex.log_re]
      exact hlogneg k hk
    · simp only [hk, if_false, hs]
      linarith [hzk k]
  · funext k
    by_cases hk : (k : ℕ) < a
    · simp only [logExp, hk, if_true, hs]
      exact Complex.exp_log (h0 k hk)
    · simp only [logExp, hk, if_false, hs]
  · intro j hj
    simp only [hj, if_true, hs]
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _
  · have hsk : ∀ k, ‖s k‖ ≤ ℓ + 4 := by
      intro k
      by_cases hk : (k : ℕ) < a
      · simp only [hk, if_true, hs]
        have h1 : ‖Complex.log (z k)‖ ≤ |(Complex.log (z k)).re| + |(Complex.log (z k)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        rw [Complex.log_re, Complex.log_im] at h1
        have h2 : |Real.log ‖z k‖| = -Real.log ‖z k‖ := abs_of_neg (hlogneg k hk)
        have h3 := Complex.abs_arg_le_pi (z k)
        have h4 := hℓk k hk
        linarith [Real.pi_lt_four]
      · simp only [hk, if_false, hs]
        linarith [hzk k]
    have : ‖s‖ ≤ ℓ + 4 := (pi_norm_le_iff_of_nonneg (by linarith)).mpr hsk
    linarith

theorem eventually_entries_le {V m n : Type} [TopologicalSpace V] [Fintype m] [Fintype n] {W : V → Matrix m n ℂ} {b₀ : V}
    (h : ContinuousAt W b₀) : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ b in 𝓝 b₀, ∀ i j, ‖W b i j‖ ≤ M := by
  classical
  have hij : ∀ i j, ∀ᶠ b in 𝓝 b₀, ‖W b i j‖ < ‖W b₀ i j‖ + 1 := by
    intro i j
    have hc : ContinuousAt (fun b => ‖W b i j‖) b₀ :=
      continuous_norm.continuousAt.comp ((continuous_id.matrix_elem i j).continuousAt.comp h)
    exact hc.eventually_lt continuousAt_const (lt_add_one _)
  refine ⟨∑ i, ∑ j, (‖W b₀ i j‖ + 1), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  · have hall : ∀ᶠ b in 𝓝 b₀, ∀ i j, ‖W b i j‖ < ‖W b₀ i j‖ + 1 :=
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hij i j
    filter_upwards [hall] with b hb i j
    calc ‖W b i j‖ ≤ ‖W b₀ i j‖ + 1 := (hb i j).le
      _ ≤ ∑ j', (‖W b₀ i j'‖ + 1) :=
          Finset.single_le_sum (f := fun j' => ‖W b₀ i j'‖ + 1) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖W b₀ i' j'‖ + 1) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖W b₀ i' j'‖ + 1))
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem differentiableOn_finset_prod {V J : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {u : Finset J} {f : J → V → ℂ}
    {B : Set V} (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) B) : DifferentiableOn ℂ (fun b => ∏ i ∈ u, f i b) B := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert i u hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i u)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GlobalTheory.ShFam.Hor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.logDom_chart_props : ∀ (n a : ℕ), IsOpen (GlobalTheory.ShFam.Hor.logDom n a) ∧ Convex ℝ (GlobalTheory.ShFam.Hor.logDom n a) ∧ (∀ s, AnalyticAt ℂ (GlobalTheory.ShFam.Hor.logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧ Set.MapsTo (GlobalTheory.ShFam.Hor.logExp a) (GlobalTheory.ShFam.Hor.logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) := by
  intro n a
  have hEq : GlobalTheory.ShFam.Hor.logDom n a = ⋂ k : Fin n, (fun s : Fin n → ℂ => s k) ⁻¹' (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1) := by
    ext s
    simp only [GlobalTheory.ShFam.Hor.logDom, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    refine forall_congr' fun k => ?_
    split_ifs <;> simp [Metric.mem_ball, dist_zero_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hEq]
    refine isOpen_iInter_of_finite fun k => ?_
    refine IsOpen.preimage (continuous_apply k) ?_
    split_ifs
    · exact isOpen_lt Complex.continuous_re continuous_const
    · exact Metric.isOpen_ball
  · rw [hEq]
    refine convex_iInter fun k => ?_
    have hc : Convex ℝ (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1) := by
      split_ifs
      · exact convex_halfSpace_lt (f := Complex.re) Complex.reLm.isLinear 0
      · exact convex_ball 0 1
    exact hc.linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k)
  · intro s
    rw [analyticAt_pi_iff]
    intro k
    show AnalyticAt ℂ (fun s : Fin n → ℂ => if (k : ℕ) < a then Complex.exp (s k) else s k) s
    have hp : AnalyticAt ℂ (fun s : Fin n → ℂ => s k) s :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt s
    split_ifs
    · exact analyticAt_cexp.comp hp
    · exact hp
  · intro s hs
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
    intro k
    have hk := hs k
    simp only [GlobalTheory.ShFam.Hor.logExp]
    split_ifs at hk ⊢ with h
    · rw [Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hk
    · exact hk
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

theorem _root_.GlobalTheory.T.exists_semi_abelian_exponential_along_disc : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : ℂ → (Sp ℂ ⟶ X)) (r : ℝ), IsSemiAbelian G → 0 < r → IsHolTo (Metric.ball (0 : ℂ) r) y → ∃ (g : ℕ) (ρ : ℝ) (e : ∀ u, (Fin g → ℂ) → (Over.mk (y u) ⟶ G)), 0 < ρ ∧ ρ ≤ r ∧ IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g → ℂ) => (show Sp ℂ ⟶ G.left from (e q.1 q.2).left)) ∧ (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e u (z + w) = e u z * e u w) ∧ Function.Surjective (e u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e u z).left)) ∧ (∀ w, ∃! v : epsPt (y u) ⟶ G, IsDerivAt0 (fun z => (e u z).left) w v.left) ∧ (∀ v : epsPt (y u) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e u 0).left → ∃! w, IsDerivAt0 (fun z => (e u z).left) w v.left)) ∧ ∀ z₀, e 0 z₀ = 1 → ∃ ζ : ℂ → (Fin g → ℂ), ζ 0 = z₀ ∧ AnalyticAt ℂ ζ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), e u (ζ u) = 1 := by
  first | exact @GlobalTheory.RelExp.exists_exp_along_disc | exact GlobalTheory.RelExp.exists_exp_along_disc | (intros; apply GlobalTheory.RelExp.exists_exp_along_disc <;> assumption)
end
