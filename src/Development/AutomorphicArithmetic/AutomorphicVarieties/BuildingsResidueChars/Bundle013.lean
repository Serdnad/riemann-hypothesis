module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.ResidualAutomorphyOfLinkedEnds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LatCls
public import Formalism.RealPlaceAnalysis.Bundle003
public import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
public import Formalism.RealPlaceAnalysis.Bundle005
public import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv

@[expose] public section

section

open MulAction UpperTheory.V.Z.Sym

private theorem smul_quotient_eq_self_iff_exists_conj_out (G : Type) [Group G] (U : Subgroup G) (y : G ⧸ U) (a : G) :
    a • y = y ↔ ∃ u ∈ U, (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out y))) u = a := by
  set g := Quotient.out y with hg
  have hy : ((g : G) : G ⧸ U) = y := Quotient.out_eq y
  rw [← hy, MulAction.Quotient.smul_mk, QuotientGroup.eq]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, smul_eq_mul]
  constructor
  · intro h
    refine ⟨g⁻¹ * a * g, ?_, by group⟩
    have := inv_mem h
    simpa [mul_assoc] using this
  · rintro ⟨u, hu, rfl⟩
    have : (g * u * g⁻¹ * g)⁻¹ * g = u⁻¹ := by group
    rw [this]; exact inv_mem hu

theorem UpperTheory.symmetric_fiber_trace_kernel :
    UpperTheory.V.Z.Sym.Glob.Fib.TrKer := by
  intro Γ G V _ _ _ _ _ B hFin hω hΓ₀ f hf
  classical
  set s := Base.Tw.one B with hs
  let δ : ConjClasses Γ → Γ := fun i => Classical.choose (ConjClasses.exists_rep i)
  have hδ : ∀ i, ConjClasses.mk (δ i) = i := fun i => Classical.choose_spec (ConjClasses.exists_rep i)
  have hRel : ∀ a b : Γ, s.Rel a b ↔ IsConj a b := by
    intro a b
    simp only [Base.Tw.Rel, hs, Base.Tw.one, hΓ₀, Subgroup.mem_bot, MulEquiv.refl_apply, exists_eq_left, mul_one, isConj_iff]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x⁻¹, by group⟩
    · rintro ⟨c, rfl⟩; exact ⟨c⁻¹, by group⟩
  have hCent : ∀ (a x : Γ), x ∈ s.Cent a ↔ x * a = a * x := by
    intro a x
    show (∃ z ∈ B.Γ₀, x⁻¹ * a * (MulEquiv.refl Γ) x = a * z) ↔ _
    simp only [hΓ₀, Subgroup.mem_bot, exists_eq_left, mul_one, MulEquiv.refl_apply]
    constructor
    · intro h; calc x * a = x * (x⁻¹ * a * x) := by rw [h]
        _ = a * x := by group
    · intro h; calc x⁻¹ * a * x = x⁻¹ * (x * a) := by rw [mul_assoc, h]
        _ = a := by group
  have h2 : ∀ z ∈ (⊥ : Subgroup Γ), ∀ y : G ⧸ B.U, B.ι z • y = y := fun z hz y => by
    rw [Subgroup.mem_bot.mp hz, map_one, one_smul]
  have h3 : ∀ h γ : Γ, LinearMap.trace ℂ V (B.W (h * γ * h⁻¹)) = LinearMap.trace ℂ V (B.W γ) := fun h γ => by
    rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]
  have h4 : ∀ u ∈ B.U, ∀ g : G, f (u⁻¹ * g * u) = f g := fun u hu g => by
    have hl := hf.left ⟨u⁻¹, inv_mem hu⟩ (g * u)
    have hr := hf.right ⟨u, hu⟩ g
    simp only [hs, Base.Tw.one, MulEquiv.refl_apply, hω, MonoidHom.one_apply, Units.val_one, inv_one, one_mul] at hl hr
    rw [mul_assoc, hl, hr]
  have h5 : ∀ g : G, {γ | LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0}.Finite := fun g =>
    (UpperTheory.orbitalFiber_support_finite Γ G V B hFin hΓ₀ f hf g).subset (fun γ h => right_ne_zero_of_mul h)
  have h8 : ∀ i x, x ∈ ((s.Cent (δ i)).subtype).range ↔ x * δ i = δ i * x := fun i x => by
    rw [Subgroup.range_subtype, hCent]
  have h9 : ∀ (i i' : ConjClasses Γ) (h : Γ), δ i' = h * δ i * h⁻¹ → i = i' := fun i i' h e => by
    rw [← hδ i, ← hδ i', ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]; exact ⟨h, e.symm⟩
  have h10 : ∀ (γ : Γ) (g : G), LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0 →
      ∃ i h, γ = h * δ i * h⁻¹ := fun γ g _ => by
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ (ConjClasses.mk γ)))
    exact ⟨ConjClasses.mk γ, c, hc.symm⟩
  have h7 : ∀ y : G ⧸ B.U, (⊥ : Subgroup Γ).relIndex (Subgroup.comap B.ι (stabilizer G y)) ≠ 0 := fun y => by
    have := hFin.stab (Quotient.out y)
    rw [hΓ₀] at this
    convert this using 2
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, mem_stabilizer_iff, Subgroup.mem_map]
    exact smul_quotient_eq_self_iff_exists_conj_out G B.U y (B.ι x)
  have hT := (Tf.trace Γ G V B hFin s f hf (ConjClasses Γ) δ (fun i j h => by
      rw [← hδ i, ← hδ j, ConjClasses.mk_eq_mk_iff_isConj]; exact (hRel _ _).mp h)
    (fun γ _ => ⟨ConjClasses.mk γ, (hRel _ _).mpr (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ _))⟩)).2
  have hP := UpperTheory.orbitalFiber_pair_correspondence Γ G (ConjClasses Γ) B.ι ⊥ B.U (fun γ => LinearMap.trace ℂ V (B.W γ)) f δ
    (fun i => ↥(s.Cent (δ i))) (fun i => (s.Cent (δ i)).subtype) bot_le h2 h3 h4 h5
    hFin.cls h7 h8 h9 h10
  rw [hT, hP]
  refine finsum_congr fun i => ?_
  simp only [Base.Tw.term, hs, Base.Tw.one, LinearMap.comp_id]
  congr 2
  rw [hΓ₀]; rfl
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem im_form {K : Type} [Field K] {τ : K} (x y : Etau K τ) :
    (x * star y).im = x.im * y.re - x.re * y.im := by
  simp; ring

private theorem smul_im' {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (r : O)
    (x : Etau K τ) : (r • x).im = algebraMap O K r * x.im := by
  rw [QuadraticAlgebra.im_smul, Algebra.smul_def]

private theorem smul_re' {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (r : O)
    (x : Etau K τ) : (r • x).re = algebraMap O K r * x.re := by
  rw [QuadraticAlgebra.re_smul, Algebra.smul_def]

private theorem fix_lat {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {τ t : K} {S : Set (Etau K τ)} (h : IsFixP O τ t S) : IsLat O τ S := by
  classical
  obtain ⟨s, hs⟩ := h.fg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (s.image (fun x : Etau K τ => t * x.im) ∪ s.image (fun x : Etau K τ => t * x.re))
  set B : K := algebraMap O K (b : O) with hBdef
  have hB : B ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have key : ∀ x ∈ Submodule.span O (s : Set (Etau K τ)),
      t * x.im * B ∈ (algebraMap O K).range ∧ t * x.re * B ∈ (algebraMap O K).range := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r1, hr1⟩ := hb (t * x.im) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
      obtain ⟨r2, hr2⟩ := hb (t * x.re) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))
      refine ⟨⟨r1, ?_⟩, ⟨r2, ?_⟩⟩
      · rw [hr1, Algebra.smul_def, hBdef]
        ring
      · rw [hr2, Algebra.smul_def, hBdef]
        ring
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · have e := add_mem hx.1 hy.1
        convert e using 1
        simp only [QuadraticAlgebra.im_add]
        ring
      · have e := add_mem hx.2 hy.2
        convert e using 1
        simp only [QuadraticAlgebra.re_add]
        ring
    | smul r x _ hx =>
      rw [smul_im', smul_re']
      refine ⟨?_, ?_⟩
      · have e := mul_mem (RingHom.mem_range_self (algebraMap O K) r) hx.1
        convert e using 1
        ring
      · have e := mul_mem (RingHom.mem_range_self (algebraMap O K) r) hx.2
        convert e using 1
        ring
  have m1 : B • (1 : Etau K τ) ∈ S := by
    rw [h.dual]
    intro x hx
    rw [hs] at hx
    have e : (x * star (B • (1 : Etau K τ))).im = x.im * B := by
      rw [im_form]
      simp
    rw [e, ← mul_assoc]
    exact (key x hx).1
  have m2 : B • (ω : Etau K τ) ∈ S := by
    rw [h.dual]
    intro x hx
    rw [hs] at hx
    have e : (x * star (B • (ω : Etau K τ))).im = -(x.re * B) := by
      rw [im_form]
      simp
    rw [e, mul_neg, ← mul_assoc]
    exact neg_mem (key x hx).2
  refine ⟨h.fg, ?_⟩
  rw [eq_top_iff]
  intro y _
  have e : y = (y.re / B) • (B • (1 : Etau K τ)) + (y.im / B) • (B • (ω : Etau K τ)) := by
    ext <;> simp <;> field_simp
  rw [e]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span m1))
    (Submodule.smul_mem _ _ (Submodule.subset_span m2))

private theorem dual_pair {O K : Type} [CommRing O] [Field K] [Algebra O K]
    {τ : K} (u v : Etau K τ) (hd : u.im * v.re - u.re * v.im ≠ 0) (y : Etau K τ) :
    y ∈ (Submodule.span O {u, v} : Submodule O (Etau K τ)) ↔
      ∀ x ∈ (Submodule.span O {u, v} : Submodule O (Etau K τ)),
        (u.im * v.re - u.re * v.im)⁻¹ * (x * star y).im ∈ (algebraMap O K).range := by
  constructor
  · intro hy x hx
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.1 hy
    obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.1 hx
    refine ⟨p * s - q * r, ?_⟩
    rw [im_form]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, smul_im', smul_re',
      map_sub, map_mul]
    field_simp
    ring
  · intro H
    obtain ⟨β, hβ⟩ := H u (Submodule.subset_span (by simp))
    obtain ⟨α, hα⟩ := H v (Submodule.subset_span (by simp))
    rw [im_form] at hα hβ
    refine Submodule.mem_span_pair.2 ⟨-α, β, ?_⟩
    ext
    · simp only [QuadraticAlgebra.re_add, smul_re', map_neg, hα, hβ]
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_add, smul_im', map_neg, hα, hβ]
      field_simp
      ring

theorem UpperTheory.isLattice_iff_fixedPoint_quadraticTorus :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ S : Set (Etau K τ), (∀ t : K, IsFixP O τ t S → IsLat O τ S) ∧ (IsLat O τ S → (∀ y ∈ S, ω * y ∈ S) → ∃ t : K, t ≠ 0 ∧ IsFixP O τ t S) := by
  intro O K _ _ _ _ _ Δ τ hL hτ S
  haveI := hL.frac
  refine ⟨fun t h => fix_lat h, fun hS hst => ?_⟩
  obtain ⟨y, x, hx, -, -, e⟩ := latCls O K Δ τ hL hτ S hS
  have e' : S = (Submodule.span O {(y : Etau K τ), (y : Etau K τ) * x} : Submodule O (Etau K τ)) := by
    rw [e]
    ext w
    simp only [SetLike.mem_coe, Submodule.mem_span_pair, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨p, q, rfl⟩, rfl⟩
      exact ⟨p, q, by simp [mul_add]⟩
    · rintro ⟨p, q, rfl⟩
      exact ⟨_, ⟨p, q, rfl⟩, by simp [mul_add]⟩
  have hn : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 := (isUnit_iff_norm_isUnit.1 y.isUnit).ne_zero
  have hd : (y : Etau K τ).im * ((y : Etau K τ) * x).re - (y : Etau K τ).re * ((y : Etau K τ) * x).im ≠ 0 := by
    have : (y : Etau K τ).im * ((y : Etau K τ) * x).re - (y : Etau K τ).re * ((y : Etau K τ) * x).im =
        -(QuadraticAlgebra.norm (y : Etau K τ) * x.im) := by
      simp [norm_def]; ring
    rw [this]
    exact neg_ne_zero.2 (mul_ne_zero hn hx)
  refine ⟨_, inv_ne_zero hd, hS.fg, fun w => ?_, hst⟩
  rw [e']
  exact dual_pair _ _ hd w
end

section

open GroundTheory.Automorphic.HarishChandra in
private noncomputable def UpperTheory.V.Af.CuspFin.vermaRep {n : ℕ} (lam : Fin n → ℂ) :
    U n →ₐ[ℂ] Module.End ℂ (U n ⧸ vermaIdeal lam) where
  toFun x := (vermaIdeal lam).mapQ (vermaIdeal lam) (LinearMap.mulLeft ℂ x)
    (fun _ hy => mul_mem_vermaIdeal lam x hy)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    simp
  map_mul' a b := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk (a * b * y) : U n ⧸ vermaIdeal lam) = Submodule.Quotient.mk (a * (b * y))
    rw [mul_assoc]
  map_zero' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    simp
  map_add' a b := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk ((a + b) * y) : U n ⧸ vermaIdeal lam) =
      Submodule.Quotient.mk (a * y) + Submodule.Quotient.mk (b * y)
    rw [add_mul, Submodule.Quotient.mk_add]
  commutes' r := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk (algebraMap ℂ (U n) r * y) : U n ⧸ vermaIdeal lam) =
      r • Submodule.Quotient.mk y
    rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.V.Af.CuspFin.vermaRep_one {n : ℕ} (lam : Fin n → ℂ) (x : U n) :
    UpperTheory.V.Af.CuspFin.vermaRep lam x (Submodule.Quotient.mk 1) = Submodule.Quotient.mk x := by
  change Submodule.Quotient.mk (x * 1) = _
  rw [mul_one]

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.V.Af.CuspFin.one_notMem_vermaIdeal {n : ℕ} (lam : Fin n → ℂ) :
    (1 : U n) ∉ vermaIdeal lam := by
  intro h
  have h0 := vermaCoord_vermaIdeal lam h
  have hnu : ¬ HasUpper (0 : Fin n × Fin n →₀ ℕ) := by
    rintro ⟨b, -, hne⟩
    exact hne rfl
  have hd : diagExp (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext; simp
  rw [← canon_zero, vermaCoord_canon_of_not lam hnu, hd, Finsupp.single_eq_zero] at h0
  simp at h0

open GroundTheory.Automorphic.HarishChandra UpperTheory.V.Af.CuspFin in
theorem UpperTheory.harishChandraProj_quantumDet_eq_prod :
    ∀ (n : ℕ) (u : ℂ), GroundTheory.Automorphic.HarishChandra.hcProjLin (Formalism.REAL.qdet (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) = ∏ k : Fin n, (MvPolynomial.C (u - (k : ℂ)) + MvPolynomial.X k) := by
  intro n u
  refine MvPolynomial.funext fun lam => ?_
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := fun a b c d => e_mul_sub_mul (a, b) (c, d)
  have hgl' : Formalism.REAL.GlRel (fun i j : Fin n => vermaRep lam (e (i, j))) := fun a b c d => by
    have h := congrArg (vermaRep lam) (hgl a b c d)
    simp only [map_sub, map_mul, apply_ite (vermaRep lam), map_zero] at h
    exact h
  have hup : ∀ a, IsUpper a → vermaRep lam (e a) (Submodule.Quotient.mk 1) = 0 := fun a ha => by
    rw [vermaRep_one, Submodule.Quotient.mk_eq_zero]
    exact nPlusU_le_vermaIdeal lam (Submodule.subset_span ⟨1, a, ha, one_mul _⟩)
  have hH : ∀ k, vermaRep lam (e (k, k)) (Submodule.Quotient.mk 1) =
      lam k • (Submodule.Quotient.mk 1 : U n ⧸ vermaIdeal lam) := fun k => by
    rw [vermaRep_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← Algebra.algebraMap_eq_smul_one]
    simpa using mul_e_sub_mem_vermaIdeal lam 1 k
  have h1 := rep_apply_of_highestWeight (vermaRep lam) lam hup hH
    (z := Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u)
    (fun k => (Formalism.REAL.qDetCentral _ n _ hgl u k k).symm)
  have h2 := Formalism.REAL.qDetHW _ n _ lam (Submodule.Quotient.mk 1) hgl'
    ⟨hH, fun a b hab => hup (a, b) hab⟩ u
  rw [map_qdet, h2] at h1
  have hv : (Submodule.Quotient.mk 1 : U n ⧸ vermaIdeal lam) ≠ 0 := fun h =>
    one_notMem_vermaIdeal lam ((Submodule.Quotient.mk_eq_zero _).1 h)
  rw [← smul_left_injective ℂ hv h1]
  simp
end
