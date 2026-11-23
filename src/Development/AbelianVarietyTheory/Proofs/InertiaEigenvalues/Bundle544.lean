module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle486
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle242
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle069
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle515
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.ZVal

private theorem add_coboundary {G M : Type} [Mul G] [AddCommGroup M]
    (a : G → M →+ M) (u : G → M) (b : M) (g g' : G)
    (ha : a (g * g') b = a g (a g' b))
    (hu : u (g * g') = u g + a g (u g')) :
    u (g * g') + (a (g * g') b - b) =
      (u g + (a g b - b)) + a g (u g' + (a g' b - b)) := by
  rw [ha, hu, map_add (a g), map_sub (a g)]
  abel

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem zval : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l]), Continuous lam → (∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → ∀ g₁ : ↥((HW l).W K s LL h).GKs, lam g₁ = Multiplicative.ofAdd 1 → ∀ z₁ ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₁ = ((F l).E K s LL h).tie.jD T z₁ → ∀ g : ↥((HW l).W K s LL h).GKs, ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  intro D HW F l _ K s LL h T hT c b lam hlc hl1 hZk g₁ hg₁ z₁ hz₁ hZ₁
  -- Reuse the algebra instances needed for the lattice and its tensor products.
  let _ : Algebra ℚ_[l] ↥LL.1 := inferInstance
  let _ : Algebra ↥(OL LL) ↥LL.1 := inferInstance
  let _ : Algebra ↥(OL LL) (RW LL) := inferInstance
  let _ : Algebra ↥(OL LL) (RA LL) := inferInstance
  let _ : Module ↥(OL LL) (RW LL) := Algebra.toModule
  let _ : Module ↥(OL LL) ↥T.L.T := T.modT
  let W := (HW l).W K s LL h
  let E := ((F l).E K s LL h).tie
  let H := W.GKs
  let M := TW (RW LL) T
  let mGroup : AddCommGroup M := TensorProduct.addCommGroup
  let _ : AddGroup M := mGroup.toAddGroup
  let _ : Sub M := mGroup.toAddGroup.toSubNegMonoid.toSub
  let N := aN W T W.X
  let j := (E.jD T).toAddMonoidHom
  let Z := Zf (D.locA l) T H c b
  have hc := GlobalTheory.HerrClassMaps.compact_GK K
  have hcl : IsClosed (H : Set ↥(GK K)) :=
    (lam_exists D HW K s LL h).elim fun _ hx => hx.2.2.2.2
  have hcs : CompactSpace ↥H := isCompact_iff_compactSpace.1 hcl.isCompact
  refine (GlobalTheory.T.exists_weakTopology_wachImage_isClosed D HW F l K s LL h T hT).elim fun τ hτ => ?_
  let _ : TopologicalSpace M := τ
  have hT2 : T2Space M := hτ.1
  have hTG : IsTopologicalAddGroup M := hτ.2.1
  have hact := hτ.2.2.1
  have hemb := hτ.2.2.2.1
  have hclo := hτ.2.2.2.2
  let r := (D.locA l).gRW LL
  let a : ↥H → M →+ M := fun g => (TWact (r (g.1 : GQ l)) T g.1).toAddMonoidHom
  have hmul (g g' : ↥H) : a (g * g') b = a g (a g' b) :=
    GlobalTheory.HerrClassMaps.TWact_mul
      (r ((g * g').1 : GQ l)) (r (g.1 : GQ l)) (r (g'.1 : GQ l))
      (GlobalTheory.HerrClassMaps.gRW_mul (D.locA l) LL (g.1 : GQ l) (g'.1 : GQ l))
      T g.1 g'.1 b
  have haj (g : ↥H) (w : W.DD T) : a g (j w) = j (W.γD T (W.resΓ g.1) w) :=
    (E.jD_act T g.1 w).symm
  let J := N.toAddSubgroup.map j
  have hJm (x : M) : x ∈ J ↔ ∃ w ∈ N, j w = x := Iff.rfl
  have hJ : IsClosed (J : Set M) := hclo
  have hJa (g : ↥H) (x : M) (hx : x ∈ J) : a g x ∈ J :=
    ((hJm x).1 hx).elim fun w hw =>
      (hJm _).2 ⟨_, GlobalTheory.NL.XStab.xstab D HW l K s LL h T _ w hw.1,
        (haj g w).symm.trans (congrArg (fun y => a g y) hw.2)⟩
  have hJk (g : ↥H) (hg : lam g = 1) (x : M) (hx : x ∈ J) : a g x = x :=
    ((hJm x).1 hx).elim fun w hw => calc
      a g x = a g (j w) := congrArg (fun y => a g y) hw.2.symm
      _ = j (W.γD T (W.resΓ g.1) w) := haj g w
      _ = j (W.γD T 1 w) := congrArg (fun δ => j (W.γD T δ w)) (hl1 g hg)
      _ = j w := congrArg (fun y => j y) (W.γD_one T w)
      _ = x := hw.2
  have hCA : ContinuousAdd M := hTG.toContinuousAdd
  have hCS : ContinuousSub M := @IsTopologicalAddGroup.to_continuousSub M τ mGroup.toAddGroup hTG
  let liftC : ↥H → ↥T.L.T := fun g => ⟨c.1 g, c.2.2 g (Set.mem_univ g)⟩
  have hLiftC : Continuous liftC :=
    c.2.1.1.subtype_mk fun g => (liftC g).2
  have hZc : Continuous Z :=
    Continuous.add (M := M) (hemb.comp hLiftC)
      (Continuous.sub (G := M) ((hact b).comp continuous_subtype_val) continuous_const)
  let k : ↥T.L.T → M := fun t => (1 : RW LL) ⊗ₜ[↥(OL LL)] t
  have ha1t (g : ↥H) (t : ↥T.L.T) : a g (k t) = k (T.actT g.1 t) :=
    GlobalTheory.HerrClassMaps.TWact_one_tmul (r (g.1 : GQ l)) T g.1 t
  have hLiftMul (g g' : ↥H) : liftC (g * g') = liftC g + T.actT g.1 (liftC g') :=
    Subtype.ext (c.2.1.2 g g')
  have hZm (g g' : ↥H) : Z (g * g') = Z g + a g (Z g') :=
    add_coboundary a (fun g => k (liftC g)) b g g' (hmul g g') (calc
      k (liftC (g * g')) = k (liftC g + T.actT g.1 (liftC g')) :=
        congrArg (fun t => k t) (hLiftMul g g')
      _ = k (liftC g) + k (T.actT g.1 (liftC g')) :=
        TensorProduct.tmul_add (R := ↥(OL LL)) (1 : RW LL) _ _
      _ = k (liftC g) + a g (k (liftC g')) :=
        congrArg (fun x => k (liftC g) + x) (ha1t g (liftC g')).symm)
  have hZk' (g : ↥H) (hg : lam g = 1) : Z g = 0 := hZk g (hl1 g hg)
  have hzJ : j z₁ ∈ J := (hJm _).2 ⟨z₁, hz₁, rfl⟩
  have HM := (GlobalTheory.NL.ZgAll.mem_and_comm a lam hlc g₁ hg₁ J hJ hJa hJk _ hzJ
    Z hZc hZm hZk' hZ₁).1
  intro g
  exact ((hJm _).1 (HM g)).elim fun w hw => ⟨w, hw.1, hw.2.symm⟩

end GlobalTheory.NL.ZVal
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GroundTheory.Global

namespace GlobalTheory.AbsTwist

variable {F : Type} [Field F] [NumberField F]

theorem eq_zero_of_normOne (f : IdeleGroup F → ℝ) (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x + f y)
    (hk : ∀ k, f (IdeleGroup.diagonal F k) = 0) (x : IdeleGroup F) (hx : x ∈ IdeleGroup.normOneSubgroup F) :
    f x = 0 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup F
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hc.continuousOn
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    linarith
  have hp : ∀ n : ℕ, f (x ^ n) = n * f x := fun n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hm, ih]; push_cast; ring
  have hb : ∀ n : ℕ, (n : ℝ) * |f x| ≤ C := fun n => by
    obtain ⟨k, hk'⟩ := hxD _ (pow_mem hx n)
    have := hC _ hk'
    rwa [hm, hk, zero_add, hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at this
  by_contra h
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |f x|)
  rw [div_lt_iff₀ (abs_pos.2 h)] at hn
  exact absurd (hb n) (not_le.2 hn)

theorem module_expScalar (t : ℝ) :
    (IdeleGroup.ideleModule F (GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)) : ℝ) =
      Real.exp ((Module.finrank ℚ F : ℝ) * t) :=
  GlobalTheory.HeckeOne.ideleNorm_expScalar F t

theorem exists_eq_mul_log_module (f : IdeleGroup F → ℝ) (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x + f y)
    (hk : ∀ k, f (IdeleGroup.diagonal F k) = 0) :
    ∃ a : ℝ, ∀ x, f x = a * Real.log (IdeleGroup.ideleModule F x : ℝ) := by
  let e : ℝ → IdeleGroup F := fun t => GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)
  have hadd : ∀ s t, f (e (s + t)) = f (e s) + f (e t) := fun s t => by
    simp only [e]
    rw [GlobalTheory.HeckeOne.expScalar_add, map_mul, hm]
  have hcont : Continuous fun t => f (e t) :=
    hc.comp ((GlobalTheory.HeckeOne.continuous_mixedIdele F).comp (GlobalTheory.HeckeOne.continuous_expScalar F))
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  refine ⟨f (e 1) / Module.finrank ℚ F, fun x => ?_⟩
  set t : ℝ := Real.log (IdeleGroup.ideleModule F x : ℝ) / Module.finrank ℚ F with ht
  have h1 := map_real_smul (AddMonoidHom.mk' (fun t => f (e t)) hadd) hcont t 1
  simp only [smul_eq_mul, mul_one, AddMonoidHom.mk'_apply] at h1
  have h2 : IdeleGroup.ideleModule F (e t) = IdeleGroup.ideleModule F x := Subtype.ext (by
    have h3 := module_expScalar (F := F) t
    rw [ht, mul_div_cancel₀ _ hn, Real.exp_log (IdeleGroup.ideleModule F x).2] at h3
    exact h3)
  have h4 : (e t)⁻¹ * x ∈ IdeleGroup.normOneSubgroup F := by
    rw [IdeleGroup.normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  have h5 := hm (e t) ((e t)⁻¹ * x)
  rw [mul_inv_cancel_left, eq_zero_of_normOne f hc hm hk _ h4, add_zero, h1, ht] at h5
  rw [h5]; ring


open GlobalTheory.Mem.Chr.CharModel in
theorem exists_norm_eq_exp (ω : HChar F) :
    ∃ c : ℝ, ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ = Real.exp (c * logNorm F x) := by
  have h0 : ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ ≠ 0 := fun x => norm_ne_zero_iff.2 (Units.ne_zero _)
  obtain ⟨a, ha⟩ := exists_eq_mul_log_module (F := F) (fun x => Real.log ‖((ω.1 x : ℂˣ) : ℂ)‖)
    ((Units.continuous_val.comp ω.2.1).norm.log h0)
    (fun x y => by rw [map_mul, Units.val_mul, norm_mul, Real.log_mul (h0 x) (h0 y)])
    (fun k => by
      have : ω.1 (IdeleGroup.diagonal F k) = 1 := ω.2.2 k
      rw [this]; simp)
  obtain ⟨b, hb⟩ := exists_eq_mul_log_module (F := F) (logNorm F) (continuous_logNorm F) (logNorm_mul F)
    (logNorm_principal F)
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine absChar_not_unitary (F := F) fun x => ?_
    change ‖Complex.exp (1 * logNorm F x)‖ = 1
    rw [hb]; simp
  refine ⟨a / b, fun x => ?_⟩
  rw [← Real.exp_log (norm_pos_iff.2 (Units.ne_zero (ω.1 x))), ha x, hb x]
  congr 1
  field_simp

end GlobalTheory.AbsTwist

namespace GlobalTheory.CuspRep.CG

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr.CharModel GlobalTheory.HeckeGal.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem absPow_val_apply (t : ℝ) (x : Ideles E) :
    (((absPow E t).1 x : ℂˣ) : ℂ) = Complex.exp ((t : ℂ) * logNorm E x) := rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem absPow_neg_mul (t : ℝ) : absPow E (-t) * absPow E t = 1 := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change (((absPow E (-t)).1 x : ℂˣ) : ℂ) * (((absPow E t).1 x : ℂˣ) : ℂ) = 1
  rw [absPow_val_apply, absPow_val_apply, ← Complex.exp_add]
  push_cast
  ring_nf
  exact Complex.exp_zero

theorem exists_isUnitary_twist_absPow (π : CG E a) (ha : 1 ≤ a) :
    ∃ (π₀ : CG E a) (t : ℝ), π₀.IsUnitary ∧ π = π₀.twist (absPow E t) := by
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar π
  obtain ⟨c, hc⟩ := GlobalTheory.AbsTwist.exists_norm_eq_exp ω
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  refine ⟨π.twist (absPow E (-(c / a))), c / a, ⟨_, fun x => ?_, hω.twist _⟩, ?_⟩
  · change ‖((ω.1 x : ℂˣ) : ℂ) * ((((absPow E (-(c / a))).1 x) ^ a : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_pow_eq_pow_val, absPow_val_apply, norm_mul, norm_pow, hc x,
      show ((-(c / a) : ℝ) : ℂ) * (logNorm E x : ℂ) = ((-(c / a) * logNorm E x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [Real.exp_eq_one_iff]
    field_simp
    ring
  · rw [← twist_mul, absPow_neg_mul, twist_one]

theorem HasSat.twist {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B)
    {ν : HChar E} (hν : ν.UnrAt w) : (π.twist ν).HasSat w (B.map (· * ν.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ ν w B hν h


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_val_absPow (t : ℝ) (w : HeightOneSpectrum (𝓞 E)) :
    ‖(((absPow E t).val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) := by
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  rw [(absPow_isAbsPow E t).2.1 w, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re,
    Complex.ofReal_re]

theorem HasSat.twist_absPow {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B)
    (t : ℝ) : (π.twist (absPow E t)).HasSat w (B.map (· * (absPow E t).val w)) ∧
      ‖(((absPow E t).val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) :=
  ⟨h.twist ((absPow_isAbsPow E t).1 w), norm_val_absPow t w⟩

end GlobalTheory.CuspRep.CG
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem fontaineBcris_of_tensorInj
    (h : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj) : GlobalTheory.Published.FontaineBcris :=
  GlobalTheory.Published.FontaineBcris.of_rest fun l _ C =>
    ⟨h l C, fun b h1 h2 => GlobalTheory.MemLoc.fundamental_exact l C b h1 h2,
      GlobalTheory.MemLoc.FundOnto.fundOnto l C, GlobalTheory.MemLoc.regular_of_tensorInj l C (h l C)⟩

theorem fontaineBcris : GlobalTheory.Published.FontaineBcris :=
  fontaineBcris_of_tensorInj GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective

end GlobalTheory.MemLoc
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.KFinExp

theorem exists_eval_sum {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (W : Submodule ℂ (Sm E N)) [FiniteDimensional ℂ W] (l : Module.Dual ℂ W) :
    ∃ a : GA E N →₀ ℂ, ∀ w : W, l w = ∑ x ∈ a.support, a x * w.1.1 x := by
  let ev : GA E N → Module.Dual ℂ W := fun x =>
    (LinearMap.proj x : (GA E N → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E N).subtype ∘ₗ W.subtype
  have hs : Submodule.span ℂ (Set.range ev) = ⊤ := Submodule.span_eq_top_of_ne_zero fun z hz => by
    by_contra h
    refine hz (Subtype.ext (Subtype.ext (funext fun x => ?_)))
    by_contra hx
    exact h ⟨ev x, ⟨x, rfl⟩, hx⟩
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hs ▸ Submodule.mem_top : l ∈ _)
  refine ⟨a, fun w => ?_⟩
  rw [← ha, Finsupp.sum, LinearMap.sum_apply]
  rfl

theorem exists_expansion (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (φ : Sm E N)
    (hφ : φ ∈ finVec (cptRep E N)) :
    ∃ (r : ℕ) (ψ : Fin r → Sm E N) (C : Fin r → Lie E N → ℂ),
      (∀ j, ψ j ∈ Submodule.span ℂ (Set.range fun k => cptRep E N k φ)) ∧
      (∀ j, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (C j) (oneL E N)) ∧
      ∀ k : Kinf E N, cptRep E N k φ = ∑ j, C j (toL k.1) • ψ j := by
  set W := Submodule.span ℂ (Set.range fun k => cptRep E N k φ)
  have hf : FiniteDimensional ℂ W := hφ
  let b := Module.finBasis ℂ W
  choose a ha using fun j => exists_eval_sum W (b.coord j)
  refine ⟨_, fun j => (b j).1, fun j y => ∑ x ∈ (a j).support, a j x * chart φ.1 x y, fun j => (b j).2,
    fun j => ContDiffAt.sum fun x _ => contDiffAt_const.mul (contDiffAt_chart φ.2 x isUnit_one), fun k => ?_⟩
  let w : W := ⟨cptRep E N k φ, Submodule.subset_span ⟨k, rfl⟩⟩
  have h := congrArg Subtype.val (b.sum_repr w)
  rw [Submodule.coe_sum] at h
  refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Submodule.coe_smul]
  congr 1
  refine (ha j w).trans (Finset.sum_congr rfl fun x _ => ?_)
  congr 1
  exact (chart_val φ.1 x (Unitary.toUnits k)).symm

end GlobalTheory.KFinExp
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.LieFin

theorem lie_mem_finVec : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (X : Lie E N) (φ : Sm E N),
    φ ∈ finVec (cptRep E N) → lie E N X φ ∈ finVec (cptRep E N) := by
  intro E _ _ _ N X φ hφ
  let S : Submodule ℂ (Sm E N) := Submodule.span ℂ (Set.range fun k => cptRep E N k φ)
  haveI : FiniteDimensional ℂ S := hφ
  let b := Module.finBasis ℝ (Lie E N)
  let T : Submodule ℂ (Sm E N) := ⨆ s, S.map (lie E N (b s))
  haveI : FiniteDimensional ℂ T := by
    haveI : ∀ s, FiniteDimensional ℂ (S.map (lie E N (b s))) := fun s => inferInstance
    exact Submodule.finiteDimensional_iSup _
  have key : ∀ (Z : Lie E N) (ψ : Sm E N), ψ ∈ S → lie E N Z ψ ∈ T := by
    intro Z ψ hψ

    rw [← b.sum_repr Z, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [map_smul, LinearMap.smul_apply]
    have h1 : lie E N (b s) ψ ∈ T :=
      (le_iSup (fun s => S.map (lie E N (b s))) s) (Submodule.mem_map_of_mem hψ)
    have h2 : ((b.repr Z s : ℝ) : ℂ) • lie E N (b s) ψ ∈ T := T.smul_mem _ h1
    simpa [Complex.coe_smul] using h2
  show FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k (lie E N X φ)))
  refine Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have e := congrArg (fun f : Module.End ℂ (Sm E N) => f φ) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  simp only [Module.End.mul_apply] at e
  change rt E N (infGL E N (Unitary.toUnits k)) (lie E N X φ) ∈ T
  have eX : toL (Matrix.of X) = X := rfl
  rw [eX] at e
  rw [e]
  exact key _ _ (Submodule.subset_span ⟨k, rfl⟩)

end GlobalTheory.LieFin
end

section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.WildKill

theorem not_lt_one_of_coprime {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : ℕ} (hab : a.Coprime b)
    (hb : A.valuation (b : Ω) < 1) : ¬ A.valuation (a : Ω) < 1 := by
  intro ha
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.2 hab
  have h1 : (u : Ω) * (a : Ω) + (v : Ω) * (b : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) huv
  have hu : ∀ w : ℤ, A.valuation (w : Ω) ≤ 1 := fun w => (A.valuation_le_one_iff _).2 (intCast_mem A w)
  have h2 : A.valuation ((u : Ω) * (a : Ω) + (v : Ω) * (b : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hu u)) ha
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hu v)) hb
  rw [h1, map_one] at h2
  exact lt_irrefl _ h2

theorem mem_of_wild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (H : Subgroup (G E Ω)) (ho : IsOpen (H : Set (G E Ω))) (σ : G E Ω) (n : ℕ)
    (hn : ¬ A.valuation (n : Ω) < 1) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hH : σ ^ n ∈ H) :
    σ ∈ H := by
  have : IsGalois E Ω := {}
  let C : ClosedSubgroup (G E Ω) := ⟨H, H.isClosed_of_isOpen ho⟩
  have hC : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField C
  rw [← hC, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hy' : (σ ^ n) y = y := (IntermediateField.mem_fixedField_iff H y).1 hy _ hH
  by_contra hne
  have hx : σ y - y ≠ 0 := sub_ne_zero.2 hne
  have hsum : ∑ i ∈ Finset.range n, (σ ^ i) (σ y - y) = 0 := by
    have : ∀ i, (σ ^ i) (σ y - y) = (σ ^ (i + 1)) y - (σ ^ i) y := by
      intro i
      rw [map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i => (σ ^ i) y), hy']
    simp
  have hlt : A.valuation (∑ i ∈ Finset.range n, ((σ ^ i) (σ y - y) / (σ y - y) - 1)) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero fun i _ =>
      GlobalTheory.valuation_pow_apply_div_sub_one_lt A σ hσ _ hx i
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum] at hlt
  apply hn
  simpa using hlt

theorem eq_one_of_wild_of_unipotent :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g l n : ℕ) [Fact g.Prime] [Fact l.Prime], l ≠ g → A.valuation (g : Ω) < 1 → ∀ (K : Type) [Field K] [CharP K l] (rb : G E Ω →* GL (Fin n) K), IsOpen (rb.ker : Set (G E Ω)) → ∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → ((rb s : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n → rb s = 1 := by
  intro E Ω _ _ _ _ _ A g l n hg hl hne hA K _ _ rb ho s hs hc
  refine mem_of_wild A rb.ker ho s (l ^ n)
    (not_lt_one_of_coprime A (Nat.Coprime.pow_left n ((Nat.coprime_primes hl.out hg.out).2 hne)) hA) hs ?_
  rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
  exact GlobalTheory.TameLabels.pow_eq_one_of_charpoly _ hc

end GlobalTheory.WildKill
end
