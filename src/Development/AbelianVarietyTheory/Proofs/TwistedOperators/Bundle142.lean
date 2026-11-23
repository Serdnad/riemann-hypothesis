module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceRed

section Gen

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem mem_max_iff (a : v.adicCompletionIntegers F) :
    IsLocalRing.residue (v.adicCompletionIntegers F) a = 0 ↔ Valued.v (a : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))

theorem exists_red {A : Type} [CommRing A] (I : Ideal A) (ψ : A →+* v.adicCompletionIntegers F)
    (hI : ∀ x, x ∈ I ↔ Valued.v (ψ x : v.adicCompletion F) < 1)
    (hs : ∀ a : v.adicCompletionIntegers F, ∃ x, Valued.v ((a : v.adicCompletion F) - ψ x) < 1) :
    ∃ r : v.adicCompletionIntegers F →+* A ⧸ I, (∀ x, r (ψ x) = Ideal.Quotient.mk I x) ∧
      ∀ a, r a = 0 ↔ Valued.v (a : v.adicCompletion F) < 1 := by
  let q := Ideal.Quotient.lift I ((IsLocalRing.residue _).comp ψ)
    (fun x hx => (mem_max_iff _).2 ((hI x).1 hx))
  have hq : Function.Bijective q := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((hI x).2 ((mem_max_iff _).1 hy))
    · intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨x, hx⟩ := hs a
      refine ⟨Ideal.Quotient.mk I x, ?_⟩
      show IsLocalRing.residue _ (ψ x) = _
      rw [eq_comm, ← sub_eq_zero, ← map_sub, mem_max_iff]
      exact hx
  let e := RingEquiv.ofBijective q hq
  refine ⟨(e.symm : _ →+* A ⧸ I).comp (IsLocalRing.residue _), fun x => ?_, fun a => ?_⟩
  · show e.symm _ = _
    rw [RingEquiv.symm_apply_eq]
    rfl
  · show e.symm _ = 0 ↔ _
    rw [map_eq_zero_iff _ e.symm.injective, mem_max_iff]

theorem exists_unitPart : ∃ t : (v.adicCompletion F)ˣ →* v.adicCompletionIntegers F,
    ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → (t u : v.adicCompletion F) = u := by
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  have hne : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) ≠ 0 := fun u =>
    (Valuation.ne_zero_iff _).2 u.ne_zero
  have hv : ∀ u : (v.adicCompletion F)ˣ,
      Valued.v ((u : v.adicCompletion F) * p ^ (WithZero.log (Valued.v (u : v.adicCompletion F)))) = 1 := by
    intro u
    rw [map_mul, map_zpow₀, hp, ← WithZero.exp_zsmul]
    conv_lhs => lhs; rw [← WithZero.exp_log (hne u)]
    rw [← WithZero.exp_add]
    simp
  refine ⟨⟨⟨fun u => ⟨(u : v.adicCompletion F) * p ^ (WithZero.log (Valued.v (u : v.adicCompletion F))),
    (hv u).le⟩, ?_⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    simp
  · intro a b
    apply Subtype.ext
    show ((a * b : (v.adicCompletion F)ˣ) : v.adicCompletion F) * p ^ _ = (_ * p ^ _) * (_ * p ^ _)
    rw [Units.val_mul, map_mul, WithZero.log_mul (hne a) (hne b), zpow_add₀ hp0]
    ring
  · intro u hu
    show (u : v.adicCompletion F) * p ^ _ = _
    rw [hu]
    simp

end Gen

variable {D : D7} {v : FinPl D} (φ : SplitProj D v)

def rdQh : D.host.E →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Fv D.host.F v) (B := D.host.E)).toRingHom

theorem rdQh_apply (x : D.host.E) : rdQh φ x = rdQ φ x := rfl

theorem rdQ_int (x : 𝓞 D.host.E) : rdQ φ (x : D.host.E) ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨p, hm, hp⟩ : IsIntegral ℤ (x : D.host.E) := x.2
  refine ReciprocityTheory.Aut.adic_le_one_of_poly v p hm ?_
  have := congrArg (rdQh φ) hp
  rw [Polynomial.hom_eval₂, map_zero, RingHom.ext_int ((rdQh φ).comp _) (Int.castRingHom _)] at this
  exact this

theorem rdQ_alg (y : D.host.F) :
    rdQ φ (algebraMap D.host.F D.host.E y) = algebraMap D.host.F (Fv D.host.F v) y := by
  show φ ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Fv D.host.F v) (B := D.host.E))
    (algebraMap D.host.F D.host.E y)) = _
  rw [AlgHom.commutes]
  exact φ.commutes (algebraMap D.host.F (Fv D.host.F v) y)

def rdO : 𝓞 D.host.E →+* v.adicCompletionIntegers D.host.F :=
  ((rdQh φ).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict (v.adicCompletionIntegers D.host.F) (rdQ_int φ)

theorem rdO_coe (x : 𝓞 D.host.E) : (rdO φ x : Fv D.host.F v) = rdQ φ (x : D.host.E) := rfl

theorem rdO_dense (a : v.adicCompletionIntegers D.host.F) :
    ∃ x, Valued.v ((a : Fv D.host.F v) - rdO φ x) < 1 := by
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v (a : Fv D.host.F v) a.2
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y, ?_⟩
  have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F y) := by
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [rdO_coe, h1, rdQ_alg]
  exact hy

theorem rdE_tmul (x : D.host.E) (y : Af D.host.F) :
    rdE φ (x ⊗ₜ[D.host.F] y) = φ (y v ⊗ₜ[D.host.F] x) := rfl

theorem rdE_int (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    rdE φ N ∈ v.adicCompletionIntegers D.host.F := by
  have hle : Formalism.L2.Herm.intAf D.host.F D.host.E ≤
      (v.adicCompletionIntegers D.host.F).toSubring.comap (rdE φ) := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨b, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b0, hb0⟩ := b.2
      show rdE φ ((b : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∈ v.adicCompletionIntegers D.host.F
      rw [← hb0]
      exact rdQ_int φ b0
    · show rdE φ ((1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F)) ∈ v.adicCompletionIntegers D.host.F
      rw [rdE_tmul]
      have : φ ((y : Af D.host.F) v ⊗ₜ[D.host.F] (1 : D.host.E)) = (y : Af D.host.F) v := φ.commutes _
      rw [this]
      exact y.2 v
  exact hle hN

def rdS : Formalism.L2.Herm.intAf D.host.F D.host.E →+* v.adicCompletionIntegers D.host.F :=
  ((rdE φ).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F)
    (fun N => rdE_int φ N.1 N.2)

theorem rdS_oToS (x : 𝓞 D.host.E) : rdS φ (Formalism.L2.DIV.oToS D.host.F D.host.E x) = rdO φ x := rfl

theorem eq_resS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (PP : Formalism.L2.DIV.Pl E) (g : Formalism.L2.Herm.intAf F E →+* Formalism.L2.DIV.kP PP)
    (hg : ∀ x, g (Formalism.L2.DIV.oToS F E x) = Ideal.Quotient.mk PP.asIdeal x) (N : Formalism.L2.Herm.intAf F E) :
    g N = Formalism.L2.DIV.resS F PP N := by
  have key : ∀ g' : Formalism.L2.Herm.intAf F E →+* Formalism.L2.DIV.kP PP,
      (∀ x, g' (Formalism.L2.DIV.oToS F E x) = Ideal.Quotient.mk PP.asIdeal x) →
      Formalism.L2.DIV.idS F PP.asIdeal ≤ RingHom.ker g' := by
    intro g' hg'
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hg']
    exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) PP.asIdeal PP.ne_bot (Ideal.Quotient.mk _ N)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hm : Formalism.L2.DIV.oToS F E b - N ∈ Formalism.L2.DIV.idS F PP.asIdeal := Ideal.Quotient.eq.1 hq
  have h1 := key g hg hm
  have h2 := key _ (Formalism.L2.DIV.resS_oToS (F := F) PP) hm
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1 h2
  rw [← h1, ← h2, hg, Formalism.L2.DIV.resS_oToS]

theorem red_dict : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → (∃ r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP, Function.Surjective r ∧ (∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) ∧ (∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP), RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b) ∧ ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F, r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩) ∧ ∀ ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ, ∃ mu : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP mu ξ := by
  intro D v φ PP hP
  obtain ⟨r, hr, hr0⟩ := exists_red PP.asIdeal (rdO φ) hP (rdO_dense φ)
  have hrel : ∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP),
      RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b := by
    intro a b
    constructor
    · rintro ⟨x, rfl, hx⟩
      have ha : a ∈ v.adicCompletionIntegers D.host.F := by
        have e : a = (a - rdQ φ (x : D.host.E)) + rdQ φ (x : D.host.E) := by ring
        rw [e]
        exact add_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le) (rdQ_int φ x)
      refine ⟨ha, ?_⟩
      rw [← hr, ← sub_eq_zero, ← map_sub, hr0]
      exact hx
    · rintro ⟨h, rfl⟩
      obtain ⟨x, hx⟩ := rdO_dense φ ⟨a, h⟩
      refine ⟨x, ?_, hx⟩
      rw [← hr, eq_comm, ← sub_eq_zero, ← map_sub, hr0]
      exact hx
  refine ⟨⟨r, fun b => ?_, hr0, hrel, fun N hN => ⟨rdE_int φ N hN, ?_⟩⟩, fun ξ => ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨_, hr x⟩
  · exact eq_resS PP (r.comp (rdS φ)) (fun x => hr x) ⟨N, hN⟩
  · obtain ⟨t, ht⟩ := exists_unitPart (F := D.host.F) (v := v)
    refine ⟨ξ.comp (r.toMonoidHom.comp t).toHomUnits, fun u k huk => ?_⟩
    obtain ⟨h, hk⟩ := (hrel _ _).1 huk
    have hu : Valued.v (u : Fv D.host.F v) = 1 := by
      refine le_antisymm h (not_lt.1 fun hlt => ?_)
      have h0 : (k : Formalism.L2.DIV.kP PP) = 0 := hk ▸ (hr0 ⟨_, h⟩).2 hlt
      have : Nontrivial (Formalism.L2.DIV.kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
      exact k.ne_zero h0
    show ξ _ = ξ k
    congr 1
    apply Units.ext
    show r (t u) = k
    rw [← hk]
    congr 1
    exact Subtype.ext (ht u hu)

end GlobalTheory.PlaceRed

end
end

section

namespace GlobalTheory.LinUnit

section General
open MeasureTheory Matrix GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

noncomputable def fac (g : GL a k) (h : GL b k) : ℝ :=
  nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card b : ℝ) / 2) *
    nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ) / 2)

theorem fac_pos (g : GL a k) (h : GL b k) : 0 < fac g h :=
  mul_pos (Real.rpow_pos_of_pos (nabs_pos' _) _) (Real.rpow_pos_of_pos (nabs_pos' _) _)

theorem om_one_eq (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    om 1 g h Φ = fun x => (fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val) := by
  funext x
  simp [om, fac]

theorem nabs_inv (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by simp [nabs]

theorem fac_sq_mul (g : GL a k) (h : GL b k) :
    fac g h * fac g h * (nabs k (Matrix.GeneralLinearGroup.det h⁻¹) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) = 1 := by
  have hg := nabs_pos' (Matrix.GeneralLinearGroup.det g)
  have hh := nabs_pos' (Matrix.GeneralLinearGroup.det h)
  rw [map_inv, nabs_inv, Real.inv_rpow hh.le, ← Real.rpow_neg hh.le, neg_neg, fac]
  set x := nabs k (Matrix.GeneralLinearGroup.det g)
  set y := nabs k (Matrix.GeneralLinearGroup.det h)
  have e1 : x ^ ((Fintype.card b : ℝ) / 2) * x ^ ((Fintype.card b : ℝ) / 2) * x ^ (-(Fintype.card b : ℝ)) = 1 := by
    rw [← Real.rpow_add hg, ← Real.rpow_add hg]; simp
  have e2 : y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (Fintype.card a : ℝ) = 1 := by
    rw [← Real.rpow_add hh, ← Real.rpow_add hh]; simp
  linear_combination (y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (-(Fintype.card a : ℝ) / 2) *
    y ^ (Fintype.card a : ℝ)) * e1 + e2

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem ip_om_one (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ip ν (om 1 g h Φ) (om 1 g h Φ) = ip ν Φ Φ := by
  have key := integral_comp_mul_mul_volM ν g h⁻¹ (fun x => Φ x * (starRingEnd ℂ) (Φ x))
  have e := fac_sq_mul g h
  rw [om_one_eq]
  unfold ip
  have : ∀ x : Matrix b a k, (fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val) *
      (starRingEnd ℂ) ((fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val)) = ((fac g h * fac g h : ℝ) : ℂ) *
      (Φ ((h⁻¹).val * x * g.val) * (starRingEnd ℂ) (Φ ((h⁻¹).val * x * g.val))) := by
    intro x
    rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  simp_rw [this]
  rw [integral_const_mul, key, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, e]
  simp


omit [DecidableEq a] [DecidableEq b] in
theorem eq_zero_of_ip_eq_zero {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) (h0 : ip ν Φ Φ = 0) : Φ = 0 := by
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨h2, ht⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hBorel : BorelSpace (Matrix b a k) := inferInstanceAs (BorelSpace (b → a → k))
  have hOpen : OpensMeasurableSpace (Matrix b a k) := ⟨le_of_eq hBorel.measurable_eq.symm⟩
  have hHaar : (volM ν b a).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hFinite : IsFiniteMeasureOnCompacts (volM ν b a) := hHaar.toIsFiniteMeasureOnCompacts
  letI : Measure.IsOpenPosMeasure (volM ν b a) := hHaar.toIsOpenPosMeasure
  have hc : Continuous fun x => Complex.normSq (Φ x) := Complex.continuous_normSq.comp hl.continuous
  have hs : HasCompactSupport fun x => Complex.normSq (Φ x) := hK.comp_left (g := Complex.normSq) (by simp)
  have e : ∫ x, Complex.normSq (Φ x) ∂(volM ν b a) = 0 := by
    unfold ip at h0
    simp_rw [Complex.mul_conj] at h0
    rw [integral_complex_ofReal] at h0
    exact_mod_cast h0
  have hInt := @Continuous.integrable_of_hasCompactSupport (Matrix b a k) ℝ _ _ _
    (volM ν b a) hOpen _ hFinite hc hs
  have := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _) hInt).1 e
  have := (hc.ae_eq_iff_eq (volM ν b a) continuous_zero).1 this
  funext x
  exact Complex.normSq_eq_zero.1 (congrFun this x)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem linOm_unitary : ∀ (D : D7) (v : FinPl D) (m n : ℕ) (g : GL (Fin n) (Fv D.host.F v)) (h : GL (Fin m) (Fv D.host.F v)), (∃ r : ℝ, 0 < r ∧ ∀ Φ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ, linOm v g h Φ = fun x => (r : ℂ) * Φ ((h⁻¹).val * x * g.val)) ∧ ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), linOm v g h Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)) ∧ ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (linOm v g h Φ) (linOm v g h Φ) = GlobalTheory.SplitWeil.ip ν Φ Φ ∧ (GlobalTheory.SplitWeil.ip ν Φ Φ = 0 → Φ = 0) := by
  intro D v m n g h
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  refine ⟨⟨fac g h, fac_pos g h, fun Φ => om_one_eq g h Φ⟩, fun Φ hΦ => ⟨?_, fun ν hν => ⟨?_, ?_⟩⟩⟩
  · exact GlobalTheory.SplitWeil.Model.om_mem_SB 1 g h hΦ
  · exact ip_om_one ν g h Φ
  · exact eq_zero_of_ip_eq_zero ν hΦ

end GlobalTheory.LinUnit
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitPlaceEmb

theorem not_isField_of_idem {A : Type} [CommRing A] (σ : A →+* A) {z : A} (hz : z * z = z) (h : z + σ z = 1) :
    ¬ IsField A := by
  intro hf
  haveI := hf.isDomain
  have h0 : z * (z - 1) = 0 := by rw [mul_sub, hz, mul_one, sub_self]
  rcases mul_eq_zero.1 h0 with h' | h'
  · rw [h', σ.map_zero, zero_add] at h
    exact zero_ne_one h
  · rw [sub_eq_zero.1 h', σ.map_one] at h
    exact one_ne_zero (add_eq_left.1 h)

theorem nonempty_algHom_of_idem {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
    (hE : Module.finrank F E = 2) (σ : E →ₐ[F] E) {z : K ⊗[F] E} (hz : z * z = z)
    (h : z + (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom z = 1) : Nonempty (E →ₐ[F] K) := by
  have h2 : Module.finrank K (K ⊗[F] E) = 2 := by rw [Module.finrank_baseChange, hE]
  obtain ⟨φ⟩ := GlobalTheory.AdelicU.nonempty_algHom_of_not_isField (K := K) h2
    (not_isField_of_idem (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom hz h)
  exact ⟨(φ.restrictScalars F).comp Algebra.TensorProduct.includeRight⟩

theorem nonempty_algHom_of_idem_map {F E K R : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
    [CommRing R] [Algebra F R] (hE : Module.finrank F E = 2) (σ : E →ₐ[F] E) (ψ : R →ₐ[F] K) {e : R ⊗[F] E}
    {ε : R} (he : e * e = e) (hs : e + (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom e = algebraMap R _ ε)
    (hψ : ψ ε = 1) : Nonempty (E →ₐ[F] K) := by
  let Φ : R ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map ψ (AlgHom.id F E)).toRingHom
  let τ : K ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom
  have hcomm : ∀ x, Φ ((Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom x) = τ (Φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine nonempty_algHom_of_idem hE σ (z := Φ e) (by rw [← map_mul, he]) ?_
  have := congrArg Φ hs
  rw [map_add (f := _), hcomm] at this
  rw [this, Algebra.TensorProduct.algebraMap_apply]
  change ψ ε ⊗ₜ[F] (1 : E) = 1
  rw [hψ]
  rfl

theorem nonempty_algHom_of_not_nonSplitAt :
    ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ¬ GlobalTheory.WeilParts.NonSplitAt D v ε → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := by
  intro D v ε hε hn
  obtain ⟨e, ⟨he, -, -⟩, hsum⟩ : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap _ _ ε := by
    by_contra h
    exact hn ⟨hε, h⟩
  obtain ⟨α, rfl, h1, -⟩ := hε
  exact nonempty_algHom_of_idem_map (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 D.sp.cm.sig
    ((evalV D.host.F v).comp (sndA D.host.F)) he hsum h1

end GlobalTheory.SplitPlaceEmb

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

def ResAt (c : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP → ∀ x : (AE D)ˣ, e * ((x : AE D) - 1) = (x : AE D) - 1 →
    ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (u : (kP PP)ˣ),
      (u : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ → ((c x : Circle) : ℂ) = ((a u : ℂˣ) : ℂ)

def UnrOff (c : (AE D)ˣ →* Circle) (P : Finset (Pl D.host.E)) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ PP ∈ P, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → UnramAt ε c

theorem ResAt.mul {c c' : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a a' : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a)
    (h' : ResAt c' PP a') : ResAt (c * c') PP (a * a') := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  have k' := h' e he x hex hx u hu
  simp only [MonoidHom.mul_apply, Circle.coe_mul, Units.val_mul, k, k']

theorem ResAt.inv {c : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a) :
    ResAt c⁻¹ PP a⁻¹ := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  simp only [MonoidHom.inv_apply, Circle.coe_inv, Units.val_inv_eq_inv_val, k]

theorem UnrOff.mul {c c' : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) (h' : UnrOff c' P) :
    UnrOff (c * c') P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.mul_apply, h v ε hε hv x h₁ h₂ h₃, h' v ε hε hv x h₁ h₂ h₃, one_mul]

theorem UnrOff.inv {c : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) :
    UnrOff c⁻¹ P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.inv_apply, h v ε hε hv x h₁ h₂ h₃, inv_one]

end GlobalTheory.StepLaw

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistAdelicTop

theorem locallyCompact_secondCountable_borel_countable :
    ∀ {D : D7} (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧
      BorelSpace (GA D V) ∧ Countable (GQ V) := by
  intro D V
  obtain ⟨hlc, hsc, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  exact ⟨hlc, hsc, ⟨rfl⟩, (GlobalTheory.RationalCountable.discrete_countable_GQ D V).2⟩

end GlobalTheory.TwistAdelicTop
end
