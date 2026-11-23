module

public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.OneUnitRoot

open IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

theorem exists_unit_pow_normV_sub_one (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (y : (v.adicCompletion E)ˣ) (hy : Valued.v ((y : v.adicCompletion E) - 1) < 1) :
    ∃ z : (v.adicCompletion E)ˣ, Valued.v (z : v.adicCompletion E) = 1 ∧ z ^ (normV v - 1) = y := by
  have hc := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set n := normV v - 1 with hn
  have hcard : Nat.card (ResidueField (v.adicCompletionIntegers E)) = normV v := by
    simpa [Formalism.UG.qV, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      Formalism.UG.P.tjcosets_card_residue v
  haveI : Finite (ResidueField (v.adicCompletionIntegers E)) :=
    GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  haveI := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers E))
  have hq0 : ((normV v : ℕ) : ResidueField (v.adicCompletionIntegers E)) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
  have hq1 : 2 ≤ normV v := by
    rw [← hcard]; exact Finite.one_lt_card
  have hnres : ((n : ℕ) : ResidueField (v.adicCompletionIntegers E)) = -1 := by
    rw [hn, Nat.cast_sub (by omega), hq0]; simp
  have hnpos : 0 < n := by omega

  have hy1 : Valued.v (y : v.adicCompletion E) = 1 := by
    have e : (y : v.adicCompletion E) = ((y : v.adicCompletion E) - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · exact map_one _
    · rwa [map_one]
  set y' : v.adicCompletionIntegers E := ⟨y, by
    show Valued.v (y : v.adicCompletion E) ≤ 1; exact hy1.le⟩
  have hm : (X ^ n - C y' : (v.adicCompletionIntegers E)[X]).Monic := monic_X_pow_sub_C y' hnpos.ne'
  have hev : eval 1 (X ^ n - C y' : (v.adicCompletionIntegers E)[X]) ∈ maximalIdeal (v.adicCompletionIntegers E) := by
    simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C]
    rw [← neg_sub, Ideal.neg_mem_iff, mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact ne_of_lt hy
  have hder : IsUnit (eval 1 (derivative (X ^ n - C y' : (v.adicCompletionIntegers E)[X]))) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    rw [← isUnit_map_iff (residue (v.adicCompletionIntegers E)), map_natCast, hnres]
    exact isUnit_one.neg
  obtain ⟨r, hr, hr1⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers E))
    _ hm 1 hev (hder.map _)
  have hrn : r ^ n = y' := by
    have := hr
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  have hrv : Valued.v (r : v.adicCompletion E) = 1 := by
    have h1 : Valued.v ((r : v.adicCompletion E) - 1) < 1 := by
      have := hr1
      rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one] at this
      exact lt_of_le_of_ne (r - 1).2 this
    have e : (r : v.adicCompletion E) = ((r : v.adicCompletion E) - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · exact map_one _
    · rwa [map_one]
  have hr0 : (r : v.adicCompletion E) ≠ 0 := by
    intro h; rw [h, map_zero] at hrv; exact zero_ne_one hrv
  refine ⟨Units.mk0 _ hr0, hrv, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact congrArg Subtype.val hrn

end GlobalTheory.OneUnitRoot
end
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.StableSubMat

theorem exists_restrict {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (V : Submodule L (Fin a → L)) (hV : IsInv τ V) :
    ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L),
      D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧
      ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) =
          D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧
        ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E =
          E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  classical
  set b := Module.finrank L V
  let f : (Fin b → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ (Module.finBasis L V).equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp (Module.finBasis L V).equivFun.symm.injective
  have hfr : LinearMap.range f = V := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨g₀, hg₀⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  set E : Matrix (Fin a) (Fin b) L := LinearMap.toMatrix' f with hE
  set D : Matrix (Fin b) (Fin a) L := LinearMap.toMatrix' g₀ with hD
  have hEf : E.mulVecLin = f := by rw [hE]; exact Matrix.toLin'_toMatrix' f
  have hDf : D.mulVecLin = g₀ := by rw [hD]; exact Matrix.toLin'_toMatrix' g₀
  have hDE : D * E = 1 := by
    rw [hD, hE, ← LinearMap.toMatrix'_comp, hg₀, LinearMap.toMatrix'_id]
  have hrange : LinearMap.range E.mulVecLin = V := by rw [hEf, hfr]

  have hED : ∀ v ∈ V, (E * D).mulVec v = v := by
    intro v hv
    rw [← hfr] at hv
    obtain ⟨w, rfl⟩ := hv
    rw [← Matrix.mulVec_mulVec]
    have h1 : D.mulVec (f w) = g₀ (f w) := by rw [← hDf]; rfl
    have h2 : ∀ u, E.mulVec u = f u := fun u => by rw [← hEf]; rfl
    rw [h1, h2, ← LinearMap.comp_apply g₀ f, hg₀, LinearMap.id_apply]
  have key : ∀ g, E * D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E =
      ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E := by
    intro g
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mul_assoc (E * D), ← Matrix.mulVec_mulVec (M := E * D)]
    apply hED
    rw [← Matrix.mulVec_mulVec]
    apply hV
    rw [← hrange]
    exact ⟨x, rfl⟩
  let σm : Γ →* Matrix (Fin b) (Fin b) L :=
    { toFun := fun g => D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E
      map_one' := by simp [hDE]
      map_mul' := by
        intro g h
        simp only [map_mul, Units.val_mul]
        have k := key h
        simp only [Matrix.mul_assoc] at k ⊢
        rw [k] }
  refine ⟨b, E, D, σm.toHomUnits, hDE, hrange, fun g => ⟨?_, ?_⟩⟩
  · rw [MonoidHom.coe_toHomUnits]; rfl
  · rw [MonoidHom.coe_toHomUnits]
    change _ = E * (D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E)
    have k := key g
    simp only [Matrix.mul_assoc] at k ⊢
    exact k.symm

end GlobalTheory.StableSubMat
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.ConstituentImage

theorem exists_constituent_image : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ τ₀ : Γ →* GL (Fin a) L) (P : GL (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (P : Matrix (Fin a) (Fin a) L) = (P : Matrix (Fin a) (Fin a) L) * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) → IsSSRep τ → ∀ (Vs : Fin n → Submodule L (Fin a → L)), iSup Vs = ⊤ → (∀ j, IsIrrSub τ₀ (Vs j)) → ∀ V, IsIrrSub τ V → ∃ (j : Fin n) (M : Matrix (Fin a) (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * M = M * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) ∧ Submodule.map M.mulVecLin (Vs j) = V ∧ Disjoint (LinearMap.ker M.mulVecLin) (Vs j) := by
  intro Γ L _ _ a n τ τ₀ P hP hss Vs hVs hirr V hV
  obtain ⟨W', hW'i, hc⟩ := hss V hV.2.1
  set p : (Fin a → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ Submodule.linearProjOfIsCompl V W' hc with hpdef
  have hpV : ∀ x, p x ∈ V := fun x => (Submodule.linearProjOfIsCompl V W' hc x).2
  have hpid : ∀ x ∈ V, p x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩)
  have hp0 : ∀ x ∈ W', p x = 0 := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨x, hx⟩)
  have hcomm : ∀ g v, p ((τ g : Matrix (Fin a) (Fin a) L).mulVec v) = (τ g : Matrix (Fin a) (Fin a) L).mulVec (p v) := by
    intro g v
    set q := v - p v
    have hq : q ∈ W' := by
      rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc, map_sub]
      have := Submodule.linearProjOfIsCompl_apply_left hc ⟨p v, hpV v⟩
      rw [this, sub_eq_zero]; rfl
    have hv : v = p v + q := by simp [q]
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_add, map_add (f := _), hpid _ (hV.2.1 g _ (hpV v)), hp0 _ (hW'i g _ hq), add_zero]
  set π : Matrix (Fin a) (Fin a) L := LinearMap.toMatrix' p with hπ
  have hπv : ∀ v, π.mulVec v = p v := fun v => by simp [hπ, LinearMap.toMatrix'_mulVec]
  have hπc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * π = π * (τ g : Matrix (Fin a) (Fin a) L) := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hπv, hcomm]
  set M : Matrix (Fin a) (Fin a) L := π * (P : Matrix (Fin a) (Fin a) L) with hM
  have hMc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * M = M * (τ₀ g : Matrix (Fin a) (Fin a) L) := by
    intro g
    rw [hM, ← Matrix.mul_assoc, hπc g, Matrix.mul_assoc, hP g, Matrix.mul_assoc]
  have hMv : ∀ g v, (τ g : Matrix (Fin a) (Fin a) L).mulVec (M.mulVec v) = M.mulVec ((τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v) := by
    intro g v
    rw [Matrix.mulVec_mulVec, hMc g, ← Matrix.mulVec_mulVec]
  have hMV : ∀ v, M.mulVec v ∈ V := fun v => by
    rw [hM, ← Matrix.mulVec_mulVec, hπv]; exact hpV _

  have hex : ∃ j, Submodule.map M.mulVecLin (Vs j) ≠ ⊥ := by
    by_contra hne
    push_neg at hne
    obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.1
    have hsup : Submodule.map M.mulVecLin ⊤ = ⊥ := by
      rw [← hVs, Submodule.map_iSup]; simp [hne]
    have hmem : M.mulVec (((P⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x) ∈ Submodule.map M.mulVecLin ⊤ :=
      ⟨_, Submodule.mem_top, rfl⟩
    rw [hsup, Submodule.mem_bot, hM, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (M := (P : Matrix (Fin a) (Fin a) L)),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, hπv, hpid x hxV] at hmem
    exact hx0 hmem
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, M, hMc, ?_, ?_⟩
  · have hinv : IsInv τ (Submodule.map M.mulVecLin (Vs j)) := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨(τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v, (hirr j).2.1 g v hv, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact (hMv g v).symm
    have hle : Submodule.map M.mulVecLin (Vs j) ≤ V := by
      rintro _ ⟨v, _, rfl⟩; exact hMV v
    rcases hV.2.2 _ hle hinv with h | h
    · exact absurd h hj
    · exact h
  · have hinv : IsInv τ₀ (LinearMap.ker M.mulVecLin ⊓ Vs j) := by
      rintro g v ⟨hk, hv⟩
      refine ⟨?_, (hirr j).2.1 g v hv⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk ⊢
      rw [← hMv, hk, Matrix.mulVec_zero]
    rcases (hirr j).2.2 _ inf_le_right hinv with h | h
    · exact disjoint_iff.2 h
    · exfalso
      apply hj
      rw [eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      have hk : v ∈ LinearMap.ker M.mulVecLin := (h ▸ (inf_le_left : LinearMap.ker M.mulVecLin ⊓ Vs j ≤ _)) hv
      simpa using hk

end GlobalTheory.ConstituentImage
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.GLCongrCptOpen

def congrSubgroup {R : Type} [CommRing R] (n : ℕ) (O : Subring R) (I : AddSubgroup R)
    (hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I) : Subgroup (GL (Fin n) R) where
  carrier := {g | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    (∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    ∀ i j, (g : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I}
  one_mem' := by
    have h : ∀ i j, (1 : Matrix (Fin n) (Fin n) R) i j ∈ O := fun i j => by
      rw [Matrix.one_apply]
      split_ifs
      exacts [O.one_mem, O.zero_mem]
    refine ⟨h, by simpa using h, fun i j => by simp⟩
  mul_mem' := by
    rintro g h ⟨g1, g2, g3⟩ ⟨h1, h2, h3⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact O.sum_mem fun k _ => O.mul_mem (g1 _ _) (h1 _ _)
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact O.sum_mem fun k _ => O.mul_mem (h2 _ _) (g2 _ _)
    · have e : ((g * h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1 =
          (g : Matrix (Fin n) (Fin n) R) * ((h : Matrix (Fin n) (Fin n) R) - 1) +
            ((g : Matrix (Fin n) (Fin n) R) - 1) := by
        rw [Units.val_mul]; noncomm_ring
      rw [← Matrix.sub_apply, e, Matrix.add_apply, Matrix.mul_apply]
      exact I.add_mem (I.sum_mem fun k _ => hI _ (g1 _ _) _ (h3 _ _)) (g3 _ _)
  inv_mem' := by
    rintro g ⟨g1, g2, g3⟩
    refine ⟨g2, by simpa only [inv_inv] using g1, fun i j => ?_⟩
    have e : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1 =
        -(((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * ((g : Matrix (Fin n) (Fin n) R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [← Matrix.sub_apply, e, Matrix.neg_apply, Matrix.mul_apply]
    exact I.neg_mem (I.sum_mem fun k _ => hI _ (g2 _ _) _ (g3 _ _))

theorem isOpen_congrSubgroup {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ)
    (O : Subring R) (I : AddSubgroup R) (hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I)
    (hO : IsOpen (O : Set R)) (hIo : IsOpen (I : Set R)) :
    IsOpen (congrSubgroup n O I hI : Set (GL (Fin n) R)) := by
  have c1 : ∀ i j, Continuous fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have c2 : ∀ i j, Continuous fun g : GL (Fin n) R => ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j :=
    fun i j => Units.continuous_coe_inv.matrix_elem i j
  change IsOpen {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    (∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    ∀ i j, (g : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (c1 i j)).inter
    ((isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (c2 i j)).inter
      (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hIo.preimage ((c1 i j).sub continuous_const)))

theorem isCompact_congrSubgroup {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (n : ℕ) (O : Subring R) (I : AddSubgroup R) (hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I)
    (hO : IsOpen (O : Set R)) (hIo : IsOpen (I : Set R)) (hOc : IsCompact (O : Set R)) :
    IsCompact (congrSubgroup n O I hI : Set (GL (Fin n) R)) := by
  have hM : IsCompact {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} := by
    have := isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => hOc))
    have e : {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} =
        (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (O : Set R)) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e]
    exact this
  have hP := hM.prod (hM.image MulOpposite.continuous_op)
  have hE := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).isCompact_preimage hP
  refine hE.of_isClosed_subset
    ((congrSubgroup n O I hI).isClosed_of_isOpen (isOpen_congrSubgroup n O I hI hO hIo)) ?_
  rintro g ⟨g1, g2, -⟩
  exact ⟨g1, _, g2, rfl⟩

theorem exists_compactOpen_congr :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (c : v.adicCompletion F), c ≠ 0 →
    ∃ K : Subgroup (GL (Fin n) (v.adicCompletion F)), IsOpen (K : Set (GL (Fin n) (v.adicCompletion F))) ∧
      IsCompact (K : Set (GL (Fin n) (v.adicCompletion F))) ∧ ∀ g ∈ K, ∀ i j,
        Valued.v ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤
          Valued.v c := by
  intro F _ _ v n c hc
  let O : Subring (v.adicCompletion F) := (v.adicCompletionIntegers F).toSubring
  have hO : IsOpen (O : Set (v.adicCompletion F)) := Valued.isOpen_valuationSubring _
  have hOc : IsCompact (O : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  let I : AddSubgroup (v.adicCompletion F) := Valued.v.leAddSubgroup (Valued.v c)
  have hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I := fun a ha x hx => by
    change Valued.v (a * x) ≤ Valued.v c
    rw [map_mul]
    have ha' : Valued.v a ≤ 1 := ha
    have hx' : Valued.v x ≤ Valued.v c := hx
    simpa using mul_le_mul' ha' hx'
  have hIo : IsOpen (I : Set (v.adicCompletion F)) := by
    have e : (I : Set (v.adicCompletion F)) = (fun x => x / c) ⁻¹' (O : Set (v.adicCompletion F)) := by
      ext x
      change Valued.v x ≤ Valued.v c ↔ Valued.v (x / c) ≤ 1
      rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc))]
    rw [e]
    exact hO.preimage (continuous_id.div_const c)
  exact ⟨congrSubgroup n O I hI, isOpen_congrSubgroup n O I hI hO hIo,
    isCompact_congrSubgroup n O I hI hO hIo hOc, fun g hg => hg.2.2⟩

end GlobalTheory.GLCongrCptOpen
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {σ₀ : KA l →+* ℂ} (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
  (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X)

def liftEx (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : Sp ℂ ⟶ Z.oF.t.G.left :=
  Z.m0.toSABMap.cart.1.lift (Fu.ex i P z).left y (by rw [Over.w (Fu.ex i P z), ← hu]; rfl)

def pushEx (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (z : Fin g → ℂ) : Over.mk p ⟶ Z.t.G :=
  Over.homMk (liftEx Z Fu y i P hu z ≫ Z.m.φ) (by
    show (liftEx Z Fu y i P hu z ≫ Z.m.φ) ≫ Z.t.G.hom = p
    rw [Category.assoc, Z.m.cart.1.w, ← Category.assoc, liftEx, IsPullback.lift_snd, ← hp])

theorem liftEx_fst (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : liftEx Z Fu y i P hu z ≫ Z.m0.toSABMap.φ = (Fu.ex i P z).left :=
  IsPullback.lift_fst _ _ _ _

theorem liftEx_snd (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : liftEx Z Fu y i P hu z ≫ Z.oF.t.G.hom = y :=
  IsPullback.lift_snd _ _ _ _

theorem pushEx_left (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (z : Fin g → ℂ) :
    (pushEx Z Fu y i P p hu hp z).left = liftEx Z Fu y i P hu z ≫ Z.m.φ := rfl

end GlobalTheory.ShFam.Hor.LogCh
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.PeriodSpan

variable {X : Scheme.{0}} (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X)

def torusPts (E : TorusExtension ((Over.pullback y).obj G)) : Set (Over.mk y ⟶ G) :=
  letI := E.addCommGroup
  {x | ∃ t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) E.X, (t ≫ E.i).left ≫ pullback.fst G.hom y = x.left}

def IsPerHol (ψ : ℂ → (Over.mk y ⟶ G)) : Prop :=
  (∀ s t, ψ (s + t) = ψ s * ψ t) ∧ IsHolTo Set.univ (fun s => (ψ s).left) ∧
    ψ (2 * Real.pi * Complex.I) = 1

def perHolSub : Subgroup (Over.mk y ⟶ G) :=
  Subgroup.closure (⋃ (ψ : ℂ → (Over.mk y ⟶ G)) (_ : IsPerHol G y ψ), Set.range ψ)

end GlobalTheory.PeriodSpan
end
end
