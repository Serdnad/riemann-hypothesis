module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

@[expose] public section

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.formal_group_law_linear_coeff_additive : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (addLaw k d i) ∧ coeff α (Katz.lift p (μ i)) = coeff α (addLaw (Fr p k) d i) := by
  first | exact @GlobalTheory.Katz.coeff_law_of_degree_le_one | exact GlobalTheory.Katz.coeff_law_of_degree_le_one | (intros; apply GlobalTheory.Katz.coeff_law_of_degree_le_one <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ f : MvPowerSeries (Fin d) R, cob2 μ (cob1 μ f) = subst (op μ x1 (op μ x2 x3)) f - subst (op μ (op μ x1 x2) x3) f ∧ swap (cob1 μ f) - cob1 μ f = subst (fun i => swap (μ i)) f - subst μ f ∧ (∀ c c', cob2 μ (c + c') = cob2 μ c + cob2 μ c' ∧ cob2 μ (c - c') = cob2 μ c - cob2 μ c' ∧ swap (c - c') = swap c - swap c') ∧ (∀ (r : R) c, cob2 μ (r • c) = r • cob2 μ c ∧ swap (r • c) = r • swap c) ∧ IsLaw (addLaw R d) ∧ (IsLaw μ → IsCoc μ (cob1 μ f)) := by
  first | exact @GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt | exact GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt | (intros; apply GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt <;> assumption)
end

section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_hopf_quotient_ker_eq_torsionIdeal :
    ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ),
      ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D),
        Function.Surjective π ∧ RingHom.ker π = torsionIdeal (R := O) (A := B) n := by
  intro O _ B _ _ _ n
  let I := torsionIdeal (R := O) (A := B) n
  have : I.IsHopfIdeal O :=
    isHopfIdeal_kerIdeal_of_bialgHom O B B (mulBy (R := O) (A := B) n)
  let π : B →ₐc[O] B ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have cocomm : IsCocomm O (B ⧸ I) := by
    constructor
    ext b
    obtain ⟨a, rfl⟩ := hπ b
    change TensorProduct.comm O (B ⧸ I) (B ⧸ I) (comul (π a)) = comul (π a)
    rw [← CoalgHomClass.map_comp_comul_apply π a, ← TensorProduct.map_comm, comm_comul]
  exact ⟨B ⧸ I, inferInstance, inferInstance, cocomm, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem⟩
end

section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.quotientTransition_surjective_same_subgroup : ∀ (O : Type) [CommRing O] (A₁ : Type) [CommRing A₁] [HopfAlgebra O A₁] [IsCocomm O A₁] [Module.Finite O A₁] [Module.Projective O A₁] (A₂ : Type) [CommRing A₂] [HopfAlgebra O A₂] [IsCocomm O A₂] [Module.Finite O A₂] [Module.Projective O A₂] (B₁ : Type) [CommRing B₁] [HopfAlgebra O B₁] [IsCocomm O B₁] [Module.Finite O B₁] [Module.Projective O B₁] (B₂ : Type) [CommRing B₂] [HopfAlgebra O B₂] [IsCocomm O B₂] [Module.Finite O B₂] [Module.Projective O B₂] (π : A₂ →ₐc[O] A₁) (j₁ : B₁ →ₐc[O] A₁) (j₂ : B₂ →ₐc[O] A₂) (r : B₂ →ₐc[O] B₁) (ρ : A₁ →ₗ[O] B₁), (∀ b, ρ (j₁ b) = b) → (∀ b, j₁ (r b) = π (j₂ b)) → kerIdeal j₁ = Ideal.map (π : A₂ →ₐ[O] A₁) (kerIdeal j₂) → Function.Surjective r := by
  first | exact @GlobalTheory.QuotTransition.transition_surjective | exact GlobalTheory.QuotTransition.transition_surjective | (intros; apply GlobalTheory.QuotTransition.transition_surjective <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.isHopfIdeal_kerIdeal_of_bialgHom' : ∀ (k A B : Type) [CommRing k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] (f : B →ₐc[k] A), (kerIdeal f).IsHopfIdeal k := by
  first | exact @GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom | exact GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom | (intros; apply GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.AWFront

theorem sub_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have e : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i
    simp [SimplexCategory.subinterval]
  unfold Sx.sub
  rw [e, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem ev_of_front {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {S : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj S) I n) (β : Cochain ((chains R).obj S) J m) (γ : Cochain ((chains R).obj S) K k)
    (hγ : μ.IsAW hk α β γ)
    (hα : ∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S s U), 0 < s → ev α s t h U x = 0)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx S N U) :
    ev γ N w h U x = μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega)))
      (ev β N _ rfl U x) := by
  have key : ∀ (s : ℤ) (hs : s = n) (H : s + (-(N : ℤ) + m) = w) (h1 : -((0 : ℕ) : ℤ) + n = s),
      μ.mul U s (-(N : ℤ) + m) w H (ev α 0 s h1 U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) =
        μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
    rintro s rfl H h1
    rfl
  have gen : ∀ (p : ℕ), p = 0 → ∀ (H : -(p : ℤ) + n + (-((N - p : ℕ) : ℤ) + m) = w) (h1 : 0 + p ≤ N)
      (h2 : p + (N - p) ≤ N),
      (m * (p : ℤ)).negOnePow • μ.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w H
        (ev α p _ rfl U (x.sub 0 p h1)) (ev β (N - p) _ rfl U (x.sub p (N - p) h2)) =
      μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
    rintro p rfl H h1 h2
    have e1 : (m * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [e1, one_smul]
    have e2 : x.sub 0 (N - 0) h2 = x := sub_full x h2
    rw [e2]
    exact key _ (by simp) H rfl
  rw [hγ N w h U x, Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => ?_), add_zero]
  · exact gen _ (by simp) _ _ _
  · rw [hα (i.succ : ℕ) _ rfl U _ (by simp), map_zero, LinearMap.zero_apply, smul_zero]

end GlobalTheory.AWFront
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.TwistFiltered

theorem ring_eq_later {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
    (hc : IsColimit c) {j : J} {x y : D.obj j} (h : c.ι.app j x = c.ι.app j y) :
    ∃ (k : J) (f : j ⟶ k), D.map f x = D.map f y :=
  (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget CommRingCat.{0}) hc) x y).1 h

def primSys (q : ℕ) {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) : J ⥤ Type where
  obj j := Prim q (D.obj j)
  map f := TypeCat.ofHom (Prim.map (q := q) (D.map f).hom)
  map_id j := by
    ext ζ
    apply Subtype.ext
    simp [Prim.map]
  map_comp f g := by
    ext ζ
    apply Subtype.ext
    simp [Prim.map]

end GlobalTheory.EtC.TwistFiltered

namespace GlobalTheory.EtC.TwistFiltered

theorem prim_map_comp {q : ℕ} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Prim.map (q := q) g ∘ Prim.map f = Prim.map (g.comp f) := by
  funext ζ
  rfl

theorem twF_preservesFilteredColimits : ∀ (q : ℕ) (i : ℤ), PreservesFilteredColimitsOfSize.{0, 0} (twF q i) := by
  intro q i
  rw [(GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} (ZMod q)) (twF q i)).2]
  intro J _ _ D c hc
  obtain ⟨hon, hinj⟩ := GlobalTheory.T.cyclotomicPrimitiveRoots_filtered_colimit q J D c hc
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : (twF q i).obj (D.obj j)),
      ((twF q i).map (c.ι.app k)).hom (((twF q i).map (D.map f)).hom y) = ((twF q i).map (c.ι.app j)).hom y := by
    intro j k f y
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, c.w]
  have hwP : ∀ {j k : J} (f : j ⟶ k), Prim.map (q := q) (c.ι.app k).hom ∘ Prim.map (D.map f).hom = Prim.map (c.ι.app j).hom := by
    intro j k f
    rw [prim_map_comp, ← CommRingCat.hom_comp, c.w]
  have hwP' : ∀ {j k : J} (f : j ⟶ k) (ζ : Prim q (D.obj j)), Prim.map (q := q) (c.ι.app k).hom (Prim.map (D.map f).hom ζ) = Prim.map (c.ι.app j).hom ζ :=
    fun f ζ => congrFun (hwP f) ζ
  refine ⟨?_, ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
    induction f using Finsupp.induction_linear with
    | zero =>
      obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
      exact ⟨j, 0, by rw [map_zero]; rfl⟩
    | add f g hf hg =>
      obtain ⟨j, y, hy⟩ := hf
      obtain ⟨j', y', hy'⟩ := hg
      refine ⟨IsFiltered.max j j', ((twF q i).map (D.map (IsFiltered.leftToMax j j'))).hom y + ((twF q i).map (D.map (IsFiltered.rightToMax j j'))).hom y', ?_⟩
      rw [map_add (f := _), hw, hw, hy, hy']
      rfl
    | single ζ a =>
      obtain ⟨j, ξ, hξ⟩ := hon ζ
      refine ⟨j, Submodule.Quotient.mk (Finsupp.single ξ a), ?_⟩
      change Submodule.Quotient.mk (Finsupp.mapDomain _ _) = _
      rw [Finsupp.mapDomain_single, hξ]
  · intro j y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (c.ι.app j).hom) x) = 0 at hy
    rw [Submodule.Quotient.mk_eq_zero] at hy
    have hlift : ∀ r ∈ twRel q i c.pt, ∃ (k : J) (s : Prim q (D.obj k) →₀ ULift.{1} (ZMod q)),
        s ∈ twRel q i (D.obj k) ∧ Finsupp.mapDomain (Prim.map (c.ι.app k).hom) s = r := by
      intro r hr
      induction hr using Submodule.span_induction with
      | mem r hr =>
        obtain ⟨ζ, ξ, a, hrel, rfl⟩ := hr
        obtain ⟨j1, ζ1, hζ1⟩ := hon ζ
        obtain ⟨j2, ξ1, hξ1⟩ := hon ξ
        obtain ⟨ζm, hζm⟩ : ∃ ζm : Prim q (D.obj (IsFiltered.max j1 j2)), Prim.map (c.ι.app _).hom ζm = ζ :=
          ⟨_, (hwP' (IsFiltered.leftToMax j1 j2) ζ1).trans hζ1⟩
        obtain ⟨ξm, hξm⟩ : ∃ ξm : Prim q (D.obj (IsFiltered.max j1 j2)), Prim.map (c.ι.app _).hom ξm = ξ :=
          ⟨_, (hwP' (IsFiltered.rightToMax j1 j2) ξ1).trans hξ1⟩
        have heq : c.ι.app (IsFiltered.max j1 j2) ξm.1 = c.ι.app (IsFiltered.max j1 j2) (ζm.1 ^ (a : ZMod q).val) := by
          rw [map_pow]
          have h1 := congrArg Subtype.val hζm
          have h2 := congrArg Subtype.val hξm
          simp only [Prim.map] at h1 h2
          rw [h1, h2, hrel]
        obtain ⟨n, g, hg⟩ := ring_eq_later hc heq
        refine ⟨n, Finsupp.single (Prim.map (D.map g).hom ξm) 1 - Finsupp.single (Prim.map (D.map g).hom ζm) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)), Submodule.subset_span ⟨_, _, a, ?_, rfl⟩, ?_⟩
        · simp only [Prim.map]
          rw [hg, map_pow]
        · rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hwP' g ξm, hwP' g ζm, hζm, hξm]
      | zero =>
        obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
        exact ⟨j, 0, zero_mem _, by simp⟩
      | add r r' _ _ hr hr' =>
        obtain ⟨k, s, hs, rfl⟩ := hr
        obtain ⟨k', s', hs', rfl⟩ := hr'
        refine ⟨IsFiltered.max k k', Finsupp.mapDomain (Prim.map (D.map (IsFiltered.leftToMax k k')).hom) s +
          Finsupp.mapDomain (Prim.map (D.map (IsFiltered.rightToMax k k')).hom) s',
          add_mem (twRel_le q i _ hs) (twRel_le q i _ hs'), ?_⟩
        rw [Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, hwP, hwP]
      | smul a r _ hr =>
        obtain ⟨k, s, hs, rfl⟩ := hr
        exact ⟨k, a • s, Submodule.smul_mem _ a hs, by rw [Finsupp.mapDomain_smul]⟩
    obtain ⟨k, s, hs, hsr⟩ := hlift _ hy
    have hz : Finsupp.mapDomain (Prim.map (c.ι.app (IsFiltered.max j k)).hom)
        (Finsupp.mapDomain (Prim.map (D.map (IsFiltered.leftToMax j k)).hom) x -
          Finsupp.mapDomain (Prim.map (D.map (IsFiltered.rightToMax j k)).hom) s) = 0 := by
      rw [Finsupp.mapDomain_sub, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, hwP, hwP, hsr, sub_self]
    have key := GlobalTheory.T.finsupp_mapDomain_eq_zero_at_filtered_stage (ULift.{1} (ZMod q)) J (primSys q D) (Prim q c.pt) (fun j => Prim.map (c.ι.app j).hom)
      (fun j k f ζ => hwP' f ζ) hinj (IsFiltered.max j k) _ hz
    obtain ⟨n, h, hn⟩ := key
    refine ⟨n, IsFiltered.leftToMax j k ≫ h, ?_⟩
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (D.map (IsFiltered.leftToMax j k ≫ h)).hom) x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change Finsupp.mapDomain (Prim.map (D.map h).hom) _ = 0 at hn
    rw [Finsupp.mapDomain_sub, sub_eq_zero, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, prim_map_comp, prim_map_comp] at hn
    rw [Functor.map_comp, CommRingCat.hom_comp, hn]
    have := twRel_le q i (D.map (IsFiltered.rightToMax j k ≫ h)).hom hs
    rwa [Functor.map_comp, CommRingCat.hom_comp] at this

end GlobalTheory.EtC.TwistFiltered
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → Function.Bijective (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) := by
  first | (exact @GlobalTheory.EtC.sec_coprod) | (exact GlobalTheory.EtC.sec_coprod) | (intros; apply GlobalTheory.EtC.sec_coprod  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section FreeYoneda
variable {R : Type} [CommRing R]

theorem freeYoneda_secMap_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.map φ (Sec.res g s) = Sec.res g (Sec.map φ s) := by
  have h := congrArg (fun k => k.hom s) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

theorem freeYoneda_res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (x : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.res x s) = Sec.res (g ≫ x) s := by
  change (F.obj.map g.op).hom ((F.obj.map x.op).hom s) = (F.obj.map (g ≫ x).op).hom s
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem freeYoneda_res_id {F : Shv R} {U : Scheme.{0}} (s : Sec F U) : Sec.res (𝟙 U) s = s := by
  change (F.obj.map (𝟙 U).op).hom s = s
  rw [op_id, CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply]

theorem freeYoneda_secMap_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (s : Sec F U) :
    Sec.map (φ ≫ ψ) s = Sec.map ψ (Sec.map φ s) := rfl


variable (R) in
theorem freeYoneda_gen {Y U : Scheme.{0}} (x : U ⟶ Y) :
    freeGen R (yoneda.obj Y) U x = Sec.res x (freeGen R (yoneda.obj Y) Y (𝟙 Y)) := by
  rw [(free_hom_sections R (yoneda.obj Y) ((free R).obj (yoneda.obj Y))).2.2.1]
  simp


variable (R) in
theorem freeYoneda_ev_bijective {Y : Scheme.{0}} (F : Shv R) :
    Function.Bijective fun h : (free R).obj (yoneda.obj Y) ⟶ F => Sec.map h (freeGen R (yoneda.obj Y) Y (𝟙 Y)) := by
  obtain ⟨hex, hext, -, -⟩ := free_hom_sections R (yoneda.obj Y) F
  constructor
  · intro φ ψ e
    apply hext
    intro U x
    rw [freeYoneda_gen R (x : U ⟶ Y), freeYoneda_secMap_res, freeYoneda_secMap_res]
    exact congrArg (Sec.res (x : U ⟶ Y)) e
  · intro s
    obtain ⟨φ, hφ⟩ := hex (fun U x => Sec.res (x : U ⟶ Y) s) (fun V U g x => by
      simp only [yoneda_obj_map]
      exact freeYoneda_res_res g x s)
    exact ⟨φ, (hφ Y (𝟙 Y)).trans (freeYoneda_res_id s)⟩


variable (R) in
theorem freeYoneda_ev_pre {Y X : Scheme.{0}} (f : Y ⟶ X) {F : Shv R} (h : (free R).obj (yoneda.obj X) ⟶ F) :
    Sec.map ((free R).map (yoneda.map f) ≫ h) (freeGen R (yoneda.obj Y) Y (𝟙 Y)) =
      Sec.res f (Sec.map h (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  rw [freeYoneda_secMap_comp, (free_hom_sections R (yoneda.obj Y) F).2.2.2, ← freeYoneda_secMap_res,
    ← freeYoneda_gen R f]
  congr 2

end FreeYoneda

theorem freeYoneda_desc_isIso : ∀ (R : Type) [CommRing R] {Y₁ Y₂ X : Scheme.{0}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X),
    (∀ F : Shv R, Function.Bijective fun s : Sec F X => (Sec.res f₁ s, Sec.res f₂ s)) →
    IsIso (biprod.desc ((free R).map (yoneda.map f₁)) ((free R).map (yoneda.map f₂))) := by
  intro R _ Y₁ Y₂ X f₁ f₂ hb
  rw [isIso_iff_coyoneda_map_bijective]
  intro F
  have key : Function.Bijective fun h : (free R).obj (yoneda.obj X) ⟶ F =>
      ((free R).map (yoneda.map f₁) ≫ h, (free R).map (yoneda.map f₂) ≫ h) := by
    have e12 := (freeYoneda_ev_bijective R (Y := Y₁) F).prodMap (freeYoneda_ev_bijective R (Y := Y₂) F)
    refine (e12.of_comp_iff' _).1 ?_
    have comm : (Prod.map (fun h : (free R).obj (yoneda.obj Y₁) ⟶ F => Sec.map h (freeGen R (yoneda.obj Y₁) Y₁ (𝟙 Y₁)))
        (fun h : (free R).obj (yoneda.obj Y₂) ⟶ F => Sec.map h (freeGen R (yoneda.obj Y₂) Y₂ (𝟙 Y₂)))) ∘
        (fun h : (free R).obj (yoneda.obj X) ⟶ F =>
          ((free R).map (yoneda.map f₁) ≫ h, (free R).map (yoneda.map f₂) ≫ h)) =
        (fun s : Sec F X => (Sec.res f₁ s, Sec.res f₂ s)) ∘
          (fun h : (free R).obj (yoneda.obj X) ⟶ F => Sec.map h (freeGen R (yoneda.obj X) X (𝟙 X))) := by
      funext h
      simp only [Function.comp_apply, Prod.map_apply]
      rw [freeYoneda_ev_pre R f₁ h, freeYoneda_ev_pre R f₂ h]
    rw [comm]
    exact (hb F).comp (freeYoneda_ev_bijective R F)
  have hβ : Function.Bijective fun g : ((free R).obj (yoneda.obj Y₁) ⊞ (free R).obj (yoneda.obj Y₂)) ⟶ F =>
      (biprod.inl ≫ g, biprod.inr ≫ g) := by
    constructor
    · intro g g' e
      simp only [Prod.mk.injEq] at e
      exact biprod.hom_ext' _ _ e.1 e.2
    · rintro ⟨a, b⟩
      exact ⟨biprod.desc a b, by simp⟩
  refine (hβ.of_comp_iff' _).1 ?_
  convert key using 1
  funext h
  simp

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.free_sections_ext_res_map : ∀ (R : Type) [CommRing R] (P : PSh) (F : Shv R), (∀ a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (a U x) = a V (P.map g.op x)) → ∃ φ : (free R).obj P ⟶ F, ∀ U x, Sec.map φ (freeGen R P U x) = a U x) ∧ (∀ φ ψ : (free R).obj P ⟶ F, (∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) → φ = ψ) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x)) ∧ ∀ (Q : PSh) (f : P ⟶ Q) U x, Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  first | (exact @GlobalTheory.EtC.free_hom_sections) | (exact GlobalTheory.EtC.free_hom_sections) | (intros; apply GlobalTheory.EtC.free_hom_sections  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheafSections_specProd_bijective : ∀ (R : Type) [CommRing R] (A B : Type) [CommRing A] [CommRing B] (F : Shv R), Function.Bijective fun s : Sec F (Spec (CommRingCat.of (A × B))) => (Sec.res (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) s, Sec.res (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) s) := by
  first | exact @GlobalTheory.EtC.sec_prod | exact GlobalTheory.EtC.sec_prod | (intros; apply GlobalTheory.EtC.sec_prod <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistModule_free_and_generator_summand : ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [Nontrivial A], Module.Free (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ∧ ∀ ζ : Prim q A, ∃ f : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), f (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  first | (exact @GlobalTheory.TwFree.twist_free) | (exact GlobalTheory.TwFree.twist_free) | (intros; apply GlobalTheory.TwFree.twist_free  <;> assumption)
end
