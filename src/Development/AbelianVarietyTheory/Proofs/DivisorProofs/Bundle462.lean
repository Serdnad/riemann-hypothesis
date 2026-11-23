module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismChainComplexBoundaryIdentities
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.hypercohomologyPullback_biprod_inl_inr_bijective : ∀ (R : Type) [CommRing R] (K L I : Cx R) (n : ℤ), Function.Bijective fun x : CohomologyClass (K ⊞ L) I n => (cpull (biprod.inl : K ⟶ K ⊞ L) I n x, cpull (biprod.inr : L ⟶ K ⊞ L) I n x) := by
  first | exact @GlobalTheory.EtC.cpull_biprod_bijective | exact GlobalTheory.EtC.cpull_biprod_bijective | (intros; apply GlobalTheory.EtC.cpull_biprod_bijective <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleHypercohomology_iso_of_injective_resolution : ∀ (R : Type) [CommRing R] (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C), C.IsStrictlyGE 0 → (∀ t, Injective (C.X t)) → QuasiIso ε → ∀ (K : Cx R) (n : ℤ), Nonempty (HK R K M n ≃+ CohomologyClass K C n) := by
  first | exact @GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution | exact GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution | (intros; apply GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ZcFun

variable {R : Type} [CommRing R]

theorem cpull_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpull_cpush {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_homotopy {K L : Cx R} {f g : K ⟶ L} (h : Homotopy f g) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  change CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • z.comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp z x.1 (by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp [zcomp, hz, Cochain.add_comp, smul_smul]

theorem main : ∀ (R : Type) [CommRing R] , (∀ (K I : Cx R) (n : ℤ) x, cpull (𝟙 K) I n x = x ∧ cpush K (𝟙 I) n x = x) ∧ (∀ {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) x, cpull (f ≫ g) I n x = cpull f I n (cpull g I n x)) ∧ (∀ (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) x, cpush K (f ≫ g) n x = cpush K g n (cpush K f n x)) ∧ (∀ {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) x, cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x)) ∧ (∀ {K L : Cx R} (f g : K ⟶ L), Nonempty (Homotopy f g) → ∀ (I : Cx R) (n : ℤ), cpull f I n = cpull g I n ∧ cpush I f n = cpush I g n) := by
  intro R _
  refine ⟨fun K I n x => ⟨cpull_id K I n x, InjResCmp.cpush_id K I n x⟩, fun f g I n x => cpull_comp f g I n x,
    fun K _ _ _ f g n x => InjResCmp.cpush_comp K f g n x, fun f g n x => cpull_cpush f g n x, ?_⟩
  rintro K L f g ⟨h⟩ I n
  exact ⟨AddMonoidHom.ext fun x => cpull_homotopy h I n x, AddMonoidHom.ext fun x => InjResCmp.cpush_homotopy I h n x⟩

end GlobalTheory.EtC.ZcFun
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.hypercohomology_trivial_of_terms_degreeZero : ∀ (R : Type) [CommRing R] (K M : Cx R) [K.IsStrictlyLE 0], (∀ p n : ℤ, p ≤ 0 → Subsingleton (CohomologyClass (sgl (K.X p)) M n)) → ∀ n : ℤ, Subsingleton (CohomologyClass K M n) := by
  first | exact @GlobalTheory.nullHtpy_stair | exact GlobalTheory.nullHtpy_stair | (intros; apply GlobalTheory.nullHtpy_stair <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod : ∀ (R : Type) [CommRing R] (M N : Shv R), FlatS M → FlatS N → FlatS (M ⊞ N) := by
  first | (exact @GlobalTheory.EtC.flatS_biprod) | (exact GlobalTheory.EtC.flatS_biprod) | (intros; apply GlobalTheory.EtC.flatS_biprod  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf : ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M], (∀ U : Scheme.{0}, Module.Flat (ULift.{1} (ZMod q)) (Sec M U)) ∧ FlatS M := by
  first | (exact @GlobalTheory.EtC.InjFlat.flat_of_injective) | (exact GlobalTheory.EtC.InjFlat.flat_of_injective) | (intros; apply GlobalTheory.EtC.InjFlat.flat_of_injective  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.hypercohomology_longExact_first_of_injective : ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x) := by
  first | (exact @GlobalTheory.EtC.longExact_first_of_injective) | (exact GlobalTheory.EtC.longExact_first_of_injective) | (intros; apply GlobalTheory.EtC.longExact_first_of_injective  <;> assumption)
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem ev_basic : ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧
      ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧
      ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧
      ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧
    (∀ α β : Cochain ((chains R).obj E) I n,
      (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧
    (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
      ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧
    ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  intro R _ E I n
  refine ⟨fun α β p s h U x => ⟨CupSpec.ev_add α β p s h U x,
      map_sub (CupSpec.evHom I n p s h U x) α β, CupSpec.ev_zero p s h U x,
      fun c => CupSpec.ev_zsmul c α p s h U x⟩,
    fun α p s h V U g x => CupSpec.ev_res α p s h g x,
    fun α β H => CupSpec.ev_ext α β H,
    fun f α p s h U x => CupSpec.ev_pull f α p s h U x, ?_⟩
  intro J m α p s h U x
  rw [CupSpec.ev_def, CupSpec.ev_def, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ← Category.assoc]
  rfl

end GlobalTheory.EtC

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem ev_delta_values : ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
    (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
    (∀ (x : Sx E 0 U), EtC.ev (δ n m α) 0 m (by simp) U x =
      Sec.map (I.d n m) (EtC.ev α 0 n (by simp) U x)) ∧
    ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
      EtC.ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (EtC.ev α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • EtC.ev α p t (by omega) U (x.face i) := by
  intro R _ E I n m hm α U
  exact ⟨fun x => CupSpec.ev_δ_zero hm α U n m (by simp) (by simp) x,
    fun p s t hs ht x => CupSpec.ev_δ_succ hm α U p s t hs ht x⟩

end GlobalTheory
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
      (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
      (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x =
        Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧
      ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
        (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
        ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
          m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  intro R _ E I n m hm α U
  have ev_def {k : ℤ} (β : Cochain ((chains R).obj E) I k) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + k = s) (x : Sx E p U) :
      ev β p s h U x = Sec.map ((chainsXIso R E p).inv ≫ β.v _ _ h) (freeGen R _ U x) := rfl
  have hzero (x : Sx E 0 U) :
      ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x) := by
    rw [ev_def, δ_v n m hm α _ m (by simp) n 1 (by omega) (by simp),
      (CupSpec.isZero_chains (R := R) E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0,
      zero_comp, smul_zero, add_zero]
    rfl
  have hsucc (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
      (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
      ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
    rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add,
      Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _),
      CupSpec.chains_d, Category.assoc, Preadditive.sum_comp]
    refine (map_add (CupSpec.mapHom _ _ (freeGen R _ U x)) _ _).trans ?_

    rw [map_zsmul, map_sum, Units.smul_def]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    rfl
  exact ⟨hzero, hsucc⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_cochain_ev_eq_of_natural :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
      (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
        Sec.res g (a p s h U x) = a p s h V (x.res g)) →
      ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x := by
  intro R _ E I n a ha
  have components : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ I.X j,
      ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ U x) = a p j (hp ▸ hij) U x := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U x
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
  have hEval := hφ _ _ h p rfl U x
  rw [eqToHom_refl, Category.id_comp] at hEval
  exact hEval

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.prism_chain_complex_boundary_identities : (∀ N (c : Pr N →₀ ℤ), Pr.d N (Pr.d N c) = 0) ∧ (∀ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) c, Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c)) ∧ (∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.Deg k (Pr.d N c)) ∧ (∀ N k (c : Pr N →₀ ℤ), Pr.Deg k c → Pr.Deg k (Pr.bd c)) ∧ (∀ N (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0) ∧ (∀ N (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)) ∧ ∀ N, Pr.Deg N (Pr.aw N) ∧ Pr.Deg N (Pr.wa N) := by
  first | (exact @GlobalTheory.EtC.PrCx.pr_complex) | (exact GlobalTheory.EtC.PrCx.pr_complex) | (intros; apply GlobalTheory.EtC.PrCx.pr_complex  <;> assumption)
end
