module

public import Development.EtaleCohomology.TateTwists.Bundle005
public import Development.EtaleCohomology.TateTwists.Bundle012
public import Development.EtaleCohomology.TateTwists.Bundle010
public import Development.EtaleCohomology.TateTwists.Bundle013
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.TateTwists.Bundle011
public import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.EpiMono
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

namespace LateralTheory.Fin.EtaleLocalPropertyBasicClosure
theorem etale_torsion_cohomology_localization_basic : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure := by
  apply LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure := etale_torsion_cohomology_localization_basic
end LateralTheory.Fin.EtaleLocalPropertyBasicClosure
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwTorsPf

section Field
variable {q : ℕ} [NeZero q] {k : Type} [Field k]

theorem prim_isPrim (ζ : Prim q k) : IsPrimitiveRoot ζ.1 q := by
  haveI : NeZero (q : k) := ⟨ζ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := ζ.2.2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] using h

theorem pow_eq_pow_cast {ζ : k} (h : IsPrimitiveRoot ζ q) {m n : ℕ} (e : ζ ^ m = ζ ^ n) :
    (m : ZMod q) = (n : ZMod q) := by
  have h0 : ζ ≠ 0 := h.ne_zero (NeZero.ne q)
  have e' : ζ ^ ((m : ℤ) - n) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, zpow_natCast, e, div_self (pow_ne_zero _ h0)]
  have hd := (h.zpow_eq_one_iff_dvd _).1 e'
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub (n : ℤ) (m : ℤ) q).2 hd
  exact_mod_cast this.symm
end Field

section Field2
variable {q : ℕ} [NeZero q] {k : Type} [Field k]

def ex (ζ0 ξ : Prim q k) : ℕ :=
  ((prim_isPrim ζ0).eq_pow_of_pow_eq_one (prim_isPrim ξ).pow_eq_one).choose

theorem ex_spec (ζ0 ξ : Prim q k) : ζ0.1 ^ ex ζ0 ξ = ξ.1 :=
  ((prim_isPrim ζ0).eq_pow_of_pow_eq_one (prim_isPrim ξ).pow_eq_one).choose_spec.2

theorem ex_cop (ζ0 ξ : Prim q k) : (ex ζ0 ξ).Coprime q := by
  have h := prim_isPrim ξ
  rw [← ex_spec ζ0 ξ] at h
  exact ((prim_isPrim ζ0).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) _).1 h

theorem ex_eq (ζ0 ξ : Prim q k) {m : ℕ} (h : ζ0.1 ^ m = ξ.1) : (ex ζ0 ξ : ZMod q) = m :=
  pow_eq_pow_cast (prim_isPrim ζ0) ((ex_spec ζ0 ξ).trans h.symm)

def exU (ζ0 ξ : Prim q k) : (ZMod q)ˣ := ZMod.unitOfCoprime _ (ex_cop ζ0 ξ)

theorem exU_rel (ζ0 η ξ : Prim q k) (a : (ZMod q)ˣ) (h : ξ.1 = η.1 ^ (a : ZMod q).val) :
    exU ζ0 ξ = exU ζ0 η * a := by
  ext
  simp only [exU, ZMod.coe_unitOfCoprime, Units.val_mul]
  rw [ex_eq ζ0 ξ (m := ex ζ0 η * (a : ZMod q).val)]
  · push_cast
    rw [ZMod.natCast_zmod_val]
  · rw [pow_mul, ex_spec, h]

theorem exU_self (ζ0 : Prim q k) : exU ζ0 ζ0 = 1 := by
  ext
  simp only [exU, ZMod.coe_unitOfCoprime, Units.val_one]
  rw [ex_eq ζ0 ζ0 (m := 1) (pow_one _)]
  simp

def val (i : ℤ) (ζ0 ξ : Prim q k) : ULift.{1} (ZMod q) := ULift.up (((exU ζ0 ξ) ^ i : (ZMod q)ˣ) : ZMod q)

def fn (i : ℤ) (ζ0 : Prim q k) : (Prim q k →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (val i ζ0)

theorem rel_le (i : ℤ) (ζ0 : Prim q k) : twRel q i k ≤ LinearMap.ker (fn i ζ0) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨η, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, fn, Finsupp.linearCombination_single]
  rw [sub_eq_zero, val, val, exU_rel ζ0 η ξ a h, mul_zpow]
  apply ULift.ext
  simp [mul_comm]

theorem field_tors (i : ℤ) (ζ : Prim q k) (c : ℕ)
    (h : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q k →₀ ULift.{1} (ZMod q)) ⧸ twRel q i k) = 0) :
    q ∣ c := by
  have h2 := congrArg ((twRel q i k).liftQ (fn i ζ) (rel_le i ζ)) h
  rw [map_nsmul, map_zero, Submodule.liftQ_apply, fn, Finsupp.linearCombination_single, val, exU_self] at h2
  have h3 := congrArg ULift.down h2
  simp at h3
  exact (ZMod.natCast_eq_zero_iff c q).1 (by simpa using h3)
end Field2

theorem twF_map_mk {q : ℕ} (i : ℤ) {A B : CommRingCat.{0}} (φ : A ⟶ B) (ζ : Prim q A) :
    ((twF q i).map φ).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (ζ.map φ.hom) 1) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map φ.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]

theorem ring_tors {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ℕ)
    (h : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = 0) :
    q ∣ c := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let f : A →+* A ⧸ m := Ideal.Quotient.mk m
  have h2 := congrArg (Submodule.mapQ _ _ (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)) (Prim.map f))
    (twRel_le q i f)) h
  rw [map_nsmul, map_zero, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at h2
  exact field_tors i (ζ.map f) c h2

theorem jsEt : Scheme.JointlySurjective (Scheme.precoverage @AlgebraicGeometry.Etale.{0}) where
  exists_eq {X} R := fun ⟨hR, _⟩ x ↦ by
    rw [Scheme.jointlySurjectivePrecoverage, Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    obtain ⟨Y, g, hg, heq⟩ := hR x
    exact ⟨Y, g, hg, heq⟩

theorem TwTors_of : LateralTheory.EtaleFoundations.TwLocPf.TwTors := by
  intro q _ i U _ ζ c hc
  let P := Scheme.Γ ⋙ twF q i
  let x : P.obj (op U) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have h1 : (toSheafify Scheme.etaleTopology P).app (op U) (c • x) =
      (toSheafify Scheme.etaleTopology P).app (op U) 0 := by
    have : ((toSheafify Scheme.etaleTopology P).app (op U)).hom (c • x) = 0 := by
      rw [map_nsmul]; exact hc
    simpa using this
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c • x) 0 h1
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  haveI := jsEt
  obtain ⟨j, y, -⟩ := 𝒰.exists_eq (Classical.arbitrary U)
  have hj := hle _ _ (Presieve.ofArrows.mk j)
  simp only [Presheaf.equalizerSieve_apply, map_zero] at hj
  have : Nonempty (𝒰.X j) := ⟨y⟩
  have : Nonempty (⊤ : (𝒰.X j).Opens) := ⟨⟨y, trivial⟩⟩
  have h3 : ((twF q i).map (𝒰.f j).appTop).hom (c • x) = 0 := hj
  have h4 : c • ((twF q i).map (𝒰.f j).appTop).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 0 :=
    (map_nsmul ((twF q i).map (𝒰.f j).appTop).hom c _).symm.trans h3
  rw [twF_map_mk] at h4
  exact ring_tors i _ c h4

end LateralTheory.EtaleFoundations.TwTorsPf
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_ev_mk : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
    (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
      ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x

def cupflip_ev_res : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h
    (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g)

def cupflip_sub_res : Prop :=
  ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) {V : Scheme.{0}} (g : V ⟶ U),
    (x.res g).sub j l h = (x.sub j l h).res g

theorem cupflip_aw_cochain_of (hm : cupflip_ev_mk) (he : cupflip_ev_res) (hs : cupflip_sub_res) :
    cupflip_aw_cochain := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hm R (E := E) (I := K) (n := k)
    (fun N w h U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n)
      (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev (R := R) α p _ rfl U (x.sub 0 p (by omega))) (ev (R := R) β (N - p) _ rfl U (x.sub p (N - p) (by omega))))
    (by
      intro N w h V U g x

      simp only [Sec.res, map_sum, Units.smul_def, map_zsmul]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      congr 1
      have := μ.nat g (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
        (ev (R := R) α p _ rfl U (x.sub 0 p (by omega))) (ev (R := R) β (N - p) _ rfl U (x.sub p (N - p) (by omega)))
      simp only [Sec.res] at this
      rw [this]
      have e1 := he R α p _ rfl V U g (x.sub 0 p (by omega))
      have e2 := he R β (N - p) _ rfl V U g (x.sub p (N - p) (by omega))
      simp only [Sec.res] at e1 e2
      rw [e1, e2, hs, hs])
  exact ⟨γ, fun N w h U x => hγ N w h U x⟩

theorem cupflip_sub_res_holds : cupflip_sub_res := by
  intro E U N x j l h V g
  simp only [Sx.res, Sx.sub]
  exact NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

theorem freeGen_res {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have key := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology ((freeP R).obj P)) g.op
    (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x))
  simp only [freeGen]
  erw [← key]
  congr 1
  simp only [freeP, ModuleCat.freeMk, ModuleCat.free]
  erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tensor_universal_property : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u

def tensor_quasi_isomorphism : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u

theorem tt_res_side_of (huniv : tensor_universal_property) (hqis : tensor_quasi_isomorphism) : tt_res_side := by
  intro q _ i I J M T e hI hJ hflat σ τ hσ hτ
  obtain ⟨hIge, ε, hε, hgen⟩ := hI
  obtain ⟨u, hu, -⟩ := (huniv (ZMod q) σ hσ).1 τ ε (𝟙 J)
  have := hIge
  have := hJ
  refine ⟨u, hqis (ZMod q) σ τ hσ hτ hflat ε u hu, fun U ζ b => ?_⟩
  rw [hu U 0 0 0 (add_zero 0), hgen U ζ]
  simp only [HomologicalComplex.id_f]
  rfl

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations

def phiT {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) {N : ℕ} {U : Scheme.{0}}
    (x : Sx E N U) (w : ℤ) (z : Pr N) : Sec (K.X w) U :=
  if h : -((z.1 : ℤ) + (z.2.1 : ℤ)) + k = w then
    ((m * (z.1 : ℤ)).negOnePow : ℤ) • μ.mul U (-(z.1 : ℤ) + n) (-(z.2.1 : ℤ) + m) w (by omega)
      (ev (R := R) α z.1 _ rfl U (x.along z.2.2.1)) (ev (R := R) β z.2.1 _ rfl U (x.along z.2.2.2))
  else 0

def phi {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) {N : ℕ} {U : Scheme.{0}}
    (x : Sx E N U) (w : ℤ) (c : Pr N →₀ ℤ) : Sec (K.X w) U :=
  c.sum fun z a => a • phiT μ hk α β x w z

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (R := R) (α - β) p s h U x = ev (R := R) α p s h U x - ev (R := R) β p s h U x := by
  simp [ev, Cochain.sub_v, Preadditive.comp_sub]
  rfl

theorem ev_zsmul' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h U x
    (c : ℤ) : ev (R := R) (c • α) p s h U x = c • ev (R := R) α p s h U x := by
  simp [ev, Cochain.smul_v, Linear.comp_smul]
  rfl

def cupflip_ev_ext : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    ∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev (R := R) α p s h U x = ev (R := R) β p s h U x) → α = β

def cupflip_eta_mk : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ η : Cochain ((chains R).obj E) K (k - 1), ∀ N s hs U x, ev (R := R) η N s hs U x = phi μ hk α β x s (h N)

def cupflip_eta_delta : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (η : Cochain ((chains R).obj E) K (k - 1)),
    (∀ N s hs U x, ev (R := R) η N s hs U x = phi μ hk α.1 β.1 x s (h N)) →
    ∀ N t ht U x, ev (R := R) (δ (k - 1) k η) N t ht U x =
      (k.negOnePow : ℤ) • (phi μ hk α.1 β.1 x t (Pr.aw N) - phi μ hk α.1 β.1 x t (Pr.wa N))

theorem phi_aw {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
    (hγ : μ.IsAW hk α β γ) (N : ℕ) (t : ℤ) (ht : -(N : ℤ) + k = t) (U : Scheme.{0}) (x : Sx E N U) :
    phi μ hk α β x t (Pr.aw N) = ev (R := R) γ N t ht U x := by
  rw [hγ N t ht U x, phi, Pr.aw, ← Finsupp.sum_finsetSum_index (fun z => zero_smul ℤ (phiT μ hk α β x t z))
    (fun z a b => add_smul a b (phiT μ hk α β x t z))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.sum_single_index (zero_smul ℤ (phiT μ hk α β x t _)), one_smul, phiT, dite_eq_left (by have := p.2; push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  rw [Units.smul_def]
  rfl

def cupflip_phi_diag : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (hk' : m + n = k)
      (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)
      (γ' : Cochain ((chains R).obj E) K k), ν.IsAW hk' β α γ' →
      ∀ (N : ℕ) (t : ℤ) (ht : -(N : ℤ) + k = t) (U : Scheme.{0}) (x : Sx E N U),
        phi μ hk α β x t (Pr.wa N) = ((n * m).negOnePow : ℤ) • ev (R := R) γ' N t ht U x

theorem cupflip_phi_diag_pf : cupflip_phi_diag := by
  intro R _ I J K μ ν hflip E n m k hk hk' α β γ' hγ' N t ht U x
  rw [hγ' N t ht U x, phi, Pr.wa, ← Finsupp.sum_finsetSum_index (fun z => zero_smul ℤ (phiT μ hk α β x t z))
    (fun z a b => add_smul a b (phiT μ hk α β x t z)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Finsupp.sum_single_index (zero_smul ℤ (phiT μ hk α β x t _)), phiT,
    dite_eq_left (by push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  rw [hflip U _ _ t (by push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  simp only [Units.smul_def, smul_smul]
  congr 1
  have e : ((-1 : ℤ) ^ ((p : ℕ) * (N - p))) = (((p : ℕ) : ℤ) * ((N - p : ℕ) : ℤ)).negOnePow := by
    rw [Int.negOnePow_def, ← Nat.cast_mul, zpow_natCast]; simp
  rw [e]
  simp only [← Units.val_mul, ← Int.negOnePow_add]
  congr 1
  rw [Int.negOnePow_eq_iff]
  exact ⟨m * ((N - p : ℕ) : ℤ) - n * m, by ring⟩

theorem cupflip_homotopy_of (hext : cupflip_ev_ext) (hmk : cupflip_eta_mk) (hdl : cupflip_eta_delta) :
    cupflip_homotopy := by
  intro h hs R _ I J K μ ν hflip E n m k hk hk' α β γ γ' hγ hγ'
  obtain ⟨η, hη⟩ := hmk h hs.1 R μ E hk α.1 β.1
  have hd := hdl h hs R μ E hk α β η hη
  refine ⟨((k.negOnePow : ℤˣ) : ℤ) • η, ?_⟩
  rw [show δ (k - 1) k (((k.negOnePow : ℤˣ) : ℤ) • η) = ((k.negOnePow : ℤˣ) : ℤ) • δ (k - 1) k η from
    (δ_hom ℤ _ _ (k - 1) k).map_smul _ _]
  apply hext R
  intro N t ht U x
  have h1 := phi_aw μ hk α.1 β.1 γ.1 hγ N t ht U x
  have h2 := cupflip_phi_diag_pf R μ ν hflip E hk hk' α.1 β.1 γ'.1 hγ' N t ht U x
  rw [ev_zsmul', hd N t ht U x, h1, h2, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul, Units.smul_def, ev_sub', ev_zsmul']

end LateralTheory.EtaleFoundations
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwResSecInj

theorem sigma_map_mono (R : Type) [CommRing R] (ι : Type) {X Y : ModuleCat.{1} (ULift.{1} R)} (f : X ⟶ Y) [Mono f] :
    Mono (Limits.Sigma.map (fun (_ : ι) => f)) := by
  let α : Discrete.functor (fun (_ : ι) => X) ⟶ Discrete.functor (fun _ => Y) := Discrete.natTrans (fun _ => f)
  have : ∀ j, Mono (α.app j) := fun j => by
    change Mono f; infer_instance
  have h1 : Mono α := NatTrans.mono_of_mono_app _
  exact (colim : (Discrete ι ⥤ ModuleCat.{1} (ULift.{1} R)) ⥤ _).map_mono α

instance evLA_mono (R : Type) [CommRing R] (U : Scheme.{0}) :
    (evaluationLeftAdjoint (ModuleCat.{1} (ULift.{1} R)) (op U)).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    have hm : ∀ c, Mono (((evaluationLeftAdjoint (ModuleCat.{1} (ULift.{1} R)) (op U)).map f).app c) := by
      intro c
      rw [evaluationLeftAdjoint_map_app]
      have e : (Limits.Sigma.desc fun h => f ≫ Sigma.ι (fun _ => Y) h) = Limits.Sigma.map (fun (_ : op U ⟶ c) => f) := by
        ext; simp
      rw [e]; exact sigma_map_mono R _ f
    exact NatTrans.mono_of_mono_app _

end LateralTheory.EtaleFoundations.TwResSecInj

open LateralTheory.EtaleFoundations.TwResSecInj in
theorem LateralTheory.EtaleFoundations.etale_injective_sheaf_sections_injective_holds : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective := by
  intro R _ M _ U
  have adj := (evaluationAdjunctionRight (ModuleCat.{1} (ULift.{1} R)) (op U)).comp
    (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))
  have hI := Injective.injective_of_adjoint adj M
  exact Module.injective_module_of_injective_object (inj := hI) _ _
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_semilinear_cohomology_operation_image_spec_of_hyp
    (hImage₂ : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
      (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
      ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
        ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β) :
    EtaleSemilinearCohomologyOperationImageSpec :=
  hImage₂

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExactLocPf

variable {R : Type} [CommRing R]

lemma kernel_lift_sec (S : ShortComplex (Shv R)) (U : Scheme.{0}) (b : Sec S.X₂ U)
    (hb : Sec.map S.g b = 0) : ∃ k : Sec (kernel S.g) U, Sec.map (kernel.ι S.g) k = b := by
  let T : ShortComplex (Shv R) := ShortComplex.mk (kernel.ι S.g) S.g (kernel.condition _)
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g)
  have : Mono T.f := by dsimp [T]; infer_instance
  have hE : (T.map (LateralTheory.EtaleFoundations.ResSecPf.secF R U)).Exact :=
    hT.map_of_mono_of_preservesKernel _ this inferInstance
  rw [ShortComplex.moduleCat_exact_iff] at hE
  exact hE b hb

lemma epi_lift (S : ShortComplex (Shv R)) (hS : S.Exact) :
    Epi (kernel.lift S.g S.f S.zero) := by
  exact hS.epi_kernelLift

end LateralTheory.EtaleFoundations.ExactLocPf

open LateralTheory.EtaleFoundations.ExactLocPf in
theorem LateralTheory.EtaleFoundations.ResSecPf.exact_loc_of : LateralTheory.EtaleFoundations.ResSecPf.exact_loc := by
  intro R _ S hS U b hb
  obtain ⟨k, hk⟩ := kernel_lift_sec S U b hb
  let p := kernel.lift S.g S.f S.zero
  have : Epi p := epi_lift S hS
  have hls : Sheaf.IsLocallySurjective p := (Sheaf.isLocallySurjective_iff_epi' (φ := p)).2 this
  refine ⟨Presheaf.imageSieve p.hom k, Presheaf.imageSieve_mem Scheme.etaleTopology p.hom (U := op U) k, ?_⟩
  rintro V g ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have e1 : S.f = p ≫ kernel.ι S.g := (kernel.lift_ι _ _ _).symm
  have e2 : Sec.map S.f a = Sec.map (kernel.ι S.g) (Sec.map p a) := by
    rw [e1]; rfl
  rw [e2, ← hk]
  change Sec.map (kernel.ι S.g) ((p.hom.app _).hom a) = _
  have ha' : (p.hom.app (op V)).hom a = ((kernel S.g).obj.map g.op).hom k := ha
  rw [ha']
  exact congrArg (fun f => f.hom k) ((kernel.ι S.g).hom.naturality g.op)
end

section

theorem LateralTheory.EtaleFoundations.pp_ev_delta_of : LateralTheory.EtaleFoundations.pp_ev_delta :=
  LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds
end
