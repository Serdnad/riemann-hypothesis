module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

@[expose] public section

section

namespace GlobalTheory

theorem finite_quotient_of_complete_nakayama : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → ∀ {T Z : Type} [AddCommGroup T] [Module R T] [AddCommGroup Z] [Module R Z], (∀ x : ℕ → T, ∃ y : T, ∀ n : ℕ, ∃ z : T, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) → (∀ c : Z, (∀ n : ℕ, ∃ z : Z, c = ϖ ^ n • z) → c = 0) → ∀ (d : T →ₗ[R] Z) (N : Submodule R Z), LinearMap.range d ≤ N → ∀ s : Finset Z, (∀ c : Z, ∃ (a : Z → R) (c' : Z) (x : T), c = ∑ i ∈ s, a i • i + ϖ • c' + d x) → Module.Finite R (Z ⧸ N) := by
  intro R _ ϖ hR T Z _ _ _ _ hT hZ d N hdN s hs
  classical
  choose A C X hACX using hs
  choose limR hlimR using hR
  choose limT hlimT using hT
  have key : ∀ c : Z, ∀ n : ℕ, c = ∑ i ∈ s, (∑ j ∈ Finset.range n, ϖ ^ j * A (C^[j] c) i) • i
      + ϖ ^ n • C^[n] c + d (∑ j ∈ Finset.range n, ϖ ^ j • X (C^[j] c)) := by
    intro c n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      simp only [Finset.sum_range_succ]
      set e := C^[n] c with he
      conv_lhs => rw [hACX e]
      simp only [add_smul, Finset.sum_add_distrib, smul_add, map_add (f := _), map_smul, Finset.smul_sum,
        mul_smul, pow_succ]
      abel
  have hfin : ∀ c : Z, c - (∑ i ∈ s, limR (fun j => A (C^[j] c) i) • i
      + d (limT (fun j => X (C^[j] c)))) = 0 := by
    intro c
    apply hZ
    intro n
    have hk := key c n
    choose b hb using fun i => hlimR (fun j => A (C^[j] c) i) n
    obtain ⟨z, hz⟩ := hlimT (fun j => X (C^[j] c)) n
    refine ⟨C^[n] c - ∑ i ∈ s, b i • i - d z, ?_⟩
    have hα : ∀ i, limR (fun j => A (C^[j] c) i)
        = (∑ j ∈ Finset.range n, ϖ ^ j * A (C^[j] c) i) + ϖ ^ n * b i :=
      fun i => sub_eq_iff_eq_add'.mp (hb i)
    have hY := sub_eq_iff_eq_add'.mp hz
    simp only [hα, hY]
    rw [sub_eq_iff_eq_add]
    refine hk.trans ?_
    simp only [add_smul, Finset.sum_add_distrib, smul_sub, map_add (f := _), map_smul, Finset.smul_sum,
      mul_smul]
    abel
  have h0 : ∀ y : T, N.mkQ (d y) = 0 := by
    intro y
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hdN ⟨y, rfl⟩
  refine ⟨⟨s.image N.mkQ, ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨c, rfl⟩ := N.mkQ_surjective q
  have hc := sub_eq_zero.mp (hfin c)

  rw [hc, map_add (f := _), h0, add_zero, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)))

end GlobalTheory
end

section

namespace GlobalTheory

private lemma exists_char_augmentation_zero_acting_as_one {K Γ V : Type} [Field K] [Group Γ]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K Γ V)
    (χ : Γ →* Kˣ) (hs : ρ.IsSemisimpleRepresentation)
    (hno : ∀ v : V, (∀ g, ρ g v = ((χ g : Kˣ) : K) • v) → v = 0) :
    ∃ x : MonoidAlgebra K Γ, MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) x = 0 ∧
      ρ.asAlgebraHom x = 1 := by
  set ε := MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) with hε
  have hsm : IsSemisimpleModule (MonoidAlgebra K Γ) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hs
  let b := Module.finBasis K V
  let m : Fin (Module.finrank K V) → ρ.asModule := fun i => ρ.asModuleEquiv.symm (b i)
  let P : Submodule (MonoidAlgebra K Γ) (Fin (Module.finrank K V) → ρ.asModule) :=
    Submodule.map (LinearMap.toSpanSingleton (MonoidAlgebra K Γ) _ m)
      (RingHom.ker (ε : MonoidAlgebra K Γ →+* K))
  obtain ⟨C, hC⟩ := exists_isCompl P
  have hm : m ∈ P ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.mp hm
  have hkill : ∀ x, ε x = 0 → x • c = 0 := by
    intro x hx
    have h1 : x • c ∈ P := by
      have : x • c = x • m - x • p := by rw [← hpc, smul_add, add_sub_cancel_left]
      rw [this]
      exact P.sub_mem (Submodule.mem_map.mpr ⟨x, RingHom.mem_ker.mpr hx,
        LinearMap.toSpanSingleton_apply _ _ _ _⟩) (P.smul_mem x hp)
    have h2 : x • c ∈ P ⊓ C := Submodule.mem_inf.mpr ⟨h1, C.smul_mem x hc⟩
    rwa [hC.inf_eq_bot, Submodule.mem_bot] at h2
  have hc0 : c = 0 := by
    funext i
    have hv := hno (ρ.asModuleEquiv (c i)) fun g => by
      have h := congrFun (hkill (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 ((χ g : Kˣ) : K))
        (by simp [hε, MonoidAlgebra.lift_single])) i
      change ρ.asModuleEquiv.symm (ρ.asAlgebraHom _ (ρ.asModuleEquiv (c i))) = 0 at h
      rw [LinearEquiv.map_eq_zero_iff, map_sub, Representation.asAlgebraHom_single,
        Representation.asAlgebraHom_single, one_smul, map_one, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
      exact h
    simpa using hv
  rw [hc0, add_zero] at hpc
  obtain ⟨y, hy, hym⟩ := Submodule.mem_map.mp (show m ∈ P from hpc ▸ hp)
  refine ⟨y, RingHom.mem_ker.mp hy, b.ext fun i => ?_⟩
  have h := congrFun hym i
  change ρ.asModuleEquiv.symm (ρ.asAlgebraHom y (ρ.asModuleEquiv (ρ.asModuleEquiv.symm (b i)))) =
    ρ.asModuleEquiv.symm (b i) at h
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_eq, LinearEquiv.apply_symm_apply] at h
  simpa using h

private lemma false_of_trace_pow_eq_card_add_one_sub {L ι : Type} [Field L] [CharZero L] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι L) (h : ∀ n : ℕ, (M ^ n).trace = ((Fintype.card ι : L) + 1) - 0 ^ n) :
    False := by
  set D : L := (Fintype.card ι : L) + 1 with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact Nat.cast_add_one_ne_zero _
  have hpoly : ∀ f : Polynomial L, (Polynomial.aeval M f).trace = D * f.eval 1 - f.eval 0 := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg => simp only [map_add (f := _), Matrix.trace_add, hf, hg, Polynomial.eval_add]; ring
    | monomial n a =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        Matrix.trace_smul, h n, Polynomial.eval_monomial, Polynomial.eval_monomial, one_pow,
        smul_eq_mul]
      ring
  set p := M.charpoly with hp
  have hvan : ∀ g : Polynomial L, D * (g * p).eval 1 - (g * p).eval 0 = 0 := by
    intro g
    rw [← hpoly, map_mul, hp, Matrix.aeval_self_charpoly, mul_zero, Matrix.trace_zero]
  have hp1 : p.eval 1 = 0 := by
    have := hvan Polynomial.X
    simp only [Polynomial.eval_mul, Polynomial.eval_X, one_mul, zero_mul, sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hD0
  have hp0 : p.eval 0 = 0 := by
    have := hvan 1
    simpa [hp1] using this
  have hpne : p ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpne 1
  set b := p.rootMultiplicity 1
  have hb : 0 < b := (Polynomial.rootMultiplicity_pos hpne).mpr hp1
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C (1 : L)) ^ b) q :=
    ((Polynomial.irreducible_X_sub_C (1 : L)).coprime_iff_not_dvd.mpr hq).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hq0 : q.eval 0 = 0 := by
    have := hp0
    rw [hpq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (by norm_num))
  have he1 : (v * q).eval 1 = 1 := by
    have := congrArg (Polynomial.eval 1) huv
    simpa [Polynomial.eval_mul, zero_pow hb.ne'] using this
  have he0 : (v * q).eval 0 = 0 := by simp [Polynomial.eval_mul, hq0]
  have hidem : (v * q) * (v * q) = v * q - (u * v) * p := by
    rw [hpq]; linear_combination (v * q) * huv
  set E := Polynomial.aeval M (v * q) with hE
  have hEE : E * E = E := by
    rw [hE, ← map_mul, hidem, map_sub, map_mul (Polynomial.aeval M) (u * v) p, hp,
      Matrix.aeval_self_charpoly, mul_zero, sub_zero]
  have htrE : E.trace = D := by rw [hE, hpoly, he1, he0]; ring
  have hid : IsIdempotentElem (Matrix.toLin' E) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hEE]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rw [LinearMap.trace_eq_matrix_trace L (Pi.basisFun L ι), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin', htrE, hD] at htr
  have hle := Submodule.finrank_le (LinearMap.range (Matrix.toLin' E))
  rw [Module.finrank_fintype_fun_eq_card] at hle
  have : Fintype.card ι + 1 = Module.finrank L (LinearMap.range (Matrix.toLin' E)) := by
    exact_mod_cast htr
  omega

theorem _root_.GlobalTheory.exists_eigenvector_of_trace_eq_add_character :
    ∀ (K L Γ V ι : Type) [Field K] [Field L] [CharZero L] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] (φ : K →+* L) (ρ : Representation K Γ V) (σ : Γ →* Matrix ι ι L) (χ : Γ →* Kˣ), ρ.IsSemisimpleRepresentation → (∀ g, φ (LinearMap.trace K V (ρ g)) = (σ g).trace + φ ((χ g : Kˣ) : K)) → ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = ((χ g : Kˣ) : K) • v := by
  intro K L Γ V ι _ _ _ _ _ _ _ _ _ φ ρ σ χ hs htr
  by_contra hcon
  push_neg at hcon
  have hno : ∀ v : V, (∀ g, ρ g v = ((χ g : Kˣ) : K) • v) → v = 0 := fun v hv => by
    by_contra h0
    obtain ⟨g, hg⟩ := hcon v h0
    exact hg (hv g)
  obtain ⟨x, hx, hρx⟩ := exists_char_augmentation_zero_acting_as_one ρ χ hs hno
  let S : MonoidAlgebra K Γ →+* Matrix ι ι L :=
    MonoidAlgebra.liftNCRingHom ((Matrix.scalar ι).comp φ) σ
      (fun _ _ => Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)
  have hkey : ∀ z : MonoidAlgebra K Γ, φ (LinearMap.trace K V (ρ.asAlgebraHom z)) =
      (S z).trace + φ (MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) z) := by
    intro z
    refine MonoidAlgebra.induction_linear z ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add (f := _), Matrix.trace_add, hf, hg]; ring
    · intro g r
      rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul, map_mul, htr g]
      have hS : S (MonoidAlgebra.single g r) = Matrix.scalar ι (φ r) * σ g := by
        simp [S, MonoidAlgebra.liftNCRingHom, MonoidAlgebra.liftNC_single]
      rw [hS]
      rw [MonoidAlgebra.lift_single, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
        Matrix.trace_smul, smul_eq_mul, smul_eq_mul, map_mul]
      simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply]
      ring
  have hdim := htr 1
  rw [map_one ρ, LinearMap.trace_one, map_natCast, map_one σ, Matrix.trace_one, map_one χ,
    Units.val_one, map_one φ] at hdim
  have hpow : ∀ n : ℕ, ((S x) ^ n).trace = ((Fintype.card ι : L) + 1) - 0 ^ n := by
    intro n
    have h1 := hkey (x ^ n)
    rw [map_pow, hρx, one_pow, LinearMap.trace_one, map_natCast, map_pow, map_pow, hx] at h1
    have h0 : φ ((0 : K) ^ n) = (0 : L) ^ n := by rw [map_pow, map_zero]
    linear_combination hdim - h1 - h0
  exact false_of_trace_pow_eq_card_add_one_sub (S x) hpow

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.TraceIso

open Module

variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def tr (k : Type) [Field k] {A : Type} [Ring A] [Algebra k A] (V : Type) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] (a : A) : k :=
  LinearMap.trace k V (Algebra.lsmul k k V a)

section

variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

theorem tr_congr (e : V ≃ₗ[A] W) (a : A) : tr k V a = tr k W a := by
  have h : Algebra.lsmul k k W a = (e.restrictScalars k).conj (Algebra.lsmul k k V a) := by
    ext w
    simp [LinearEquiv.conj_apply]
  rw [tr, tr, h, LinearMap.trace_conj']

theorem tr_prod [FiniteDimensional k V] [FiniteDimensional k W] (a : A) :
    tr k (V × W) a = tr k V a + tr k W a := by
  have h : Algebra.lsmul k k (V × W) a = (Algebra.lsmul k k V a).prodMap (Algebra.lsmul k k W a) := by
    ext <;> simp
  rw [tr, h, LinearMap.trace_prodMap']
  rfl

theorem finiteDimensional_sub [FiniteDimensional k V] (P : Submodule A V) : FiniteDimensional k P := inferInstanceAs (FiniteDimensional k (P.restrictScalars k))

theorem finrank_eq_zero_of_hom [CharZero k] [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (h : ∀ a : A, tr k V a = tr k W a)
    (h₁ : ∀ f : V →ₗ[A] W, f = 0) (h₂ : ∀ f : W →ₗ[A] V, f = 0) : finrank k V = 0 := by
  classical
  let p : End A (V × W) := (LinearMap.inl A V W).comp (LinearMap.fst A V W)
  let F : End (End A (V × W)) (V × W) :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := by
        rintro φ ⟨v, w⟩
        have e₁ := LinearMap.congr_fun
          (h₁ ((LinearMap.snd A V W).comp (φ.comp (LinearMap.inl A V W)))) v
        have e₂ := LinearMap.congr_fun
          (h₂ ((LinearMap.fst A V W).comp (φ.comp (LinearMap.inr A V W)))) w
        have e₃ : φ (v, w) = φ (v, 0) + φ (0, w) := by rw [← map_add (f := _)]; simp
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.snd_apply,
          LinearMap.fst_apply, LinearMap.zero_apply] at e₁ e₂
        change ((φ (v, w)).1, (0 : W)) = φ (v, 0)
        rw [e₃]
        ext
        · simp [e₂]
        · exact e₁.symm }
  let b := Module.finBasis k (V × W)
  haveI : IsSemisimpleModule A (V × W) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A V W))
      (IsSemisimpleModule.range (LinearMap.inr A V W))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have hall : (p.restrictScalars k) = Algebra.lsmul k k (V × W) r :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hV : Algebra.lsmul k k V r = 1 := by
    ext v
    exact (congrArg Prod.fst (LinearMap.congr_fun hall (v, 0))).symm
  have hW : Algebra.lsmul k k W r = 0 := by
    ext w
    exact (congrArg Prod.snd (LinearMap.congr_fun hall (0, w))).symm
  have := h r
  unfold tr at this
  rw [hV, hW, LinearMap.trace_one, map_zero] at this
  exact_mod_cast this

theorem split_of_hom [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (f : V →ₗ[A] W) (hf : f ≠ 0) :
    ∃ (P : Submodule A V) (Q S : Submodule A W), Nonempty (V ≃ₗ[A] P × S) ∧ Nonempty (W ≃ₗ[A] Q × S) ∧
      finrank k P < finrank k V ∧ finrank k Q < finrank k W := by
  obtain ⟨P', hP'⟩ := exists_isCompl (LinearMap.ker f)
  obtain ⟨Q, hQ⟩ := exists_isCompl (LinearMap.range f)
  let e₁ : V ≃ₗ[A] (LinearMap.ker f) × (LinearMap.range f) :=
    (Submodule.prodEquivOfIsCompl _ _ hP').symm.trans
      ((LinearEquiv.refl A _).prodCongr
        ((Submodule.quotientEquivOfIsCompl _ _ hP').symm.trans f.quotKerEquivRange))
  let e₂ : W ≃ₗ[A] Q × (LinearMap.range f) := (Submodule.prodEquivOfIsCompl _ _ hQ.symm).symm
  haveI := finiteDimensional_sub (k := k) (LinearMap.ker f)
  haveI := finiteDimensional_sub (k := k) (LinearMap.range f)
  haveI := finiteDimensional_sub (k := k) Q
  haveI : Nontrivial (LinearMap.range f) :=
    Submodule.nontrivial_iff_ne_bot.2 fun h => hf (LinearMap.range_eq_bot.1 h)
  have hpos : 0 < finrank k (LinearMap.range f) := Module.finrank_pos
  refine ⟨_, Q, _, ⟨e₁⟩, ⟨e₂⟩, ?_, ?_⟩
  · rw [(e₁.restrictScalars k).finrank_eq, finrank_prod]; omega
  · rw [(e₂.restrictScalars k).finrank_eq, finrank_prod]; omega

end

theorem nonempty_linear_equiv_of_charpoly_eq [CharZero k] (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
    finrank k V + finrank k W ≤ n → (∀ a : A, tr k V a = tr k W a) → Nonempty (V ≃ₗ[A] W) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have step : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
      [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
      finrank k V + finrank k W ≤ n → (∀ a : A, tr k V a = tr k W a) → ∀ f : V →ₗ[A] W, f ≠ 0 →
      Nonempty (V ≃ₗ[A] W) := by
    intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h f hf
    obtain ⟨P, Q, S, ⟨e₁⟩, ⟨e₂⟩, hP, hQ⟩ := split_of_hom (k := k) f hf
    haveI := finiteDimensional_sub (k := k) P
    haveI := finiteDimensional_sub (k := k) Q
    haveI := finiteDimensional_sub (k := k) S
    obtain ⟨e⟩ := ih (finrank k P + finrank k Q) (by omega) P Q le_rfl fun a => by
      have := h a
      rw [tr_congr e₁, tr_congr e₂, tr_prod, tr_prod] at this
      exact add_right_cancel this
    exact ⟨e₁.trans ((e.prodCongr (LinearEquiv.refl A _)).trans e₂.symm)⟩
  intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h
  by_cases h₁ : ∀ f : V →ₗ[A] W, f = 0
  · by_cases h₂ : ∀ f : W →ₗ[A] V, f = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom h h₁ h₂)
      haveI : Subsingleton W :=
        Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom (fun a => (h a).symm) h₂ h₁)
      exact ⟨LinearEquiv.ofSubsingleton V W⟩
    · push_neg at h₂
      obtain ⟨f, hf⟩ := h₂
      obtain ⟨e⟩ := step W V (by omega) (fun a => (h a).symm) f hf
      exact ⟨e.symm⟩
  · push_neg at h₁
    obtain ⟨f, hf⟩ := h₁
    exact step V W hn h f hf

theorem exists_equiv_of_trace_eq [CharZero k] {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) (hρ : ρ.IsSemisimpleRepresentation)
    (hσ : σ.IsSemisimpleRepresentation)
    (h : ∀ g, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1 hρ
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 hσ
  have key : ∀ a : MonoidAlgebra k Γ, tr k ρ.asModule a = tr k σ.asModule a := by
    intro a
    unfold tr
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      have e₁ : LinearMap.trace k _ (Algebra.lsmul k k ρ.asModule (MonoidAlgebra.of k Γ g)) =
          LinearMap.trace k V (ρ g) := by
        rw [← LinearMap.trace_conj' (ρ g) ρ.asModuleEquiv.symm]
        congr 1
        ext v
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
        rfl
      have e₂ : LinearMap.trace k _ (Algebra.lsmul k k σ.asModule (MonoidAlgebra.of k Γ g)) =
          LinearMap.trace k W (σ g) := by
        rw [← LinearMap.trace_conj' (σ g) σ.asModuleEquiv.symm]
        congr 1
        ext v
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
        rfl
      rw [e₁, e₂, h]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | smul c a ha => simp only [map_smul, ha]
  obtain ⟨e⟩ := nonempty_linear_equiv_of_charpoly_eq (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule σ.asModule le_rfl key
  refine ⟨ρ.asModuleEquiv.symm.trans ((e.restrictScalars k).trans σ.asModuleEquiv), fun g v => ?_⟩
  change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
    σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul]
  simp

end GlobalTheory.TraceIso

end
end

section

open NumberField

namespace GlobalTheory

theorem span_image_span_eq_of_integral (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O]
    (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V']
    [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V')
    (he : ∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) (S : Set V) :
    Submodule.span O (iV '' (Submodule.span (𝓞 K) S : Set V)) = Submodule.span O (iV '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨z, hz⟩ := he a
      have h1 : a • x = ((a : K)) • x := (algebraMap_smul K a x).symm
      rw [h1, LinearMap.map_smulₛₗ, ← hz, algebraMap_smul]
      exact Submodule.smul_mem _ z hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

end GlobalTheory
end
