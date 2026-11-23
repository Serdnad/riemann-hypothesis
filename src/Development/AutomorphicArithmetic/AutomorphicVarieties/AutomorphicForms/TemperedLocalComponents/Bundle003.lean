module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RInv2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RChar2

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial Formalism.L2.Host Neutral.B1
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
open scoped Matrix

section Hecke

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem isOpen_ker_kills {M : ℕ} (hM : 1 ≤ M) {φ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    IsOpen (φ.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := F) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

private theorem exists_hchar_fin {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    {M : ℕ} (hM : 1 ≤ M) {φ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    ∃ χ : HChar F, IsAlgPos χ 0 ∧ IsLAdicOf art ι χ 0 φ := by
  have ho := isOpen_ker_kills hM hφ
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfi : Finite (_root_.Formalism.ConjugateSelfDual.G F Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, h2⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι φ (continuous_of_isOpen_ker' φ ho) hpos
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact φ.ker.pow_index_mem s)
  exact ⟨χ, isAlgPos_zero_of_orderDvd hpos h1, h2⟩

private theorem isAlgPos_mul {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem isAlgPos_inv {χ : HChar F} {n : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

private theorem exists_hchar_cyc {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) (j : ℤ) :
    ∃ (χ : HChar F) (n : (F →+* ℂ) → ℤ), IsAlgPos χ n ∧ IsLAdicOf art ι χ n (cycBar F Ω l ^ j) := by
  have key : ∀ m : ℕ, ∃ (χ : HChar F) (n : (F →+* ℂ) → ℤ), IsAlgPos χ n ∧ IsLAdicOf art ι χ n (cycBar F Ω l ^ m) := fun m => by
    have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F m
    obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
    have e : μ = cycBar F Ω l ^ m := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
    exact ⟨_, _, h, e ▸ hL⟩
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · simpa using key m
  · obtain ⟨χ, n, h1, h2⟩ := key m
    exact ⟨_, _, isAlgPos_inv h1, by simpa using h2.inv⟩

private theorem exists_hchar {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) {wt : ℤ}
    {θ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ} (hθ : IsCycWt l wt θ) (j : ℤ) :
    ∃ (χ : HChar F) (n : (F →+* ℂ) → ℤ), IsAlgPos χ n ∧ IsLAdicOf art ι χ n (θ * cycBar F Ω l ^ j) := by
  obtain ⟨M, φ, hM, hφ, rfl⟩ := hθ
  obtain ⟨χ, h1, h2⟩ := exists_hchar_fin ha ι hM hφ
  obtain ⟨χ', n, h3, h4⟩ := exists_hchar_cyc ha ι (wt + j)
  refine ⟨_, _, isAlgPos_mul h1 h3, ?_⟩
  have e : cycBar F Ω l ^ wt * φ * cycBar F Ω l ^ j = φ * cycBar F Ω l ^ (wt + j) := by
    rw [zpow_add, mul_comm _ φ, mul_assoc]
  exact e ▸ h2.mul h4

end Hecke

private theorem roots_stable {k : Type} [Field k] {n : ℕ} (f : k →+* ℂ) (M P : GL (Fin n) k) (t : kˣ)
    (h : (M : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (M : Matrix (Fin n) (Fin n) k) =
      (t : k) • (P : Matrix (Fin n) (Fin n) k)) (B : Multiset ℂ)
    (hB : (M : Matrix (Fin n) (Fin n) k).charpoly.map f = (B.map fun b => X - C b).prod) :
    B.map (fun b => f t * b⁻¹) = B := by
  set N : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) k).map f with hN
  set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) k).map f with hQ
  have hdet : ∀ U : GL (Fin n) k, ((U : Matrix (Fin n) (Fin n) k).map f).det ≠ 0 := fun U => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero f).2 (Matrix.GeneralLinearGroup.det U).ne_zero
  have h' : Nᵀ * Q * N = f t • Q := by
    have := congrArg (fun Z : Matrix (Fin n) (Fin n) k => Z.map f) h
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [this]
    ext i j
    simp [hQ]
  rw [← Matrix.charpoly_map, ← hN] at hB
  have hc : B.card = n := by
    have := congrArg natDegree hB
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have ev : ∀ x : ℂ, (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N).det = (B.map fun b => x - b).prod := fun x => by
    have := congrArg (eval x) hB
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at this
    simpa [Matrix.smul_one_eq_diagonal] using this
  have e0 : N.det = B.prod := by
    have := ev 0
    simp only [zero_smul, zero_sub, Matrix.det_neg, Fintype.card_fin] at this
    rw [Multiset.prod_map_neg, hc] at this
    exact mul_left_cancel₀ (pow_ne_zero _ (by simp)) this
  have hb : ∀ b ∈ B, b ≠ 0 := fun b hb h0 => hdet M (e0.trans (Multiset.prod_eq_zero (h0 ▸ hb)))
  have key : ∀ x : ℂ, x ≠ 0 → ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod = (B.map fun b => x - b).prod := by
    intro x hx
    have e1 : Nᵀ * Q * (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N) =
        (-x) • (((f t / x) • (1 : Matrix (Fin n) (Fin n) ℂ) - N)ᵀ * Q) := by
      rw [mul_sub, h', Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, sub_mul, smul_sub,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one, one_mul, neg_mul, mul_div_cancel₀ _ hx, neg_smul, neg_smul]
      abel
    have e2 := congrArg Matrix.det e1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
      ev, ev, e0, Fintype.card_fin] at e2
    have e3 : B.prod * ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod =
        (-x) ^ n * (B.map fun b => f t / x - b).prod := by
      rw [← hc, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul, Multiset.map_map]
      conv_lhs => rw [← Multiset.map_id' B, Multiset.map_map, ← Multiset.prod_map_mul]
      refine congrArg _ (Multiset.map_congr rfl fun b h => ?_)
      have := hb b h
      simp only [Function.comp_apply]
      field_simp
      ring
    refine mul_left_cancel₀ (mul_ne_zero (e0 ▸ hdet M) (hdet P)) ?_
    rw [← hQ]
    linear_combination Q.det * e3 - e2
  have hp : ((B.map fun b => f t * b⁻¹).map fun b => X - C b).prod = (B.map fun b => X - C b).prod := by
    refine eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun x hx => ?_)
    have := key x hx
    simpa [eval_multiset_prod, Multiset.map_map] using this
  have := congrArg roots hp
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at this

private theorem sat_stable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)} {θ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ}
    (hr : DualTw r θ) {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) {χ : HChar F} {a : (F →+* ℂ) → ℤ}
    (hχ : IsLAdicOf art ι χ a (θ * cycBar F Ω l ^ ((n : ℤ) - 1))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (hu : χ.UnrAt w) {B : Multiset ℂˣ}
    (hB : FrobEig ι r w (algSat n (normV w) B)) : (B.map (·⁻¹)).map (· * χ.val w) = B := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  obtain ⟨P, hP⟩ := hr
  have h1 := roots_stable ι.toRingHom _ P _ (hP σ⁻¹) _ ((hB A hA).2 σ hσ)
  have h2 := hχ.frob_unr ha (Or.inl hw) hu hA hσ
  have h3 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
    rw [cycBar, MonoidHom.comp_apply, Units.coe_map, cycZ_of_isFrob hw hA hσ]
    simp
  have hq : (0 : ℝ) < normV w := by
    have : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
    have h : 0 < normV w := by
      have : 1 < normV w := by
        simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
      exact zero_lt_one.trans this
    exact_mod_cast h
  set c : ℂ := (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  have hcc : c * c = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hc, ← Complex.ofReal_mul, ← Real.rpow_add hq, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; rfl, Real.rpow_intCast]
    simp
  have h4 : ι ((θ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c * c * (χ.val w : ℂˣ) := by
    have h5 := congrArg ι h2
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, h3, map_mul, map_zpow₀,
      map_natCast, map_inv₀, ι.apply_symm_apply, ← hcc] at h5
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, h5, inv_mul_cancel₀ (Units.ne_zero _)]
  refine Multiset.map_injective (f := fun α : ℂˣ => c * (α : ℂ))
    (fun x y e => Units.ext (mul_left_cancel₀ hc0 e)) ?_
  have h6 : algSat n (normV w) B = B.map fun α : ℂˣ => c * (α : ℂ) := by
    change Multiset.map _ (B.bind fun a : ℂˣ => ({(a : ℂ)} : Multiset ℂ)) = _
    rw [Multiset.bind_singleton, Multiset.map_map]
    rfl
  rw [h6] at h1
  refine Eq.trans ?_ h1
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  change c * _ = ι _ * (c * _)⁻¹
  rw [h4]
  simp only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

private theorem hasSat_invT {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} {π π' : TR.CuspSub F a}
    (h : IsInvTOf π π') {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    π'.HasSat w (B.map (·⁻¹)) := by
  obtain ⟨e, he, -⟩ := h
  refine InvT.hasSatGL_invT e (fun g x => ?_) hB
  rw [TR.CuspSub.locRep_eq, TR.CuspSub.locRep_eq, he, InvT.locGL_invT]

private theorem isTwistOf_twist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} (π : TR.CuspSub F a)
    (χ : HChar F) : IsTwistOf π χ (π.twist χ) := by
  refine ⟨π.toTwist χ, (TR.dchi χ).toLinearMap, fun z u hu => ?_, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  · have e : u = TR.expU z := Units.ext (funext hu)
    rw [e]
    exact TR.chiInf_expU χ z
  all_goals simp [TR.CuspSub.op_toTwist, TR.opMul, TR.opAdd]
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Filter Topology Matrix

namespace UpperTheory.V.Af.GlobalFixedVectors

theorem sub_fixed {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤)
    (W : Submodule ℂ V) (hW : ∀ g, ∀ v ∈ W, τ g v ∈ W) (h0 : W ≠ ⊥) (K : Subgroup Γ) (hK : HasFixed σ K) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ u ∈ K, τ u v = v :=
  _root_.UpperTheory.Reformulated.B.SubgroupFixed.sub_fixed σ hσ τ h W hW h0 K hK

variable {F : Type} [Field F] [NumberField F] {n M : ℕ}

theorem mem_Ohat {x : Af F} : x ∈ Ohat F ↔ ∀ w : HeightOneSpectrum (𝓞 F), pLoc F w x ∈ w.adicCompletionIntegers F := by
  simp [Ohat, Subring.mem_iInf]

theorem gl_ext {g h : GL (Fin n) (Af F)}
    (e : ∀ w, GeneralLinearGroup.map (pLoc F w) g = GeneralLinearGroup.map (pLoc F w) h) : g = h := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin n) (w.adicCompletion F) => x i j) (e w)

theorem pLoc_sLoc (w : HeightOneSpectrum (𝓞 F)) (x : w.adicCompletion F) : pLoc F w (sLoc F w x) = x := by
  classical
  exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w x

theorem pLoc_sLoc_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : w.adicCompletion F) : pLoc F v (sLoc F w x) = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) h x

theorem sLoc_mem (w : HeightOneSpectrum (𝓞 F)) {x : Af F} (hx : x ∈ Ohat F) : sLoc F w (pLoc F w x) ∈ Ohat F :=
  mem_Ohat.2 fun v => by
    by_cases h : v = w
    · subst h; rw [pLoc_sLoc]; exact mem_Ohat.1 hx v
    · rw [pLoc_sLoc_of_ne h]; exact zero_mem _

noncomputable def eLoc (w : HeightOneSpectrum (𝓞 F)) : Ohat F →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w (pLoc F w x), sLoc_mem w x.2⟩
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem eLoc_eq (w : HeightOneSpectrum (𝓞 F)) (x : Ohat F) : eLoc w x = eLoc w 1 * x := by
  refine Subtype.ext (FiniteAdeleRing.ext _ fun v => ?_)
  change pLoc F v (sLoc F w (pLoc F w x)) = pLoc F v (sLoc F w (pLoc F w (1 : Ohat F)) * x)
  rw [map_mul]
  by_cases h : v = w
  · subst h; simp [pLoc_sLoc]
  · simp [pLoc_sLoc_of_ne h]

theorem loc_mem (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (Af F)} (hk : k ∈ KLev F n M) :
    GeneralLinearGroup.map (pLoc F w) k ∈ KLoc F w n M := by
  obtain ⟨g, hg, rfl⟩ := hk
  refine ⟨cornerGL n (eLoc w) g, ?_, ?_⟩
  · ext i j
    have h1 := congrArg (fun x : GL (Fin n) (Ohat F ⧸ Ideal.span {(M : ↥(Ohat F))}) => x i j) (MonoidHom.mem_ker.1 hg)
    change Ideal.Quotient.mk _ (g i j) = (1 : Matrix (Fin n) (Fin n) _) i j at h1
    change Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j -
      eLoc w ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j) + eLoc w (g i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [eLoc_eq w (g i j), eLoc_eq w (_ : Ohat F)]
    simp [h1, Matrix.one_apply, apply_ite (Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat F))}))]
  · ext i j : 2
    change ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j : Af F) -
      sLoc F w (pLoc F w ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j : Ohat F)) + sLoc F w (pLoc F w (g i j)) =
      (1 : Matrix (Fin n) (Fin n) (Af F)) i j - sLoc F w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion F)) i j) +
        sLoc F w (pLoc F w (g i j))
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem tendsto_of_loc {α : Type} {𝓕 : Filter α} {f : α → Af F} {x : Af F} (hx : x ∈ Ohat F) (hf : ∀ᶠ a in 𝓕, f a ∈ Ohat F)
    (h : ∀ w, ∀ᶠ a in 𝓕, pLoc F w (f a) = pLoc F w x) : Tendsto f 𝓕 (𝓝 x) := by
  classical
  let s := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  let lift : Af F → ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun y v => if h : y ∈ Ohat F then ⟨pLoc F v y, mem_Ohat.1 h v⟩ else ⟨0, zero_mem _⟩
  have hl : ∀ y ∈ Ohat F, s (lift y) = y := fun y hy => FiniteAdeleRing.ext _ fun v => by
    change ((lift y v : _) : v.adicCompletion F) = pLoc F v y
    simp [lift, hy]
  have h1 : Tendsto (fun a => lift (f a)) 𝓕 (𝓝 (lift x)) := tendsto_pi_nhds.2 fun v =>
    tendsto_const_nhds.congr' <| by
      filter_upwards [hf, h v] with a ha hav
      simp [lift, ha, hx, hav]
  have h2 := (hs.tendsto _).comp h1
  rw [hl x hx] at h2
  exact h2.congr' (hf.mono fun a ha => hl _ ha)

theorem entry_mem {k : GL (Fin n) (Af F)} (hk : k ∈ KLev F n M) (i j : Fin n) : k i j ∈ Ohat F := by
  obtain ⟨g, -, rfl⟩ := hk
  exact (g i j).2


variable (n M) in
noncomputable def KAway (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GL (Fin n) (Af F)) :=
  KLev F n M ⊓ ⨅ w ∈ S, (GeneralLinearGroup.map (pLoc F w)).ker

theorem mem_KAway {S : Finset (HeightOneSpectrum (𝓞 F))} {k : GL (Fin n) (Af F)} :
    k ∈ KAway n M S ↔ k ∈ KLev F n M ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc F w) k = 1 := by
  simp [KAway, Subgroup.mem_iInf]

theorem exists_KAway_subset {U : Set (GL (Fin n) (Af F))} (hU : U ∈ 𝓝 (1 : GL (Fin n) (Af F))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (KAway n M S : Set (GL (Fin n) (Af F))) ⊆ U := by
  classical
  by_contra hn
  push Not at hn
  choose k hk hkU using fun S => Set.not_subset.1 (hn S)
  have ent : ∀ k : Finset (HeightOneSpectrum (𝓞 F)) → GL (Fin n) (Af F), (∀ S, k S ∈ KAway n M S) →
      Tendsto (fun S => (k S).val) atTop (𝓝 1) := fun k hk =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_of_loc (entry_mem (one_mem (KLev F n M)) i j) (.of_forall fun S => entry_mem (mem_KAway.1 (hk S)).1 i j) fun w => by
        filter_upwards [eventually_ge_atTop {w}] with S hS
        have e := (mem_KAway.1 (hk S)).2 w (hS (Finset.mem_singleton_self w))
        rw [← map_one (GeneralLinearGroup.map (pLoc F w))] at e
        exact congrArg (fun x : GL (Fin n) (w.adicCompletion F) => x i j) e
  have ht : Tendsto k atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact (ent k hk).prodMk_nhds
      ((MulOpposite.continuous_op.tendsto _).comp (ent (fun S => (k S)⁻¹) fun S => inv_mem (hk S)))
  obtain ⟨S, hS⟩ := (ht.eventually hU).exists
  exact hkU S hS

end UpperTheory.V.Af.GlobalFixedVectors

end
