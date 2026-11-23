module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMemOfSpanBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90TensorPadicUnramifiedExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousOperatorLinear
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import GroundTheory.Brauer.SkolemNoether
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F), (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).IsHermitian ∧ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).det ≠ 0 ∧ (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ = ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.LKMid.pair_form_laws) | (exact GlobalTheory.LKMid.pair_form_laws) | (intros; apply GlobalTheory.LKMid.pair_form_laws  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧ Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range := by
  first | (exact @GlobalTheory.LKMid.SigIter.main) | (exact GlobalTheory.LKMid.SigIter.main) | (intros; apply GlobalTheory.LKMid.SigIter.main  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem conj_rel_alg' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β e e' : G.Cˣ) (a' : G.C) (r r' : ℚˣ) :
    algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) =
      algebraMap ℚ G.C ((r : ℚ) / r') * (((e * e'⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (r' : ℚ) *
        ((e' : G.C) * a' * ((β : G.C) * sh G (e' : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))) *
        ((β : G.C) * sh G ((e * e'⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  have hsh : sh G ((e * e'⁻¹ : G.Cˣ) : G.C) = sh G ((e'⁻¹ : G.Cˣ) : G.C) * sh G (e : G.C) := by
    simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
  have h1 : sh G (e' : G.C) * sh G ((e'⁻¹ : G.Cˣ) : G.C) = 1 := by
    simp only [sh]
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hrr : (r' : ℚ) * ((r : ℚ) / r') = r := by field_simp
  have key2 : ((e : G.C) * ((e'⁻¹ : G.Cˣ) : G.C)) * ((e' : G.C) * a' * ((β : G.C) * sh G (e' : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) *
      ((β : G.C) * (sh G ((e'⁻¹ : G.Cˣ) : G.C) * sh G (e : G.C)) * ((β⁻¹ : G.Cˣ) : G.C)) =
      (e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
    simp only [mul_assoc]
    rw [Units.inv_mul_cancel_left, Units.inv_mul_cancel_left, ← mul_assoc (sh G (e' : G.C)), h1, one_mul]
  rw [hsh, Units.val_mul]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, hrr]
  rw [key2]

theorem commute_of_commute_of_separable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (y₀ : G.C)
    (hsep : (minpoly G.F y₀).Separable) (hdeg : (minpoly G.F y₀).natDegree = G.n) (a b : G.C)
    (ha : Commute a y₀) (hb : Commute b y₀) : Commute a b := by
  have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y₀ hsep hdeg
  have hamem : a ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact ha.eq.symm
  have hbmem : b ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hb.eq.symm
  rw [hc] at hamem
  have h2 := Algebra.adjoin_le_centralizer_centralizer G.F ({y₀} : Set G.C) hamem
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact (h2 b hbmem).symm

theorem units_conj_of_minpoly_eq_of_separable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (a b : G.Cˣ)
    (hab : minpoly G.F (a : G.C) = minpoly G.F (b : G.C)) (hsep : (minpoly G.F (b : G.C)).Separable)
    (hdeg : (minpoly G.F (b : G.C)).natDegree = G.n) : ∃ g : G.Cˣ, (a : G.C) = g * b * ↑g⁻¹ := by
  haveI : Infinite G.F := Infinite.of_injective (Nat.cast : ℕ → G.F) Nat.cast_injective
  obtain ⟨g, hg⟩ := GlobalTheory.LKInv.exists_unit_conj_of_minpoly_eq G.F G.C G.n G.rankC (b : G.C) (a : G.C) hsep hdeg hab
  refine ⟨g, ?_⟩
  rw [hg, mul_assoc, Units.mul_inv, mul_one]

end GlobalTheory.LKCx.ClsReg
end
end

section

open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

namespace GlobalTheory.LKMid

theorem twistedNormProductIterate_map_intertwining {H H' : Type} [Group H] [Group H'] (θ : H →* H) (θ' : H' →* H') (f : H →* H')
    (hf : ∀ x, f (θ x) = θ' (f x)) (r : ℕ) (x : H) : f (nrmG θ r x) = nrmG θ' r (f x) := by
  unfold nrmG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (Function.Semiconj.iterate_right (f := f) (ga := θ) (gb := θ') hf i) x

theorem twistedNormProductIterate_mul_commGroup {H : Type} [CommGroup H] (θ : H →* H) (r : ℕ) (a b : H) :
    nrmG θ r (a * b) = nrmG θ r a * nrmG θ r b := by
  unfold nrmG
  rw [← List.prod_map_mul]
  congr 1
  apply List.map_congr_left
  intro i hi
  clear hi
  induction i generalizing a b with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_mul, ih]

end GlobalTheory.LKMid

namespace GlobalTheory.LKMid

theorem det_unramifiedExtFrobeniusGLEntrywise_GL_one (p : ℕ) [Fact p.Prime] (r : ℕ) (x : GL (Fin 1) (Qr p r)) :
    Matrix.GeneralLinearGroup.det (GlobalTheory.LKLoc.sig p (Q0 p) 1 r x) =
      Units.map (frobQ p r).toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det x) := by
  ext
  simp [GlobalTheory.LKLoc.sig, Matrix.det_unique]
  rfl

theorem generalLinearGroup_det_injective_GL_one (R : Type) [CommRing R] :
    Function.Injective (Matrix.GeneralLinearGroup.det : GL (Fin 1) R →* Rˣ) := by
  intro x y h
  ext i j
  have := congrArg Units.val h
  simp [Matrix.det_unique] at this
  fin_cases i; fin_cases j
  exact this

theorem generalLinearGroup_det_scalar_GL_one (R : Type) [CommRing R] (u : Rˣ) :
    Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) u) = u := by
  ext
  simp [Matrix.det_unique]

theorem exists_sig_twisted_conj_of_nrmG_eq : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ δ' : GL (Fin 1) (Qr p r),
    nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ' →
    ∃ h : GL (Fin 1) (Qr p r), δ' = h⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r h := by
  intro p _ r hr δ δ' hN
  let D : GL (Fin 1) (Qr p r) →* (Qr p r)ˣ := Matrix.GeneralLinearGroup.det
  let θ : (Qr p r)ˣ →* (Qr p r)ˣ := Units.map (frobQ p r).toRingHom.toMonoidHom
  have hD : ∀ x, D (GlobalTheory.LKLoc.sig p (Q0 p) 1 r x) = θ (D x) := det_unramifiedExtFrobeniusGLEntrywise_GL_one p r
  have hN' : nrmG θ r (D δ) = nrmG θ r (D δ') := by
    rw [← twistedNormProductIterate_map_intertwining _ _ D hD, ← twistedNormProductIterate_map_intertwining _ _ D hD, hN]
  let c : (Qr p r)ˣ := D δ' * (D δ)⁻¹
  have hc : nrmG θ r c = 1 := by
    have h1 : nrmG θ r c * nrmG θ r (D δ) = nrmG θ r (D δ) := by
      rw [← twistedNormProductIterate_mul_commGroup, inv_mul_cancel_right, hN']
    exact mul_eq_right.1 h1
  let L := Algebra.TensorProduct.lid ℚ_[p] (Qr p r)
  let Φ := Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (frobQ p r)
  have hL : ∀ x, L (Φ x) = frobQ p r (L x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      simp only [L, Φ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, AlgHom.id_apply]
      exact ((frobQ p r).toLinearMap.map_smul b y).symm
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  have hLs : ∀ y, L.symm (frobQ p r y) = Φ (L.symm y) := by
    intro y
    apply L.injective
    rw [hL, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  let fS : (Qr p r)ˣ →* (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ := Units.map L.symm.toAlgHom.toRingHom.toMonoidHom
  let fL : (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ →* (Qr p r)ˣ := Units.map L.toAlgHom.toRingHom.toMonoidHom
  let ΦU : (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ →* (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ := Units.map Φ.toRingHom.toMonoidHom
  have hfS : ∀ x, fS (θ x) = ΦU (fS x) := fun x => Units.ext (hLs x)
  have hfL : ∀ x, fL (ΦU x) = θ (fL x) := fun x => Units.ext (hL x)
  have hLS : ∀ x, fL (fS x) = x := fun x => Units.ext (AlgEquiv.apply_symm_apply L x)
  have ha : nrmG ΦU r (fS c) = 1 := by
    rw [← twistedNormProductIterate_map_intertwining _ _ fS hfS, hc, map_one]
  obtain ⟨g, hg⟩ := hilbert90_frobenius_tensor_unramified_padic p r hr ℚ_[p] (fS c) ha
  have hc' : c = (fL g)⁻¹ * θ (fL g) := by
    rw [← hLS c, hg, map_mul, map_inv, hfL]
  refine ⟨GeneralLinearGroup.scalar (Fin 1) (fL g), generalLinearGroup_det_injective_GL_one _ ?_⟩
  have hs : D (GeneralLinearGroup.scalar (Fin 1) (fL g)) = fL g := generalLinearGroup_det_scalar_GL_one _ _
  have e : D δ' = c * D δ := by rw [inv_mul_cancel_right]
  change D δ' = D ((GeneralLinearGroup.scalar (Fin 1) (fL g))⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r (GeneralLinearGroup.scalar (Fin 1) (fL g)))
  rw [map_mul, map_mul, map_inv, hD, hs, e, hc']
  exact mul_right_comm _ _ _

end GlobalTheory.LKMid
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_unit_of_frobenius_norm_one_tensor_Qr : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ (B : Type) [CommRing B] [Algebra ℚ_[p] B] [Module.Finite ℚ_[p] B] (a : (B ⊗[ℚ_[p]] Qr p r)ˣ), nrmG (Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom) r a = 1 → ∃ g : (B ⊗[ℚ_[p]] Qr p r)ˣ, a = g⁻¹ * Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom g := by
  first | (exact @GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic) | (exact GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic) | (intros; apply GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.ColEval

theorem word_succ {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) {t : ℕ} (u : Fin (t + 1) → Fin N → K) :
    word mul u = mul (u 0) * word mul (fun i => u i.succ) := by
  simp [word, List.ofFn_succ]

theorem mul_eq_sum {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (v : Fin N → K) :
    mul v = ∑ k, v k • mul (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A]
  [IsScalarTower (𝓞 F) F A] {S : Sys F A} {E A' : Type} [Field E] [Algebra F E] [AddCommGroup A'] [Module E A']
  {s : Fin S.D → Fin S.N → E} {δ : ℕ}

theorem mul_single_ι (Φ : S.Flat E A' s δ) (k : Fin S.N) (y : A) :
    Φ.mul (Pi.single k 1) (Φ.ι y) = Φ.ι (S.mul (Pi.single k 1) y) := by
  rw [← Φ.mul_ι]
  congr 2
  ext j
  by_cases h : j = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem word_ι_expand (Φ : S.Flat E A' s δ) : ∀ (t : ℕ) (U : Fin t → Fin S.N → E) (z : A),
    word Φ.mul U (Φ.ι z) =
      ∑ e : Fin t → Fin S.N, (∏ q, U q (e q)) • Φ.ι (word S.mul (fun q => Pi.single (e q) (1 : F)) z)
  | 0, U, z => by simp [word]
  | t + 1, U, z => by

    rw [word_succ, Module.End.mul_apply, word_ι_expand Φ t, map_sum]
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) => Fin S.N).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, word_succ,
      Module.End.mul_apply, map_smul, mul_eq_sum Φ.mul (U 0), LinearMap.sum_apply, LinearMap.smul_apply,
      mul_single_ι, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => ?_
    rw [mul_comm]

end GlobalTheory.HSShort.ColEval

namespace GlobalTheory.HSShort.ColEval

theorem columns_eval : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∃ c' : Fin d → A' →ₗ[E] E, (∀ x ∈ Submodule.span E (Φ.ι '' S.V S.T), ∑ i, c' i x • Φ.ι (b i) = x) ∧ ∀ (κ : S.Col) (u : Fin (S.D + 1) × Fin S.N → E), word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x) ∈ Submodule.span E (Φ.ι '' S.V S.T) ∧ ∀ i, aeval u (coordP S.mul (c i) κ.β (κ.x : A)) = c' i (word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x)) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc
  set W := Submodule.span E (Φ.ι '' (S.V S.T : Set A)) with hW
  have hli : LinearIndependent E (fun i => Φ.ι (b i)) := Φ.indep d b b.linearIndependent
  have hιV : ∀ (y : A) (hy : y ∈ S.V S.T), Φ.ι y = ∑ i, algebraMap F E (b.repr ⟨y, hy⟩ i) • Φ.ι (b i) := by
    intro y hy
    conv_lhs => rw [show y = ((⟨y, hy⟩ : S.V S.T) : A) from rfl, ← b.sum_repr ⟨y, hy⟩]

    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, LinearMap.map_smulₛₗ]
  have hWspan : W = Submodule.span E (Set.range fun i => Φ.ι (b i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [hιV y hy]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨b i, (b i).2, rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Finsupp.linearEquivFunOnFinite E E (Fin d)).toLinearMap ∘ₗ (hli.repr ∘ₗ Submodule.inclusion (le_of_eq hWspan)))
  have h1 : ∀ x ∈ W, ∑ i, g x i • Φ.ι (b i) = x := by
    intro x hx
    have hx' : x ∈ Submodule.span E (Set.range fun i => Φ.ι (b i)) := hWspan ▸ hx
    have e1 := LinearMap.congr_fun hg ⟨x, hx⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe] at e1
    rw [e1, show Submodule.inclusion (le_of_eq hWspan) ⟨x, hx⟩ = ⟨x, hx'⟩ from rfl]
    have e2 := hli.linearCombination_repr ⟨x, hx'⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e2
    simpa using e2
  have h2 : ∀ x ∈ W, ∀ a : Fin d → E, ∑ i, a i • Φ.ι (b i) = x → ∀ i, g x i = a i := by
    intro x hx a ha
    have h0 : ∑ i, (g x i - a i) • Φ.ι (b i) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1 x hx, ha, sub_self]
    intro i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  have h3 : ∀ (y : A) (hy : y ∈ S.V S.T) i, g (Φ.ι y) i = algebraMap F E (c i y) := by
    intro y hy i
    rw [h2 _ (Submodule.subset_span ⟨y, hy, rfl⟩) _ (hιV y hy).symm i]
    congr 1
    exact (hc i ⟨y, hy⟩).symm
  refine ⟨fun i => LinearMap.proj i ∘ₗ g, fun x hx => h1 x hx, fun κ u => ?_⟩
  have hmem : ∀ e : Fin κ.t → Fin S.N, word S.mul (fun q => Pi.single (e q) (1 : F)) (κ.x : A) ∈ S.V S.T := by
    intro e
    have := (GlobalTheory.HSShort.wordMem F A S hS κ.j κ.t (by rw [κ.add])).1 (fun q => Pi.single (e q) (1 : F)) κ.x κ.x.2
    rwa [κ.add] at this
  rw [word_ι_expand Φ κ.t]
  refine ⟨Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem e, rfl⟩), fun i => ?_⟩

  simp only [coordP, map_sum, map_mul, aeval_C, map_prod, aeval_X, LinearMap.coe_comp, Function.comp_apply,
  LinearMap.map_smul, LinearMap.coe_proj, Function.eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [h3 _ (hmem e) i, mul_comm]

end GlobalTheory.HSShort.ColEval
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.symbols_of_evaluated_columns_hermitianMultSystem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → ∀ l : Fin S.N → E, (∀ (a : Fin (S.T - S.D)) (α : MonoDeg (Fin S.D) a) (p : Fin δ), ∃ h : word Φ.mul (fun q k => join s l ((col (ix (⟨a, α⟩, p))).β q, k)) (Φ.ι (col (ix (⟨a, α⟩, p))).x) ∈ Φ.U a, ∀ α' p', Φ.sym a ⟨_, h⟩ (α', p') = if α'.1 = α.1 then (∑ k, l k * Φ.y p' k) ^ (S.T - a) * Φ.res (Φ.ι (m p)) p' else 0) ∧ ∀ k, k ∉ Set.range ix → (col k).j = S.D → word Φ.mul (fun q j => join s l ((col k).β q, j)) (Φ.ι (col k).x) ∈ Φ.U (S.T - S.D) := by
  first | exact @GlobalTheory.HSShort.symbols_of_columns | exact GlobalTheory.HSShort.symbols_of_columns | (intros; apply GlobalTheory.HSShort.symbols_of_columns <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.additive_homogeneous_operator_linear : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (ψ : AddChar K ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ (n m : ℕ) (A : (Matrix (Fin n) (Fin m) K → ℂ) → Matrix (Fin n) (Fin m) K → ℂ),
    (∀ f ∈ SB (Matrix (Fin n) (Fin m) K), ∀ f' ∈ SB (Matrix (Fin n) (Fin m) K), A (f + f') = A f + A f') →
    (∀ (c : ℂ), ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A (c • f) = c • A f) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => f (Y + Z)) = fun Y => A f (Y + Z)) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * f Y) = fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * A f Y) →
    ∃ c : ℂ, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A f = c • f := by
  first | exact @GlobalTheory.SchurLin.schur_linear_model | exact GlobalTheory.SchurLin.schur_linear_model | (intros; apply GlobalTheory.SchurLin.schur_linear_model <;> assumption)
end

section

open MeasureTheory Matrix


theorem _root_.GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (μ : @Measure (κ → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ),
      ∫ y, GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ := by
  first | exact @GlobalTheory.schr_unitary | exact GlobalTheory.schr_unitary | (intros; apply GlobalTheory.schr_unitary <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.adelic_schwartz_mem_L2 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
    ∀ μ : MeasureTheory.Measure (κ → AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, MeasureTheory.MemLp Φ 2 μ := by
  first | exact @GlobalTheory.WeilM.schA_memLp_two | exact GlobalTheory.WeilM.schA_memLp_two | (intros; apply GlobalTheory.WeilM.schA_memLp_two <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem units_conj_of_minpoly_eq_of_irreducible : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (a b : G.Cˣ),
    minpoly G.F (a : G.C) = minpoly G.F (b : G.C) → Irreducible (minpoly G.F (b : G.C)) →
      ∃ g : G.Cˣ, (a : G.C) = g * b * ↑g⁻¹ := by
  intro p _ G a b h hirr
  have hb : IsIntegral G.F (b : G.C) := IsIntegral.of_finite G.F _
  haveI : Fact (Irreducible (minpoly G.F (b : G.C))) := ⟨hirr⟩
  haveI : FiniteDimensional G.F (AdjoinRoot (minpoly G.F (b : G.C))) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero hb)).finite
  have ha : Polynomial.aeval (a : G.C) (minpoly G.F (b : G.C)) = 0 := by rw [← h]; exact minpoly.aeval _ _
  obtain ⟨y, hy⟩ := GroundTheory.Brauer.exists_unit_conj (evalQuot _ (b : G.C) (minpoly.aeval _ _))
    (evalQuot _ (a : G.C) ha)
  refine ⟨y, ?_⟩
  have := hy (AdjoinRoot.root _)
  rwa [evalQuot_root, evalQuot_root] at this

end GlobalTheory.LKCx
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.exists_hasNonzeroSec_pow_of_ample_sub_ample' : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsAmpleLB B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  first | exact @GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample | exact GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample | (intros; apply GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample <;> assumption)
end
