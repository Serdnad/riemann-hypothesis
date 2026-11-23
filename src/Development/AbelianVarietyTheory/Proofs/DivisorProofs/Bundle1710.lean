module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1576
import Mathlib.Algebra.Lie.OfAssociative
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle164
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableFockVacuumGaussianDefinitePair
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle240
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046

@[expose] public section

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.NrmUnique

theorem phi_surj_commutant : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < r → γ.charpoly.Separable → ∀ X : Matrix (Fin n) (Fin n) (KQ p K r), Commute X (γ.map (inclK p K r)) → ∃ x, GlobalTheory.PolyTensor.phi p K n γ r x = X := GlobalTheory.T.exists_matrixAdjoinTensorUnramified_of_commute_separable

theorem phi_injective : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < r → Function.Injective (GlobalTheory.PolyTensor.phi p K n γ r) := GlobalTheory.T.matrixAdjoinTensorUnramifiedToMatrix_injective

theorem hilbert_ninety_gl1 : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ δ' : GL (Fin 1) (Qr p r), nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ' → ∃ h : GL (Fin 1) (Qr p r), δ' = h⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r h := GlobalTheory.T.twisted_conj_of_twistedNorm_eq_GL_one_unramified

theorem map_nrmG {H H' : Type} [Group H] [Group H'] (θ : H →* H) (θ' : H' →* H') (f : H →* H')
    (hf : ∀ x, f (θ x) = θ' (f x)) (r : ℕ) (a : H) : f (nrmG θ r a) = nrmG θ' r (f a) := by
  unfold nrmG
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact Function.Semiconj.iterate_right (f := f) hf i a

theorem nrmG_mul {H : Type} [CommGroup H] (θ : H →* H) (r : ℕ) (a b : H) :
    nrmG θ r (a * b) = nrmG θ r a * nrmG θ r b := by
  unfold nrmG
  rw [← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact iterate_map_mul θ i a b

theorem nrmG_inv {H : Type} [CommGroup H] (θ : H →* H) (r : ℕ) (a : H) :
    nrmG θ r a⁻¹ = (nrmG θ r a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← nrmG_mul, inv_mul_cancel]
  simp [nrmG, iterate_map_one]

theorem gl_one_mul_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem twConj_place (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 0 < r) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (n : ℕ) (γ : GL (Fin n) K) (hγ : γ.val.charpoly.Separable)
    (δ δ' : GL (Fin n) (KQ p K r))
    (hc : Commute δ.val (γ.val.map (inclK p K r))) (hc' : Commute δ'.val (γ.val.map (inclK p K r)))
    (hN : nrmG (sigRes p K n r) r δ = nrmG (sigRes p K n r) r δ') :
    ∃ h : GL (Fin n) (KQ p K r), δ' = h⁻¹ * δ * sigRes p K n r h ∧
      ∀ y : GL (Fin n) K, Commute y.val γ.val → Commute h.val (y.val.map (inclK p K r)) := by
  have hinj := phi_injective p K n r γ.val hr
  have lift : ∀ d : GL (Fin n) (KQ p K r), Commute d.val (γ.val.map (inclK p K r)) →
      ∃ u : (GlobalTheory.PolyTensor.PolyAlg p K n γ.val ⊗[ℚ_[p]] Qr p r)ˣ,
        GlobalTheory.PolyTensor.phi p K n γ.val r u = d.val := by
    intro d hd
    obtain ⟨x, hx⟩ := phi_surj_commutant p K n r γ.val hr hγ d.val hd
    obtain ⟨x', hx'⟩ := phi_surj_commutant p K n r γ.val hr hγ (d⁻¹).val (Commute.units_inv_left hd)
    have h1 : x * x' = 1 := hinj (by rw [map_mul, map_one, hx, hx']; exact d.mul_inv)
    exact ⟨⟨x, x', h1, by rw [mul_comm]; exact h1⟩, hx⟩
  obtain ⟨u, hu⟩ := lift δ hc
  obtain ⟨u', hu'⟩ := lift δ' hc'
  let Φ : (GlobalTheory.PolyTensor.PolyAlg p K n γ.val ⊗[ℚ_[p]] Qr p r)ˣ →* GL (Fin n) (KQ p K r) :=
    Units.map (GlobalTheory.PolyTensor.phi p K n γ.val r).toMonoidHom
  let τ : (GlobalTheory.PolyTensor.PolyAlg p K n γ.val ⊗[ℚ_[p]] Qr p r)ˣ →* (GlobalTheory.PolyTensor.PolyAlg p K n γ.val ⊗[ℚ_[p]] Qr p r)ˣ :=
    Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] (GlobalTheory.PolyTensor.PolyAlg p K n γ.val)) (frobQ p r)).toRingHom.toMonoidHom
  have hΦ : ∀ a, Φ (τ a) = sigRes p K n r (Φ a) := fun a =>
    Units.ext (GlobalTheory.PolyTensor.phi_tw p K n γ.val r a)
  have hΦinj : Function.Injective Φ := fun a b h => Units.ext (hinj (congrArg Units.val h))
  have hδ : Φ u = δ := Units.ext hu
  have hδ' : Φ u' = δ' := Units.ext hu'
  have hNu : nrmG τ r u = nrmG τ r u' :=
    hΦinj (by rw [map_nrmG τ _ Φ hΦ, map_nrmG τ _ Φ hΦ, hδ, hδ', hN])
  have hn1 : nrmG τ r (u' * u⁻¹) = 1 := by rw [nrmG_mul, nrmG_inv, hNu, mul_inv_cancel]
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unit_of_frobenius_norm_one_tensor_Qr p r hr (GlobalTheory.PolyTensor.PolyAlg p K n γ.val) (u' * u⁻¹) hn1
  have hu'g : u' = g⁻¹ * u * τ g := by
    calc u' = (u' * u⁻¹) * u := by group
      _ = g⁻¹ * τ g * u := by rw [hg]
      _ = g⁻¹ * u * τ g := by rw [mul_assoc, mul_comm (τ g) u, ← mul_assoc]
  refine ⟨Φ g, ?_, fun y hy => ?_⟩
  · rw [← hδ', ← hδ, hu'g, map_mul, map_mul, map_inv, hΦ]
  · exact (GlobalTheory.PolyTensor.phi_commute p K n γ.val r y.val hy (g : _)).symm

theorem nrm_unique : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z δ' z' : Gr G r), 0 < r →
    regular₂ G γ → IsNrm G r γ δ z → IsNrm G r γ δ' z' → ∃ g : Gr G r, δ' = g⁻¹ * δ * sigG G r g ∧
      ∀ y ∈ Subgroup.centralizer {γ}, carry G r z' y = g⁻¹ * carry G r z y * g := by
  intro p _ G r γ δ z δ' z' hr hreg h h'
  obtain ⟨hex, -⟩ := GlobalTheory.T.twistedNormConj_normalize_and_degree_one p G
  obtain ⟨hit, hfix, -, -⟩ := GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points p G r hr
  set d := z * δ * (sigG G r z)⁻¹ with hd
  set d' := z' * δ' * (sigG G r z')⁻¹ with hd'
  have hN : nrmG (sigG G r) r d = inclG G r γ := by
    have := hex r γ δ z hr h
    simpa [IsNrm] using this
  have hN' : nrmG (sigG G r) r d' = inclG G r γ := by
    have := hex r γ δ' z' hr h'
    simpa [IsNrm] using this
  have comm : ∀ e, nrmG (sigG G r) r e = inclG G r γ → e * inclG G r γ = inclG G r γ * e := by
    intro e he
    have := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r e 1).2
    rw [he, hfix, hit] at this
    exact this
  have hc := comm d hN
  have hc' := comm d' hN'
  have key : ∀ (w : Fin G.m) (e : Gr G r),
      (nrmG (sigG G r) r e).2 w = nrmG (sigRes p (G.Fw w) G.n r) r (e.2 w) := fun w e =>
    map_nrmG (sigG G r) (sigRes p (G.Fw w) G.n r) ((Pi.evalMonoidHom _ w).comp (MonoidHom.snd _ _))
      (fun _ => rfl) r e
  have key1 : ∀ e : Gr G r, (nrmG (sigG G r) r e).1 = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r e.1 := fun e =>
    map_nrmG (sigG G r) (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) (MonoidHom.fst _ _) (fun _ => rfl) r e
  have hNw : ∀ w, nrmG (sigRes p (G.Fw w) G.n r) r (d.2 w) = nrmG (sigRes p (G.Fw w) G.n r) r (d'.2 w) :=
    fun w => by rw [← key, ← key, hN, hN']
  have hN1 : nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r d.1 = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r d'.1 := by
    rw [← key1, ← key1, hN, hN']
  have hcw : ∀ (e : Gr G r), e * inclG G r γ = inclG G r γ * e →
      ∀ w, Commute (e.2 w).val ((γ.2 w).val.map (inclK p (G.Fw w) r)) := by
    intro e he w
    have := congrArg (fun x : Gr G r => (x.2 w).val) he
    exact this
  choose H hH hHc using fun w => twConj_place p r hr (G.Fw w) G.n (γ.2 w) (hreg w) (d.2 w) (d'.2 w)
    (hcw d hc w) (hcw d' hc' w) (hNw w)
  obtain ⟨h0, hh0⟩ := hilbert_ninety_gl1 p r hr d.1 d'.1 hN1
  let hh : Gr G r := (h0, H)
  have hdd : d' = hh⁻¹ * d * sigG G r hh := Prod.ext hh0 (funext hH)
  have hcomm : ∀ y ∈ Subgroup.centralizer {γ}, hh * inclG G r y = inclG G r y * hh := by
    intro y hy
    have hy' : γ * y = y * γ := Subgroup.mem_centralizer_iff.1 hy γ rfl
    refine Prod.ext (gl_one_mul_comm _ _) (funext fun w => ?_)
    have hyw : Commute (y.2 w).val (γ.2 w).val := by
      have := congrArg (fun x : Gp G => (x.2 w).val) hy'
      exact this.symm
    exact Units.ext (hHc w (y.2 w) hyw)
  refine ⟨z⁻¹ * hh * z', ?_, fun y hy => ?_⟩
  · have e1 : δ' = z'⁻¹ * d' * sigG G r z' := by rw [hd']; group
    rw [e1, hdd, hd]
    simp only [map_mul, map_inv]
    group
  · have h2 : hh⁻¹ * inclG G r y * hh = inclG G r y := by
      rw [mul_assoc, ← hcomm y hy, inv_mul_cancel_left]
    simp only [carry, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show (z⁻¹ * hh * z')⁻¹ * (z⁻¹ * inclG G r y * z) * (z⁻¹ * hh * z') =
      z'⁻¹ * (hh⁻¹ * inclG G r y * hh) * z' by group, h2]

end GlobalTheory.NrmUnique
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.CarryCent

theorem commute_of_commute_sep {K : Type} [Field K] {n : ℕ} (N A B : Matrix (Fin n) (Fin n) K)
    (hN : N.charpoly.Separable) (hA : Commute A N) (hB : Commute B N) : Commute A B := by
  obtain ⟨q, rfl⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n N A hN hA
  obtain ⟨q', rfl⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n N B hN hB
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, mul_comm]

theorem map_coord_commute {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin n) R)
    (hX : Commute X (N.map (algebraMap K R))) (f : R →ₗ[K] K) : Commute (X.map f) N := by
  have k1 : (X * N.map (algebraMap K R)).map f = X.map f * N := by
    ext i j

    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have k2 : (N.map (algebraMap K R) * X).map f = N * X.map f := by
    ext i j

    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have h := congrArg (fun Y => Y.map f) hX.eq
  simp only [k1, k2] at h
  exact h

theorem commute_of_commute_map {K R : Type} [Field K] [CommRing R] [Algebra K R] [Module.Finite K R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (hN : N.charpoly.Separable) (X Y : Matrix (Fin n) (Fin n) R)
    (hX : Commute X (N.map (algebraMap K R))) (hY : Commute Y (N.map (algebraMap K R))) : Commute X Y := by
  let b := Module.Free.chooseBasis K R
  have dec : ∀ Z : Matrix (Fin n) (Fin n) R, Z = ∑ k, b k • (Z.map (b.coord k)).map (algebraMap K R) := by
    intro Z
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Module.Basis.coord_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr (Z i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [dec X, dec Y]
  refine Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
  refine ((Commute.map ?_ (algebraMap K R).mapMatrix).smul_left _).smul_right _
  exact commute_of_commute_sep N _ _ hN (map_coord_commute N X hX _) (map_coord_commute N Y hY _)

variable {p : ℕ} [Fact p.Prime]

theorem commute_of_commute_reg (G : HTGroup p) (r : ℕ) (hr : 0 < r) (γ : Gp G) (hγ : regular₂ G γ) (a b : Gr G r)
    (ha : Commute a (inclG G r γ)) (hb : Commute b (inclG G r γ)) : Commute a b := by
  refine Prod.ext ?_ (funext fun w => ?_)
  · change a.1 * b.1 = b.1 * a.1
    apply Units.ext
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  · change a.2 w * b.2 w = b.2 w * a.2 w
    letI : Algebra (G.Fw w) (KQ p (G.Fw w) r) := Algebra.TensorProduct.leftAlgebra
    haveI : FiniteDimensional ℚ_[p] (Qr p r) :=
      ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
    haveI : Module.Finite (G.Fw w) (KQ p (G.Fw w) r) :=
      inferInstanceAs (Module.Finite (G.Fw w) ((G.Fw w) ⊗[ℚ_[p]] Qr p r))
    have hw : ∀ x : Gr G r, Commute x (inclG G r γ) →
        Commute (x.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))
          (((γ.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).map
            (algebraMap (G.Fw w) (KQ p (G.Fw w) r))) := by
      intro x hx
      have := congrArg (fun y : Gr G r => ((y.2 w : GL (Fin G.n) (KQ p (G.Fw w) r)) :
        Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))) hx.eq
      exact this
    exact Units.ext (commute_of_commute_map _ (hγ w) _ _ (hw a ha) (hw b hb)).eq

end GlobalTheory.CarryCent

namespace GlobalTheory.CarryCent

variable {p : ℕ} [Fact p.Prime]

theorem map_centralizer_carry : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r),
    0 < r → regular₂ G γ → IsNrm G r γ δ z →
    (Subgroup.centralizer {γ}).map (carry G r z) = GlobalTheory.BCT.twCent (sigG G r) δ := by
  intro p _ G r γ δ z hr hγ hN
  set δ' := z * δ * (sigG G r z)⁻¹ with hδ'
  have hN' : nrmG (sigG G r) r δ' = inclG G r γ := by
    have h := (GlobalTheory.T.twistedNormConj_normalize_and_degree_one p G).1 r γ δ z hr hN
    simpa [IsNrm] using h
  obtain ⟨hit, hfix, hinj, hrange⟩ := GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points p G r hr
  have hδc : Commute δ' (inclG G r γ) := by
    have h2 := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ' 1).2
    rw [hN', hfix, hit] at h2
    exact h2
  have memT : ∀ h, h ∈ GlobalTheory.BCT.twCent (sigG G r) δ' ↔ ∃ g ∈ Subgroup.centralizer {γ}, inclG G r g = h := by
    intro h
    constructor
    · intro hh
      change h * δ' = δ' * sigG G r h at hh
      have hc : Commute h (inclG G r γ) := by
        have h1 := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ' h).1
        have e : h⁻¹ * δ' * sigG G r h = δ' := by rw [mul_assoc, ← hh, inv_mul_cancel_left]
        rw [e, hN', hit] at h1
        change h * inclG G r γ = inclG G r γ * h
        calc h * inclG G r γ = h * (h⁻¹ * inclG G r γ * h) := by rw [← h1]
          _ = inclG G r γ * h := by group
      have hcd : Commute h δ' := commute_of_commute_reg G r hr γ hγ h δ' hc hδc
      have hs : sigG G r h = h := mul_left_cancel (hh.symm.trans hcd.eq)
      obtain ⟨g, rfl⟩ := hrange h hs
      refine ⟨g, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul]
      exact hc.eq
    · rintro ⟨g, hg, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      have hc : Commute (inclG G r g) (inclG G r γ) := by
        change inclG G r g * inclG G r γ = inclG G r γ * inclG G r g
        rw [← map_mul, ← map_mul, hg]
      have hcd := commute_of_commute_reg G r hr γ hγ _ δ' hc hδc
      change inclG G r g * δ' = δ' * sigG G r (inclG G r g)
      rw [hfix]
      exact hcd.eq
  have conjT : ∀ x, x ∈ GlobalTheory.BCT.twCent (sigG G r) δ ↔ z * x * z⁻¹ ∈ GlobalTheory.BCT.twCent (sigG G r) δ' := by
    intro x
    change x * δ = δ * sigG G r x ↔ z * x * z⁻¹ * δ' = δ' * sigG G r (z * x * z⁻¹)
    rw [hδ', map_mul, map_mul, map_inv]
    have e1 : z * x * z⁻¹ * (z * δ * (sigG G r z)⁻¹) = z * (x * δ) * (sigG G r z)⁻¹ := by group
    have e2 : z * δ * (sigG G r z)⁻¹ * (sigG G r z * sigG G r x * (sigG G r z)⁻¹) =
        z * (δ * sigG G r x) * (sigG G r z)⁻¹ := by group
    rw [e1, e2, mul_left_inj, mul_right_inj]
  ext x
  rw [conjT, memT, Subgroup.mem_map]
  refine exists_congr fun g => and_congr_right fun _ => ?_
  change z⁻¹ * inclG G r g * z⁻¹⁻¹ = x ↔ inclG G r g = z * x * z⁻¹
  constructor
  · rintro rfl; group
  · intro e; rw [e]; group

end GlobalTheory.CarryCent
end

section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

namespace GlobalTheory.FlagPlucker

theorem isAmpleLB_of_finite_fibres (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (hf : IsProper f)
    (ι : Type) [Fintype ι] (L : ι → LB X) (hL : ∀ i, (L i).IsLB) (M : ι → ℕ)
    (t : ∀ i, Fin (M i + 1) → (L i).Sec) (ht : ∀ i, ⨆ m, nonzeroLocus (t i m) = ⊤)
    (hfin : ∀ (K : Type) [Field K] [IsAlgClosed K] (a : Sp K ⟶ X),
      {a' : Sp K ⟶ X | a' ≫ f = a ≫ f ∧
        ∀ i, a' ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i) = a ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i)}.Finite)
    (w : ι → ℕ) (hw : ∀ i, 1 ≤ w i) (N : LB X) (hN : N.IsLB)
    (hcls : GlobalTheory.CechPic.cls N hN = ∑ i, w i • GlobalTheory.CechPic.cls (L i) (hL i)) : GlobalTheory.IsAmpleLB N := by
  obtain ⟨Q, Ψ, r, P, hP, hr, hΨ, hc, hinj⟩ :=
    GlobalTheory.AmpleSeparateOverRing.exists_ample_model R X f ι L hL M t ht w hw Finset.univ
  have : LocallyOfFiniteType (Ψ ≫ r) := by rw [hΨ]; infer_instance
  have : LocallyOfFiniteType Ψ := locallyOfFiniteType_of_comp Ψ r
  have : IsProper (Ψ ≫ r) := by rw [hΨ]; infer_instance
  have : IsProper Ψ := IsProper.of_comp Ψ r
  have : LocallyQuasiFinite Ψ := GlobalTheory.locallyQuasiFinite_of_finite_geometric_points Ψ fun K _ _ y => by
    by_cases hy : ∃ a : Spec (.of K) ⟶ X, a ≫ Ψ = y
    · obtain ⟨a, rfl⟩ := hy
      have hs : {a' : Spec (.of K) ⟶ X | a' ≫ Ψ = a ≫ Ψ}.Finite := (hfin K a).subset fun a' ha' => by
        obtain ⟨e1, e2⟩ := hinj K a' a ha'
        exact ⟨e1, fun i => e2 i (Finset.mem_univ i)⟩
      exact hs.to_subtype
    · haveI : IsEmpty {x : Spec (.of K) ⟶ X // x ≫ Ψ = y} := ⟨fun x => hy ⟨x.1, x.2⟩⟩
      infer_instance
  have := IsFinite.of_isProper_of_locallyQuasiFinite Ψ
  have hcls' : CechPic.cls (P.pull Ψ) (LB.isLB_pull hP.isLB Ψ) = CechPic.cls N hN := by
    rw [hc, hcls]
    exact Finset.sum_congr rfl fun i _ => natCast_zsmul _ _
  exact (isAmpleLB_congr (LB.isLB_pull hP.isLB Ψ) hN
    ((CechPic.cls_eq_iff _ _).1 hcls')).1 (hP.pull_of_isAffineHom Ψ)

end GlobalTheory.FlagPlucker

noncomputable section

namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}


open Classical in
def ind (σ : E →+* ℂ) (m : ℕ) : Ix Dw → ℤ :=
  fun ix => ix.elim 0 fun p => if p.1 = σ ∧ (p.2 : ℕ) ≤ m then 1 else 0

def plkU (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) :
    Matrix (Fin Mc.n) (Fin (Dw.mult σ)) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U) :=
  (chg Mc (F.M k).toMChart).map (π.appLE (Mc.U ⊓ (F.M k).U) (F.U k ⊓ π ⁻¹ᵁ Mc.U)
      (fun _ hp => ⟨hp.2, F.le k hp.1⟩)).hom *
    (F.u k σ).map (resG Z (inf_le_left : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ F.U k))

def plkMinor (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) (m : Fin (Dw.mult σ))
    (r : Fin ((m : ℕ) + 1) → Fin Mc.n) : Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U) :=
  ((plkU F Mc k σ).submatrix r (Fin.castLE m.2)).det

abbrev plkNum (Mc : MChart Y) (m : ℕ) : ℕ := Fintype.card (Fin (m + 1) → Fin Mc.n)

def plkIdx (Mc : MChart Y) (m : ℕ) : Fin (plkNum Mc m + 1) → Option (Fin (m + 1) → Fin Mc.n) :=
  Fin.cases none fun i => some ((Fintype.equivFin _).symm i)

theorem plk_le (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (e : Ix Dw → ℤ) (j : ((F.LL e).pull g).ι) :
    ((F.LL e).pull g).U j ≤ g ⁻¹ᵁ (F.U (j PUnit.unit) ⊓ π ⁻¹ᵁ Mc.U) :=
  fun _ hp => ⟨LB.wchart_le _ _ j PUnit.unit hp, hg trivial⟩

def plkLoc (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U)
    (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (q : Fin (plkNum Mc m + 1)) (j : ((F.LL (ind σ m)).pull g).ι) :
    Γ(T, ((F.LL (ind σ m)).pull g).U j) :=
  match plkIdx Mc m q with
  | none => 0
  | some r => (g.appLE _ _ (plk_le F Mc g hg (ind σ m) j)).hom (plkMinor F Mc (j PUnit.unit) σ m r)

end GlobalTheory.FlagPlucker

end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.det_columns_ne_zero_of_pointValues_independent : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (u : Fin (S.D + 1) × Fin S.N → E), LinearIndependent E (fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x)) → S.det c col ≠ 0 := by
  first | exact @GlobalTheory.HSShort.DetNe.det_ne_zero_of_indep | exact GlobalTheory.HSShort.DetNe.det_ne_zero_of_indep | (intros; apply GlobalTheory.HSShort.DetNe.det_ne_zero_of_indep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.differentiable_fockVacuum_gaussian_definitePair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → Differentiable ℂ (GlobalTheory.VacRealForm.gZ σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f) := by
  first | exact @GlobalTheory.VacRealForm.differentiable_gZ_top | exact GlobalTheory.VacRealForm.differentiable_gZ_top | (intros; apply GlobalTheory.VacRealForm.differentiable_gZ_top <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.SecIntegral

theorem exists_integral_relation : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∃ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  intro F _ S hS r e u th hcov
  have hI : AlgebraicGeometry.IsIntegral S.Y := hS.isIntegral
  have hη : IsGenericPoint (genericPoint S.Y) Set.univ := by
    simpa using genericPoint_spec S.Y
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring F (S.Y.residueField (genericPoint S.Y)) (S.baseHom (resPt (genericPoint S.Y))) r e
    (fun i => S.val (resPt (genericPoint S.Y)) (S.comb (u i))) (S.powVal (resPt (genericPoint S.Y)) th)
    (GlobalTheory.T.exists_ratio_mem_valuationSubring_at_generic_point F S hS r e u th hcov _ hη)
  obtain ⟨a, ha, h0⟩ := GlobalTheory.T.homogeneous_components_of_cone_integral_equation _ _ _ r e m _ _ b hb
  exact ⟨m, a, ha, GlobalTheory.T.linearSystem_relation_of_generic_point F S hI r e u th _ hη m a ha h0⟩

end GlobalTheory.SecIntegral
end
end
