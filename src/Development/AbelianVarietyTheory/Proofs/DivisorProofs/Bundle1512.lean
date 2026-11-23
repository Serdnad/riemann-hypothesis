module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle442
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

theorem iterate_fst (G : HTGroup p) (r k : ℕ) (g : Gr G r) :
    ((⇑(sigG G r))^[k] g).1 = (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem iterate_snd (G : HTGroup p) (r k : ℕ) (g : Gr G r) (i : Fin G.m) :
    ((⇑(sigG G r))^[k] g).2 i = (⇑(sigRes p (G.Fw i) G.n r))^[k] (g.2 i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem unramifiedExtFrobeniusGL_one_iterate_degree (r : ℕ) (hr : 0 < r) (g : GL (Fin 1) (Qr p r)) :
    (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin 1), ((⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g).val i j
      = (⇑(frobQ p r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, GlobalTheory.LKResNrmConj.frobQ_iterate_self p r hr]

theorem inclK_injective (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    Function.Injective (inclK p K r) :=
  Algebra.TensorProduct.includeLeft_injective (S := ℚ_[p]) (algebraMap ℚ_[p] (Qr p r)).injective

theorem iterate_self (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) : (⇑(sigG G r))^[r] g = g := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · rw [iterate_fst, unramifiedExtFrobeniusGL_one_iterate_degree r hr]
  · rw [iterate_snd, GlobalTheory.LKResNrmConj.sigRes_iterate_self p (G.Fw i) G.n r hr]

theorem fix_incl (G : HTGroup p) (r : ℕ) (γ : Gp G) : sigG G r (inclG G r γ) = inclG G r γ := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change frobQ p r (((inclG G r γ).1 : Matrix (Fin 1) (Fin 1) (Qr p r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe]
    by_cases h : a = b
    · subst h; simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h]
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change sigKQ p (G.Fw i) r (((inclG G r γ).2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_snd, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact sigKQ_apply_inclK p (G.Fw i) r _

end GlobalTheory.LKMid.SigIter

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

theorem incl_injective (G : HTGroup p) (r : ℕ) : Function.Injective (inclG G r) := by
  intro γ γ' h
  have h1 := congrArg (fun g : Gr G r => ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) h
  have h2 := fun i (a b : Fin G.n) =>
    congrArg (fun g : Gr G r => ((g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) h
  simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
    MonoidHom.coe_coe, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Matrix.diagonal_apply_eq] at h1 h2
  refine Prod.ext (Units.ext ((algebraMap ℚ_[p] (Qr p r)).injective h1)) (funext fun i => ?_)
  exact Units.ext (Matrix.ext fun a b => inclK_injective (G.Fw i) r (h2 i a b))

theorem fixed_mem_range (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) (hg : sigG G r g = g) :
    g ∈ (inclG G r).range := by
  have hf : frobQ p r ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) = (g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 :=
    congrArg (fun x : Gr G r => ((x.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) hg
  obtain ⟨c, hc⟩ := frobQ_fixed_mem p r hr _ hf
  have hdet1 : IsUnit ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) := by
    have := Matrix.isUnits_det_units g.1
    rwa [Matrix.det_fin_one] at this
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact not_isUnit_zero (hc ▸ hdet1)
  have hfix : ∀ i (a b : Fin G.n), ∃ x : G.Fw i,
      inclK p (G.Fw i) r x = (g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b := fun i a b =>
    sigKQ_fixed_eq_inclK p (G.Fw i) r hr _
      (congrArg (fun x : Gr G r => ((x.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) hg)
  choose M hM using hfix
  have hmap : ∀ i, (Matrix.of (M i)).map (inclK p (G.Fw i) r) = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
    fun i => Matrix.ext fun a b => hM i a b
  have hdet : ∀ i, (Matrix.of (M i)).det ≠ 0 := by
    intro i h0
    have e := RingHom.map_det (inclK p (G.Fw i) r).toRingHom (Matrix.of (M i))
    rw [h0, map_zero, RingHom.mapMatrix_apply] at e
    have e' : (Matrix.of (M i)).map (inclK p (G.Fw i) r).toRingHom = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
      hmap i
    rw [e'] at e
    have hu := Matrix.isUnits_det_units (g.2 i)
    rw [← e] at hu
    have hsub : Subsingleton (KQ p (G.Fw i) r) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
    have := inclK_injective (G.Fw i) r (Subsingleton.elim (inclK p (G.Fw i) r 1) (inclK p (G.Fw i) r 0))
    exact one_ne_zero this
  refine ⟨(Units.mk0 c hc0, fun i => GeneralLinearGroup.mkOfDetNeZero (Matrix.of (M i)) (hdet i)), ?_⟩
  refine Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) (funext fun i => Units.ext ?_)
  · have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe, Matrix.diagonal_apply_eq, Units.val_mk0]
    exact hc
  · rw [← hmap i]
    rfl

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r →
    (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧
      Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range :=
  fun _ _ G r hr => ⟨iterate_self G r hr, fix_incl G r, incl_injective G r, fixed_mem_range G r hr⟩

end GlobalTheory.LKMid.SigIter
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKCentAf

theorem baseChange_centralizer_comm (K k B A : Type) [Field K] [CommRing k] [Algebra K k] [Ring B]
    [Algebra K B] [Ring A] [Algebra K A] (γ : B) (f : A →ₐ[K] B)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) :
    ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y ↔
      y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id k k) f) := by
  let ad : B →ₗ[K] B := LinearMap.mulRight K γ - LinearMap.mulLeft K γ
  have hex : Function.Exact f.toLinearMap ad := by
    intro x
    simp only [ad, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply]
    exact hcent x
  have hmap : ∀ y, Algebra.TensorProduct.map (AlgHom.id k k) f y = LinearMap.lTensor k f.toLinearMap y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have had : ∀ y : k ⊗[K] B, y * ((1 : k) ⊗ₜ[K] γ) - ((1 : k) ⊗ₜ[K] γ) * y = LinearMap.lTensor k ad y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      simp [ad, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add (f := _), ← hx, ← hy]; noncomm_ring
  have hex' := Module.Flat.lTensor_exact k hex
  intro y
  rw [← sub_eq_zero, had, hex' y]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, hmap z⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hmap z).symm⟩

theorem commute_of_centralizer (K k B A : Type) [Field K] [CommRing k] [Algebra K k] [Ring B]
    [Algebra K B] [CommRing A] [Algebra K A] (γ : B) (f : A →ₐ[K] B)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) (y z : k ⊗[K] B)
    (hy : y * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * y)
    (hz : z * ((1 : k) ⊗ₜ[K] γ) = ((1 : k) ⊗ₜ[K] γ) * z) : y * z = z * y := by
  obtain ⟨y', rfl⟩ := (baseChange_centralizer_comm K k B A γ f hcent y).1 hy
  obtain ⟨z', rfl⟩ := (baseChange_centralizer_comm K k B A γ f hcent z).1 hz
  rw [← map_mul, ← map_mul, mul_comm]

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem cent_iff_mem (P : Pair G) (y : G.C) :
    y * (P.γ : G.C) = (P.γ : G.C) * y ↔
      y ∈ Set.range ((Algebra.adjoin G.F ({(P.γ : G.C)} : Set G.C)).val.restrictScalars ℚ) := by
  have hcsa := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC (P.γ : G.C) P.reg.2 P.reg.1
  constructor
  · intro h
    have hy : y ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
      rw [Subalgebra.mem_centralizer_iff]
      simpa using h.symm
    rw [hcsa] at hy
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    have hw : (w : G.C) ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by rw [hcsa]; exact w.2
    rw [Subalgebra.mem_centralizer_iff] at hw
    exact (hw _ rfl).symm

theorem conj_commute (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t)
    (a : G.GAf) (ha : a ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self)) :
    (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) *
        ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) =
      ((1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C)) *
        (((x⁻¹ * (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x : (AfP p ⊗[ℚ] G.C)ˣ)) : AfP p ⊗[ℚ] G.C) := by
  set U : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom P.γ with hU
  have hUv : (U : AfP p ⊗[ℚ] G.C) = (1 : AfP p) ⊗ₜ[ℚ] (P.γ : G.C) := rfl
  have hδ : ((P.toAf x t hx P.self : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = x * U * x⁻¹ := rfl
  have h1 := congrArg (fun g : G.GAf => (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1) ha
  simp only [Subgroup.coe_mul, Prod.fst_mul, MonoidHom.id_apply] at h1
  rw [hδ] at h1
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have h2 : x⁻¹ * A * x * U = U * (x⁻¹ * A * x) := by
    calc x⁻¹ * A * x * U = x⁻¹ * (A * (x * U * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * U * x⁻¹ * A) * x := by rw [h1]
      _ = U * (x⁻¹ * A * x) := by group
  rw [← hUv, ← Units.val_mul, ← Units.val_mul, h2]

theorem twCent_comm : ∀ {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
    ∀ a ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self),
    ∀ b ∈ GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self), a * b = b * a := by
  intro p _ G P x t hx a ha b hb
  have hc := commute_of_centralizer ℚ (AfP p) G.C _ (P.γ : G.C) _ (cent_iff_mem P) _ _
    (conj_commute P x t hx a ha) (conj_commute P x t hx b hb)
  set A := (a : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  set B := (b : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
  have hc' : (x⁻¹ * A * x) * (x⁻¹ * B * x) = (x⁻¹ * B * x) * (x⁻¹ * A * x) := Units.ext (by
    simpa only [Units.val_mul] using hc)
  have hAB : A * B = B * A := by
    calc A * B = x * ((x⁻¹ * A * x) * (x⁻¹ * B * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * B * x) * (x⁻¹ * A * x)) * x⁻¹ := by rw [hc']
      _ = B * A := by group
  apply Subtype.ext
  apply Prod.ext
  · simpa only [Subgroup.coe_mul, Prod.fst_mul] using hAB
  · simp only [Subgroup.coe_mul, Prod.snd_mul]
    exact mul_comm _ _

end GlobalTheory.LKCentAf
end
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

abbrev FM (P : Pair G) : Type := AdjoinRoot P.pol

def jM (P : Pair G) : FM P →ₐ[G.F] G.C :=
  Ideal.Quotient.liftₐ _ (aeval (P.γ : G.C)) fun f hf => by
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.1 hf
    rw [map_mul, Pair.pol, minpoly.aeval, zero_mul]

theorem jM_mk (P : Pair G) (f : G.F[X]) : jM P (AdjoinRoot.mk P.pol f) = aeval (P.γ : G.C) f := rfl

theorem jM_root (P : Pair G) : jM P (AdjoinRoot.root P.pol) = P.γ := by
  rw [← AdjoinRoot.mk_X, jM_mk, aeval_X]

theorem jM_injective (P : Pair G) : Function.Injective (jM P) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [jM_mk] at ha
  exact AdjoinRoot.mk_eq_zero.2 (minpoly.dvd G.F _ ha)

theorem jM_algQ (P : Pair G) (q : ℚ) : jM P (algebraMap ℚ (FM P) q) = algebraMap ℚ G.C q := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F (FM P), AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem jM_comm (P : Pair G) (a : FM P) : jM P a * P.γ = P.γ * jM P a := by
  rw [← jM_root, ← map_mul, ← map_mul, mul_comm]

theorem exists_jM (P : Pair G) (u : G.C) (hu : u * P.γ = P.γ * u) : ∃ a, jM P a = u := by
  have hc : u ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact hu.symm
  rw [GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC _ P.reg.2 P.reg.1,
    Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨f, rfl⟩ := hc
  exact ⟨AdjoinRoot.mk _ f, rfl⟩

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp [sh, map_mul]

theorem sh_one : sh G (1 : G.C) = 1 := by simp [sh]

theorem sh_add (x y : G.C) : sh G (x + y) = sh G x + sh G y := by simp [sh, map_add (f := _)]

theorem sh_zero : sh G (0 : G.C) = 0 := by simp [sh]

theorem sh_sh (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_algF (a : G.F) : sh G (algebraMap G.F G.C a) = algebraMap G.F G.C (IsCMField.complexConj G.F a) :=
  G.star_F a

def iC (P : Pair G) (x : G.C) : G.C := (P.β : G.C) * sh G x * ((P.β⁻¹ : G.Cˣ) : G.C)

theorem iC_mul (P : Pair G) (x y : G.C) : iC P (x * y) = iC P y * iC P x := by
  simp only [iC, sh_mul, mul_assoc, Units.inv_mul_cancel_left]

theorem iC_one (P : Pair G) : iC P 1 = 1 := by simp [iC, sh_one]

theorem iC_add (P : Pair G) (x y : G.C) : iC P (x + y) = iC P x + iC P y := by
  simp [iC, sh_add, mul_add, add_mul]

theorem iC_zero (P : Pair G) : iC P 0 = 0 := by simp [iC, sh_zero]

theorem iC_algF (P : Pair G) (a : G.F) :
    iC P (algebraMap G.F G.C a) = algebraMap G.F G.C (IsCMField.complexConj G.F a) := by
  rw [iC, sh_algF, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

theorem iC_algQ (P : Pair G) (q : ℚ) : iC P (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, iC_algF]
  congr 1
  simp

theorem iC_gamma_mul (P : Pair G) : iC P P.γ * P.γ = algebraMap ℚ G.C P.c := by
  have h := P.sim
  have h2 : (P.β : G.C) * sh G P.γ = ((P.γ⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C P.c * P.β) := by
    rw [← h]; simp only [← mul_assoc, Units.inv_mul, one_mul]
  calc iC P P.γ * P.γ = ((P.β : G.C) * sh G P.γ) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := rfl
    _ = ((P.γ⁻¹ : G.Cˣ) : G.C) * algebraMap ℚ G.C P.c * P.γ := by
        rw [h2]; simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [mul_assoc, Algebra.commutes, ← mul_assoc, Units.inv_mul, one_mul]

theorem iC_comm (P : Pair G) (u : G.C) (hu : u * P.γ = P.γ * u) : iC P u * P.γ = P.γ * iC P u := by
  have h1 : iC P u * iC P P.γ = iC P P.γ * iC P u := by rw [← iC_mul, ← iC_mul, hu]
  have hg : iC P P.γ = algebraMap ℚ G.C P.c * ((P.γ⁻¹ : G.Cˣ) : G.C) := by
    rw [← iC_gamma_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [hg, ← mul_assoc, ← Algebra.commutes, mul_assoc, mul_assoc] at h1
  have hc : IsUnit (algebraMap ℚ G.C P.c) := (P.c.isUnit).map _
  have h2 := hc.mul_left_cancel h1
  calc iC P u * P.γ = P.γ * (((P.γ⁻¹ : G.Cˣ) : G.C) * iC P u) * P.γ := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = P.γ * (iC P u * ((P.γ⁻¹ : G.Cˣ) : G.C)) * P.γ := by rw [h2]
    _ = _ := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

theorem iC_iC (P : Pair G) (x : G.C) : iC P (iC P x) = x := by
  have hb : sh G (P.β : G.C) = P.β := P.sym
  have hbi : sh G ((P.β⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C) := by
    have e : sh G ((P.β⁻¹ : G.Cˣ) : G.C) * P.β = 1 := by
      rw [← hb, ← sh_mul, Units.mul_inv, sh_one]
    calc sh G ((P.β⁻¹ : G.Cˣ) : G.C) = sh G ((P.β⁻¹ : G.Cˣ) : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [e, one_mul]
  simp only [iC, sh_mul, hb, hbi, sh_sh, mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

def iMf (P : Pair G) (a : FM P) : FM P := (exists_jM P (iC P (jM P a)) (iC_comm P _ (jM_comm P a))).choose

theorem jM_iMf (P : Pair G) (a : FM P) : jM P (iMf P a) = iC P (jM P a) :=
  (exists_jM P (iC P (jM P a)) (iC_comm P _ (jM_comm P a))).choose_spec

def iM (P : Pair G) : FM P →ₐ[ℚ] FM P where
  toFun := iMf P
  map_one' := jM_injective P (by rw [jM_iMf, map_one, iC_one])
  map_mul' a b := jM_injective P (by
    rw [mul_comm (iMf P a), jM_iMf, map_mul, map_mul, jM_iMf, jM_iMf, iC_mul])
  map_zero' := jM_injective P (by rw [jM_iMf, map_zero, iC_zero])
  map_add' a b := jM_injective P (by rw [jM_iMf, map_add (f := _), map_add (f := _), jM_iMf, jM_iMf, iC_add])
  commutes' q := jM_injective P (by rw [jM_iMf, jM_algQ, iC_algQ])

theorem jM_iM (P : Pair G) (a : FM P) : jM P (iM P a) = iC P (jM P a) := jM_iMf P a

theorem iM_algF (P : Pair G) (a : G.F) :
    iM P (algebraMap G.F (FM P) a) = algebraMap G.F (FM P) (IsCMField.complexConj G.F a) :=
  jM_injective P (by rw [jM_iM, AlgHom.commutes, AlgHom.commutes, iC_algF])

theorem iM_root_mul (P : Pair G) :
    iM P (AdjoinRoot.root P.pol) * AdjoinRoot.root P.pol = algebraMap ℚ (FM P) P.c :=
  jM_injective P (by rw [map_mul, jM_iM, jM_root, jM_algQ, iC_gamma_mul])

theorem iM_iM (P : Pair G) (a : FM P) : iM P (iM P a) = a :=
  jM_injective P (by rw [jM_iM, jM_iM, iC_iC])

theorem mul_iM_of_cent (P : Pair G) (w : P.cent) (a : FM P) (ha : jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C)) :
    a * iM P a = algebraMap ℚ (FM P) ((w : G.Cˣ × ℚˣ).2 : ℚ) :=
  jM_injective P (by
    rw [map_mul, jM_iM, jM_algQ, ha, iC, ← mul_assoc, ← mul_assoc, w.2.2, mul_assoc, Units.mul_inv, mul_one])

theorem exists_pow_mem_conj {H : Type} [Group H] (K K₀ : Subgroup H) (g y : H) (hK : K.Commensurable K₀)
    (hy : y ∈ K.map (MulAut.conj g).toMonoidHom) :
    ∃ m : ℕ, 0 < m ∧ y ^ m ∈ K₀.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨k, hk, rfl⟩ := hy
  obtain ⟨m, hm0, -, hm⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (H := K₀.subgroupOf K) hK.2.relIndex_ne_zero (⟨k, hk⟩ : K)
  refine ⟨m, hm0, k ^ m, ?_, by simp [map_pow]⟩
  simpa [Subgroup.mem_subgroupOf] using hm

end GlobalTheory.StabFin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.summable_rational_schwartzBruhat_mul_polynomial_decay : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) → ∀ (a : κ → FiniteAdeleRing (𝓞 F) F), ∃ M : ℕ, ∀ c : κ → mixedEmbedding.mixedSpace F, Summable fun ξ : κ → F => ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) + a i)‖ * ((1 + ‖((fun i => mixedEmbedding F (ξ i)) + c : κ → mixedEmbedding.mixedSpace F)‖) ^ M)⁻¹ := by
  first | exact @GlobalTheory.LatSumSB.summable_sb_mul_decay | exact GlobalTheory.LatSumSB.summable_sb_mul_decay | (intros; apply GlobalTheory.LatSumSB.summable_sb_mul_decay <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory


theorem _root_.GlobalTheory.T.tsum_norm_adelicSchwartz_rationalTranslates_le : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι], ∀ Φ ∈ GlobalTheory.WeilM.schA F ι,
    ∃ B : ℝ, ∀ z : ι → AF F, ∑' ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ ≤ B := by
  first | exact @GlobalTheory.UniformTranslateBound.tsum_norm_translate_le | exact GlobalTheory.UniformTranslateBound.tsum_norm_translate_le | (intros; apply GlobalTheory.UniformTranslateBound.tsum_norm_translate_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

theorem _root_.GlobalTheory.T.nonempty_cartier_of_locally_principal' : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData), (∀ y : Y, ∃ (W : Y.affineOpens) (a : Γ(Y, W.1)), y ∈ W.1 ∧ a ∈ nonZeroDivisors Γ(Y, W.1) ∧ I.ideal W = Ideal.span {a}) → Nonempty (Cartier I) := by
  first | exact @GlobalTheory.CompHS.nonempty_cartier_of_locally_principal | exact GlobalTheory.CompHS.nonempty_cartier_of_locally_principal | (intros; apply GlobalTheory.CompHS.nonempty_cartier_of_locally_principal <;> assumption)
end
