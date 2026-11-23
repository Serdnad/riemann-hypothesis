module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleLiftOfSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle105
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle106
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltration
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle293
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ChartBc

section Ring
variable {R R' D : Type} [CommRing R] [CommRing R'] [CommRing D] [Algebra R R'] [Algebra R D]

theorem left_right (r : R) : (algebraMap R R' r) ⊗ₜ[R] (1 : D) = (1 : R') ⊗ₜ[R] (algebraMap R D r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem dp_right {I : Ideal R} {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {J : Ideal D}
    (δ : DividedPowers J)
    (δ' : DividedPowers (I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D)))
    (hJ : J = I.map (algebraMap R D)) (hδ : IsDPMorphism γ δ (algebraMap R D))
    (hδ' : IsDPMorphism γ' δ' (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D))
    (hσ : IsDPMorphism γ γ' (algebraMap R R')) :
    IsDPMorphism δ δ' (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom := by
  have key : ∀ r : R, (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom (algebraMap R D r) =
      (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D) (algebraMap R R' r) := fun r =>
    (left_right r).symm
  refine IsDPMorphism.on_span δ δ' (S := algebraMap R D '' I) (by rw [hJ]; rfl) ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [key]
    exact Ideal.mem_map_of_mem _ (hσ.1 (Ideal.mem_map_of_mem _ ha))
  · rintro n _ ⟨a, ha, rfl⟩
    rw [hδ.2 a ha, key, key, hδ'.2 _ (hσ.1 (Ideal.mem_map_of_mem _ ha)), hσ.2 a ha]

theorem lift_unique {I' : Ideal R'} {J : Ideal D} {B : Type} [CommRing B]
    (hle : J ≤ (I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D)).comap
      (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom)
    (a : R' ⧸ I' →+* B) (b : D ⧸ J →+* B)
    (hab : ∀ r, a (Ideal.Quotient.mk I' (algebraMap R R' r)) = b (Ideal.Quotient.mk J (algebraMap R D r))) :
    ∃! φ : (R' ⊗[R] D) ⧸ I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D) →+* B,
      φ.comp (Ideal.quotientMap _ (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D)
        Ideal.le_comap_map) = a ∧
      φ.comp (Ideal.quotientMap _ (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom hle) = b := by
  letI : Algebra R B := ((a.comp (Ideal.Quotient.mk I')).comp (algebraMap R R')).toAlgebra
  let f1 : R' →ₐ[R] B := { a.comp (Ideal.Quotient.mk I') with commutes' := fun _ => rfl }
  let f2 : D →ₐ[R] B := { b.comp (Ideal.Quotient.mk J) with commutes' := fun r => (hab r).symm }
  let Φ : R' ⊗[R] D →ₐ[R] B := Algebra.TensorProduct.productMap f1 f2
  have hΦ : ∀ r x, Φ (r ⊗ₜ[R] x) = a (Ideal.Quotient.mk I' r) * b (Ideal.Quotient.mk J x) := fun r x => by
    simp only [Φ, Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  have hker : I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D) ≤ RingHom.ker Φ.toRingHom := by
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Φ (x ⊗ₜ[R] 1) = 0
    rw [hΦ, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, zero_mul]
  let φ := Ideal.Quotient.lift _ Φ.toRingHom fun z hz => hker hz
  have hφ : ∀ r x, φ (Ideal.Quotient.mk _ (r ⊗ₜ[R] x)) = a (Ideal.Quotient.mk I' r) * b (Ideal.Quotient.mk J x) :=
    fun r x => by
      rw [Ideal.Quotient.lift_mk]
      exact hΦ r x
  refine ⟨φ, ⟨?_, ?_⟩, ?_⟩
  · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
    change φ (Ideal.Quotient.mk _ (r ⊗ₜ[R] 1)) = a (Ideal.Quotient.mk I' r)
    rw [hφ, map_one, map_one, mul_one]
  · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    change φ (Ideal.Quotient.mk _ ((1 : R') ⊗ₜ[R] x)) = b (Ideal.Quotient.mk J x)
    rw [hφ, map_one, map_one, one_mul]
  · rintro φ₂ ⟨h1, h2⟩
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun w => ?_)
    refine TensorProduct.inductionOn w (fun r x => ?_) (fun u v hu hv => ?_)
    · have t : r ⊗ₜ[R] x = (r ⊗ₜ[R] (1 : D)) * ((1 : R') ⊗ₜ[R] x) := by simp
      have e1 := RingHom.congr_fun h1 (Ideal.Quotient.mk I' r)
      have e2 := RingHom.congr_fun h2 (Ideal.Quotient.mk J x)
      change φ₂ (Ideal.Quotient.mk _ (r ⊗ₜ[R] 1)) = _ at e1
      change φ₂ (Ideal.Quotient.mk _ ((1 : R') ⊗ₜ[R] x)) = _ at e2
      change φ₂ (Ideal.Quotient.mk _ (r ⊗ₜ[R] x)) = φ (Ideal.Quotient.mk _ (r ⊗ₜ[R] x))
      rw [hφ, t, map_mul, map_mul, e1, e2]
    · simp only [RingHom.comp_apply, map_add (f := _)] at hu hv ⊢
      rw [hu, hv]

end Ring

theorem chart_bc : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q κ' σ) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O)
    (hnil : p = 0 → IsNilpotent I') {V : X.Opens} {d : ℕ}
    (c : Chart γ p q κ V d),
    letI := σ.toAlgebra
    letI := c.D.i.toAlgebra
    ∃ (c' : Chart γ' p q κ' V d) (e : c.D ⟶ (m.mor p).functor.obj c'.D), (∀ i, e.φ (c.t i) = c'.t i) ∧
      (FlatT c.D → FlatT c'.D) ∧
      ∃ f : R' ⊗[R] c.D.B ≃+* c'.D.B, (∀ r, f (r ⊗ₜ 1) = c'.D.i r) ∧ ∀ x, f (1 ⊗ₜ x) = e.φ x := by
  intro O R R' _ _ _ I I' γ γ' p X q κ κ' σ m hu hg hnil V d c
  letI a1 : Algebra R R' := σ.toAlgebra
  letI a2 : Algebra R c.D.B := c.D.i.toAlgebra
  let iL : R' →+* R' ⊗[R] c.D.B := Algebra.TensorProduct.includeLeftRingHom
  let iR : c.D.B →+* R' ⊗[R] c.D.B := (Algebra.TensorProduct.includeRight : c.D.B →ₐ[R] R' ⊗[R] c.D.B).toRingHom
  have hcomm : ∀ r, iR (c.D.i r) = iL (σ r) := fun r => (left_right (R := R) (R' := R') (D := c.D.B) r).symm
  have hEt : (MvPolynomial.eval₂Hom iL (fun i => (1 : R') ⊗ₜ[R] c.t i) :
      MvPolynomial (Fin d) R' →+* R' ⊗[R] c.D.B).Etale :=
    GlobalTheory.CompanionTheory.ChartAlg.etale_tensor (O := R) (R := R') (G := c.D.B) c.t c.etale
  haveI hF : Module.Flat R' (R' ⊗[R] c.D.B) := GlobalTheory.CompanionTheory.ChartAlg.flat_of_etale _ hEt
  obtain ⟨δ', hδ'⟩ : ∃ δ' : DividedPowers (I'.map iL), IsDPMorphism γ' δ' iL :=
    GlobalTheory.CompanionTheory.JLiftDP.dpFlat R' (R' ⊗[R] c.D.B) I' γ'
  have hle : c.D.J ≤ (I'.map iL).comap iR := by
    rw [c.J_eq]
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    change iR (c.D.i x) ∈ I'.map iL
    rw [hcomm]
    exact Ideal.mem_map_of_mem iL (m.hI.1 (Ideal.mem_map_of_mem σ hx))
  let h : c.D.B ⧸ c.D.J →+* (R' ⊗[R] c.D.B) ⧸ I'.map iL := Ideal.quotientMap _ iR hle
  let ψ : R' ⧸ I' →+* (R' ⊗[R] c.D.B) ⧸ I'.map iL := Ideal.quotientMap _ iL Ideal.le_comap_map
  let y₀ : PtOver X q κ (c.D.B ⧸ c.D.J) := c.D.y
  have hw : ∀ r, y₀.1.1 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk c.D.J (c.D.i r) := c.D.w
  have hhy : h.comp y₀.1.1 = ψ.comp m.bar := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
    change h (y₀.1.1 (Ideal.Quotient.mk I r)) = Ideal.Quotient.mk _ (iL (σ r))
    rw [hw, ← hcomm]
    rfl
  have hκ' : m.bar.comp κ = κ' := by
    have := m.bar_κ
    rw [hg, RingHom.comp_id] at this
    exact this
  let y' : PtOver X q κ' ((R' ⊗[R] c.D.B) ⧸ I'.map iL) :=
    ⟨(ψ, Spec.map (CommRingCat.ofHom h) ≫ pt c.D), by
      change (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) ≫ q = _
      have e0 : pt c.D ≫ q = Spec.map (CommRingCat.ofHom (y₀.1.1.comp κ)) := y₀.2
      rw [Category.assoc, e0, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hhy,
        RingHom.comp_assoc, hκ']⟩
  let D' : Thick (nlFun γ' p X q κ') := mkT (R' ⊗[R] c.D.B) iL (I'.map iL) δ'
    ⟨fun hp => by
      have h1 : IsNilpotent (p : c.D.B) := c.D.adm.1 hp
      have h2 := h1.map iR
      rwa [map_natCast] at h2,
     fun hp => by
      obtain ⟨n, hn⟩ := hnil hp
      exact ⟨n, by rw [← Ideal.map_pow, hn]; exact Ideal.map_bot⟩⟩ hδ' y' (fun r => rfl)
  have hin : InU V D' := fun x _ => c.inV (show Spec.map (CommRingCat.ofHom h) x ∈ (⊤ : (Spec (CommRingCat.of (c.D.B ⧸ c.D.J))).Opens) from trivial)
  let c' : Chart γ' p q κ' V d :=
    { D := D'
      t := fun k => (1 : R') ⊗ₜ[R] c.t k
      etale := hEt
      J_eq := rfl
      inV := hin
      rep := fun B z hz => by
        let y0 : PtOver X q κ B := ⟨(z.1.1.comp m.bar, z.1.2), by
          rw [z.2, RingHom.comp_assoc, hκ']⟩
        obtain ⟨φ, hφ, hun⟩ := c.rep B y0 hz
        have hφ1 : φ.comp y₀.1.1 = z.1.1.comp m.bar := congrArg (fun w : PtOver X q κ B => w.1.1) hφ
        have hφ2 : Spec.map (CommRingCat.ofHom φ) ≫ pt c.D = z.1.2 :=
          congrArg (fun w : PtOver X q κ B => w.1.2) hφ
        have hab : ∀ r, z.1.1 (Ideal.Quotient.mk I' (algebraMap R R' r)) =
            φ (Ideal.Quotient.mk c.D.J (algebraMap R c.D.B r)) := fun r => by
          have e1 := RingHom.congr_fun hφ1 (Ideal.Quotient.mk I r)
          change φ (y₀.1.1 (Ideal.Quotient.mk I r)) = _ at e1
          rw [hw] at e1
          exact e1.symm
        obtain ⟨φ', ⟨h1, h2⟩, hu'⟩ := lift_unique (R := R) (R' := R') (D := c.D.B) hle z.1.1 φ hab
        refine ⟨φ', ?_, fun φ₂ hφ₂ => hu' φ₂ ?_⟩
        · refine Subtype.ext (Prod.ext h1 ?_)
          change Spec.map (CommRingCat.ofHom φ') ≫ (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) = z.1.2
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          have e2 : φ'.comp h = φ := h2
          rw [e2, hφ2]
        · have ha : φ₂.comp ψ = z.1.1 := congrArg (fun w : PtOver X q κ' B => w.1.1) hφ₂
          have hb : Spec.map (CommRingCat.ofHom φ₂) ≫ (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) = z.1.2 :=
            congrArg (fun w : PtOver X q κ' B => w.1.2) hφ₂
          refine ⟨ha, hun (φ₂.comp h) (Subtype.ext (Prod.ext ?_ ?_))⟩
          · change (φ₂.comp h).comp y₀.1.1 = z.1.1.comp m.bar
            rw [RingHom.comp_assoc, hhy, ← RingHom.comp_assoc, ha]
          · change Spec.map (CommRingCat.ofHom (φ₂.comp h)) ≫ pt c.D = z.1.2
            rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
            exact hb }
  let e : c.D ⟶ (m.mor p).functor.obj c'.D :=
    mkH (T' := (m.mor p).functor.obj c'.D) iR hcomm
      (dp_right (R := R) (R' := R') (D := c.D.B) c.D.δ δ' c.J_eq c.D.compat hδ' m.hI) hle
      (Subtype.ext (Prod.ext hhy (by
        change Spec.map (CommRingCat.ofHom h) ≫ pt c.D = (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) ≫ m.u
        rw [hu, Category.comp_id])))
  exact ⟨c', e, fun _ => rfl, fun _ => RingHom.flat_algebraMap_iff.2 hF, RingEquiv.refl _, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.ChartBc
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ChartP

open GlobalTheory.CompanionTheory.ChartAlg

section Lift

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} {T : Fin d → Γ(X, V)}
  (𝓛 : CrystallineSemistableComparison.B.Lift (strV q V) T R I κ)

def barI : R ⧸ I →+* 𝓛.D ⧸ I.map 𝓛.i := Ideal.quotientMap (I.map 𝓛.i) 𝓛.i Ideal.le_comap_map

theorem barI_mk (r : R) : barI 𝓛 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (𝓛.i r) := rfl

theorem j_strV : 𝓛.j.comp (strV q V) = (barI 𝓛).comp κ := by
  refine RingHom.ext fun o => ?_
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (κ o)
  rw [RingHom.comp_apply, RingHom.comp_apply, 𝓛.hj o x hx, ← hx, barI_mk]

def ptL (hV : IsAffineOpen V) : PtOver X q κ (𝓛.D ⧸ I.map 𝓛.i) :=
  ⟨(barI 𝓛, Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec), by
    change (Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec) ≫ q = Spec.map (CommRingCat.ofHom ((barI 𝓛).comp κ))
    rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← j_strV]
    rfl⟩

theorem rep_lift (hV : IsAffineOpen V) (B : CommRingCat.{0}) (y' : PtOver X q κ B) (hy' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V) :
    ∃! φ : 𝓛.D ⧸ I.map 𝓛.i →+* B, (ptFun X q κ).map (CommRingCat.ofHom φ) (ptL 𝓛 hV) = y' := by
  let e' : Γ(X, V) →+* B := GlobalTheory.Cris.evalAt y'.1.2 V hy'
  let ψ' : R ⧸ I →+* B := y'.1.1
  have hbase : ∀ o x, Ideal.Quotient.mk I x = κ o → e' (strV q V o) = (ψ'.comp (Ideal.Quotient.mk I)) x := by
    intro o x hx
    rw [RingHom.comp_apply, hx]
    exact evalAt_base q κ ψ' y'.1.2 y'.2 hy' o
  obtain ⟨f, ⟨hf1, hf2⟩, hfu⟩ := 𝓛.univ B (ψ'.comp (Ideal.Quotient.mk I)) e'
    (fun x hx => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]) hbase
  have hk : ∀ a ∈ I.map 𝓛.i, f a = 0 := by
    have hle : I.map 𝓛.i ≤ RingHom.ker f := Ideal.map_le_iff_le_comap.2 fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hf1, RingHom.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    exact fun a ha => hle ha
  let φ : 𝓛.D ⧸ I.map 𝓛.i →+* B := Ideal.Quotient.lift _ f hk
  have hφ : ∀ z, φ (Ideal.Quotient.mk _ z) = f z := fun z => rfl
  have hφj : φ.comp 𝓛.j = e' := by
    refine RingHom.ext fun r => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (𝓛.j r)
    rw [RingHom.comp_apply, ← hz, hφ]
    exact hf2 r z hz
  have hφψ : φ.comp (barI 𝓛) = ψ' := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun r => ?_
    change φ (barI 𝓛 (Ideal.Quotient.mk I r)) = ψ' (Ideal.Quotient.mk I r)
    rw [barI_mk, hφ]
    exact RingHom.congr_fun hf1 r
  refine ⟨φ, ?_, ?_⟩
  · refine Subtype.ext (Prod.ext hφψ ?_)
    change Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec = y'.1.2
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφj]
    exact eq_specMap hV y'.1.2 hy'
  · intro φ' h'
    have h1 : φ'.comp (barI 𝓛) = ψ' := congrArg (fun z => z.1.1) h'
    have h2 : Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec = y'.1.2 :=
      congrArg (fun z => z.1.2) h'
    have h3 : e' = φ'.comp 𝓛.j := by
      refine evalAt_specMap hV (φ'.comp 𝓛.j) y'.1.2 ?_ hy'
      rw [← h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h4 : φ'.comp (Ideal.Quotient.mk _) = f := by
      refine hfu _ ⟨?_, fun r z hz => ?_⟩
      · refine RingHom.ext fun r => ?_
        exact RingHom.congr_fun h1 (Ideal.Quotient.mk I r)
      · rw [h3]
        exact congrArg φ' hz
    apply Ideal.Quotient.ringHom_ext
    exact h4

variable (γ : DividedPowers I) (p : ℕ) (δ : DividedPowers (I.map 𝓛.i)) (hδ : IsDPMorphism γ δ 𝓛.i)
  (hadm : (p ≠ 0 → IsNilpotent (p : 𝓛.D)) ∧ (p = 0 → IsNilpotent (I.map 𝓛.i))) (hV : IsAffineOpen V)

def thL : Thick (nlFun γ p X q κ) := mkT 𝓛.D 𝓛.i (I.map 𝓛.i) δ hadm hδ (ptL 𝓛 hV) (fun _ => rfl)

theorem thL_inU : InU V (thL 𝓛 γ p δ hδ hadm hV) := top_le_specMap hV 𝓛.j

theorem ev_thL : ev (thL 𝓛 γ p δ hδ hadm hV) (thL_inU 𝓛 γ p δ hδ hadm hV) = 𝓛.j :=
  evalAt_specMap hV 𝓛.j _ rfl _

def chartL (het : (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t : MvPolynomial (Fin d) R →+* 𝓛.D).Etale) : Chart γ p q κ V d where
  D := thL 𝓛 γ p δ hδ hadm hV
  t := 𝓛.t
  etale := het
  J_eq := rfl
  inV := thL_inU 𝓛 γ p δ hδ hadm hV
  rep := rep_lift 𝓛 hV

end Lift

theorem exists_chart : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ}
    (c : Coord q V d), ∃ c' : Chart γ p q κ V d, FlatT c'.D ∧ ∀ i, ev c'.D c'.inV (c.t i) = Ideal.Quotient.mk _ (c'.t i) := by
  intro O R _ _ I γ p hp hn X q κ V d c
  obtain ⟨𝓛⟩ := GlobalTheory.CompanionTheory.EtaleLift.nonempty_lift (strV q V) c.t I κ c.etale
  have hflat : 𝓛.i.Flat := (GlobalTheory.CompanionTheory.LiftFlat.lift_flat 𝓛.i 𝓛.t 𝓛.et).1
  obtain ⟨δ, hδ⟩ : ∃ δ : DividedPowers (I.map 𝓛.i), IsDPMorphism γ δ 𝓛.i := by
    letI := 𝓛.i.toAlgebra
    haveI : Module.Flat R 𝓛.D := hflat
    exact GlobalTheory.CompanionTheory.JLiftDP.dpFlat R 𝓛.D I γ
  have hadm : (p ≠ 0 → IsNilpotent (p : 𝓛.D)) ∧ (p = 0 → IsNilpotent (I.map 𝓛.i)) :=
    ⟨fun _ => by simpa using hn.map 𝓛.i, fun h => absurd h hp⟩
  exact ⟨chartL 𝓛 γ p δ hδ hadm c.affine 𝓛.et, hflat, fun i =>
    (RingHom.congr_fun (ev_thL 𝓛 γ p δ hδ hadm c.affine) (c.t i)).trans (𝓛.hT i)⟩

end GlobalTheory.CompanionTheory.ChartP
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteTr

theorem tr_tf : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (l s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → fil δ s = ⊥ → (∀ (r : ℕ) (x : B), (l : B) * x ∈ fil δ r → x ∈ fil δ r) → fil δ' s = ⊥ ∧ (∀ (r : ℕ) (x : (pq B).P ⧸ fil (eta δ) (max s 1)), (l : (pq B).P ⧸ fil (eta δ) (max s 1)) * x ∈ fil δ' r → x ∈ fil δ' r) ∧ IsNilpotent (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) := by
  intro B _ J δ l s δ' hδ' hs ht
  obtain ⟨-, hanti, h0, crit⟩ := GlobalTheory.T.divided_power_polynomial_filtration δ (pq B) (eta δ) (eta_std δ)
  have hanti' : ∀ a c, a ≤ c → fil (eta δ) c ≤ fil (eta δ) a := fun a c h =>
    GlobalTheory.Cris.ExpBij.dpFil_anti (eta δ) h
  have hmap : ∀ r, fil δ' r = (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) := fun r =>
    le_antisymm (FubiniStudyChowHeightFormula₂.Adr.Fil.fil_le_map_fil _ _ (eta δ) _ _ δ' _ hδ' rfl r)
      (FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le (eta δ) δ' _ hδ' r)
  have htop : fil δ' (max s 1) = ⊥ := by rw [hmap, Ideal.map_quotient_self]
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos s with rfl | hpos
    · have h10 : (1 : B) = 0 := by
        have : (1 : B) ∈ fil δ 0 := by rw [h0]; trivial
        rwa [hs, Ideal.mem_bot] at this
      haveI : Subsingleton B := subsingleton_of_zero_eq_one h10.symm
      haveI : Subsingleton (pq B).P := Module.subsingleton B (pq B).P
      haveI : Subsingleton ((pq B).P ⧸ fil (eta δ) (max 0 1)) :=
        Ideal.Quotient.mk_surjective.subsingleton
      exact eq_bot_iff.2 fun x _ => (Ideal.mem_bot).2 (Subsingleton.elim x 0)
    · have e : fil (eta δ) s = fil (eta δ) (max s 1) := by rw [max_eq_left hpos]
      rw [hmap, e, Ideal.map_quotient_self]
  · intro r x hx
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key : ∀ y : (pq B).P, Ideal.Quotient.mk (fil (eta δ) (max s 1)) y ∈ fil δ' r ↔
        y ∈ fil (eta δ) (min r (max s 1)) := by
      intro y
      rw [hmap, Ideal.mem_quotient_iff_mem_sup]
      rcases le_total r (max s 1) with h | h
      · rw [min_eq_left h, sup_eq_left.2 (hanti' _ _ h)]
      · rw [min_eq_right h, sup_eq_right.2 (hanti' _ _ h)]
    have hz : (l : (pq B).P) * z ∈ fil (eta δ) (min r (max s 1)) :=
      (key _).1 (by simpa only [map_mul, map_natCast] using hx)
    refine (key z).2 ((crit _ z).2 fun k => ht _ _ ?_)
    have h1 := (crit _ _).1 hz k
    have e : (pq B).e.repr ((l : (pq B).P) * z) k = (l : B) * (pq B).e.repr z k := by
      rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    rwa [e] at h1
  · have hp : ∀ n, (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) ^ n ≤ fil δ' n := by
      intro n
      induction n with
      | zero =>
        intro a _
        exact GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ' a
      | succ n ih =>
        rw [pow_succ]
        exact Ideal.mul_le.2 fun a ha b hb =>
          GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ' (ih ha) (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ' hb)
    exact ⟨max s 1, le_bot_iff.1 ((hp _).trans htop.le)⟩

end GlobalTheory.CompanionTheory.SiteTr
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteTrCrit

variable {B : Type} [CommRing B] {J : Ideal B}

theorem sum_eq (δ : DividedPowers J) (b : ℕ →₀ B) :
    (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) =
      Finsupp.linearCombination B (pq B).e b := by
  rw [Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [(eta_std δ).var k, Algebra.smul_def]

theorem repr_sum (δ : DividedPowers J) (b : ℕ →₀ B) :
    (pq B).e.repr (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = b := by
  rw [sum_eq]
  exact (pq B).e.repr_linearCombination b

theorem crit_sup (δ : DividedPowers J) (r : ℕ) (z : (pq B).P) (c : B) :
    z ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔
      ∀ k, (pq B).e.repr z k ∈ fil δ (r - k) ⊔ Ideal.span {c} := by
  have crit := (GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (eta_std δ)).2.2.2 r
  constructor
  · intro hz k
    obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    have e : w * algebraMap B (pq B).P c = c • w := by rw [Algebra.smul_def, mul_comm]
    rw [e, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mem_sup_left ((crit f).1 hf k))
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)))
  · intro h
    rw [← (pq B).e.linearCombination_repr z, Finsupp.linearCombination_apply]
    refine Ideal.sum_mem _ fun k _ => ?_
    obtain ⟨f, hf, g, hg, e⟩ := Submodule.mem_sup.1 (h k)
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    rw [← e]
    beta_reduce
    rw [add_smul]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ((crit _).2 fun j => ?_)) (Ideal.mem_sup_right ?_)
    · rw [map_smul, (pq B).e.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
      split_ifs with hj
      · rw [← hj]; exact hf
      · exact Ideal.zero_mem _
    · rw [mul_comm w c, mul_smul, Algebra.smul_def c]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.SiteTrCrit


open GlobalTheory.CompanionTheory.SiteTrCrit in
theorem GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → ∀ (b : ℕ →₀ B) (r : ℕ), r ≤ s → ∀ c : B, (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ⊔ Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) := by
  intro B _ J δ s δ' hδ' b r hr c
  have hK : fil (eta δ) (max s 1) ≤ fil (eta δ) r :=
    GlobalTheory.Cris.ExpBij.dpFil_anti (eta δ) (le_max_of_le_left hr)
  have hfil : fil δ' r = (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) :=
    le_antisymm (FubiniStudyChowHeightFormula₂.Adr.Fil.fil_le_map_fil _ _ (eta δ) _ _ δ' _ hδ' rfl r)
      (FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le (eta δ) δ' _ hδ' r)
  have hsup : (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) ⊔
      Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} =
      (fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c}).map
        (Ideal.Quotient.mk (fil (eta δ) (max s 1))) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [hfil, hsup, Ideal.mem_quotient_iff_mem hK, Ideal.mem_quotient_iff_mem (hK.trans le_sup_left),
    crit_sup, (GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (eta_std δ)).2.2.2, repr_sum]
  exact ⟨Iff.rfl, Iff.rfl⟩
end

section


theorem _root_.GlobalTheory.T.slice_branches_holds : GroundTheory.Heights₂.Heights.SliceBranches.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches | exact GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches | (intros; apply GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches <;> assumption)
end
