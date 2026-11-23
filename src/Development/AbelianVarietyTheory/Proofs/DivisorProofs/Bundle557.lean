module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveTwoCocycleCoeffRelationsOnePair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
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
public import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem mu_dvd_of_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι κ : Type) [Fintype ι] (R S : Matrix ι ι F.B) (R0 S0 : Matrix ι ι (Ainf p O)) (Y : Matrix ι κ F.B) (F0 : Matrix ι κ (Ainf p O)), (∀ i j, F.τ ∣ R i j - F.a (R0 i j)) → (∀ i j, F.τ ∣ S i j - F.a (S0 i j)) → (∀ i m, F.τ ∣ Y i m - F.a (F0 i m)) → R * Y.map F.σ = S * Y → ∀ i m, Sandwich.mu ε ∣ (R0 * F0.map WittVector.frobenius - S0 * F0) i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F ι κ _ R S R0 S0 Y F0 hR hS hY hRS i m
  apply (F.a_dvd _).1
  set q := Ideal.Quotient.mk (Ideal.span {F.τ})
  have key : ∀ x y : F.B, F.τ ∣ x - y → q x = q y := fun x y h =>
    Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)
  have hR' : ∀ i j, q (R i j) = q (F.a (R0 i j)) := fun i j => key _ _ (hR i j)
  have hS' : ∀ i j, q (S i j) = q (F.a (S0 i j)) := fun i j => key _ _ (hS i j)
  have hY' : ∀ i m, q (Y i m) = q (F.a (F0 i m)) := fun i m => key _ _ (hY i m)
  have hYσ : ∀ i m, q (F.σ (Y i m)) = q (F.a (WittVector.frobenius (F0 i m))) := fun i m => by
    apply key
    rw [← F.σ_a, ← map_sub]
    exact tau_dvd_sigma F _ (hY i m)
  have h := congrArg (fun M => q (M i m)) hRS

  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul] at h
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change q _ = 0
  rw [Matrix.sub_apply, map_sub, map_sub, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply]

  simp only [map_sum, map_mul, Matrix.map_apply, ← hR', ← hS', ← hYσ, ← hY']
  exact h

end GlobalTheory.WinLift
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
open GlobalTheory.QLog.Window

namespace GlobalTheory.QLog.WindowMat

theorem integers_isIntegrallyClosedIn {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

theorem hasPeriod_zero {p : ℕ} {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q] [Algebra B Q]
    {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d) {θ : B →+* O} (h : IsFrame p Q θ)
    (t : G.Tate) : c.HasPeriod θ t (0 : MvPowerSeries (Fin d) Q) 0 := by
  refine (c.hasPeriod_iff h t (0 : MvPowerSeries (Fin d) Q) 0).2 fun n z _ => ⟨0, fun m => ⟨0, fun N _ => ⟨0, ?_⟩⟩, 0, ?_⟩
  · have h0 : trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N) (0 : MvPowerSeries (Fin d) Q) = 0 :=
      map_zero _
    rw [h0, map_zero, sub_zero, mul_zero, map_zero]
  · simp

section Transfer

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] (θ : B →+* O) (Θ : Q →+* C)
  (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
include hΘ

theorem in_map_top {σ : Type} {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal O) (map Θ f) := fun α => by
  obtain ⟨b, -, eb⟩ := hf α
  exact ⟨θ b, Submodule.mem_top, by rw [coeff_map, eb, hΘ]⟩

theorem map_eq_zero_of_in_ker {σ : Type} {f : MvPowerSeries σ Q} (hf : In (RingHom.ker θ) f) :
    map Θ f = 0 := by
  ext α
  obtain ⟨b, hb, eb⟩ := hf α
  rw [coeff_map, eb, hΘ, RingHom.mem_ker.1 hb, map_zero, map_zero]

theorem map_comb {σ ι : Type} [Finite σ] [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) fun i => map Θ (e i) := by
  unfold comb

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul', hΘ]

theorem lin_map {d : ℕ} (f : MvPowerSeries (Fin d) Q) (i : Fin d) : lin (map Θ f) i = Θ (lin f i) := by
  simp only [lin, coeff_map]

theorem up_map {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i) (i : Fin d) :
    up C μ i = map Θ (up Q μ' i) := by
  ext α
  simp only [up, coeff_map, ← hμ, hΘ]

theorem ql_map {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i)
    (h0 : ∀ i, constantCoeff (μ' i) = 0) {f : MvPowerSeries (Fin d) Q} (hf : QL μ' ⊤ f) :
    QL μ ⊤ (map Θ f) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, hf.1, map_zero]
  · obtain ⟨b, -, eb⟩ := hf.2.1 i
    exact ⟨θ b, Submodule.mem_top, by rw [lin_map θ Θ hΘ, eb, hΘ]⟩
  · have : up C μ = fun i => map Θ (up Q μ' i) := funext (up_map θ Θ hΘ hμ)
    rw [this, ← map_formalGroupLawCoboundaryOne_eq Θ _ (constantCoeff_up h0)]
    exact in_map_top θ Θ hΘ hf.2.2

theorem formalGroupLawCoboundaryOne_map_eq_zero {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i)
    (h0 : ∀ i, constantCoeff (μ' i) = 0) {f : MvPowerSeries (Fin d) Q}
    (hf : In (RingHom.ker θ) (cob1 (up Q μ') f)) : cob1 (up C μ) (map Θ f) = 0 := by
  have : up C μ = fun i => map Θ (up Q μ' i) := funext (up_map θ Θ hΘ hμ)
  rw [this, ← map_formalGroupLawCoboundaryOne_eq Θ _ (constantCoeff_up h0)]
  exact map_eq_zero_of_in_ker θ Θ hΘ hf

end Transfer

theorem comb_sum {B Q σ ι κ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype ι] [Fintype κ]
    (R : κ → ι → B) (a : ι → B) (e : κ → MvPowerSeries σ Q) :
    comb (fun l => ∑ i, R l i * a i) e = ∑ i, algebraMap B Q (a i) • comb (fun l => R l i) e := by
  unfold comb

  simp only [map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem din_of_in {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] {f : MvPowerSeries σ Q}
    (hf : In (⊤ : Ideal B) f) : DIn (⊤ : Ideal B) f := fun α i => by
  obtain ⟨b, -, eb⟩ := hf α
  exact ⟨(α i : B) * b, Submodule.mem_top, by rw [eb, map_mul, map_natCast]⟩

end GlobalTheory.QLog.WindowMat
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem algHom_eval_comp_eq_evA_map :
    ∀ (p m : ℕ) (O A k A' σ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing k]
      [CommRing A'] [Algebra k A'] [Fintype σ] (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A),
      IsEval p x E → ∀ (r : O →+* k) (g : A →+* A'),
      (∀ c, g (algebraMap O A c) = algebraMap k A' (r c)) → (p : A') ^ m = 0 →
      ∀ hx : ∀ i, IsNilpotent (g (x i)), ∀ f,
        g (E f) = evA k (fun i => g (x i)) hx (map r f) := by
  intro p m O A k A' σ _ _ _ _ _ _ _ x E hE r g hg _ hx f
  letI : Algebra O A' := ((algebraMap k A').comp r).toAlgebra
  have hs : HasSubst (fun i => (C (g (x i)) : MvPowerSeries Empty A')) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  have hevX : ∀ i, evA k (fun i => g (x i)) hx (X i) = g (x i) := by
    intro i
    simp [evA, coe_substAlgHom, subst_X hs]
  let φ : MvPowerSeries σ O →ₐ[O] A' :=
    { g.comp E.toRingHom with
      commutes' := fun c => by
        show g (E (algebraMap O _ c)) = (algebraMap k A').comp r c
        rw [AlgHom.commutes, hg]; rfl }
  let ψ : MvPowerSeries σ O →ₐ[O] A' :=
    { (evA k (fun i => g (x i)) hx).toRingHom.comp (map r) with
      commutes' := fun c => by
        show evA k (fun i => g (x i)) hx (map r (algebraMap O _ c)) = (algebraMap k A').comp r c
        have hm : map r (algebraMap O (MvPowerSeries σ O) c) =
            algebraMap k (MvPowerSeries σ k) (r c) := by
          simp [MvPowerSeries.algebraMap_apply, map_C]
        rw [hm, AlgHom.commutes]; rfl }
  have hφX : ∀ i, φ (X i) = g (x i) := fun i => by
    show g (E (X i)) = _
    rw [hE.1 i]
  have hψX : ∀ i, ψ (X i) = g (x i) := fun i => by
    show evA k (fun i => g (x i)) hx (map r (X i)) = _
    rw [map_X, hevX]
  have key := GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent O σ A' φ ψ
    (fun i => by rw [hφX]; exact hx i) (fun i => by rw [hφX, hψX])
  exact DFunLike.congr_fun key f

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def IsLevelStructureOfLevel {D : Datum F} {p N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (N₁ : ℕ)
    (α : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  (∀ a c, α (a + c) = α a * α c) ∧ (∀ a, α (N₁ • a) = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (∀ a, toUnit (Over.mk x) ≫ α a = 1 ↔ ∃ b, a = N₁ • b) ∧
      (∀ g : Over.mk x ⟶ o.A, g ^ N₁ = 1 → ∃ a, toUnit _ ≫ α a = g) ∧
      ∃ z : kˣ, IsPrimitiveRoot z N₁ ∧
        ∀ a b, Out.WeilIs o.A o.PP.L N₁ (toUnit (Over.mk x) ≫ α a) (toUnit _ ≫ α b) (unitOn (z ^ D.EF a b))

def LevelStructurePullback {D : Datum F} {p N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} {s' : S' ⟶ Sp (D.OEp p)}
    {o' : Obj D p N s'} {o : Obj D p N s} {f : S' ⟶ S} (m : ObjMap o' o f) (α' : D.La → (𝟙_ (Over S') ⟶ o'.A))
    (α : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  ∀ a, (α' a).left ≫ m.φ = f ≫ (α a).left

def HasLevelStructureOfLevel {D : Datum F} {p N : ℕ} {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp (D.OEp p)} (o₁ : Obj D p N s₁) (N₁ : ℕ)
    (α₁ : D.La → (𝟙_ (Over X₁) ⟶ o₁.A)) : Prop :=
  ∀ (S : Scheme.{0}) (s : S ⟶ Sp (D.OEp p)) (o : Obj D p N s) (α : D.La → (𝟙_ (Over S) ⟶ o.A)), IsLevelStructureOfLevel o N₁ α →
    ∃! f : S ⟶ X₁, f ≫ s₁ = s ∧ ∃ m : ObjMap o o₁ f, LevelStructurePullback m α α₁

end GlobalTheory.UPel
end
end

section

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

structure IntSim (D : Datum F) (p : ℕ) where
  c : ℕ
  k : ℕ
  c_cop : c.Coprime p
  k_cop : k.Coprime p
  g : ℕ → D.La →ₗ[𝓞 F] D.La
  compat : ∀ n m : ℕ, (n * m).Coprime p → ∀ a, ∃ b, g (n * m) a - g n a = n • b
  sim : ∀ n : ℕ, n.Coprime p → ∃ u : ℤ, IsCoprime u (n : ℤ) ∧
    ∀ a b, (n : ℤ) ∣ D.EF (g n a) (g n b) - c * u * D.EF a b
  onto : ∀ n : ℕ, n.Coprime p → ∀ a, ∃ b d, g n b = k • a + n • d

namespace IntSim

variable {D : Datum F} {p : ℕ}

end IntSim

variable {S : Scheme.{0}}

def HeckeRel {D : Datum F} {p N N' : ℕ} (g : IntSim D p) {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s)
    (o' : Obj D p N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ Etale ψ.left ∧
    (∀ x, o'.eta x = o.eta ((N' / (N * g.k)) • g.g N' x) ≫ ψ) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (t : Over.mk x ⟶ o.A),
      t ≫ ψ = 1 ↔ ∃ a, t = toUnit _ ≫ o.eta ((N' / g.k) • g.g N' a)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n → n.Coprime p →
      ∀ (P Q : Over.mk x ⟶ o.A), P ^ n = 1 → Q ^ n = 1 → ∀ ζ : kˣ,
        Out.WeilIs o'.A o'.PP.L n (P ≫ ψ) (Q ≫ ψ) (unitOn ζ) →
          Out.WeilIs o.A o.PP.L ((g.k ^ 2 * n : ℕ) : ℤ) P Q (unitOn (ζ ^ g.c))

def IsHecke {D : Datum F} {p N N' : ℕ} (g : IntSim D p) (M' : IntModel D p N') (M : IntModel D p N)
    (π : M'.X ⟶ M.X) : Prop :=
  π ≫ M.s = M'.s ∧ ∃ (o : Obj D p N M'.s) (ψ : M'.univ.A ⟶ o.A), HeckeRel g M'.univ o ψ ∧ Nonempty (ObjMap o M.univ π)

end GlobalTheory.UPel
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.TangentOrigin

namespace GlobalTheory.AnPer

theorem exists_point_hol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens E)
    (X : Scheme.{0}) (e : E → (Sp ℂ ⟶ X)) (U : X.Opens), IsAffineOpen U → IsHolTo (W : Set E) e → (∀ p ∈ W, ⊤ ≤ e p ⁻¹ᵁ U) →
    ∃ x : Sp (Hol W) ⟶ X, ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x = e p := by
  intro E _ _ _ W X e U hU he hW
  have ha : ∀ f : Γ(X, U), AnalyticOnNhd ℂ (fun p => valAt' (e p) U f) W := fun f p hp =>
    SCV.analyticAt_of_differentiableOn (he U f).2 ((he U f).1.mem_nhds ⟨hp, hW p hp⟩)
  have hv : ∀ (f : Γ(X, U)) (p : E) (hp : p ∈ W), (Hol.mk _ (ha f)).fn p = evalPt (e p) U (hW p hp) f :=
    fun f p hp => (Hol.fn_mk _ _ hp).trans (valAt'_eq_evalPt _ _ _ _)
  let ψ : Γ(X, U) →+* Hol W :=
    { toFun := fun f => Hol.mk _ (ha f)
      map_one' := Hol.ext_fn fun p hp => by rw [hv _ p hp, map_one, ← Hol.ev_apply p hp, map_one]
      map_mul' := fun f g => Hol.ext_fn fun p hp => by rw [Hol.fn_mul _ _ hp, hv _ p hp, hv _ p hp, hv _ p hp, map_mul]
      map_zero' := Hol.ext_fn fun p hp => by rw [hv _ p hp, map_zero, ← Hol.ev_apply p hp, map_zero]
      map_add' := fun f g => Hol.ext_fn fun p hp => by rw [Hol.fn_add _ _ hp, hv _ p hp, hv _ p hp, hv _ p hp, map_add (f := _)] }
  obtain ⟨x, hx, hxψ⟩ := exists_evalPt_eq hU ψ
  have h' : ∀ (p : E) (hp : p ∈ W), ⊤ ≤ (spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x) ⁻¹ᵁ U := fun p hp q _ => hx trivial
  refine ⟨x, hx, fun p hp => ext_evalPt hU (h' p hp) (hW p hp) (RingHom.ext fun f => ?_)⟩
  rw [evalPt_spMap_comp _ x U hx, hxψ]
  exact (Hol.ev_apply p hp _).trans (hv f p hp)

theorem point_hol_ext : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E)
    (X S : Scheme.{0}) (s : X ⟶ S) [IsSeparated s] (x x' : Sp (Hol W) ⟶ X), x ≫ s = x' ≫ s →
    (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x = spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x') → x = x' := by
  intro E _ _ W X S s _ x x' hs h
  have : _root_.IsReduced (Hol W) := isReduced_of_injective (holSub W).val Subtype.val_injective
  suffices IsDominant (equalizer.ι x x') from
    ext_of_isDominant_of_isSeparated s hs (equalizer.ι x x') (equalizer.condition _ _)
  refine ⟨?_⟩
  have hd : Dense (Set.range fun p : W => PrimeSpectrum.comap (Hol.ev p.1 p.2 : Hol W →+* ℂ) default) := by
    rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro f hf
    have : f = 0 := Hol.ext_fn fun p hp => by
      have h1 := (PrimeSpectrum.mem_vanishingIdeal _ _).1 hf _ ⟨⟨p, hp⟩, rfl⟩
      have h2 : Hol.ev p hp f ∈ (default : PrimeSpectrum ℂ).asIdeal := h1
      rw [Ideal.eq_bot_of_prime (default : PrimeSpectrum ℂ).asIdeal, Ideal.mem_bot] at h2
      rw [← Hol.ev_apply p hp, ← Hol.ev_apply p hp, h2, map_zero]
    rw [this]
    exact zero_mem _
  refine Dense.mono ?_ hd
  rintro _ ⟨p, rfl⟩
  refine ⟨equalizer.lift _ (h p.1 p.2) (default : PrimeSpectrum ℂ), ?_⟩
  exact congrArg (fun m : Sp ℂ ⟶ Sp (Hol W) => m (default : PrimeSpectrum ℂ)) (equalizer.lift_ι _ (h p.1 p.2))

end GlobalTheory.AnPer
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R), cob2 (addLaw R d) c = 0 → ∀ m : Fin d, (∀ n, 0 < n → coeff (Finsupp.single (Sum.inl m) n) c = 0) ∧ ∀ i j l, 0 < i → 0 < j → 0 < l → coeff (Finsupp.single (Sum.inl m) (i + j) + Finsupp.single (Sum.inr m) l) c * ((i + j).choose i : R) = coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (j + l)) c * ((j + l).choose j : R) := by
  first | exact @GlobalTheory.Katz.CocRel.relations | exact GlobalTheory.Katz.CocRel.relations | (intros; apply GlobalTheory.Katz.CocRel.relations <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.WDer

theorem X_mem_intBy (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] {τ : Type}
    (j : τ) : (X j : MvPowerSeries τ (Fr p k)) ∈ intBy p k τ 1 := by
  classical
  intro β
  refine ⟨if β = Finsupp.single j 1 then 1 else 0, ?_⟩
  rw [coeff_X, one_mul]
  split_ifs <;> simp

theorem lift_mem_intBy (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] {τ : Type}
    (f : MvPowerSeries τ k) : lift p f ∈ intBy p k τ 1 := by
  intro β
  exact ⟨WittVector.teichmuller p (coeff β f), by rw [coeff_lift, one_mul]⟩

theorem coboundaryOne_teichmullerLift_mem_integralDifferential (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ)
    (g : MvPowerSeries (Fin d) (Fr p k)) (hg : g ∈ quasiInt p k (Fin d)) :
    cob1 (fun i => lift p (μ i)) g ∈ quasiInt p k (Fin d ⊕ Fin d) := by
  unfold cob1 inL inR
  refine sub_mem (sub_mem ?_ ?_) ?_
  · exact GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_lift p (hμ.const i)) (fun i => lift_mem_intBy p k _) hg
  · exact GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_X _) (fun i => X_mem_intBy p k _) hg
  · exact GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_X _) (fun i => X_mem_intBy p k _) hg

theorem main : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ (N : ℕ) (g h : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → g ∈ quasiInt p k (Fin d) → (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α h = 0) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (g + h)) = algebraMap (WittVector p k) (Fr p k) w) → ∀ (α : Fin d →₀ ℕ) (i : Fin d), α.degree = N → ∃ w : WittVector p k, (α i : Fr p k) * coeff α h = algebraMap (WittVector p k) (Fr p k) w := by
  intro p _ k _ _ _ d μ hμ N g h hN hg hh hcob α i hα
  classical
  by_cases hi : α i = 0
  · exact ⟨0, by simp [hi]⟩
  set β : Fin d →₀ ℕ := α - Finsupp.single i 1 with hβdef
  have hαβ : α = β + Finsupp.single i 1 := by
    ext j
    simp only [hβdef, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs with hj
    · subst hj; omega
    · omega
  have hβdeg : β.degree + 1 = N := by
    rw [← hα, hαβ, map_add (f := _), Finsupp.degree_single]
  have hβ0 : β ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hβdeg
    omega
  set γ : Fin d ⊕ Fin d →₀ ℕ := β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 with hγdef
  have hγdeg : γ.degree = N := by
    rw [hγdef, map_add (f := _), Finsupp.degree_mapDomain, Finsupp.degree_single, hβdeg]
  have hγi : γ (Sum.inr i) = 1 := by
    rw [hγdef, Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range, Finsupp.single_eq_same, zero_add]
    rintro ⟨j, hj⟩
    exact Sum.inl_ne_inr hj

  obtain ⟨wg, hwg⟩ := coboundaryOne_teichmullerLift_mem_integralDifferential p k d μ hμ g hg γ (Sum.inr i)
  rw [hγi, Nat.cast_one, one_mul] at hwg
  obtain ⟨wt, hwt⟩ := hcob γ hγdeg

  have hlin : ∀ j (a : Fin d ⊕ Fin d →₀ ℕ), a.degree ≤ 1 →
      coeff a (lift p (μ j)) = coeff a (addLaw (Fr p k) d j) :=
    fun j a ha => (GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ j a ha).2
  have hlead := ((GlobalTheory.T.coboundary_eq_additive_leading_terms (Fr p k) d (fun j => lift p (μ j)) N hlin).1 h hh γ).2
    hγdeg.le
  have hhom := (GlobalTheory.T.additive_formal_group_coboundary_homogeneous (Fr p k) d N).2.2.2 h β i hβ0
  rw [formalCoboundary_add (fun j => constantCoeff_lift p (hμ.const j)), map_add (f := _), hwg, hlead,
    hhom, ← hαβ] at hwt
  refine ⟨wt - wg, ?_⟩
  have hai : α i = β i + 1 := by
    conv_lhs => rw [hαβ]
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [map_sub, ← hwt, hai, add_sub_cancel_left]

end GlobalTheory.Katz.WDer
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ i, constantCoeff (μ i) = 0) → (∀ g c, Red p g c → Red p (cob2 (fun i => Katz.lift p (μ i)) g) (cob2 μ c) ∧ Red p (swap g) (swap c)) ∧ (∀ b b', Red p b b' → Red p (cob1 (fun i => Katz.lift p (μ i)) b) (cob1 μ b') ∧ RedV p (lin b) (lin b')) ∧ (∀ i, Red p (op (fun i => Katz.lift p (μ i)) x1 (op (fun i => Katz.lift p (μ i)) x2 x3) i) (op μ x1 (op μ x2 x3) i) ∧ Red p (op (fun i => Katz.lift p (μ i)) (op (fun i => Katz.lift p (μ i)) x1 x2) x3 i) (op μ (op μ x1 x2) x3 i)) ∧ ∀ (c : WittVector p k) g, g ∈ intBy p k (Fin d ⊕ Fin d) c → cob2 (fun i => Katz.lift p (μ i)) g ∈ intBy p k _ c ∧ swap g ∈ intBy p k _ c := by
  first | exact @GlobalTheory.Katz.red_coboundaries | exact GlobalTheory.Katz.red_coboundaries | (intros; apply GlobalTheory.Katz.red_coboundaries <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.chain_complex_exact_square : ∀ (R : Type) [CommRing R] {X₁ X₂ X₃ X₄ : Scheme.{0}} (a : X₁ ⟶ X₂) (b : X₁ ⟶ X₃) (c : X₂ ⟶ X₄) (d : X₃ ⟶ X₄) (w₁ : biprod.lift ((free R).map (yoneda.map a)) (-(free R).map (yoneda.map b)) ≫ biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) = 0) (w₂ : biprod.lift ((chains R).map (sch.map a)) (-(chains R).map (sch.map b)) ≫ biprod.desc ((chains R).map (sch.map c)) ((chains R).map (sch.map d)) = 0), (ShortComplex.mk _ _ w₁).ShortExact → (ShortComplex.mk _ _ w₂).ShortExact := by
  first | (exact @GlobalTheory.EtC.chains_shortExact_of_free) | (exact GlobalTheory.EtC.chains_shortExact_of_free) | (intros; apply GlobalTheory.EtC.chains_shortExact_of_free <;> assumption)
end
